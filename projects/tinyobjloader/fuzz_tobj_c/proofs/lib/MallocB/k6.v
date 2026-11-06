(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx k5 js.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.

(* [comment removed for export] *)
Module CSecLinks.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rl"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "div"; "pow"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "None"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "ageom"; "AA"; "aa_depot"; "aa_geom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4"; "slink4"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv"; "pendS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "slink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.CInvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.CRebuildS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Links.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S0SaVCST;R1A2SaS22R2A2S5F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0SaVCST;R1A2S4S21R2A1A1F_;Fa;").

Lemma slink4_refl : ltac2:(tb__ "0|2|
S16S0S0S6S0S2SbS15R4A1M0R1A2ScR1SdG0SeR3Z8A2A2A2A2S4S3S14S10Q8A1M1A1S7R3S11Q40R2A2A2S12G1A1A3A1F_;Fz;S1aR5R4R3R2R2A5F_;Fr;FL;Fua;FG;").
Proof. intros G ua L r RD. split; [reflexivity|]. split; [reflexivity|]. split; [intros a; left; reflexivity | exact RD]. Qed.

Theorem links_kept : ltac2:(tb__ "0|4|
S17S6S13S10Q40M0A1M1A1S1bS0S0S6S6S6S6S20S1cRaR9R8R7A5S2SbZfc01R7A2ScR7SfZ2Z27A2A2A2S19RcA1S16S24R9A1S0S1eReR9R1RbA4S23RaR2R9R8A4S1aR4RbR3R9R8A5S1dS18R11A1R9R8A3S2S1fVCST;VXGL;R12R12S7RcA1S7R9A1A6S2S0S2SbS15ReA1M2R1A2ScR1SdG2SeR6Z8A2A2A2A2S4S3S14S10Q8A1M3A1S7RbS11G0R2A2A2S12G3A1A3A1F_;Fz;S2S1S3G1S9RaR1A2S9RdR1A2A3Fi;S1S3S13G3A1S8RaR1A2S8RdR1A2A3Fl;A2A2A2F_;F_;F_;F_;TL;TG;F_;F_;Frho3;Frho2;Frho1;Frho0;Fua;Fnv;Fmd;Ftp;Fr;FAs;").
Proof.
  intros A r tp md nv ua rho0 rho1 rho2 rho3 HA Hnv. cbn zeta. intros HPD (W1 & L1 & M1 & D1) (W2 & L2 & M2 & D2) (W3 & L3 & M3).
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (Hsep & Hlive & HPR & HSR & HQR & HDW & HIA & HTH & HMI).
  set (G := aa_geom A) in *. set (T := ag_thread G) in *. set (L := secmapsize nv) in *.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & ACV). fold T in G4, G5, G10, G13, G14.
  pose proof (geom_bands _ HG) as (FB & TB & CB & DB & TI & CI & DI). fold G T in TB, TI. fold G in FB, CB, DB, CI, DI.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in FB, TB, CB, DB, TI, CI, DI. rewrite FS_total_val in FB.
  destruct HPD as (PM & PAL & PL0 & PDI & ST & SC & SD & SF & SS & SP & SX & SDB). fold G L in PM, PL0, PDI, ST, SC, SD, SF, SS, SP, SX, SDB. fold T in ST.
  pose proof (secmapsize_bounds nv ltac:(clear -Hnv; lia)) as [SMB SMM]. fold L in SMB, SMM. unfold PG in SMM, PAL.
  pose proof (dyn_in_big _ _ _ PDI ltac:(clear -SMB; lia)) as UI. destruct PDI as (_ & _ & PDT & _ & PDB).
  pose proof (pab_facts _ A HSR) as (P1 & P2 & P3 & P4 & P5). fold G in P1, P2, P3.
  assert (U8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(clear; lia)) as X. rewrite PAL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (L8 : L mod 8 = 0).
  { pose proof (Z.div_mod L 4096 ltac:(clear; lia)) as X. rewrite SMM, Z.add_0_r in X. rewrite X. replace (4096 * (L / 4096)) with ((512 * (L / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (UT : ua + L <= 140737479966720) by (clear -PDT ACV; lia).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in PDB.
  pose proof (live_foot_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A _ HG Hsep HI3 HPR HSR SS SX) as LFN.
  unfold sepZ in SF, ST. cbn [fst snd] in SF, ST. rewrite FS_total_val in SF.
  assert (ESHL : Sh (ua + L) = Sh ua + L / 8).
  { unfold Sh. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by (clear; lia). clear. lia. }

  assert (RUNB : forall z, Sh ua <= z < Sh ua + L / 8 -> 2147446784 <= z < 17594333495296).
  { intros z Hz. rewrite <- ESHL in Hz.
    pose proof (sh_run_band2 ua (ua + L) z ltac:(unfold IMG_HI in UI; clear -UI; lia) ltac:(clear -UT PL0; lia) Hz) as BY.
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BY. exact BY. }
  idtac "lk:0".

  assert (NOC : forall a, client_addrA CST A a -> ~ rtint G a /\ ~ (ua <= a < ua + L)).
  { intros a Hcl.
    destruct (client_addr_cases CST A a _ HF Hcl) as [S|[Lv|[FR|[C|FL]]]].
    - fold G in S. split; [|clear -S PDT; lia].
      intros [X|X]; [unfold SEC_INST in X; clear -X S ACV; lia | clear -X S P2; lia].
    - destruct Lv as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & _). unfold IMG_HI in S2.
      pose proof (rz_bound n) as RZ.
      pose proof (LFN b n a Hbn ltac:(left; clear -Hx RZ; lia)) as NZ.
      pose proof (live_foot _ A HG Hsep HI3 HPR HSR b n a Hbn ltac:(left; clear -Hx RZ; lia)) as (X1 & X2 & _).
      pose proof (live_foot_pab _ A HG Hsep HI3 HPR HSR b n a Hbn ltac:(left; clear -Hx RZ; lia)) as X3. fold G T in X2, X3.
      split; [|intros X; apply NZ; left; exact X].
      intros [X|X]; [unfold SEC_INST, IMG_HI in *; clear -X X1; lia | exact (X3 X)].
    - destruct FR as (c & p & Hcp & Hp & _ & Hx). pose proof (fs_geom_nums G c p HG Hcp Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in M. fold G in Hx.
      destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). fold G in PF. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      split; [|clear -Hx M SF; lia].
      intros [X|X]; [unfold SEC_INST in X; clear -X Hx M; lia | unfold kPtrArrayReserve in X; clear -X Hx M PF; lia].
    - destruct (HCST _ C) as [X0 _]. unfold IMG_LO, IMG_HI in X0.
      split; [|unfold IMG_HI in UI; clear -X0 UI; lia].
      intros [X|X].
      + apply (HCSTS a C). unfold IMG_S, in_rangesZ. unfold SEC_INST in *.
        exists 0xeaa98, (0xead04 - 0xeaa98). split; [left; reflexivity | clear -X; lia].
      + unfold IMG_HI in P1. clear -X X0 P1. lia.
    - destruct FL as (c & p & Hcp & Hp & _ & Ea). pose proof (fs_geom_nums G c p HG Hcp Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G in Ea. unfold fs_flags in M, Ea. rewrite FS_kFlagsOffset_val in M, Ea. unfold IMG_HI in M.
      destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). fold G in PF. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      split; [|clear -M Ea SF; lia].
      intros [X|X]; [unfold SEC_INST in X; clear -X M Ea; lia | unfold kPtrArrayReserve in X; clear -X M Ea PF; lia]. }
  idtac "lk:1".

  destruct (AInvA_X A r tp md HA) as (HXd & _ & _).
  assert (NOD : forall a, KEEPD CST XGL A a -> ~ DFP (aa_depot A) a).
  { intros a HK. exact (keep_not_DFP UStopLe CST XGL HCST HXGL HCSTD A r tp md a HXd HK). }
  assert (BAND : forall a, 2147446784 <= a < 17594333495296 -> ~ DFP (aa_depot A) a).
  { intros a HB' HD.
    assert (HSEC : forall i ch, nth_error (aa_sec A) i = Some ch -> dyn_in (topG (aa_geom A)) (sc_map_beg ch) (sc_map_size ch)).
    { intros i ch Hi. destruct HSR as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
    assert (HPAB : dyn_ok (topG (aa_geom A)) (ag_pab (aa_geom A)) kPtrArrayReserve) by (destruct HSR as (_ & _ & _ & _ & X4' & _); exact X4').
    pose proof (zones_not_DFPw A a HG HI3 HSEC HPAB) as ZN. cbn zeta in ZN.
    destruct (DFP_split _ _ HD) as [Hs|Hws]; [pose proof (dstat_range a Hs) as DR; unfold MAP1, MAP1N, STORE in DR; clear -HB' DR; lia | ].
    apply ZN; [do 8 right; left; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact HB' | exact Hws]. }

  assert (BRT : forall a, 2147446784 <= a < 17594333495296 -> ~ rtint G a).
  { intros a HB' [X|X]; [unfold SEC_INST in X; clear -X HB'; lia |].
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in P3. clear -X HB' P3. lia. }
  idtac "lk:2".

  assert (NOS : forall a, client_shadowA CST XGL A a -> 2147446784 <= a < 17594333495296 /\ ~ (Sh ua <= a < Sh ua + L / 8)).
  { intros a C1. pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep C1) as B0. unfold SHADOW_OFF, HIGH_SHADOW_END in B0.
    split; [clear -B0; lia|]. intros X.
    assert (XIN : forall x, a = Sh x -> 0 <= x -> ua <= x < ua + L).
    { intros x -> Hx0. unfold Sh in X. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL.
      pose proof (Z.div_mod ua 8 ltac:(clear; lia)) as DU. rewrite U8, Z.add_0_r in DU.
      pose proof (Z.div_mod x 8 ltac:(clear; lia)) as DX. pose proof (Z.mod_pos_bound x 8 ltac:(clear; lia)) as MX. clear -X DL DU DX MX. lia. }
    destruct C1 as [(y & Cy & Ey)|(y & Gy & Ey)].
    - destruct (client_addr_bounds CST HCST A y _ HG HF Hsep Cy) as [By _]. pose proof (XIN y Ey ltac:(clear -By; lia)) as YIN.
      exact (proj2 (NOC y Cy) YIN).
    - destruct (HXGL y Gy) as [Y1 Y2]. pose proof (XIN y Ey ltac:(clear -Y1; unfold IMG_LO in *; lia)) as YIN. clear -YIN Y2 UI. lia. }
  idtac "lk:3".

  assert (DEFB : forall z, 2147446784 <= z < 17594333495296 -> rm rho0 (Z_to_bv 64 z) <> None -> rm rho3 (Z_to_bv 64 z) <> None).
  { intros z Hz Hd.
    assert (EZ : bv_unsigned (Z_to_bv 64 z) = z) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616; apply Z.mod_small; clear -Hz; lia).
    assert (H1 : rm rho1 (Z_to_bv 64 z) <> None).
    { destruct (M1 (Z_to_bv 64 z)) as [E|[(N & _)|(_ & N)]]; [rewrite E; exact Hd | exact (False_ind _ (Hd N)) | exact N]. }
    assert (H2 : rm rho2 (Z_to_bv 64 z) <> None).
    { destruct (M2 (Z_to_bv 64 z)) as [E|[(N & _)|[(_ & N)|N]]]; [rewrite E; exact H1 | exact (False_ind _ (H1 N)) | exact N |].
      rewrite EZ in N. exact (False_ind _ (BRT z Hz N)). }
    rewrite (M3 (Z_to_bv 64 z)); [exact H2|]. rewrite EZ. exact (BAND z Hz). }
  idtac "lk:4".
  split; [|split; [|split]].
  - split.
    + intros a Ba Hcl.
      assert (EZ : bv_unsigned (Z_to_bv 64 a) = a) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616; apply Z.mod_small; clear -Ba; lia).
      assert (KD : KEEPD CST XGL A a) by (destruct Hcl as [(C1 & _)|(C1 & _)]; [left; exact C1 | right; exact C1]).
      rewrite (M3 (Z_to_bv 64 a)) by (rewrite EZ; exact (NOD a KD)).
      destruct Hcl as [(C1 & _ & NE)|(C1 & _ & Hd)].
      * destruct (NOC a C1) as (N1 & N2).
        destruct (client_addr_bounds CST HCST A a _ HG HF Hsep C1) as [_ NB].
        assert (NRUN : ~ (Sh ua <= a < Sh ua + L / 8)) by (intros X; pose proof (RUNB a X) as Y; clear -Y NB; lia).
        assert (E1 : rm rho1 (Z_to_bv 64 a) = rm rho0 (Z_to_bv 64 a)).
        { destruct (M1 (Z_to_bv 64 a)) as [E|[(_ & _ & N)|(N & _)]]; [exact E | | ]; rewrite EZ in N; exfalso;
            [unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in N; clear -N NB; lia | exact (NRUN N)]. }
        rewrite <- E1.
        destruct (M2 (Z_to_bv 64 a)) as [E|[(_ & _ & N)|[(N & _)|N]]]; [exact E | | | ]; rewrite EZ in N; exfalso;
          [unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in N; clear -N NB; lia | exact (NRUN N) | exact (N1 N)].
      * destruct (NOS a C1) as (B0 & NRUN).
        assert (E1 : rm rho1 (Z_to_bv 64 a) = rm rho0 (Z_to_bv 64 a)).
        { destruct (M1 (Z_to_bv 64 a)) as [E|[(N & _)|(N & _)]]; [exact E | exact (False_ind _ (Hd N)) | rewrite EZ in N; exact (False_ind _ (NRUN N))]. }
        rewrite <- E1. rewrite <- E1 in Hd.
        destruct (M2 (Z_to_bv 64 a)) as [E|[(N & _)|[(N & _)|N]]]; [exact E | exact (False_ind _ (Hd N)) | rewrite EZ in N; exact (False_ind _ (NRUN N)) |].
        rewrite EZ in N. exact (False_ind _ (BRT a B0 N)).
    + intros x j Hx Hj Hdef.
      assert (Bx : SHADOW_OFF <= Sh x < HIGH_SHADOW_END).
      { destruct Hx as [[C1 C2]|GX].
        - destruct (client_addr_bounds CST HCST A x _ HG HF Hsep C1) as [B _]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. clear -B. lia.
        - destruct (HXGL x GX) as [X0 X1]. unfold IMG_LO, IMG_HI, Sh, SHADOW_OFF, HIGH_SHADOW_END in *. clear -X0 X1. lia. }
      unfold SHADOW_OFF, HIGH_SHADOW_END in Bx.
      destruct (word_byte_range (Sh x) j ltac:(clear -Bx; lia) Hj) as (W1' & W2' & W3').
      unfold word_byte in *. apply DEFB; [|exact Hdef]. clear -W3' Bx Hj. lia.
  - intros z Hz. pose proof (RUNB z Hz) as Bz.
    assert (EZ : bv_unsigned (Z_to_bv 64 z) = z) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616; apply Z.mod_small; clear -Bz; lia).
    rewrite (M3 (Z_to_bv 64 z)); [exact (D2 z Hz)|]. rewrite EZ. exact (BAND z Bz).
  - intros i. rewrite W3, W2. apply W1.
  - intros l. rewrite L3, L2. apply L1.
Qed.
End Links.
End CSecLinks.

(* [comment removed for export] *)
Module CDepotCallMW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Specif"; "sig"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.CDepotCallMW1.INST"; "T4_i"; "nobj_i"; "CP1"; "CP2"; "CP3"; "sd_1"; "sd_2"; "sd_3"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "list"; "nil"; "option"; "pair"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.CDepotCallW"; "T40"; "T4a"; "T4b"; "T4c"; "T4d"; "T4m1"; "T4m2"; "T4m3"; "X4"; "X4a"; "X4b"; "X4c"; "X4r"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SegD_wf SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.CDepotCallW.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CallocMemoSPW1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.

Lemma by_casesN : ltac2:(tb__ "0|2|
S24OF_;R1Z1M0A1R2Z2A1R3Z3M1A1S24S2S13G0R1A2S13R1G1A2A2R6R2A1F_;Fsz;F_;F_;F_;FP;").
Proof. intros P H1 H2 H3 sz Hsz. assert (E : sz = 1 \/ sz = 2 \/ sz = 3) by lia. destruct E as [-> | [-> | ->]]; assumption. Qed.
Ltac memo_rw t M := lazymatch goal with |- context [t] => pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta | _ => fail "memo_rw: stage term not found" t end.
Ltac vmc := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Definition mE : {x | E4d (Wcan 1) st tmax = x} := exist _ m_E4d m_E4d_eq.
Definition mC5 : {x | C5 (Wcan 1) st tmax = x} := exist _ m_C5 m_C5_eq.
Lemma mXr_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S23U1Vst;Vtmax;Z1A4R1A3Lx;A2"). Proof. eexists. unfold X4r, X4f. memo_rw (E4d (Wcan 1) st tmax) mE. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXa_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S20U1Vst;Vtmax;Z1A4R1A3Lx;A2"). Proof. eexists. unfold X4a. memo_rw (X4r 1%nat st tmax 1) mXr_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXb_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S21U1Vst;Vtmax;Z1A4R1A3Lx;A2"). Proof. eexists. unfold X4b. memo_rw (X4a 1%nat st tmax 1) mXa_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXc_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S22U1Vst;Vtmax;Z1A4R1A3Lx;A2"). Proof. eexists. unfold X4c. memo_rw (X4b 1%nat st tmax 1) mXb_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mX_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1fU1Vst;Vtmax;Z1A4R1A3Lx;A2"). Proof. eexists. unfold X4. memo_rw (X4c 1%nat st tmax 1) mXc_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXr_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S23U1Vst;Vtmax;Z2A4R1A3Lx;A2"). Proof. eexists. unfold X4r, X4f. memo_rw (E4d (Wcan 1) st tmax) mE. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXa_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S20U1Vst;Vtmax;Z2A4R1A3Lx;A2"). Proof. eexists. unfold X4a. memo_rw (X4r 1%nat st tmax 2) mXr_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXb_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S21U1Vst;Vtmax;Z2A4R1A3Lx;A2"). Proof. eexists. unfold X4b. memo_rw (X4a 1%nat st tmax 2) mXa_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXc_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S22U1Vst;Vtmax;Z2A4R1A3Lx;A2"). Proof. eexists. unfold X4c. memo_rw (X4b 1%nat st tmax 2) mXb_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mX_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1fU1Vst;Vtmax;Z2A4R1A3Lx;A2"). Proof. eexists. unfold X4. memo_rw (X4c 1%nat st tmax 2) mXc_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXr_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S23U1Vst;Vtmax;Z3A4R1A3Lx;A2"). Proof. eexists. unfold X4r, X4f. memo_rw (E4d (Wcan 1) st tmax) mE. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXa_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S20U1Vst;Vtmax;Z3A4R1A3Lx;A2"). Proof. eexists. unfold X4a. memo_rw (X4r 1%nat st tmax 3) mXr_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXb_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S21U1Vst;Vtmax;Z3A4R1A3Lx;A2"). Proof. eexists. unfold X4b. memo_rw (X4a 1%nat st tmax 3) mXa_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXc_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S22U1Vst;Vtmax;Z3A4R1A3Lx;A2"). Proof. eexists. unfold X4c. memo_rw (X4b 1%nat st tmax 3) mXb_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mX_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1fU1Vst;Vtmax;Z3A4R1A3Lx;A2"). Proof. eexists. unfold X4. memo_rw (X4c 1%nat st tmax 3) mXc_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.

Definition gP (o : option (wsub * list sobj * axst)) : wsub * list sobj * axst := ltac2:(tb__ "0|4|
S10SdSdS14SeS15A1M0A2S0A2M1A1G1Lo;Vo;G1R1Lx;S11SdSeSdS25S16A2M2A1M3G0A2S0S11G3G0SfG2A1SfS15A1A4S26Z0A1A4X10x2").
Definition CP1 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (proj1_sig mX_1) 1)).
Definition CP2 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (proj1_sig mX_2) 2)).
Definition CP3 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (proj1_sig mX_3) 3)).
Definition CP (sz : Z) : wsub * list sobj * axst := ltac2:(tb__ "0|1|
ScSdSdS14SeS15A1A2S0A2L_;M0S12Vsz;Z1A2S6G0S12Vsz;Z2A2S7S8Xcx2Xcx2").
Definition s4_i (sz : Z) : wsub := fst (fst (CP sz)).
Definition R4_i (sz : Z) : list sobj := snd (fst (CP sz)).
Definition T4_i (sz : Z) : axst := snd (CP sz).
Definition nobj_i : nat := 49%nat.
Lemma mT0_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S17U1Vst;Vtmax;S4Z1A5R1A3Lx;A2"). Proof. eexists. unfold T40. memo_rw (X4 1%nat st tmax 1) mX_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTa_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S18U1Vst;Vtmax;S4Z1A5R1A3Lx;A2"). Proof. eexists. unfold T4a. memo_rw (T40 1%nat st tmax T4_i 1) mT0_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTb_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S19U1Vst;Vtmax;S4Z1A5R1A3Lx;A2"). Proof. eexists. unfold T4b. memo_rw (T4a 1%nat st tmax T4_i 1) mTa_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTc_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1aU1Vst;Vtmax;S4S5Z1A6R1A3Lx;A2"). Proof. eexists. unfold T4c. memo_rw (T4b 1%nat st tmax T4_i 1) mTb_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT1_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1cU1Vst;Vtmax;S4S5Z1A6R1A3Lx;A2"). Proof. eexists. unfold T4m1. memo_rw (T4c 1%nat st tmax T4_i nobj_i 1) mTc_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT2_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1dU1Vst;Vtmax;S4S5Z1A6R1A3Lx;A2"). Proof. eexists. unfold T4m2. memo_rw (T4m1 1%nat st tmax T4_i nobj_i 1) mT1_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT3_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1eU1Vst;Vtmax;S4S5Z1A6R1A3Lx;A2"). Proof. eexists. unfold T4m3. memo_rw (T4m2 1%nat st tmax T4_i nobj_i 1) mT2_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTd_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1bU1Vst;Vtmax;S4S5Z1A6R1A3Lx;A2"). Proof. eexists. unfold T4d. memo_rw (T4m3 1%nat st tmax T4_i nobj_i 1) mT3_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT0_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S17U1Vst;Vtmax;S4Z2A5R1A3Lx;A2"). Proof. eexists. unfold T40. memo_rw (X4 1%nat st tmax 2) mX_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTa_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S18U1Vst;Vtmax;S4Z2A5R1A3Lx;A2"). Proof. eexists. unfold T4a. memo_rw (T40 1%nat st tmax T4_i 2) mT0_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTb_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S19U1Vst;Vtmax;S4Z2A5R1A3Lx;A2"). Proof. eexists. unfold T4b. memo_rw (T4a 1%nat st tmax T4_i 2) mTa_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTc_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1aU1Vst;Vtmax;S4S5Z2A6R1A3Lx;A2"). Proof. eexists. unfold T4c. memo_rw (T4b 1%nat st tmax T4_i 2) mTb_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT1_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1cU1Vst;Vtmax;S4S5Z2A6R1A3Lx;A2"). Proof. eexists. unfold T4m1. memo_rw (T4c 1%nat st tmax T4_i nobj_i 2) mTc_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT2_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1dU1Vst;Vtmax;S4S5Z2A6R1A3Lx;A2"). Proof. eexists. unfold T4m2. memo_rw (T4m1 1%nat st tmax T4_i nobj_i 2) mT1_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT3_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1eU1Vst;Vtmax;S4S5Z2A6R1A3Lx;A2"). Proof. eexists. unfold T4m3. memo_rw (T4m2 1%nat st tmax T4_i nobj_i 2) mT2_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTd_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1bU1Vst;Vtmax;S4S5Z2A6R1A3Lx;A2"). Proof. eexists. unfold T4d. memo_rw (T4m3 1%nat st tmax T4_i nobj_i 2) mT3_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT0_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S17U1Vst;Vtmax;S4Z3A5R1A3Lx;A2"). Proof. eexists. unfold T40. memo_rw (X4 1%nat st tmax 3) mX_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTa_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S18U1Vst;Vtmax;S4Z3A5R1A3Lx;A2"). Proof. eexists. unfold T4a. memo_rw (T40 1%nat st tmax T4_i 3) mT0_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTb_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S19U1Vst;Vtmax;S4Z3A5R1A3Lx;A2"). Proof. eexists. unfold T4b. memo_rw (T4a 1%nat st tmax T4_i 3) mTa_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTc_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1aU1Vst;Vtmax;S4S5Z3A6R1A3Lx;A2"). Proof. eexists. unfold T4c. memo_rw (T4b 1%nat st tmax T4_i 3) mTb_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT1_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1cU1Vst;Vtmax;S4S5Z3A6R1A3Lx;A2"). Proof. eexists. unfold T4m1. memo_rw (T4c 1%nat st tmax T4_i nobj_i 3) mTc_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT2_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1dU1Vst;Vtmax;S4S5Z3A6R1A3Lx;A2"). Proof. eexists. unfold T4m2. memo_rw (T4m1 1%nat st tmax T4_i nobj_i 3) mT1_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT3_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1eU1Vst;Vtmax;S4S5Z3A6R1A3Lx;A2"). Proof. eexists. unfold T4m3. memo_rw (T4m2 1%nat st tmax T4_i nobj_i 3) mT2_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTd_3 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1bU1Vst;Vtmax;S4S5Z3A6R1A3Lx;A2"). Proof. eexists. unfold T4d. memo_rw (T4m3 1%nat st tmax T4_i nobj_i 3) mT3_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Definition sd_1 : wsub := Eval vm_compute in (infer_sub GW (ax_S (proj1_sig mTd_1)) (ax_S (proj1_sig mC5))).
Definition sd_2 : wsub := Eval vm_compute in (infer_sub GW (ax_S (proj1_sig mTd_2)) (ax_S (proj1_sig mC5))).
Definition sd_3 : wsub := Eval vm_compute in (infer_sub GW (ax_S (proj1_sig mTd_3)) (ax_S (proj1_sig mC5))).
Definition sd_i (sz : Z) : wsub := ltac2:(tb__ "0|1|
ScS14L_;M0S12Vsz;Z1A2S9G0S12Vsz;Z2A2SaSbXcx2Xcx2").

End INST.
End CDepotCallMW1.

(* [comment removed for export] *)
Module SpineCallocSec5.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "nil"; "true"; "prod"; "Some"; "option"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "ss_next"; "sv"; "holds"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU"; "F_g4"; "DPENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Placement StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import EnsureMapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.CInvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SEC5.
Variable nW : nat. Variable st : ustop. Variable tmax : Z. Variable hi : bool.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S15S21VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S6S25S22Vnx;A2S9A3").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
S24VnW;Vst;Vnx;VBX;A4").

Lemma F_g4_hold : ltac2:(tb__ "0|1|
S4S4F_;S4S19SeS1aQ40A1M0SeS5G0A1S5S1dA1S1cVJG;R9R8R7R6R5R4R3R2R1A9S1bSfS12R5A1S17Vnx;A1A3F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & ENS & _).
  destruct HJ as (_ & _ & _ & HP & _ & _ & _ & Hnv & _). cbn zeta in Hnv.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  destruct HP as (_ & _ & _ & (D1 & D2 & D3 & _) & _). pose proof (topG_range (aa_geom A)) as TG.
  pose proof (secmapsize_bounds nv ltac:(lia)) as (MB1 & MB2).
  assert (NSV : secneeded nv = (nv + 8 - 1) / 8 * 8 + 4096) by reflexivity.
  pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (nv + 8 - 1) 8 ltac:(lia)) as MBd.
  pose proof (urange a) as Ra.
  unfold F_g4. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval branch_taken]. intros H. unfold bv_ltu in H. apply Z.ltb_lt in H.
  rewrite !add_val, ENS, Enx, E12, !u64_lit in H by lia. fold nv in H.
  rewrite (Z.mod_small (bv_unsigned a + 4096)) in H by lia. rewrite (Z.mod_small (bv_unsigned a + 6144)) in H by lia.
  rewrite !Z.mod_small in H by lia. lia.
Qed.

Section G41.
Variables (T4 U4 X5 : axst).
Hypothesis WU4 : ltac2:(tb__ "0|0|
S0S6S13S1VU4;A1A1S9A3").
Hypothesis DU4 : ltac2:(tb__ "0|4|
S0ScSaS5SaS11S11A2M0A1M1S5SfA1M2A2M3A1S1fS1VT4;A1S1VU4;A1A2SbG3SdG1G2S8G0A1S17Vnx;A1A4A2A3").
Hypothesis NXU4 : ltac2:(tb__ "0|0|
S0S15S10S1VU4;A1A1S10S1VT4;A1A1A3").
Hypothesis HU4 : ltac2:(tb__ "0|0|
S0S2S3VT4;S1VU4;A1A2VU4;A3").
Hypothesis Cert5 : ltac2:(tb__ "0|1|
S0S6S20S23Ufa0S7S14S18S8S14A1A3VGS;S7S2VU4;S8S2A1M0A3S7S2VX5;G0A3A6S9A3").

Lemma RSU4 : ltac2:(tb__ "0|1|
S4S4F_;S4S19SeS1aQ40A1M0SeS5G0A1S1eS16Vsegs;VJG;R8R7R6R5R4A5VT4;R3R2R1A6S16Vsegs;VJG;R9R8R7R6R5A5VU4;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]]. rewrite <- HU4.
  eapply SPA_restate; [exact WU4 | exact DU4 | exact NXU4 | constructor | | exact Hw].
  exact (F_g4_hold BX A Kc rho a rhoX tp tr md (proj2 Hw)).
Qed.
End G41.
End SEC5.
End SpineCallocSec5.

(* [comment removed for export] *)
Module SpineCallocSecE2.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "ax_X"; "ax_base"; "shadow_addr"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nil"; "list"; "app"; "prod"; "pair"; "option"; "length"; "None"; "Some"; "false"; "fst"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sprop"; "ss_next"; "sobj"; "SLit"; "reg_sv"; "SVar"; "rw"; "ss_facts"; "eval"; "ss_objs"; "SPBranch"; "rm"; "swf"; "sprop_below"; "SPNot"; "obj_range"; "ranges_disjoint"; "ro_addr"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_sec"; "aa_geom"; "sec_chunk"; "aa_ptr_committed"; "budget_bound"; "ageom"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "le"; "of_nat"; "pow"; "div"; "ge"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST"; "genL"; "Bw"; "F_l2"; "F_g3"; "O_1"; "O_2"; "x11e3"; "O_blk"; "O_w"; "a0e3"; "carveS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "V_NCH"; "V_NRES"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4"; "slink4"; "JGo"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "alloc_top"; "m_vmmaps"; "map_contains"; "region_free"; "vm_forget_range"; "vm_maps"; "vm_reserved"; "with_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "SKEL0"; "JGs"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_fixed_rw_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "overlap_sum";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Placement StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import EnsureMapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.CInvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSecE1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac rr X := intros; eapply X; revgoals; [> eassumption ..].

Section SEC4E.
Variable nW : nat. Variable st : ustop. Variable tmax : Z. Variable hi : bool.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S1bS71VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0ScS54S89Vnx;A2SdA3").
Variable AX : AA -> AA.
Hypothesis AXg : ltac2:(tb__ "0|0|
S3dS0S43S3fVAX;R1A1A1S3fR1A1A3FX;").
Hypothesis AXs : ltac2:(tb__ "0|0|
S3dS0SfS40A1S3eVAX;R1A1A1S3eR1A1A3FX;").
Hypothesis AXp : ltac2:(tb__ "0|0|
S3dS0S1aS41VAX;R1A1A1S41R1A1A3FX;").
Hypothesis AXb : ltac2:(tb__ "0|0|
S3dS0S1aS42VAX;R1A1A1S42R1A1A3FX;").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
S82VnW;Vst;Vnx;VBX;A4").
Let slink : Z -> Z -> valuation -> valuation -> Prop := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.slink.
Let AXP : AA -> AA := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4.AXP AX.
Let JGo : ltac2:(tb__ "0|0|
S3dS4fS1cS3bQ40A1S38Fa;Frho;FKc;FA;") := ltac2:(tb__ "0|0|
S74VnW;Vst;Vnx;VAX;A4").

Lemma ecfg_2 : ltac2:(tb__ "0|3|
SfS1aA1S5S5S5S38S4dOF_;SfS3bQ40A1A1S1cS39Vsegs;VGS;R4A3S0ScS54VGS;S1fS4R8A1A1A2SdA3S0ScS34S4eUfa0RaVGS;SbS32S33R9Z1S21Z0M0A1M1A3SeS32A1M2A3SbS32S33R8G0G1A3SbS32S33R7G0G1A3G2A3A3A6SdA3S1cS4cVsegs;S37Vsegs;R8RaR1R6A5R7A3Frho';S1cS4cVsegs;S37Vsegs;R9RaR1R7A5R8A3Frho';S4cVsegs;S37Vsegs;R9RcR6R7A5R8A3F_;F_;F_;F_;F_;Frho;Ftp;FQ;FJx;FE2;FE1;FC;Fcutpcs;").
Proof.
  intros cutpcs C E1 E2 Jx Q tp rho HST NXC HC HE1 HE2.
  apply (ecfg_cutG 4000%nat cutpcs GS [mkVNA C 1 (SLit 0)] [mkVNA E1 0 (SLit 0); mkVNA E2 0 (SLit 0)] Jx Q tp C rho HST).
  - intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. apply Pos.leb_le. exact NXC.
  - exact HC.
  - intros E' rho' HinE. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    + eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HE1 rho')].
    + eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HE2 rho')].
  - left. reflexivity.
Qed.

Section G3E.

Variables (D2 U2 X3a X3b CS3 G3 X3a3 L3a L3b CO3b T4a T4b Y4a0 Y4a1 Y4b0 Y4b1 : axst).
Variables (sLa sLb s4a0 s4a1 s4b0 s4b1 : wsub).

Hypothesis WU2 : ltac2:(tb__ "0|0|
S0ScS2aS4VU2;A1A1SdA3").
Hypothesis DU2 : ltac2:(tb__ "0|4|
S0S13S11SfS11S1dS1dA2M0A1M1SfS1eA1M2A2M3A1S80S4VD2;A1S4VU2;A1A2S16G3S12G1G2SeG0A1S5bA4A2A3").
Hypothesis NXU2 : ltac2:(tb__ "0|0|
S0S1bS1fS4VU2;A1A1S1fS4VD2;A1A1A3").
Hypothesis HU2 : ltac2:(tb__ "0|0|
S0S5S7VD2;S4VU2;A1A2VU2;A3").

Hypothesis Cert3 : ltac2:(tb__ "0|1|
S0ScS35S4eUfa0SbS1aZ706a0SbS1aZ410f0SeS1aA1A3A3VGS;SbS5VU2;SeS5A1M0A3SbS5VX3a;SbS5VX3b;G0A3A3A6SdA3").

Hypothesis WC3 : ltac2:(tb__ "0|0|
S0ScS2aS4VCS3;A1A1SdA3").
Hypothesis DC3 : ltac2:(tb__ "0|4|
S0S13S11SfS11S1dS1dA2M0A1M1SfS1eA1M2A2M3A1S80S4VX3a;A1S4VCS3;A1A2S16G3S12G1G2SbG0S12S1dS1dS61S59A4SeG0A1A3SeS1eA1A4A2A3").
Hypothesis NXC3 : ltac2:(tb__ "0|0|
S0S1bS1fS4VCS3;A1A1S1fS4VX3a;A1A1A3").
Hypothesis HC3 : ltac2:(tb__ "0|0|
S0S5S7VX3a;S4VCS3;A1A2VCS3;A3").
Hypothesis FX3a : ltac2:(tb__ "0|0|
S65S1eS10S1eSbS1eS28S6cS23S6fA1S23S70A1A3SeS1eA1A3S5bA3S25S4VX3a;A1A1A3").
Hypothesis IC3 : ltac2:(tb__ "0|0|
S0S13S6dA1S85S4eS30S4VCS3;A1A1A2S16S6dS6eA2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1Z11A2S21ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZaA2S59A3").
Hypothesis BBw : ltac2:(tb__ "0|0|
S0ScS31S1fS4VCS3;A1A1S59A2SdA3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZbA2S21Z20000A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZcA2S21Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZdA2S21Z32A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZeA2S21ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZfA2S21Z0A1A3").
Hypothesis XC3 : ax_X CS3 = [].
Hypothesis SK3 : ltac2:(tb__ "0|2|
S0SfS11S11S1dS1dA2S1dA2M0A1S68S20G0S69S27S4VCS3;A1A1A4S68S20G0S69S10S20SbS20S5dVnx;A1SbS20S5cVnx;A1SeS20A1M1A3A3S10S20S81VnW;Vnx;A2G1A3A3A4A3").
Hypothesis FC3 : ltac2:(tb__ "0|0|
S65S1eS10S1eS53VW;Vst;A2S52S51A1A3S25S4VCS3;A1A1A3").
Hypothesis FCS3 : ltac2:(tb__ "0|0|
S65S1eS10S1eSbS1eS28S6cS23S6fA1S23S70A1A3SeS1eA1A3S5bA3S25S4VCS3;A1A1A3").
Hypothesis NXS3 : ltac2:(tb__ "0|0|
S0ScS54VGS;S1fS4VCS3;A1A1A2SdA3").

Hypothesis HG3 : ltac2:(tb__ "0|1|
S0S5S7VCS3;S84S4VCS3;A1M0S59S10S20S27G0A1SbS20S5fSeS20A1A3A3S1fG0A1A4A2VG3;A3").

Hypothesis Cert3a : ltac2:(tb__ "0|1|
S0ScS35S4eUfa0SbS1aZ410f0SeS1aA1A3VGS;SbS5VG3;SeS5A1M0A3SbS5VX3a3;G0A3A6SdA3").

Hypothesis ELa : ltac2:(tb__ "0|0|
S0ScS6VX3a3;S58VX3a3;A1VsLa;A3SdA3").
Hypothesis IDa : ltac2:(tb__ "0|0|
S0ScS55VsLa;VGS;A2SdA3").
Hypothesis GLa : ltac2:(tb__ "0|0|
S0S1dS56VsLa;S1fS4VX3a3;A1A1A2S5eA3").
Hypothesis FBLa : ltac2:(tb__ "0|0|
S0ScS67S1eS2bS1fS4S58VX3a3;A1A1A1A1S5aS1fS4VX3a3;A1A1A1A3SdA3").
Hypothesis HL3a : ltac2:(tb__ "0|0|
S0S5S36S5aS1fS4VX3a3;A1A1A1S58VX3a3;A1A2VL3a;A3").
Hypothesis ELb : ltac2:(tb__ "0|0|
S0ScS6VX3b;S58VX3b;A1VsLb;A3SdA3").
Hypothesis IDb : ltac2:(tb__ "0|0|
S0ScS55VsLb;VGS;A2SdA3").
Hypothesis GLb : ltac2:(tb__ "0|0|
S0S1dS56VsLb;S1fS4VX3b;A1A1A2S5eA3").
Hypothesis FBLb : ltac2:(tb__ "0|0|
S0ScS67S1eS2bS1fS4S58VX3b;A1A1A1A1S5aS1fS4VX3b;A1A1A1A3SdA3").
Hypothesis HL3b : ltac2:(tb__ "0|0|
S0S5S36S5aS1fS4VX3b;A1A1A1S58VX3b;A1A2VL3b;A3").

Hypothesis HCOb : ltac2:(tb__ "0|0|
S0S5S62VL3b;S60A2VCO3b;A3").
Hypothesis WCOb : ltac2:(tb__ "0|0|
S0ScS2aS4VCO3b;A1A1SdA3").
Hypothesis XCb : ax_X L3b = [].
Hypothesis SKb : ltac2:(tb__ "0|2|
S0SfS11S11S1dS1dA2S1dA2M0A1S68S20G0S69S27S4VL3b;A1A1A4S68S20G0S69S10S20SbS20S5dVnx;A1SbS20S5cVnx;A1SeS20A1M1A3A3S10S20S81VnW;Vnx;A2G1A3A3A4A3").
Hypothesis FCb : ltac2:(tb__ "0|0|
S65S1eS10S1eS53VW;Vst;A2S52S51A1A3S25S4VL3b;A1A1A3").
Hypothesis FXb : ltac2:(tb__ "0|0|
S65S1eSbS1eS2cS28S6cS23S6fA1S23S70A1A3A1SeS1eA1A3S25S4VL3b;A1A1A3").

Hypothesis Cert4a : ltac2:(tb__ "0|1|
S0ScS35S4eUfa0SbS1aZ3c614SeS1aA1A3VGS;SbS5VL3a;SeS5A1M0A3SbS5VY4a0;SbS5VY4a1;G0A3A3A6SdA3").
Hypothesis E4a0 : ltac2:(tb__ "0|0|
S0ScS6VY4a0;VT4a;Vs4a0;A3SdA3").
Hypothesis I4a0 : ltac2:(tb__ "0|0|
S0ScS55Vs4a0;VGS;A2SdA3").
Hypothesis E4a1 : ltac2:(tb__ "0|0|
S0ScS6VY4a1;VT4a;Vs4a1;A3SdA3").
Hypothesis I4a1 : ltac2:(tb__ "0|0|
S0ScS55Vs4a1;VGS;A2SdA3").
Hypothesis Cert4b : ltac2:(tb__ "0|1|
S0ScS35S4eUfa0SbS1aZ3c614SeS1aA1A3VGS;SbS5VCO3b;SeS5A1M0A3SbS5VY4b0;SbS5VY4b1;G0A3A3A6SdA3").
Hypothesis E4b0 : ltac2:(tb__ "0|0|
S0ScS6VY4b0;VT4b;Vs4b0;A3SdA3").
Hypothesis I4b0 : ltac2:(tb__ "0|0|
S0ScS55Vs4b0;VGS;A2SdA3").
Hypothesis E4b1 : ltac2:(tb__ "0|0|
S0ScS6VY4b1;VT4b;Vs4b1;A3SdA3").
Hypothesis I4b1 : ltac2:(tb__ "0|0|
S0ScS55Vs4b1;VGS;A2SdA3").

Hypothesis NXEU2 : ltac2:(tb__ "0|0|
S0ScS54VGS;S1fS4VU2;A1A1A2SdA3").
Hypothesis NXEG3 : ltac2:(tb__ "0|0|
S0ScS54VGS;S1fS4VG3;A1A1A2SdA3").
Hypothesis NXEL3a : ltac2:(tb__ "0|0|
S0ScS54VGS;S1fS4VL3a;A1A1A2SdA3").
Hypothesis NXECOb : ltac2:(tb__ "0|0|
S0ScS54VGS;S1fS4VCO3b;A1A1A2SdA3").
Hypothesis ECert3 : ltac2:(tb__ "0|3|
S0ScS34S4eUfa0SbS1aZ706a0SbS1aZ410f0SeS1aA1A3A3VGS;SbS32S33VU2;Z1S21Z0M0A1M1A3SeS32A1M2A3SbS32S33VX3a;G0G1A3SbS32S33VX3b;G0G1A3G2A3A3A6SdA3").
Hypothesis ECert3a : ltac2:(tb__ "0|3|
S0ScS34S4eUfa0SbS1aZ410f0SeS1aA1A3VGS;SbS32S33VG3;Z1S21Z0M0A1M1A3SeS32A1M2A3SbS32S33VX3a3;G0G1A3G2A3A6SdA3").
Hypothesis ECert4a : ltac2:(tb__ "0|3|
S0ScS34S4eUfa0SbS1aZ3c614SeS1aA1A3VGS;SbS32S33VL3a;Z1S21Z0M0A1M1A3SeS32A1M2A3SbS32S33VY4a0;G0G1A3SbS32S33VY4a1;G0G1A3G2A3A3A6SdA3").
Hypothesis ECert4b : ltac2:(tb__ "0|3|
S0ScS34S4eUfa0SbS1aZ3c614SeS1aA1A3VGS;SbS32S33VCO3b;Z1S21Z0M0A1M1A3SeS32A1M2A3SbS32S33VY4b0;G0G1A3SbS32S33VY4b1;G0G1A3G2A3A3A6SdA3").

Lemma RSU' : ltac2:(tb__ "0|1|
S3dS4fS1cS3bQ40A1M0S1cSfG0A1S4dS45S44S47S14S40S3eR7A1A2A1Z1A2S48Z2Z14A2A2S37Vsegs;VJG;VAX;R8R7R6R5A5VD2;R4R3R2A6S37Vsegs;VJG;VAX;R9R8R7R6A5VU2;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr RSU. Qed.
Lemma RS3' : ltac2:(tb__ "0|1|
S3dS4fS1cS3bQ40A1M0S1cSfG0A1S4dS37Vsegs;VJG;VAX;R7R6R5R4A5VX3a;R3R2R1A6S37Vsegs;VJG;VAX;R8R7R6R5A5VCS3;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr RS3. Qed.
Lemma ens_oblig' : ltac2:(tb__ "0|c|
S3dS4fS1cS3bQ40M0A1M1S1cSfG1A1S57VW;Vst;A2S50R6A1S45S44S47S14S40S3eR8A1A2A1Z1A2S48Z2Z14A2A2SfS77A1M2S75S76S87Vsegs;R8R7VCS3;S12G2S6aR3S6bR2R1A2A4A5VJG;VAX;RdRcRbRaR9R8R4R2A9S26RaS59A2G1S3aG0R1A2M3S1aZ20000S1aS1S0S1aS4bR2Z1000A2Z0M4A3S1S45G4R2A2S1S46S44R2R1A2M5S78S79R6A1M6A1A2S1S0ScS7bS7eG6A1R3S3cG0R1A2M7A3SdA3S1S0ScS7aS7dG6A1M8R3G7A3SdA3S1S46S86G8R2G5A3R1A2S1S4aS88R6RcA2R1A2S1S20S66S20R1S27S4VCS3;A1A1A3S2eS2dRfR2A2S12S1aS1aR4S44R4R3A2A4A2F_;Fo;S1G1S1S46R3G3A2S45G3S44R3R2A2A2A2S0ScS2fVsegs;R2A2S17A3F_;Fx;S1S11S1dS1dA2M9S1aS66G9R2S8VCS3;A1A3S1S46S3aG0S26R10S18S1dS1dR3A3A2A2MaR2A2S45R2S44GaS3aG0S26R10S19S1dS1dR3A3A2A2A2A2A2S2S1S46R6S3aG0SaS3aG0S26R11S9VCS3;A1A2A2R3A2A2MbA2S45GbS44R6R5A2A2A2A1F_;F_;Fy;Frr;VJGo;R11R10RfReRdRcR8S7cR2G5S7fS83G6R3G7A3R6A2A3A8A2A2A2A2A2A2A2A2A2A2Tnlit;Tua;Ta0;F_;F_;Fmd;Fms;Ftr;F_;F_;F_;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr ens_oblig. Qed.
Lemma ensure_post' : ltac2:(tb__ "0|6|
S3dS4fS1cS3bQ40M0A1M1S1cSfG1A1SfS77A1M2S75S76S57VW;Vst;A2S1aS1S46S72S3aG0R8A2A1M3R1A2S45R1S44G3S49S63S3aG0S24R9PcM4A2A2A1Z8A2A2A2A2S2S0S13S3bQ8A1M5A1S29RaS3cG0R2A2A2S15G5A1A3A1F_;Fz;S37Vsegs;VJGo;RbRaR9R8A4VG3;R7R6S12G2S6aR5S6bR4R3A2A4A6S3S1cS1cS3S1cS1cS1S73S3fReA1S3aG0RbA2S63S3aG0S24RcG4A2A2A1RcR1A5S37Vsegs;VJG;VAXP;ReRdR1RbA5VG3;R2R9S12G2S6aR8S6bR7R6A2A4A6A2Lrho'';A2Lr2;A2F_;F_;F_;Fmd';Fms;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof. rr ensure_post. Qed.
Lemma carve_w' : ltac2:(tb__ "0|1|
S3dS4fS1cS3bQ40A1M0S1cSfG0A1S4dS57VW;Vst;A2S37Vsegs;VJG;VAX;R8R7R6R5A5VL3b;R4R3R2A6S37Vsegs;VJG;VAX;R9R8R7R6A5VCO3b;R5R4R3A6F_;F_;Fw;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof. rr carve_w. Qed.

Lemma epath_b : ltac2:(tb__ "0|2|
S3dS4fS1cS3bQ40A1M0S4dOF_;S57VW;Vst;A2S64VW;Vst;A2S50R6A1S1cSfG0A1M1S4cVsegs;S37Vsegs;VJG;VAX;RaR9R8R7A5VT4b;R2R1A5R6A3FtY;FrY;S1cG1S4cVsegs;S37Vsegs;VJG;VAX;RbRaR9R8A5VX3b;R2R1A5R7A3Ftp;Fr;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HW HUS HKc HCb r tp.
  pose proof (JGs_stable nW st tmax nx Hnx NXG AX A Kc rho a HUS HKc) as HST.
  apply (etc_pre (SPA segs (JG AX A Kc rho a) CO3b (rho_sub r sLb) tp));
    [intros w Hw; exact (carve_w' A Kc rho a _ tp w HW (gen_x11 nW st tmax nx Hnx NXG AX A Kc rho a X3b L3b sLb r tp w HUS HKc ELb IDb GLb FBLb HL3b Hw))|].
  apply (ecfg_2 [0x3c614] CO3b Y4b0 Y4b1 (JG AX A Kc rho a) Q tp _ HST NXECOb ECert4b); intros rE.
  - apply (etc_pre (SPA segs (JG AX A Kc rho a) T4b (rho_sub rE s4b0) tp)); [intros w Hw; exact (join4 nW st tmax nx Hnx NXG AX A Kc rho a Y4b0 T4b s4b0 rE tp w HUS HKc E4b0 I4b0 Hw) | apply HCb].
  - apply (etc_pre (SPA segs (JG AX A Kc rho a) T4b (rho_sub rE s4b1) tp)); [intros w Hw; exact (join4 nW st tmax nx Hnx NXG AX A Kc rho a Y4b1 T4b s4b1 rE tp w HUS HKc E4b1 I4b1 Hw) | apply HCb].
Qed.

Lemma epath_a : ltac2:(tb__ "0|6|
S3dS4fS1cS3bQ40M0A1M1S4dOF_;S57VW;Vst;A2S64VW;Vst;A2S50R6A1S45S44S47S14S40S3eR8A1A2A1Z1A2S48Z2Z14A2A2S1aS1S46S72S3aG0R7A2A1M2R1A2S45R1S44G2S49S63S3aG0S24R8PcM3A2A2A1Z8A2A2A2A2S2S0S13S3bQ8A1M4A1S29R9S3cG0R2A2A2S15G4A1A3A1F_;Fz;S1cS1cSfG1A1M5S73S3fRdA1S3aG0RaA2S63S3aG0S24RbG3A2A2A1RbR3A5S4cVsegs;S37Vsegs;VJG;VAXP;ReRdR4RbA5VT4a;R3R2A5RaA3F_;FtY;FrY;Frho'';S1cG5S4cVsegs;S37Vsegs;VJG;VAX;RdRcRbRaA5VX3a;R2R1A5R9A3Ftp;Fr;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HW HUS HKc Hok RUNDEF HCa r tp.
  pose proof (JGs_stable nW st tmax nx Hnx NXG AX A Kc rho a HUS HKc) as HST.
  apply (etc_pre (SPA segs (JG AX A Kc rho a) CS3 r tp)); [intros w Hw; exact (RS3' A Kc rho a r tp w Hw)|].
  assert (HST' : stableA segs (ss_next (ax_S CS3)) (JG AX A Kc rho a)).
  { eapply stableA_mono; [|exact HST]. apply Pos.leb_le. exact NXS3. }
  eapply etriple_seq.
  { apply (etriple_fixed_commitA segs (JG AX A Kc rho a) (JGo A Kc rho a) CS3 r tp Bw 131072 HST' IC3 R17 R10 BBw R11 R12 R13 R14 R15 eq_refl ltac:(lia)).
    exact (ens_oblig' A Kc rho a r tp HW HKc Hok). }
  fold O_blk. rewrite HG3.
  apply (etc_pre (fun w => exists r2 rho'', slink4 (aa_geom A) (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho'' /\ SPA segs (JG AXP A Kc rho'' a) G3 r2 tp w));
    [intros w Hw; destruct w as [tr [ms md]]; exact (ensure_post' A Kc rho a r tp tr ms md HW RUNDEF Hw)|].
  apply etriple_ex; intros r2. apply etriple_ex; intros rho''.
  apply (etriple_pre_pure segs _ _ (slink4 (aa_geom A) (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho'')); [intros w [SL _]; exact SL|]. intros SL.
  apply (etc_pre (SPA segs (JG AXP A Kc rho'' a) G3 r2 tp)); [intros w [_ Hw]; exact Hw|].
  pose proof (JGs_stable nW st tmax nx Hnx NXG AXP A Kc rho'' a HUS HKc) as HST2.
  apply (ecfg_1 nx [0x410f0] G3 X3a3 (JG AXP A Kc rho'' a) Q tp r2 HST2 NXEG3 ECert3a). intros rE.
  apply (etc_pre (SPA segs (JG AXP A Kc rho'' a) L3a (rho_sub rE sLa) tp));
    [intros w Hw; exact (gen_x11 nW st tmax nx Hnx NXG AXP A Kc rho'' a X3a3 L3a sLa rE tp w HUS HKc ELa IDa GLa FBLa HL3a Hw)|].
  apply (ecfg_2 [0x3c614] L3a Y4a0 Y4a1 (JG AXP A Kc rho'' a) Q tp _ HST2 NXEL3a ECert4a); intros rE'.
  - apply (etc_pre (SPA segs (JG AXP A Kc rho'' a) T4a (rho_sub rE' s4a0) tp)); [intros w Hw; exact (join4 nW st tmax nx Hnx NXG AXP A Kc rho'' a Y4a0 T4a s4a0 rE' tp w HUS HKc E4a0 I4a0 Hw) | apply HCa; exact SL].
  - apply (etc_pre (SPA segs (JG AXP A Kc rho'' a) T4a (rho_sub rE' s4a1) tp)); [intros w Hw; exact (join4 nW st tmax nx Hnx NXG AXP A Kc rho'' a Y4a1 T4a s4a1 rE' tp w HUS HKc E4a1 I4a1 Hw) | apply HCa; exact SL].
Qed.

Theorem esec_g3 : ltac2:(tb__ "0|6|
S3dS4fS1cS3bQ40M0A1M1S4dOF_;S57VW;Vst;A2S64VW;Vst;A2S50R6A1S45S44S47S14S40S3eR8A1A2A1Z1A2S48Z2Z14A2A2S1aS1S46S72S3aG0R7A2A1M2R1A2S45R1S44G2S49S63S3aG0S24R8PcM3A2A2A1Z8A2A2A2A2S2S0S13S3bQ8A1M4A1S29R9S3cG0R2A2A2S15G4A1A3A1F_;Fz;S1cS1cSfG1A1M5S73S3fRdA1S3aG0RaA2S63S3aG0S24RbG3A2A2A1RbR3A5S4cVsegs;S37Vsegs;VJG;VAXP;ReRdR4RbA5VT4a;R3R2A5RaA3F_;FtY;FrY;Frho'';S1cG5S4cVsegs;S37Vsegs;VJG;VAX;RdRcRbRaA5VT4b;R2R1A5R9A3FtY;FrY;S1cG5S4cVsegs;S37Vsegs;VJG;VAX;ReRdRcRbA5VD2;R2R1A5RaA3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  assert (USED := (WU2, DU2, NXU2, HU2, Cert3, WC3, DC3, NXC3, HC3, FX3a, IC3, R17, R10, BBw, R11, R12, R13, R14, R15, XC3, SK3, FC3, FCS3, NXS3, HG3, Cert3a, ELa, IDa, GLa, FBLa, HL3a, ELb, IDb, GLb, FBLb, HL3b, HCOb, WCOb, XCb, SKb, FCb, FXb, Cert4a, E4a0, I4a0, E4a1, I4a1, Cert4b, E4b0, I4b0, E4b1, I4b1, NXEU2, NXEG3, NXEL3a, NXECOb, ECert3, ECert3a, ECert4a, ECert4b)); clear USED.
  intros A Kc rho a Q HW HUS HKc Hok RUNDEF HCa HCb rX tX.
  pose proof (JGs_stable nW st tmax nx Hnx NXG AX A Kc rho a HUS HKc) as HST.
  apply (etc_pre (SPA segs (JG AX A Kc rho a) U2 rX tX)); [intros w Hw; exact (RSU' A Kc rho a rX tX w Hok Hw)|].
  apply (ecfg_2 [0x706a0; 0x410f0] U2 X3a X3b (JG AX A Kc rho a) Q tX rX HST NXEU2 ECert3); intros rE.
  - exact (epath_a A Kc rho a Q HW HUS HKc Hok RUNDEF HCa rE tX).
  - exact (epath_b A Kc rho a Q HW HUS HKc HCb rE tX).
Qed.
End G3E.
End SEC4E.
End SpineCallocSecE2.

(* [comment removed for export] *)
Module SpineMallocSec5IW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "entailsA"; "leafA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS"; "X5s"; "WI"; "T5d"; "X5r"; "permS"; "T50"; "T5a"; "T5b"; "T5c"; "T5m1"; "T5m2"; "T5m3"; "X5a"; "X5b"; "X5c"; "X5f"; "C5S"; "coveredbL"; "in_fambS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineMallocSec5IW2.INST"; "X5ac"; "X5bc"; "T4a_i"; "T4b_i"; "nobja"; "nobjb"; "U4ac"; "U4bc"; "s4a_i"; "s4b_i"; "R4a_i"; "R4b_i"; "pm__29"; "pm__30"; "pm__31"; "pm__32"; "pm__83"; "pm__84"; "pm__85"; "pm__86"; "C5ac"; "C5bc"; "pm__100"; "pm__101"; "pm__102"; "pm__17"; "pm__18"; "pm__19"; "pm__20"; "pm__21"; "pm__22"; "pm__23"; "pm__24"; "pm__25"; "pm__26"; "pm__27"; "pm__28"; "pm__33"; "pm__34"; "pm__35"; "pm__36"; "pm__37"; "pm__38"; "pm__39"; "pm__40"; "pm__41"; "pm__42"; "pm__43"; "pm__44"; "pm__45"; "pm__46"; "pm__47"; "pm__48"; "pm__71"; "pm__72"; "pm__73"; "pm__74"; "pm__75"; "pm__76"; "pm__77"; "pm__78"; "pm__79"; "pm__80"; "pm__81"; "pm__82"; "pm__87"; "pm__88"; "pm__89"; "pm__90"; "pm__91"; "pm__92"; "pm__93"; "pm__94"; "pm__95"; "pm__96"; "pm__97"; "pm__98"; "pm__99"; "sda_i"; "sdb_i"; "CPa1"; "CPa2"; "CPb1"; "CPb2"; "EXoa"; "EXob"; "pm__0"; "pm__1"; "pm__10"; "pm__103"; "pm__104"; "pm__105"; "pm__106"; "pm__107"; "pm__11"; "pm__12"; "pm__13"; "pm__14"; "pm__15"; "pm__16"; "pm__2"; "pm__3"; "pm__4"; "pm__49"; "pm__5"; "pm__50"; "pm__51"; "pm__52"; "pm__53"; "pm__54"; "pm__55"; "pm__56"; "pm__57"; "pm__58"; "pm__59"; "pm__6"; "pm__60"; "pm__61"; "pm__62"; "pm__63"; "pm__64"; "pm__65"; "pm__66"; "pm__67"; "pm__68"; "pm__69"; "pm__7"; "pm__70"; "pm__8"; "pm__9"; "run5a"; "run5b"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "cons"; "list"; "prod"; "S"; "nat"; "option"; "pair"; "Some"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "omrg"; "oreb"; "F_call"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "ss_facts"; "SLit"; "sstate"; "ss_next"; "SVar"; "ss_objs"; "sprop_below"; "SAlu"; "SPUle"; "swf"; "SExt"; "SPBranch"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST"; "isSome"; "O_1"; "O_2"; "O_blk"; "O_w"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IW2"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "wsub_id_below"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3";
"state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU"; "DPENT"; "F_g4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4IW2"; "T4ac"; "T4bc"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "V_NCH"; "V_NRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4IW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSec6.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

Lemma by_cases12 : ltac2:(tb__ "0|2|
Sa1OF_;R1Z1M0A1R2Z2A1R3Z3A1R4Z4M1A1Sa1S1S8G0R1A2S8R1G1A2A2R7R2A1F_;Fsz;F_;F_;F_;F_;FP;").
Proof. intros P H1 H2 H3 H4 sz Hsz. assert (E : sz = 1 \/ sz = 2 \/ sz = 3 \/ sz = 4) by lia. destruct E as [-> | [-> | [-> | ->]]]; assumption. Qed.
Definition gP (o : option (wsub * list sobj * axst)) : wsub * list sobj * axst := ltac2:(tb__ "0|4|
SabSa8Sa8Sd7Sa7Sb5A1M0A2S2A2M1A1G1Lo;Vo;G1R1Lx;SacSa8Sa7Sa8Sa2Sb3A2M2A1M3G0A2S2SacG3G0Sa5G2A1Sa5Sb5A1A4SccZ0A1A4Xabx2").
Lemma Htmax_0 : 1 <= tmax <= SZMAX.
Proof. unfold SZMAX. subst tmax. lia. Qed.

Definition U4ac : axst := Eval vm_compute in (U4p nx0 T4ac).
Lemma WU4a_0 : ltac2:(tb__ "0|0|
S0Sa3SbfS3S23A1A1Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DU4a_0 : ltac2:(tb__ "0|4|
S0SabSa8Sa7Sa8Sb3Sb3A2M0A1M1Sa7Sb4A1M2A2M3A1SdbS3SdfA1S3S23A1A2SadG3SacG1G2Sa5G0A1SddSd5A1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXU4a_0 : ltac2:(tb__ "0|0|
S0Sa2Sb9S3S23A1A1Sb9S3SdfA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HU4a_0 : ltac2:(tb__ "0|0|
S0S2S4SdfS3S23A1A2S23A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run5a : option (list leafA) := Eval vm_compute in (runT5 U4ac).
Lemma run5a__runeq : ltac2:(tb__ "0|1|
S0Sa7SabSa7S7A1A1M0A1Se5SdeUfa0Sa6Sa1SdcSa5Sa1A1A3Sa6S2S23Sa5S2A1A3A4Sa6G0S9fSa5G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run5a]). Qed.
Definition X5ac : axst := Eval vm_compute in (leafS 0 run5a).
Lemma Cert5a_0 : ltac2:(tb__ "0|1|
S0Sa3Se4SdeUfa0Sa6Sa1SdcSa5Sa1A1A3VGS0;Sa6S2S23Sa5S2A1M0A3Sa6S2S1dG0A3A6Sa4A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [DPENT] GS0 [U4ac] [X5ac] [run5a]); [exact run5a__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition C5ac : axst := Eval vm_compute in (C5S X5ac).

Definition CPa1 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5ac 1) 1)).
Definition CPa2 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5ac 2) 2)).
Definition CPa (sz : Z) : wsub * list sobj * axst := ltac2:(tb__ "0|0|
Sa3Sa8Sa8Sd7Sa7Sb5A1A2S2A2L_;S9Vsz;Z1A2S6dS6eXa3x2").
Definition s4a_i (sz : Z) : wsub := fst (fst (CPa sz)).
Definition R4a_i (sz : Z) : list sobj := snd (fst (CPa sz)).
Definition T4a_i (sz : Z) : axst := snd (CPa sz).
Definition nobja : nat := Eval vm_compute in (length (ss_objs (ax_S (T5b (T4a_i 1) (X5s X5ac 1))))).
Definition sda_i (sz : Z) : wsub := ltac2:(tb__ "0|0|
Se2VGS0;S3ScS21S1fVsz;A1SaS1dVsz;A2A3A1S3S31A1A3").
Definition EXoa : list sobj := ltac2:(tb__ "0|0|
Sa6Sb5Sc5Sd5A1Sa6Sb5Sc4Sd5A1Sa6Sb5Sc6Sa5Sb5A1A3A3A3").

Lemma NXEa_0 : ltac2:(tb__ "0|0|
S0Sa3Sf0VGS0;Sb9S3S1dA1A1A2Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBEa_0 : ltac2:(tb__ "0|0|
S0Sa3Sc8Sb4SbcSb9S3S1dA1A1A1Sb2A3Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XE5a_0 : ax_X X5ac = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F192a_0 : ltac2:(tb__ "0|1|
Sc9Sb4Sa6Sb4SbeSb7Z1A1SbaPc0A1M0A2Sa6Sb4SbeG0Sb7Vtmax;A1A2Sa5Sb4A1A3A3Sb6S3S1dA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FDEPa_0 : ltac2:(tb__ "0|0|
Sc9Sb4SecSebA1Sb6S3S1dA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FUNWa_0 : ltac2:(tb__ "0|0|
Sc9Sb4SedVW;Vst;A2Sb6S3S1dA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FXBa_0 : ltac2:(tb__ "0|0|
ScaSb4Sc1SdaSbaSe9A1SbaSeaA1A3Sb6S3S1dA1A1A3"). Proof. apply In_of_inclb. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Ltac PM_sub0 t := t.
Ltac PM_all0 := idtac.
Definition pm__0 : axst := ltac:(let t := eval cbv delta [X5f] in (X5f X5ac) in let t := eval cbv beta zeta in t in let t := PM_sub0 t in exact t).
Lemma pm__0_eq : ltac2:(tb__ "0|0|
S0S2S19S1dA1S73A3"). Proof. cbv delta [X5f pm__0]; cbv beta zeta. PM_all0. reflexivity. Qed.
Ltac PM_sub1 t := let t := lazymatch (eval pattern (X5f X5ac) in t) with ?P _ => eval cbv beta in (P pm__0) end in PM_sub0 t.
Ltac PM_all1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__0_eq; PM_all0.
Definition pm__1 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub1 t in exact t).
Lemma pm__1_eq : ltac2:(tb__ "0|0|
S0S2SdS1dZ1A2S74A3"). Proof. cbv delta [X5r pm__1]; cbv beta zeta. PM_all1. reflexivity. Qed.
Ltac PM_sub2 t := let t := lazymatch (eval pattern (X5r X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__1) end in PM_sub1 t.
Ltac PM_all2 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__1_eq; PM_all1.
Definition pm__2 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub2 t in exact t).
Lemma pm__2_eq : ltac2:(tb__ "0|0|
S0S2SdS1dZ2A2S81A3"). Proof. cbv delta [X5r pm__2]; cbv beta zeta. PM_all2. reflexivity. Qed.
Ltac PM_sub3 t := let t := lazymatch (eval pattern (X5r X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__2) end in PM_sub2 t.
Ltac PM_all3 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__2_eq; PM_all2.
Definition pm__3 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5ac 3) in let t := eval cbv beta zeta in t in let t := PM_sub3 t in exact t).
Lemma pm__3_eq : ltac2:(tb__ "0|0|
S0S2SdS1dZ3A2S82A3"). Proof. cbv delta [X5r pm__3]; cbv beta zeta. PM_all3. reflexivity. Qed.
Ltac PM_sub4 t := let t := lazymatch (eval pattern (X5r X5ac 3) in t) with ?P _ => eval cbv beta in (P pm__3) end in PM_sub3 t.
Ltac PM_all4 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__3_eq; PM_all3.
Definition pm__4 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5ac 4) in let t := eval cbv beta zeta in t in let t := PM_sub4 t in exact t).
Lemma pm__4_eq : ltac2:(tb__ "0|0|
S0S2SdS1dZ4A2S83A3"). Proof. cbv delta [X5r pm__4]; cbv beta zeta. PM_all4. reflexivity. Qed.
Ltac PM_sub5 t := let t := lazymatch (eval pattern (X5r X5ac 4) in t) with ?P _ => eval cbv beta in (P pm__4) end in PM_sub4 t.
Ltac PM_all5 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__4_eq; PM_all4.
Definition pm__5 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub5 t in exact t).
Lemma pm__5_eq : ltac2:(tb__ "0|0|
S0S2S16S1dZ1A2S85A3"). Proof. cbv delta [X5a pm__5]; cbv beta zeta. PM_all5. reflexivity. Qed.
Ltac PM_sub6 t := let t := lazymatch (eval pattern (X5a X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__5) end in PM_sub5 t.
Ltac PM_all6 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__5_eq; PM_all5.
Definition pm__6 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub6 t in exact t).
Lemma pm__6_eq : ltac2:(tb__ "0|0|
S0S2S16S1dZ2A2S90A3"). Proof. cbv delta [X5a pm__6]; cbv beta zeta. PM_all6. reflexivity. Qed.
Ltac PM_sub7 t := let t := lazymatch (eval pattern (X5a X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__6) end in PM_sub6 t.
Ltac PM_all7 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__6_eq; PM_all6.
Definition pm__7 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5ac 3) in let t := eval cbv beta zeta in t in let t := PM_sub7 t in exact t).
Lemma pm__7_eq : ltac2:(tb__ "0|0|
S0S2S16S1dZ3A2S9bA3"). Proof. cbv delta [X5a pm__7]; cbv beta zeta. PM_all7. reflexivity. Qed.
Ltac PM_sub8 t := let t := lazymatch (eval pattern (X5a X5ac 3) in t) with ?P _ => eval cbv beta in (P pm__7) end in PM_sub7 t.
Ltac PM_all8 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__7_eq; PM_all7.
Definition pm__8 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5ac 4) in let t := eval cbv beta zeta in t in let t := PM_sub8 t in exact t).
Lemma pm__8_eq : ltac2:(tb__ "0|0|
S0S2S16S1dZ4A2S9dA3"). Proof. cbv delta [X5a pm__8]; cbv beta zeta. PM_all8. reflexivity. Qed.
Ltac PM_sub9 t := let t := lazymatch (eval pattern (X5a X5ac 4) in t) with ?P _ => eval cbv beta in (P pm__8) end in PM_sub8 t.
Ltac PM_all9 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__8_eq; PM_all8.
Definition pm__9 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub9 t in exact t).
Lemma pm__9_eq : ltac2:(tb__ "0|0|
S0S2S17S1dZ1A2S9eA3"). Proof. cbv delta [X5b pm__9]; cbv beta zeta. PM_all9. reflexivity. Qed.
Ltac PM_sub10 t := let t := lazymatch (eval pattern (X5b X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__9) end in PM_sub9 t.
Ltac PM_all10 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__9_eq; PM_all9.
Definition pm__10 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub10 t in exact t).
Lemma pm__10_eq : ltac2:(tb__ "0|0|
S0S2S17S1dZ2A2S75A3"). Proof. cbv delta [X5b pm__10]; cbv beta zeta. PM_all10. reflexivity. Qed.
Ltac PM_sub11 t := let t := lazymatch (eval pattern (X5b X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__10) end in PM_sub10 t.
Ltac PM_all11 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__10_eq; PM_all10.
Definition pm__11 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5ac 3) in let t := eval cbv beta zeta in t in let t := PM_sub11 t in exact t).
Lemma pm__11_eq : ltac2:(tb__ "0|0|
S0S2S17S1dZ3A2S7bA3"). Proof. cbv delta [X5b pm__11]; cbv beta zeta. PM_all11. reflexivity. Qed.
Ltac PM_sub12 t := let t := lazymatch (eval pattern (X5b X5ac 3) in t) with ?P _ => eval cbv beta in (P pm__11) end in PM_sub11 t.
Ltac PM_all12 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__11_eq; PM_all11.
Definition pm__12 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5ac 4) in let t := eval cbv beta zeta in t in let t := PM_sub12 t in exact t).
Lemma pm__12_eq : ltac2:(tb__ "0|0|
S0S2S17S1dZ4A2S7cA3"). Proof. cbv delta [X5b pm__12]; cbv beta zeta. PM_all12. reflexivity. Qed.
Ltac PM_sub13 t := let t := lazymatch (eval pattern (X5b X5ac 4) in t) with ?P _ => eval cbv beta in (P pm__12) end in PM_sub12 t.
Ltac PM_all13 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__12_eq; PM_all12.
Definition pm__13 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub13 t in exact t).
Lemma pm__13_eq : ltac2:(tb__ "0|0|
S0S2S18S1dZ1A2S7dA3"). Proof. cbv delta [X5c pm__13]; cbv beta zeta. PM_all13. reflexivity. Qed.
Ltac PM_sub14 t := let t := lazymatch (eval pattern (X5c X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__13) end in PM_sub13 t.
Ltac PM_all14 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__13_eq; PM_all13.
Definition pm__14 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub14 t in exact t).
Lemma pm__14_eq : ltac2:(tb__ "0|0|
S0S2S18S1dZ2A2S7eA3"). Proof. cbv delta [X5c pm__14]; cbv beta zeta. PM_all14. reflexivity. Qed.
Ltac PM_sub15 t := let t := lazymatch (eval pattern (X5c X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__14) end in PM_sub14 t.
Ltac PM_all15 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__14_eq; PM_all14.
Definition pm__15 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5ac 3) in let t := eval cbv beta zeta in t in let t := PM_sub15 t in exact t).
Lemma pm__15_eq : ltac2:(tb__ "0|0|
S0S2S18S1dZ3A2S7fA3"). Proof. cbv delta [X5c pm__15]; cbv beta zeta. PM_all15. reflexivity. Qed.
Ltac PM_sub16 t := let t := lazymatch (eval pattern (X5c X5ac 3) in t) with ?P _ => eval cbv beta in (P pm__15) end in PM_sub15 t.
Ltac PM_all16 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__15_eq; PM_all15.
Definition pm__16 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5ac 4) in let t := eval cbv beta zeta in t in let t := PM_sub16 t in exact t).
Lemma pm__16_eq : ltac2:(tb__ "0|0|
S0S2S18S1dZ4A2S80A3"). Proof. cbv delta [X5c pm__16]; cbv beta zeta. PM_all16. reflexivity. Qed.
Ltac PM_sub17 t := let t := lazymatch (eval pattern (X5c X5ac 4) in t) with ?P _ => eval cbv beta in (P pm__16) end in PM_sub16 t.
Ltac PM_all17 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__16_eq; PM_all16.
Definition pm__17 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub17 t in exact t).
Lemma pm__17_eq : ltac2:(tb__ "0|0|
S0S2SaS1dZ1A2S36A3"). Proof. cbv delta [X5s pm__17]; cbv beta zeta. PM_all17. reflexivity. Qed.
Ltac PM_sub18 t := let t := lazymatch (eval pattern (X5s X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__17) end in PM_sub17 t.
Ltac PM_all18 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__17_eq; PM_all17.
Definition pm__18 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub18 t in exact t).
Lemma pm__18_eq : ltac2:(tb__ "0|0|
S0S2SaS1dZ2A2S37A3"). Proof. cbv delta [X5s pm__18]; cbv beta zeta. PM_all18. reflexivity. Qed.
Ltac PM_sub19 t := let t := lazymatch (eval pattern (X5s X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__18) end in PM_sub18 t.
Ltac PM_all19 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__18_eq; PM_all18.
Definition pm__19 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5ac 3) in let t := eval cbv beta zeta in t in let t := PM_sub19 t in exact t).
Lemma pm__19_eq : ltac2:(tb__ "0|0|
S0S2SaS1dZ3A2S38A3"). Proof. cbv delta [X5s pm__19]; cbv beta zeta. PM_all19. reflexivity. Qed.
Ltac PM_sub20 t := let t := lazymatch (eval pattern (X5s X5ac 3) in t) with ?P _ => eval cbv beta in (P pm__19) end in PM_sub19 t.
Ltac PM_all20 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__19_eq; PM_all19.
Definition pm__20 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5ac 4) in let t := eval cbv beta zeta in t in let t := PM_sub20 t in exact t).
Lemma pm__20_eq : ltac2:(tb__ "0|0|
S0S2SaS1dZ4A2S39A3"). Proof. cbv delta [X5s pm__20]; cbv beta zeta. PM_all20. reflexivity. Qed.
Ltac PM_sub21 t := let t := lazymatch (eval pattern (X5s X5ac 4) in t) with ?P _ => eval cbv beta in (P pm__20) end in PM_sub20 t.
Ltac PM_all21 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__20_eq; PM_all20.
Definition pm__21 : axst := ltac2:(tb__ "0|0|
Sd4S1fZ1A1Sb6S3S36A1A1A2").
Lemma pm__21_eq : ltac2:(tb__ "0|1|
S0S2SfS1fZ1M0A1SaS1dG0A2A2S3aA3"). Proof. cbv delta [T50 pm__21]; cbv beta zeta. PM_all21. reflexivity. Qed.
Ltac PM_sub22 t := let t := lazymatch (eval pattern (T50 (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__21) end in PM_sub21 t.
Ltac PM_all22 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__21_eq; PM_all21.
Definition pm__22 : axst := ltac2:(tb__ "0|0|
Sd4S1fZ2A1Sb6S3S37A1A1A2").
Lemma pm__22_eq : ltac2:(tb__ "0|1|
S0S2SfS1fZ2M0A1SaS1dG0A2A2S3bA3"). Proof. cbv delta [T50 pm__22]; cbv beta zeta. PM_all22. reflexivity. Qed.
Ltac PM_sub23 t := let t := lazymatch (eval pattern (T50 (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__22) end in PM_sub22 t.
Ltac PM_all23 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__22_eq; PM_all22.
Definition pm__23 : axst := ltac2:(tb__ "0|0|
Sd4S1fZ3A1Sb6S3S38A1A1A2").
Lemma pm__23_eq : ltac2:(tb__ "0|1|
S0S2SfS1fZ3M0A1SaS1dG0A2A2S3cA3"). Proof. cbv delta [T50 pm__23]; cbv beta zeta. PM_all23. reflexivity. Qed.
Ltac PM_sub24 t := let t := lazymatch (eval pattern (T50 (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__23) end in PM_sub23 t.
Ltac PM_all24 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__23_eq; PM_all23.
Definition pm__24 : axst := ltac2:(tb__ "0|0|
Sd4S1fZ4A1Sb6S3S39A1A1A2").
Lemma pm__24_eq : ltac2:(tb__ "0|1|
S0S2SfS1fZ4M0A1SaS1dG0A2A2S3dA3"). Proof. cbv delta [T50 pm__24]; cbv beta zeta. PM_all24. reflexivity. Qed.
Ltac PM_sub25 t := let t := lazymatch (eval pattern (T50 (T4a_i 4) (X5s X5ac 4)) in t) with ?P _ => eval cbv beta in (P pm__24) end in PM_sub24 t.
Ltac PM_all25 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__24_eq; PM_all24.
Definition pm__25 : axst := ltac2:(tb__ "0|0|
Sb1S3aU0A2").
Lemma pm__25_eq : ltac2:(tb__ "0|1|
S0S2S10S1fZ1M0A1SaS1dG0A2A2S3eA3"). Proof. cbv delta [T5a pm__25]; cbv beta zeta. PM_all25. reflexivity. Qed.
Ltac PM_sub26 t := let t := lazymatch (eval pattern (T5a (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__25) end in PM_sub25 t.
Ltac PM_all26 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__25_eq; PM_all25.
Definition pm__26 : axst := ltac2:(tb__ "0|0|
Sb1S3bU0A2").
Lemma pm__26_eq : ltac2:(tb__ "0|1|
S0S2S10S1fZ2M0A1SaS1dG0A2A2S3fA3"). Proof. cbv delta [T5a pm__26]; cbv beta zeta. PM_all26. reflexivity. Qed.
Ltac PM_sub27 t := let t := lazymatch (eval pattern (T5a (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__26) end in PM_sub26 t.
Ltac PM_all27 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__26_eq; PM_all26.
Definition pm__27 : axst := ltac2:(tb__ "0|0|
Sb1S3cU0A2").
Lemma pm__27_eq : ltac2:(tb__ "0|1|
S0S2S10S1fZ3M0A1SaS1dG0A2A2S40A3"). Proof. cbv delta [T5a pm__27]; cbv beta zeta. PM_all27. reflexivity. Qed.
Ltac PM_sub28 t := let t := lazymatch (eval pattern (T5a (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__27) end in PM_sub27 t.
Ltac PM_all28 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__27_eq; PM_all27.
Definition pm__28 : axst := ltac2:(tb__ "0|0|
Sb1S3dU0A2").
Lemma pm__28_eq : ltac2:(tb__ "0|1|
S0S2S10S1fZ4M0A1SaS1dG0A2A2S41A3"). Proof. cbv delta [T5a pm__28]; cbv beta zeta. PM_all28. reflexivity. Qed.
Ltac PM_sub29 t := let t := lazymatch (eval pattern (T5a (T4a_i 4) (X5s X5ac 4)) in t) with ?P _ => eval cbv beta in (P pm__28) end in PM_sub28 t.
Ltac PM_all29 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__28_eq; PM_all28.
Definition pm__29 : axst := ltac2:(tb__ "0|0|
Sb1S3eU1A2").
Lemma pm__29_eq : ltac2:(tb__ "0|1|
S0S2S11S1fZ1M0A1SaS1dG0A2A2S29A3"). Proof. cbv delta [T5b pm__29]; cbv beta zeta. PM_all29. reflexivity. Qed.
Ltac PM_sub30 t := let t := lazymatch (eval pattern (T5b (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__29) end in PM_sub29 t.
Ltac PM_all30 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__29_eq; PM_all29.
Definition pm__30 : axst := ltac2:(tb__ "0|0|
Sb1S3fU1A2").
Lemma pm__30_eq : ltac2:(tb__ "0|1|
S0S2S11S1fZ2M0A1SaS1dG0A2A2S2aA3"). Proof. cbv delta [T5b pm__30]; cbv beta zeta. PM_all30. reflexivity. Qed.
Ltac PM_sub31 t := let t := lazymatch (eval pattern (T5b (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__30) end in PM_sub30 t.
Ltac PM_all31 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__30_eq; PM_all30.
Definition pm__31 : axst := ltac2:(tb__ "0|0|
Sb1S40U1A2").
Lemma pm__31_eq : ltac2:(tb__ "0|1|
S0S2S11S1fZ3M0A1SaS1dG0A2A2S2bA3"). Proof. cbv delta [T5b pm__31]; cbv beta zeta. PM_all31. reflexivity. Qed.
Ltac PM_sub32 t := let t := lazymatch (eval pattern (T5b (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__31) end in PM_sub31 t.
Ltac PM_all32 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__31_eq; PM_all31.
Definition pm__32 : axst := ltac2:(tb__ "0|0|
Sb1S41U1A2").
Lemma pm__32_eq : ltac2:(tb__ "0|1|
S0S2S11S1fZ4M0A1SaS1dG0A2A2S2cA3"). Proof. cbv delta [T5b pm__32]; cbv beta zeta. PM_all32. reflexivity. Qed.
Ltac PM_sub33 t := let t := lazymatch (eval pattern (T5b (T4a_i 4) (X5s X5ac 4)) in t) with ?P _ => eval cbv beta in (P pm__32) end in PM_sub32 t.
Ltac PM_all33 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__32_eq; PM_all32.
Definition pm__33 : axst := ltac2:(tb__ "0|1|
S4S29Sd3S3S29A1M0SceSbbG0A1SeS21A1A2A2A2").
Lemma pm__33_eq : ltac2:(tb__ "0|1|
S0S2S12S21S1fZ1M0A1SaS1dG0A2A3S42A3"). Proof. cbv delta [T5c pm__33]; cbv beta zeta. PM_all33. reflexivity. Qed.
Ltac PM_sub34 t := let t := lazymatch (eval pattern (T5c nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__33) end in PM_sub33 t.
Ltac PM_all34 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__33_eq; PM_all33.
Definition pm__34 : axst := ltac2:(tb__ "0|1|
S4S2aSd3S3S2aA1M0SceSbbG0A1SeS21A1A2A2A2").
Lemma pm__34_eq : ltac2:(tb__ "0|1|
S0S2S12S21S1fZ2M0A1SaS1dG0A2A3S43A3"). Proof. cbv delta [T5c pm__34]; cbv beta zeta. PM_all34. reflexivity. Qed.
Ltac PM_sub35 t := let t := lazymatch (eval pattern (T5c nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__34) end in PM_sub34 t.
Ltac PM_all35 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__34_eq; PM_all34.
Definition pm__35 : axst := ltac2:(tb__ "0|1|
S4S2bSd3S3S2bA1M0SceSbbG0A1SeS21A1A2A2A2").
Lemma pm__35_eq : ltac2:(tb__ "0|1|
S0S2S12S21S1fZ3M0A1SaS1dG0A2A3S44A3"). Proof. cbv delta [T5c pm__35]; cbv beta zeta. PM_all35. reflexivity. Qed.
Ltac PM_sub36 t := let t := lazymatch (eval pattern (T5c nobja (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__35) end in PM_sub35 t.
Ltac PM_all36 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__35_eq; PM_all35.
Definition pm__36 : axst := ltac2:(tb__ "0|1|
S4S2cSd3S3S2cA1M0SceSbbG0A1SeS21A1A2A2A2").
Lemma pm__36_eq : ltac2:(tb__ "0|1|
S0S2S12S21S1fZ4M0A1SaS1dG0A2A3S45A3"). Proof. cbv delta [T5c pm__36]; cbv beta zeta. PM_all36. reflexivity. Qed.
Ltac PM_sub37 t := let t := lazymatch (eval pattern (T5c nobja (T4a_i 4) (X5s X5ac 4)) in t) with ?P _ => eval cbv beta in (P pm__36) end in PM_sub36 t.
Ltac PM_all37 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__36_eq; PM_all36.
Definition pm__37 : axst := ltac2:(tb__ "0|0|
Sb0S42SbA2").
Lemma pm__37_eq : ltac2:(tb__ "0|1|
S0S2S13S21S1fZ1M0A1SaS1dG0A2A3S46A3"). Proof. cbv delta [T5m1 pm__37]; cbv beta zeta. PM_all37. reflexivity. Qed.
Ltac PM_sub38 t := let t := lazymatch (eval pattern (T5m1 nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__37) end in PM_sub37 t.
Ltac PM_all38 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__37_eq; PM_all37.
Definition pm__38 : axst := ltac2:(tb__ "0|0|
Sb0S43SbA2").
Lemma pm__38_eq : ltac2:(tb__ "0|1|
S0S2S13S21S1fZ2M0A1SaS1dG0A2A3S47A3"). Proof. cbv delta [T5m1 pm__38]; cbv beta zeta. PM_all38. reflexivity. Qed.
Ltac PM_sub39 t := let t := lazymatch (eval pattern (T5m1 nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__38) end in PM_sub38 t.
Ltac PM_all39 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__38_eq; PM_all38.
Definition pm__39 : axst := ltac2:(tb__ "0|0|
Sb0S44SbA2").
Lemma pm__39_eq : ltac2:(tb__ "0|1|
S0S2S13S21S1fZ3M0A1SaS1dG0A2A3S48A3"). Proof. cbv delta [T5m1 pm__39]; cbv beta zeta. PM_all39. reflexivity. Qed.
Ltac PM_sub40 t := let t := lazymatch (eval pattern (T5m1 nobja (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__39) end in PM_sub39 t.
Ltac PM_all40 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__39_eq; PM_all39.
Definition pm__40 : axst := ltac2:(tb__ "0|0|
Sb0S45SbA2").
Lemma pm__40_eq : ltac2:(tb__ "0|1|
S0S2S13S21S1fZ4M0A1SaS1dG0A2A3S49A3"). Proof. cbv delta [T5m1 pm__40]; cbv beta zeta. PM_all40. reflexivity. Qed.
Ltac PM_sub41 t := let t := lazymatch (eval pattern (T5m1 nobja (T4a_i 4) (X5s X5ac 4)) in t) with ?P _ => eval cbv beta in (P pm__40) end in PM_sub40 t.
Ltac PM_all41 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__40_eq; PM_all40.
Definition pm__41 : axst := ltac2:(tb__ "0|0|
Sb0S46SbA2").
Lemma pm__41_eq : ltac2:(tb__ "0|1|
S0S2S14S21S1fZ1M0A1SaS1dG0A2A3S4aA3"). Proof. cbv delta [T5m2 pm__41]; cbv beta zeta. PM_all41. reflexivity. Qed.
Ltac PM_sub42 t := let t := lazymatch (eval pattern (T5m2 nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__41) end in PM_sub41 t.
Ltac PM_all42 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__41_eq; PM_all41.
Definition pm__42 : axst := ltac2:(tb__ "0|0|
Sb0S47SbA2").
Lemma pm__42_eq : ltac2:(tb__ "0|1|
S0S2S14S21S1fZ2M0A1SaS1dG0A2A3S4bA3"). Proof. cbv delta [T5m2 pm__42]; cbv beta zeta. PM_all42. reflexivity. Qed.
Ltac PM_sub43 t := let t := lazymatch (eval pattern (T5m2 nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__42) end in PM_sub42 t.
Ltac PM_all43 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__42_eq; PM_all42.
Definition pm__43 : axst := ltac2:(tb__ "0|0|
Sb0S48SbA2").
Lemma pm__43_eq : ltac2:(tb__ "0|1|
S0S2S14S21S1fZ3M0A1SaS1dG0A2A3S4cA3"). Proof. cbv delta [T5m2 pm__43]; cbv beta zeta. PM_all43. reflexivity. Qed.
Ltac PM_sub44 t := let t := lazymatch (eval pattern (T5m2 nobja (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__43) end in PM_sub43 t.
Ltac PM_all44 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__43_eq; PM_all43.
Definition pm__44 : axst := ltac2:(tb__ "0|0|
Sb0S49SbA2").
Lemma pm__44_eq : ltac2:(tb__ "0|1|
S0S2S14S21S1fZ4M0A1SaS1dG0A2A3S4dA3"). Proof. cbv delta [T5m2 pm__44]; cbv beta zeta. PM_all44. reflexivity. Qed.
Ltac PM_sub45 t := let t := lazymatch (eval pattern (T5m2 nobja (T4a_i 4) (X5s X5ac 4)) in t) with ?P _ => eval cbv beta in (P pm__44) end in PM_sub44 t.
Ltac PM_all45 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__44_eq; PM_all44.
Definition pm__45 : axst := ltac2:(tb__ "0|0|
Sb0S4aSbA2").
Lemma pm__45_eq : ltac2:(tb__ "0|1|
S0S2S15S21S1fZ1M0A1SaS1dG0A2A3S4eA3"). Proof. cbv delta [T5m3 pm__45]; cbv beta zeta. PM_all45. reflexivity. Qed.
Ltac PM_sub46 t := let t := lazymatch (eval pattern (T5m3 nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__45) end in PM_sub45 t.
Ltac PM_all46 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__45_eq; PM_all45.
Definition pm__46 : axst := ltac2:(tb__ "0|0|
Sb0S4bSbA2").
Lemma pm__46_eq : ltac2:(tb__ "0|1|
S0S2S15S21S1fZ2M0A1SaS1dG0A2A3S4fA3"). Proof. cbv delta [T5m3 pm__46]; cbv beta zeta. PM_all46. reflexivity. Qed.
Ltac PM_sub47 t := let t := lazymatch (eval pattern (T5m3 nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__46) end in PM_sub46 t.
Ltac PM_all47 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__46_eq; PM_all46.
Definition pm__47 : axst := ltac2:(tb__ "0|0|
Sb0S4cSbA2").
Lemma pm__47_eq : ltac2:(tb__ "0|1|
S0S2S15S21S1fZ3M0A1SaS1dG0A2A3S50A3"). Proof. cbv delta [T5m3 pm__47]; cbv beta zeta. PM_all47. reflexivity. Qed.
Ltac PM_sub48 t := let t := lazymatch (eval pattern (T5m3 nobja (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__47) end in PM_sub47 t.
Ltac PM_all48 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__47_eq; PM_all47.
Definition pm__48 : axst := ltac2:(tb__ "0|0|
Sb0S4dSbA2").
Lemma pm__48_eq : ltac2:(tb__ "0|1|
S0S2S15S21S1fZ4M0A1SaS1dG0A2A3S51A3"). Proof. cbv delta [T5m3 pm__48]; cbv beta zeta. PM_all48. reflexivity. Qed.
Ltac PM_sub49 t := let t := lazymatch (eval pattern (T5m3 nobja (T4a_i 4) (X5s X5ac 4)) in t) with ?P _ => eval cbv beta in (P pm__48) end in PM_sub48 t.
Ltac PM_all49 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__48_eq; PM_all48.
Definition pm__49 : axst := ltac2:(tb__ "0|0|
Sb0S4eSbA2").
Lemma pm__49_eq : ltac2:(tb__ "0|1|
S0S2ScS21S1fZ1M0A1SaS1dG0A2A3S84A3"). Proof. cbv delta [T5d pm__49]; cbv beta zeta. PM_all49. reflexivity. Qed.
Ltac PM_sub50 t := let t := lazymatch (eval pattern (T5d nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__49) end in PM_sub49 t.
Ltac PM_all50 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__49_eq; PM_all49.
Definition pm__50 : axst := ltac2:(tb__ "0|0|
Sb0S4fSbA2").
Lemma pm__50_eq : ltac2:(tb__ "0|1|
S0S2ScS21S1fZ2M0A1SaS1dG0A2A3S86A3"). Proof. cbv delta [T5d pm__50]; cbv beta zeta. PM_all50. reflexivity. Qed.
Ltac PM_sub51 t := let t := lazymatch (eval pattern (T5d nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__50) end in PM_sub50 t.
Ltac PM_all51 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__50_eq; PM_all50.
Definition pm__51 : axst := ltac2:(tb__ "0|0|
Sb0S50SbA2").
Lemma pm__51_eq : ltac2:(tb__ "0|1|
S0S2ScS21S1fZ3M0A1SaS1dG0A2A3S87A3"). Proof. cbv delta [T5d pm__51]; cbv beta zeta. PM_all51. reflexivity. Qed.
Ltac PM_sub52 t := let t := lazymatch (eval pattern (T5d nobja (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__51) end in PM_sub51 t.
Ltac PM_all52 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__51_eq; PM_all51.
Definition pm__52 : axst := ltac2:(tb__ "0|0|
Sb0S51SbA2").
Lemma pm__52_eq : ltac2:(tb__ "0|1|
S0S2ScS21S1fZ4M0A1SaS1dG0A2A3S88A3"). Proof. cbv delta [T5d pm__52]; cbv beta zeta. PM_all52. reflexivity. Qed.
Ltac PM_sub53 t := let t := lazymatch (eval pattern (T5d nobja (T4a_i 4) (X5s X5ac 4)) in t) with ?P _ => eval cbv beta in (P pm__52) end in PM_sub52 t.
Ltac PM_all53 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__52_eq; PM_all52.
Definition pm__53 : axst := ltac:(let t := eval cbv delta [C5S] in (C5S X5ac) in let t := eval cbv beta zeta in t in let t := PM_sub53 t in exact t).
Lemma pm__53_eq : ltac2:(tb__ "0|0|
S0S2S1aS1dA1S89A3"). Proof. cbv delta [C5S pm__53]; cbv beta zeta. PM_all53. reflexivity. Qed.
Ltac PM_sub54 t := let t := lazymatch (eval pattern (C5S X5ac) in t) with ?P _ => eval cbv beta in (P pm__53) end in PM_sub53 t.
Ltac PM_all54 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__53_eq; PM_all53.
Lemma WX5ra_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3SbfS3SdS1dR2A2A1A1Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma DX5ra_0 : ltac2:(tb__ "0|4|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0SabSa8Sa7Sa8Sb3Sb3A2M0A1M1Sa7Sb4A1M2A2M3A1SdbS3S19S1dA1A1S3SdS1dR2A2A1A2SadG3SacG1G2Sa6G0SacSb3Sb3Sc0SaeQ20SbaPc0A1A3Sb7R2A1A4Sa5G0A1A3Sa5Sb4A1A4A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL1a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd1S3SdS1dR2A2A1SbSb7Nee0A1A3A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL2a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd1S3S16S1dR2A2A1Sa9SbA1Sb7N8e0A1A3A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL3a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd1S3S17S1dR2A2A1Sa9Sa9SbA1A1Sb7N840A1A3A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL4a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd1S3S18S1dR2A2A1Sa9Sa9Sa9SbA1A1A1Sb7N48A1A3A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HERa_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0SabSa7Sb5A1M0A1Se7SaS1dR2A2SccR2A1S25R2A1A3SadG0S27R2A1A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HT4a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0S2Se8S25R2A1SccR2A1ScdR2A1SaS1dR2A2S27R2A1A5S1fR2A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XX4a_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa7Sa8Sb3Sb3A2M0A1S5SaS1dR2A2A1Sa5G0A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma FBX4a_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc8Sb4SbcSb9S3SaS1dR2A2A1M0A1A1Sb6G0A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Hchk4a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Se6SaS1dR2A2SccR2A1S25R2A1S27R2A1Sa6S2ScdR2A1Sa5S2A1A3A5Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma NX4a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa2Sb9S3SaS1dR2A2A1A1Sb9S3S1dA1A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma WG10a_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sb3Sd6S25R2A1PaM0A2SbdSd9SbaG0A1Sb7N8e0A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG15a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sb3Sd6S25R2A1PfA2Sb7N600A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG12a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sb3Sd6S25R2A1PcA2SbdSd9SbaPaA1Sb7N840A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FAM4a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc8Sb5S1cU2Sd5S71A3S27R2A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NEWOa_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa7Sb5A1Se3S3SccR2A1A1S3ScdR2A1A1A2Sa5Sb5A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XPosta_0 : ltac2:(tb__ "0|1|
Sa1S0Sa7Sa8Sb3Sb3A2M0A1S5ScdR1A1A1Sa5G0A1A3Fsz;"). Proof. intros sz. reflexivity. Qed.
Lemma FBT4a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc8Sb4SbcSb9S3S1fR2A1A1A1A1Sb6S3SaS1dR2A2A1A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XT4a_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa7Sa8Sb3Sb3A2M0A1S5S1fR2A1A1Sa5G0A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RB1a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd2S3SfS1fR2A1SaS1dR2A2A2A1U0A2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma RB2a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd2S3S10S1fR2A1SaS1dR2A2A2A1U1A2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma PERM_nda_0 : ltac2:(tb__ "0|0|
S0Sa3ScfSeS21A1A1Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_lta_0 : ltac2:(tb__ "0|0|
S0Sa3Sc8SaaSaaSefR1S21A2Li;SeS21A1A3Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_cova_0 : ltac2:(tb__ "0|0|
S0Sa3Sc8SaaSaaScbSaaSeeR1A1SeS21A1A3Li;Se1U0S21A2A3Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_lena_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0SaaSafSb5SbbS3S11S1fR2A1SaS1dR2A2A2A1A1A2S21A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG1a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd0S3S12S21S1fR2A1SaS1dR2A2A3A1SbA2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG2a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd0S3S13S21S1fR2A1SaS1dR2A2A3A1SbA2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG3a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd0S3S14S21S1fR2A1SaS1dR2A2A3A1SbA2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG4a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd0S3S15S21S1fR2A1SaS1dR2A2A3A1SbA2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma ENT5a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3S6ScS21S1fR2A1SaS1dR2A2A3S31S6bR2A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sda_i]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SID5a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sd8S6bR2A1VGS0;A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sda_i]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma R4cova_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3S1bSb6S3ScS21S1fR2A1SaS1dR2A2A3A1M0A1S27R2A1SbbG0A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.

Definition U4bc : axst := Eval vm_compute in (U4p nx0 T4bc).
Lemma WU4b_0 : ltac2:(tb__ "0|0|
S0Sa3SbfS3S24A1A1Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DU4b_0 : ltac2:(tb__ "0|4|
S0SabSa8Sa7Sa8Sb3Sb3A2M0A1M1Sa7Sb4A1M2A2M3A1SdbS3Se0A1S3S24A1A2SadG3SacG1G2Sa5G0A1SddSd5A1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXU4b_0 : ltac2:(tb__ "0|0|
S0Sa2Sb9S3S24A1A1Sb9S3Se0A1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HU4b_0 : ltac2:(tb__ "0|0|
S0S2S4Se0S3S24A1A2S24A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run5b : option (list leafA) := Eval vm_compute in (runT5 U4bc).
Lemma run5b__runeq : ltac2:(tb__ "0|1|
S0Sa7SabSa7S7A1A1M0A1Se5SdeUfa0Sa6Sa1SdcSa5Sa1A1A3Sa6S2S24Sa5S2A1A3A4Sa6G0Sa0Sa5G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run5b]). Qed.
Definition X5bc : axst := Eval vm_compute in (leafS 0 run5b).
Lemma Cert5b_0 : ltac2:(tb__ "0|1|
S0Sa3Se4SdeUfa0Sa6Sa1SdcSa5Sa1A1A3VGS0;Sa6S2S24Sa5S2A1M0A3Sa6S2S1eG0A3A6Sa4A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [DPENT] GS0 [U4bc] [X5bc] [run5b]); [exact run5b__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition C5bc : axst := Eval vm_compute in (C5S X5bc).

Definition CPb1 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5bc 1) 1)).
Definition CPb2 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5bc 2) 2)).
Definition CPb (sz : Z) : wsub * list sobj * axst := ltac2:(tb__ "0|0|
Sa3Sa8Sa8Sd7Sa7Sb5A1A2S2A2L_;S9Vsz;Z1A2S6fS70Xa3x2").
Definition s4b_i (sz : Z) : wsub := fst (fst (CPb sz)).
Definition R4b_i (sz : Z) : list sobj := snd (fst (CPb sz)).
Definition T4b_i (sz : Z) : axst := snd (CPb sz).
Definition nobjb : nat := Eval vm_compute in (length (ss_objs (ax_S (T5b (T4b_i 1) (X5s X5bc 1))))).
Definition sdb_i (sz : Z) : wsub := ltac2:(tb__ "0|0|
Se2VGS0;S3ScS22S20Vsz;A1SaS1eVsz;A2A3A1S3S32A1A3").
Definition EXob : list sobj := ltac2:(tb__ "0|0|
Sa6Sb5Sc5Sd5A1Sa6Sb5Sc4Sd5A1Sa6Sb5Sc7Sa5Sb5A1A3A3A3").

Lemma NXEb_0 : ltac2:(tb__ "0|0|
S0Sa3Sf0VGS0;Sb9S3S1eA1A1A2Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBEb_0 : ltac2:(tb__ "0|0|
S0Sa3Sc8Sb4SbcSb9S3S1eA1A1A1Sb2A3Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XE5b_0 : ax_X X5bc = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F192b_0 : ltac2:(tb__ "0|1|
Sc9Sb4Sa6Sb4SbeSb7Z1A1SbaPc0A1M0A2Sa6Sb4SbeG0Sb7Vtmax;A1A2Sa5Sb4A1A3A3Sb6S3S1eA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FDEPb_0 : ltac2:(tb__ "0|0|
Sc9Sb4SecSebA1Sb6S3S1eA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FUNWb_0 : ltac2:(tb__ "0|0|
Sc9Sb4SedVW;Vst;A2Sb6S3S1eA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FXBb_0 : ltac2:(tb__ "0|0|
ScaSb4Sc2Sc1SdaSbaSe9A1SbaSeaA1A3A1Sb6S3S1eA1A1A3"). Proof. apply In_of_inclb. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition pm__54 : axst := ltac:(let t := eval cbv delta [X5f] in (X5f X5bc) in let t := eval cbv beta zeta in t in let t := PM_sub54 t in exact t).
Lemma pm__54_eq : ltac2:(tb__ "0|0|
S0S2S19S1eA1S8aA3"). Proof. cbv delta [X5f pm__54]; cbv beta zeta. PM_all54. reflexivity. Qed.
Ltac PM_sub55 t := let t := lazymatch (eval pattern (X5f X5bc) in t) with ?P _ => eval cbv beta in (P pm__54) end in PM_sub54 t.
Ltac PM_all55 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__54_eq; PM_all54.
Definition pm__55 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub55 t in exact t).
Lemma pm__55_eq : ltac2:(tb__ "0|0|
S0S2SdS1eZ1A2S8bA3"). Proof. cbv delta [X5r pm__55]; cbv beta zeta. PM_all55. reflexivity. Qed.
Ltac PM_sub56 t := let t := lazymatch (eval pattern (X5r X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__55) end in PM_sub55 t.
Ltac PM_all56 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__55_eq; PM_all55.
Definition pm__56 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub56 t in exact t).
Lemma pm__56_eq : ltac2:(tb__ "0|0|
S0S2SdS1eZ2A2S8cA3"). Proof. cbv delta [X5r pm__56]; cbv beta zeta. PM_all56. reflexivity. Qed.
Ltac PM_sub57 t := let t := lazymatch (eval pattern (X5r X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__56) end in PM_sub56 t.
Ltac PM_all57 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__56_eq; PM_all56.
Definition pm__57 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5bc 3) in let t := eval cbv beta zeta in t in let t := PM_sub57 t in exact t).
Lemma pm__57_eq : ltac2:(tb__ "0|0|
S0S2SdS1eZ3A2S8dA3"). Proof. cbv delta [X5r pm__57]; cbv beta zeta. PM_all57. reflexivity. Qed.
Ltac PM_sub58 t := let t := lazymatch (eval pattern (X5r X5bc 3) in t) with ?P _ => eval cbv beta in (P pm__57) end in PM_sub57 t.
Ltac PM_all58 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__57_eq; PM_all57.
Definition pm__58 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5bc 4) in let t := eval cbv beta zeta in t in let t := PM_sub58 t in exact t).
Lemma pm__58_eq : ltac2:(tb__ "0|0|
S0S2SdS1eZ4A2S8eA3"). Proof. cbv delta [X5r pm__58]; cbv beta zeta. PM_all58. reflexivity. Qed.
Ltac PM_sub59 t := let t := lazymatch (eval pattern (X5r X5bc 4) in t) with ?P _ => eval cbv beta in (P pm__58) end in PM_sub58 t.
Ltac PM_all59 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__58_eq; PM_all58.
Definition pm__59 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub59 t in exact t).
Lemma pm__59_eq : ltac2:(tb__ "0|0|
S0S2S16S1eZ1A2S8fA3"). Proof. cbv delta [X5a pm__59]; cbv beta zeta. PM_all59. reflexivity. Qed.
Ltac PM_sub60 t := let t := lazymatch (eval pattern (X5a X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__59) end in PM_sub59 t.
Ltac PM_all60 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__59_eq; PM_all59.
Definition pm__60 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub60 t in exact t).
Lemma pm__60_eq : ltac2:(tb__ "0|0|
S0S2S16S1eZ2A2S91A3"). Proof. cbv delta [X5a pm__60]; cbv beta zeta. PM_all60. reflexivity. Qed.
Ltac PM_sub61 t := let t := lazymatch (eval pattern (X5a X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__60) end in PM_sub60 t.
Ltac PM_all61 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__60_eq; PM_all60.
Definition pm__61 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5bc 3) in let t := eval cbv beta zeta in t in let t := PM_sub61 t in exact t).
Lemma pm__61_eq : ltac2:(tb__ "0|0|
S0S2S16S1eZ3A2S92A3"). Proof. cbv delta [X5a pm__61]; cbv beta zeta. PM_all61. reflexivity. Qed.
Ltac PM_sub62 t := let t := lazymatch (eval pattern (X5a X5bc 3) in t) with ?P _ => eval cbv beta in (P pm__61) end in PM_sub61 t.
Ltac PM_all62 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__61_eq; PM_all61.
Definition pm__62 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5bc 4) in let t := eval cbv beta zeta in t in let t := PM_sub62 t in exact t).
Lemma pm__62_eq : ltac2:(tb__ "0|0|
S0S2S16S1eZ4A2S93A3"). Proof. cbv delta [X5a pm__62]; cbv beta zeta. PM_all62. reflexivity. Qed.
Ltac PM_sub63 t := let t := lazymatch (eval pattern (X5a X5bc 4) in t) with ?P _ => eval cbv beta in (P pm__62) end in PM_sub62 t.
Ltac PM_all63 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__62_eq; PM_all62.
Definition pm__63 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub63 t in exact t).
Lemma pm__63_eq : ltac2:(tb__ "0|0|
S0S2S17S1eZ1A2S94A3"). Proof. cbv delta [X5b pm__63]; cbv beta zeta. PM_all63. reflexivity. Qed.
Ltac PM_sub64 t := let t := lazymatch (eval pattern (X5b X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__63) end in PM_sub63 t.
Ltac PM_all64 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__63_eq; PM_all63.
Definition pm__64 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub64 t in exact t).
Lemma pm__64_eq : ltac2:(tb__ "0|0|
S0S2S17S1eZ2A2S95A3"). Proof. cbv delta [X5b pm__64]; cbv beta zeta. PM_all64. reflexivity. Qed.
Ltac PM_sub65 t := let t := lazymatch (eval pattern (X5b X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__64) end in PM_sub64 t.
Ltac PM_all65 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__64_eq; PM_all64.
Definition pm__65 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5bc 3) in let t := eval cbv beta zeta in t in let t := PM_sub65 t in exact t).
Lemma pm__65_eq : ltac2:(tb__ "0|0|
S0S2S17S1eZ3A2S96A3"). Proof. cbv delta [X5b pm__65]; cbv beta zeta. PM_all65. reflexivity. Qed.
Ltac PM_sub66 t := let t := lazymatch (eval pattern (X5b X5bc 3) in t) with ?P _ => eval cbv beta in (P pm__65) end in PM_sub65 t.
Ltac PM_all66 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__65_eq; PM_all65.
Definition pm__66 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5bc 4) in let t := eval cbv beta zeta in t in let t := PM_sub66 t in exact t).
Lemma pm__66_eq : ltac2:(tb__ "0|0|
S0S2S17S1eZ4A2S97A3"). Proof. cbv delta [X5b pm__66]; cbv beta zeta. PM_all66. reflexivity. Qed.
Ltac PM_sub67 t := let t := lazymatch (eval pattern (X5b X5bc 4) in t) with ?P _ => eval cbv beta in (P pm__66) end in PM_sub66 t.
Ltac PM_all67 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__66_eq; PM_all66.
Definition pm__67 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub67 t in exact t).
Lemma pm__67_eq : ltac2:(tb__ "0|0|
S0S2S18S1eZ1A2S98A3"). Proof. cbv delta [X5c pm__67]; cbv beta zeta. PM_all67. reflexivity. Qed.
Ltac PM_sub68 t := let t := lazymatch (eval pattern (X5c X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__67) end in PM_sub67 t.
Ltac PM_all68 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__67_eq; PM_all67.
Definition pm__68 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub68 t in exact t).
Lemma pm__68_eq : ltac2:(tb__ "0|0|
S0S2S18S1eZ2A2S99A3"). Proof. cbv delta [X5c pm__68]; cbv beta zeta. PM_all68. reflexivity. Qed.
Ltac PM_sub69 t := let t := lazymatch (eval pattern (X5c X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__68) end in PM_sub68 t.
Ltac PM_all69 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__68_eq; PM_all68.
Definition pm__69 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5bc 3) in let t := eval cbv beta zeta in t in let t := PM_sub69 t in exact t).
Lemma pm__69_eq : ltac2:(tb__ "0|0|
S0S2S18S1eZ3A2S9aA3"). Proof. cbv delta [X5c pm__69]; cbv beta zeta. PM_all69. reflexivity. Qed.
Ltac PM_sub70 t := let t := lazymatch (eval pattern (X5c X5bc 3) in t) with ?P _ => eval cbv beta in (P pm__69) end in PM_sub69 t.
Ltac PM_all70 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__69_eq; PM_all69.
Definition pm__70 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5bc 4) in let t := eval cbv beta zeta in t in let t := PM_sub70 t in exact t).
Lemma pm__70_eq : ltac2:(tb__ "0|0|
S0S2S18S1eZ4A2S9cA3"). Proof. cbv delta [X5c pm__70]; cbv beta zeta. PM_all70. reflexivity. Qed.
Ltac PM_sub71 t := let t := lazymatch (eval pattern (X5c X5bc 4) in t) with ?P _ => eval cbv beta in (P pm__70) end in PM_sub70 t.
Ltac PM_all71 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__70_eq; PM_all70.
Definition pm__71 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub71 t in exact t).
Lemma pm__71_eq : ltac2:(tb__ "0|0|
S0S2SaS1eZ1A2S52A3"). Proof. cbv delta [X5s pm__71]; cbv beta zeta. PM_all71. reflexivity. Qed.
Ltac PM_sub72 t := let t := lazymatch (eval pattern (X5s X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__71) end in PM_sub71 t.
Ltac PM_all72 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__71_eq; PM_all71.
Definition pm__72 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub72 t in exact t).
Lemma pm__72_eq : ltac2:(tb__ "0|0|
S0S2SaS1eZ2A2S53A3"). Proof. cbv delta [X5s pm__72]; cbv beta zeta. PM_all72. reflexivity. Qed.
Ltac PM_sub73 t := let t := lazymatch (eval pattern (X5s X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__72) end in PM_sub72 t.
Ltac PM_all73 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__72_eq; PM_all72.
Definition pm__73 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5bc 3) in let t := eval cbv beta zeta in t in let t := PM_sub73 t in exact t).
Lemma pm__73_eq : ltac2:(tb__ "0|0|
S0S2SaS1eZ3A2S54A3"). Proof. cbv delta [X5s pm__73]; cbv beta zeta. PM_all73. reflexivity. Qed.
Ltac PM_sub74 t := let t := lazymatch (eval pattern (X5s X5bc 3) in t) with ?P _ => eval cbv beta in (P pm__73) end in PM_sub73 t.
Ltac PM_all74 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__73_eq; PM_all73.
Definition pm__74 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5bc 4) in let t := eval cbv beta zeta in t in let t := PM_sub74 t in exact t).
Lemma pm__74_eq : ltac2:(tb__ "0|0|
S0S2SaS1eZ4A2S55A3"). Proof. cbv delta [X5s pm__74]; cbv beta zeta. PM_all74. reflexivity. Qed.
Ltac PM_sub75 t := let t := lazymatch (eval pattern (X5s X5bc 4) in t) with ?P _ => eval cbv beta in (P pm__74) end in PM_sub74 t.
Ltac PM_all75 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__74_eq; PM_all74.
Definition pm__75 : axst := ltac2:(tb__ "0|0|
Sd4S20Z1A1Sb6S3S52A1A1A2").
Lemma pm__75_eq : ltac2:(tb__ "0|1|
S0S2SfS20Z1M0A1SaS1eG0A2A2S56A3"). Proof. cbv delta [T50 pm__75]; cbv beta zeta. PM_all75. reflexivity. Qed.
Ltac PM_sub76 t := let t := lazymatch (eval pattern (T50 (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__75) end in PM_sub75 t.
Ltac PM_all76 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__75_eq; PM_all75.
Definition pm__76 : axst := ltac2:(tb__ "0|0|
Sd4S20Z2A1Sb6S3S53A1A1A2").
Lemma pm__76_eq : ltac2:(tb__ "0|1|
S0S2SfS20Z2M0A1SaS1eG0A2A2S57A3"). Proof. cbv delta [T50 pm__76]; cbv beta zeta. PM_all76. reflexivity. Qed.
Ltac PM_sub77 t := let t := lazymatch (eval pattern (T50 (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__76) end in PM_sub76 t.
Ltac PM_all77 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__76_eq; PM_all76.
Definition pm__77 : axst := ltac2:(tb__ "0|0|
Sd4S20Z3A1Sb6S3S54A1A1A2").
Lemma pm__77_eq : ltac2:(tb__ "0|1|
S0S2SfS20Z3M0A1SaS1eG0A2A2S58A3"). Proof. cbv delta [T50 pm__77]; cbv beta zeta. PM_all77. reflexivity. Qed.
Ltac PM_sub78 t := let t := lazymatch (eval pattern (T50 (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__77) end in PM_sub77 t.
Ltac PM_all78 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__77_eq; PM_all77.
Definition pm__78 : axst := ltac2:(tb__ "0|0|
Sd4S20Z4A1Sb6S3S55A1A1A2").
Lemma pm__78_eq : ltac2:(tb__ "0|1|
S0S2SfS20Z4M0A1SaS1eG0A2A2S59A3"). Proof. cbv delta [T50 pm__78]; cbv beta zeta. PM_all78. reflexivity. Qed.
Ltac PM_sub79 t := let t := lazymatch (eval pattern (T50 (T4b_i 4) (X5s X5bc 4)) in t) with ?P _ => eval cbv beta in (P pm__78) end in PM_sub78 t.
Ltac PM_all79 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__78_eq; PM_all78.
Definition pm__79 : axst := ltac2:(tb__ "0|0|
Sb1S56U0A2").
Lemma pm__79_eq : ltac2:(tb__ "0|1|
S0S2S10S20Z1M0A1SaS1eG0A2A2S5aA3"). Proof. cbv delta [T5a pm__79]; cbv beta zeta. PM_all79. reflexivity. Qed.
Ltac PM_sub80 t := let t := lazymatch (eval pattern (T5a (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__79) end in PM_sub79 t.
Ltac PM_all80 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__79_eq; PM_all79.
Definition pm__80 : axst := ltac2:(tb__ "0|0|
Sb1S57U0A2").
Lemma pm__80_eq : ltac2:(tb__ "0|1|
S0S2S10S20Z2M0A1SaS1eG0A2A2S5bA3"). Proof. cbv delta [T5a pm__80]; cbv beta zeta. PM_all80. reflexivity. Qed.
Ltac PM_sub81 t := let t := lazymatch (eval pattern (T5a (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__80) end in PM_sub80 t.
Ltac PM_all81 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__80_eq; PM_all80.
Definition pm__81 : axst := ltac2:(tb__ "0|0|
Sb1S58U0A2").
Lemma pm__81_eq : ltac2:(tb__ "0|1|
S0S2S10S20Z3M0A1SaS1eG0A2A2S5cA3"). Proof. cbv delta [T5a pm__81]; cbv beta zeta. PM_all81. reflexivity. Qed.
Ltac PM_sub82 t := let t := lazymatch (eval pattern (T5a (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__81) end in PM_sub81 t.
Ltac PM_all82 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__81_eq; PM_all81.
Definition pm__82 : axst := ltac2:(tb__ "0|0|
Sb1S59U0A2").
Lemma pm__82_eq : ltac2:(tb__ "0|1|
S0S2S10S20Z4M0A1SaS1eG0A2A2S5dA3"). Proof. cbv delta [T5a pm__82]; cbv beta zeta. PM_all82. reflexivity. Qed.
Ltac PM_sub83 t := let t := lazymatch (eval pattern (T5a (T4b_i 4) (X5s X5bc 4)) in t) with ?P _ => eval cbv beta in (P pm__82) end in PM_sub82 t.
Ltac PM_all83 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__82_eq; PM_all82.
Definition pm__83 : axst := ltac2:(tb__ "0|0|
Sb1S5aU1A2").
Lemma pm__83_eq : ltac2:(tb__ "0|1|
S0S2S11S20Z1M0A1SaS1eG0A2A2S2dA3"). Proof. cbv delta [T5b pm__83]; cbv beta zeta. PM_all83. reflexivity. Qed.
Ltac PM_sub84 t := let t := lazymatch (eval pattern (T5b (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__83) end in PM_sub83 t.
Ltac PM_all84 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__83_eq; PM_all83.
Definition pm__84 : axst := ltac2:(tb__ "0|0|
Sb1S5bU1A2").
Lemma pm__84_eq : ltac2:(tb__ "0|1|
S0S2S11S20Z2M0A1SaS1eG0A2A2S2eA3"). Proof. cbv delta [T5b pm__84]; cbv beta zeta. PM_all84. reflexivity. Qed.
Ltac PM_sub85 t := let t := lazymatch (eval pattern (T5b (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__84) end in PM_sub84 t.
Ltac PM_all85 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__84_eq; PM_all84.
Definition pm__85 : axst := ltac2:(tb__ "0|0|
Sb1S5cU1A2").
Lemma pm__85_eq : ltac2:(tb__ "0|1|
S0S2S11S20Z3M0A1SaS1eG0A2A2S2fA3"). Proof. cbv delta [T5b pm__85]; cbv beta zeta. PM_all85. reflexivity. Qed.
Ltac PM_sub86 t := let t := lazymatch (eval pattern (T5b (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__85) end in PM_sub85 t.
Ltac PM_all86 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__85_eq; PM_all85.
Definition pm__86 : axst := ltac2:(tb__ "0|0|
Sb1S5dU1A2").
Lemma pm__86_eq : ltac2:(tb__ "0|1|
S0S2S11S20Z4M0A1SaS1eG0A2A2S30A3"). Proof. cbv delta [T5b pm__86]; cbv beta zeta. PM_all86. reflexivity. Qed.
Ltac PM_sub87 t := let t := lazymatch (eval pattern (T5b (T4b_i 4) (X5s X5bc 4)) in t) with ?P _ => eval cbv beta in (P pm__86) end in PM_sub86 t.
Ltac PM_all87 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__86_eq; PM_all86.
Definition pm__87 : axst := ltac2:(tb__ "0|1|
S4S2dSd3S3S2dA1M0SceSbbG0A1SeS22A1A2A2A2").
Lemma pm__87_eq : ltac2:(tb__ "0|1|
S0S2S12S22S20Z1M0A1SaS1eG0A2A3S5eA3"). Proof. cbv delta [T5c pm__87]; cbv beta zeta. PM_all87. reflexivity. Qed.
Ltac PM_sub88 t := let t := lazymatch (eval pattern (T5c nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__87) end in PM_sub87 t.
Ltac PM_all88 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__87_eq; PM_all87.
Definition pm__88 : axst := ltac2:(tb__ "0|1|
S4S2eSd3S3S2eA1M0SceSbbG0A1SeS22A1A2A2A2").
Lemma pm__88_eq : ltac2:(tb__ "0|1|
S0S2S12S22S20Z2M0A1SaS1eG0A2A3S5fA3"). Proof. cbv delta [T5c pm__88]; cbv beta zeta. PM_all88. reflexivity. Qed.
Ltac PM_sub89 t := let t := lazymatch (eval pattern (T5c nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__88) end in PM_sub88 t.
Ltac PM_all89 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__88_eq; PM_all88.
Definition pm__89 : axst := ltac2:(tb__ "0|1|
S4S2fSd3S3S2fA1M0SceSbbG0A1SeS22A1A2A2A2").
Lemma pm__89_eq : ltac2:(tb__ "0|1|
S0S2S12S22S20Z3M0A1SaS1eG0A2A3S60A3"). Proof. cbv delta [T5c pm__89]; cbv beta zeta. PM_all89. reflexivity. Qed.
Ltac PM_sub90 t := let t := lazymatch (eval pattern (T5c nobjb (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__89) end in PM_sub89 t.
Ltac PM_all90 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__89_eq; PM_all89.
Definition pm__90 : axst := ltac2:(tb__ "0|1|
S4S30Sd3S3S30A1M0SceSbbG0A1SeS22A1A2A2A2").
Lemma pm__90_eq : ltac2:(tb__ "0|1|
S0S2S12S22S20Z4M0A1SaS1eG0A2A3S61A3"). Proof. cbv delta [T5c pm__90]; cbv beta zeta. PM_all90. reflexivity. Qed.
Ltac PM_sub91 t := let t := lazymatch (eval pattern (T5c nobjb (T4b_i 4) (X5s X5bc 4)) in t) with ?P _ => eval cbv beta in (P pm__90) end in PM_sub90 t.
Ltac PM_all91 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__90_eq; PM_all90.
Definition pm__91 : axst := ltac2:(tb__ "0|0|
Sb0S5eSbA2").
Lemma pm__91_eq : ltac2:(tb__ "0|1|
S0S2S13S22S20Z1M0A1SaS1eG0A2A3S62A3"). Proof. cbv delta [T5m1 pm__91]; cbv beta zeta. PM_all91. reflexivity. Qed.
Ltac PM_sub92 t := let t := lazymatch (eval pattern (T5m1 nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__91) end in PM_sub91 t.
Ltac PM_all92 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__91_eq; PM_all91.
Definition pm__92 : axst := ltac2:(tb__ "0|0|
Sb0S5fSbA2").
Lemma pm__92_eq : ltac2:(tb__ "0|1|
S0S2S13S22S20Z2M0A1SaS1eG0A2A3S63A3"). Proof. cbv delta [T5m1 pm__92]; cbv beta zeta. PM_all92. reflexivity. Qed.
Ltac PM_sub93 t := let t := lazymatch (eval pattern (T5m1 nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__92) end in PM_sub92 t.
Ltac PM_all93 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__92_eq; PM_all92.
Definition pm__93 : axst := ltac2:(tb__ "0|0|
Sb0S60SbA2").
Lemma pm__93_eq : ltac2:(tb__ "0|1|
S0S2S13S22S20Z3M0A1SaS1eG0A2A3S64A3"). Proof. cbv delta [T5m1 pm__93]; cbv beta zeta. PM_all93. reflexivity. Qed.
Ltac PM_sub94 t := let t := lazymatch (eval pattern (T5m1 nobjb (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__93) end in PM_sub93 t.
Ltac PM_all94 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__93_eq; PM_all93.
Definition pm__94 : axst := ltac2:(tb__ "0|0|
Sb0S61SbA2").
Lemma pm__94_eq : ltac2:(tb__ "0|1|
S0S2S13S22S20Z4M0A1SaS1eG0A2A3S65A3"). Proof. cbv delta [T5m1 pm__94]; cbv beta zeta. PM_all94. reflexivity. Qed.
Ltac PM_sub95 t := let t := lazymatch (eval pattern (T5m1 nobjb (T4b_i 4) (X5s X5bc 4)) in t) with ?P _ => eval cbv beta in (P pm__94) end in PM_sub94 t.
Ltac PM_all95 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__94_eq; PM_all94.
Definition pm__95 : axst := ltac2:(tb__ "0|0|
Sb0S62SbA2").
Lemma pm__95_eq : ltac2:(tb__ "0|1|
S0S2S14S22S20Z1M0A1SaS1eG0A2A3S66A3"). Proof. cbv delta [T5m2 pm__95]; cbv beta zeta. PM_all95. reflexivity. Qed.
Ltac PM_sub96 t := let t := lazymatch (eval pattern (T5m2 nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__95) end in PM_sub95 t.
Ltac PM_all96 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__95_eq; PM_all95.
Definition pm__96 : axst := ltac2:(tb__ "0|0|
Sb0S63SbA2").
Lemma pm__96_eq : ltac2:(tb__ "0|1|
S0S2S14S22S20Z2M0A1SaS1eG0A2A3S67A3"). Proof. cbv delta [T5m2 pm__96]; cbv beta zeta. PM_all96. reflexivity. Qed.
Ltac PM_sub97 t := let t := lazymatch (eval pattern (T5m2 nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__96) end in PM_sub96 t.
Ltac PM_all97 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__96_eq; PM_all96.
Definition pm__97 : axst := ltac2:(tb__ "0|0|
Sb0S64SbA2").
Lemma pm__97_eq : ltac2:(tb__ "0|1|
S0S2S14S22S20Z3M0A1SaS1eG0A2A3S68A3"). Proof. cbv delta [T5m2 pm__97]; cbv beta zeta. PM_all97. reflexivity. Qed.
Ltac PM_sub98 t := let t := lazymatch (eval pattern (T5m2 nobjb (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__97) end in PM_sub97 t.
Ltac PM_all98 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__97_eq; PM_all97.
Definition pm__98 : axst := ltac2:(tb__ "0|0|
Sb0S65SbA2").
Lemma pm__98_eq : ltac2:(tb__ "0|1|
S0S2S14S22S20Z4M0A1SaS1eG0A2A3S69A3"). Proof. cbv delta [T5m2 pm__98]; cbv beta zeta. PM_all98. reflexivity. Qed.
Ltac PM_sub99 t := let t := lazymatch (eval pattern (T5m2 nobjb (T4b_i 4) (X5s X5bc 4)) in t) with ?P _ => eval cbv beta in (P pm__98) end in PM_sub98 t.
Ltac PM_all99 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__98_eq; PM_all98.
Definition pm__99 : axst := ltac2:(tb__ "0|0|
Sb0S66SbA2").
Lemma pm__99_eq : ltac2:(tb__ "0|1|
S0S2S15S22S20Z1M0A1SaS1eG0A2A3S6aA3"). Proof. cbv delta [T5m3 pm__99]; cbv beta zeta. PM_all99. reflexivity. Qed.
Ltac PM_sub100 t := let t := lazymatch (eval pattern (T5m3 nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__99) end in PM_sub99 t.
Ltac PM_all100 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__99_eq; PM_all99.
Definition pm__100 : axst := ltac2:(tb__ "0|0|
Sb0S67SbA2").
Lemma pm__100_eq : ltac2:(tb__ "0|1|
S0S2S15S22S20Z2M0A1SaS1eG0A2A3S33A3"). Proof. cbv delta [T5m3 pm__100]; cbv beta zeta. PM_all100. reflexivity. Qed.
Ltac PM_sub101 t := let t := lazymatch (eval pattern (T5m3 nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__100) end in PM_sub100 t.
Ltac PM_all101 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__100_eq; PM_all100.
Definition pm__101 : axst := ltac2:(tb__ "0|0|
Sb0S68SbA2").
Lemma pm__101_eq : ltac2:(tb__ "0|1|
S0S2S15S22S20Z3M0A1SaS1eG0A2A3S34A3"). Proof. cbv delta [T5m3 pm__101]; cbv beta zeta. PM_all101. reflexivity. Qed.
Ltac PM_sub102 t := let t := lazymatch (eval pattern (T5m3 nobjb (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__101) end in PM_sub101 t.
Ltac PM_all102 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__101_eq; PM_all101.
Definition pm__102 : axst := ltac2:(tb__ "0|0|
Sb0S69SbA2").
Lemma pm__102_eq : ltac2:(tb__ "0|1|
S0S2S15S22S20Z4M0A1SaS1eG0A2A3S35A3"). Proof. cbv delta [T5m3 pm__102]; cbv beta zeta. PM_all102. reflexivity. Qed.
Ltac PM_sub103 t := let t := lazymatch (eval pattern (T5m3 nobjb (T4b_i 4) (X5s X5bc 4)) in t) with ?P _ => eval cbv beta in (P pm__102) end in PM_sub102 t.
Ltac PM_all103 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__102_eq; PM_all102.
Definition pm__103 : axst := ltac2:(tb__ "0|0|
Sb0S6aSbA2").
Lemma pm__103_eq : ltac2:(tb__ "0|1|
S0S2ScS22S20Z1M0A1SaS1eG0A2A3S76A3"). Proof. cbv delta [T5d pm__103]; cbv beta zeta. PM_all103. reflexivity. Qed.
Ltac PM_sub104 t := let t := lazymatch (eval pattern (T5d nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__103) end in PM_sub103 t.
Ltac PM_all104 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__103_eq; PM_all103.
Definition pm__104 : axst := ltac2:(tb__ "0|0|
Sb0S33SbA2").
Lemma pm__104_eq : ltac2:(tb__ "0|1|
S0S2ScS22S20Z2M0A1SaS1eG0A2A3S77A3"). Proof. cbv delta [T5d pm__104]; cbv beta zeta. PM_all104. reflexivity. Qed.
Ltac PM_sub105 t := let t := lazymatch (eval pattern (T5d nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__104) end in PM_sub104 t.
Ltac PM_all105 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__104_eq; PM_all104.
Definition pm__105 : axst := ltac2:(tb__ "0|0|
Sb0S34SbA2").
Lemma pm__105_eq : ltac2:(tb__ "0|1|
S0S2ScS22S20Z3M0A1SaS1eG0A2A3S78A3"). Proof. cbv delta [T5d pm__105]; cbv beta zeta. PM_all105. reflexivity. Qed.
Ltac PM_sub106 t := let t := lazymatch (eval pattern (T5d nobjb (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__105) end in PM_sub105 t.
Ltac PM_all106 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__105_eq; PM_all105.
Definition pm__106 : axst := ltac2:(tb__ "0|0|
Sb0S35SbA2").
Lemma pm__106_eq : ltac2:(tb__ "0|1|
S0S2ScS22S20Z4M0A1SaS1eG0A2A3S79A3"). Proof. cbv delta [T5d pm__106]; cbv beta zeta. PM_all106. reflexivity. Qed.
Ltac PM_sub107 t := let t := lazymatch (eval pattern (T5d nobjb (T4b_i 4) (X5s X5bc 4)) in t) with ?P _ => eval cbv beta in (P pm__106) end in PM_sub106 t.
Ltac PM_all107 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__106_eq; PM_all106.
Definition pm__107 : axst := ltac:(let t := eval cbv delta [C5S] in (C5S X5bc) in let t := eval cbv beta zeta in t in let t := PM_sub107 t in exact t).
Lemma pm__107_eq : ltac2:(tb__ "0|0|
S0S2S1aS1eA1S7aA3"). Proof. cbv delta [C5S pm__107]; cbv beta zeta. PM_all107. reflexivity. Qed.
Ltac PM_sub108 t := let t := lazymatch (eval pattern (C5S X5bc) in t) with ?P _ => eval cbv beta in (P pm__107) end in PM_sub107 t.
Ltac PM_all108 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__107_eq; PM_all107.
Lemma WX5rb_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3SbfS3SdS1eR2A2A1A1Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma DX5rb_0 : ltac2:(tb__ "0|4|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0SabSa8Sa7Sa8Sb3Sb3A2M0A1M1Sa7Sb4A1M2A2M3A1SdbS3S19S1eA1A1S3SdS1eR2A2A1A2SadG3SacG1G2Sa6G0SacSb3Sb3Sc0SaeQ20SbaPc0A1A3Sb7R2A1A4Sa5G0A1A3Sa5Sb4A1A4A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL1b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd1S3SdS1eR2A2A1SbSb7Nee0A1A3A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL2b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd1S3S16S1eR2A2A1Sa9SbA1Sb7N8e0A1A3A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL3b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd1S3S17S1eR2A2A1Sa9Sa9SbA1A1Sb7N840A1A3A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL4b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd1S3S18S1eR2A2A1Sa9Sa9Sa9SbA1A1A1Sb7N48A1A3A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HERb_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0SabSa7Sb5A1M0A1Se7SaS1eR2A2SccR2A1S26R2A1A3SadG0S28R2A1A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HT4b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0S2Se8S26R2A1SccR2A1ScdR2A1SaS1eR2A2S28R2A1A5S20R2A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XX4b_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa7Sa8Sb3Sb3A2M0A1S5SaS1eR2A2A1Sa5G0A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma FBX4b_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc8Sb4SbcSb9S3SaS1eR2A2A1M0A1A1Sb6G0A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Hchk4b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Se6SaS1eR2A2SccR2A1S26R2A1S28R2A1Sa6S2ScdR2A1Sa5S2A1A3A5Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma NX4b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa2Sb9S3SaS1eR2A2A1A1Sb9S3S1eA1A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma WG10b_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sb3Sd6S26R2A1PaM0A2SbdSd9SbaG0A1Sb7N8e0A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG15b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sb3Sd6S26R2A1PfA2Sb7N600A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG12b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sb3Sd6S26R2A1PcA2SbdSd9SbaPaA1Sb7N840A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FAM4b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc8Sb5S1cU2Sd5S72A3S28R2A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NEWOb_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa7Sb5A1Se3S3SccR2A1A1S3ScdR2A1A1A2Sa5Sb5A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XPostb_0 : ltac2:(tb__ "0|1|
Sa1S0Sa7Sa8Sb3Sb3A2M0A1S5ScdR1A1A1Sa5G0A1A3Fsz;"). Proof. intros sz. reflexivity. Qed.
Lemma FBT4b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc8Sb4SbcSb9S3S20R2A1A1A1A1Sb6S3SaS1eR2A2A1A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XT4b_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa7Sa8Sb3Sb3A2M0A1S5S20R2A1A1Sa5G0A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RB1b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd2S3SfS20R2A1SaS1eR2A2A2A1U0A2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma RB2b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd2S3S10S20R2A1SaS1eR2A2A2A1U1A2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma PERM_ndb_0 : ltac2:(tb__ "0|0|
S0Sa3ScfSeS22A1A1Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_ltb_0 : ltac2:(tb__ "0|0|
S0Sa3Sc8SaaSaaSefR1S22A2Li;SeS22A1A3Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_covb_0 : ltac2:(tb__ "0|0|
S0Sa3Sc8SaaSaaScbSaaSeeR1A1SeS22A1A3Li;Se1U0S22A2A3Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_lenb_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0SaaSafSb5SbbS3S11S20R2A1SaS1eR2A2A2A1A1A2S22A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG1b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd0S3S12S22S20R2A1SaS1eR2A2A3A1SbA2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG2b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd0S3S13S22S20R2A1SaS1eR2A2A3A1SbA2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG3b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd0S3S14S22S20R2A1SaS1eR2A2A3A1SbA2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG4b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd0S3S15S22S20R2A1SaS1eR2A2A3A1SbA2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma ENT5b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3S6ScS22S20R2A1SaS1eR2A2A3S32S6cR2A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sdb_i]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SID5b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sd8S6cR2A1VGS0;A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sdb_i]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma R4covb_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3S1bSb6S3ScS22S20R2A1SaS1eR2A2A3A1M0A1S28R2A1SbbG0A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.

End INST.
End SpineMallocSec5IW2.

(* [comment removed for export] *)
Module SpineMallocSec5ILW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "entailsA"; "leafA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS"; "X5s"; "WI"; "T5d"; "X5r"; "permS"; "T50"; "T5a"; "T5b"; "T5c"; "T5m1"; "T5m2"; "T5m3"; "X5a"; "X5b"; "X5c"; "X5f"; "C5S"; "coveredbL"; "in_fambS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineMallocSec5ILW2.INST"; "X5ac"; "X5bc"; "T4a_i"; "T4b_i"; "nobja"; "nobjb"; "U4ac"; "U4bc"; "s4a_i"; "s4b_i"; "R4a_i"; "R4b_i"; "pm__29"; "pm__30"; "pm__31"; "pm__32"; "pm__83"; "pm__84"; "pm__85"; "pm__86"; "C5ac"; "C5bc"; "pm__100"; "pm__101"; "pm__102"; "pm__17"; "pm__18"; "pm__19"; "pm__20"; "pm__21"; "pm__22"; "pm__23"; "pm__24"; "pm__25"; "pm__26"; "pm__27"; "pm__28"; "pm__33"; "pm__34"; "pm__35"; "pm__36"; "pm__37"; "pm__38"; "pm__39"; "pm__40"; "pm__41"; "pm__42"; "pm__43"; "pm__44"; "pm__45"; "pm__46"; "pm__47"; "pm__48"; "pm__71"; "pm__72"; "pm__73"; "pm__74"; "pm__75"; "pm__76"; "pm__77"; "pm__78"; "pm__79"; "pm__80"; "pm__81"; "pm__82"; "pm__87"; "pm__88"; "pm__89"; "pm__90"; "pm__91"; "pm__92"; "pm__93"; "pm__94"; "pm__95"; "pm__96"; "pm__97"; "pm__98"; "pm__99"; "sda_i"; "sdb_i"; "CPa1"; "CPa2"; "CPb1"; "CPb2"; "EXoa"; "EXob"; "pm__0"; "pm__1"; "pm__10"; "pm__103"; "pm__104"; "pm__105"; "pm__106"; "pm__107"; "pm__11"; "pm__12"; "pm__13"; "pm__14"; "pm__15"; "pm__16"; "pm__2"; "pm__3"; "pm__4"; "pm__49"; "pm__5"; "pm__50"; "pm__51"; "pm__52"; "pm__53"; "pm__54"; "pm__55"; "pm__56"; "pm__57"; "pm__58"; "pm__59"; "pm__6"; "pm__60"; "pm__61"; "pm__62"; "pm__63"; "pm__64"; "pm__65"; "pm__66"; "pm__67"; "pm__68"; "pm__69"; "pm__7"; "pm__70"; "pm__8"; "pm__9"; "run5a"; "run5b"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "cons"; "list"; "prod"; "S"; "nat"; "option"; "pair"; "Some"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "omrg"; "oreb"; "F_call"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "ss_facts"; "SLit"; "sstate"; "ss_next"; "SVar"; "ss_objs"; "sprop_below"; "SAlu"; "SPUle"; "swf"; "SExt"; "SPBranch"; "SPNot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST"; "isSome"; "O_1"; "O_2"; "O_blk"; "O_w"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3ILW2"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "wsub_id_below"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3";
"state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU"; "DPENT"; "F_g4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4ILW2"; "T4ac"; "T4bc"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "V_NCH"; "V_NRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4ILW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSec6.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

Lemma by_cases12 : ltac2:(tb__ "0|2|
Sa1OF_;R1Z1M0A1R2Z2A1R3Z3A1R4Z4M1A1Sa1S1S8G0R1A2S8R1G1A2A2R7R2A1F_;Fsz;F_;F_;F_;F_;FP;").
Proof. intros P H1 H2 H3 H4 sz Hsz. assert (E : sz = 1 \/ sz = 2 \/ sz = 3 \/ sz = 4) by lia. destruct E as [-> | [-> | [-> | ->]]]; assumption. Qed.
Definition gP (o : option (wsub * list sobj * axst)) : wsub * list sobj * axst := ltac2:(tb__ "0|4|
SabSa8Sa8Sd7Sa7Sb5A1M0A2S2A2M1A1G1Lo;Vo;G1R1Lx;SacSa8Sa7Sa8Sa2Sb3A2M2A1M3G0A2S2SacG3G0Sa5G2A1Sa5Sb5A1A4SccZ0A1A4Xabx2").
Lemma Htmax_0 : 1 <= tmax <= SZMAX.
Proof. unfold SZMAX. subst tmax. lia. Qed.

Definition U4ac : axst := Eval vm_compute in (U4p nx0 T4ac).
Lemma WU4a_0 : ltac2:(tb__ "0|0|
S0Sa3SbfS3S23A1A1Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DU4a_0 : ltac2:(tb__ "0|4|
S0SabSa8Sa7Sa8Sb3Sb3A2M0A1M1Sa7Sb4A1M2A2M3A1SdbS3SdfA1S3S23A1A2SadG3SacG1G2Sa5G0A1SddSd5A1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXU4a_0 : ltac2:(tb__ "0|0|
S0Sa2Sb9S3S23A1A1Sb9S3SdfA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HU4a_0 : ltac2:(tb__ "0|0|
S0S2S4SdfS3S23A1A2S23A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run5a : option (list leafA) := Eval vm_compute in (runT5 U4ac).
Lemma run5a__runeq : ltac2:(tb__ "0|1|
S0Sa7SabSa7S7A1A1M0A1Se5SdeUfa0Sa6Sa1SdcSa5Sa1A1A3Sa6S2S23Sa5S2A1A3A4Sa6G0S9fSa5G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run5a]). Qed.
Definition X5ac : axst := Eval vm_compute in (leafS 0 run5a).
Lemma Cert5a_0 : ltac2:(tb__ "0|1|
S0Sa3Se4SdeUfa0Sa6Sa1SdcSa5Sa1A1A3VGS0;Sa6S2S23Sa5S2A1M0A3Sa6S2S1dG0A3A6Sa4A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [DPENT] GS0 [U4ac] [X5ac] [run5a]); [exact run5a__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition C5ac : axst := Eval vm_compute in (C5S X5ac).

Definition CPa1 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5ac 1) 1)).
Definition CPa2 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5ac 2) 2)).
Definition CPa (sz : Z) : wsub * list sobj * axst := ltac2:(tb__ "0|0|
Sa3Sa8Sa8Sd7Sa7Sb5A1A2S2A2L_;S9Vsz;Z1A2S6dS6eXa3x2").
Definition s4a_i (sz : Z) : wsub := fst (fst (CPa sz)).
Definition R4a_i (sz : Z) : list sobj := snd (fst (CPa sz)).
Definition T4a_i (sz : Z) : axst := snd (CPa sz).
Definition nobja : nat := Eval vm_compute in (length (ss_objs (ax_S (T5b (T4a_i 1) (X5s X5ac 1))))).
Definition sda_i (sz : Z) : wsub := ltac2:(tb__ "0|0|
Se2VGS0;S3ScS21S1fVsz;A1SaS1dVsz;A2A3A1S3S31A1A3").
Definition EXoa : list sobj := ltac2:(tb__ "0|0|
Sa6Sb5Sc5Sd5A1Sa6Sb5Sc4Sd5A1Sa6Sb5Sc6Sa5Sb5A1A3A3A3").

Lemma NXEa_0 : ltac2:(tb__ "0|0|
S0Sa3Sf0VGS0;Sb9S3S1dA1A1A2Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBEa_0 : ltac2:(tb__ "0|0|
S0Sa3Sc8Sb4SbcSb9S3S1dA1A1A1Sb2A3Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XE5a_0 : ax_X X5ac = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F192a_0 : ltac2:(tb__ "0|1|
Sc9Sb4Sa6Sb4SbeSb7Z1A1SbaPc0A1M0A2Sa6Sb4SbeG0Sb7Vtmax;A1A2Sa5Sb4A1A3A3Sb6S3S1dA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FDEPa_0 : ltac2:(tb__ "0|0|
Sc9Sb4SecSebA1Sb6S3S1dA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FUNWa_0 : ltac2:(tb__ "0|0|
Sc9Sb4SedVW;Vst;A2Sb6S3S1dA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FXBa_0 : ltac2:(tb__ "0|0|
ScaSb4Sc1SdaSbaSe9A1SbaSeaA1A3Sb6S3S1dA1A1A3"). Proof. apply In_of_inclb. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Ltac PM_sub0 t := t.
Ltac PM_all0 := idtac.
Definition pm__0 : axst := ltac:(let t := eval cbv delta [X5f] in (X5f X5ac) in let t := eval cbv beta zeta in t in let t := PM_sub0 t in exact t).
Lemma pm__0_eq : ltac2:(tb__ "0|0|
S0S2S19S1dA1S73A3"). Proof. cbv delta [X5f pm__0]; cbv beta zeta. PM_all0. reflexivity. Qed.
Ltac PM_sub1 t := let t := lazymatch (eval pattern (X5f X5ac) in t) with ?P _ => eval cbv beta in (P pm__0) end in PM_sub0 t.
Ltac PM_all1 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__0_eq; PM_all0.
Definition pm__1 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub1 t in exact t).
Lemma pm__1_eq : ltac2:(tb__ "0|0|
S0S2SdS1dZ1A2S74A3"). Proof. cbv delta [X5r pm__1]; cbv beta zeta. PM_all1. reflexivity. Qed.
Ltac PM_sub2 t := let t := lazymatch (eval pattern (X5r X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__1) end in PM_sub1 t.
Ltac PM_all2 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__1_eq; PM_all1.
Definition pm__2 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub2 t in exact t).
Lemma pm__2_eq : ltac2:(tb__ "0|0|
S0S2SdS1dZ2A2S81A3"). Proof. cbv delta [X5r pm__2]; cbv beta zeta. PM_all2. reflexivity. Qed.
Ltac PM_sub3 t := let t := lazymatch (eval pattern (X5r X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__2) end in PM_sub2 t.
Ltac PM_all3 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__2_eq; PM_all2.
Definition pm__3 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5ac 3) in let t := eval cbv beta zeta in t in let t := PM_sub3 t in exact t).
Lemma pm__3_eq : ltac2:(tb__ "0|0|
S0S2SdS1dZ3A2S82A3"). Proof. cbv delta [X5r pm__3]; cbv beta zeta. PM_all3. reflexivity. Qed.
Ltac PM_sub4 t := let t := lazymatch (eval pattern (X5r X5ac 3) in t) with ?P _ => eval cbv beta in (P pm__3) end in PM_sub3 t.
Ltac PM_all4 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__3_eq; PM_all3.
Definition pm__4 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5ac 4) in let t := eval cbv beta zeta in t in let t := PM_sub4 t in exact t).
Lemma pm__4_eq : ltac2:(tb__ "0|0|
S0S2SdS1dZ4A2S83A3"). Proof. cbv delta [X5r pm__4]; cbv beta zeta. PM_all4. reflexivity. Qed.
Ltac PM_sub5 t := let t := lazymatch (eval pattern (X5r X5ac 4) in t) with ?P _ => eval cbv beta in (P pm__4) end in PM_sub4 t.
Ltac PM_all5 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__4_eq; PM_all4.
Definition pm__5 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub5 t in exact t).
Lemma pm__5_eq : ltac2:(tb__ "0|0|
S0S2S16S1dZ1A2S85A3"). Proof. cbv delta [X5a pm__5]; cbv beta zeta. PM_all5. reflexivity. Qed.
Ltac PM_sub6 t := let t := lazymatch (eval pattern (X5a X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__5) end in PM_sub5 t.
Ltac PM_all6 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__5_eq; PM_all5.
Definition pm__6 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub6 t in exact t).
Lemma pm__6_eq : ltac2:(tb__ "0|0|
S0S2S16S1dZ2A2S90A3"). Proof. cbv delta [X5a pm__6]; cbv beta zeta. PM_all6. reflexivity. Qed.
Ltac PM_sub7 t := let t := lazymatch (eval pattern (X5a X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__6) end in PM_sub6 t.
Ltac PM_all7 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__6_eq; PM_all6.
Definition pm__7 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5ac 3) in let t := eval cbv beta zeta in t in let t := PM_sub7 t in exact t).
Lemma pm__7_eq : ltac2:(tb__ "0|0|
S0S2S16S1dZ3A2S9bA3"). Proof. cbv delta [X5a pm__7]; cbv beta zeta. PM_all7. reflexivity. Qed.
Ltac PM_sub8 t := let t := lazymatch (eval pattern (X5a X5ac 3) in t) with ?P _ => eval cbv beta in (P pm__7) end in PM_sub7 t.
Ltac PM_all8 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__7_eq; PM_all7.
Definition pm__8 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5ac 4) in let t := eval cbv beta zeta in t in let t := PM_sub8 t in exact t).
Lemma pm__8_eq : ltac2:(tb__ "0|0|
S0S2S16S1dZ4A2S9dA3"). Proof. cbv delta [X5a pm__8]; cbv beta zeta. PM_all8. reflexivity. Qed.
Ltac PM_sub9 t := let t := lazymatch (eval pattern (X5a X5ac 4) in t) with ?P _ => eval cbv beta in (P pm__8) end in PM_sub8 t.
Ltac PM_all9 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__8_eq; PM_all8.
Definition pm__9 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub9 t in exact t).
Lemma pm__9_eq : ltac2:(tb__ "0|0|
S0S2S17S1dZ1A2S9eA3"). Proof. cbv delta [X5b pm__9]; cbv beta zeta. PM_all9. reflexivity. Qed.
Ltac PM_sub10 t := let t := lazymatch (eval pattern (X5b X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__9) end in PM_sub9 t.
Ltac PM_all10 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__9_eq; PM_all9.
Definition pm__10 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub10 t in exact t).
Lemma pm__10_eq : ltac2:(tb__ "0|0|
S0S2S17S1dZ2A2S75A3"). Proof. cbv delta [X5b pm__10]; cbv beta zeta. PM_all10. reflexivity. Qed.
Ltac PM_sub11 t := let t := lazymatch (eval pattern (X5b X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__10) end in PM_sub10 t.
Ltac PM_all11 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__10_eq; PM_all10.
Definition pm__11 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5ac 3) in let t := eval cbv beta zeta in t in let t := PM_sub11 t in exact t).
Lemma pm__11_eq : ltac2:(tb__ "0|0|
S0S2S17S1dZ3A2S7bA3"). Proof. cbv delta [X5b pm__11]; cbv beta zeta. PM_all11. reflexivity. Qed.
Ltac PM_sub12 t := let t := lazymatch (eval pattern (X5b X5ac 3) in t) with ?P _ => eval cbv beta in (P pm__11) end in PM_sub11 t.
Ltac PM_all12 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__11_eq; PM_all11.
Definition pm__12 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5ac 4) in let t := eval cbv beta zeta in t in let t := PM_sub12 t in exact t).
Lemma pm__12_eq : ltac2:(tb__ "0|0|
S0S2S17S1dZ4A2S7cA3"). Proof. cbv delta [X5b pm__12]; cbv beta zeta. PM_all12. reflexivity. Qed.
Ltac PM_sub13 t := let t := lazymatch (eval pattern (X5b X5ac 4) in t) with ?P _ => eval cbv beta in (P pm__12) end in PM_sub12 t.
Ltac PM_all13 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__12_eq; PM_all12.
Definition pm__13 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub13 t in exact t).
Lemma pm__13_eq : ltac2:(tb__ "0|0|
S0S2S18S1dZ1A2S7dA3"). Proof. cbv delta [X5c pm__13]; cbv beta zeta. PM_all13. reflexivity. Qed.
Ltac PM_sub14 t := let t := lazymatch (eval pattern (X5c X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__13) end in PM_sub13 t.
Ltac PM_all14 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__13_eq; PM_all13.
Definition pm__14 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub14 t in exact t).
Lemma pm__14_eq : ltac2:(tb__ "0|0|
S0S2S18S1dZ2A2S7eA3"). Proof. cbv delta [X5c pm__14]; cbv beta zeta. PM_all14. reflexivity. Qed.
Ltac PM_sub15 t := let t := lazymatch (eval pattern (X5c X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__14) end in PM_sub14 t.
Ltac PM_all15 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__14_eq; PM_all14.
Definition pm__15 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5ac 3) in let t := eval cbv beta zeta in t in let t := PM_sub15 t in exact t).
Lemma pm__15_eq : ltac2:(tb__ "0|0|
S0S2S18S1dZ3A2S7fA3"). Proof. cbv delta [X5c pm__15]; cbv beta zeta. PM_all15. reflexivity. Qed.
Ltac PM_sub16 t := let t := lazymatch (eval pattern (X5c X5ac 3) in t) with ?P _ => eval cbv beta in (P pm__15) end in PM_sub15 t.
Ltac PM_all16 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__15_eq; PM_all15.
Definition pm__16 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5ac 4) in let t := eval cbv beta zeta in t in let t := PM_sub16 t in exact t).
Lemma pm__16_eq : ltac2:(tb__ "0|0|
S0S2S18S1dZ4A2S80A3"). Proof. cbv delta [X5c pm__16]; cbv beta zeta. PM_all16. reflexivity. Qed.
Ltac PM_sub17 t := let t := lazymatch (eval pattern (X5c X5ac 4) in t) with ?P _ => eval cbv beta in (P pm__16) end in PM_sub16 t.
Ltac PM_all17 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__16_eq; PM_all16.
Definition pm__17 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5ac 1) in let t := eval cbv beta zeta in t in let t := PM_sub17 t in exact t).
Lemma pm__17_eq : ltac2:(tb__ "0|0|
S0S2SaS1dZ1A2S36A3"). Proof. cbv delta [X5s pm__17]; cbv beta zeta. PM_all17. reflexivity. Qed.
Ltac PM_sub18 t := let t := lazymatch (eval pattern (X5s X5ac 1) in t) with ?P _ => eval cbv beta in (P pm__17) end in PM_sub17 t.
Ltac PM_all18 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__17_eq; PM_all17.
Definition pm__18 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5ac 2) in let t := eval cbv beta zeta in t in let t := PM_sub18 t in exact t).
Lemma pm__18_eq : ltac2:(tb__ "0|0|
S0S2SaS1dZ2A2S37A3"). Proof. cbv delta [X5s pm__18]; cbv beta zeta. PM_all18. reflexivity. Qed.
Ltac PM_sub19 t := let t := lazymatch (eval pattern (X5s X5ac 2) in t) with ?P _ => eval cbv beta in (P pm__18) end in PM_sub18 t.
Ltac PM_all19 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__18_eq; PM_all18.
Definition pm__19 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5ac 3) in let t := eval cbv beta zeta in t in let t := PM_sub19 t in exact t).
Lemma pm__19_eq : ltac2:(tb__ "0|0|
S0S2SaS1dZ3A2S38A3"). Proof. cbv delta [X5s pm__19]; cbv beta zeta. PM_all19. reflexivity. Qed.
Ltac PM_sub20 t := let t := lazymatch (eval pattern (X5s X5ac 3) in t) with ?P _ => eval cbv beta in (P pm__19) end in PM_sub19 t.
Ltac PM_all20 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__19_eq; PM_all19.
Definition pm__20 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5ac 4) in let t := eval cbv beta zeta in t in let t := PM_sub20 t in exact t).
Lemma pm__20_eq : ltac2:(tb__ "0|0|
S0S2SaS1dZ4A2S39A3"). Proof. cbv delta [X5s pm__20]; cbv beta zeta. PM_all20. reflexivity. Qed.
Ltac PM_sub21 t := let t := lazymatch (eval pattern (X5s X5ac 4) in t) with ?P _ => eval cbv beta in (P pm__20) end in PM_sub20 t.
Ltac PM_all21 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__20_eq; PM_all20.
Definition pm__21 : axst := ltac2:(tb__ "0|0|
Sd4S1fZ1A1Sb6S3S36A1A1A2").
Lemma pm__21_eq : ltac2:(tb__ "0|1|
S0S2SfS1fZ1M0A1SaS1dG0A2A2S3aA3"). Proof. cbv delta [T50 pm__21]; cbv beta zeta. PM_all21. reflexivity. Qed.
Ltac PM_sub22 t := let t := lazymatch (eval pattern (T50 (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__21) end in PM_sub21 t.
Ltac PM_all22 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__21_eq; PM_all21.
Definition pm__22 : axst := ltac2:(tb__ "0|0|
Sd4S1fZ2A1Sb6S3S37A1A1A2").
Lemma pm__22_eq : ltac2:(tb__ "0|1|
S0S2SfS1fZ2M0A1SaS1dG0A2A2S3bA3"). Proof. cbv delta [T50 pm__22]; cbv beta zeta. PM_all22. reflexivity. Qed.
Ltac PM_sub23 t := let t := lazymatch (eval pattern (T50 (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__22) end in PM_sub22 t.
Ltac PM_all23 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__22_eq; PM_all22.
Definition pm__23 : axst := ltac2:(tb__ "0|0|
Sd4S1fZ3A1Sb6S3S38A1A1A2").
Lemma pm__23_eq : ltac2:(tb__ "0|1|
S0S2SfS1fZ3M0A1SaS1dG0A2A2S3cA3"). Proof. cbv delta [T50 pm__23]; cbv beta zeta. PM_all23. reflexivity. Qed.
Ltac PM_sub24 t := let t := lazymatch (eval pattern (T50 (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__23) end in PM_sub23 t.
Ltac PM_all24 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__23_eq; PM_all23.
Definition pm__24 : axst := ltac2:(tb__ "0|0|
Sd4S1fZ4A1Sb6S3S39A1A1A2").
Lemma pm__24_eq : ltac2:(tb__ "0|1|
S0S2SfS1fZ4M0A1SaS1dG0A2A2S3dA3"). Proof. cbv delta [T50 pm__24]; cbv beta zeta. PM_all24. reflexivity. Qed.
Ltac PM_sub25 t := let t := lazymatch (eval pattern (T50 (T4a_i 4) (X5s X5ac 4)) in t) with ?P _ => eval cbv beta in (P pm__24) end in PM_sub24 t.
Ltac PM_all25 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__24_eq; PM_all24.
Definition pm__25 : axst := ltac2:(tb__ "0|0|
Sb1S3aU0A2").
Lemma pm__25_eq : ltac2:(tb__ "0|1|
S0S2S10S1fZ1M0A1SaS1dG0A2A2S3eA3"). Proof. cbv delta [T5a pm__25]; cbv beta zeta. PM_all25. reflexivity. Qed.
Ltac PM_sub26 t := let t := lazymatch (eval pattern (T5a (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__25) end in PM_sub25 t.
Ltac PM_all26 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__25_eq; PM_all25.
Definition pm__26 : axst := ltac2:(tb__ "0|0|
Sb1S3bU0A2").
Lemma pm__26_eq : ltac2:(tb__ "0|1|
S0S2S10S1fZ2M0A1SaS1dG0A2A2S3fA3"). Proof. cbv delta [T5a pm__26]; cbv beta zeta. PM_all26. reflexivity. Qed.
Ltac PM_sub27 t := let t := lazymatch (eval pattern (T5a (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__26) end in PM_sub26 t.
Ltac PM_all27 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__26_eq; PM_all26.
Definition pm__27 : axst := ltac2:(tb__ "0|0|
Sb1S3cU0A2").
Lemma pm__27_eq : ltac2:(tb__ "0|1|
S0S2S10S1fZ3M0A1SaS1dG0A2A2S40A3"). Proof. cbv delta [T5a pm__27]; cbv beta zeta. PM_all27. reflexivity. Qed.
Ltac PM_sub28 t := let t := lazymatch (eval pattern (T5a (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__27) end in PM_sub27 t.
Ltac PM_all28 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__27_eq; PM_all27.
Definition pm__28 : axst := ltac2:(tb__ "0|0|
Sb1S3dU0A2").
Lemma pm__28_eq : ltac2:(tb__ "0|1|
S0S2S10S1fZ4M0A1SaS1dG0A2A2S41A3"). Proof. cbv delta [T5a pm__28]; cbv beta zeta. PM_all28. reflexivity. Qed.
Ltac PM_sub29 t := let t := lazymatch (eval pattern (T5a (T4a_i 4) (X5s X5ac 4)) in t) with ?P _ => eval cbv beta in (P pm__28) end in PM_sub28 t.
Ltac PM_all29 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__28_eq; PM_all28.
Definition pm__29 : axst := ltac2:(tb__ "0|0|
Sb1S3eU1A2").
Lemma pm__29_eq : ltac2:(tb__ "0|1|
S0S2S11S1fZ1M0A1SaS1dG0A2A2S29A3"). Proof. cbv delta [T5b pm__29]; cbv beta zeta. PM_all29. reflexivity. Qed.
Ltac PM_sub30 t := let t := lazymatch (eval pattern (T5b (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__29) end in PM_sub29 t.
Ltac PM_all30 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__29_eq; PM_all29.
Definition pm__30 : axst := ltac2:(tb__ "0|0|
Sb1S3fU1A2").
Lemma pm__30_eq : ltac2:(tb__ "0|1|
S0S2S11S1fZ2M0A1SaS1dG0A2A2S2aA3"). Proof. cbv delta [T5b pm__30]; cbv beta zeta. PM_all30. reflexivity. Qed.
Ltac PM_sub31 t := let t := lazymatch (eval pattern (T5b (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__30) end in PM_sub30 t.
Ltac PM_all31 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__30_eq; PM_all30.
Definition pm__31 : axst := ltac2:(tb__ "0|0|
Sb1S40U1A2").
Lemma pm__31_eq : ltac2:(tb__ "0|1|
S0S2S11S1fZ3M0A1SaS1dG0A2A2S2bA3"). Proof. cbv delta [T5b pm__31]; cbv beta zeta. PM_all31. reflexivity. Qed.
Ltac PM_sub32 t := let t := lazymatch (eval pattern (T5b (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__31) end in PM_sub31 t.
Ltac PM_all32 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__31_eq; PM_all31.
Definition pm__32 : axst := ltac2:(tb__ "0|0|
Sb1S41U1A2").
Lemma pm__32_eq : ltac2:(tb__ "0|1|
S0S2S11S1fZ4M0A1SaS1dG0A2A2S2cA3"). Proof. cbv delta [T5b pm__32]; cbv beta zeta. PM_all32. reflexivity. Qed.
Ltac PM_sub33 t := let t := lazymatch (eval pattern (T5b (T4a_i 4) (X5s X5ac 4)) in t) with ?P _ => eval cbv beta in (P pm__32) end in PM_sub32 t.
Ltac PM_all33 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__32_eq; PM_all32.
Definition pm__33 : axst := ltac2:(tb__ "0|1|
S4S29Sd3S3S29A1M0SceSbbG0A1SeS21A1A2A2A2").
Lemma pm__33_eq : ltac2:(tb__ "0|1|
S0S2S12S21S1fZ1M0A1SaS1dG0A2A3S42A3"). Proof. cbv delta [T5c pm__33]; cbv beta zeta. PM_all33. reflexivity. Qed.
Ltac PM_sub34 t := let t := lazymatch (eval pattern (T5c nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__33) end in PM_sub33 t.
Ltac PM_all34 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__33_eq; PM_all33.
Definition pm__34 : axst := ltac2:(tb__ "0|1|
S4S2aSd3S3S2aA1M0SceSbbG0A1SeS21A1A2A2A2").
Lemma pm__34_eq : ltac2:(tb__ "0|1|
S0S2S12S21S1fZ2M0A1SaS1dG0A2A3S43A3"). Proof. cbv delta [T5c pm__34]; cbv beta zeta. PM_all34. reflexivity. Qed.
Ltac PM_sub35 t := let t := lazymatch (eval pattern (T5c nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__34) end in PM_sub34 t.
Ltac PM_all35 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__34_eq; PM_all34.
Definition pm__35 : axst := ltac2:(tb__ "0|1|
S4S2bSd3S3S2bA1M0SceSbbG0A1SeS21A1A2A2A2").
Lemma pm__35_eq : ltac2:(tb__ "0|1|
S0S2S12S21S1fZ3M0A1SaS1dG0A2A3S44A3"). Proof. cbv delta [T5c pm__35]; cbv beta zeta. PM_all35. reflexivity. Qed.
Ltac PM_sub36 t := let t := lazymatch (eval pattern (T5c nobja (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__35) end in PM_sub35 t.
Ltac PM_all36 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__35_eq; PM_all35.
Definition pm__36 : axst := ltac2:(tb__ "0|1|
S4S2cSd3S3S2cA1M0SceSbbG0A1SeS21A1A2A2A2").
Lemma pm__36_eq : ltac2:(tb__ "0|1|
S0S2S12S21S1fZ4M0A1SaS1dG0A2A3S45A3"). Proof. cbv delta [T5c pm__36]; cbv beta zeta. PM_all36. reflexivity. Qed.
Ltac PM_sub37 t := let t := lazymatch (eval pattern (T5c nobja (T4a_i 4) (X5s X5ac 4)) in t) with ?P _ => eval cbv beta in (P pm__36) end in PM_sub36 t.
Ltac PM_all37 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__36_eq; PM_all36.
Definition pm__37 : axst := ltac2:(tb__ "0|0|
Sb0S42SbA2").
Lemma pm__37_eq : ltac2:(tb__ "0|1|
S0S2S13S21S1fZ1M0A1SaS1dG0A2A3S46A3"). Proof. cbv delta [T5m1 pm__37]; cbv beta zeta. PM_all37. reflexivity. Qed.
Ltac PM_sub38 t := let t := lazymatch (eval pattern (T5m1 nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__37) end in PM_sub37 t.
Ltac PM_all38 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__37_eq; PM_all37.
Definition pm__38 : axst := ltac2:(tb__ "0|0|
Sb0S43SbA2").
Lemma pm__38_eq : ltac2:(tb__ "0|1|
S0S2S13S21S1fZ2M0A1SaS1dG0A2A3S47A3"). Proof. cbv delta [T5m1 pm__38]; cbv beta zeta. PM_all38. reflexivity. Qed.
Ltac PM_sub39 t := let t := lazymatch (eval pattern (T5m1 nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__38) end in PM_sub38 t.
Ltac PM_all39 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__38_eq; PM_all38.
Definition pm__39 : axst := ltac2:(tb__ "0|0|
Sb0S44SbA2").
Lemma pm__39_eq : ltac2:(tb__ "0|1|
S0S2S13S21S1fZ3M0A1SaS1dG0A2A3S48A3"). Proof. cbv delta [T5m1 pm__39]; cbv beta zeta. PM_all39. reflexivity. Qed.
Ltac PM_sub40 t := let t := lazymatch (eval pattern (T5m1 nobja (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__39) end in PM_sub39 t.
Ltac PM_all40 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__39_eq; PM_all39.
Definition pm__40 : axst := ltac2:(tb__ "0|0|
Sb0S45SbA2").
Lemma pm__40_eq : ltac2:(tb__ "0|1|
S0S2S13S21S1fZ4M0A1SaS1dG0A2A3S49A3"). Proof. cbv delta [T5m1 pm__40]; cbv beta zeta. PM_all40. reflexivity. Qed.
Ltac PM_sub41 t := let t := lazymatch (eval pattern (T5m1 nobja (T4a_i 4) (X5s X5ac 4)) in t) with ?P _ => eval cbv beta in (P pm__40) end in PM_sub40 t.
Ltac PM_all41 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__40_eq; PM_all40.
Definition pm__41 : axst := ltac2:(tb__ "0|0|
Sb0S46SbA2").
Lemma pm__41_eq : ltac2:(tb__ "0|1|
S0S2S14S21S1fZ1M0A1SaS1dG0A2A3S4aA3"). Proof. cbv delta [T5m2 pm__41]; cbv beta zeta. PM_all41. reflexivity. Qed.
Ltac PM_sub42 t := let t := lazymatch (eval pattern (T5m2 nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__41) end in PM_sub41 t.
Ltac PM_all42 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__41_eq; PM_all41.
Definition pm__42 : axst := ltac2:(tb__ "0|0|
Sb0S47SbA2").
Lemma pm__42_eq : ltac2:(tb__ "0|1|
S0S2S14S21S1fZ2M0A1SaS1dG0A2A3S4bA3"). Proof. cbv delta [T5m2 pm__42]; cbv beta zeta. PM_all42. reflexivity. Qed.
Ltac PM_sub43 t := let t := lazymatch (eval pattern (T5m2 nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__42) end in PM_sub42 t.
Ltac PM_all43 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__42_eq; PM_all42.
Definition pm__43 : axst := ltac2:(tb__ "0|0|
Sb0S48SbA2").
Lemma pm__43_eq : ltac2:(tb__ "0|1|
S0S2S14S21S1fZ3M0A1SaS1dG0A2A3S4cA3"). Proof. cbv delta [T5m2 pm__43]; cbv beta zeta. PM_all43. reflexivity. Qed.
Ltac PM_sub44 t := let t := lazymatch (eval pattern (T5m2 nobja (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__43) end in PM_sub43 t.
Ltac PM_all44 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__43_eq; PM_all43.
Definition pm__44 : axst := ltac2:(tb__ "0|0|
Sb0S49SbA2").
Lemma pm__44_eq : ltac2:(tb__ "0|1|
S0S2S14S21S1fZ4M0A1SaS1dG0A2A3S4dA3"). Proof. cbv delta [T5m2 pm__44]; cbv beta zeta. PM_all44. reflexivity. Qed.
Ltac PM_sub45 t := let t := lazymatch (eval pattern (T5m2 nobja (T4a_i 4) (X5s X5ac 4)) in t) with ?P _ => eval cbv beta in (P pm__44) end in PM_sub44 t.
Ltac PM_all45 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__44_eq; PM_all44.
Definition pm__45 : axst := ltac2:(tb__ "0|0|
Sb0S4aSbA2").
Lemma pm__45_eq : ltac2:(tb__ "0|1|
S0S2S15S21S1fZ1M0A1SaS1dG0A2A3S4eA3"). Proof. cbv delta [T5m3 pm__45]; cbv beta zeta. PM_all45. reflexivity. Qed.
Ltac PM_sub46 t := let t := lazymatch (eval pattern (T5m3 nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__45) end in PM_sub45 t.
Ltac PM_all46 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__45_eq; PM_all45.
Definition pm__46 : axst := ltac2:(tb__ "0|0|
Sb0S4bSbA2").
Lemma pm__46_eq : ltac2:(tb__ "0|1|
S0S2S15S21S1fZ2M0A1SaS1dG0A2A3S4fA3"). Proof. cbv delta [T5m3 pm__46]; cbv beta zeta. PM_all46. reflexivity. Qed.
Ltac PM_sub47 t := let t := lazymatch (eval pattern (T5m3 nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__46) end in PM_sub46 t.
Ltac PM_all47 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__46_eq; PM_all46.
Definition pm__47 : axst := ltac2:(tb__ "0|0|
Sb0S4cSbA2").
Lemma pm__47_eq : ltac2:(tb__ "0|1|
S0S2S15S21S1fZ3M0A1SaS1dG0A2A3S50A3"). Proof. cbv delta [T5m3 pm__47]; cbv beta zeta. PM_all47. reflexivity. Qed.
Ltac PM_sub48 t := let t := lazymatch (eval pattern (T5m3 nobja (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__47) end in PM_sub47 t.
Ltac PM_all48 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__47_eq; PM_all47.
Definition pm__48 : axst := ltac2:(tb__ "0|0|
Sb0S4dSbA2").
Lemma pm__48_eq : ltac2:(tb__ "0|1|
S0S2S15S21S1fZ4M0A1SaS1dG0A2A3S51A3"). Proof. cbv delta [T5m3 pm__48]; cbv beta zeta. PM_all48. reflexivity. Qed.
Ltac PM_sub49 t := let t := lazymatch (eval pattern (T5m3 nobja (T4a_i 4) (X5s X5ac 4)) in t) with ?P _ => eval cbv beta in (P pm__48) end in PM_sub48 t.
Ltac PM_all49 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__48_eq; PM_all48.
Definition pm__49 : axst := ltac2:(tb__ "0|0|
Sb0S4eSbA2").
Lemma pm__49_eq : ltac2:(tb__ "0|1|
S0S2ScS21S1fZ1M0A1SaS1dG0A2A3S84A3"). Proof. cbv delta [T5d pm__49]; cbv beta zeta. PM_all49. reflexivity. Qed.
Ltac PM_sub50 t := let t := lazymatch (eval pattern (T5d nobja (T4a_i 1) (X5s X5ac 1)) in t) with ?P _ => eval cbv beta in (P pm__49) end in PM_sub49 t.
Ltac PM_all50 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__49_eq; PM_all49.
Definition pm__50 : axst := ltac2:(tb__ "0|0|
Sb0S4fSbA2").
Lemma pm__50_eq : ltac2:(tb__ "0|1|
S0S2ScS21S1fZ2M0A1SaS1dG0A2A3S86A3"). Proof. cbv delta [T5d pm__50]; cbv beta zeta. PM_all50. reflexivity. Qed.
Ltac PM_sub51 t := let t := lazymatch (eval pattern (T5d nobja (T4a_i 2) (X5s X5ac 2)) in t) with ?P _ => eval cbv beta in (P pm__50) end in PM_sub50 t.
Ltac PM_all51 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__50_eq; PM_all50.
Definition pm__51 : axst := ltac2:(tb__ "0|0|
Sb0S50SbA2").
Lemma pm__51_eq : ltac2:(tb__ "0|1|
S0S2ScS21S1fZ3M0A1SaS1dG0A2A3S87A3"). Proof. cbv delta [T5d pm__51]; cbv beta zeta. PM_all51. reflexivity. Qed.
Ltac PM_sub52 t := let t := lazymatch (eval pattern (T5d nobja (T4a_i 3) (X5s X5ac 3)) in t) with ?P _ => eval cbv beta in (P pm__51) end in PM_sub51 t.
Ltac PM_all52 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__51_eq; PM_all51.
Definition pm__52 : axst := ltac2:(tb__ "0|0|
Sb0S51SbA2").
Lemma pm__52_eq : ltac2:(tb__ "0|1|
S0S2ScS21S1fZ4M0A1SaS1dG0A2A3S88A3"). Proof. cbv delta [T5d pm__52]; cbv beta zeta. PM_all52. reflexivity. Qed.
Ltac PM_sub53 t := let t := lazymatch (eval pattern (T5d nobja (T4a_i 4) (X5s X5ac 4)) in t) with ?P _ => eval cbv beta in (P pm__52) end in PM_sub52 t.
Ltac PM_all53 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__52_eq; PM_all52.
Definition pm__53 : axst := ltac:(let t := eval cbv delta [C5S] in (C5S X5ac) in let t := eval cbv beta zeta in t in let t := PM_sub53 t in exact t).
Lemma pm__53_eq : ltac2:(tb__ "0|0|
S0S2S1aS1dA1S89A3"). Proof. cbv delta [C5S pm__53]; cbv beta zeta. PM_all53. reflexivity. Qed.
Ltac PM_sub54 t := let t := lazymatch (eval pattern (C5S X5ac) in t) with ?P _ => eval cbv beta in (P pm__53) end in PM_sub53 t.
Ltac PM_all54 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__53_eq; PM_all53.
Lemma WX5ra_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3SbfS3SdS1dR2A2A1A1Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma DX5ra_0 : ltac2:(tb__ "0|4|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0SabSa8Sa7Sa8Sb3Sb3A2M0A1M1Sa7Sb4A1M2A2M3A1SdbS3S19S1dA1A1S3SdS1dR2A2A1A2SadG3SacG1G2Sa6G0SacSb3Sb3Sc0SaeQ20SbaPc0A1A3Sb7R2A1A4Sa5G0A1A3Sa5Sb4A1A4A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL1a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd1S3SdS1dR2A2A1SbSb7Nee0A1A3A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL2a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd1S3S16S1dR2A2A1Sa9SbA1Sb7N8e0A1A3A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL3a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd1S3S17S1dR2A2A1Sa9Sa9SbA1A1Sb7N840A1A3A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL4a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd1S3S18S1dR2A2A1Sa9Sa9Sa9SbA1A1A1Sb7N48A1A3A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HERa_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0SabSa7Sb5A1M0A1Se7SaS1dR2A2SccR2A1S25R2A1A3SadG0S27R2A1A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HT4a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0S2Se8S25R2A1SccR2A1ScdR2A1SaS1dR2A2S27R2A1A5S1fR2A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XX4a_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa7Sa8Sb3Sb3A2M0A1S5SaS1dR2A2A1Sa5G0A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma FBX4a_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc8Sb4SbcSb9S3SaS1dR2A2A1M0A1A1Sb6G0A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Hchk4a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Se6SaS1dR2A2SccR2A1S25R2A1S27R2A1Sa6S2ScdR2A1Sa5S2A1A3A5Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma NX4a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa2Sb9S3SaS1dR2A2A1A1Sb9S3S1dA1A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma WG10a_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sb3Sd6S25R2A1PaM0A2SbdSd9SbaG0A1Sb7N8e0A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG15a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sb3Sd6S25R2A1PfA2Sb7N600A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG12a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sb3Sd6S25R2A1PcA2SbdSd9SbaPaA1Sb7N840A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FAM4a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc8Sb5S1cU2Sd5S71A3S27R2A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NEWOa_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa7Sb5A1Se3S3SccR2A1A1S3ScdR2A1A1A2Sa5Sb5A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XPosta_0 : ltac2:(tb__ "0|1|
Sa1S0Sa7Sa8Sb3Sb3A2M0A1S5ScdR1A1A1Sa5G0A1A3Fsz;"). Proof. intros sz. reflexivity. Qed.
Lemma FBT4a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc8Sb4SbcSb9S3S1fR2A1A1A1A1Sb6S3SaS1dR2A2A1A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XT4a_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa7Sa8Sb3Sb3A2M0A1S5S1fR2A1A1Sa5G0A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RB1a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd2S3SfS1fR2A1SaS1dR2A2A2A1U0A2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma RB2a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd2S3S10S1fR2A1SaS1dR2A2A2A1U1A2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma PERM_nda_0 : ltac2:(tb__ "0|0|
S0Sa3ScfSeS21A1A1Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_lta_0 : ltac2:(tb__ "0|0|
S0Sa3Sc8SaaSaaSefR1S21A2Li;SeS21A1A3Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_cova_0 : ltac2:(tb__ "0|0|
S0Sa3Sc8SaaSaaScbSaaSeeR1A1SeS21A1A3Li;Se1U0S21A2A3Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_lena_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0SaaSafSb5SbbS3S11S1fR2A1SaS1dR2A2A2A1A1A2S21A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG1a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd0S3S12S21S1fR2A1SaS1dR2A2A3A1SbA2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG2a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd0S3S13S21S1fR2A1SaS1dR2A2A3A1SbA2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG3a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd0S3S14S21S1fR2A1SaS1dR2A2A3A1SbA2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG4a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd0S3S15S21S1fR2A1SaS1dR2A2A3A1SbA2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma ENT5a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3S6ScS21S1fR2A1SaS1dR2A2A3S31S6bR2A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sda_i]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SID5a_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sd8S6bR2A1VGS0;A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sda_i]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma R4cova_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3S1bSb6S3ScS21S1fR2A1SaS1dR2A2A3A1M0A1S27R2A1SbbG0A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all54; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.

Definition U4bc : axst := Eval vm_compute in (U4p nx0 T4bc).
Lemma WU4b_0 : ltac2:(tb__ "0|0|
S0Sa3SbfS3S24A1A1Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DU4b_0 : ltac2:(tb__ "0|4|
S0SabSa8Sa7Sa8Sb3Sb3A2M0A1M1Sa7Sb4A1M2A2M3A1SdbS3Se0A1S3S24A1A2SadG3SacG1G2Sa5G0A1SddSd5A1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXU4b_0 : ltac2:(tb__ "0|0|
S0Sa2Sb9S3S24A1A1Sb9S3Se0A1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HU4b_0 : ltac2:(tb__ "0|0|
S0S2S4Se0S3S24A1A2S24A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run5b : option (list leafA) := Eval vm_compute in (runT5 U4bc).
Lemma run5b__runeq : ltac2:(tb__ "0|1|
S0Sa7SabSa7S7A1A1M0A1Se5SdeUfa0Sa6Sa1SdcSa5Sa1A1A3Sa6S2S24Sa5S2A1A3A4Sa6G0Sa0Sa5G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run5b]). Qed.
Definition X5bc : axst := Eval vm_compute in (leafS 0 run5b).
Lemma Cert5b_0 : ltac2:(tb__ "0|1|
S0Sa3Se4SdeUfa0Sa6Sa1SdcSa5Sa1A1A3VGS0;Sa6S2S24Sa5S2A1M0A3Sa6S2S1eG0A3A6Sa4A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [DPENT] GS0 [U4bc] [X5bc] [run5b]); [exact run5b__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition C5bc : axst := Eval vm_compute in (C5S X5bc).

Definition CPb1 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5bc 1) 1)).
Definition CPb2 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (X5s X5bc 2) 2)).
Definition CPb (sz : Z) : wsub * list sobj * axst := ltac2:(tb__ "0|0|
Sa3Sa8Sa8Sd7Sa7Sb5A1A2S2A2L_;S9Vsz;Z1A2S6fS70Xa3x2").
Definition s4b_i (sz : Z) : wsub := fst (fst (CPb sz)).
Definition R4b_i (sz : Z) : list sobj := snd (fst (CPb sz)).
Definition T4b_i (sz : Z) : axst := snd (CPb sz).
Definition nobjb : nat := Eval vm_compute in (length (ss_objs (ax_S (T5b (T4b_i 1) (X5s X5bc 1))))).
Definition sdb_i (sz : Z) : wsub := ltac2:(tb__ "0|0|
Se2VGS0;S3ScS22S20Vsz;A1SaS1eVsz;A2A3A1S3S32A1A3").
Definition EXob : list sobj := ltac2:(tb__ "0|0|
Sa6Sb5Sc5Sd5A1Sa6Sb5Sc4Sd5A1Sa6Sb5Sc7Sa5Sb5A1A3A3A3").

Lemma NXEb_0 : ltac2:(tb__ "0|0|
S0Sa3Sf0VGS0;Sb9S3S1eA1A1A2Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBEb_0 : ltac2:(tb__ "0|0|
S0Sa3Sc8Sb4SbcSb9S3S1eA1A1A1Sb2A3Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XE5b_0 : ax_X X5bc = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F192b_0 : ltac2:(tb__ "0|1|
Sc9Sb4Sa6Sb4SbeSb7Z1A1SbaPc0A1M0A2Sa6Sb4SbeG0Sb7Vtmax;A1A2Sa5Sb4A1A3A3Sb6S3S1eA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FDEPb_0 : ltac2:(tb__ "0|0|
Sc9Sb4SecSebA1Sb6S3S1eA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FUNWb_0 : ltac2:(tb__ "0|0|
Sc9Sb4SedVW;Vst;A2Sb6S3S1eA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FXBb_0 : ltac2:(tb__ "0|0|
ScaSb4Sc2Sc1SdaSbaSe9A1SbaSeaA1A3A1Sb6S3S1eA1A1A3"). Proof. apply In_of_inclb. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition pm__54 : axst := ltac:(let t := eval cbv delta [X5f] in (X5f X5bc) in let t := eval cbv beta zeta in t in let t := PM_sub54 t in exact t).
Lemma pm__54_eq : ltac2:(tb__ "0|0|
S0S2S19S1eA1S8aA3"). Proof. cbv delta [X5f pm__54]; cbv beta zeta. PM_all54. reflexivity. Qed.
Ltac PM_sub55 t := let t := lazymatch (eval pattern (X5f X5bc) in t) with ?P _ => eval cbv beta in (P pm__54) end in PM_sub54 t.
Ltac PM_all55 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__54_eq; PM_all54.
Definition pm__55 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub55 t in exact t).
Lemma pm__55_eq : ltac2:(tb__ "0|0|
S0S2SdS1eZ1A2S8bA3"). Proof. cbv delta [X5r pm__55]; cbv beta zeta. PM_all55. reflexivity. Qed.
Ltac PM_sub56 t := let t := lazymatch (eval pattern (X5r X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__55) end in PM_sub55 t.
Ltac PM_all56 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__55_eq; PM_all55.
Definition pm__56 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub56 t in exact t).
Lemma pm__56_eq : ltac2:(tb__ "0|0|
S0S2SdS1eZ2A2S8cA3"). Proof. cbv delta [X5r pm__56]; cbv beta zeta. PM_all56. reflexivity. Qed.
Ltac PM_sub57 t := let t := lazymatch (eval pattern (X5r X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__56) end in PM_sub56 t.
Ltac PM_all57 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__56_eq; PM_all56.
Definition pm__57 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5bc 3) in let t := eval cbv beta zeta in t in let t := PM_sub57 t in exact t).
Lemma pm__57_eq : ltac2:(tb__ "0|0|
S0S2SdS1eZ3A2S8dA3"). Proof. cbv delta [X5r pm__57]; cbv beta zeta. PM_all57. reflexivity. Qed.
Ltac PM_sub58 t := let t := lazymatch (eval pattern (X5r X5bc 3) in t) with ?P _ => eval cbv beta in (P pm__57) end in PM_sub57 t.
Ltac PM_all58 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__57_eq; PM_all57.
Definition pm__58 : axst := ltac:(let t := eval cbv delta [X5r] in (X5r X5bc 4) in let t := eval cbv beta zeta in t in let t := PM_sub58 t in exact t).
Lemma pm__58_eq : ltac2:(tb__ "0|0|
S0S2SdS1eZ4A2S8eA3"). Proof. cbv delta [X5r pm__58]; cbv beta zeta. PM_all58. reflexivity. Qed.
Ltac PM_sub59 t := let t := lazymatch (eval pattern (X5r X5bc 4) in t) with ?P _ => eval cbv beta in (P pm__58) end in PM_sub58 t.
Ltac PM_all59 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__58_eq; PM_all58.
Definition pm__59 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub59 t in exact t).
Lemma pm__59_eq : ltac2:(tb__ "0|0|
S0S2S16S1eZ1A2S8fA3"). Proof. cbv delta [X5a pm__59]; cbv beta zeta. PM_all59. reflexivity. Qed.
Ltac PM_sub60 t := let t := lazymatch (eval pattern (X5a X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__59) end in PM_sub59 t.
Ltac PM_all60 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__59_eq; PM_all59.
Definition pm__60 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub60 t in exact t).
Lemma pm__60_eq : ltac2:(tb__ "0|0|
S0S2S16S1eZ2A2S91A3"). Proof. cbv delta [X5a pm__60]; cbv beta zeta. PM_all60. reflexivity. Qed.
Ltac PM_sub61 t := let t := lazymatch (eval pattern (X5a X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__60) end in PM_sub60 t.
Ltac PM_all61 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__60_eq; PM_all60.
Definition pm__61 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5bc 3) in let t := eval cbv beta zeta in t in let t := PM_sub61 t in exact t).
Lemma pm__61_eq : ltac2:(tb__ "0|0|
S0S2S16S1eZ3A2S92A3"). Proof. cbv delta [X5a pm__61]; cbv beta zeta. PM_all61. reflexivity. Qed.
Ltac PM_sub62 t := let t := lazymatch (eval pattern (X5a X5bc 3) in t) with ?P _ => eval cbv beta in (P pm__61) end in PM_sub61 t.
Ltac PM_all62 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__61_eq; PM_all61.
Definition pm__62 : axst := ltac:(let t := eval cbv delta [X5a] in (X5a X5bc 4) in let t := eval cbv beta zeta in t in let t := PM_sub62 t in exact t).
Lemma pm__62_eq : ltac2:(tb__ "0|0|
S0S2S16S1eZ4A2S93A3"). Proof. cbv delta [X5a pm__62]; cbv beta zeta. PM_all62. reflexivity. Qed.
Ltac PM_sub63 t := let t := lazymatch (eval pattern (X5a X5bc 4) in t) with ?P _ => eval cbv beta in (P pm__62) end in PM_sub62 t.
Ltac PM_all63 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__62_eq; PM_all62.
Definition pm__63 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub63 t in exact t).
Lemma pm__63_eq : ltac2:(tb__ "0|0|
S0S2S17S1eZ1A2S94A3"). Proof. cbv delta [X5b pm__63]; cbv beta zeta. PM_all63. reflexivity. Qed.
Ltac PM_sub64 t := let t := lazymatch (eval pattern (X5b X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__63) end in PM_sub63 t.
Ltac PM_all64 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__63_eq; PM_all63.
Definition pm__64 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub64 t in exact t).
Lemma pm__64_eq : ltac2:(tb__ "0|0|
S0S2S17S1eZ2A2S95A3"). Proof. cbv delta [X5b pm__64]; cbv beta zeta. PM_all64. reflexivity. Qed.
Ltac PM_sub65 t := let t := lazymatch (eval pattern (X5b X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__64) end in PM_sub64 t.
Ltac PM_all65 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__64_eq; PM_all64.
Definition pm__65 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5bc 3) in let t := eval cbv beta zeta in t in let t := PM_sub65 t in exact t).
Lemma pm__65_eq : ltac2:(tb__ "0|0|
S0S2S17S1eZ3A2S96A3"). Proof. cbv delta [X5b pm__65]; cbv beta zeta. PM_all65. reflexivity. Qed.
Ltac PM_sub66 t := let t := lazymatch (eval pattern (X5b X5bc 3) in t) with ?P _ => eval cbv beta in (P pm__65) end in PM_sub65 t.
Ltac PM_all66 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__65_eq; PM_all65.
Definition pm__66 : axst := ltac:(let t := eval cbv delta [X5b] in (X5b X5bc 4) in let t := eval cbv beta zeta in t in let t := PM_sub66 t in exact t).
Lemma pm__66_eq : ltac2:(tb__ "0|0|
S0S2S17S1eZ4A2S97A3"). Proof. cbv delta [X5b pm__66]; cbv beta zeta. PM_all66. reflexivity. Qed.
Ltac PM_sub67 t := let t := lazymatch (eval pattern (X5b X5bc 4) in t) with ?P _ => eval cbv beta in (P pm__66) end in PM_sub66 t.
Ltac PM_all67 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__66_eq; PM_all66.
Definition pm__67 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub67 t in exact t).
Lemma pm__67_eq : ltac2:(tb__ "0|0|
S0S2S18S1eZ1A2S98A3"). Proof. cbv delta [X5c pm__67]; cbv beta zeta. PM_all67. reflexivity. Qed.
Ltac PM_sub68 t := let t := lazymatch (eval pattern (X5c X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__67) end in PM_sub67 t.
Ltac PM_all68 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__67_eq; PM_all67.
Definition pm__68 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub68 t in exact t).
Lemma pm__68_eq : ltac2:(tb__ "0|0|
S0S2S18S1eZ2A2S99A3"). Proof. cbv delta [X5c pm__68]; cbv beta zeta. PM_all68. reflexivity. Qed.
Ltac PM_sub69 t := let t := lazymatch (eval pattern (X5c X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__68) end in PM_sub68 t.
Ltac PM_all69 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__68_eq; PM_all68.
Definition pm__69 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5bc 3) in let t := eval cbv beta zeta in t in let t := PM_sub69 t in exact t).
Lemma pm__69_eq : ltac2:(tb__ "0|0|
S0S2S18S1eZ3A2S9aA3"). Proof. cbv delta [X5c pm__69]; cbv beta zeta. PM_all69. reflexivity. Qed.
Ltac PM_sub70 t := let t := lazymatch (eval pattern (X5c X5bc 3) in t) with ?P _ => eval cbv beta in (P pm__69) end in PM_sub69 t.
Ltac PM_all70 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__69_eq; PM_all69.
Definition pm__70 : axst := ltac:(let t := eval cbv delta [X5c] in (X5c X5bc 4) in let t := eval cbv beta zeta in t in let t := PM_sub70 t in exact t).
Lemma pm__70_eq : ltac2:(tb__ "0|0|
S0S2S18S1eZ4A2S9cA3"). Proof. cbv delta [X5c pm__70]; cbv beta zeta. PM_all70. reflexivity. Qed.
Ltac PM_sub71 t := let t := lazymatch (eval pattern (X5c X5bc 4) in t) with ?P _ => eval cbv beta in (P pm__70) end in PM_sub70 t.
Ltac PM_all71 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__70_eq; PM_all70.
Definition pm__71 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5bc 1) in let t := eval cbv beta zeta in t in let t := PM_sub71 t in exact t).
Lemma pm__71_eq : ltac2:(tb__ "0|0|
S0S2SaS1eZ1A2S52A3"). Proof. cbv delta [X5s pm__71]; cbv beta zeta. PM_all71. reflexivity. Qed.
Ltac PM_sub72 t := let t := lazymatch (eval pattern (X5s X5bc 1) in t) with ?P _ => eval cbv beta in (P pm__71) end in PM_sub71 t.
Ltac PM_all72 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__71_eq; PM_all71.
Definition pm__72 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5bc 2) in let t := eval cbv beta zeta in t in let t := PM_sub72 t in exact t).
Lemma pm__72_eq : ltac2:(tb__ "0|0|
S0S2SaS1eZ2A2S53A3"). Proof. cbv delta [X5s pm__72]; cbv beta zeta. PM_all72. reflexivity. Qed.
Ltac PM_sub73 t := let t := lazymatch (eval pattern (X5s X5bc 2) in t) with ?P _ => eval cbv beta in (P pm__72) end in PM_sub72 t.
Ltac PM_all73 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__72_eq; PM_all72.
Definition pm__73 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5bc 3) in let t := eval cbv beta zeta in t in let t := PM_sub73 t in exact t).
Lemma pm__73_eq : ltac2:(tb__ "0|0|
S0S2SaS1eZ3A2S54A3"). Proof. cbv delta [X5s pm__73]; cbv beta zeta. PM_all73. reflexivity. Qed.
Ltac PM_sub74 t := let t := lazymatch (eval pattern (X5s X5bc 3) in t) with ?P _ => eval cbv beta in (P pm__73) end in PM_sub73 t.
Ltac PM_all74 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__73_eq; PM_all73.
Definition pm__74 : axst := ltac:(let t := eval cbv delta [X5s] in (X5s X5bc 4) in let t := eval cbv beta zeta in t in let t := PM_sub74 t in exact t).
Lemma pm__74_eq : ltac2:(tb__ "0|0|
S0S2SaS1eZ4A2S55A3"). Proof. cbv delta [X5s pm__74]; cbv beta zeta. PM_all74. reflexivity. Qed.
Ltac PM_sub75 t := let t := lazymatch (eval pattern (X5s X5bc 4) in t) with ?P _ => eval cbv beta in (P pm__74) end in PM_sub74 t.
Ltac PM_all75 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__74_eq; PM_all74.
Definition pm__75 : axst := ltac2:(tb__ "0|0|
Sd4S20Z1A1Sb6S3S52A1A1A2").
Lemma pm__75_eq : ltac2:(tb__ "0|1|
S0S2SfS20Z1M0A1SaS1eG0A2A2S56A3"). Proof. cbv delta [T50 pm__75]; cbv beta zeta. PM_all75. reflexivity. Qed.
Ltac PM_sub76 t := let t := lazymatch (eval pattern (T50 (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__75) end in PM_sub75 t.
Ltac PM_all76 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__75_eq; PM_all75.
Definition pm__76 : axst := ltac2:(tb__ "0|0|
Sd4S20Z2A1Sb6S3S53A1A1A2").
Lemma pm__76_eq : ltac2:(tb__ "0|1|
S0S2SfS20Z2M0A1SaS1eG0A2A2S57A3"). Proof. cbv delta [T50 pm__76]; cbv beta zeta. PM_all76. reflexivity. Qed.
Ltac PM_sub77 t := let t := lazymatch (eval pattern (T50 (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__76) end in PM_sub76 t.
Ltac PM_all77 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__76_eq; PM_all76.
Definition pm__77 : axst := ltac2:(tb__ "0|0|
Sd4S20Z3A1Sb6S3S54A1A1A2").
Lemma pm__77_eq : ltac2:(tb__ "0|1|
S0S2SfS20Z3M0A1SaS1eG0A2A2S58A3"). Proof. cbv delta [T50 pm__77]; cbv beta zeta. PM_all77. reflexivity. Qed.
Ltac PM_sub78 t := let t := lazymatch (eval pattern (T50 (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__77) end in PM_sub77 t.
Ltac PM_all78 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__77_eq; PM_all77.
Definition pm__78 : axst := ltac2:(tb__ "0|0|
Sd4S20Z4A1Sb6S3S55A1A1A2").
Lemma pm__78_eq : ltac2:(tb__ "0|1|
S0S2SfS20Z4M0A1SaS1eG0A2A2S59A3"). Proof. cbv delta [T50 pm__78]; cbv beta zeta. PM_all78. reflexivity. Qed.
Ltac PM_sub79 t := let t := lazymatch (eval pattern (T50 (T4b_i 4) (X5s X5bc 4)) in t) with ?P _ => eval cbv beta in (P pm__78) end in PM_sub78 t.
Ltac PM_all79 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__78_eq; PM_all78.
Definition pm__79 : axst := ltac2:(tb__ "0|0|
Sb1S56U0A2").
Lemma pm__79_eq : ltac2:(tb__ "0|1|
S0S2S10S20Z1M0A1SaS1eG0A2A2S5aA3"). Proof. cbv delta [T5a pm__79]; cbv beta zeta. PM_all79. reflexivity. Qed.
Ltac PM_sub80 t := let t := lazymatch (eval pattern (T5a (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__79) end in PM_sub79 t.
Ltac PM_all80 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__79_eq; PM_all79.
Definition pm__80 : axst := ltac2:(tb__ "0|0|
Sb1S57U0A2").
Lemma pm__80_eq : ltac2:(tb__ "0|1|
S0S2S10S20Z2M0A1SaS1eG0A2A2S5bA3"). Proof. cbv delta [T5a pm__80]; cbv beta zeta. PM_all80. reflexivity. Qed.
Ltac PM_sub81 t := let t := lazymatch (eval pattern (T5a (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__80) end in PM_sub80 t.
Ltac PM_all81 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__80_eq; PM_all80.
Definition pm__81 : axst := ltac2:(tb__ "0|0|
Sb1S58U0A2").
Lemma pm__81_eq : ltac2:(tb__ "0|1|
S0S2S10S20Z3M0A1SaS1eG0A2A2S5cA3"). Proof. cbv delta [T5a pm__81]; cbv beta zeta. PM_all81. reflexivity. Qed.
Ltac PM_sub82 t := let t := lazymatch (eval pattern (T5a (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__81) end in PM_sub81 t.
Ltac PM_all82 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__81_eq; PM_all81.
Definition pm__82 : axst := ltac2:(tb__ "0|0|
Sb1S59U0A2").
Lemma pm__82_eq : ltac2:(tb__ "0|1|
S0S2S10S20Z4M0A1SaS1eG0A2A2S5dA3"). Proof. cbv delta [T5a pm__82]; cbv beta zeta. PM_all82. reflexivity. Qed.
Ltac PM_sub83 t := let t := lazymatch (eval pattern (T5a (T4b_i 4) (X5s X5bc 4)) in t) with ?P _ => eval cbv beta in (P pm__82) end in PM_sub82 t.
Ltac PM_all83 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__82_eq; PM_all82.
Definition pm__83 : axst := ltac2:(tb__ "0|0|
Sb1S5aU1A2").
Lemma pm__83_eq : ltac2:(tb__ "0|1|
S0S2S11S20Z1M0A1SaS1eG0A2A2S2dA3"). Proof. cbv delta [T5b pm__83]; cbv beta zeta. PM_all83. reflexivity. Qed.
Ltac PM_sub84 t := let t := lazymatch (eval pattern (T5b (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__83) end in PM_sub83 t.
Ltac PM_all84 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__83_eq; PM_all83.
Definition pm__84 : axst := ltac2:(tb__ "0|0|
Sb1S5bU1A2").
Lemma pm__84_eq : ltac2:(tb__ "0|1|
S0S2S11S20Z2M0A1SaS1eG0A2A2S2eA3"). Proof. cbv delta [T5b pm__84]; cbv beta zeta. PM_all84. reflexivity. Qed.
Ltac PM_sub85 t := let t := lazymatch (eval pattern (T5b (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__84) end in PM_sub84 t.
Ltac PM_all85 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__84_eq; PM_all84.
Definition pm__85 : axst := ltac2:(tb__ "0|0|
Sb1S5cU1A2").
Lemma pm__85_eq : ltac2:(tb__ "0|1|
S0S2S11S20Z3M0A1SaS1eG0A2A2S2fA3"). Proof. cbv delta [T5b pm__85]; cbv beta zeta. PM_all85. reflexivity. Qed.
Ltac PM_sub86 t := let t := lazymatch (eval pattern (T5b (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__85) end in PM_sub85 t.
Ltac PM_all86 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__85_eq; PM_all85.
Definition pm__86 : axst := ltac2:(tb__ "0|0|
Sb1S5dU1A2").
Lemma pm__86_eq : ltac2:(tb__ "0|1|
S0S2S11S20Z4M0A1SaS1eG0A2A2S30A3"). Proof. cbv delta [T5b pm__86]; cbv beta zeta. PM_all86. reflexivity. Qed.
Ltac PM_sub87 t := let t := lazymatch (eval pattern (T5b (T4b_i 4) (X5s X5bc 4)) in t) with ?P _ => eval cbv beta in (P pm__86) end in PM_sub86 t.
Ltac PM_all87 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__86_eq; PM_all86.
Definition pm__87 : axst := ltac2:(tb__ "0|1|
S4S2dSd3S3S2dA1M0SceSbbG0A1SeS22A1A2A2A2").
Lemma pm__87_eq : ltac2:(tb__ "0|1|
S0S2S12S22S20Z1M0A1SaS1eG0A2A3S5eA3"). Proof. cbv delta [T5c pm__87]; cbv beta zeta. PM_all87. reflexivity. Qed.
Ltac PM_sub88 t := let t := lazymatch (eval pattern (T5c nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__87) end in PM_sub87 t.
Ltac PM_all88 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__87_eq; PM_all87.
Definition pm__88 : axst := ltac2:(tb__ "0|1|
S4S2eSd3S3S2eA1M0SceSbbG0A1SeS22A1A2A2A2").
Lemma pm__88_eq : ltac2:(tb__ "0|1|
S0S2S12S22S20Z2M0A1SaS1eG0A2A3S5fA3"). Proof. cbv delta [T5c pm__88]; cbv beta zeta. PM_all88. reflexivity. Qed.
Ltac PM_sub89 t := let t := lazymatch (eval pattern (T5c nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__88) end in PM_sub88 t.
Ltac PM_all89 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__88_eq; PM_all88.
Definition pm__89 : axst := ltac2:(tb__ "0|1|
S4S2fSd3S3S2fA1M0SceSbbG0A1SeS22A1A2A2A2").
Lemma pm__89_eq : ltac2:(tb__ "0|1|
S0S2S12S22S20Z3M0A1SaS1eG0A2A3S60A3"). Proof. cbv delta [T5c pm__89]; cbv beta zeta. PM_all89. reflexivity. Qed.
Ltac PM_sub90 t := let t := lazymatch (eval pattern (T5c nobjb (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__89) end in PM_sub89 t.
Ltac PM_all90 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__89_eq; PM_all89.
Definition pm__90 : axst := ltac2:(tb__ "0|1|
S4S30Sd3S3S30A1M0SceSbbG0A1SeS22A1A2A2A2").
Lemma pm__90_eq : ltac2:(tb__ "0|1|
S0S2S12S22S20Z4M0A1SaS1eG0A2A3S61A3"). Proof. cbv delta [T5c pm__90]; cbv beta zeta. PM_all90. reflexivity. Qed.
Ltac PM_sub91 t := let t := lazymatch (eval pattern (T5c nobjb (T4b_i 4) (X5s X5bc 4)) in t) with ?P _ => eval cbv beta in (P pm__90) end in PM_sub90 t.
Ltac PM_all91 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__90_eq; PM_all90.
Definition pm__91 : axst := ltac2:(tb__ "0|0|
Sb0S5eSbA2").
Lemma pm__91_eq : ltac2:(tb__ "0|1|
S0S2S13S22S20Z1M0A1SaS1eG0A2A3S62A3"). Proof. cbv delta [T5m1 pm__91]; cbv beta zeta. PM_all91. reflexivity. Qed.
Ltac PM_sub92 t := let t := lazymatch (eval pattern (T5m1 nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__91) end in PM_sub91 t.
Ltac PM_all92 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__91_eq; PM_all91.
Definition pm__92 : axst := ltac2:(tb__ "0|0|
Sb0S5fSbA2").
Lemma pm__92_eq : ltac2:(tb__ "0|1|
S0S2S13S22S20Z2M0A1SaS1eG0A2A3S63A3"). Proof. cbv delta [T5m1 pm__92]; cbv beta zeta. PM_all92. reflexivity. Qed.
Ltac PM_sub93 t := let t := lazymatch (eval pattern (T5m1 nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__92) end in PM_sub92 t.
Ltac PM_all93 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__92_eq; PM_all92.
Definition pm__93 : axst := ltac2:(tb__ "0|0|
Sb0S60SbA2").
Lemma pm__93_eq : ltac2:(tb__ "0|1|
S0S2S13S22S20Z3M0A1SaS1eG0A2A3S64A3"). Proof. cbv delta [T5m1 pm__93]; cbv beta zeta. PM_all93. reflexivity. Qed.
Ltac PM_sub94 t := let t := lazymatch (eval pattern (T5m1 nobjb (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__93) end in PM_sub93 t.
Ltac PM_all94 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__93_eq; PM_all93.
Definition pm__94 : axst := ltac2:(tb__ "0|0|
Sb0S61SbA2").
Lemma pm__94_eq : ltac2:(tb__ "0|1|
S0S2S13S22S20Z4M0A1SaS1eG0A2A3S65A3"). Proof. cbv delta [T5m1 pm__94]; cbv beta zeta. PM_all94. reflexivity. Qed.
Ltac PM_sub95 t := let t := lazymatch (eval pattern (T5m1 nobjb (T4b_i 4) (X5s X5bc 4)) in t) with ?P _ => eval cbv beta in (P pm__94) end in PM_sub94 t.
Ltac PM_all95 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__94_eq; PM_all94.
Definition pm__95 : axst := ltac2:(tb__ "0|0|
Sb0S62SbA2").
Lemma pm__95_eq : ltac2:(tb__ "0|1|
S0S2S14S22S20Z1M0A1SaS1eG0A2A3S66A3"). Proof. cbv delta [T5m2 pm__95]; cbv beta zeta. PM_all95. reflexivity. Qed.
Ltac PM_sub96 t := let t := lazymatch (eval pattern (T5m2 nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__95) end in PM_sub95 t.
Ltac PM_all96 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__95_eq; PM_all95.
Definition pm__96 : axst := ltac2:(tb__ "0|0|
Sb0S63SbA2").
Lemma pm__96_eq : ltac2:(tb__ "0|1|
S0S2S14S22S20Z2M0A1SaS1eG0A2A3S67A3"). Proof. cbv delta [T5m2 pm__96]; cbv beta zeta. PM_all96. reflexivity. Qed.
Ltac PM_sub97 t := let t := lazymatch (eval pattern (T5m2 nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__96) end in PM_sub96 t.
Ltac PM_all97 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__96_eq; PM_all96.
Definition pm__97 : axst := ltac2:(tb__ "0|0|
Sb0S64SbA2").
Lemma pm__97_eq : ltac2:(tb__ "0|1|
S0S2S14S22S20Z3M0A1SaS1eG0A2A3S68A3"). Proof. cbv delta [T5m2 pm__97]; cbv beta zeta. PM_all97. reflexivity. Qed.
Ltac PM_sub98 t := let t := lazymatch (eval pattern (T5m2 nobjb (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__97) end in PM_sub97 t.
Ltac PM_all98 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__97_eq; PM_all97.
Definition pm__98 : axst := ltac2:(tb__ "0|0|
Sb0S65SbA2").
Lemma pm__98_eq : ltac2:(tb__ "0|1|
S0S2S14S22S20Z4M0A1SaS1eG0A2A3S69A3"). Proof. cbv delta [T5m2 pm__98]; cbv beta zeta. PM_all98. reflexivity. Qed.
Ltac PM_sub99 t := let t := lazymatch (eval pattern (T5m2 nobjb (T4b_i 4) (X5s X5bc 4)) in t) with ?P _ => eval cbv beta in (P pm__98) end in PM_sub98 t.
Ltac PM_all99 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__98_eq; PM_all98.
Definition pm__99 : axst := ltac2:(tb__ "0|0|
Sb0S66SbA2").
Lemma pm__99_eq : ltac2:(tb__ "0|1|
S0S2S15S22S20Z1M0A1SaS1eG0A2A3S6aA3"). Proof. cbv delta [T5m3 pm__99]; cbv beta zeta. PM_all99. reflexivity. Qed.
Ltac PM_sub100 t := let t := lazymatch (eval pattern (T5m3 nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__99) end in PM_sub99 t.
Ltac PM_all100 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__99_eq; PM_all99.
Definition pm__100 : axst := ltac2:(tb__ "0|0|
Sb0S67SbA2").
Lemma pm__100_eq : ltac2:(tb__ "0|1|
S0S2S15S22S20Z2M0A1SaS1eG0A2A3S33A3"). Proof. cbv delta [T5m3 pm__100]; cbv beta zeta. PM_all100. reflexivity. Qed.
Ltac PM_sub101 t := let t := lazymatch (eval pattern (T5m3 nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__100) end in PM_sub100 t.
Ltac PM_all101 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__100_eq; PM_all100.
Definition pm__101 : axst := ltac2:(tb__ "0|0|
Sb0S68SbA2").
Lemma pm__101_eq : ltac2:(tb__ "0|1|
S0S2S15S22S20Z3M0A1SaS1eG0A2A3S34A3"). Proof. cbv delta [T5m3 pm__101]; cbv beta zeta. PM_all101. reflexivity. Qed.
Ltac PM_sub102 t := let t := lazymatch (eval pattern (T5m3 nobjb (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__101) end in PM_sub101 t.
Ltac PM_all102 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__101_eq; PM_all101.
Definition pm__102 : axst := ltac2:(tb__ "0|0|
Sb0S69SbA2").
Lemma pm__102_eq : ltac2:(tb__ "0|1|
S0S2S15S22S20Z4M0A1SaS1eG0A2A3S35A3"). Proof. cbv delta [T5m3 pm__102]; cbv beta zeta. PM_all102. reflexivity. Qed.
Ltac PM_sub103 t := let t := lazymatch (eval pattern (T5m3 nobjb (T4b_i 4) (X5s X5bc 4)) in t) with ?P _ => eval cbv beta in (P pm__102) end in PM_sub102 t.
Ltac PM_all103 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__102_eq; PM_all102.
Definition pm__103 : axst := ltac2:(tb__ "0|0|
Sb0S6aSbA2").
Lemma pm__103_eq : ltac2:(tb__ "0|1|
S0S2ScS22S20Z1M0A1SaS1eG0A2A3S76A3"). Proof. cbv delta [T5d pm__103]; cbv beta zeta. PM_all103. reflexivity. Qed.
Ltac PM_sub104 t := let t := lazymatch (eval pattern (T5d nobjb (T4b_i 1) (X5s X5bc 1)) in t) with ?P _ => eval cbv beta in (P pm__103) end in PM_sub103 t.
Ltac PM_all104 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__103_eq; PM_all103.
Definition pm__104 : axst := ltac2:(tb__ "0|0|
Sb0S33SbA2").
Lemma pm__104_eq : ltac2:(tb__ "0|1|
S0S2ScS22S20Z2M0A1SaS1eG0A2A3S77A3"). Proof. cbv delta [T5d pm__104]; cbv beta zeta. PM_all104. reflexivity. Qed.
Ltac PM_sub105 t := let t := lazymatch (eval pattern (T5d nobjb (T4b_i 2) (X5s X5bc 2)) in t) with ?P _ => eval cbv beta in (P pm__104) end in PM_sub104 t.
Ltac PM_all105 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__104_eq; PM_all104.
Definition pm__105 : axst := ltac2:(tb__ "0|0|
Sb0S34SbA2").
Lemma pm__105_eq : ltac2:(tb__ "0|1|
S0S2ScS22S20Z3M0A1SaS1eG0A2A3S78A3"). Proof. cbv delta [T5d pm__105]; cbv beta zeta. PM_all105. reflexivity. Qed.
Ltac PM_sub106 t := let t := lazymatch (eval pattern (T5d nobjb (T4b_i 3) (X5s X5bc 3)) in t) with ?P _ => eval cbv beta in (P pm__105) end in PM_sub105 t.
Ltac PM_all106 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__105_eq; PM_all105.
Definition pm__106 : axst := ltac2:(tb__ "0|0|
Sb0S35SbA2").
Lemma pm__106_eq : ltac2:(tb__ "0|1|
S0S2ScS22S20Z4M0A1SaS1eG0A2A3S79A3"). Proof. cbv delta [T5d pm__106]; cbv beta zeta. PM_all106. reflexivity. Qed.
Ltac PM_sub107 t := let t := lazymatch (eval pattern (T5d nobjb (T4b_i 4) (X5s X5bc 4)) in t) with ?P _ => eval cbv beta in (P pm__106) end in PM_sub106 t.
Ltac PM_all107 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__106_eq; PM_all106.
Definition pm__107 : axst := ltac:(let t := eval cbv delta [C5S] in (C5S X5bc) in let t := eval cbv beta zeta in t in let t := PM_sub107 t in exact t).
Lemma pm__107_eq : ltac2:(tb__ "0|0|
S0S2S1aS1eA1S7aA3"). Proof. cbv delta [C5S pm__107]; cbv beta zeta. PM_all107. reflexivity. Qed.
Ltac PM_sub108 t := let t := lazymatch (eval pattern (C5S X5bc) in t) with ?P _ => eval cbv beta in (P pm__107) end in PM_sub107 t.
Ltac PM_all108 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.memo_rw pm__107_eq; PM_all107.
Lemma WX5rb_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3SbfS3SdS1eR2A2A1A1Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma DX5rb_0 : ltac2:(tb__ "0|4|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0SabSa8Sa7Sa8Sb3Sb3A2M0A1M1Sa7Sb4A1M2A2M3A1SdbS3S19S1eA1A1S3SdS1eR2A2A1A2SadG3SacG1G2Sa6G0SacSb3Sb3Sc0SaeQ20SbaPc0A1A3Sb7R2A1A4Sa5G0A1A3Sa5Sb4A1A4A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL1b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd1S3SdS1eR2A2A1SbSb7Nee0A1A3A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL2b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd1S3S16S1eR2A2A1Sa9SbA1Sb7N8e0A1A3A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL3b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd1S3S17S1eR2A2A1Sa9Sa9SbA1A1Sb7N840A1A3A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SPL4b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd1S3S18S1eR2A2A1Sa9Sa9Sa9SbA1A1A1Sb7N48A1A3A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HERb_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0SabSa7Sb5A1M0A1Se7SaS1eR2A2SccR2A1S26R2A1A3SadG0S28R2A1A2A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma HT4b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0S2Se8S26R2A1SccR2A1ScdR2A1SaS1eR2A2S28R2A1A5S20R2A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XX4b_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa7Sa8Sb3Sb3A2M0A1S5SaS1eR2A2A1Sa5G0A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma FBX4b_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc8Sb4SbcSb9S3SaS1eR2A2A1M0A1A1Sb6G0A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma Hchk4b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Se6SaS1eR2A2SccR2A1S26R2A1S28R2A1Sa6S2ScdR2A1Sa5S2A1A3A5Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma NX4b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa2Sb9S3SaS1eR2A2A1A1Sb9S3S1eA1A1A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma WG10b_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sb3Sd6S26R2A1PaM0A2SbdSd9SbaG0A1Sb7N8e0A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG15b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sb3Sd6S26R2A1PfA2Sb7N600A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WG12b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sb3Sd6S26R2A1PcA2SbdSd9SbaPaA1Sb7N840A1A3A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FAM4b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc8Sb5S1cU2Sd5S72A3S28R2A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NEWOb_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa7Sb5A1Se3S3SccR2A1A1S3ScdR2A1A1A2Sa5Sb5A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XPostb_0 : ltac2:(tb__ "0|1|
Sa1S0Sa7Sa8Sb3Sb3A2M0A1S5ScdR1A1A1Sa5G0A1A3Fsz;"). Proof. intros sz. reflexivity. Qed.
Lemma FBT4b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc8Sb4SbcSb9S3S20R2A1A1A1A1Sb6S3SaS1eR2A2A1A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma XT4b_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa7Sa8Sb3Sb3A2M0A1S5S20R2A1A1Sa5G0A1A3F_;Fsz;"). Proof. apply by_cases12; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RB1b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd2S3SfS20R2A1SaS1eR2A2A2A1U0A2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma RB2b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd2S3S10S20R2A1SaS1eR2A2A2A1U1A2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma PERM_ndb_0 : ltac2:(tb__ "0|0|
S0Sa3ScfSeS22A1A1Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_ltb_0 : ltac2:(tb__ "0|0|
S0Sa3Sc8SaaSaaSefR1S22A2Li;SeS22A1A3Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_covb_0 : ltac2:(tb__ "0|0|
S0Sa3Sc8SaaSaaScbSaaSeeR1A1SeS22A1A3Li;Se1U0S22A2A3Sa4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma PERM_lenb_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0SaaSafSb5SbbS3S11S20R2A1SaS1eR2A2A2A1A1A2S22A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG1b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd0S3S12S22S20R2A1SaS1eR2A2A3A1SbA2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG2b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd0S3S13S22S20R2A1SaS1eR2A2A3A1SbA2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG3b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd0S3S14S22S20R2A1SaS1eR2A2A3A1SbA2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma MRG4b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sc3Sb8Sd0S3S15S22S20R2A1SaS1eR2A2A3A1SbA2A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma ENT5b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3S6ScS22S20R2A1SaS1eR2A2A3S32S6cR2A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sdb_i]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma SID5b_0 : ltac2:(tb__ "0|0|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3Sd8S6cR2A1VGS0;A2Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax sdb_i]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.
Lemma R4covb_0 : ltac2:(tb__ "0|1|
Sa1S1S8Z1R1A2S8R1Vtmax;A2A2S0Sa3S1bSb6S3ScS22S20R2A1SaS1eR2A2A3A1M0A1S28R2A1SbbG0A1A3Sa4A3F_;Fsz;"). Proof. apply by_cases12; (cbv beta zeta delta [W st tmax]; PM_all108; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). Qed.

End INST.
End SpineMallocSec5ILW2.

