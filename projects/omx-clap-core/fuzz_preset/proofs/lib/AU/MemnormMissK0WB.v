(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormMissK0W.v (a working branch 3cae605a900a, file sha256 a9a324f041dc) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53; pin f8f98a95bc52); module paths changed; its 6 image addresses moved by code-verified function pairs (6 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin B (pinned fuzz_preset.asan-ubsan f8f98a95bc52, twin 3b5e1a099b53; this file at 08394634e479) to B' (#102 pin d663f82d7f48, twin c90d4fa54d43) by the relocation route of record, frozen alreloc a5c53bb2bed4ad03 (a Theorem Labs lane's internal file alreloc.py.frozen-a5c53bb2bed4ad03), --assume-source, --resolve none (alreloc flagged no numeral of these files) (0 lines name this file); 6 numerals changed. *)
(* Theorem Labs, 2026-10-30: MemnormMissK0W, the AIfaceMw variant of
   cgif/cgif_file_fuzzer lib/MemnormMissK0.v (file sha256 7b37329e3458; donor not released): the refill's stack window is the Section variable RW (0 <= RW, 176 + RW <= AFSTACK: hypothesis
   RWB) of MnRefillW.v, not RSTACK = 1024.  Same proof script; the changes are AIfaceM -> AIfaceMw (fields if_ ->
   ifw_), the refill leaves -> their _w forms at RW, RSTACK -> RW, the refill-window steps through
   MnRefillW.win_af_w and the other frame lia steps under RWB, RW (and RWB) in the explicit arguments of the W
   twins' lemmas, and the imports of the W twins.  MemnormMissK0.v is unchanged.  rule 24: no function proved (kind:
   re-statement of a proved miss walk over a wider refill window). *)
(* Theorem Labs, 2026-10 (task MEMNORM): the memnorm-kept twins of AGin0's k-path MISS arms: [alloc_missk0_em]
   (can_fill = 0) and [alloc_missk_cf_em] (can_fill cf in {0, 1}) conclude MemnormT.alloc_leaf_em (ErrnoG.alloc_leaf_e
   plus `memnorm mem -> memnorm mem'`) in place of ErrnoG.alloc_leaf_e.
   rule 24: no function proved (kind: arm twins, frame corollaries over the refill's memnorm-kept contract).

   AGin0.v's _e part with the refill's add-on IFME replaced by the refill's memnorm-kept contract RFm
   (MnRefillW.amm_refill_w_t), and AGin's steps replaced by their memnorm-kept twins in MemnormMissK (REFILL_em, LEAFJ_em,
   OOMJ_em); can_fill enters only through AGin0WB.MISS1 and AGin0WB.TAILJ0, cited.  The cf = 1 case of alloc_missk_cf_em is
   MemnormMissKWB.alloc_missk_em.  Copied (marked): AGin0's JOIN_e / missk_core_e / alloc_missk0_e / alloc_missk_cf_e
   scripts.  AGin0 and every existing statement are unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YG0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG02 YG06 YG07 YG0k YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0h.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YB1w YE3d YFhy YFhm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGhy.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFi1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGhz AGi2 AGi4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGj6.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFi3 AllocG AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif AGif0cgif AGjc AGjd AGje AGjb AGjg AGja AGj8 AGj7 AGj9.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MnRefillW.
(* field round 3: memnorm and the read-only data predicate at Allocate's entry, used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfNames YG0dcf YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGinWB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoApart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGin0WB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require MemnormMissGWB MemnormMissKWB.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Ltac bvne := first [cbn; lia | vm_compute; congruence | intros X; vm_compute in X; discriminate X].
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : YGcfNames.CfImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* copy of AGin0.v:52-67 (section b), with the refill's memnorm-kept contract in place of IFME, and AGin0.v:70-72 *)
Section b.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variables (nmax lmax : Z).
Variable lpost : astate -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variables (mtag stag : Z).
Hypothesis IF : AGif0n.AIface B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
Hypothesis TS : TfibSyms B.
Variable rtree : Z -> M unit.
Variable RW : Z.
Hypothesis RWB : 0 <= RW /\ 176 + RW <= AFSTACK.
(* The miss fields: c5 AGif0n.AIfaceM, as AGin. *)
Hypothesis IFM : MnRefillW.AIfaceMw B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW.
(* The refill callee with errno and memnorm kept (MnRefillW.amm_refill_w_t), in place of AGin0's IFME. *)
Hypothesis RFm : MnRefillW.amm_refill_w_t B ARX AOX rpre lpost rtree RW.
Hypothesis EAI : ErrnoApart.errno_in_img.
Hypothesis EAS : ErrnoApart.errno_apart_shadow_ag.
Hypothesis EAD : ErrnoApart.errno_apart_dzone_ag.
(* AGin's section-b definitions (copy of AGin0.v:76-84). *)
Local Abbreviation Finst := (AGinWB.Finst B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF).
Local Abbreviation if_mview := (AGinWB.if_mview B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM).
Local Abbreviation if_shape_miss := (AGinWB.if_shape_miss B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM).
Local Abbreviation vregs := AGinWB.vregs.
Local Abbreviation vregs_other := AGinWB.vregs_other.
Local Abbreviation vregs_10 := AGinWB.vregs_10.
Local Abbreviation vregs_11 := AGinWB.vregs_11.
Local Abbreviation vregs_12 := AGinWB.vregs_12.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* copy of AGin0.v:87-125 (section c) *)
Section c.
Variables (inst : Z) (ly : alayout) (S : astate) (W : world tfibsegs).
Variables (regs0 regsU : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (tr : list Z).
Hypothesis HARX : ARX inst ly S W mem0 md0.
Hypothesis HRP : rpre S n.
Hypothesis Nrange : 0 <= n <= 48.
Hypothesis Hmiss : pc_chunks (cache S (chunk_class n)) = [].
Hypothesis Hnnmax : n < nmax.
Hypothesis HBB : blocks_bytes S + n <= lmax.
Hypothesis Htr : U tr S.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Hi11 : getr regs0 11 = w64 inst.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let BPv : Z := bv_unsigned (getr regs0 12).
Let T : Z := ly_T ly.
Let cl : Z := chunk_class n.
Let csz : Z := class_size cl.
Let S1 : astate := set_nev (st_nev S + 1) S.
Let md0' : list word -> Model := fun mat => with_vm_backing (m_vm_lazy md0) mat md0.
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Hso : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly /\ SOv mod 8 = 0.
Hypothesis Hbp : sp0 <= BPv /\ BPv + 8 * 30 <= ly_stk_hi ly /\ BPv mod 8 = 0.
Hypothesis Hcf0 : getr regs0 15 = w64 0.
Hypothesis Hpres0 : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis PSO : val_mem tfibsegs (mrestrict (w_H W) mem0) SOv 8 BPv.
Hypothesis PLEN : val_mem tfibsegs (mrestrict (w_H W) mem0) (SOv + 8) 8 (Z.of_nat (length tr)).
Hypothesis PBUF0 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem0) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).
(* field round 3: the refill's call-state facts at the entry memory (AbudgetRestate's lane text) *)
Hypothesis HRO0 : YG0dcf.arodata_ok_cf tfibsegs B mem0.
Hypothesis HUo : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr regsU r = getr regs0 r.
Hypothesis HU10 : getr regsU 10%bv = getr regs0 11%bv.
Hypothesis HU11 : getr regsU 11%bv = getr regs0 10%bv.
Hypothesis HU12 : getr regsU 12%bv = w64 8.
Hypothesis HU14 : getr regsU 14%bv = w64 1.

(* AGin's section-c facts (copy of AGin0.v:129-131). *)
Local Abbreviation Hn0 := (AGinWB.Hn0 ly regs0 n tr Nrange Htrlen).
Local Abbreviation FP := (AGinWB.FP n Nrange).
Local Abbreviation Hcl_class := (AGinWB.Hcl_class n).
Let E0m : env := AGj6.E0 ly regs0 n tr cl 1 0 csz 0 0 0 0 0 0.
(* AGin0WB.MISS1 (cf = 0). *)
Local Abbreviation MISS1 := (AGin0WB.MISS1 B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TS rtree RW IFM inst ly S W regs0 regsU mem0 md0 n tr
  HARX Nrange Hmiss Htrlen Hn Hi11 Htp Hsp Hso Hbp Hcf0 Hpres0 PSO PLEN PBUF0 HUo HU10 HU11 HU12 HU14).
(* MemnormMissK's steps that do not read can_fill (the remaining arguments, given by eassumption). *)
Local Abbreviation PL_em := (MemnormMissGWB.PL_em B mt ARX AOX lpost inst ly S W regsU mem0 md0 n tr).
Local Abbreviation ms1_shape := (AGinWB.ms1_shape W).
Local Abbreviation RAZ1 := (AGinWB.RAZ1 ly W regs0 n tr Htrlen).
Local Abbreviation REFILL_em := (MemnormMissKWB.REFILL_em B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM RFm inst ly S W regs0 mem0 md0 n tr
  HARX HRP Nrange Hmiss Htrlen Hi11 Hgp Hsp Hso Hbp HRO0).
Local Abbreviation OOMJ_em := (MemnormMissKWB.OOMJ_em B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree RW RWB IFM inst ly S W regs0 regsU mem0 md0 n tr
  HARX Nrange Hmiss Htrlen Htp Hra Hsp Hso Hbp HUo).

(* --- The refill-call machine state (copy of AGin0.v:172-178). --- *)
Section f.
Variables (ms1 : machine_state) (mat1 : list word) (Em : env).
Hypothesis HEm : forall k, (k < aHAV)%nat -> ew Em k = ew E0m k.
Hypothesis HSC : st_ok tfibsegs Em AGi4.MK_CALL (restrict (w_H W) ms1).
Hypothesis MEQW : forall x : word, ~ AGj8.WINM ly regs0 (bv_unsigned x) -> (ms_mem ms1) x = mem0 x.
Hypothesis PRESW : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a.
Hypothesis BUFW : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).

(* --- After the refill (copy of AGin0.v:182-198), with the refill's keep. --- *)
Section g0.
Variables (S' : astate) (ly' : alayout) (W' : world tfibsegs) (regsR : bvmap 5 word) (memR : word -> option byte) (mdR : Model).
Hypothesis HARXp : ARX inst ly' S' W' memR mdR.
Hypothesis HLPp : lpost S'.
Hypothesis CIp : st_cache_inited S' = true.
Hypothesis HBBp : blocks_bytes S' = blocks_bytes S.
Hypothesis HDPp : st_depot S' = st_depot S.
Hypothesis Hly : layout_le (length (st_secs S)) ly ly'.
Hypothesis HWLE : wle W W'.
Hypothesis HAREGS : aregs_preserved (ms_regs ms1) regsR.
Hypothesis HSIO : same_io (md0' mat1) mdR.
Hypothesis HFRA : forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly' S' a -> ~ (spZ (ms_regs ms1) - RW <= a < spZ (ms_regs ms1)) ->
  aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) (ms_mem ms1) a.
Hypothesis HFRR : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' S' (bv_unsigned x) ->
  ~ (spZ (ms_regs ms1) - RW <= bv_unsigned x < spZ (ms_regs ms1)) -> memR x = (ms_mem ms1) x.
Hypothesis HPRR : forall a, spZ (ms_regs ms1) - RW <= a < spZ (ms_regs ms1) -> apresent (w_H W') memR a.
(* ERRNO-KEPT: the refill keeps errno (MnRefillW.rleaf_e_w RW); used only by the _e lemmas. *)
Hypothesis HERRp : ErrnoG.errno_kept B (ms_mem ms1) memR.
Hypothesis HMN : MemnormT.memnorm_keep tfibsegs (ms_mem ms1) memR.

(* --- The a0 = 1 cache join (copy of AGin0.v:211-218). --- *)
Section g.
Variables (l : list Z) (off : Z).
Hypothesis Hcache' : pc_chunks (cache S' cl) = l ++ [off].
Hypothesis HA1 : getr regsR 10 = w64 1.
Let cnt' : Z := Z.of_nat (length (l ++ [off])).
Let v' : Z := off / 16.
Let DPOST' : Z -> (word -> option byte) -> Prop := fun z m => dpost inst ly' S' W' tr z m.
Local Abbreviation HV' := (AGinWB.HV' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly regs0 n tr Nrange Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
(* AGin0WB.TAILJ0, the cf = 0 join tail (the remaining arguments are the join state's junk values). *)
Local Abbreviation TAILJ0 := (AGin0WB.TAILJ0 B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TS rtree RW RWB IFM inst ly S W regs0 mem0 md0 n tr
  HARX Nrange Hmiss Htr Htrlen Hn Hi11 Htp Hgp Hra Hsp Hso Hbp Hcf0 PSO PLEN ms1 Em HEm HSC MEQW PRESW BUFW
  S' ly' W' regsR memR mdR HARXp CIp HDPp Hly HAREGS HFRA HPRR l off Hcache' HA1).
(* MemnormMissKWB.LEAFJ_em, the join leaf with errno and memnorm kept (the remaining arguments are the junk byte and the
   result). *)
Local Abbreviation LEAFJ_em := (MemnormMissKWB.LEAFJ_em B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree RW RWB IFM EAI EAS EAD inst ly S W regs0 regsU mem0 md0 n tr
  HARX HRP Nrange Hmiss Hnnmax HBB Htr Htrlen Hsp Hso Hbp HUo ms1 mat1 Em HEm HSC MEQW PRESW
  S' ly' W' memR mdR HARXp CIp HBBp Hly HWLE HSIO HFRA HFRR HPRR HERRp HMN l off Hcache').
(* AGin0WB.JOIN_e over LEAFJ_em. *)
Lemma JOIN0_em : amreal tfibsegs (malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs 0x36ff4 regsR memR mdR) PL_em.
Proof.
(* copy of AGin0.v:332-335 *)
destruct (@AGjd.vw_junk_values _ _ B W' ly' inst memR n cl cnt' v' TS HV' Nrange Hcl_class)
  as (j0 & j1 & j2 & j3 & j4 & jb & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hjb & Hjb_def).
eapply amreal_mono; [| eapply TAILJ0; eassumption].
intros r W'' c'' H. eapply LEAFJ_em; eassumption.
Qed.
End g.
End g0.
End f.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* AGin0WB.missk_core_e over alloc_leaf_em: MISS1 at cf = 0, the refill through REFILL_em (rleaf_em), the branches
   through OOMJ_em / JOIN0_em. *)
Lemma missk_core0_em : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0)
(MemnormT.alloc_leaf_em tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr).
Proof.
(* copy of AGin0.v:387-422, over the _em lemmas *)
assert (CORE : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0) PL_em).
{
rewrite (if_shape_miss n tr S Hn0 FP Hmiss). fold cl.
eapply amreal_pure; [reflexivity|].
eapply amreal_pure; [unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage; lia); reflexivity|].
change (set_nev (st_nev S + 1) S) with S1.
eapply (YG0d.amreal_mbind tfibsegs (rtree cl) (fun _ : unit => malloc_join_t stag n tr cl) S1 W _
(fun r W1 c1 => exists ms1 mat1 Em,
  ((forall k, (k < aHAV)%nat -> ew Em k = ew E0m k) /\ st_ok tfibsegs Em AGi4.MK_CALL (restrict (w_H W) ms1) /\
   (forall x : word, ~ AGj8.WINM ly regs0 (bv_unsigned x) -> ms_mem ms1 x = mem0 x) /\
   (forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a) /\
   (forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0))) /\
  MnRefillW.rleaf_em_w RW B ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1) r W1 c1)).
- (* MISS1, then the refill callee *)
  eapply amreal_SRr_pre; [exact MISS1|]. intros W1 c1 _ HC.
  destruct HC as (-> & ms1 & mat1 & Em & -> & HEm & HSC & MEQW & PRESW & BUFW).
  assert (SHAPE : ms1 = mkst (ms_regs ms1) (w64 0x37494) (ms_mem ms1) (seg_rom tfibsegs)) by (eapply ms1_shape; eassumption).
  assert (RR : amreal tfibsegs (rtree cl S1) W (cfg_at tfibsegs A_Refill (ms_regs ms1) (ms_mem ms1) (md0' mat1))
    (MnRefillW.rleaf_em_w RW B ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1))) by (eapply REFILL_em; eassumption).
  unfold cfg_at, A_Refill in RR. rewrite SHAPE at 1.
  eapply amreal_mono; [| exact RR]. intros r W2 c2 HRL. exists ms1, mat1, Em. split; [|exact HRL]. repeat (split; [assumption|]). exact BUFW.
- (* the post-refill branch on the class cache *)
  intros [] Sp W1 c1 (ms1 & mat1 & Em & (HEm & HSC & MEQW & PRESW & BUFW) & HRL).
  destruct HRL as (ly' & regsR & memR & mdR & -> & HARXp & HLPp & CIp & HBBp & HDPp & Hly & HWLE & HAREGS & HSIO & HFRA & HFRR & HERRp & HMN & HPRR & HA0e).
  cbn [snd] in *.
  assert (RA : raZ (ms_regs ms1) = 0x36ff4) by (eapply RAZ1; eassumption). rewrite RA.
  destruct (pc_chunks (cache Sp cl)) as [|x t] eqn:El.
  + assert (HA0 : getr regsR 10 = w64 0) by (rewrite HA0e; try rewrite El; reflexivity).
    eapply OOMJ_em; eassumption.
  + assert (LX : exists l off, x :: t = l ++ [off]) by (exists (List.removelast (x :: t)), (List.last (x :: t) 0); apply List.app_removelast_last; discriminate).
    destruct LX as (l & off & LX). rewrite LX in El.
    assert (HA1 : getr regsR 10 = w64 1) by (rewrite HA0e; try rewrite El; destruct l; reflexivity).
    eapply JOIN0_em; eassumption.
}
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0) PL_em CORE)].
intros r W' c' [HL HP]. exact (HL HP).
Qed.
End c.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The theorem, can_fill = 0: AGin0WB.alloc_missk0_e concluding alloc_leaf_em. *)
Theorem alloc_missk0_em : forall inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 0 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Proof.
(* copy of AGin0.v:499-542, over missk_core0_em *)
intros inst so bp ly S W regs mem md n tr PRE HRO Nrange Hmiss.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres0 & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hn0 & Hlive).
unfold spZ, raZ, AFSTACK_G in *. rewrite (ts_tp B TS) in Htp.
pose proof (Finst inst ly S W mem md HARX) as HIO. pose proof HIO as (HIO1 & HIO2 & HIO3).
assert (Hnn : n < nmax) by lia.
assert (FP0 : from_primary n = true) by (eapply AGinWB.FP; eassumption).
pose proof (if_mview inst ly S W mem md n HARX ltac:(lia) FP0 Hmiss) as HMV0.
pose proof (lo_top ly (AGif0n.mv_ly B W ly inst mem (chunk_class n) HMV0)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
set (regs0 := vregs regs n inst bp).
assert (Hso64 : 0 <= so < 2 ^ 64) by (unfold kHighMemEnd, kHighMemBeg in T4, T7; lia).
assert (Hbp64 : 0 <= bp < 2 ^ 64) by (unfold kHighMemEnd, kHighMemBeg in T4, T7; lia).
assert (Hinst64 : 0 <= inst < 2 ^ 64) by lia.
assert (HUo : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr regs r = getr regs0 r)
by (intros r H10 H11 H12; unfold regs0; symmetry; exact (vregs_other regs n inst bp r H10 H11 H12)).
assert (HU10 : getr regs 10%bv = getr regs0 11%bv) by (unfold regs0; rewrite Hr10, vregs_11; reflexivity).
assert (HU11 : getr regs 11%bv = getr regs0 10%bv) by (unfold regs0; rewrite Hr11, vregs_10; reflexivity).
assert (HU12 : getr regs 12%bv = w64 8) by exact Hr12.
assert (HU14 : getr regs 14%bv = w64 1) by exact Hr14.
assert (Hn : getr regs0 10 = w64 n) by (unfold regs0; apply vregs_10).
assert (Hi11 : getr regs0 11 = w64 inst) by (unfold regs0; apply vregs_11).
assert (R2 : getr regs0 2 = getr regs 2) by (unfold regs0; apply vregs_other; bvne).
assert (R1 : getr regs0 1 = getr regs 1) by (unfold regs0; apply vregs_other; bvne).
assert (R12 : bv_unsigned (getr regs0 12) = bp) by (unfold regs0; rewrite vregs_12; apply w64_unsigned; exact Hbp64).
assert (R13 : bv_unsigned (getr regs0 13) = so)
by (unfold regs0; rewrite (vregs_other regs n inst bp 13%bv) by bvne; rewrite Hr13; apply w64_unsigned; exact Hso64).
assert (Htp0 : getr regs0 4 = w64 TFIB_TP) by (unfold regs0; rewrite (vregs_other regs n inst bp 4%bv) by bvne; exact Htp).
assert (Hgp0 : getr regs0 3 = w64 (as_gp B)) by (unfold regs0; rewrite (vregs_other regs n inst bp 3%bv) by bvne; exact Hgp).
assert (Hcf0 : getr regs0 15 = w64 0) by (unfold regs0; rewrite (vregs_other regs n inst bp 15%bv) by bvne; exact Hr15).
assert (Hra0 : YK0s.ret_ok (getr regs0 1)) by (rewrite R1; exact Hra).
assert (Hra40 : 4096 <= bv_unsigned (getr regs0 1)) by (rewrite R1; exact Hra4096).
assert (Hsp : ly_stk_lo ly + AFSTACK <= bv_unsigned (getr regs0 2) /\ ly_bot ly < bv_unsigned (getr regs0 2) /\
bv_unsigned (getr regs0 2) <= ly_stk_hi ly /\ bv_unsigned (getr regs0 2) mod 16 = 0) by (rewrite R2; unfold AFSTACK; repeat split; assumption).
assert (Hso : bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 13) /\ bv_unsigned (getr regs0 13) + 16 <= ly_stk_hi ly /\
bv_unsigned (getr regs0 13) mod 8 = 0) by (rewrite R2, R13; repeat split; assumption).
assert (Hbp : bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 12) /\ bv_unsigned (getr regs0 12) + 8 * 30 <= ly_stk_hi ly /\
bv_unsigned (getr regs0 12) mod 8 = 0) by (rewrite R2, R12; repeat split; assumption).
assert (Hpres00 : forall a, bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W) mem a)
by (rewrite R2; unfold AFSTACK; exact Hpres0).
assert (PSO0 : val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 13)) 8 (bv_unsigned (getr regs0 12))) by (rewrite R13, R12; exact PSO).
assert (PLEN0 : val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 13) + 8) 8 (Z.of_nat (length tr))) by (rewrite R13; exact PLEN).
assert (PBUF0 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 12) + 8 * Z.of_nat i) 8 (nth i tr 0))
by (rewrite R12; exact PBUF).
change (cfg_at tfibsegs 0x326a4 regs mem md) with (cfg_at tfibsegs A_Allocate regs mem md).
eapply (missk_core0_em inst ly S W regs0 regs mem md n tr); eassumption.
Qed.
(* The k-path MISS arm for can_fill cf in {0, 1}: alloc_missk0_em (cf = 0) or MemnormMissKWB.alloc_missk_em (cf = 1). *)
Theorem alloc_missk_cf_em : forall cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 cf inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Proof.
(* copy of AGin0.v:551-553, over the _em theorems *)
intros cf inst so bp ly S W regs mem md n tr [-> | ->].
- exact (alloc_missk0_em inst so bp ly S W regs mem md n tr).
- exact (MemnormMissKWB.alloc_missk_em B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TS rtree RW RWB IFM RFm EAI EAS EAD inst so bp ly S W regs mem md n tr).
Qed.
End b.
End a.
