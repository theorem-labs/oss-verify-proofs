(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGin0.v (cold/c-asan-nmax-param 57e82b93d43, file sha256 1b54805973d3) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 17 image addresses moved by code-verified function pairs (20 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_state/lib/A/AGin0.v (donor image sha256 64b53ff86172), with its module paths changed, names TfibSyms -> SegBSyms and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* The k-path MISS arm of the frame-generic Allocate contract (AllocG.alloc_leaf) at can_fill = 0 (calloc's call,
   Allocate's a5 = 0), and the k-path MISS arm for can_fill cf in {0, 1}.

   Ported from proofs/cgif/cgif_file_fuzzer/lib/AFhy.v..YFjg.v (cgif_file's released malloc walk, same image) with the
   caller's frame made abstract; the cf = 0 tail comes from TkCf0's AGc0 / AGc2 (seg2cf0_even / seg2cf0_odd, post
   AGc0.at_RET0K), which the c5 AGjg.tail_inner takes for its left case (can_fill = 0).
   The cf = 0 twin of AGin.alloc_missk (frozen AIfaceM: interface AGif0n.AIface + AIfaceM, U : list Z -> astate -> Prop,
   and the AIfaceM field if_depot_miss), with AGin's Section variables and hypotheses in AGin's order.  The steps
   that do not read can_fill are AGin's lemmas, cited: the refill call (REFILL), the post-refill frame and view facts
   (HS3, PRES', HV', ...), the depot call at the post-refill state (HDEP, from the field if_depot_miss with HARX / Htr
   at the entry state S), the join leaf (LEAFJ) and the class-full OOM arm (OOMJ).
   can_fill (a5, atom 15 of the virtual regs0) enters only through the seed facts and the tail:
   - SEEDM / MISS1 (AGja.SEEDM_ok) and FACTS' / HS5 / HS6 / HS7 / ATJ (AGje.FACTS_ok) are AGin's, with the left case
     (cf = 0) of the seed's disjunction;
   - TAILJ0 is AGin.TAILJ (AGj7.segJ, then AGjg.tail_inner) with the left case of tail_inner's disjunction;
   - JOIN, missk_core and alloc_missk0 are AGin's, over these lemmas. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YG0b.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG02 YG06 YG07 YG0k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AFl1.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0h.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1w AE3d AFhy AFhm AGhy AFi1 AGhz AGi2 AGi4.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YFen.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AGj6 AFi3.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YGAlloc AGif0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AGif2cgif AGif0cgif AGjc AGjd AGje AGjb AGjg AGja AGj8 AGj7 AGj9 AB13.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YA00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AGin.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import ErrnoG.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require ErrnoApart.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Ltac bvne := first [cbn; lia | vm_compute; congruence | intros X; vm_compute in X; discriminate X].
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
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
Hypothesis TS : SegBSyms B.
Variable rtree : Z -> M unit.
(* The miss fields: c5 AGif0n.AIfaceM, as AGin. *)
Hypothesis IFM : AGif0n.AIfaceM B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree.
(* ERRNO-KEPT (the _e twins only): the refill with errno kept, and h-decbox-a9's errno-apart image Props. *)
Hypothesis IFME : ErrnoG.AIfaceME B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree.
Hypothesis EAI : ErrnoApart.errno_in_img.
Hypothesis EAS : ErrnoApart.errno_apart_shadow_ag.
Hypothesis EAD : ErrnoApart.errno_apart_dzone_ag.
(* The depot call at the post-refill state Sp with U taken at the entry state S0: the AIfaceM field, as AGin. *)
Definition if_depot_miss := AGif0n.if_depot_miss B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM.
(* AGin's section-b definitions. *)
Local Abbreviation Finst := (AGin.Finst B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF).
Local Abbreviation rleaf := AGin.rleaf.
Local Abbreviation if_mview := (AGin.if_mview B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM).
Local Abbreviation if_shape_miss := (AGin.if_shape_miss B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM).
Local Abbreviation vregs := AGin.vregs.
Local Abbreviation vregs_other := AGin.vregs_other.
Local Abbreviation vregs_10 := AGin.vregs_10.
Local Abbreviation vregs_11 := AGin.vregs_11.
Local Abbreviation vregs_12 := AGin.vregs_12.

(* ---------------------------------------------------------------------------------------------------------------- *)
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
Hypothesis HUo : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr regsU r = getr regs0 r.
Hypothesis HU10 : getr regsU 10%bv = getr regs0 11%bv.
Hypothesis HU11 : getr regsU 11%bv = getr regs0 10%bv.
Hypothesis HU12 : getr regsU 12%bv = w64 8.
Hypothesis HU14 : getr regsU 14%bv = w64 1.

(* AGin's section-c facts (they do not read can_fill). *)
Local Abbreviation HIO := (AGin.HIO B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF inst ly S W mem0 md0 HARX).
Local Abbreviation Hn0 := (AGin.Hn0 ly regs0 n tr Nrange Htrlen).
Local Abbreviation FP := (AGin.FP n Nrange).
Local Abbreviation Hcl_class := (AGin.Hcl_class n).
Local Abbreviation Hcl := (AGin.Hcl ly regs0 n tr Nrange Htrlen).
Local Abbreviation Hcl_def := (AGin.Hcl_def n Nrange).
Local Abbreviation HMV := (AGin.HMV B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange Hmiss Htrlen).
Local Abbreviation Hinst := (AGin.Hinst B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF inst ly S W regs0 mem0 md0 n tr HARX Htrlen Hi11).
Local Abbreviation Hvd := (AGin.Hvd ly regs0 n tr Htrlen).
Local Abbreviation Hcntd := (AGin.Hcntd ly regs0 n tr Htrlen).
Local Abbreviation Hjbd := (AGin.Hjbd ly regs0 n tr Htrlen).
Local Abbreviation Hv2d := AGin.Hv2d.
Local Abbreviation LY := (AGin.LY B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange Hmiss Htrlen).
Local Abbreviation IMG := (AGin.IMG B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange Hmiss Htrlen).
Lemma STK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd. Proof. exact (AGin.STK B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange Hmiss Htrlen). Qed.
Lemma Usp : 0 <= sp0 < 2 ^ 64. Proof. exact (AGin.Usp regs0). Qed.
Let E0m : env := AGj6.E0 ly regs0 n tr cl 1 0 csz 0 0 0 0 0 0.
Let DPOSTm : Z -> (word -> option byte) -> Prop := fun z m => dpost inst ly S W tr z m.
Let mat0 : list word := m_vm_materialized md0.

(* AGin.SEEDM / MISS1 with cf = 0: the seed reads can_fill through AGja.SEEDM_ok's disjunction. *)
Lemma SEEDM : st_ok tfibsegs E0m AGi4.MK_1 (restrict (w_H W) (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs))).
Proof.
exact (@AGja.SEEDM_ok _ _ W ly regs0 mem0 n tr cl 1 0 csz 0 0 0 0 0 0 Hcl Hvd Hcntd Hjbd Hv2d LY IMG Hn Htp Hsp Htrlen Hso Hbp (or_introl Hcf0) DPOSTm Nrange Hcl_def B inst TS Hi11 HIO (AGif0n.mv_tsd B W ly inst mem0 cl HMV) (AGif0n.mv_const B W ly inst mem0 cl HMV) (AGif0n.mv_inst B W ly inst mem0 cl HMV) (AGif0n.mv_cnt0 B W ly inst mem0 cl HMV) (AGif0n.mv_unw B W ly inst mem0 cl HMV) PSO PLEN Hpres0 regsU HUo HU10 HU11 HU12 HU14).
Qed.
Lemma MISS1 : SRr tfibsegs W (cfg_at tfibsegs A_Allocate regsU mem0 md0)
(AGj8.at_STM W ly regs0 mem0 md0 n tr cl 1 0 csz 0 0 0 0 0 0 AGi4.MK_CALL).
Proof.
replace (cfg_at tfibsegs A_Allocate regsU mem0 md0) with (mkCfg (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs)) (md0' mat0))
by (unfold cfg_at, md0', mat0; rewrite with_vm_backing_id; reflexivity).
exact (@AGj8.miss1 _ _ W ly regs0 mem0 md0 n tr cl 1 0 csz 0 0 0 0 0 0 Hcl Hvd Hcntd Hv2d LY IMG Hn Hsp Htrlen Hso Hbp DPOSTm Nrange Hcl_def mat0 regsU PBUF0 [] 0 Hpres0 SEEDM).
Qed.
(* AGin's pre-leaf, its refill call and its OOM arm (the remaining arguments are the post-MISS1 / post-refill facts,
   given by eassumption as in AGin.missk_core). *)
Local Abbreviation PL := (AGin.PL B mt ARX AOX lpost inst ly S W regsU mem0 md0 n tr).
Local Abbreviation ms1_shape := (AGin.ms1_shape W).
Local Abbreviation REFILL := (AGin.REFILL B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 mem0 md0 n tr HARX HRP Nrange Hmiss Htrlen Hi11 Hgp Hsp Hso Hbp).
Local Abbreviation RAZ1 := (AGin.RAZ1 ly W regs0 n tr Htrlen).
Local Abbreviation OOMJ := (AGin.OOMJ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree IFM inst ly S W regs0 regsU mem0 md0 n tr HARX Nrange Hmiss Htrlen Htp Hra Hsp Hso Hbp HUo).
Local Abbreviation PL_e := (AGin.PL_e B mt ARX AOX lpost inst ly S W regsU mem0 md0 n tr).
Local Abbreviation REFILL_e := (AGin.REFILL_e B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM IFME inst ly S W regs0 mem0 md0 n tr HARX HRP Nrange Hmiss Htrlen Hi11 Hgp Hsp Hso Hbp).
Local Abbreviation OOMJ_e := (AGin.OOMJ_e B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree IFM inst ly S W regs0 regsU mem0 md0 n tr HARX Nrange Hmiss Htrlen Htp Hra Hsp Hso Hbp HUo).

(* --- The refill-call machine state (AGin's section f). --- *)
Section f.
Variables (ms1 : machine_state) (mat1 : list word) (Em : env).
Hypothesis HEm : forall k, (k < aHAV)%nat -> ew Em k = ew E0m k.
Hypothesis HSC : st_ok tfibsegs Em AGi4.MK_CALL (restrict (w_H W) ms1).
Hypothesis MEQW : forall x : word, ~ AGj8.WINM ly regs0 (bv_unsigned x) -> (ms_mem ms1) x = mem0 x.
Hypothesis PRESW : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a.
Hypothesis BUFW : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* After the refill (AGin's section g0).                                                                              *)
Section g0.
Variables (S' : astate) (ly' : alayout) (W' : world tfibsegs) (regsR : bvmap 5 word) (memR : word -> option byte) (mdR : Model).
Hypothesis HARXp : ARX inst ly' S' W' memR mdR.
Hypothesis HLPp : lpost S'.
Hypothesis CIp : st_cache_inited S' = true.
Hypothesis HBBp : blocks_bytes S' = blocks_bytes S.
Hypothesis Hly : layout_le (length (st_secs S)) ly ly'.
Hypothesis HWLE : wle W W'.
Hypothesis HAREGS : aregs_preserved (ms_regs ms1) regsR.
Hypothesis HSIO : same_io (md0' mat1) mdR.
Hypothesis HFRA : forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly' S' a -> ~ (spZ (ms_regs ms1) - RSTACK <= a < spZ (ms_regs ms1)) ->
  aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) (ms_mem ms1) a.
Hypothesis HFRR : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' S' (bv_unsigned x) ->
  ~ (spZ (ms_regs ms1) - RSTACK <= bv_unsigned x < spZ (ms_regs ms1)) -> memR x = (ms_mem ms1) x.
Hypothesis HPRR : forall a, spZ (ms_regs ms1) - RSTACK <= a < spZ (ms_regs ms1) -> apresent (w_H W') memR a.
(* ERRNO-KEPT: the refill keeps errno (ErrnoG.rleaf_e); used only by the _e lemmas. *)
Hypothesis HERRp : ErrnoG.errno_kept B (ms_mem ms1) memR.
Let msR : machine_state := mkst regsR (w64 0x3793c) memR (seg_rom tfibsegs).
Let cR : config := mkCfg msR (with_vm_backing (m_vm_lazy mdR) (m_vm_materialized mdR) mdR).
Let ms3 : machine_state := mkst regsR (w64 0x3793c) (mrestrict (w_H W') memR) (seg_rom tfibsegs).
Let E1 : env := havoc Em hRFk (map (getr regsR) CLOB).
Local Abbreviation Hsp' := (AGin.Hsp' ly S regs0 Hsp ly' Hly).
Local Abbreviation Hso' := (AGin.Hso' ly S regs0 Hso ly' Hly).
Local Abbreviation Hbp' := (AGin.Hbp' ly S regs0 Hbp ly' Hly).
Lemma PRES' : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W') memR a. Proof. exact (AGin.PRES' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange Hmiss Htrlen Hsp Hso Hbp ms1 Em HEm HSC PRESW S' ly' W' memR mdR HARXp Hly HFRA HPRR). Qed.
Lemma HS3 : st_ok tfibsegs E1 AGi4.SSK3 ms3. Proof. exact (AGin.HS3 B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange Hmiss Htrlen Hsp Hso Hbp ms1 Em HEm HSC S' ly' W' regsR memR mdR HARXp Hly HAREGS HFRA). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The a0 = 1 cache join, at the post-refill layout ly' (AGin's section g).                                          *)
Section g.
Variables (l : list Z) (off : Z).
Hypothesis Hcache' : pc_chunks (cache S' cl) = l ++ [off].
Hypothesis HA1 : getr regsR 10 = w64 1.
Let cnt' : Z := Z.of_nat (length (l ++ [off])).
Let v' : Z := off / 16.
Let DPOST' : Z -> (word -> option byte) -> Prop := fun z m => dpost inst ly' S' W' tr z m.
Local Abbreviation HV' := (AGin.HV' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly regs0 n tr Nrange Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation LY' := (AGin.LY' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly regs0 n tr Nrange Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation IMG' := (AGin.IMG' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly regs0 n tr Nrange Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation Hv' := (AGin.Hv' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree IFM inst ly regs0 n tr Nrange Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation Hv2' := (AGin.Hv2' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree IFM inst ly regs0 n tr Nrange Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation Hcnt' := (AGin.Hcnt' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree IFM inst ly regs0 n tr Nrange Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation HKpres' := (AGin.HKpres' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree IFM inst ly regs0 n tr Nrange Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation HSKpres' := (AGin.HSKpres' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree IFM inst ly regs0 n tr Nrange Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation HPB250' := (AGin.HPB250' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree IFM inst ly regs0 n tr Nrange Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Lemma BUF' : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W') memR) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).
Proof. exact (AGin.BUF' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange Hmiss Htrlen Hsp Hso Hbp ms1 Em HEm HSC BUFW S' ly' W' memR mdR HARXp Hly HFRA). Qed.

Section gj.
Variables (j0 jb j1 j2 j3 j4 : Z).
Hypothesis Hj0 : val_mem tfibsegs (mrestrict (w_H W') memR) (ly_T ly' + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfibsegs (mrestrict (w_H W') memR) (ly_T ly' + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfibsegs (mrestrict (w_H W') memR) (ly_T ly' + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfibsegs (mrestrict (w_H W') memR) (ly_T ly' + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfibsegs (mrestrict (w_H W') memR) (AGj6.SSLOTv ly' cl) 8 j4.
Hypothesis Hjb : 0 <= jb <= 255.
Hypothesis Hjb_def : val_mem tfibsegs (mrestrict (w_H W') memR) (AGj6.Kv ly' cl v' + AGj6.RZ - 15) 1 jb.
Let E0' : env := AGj6.E0 ly' regs0 n tr cl cnt' v' csz j0 jb j1 j2 j3 j4.
Let Es : env := env_merge PND E1 E0'.
Lemma HEs : forall k, (k < aHAV)%nat -> ew Es k = ew E0' k. Proof. exact (AGin.HEs ly S regs0 n tr Htrlen Em HEm ly' regsR Hly l off j0 jb j1 j2 j3 j4). Qed.
Lemma AGs : env_agree 64 E0' Es. Proof. exact (AGin.AGs ly S regs0 n tr Htrlen Em HEm ly' regsR Hly l off j0 jb j1 j2 j3 j4). Qed.
Lemma Es2 : bv_unsigned (ew Es 2) = sp0. Proof. exact (AGin.Es2 ly S regs0 n tr Htrlen Em HEm ly' regsR Hly l off j0 jb j1 j2 j3 j4). Qed.
Lemma REG0' : Forall (region_ok tfibsegs E0' (mrestrict (w_H W') memR)) REG0KG. Proof. exact (AGin.REG0' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TS rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange Hmiss Htrlen Hi11 Hsp Hso Hbp PSO PLEN ms1 Em HEm HSC MEQW PRESW S' ly' W' memR mdR HARXp CIp Hly HFRA HPRR l off Hcache' j0 jb j1 j2 j3 j4 Hj0 Hj1 Hj2 Hj3 Hj4 Hjb Hjb_def). Qed.
Lemma PAIRS' : pairwise_disjoint E0' REG0KG. Proof. exact (AGin.PAIRS' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TS rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange Htrlen Hi11 Hsp Hso Hbp S' ly' W' memR mdR HARXp CIp Hly l off Hcache' j0 jb j1 j2 j3 j4). Qed.
Lemma region_ok_agree_on_lt : forall r, In r TAIL0KG -> region_ok tfibsegs E0' (mrestrict (w_H W') memR) r -> region_ok tfibsegs Es (ms_mem ms3) r.
Proof. exact (AGin.region_ok_agree_on_lt ly S regs0 n tr Htrlen Em HEm ly' W' regsR memR Hly l off j0 jb j1 j2 j3 j4). Qed.
Local Abbreviation HDAOK := (AGin.HDAOK B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF inst tr S' ly' W').
Local Abbreviation HDEP := (AGin.HDEP B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W mem0 md0 tr HARX Htr S' ly' W' memR mdR HARXp).
(* AGin.FACTS' / HS5 / HS6 / HS7 / ATJ with cf = 0: the join state's facts read can_fill through AGje.FACTS_ok's
   disjunction. *)
Lemma FACTS' : atoms_ok E0' (f_atoms FKG).
Proof. exact (proj1 (@AGje.FACTS_ok _ _ W' ly' regs0 memR n tr cl cnt' v' csz j0 jb j1 j2 j3 j4 Hcl Hv' Hcnt' Hjb Hv2' LY' IMG' Hn Hsp' Htrlen Hso' Hbp' (or_introl Hcf0) DPOST' Nrange B inst TS HV' Hi11 HIO Hcl_class)). Qed.
Lemma HS5 : st_ok tfibsegs Es (mkSS (ss_pc AGi4.SSK3) (sr_set (ss_regs AGi4.SSK3) 10%bv (SLit 1)) (ss_mem AGi4.SSK3) (ss_resv AGi4.SSK3) (ss_facts AGi4.SSK3)) ms3.
Proof.
assert (HS4 : st_ok tfibsegs Es AGi4.SSK3 ms3).
{ pose proof AGi4.SSK3_atoms as (A1 & A2 & A3 & A4 & A5). pose proof AGi4.tlREG0K_facts as (_ & _ & T3).
  apply (st_ok_agree_on2 tfibsegs PND E1 Es AGi4.SSK3 ms3 HS3 (env_merge_on PND E1 E0') A1 A2 A3 A4).
  rewrite A5. exact (atoms_ok_agree 64 E0' Es _ AGs T3 FACTS'). }
apply (st_ok_pin_regU Es AGi4.SSK3 ms3 10%bv (SLit 1) HS4); [intros X; discriminate X|].
pose proof (st_ok_reg tfibsegs Es AGi4.SSK3 ms3 10%bv HS4) as R. unfold YP0e.U. rewrite <- R. unfold ms3. cbn [ms_regs mkst]. rewrite HA1. reflexivity.
Qed.
Lemma HS6 : st_ok tfibsegs Es (mkSS 0x3793c (sr_set (ss_regs AGi4.SSK3) 10%bv (SLit 1)) [AGi4.K3bst; AGi4.K3scr; AGi4.K3top] None (ss_facts AGi4.SSK3)) ms3.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U_. pose proof Hso as (O1 & O2 & O3).
pose proof (st_ok_mem_surgery Es _ ms3 [AGi4.K3bst; AGi4.K3scr; AGi4.K3top] HS5) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. apply X. clear X.
intros (HW & HF & HP). unfold ms3 in *. cbn [ms_mem mkst] in *.
assert (BV : base_val Es (Some 2%nat) = sp0) by (cbn [base_val]; exact Es2).
assert (BV13 : base_val Es (Some 13%nat) = SOv) by (cbn [base_val]; rewrite (HEs 13%nat ltac:(cbv; lia)); reflexivity).
split; [reflexivity|]. split.
- apply Forall_cons; [exact (Forall_inv HF)|]. apply Forall_cons; [|exact (Forall_inv_tail (Forall_inv_tail HF))].
pose proof (Forall_inv (Forall_inv_tail HF)) as (R1 & R2 & R3 & R4). cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in R1, R2, R3, R4.
rewrite BV in R1, R2, R3, R4.
unfold region_ok, AGi4.K3scr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV.
split; [clear - Hlo K1; unfold AFSTACK, kHighMemBeg in *; unfold sp0 in *; lia|]. split; [clear - U_; unfold sp0 in *; lia|]. split; [|exact R4].
intros o Ho. apply apresent_writable; [clear - Ho Hlo K1 U_; unfold TFIB_IMG_END, AFSTACK, kHighMemBeg in *; unfold sp0 in *; lia|]. apply PRES'. clear - Ho; unfold AFSTACK; lia.
- unfold AGi4.K3bst, AGi4.K3scr, AGi4.K3top. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite BV, BV13. repeat split; unfold sp0, SOv in *; lia.
Qed.
Lemma HS7 : st_ok tfibsegs Es AGi4.MK_AFTER ms3.
Proof.
rewrite AGi4.MK_AFTER_eq3. pose proof AGi4.tlREG0K_facts as (T1 & T2 & T3).
pose proof (st_ok_mem_surgery Es _ ms3 ([AGi4.K3bst; AGi4.K3scr; AGi4.K3top] ++ TAIL0KG) HS6) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. apply X. clear X.
intros HM. pose proof PAIRS' as PP. unfold REG0KG in PP. cbn [pairwise_disjoint] in PP. destruct PP as (A0 & A1 & A2 & PT).
pose proof REG0' as RR. unfold REG0KG in RR. apply Forall_inv_tail, Forall_inv_tail, Forall_inv_tail in RR.
apply mem_ok_app; [exact HM | exact T2 | | |].
- apply Forall_forall. intros r Hr. apply (region_ok_agree_on_lt r); [exact Hr|]. exact (proj1 (Forall_forall _ _) RR r Hr).
- exact (pairwise_disjoint_agree 64 E0' Es TAIL0KG AGs T1 PT).
- intros r Hr.
  assert (Hb : obase_lt 64 (YP09.r_base r) = true).
  { pose proof (proj1 (forallb_forall _ _) T1 r Hr) as Ha. unfold region_atoms_lt in Ha. apply andb_prop in Ha as [Ha _]. exact Ha. }
  assert (D0 : extent_disjoint Es R_soG r) by (apply (extent_disjoint_agree 64 E0' Es R_soG r AGs eq_refl Hb); apply (all_disjoint_In E0' _ _ r A0); right; right; exact Hr).
  assert (D1 : extent_disjoint Es R_scrG r) by (apply (extent_disjoint_agree 64 E0' Es R_scrG r AGs eq_refl Hb); apply (all_disjoint_In E0' _ _ r A1); right; exact Hr).
  assert (D2 : extent_disjoint Es R_slotG r) by (apply (extent_disjoint_agree 64 E0' Es R_slotG r AGs eq_refl Hb); apply (all_disjoint_In E0' _ _ r A2); exact Hr).
  cbn [all_disjoint]. split; [|split; [|split; [|exact I]]].
  + exact (AFhm.extent_disjoint_ext3 Es r R_soG AGi4.K3bst eq_refl (AFhm.extent_disjoint_sym Es R_soG r D0)).
  + exact (AFhm.extent_disjoint_ext3 Es r R_scrG AGi4.K3scr eq_refl (AFhm.extent_disjoint_sym Es R_scrG r D1)).
  + exact (AFhm.extent_disjoint_ext3 Es r R_slotG AGi4.K3top eq_refl (AFhm.extent_disjoint_sym Es R_slotG r D2)).
Qed.
Lemma ATJ : AGj6.at_ST W' ly' regs0 memR mdR n tr cl cnt' v' csz j0 jb j1 j2 j3 j4 AGi4.MK_AFTER W' cR.
Proof.
split; [reflexivity|]. exists msR, (m_vm_materialized mdR), Es. split; [reflexivity|]. split; [exact HEs|].
split; [unfold msR; rewrite restrict_mkst_fx; exact HS7|].
split; [intros x _; reflexivity|]. split; [exact PRES' | exact BUF'].
Qed.
(* AGin.TAILJ with cf = 0: AGj7.segJ to the join state, then AGjg.tail_inner, whose can_fill = 0 case ends in TkCf0's
   AGc2.seg2cf0_even / _odd (post AGc0.at_RET0K, read back as at_RETkw by AGjg.at_RET0K_w). *)
Lemma TAILJ0 : amreal tfibsegs (malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs 0x3793c regsR memR mdR)
(fun r W'' c'' => exists odd z, r = (ck_user (new_chunk cl off n), st_final S' cl l off n tr z) /\
(odd = true <-> AGj6.NPv n mod 8 <> 0) /\
AGif0n.at_RETkw W' ly' regs0 memR mdR n cl cnt' v' jb DPOST' odd z W'' c'').
Proof.
replace (cfg_at tfibsegs 0x3793c regsR memR mdR) with cR by (unfold cfg_at, cR, msR; rewrite with_vm_backing_id; reflexivity).
eapply amreal_SRr_pre.
{ exact (@AGj7.segJ _ _ W' ly' regs0 memR mdR n tr cl cnt' v' csz j0 jb j1 j2 j3 j4 Hcl Hv' Hcnt' Hv2' LY' IMG' Hsp' Htrlen Hbp' DPOST' Nrange l off W' cR ATJ). }
intros W2 c2 _ HJ. pose proof (proj1 HJ) as EW. subst W2.
exact (@AGjg.tail_inner _ _ W' ly' regs0 memR mdR n tr cl cnt' v' csz j0 jb j1 j2 j3 j4 Hcl Hv' Hcnt' Hjb Hv2' LY' IMG' Hn Htp (or_introl Hcf0) Hra Hsp' Htrlen Hso' Hbp' Hinst DPOST' HKpres' HSKpres' HPB250' Nrange Hcl_def B S' l off stag Hgp Hcache' HDEP HDAOK c2 HJ).
Qed.
End gj.
(* The join leaf (AGin.LEAFJ; the remaining arguments are the junk values of the join state). *)
Local Abbreviation LEAFJ := (AGin.LEAFJ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 regsU mem0 md0 n tr HARX HRP Nrange Hmiss Hnnmax HBB Htr Htrlen Hsp Hso Hbp HUo ms1 mat1 Em HEm HSC MEQW PRESW S' ly' W' memR mdR HARXp CIp HBBp Hly HWLE HSIO HFRA HFRR HPRR l off Hcache').
Lemma JOIN : amreal tfibsegs (malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs 0x3793c regsR memR mdR) PL.
Proof.
destruct (@AGjd.vw_junk_values _ _ B W' ly' inst memR n cl cnt' v' TS HV' Nrange Hcl_class)
  as (j0 & j1 & j2 & j3 & j4 & jb & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hjb & Hjb_def).
eapply amreal_mono; [| eapply TAILJ0; eassumption].
intros r W'' c'' H. eapply LEAFJ; eassumption.
Qed.
Local Abbreviation LEAFJ_e := (AGin.LEAFJ_e B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree IFM EAI EAS EAD inst ly S W regs0 regsU mem0 md0 n tr HARX HRP Nrange Hmiss Hnnmax HBB Htr Htrlen Hsp Hso Hbp HUo ms1 mat1 Em HEm HSC MEQW PRESW S' ly' W' memR mdR HARXp CIp HBBp Hly HWLE HSIO HFRA HFRR HPRR HERRp l off Hcache').
Lemma JOIN_e : amreal tfibsegs (malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs 0x3793c regsR memR mdR) PL_e.
Proof.
destruct (@AGjd.vw_junk_values _ _ B W' ly' inst memR n cl cnt' v' TS HV' Nrange Hcl_class)
  as (j0 & j1 & j2 & j3 & j4 & jb & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hjb & Hjb_def).
eapply amreal_mono; [| eapply TAILJ0; eassumption].
intros r W'' c'' H. eapply LEAFJ_e; eassumption.
Qed.
End g.
End g0.
End f.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* AGin.missk_core, over MISS1 / JOIN above. *)
Lemma missk_core : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0)
(alloc_leaf tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr).
Proof.
assert (CORE : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0) PL).
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
  rleaf ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1) r W1 c1)).
- (* MISS1, then the refill callee *)
  eapply amreal_SRr_pre; [exact MISS1|]. intros W1 c1 _ HC.
  destruct HC as (-> & ms1 & mat1 & Em & -> & HEm & HSC & MEQW & PRESW & BUFW).
  assert (SHAPE : ms1 = mkst (ms_regs ms1) (w64 0x37ddc) (ms_mem ms1) (seg_rom tfibsegs)) by (eapply ms1_shape; eassumption).
  assert (RR : amreal tfibsegs (rtree cl S1) W (cfg_at tfibsegs A_Refill (ms_regs ms1) (ms_mem ms1) (md0' mat1))
    (rleaf ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1))) by (eapply REFILL; eassumption).
  unfold cfg_at, A_Refill in RR. rewrite SHAPE at 1.
  eapply amreal_mono; [| exact RR]. intros r W2 c2 HRL. exists ms1, mat1, Em. split; [|exact HRL]. repeat (split; [assumption|]). exact BUFW.
- (* the post-refill branch on the class cache *)
  intros [] Sp W1 c1 (ms1 & mat1 & Em & (HEm & HSC & MEQW & PRESW & BUFW) & HRL).
  destruct HRL as (ly' & regsR & memR & mdR & -> & HARXp & HLPp & CIp & HBBp & Hly & HWLE & HAREGS & HSIO & HFRA & HFRR & HPRR & HA0e).
  cbn [snd] in *.
  assert (RA : raZ (ms_regs ms1) = 0x3793c) by (eapply RAZ1; eassumption). rewrite RA.
  destruct (pc_chunks (cache Sp cl)) as [|x t] eqn:El.
  + assert (HA0 : getr regsR 10 = w64 0) by (rewrite HA0e; try rewrite El; reflexivity).
    eapply OOMJ; eassumption.
  + assert (LX : exists l off, x :: t = l ++ [off]) by (exists (List.removelast (x :: t)), (List.last (x :: t) 0); apply List.app_removelast_last; discriminate).
    destruct LX as (l & off & LX). rewrite LX in El.
    assert (HA1 : getr regsR 10 = w64 1) by (rewrite HA0e; try rewrite El; destruct l; reflexivity).
    eapply JOIN; eassumption.
}
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0) PL CORE)].
intros r W' c' [HL HP]. exact (HL HP).
Qed.
(* ERRNO-KEPT twin of missk_core (ErrnoG.alloc_leaf_e). *)
Lemma missk_core_e : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0)
(ErrnoG.alloc_leaf_e tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr).
Proof.
assert (CORE : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0) PL_e).
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
  ErrnoG.rleaf_e B ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1) r W1 c1)).
- (* MISS1, then the refill callee *)
  eapply amreal_SRr_pre; [exact MISS1|]. intros W1 c1 _ HC.
  destruct HC as (-> & ms1 & mat1 & Em & -> & HEm & HSC & MEQW & PRESW & BUFW).
  assert (SHAPE : ms1 = mkst (ms_regs ms1) (w64 0x37ddc) (ms_mem ms1) (seg_rom tfibsegs)) by (eapply ms1_shape; eassumption).
  assert (RR : amreal tfibsegs (rtree cl S1) W (cfg_at tfibsegs A_Refill (ms_regs ms1) (ms_mem ms1) (md0' mat1))
    (ErrnoG.rleaf_e B ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1))) by (eapply REFILL_e; eassumption).
  unfold cfg_at, A_Refill in RR. rewrite SHAPE at 1.
  eapply amreal_mono; [| exact RR]. intros r W2 c2 HRL. exists ms1, mat1, Em. split; [|exact HRL]. repeat (split; [assumption|]). exact BUFW.
- (* the post-refill branch on the class cache *)
  intros [] Sp W1 c1 (ms1 & mat1 & Em & (HEm & HSC & MEQW & PRESW & BUFW) & HRL).
  destruct HRL as (ly' & regsR & memR & mdR & -> & HARXp & HLPp & CIp & HBBp & Hly & HWLE & HAREGS & HSIO & HFRA & HFRR & HERRp & HPRR & HA0e).
  cbn [snd] in *.
  assert (RA : raZ (ms_regs ms1) = 0x3793c) by (eapply RAZ1; eassumption). rewrite RA.
  destruct (pc_chunks (cache Sp cl)) as [|x t] eqn:El.
  + assert (HA0 : getr regsR 10 = w64 0) by (rewrite HA0e; try rewrite El; reflexivity).
    eapply OOMJ_e; eassumption.
  + assert (LX : exists l off, x :: t = l ++ [off]) by (exists (List.removelast (x :: t)), (List.last (x :: t) 0); apply List.app_removelast_last; discriminate).
    destruct LX as (l & off & LX). rewrite LX in El.
    assert (HA1 : getr regsR 10 = w64 1) by (rewrite HA0e; try rewrite El; destruct l; reflexivity).
    eapply JOIN_e; eassumption.
}
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0) PL_e CORE)].
intros r W' c' [HL HP]. exact (HL HP).
Qed.
End c.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The theorem, can_fill = 0: from alloc_pre at Allocate's entry (a5 = 0), the virtual register file
   regs0 := vregs regs n inst bp (AGin.alloc_missk with cf = 0). *)
Theorem alloc_missk0 : forall inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 0 inst so bp ly S W regs mem md n tr ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x33118 regs mem md)
(alloc_leaf tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Proof.
intros inst so bp ly S W regs mem md n tr PRE Nrange Hmiss.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres0 & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hn0 & Hlive).
unfold spZ, raZ, AFSTACK_G in *. rewrite (ts_tp B TS) in Htp.
pose proof (Finst inst ly S W mem md HARX) as HIO. pose proof HIO as (HIO1 & HIO2 & HIO3).
assert (Hnn : n < nmax) by lia.
assert (FP0 : from_primary n = true) by (eapply AGin.FP; eassumption).
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
change (cfg_at tfibsegs 0x33118 regs mem md) with (cfg_at tfibsegs A_Allocate regs mem md).
eapply (missk_core inst ly S W regs0 regs mem md n tr); eassumption.
Qed.
(* The k-path MISS arm for can_fill cf in {0, 1}: alloc_missk0 (cf = 0) or AGin.alloc_missk (cf = 1). *)
Theorem alloc_missk_cf : forall cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 cf inst so bp ly S W regs mem md n tr ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x33118 regs mem md)
(alloc_leaf tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Proof.
intros cf inst so bp ly S W regs mem md n tr [-> | ->].
- exact (alloc_missk0 inst so bp ly S W regs mem md n tr).
- exact (AGin.alloc_missk B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TS rtree IFM inst so bp ly S W regs mem md n tr).
Qed.
(* ERRNO-KEPT twins of alloc_missk0 / alloc_missk_cf (ErrnoG.alloc_leaf_e). *)
Theorem alloc_missk0_e : forall inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 0 inst so bp ly S W regs mem md n tr ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x33118 regs mem md)
(ErrnoG.alloc_leaf_e tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Proof.
intros inst so bp ly S W regs mem md n tr PRE Nrange Hmiss.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres0 & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hn0 & Hlive).
unfold spZ, raZ, AFSTACK_G in *. rewrite (ts_tp B TS) in Htp.
pose proof (Finst inst ly S W mem md HARX) as HIO. pose proof HIO as (HIO1 & HIO2 & HIO3).
assert (Hnn : n < nmax) by lia.
assert (FP0 : from_primary n = true) by (eapply AGin.FP; eassumption).
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
change (cfg_at tfibsegs 0x33118 regs mem md) with (cfg_at tfibsegs A_Allocate regs mem md).
eapply (missk_core_e inst ly S W regs0 regs mem md n tr); eassumption.
Qed.
Theorem alloc_missk_cf_e : forall cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 cf inst so bp ly S W regs mem md n tr ->
0 <= n <= 48 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x33118 regs mem md)
(ErrnoG.alloc_leaf_e tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Proof.
intros cf inst so bp ly S W regs mem md n tr [-> | ->].
- exact (alloc_missk0_e inst so bp ly S W regs mem md n tr).
- exact (AGin.alloc_missk_e B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TS rtree IFM IFME EAI EAS EAD inst so bp ly S W regs mem md n tr).
Qed.
End b.
End a.
