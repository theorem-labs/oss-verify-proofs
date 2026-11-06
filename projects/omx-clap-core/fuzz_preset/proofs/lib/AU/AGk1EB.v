(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGk1E.v (a working branch 29b7505aa27, file sha256 2bfaa2bc9453) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53; pin f8f98a95bc52); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin B (pinned fuzz_preset.asan-ubsan f8f98a95bc52, twin 3b5e1a099b53; this file at 74f20580f552) to B' (#102 pin d663f82d7f48, twin c90d4fa54d43) by the relocation route of record, frozen alreloc a5c53bb2bed4ad03 (a Theorem Labs lane's internal file alreloc.py.frozen-a5c53bb2bed4ad03), --assume-source, --resolve resolve-B102.txt (sha256 5cd2316e3413; internal record) (0 lines name this file); 0 numerals changed. *)
(* The errno-kept twin of the miss arms' shared OOM tail AGk1.miss_oom_tail: the same tail, concluding
   ErrnoG.alloc_leaf_e (AllocG.alloc_leaf plus errno kept on the grant branch) in place of alloc_leaf.

   The tail ends in the refusal leaf (a0 = 0, the result (PNull, S')), so alloc_leaf_e's errno conjunct
   (fst r <> PNull -> errno_kept ..) is vacuous there: [alloc_leaf_e_null] closes it from alloc_leaf.
   AGk1's Section variables and hypotheses, in AGk1's order; no add-on and no ErrnoApart Prop.  The tail's steps are
   AGk1's lemmas, cited (ATN: the symbolic state at the refill's return; LEAFN: the OOM leaf); only miss_oom_tail's
   five-line script is copied, with the leaf mapped through alloc_leaf_e_null.
   Also the two bridges into alloc_leaf_e that the miss arms' twins (AGimE, AGim0E) use: [alloc_leaf_e_null] (a
   refusal result) and [alloc_leaf_e_of] (alloc_leaf, and errno kept in the memory of the returned configuration on
   the grant branch). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGhy AGhz AGi4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFi3 AllocG AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoG.
(* The original tail (AGk1.miss_oom_tail and its leaf lemmas), used qualified. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGk1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The bridges into alloc_leaf_e.                                                                                    *)
(* A refusal result (fst r = PNull): alloc_leaf_e's errno conjunct is about the grant branch only. *)
Lemma alloc_leaf_e_null : forall (segs : list Segment) B mt ARX AOX lpost oomb inst ly S (W : world segs) regs mem md n tr
(r : sptr * astate) (W' : world segs) c',
fst r = PNull ->
alloc_leaf segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c' ->
alloc_leaf_e segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c'.
Proof.
intros segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c' Hr (ly' & regs' & mem' & md' & Hc & HP & HR & HL & HT & HO).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [intros X; exfalso; exact (X Hr)|].
split; [exact HR|]. split; [exact HL|]. split; [exact HT | exact HO].
Qed.

(* alloc_leaf, and on the grant branch errno kept from the entry memory to the memory of the returned configuration. *)
Lemma alloc_leaf_e_of : forall (segs : list Segment) B mt ARX AOX lpost oomb inst ly S (W : world segs) regs mem md n tr
(r : sptr * astate) (W' : world segs) c',
alloc_leaf segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c' ->
(fst r <> PNull -> forall regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' -> errno_kept B mem mem') ->
alloc_leaf_e segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c'.
Proof.
intros segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & HR & HL & HT & HO) HE.
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [intros X; exact (HE X regs' mem' md' Hc)|].
split; [exact HR|]. split; [exact HL|]. split; [exact HT | exact HO].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* AGk1's section b: the same variables and hypotheses, in AGk1's order.                                              *)
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
Variable rtree : Z -> M unit.
Hypothesis IFM : AGif0n.AIfaceM B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree.
Hypothesis TS : TfibSyms B.

(* The caller at Allocate's entry: the virtual register file regs0 of the walk (atom 2 = the entry sp, 13 = the stack
   object) and the entry registers regsU. *)
Variables (inst : Z) (ly : alayout) (S : astate) (W : world tfibsegs).
Variables (regs0 regsU : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (tr : list Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let cl : Z := chunk_class n.
Hypothesis HARX : ARX inst ly S W mem0 md0.
Hypothesis Hn0 : 0 <= n.
Hypothesis FP : from_primary n = true.
Hypothesis LY : layout_ok ly.
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Hso : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly /\ SOv mod 8 = 0.
Hypothesis HUo : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr regsU r = getr regs0 r.

(* The refill call: its registers, memory and model (if_refill's premises at the call). *)
Variables (regsC : bvmap 5 word) (memC : word -> option byte) (mdC : Model).
Hypothesis SPC : spZ regsC = sp0 - 176.
Hypothesis AGC : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> aview tfibsegs (w_H W) memC a = aview tfibsegs (w_H W) mem0 a.
Hypothesis RAWC : forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) ->
  ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) -> memC x = mem0 x.
Hypothesis PRESC : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) memC a.
Hypothesis SIOC : same_io md0 mdC.

(* The refill's refusal: rleaf at the post-refill state S' (layout ly' >= ly), with the class cache still empty and
   a0 = 0. *)
Variables (S' : astate) (ly' : alayout) (W' : world tfibsegs) (regsR : bvmap 5 word) (memR : word -> option byte) (mdR : Model).
Hypothesis HARXp : ARX inst ly' S' W' memR mdR.
Hypothesis HLPp : lpost S'.
Hypothesis Hly : layout_le (length (st_secs S)) ly ly'.
Hypothesis HWLE : wle W W'.
Hypothesis HSIO : same_io mdC mdR.
Hypothesis HFRA : forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly' S' a -> ~ (spZ regsC - RSTACK <= a < spZ regsC) ->
  aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) memC a.
Hypothesis HFRR : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' S' (bv_unsigned x) ->
  ~ (spZ regsC - RSTACK <= bv_unsigned x < spZ regsC) -> memR x = memC x.
Hypothesis HPRR : forall a, spZ regsC - RSTACK <= a < spZ regsC -> apresent (w_H W') memR a.
Hypothesis Hc0 : pc_chunks (cache S' cl) = [].
Hypothesis HA0 : getr regsR 10 = w64 0.

(* The symbolic state at the refill's return, and the segment run to the ret. *)
Let ms3 : machine_state := mkst regsR (w64 A_REFILL_RET) (mrestrict (w_H W') memR) (seg_rom tfibsegs).
Variables (E0m E1 : env) (SS3 MSN0 : sstate) (r1 r2 r3 : YP09.region) (WN : Z -> Prop).
Hypothesis HE0_2 : ew E0m 2 = getr regs0 2.
Hypothesis HE0_13 : ew E0m 13 = getr regs0 13.
Hypothesis HE1 : forall k, (k < aHAV)%nat -> ew E1 k = ew E0m k.
Hypothesis HS3 : st_ok tfibsegs E1 SS3 ms3.
Hypothesis Hmem3 : ss_mem SS3 = [r1; trim_lo r2 (-176); r3].
Hypothesis HMS : MSN0 = mkSS (ss_pc SS3) (sr_set (ss_regs SS3) 10%bv (SLit 0)) ([r1; r2; r3] ++ AGi4.NREGS) (ss_resv SS3) (ss_facts SS3).
Hypothesis Hx1 : ext3 r1 = ext3 R_soG.
Hypothesis Hx2 : ext3 r2 = ext3 R_scrG.
Hypothesis Hx3 : ext3 r3 = ext3 R_slotG.
Hypothesis Hwf : regions_wf [r1; r2; r3] = true.
Hypothesis Hc2 : YP09.r_chunks (trim_lo r2 (-176)) = YP09.r_chunks r2.
Hypothesis HWN : forall a, WN a -> (sp0 - AFSTACK <= a < sp0) \/ (TFIB_OOM <= a < TFIB_OOM + 1) \/ (TFIB_ERRNO <= a < TFIB_ERRNO + 4).
Hypothesis SEGN : forall W0 c, AGk1.STN E0m W' regs0 memR mdR MSN0 W0 c -> SRr tfibsegs W0 c (AGk1.RETN WN W' regs0 memR mdR).

Let msR : machine_state := mkst regsR (w64 A_REFILL_RET) memR (seg_rom tfibsegs).
Let cR : config := mkCfg msR (with_vm_backing (m_vm_lazy mdR) (m_vm_materialized mdR) mdR).

(* AGk1's section-b lemmas, cited. *)
Local Abbreviation ATN := (@AGk1.ATN _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM TS inst ly S W regs0 mem0 md0 n
  HARX Hn0 FP LY Hsp Hso regsC memC SPC PRESC S' ly' W' regsR memR mdR HARXp Hly HFRA HPRR Hc0 HA0 E0m E1 SS3 MSN0 r1 r2 r3
  HE0_2 HE0_13 HE1 HS3 Hmem3 HMS Hx1 Hx2 Hx3 Hwf Hc2).
Local Abbreviation LEAFN := (@AGk1.LEAFN _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM TS inst ly S W regs0 regsU mem0 md0 n tr
  HARX LY Hsp HUo regsC memC mdC SPC AGC RAWC PRESC SIOC S' ly' W' memR mdR HARXp HLPp Hly HWLE HSIO HFRA HFRR HPRR Hc0 WN HWN).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The OOM tail, concluding alloc_leaf_e. *)
Theorem miss_oom_tail_e : amreal tfibsegs (AGif0n.malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs A_REFILL_RET regsR memR mdR)
(fun r W'' c'' => (exists trc, apath (mt n tr S) trc r /\ gflag trc = true) ->
  alloc_leaf_e tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr r W'' c'').
Proof.
(* copy of AGk1.v:338-341, + errno *)
unfold AGif0n.malloc_join_t. rewrite bind_assoc_eq. eapply amreal_pure; [exact (pop_miss S' cl Hc0)|]. eapply amreal_pure; [reflexivity|].
unfold AGif0n.malloc_K_t. cbn [amreal].
replace (cfg_at tfibsegs A_REFILL_RET regsR memR mdR) with cR by (unfold cfg_at, cR, msR; rewrite with_vm_backing_id; reflexivity).
eapply SRr_mono; [exact (SEGN W' cR ATN)|]. intros W6 c6 _ HR.
exact (fun HPATH => alloc_leaf_e_null tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr (PNull, S') W6 c6 eq_refl
  (LEAFN W6 c6 HR HPATH)).
Qed.
End b.
End a.
