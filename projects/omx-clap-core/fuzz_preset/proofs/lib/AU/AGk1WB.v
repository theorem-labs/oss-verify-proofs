(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30: AGk1W, the AIfaceMw variant of
   cgif/cgif_file_fuzzer lib/AGk1.v (file sha256 fb649113cf46; donor not released): the refill's stack window is the Section variable RW (0 <= RW, 176 + RW <= AFSTACK: hypothesis
   RWB) of MnRefillW.v, not RSTACK = 1024.  Same proof script; the changes are AIfaceM -> AIfaceMw (fields if_ ->
   ifw_), the refill leaves -> their _w forms at RW, RSTACK -> RW, the refill-window steps through
   MnRefillW.win_af_w and the other frame lia steps under RWB, RW (and RWB) in the explicit arguments of the W
   twins' lemmas, and the imports of the W twins.  AGk1.v is unchanged.  rule 24: no function proved (kind:
   re-statement of a proved miss walk over a wider refill window). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGk1W.v (a working branch 3295f3a9fd5f, file sha256 819f6f3596ad) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53; pin f8f98a95bc52); module paths changed; its 2 image addresses moved by code-verified function pairs (1 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py); 1 hand maps (agreloc-resolve-B.tsv (sha256 82a29203ac12; internal record), each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin B (pinned fuzz_preset.asan-ubsan f8f98a95bc52, twin 3b5e1a099b53; this file at bf3d4cdda1c5) to B' (#102 pin d663f82d7f48, twin c90d4fa54d43) by the relocation route of record, frozen alreloc a5c53bb2bed4ad03 (a Theorem Labs lane's internal file alreloc.py.frozen-a5c53bb2bed4ad03), --assume-source, --resolve resolve-B102-r6g2.txt (sha256 32fdfbf5eca4; internal record) (0 lines name this file); 2 numerals changed. *)
(* The OOM tail of the MISS arms of the frame-generic Allocate contract (AllocG.alloc_leaf), over the miss fields
   AGif0n.AIfaceM: from the refill callee's refusal (rleaf with a0 = 0, the class cache still empty) at the refill's
   return into Allocate, the run to Allocate's ret and the leaf's out-of-memory case (a0 = 0, the out-of-memory byte
   set, errno left to the caller), with the aview frame clause and the raw frame clause of alloc_post.

   Ported from cgif_file's released malloc_missg (YFim.v Section h: HSN, ATN, TAILN; YFin.v the same for the k path)
   with the caller's frame made abstract.  It is the one tail of the g miss arm (AGim, n in 49..64512) and the k miss
   arm (AGin, n <= 48), for both call sites (can_fill = 0 and 1: the tail does not read a5).  The two arms differ only
   in the symbolic state at the refill's return and in the segment lemma that runs it to the ret; both are parameters:
   - [SS3] (AGi4.SS3 / AGi4.SSK3) with its three stack regions [r1 r2 r3] (AGi4.R3bst / R3scr / R3top, the k twins
     K3bst / K3scr / K3top), and [MSN0] (AGi4.MS_N0 / AGi4.MK_N0) = SS3 with a0 := 0 and the out-of-memory regions
     AGi4.NREGS;
   - [SEGN]: the segment run from MSN0 to the ret (AGiv.segN / AGj9.segN), stated over [STN] / [RETN] below, which
     are AGiv.at_STN / AGiv.at_RETN (and AGj9's) with the walk's environment [E0m] and write window [WN] abstract. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MnRefillW.
(* field round 3: MnRefillW's records take the unit's CfImg (the RELRO bounds of arodata_ok_cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfNames.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Ltac bvne := first [cbn; lia | vm_compute; congruence | intros X; vm_compute in X; discriminate X].
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : YGcfNames.CfImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Machine helper lemmas (generic), as in the released malloc_missg.                                                 *)
Local Lemma apresent_aview_some : forall (H : word -> bool) m a, TFIB_IMG_END <= a < 2 ^ 64 -> apresent H m a -> aview tfibsegs H m a <> None.
Proof. intros H m a Ha Hp. destruct (apresent_mbyte H m a Hp) as [b Hb]. unfold aview. rewrite Hb. cbn. discriminate. Qed.
Local Lemma aview_some_apresent : forall (H : word -> bool) m a, TFIB_IMG_END <= a < 2 ^ 64 -> aview tfibsegs H m a <> None -> apresent H m a.
Proof.
intros H m a Ha Hv. destruct (mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:E.
- exact (mbyte_high_apresent H m a b Ha E).
- exfalso. apply Hv. unfold aview. rewrite E. reflexivity.
Qed.
Local Lemma apresent_xfer : forall (H H' : word -> bool) m m' a, TFIB_IMG_END <= a < 2 ^ 64 ->
aview tfibsegs H' m' a = aview tfibsegs H m a -> apresent H m a -> apresent H' m' a.
Proof. intros H H' m m' a Ha E Hp. apply aview_some_apresent; [exact Ha|]. rewrite E. exact (apresent_aview_some H m a Ha Hp). Qed.
Local Lemma same_io_wvb : forall md mat, same_io md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. apply same_io_with_vm_backing. Qed.
Local Lemma same_io_tr : forall m1 m2 m3, same_io m1 m2 -> same_io m2 m3 -> same_io m1 m3.
Proof. intros m1 m2 m3 (A1 & A2 & A3 & A4) (C1 & C2 & C3 & C4). unfold same_io. rewrite C1, C2, C3, C4. repeat split; assumption. Qed.
Local Lemma rw_writable : forall (m : word -> option byte) a, 0xa2000 <= a < 0x601000 -> writable_at tfibsegs m a.
Proof. intros m a Ha. unfold writable_at. apply YB13.tfib_rw_window. rewrite unsigned_lit_small by lia. exact Ha. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The segment lemmas' pre and post (AGiv.at_STN / at_RETN, AGj9.at_STN / at_RETN), with the walk's environment
   [E0] and the run's write window [WN] as parameters: AGiv.at_STN W ly regs0 mem0 md0 n tr cl cnt v csz j0 jb j1 j2 j3
   j4 kz is STN (AGis.E0 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz) W regs0 mem0 md0, AGiv.at_RETN W regs0 mem0 md0
   is RETN (AGiv.WINN regs0) W regs0 mem0 md0, and the same for AGj9 (AGj6.E0, AGj9.WINN). *)
Definition STN (E0 : env) (W : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
(ss : sstate) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall k, (k < aHAV)%nat -> ew E' k = ew E0 k) /\
st_ok tfibsegs E' ss (restrict (w_H W) ms) /\
ms_mem ms = mem0 /\
(forall a, bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W) (ms_mem ms) a).
Definition RETN (WN : Z -> Prop) (W : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
(W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 10 = Z_to_bv 64 0 /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) /\
(forall x : word, ~ WN (bv_unsigned x) -> mem' x = mem0 x) /\
(forall a, bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W) mem' a) /\
val_mem tfibsegs (mrestrict (w_H W) mem') TFIB_OOM 1 1.

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
Variable rtree : Z -> M unit.
Variable RW : Z.
Hypothesis RWB : 0 <= RW /\ 176 + RW <= AFSTACK.
Hypothesis IFM : MnRefillW.AIfaceMw B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW.
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
Hypothesis HFRA : forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly' S' a -> ~ (spZ regsC - RW <= a < spZ regsC) ->
  aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) memC a.
Hypothesis HFRR : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' S' (bv_unsigned x) ->
  ~ (spZ regsC - RW <= bv_unsigned x < spZ regsC) -> memR x = memC x.
Hypothesis HPRR : forall a, spZ regsC - RW <= a < spZ regsC -> apresent (w_H W') memR a.
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
Hypothesis SEGN : forall W0 c, STN E0m W' regs0 memR mdR MSN0 W0 c -> SRr tfibsegs W0 c (RETN WN W' regs0 memR mdR).

Let msR : machine_state := mkst regsR (w64 A_REFILL_RET) memR (seg_rom tfibsegs).
Let cR : config := mkCfg msR (with_vm_backing (m_vm_lazy mdR) (m_vm_materialized mdR) mdR).

Local Lemma STK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof. pose proof (lo_top ly LY) as (_ & _ & _ & H4 & _ & _ & H7). split; [exact H7 | exact H4]. Qed.
Local Lemma Usp : 0 <= sp0 < 2 ^ 64. Proof. unfold sp0. apply u64_range. Qed.
Local Lemma SP_U : bv_unsigned (getr regsU 2) = sp0. Proof. rewrite (HUo 2%bv) by bvne. reflexivity. Qed.
(* The callee-saved registers a post keeps from regs0 are the entry regsU's. *)
Local Lemma CS_leaf : forall regs' : bvmap 5 word,
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) ->
aregs_preserved regsU regs'.
Proof.
intros regs' RCS r Hr. assert (HrZ : bv_unsigned (Z_to_bv 5 r) = r).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32. unfold acallee_saved in Hr. apply Z.mod_small. lia. }
rewrite (HUo (Z_to_bv 5 r)) by (rewrite HrZ; unfold acallee_saved in Hr; lia).
apply RCS. unfold acallee_saved in Hr.
assert (H18 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear - H18.
assert (E5 : forall k : Z, 0 <= k < 32 -> forall b : bv 5, bv_unsigned b = k -> Z_to_bv 5 k = b) by (intros k Hk b Hb; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 5) with 32; rewrite Z.mod_small by lia; symmetry; exact Hb).
destruct H18 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
[ rewrite (E5 2 ltac:(lia) 2%bv eq_refl) | rewrite (E5 3 ltac:(lia) 3%bv eq_refl) | rewrite (E5 4 ltac:(lia) 4%bv eq_refl)
| rewrite (E5 8 ltac:(lia) 8%bv eq_refl) | rewrite (E5 9 ltac:(lia) 9%bv eq_refl) | rewrite (E5 18 ltac:(lia) 18%bv eq_refl)
| rewrite (E5 19 ltac:(lia) 19%bv eq_refl) | rewrite (E5 20 ltac:(lia) 20%bv eq_refl) | rewrite (E5 21 ltac:(lia) 21%bv eq_refl)
| rewrite (E5 22 ltac:(lia) 22%bv eq_refl) | rewrite (E5 23 ltac:(lia) 23%bv eq_refl) | rewrite (E5 24 ltac:(lia) 24%bv eq_refl)
| rewrite (E5 25 ltac:(lia) 25%bv eq_refl) | rewrite (E5 26 ltac:(lia) 26%bv eq_refl) | rewrite (E5 27 ltac:(lia) 27%bv eq_refl) ];
cbn [In]; tauto.
Qed.
Local Lemma CFG_leaf : forall regs' mem' md', mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) md' = cfg_at tfibsegs (raZ regsU) regs' mem' md'.
Proof. intros regs' mem' md'. unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. rewrite (HUo 1%bv) by bvne. reflexivity. Qed.

(* --- The frame across the refill, at the post-refill layout ly'. --- *)
Local Lemma LyEq : ly_stk_lo ly' = ly_stk_lo ly /\ ly_stk_hi ly' = ly_stk_hi ly /\ ly_top ly' = ly_top ly /\ ly_T ly' = ly_T ly.
Proof. destruct Hly as (_ & _ & _ & HT & _ & _ & _ & _ & Htop & Hlo & Hhi & _). repeat split; assumption. Qed.
Local Lemma Hsp' : ly_stk_lo ly' + AFSTACK <= sp0 /\ ly_bot ly' < sp0 /\ sp0 <= ly_stk_hi ly' /\ sp0 mod 16 = 0.
Proof. pose proof LyEq as (E1' & E2' & E3' & _). pose proof Hsp as H. unfold ly_bot in *. rewrite E1', E2', E3'. exact H. Qed.
(* A stack address is owned neither at S (layout ly) nor at S' (layout ly'). *)
Local Lemma NOWN : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX ly S a /\ ~ AOX ly' S' a.
Proof.
intros a Ha. pose proof LyEq as (E1' & E2' & _). split.
- exact (MnRefillW.ifw_stack B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly S W mem0 md0 a HARX Ha).
- apply (MnRefillW.ifw_stack B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly' S' W' memR mdR a HARXp). rewrite E1', E2'. exact Ha.
Qed.
(* The refill keeps the caller's stack: any address in the stack, outside the callee window. *)
Local Lemma STKkept : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp0 - 176 - RW <= a < sp0 - 176) ->
  aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) memC a.
Proof.
intros a Ha Hnw. pose proof STK as [K1 K2]. destruct (NOWN a Ha) as [N1 N2].
apply (HFRA a); [clear - Ha K1 K2; unfold kHighMemBeg, kHighMemEnd in *; lia | exact N1 | exact N2 | rewrite SPC; exact Hnw].
Qed.
Local Lemma PRES' : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W') memR a.
Proof.
intros a Ha. pose proof Hsp as (S1' & S2' & S3' & S4'). pose proof STK as [K1 K2]. pose proof Usp as Us.
assert (Hhi' : TFIB_IMG_END <= a < 2 ^ 64) by (clear - Ha S1' K1 Us; unfold TFIB_IMG_END, AFSTACK, kHighMemBeg in *; unfold sp0 in *; lia).
assert (Hst : ly_stk_lo ly <= a < ly_stk_hi ly) by (clear - Ha S1' S3'; unfold AFSTACK, sp0 in *; lia).
destruct (Z_lt_le_dec a (sp0 - 176 - RW)) as [H1|H1]; [|destruct (Z_lt_le_dec a (sp0 - 176)) as [H2|H2]].
- apply (apresent_xfer (w_H W) (w_H W') memC memR a Hhi'); [apply STKkept; [exact Hst | lia] | exact (PRESC a Ha)].
- apply HPRR. rewrite SPC. lia.
- apply (apresent_xfer (w_H W) (w_H W') memC memR a Hhi'); [apply STKkept; [exact Hst | lia] | exact (PRESC a Ha)].
Qed.

(* --- The symbolic state at the refill's return with a0 = 0: SS3 with the out-of-memory regions. --- *)
Local Lemma HSN : st_ok tfibsegs E1 MSN0 ms3.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as Us. pose proof Hso as (O1 & O2 & O3).
assert (H4 : st_ok tfibsegs E1 (mkSS (ss_pc SS3) (sr_set (ss_regs SS3) 10%bv (SLit 0)) (ss_mem SS3) (ss_resv SS3) (ss_facts SS3)) ms3).
{ apply (st_ok_pin_regU E1 SS3 ms3 10%bv (SLit 0) HS3); [intros X; discriminate X|].
  pose proof (st_ok_reg tfibsegs E1 SS3 ms3 10%bv HS3) as R. unfold YP0e.U. rewrite <- R. unfold ms3. cbn [ms_regs mkst]. rewrite HA0. reflexivity. }
rewrite HMS. pose proof (st_ok_mem_surgery E1 _ ms3 ([r1; r2; r3] ++ AGi4.NREGS) H4) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. apply X. clear X H4.
intros (HW & HF & HP). rewrite Hmem3 in HF. unfold ms3 in *. cbn [ms_mem mkst] in *.
assert (BV : base_val E1 (Some 2%nat) = sp0) by (cbn [base_val]; rewrite (HE1 2%nat ltac:(cbv; lia)), HE0_2; reflexivity).
assert (BV13 : base_val E1 (Some 13%nat) = SOv) by (cbn [base_val]; rewrite (HE1 13%nat ltac:(cbv; lia)), HE0_13; reflexivity).
assert (X1 : YP09.r_base r1 = Some 13%nat /\ YP09.r_lo r1 = 0 /\ YP09.r_hi r1 = 16).
{ unfold ext3 in Hx1. injection Hx1 as Q1 Q2 Q3. rewrite Q1, Q2, Q3. split; [|split]; reflexivity. }
assert (X2 : YP09.r_base r2 = Some 2%nat /\ YP09.r_lo r2 = - AFSTACK /\ YP09.r_hi r2 = 0).
{ unfold ext3 in Hx2. injection Hx2 as Q1 Q2 Q3. rewrite Q1, Q2, Q3. split; [|split]; reflexivity. }
assert (X3 : YP09.r_base r3 = Some 2%nat /\ YP09.r_lo r3 = 0 /\ YP09.r_hi r3 = 0).
{ unfold ext3 in Hx3. injection Hx3 as Q1 Q2 Q3. rewrite Q1, Q2, Q3. split; [|split]; reflexivity. }
destruct X1 as (B1 & L1 & U1). destruct X2 as (B2 & L2 & U2). destruct X3 as (B3 & L3 & U3).
assert (OOM1 : val_mem tfibsegs (mrestrict (w_H W') memR) (TFIB_OOM + 1) 1 1).
{ pose proof (MnRefillW.ifw_mview B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly' S' W' memR mdR n HARXp Hn0 FP Hc0) as HMVp.
  pose proof (proj1 (Forall_forall _ _) (AGif0n.mv_const B W' ly' inst memR cl HMVp) (z1 (ANum (TFIB_OOM + 1)) 1)) as C.
  rewrite (ts_const B TS ly') in C. specialize (C ltac:(unfold Tfib_const; apply in_app_iff; right; apply in_app_iff; left; apply (nth_error_In _ 60); reflexivity)).
  exact (cell_holds_val_mem B ly' (w_H W') memR (ANum (TFIB_OOM + 1)) 1 (ANum 1) C). }
split.
{ rewrite regions_wf_app, Hwf. reflexivity. }
split.
- apply Forall_cons; [exact (Forall_inv HF)|]. apply Forall_cons.
  { pose proof (Forall_inv (Forall_inv_tail HF)) as (R1 & R2 & R3 & R4).
    change (YP09.r_base (trim_lo r2 (-176))) with (YP09.r_base r2) in R4. rewrite Hc2, B2, BV in R4.
    assert (WF2 : YP09.region_wf r2 = true) by (cbn [regions_wf] in Hwf; apply andb_prop in Hwf as [_ Hwf']; apply andb_prop in Hwf' as [Hwf' _]; exact Hwf').
    unfold YP09.region_wf in WF2. apply andb_prop in WF2 as [WF2 _]. apply andb_prop in WF2 as [_ WF2].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B2, L2, U2, BV.
    split; [clear - Hlo K1; unfold AFSTACK, kHighMemBeg in *; unfold sp0 in *; lia|]. split; [clear - Us; unfold sp0 in *; lia|]. split; [|exact R4].
    intros o Ho. rewrite L2, U2 in WF2.
    assert (Ho' : - AFSTACK <= o < 0) by (apply orb_prop in WF2 as [WF2|WF2]; [apply Z.leb_le in WF2; lia | apply andb_prop in WF2 as [W1 W2]; apply Z.leb_le in W1, W2; lia]).
    apply apresent_writable; [clear - Ho' Hlo K1 Us; unfold TFIB_IMG_END, AFSTACK, kHighMemBeg in *; unfold sp0 in *; lia|]. apply PRES'. clear - Ho'; unfold AFSTACK in *; lia. }
  apply Forall_cons; [exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HF)))|].
  unfold AGi4.NREGS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + unfold region_ok, lit1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold TFIB_OOM; lia|]. split; [unfold TFIB_OOM; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia |]. rewrite Z.add_0_l. exact OOM1.
  + unfold region_ok, AGi4.oomR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold TFIB_OOM; lia|]. split; [unfold TFIB_OOM; lia|]. split; [|apply Forall_nil]. intros o Ho. rewrite Z.add_0_l. apply rw_writable. unfold TFIB_OOM in *. lia.
  + unfold region_ok, AGi4.errR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold TFIB_ERRNO; lia|]. split; [unfold TFIB_ERRNO; lia|]. split; [|apply Forall_nil]. intros o Ho. rewrite Z.add_0_l. apply rw_writable. unfold TFIB_ERRNO in *. lia.
- unfold AGi4.NREGS, lit1, AGi4.oomR, AGi4.errR. cbn [pairwise_disjoint all_disjoint app]. unfold extent_disjoint.
  rewrite B1, L1, U1, B2, L2, U2, B3, L3, U3. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !BV, BV13. cbn [base_val].
  clear - Hlo Hhi K1 K2 Us O1 O2. unfold TFIB_OOM, TFIB_ERRNO, AFSTACK, kHighMemBeg, kHighMemEnd in *. unfold sp0, SOv in *. repeat split; lia.
Qed.
Local Lemma ATN : STN E0m W' regs0 memR mdR MSN0 W' cR.
Proof.
split; [reflexivity|]. exists msR, (m_vm_materialized mdR), E1. split; [reflexivity|]. split; [exact HE1|].
split; [unfold msR; rewrite restrict_mkst_fx; exact HSN|]. split; [reflexivity | exact PRES'].
Qed.

(* --- The OOM leaf, given its granted path: if_oom at S', and the frame back to the entry memory. --- *)
Local Definition PLN (r : sptr * astate) (W'' : world tfibsegs) (c'' : config) : Prop :=
(exists trc, apath (mt n tr S) trc r /\ gflag trc = true) ->
alloc_leaf tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr r W'' c''.
Local Lemma LEAFN : forall W'' c'', RETN WN W' regs0 memR mdR W'' c'' -> PLN (PNull, S') W'' c''.
Proof.
intros W'' c'' HR HPATH.
pose proof Hsp' as (Hlo' & Hbot' & Hhi' & Hal').
destruct HR as (-> & regs' & mem' & mat & -> & A0 & CS' & MEQ' & PRS' & VOOM). fold sp0 in PRS'.
assert (AVR : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> a <> TFIB_OOM -> ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4) ->
  aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W') memR a).
{ intros a Ra N1 N2 N3. apply aview_same. apply MEQ'. rewrite unsigned_lit_small by exact Ra.
  intros X. destruct (HWN a X) as [X1|[X1|X1]]; [exact (N1 X1) | apply N2; lia | exact (N3 X1)]. }
assert (RAWN : forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) -> bv_unsigned x <> TFIB_OOM ->
  ~ (TFIB_ERRNO <= bv_unsigned x < TFIB_ERRNO + 4) -> mem' x = memR x).
{ intros x N1 N2 N3. apply MEQ'. intros X. destruct (HWN _ X) as [X1|[X1|X1]]; [exact (N1 X1) | apply N2; lia | exact (N3 X1)]. }
destruct (MnRefillW.ifw_oom B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly' S S' W' memR mdR n tr sp0 mem'
  (with_vm_backing (m_vm_lazy mdR) mat mdR) HARXp HLPp Hc0 AVR RAWN PRES' PRS' Hlo' Hhi' VOOM (same_io_wvb mdR mat)
  ltac:(apply m_vmmaps_wvb) ltac:(apply m_vm_lazy_wvb) HPATH) as (HARXf & HLPf & HOOM & HUNWA).
exists ly', regs', mem', (with_vm_backing (m_vm_lazy mdR) mat mdR).
split; [exact (CFG_leaf regs' mem' _)|].
split.
{ split; [exact HARXf|]. split; [exact Hly|]. split; [exact HWLE|]. split; [exact (CS_leaf regs' CS')|].
  split; [exact (same_io_tr _ _ _ (same_io_tr _ _ _ SIOC HSIO) (same_io_wvb mdR mat))|].
  split.
  { (* the aview frame *)
    intros a Ra NO NO' NS NE.
    assert (NOO : a <> TFIB_OOM) by (intros ->; exact (NO' HOOM)).
    assert (NER : ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4)) by (intros X; apply NS; unfold ascratch; right; rewrite (ts_errno B TS); exact X).
    assert (NST : ~ (sp0 - AFSTACK <= a < sp0)) by (intros X; apply NS; unfold ascratch, spZ, AFSTACK_G; left; rewrite SP_U; unfold AFSTACK in X; exact X).
    transitivity (aview tfibsegs (w_H W') memR a); [exact (AVR a Ra NST NOO NER)|].
    transitivity (aview tfibsegs (w_H W) memC a).
    { apply (HFRA a); [exact Ra | exact NO | exact NO' | intros X; apply NST; exact (MnRefillW.win_af_w RW RWB _ _ _ SPC X)]. }
    exact (AGC a Ra NST). }
  split.
  { (* the raw frame: the same three steps on the raw memory *)
    intros x NO NO' NS NE.
    assert (NOO : bv_unsigned x <> TFIB_OOM) by (intros X; apply NO'; rewrite X; exact HOOM).
    assert (NER : ~ (TFIB_ERRNO <= bv_unsigned x < TFIB_ERRNO + 4)) by (intros X; apply NS; unfold ascratch; right; rewrite (ts_errno B TS); exact X).
    assert (NST : ~ (sp0 - AFSTACK <= bv_unsigned x < sp0)) by (intros X; apply NS; unfold ascratch, spZ, AFSTACK_G; left; rewrite SP_U; unfold AFSTACK in X; exact X).
    transitivity (memR x); [exact (RAWN x NST NOO NER)|].
    transitivity (memC x).
    { apply HFRR; [exact NO | exact NO' | intros X; apply NST; exact (MnRefillW.win_af_w RW RWB _ _ _ SPC X)]. }
    apply RAWC; [exact NST|]. intros Hu.
    apply NO'. replace (bv_unsigned x) with (ly_T ly' + t_unwinding); [exact HUNWA|].
    pose proof LyEq as (_ & _ & _ & HT). rewrite HT. lia. }
  intros a Ha. unfold spZ, AFSTACK_G in Ha. rewrite SP_U in Ha. unfold AFSTACK in PRS'. exact (PRS' a Ha). }
split; [cbn [fst]; rewrite A0; cbn [sptr_addr sptr_exp aeval]; reflexivity|].
split; [exact HLPf|].
split; [exact HPATH|].
intros _. exact VOOM.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The OOM tail: from the refill's refusal at its return into Allocate, the cache join's empty pop, the run to the
   ret, and the leaf's out-of-memory case (given the granted path, as the arms' pre-leaf PL). *)
Theorem miss_oom_tail : amreal tfibsegs (AGif0n.malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs A_REFILL_RET regsR memR mdR)
(fun r W'' c'' => (exists trc, apath (mt n tr S) trc r /\ gflag trc = true) ->
  alloc_leaf tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr r W'' c'').
Proof.
unfold AGif0n.malloc_join_t. rewrite bind_assoc_eq. eapply amreal_pure; [exact (pop_miss S' cl Hc0)|]. eapply amreal_pure; [reflexivity|].
unfold AGif0n.malloc_K_t. cbn [amreal].
replace (cfg_at tfibsegs A_REFILL_RET regsR memR mdR) with cR by (unfold cfg_at, cR, msR; rewrite with_vm_backing_id; reflexivity).
eapply SRr_mono; [exact (SEGN W' cR ATN)|]. intros W6 c6 _ HR. exact (LEAFN W6 c6 HR).
Qed.
End b.
End a.
