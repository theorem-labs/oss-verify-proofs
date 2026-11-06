(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGim0.v (a working branch ced28ed2383, file sha256 5f35b4daaba9) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 11 image addresses moved by code-verified function pairs (13 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* The g-path MISS arm of the frame-generic Allocate contract (AllocG.alloc_leaf) at can_fill = 0 (calloc's call,
   Allocate's a5 = 0), and the g-path MISS arm for can_fill cf in {0, 1}.

   Ported from proofs/cgif/cgif_file_fuzzer/lib/AFhy.v..YFjg.v (cgif_file's released malloc walk, same image) with the
   caller's frame made abstract; the cf = 0 tail comes from a Theorem Labs lane's AGc0 / AGc1 (seg2cf0_even / seg2cf0_odd, post
   AGc0.at_RET0), which the c5 AGj2.tail_inner takes for its left case (can_fill = 0).
   The cf = 0 twin of AGim.alloc_missg (frozen AIfaceM: interface AGif0n.AIface + AIfaceM, U : list Z -> astate -> Prop,
   and the AIfaceM field if_depot_miss), with AGim's Section variables and hypotheses in AGim's order.  The steps
   that do not read can_fill are AGim's lemmas, cited: the refill call (REFILL), the post-refill frame and view facts
   (HS3, PRES', HV', ...), the depot call at the post-refill state (HDEP, from the field if_depot_miss with HARX / Htr
   at the entry state S), the join leaf (LEAFJ) and the class-full OOM arm (OOMJ, the miss arms' shared OOM tail
   AGk1.miss_oom_tail).
   can_fill (a5, atom 15 of the virtual regs0) enters only through the seed facts and the tail:
   - the seed: AGiw.SEEDM_ok takes can_fill = 1 only.  FACTSM0 moves AGiw.FACTSM_ok from the register file with
     x15 := 1 to regs0 (the two environments differ only at atom 15, and FGG's fact on atom 15 is the range [0, 1]);
     SEEDM is AGiw.SEEDM_ok's script over FACTSM0 and AGiw.REGM_ok / PAIRSM_ok, AGj0.REGS_ok; MISS1 is AGim's;
   - FACTS' / HS5 / HS6 / HS7 / ATJ are AGim's, with the left case (cf = 0) of AGj0.FACTS_ok's disjunction;
   - TAILJ0 is AGim.TAILJ (AGit.segJ, then AGj2.tail_inner) with the left case of tail_inner's disjunction;
   - JOIN, missg_core and alloc_missg0 are AGim's, over these lemmas. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YG0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG02 YG06 YG07 YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0h.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AE3d AFhy AFhm AGhy AGhz AGi4.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGis AFi3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AllocG AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif AGif0cgif AGiz AGj0 AGj2 AGiw AGiu AGit AGiv AB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YA00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AGim.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Ltac bvne := first [cbn; lia | vm_compute; congruence | intros X; vm_compute in X; discriminate X].
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The facts of a list of atoms, moved to an environment that differs only at atom 15 (can_fill).                    *)
Definition f15_ok (z : Z) (p : nat * afact) : bool :=
negb (Nat.eqb (fst p) 15) ||
((af_lo (snd p) <=? z) && (z <=? af_hi (snd p)) && (z mod 2 ^ af_al2 (snd p) =? 0) && (0 <=? af_al2 (snd p)) && (af_al2 (snd p) <=? 64)).
Lemma atoms_ok_x15 : forall (E E' : env) (z : Z) (l : list (nat * afact)),
(forall k, k <> 15%nat -> ew E' k = ew E k) -> bv_unsigned (ew E' 15) = z ->
forallb (f15_ok z) l = true -> atoms_ok E l -> atoms_ok E' l.
Proof.
intros E E' z l HE Hz. induction l as [|[k f] r IH]; cbn [atoms_ok forallb]; intros HB HA; [exact I|].
apply andb_prop in HB as [Hb HB]. destruct HA as [Hf HA]. split; [|exact (IH HB HA)].
unfold f15_ok in Hb. cbn [fst snd] in Hb. revert Hb. destruct (Nat.eqb_spec k 15) as [->|Hk]; cbn [negb orb]; intros Hb.
- apply andb_prop in Hb as [Hb H5]. apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1, H2, H4, H5. apply Z.eqb_eq in H3. unfold afact_ok. rewrite Hz.
  split; [split; assumption | split; [assumption | split; assumption]].
- unfold afact_ok in *. rewrite (HE k Hk). exact Hf.
Qed.
(* FGG's fact on atom 15 holds at 0 (AGhy.frame_facts: atom 15 in [0, 1]). *)
Lemma FGG_f15 : forallb (f15_ok 0) (f_atoms FGG) = true.
Proof. vm_compute. reflexivity. Qed.
(* AGis.E0 over a register file with x15 updated: every other atom is unchanged. *)
Lemma E0_r15 : forall ly (regs : bvmap 5 word) n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz (x : word) k, k <> 15%nat ->
ew (AGis.E0 ly (regupd regs 15%bv x) n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz) k = ew (AGis.E0 ly regs n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz) k.
Proof.
intros ly regs n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz x k Hk. unfold AGis.E0, Ereg. cbn [ew].
destruct (k <? 32)%nat eqn:E; [|reflexivity]. apply Nat.ltb_lt in E.
apply getr_other. intros H. apply Hk.
assert (H' : bv_unsigned (Z_to_bv 5 (Z.of_nat k)) = 15) by (rewrite H; reflexivity).
rewrite Z_to_bv_unsigned in H'. unfold bv_wrap, bv_modulus in H'. change (2 ^ Z.of_N 5) with 32 in H'.
rewrite Z.mod_small in H' by lia. lia.
Qed.

Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* AGim's section b: the same variables and hypotheses, in AGim's order.                                              *)
Section b.
Variable B : asyms.
(* The trace premise (C5): a predicate on the trace and the state (cgif: In tr (as_universe B)). *)
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variables (nmax lmax : Z).
Variable lpost : astate -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variables (mtag stag : Z).
Hypothesis IF : AIface B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
Hypothesis TS : TfibSyms B.
Variable rtree : Z -> M unit.
Hypothesis IFM : AIfaceM B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree.
(* if_depot_miss: the depot callee at the post-refill state Sp, from the entry state's ARX and trace premise (AGim's
   section-b definition, the same text). *)
Definition Fdepot_miss := if_depot_miss B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM.
(* AGim's section-b definitions. *)
Local Abbreviation Finst := (@AGim.Finst _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF).
Local Abbreviation Fmview := (@AGim.Fmview _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM).
Local Abbreviation Fshape_miss := (@AGim.Fshape_miss _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM).
Local Abbreviation vregs := AGim.vregs.
Local Abbreviation vregs_other := AGim.vregs_other.
Local Abbreviation vregs_10 := AGim.vregs_10.
Local Abbreviation vregs_11 := AGim.vregs_11.
Local Abbreviation vregs_12 := AGim.vregs_12.

(* ---------------------------------------------------------------------------------------------------------------- *)
Section c.
Variables (inst : Z) (ly : alayout) (S : astate) (W : world tfibsegs).
Variables (regs0 regsU : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (tr : list Z).
Hypothesis HARX : ARX inst ly S W mem0 md0.
Hypothesis HRP : rpre S n.
Hypothesis Nrange0 : 49 <= n <= 64512.
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
Let kz : Z := rz_log n.
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

(* AGim's section-c facts (they do not read can_fill). *)
Local Abbreviation HIO := (@AGim.HIO _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF inst ly S W mem0 md0 HARX).
Local Abbreviation Hn0 := (@AGim.Hn0 ly regs0 n tr Nrange0 Htrlen).
Local Abbreviation Hkz1 := (@AGim.Hkz1 n Nrange0).
Local Abbreviation Nrange := (@AGim.Nrange n Nrange0).
Local Abbreviation FP := (@AGim.FP n Nrange0).
Local Abbreviation Hcl := (@AGim.Hcl ly regs0 n tr Nrange0 Htrlen).
Local Abbreviation Hcl_def := (@AGim.Hcl_def n Nrange0).
Local Abbreviation HMV := (@AGim.HMV _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange0 Hmiss Htrlen).
Local Abbreviation Hinst := (@AGim.Hinst _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF inst ly S W regs0 mem0 md0 n tr HARX Htrlen Hi11).
Local Abbreviation Hvd := (@AGim.Hvd ly regs0 n tr Htrlen).
Local Abbreviation Hcntd := (@AGim.Hcntd ly regs0 n tr Htrlen).
Local Abbreviation Hjbd := (@AGim.Hjbd ly regs0 n tr Htrlen).
Local Abbreviation Hv2d := AGim.Hv2d.
Local Abbreviation LY := (@AGim.LY _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange0 Hmiss Htrlen).
Local Abbreviation IMG := (@AGim.IMG _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange0 Hmiss Htrlen).
Lemma STK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof. exact (@AGim.STK _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange0 Hmiss Htrlen). Qed.
Lemma Usp : 0 <= sp0 < 2 ^ 64. Proof. exact (@AGim.Usp regs0). Qed.
Lemma Hcl_class : cl = chunk_class n. Proof. reflexivity. Qed.
Let E0m : env := AGis.E0 ly regs0 n tr cl 1 0 csz 0 0 0 0 0 0 kz.
Let DPOSTm : Z -> (word -> option byte) -> Prop := fun z m => dpost inst ly S W tr z m.
Let mat0 : list word := m_vm_materialized md0.

(* --- The seed at can_fill = 0. --- *)
(* AGiw.FACTSM_ok holds over regs1 (regs0 with x15 := 1); E0m differs from its environment only at atom 15. *)
Let regs1 : bvmap 5 word := regupd regs0 15%bv (w64 1).
Lemma FACTSM0 : facts_ok E0m FGG.
Proof.
assert (G : forall r : bv 5, r <> 15%bv -> getr regs1 r = getr regs0 r) by (intros r Hr; unfold regs1; apply getr_other; exact Hr).
assert (Hn1 : getr regs1 10 = w64 n) by (rewrite G by (intros X; discriminate X); exact Hn).
assert (Hi1 : getr regs1 11 = w64 inst) by (rewrite G by (intros X; discriminate X); exact Hi11).
assert (Hcf1 : getr regs1 15 = w64 1) by (unfold regs1; apply getr_same; intros X; discriminate X).
assert (G2 : getr regs1 2 = getr regs0 2) by (apply G; intros X; discriminate X).
assert (G12 : getr regs1 12 = getr regs0 12) by (apply G; intros X; discriminate X).
assert (G13 : getr regs1 13 = getr regs0 13) by (apply G; intros X; discriminate X).
assert (Hsp1 : ly_stk_lo ly + AFSTACK <= bv_unsigned (getr regs1 2) /\ ly_bot ly < bv_unsigned (getr regs1 2) /\
  bv_unsigned (getr regs1 2) <= ly_stk_hi ly /\ bv_unsigned (getr regs1 2) mod 16 = 0) by (rewrite G2; exact Hsp).
assert (Hso1 : bv_unsigned (getr regs1 2) <= bv_unsigned (getr regs1 13) /\ bv_unsigned (getr regs1 13) + 16 <= ly_stk_hi ly /\
  bv_unsigned (getr regs1 13) mod 8 = 0) by (rewrite G2, G13; exact Hso).
assert (Hbp1 : bv_unsigned (getr regs1 2) <= bv_unsigned (getr regs1 12) /\ bv_unsigned (getr regs1 12) + 8 * 30 <= ly_stk_hi ly /\
  bv_unsigned (getr regs1 12) mod 8 = 0) by (rewrite G2, G12; exact Hbp).
pose proof (@AGiw.FACTSM_ok _ W ly regs1 mem0 n tr cl 1 0 csz 0 0 0 0 0 0 kz Hcl Hvd Hcntd Hjbd Hv2d LY IMG Hn1 Hsp1 Htrlen Hso1 Hbp1 Hcf1
  DPOSTm Hkz1 Nrange inst Hi1 HIO) as FM1.
split.
- apply (atoms_ok_x15 (AGis.E0 ly regs1 n tr cl 1 0 csz 0 0 0 0 0 0 kz) E0m 0 (f_atoms FGG)); [| | exact FGG_f15 | exact (proj1 FM1)].
  + intros k Hk. unfold E0m, regs1. symmetry. exact (E0_r15 ly regs0 n tr cl 1 0 csz 0 0 0 0 0 0 kz (w64 1) k Hk).
  + unfold E0m, AGis.E0. rewrite (ew_Ereg_nat regs0 _ 15%nat 15%bv eq_refl), Hcf0. reflexivity.
- unfold FGG. cbn [f_conds f_alias FG conds_ok alias_ok]. split; exact I.
Qed.
(* AGiw.SEEDM_ok's script, over FACTSM0. *)
Lemma SEEDM : st_ok tfibsegs E0m AGi4.MS_1 (restrict (w_H W) (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs))).
Proof.
assert (RG : regs_ok E0m REGS_G regsU)
by exact (AGj0.REGS_ok W ly regs0 mem0 n tr cl 1 0 csz 0 0 0 0 0 0 kz Htp Htrlen DPOSTm regsU HUo HU10 HU11 HU12 HU14).
rewrite restrict_mkst_fx. unfold AGi4.MS_1, w64, st_ok.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact RG|]. split; [|exact FACTSM0].
split; [vm_compute; reflexivity|].
split; [exact (@AGiw.REGM_ok _ W ly regs0 mem0 n tr cl 1 0 csz 0 0 0 0 0 0 kz Hcl Hvd Hcntd Hv2d LY IMG Hsp Htrlen Hso Hbp DPOSTm Hkz1 Nrange B inst TS HMV Hi11 HIO PSO PLEN Hpres0)
| exact (@AGiw.PAIRSM_ok _ W ly regs0 mem0 n tr cl 1 0 csz 0 0 0 0 0 0 kz Hcl Hvd Hcntd Hv2d LY IMG Hsp Htrlen Hso Hbp DPOSTm Hkz1 Nrange inst Hi11 HIO)].
Qed.
(* AGim.MISS1 over SEEDM. *)
Lemma MISS1 : SRr tfibsegs W (cfg_at tfibsegs A_Allocate regsU mem0 md0)
(AGiu.at_STM W ly regs0 mem0 md0 n tr cl 1 0 csz 0 0 0 0 0 0 kz AGi4.MS_CALL).
Proof.
replace (cfg_at tfibsegs A_Allocate regsU mem0 md0) with (mkCfg (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs)) (md0' mat0))
by (unfold cfg_at, md0', mat0; rewrite with_vm_backing_id; reflexivity).
exact (@AGiu.miss1 _ _ W ly regs0 mem0 md0 n tr cl 1 0 csz 0 0 0 0 0 0 kz Hcl Hvd Hcntd Hv2d LY IMG Hn Hsp Htrlen Hso Hbp DPOSTm Hkz1 Nrange Hcl_def mat0 regsU PBUF0 [] 0 Hpres0 SEEDM).
Qed.
(* AGim's pre-leaf, its refill call and its OOM arm (the remaining arguments are the post-MISS1 / post-refill facts,
   given by eassumption as in AGim.missg_core). *)
Local Abbreviation PL := (@AGim.PL _ B mt ARX AOX lpost inst ly S W regsU mem0 md0 n tr).
Local Abbreviation ms1_shape := (@AGim.ms1_shape _ W).
Local Abbreviation REFILL := (@AGim.REFILL _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 mem0 md0 n tr HARX HRP Nrange0 Hmiss Htrlen Hi11 Hgp Hsp Hso Hbp).
Local Abbreviation RAZ1 := (@AGim.RAZ1 _ ly W regs0 n tr Htrlen).
Local Abbreviation OOMJ := (@AGim.OOMJ _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree IFM inst ly S W regs0 regsU mem0 md0 n tr HARX Nrange0 Hmiss Htrlen Htp Hra Hsp Hso Hbp HUo).

(* --- The refill-call machine state (AGim's section f). --- *)
Section f.
Variables (ms1 : machine_state) (mat1 : list word) (Em : env).
Hypothesis HEm : forall k, (k < aHAV)%nat -> ew Em k = ew E0m k.
Hypothesis HSC : st_ok tfibsegs Em AGi4.MS_CALL (restrict (w_H W) ms1).
Hypothesis MEQW : forall x : word, ~ AGiu.WINM ly regs0 (bv_unsigned x) -> (ms_mem ms1) x = mem0 x.
Hypothesis PRESW : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a.
Hypothesis BUFW : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* After the refill (AGim's section g0).                                                                              *)
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
  ~ (spZ (ms_regs ms1) - RSTACK <= bv_unsigned x < spZ (ms_regs ms1)) -> memR x = ms_mem ms1 x.
Hypothesis HPRR : forall a, spZ (ms_regs ms1) - RSTACK <= a < spZ (ms_regs ms1) -> apresent (w_H W') memR a.
Let msR : machine_state := mkst regsR (w64 0x36844) memR (seg_rom tfibsegs).
Let cR : config := mkCfg msR (with_vm_backing (m_vm_lazy mdR) (m_vm_materialized mdR) mdR).
Let ms3 : machine_state := mkst regsR (w64 0x36844) (mrestrict (w_H W') memR) (seg_rom tfibsegs).
Let E1 : env := havoc Em hRF (map (getr regsR) CLOB).
Local Abbreviation Hsp' := (@AGim.Hsp' ly S regs0 Hsp ly' Hly).
Local Abbreviation Hso' := (@AGim.Hso' ly S regs0 Hso ly' Hly).
Local Abbreviation Hbp' := (@AGim.Hbp' ly S regs0 Hbp ly' Hly).
Lemma PRES' : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W') memR a.
Proof. exact (@AGim.PRES' _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange0 Hmiss Htrlen Hsp Hso Hbp ms1 Em HEm HSC PRESW S' ly' W' memR mdR HARXp Hly HFRA HPRR). Qed.
Lemma HS3 : st_ok tfibsegs E1 AGi4.SS3 ms3.
Proof. exact (@AGim.HS3 _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange0 Hmiss Htrlen Hsp Hso Hbp ms1 Em HEm HSC S' ly' W' regsR memR mdR HARXp Hly HAREGS HFRA). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The a0 = 1 cache join, at the post-refill layout ly' (AGim's section g).                                          *)
Section g.
Variables (l : list Z) (off : Z).
Hypothesis Hcache' : pc_chunks (cache S' cl) = l ++ [off].
Hypothesis HA1 : getr regsR 10 = w64 1.
Let cnt' : Z := Z.of_nat (length (l ++ [off])).
Let v' : Z := off / 16.
Let DPOST' : Z -> (word -> option byte) -> Prop := fun z m => dpost inst ly' S' W' tr z m.
Local Abbreviation HV' := (@AGim.HV' _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly regs0 n tr Nrange0 Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation LY' := (@AGim.LY' _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly regs0 n tr Nrange0 Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation IMG' := (@AGim.IMG' _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly regs0 n tr Nrange0 Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation Hv' := (@AGim.Hv' _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree IFM inst ly regs0 n tr Nrange0 Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation Hv2' := (@AGim.Hv2' _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree IFM inst ly regs0 n tr Nrange0 Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation Hcnt' := (@AGim.Hcnt' _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree IFM inst ly regs0 n tr Nrange0 Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation HKpres' := (@AGim.HKpres' _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree IFM inst ly regs0 n tr Nrange0 Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation HSKpres' := (@AGim.HSKpres' _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree IFM inst ly regs0 n tr Nrange0 Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation HPB250' := (@AGim.HPB250' _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree IFM inst ly regs0 n tr Nrange0 Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Lemma BUF' : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W') memR) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).
Proof. exact (@AGim.BUF' _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange0 Hmiss Htrlen Hsp Hso Hbp ms1 Em HEm HSC BUFW S' ly' W' memR mdR HARXp Hly HFRA). Qed.

Section gj.
Variables (j0 jb j1 j2 j3 j4 : Z).
Hypothesis Hj0 : val_mem tfibsegs (mrestrict (w_H W') memR) (ly_T ly' + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfibsegs (mrestrict (w_H W') memR) (ly_T ly' + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfibsegs (mrestrict (w_H W') memR) (ly_T ly' + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfibsegs (mrestrict (w_H W') memR) (ly_T ly' + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfibsegs (mrestrict (w_H W') memR) (AGis.SSLOTv ly' cl) 8 j4.
Hypothesis Hjb : 0 <= jb <= 255.
Hypothesis Hjb_def : val_mem tfibsegs (mrestrict (w_H W') memR) (AGis.Kv ly' cl v' + AGis.RZ kz - 15) 1 jb.
Let E0' : env := AGis.E0 ly' regs0 n tr cl cnt' v' csz j0 jb j1 j2 j3 j4 kz.
Let Es : env := env_merge PND E1 E0'.
Lemma HEs : forall k, (k < aHAV)%nat -> ew Es k = ew E0' k. Proof. exact (@AGim.HEs ly S regs0 n tr Htrlen Em HEm ly' regsR Hly l off j0 jb j1 j2 j3 j4). Qed.
Lemma AGs : env_agree 64 E0' Es. Proof. exact (@AGim.AGs ly S regs0 n tr Htrlen Em HEm ly' regsR Hly l off j0 jb j1 j2 j3 j4). Qed.
Lemma Es2 : bv_unsigned (ew Es 2) = sp0. Proof. exact (@AGim.Es2 ly S regs0 n tr Htrlen Em HEm ly' regsR Hly l off j0 jb j1 j2 j3 j4). Qed.
Lemma REG0' : Forall (region_ok tfibsegs E0' (mrestrict (w_H W') memR)) REG0G.
Proof. exact (@AGim.REG0' _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TS rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange0 Hmiss Htrlen Hi11 Hsp Hso Hbp PSO PLEN ms1 Em HEm HSC MEQW PRESW S' ly' W' memR mdR HARXp CIp Hly HFRA HPRR l off Hcache' j0 jb j1 j2 j3 j4 Hj0 Hj1 Hj2 Hj3 Hj4 Hjb Hjb_def). Qed.
Lemma PAIRS' : pairwise_disjoint E0' REG0G.
Proof. exact (@AGim.PAIRS' _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TS rtree IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange0 Htrlen Hi11 Hsp Hso Hbp S' ly' W' memR mdR HARXp CIp Hly l off Hcache' j0 jb j1 j2 j3 j4). Qed.
Lemma region_ok_agree_on_lt : forall r, In r TAIL0G -> region_ok tfibsegs E0' (mrestrict (w_H W') memR) r -> region_ok tfibsegs Es (ms_mem ms3) r.
Proof. exact (@AGim.region_ok_agree_on_lt _ ly S regs0 n tr Htrlen Em HEm ly' W' regsR memR Hly l off j0 jb j1 j2 j3 j4). Qed.
Local Abbreviation HDAOK := (@AGim.HDAOK _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF inst tr S' ly' W').
Local Abbreviation HDEP := (@AGim.HDEP _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W mem0 md0 tr HARX Htr S' ly' W' memR mdR HARXp).
(* AGim.FACTS' / HS5 / HS6 / HS7 / ATJ with cf = 0: the join state's facts read can_fill through AGj0.FACTS_ok's
   disjunction. *)
Lemma FACTS' : atoms_ok E0' (f_atoms FGG).
Proof. exact (proj1 (@AGj0.FACTS_ok _ _ W' ly' regs0 memR n tr cl cnt' v' csz j0 jb j1 j2 j3 j4 kz Hcl Hv' Hcnt' Hjb Hv2' LY' IMG' Hn Hsp' Htrlen Hso' Hbp' (or_introl Hcf0) DPOST' Hkz1 Nrange B inst TS HV' Hi11 HIO Hcl_class)). Qed.
Lemma HS5 : st_ok tfibsegs Es (mkSS (ss_pc AGi4.SS3) (sr_set (ss_regs AGi4.SS3) 10%bv (SLit 1)) (ss_mem AGi4.SS3) (ss_resv AGi4.SS3) (ss_facts AGi4.SS3)) ms3.
Proof.
assert (HS4 : st_ok tfibsegs Es AGi4.SS3 ms3).
{ pose proof AGi4.SS3_atoms as (A1 & A2 & A3 & A4 & A5). pose proof AGi4.tlREG0_facts as (_ & _ & T3).
  apply (st_ok_agree_on2 tfibsegs PND E1 Es AGi4.SS3 ms3 HS3 (env_merge_on PND E1 E0') A1 A2 A3 A4).
  rewrite A5. exact (atoms_ok_agree 64 E0' Es _ AGs T3 FACTS'). }
apply (st_ok_pin_regU Es AGi4.SS3 ms3 10%bv (SLit 1) HS4); [intros X; discriminate X|].
pose proof (st_ok_reg tfibsegs Es AGi4.SS3 ms3 10%bv HS4) as R. unfold YP0e.U. rewrite <- R. unfold ms3. cbn [ms_regs mkst]. rewrite HA1. reflexivity.
Qed.
Lemma HS6 : st_ok tfibsegs Es (mkSS 0x36844 (sr_set (ss_regs AGi4.SS3) 10%bv (SLit 1)) [AGi4.R3bst; AGi4.R3scr; AGi4.R3top] None (ss_facts AGi4.SS3)) ms3.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U_. pose proof Hso as (O1 & O2 & O3).
pose proof (st_ok_mem_surgery Es _ ms3 [AGi4.R3bst; AGi4.R3scr; AGi4.R3top] HS5) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. apply X. clear X.
intros (HW & HF & HP). unfold ms3 in *. cbn [ms_mem mkst] in *.
assert (BV : base_val Es (Some 2%nat) = sp0) by (cbn [base_val]; exact Es2).
assert (BV13 : base_val Es (Some 13%nat) = SOv) by (cbn [base_val]; rewrite (HEs 13%nat ltac:(cbv; lia)); reflexivity).
split; [reflexivity|]. split.
- apply Forall_cons; [exact (Forall_inv HF)|]. apply Forall_cons; [|exact (Forall_inv_tail (Forall_inv_tail HF))].
pose proof (Forall_inv (Forall_inv_tail HF)) as (R1 & R2 & R3 & R4). cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in R1, R2, R3, R4.
rewrite BV in R1, R2, R3, R4.
unfold region_ok, AGi4.R3scr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV.
split; [clear - Hlo K1; unfold AFSTACK, kHighMemBeg in *; unfold sp0 in *; lia|]. split; [clear - U_; unfold sp0 in *; lia|]. split; [|exact R4].
intros o Ho. apply apresent_writable; [clear - Ho Hlo K1 U_; unfold TFIB_IMG_END, AFSTACK, kHighMemBeg in *; unfold sp0 in *; lia|]. apply PRES'. clear - Ho; unfold AFSTACK; lia.
- unfold AGi4.R3bst, AGi4.R3scr, AGi4.R3top. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite BV, BV13. repeat split; unfold sp0, SOv in *; lia.
Qed.
Lemma HS7 : st_ok tfibsegs Es AGi4.MS_AFTER ms3.
Proof.
rewrite AGi4.MS_AFTER_eq3. pose proof AGi4.tlREG0_facts as (T1 & T2 & T3).
pose proof (st_ok_mem_surgery Es _ ms3 ([AGi4.R3bst; AGi4.R3scr; AGi4.R3top] ++ TAIL0G) HS6) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. apply X. clear X.
intros HM. pose proof PAIRS' as PP. unfold REG0G in PP. cbn [pairwise_disjoint] in PP. destruct PP as (A0 & A1 & A2 & PT).
pose proof REG0' as RR. unfold REG0G in RR. apply Forall_inv_tail, Forall_inv_tail, Forall_inv_tail in RR.
apply mem_ok_app; [exact HM | exact T2 | | |].
- apply Forall_forall. intros r Hr. apply (region_ok_agree_on_lt r); [exact Hr|]. exact (proj1 (Forall_forall _ _) RR r Hr).
- exact (pairwise_disjoint_agree 64 E0' Es TAIL0G AGs T1 PT).
- intros r Hr.
  assert (Hb : obase_lt 64 (YP09.r_base r) = true).
  { pose proof (proj1 (forallb_forall _ _) T1 r Hr) as Ha. unfold region_atoms_lt in Ha. apply andb_prop in Ha as [Ha _]. exact Ha. }
  assert (D0 : extent_disjoint Es R_soG r) by (apply (extent_disjoint_agree 64 E0' Es R_soG r AGs eq_refl Hb); apply (all_disjoint_In E0' _ _ r A0); right; right; exact Hr).
  assert (D1 : extent_disjoint Es R_scrG r) by (apply (extent_disjoint_agree 64 E0' Es R_scrG r AGs eq_refl Hb); apply (all_disjoint_In E0' _ _ r A1); right; exact Hr).
  assert (D2 : extent_disjoint Es R_slotG r) by (apply (extent_disjoint_agree 64 E0' Es R_slotG r AGs eq_refl Hb); apply (all_disjoint_In E0' _ _ r A2); exact Hr).
  cbn [all_disjoint]. split; [|split; [|split; [|exact I]]].
  + exact (AFhm.extent_disjoint_ext3 Es r R_soG AGi4.R3bst eq_refl (AFhm.extent_disjoint_sym Es R_soG r D0)).
  + exact (AFhm.extent_disjoint_ext3 Es r R_scrG AGi4.R3scr eq_refl (AFhm.extent_disjoint_sym Es R_scrG r D1)).
  + exact (AFhm.extent_disjoint_ext3 Es r R_slotG AGi4.R3top eq_refl (AFhm.extent_disjoint_sym Es R_slotG r D2)).
Qed.
Lemma ATJ : AGis.at_ST W' ly' regs0 memR mdR n tr cl cnt' v' csz j0 jb j1 j2 j3 j4 kz AGi4.MS_AFTER W' cR.
Proof.
split; [reflexivity|]. exists msR, (m_vm_materialized mdR), Es. split; [reflexivity|]. split; [exact HEs|].
split; [unfold msR; rewrite restrict_mkst_fx; exact HS7|].
split; [intros x _; reflexivity|]. split; [exact PRES' | exact BUF'].
Qed.
(* AGim.TAILJ with cf = 0: AGit.segJ to the join state, then AGj2.tail_inner, whose can_fill = 0 case ends in a Theorem Labs lane's
   AGc1.seg2cf0_even / _odd (post AGc0.at_RET0, read back as at_RETw by AGj2.at_RET0_w). *)
Lemma TAILJ0 : amreal tfibsegs (malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs 0x36844 regsR memR mdR)
(fun r W'' c'' => exists odd z, r = (ck_user (new_chunk cl off n), st_final S' cl l off n tr z) /\
(odd = true <-> n mod 8 <> 0) /\
at_RETw W' ly' regs0 memR mdR n cl cnt' v' jb kz DPOST' odd z W'' c'').
Proof.
replace (cfg_at tfibsegs 0x36844 regsR memR mdR) with cR by (unfold cfg_at, cR, msR; rewrite with_vm_backing_id; reflexivity).
eapply amreal_SRr_pre.
{ exact (@AGit.segJ _ _ W' ly' regs0 memR mdR n tr cl cnt' v' csz j0 jb j1 j2 j3 j4 kz Hcl Hv' Hcnt' Hv2' LY' IMG' Hsp' Htrlen Hbp' DPOST' Hkz1 Nrange l off W' cR ATJ). }
intros W2 c2 _ HJ. pose proof (proj1 HJ) as EW. subst W2.
exact (@AGj2.tail_inner _ _ W' ly' regs0 memR mdR n tr cl cnt' v' csz j0 jb j1 j2 j3 j4 kz Hcl Hv' Hcnt' Hjb Hv2' LY' IMG' Hn Htp (or_introl Hcf0) Hra Hsp' Htrlen Hso' Hbp' Hinst DPOST' HKpres' HSKpres' HPB250' Hkz1 Nrange Hcl_def B S' l off stag Hgp Hcache' HDEP HDAOK c2 HJ).
Qed.
End gj.
(* The join leaf (AGim.LEAFJ; the remaining arguments are the junk byte of the join state and the result). *)
Local Abbreviation LEAFJ := (@AGim.LEAFJ _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree IFM inst ly S W regs0 regsU mem0 md0 n tr HARX HRP Nrange0 Hmiss Hnnmax HBB Htr Htrlen Hsp Hso Hbp HUo ms1 mat1 Em HEm HSC MEQW PRESW S' ly' W' memR mdR HARXp CIp HBBp Hly HWLE HSIO HFRA HFRR HPRR l off Hcache').
Lemma JOIN : amreal tfibsegs (malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs 0x36844 regsR memR mdR) PL.
Proof.
destruct (@AGiz.vw_junk_values _ _ B W' ly' inst memR n cl cnt' v' kz TS HV' Hkz1 Nrange Hcl_class)
  as (j0 & j1 & j2 & j3 & j4 & jb & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hjb & Hjb_def).
eapply amreal_mono; [| eapply TAILJ0; eassumption].
intros r W'' c'' H. eapply LEAFJ; eassumption.
Qed.
End g.
End g0.
End f.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* AGim.missg_core, over MISS1 / JOIN above. *)
Lemma missg_core : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0)
(alloc_leaf tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr).
Proof.
assert (CORE : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0) PL).
{
rewrite (Fshape_miss n tr S Hn0 FP Hmiss). fold cl.
eapply amreal_pure; [reflexivity|].
eapply amreal_pure; [unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage; lia); reflexivity|].
change (set_nev (st_nev S + 1) S) with S1.
eapply (YG0d.amreal_mbind tfibsegs (rtree cl) (fun _ : unit => malloc_join_t stag n tr cl) S1 W _
(fun r W1 c1 => exists ms1 mat1 Em,
  ((forall k, (k < aHAV)%nat -> ew Em k = ew E0m k) /\ st_ok tfibsegs Em AGi4.MS_CALL (restrict (w_H W) ms1) /\
   (forall x : word, ~ AGiu.WINM ly regs0 (bv_unsigned x) -> ms_mem ms1 x = mem0 x) /\
   (forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a) /\
   (forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0))) /\
  rleaf ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1) r W1 c1)).
- (* MISS1, then the refill callee *)
  eapply amreal_SRr_pre; [exact MISS1|]. intros W1 c1 _ HC.
  destruct HC as (-> & ms1 & mat1 & Em & -> & HEm & HSC & MEQW & PRESW & BUFW).
  assert (SHAPE : ms1 = mkst (ms_regs ms1) (w64 0x36ce4) (ms_mem ms1) (seg_rom tfibsegs)) by (eapply ms1_shape; eassumption).
  assert (RR : amreal tfibsegs (rtree cl S1) W (cfg_at tfibsegs A_Refill (ms_regs ms1) (ms_mem ms1) (md0' mat1))
    (rleaf ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1))) by (eapply REFILL; eassumption).
  unfold cfg_at, A_Refill in RR. rewrite SHAPE at 1.
  eapply amreal_mono; [| exact RR]. intros r W2 c2 HRL. exists ms1, mat1, Em. split; [|exact HRL]. repeat (split; [assumption|]). exact BUFW.
- (* the post-refill branch on the class cache *)
  intros [] Sp W1 c1 (ms1 & mat1 & Em & (HEm & HSC & MEQW & PRESW & BUFW) & HRL).
  destruct HRL as (ly' & regsR & memR & mdR & -> & HARXp & HLPp & CIp & HBBp & Hly & HWLE & HAREGS & HSIO & HFRA & HFRR & HPRR & HA0e).
  cbn [snd] in *.
  assert (RA : raZ (ms_regs ms1) = 0x36844) by (eapply RAZ1; eassumption). rewrite RA.
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
End c.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The theorem, can_fill = 0: from alloc_pre at Allocate's entry (a5 = 0), the virtual register file
   regs0 := vregs regs n inst bp (AGim.alloc_missg with cf = 0). *)
Theorem alloc_missg0 : forall inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 0 inst so bp ly S W regs mem md n tr ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x31ef4 regs mem md)
(alloc_leaf tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Proof.
intros inst so bp ly S W regs mem md n tr PRE Nrange0 Hmiss.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres0 & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hn0 & Hlive).
unfold spZ, raZ, AFSTACK_G in *. rewrite (ts_tp B TS) in Htp.
pose proof (Finst inst ly S W mem md HARX) as HIO. pose proof HIO as (HIO1 & HIO2 & HIO3).
assert (Hnn : n < nmax) by lia.
assert (FP0 : from_primary n = true) by (eapply AGim.FP; eassumption).
pose proof (Fmview inst ly S W mem md n HARX ltac:(lia) FP0 Hmiss) as HMV0.
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
change (cfg_at tfibsegs 0x31ef4 regs mem md) with (cfg_at tfibsegs A_Allocate regs mem md).
eapply (missg_core inst ly S W regs0 regs mem md n tr); eassumption.
Qed.
(* The g-path MISS arm for can_fill cf in {0, 1}: alloc_missg0 (cf = 0) or AGim.alloc_missg (cf = 1). *)
Theorem alloc_missg_cf : forall cf inst so bp ly S W regs mem md n tr, cf = 0 \/ cf = 1 ->
alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 cf inst so bp ly S W regs mem md n tr ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x31ef4 regs mem md)
(alloc_leaf tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Proof.
intros cf inst so bp ly S W regs mem md n tr [-> | ->].
- exact (alloc_missg0 inst so bp ly S W regs mem md n tr).
- exact (@AGim.alloc_missg _ _ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TS rtree IFM inst so bp ly S W regs mem md n tr).
Qed.
End b.
End a.
