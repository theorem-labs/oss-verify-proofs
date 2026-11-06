(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGje.v (a working branch ced28ed2383, file sha256 e3fbcd367cc3) onto omx-clap-core/fuzz_state's asan-ubsan image (fuzz_state.asan-ubsan, pinned sha256 5ac5ce0954f8; addresses read from its unstripped build b1566a1ca816); module paths changed; its 1 image addresses moved by code-verified function pairs (2 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* The generic k seed of the frame-generic Allocate walk (requests of 0..48 bytes): the walk's environment
   E0 = Ereg regs0 XW (AGj6's, regs0 the virtual register file of AGhy) satisfies AGi2.KS_1 = AGhy.SSGK at
   Allocate's entry, where the machine registers [regsU] are REGS_G over regs0 (a0 = this = atom aINST, a1 = n =
   atom 10, a2 = 8, a4 = 1, the rest as regs0).  Over the walk header of AGjd (the allocator instance [inst] and the
   view [AGif0cgif.hview]); no allocator model.  The k twin of AGj0. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YE3d YFhy AGhy YFi1 AGi2 AGj6 AGif0cgif AGjd.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia ].
Section e.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (tr : list Z).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let BPv : Z := bv_unsigned (getr regs0 12).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation RZ := (@AGj6.RZ).
Local Abbreviation NPv := (@AGj6.NPv n).
Local Abbreviation R8v := (@AGj6.R8v n).
Local Abbreviation N8D := (@AGj6.N8D n).
Local Abbreviation Pv := (@AGj6.Pv ly cl).
Local Abbreviation PVv := (@AGj6.PVv ly cl cnt).
Local Abbreviation Kv := (@AGj6.Kv ly cl v).
Local Abbreviation SHBv := (@AGj6.SHBv).
Local Abbreviation SKv := (@AGj6.SKv ly cl v).
Local Abbreviation SSLOTv := (@AGj6.SSLOTv ly cl).
Local Abbreviation PBv := (@AGj6.PBv ly n cl v).
Local Abbreviation NDv := (@AGj6.NDv n).
Local Abbreviation E0 := (@AGj6.E0 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaT := (@AGj6.EaT ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaC := (@AGj6.EaC ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSB := (@AGj6.EaSB ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaTOP := (@AGj6.EaTOP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation Er := (@AGj6.Er ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E2 := (@AGj6.E2 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E10 := (@AGj6.E10 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E11 := (@AGj6.E11 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaP := (@AGj6.EaP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaK := (@AGj6.EaK ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSK := (@AGj6.EaSK ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSSLOT := (@AGj6.EaSSLOT ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaPB := (@AGj6.EaPB ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaPV := (@AGj6.EaPV ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaNP := (@AGj6.EaNP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaND := (@AGj6.EaND ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Hypotheses (Hcl : 1 <= cl <= 31) (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32) (Hcnt : 1 <= cnt <= 16) (Hjb : 0 <= jb <= 255).
Hypothesis Hv2 : v mod 2 = 0.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
(* The stack object and the trace buffer lie in the caller's frame, above Allocate's entry sp. *)
Hypothesis Hso : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly /\ SOv mod 8 = 0.
Hypothesis Hbp : sp0 <= BPv /\ BPv + 8 * 30 <= ly_stk_hi ly /\ BPv mod 8 = 0.
(* The allocator instance (atom aINST = register 11 of the virtual regs0) lies in the image, below the depot. *)
Hypothesis Hinst : TFIB_IMG_LO <= bv_unsigned (getr regs0 11) /\ bv_unsigned (getr regs0 11) + 0xe60 <= 0x17a308.
(* can_fill (atom 15) is 0 or 1. *)
Hypothesis Hcf : getr regs0 15 = w64 0 \/ getr regs0 15 = w64 1.
Variable DPOST : Z -> (word -> option byte) -> Prop.
Hypothesis Nrange : 0 <= n <= 48.
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Variables (B : asyms) (inst : Z).
Hypothesis TS : TfibSyms B.
Hypothesis HV : hview B W ly inst mem0 cl cnt v.
Hypothesis Hi11 : getr regs0 11 = w64 inst.
Hypothesis HIO : inst_ok inst.
Let m0 := mrestrict (w_H W) mem0.
Hypothesis PSO : val_mem tfibsegs m0 SOv 8 BPv.
Hypothesis PLEN : val_mem tfibsegs m0 (SOv + 8) 8 (Z.of_nat (length tr)).
Hypothesis Hpres0 : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcsz_def : csz = class_size cl.
Hypothesis Hj0 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfibsegs (mrestrict (w_H W) mem0) SSLOTv 8 j4.
Hypothesis Hjb_def : val_mem tfibsegs (mrestrict (w_H W) mem0) (Kv + RZ - 15) 1 jb.
(* The registers at Allocate's entry: REGS_G over regs0 (a0 = this, a1 = n, a2 = 8, a4 = 1). *)
Variable regsU : bvmap 5 word.
Hypothesis HUo : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr regsU r = getr regs0 r.
Hypothesis HU10 : getr regsU 10%bv = getr regs0 11%bv.
Hypothesis HU11 : getr regsU 11%bv = getr regs0 10%bv.
Hypothesis HU12 : getr regsU 12%bv = w64 8.
Hypothesis HU14 : getr regsU 14%bv = w64 1.
Local Abbreviation tr_length := (@AGj6.tr_length tr Htrlen).
Local Abbreviation Kv_range := (@AGj6.Kv_range ly regs0 mem0 n tr cl v Hcl Hv Hv2 Htrlen DPOST).
Local Abbreviation high_facts := (@AGj6.high_facts _ ly regs0 mem0 n tr v Hv LY IMG Htrlen DPOST).
Local Abbreviation blocks_facts := (@AGj6.blocks_facts _ ly LY IMG).
Local Abbreviation HCX := (@AGj6.HCX _ ly LY).
Local Abbreviation RZ_num := (@AGj6.RZ_num n Nrange).
Local Abbreviation K0_facts := (@AGj6.K0_facts n Nrange).
Local Abbreviation derived_ranges := (@AGj6.derived_ranges _ ly regs0 mem0 n tr cl cnt v Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Nrange).
Local Abbreviation stack_ivs := (@AGj6.stack_ivs _ ly regs0 mem0 n tr v Hv LY Hsp Htrlen Hbp DPOST).
Local Abbreviation vcls := (vw_cls_geom B W ly inst mem0 n cl cnt v TS HV Nrange Hcl_class).
Local Abbreviation vKgeom := (vw_Kv_geom B W ly inst mem0 n cl cnt v TS HV Nrange Hcl_class).
Local Abbreviation vKv32 := (vw_Kv32 B W ly inst mem0 n cl cnt v TS HV Nrange Hcl_class).
Local Abbreviation vcl_k0 := (vw_cl_k0 B W ly inst mem0 n cl cnt v TS HV Nrange Hcl_class).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The regions of REG0KG are pairwise disjoint.                                                                     *)
Local Ltac ext_prep :=
unfold REG0KG, R_soG, R_scrG, R_slotG, TAIL0KG, TAIL0G, iatom8, ilits8, lit1, lit4, lit8, lits8, atom8, extent_of_region, CTZ_TABLE;
cbn [map firstn app YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ];
unfold aSB, aSHB, aC, aT, aTOP, aSK, aP, aPV, aK, aSSLOT, aINST, aSO;
rewrite ?E2, ?E11, ?Hi11, ?(Er 13 13%bv eq_refl), ?EaT, ?EaC, ?EaP, ?EaPV, ?EaK, ?EaSK, ?EaSSLOT; unfold w64;
rewrite ?unsigned_lit_small by zlia.
Lemma PAIRS_ok : pairwise_disjoint E0 REG0KG.
Proof.
pose proof high_facts as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9). pose proof derived_ranges as DR. pose proof Kv_range as HKR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S2 & S3 & S4).
destruct HIO as (IO1 & IO2 & IO3). pose proof RZ_num as RZN.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, HKR, T2, T4, T7.
(* the extents, rewritten once with no disjunctive fact in the context *)
apply pairwise_disjoint_of_extents. ext_prep.
cbn [zpairwise_disjoint].
(* the disjointness facts of the layout *)
pose proof (pairwise_ij _ _ 2 5 _ _ (lo_disj ly LY) eq_refl eq_refl) as ZT.
pose proof (pairwise_ij _ _ 0 7 _ _ (lo_disj ly LY) eq_refl eq_refl) as ZP.
pose proof (pairwise_ij _ _ 6 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as ZC.
unfold zdisjoint in ZT, ZP, ZC. cbn [fst snd] in ZT, ZP, ZC.
pose proof stack_ivs as (SI1 & SI2 & SI3). pose proof HCX as [CP CT]. unfold zdisjoint in CP, CT. cbn [fst snd] in CP, CT.
pose proof blocks_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PT). unfold zdisjoint in PT. cbn [fst snd] in PT.
split; [|split; [|split]].
- (* the stack object against the rest *)
clear - sp0 SOv T SB S1 S2 S3 T1 T4 T7 Hso ZT ZP ZC hf3 hf4 hf5 hf6 DR HKR Hcl Hcnt RZN IO1 IO2.
unfold TFIB_TP, TFIB_TSD, t_unwinding, AFSTACK in *. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold sp0, SOv, T, SB in *. unfold AGj6.PVv, AGj6.SSLOTv, AGj6.Pv in *. unfold t_cache, t_stats, kThreadObjSize, kPrimResvSize, kSpaceSize in *.
(* each goal first without the layout's disjunctions (lia splits on every disjunction it sees) *)
repeat split; first [ solve [clear ZT ZP ZC; lia] | zlia ].
- (* the scratch window below the entry sp against the rest *)
clear - sp0 T SB S1 S2 S3 T1 T4 T7 SI1 SI2 SI3 hf3 hf4 hf5 hf6 DR HKR Hcl Hcnt RZN IO1 IO2.
unfold TFIB_TP, TFIB_TSD, t_unwinding, AFSTACK in *. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold sp0, T, SB in *. unfold AGj6.PVv, AGj6.SSLOTv, AGj6.Pv in *. unfold t_cache, t_stats, kThreadObjSize, kPrimResvSize, kSpaceSize in *.
repeat split; first [ solve [clear SI1 SI2 SI3; lia] | zlia ].
- (* the empty slot at the entry sp against the tail *)
clear - sp0 T SB S1 S2 S3 T1 T4 T7 SI1 SI2 SI3 hf3 hf4 hf5 hf6 DR HKR Hcl Hcnt RZN IO1 IO2.
unfold TFIB_TP, TFIB_TSD, t_unwinding, AFSTACK in *. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold sp0, T, SB in *. unfold AGj6.PVv, AGj6.SSLOTv, AGj6.Pv in *. unfold t_cache, t_stats, kThreadObjSize, kPrimResvSize, kSpaceSize in *.
repeat split; first [ solve [clear SI1 SI2 SI3; lia] | zlia ].
- (* the tail: the released regions, the instance fields based at aINST *)
clear - T SB hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 DR HKR CP CT PT Hcl Hcnt RZN IO1 IO2.
unfold TFIB_TP, TFIB_TSD, t_unwinding in *. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold T, SB in *. unfold AGj6.PVv, AGj6.SSLOTv, AGj6.Pv in *. unfold t_cache, t_stats, kThreadObjSize, kPrimResvSize in *.
repeat split; first
[ solve [clear CP CT PT; lia]
| solve [clear CP CT PT; unfold zone3cases in hf1, hf7; unfold TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in hf1, hf7; lia]
| zlia ].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The facts of FKG: the frame atoms, then the released facts (YFi1.FK without its sp fact).                        *)
Lemma FACTS_ok : facts_ok E0 FKG.
Proof.
pose proof high_facts as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9). pose proof derived_ranges as DR. pose proof Kv_range as HKR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S2 & S3 & S4).
pose proof vcls as (K1 & K2 & K3 & K4 & K5 & K6). destruct HIO as (IO1 & IO2 & IO3).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, HKR, T2, T4, T7.
pose proof tr_length as TL. pose proof vKgeom as (V1 & V2 & V3 & _). pose proof (lo_space_al ly LY) as SAL. pose proof (lo_T_al ly LY) as TAL. pose proof (lo_C_al ly LY) as CAL.
unfold page_aligned in TAL. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in V1, V2.
assert (E2' : ew E0 2 = w64 sp0) by (rewrite E2; unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (AF : forall k X lo hi al, ew E0 k = w64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; zlia. }
unfold facts_ok, FKG, frame_facts. cbn [f_atoms f_conds f_alias FK tl app atoms_ok conds_ok alias_ok].
split; [|split; exact I].
unfold aSB, aSHB, aC, aT, aTOP, aSK, aP, aPV, aK, aSSLOT, aLEN, aJ0, aR8, aCL, aCNT, aV, aCSZ, aJB, aJ1, aJ2, aJ3, aJ4, aPB, aN8D, aCNT8, aNP, aND,
aINST, aSO, aBP.
pose proof RZ_num as (RZr & RZ8 & Nlo & NPr & R8r & NPR8 & N8r & NPN8 & FILN). pose proof vKv32 as K32. pose proof vcl_k0 as CK.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, AFSTACK.
(* the frame atoms: the entry sp, the instance, the stack object, the buffer, can_fill *)
split. { apply (AF 2%nat sp0); [exact E2'| | | |].
all: pose proof (u64_range (getr regs0 2)) as U; clear - U S1 S2 S3 S4 T1 T4 T7; unfold sp0, AFSTACK in *; first [zlia | replace (2 ^ 4) with 16 by reflexivity; exact S4]. }
split. { apply (AF 11%nat inst); [rewrite E11; exact Hi11| | | |].
all: clear - IO1 IO2 IO3; first [zlia | replace (2 ^ 3) with 8 by reflexivity; exact IO3]. }
split. { apply (AF 13%nat SOv); [rewrite (Er 13 13%bv eq_refl); unfold SOv, w64; symmetry; apply Z_to_bv_bv_unsigned| | | |].
all: pose proof (u64_range (getr regs0 13)) as U; clear - U Hso S1 S2 S3 T1 T4 T7; unfold SOv, sp0, AFSTACK in *;
first [zlia | replace (2 ^ 3) with 8 by reflexivity; exact (proj2 (proj2 Hso))]. }
split. { apply (AF 12%nat BPv); [rewrite (Er 12 12%bv eq_refl); unfold BPv, w64; symmetry; apply Z_to_bv_bv_unsigned| | | |].
all: pose proof (u64_range (getr regs0 12)) as U; clear - U Hbp S1 S2 S3 T1 T4 T7; unfold BPv, sp0, AFSTACK in *;
first [zlia | replace (2 ^ 3) with 8 by reflexivity; exact (proj2 (proj2 Hbp))]. }
split. { destruct Hcf as [Hc|Hc]; [apply (AF 15%nat 0) | apply (AF 15%nat 1)]; try (rewrite (Er 15 15%bv eq_refl); exact Hc);
first [reflexivity | zlia]. }
(* the released facts *)
split. { apply (AF 10%nat n); [rewrite E10, Hn; reflexivity| | | |].
all: clear - Nlo; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 32%nat T); [exact EaT| | | |].
all: clear - hf1 hf2 TAL; first [zlia | exact TAL]. }
split. { apply (AF 33%nat (ly_C ly)); [exact EaC| | | |].
all: clear - hf7 hf8 CAL; first [zlia | exact CAL]. }
split. { apply (AF 34%nat SB); [exact EaSB| | | |].
all: clear - hf3 hf4 hf5 hf6 SAL; first [zlia | exact SAL]. }
split. { apply (AF 35%nat (ly_top ly)); [exact EaTOP| | | |].
all: clear - T1 T2 T3 T4 T7; first [zlia | exact T3]. }
split. { apply (AF 36%nat (Z.of_nat (length tr))); [reflexivity| | | |].
all: clear - TL; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 37%nat (j0 mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - j0; first [zlia | pose proof (Z.mod_pos_bound j0 (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 38%nat R8v); [reflexivity| | | |].
all: clear - DR R8r; first [zlia | replace (2 ^ 3) with 8 by reflexivity; zlia]. }
split. { apply (AF 39%nat cl); [reflexivity| | | |].
all: clear - CK; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 40%nat Pv); [exact EaP| | | |].
all: clear - DR hf1 hf2 TAL; unfold AGj6.Pv, t_cache in *; first [zlia | replace (2 ^ 4) with 16 by reflexivity; apply Z.mod_divide in TAL as [q Hq]; [|zlia]; apply Z.mod_divide; [zlia|]; exists (q * 256 + 13 + 5 * cl); zlia]. }
split. { apply (AF 41%nat cnt); [reflexivity| | | |].
all: clear - Hcnt; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 42%nat v); [reflexivity| | | |].
all: clear - Hv; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 43%nat (csz mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - csz; first [zlia | pose proof (Z.mod_pos_bound csz (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 44%nat PVv); [exact EaPV| | | |].
all: clear - DR hf1 hf2 TAL Hcnt; unfold AGj6.PVv, AGj6.Pv, t_cache in *; first [zlia | replace (2 ^ 2) with 4 by reflexivity; apply Z.mod_divide in TAL as [q Hq]; [|zlia]; apply Z.mod_divide; [zlia|]; exists (q * 1024 + 56 + 20 * cl + (cnt - 1)); zlia]. }
split. { apply (AF 45%nat Kv); [exact EaK| | | |].
all: clear - V1 V2 K32 K1 K5; first [zlia | replace (2 ^ 5) with 32 by reflexivity; exact K32]. }
split. { apply (AF 46%nat jb); [reflexivity| | | |].
all: clear - Hjb; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 47%nat SHBv); [reflexivity| | | |].
all: clear; unfold AGj6.SHBv; first [zlia | reflexivity]. }
split. { apply (AF 48%nat SKv); [exact EaSK| | | |].
all: clear - DR K32; unfold AGj6.SKv, AGj6.SHBv in *; first [zlia | replace (2 ^ 2) with 4 by reflexivity; apply Z.mod_divide in K32 as [q Hq]; [|zlia]; apply Z.mod_divide; [zlia|]; exists (536862720 + q); rewrite Hq; replace (q * 32) with (q * 4 * 8) by zlia; rewrite Z.div_mul by zlia; zlia]. }
split. { apply (AF 49%nat (j1 mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - j1; first [zlia | pose proof (Z.mod_pos_bound j1 (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 50%nat (j2 mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - j2; first [zlia | pose proof (Z.mod_pos_bound j2 (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 51%nat (j3 mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - j3; first [zlia | pose proof (Z.mod_pos_bound j3 (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 52%nat SSLOTv); [exact EaSSLOT| | | |].
all: clear - DR hf1 hf2 TAL; unfold AGj6.SSLOTv, t_stats in *; first [zlia | replace (2 ^ 3) with 8 by reflexivity; apply Z.mod_divide in TAL as [q Hq]; [|zlia]; apply Z.mod_divide; [zlia|]; exists (q * 512 + 364 + cl); zlia]. }
split. { apply (AF 53%nat (j4 mod 2 ^ 64)); [apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity| | | |].
all: clear - j4; first [zlia | pose proof (Z.mod_pos_bound j4 (2 ^ 64) ltac:(zlia)); zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 54%nat PBv); [exact EaPB| | | |].
all: clear - DR; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 55%nat N8D); [reflexivity| | | |].
all: clear - DR; first [zlia | replace (2 ^ 3) with 8 by reflexivity; zlia]. }
split. { apply (AF 56%nat (N8D / 8)); [reflexivity| | | |].
all: clear - DR; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split. { apply (AF 62%nat NPv); [exact EaNP| | | |].
all: clear - NPr; first [zlia | replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r]. }
split; [|exact I]. { apply (AF 63%nat NDv); [exact EaND| | | |].
all: clear - DR; first [zlia | replace (2 ^ 3) with 8 by reflexivity; zlia]. }
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The machine registers at Allocate's entry are REGS_G over E0.                                                    *)
Local Ltac reg_atom :=
cbn [sv_denot]; unfold AGj6.E0; rewrite Z.add_0_r, ew_Ereg_lt by lia;
match goal with |- _ = Z_to_bv 64 (bv_unsigned (getr _ ?x)) => let y := eval vm_compute in x in change x with y end;
rewrite Z_to_bv_bv_unsigned; reflexivity.
Local Ltac reg_other := rewrite HUo by (let Hc := fresh "Hc" in intro Hc; vm_compute in Hc; discriminate Hc).
Local Ltac reg_case :=
match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) => let x := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with x end;
lazymatch goal with
| |- _ = sv_denot _ (SLit 0) => exact (getr_zero regsU)
| |- _ = sv_denot _ (SLit 8) => exact HU12
| |- _ = sv_denot _ (SLit 1) => exact HU14
| |- _ = sv_denot _ (SOff 11 0) => transitivity (getr regs0 11%bv); [exact HU10 | reg_atom]
| |- _ = sv_denot _ (SOff 10 0) => transitivity (getr regs0 10%bv); [exact HU11 | reg_atom]
| |- _ = sv_denot _ (SLit _) => reg_other; exact Htp
| |- _ = sv_denot _ (SOff _ 0) => reg_other; reg_atom
end.
Lemma REGS_ok : regs_ok E0 REGS_G regsU.
Proof.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [reg_case|]).
destruct Hr.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The seed.                                                                                                        *)
Lemma SEED_ok : st_ok tfibsegs E0 KS_1 (restrict (w_H W) (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs))).
Proof.
assert (R0 : Forall (region_ok tfibsegs E0 (mrestrict (w_H W) mem0)) REG0KG) by (eapply AGjd.REG0K_ok; eassumption).
rewrite restrict_mkst_fx. unfold KS_1, SSGK, w64, st_ok.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact REGS_ok|]. split; [|exact FACTS_ok].
split; [vm_compute; reflexivity|]. split; [exact R0 | exact PAIRS_ok].
Qed.
End e.
End d.
About REGS_ok.
About PAIRS_ok.
About FACTS_ok.
About SEED_ok.
