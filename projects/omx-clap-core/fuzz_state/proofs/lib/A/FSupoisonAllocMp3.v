(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFjg.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan build. *)
(* Modified by Theorem Labs, 2026-10: Htr is areq_ok S (KDepot tr), the depot walk's trace-length premise, instead of In tr (as_universe B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/AFjg.v, with its module names changed; 618 of its 748 lines of code are new or changed and 280 lines of the source are left out. *)
(* Malloc PRIMARY hit-k walk (n <= 48) under ARU, any UP: threads lib/A/AFil.v (malloc_hitk) over AFjg.v (D1w, tail_inner, hitk_inner), AFjb.v (D1W_ok, LEAF_ok), AFjf.v (AR_transport, AR_final, LEAF_final), AFje.v (SEED_ok), AFjc.v (junk_values, KPRES, SKPRES, PB250, shadow250), AFi1.v (SS0K, REG0K), AFj6.v (zone facts), with lib/A/FSupoison.v, FSupoisonU.v, FSupoisonAllocR.v and FSupoisonAllocMp1.v. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* The trace premises follow S0 946ad86dc9f: Htr is areq_ok S (KDepot tr) in section e (as AFjb / AFjg) and tr_admit (as_universe B) S tr in malloc_hitkU (as AFil); hitk_innerU gets the trace length (tr_admit_len). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG07.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AE3d AFhy AFi1 AFi2 AFj6 AFhz AFi3 AFjc AFjd AFje AFjb AFjf AFj3 AFj4 AFj5 AFjg.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YL0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU FSupoisonAllocR FSupoisonAllocMp1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module AllocR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocR.
Module Mp1 := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocMp1.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia ].

(* Where each region of the hit-g seed (AFhy.v REG0K) sits: an absolute literal below the shadow, or one of nine
   symbolic bases (sp, T, C, P, PV, K, SK, SSLOT, U) with these offsets. *)
Definition reg_lowb (r : YP09.region) : bool :=
  match YP09.r_base r with
  | None => (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? SHADOW_OFF)
  | Some _ => true
  end.
Definition reg_someb (r : YP09.region) : bool :=
  match YP09.r_base r with
  | None => true
  | Some k =>
      (Nat.eqb k 2 && (- ASTACK <=? YP09.r_lo r) && (YP09.r_hi r <=? 0)) ||
      (Nat.eqb k 32 && (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? kThreadObjSize)) ||
      (Nat.eqb k 33 && (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 256)) ||
      (Nat.eqb k 40 && (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 16)) ||
      (Nat.eqb k 44 && (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 4)) ||
      (Nat.eqb k 45 && (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 16)) ||
      (Nat.eqb k 48 && (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 1)) ||
      (Nat.eqb k 52 && (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 8)) ||
      (Nat.eqb k 60 && (- 16 <=? YP09.r_lo r) && (YP09.r_hi r <=? 0))
  end.
Lemma REG0K_classb : forallb (fun r => reg_lowb r && reg_someb r) REG0K = true.
Proof. vm_compute. reflexivity. Qed.

(* The section of lib/A/AFjg.v, with the user-poisoned head list UP threaded: the donor's ARm / AR of mem0 is
   replaced by FSupoison.ARU of UP over the SAME mem0, which is the memory the machine runs on. Every other
   hypothesis is the donor's, on that real mem0. Arguments abstract in declaration order (Proof using All). *)
Set Default Proof Using "All".
Section d.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (ch : list (Z * Z * Z)).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Variables (B : asyms) (S : astate) (l : list Z) (off : Z).
Variable UP : list (Z * Z).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Local Abbreviation RZ := (@AFj6.RZ).
Local Abbreviation R8v := (@AFj6.R8v n).
Local Abbreviation NPv := (@AFj6.NPv n).
Local Abbreviation N8D := (@AFj6.N8D n).
Local Abbreviation Pv := (@AFj6.Pv ly cl).
Local Abbreviation PVv := (@AFj6.PVv ly cl cnt).
Local Abbreviation Kv := (@AFj6.Kv ly cl v).
Local Abbreviation SKv := (@AFj6.SKv ly cl v).
Local Abbreviation SSLOTv := (@AFj6.SSLOTv ly cl).
Local Abbreviation PBv := (@AFj6.PBv ly n cl v).
Local Abbreviation Uv := (@AFj6.Uv ly cl v).
Local Abbreviation SUv := (@AFj6.SUv ly cl v).
Local Abbreviation FILv := (@AFj6.FILv n).
Local Abbreviation tr := (@AFj6.tr ly regs0 ch).
Local Abbreviation E0 := (@AFj6.E0 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation WIN := (@AFj6.WIN ly regs0 n cl v).
Local Abbreviation WINT := (@AFj6.WINT ly cl).
Local Abbreviation DZONE := (@AFj6.DZONE ly).
Hypotheses (Hcl : 1 <= cl <= 31) (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32) (Hcnt : 1 <= cnt <= 16) (Hjb : 0 <= jb <= 255).
Hypothesis Hv2 : v mod 2 = 0.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis HKpres : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Hypothesis HSKpres : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Hypothesis HPB250 : NPv mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W) mem0) PBv 1 250.
Hypothesis Nrange : 0 <= n <= 48.
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Hypothesis TS : TfibSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis HARU : FSP.ARU tfibsegs B ly S UP W mem0 md0.
Hypothesis Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S cl) = l ++ [off].
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcnt_def : cnt = Z.of_nat (length (l ++ [off])).
Hypothesis Hoff_def : off = 16 * v.
Hypothesis Hcsz_def : csz = class_size cl.
Hypothesis Hj0 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfibsegs (mrestrict (w_H W) mem0) SSLOTv 8 j4.
Hypothesis Hjb_def : val_mem tfibsegs (mrestrict (w_H W) mem0) (Kv + RZ - 15) 1 jb.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The two readings. AR holds of FSupoison.unpoison UP mem0; the machine runs on mem0.                             *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma HARu : AR tfibsegs B ly S W (FSP.unpoison UP mem0) md0.
Proof. exact (FSP.ARU_AR tfibsegs B ly S UP W mem0 md0 HARU). Qed.

Lemma HARmu : ARm B ly S (aview tfibsegs (w_H W) (FSP.unpoison UP mem0)).
Proof. exact (FSP.ARU_ARm tfibsegs B ly S UP W mem0 md0 HARU). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. hitk_regions_off_ush: where the walk's regions are, and that none of their bytes is user-poisoned.              *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Local Abbreviation derived_ranges := (@AFj6.derived_ranges _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG DPOST Nrange).
Local Abbreviation high_facts := (@AFj6.high_facts _ ly regs0 mem0 n v Hv LY IMG DPOST).
Local Abbreviation blocks_facts := (@AFj6.blocks_facts _ ly LY IMG).
Local Abbreviation cls_geom := (@AFjc.cls_geom ly regs0 (FSP.unpoison UP mem0) n cl v DPOST Nrange l off Hcl_class).
Local Abbreviation shadow250 := (@AFjc.shadow250 _ W ly regs0 (FSP.unpoison UP mem0) n cl cnt v csz Hv2 LY Hsp DPOST Nrange B S l off HARmu Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).

(* The bytes the hit-g walk's regions (AFhy.v REG0K) and its leaf fix. *)
Definition hitk_fixed (a : Z) : Prop :=
  (sp0 - ASTACK <= a < sp0) \/ (0 <= a < SHADOW_OFF) \/
  (T <= a < T + kThreadObjSize) \/ (ly_C ly <= a < ly_C ly + 256) \/
  (Kv <= a < Kv + csz) \/ (exists g, g mod 8 = 0 /\ Kv <= g < Kv + csz /\ a = shadow_addr g) \/
  DZONE a.

Lemma offU_stk : forall a, sp0 - ASTACK <= a < sp0 -> AllocR.offU UP a.
Proof.
intros a Ha. pose proof Hsp as (S1 & S2 & S3 & S4).
exact (AllocR.stack_offU B ly S UP W mem0 md0 a HARU ltac:(unfold ASTACK in *; lia)).
Qed.

Lemma offU_T : forall a, T <= a < T + kThreadObjSize -> AllocR.offU UP a.
Proof.
intros a Ha. apply (Mp1.offU_owned B ly S UP W mem0 md0 (ly_T ly, kThreadObjSize) a HARU
  ltac:(unfold owned_extents; cbn [In]; tauto)). cbn [fst snd]. unfold T in Ha. exact Ha.
Qed.

Lemma offU_C : forall a, ly_C ly <= a < ly_C ly + 256 -> AllocR.offU UP a.
Proof.
intros a Ha. apply (Mp1.offU_owned B ly S UP W mem0 md0 (ly_C ly, 256) a HARU
  ltac:(unfold owned_extents; cbn [In]; tauto)). cbn [fst snd]. exact Ha.
Qed.

Lemma offU_NB : forall a, ly_NB ly <= a < ly_NB ly + kNodesBlockSize -> AllocR.offU UP a.
Proof.
intros a Ha. apply (Mp1.offU_owned B ly S UP W mem0 md0 (ly_NB ly, kNodesBlockSize) a HARU
  ltac:(unfold owned_extents; cbn [In]; tauto)). cbn [fst snd]. exact Ha.
Qed.

Lemma offU_SB : forall a, ly_SB ly <= a < ly_SB ly + kStoreBlockSize -> AllocR.offU UP a.
Proof.
intros a Ha. apply (Mp1.offU_owned B ly S UP W mem0 md0 (ly_SB ly, kStoreBlockSize) a HARU
  ltac:(unfold owned_extents; cbn [In]; tauto)). cbn [fst snd]. exact Ha.
Qed.

Lemma offU_lo : forall a, 0 <= a < SHADOW_OFF -> AllocR.offU UP a.
Proof. intros a Ha. exact (Mp1.offU_lit B ly S UP W mem0 md0 a HARU Ha). Qed.

Lemma offU_K : forall a, Kv <= a < Kv + csz -> AllocR.offU UP a.
Proof.
intros a Ha. pose proof derived_ranges as DR. pose proof cls_geom as (K1 & _ & K3 & _).
apply (Mp1.offU_hi B ly S UP W mem0 md0 a HARU). ceil. unfold kHighMemBeg, ASAN_CEIL, kMaxSize in *. lia.
Qed.

(* A shadow byte of the cached chunk the walk hands out: the allocator's value there is 250, so it is not one of
   UP's (which read 0 in the unpoisoned reading and 0xf7 in the real one). *)
Lemma offU_Ksh : forall g, g mod 8 = 0 -> Kv <= g < Kv + csz -> AllocR.offU UP (shadow_addr g).
Proof.
intros g G8 Hg. pose proof derived_ranges as DR. pose proof cls_geom as (K1 & _ & K3 & _).
apply (AllocR.offU_nonzero B ly S UP W mem0 md0 (shadow_addr g) 250 HARU).
- unfold shadow_addr. ceil. pose proof (Z.div_pos g 8 ltac:(unfold kHighMemBeg in *; lia) ltac:(lia)) as D1.
  pose proof (Z.div_le_upper_bound g 8 (2 ^ 44) ltac:(lia) ltac:(unfold ASAN_CEIL, kMaxSize in *; lia)) as D2.
  unfold SHADOW_OFF. lia.
- exact (shadow250 g G8 ltac:(rewrite <- Hcsz_def; exact Hg)).
- lia.
- lia.
Qed.

Lemma offU_dz : forall a, DZONE a -> AllocR.offU UP a.
Proof.
intros a Ha. unfold AFj6.DZONE in Ha. destruct Ha as [Ha|[Ha|Ha]].
- apply offU_lo. unfold SHADOW_OFF. lia.
- exact (offU_NB a Ha).
- exact (offU_SB a Ha).
Qed.

Lemma hitk_regions_off_ush : forall a, hitk_fixed a -> AllocR.offU UP a.
Proof.
intros a [Ha|[Ha|[Ha|[Ha|[Ha|[(g & G8 & Hg & ->)|Ha]]]]]].
- exact (offU_stk a Ha). - exact (offU_lo a Ha). - exact (offU_T a Ha). - exact (offU_C a Ha).
- exact (offU_K a Ha). - exact (offU_Ksh g G8 Hg). - exact (offU_dz a Ha).
Qed.

(* The shadow byte of the j-th user granule of the new chunk. *)
Lemma sh_of_U : forall j, shadow_addr (Kv + RZ + 8 * j) = SUv + j.
Proof.
intros j. pose proof derived_ranges as DR. pose proof (Z.div_mod Kv 16 ltac:(lia)) as DK.
unfold shadow_addr, AFj6.SUv, AFj6.Uv, AFj6.SHBv, SHADOW_OFF.
replace (Kv + RZ + 8 * j) with ((Kv / 16 * 2 + RZ / 8 + j) * 8) by lia.
replace (Kv + RZ) with ((Kv / 16 * 2 + RZ / 8) * 8) by lia.
rewrite !Z.div_mul by lia. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The donor's FACT / SEED inputs, moved from the real memory to the unpoisoned reading.                           *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma Hj0u : val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP mem0)) (T + 2784) 8 j0.
Proof.
apply (AllocR.val_mem_to_unpoison (w_H W) UP mem0 (T + 2784) 8 j0); [|exact Hj0].
intros k Hk. apply offU_T. unfold kThreadObjSize. lia.
Qed.

Lemma Hj1u : val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP mem0)) (T + 2800) 8 j1.
Proof.
apply (AllocR.val_mem_to_unpoison (w_H W) UP mem0 (T + 2800) 8 j1); [|exact Hj1].
intros k Hk. apply offU_T. unfold kThreadObjSize. lia.
Qed.

Lemma Hj2u : val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP mem0)) (T + 2808) 8 j2.
Proof.
apply (AllocR.val_mem_to_unpoison (w_H W) UP mem0 (T + 2808) 8 j2); [|exact Hj2].
intros k Hk. apply offU_T. unfold kThreadObjSize. lia.
Qed.

Lemma Hj3u : val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP mem0)) (T + 2816) 8 j3.
Proof.
apply (AllocR.val_mem_to_unpoison (w_H W) UP mem0 (T + 2816) 8 j3); [|exact Hj3].
intros k Hk. apply offU_T. unfold kThreadObjSize. lia.
Qed.

Lemma Hj4u : val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP mem0)) SSLOTv 8 j4.
Proof.
pose proof derived_ranges as DR.
apply (AllocR.val_mem_to_unpoison (w_H W) UP mem0 SSLOTv 8 j4); [|exact Hj4].
intros k Hk. apply offU_T. unfold kThreadObjSize, t_unwinding, T in *. lia.
Qed.

Lemma Hjbu : val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP mem0)) (Kv + RZ - 15) 1 jb.
Proof.
pose proof derived_ranges as DR. pose proof cls_geom as (K1 & _ & _ & _ & K5 & K6).
apply (AllocR.val_mem_to_unpoison (w_H W) UP mem0 (Kv + RZ - 15) 1 jb); [|exact Hjb_def].
intros k Hk. apply offU_K. rewrite Hcsz_def. lia.
Qed.

Lemma HKpresu : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) (FSP.unpoison UP mem0) a.
Proof. intros a Ha. apply AllocR.apresent_to_unpoison. exact (HKpres a Ha). Qed.

Lemma HSKpresu : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) (FSP.unpoison UP mem0) a.
Proof. intros a Ha. apply AllocR.apresent_to_unpoison. exact (HSKpres a Ha). Qed.

Lemma HPB250u : NPv mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP mem0)) PBv 1 250.
Proof.
intros E8. pose proof derived_ranges as DR. pose proof cls_geom as (K1 & _ & _ & _ & K5 & K6).
pose proof (Z.div_mod NPv 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound NPv 8 ltac:(lia)) as MB.
pose proof (Z.div_mod Kv 16 ltac:(lia)) as DK.
apply (AllocR.val_mem_to_unpoison (w_H W) UP mem0 PBv 1 250); [|exact (HPB250 E8)].
intros k Hk.
replace (PBv + Z.of_nat k) with (shadow_addr (Kv + RZ + N8D)).
2:{ replace (Z.of_nat k) with 0 by lia. rewrite Z.add_0_r.
    unfold shadow_addr, AFj6.PBv, AFj6.SHBv, SHADOW_OFF. reflexivity. }
apply offU_Ksh.
- unfold AFj6.N8D. replace (Kv + RZ + NPv / 8 * 8) with ((Kv / 16 * 2 + RZ / 8 + NPv / 8) * 8) by lia.
  apply Z.mod_mul. lia.
- rewrite Hcsz_def. unfold AFj6.N8D in *. lia.
Qed.

Lemma Hpres0u : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (FSP.unpoison UP mem0) a.
Proof. intros a Ha. apply AllocR.apresent_to_unpoison. exact (Hpres0 a Ha). Qed.

(* The walk's symbolic seed at the unpoisoned reading: the donor's SEED_ok, applied there. *)
Lemma SEEDu : st_ok tfibsegs E0 SS0K (restrict (w_H W) (YK11.mkst regs0 (w64 0x53074) (FSP.unpoison UP mem0) (seg_rom tfibsegs))).
Proof.
exact (@AFje.SEED_ok _ _ W ly regs0 (FSP.unpoison UP mem0) n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Htp Hsp DPOST Nrange Hcl_def B S l off TS HTSD HARmu Hpres0u Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj0u Hj1u Hj2u Hj3u Hj4u Hjbu).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The depot post, moved between the two readings (its cells are the constant cells and the depot zone).           *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Local Abbreviation depot_ids_bound := (@AFjb.depot_ids_bound B TS).
Local Abbreviation depot_mem_ok_agree := (@AFjb.depot_mem_ok_agree ly regs0 mem0 n v Hv DPOST B l off TS).

Lemma DPOST3_xfer : forall z (m1 m2 : word -> option byte),
  (forall a, DZONE a -> aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m1 a) ->
  (forall c k, In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
     aview tfibsegs (w_H W) m2 (aeval B ly (c_at c) + k) = aview tfibsegs (w_H W) m1 (aeval B ly (c_at c) + k)) ->
  AFjb.DPOST3 W ly regs0 ch B S z m1 -> AFjb.DPOST3 W ly regs0 ch B S z m2.
Proof.
intros z m1 m2 EZ EC (AOK & DEP & CST). split; [exact AOK|]. split.
- apply (depot_mem_ok_agree (depot_after z tr S) (aview tfibsegs (w_H W) m1)); [|exact EZ|exact DEP].
  pose proof (wf_depot _ _ _ _ _ (am_wf B ly S _ HARmu)) as [ND INCL].
  pose proof (depot_ids_bound S _ (conj ND INCL)). unfold depot_after. destruct (z =? 0); [lia|].
  unfold depot_ids in *. cbn. rewrite length_app. cbn. lia.
- exact (Mp1.cells_agree_list B ly (aview tfibsegs (w_H W) m1) (aview tfibsegs (w_H W) m2) (as_const B ly) EC CST).
Qed.

Lemma const_off : forall c k, In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
  AllocR.offU UP (aeval B ly (c_at c) + k).
Proof. intros c k Hc Hk. exact (Mp1.const_offU B ly S UP W mem0 md0 c k TS HARU HTSD Hc Hk). Qed.

(* The post of the depot call reads the same in both readings. *)
Lemma DPOST3_to_u : forall z (m : word -> option byte),
  AFjb.DPOST3 W ly regs0 ch B S z m -> AFjb.DPOST3 W ly regs0 ch B S z (FSP.unpoison UP m).
Proof.
intros z m H. apply (DPOST3_xfer z m (FSP.unpoison UP m)); [| |exact H].
- intros a Ha. apply AllocR.aview_unpoison. exact (offU_dz a Ha).
- intros c k Hc Hk. apply AllocR.aview_unpoison. exact (const_off c k Hc Hk).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* hitk_seed_regions_off_ush: every byte a region of the walk's seed (AFhy.v REG0K) fixes is off UP (the image's       *)
(* literals, the stack window, T, C, the cached chunk's header and user area, and its first shadow byte). Hence the   *)
(* donor's seed, which SEED_ok gives at the unpoisoned reading, holds of the real memory too.                        *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Local Abbreviation E2 := (@AFj6.E2 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaT := (@AFj6.EaT ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaC := (@AFj6.EaC ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaP := (@AFj6.EaP ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaPV := (@AFj6.EaPV ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaK := (@AFj6.EaK ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSK := (@AFj6.EaSK ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSSLOT := (@AFj6.EaSSLOT ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaU := (@AFj6.EaU ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).

Lemma regions_off_classb : forall rs, forallb (fun r => reg_lowb r && reg_someb r) rs = true ->
  AllocR.regions_offU UP E0 rs.
Proof.
pose proof derived_ranges as DR. pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
pose proof cls_geom as (K1 & _ & _ & _ & K5 & K6). pose proof Hsp as (SP1 & SP2 & SP3 & SP4).
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (Z.div_mod Kv 16 ltac:(lia)) as DK.
destruct F1 as (ZT1 & ZT2 & _). destruct F7 as (ZC1 & ZC2 & _).
ceil. unfold kThreadObjSize, ASAN_CEIL, t_cache, t_unwinding, kHighMemBeg in *.
assert (RT : 0 <= ly_T ly < 2 ^ 64) by lia.
assert (RC : 0 <= ly_C ly < 2 ^ 64) by lia.
assert (RK : 0 <= Kv < 2 ^ 64) by lia.
assert (RSK : 0 <= SKv < 2 ^ 64) by lia.
assert (RPv : 0 <= Pv < 2 ^ 64) by lia.
assert (RPVv : 0 <= PVv < 2 ^ 64) by lia.
assert (RSS : 0 <= SSLOTv < 2 ^ 64) by lia.
assert (RU : 0 <= Uv < 2 ^ 64) by lia.
intros rs HC r a Hr Ha.
pose proof (proj1 (forallb_forall _ _) HC r Hr) as K. apply andb_prop in K as [KL KS].
unfold reg_lowb in KL. unfold reg_someb in KS.
set (rb := YP09.r_base r) in *. clearbody rb. destruct rb as [k|]; cbn [base_val] in Ha.
2:{ apply andb_prop in KL as [K1' K2']. apply Z.leb_le in K1'. apply Z.leb_le in K2'. apply offU_lo. lia. }
repeat match type of KS with (_ || _) = true => apply Bool.orb_prop in KS; destruct KS as [KS|KS] end;
  apply andb_prop in KS as [KS K3']; apply andb_prop in KS as [K1' K2'];
  apply Nat.eqb_eq in K1'; subst k; apply Z.leb_le in K2'; apply Z.leb_le in K3'.
- rewrite E2 in Ha. change (bv_unsigned (getr regs0 2)) with sp0 in Ha. apply offU_stk. unfold ASTACK in *. lia.
- rewrite EaT in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RT. apply offU_T. lia.
- rewrite EaC in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RC. apply offU_C. lia.
- rewrite EaP in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RPv.
  apply offU_T. unfold kThreadObjSize, t_cache in *. lia.
- rewrite EaPV in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RPVv.
  apply offU_T. unfold kThreadObjSize, t_cache in *. lia.
- rewrite EaK in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RK.
  apply offU_K. rewrite Hcsz_def. lia.
- rewrite EaSK in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RSK.
  replace a with (shadow_addr Kv) by (unfold shadow_addr, AFj6.SKv, AFj6.SHBv, SHADOW_OFF in *; lia).
  apply offU_Ksh; [|rewrite Hcsz_def; lia].
  replace Kv with (Kv / 16 * 2 * 8) by lia. apply Z.mod_mul. lia.
- rewrite EaSSLOT in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RSS.
  apply offU_T. unfold kThreadObjSize, t_unwinding in *. lia.
- rewrite EaU in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by exact RU.
  apply offU_K. unfold AFj6.Uv in *. rewrite Hcsz_def. lia.
Qed.

Lemma hitk_seed_regions_off_ush : AllocR.regions_offU UP E0 (ss_mem SS0K).
Proof. change (ss_mem SS0K) with REG0K. exact (regions_off_classb REG0K REG0K_classb). Qed.

(* The donor's seed on the real memory. *)
Lemma SEEDr : st_ok tfibsegs E0 SS0K (restrict (w_H W) (YK11.mkst regs0 (w64 0x53074) mem0 (seg_rom tfibsegs))).
Proof.
exact (proj1 (AllocR.st_ok_unpoison_iff UP E0 SS0K (w_H W) regs0 (w64 0x53074) mem0 (seg_rom tfibsegs)
  hitk_seed_regions_off_ush) SEEDu).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. The donor walk's own hypotheses (lib/A/AFjg.v section e), all on the REAL mem0 the machine runs on.             *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section e.
Variable mat0 : list word.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hch : if sp0 + 16 <? ly_top ly
then (if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\
fpchain (rdword (aview tfibsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch)
else ch = [].
Hypothesis U1 : tfib_unwind_spec.
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Htr : areq_ok S (KDepot tr).
Hypothesis HD1 : tfib_depot_spec B.
Hypothesis HDPOST : forall z m, DPOST z m -> AFjb.DPOST3 W ly regs0 ch B S z m.
Hypothesis HDPOST' : forall z m, AFjb.DPOST3 W ly regs0 ch B S z m -> DPOST z m.
Hypothesis Hmat0 : mat0 = m_vm_materialized md0.

Local Abbreviation at_RET := (@AFj6.at_RET _ W ly regs0 mem0 md0 n cl cnt v jb DPOST).
Local Abbreviation at_RETu := (@AFj6.at_RET _ W ly regs0 (FSP.unpoison UP mem0) md0 n cl cnt v jb DPOST).
Local Abbreviation MPF := (@AFjb.MPF ly regs0 n ch cl B S l off).
Local Abbreviation Kc_user := (@AFjb.Kc_user ly regs0 mem0 n ch cl v Hcl DPOST Nrange B S l off Hoff_def).
Local Abbreviation WR_owned := (@AFjb.WR_owned _ W ly regs0 (FSP.unpoison UP mem0) n ch cl cnt v csz jb Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HPB250u Nrange B S l off TS HARmu Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def).
Local Abbreviation AR_finalu := (@AFjf.AR_final _ _ W ly regs0 (FSP.unpoison UP mem0) md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HKpresu HSKpresu HPB250u Nrange Hcl_def SEEDu B S l off TS HTSD HARmu Hinited Hcache Hcl_class Hcnt_def Hoff_def Hcsz_def Hj4u Hjbu).
Local Abbreviation SF_chunks := (@AFjb.SF_chunks _ W ly regs0 (FSP.unpoison UP mem0) n ch cl cnt v Hcl Hv Hv2 DPOST Nrange B S l off HARmu Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation case0_sizes := (@AFj6.case0_sizes n Nrange).
Local Abbreviation aview_agree := (@AFjb.aview_agree W).

(* The leaf of the hit-g walk in ARU form. Port-from: lib/A/AFjb.v:491 LEAF_ok; the AR of the new state is the
   donor's AR_transport (through AFjf.v:1132 AR_final) at the unpoisoned readings of mem0 and mem'; the frame,
   the registers and the stack presence are the donor's, on the real memory; upoison_ok / upoisoned are
   re-established: malloc keeps every live block, and it writes only the new chunk, which is outside them. *)
Lemma LEAF_okU : forall odd z W' c', at_RET odd z W' c' -> (odd = true <-> NPv mod 8 <> 0) -> MPF z ->
  FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n
    (ck_user (AFjb.new_chunk cl off n), AFjb.st_final S cl l off n tr z) W' c'.
Proof.
intros odd z W' c' HR Hodd MP.
pose proof derived_ranges as DR. pose proof cls_geom as (K1 & _ & _ & _ & K5 & K6).
pose proof Hsp as (SP1 & SP2 & SP3 & SP4). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (Z.div_mod NPv 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound NPv 8 ltac:(lia)) as MB.
pose proof (Z.div_mod Kv 16 ltac:(lia)) as DK.
destruct HR as (-> & regs' & mem' & mat & -> & R10 & RCS & (memD & DP & PRD & EQD) & MEQF & PRS & PRW & VALS).
destruct VALS as (V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11).
assert (SHPB : forall k, 0 <= k < 1 -> NPv mod 8 <> 0 -> AllocR.offU UP (PBv + k)).
{ intros k Hk E8. replace (PBv + k) with (shadow_addr (Kv + RZ + N8D)).
  2:{ replace k with 0 by lia. rewrite Z.add_0_r. unfold shadow_addr, AFj6.PBv, AFj6.SHBv, SHADOW_OFF. reflexivity. }
  apply offU_Ksh.
  - unfold AFj6.N8D. replace (Kv + RZ + NPv / 8 * 8) with ((Kv / 16 * 2 + RZ / 8 + NPv / 8) * 8) by lia.
    apply Z.mod_mul. lia.
  - rewrite Hcsz_def. unfold AFj6.N8D in *. lia. }
assert (HRu : at_RETu odd z W (mkCfg (YK11.mkst regs' (getr regs0 1) (FSP.unpoison UP mem') (seg_rom tfibsegs))
  (with_vm_backing (m_vm_lazy md0) mat md0))).
{ split; [reflexivity|]. exists regs', (FSP.unpoison UP mem'), mat. split; [reflexivity|].
  split; [exact R10|]. split; [exact RCS|].
  split.
  { exists (FSP.unpoison UP memD). split; [apply HDPOST'; apply DPOST3_to_u; exact (HDPOST z memD DP)|]. split.
    - intros a Ha HP. apply AllocR.apresent_to_unpoison. apply (PRD a Ha).
      exact (AllocR.apresent_of_unpoison (w_H W) UP mem0 a (offU_dz a Ha) HP).
    - intros x Hx. unfold FSP.unpoison.
      destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact (EQD x Hx)]. }
  split.
  { intros x N1 N2 N3 N4. unfold FSP.unpoison.
    destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact (MEQF x N1 N2 N3 N4)]. }
  split; [intros a Ha; apply AllocR.apresent_to_unpoison; exact (PRS a Ha)|].
  split; [intros a Ha; apply AllocR.apresent_to_unpoison; exact (PRW a Ha)|].
  cbv zeta.
  split. { apply (AllocR.val_mem_to_unpoison (w_H W) UP mem' (Kv + RZ - 16) 1); [|exact V3].
    intros k Hk. apply offU_K. rewrite Hcsz_def. lia. }
  split. { apply (AllocR.val_mem_to_unpoison (w_H W) UP mem' (Kv + RZ - 15) 1); [|exact V4].
    intros k Hk. apply offU_K. rewrite Hcsz_def. lia. }
  split. { apply (AllocR.val_mem_to_unpoison (w_H W) UP mem' (Kv + RZ - 14) 2); [|exact V5].
    intros k Hk. apply offU_K. rewrite Hcsz_def. lia. }
  split. { apply (AllocR.val_mem_to_unpoison (w_H W) UP mem' (Kv + RZ - 12) 4); [|exact V6].
    intros k Hk. apply offU_K. rewrite Hcsz_def. lia. }
  split. { apply (AllocR.val_mem_to_unpoison (w_H W) UP mem' Pv 4); [|exact V7].
    intros k Hk. apply offU_T. unfold kThreadObjSize, t_cache in *. lia. }
  split. { apply (AllocR.val_mem_to_unpoison (w_H W) UP mem' (T + t_unwinding) 1); [|exact V8].
    intros k Hk. apply offU_T. unfold kThreadObjSize, t_unwinding in *. lia. }
  split. { intros x Hx. unfold FSP.unpoison.
    destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact (V9 x Hx)]. }
  split. { intros Eodd. apply (AllocR.val_mem_to_unpoison (w_H W) UP mem' PBv 1); [|exact (V10 Eodd)].
    intros k Hk. apply SHPB; [lia | exact (proj1 Hodd Eodd)]. }
  intros x Hx. rewrite (AllocR.unpoison_offU_w UP mem' x (offU_K (bv_unsigned x) ltac:(rewrite Hcsz_def; lia))).
  exact (V11 x Hx). }
pose proof (AR_finalu HDPOST odd z regs' (FSP.unpoison UP mem') mat HRu Hodd MP HARu) as ARfin.
exists ly, regs', mem', (with_vm_backing (m_vm_lazy md0) mat md0).
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
cbn [fst snd]. split; [| split; [rewrite R10, Kc_user; reflexivity | exact (proj2 MP)]].
apply (AllocR.acall_postU_intro B ASTACK ly S UP W regs0 mem0 md0 _ ly _ W regs' mem' _ HARU ARfin).
- apply layout_le_refl.
- apply wle_refl.
- intros r Hr. apply RCS. unfold acallee_saved in Hr.
  assert (H18 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear - RCS H18.
  assert (E5 : forall k : Z, 0 <= k < 32 -> forall b : bv 5, bv_unsigned b = k -> Z_to_bv 5 k = b) by (intros k Hk b Hb; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 5) with 32; rewrite Z.mod_small by lia; symmetry; exact Hb).
  destruct H18 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
  [ rewrite (E5 2 ltac:(lia) 2%bv eq_refl) | rewrite (E5 3 ltac:(lia) 3%bv eq_refl) | rewrite (E5 4 ltac:(lia) 4%bv eq_refl)
  | rewrite (E5 8 ltac:(lia) 8%bv eq_refl) | rewrite (E5 9 ltac:(lia) 9%bv eq_refl) | rewrite (E5 18 ltac:(lia) 18%bv eq_refl)
  | rewrite (E5 19 ltac:(lia) 19%bv eq_refl) | rewrite (E5 20 ltac:(lia) 20%bv eq_refl) | rewrite (E5 21 ltac:(lia) 21%bv eq_refl)
  | rewrite (E5 22 ltac:(lia) 22%bv eq_refl) | rewrite (E5 23 ltac:(lia) 23%bv eq_refl) | rewrite (E5 24 ltac:(lia) 24%bv eq_refl)
  | rewrite (E5 25 ltac:(lia) 25%bv eq_refl) | rewrite (E5 26 ltac:(lia) 26%bv eq_refl) | rewrite (E5 27 ltac:(lia) 27%bv eq_refl) ];
  cbn [In]; tauto.
- unfold same_io. destruct md0; cbn; repeat split; reflexivity.
- intros a Ra NO NO' NS NE. apply aview_agree; [exact Ra|]. apply MEQF; rewrite unsigned_lit_small by exact Ra.
  + intros Hw. destruct (WR_owned odd a Ra ltac:(intros Ho; apply Hodd; exact Ho) (or_introl Hw)) as [Hs|Ho]; [|exact (NO Ho)].
    apply NS. unfold ascratch, spZ. left. exact Hs.
  + intros Hw. destruct (WR_owned odd a Ra ltac:(intros Ho; apply Hodd; exact Ho) (or_intror (or_introl Hw))) as [Hs|Ho]; [|exact (NO Ho)].
    apply NS. unfold ascratch, spZ. left. exact Hs.
  + intros Hu. apply NE. split; [discriminate|]. rewrite Kc_user.
    pose proof case0_sizes as (_ & _ & _ & _ & _ & _ & RQ). rewrite RQ. exact Hu.
  + intros Hw. destruct (WR_owned odd a Ra ltac:(intros Ho; apply Hodd; exact Ho) (or_intror (or_intror Hw))) as [Hs|Ho]; [|exact (NO Ho)].
    apply NS. unfold ascratch, spZ. left. exact Hs.
- intros a Ha. exact (PRS a Ha).
- apply (AllocR.upoison_ok_keep B ly S ly (AFjb.st_final S cl l off n tr z) UP
    (FSP.ARU_ok tfibsegs B ly S UP W mem0 md0 HARU)).
  intros r p n0 Hr Hb _ _. unfold ablocks, blocks in Hb |- *. rewrite (SF_chunks z), filter_app, !map_app.
  apply in_app_iff. left. exact Hb.
- apply (AllocR.upoisoned_keep UP W W mem0 mem' (FSP.ARU_poisoned tfibsegs B ly S UP W mem0 md0 HARU)).
  intros s Hs. pose proof (FSP.ush_facts tfibsegs B ly S UP W mem0 md0 s HARU Hs) as (Hown & Hs1 & Hs2).
  assert (Rs : 0 <= s < 2 ^ 64) by (unfold SHADOW_OFF, kHighMemBeg in *; lia).
  assert (NOFF : ~ AllocR.offU UP s).
  { unfold AllocR.offU. rewrite Z.mod_small by exact Rs. rewrite Hs. discriminate. }
  apply aview_agree; [exact Rs|]. apply MEQF; rewrite unsigned_lit_small by exact Rs.
  + intros HW. unfold AFj6.WIN in HW.
    pose proof (zone3_apart_hsh _ _ s (proj1 high_facts) ltac:(unfold kLowShadowBeg, SHADOW_OFF in *; lia)) as NT.
    destruct HW as [HW|[HW|[HW|HW]]].
    * unfold ASTACK, kHighMemBeg, SHADOW_OFF in *. lia.
    * apply NT. unfold AFj6.WINT in HW. unfold kThreadObjSize, t_unwinding, t_cache in *. lia.
    * unfold AFj6.Uv, kHighMemBeg, SHADOW_OFF in *. lia.
    * destruct HW as [Eodd HW]. apply NOFF. replace s with (PBv + 0) by lia.
      apply SHPB; [lia | exact (proj1 Hodd Eodd)].
  + intros HD. exact (NOFF (offU_dz s HD)).
  + intros HU. unfold kHighMemBeg, SHADOW_OFF in *. lia.
  + intros HU. apply NOFF.
    replace s with (shadow_addr (Kv + RZ + 8 * (s - SUv))) by (rewrite sh_of_U; lia).
    apply offU_Ksh.
    * replace (Kv + RZ + 8 * (s - SUv)) with ((Kv / 16 * 2 + RZ / 8 + (s - SUv)) * 8) by lia.
      apply Z.mod_mul. lia.
    * unfold AFj6.N8D in HU. rewrite Z.div_mul in HU by lia. rewrite Hcsz_def. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 6. The depot call. Port-from: lib/A/AFjb.v:397 D1W_ok and AFjg.v:333 D1w; only the two AR-consuming inputs of     *)
(*    tfib_depot_spec (the constant cells and the depot's own cells) are re-derived: AR gives them at the unpoisoned  *)
(*    reading, and they move to the real memory because the constant cells and the depot zone are off UP.            *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Local Abbreviation CZONE_untouched := (@AFjb.CZONE_untouched _ ly regs0 (FSP.unpoison UP mem0) n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange l off).
Local Abbreviation const_cells_zone := (@AFjb.const_cells_zone ly regs0 (FSP.unpoison UP mem0) n v Hv DPOST B l off TS HTSD).
Local Abbreviation depot_at0u := (@AFjb.depot_at0 _ W ly regs0 (FSP.unpoison UP mem0) n cl cnt v jb Hcl Hv Hcnt Hjb Hsp DPOST Nrange B S HARmu).
Local Abbreviation DZONE_disj := (@AFj6.DZONE_disj _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange).

Lemma D1W_okU : forall (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
getr regs 10 = Z_to_bv 64 (sp0 - IFRAME + 16) -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = Z_to_bv 64 TFIB_TP -> getr regs 1 = Z_to_bv 64 0x322a0 ->
bv_unsigned (getr regs 2) = sp0 - 2272 ->
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem a) ->
(forall x : word, ~ WIN false (bv_unsigned x) -> mem x = mem0 x) ->
SRr tfibsegs W (mkCfg (YK11.mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (YK11.mkst regs' (Z_to_bv 64 0x322a0) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp0 - 2272 - DEP_STK <= bv_unsigned x < sp0 - 2272) -> ~ DZONE (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
AFjb.DPOST3 W ly regs0 ch B S z mem').
Proof.
intros regs mem md R10 R11 R3 R4 R1 Rsp BUF PRES MEQ.
destruct Hsp as (SP1 & SP2 & SP3 & SP4). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (CST : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly)).
{ apply (Mp1.const_cells_real B ly S UP W mem0 md0 mem TS HARU HTSD).
  intros c k Hc Hk. pose proof (CZONE_untouched false _ (const_cells_zone c k Hc Hk)) as (Ra & N1 & _).
  apply MEQ. rewrite unsigned_lit_small by exact Ra. exact N1. }
assert (DEP : depot_mem_ok B ly S (aview tfibsegs (w_H W) mem)).
{ apply (depot_mem_ok_agree S (aview tfibsegs (w_H W) (FSP.unpoison UP mem0))).
  - pose proof (wf_depot _ _ _ _ _ (am_wf B ly S _ HARmu)) as [ND INC].
    pose proof (depot_ids_bound S _ (conj ND INC)). lia.
  - intros a Ha. pose proof (DZONE_disj false a Ha) as (N1 & _). pose proof blocks_facts as (NBhi & SBhi & _).
    assert (Ra : 0 <= a < 2 ^ 64)
      by (clear - Ha NBhi SBhi; unfold AFj6.DZONE in Ha; ceil;
          unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kNodesBlockSize, kStoreBlockSize in *; lia).
    rewrite (AllocR.aview_unpoison (w_H W) UP mem0 a (offU_dz a Ha)).
    apply aview_agree; [exact Ra|]. apply MEQ. rewrite unsigned_lit_small by exact Ra. exact N1.
  - exact depot_at0u. }
eapply SRr_mono.
{ apply (HD1 W ly S regs mem md (sp0 - IFRAME + 16) tr LY IMG (am_wf B ly S _ HARmu) Htr CST DEP R10 R11).
  - rewrite R3, Hgp. reflexivity.
  - exact R4.
  - rewrite R1. apply ret_ok_even. reflexivity.
  - exact BUF.
  - unfold IFRAME. apply Z.mod_divide; [zlia|]. pose proof SP4 as S4'. apply Z.mod_divide in S4' as [q Hq]; [|zlia]. exists (2 * q - 264). zlia.
  - unfold IFRAME, ASTACK in *. zlia.
  - unfold IFRAME, ASTACK in *. zlia.
  - right. rewrite Rsp. unfold IFRAME. zlia.
  - rewrite Rsp. apply Z.mod_divide; [zlia|]. pose proof SP4 as S4'. apply Z.mod_divide in S4' as [q Hq]; [|zlia]. exists (q - 142). zlia.
  - rewrite Rsp. unfold DEP_STK, ASTACK in *. zlia.
  - rewrite Rsp. zlia.
  - rewrite Rsp. intros a Ha. apply PRES. unfold DEP_STK, ASTACK in *. zlia. }
intros W' c' Hle (-> & z & regs' & mem' & mat & -> & AOK & RP & FR & PR' & DEP' & CST'). split; [reflexivity|].
exists z, regs', mem', mat. split; [rewrite R1; reflexivity|]. split; [exact RP|].
split; [|split; [exact PR'| exact (conj AOK (conj DEP' CST'))]].
intros x N1 N2. apply FR; [rewrite Rsp; exact N1|].
intros FP. apply N2. unfold depot_footprint, AFj6.DZONE in *.
rewrite (ts_depot B TS), (ts_store B TS) in FP. unfold TFIB_DEPOT, TFIB_STORE, d_map1 in FP. zlia.
Qed.

Lemma D1wU : forall (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
getr regs 10 = Z_to_bv 64 (sp0 - IFRAME + 16) -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = Z_to_bv 64 TFIB_TP -> getr regs 1 = Z_to_bv 64 0x322a0 ->
bv_unsigned (getr regs 2) = sp0 - 2272 ->
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem a) ->
(forall x : word, ~ WIN false (bv_unsigned x) -> mem x = mem0 x) ->
SRr tfibsegs W (mkCfg (YK11.mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (YK11.mkst regs' (Z_to_bv 64 0x322a0) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp0 - 2272 - DEP_STK <= bv_unsigned x < sp0 - 2272) -> ~ DZONE (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
DPOST z mem').
Proof.
intros regs mem md R10 R11 R3 R4 R1 Rsp BUF PRES MEQ.
eapply SRr_mono; [exact (D1W_okU regs mem md R10 R11 R3 R4 R1 Rsp BUF PRES MEQ)|].
intros W' c' _ (-> & z & regs' & mem' & mat & -> & RP & FR & PR & DP). split; [reflexivity|].
exists z, regs', mem', mat. repeat (split; [assumption || reflexivity|]). apply HDPOST'. exact DP.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 7. The walk after the join point, and the whole hit-g inner walk. Port-from: lib/A/AFjg.v:362 tail_inner and      *)
(*    AFjg.v:408 hitk_inner, text unchanged except that the leaf is LEAF_okU and the depot call is D1wU.             *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Local Abbreviation at_ST := (@AFj6.at_ST _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4).
Local Open Scope am_scope.
Local Abbreviation seg1J := (@AFj3.seg1J _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Hra4096 Hsp Hch DPOST Nrange Hcl_def mat0 U1 SEEDr l off).
Local Abbreviation segC2 := (@AFj3.segC2 _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Hn Hsp DPOST Nrange l off).
Local Abbreviation segD := (@AFj4.segD _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 LY Hsp DPOST l off D1wU).
Local Abbreviation seg2aK := (@AFj4.seg2aK _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HSKpres Nrange l off).
Local Abbreviation seg2b_even := (@AFj4.seg2b_even _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Hsp DPOST Nrange Hcl_def l off).
Local Abbreviation seg2c_even := (@AFj4.seg2c_even _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Htp Hra Hsp DPOST HKpres Nrange l off).
Local Abbreviation seg2b_odd := (@AFj5.seg2b_odd _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hsp DPOST HSKpres HPB250 Nrange Hcl_def l off).
Local Abbreviation seg2c_odd := (@AFj5.seg2c_odd _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Htp Hra Hsp DPOST HKpres HPB250 Nrange l off).
Local Abbreviation K0_facts := (@AFj6.K0_facts n Nrange).

Theorem tail_innerU : forall c1, at_ST KS_JN W c1 ->
amreal tfibsegs (malloc_join n tr cl S) W c1
(fun r W' c' => Wf (as_universe B) (snd r) /\ qtight (snd r) ->
   FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n r W' c').
Proof.
intros c1 HJ.
pose proof case0_sizes as (L & RS & R8 & NP & FP & NS & RQ). pose proof K0_facts as (_ & RF4 & NPr & _).
unfold malloc_join. rewrite bind_assoc_eq. eapply amreal_pure; [exact (pop_hit S cl l off Hcache)|]. eapply amreal_pure; [reflexivity|].
unfold malloc_K. cbv beta iota. change (AFi3.st_popped S cl l) with (AFjb.st_popped S cl l).
change {| ck_beg := PPrim (region_off cl + off); ck_req := n; ck_state := CAllocated |} with (AFjb.new_chunk cl off n).
replace (needs_remap (ck_n (AFjb.new_chunk cl off n))) with false.
2:{ symmetry. apply Z.leb_gt. unfold AFjb.new_chunk, ck_n. cbn [ck_req]. rewrite RQ. unfold kClearShadowMmapThreshold.
apply Z.div_lt_upper_bound; zlia. }
unfold depot_put. rewrite bind_assoc_eq. unfold bind at 1. unfold askz. cbn [ibind amreal].
eapply SRr_bind. { exact (segC2 W c1 HJ). }
intros W1 c1' Hle1 HPD.
eapply SRr_mono. { exact (segD W1 c1' HPD). }
intros W2 c2 Hle2 [z HPD2]. exists z.
split. { destruct HPD2 as (_ & ms2 & mat2 & E2 & regs2 & mem2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDP). exact (proj1 (HDPOST _ _ HDP)). }
assert (FIN : forall s', s' = depot_after z tr (AFjb.st_popped S cl l) ->
amreal tfibsegs ((ret () ;; modify (fun s : astate => set_chunks (upd_chunk (st_chunks s) (AFjb.new_chunk cl off n)) s) ;;
ret (ck_user (AFjb.new_chunk cl off n))) s') W2 c2
(fun r W' c' => Wf (as_universe B) (snd r) /\ qtight (snd r) ->
   FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n r W' c')).
{ intros s' ->. eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|]. cbn [amreal ret].
change (set_chunks (upd_chunk (st_chunks (depot_after z tr (AFjb.st_popped S cl l))) (AFjb.new_chunk cl off n)) (depot_after z tr (AFjb.st_popped S cl l)))
with (AFjb.st_final S cl l off n tr z).
destruct (Z.eq_dec (NPv mod 8) 0) as [H8|H8].
- eapply SRr_bind; [exact (seg2aK z W2 c2 HPD2)|]. intros W3 c3 _ H3.
eapply SRr_bind; [exact (seg2b_even H8 z W3 c3 H3)|]. intros W4 c4 _ H4.
eapply SRr_mono; [exact (seg2c_even H8 z W4 c4 H4)|]. intros W' c' _ HR MP.
exact (LEAF_okU false z W' c' HR ltac:(split; [intros E; discriminate E | intros X; exfalso; exact (X H8)]) MP).
- eapply SRr_bind; [exact (seg2aK z W2 c2 HPD2)|]. intros W3 c3 _ H3.
eapply SRr_bind; [exact (seg2b_odd H8 z W3 c3 H3)|]. intros W4 c4 _ H4.
eapply SRr_mono; [exact (seg2c_odd H8 z W4 c4 H4)|]. intros W' c' _ HR MP.
exact (LEAF_okU true z W' c' HR ltac:(split; [intros _; exact H8 | intros _; reflexivity]) MP). }
destruct (z =? 0) eqn:Ez.
- eapply amreal_pure; [reflexivity|]. apply FIN. unfold depot_after. rewrite Ez. reflexivity.
- rewrite bind_assoc_eq. eapply amreal_pure; [reflexivity|].
rewrite bind_assoc_eq. unfold mcheck at 1.
destruct (depot_ids (AFjb.st_popped S cl l) + 1 <? kDepotIdsPerBlock); [| unfold bind at 1; unfold fail; cbn [ibind amreal]; exact I].
eapply amreal_pure; [reflexivity|].
rewrite bind_assoc_eq. unfold mcheck at 1.
destruct (kStartFramesMax + depot_frames (AFjb.st_popped S cl l) + Z.of_nat (length tr) + 1 <? kStoreFramesPerBlock);
[| unfold bind at 1; unfold fail; cbn [ibind amreal]; exact I].
eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|].
apply FIN. unfold depot_after. rewrite Ez. reflexivity.
Qed.

Theorem hitk_innerU : amreal tfibsegs (malloc_join n tr cl S) W (cfg_at tfibsegs 0x53074 regs0 mem0 md0)
(fun r W' c' => Wf (as_universe B) (snd r) /\ qtight (snd r) ->
   FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n r W' c').
Proof.
eapply amreal_SRr_pre.
{ replace (cfg_at tfibsegs 0x53074 regs0 mem0 md0)
    with (mkCfg (YK11.mkst regs0 (w64 0x53074) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
    by (unfold cfg_at; rewrite Hmat0, with_vm_backing_id; reflexivity).
  exact seg1J. }
intros W1 c1 _ HJ. pose proof (proj1 HJ) as EW. subst W1. exact (tail_innerU c1 HJ).
Qed.
End e.
End d.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 8. malloc_hitk for any UP. Port-from: lib/A/AFik.v:46; the facts the donor reads off ARm are read off ARm of the   *)
(*    unpoisoned reading and moved to the real memory (the thread object and the cached chunk are off UP, and the    *)
(*    chunk's shadow holds 250 there, so it is off UP too).                                                          *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section b.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Hypothesis U1 : tfib_unwind_spec.
Hypothesis D1 : tfib_depot_spec B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (ch : list (Z * Z * Z)).
Variable UP : list (Z * Z).
Let tr : list Z := call_trace ly 0x53314 regs0 ch.
Hypothesis PRE : FSU.acall_preU tfibsegs B ly S UP W regs0 mem0 md0 ch.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Nrange0 : 0 <= n <= 48.
Hypothesis Htr : tr_admit (as_universe B) S tr.
Hypothesis Hlive : blocks_bytes S + n <= LIVE_MAX.
Variables (l : list Z) (off : Z).
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S (chunk_class n)) = l ++ [off].

Theorem malloc_hitkU :
amreal tfibsegs (malloc n tr S) W (cfg_at tfibsegs 0x53074 regs0 mem0 md0)
  (FSU.malloc_leafU tfibsegs B ly S UP W regs0 mem0 md0 n).
Proof.
pose proof (AllocR.ARU_of_acall_preU B ly S UP W regs0 mem0 md0 ch PRE) as HARU0.
destruct PRE as ((HAR0 & Hev & Hra & Hal & Hlo & Hbot & Hhi & Hpres0u & Hgp & Htp & CH & HQT) & HOK & HPO).
pose proof (proj1 HAR0) as HARm0. unfold spZ in *.
set (S1 := set_nev (st_nev S + 1) S).
pose proof (ARm_tick B ly S _ HARm0 Hev) as HARm. fold S1 in HARm.
pose proof (AR_tick B ly S W (FSP.unpoison UP mem0) md0 HAR0 Hev) as HAR1. fold S1 in HAR1.
pose proof (AllocR.ARU_tick B ly S UP W mem0 md0 HARU0 Hev) as HARU1. fold S1 in HARU1.
assert (Hinited1 : st_cache_inited S1 = true) by exact Hinited.
assert (Hcache1 : pc_chunks (cache S1 (chunk_class n)) = l ++ [off]) by exact Hcache.
(* qmeter is not needed by the inner walk; the leaf's qtight comes from MPF. *)
assert (LY : layout_ok ly) by exact (am_layout _ _ _ _ HARm).
assert (IMG : img_cover ly) by exact (img_cover_of_ledger ly S1 md0 (proj1 (proj2 HAR1))).
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd _ _ _ _ HARm); exact (ts_tsd B TS)).
rewrite (ts_tp B TS) in Htp.
pose proof (AllocR.chain_pre_real B ly S UP W regs0 mem0 md0 ch HARU0 ltac:(unfold spZ, ASTACK in *; lia) CH) as CHr.
destruct CHr as [Hra4096 Hch]. unfold raZ in Hra4096. unfold frame0_ok, spZ, s0Z in Hch.
set (sp0 := bv_unsigned (getr regs0 2)) in *.
assert (Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0)
  by (repeat split; assumption).
assert (Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a).
{ apply (AllocR.stack_present_real B ly S UP W mem0 md0 (sp0 - ASTACK) sp0 HARU0);
  [unfold ASTACK in *; lia | lia | exact Hpres0u]. }
assert (Nrange : 0 <= n <= 48) by exact Nrange0.
set (cl := chunk_class n) in *. set (cnt := Z.of_nat (length (l ++ [off]))). set (v := off / 16). set (csz := class_size cl).
set (DPOST := fun z m => AFjb.DPOST3 W ly regs0 ch B S1 z m).
assert (Hcl_class : cl = chunk_class n) by reflexivity.
assert (Hcnt_def : cnt = Z.of_nat (length (l ++ [off]))) by reflexivity.
assert (Hcsz_def : csz = class_size cl) by reflexivity.
assert (Hcl : 1 <= cl <= 31) by exact (@AFjc.Hcl' ly regs0 (FSP.unpoison UP mem0) n cl v DPOST Nrange l off Hcl_class).
assert (Hoffv : off = 16 * v /\ v mod 2 = 0).
{ pose proof (wf_classes _ _ _ _ _ (am_wf _ _ _ _ HARm) cl Hcl) as CL. pose proof (wr_elems _ _ _ _ _ _ CL) as EL. rewrite Hcache1 in EL.
pose proof (proj1 (Forall_forall _ _) EL off ltac:(rewrite !in_app_iff; cbn; tauto)) as [_ O2].
pose proof (class_ok cl Hcl) as (K1 & K2 & _). apply Z.mod_divide in O2 as [q Hq]; [|lia]. apply Z.mod_divide in K2 as [r Hr]; [|lia].
subst v. rewrite Hq, Hr. replace (q * (r * 32)) with ((2 * q * r) * 16) by lia. rewrite Z.div_mul by lia. split; [lia|].
rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. }
destruct Hoffv as [Hoff_def Hv2].
assert (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32)
by exact (@AFjc.Hv' _ W ly regs0 (FSP.unpoison UP mem0) n cl cnt v Hv2 DPOST Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def).
assert (Hcnt : 1 <= cnt <= 16)
by exact (@AFjc.Hcnt' _ W ly regs0 (FSP.unpoison UP mem0) n cl cnt v Hv2 Hsp DPOST Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def).
pose proof (@AFj6.derived_ranges _ ly regs0 mem0 n cl cnt v Hcl Hv Hcnt Hv2 LY IMG DPOST Nrange) as DR.
pose proof (@AFj6.high_facts _ ly regs0 mem0 n v Hv LY IMG DPOST) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
pose proof (@AFjc.cls_geom ly regs0 (FSP.unpoison UP mem0) n cl v DPOST Nrange l off Hcl_class) as (C1 & _ & C3 & _ & C5 & C6).
pose proof (Z.div_mod (AFj6.Kv ly cl v) 16 ltac:(lia)) as DK.
assert (OT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> AllocR.offU UP a).
{ intros a Ha. apply (Mp1.offU_owned B ly S1 UP W mem0 md0 (ly_T ly, kThreadObjSize) a HARU1
    ltac:(unfold owned_extents; cbn [In]; tauto)). cbn [fst snd]. exact Ha. }
assert (OKv : forall a, AFj6.Kv ly cl v <= a < AFj6.Kv ly cl v + csz -> AllocR.offU UP a).
{ intros a Ha. apply (Mp1.offU_hi B ly S1 UP W mem0 md0 a HARU1).
  ceil. unfold kHighMemBeg, ASAN_CEIL, kMaxSize in *. rewrite Hcsz_def in Ha. lia. }
assert (OKS : forall g, g mod 8 = 0 -> AFj6.Kv ly cl v <= g < AFj6.Kv ly cl v + csz -> AllocR.offU UP (shadow_addr g)).
{ intros g G8 Hg. apply (AllocR.offU_nonzero B ly S1 UP W mem0 md0 (shadow_addr g) 250 HARU1).
  - unfold shadow_addr. ceil.
    pose proof (Z.div_pos g 8 ltac:(unfold kHighMemBeg in *; lia) ltac:(lia)) as D1'.
    pose proof (Z.div_le_upper_bound g 8 (2 ^ 44) ltac:(lia) ltac:(unfold ASAN_CEIL, kMaxSize in *; rewrite Hcsz_def in Hg; lia)) as D2'.
    unfold SHADOW_OFF. lia.
  - exact (@AFjc.shadow250 _ W ly regs0 (FSP.unpoison UP mem0) n cl cnt v csz Hv2 LY Hsp DPOST Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def g G8 ltac:(rewrite <- Hcsz_def; exact Hg)).
  - lia.
  - lia. }
assert (SHK : forall j, shadow_addr (AFj6.Kv ly cl v + 8 * j) = AFj6.SKv ly cl v + j).
{ intros j. unfold shadow_addr, AFj6.SKv, AFj6.SHBv, SHADOW_OFF.
  replace (AFj6.Kv ly cl v + 8 * j) with ((AFj6.Kv ly cl v / 16 * 2 + j) * 8) by lia.
  replace (AFj6.Kv ly cl v) with (AFj6.Kv ly cl v / 16 * 2 * 8) at 2 by lia.
  rewrite !Z.div_mul by lia. lia. }
destruct (@AFjc.junk_values _ W ly regs0 (FSP.unpoison UP mem0) n cl cnt v csz Hv2 LY IMG Hsp DPOST Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def)
as (j0 & j1 & j2 & j3 & j4 & jb & Hj0u & Hj1u & Hj2u & Hj3u & Hj4u & Hjb & Hjbu).
assert (Hj0 : val_mem tfibsegs (mrestrict (w_H W) mem0) (ly_T ly + 2784) 8 j0)
  by (apply (AllocR.val_mem_of_unpoison (w_H W) UP mem0 (ly_T ly + 2784) 8 j0); [intros k Hk; apply OT; unfold kThreadObjSize; lia | exact Hj0u]).
assert (Hj1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (ly_T ly + 2800) 8 j1)
  by (apply (AllocR.val_mem_of_unpoison (w_H W) UP mem0 (ly_T ly + 2800) 8 j1); [intros k Hk; apply OT; unfold kThreadObjSize; lia | exact Hj1u]).
assert (Hj2 : val_mem tfibsegs (mrestrict (w_H W) mem0) (ly_T ly + 2808) 8 j2)
  by (apply (AllocR.val_mem_of_unpoison (w_H W) UP mem0 (ly_T ly + 2808) 8 j2); [intros k Hk; apply OT; unfold kThreadObjSize; lia | exact Hj2u]).
assert (Hj3 : val_mem tfibsegs (mrestrict (w_H W) mem0) (ly_T ly + 2816) 8 j3)
  by (apply (AllocR.val_mem_of_unpoison (w_H W) UP mem0 (ly_T ly + 2816) 8 j3); [intros k Hk; apply OT; unfold kThreadObjSize; lia | exact Hj3u]).
assert (Hj4 : val_mem tfibsegs (mrestrict (w_H W) mem0) (AFj6.SSLOTv ly cl) 8 j4)
  by (apply (AllocR.val_mem_of_unpoison (w_H W) UP mem0 (AFj6.SSLOTv ly cl) 8 j4);
      [intros k Hk; apply OT; unfold kThreadObjSize, t_unwinding in *; lia | exact Hj4u]).
assert (Hjb_def : val_mem tfibsegs (mrestrict (w_H W) mem0) (AFj6.Kv ly cl v + AFj6.RZ - 15) 1 jb)
  by (apply (AllocR.val_mem_of_unpoison (w_H W) UP mem0 (AFj6.Kv ly cl v + AFj6.RZ - 15) 1 jb);
      [intros k Hk; apply OKv; rewrite Hcsz_def; lia | exact Hjbu]).
assert (HKpres : forall a, AFj6.Kv ly cl v <= a < AFj6.Kv ly cl v + AFj6.RZ + AFj6.R8v n -> apresent (w_H W) mem0 a).
{ intros a Ha. apply (AllocR.apresent_of_unpoison (w_H W) UP mem0 a ltac:(apply OKv; rewrite Hcsz_def; lia)).
  exact (@AFjc.KPRES _ W ly regs0 (FSP.unpoison UP mem0) n cl cnt v csz Hv2 LY Hsp DPOST Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def a Ha). }
assert (HSKpres : forall a, AFj6.SKv ly cl v <= a < AFj6.SKv ly cl v + (AFj6.RZ + AFj6.R8v n) / 8 -> apresent (w_H W) mem0 a).
{ intros a Ha. apply (AllocR.apresent_of_unpoison (w_H W) UP mem0 a
    ltac:(replace a with (shadow_addr (AFj6.Kv ly cl v + 8 * (a - AFj6.SKv ly cl v))) by (rewrite SHK; lia);
          apply OKS; [replace (AFj6.Kv ly cl v + 8 * (a - AFj6.SKv ly cl v)) with ((AFj6.Kv ly cl v / 16 * 2 + (a - AFj6.SKv ly cl v)) * 8) by lia; apply Z.mod_mul; lia
                     | rewrite Hcsz_def; pose proof (Z.mul_div_le (AFj6.RZ + AFj6.R8v n) 8 ltac:(lia)); lia])).
  exact (@AFjc.SKPRES _ W ly regs0 (FSP.unpoison UP mem0) n cl cnt v csz Hv2 LY IMG Hsp DPOST Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def a Ha). }
assert (HPB250 : AFj6.NPv n mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W) mem0) (AFj6.PBv ly n cl v) 1 250).
{ intros E8. apply (AllocR.val_mem_of_unpoison (w_H W) UP mem0 (AFj6.PBv ly n cl v) 1 250).
  - intros k Hk. replace (AFj6.PBv ly n cl v + Z.of_nat k) with (shadow_addr (AFj6.Kv ly cl v + AFj6.RZ + AFj6.N8D n)).
    2:{ replace (Z.of_nat k) with 0 by lia. rewrite Z.add_0_r.
        unfold shadow_addr, AFj6.PBv, AFj6.SHBv, SHADOW_OFF. reflexivity. }
    apply OKS.
    + unfold AFj6.N8D. pose proof (Z.div_mod (AFj6.NPv n) 8 ltac:(lia)).
      replace (AFj6.Kv ly cl v + AFj6.RZ + AFj6.NPv n / 8 * 8) with ((AFj6.Kv ly cl v / 16 * 2 + AFj6.RZ / 8 + AFj6.NPv n / 8) * 8) by lia.
      apply Z.mod_mul. lia.
    + rewrite Hcsz_def. unfold AFj6.N8D in *. pose proof (Z.div_mod (AFj6.NPv n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (AFj6.NPv n) 8 ltac:(lia)). lia.
  - exact (@AFjc.PB250 _ W ly regs0 (FSP.unpoison UP mem0) n cl cnt v csz Hv2 LY IMG Hsp DPOST Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def E8). }
pose proof (@AFj6.case0_sizes n Nrange) as (L & RS & R8 & NP & FP & NS & RQ).
assert (Hcl_def : cl = class_id (AFj6.R8v n + AFj6.RZ)) by (subst cl; unfold chunk_class; rewrite NS, <- RS; reflexivity).
eapply (amreal_atok _ true (malloc_post (as_universe B) S n)).
{ apply (malloc_ok (as_universe B) S n tr (ts_universe B TS) (am_wf _ _ _ _ HARm0) Hev); [unfold MALLOC_MAX; lia | exact Hlive | exact Htr]. }
rewrite (malloc_primary_eq n tr S FP). eapply amreal_pure; [reflexivity|].
eapply amreal_pure; [unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage; lia); reflexivity|].
fold S1. rewrite <- Hcl_class.
eapply amreal_pure; [apply refill_tree_ready; [exact Hinited1 | rewrite Hcache1; destruct l; discriminate]|].
eapply amreal_mono;
  [| exact (hitk_innerU W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 B S1 l off UP DPOST
     Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Htp Hsp HKpres HSKpres HPB250 Nrange Hcl_def TS HTSD HARU1 Hpres0
     Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def
     (m_vm_materialized md0) Hra Hra4096 Hch U1 Hgp (tr_admit_len _ _ _ (ts_universe B TS) Htr) D1 (fun z m H => H) (fun z m H => H) eq_refl)].
intros [p s'] W' c' H [ns MP]. cbn [fst snd] in H, MP. destruct MP as (WF' & _ & _ & _ & _ & QT).
exact (H (conj WF' (QT (qmeter_tight _ HQT)))).
Qed.
End b.
End a.
