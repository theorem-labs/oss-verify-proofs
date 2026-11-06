(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGikE.v (a working branch 5ad50e61fc6a, file sha256 c03df2669bb1) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53); module paths changed; its 3 image addresses moved by code-verified function pairs (3 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py); no other numeral changed. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The hit-g arm of AGik.v with errno kept: [ARM_HITG_e] is AGik.ARM_HITG with ErrnoG.alloc_leaf_e (AllocG.alloc_leaf
   plus errno's 4 bytes unchanged on the grant branch) in place of AllocG.alloc_leaf.

   The hit path never writes errno.  at_RETw's raw frame MEQF (AGif0n.v:89-91) keeps every byte outside
   ImgBaseAG.WIN, ag_dzone, the new block and its shadow; ErrnoApart puts errno outside each of them
   (errno_apart_win_g, the image fact errno_apart_dzone_ag, errno_apart_blk_g, errno_apart_shd_g).
   [errno_kept_at_RETw] states that once, over MEQF's own form.  ARM_HITG's MEQF is local to its proof and amreal has
   no conjunction rule, so ARM_HITG_e repeats ARM_HITG's proof (the block marked as a copy) and adds the errno
   conjunct from the same MEQF.  AGik.v is unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG07 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0h.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YB1w YE3d YFhy.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGhy.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGis AGhz.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFi3 AllocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif0cgif AGiz AGj0 AGj2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG ErrnoApart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGik.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* errno is kept by a memory that equals [mem] outside at_RETw's raw frame zones (AGif0n.v:89-91, the clause in the
   form at_RETw states it): ImgBaseAG.WIN, ag_dzone, the new block [Kv + RZ kz, + n) and its shadow. *)
Lemma errno_kept_at_RETw :
ErrnoApart.errno_in_img (IM := AImg_cgif) -> ErrnoApart.errno_apart_shadow_ag (AG := AGImg_cgif) ->
ErrnoApart.errno_apart_dzone_ag (AG := AGImg_cgif) ->
forall B ly (regs0 : bvmap 5 word) n cl v kz odd (mem mem' : word -> option byte),
TfibSyms B -> layout_ok ly -> ImgBase.im_img_cover ly ->
ly_stk_lo ly + ImgBaseAG.AFSTACK <= bv_unsigned (getr regs0 2) -> 0 <= cl < kNumClasses -> 0 <= v -> 0 <= n ->
(forall x : word, ~ ImgBaseAG.WIN ly regs0 n cl v kz odd (bv_unsigned x) -> ~ ImgBaseAG.ag_dzone ly (bv_unsigned x) ->
 ~ (ImgBaseAG.Kv ly cl v + ImgBaseAG.RZ kz <= bv_unsigned x < ImgBaseAG.Kv ly cl v + ImgBaseAG.RZ kz + n) ->
 ~ (ImgBaseAG.SUv ly cl v kz <= bv_unsigned x < ImgBaseAG.SUv ly cl v kz + ImgBaseAG.N8D n / 8) -> mem' x = mem x) ->
ErrnoG.errno_kept B mem mem'.
Proof.
intros Hei Hesh Hedz B ly regs0 n cl v kz odd mem mem' TS LY IMG HSP Hcl Hv Hn MEQ. unfold ErrnoG.errno_kept. intros i Hi.
pose proof (ts_errno B TS) as EE. unfold TFIB_ERRNO in EE.
assert (Ra : 0 <= as_errno B + i < 2 ^ 64) by lia.
assert (Hae : as_errno B <= as_errno B + i < as_errno B + 4) by lia.
assert (HaU : bv_unsigned (w64 (as_errno B + i)) = as_errno B + i) by (apply w64_unsigned; exact Ra).
pose proof (MEQ (w64 (as_errno B + i))) as ME. rewrite HaU in ME. apply ME.
- intros Hw. exact (ErrnoApart.errno_apart_win_g Hei Hesh B ly regs0 n cl v kz odd _ TS LY IMG HSP Hcl Hv Hn Hw Hae).
- intros Hd. exact (Hedz B ly _ TS LY IMG Hd Hae).
- intros Hb. exact (ErrnoApart.errno_apart_blk_g Hei B ly n cl v kz _ TS LY IMG (proj1 Hcl) Hv Hb Hae).
- intros Hs. exact (ErrnoApart.errno_apart_shd_g Hesh B ly n cl v kz _ TS LY (proj1 Hcl) Hv Hs Hae).
Qed.

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
(* copy of AGik.v:53 *)
Local Ltac bvne := first [cbn; lia | vm_compute; congruence | intros X; vm_compute in X; discriminate X].
(* can_fill of the caller's call site: 1 (malloc, realloc) or 0 (calloc). *)
Variable cf : Z.
Hypothesis Hcf01 : cf = 0 \/ cf = 1.
(* The image facts errno_kept_at_RETw reads (cgif_file: ErrnoApartcgif.v). *)
Hypothesis Hei : ErrnoApart.errno_in_img (IM := AImg_cgif).
Hypothesis Hesh : ErrnoApart.errno_apart_shadow_ag (AG := AGImg_cgif).
Hypothesis Hedz : ErrnoApart.errno_apart_dzone_ag (AG := AGImg_cgif).
Theorem ARM_HITG_e : forall inst so bp ly S W regs mem md n tr l off,
alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 cf inst so bp ly S W regs mem md n tr ->
49 <= n <= 64512 -> st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(ErrnoG.alloc_leaf_e tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Proof.
(* copy of AGik.v:90-275, + errno *)
intros inst so bp ly S W regs mem md n tr l off PRE Nrange0 Hinited Hcache.
destruct IF as [Finst Fview Fshape Fdepot Fdaok Fpost Fowned Funinit].
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres0 & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hn0 & Hlive).
unfold spZ, raZ, AFSTACK_G in *. rewrite (ts_tp B TS) in Htp.
pose proof (Finst _ _ _ _ _ _ HARX) as HIO. pose proof HIO as (HIO1 & HIO2 & HIO3).
(* The class and the redzone log. *)
set (kz := rz_log n).
assert (Hkz : 1 <= kz <= 6 /\ rz_lo kz <= n <= rz_hi kz).
{ subst kz. unfold rz_log. clear - Nrange0.
destruct (Z.leb_spec n 48); [lia|]. destruct (Z.leb_spec n 96); [cbn; lia|]. destruct (Z.leb_spec n 448); [cbn; lia|].
destruct (Z.leb_spec n 3968); [cbn; lia|]. destruct (Z.leb_spec n 16128); [cbn; lia|]. destruct (Z.leb_spec n 32256); [cbn; lia|].
destruct (Z.leb_spec n 64512); [cbn; lia|]. lia. }
destruct Hkz as [Hkz Nrange].
pose proof (AGis.casek_sizes n kz Hkz Nrange) as (L & RS & R8 & NP & FP & NS & RQ).
destruct (Fview inst ly S W mem md n l off HARX HRP ltac:(lia) FP Hinited Hcache) as (Hoff32 & HV).
apply hview_cgif in HV.
set (cl := chunk_class n) in *. set (cnt := Z.of_nat (length (l ++ [off]))) in *. set (v := off / 16) in *. set (csz := class_size cl).
assert (Hcl_class : cl = chunk_class n) by reflexivity.
assert (Hcnt_def : cnt = Z.of_nat (length (l ++ [off]))) by reflexivity.
assert (Hcsz_def : csz = class_size cl) by reflexivity.
assert (Hoff_def : off = 16 * v).
{ subst v. pose proof Hoff32 as H32. apply Z.mod_divide in H32 as [q Hq]; [|lia]. rewrite Hq.
  replace (q * 32) with ((2 * q) * 16) by lia. rewrite Z.div_mul by lia. lia. }
pose proof HV as [HLY HIMG HTSD Hcnt Hvv Hconst Hinstc Hcachec Hunw Hjunk Hchunk Hshadow].
destruct Hvv as (Hv0 & Hv2 & Hvcl).
assert (Hcl_def : cl = class_id (R8v n + AGis.RZ kz)) by (subst cl; unfold chunk_class; rewrite NS, <- RS; reflexivity).
(* The view's consequences (AGiz). *)
assert (Hcl : 1 <= cl <= 31) by (assert (1 <= cl <= 30) by (eapply vw_cl_range; eassumption); lia).
assert (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32) by (eapply vw_Hv; eassumption).
assert (HKpres : forall a, Kv ly cl v <= a < Kv ly cl v + AGis.RZ kz + R8v n -> apresent (w_H W) mem a) by (eapply vw_KPRES; eassumption).
assert (HSKpres : forall a, SKv ly cl v <= a < SKv ly cl v + (AGis.RZ kz + R8v n) / 8 -> apresent (w_H W) mem a) by (eapply vw_SKPRES; eassumption).
assert (HPB250 : n mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W) mem) (PBv ly n cl v kz) 1 250) by (eapply vw_PB250; eassumption).
assert (JV : exists j0 j1 j2 j3 j4 jb,
val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + 2784) 8 j0 /\ val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + 2800) 8 j1 /\
val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + 2808) 8 j2 /\ val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + 2816) 8 j3 /\
val_mem tfibsegs (mrestrict (w_H W) mem) (SSLOTv ly cl) 8 j4 /\ 0 <= jb <= 255 /\
val_mem tfibsegs (mrestrict (w_H W) mem) (Kv ly cl v + AGis.RZ kz - 15) 1 jb) by (eapply vw_junk_values; eassumption).
destruct JV as (j0 & j1 & j2 & j3 & j4 & jb & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hjb & Hjb_def).
(* The walk's virtual register file. *)
set (regs0 := vregs regs n inst bp).
pose proof (lo_top ly HLY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
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
assert (Hcf : getr regs0 15 = w64 0 \/ getr regs0 15 = w64 1)
by (unfold regs0; rewrite (vregs_other regs n inst bp 15%bv) by bvne; rewrite Hr15; destruct Hcf01 as [E|E]; rewrite E; [left | right]; reflexivity).
assert (Hra0 : YK0s.ret_ok (getr regs0 1)) by (rewrite R1; exact Hra).
assert (Hra40 : 4096 <= bv_unsigned (getr regs0 1)) by (rewrite R1; exact Hra4096).
assert (Hsp : ly_stk_lo ly + AFSTACK <= bv_unsigned (getr regs0 2) /\ ly_bot ly < bv_unsigned (getr regs0 2) /\
bv_unsigned (getr regs0 2) <= ly_stk_hi ly /\ bv_unsigned (getr regs0 2) mod 16 = 0) by (rewrite R2; unfold AFSTACK; repeat split; assumption).
assert (Hso : bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 13) /\ bv_unsigned (getr regs0 13) + 16 <= ly_stk_hi ly /\
bv_unsigned (getr regs0 13) mod 8 = 0) by (rewrite R2, R13; repeat split; assumption).
assert (Hbp : bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 12) /\ bv_unsigned (getr regs0 12) + 8 * 30 <= ly_stk_hi ly /\
bv_unsigned (getr regs0 12) mod 8 = 0) by (rewrite R2, R12; repeat split; assumption).
assert (Hinst : TFIB_IMG_LO <= bv_unsigned (getr regs0 11) /\ bv_unsigned (getr regs0 11) + 0xe60 <= 0x17d5c8)
by (rewrite Hi11, w64_unsigned by exact Hinst64; exact (inst_ok_img inst HIO)).
assert (Hpres00 : forall a, bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W) mem a)
by (rewrite R2; unfold AFSTACK; exact Hpres0).
assert (PSO0 : val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 13)) 8 (bv_unsigned (getr regs0 12))) by (rewrite R13, R12; exact PSO).
assert (PLEN0 : val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 13) + 8) 8 (Z.of_nat (length tr))) by (rewrite R13; exact PLEN).
assert (PBUF0 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 12) + 8 * Z.of_nat i) 8 (nth i tr 0))
by (rewrite R12; exact PBUF).
(* The seed at Allocate's entry (AGj0). *)
assert (SEED : st_ok tfibsegs (AGis.E0 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz) SS_1
(restrict (w_H W) (mkst regs (w64 A_Allocate) mem (seg_rom tfibsegs)))).
{ exact (@SEED_ok _ _ W ly regs0 mem n tr cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 HLY HIMG Hn Htp0 Hsp Htrlen Hso Hbp Hcf
  (fun (_ : Z) (_ : word -> option byte) => True) Hkz Nrange B inst TS HV Hi11 HIO PSO0 PLEN0 Hpres00 Hcl_class Hcsz_def
  Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def regs HUo HU10 HU11 HU12 HU14). }
(* The model state at the pop: the tick. *)
set (S1 := set_nev (st_nev S + 1) S).
assert (Hcache1 : pc_chunks (cache S1 cl) = l ++ [off]) by exact Hcache.
(* The depot callee, at this allocator. *)
assert (HDEP : forall (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) (buf : Z),
(forall x : word, DZONE ly (bv_unsigned x) \/ CZONE ly (bv_unsigned x) -> mem1 x = mem x) ->
getr regs1 10 = Z_to_bv 64 buf -> getr regs1 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs1 3 = Z_to_bv 64 (as_gp B) -> getr regs1 4 = Z_to_bv 64 TFIB_TP -> YK0s.ret_ok (getr regs1 1) ->
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem1) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
buf + 8 * 30 <= bv_unsigned (getr regs1 2) - DEP_STK \/ bv_unsigned (getr regs1 2) <= buf ->
bv_unsigned (getr regs1 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs1 2) - DEP_STK ->
bv_unsigned (getr regs1 2) <= ly_stk_hi ly ->
(forall a, bv_unsigned (getr regs1 2) - DEP_STK <= a < bv_unsigned (getr regs1 2) -> apresent (w_H W) mem1 a) ->
SRr tfibsegs W (mkCfg (mkst regs1 (Z_to_bv 64 A_StackDepotPut) mem1 (seg_rom tfibsegs)) md1)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs1 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md1) mat md1) /\
regs_preserved regs1 regs' /\
(forall x : word, ~ (bv_unsigned (getr regs1 2) - DEP_STK <= bv_unsigned x < bv_unsigned (getr regs1 2)) ->
~ DZONE ly (bv_unsigned x) -> mem' x = mem1 x) /\
(forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem' a) /\
dpost inst ly S W tr z mem')).
{ intros regs1 mem1 md1 buf. exact (Fdepot inst ly S W mem md tr regs1 mem1 md1 buf HARX Htr). }
assert (HDAOK : forall z m, dpost inst ly S W tr z m -> aok S1 (KDepot tr) z) by (intros z m H; exact (Fdaok _ _ _ _ _ _ _ H)).
assert (Hmat0 : m_vm_materialized md = m_vm_materialized md) by reflexivity.
(* The walk (AGj2). *)
assert (MAIN : amreal tfibsegs (malloc_join_t stag n tr cl S1) W (cfg_at tfibsegs A_Allocate regs mem md)
(fun r W' c' => exists odd z, r = (ck_user (new_chunk cl off n), st_final S1 cl l off n tr z) /\
(odd = true <-> n mod 8 <> 0) /\
at_RETw W ly regs0 mem md n cl cnt v jb kz (fun z m => dpost inst ly S W tr z m) odd z W' c')).
{ eapply hitg_inner; try first [exact SEED | exact HDEP | exact HDAOK | exact Hmat0 | eassumption].
  Unshelve. all: try first [exact (m_vm_materialized md) | exact B]. }
(* The model's steps before the pop (shape (b)). *)
assert (MAIN' : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(fun r W' c' => exists odd z, r = (ck_user (new_chunk cl off n), st_final S1 cl l off n tr z) /\
(odd = true <-> n mod 8 <> 0) /\
at_RETw W ly regs0 mem md n cl cnt v jb kz (fun z m => dpost inst ly S W tr z m) odd z W' c')).
{ rewrite (Fshape n tr S l off ltac:(lia) FP Hinited Hcache).
  eapply amreal_pure; [reflexivity|].
  eapply amreal_pure; [unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage; lia); reflexivity|].
  exact MAIN. }
(* The leaf. *)
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs _ _ _ _ MAIN')].
intros r W' c' [(odd & z & -> & Hodd & HR) HPATH].
pose proof HR as HR0.
destruct HR as (-> & regs' & mem' & mat & -> & R10 & RCS & (memD & DP & PRD & EQD) & MEQF & PRS & PRW & VALS).
assert (WF : wframe W ly regs0 mem tr) by (split; [exact Hsp|]; split; [exact Htrlen|]; split; [exact Hso|]; split; [exact Hbp | exact Hpres00]).
destruct (Fpost inst ly S W mem md n tr l off regs0 jb odd z regs' mem' mat HARX HRP ltac:(lia) Hlive Htr Nrange0 Hinited Hcache WF Hjb Hjb_def
  HR0 Hodd HPATH)
as [HARX' HLP].
assert (KU : sptr_addr B ly (ck_user (new_chunk cl off n)) = Kv ly cl v + AGis.RZ kz).
{ unfold new_chunk, ck_user, ck_rz. cbn [ck_beg ck_req padd]. rewrite RS.
  rewrite (AGis.Kv_is_sptr ly cl v Hcl B off Hoff_def). unfold sptr_addr. cbn. lia. }
(* The raw frame (at_RETw's raw MEQF); the aview frame follows from it. *)
assert (RAWF : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ ascratch B AFSTACK_G regs (bv_unsigned x) ->
  ~ (Kv ly cl v + AGis.RZ kz <= bv_unsigned x < Kv ly cl v + AGis.RZ kz + n) -> mem' x = mem x).
{ intros x NO NSc NE. pose proof (u64_range x) as Ra.
  assert (OWN : hit_writes ly n cl v kz odd (bv_unsigned x) -> False).
  { intros HW. apply NO. exact (Fowned inst ly S W mem md n l off odd (bv_unsigned x) HARX HRP Nrange0 Hinited Hcache Ra (proj1 Hodd) HW). }
  apply MEQF.
  - intros Hw. unfold ImgBaseAG.WIN in Hw. destruct Hw as [Hs|Hw].
    + apply NSc. unfold ascratch. left. unfold spZ, AFSTACK_G. rewrite <- R2. unfold ImgBaseAG.AFSTACK in Hs. exact Hs.
    + apply OWN. unfold hit_writes. destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw | right; left; exact Hw | right; right; left; exact Hw].
  - intros Hd. apply OWN. unfold hit_writes. right; right; right; left; exact Hd.
  - exact NE.
  - intros Hs. apply OWN. unfold hit_writes. right; right; right; right; exact Hs. }
(* errno: the same raw MEQF keeps it (errno_kept_at_RETw). *)
assert (ERRNO : ErrnoG.errno_kept B mem mem').
{ refine (errno_kept_at_RETw Hei Hesh Hedz B ly regs0 n cl v kz odd mem mem' TS HLY HIMG (proj1 Hsp) _ (proj1 Hv) _ MEQF).
  - clear - Hcl. unfold kNumClasses. lia.
  - clear - Nrange0. lia. }
assert (NEu : forall a, ~ (fst (ck_user (new_chunk cl off n), st_final S1 cl l off n tr z) <> PNull /\
  sptr_addr B ly (fst (ck_user (new_chunk cl off n), st_final S1 cl l off n tr z)) <= a <
  sptr_addr B ly (fst (ck_user (new_chunk cl off n), st_final S1 cl l off n tr z)) + req_size n) ->
  ~ (Kv ly cl v + AGis.RZ kz <= a < Kv ly cl v + AGis.RZ kz + n)).
{ intros a NE Hu. apply NE. cbn [fst]. split; [unfold new_chunk, ck_user, padd; cbn; discriminate|]. rewrite KU, RQ. exact Hu. }
exists ly, regs', mem', (with_vm_backing (m_vm_lazy md) mat md).
split. { unfold cfg_at, raZ, w64. rewrite R1, Z_to_bv_bv_unsigned. reflexivity. }
split.
{ split; [exact HARX'|]. split; [apply layout_le_refl|]. split; [apply wle_refl|].
split.
{ intros r Hr. assert (HrZ : bv_unsigned (Z_to_bv 5 r) = r).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32. unfold acallee_saved in Hr. apply Z.mod_small. lia. }
  rewrite <- (vregs_other regs n inst bp (Z_to_bv 5 r)) by (rewrite HrZ; unfold acallee_saved in Hr; lia). fold regs0.
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
  cbn [In]; tauto. }
split. { unfold same_io. destruct md; cbn; repeat split; reflexivity. }
split.
{ intros a Ra NO NO' NSc NE.
  apply aview_same. pose proof (RAWF (Z_to_bv 64 a)) as RW. rewrite unsigned_lit_small in RW by exact Ra.
  exact (RW NO NSc (NEu a NE)). }
split.
{ intros x NO NO' NSc NE. exact (RAWF x NO NSc (NEu _ NE)). }
intros a Ha. unfold spZ, AFSTACK_G in Ha. rewrite <- R2 in Ha. unfold ImgBaseAG.AFSTACK in PRS. exact (PRS a Ha). }
split. { intros _. exact ERRNO. }
split. { cbn [fst]. rewrite R10, KU. reflexivity. }
split; [exact HLP|].
split; [exact HPATH|].
cbn [fst]. unfold new_chunk, ck_user, padd. cbn. intros X; discriminate X.
Qed.
End b.
End a.
