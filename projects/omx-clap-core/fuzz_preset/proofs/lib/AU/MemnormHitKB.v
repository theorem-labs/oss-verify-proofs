(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormHitK.v (a working branch 29b7505aa27, file sha256 27e8828a0fd7) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53; pin f8f98a95bc52); module paths changed; its 3 image addresses moved by code-verified function pairs (4 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin B (pinned fuzz_preset.asan-ubsan f8f98a95bc52, twin 3b5e1a099b53; this file at 74f20580f552) to B' (#102 pin d663f82d7f48, twin c90d4fa54d43) by the relocation route of record, frozen alreloc a5c53bb2bed4ad03 (a Theorem Labs lane's internal file alreloc.py.frozen-a5c53bb2bed4ad03), --assume-source, --resolve resolve-B102.txt (sha256 5cd2316e3413; internal record) (2 lines name this file); 3 numerals changed. *)
(* Theorem Labs, 2026-10 (task MEMNORM): the hit-k arm of AGil.v with memnorm kept.  [ARM_HITK_em] is
   AGil.ARM_HITK_e with MemnormT.alloc_leaf_em (ErrnoG.alloc_leaf_e plus `memnorm mem -> memnorm mem'`) in place of
   ErrnoG.alloc_leaf_e.  rule 24: no function proved (kind: arm twin, frame corollary).

   As in the g pilot (MemnormHitGB.v): the keep comes from the arm's own raw frame, at_RETkw's MEQF (AGif0n.v:111-113),
   which keeps every byte outside ImgBaseAG.K6.WIN, ag_dzone, the new block [K6.Kv + 16, + K6.NPv n) and its shadow;
   none of those zones holds a read-only byte or reaches TASK_SIZE ([memnorm_at_RETkw]):
   - the stack window, the class span (Kv / Uv), the block, PBW and the shadow lie at or above kImgEnd, where tfibsegs
     has no segment (MemnormHitGB.mn_safe_high), and below TASK_SIZE (layout_ok: lo_top / lo_space_in / lo_high,
     YG0f.v:309-323);
   - the thread object's cells (K6.WINT) and the depot's node and store blocks are owned extents
     (MemnormHitGB.mn_safe_owned); the depot zone's static part [0x17d5c8, 0x5cdd50) lies in tfibsegs' read-write
     segments (MemnormSafeAB.mn_safe_rw).
   The proof of ARM_HITK_em is AGil.v:307-494 (blocks marked as copies; the section header is AGil.v:45-60, :89-90,
   :282-284, and EA_K is AGil.EA_K at this section's B TS EAI EAS EAD) plus the memnorm conjunct from the same MEQF;
   no runner is swapped and no walk is touched.  AGil.v is unchanged. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFi1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGhz AGi0 AGi2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFi3 AllocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGjg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoApart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGj6 AGjd AGje.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGil.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ImgBaseAG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require MemnormHitGB MemnormSafeAB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* memnorm is kept by a memory that equals [mem] outside at_RETkw's raw frame zones (AGif0n.v:111-113, the clause in
   the form at_RETkw states it). *)
Lemma memnorm_at_RETkw : forall ly (regs0 : bvmap 5 word) n cl v odd (mem mem' : word -> option byte),
layout_ok ly -> img_cover ly ->
ly_stk_lo ly + ImgBaseAG.AFSTACK <= bv_unsigned (getr regs0 2) -> bv_unsigned (getr regs0 2) <= ly_stk_hi ly ->
1 <= cl <= 31 -> 0 <= v -> 16 * v + 2 ^ 16 <= 2 ^ 32 -> 0 <= n <= 48 ->
(forall x : word, ~ ImgBaseAG.K6.WIN ly regs0 n cl v odd (bv_unsigned x) -> ~ ImgBaseAG.ag_dzone ly (bv_unsigned x) ->
 ~ (ImgBaseAG.K6.Kv ly cl v + ImgBaseAG.K6.RZ <= bv_unsigned x < ImgBaseAG.K6.Kv ly cl v + ImgBaseAG.K6.RZ + ImgBaseAG.K6.NPv n) ->
 ~ (ImgBaseAG.K6.SUv ly cl v <= bv_unsigned x < ImgBaseAG.K6.SUv ly cl v + ImgBaseAG.K6.N8D n / 8) -> mem' x = mem x) ->
MemnormT.memnorm_keep tfibsegs mem mem'.
Proof.
intros ly regs0 n cl v odd mem mem' LY IMG HSP HSH Hcl Hv Hv2 Hn MEQ.
pose proof (ErrnoApart.ly_space_high ly LY) as SH. pose proof (lo_space_in ly LY) as [S1 S2]. pose proof (lo_high ly LY) as [P1 P2].
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). pose proof (ASAN_CEIL_range) as [CR _].
assert (C0 : 0 <= cl * 2 ^ 32 <= 31 * 2 ^ 32) by nia.
assert (RZ16 : ImgBaseAG.K6.RZ = 16) by reflexivity.
assert (KU : kImgEnd <= ImgBaseAG.K6.Kv ly cl v /\ ImgBaseAG.K6.Kv ly cl v + 16 + 65536 <= ASAN_CEIL).
{ unfold ImgBaseAG.K6.Kv. unfold in_high, kSpaceSize, kPrimResvSize, kImgEnd in *. lia. }
assert (UE : ImgBaseAG.K6.Uv ly cl v = ImgBaseAG.K6.Kv ly cl v + 16) by reflexivity.
assert (UU0 : 0 <= ImgBaseAG.K6.Uv ly cl v <= ASAN_CEIL) by (rewrite UE; unfold kImgEnd in KU; lia).
assert (UU : 0 <= ImgBaseAG.K6.Uv ly cl v / 8 <= ASAN_CEIL / 8)
  by (split; [apply Z.div_pos | apply Z.div_le_mono]; lia).
assert (NP : 1 <= ImgBaseAG.K6.NPv n <= 48) by (unfold ImgBaseAG.K6.NPv; lia).
assert (N0 : 0 <= ImgBaseAG.K6.N8D n <= 48).
{ unfold ImgBaseAG.K6.N8D. pose proof (Z.div_pos (ImgBaseAG.K6.NPv n) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.mul_div_le (ImgBaseAG.K6.NPv n) 8 ltac:(lia)). lia. }
assert (SHB : ImgBaseAG.SHBv = 0x7fff8000) by reflexivity.
apply (MemnormT.memnorm_frame4 tfibsegs (ImgBaseAG.K6.WIN ly regs0 n cl v odd) (ImgBaseAG.ag_dzone ly)
  (fun a => ImgBaseAG.K6.Kv ly cl v + ImgBaseAG.K6.RZ <= a < ImgBaseAG.K6.Kv ly cl v + ImgBaseAG.K6.RZ + ImgBaseAG.K6.NPv n)
  (fun a => ImgBaseAG.K6.SUv ly cl v <= a < ImgBaseAG.K6.SUv ly cl v + ImgBaseAG.K6.N8D n / 8) mem mem').
- intros x Hw. unfold ImgBaseAG.K6.WIN in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
  + apply MemnormHitGB.mn_safe_high. unfold ImgBaseAG.AFSTACK, kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
  + apply (MemnormHitGB.mn_safe_owned ly (ly_T ly, kThreadObjSize) x LY IMG
      ltac:(unfold owned_extents; right; right; left; reflexivity)).
    cbn [fst snd]. unfold ImgBaseAG.K6.WINT, ImgBaseAG.K6.Pv, ImgBaseAG.K6.SSLOTv in Hw.
    unfold kThreadObjSize, t_cache, t_stats, t_unwinding in *. lia.
  + apply MemnormHitGB.mn_safe_high. rewrite UE in Hw. unfold TASK_SIZE. lia.
  + destruct Hw as [_ Hw]. apply MemnormHitGB.mn_safe_high. unfold ImgBaseAG.K6.PBv in Hw. rewrite SHB, RZ16 in Hw.
    assert (0 <= (ImgBaseAG.K6.Kv ly cl v + 16 + ImgBaseAG.K6.N8D n) / 8 <= ASAN_CEIL / 8)
      by (split; [apply Z.div_pos | apply Z.div_le_mono]; lia).
    unfold kImgEnd, TASK_SIZE in *. lia.
- intros x Hd. change (AGis.DZONE ly (bv_unsigned x)) in Hd. destruct Hd as [Hd|[Hd|Hd]].
  + apply MemnormSafeAB.mn_safe_rw. unfold TASK_SIZE. lia.
  + apply (MemnormHitGB.mn_safe_owned ly (ly_NB ly, kNodesBlockSize) x LY IMG
      ltac:(unfold owned_extents; right; right; right; right; left; reflexivity)). exact Hd.
  + apply (MemnormHitGB.mn_safe_owned ly (ly_SB ly, kStoreBlockSize) x LY IMG
      ltac:(unfold owned_extents; right; right; right; right; right; left; reflexivity)). exact Hd.
- intros x Hb. apply MemnormHitGB.mn_safe_high. rewrite RZ16 in Hb. unfold TASK_SIZE. lia.
- intros x Hs. apply MemnormHitGB.mn_safe_high. unfold ImgBaseAG.K6.SUv in Hs. rewrite SHB in Hs.
  assert (0 <= ImgBaseAG.K6.N8D n / 8 <= 6) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  unfold kImgEnd, TASK_SIZE in *. lia.
- exact MEQ.
Qed.

(* copy of AGil.v:45-60 (the section header), unchanged *)
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
Hypothesis IFK : AIfaceK B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
Hypothesis TS : TfibSyms B.
Local Ltac bvne := first [cbn; lia | vm_compute; congruence | intros X; vm_compute in X; discriminate X].
(* copy of AGil.v:88-90, unchanged *)
(* can_fill of the caller's call site: 1 (malloc, realloc) or 0 (calloc). *)
Variable cf : Z.
Hypothesis Hcf01 : cf = 0 \/ cf = 1.
(* copy of AGil.v:279-284, unchanged *)
(* ERRNO-KEPT: errno's 4 bytes lie outside at_RETkw's raw frame (the WIN windows, the depot zone, the new block and
   its shadow) at any layout and stack pointer in that layout's stack.  From h-decbox-a9's ErrnoApart
   image Props (discharged once per image in ErrnoApartcgif). *)
Hypothesis EAI : ErrnoApart.errno_in_img.
Hypothesis EAS : ErrnoApart.errno_apart_shadow_ag.
Hypothesis EAD : ErrnoApart.errno_apart_dzone_ag.
(* AGil.EA_K (AGil.v:285) at this section's variables *)
Let EA_K := AGil.EA_K B TS EAI EAS EAD.
(* MEMNORM-KEPT twin of AGil.ARM_HITK_e (MemnormT.alloc_leaf_em). *)
Theorem ARM_HITK_em : forall inst so bp ly S W regs mem md n tr l off,
alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 cf inst so bp ly S W regs mem md n tr ->
0 <= n <= 48 -> st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Proof.
(* copy of AGil.v:307-490, unchanged *)
intros inst so bp ly S W regs mem md n tr l off PRE Nrange Hinited Hcache.
destruct IF as [Finst Fview Fshape Fdepot Fdaok Fpost Fowned Funinit].
destruct IFK as [Fpostk Fownedk].
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres0 & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hn0 & Hlive).
unfold spZ, raZ, AFSTACK_G in *. rewrite (ts_tp B TS) in Htp.
pose proof (Finst _ _ _ _ _ _ HARX) as HIO. pose proof HIO as (HIO1 & HIO2 & HIO3).
(* The k sizes: redzone 16, header size NPv = max n 1. *)
pose proof (AGj6.case0_sizes n Nrange) as (L & RS & R8 & NP & FP & NS & RQ).
pose proof (AGj6.K0_facts n Nrange) as (_ & _ & NPr & _).
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
assert (Hcl_def : cl = class_id (AGj6.R8v n + AGj6.RZ))
by (subst cl; unfold chunk_class; first [rewrite NS; reflexivity | rewrite NS, <- RS; reflexivity]).
(* The view's consequences (AGjd). *)
assert (Hcl : 1 <= cl <= 31) by (assert (1 <= cl <= 30) by (eapply AGjd.vw_cl_range; eassumption); lia).
assert (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32) by (eapply AGjd.vw_Hv; eassumption).
assert (HKpres : forall a, AGj6.Kv ly cl v <= a < AGj6.Kv ly cl v + AGj6.RZ + AGj6.R8v n -> apresent (w_H W) mem a)
by (eapply AGjd.vw_KPRES; eassumption).
assert (HSKpres : forall a, AGj6.SKv ly cl v <= a < AGj6.SKv ly cl v + (AGj6.RZ + AGj6.R8v n) / 8 -> apresent (w_H W) mem a)
by (eapply AGjd.vw_SKPRES; eassumption).
assert (HPB250 : AGj6.NPv n mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W) mem) (AGj6.PBv ly n cl v) 1 250)
by (eapply AGjd.vw_PB250; eassumption).
assert (JV : exists j0 j1 j2 j3 j4 jb,
val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + 2784) 8 j0 /\ val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + 2800) 8 j1 /\
val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + 2808) 8 j2 /\ val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + 2816) 8 j3 /\
val_mem tfibsegs (mrestrict (w_H W) mem) (AGj6.SSLOTv ly cl) 8 j4 /\ 0 <= jb <= 255 /\
val_mem tfibsegs (mrestrict (w_H W) mem) (AGj6.Kv ly cl v + AGj6.RZ - 15) 1 jb) by (eapply AGjd.vw_junk_values; eassumption).
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
(* can_fill: the walk's atom 15 is 0 or 1 (AGje.SEED_ok / AGjg's Hcf). *)
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
(* The seed at Allocate's entry (AGje). *)
assert (SEED : st_ok tfibsegs (AGj6.E0 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4) KS_1
(restrict (w_H W) (mkst regs (w64 A_Allocate) mem (seg_rom tfibsegs)))).
{ exact (@AGje.SEED_ok _ _ W ly regs0 mem n tr cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 HLY HIMG Hn Htp0 Hsp Htrlen Hso Hbp Hcf
  (fun (_ : Z) (_ : word -> option byte) => True) Nrange B inst TS HV Hi11 HIO PSO0 PLEN0 Hpres00 Hcl_class Hcsz_def
  Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def regs HUo HU10 HU11 HU12 HU14). }
(* The model state at the pop: the tick. *)
set (S1 := set_nev (st_nev S + 1) S).
assert (Hcache1 : pc_chunks (cache S1 cl) = l ++ [off]) by exact Hcache.
(* The depot callee, at this allocator. *)
assert (HDEP : forall (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) (buf : Z),
(forall x : word, AGj6.DZONE ly (bv_unsigned x) \/ CZONE ly (bv_unsigned x) -> mem1 x = mem x) ->
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
~ AGj6.DZONE ly (bv_unsigned x) -> mem' x = mem1 x) /\
(forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem' a) /\
dpost inst ly S W tr z mem')).
{ intros regs1 mem1 md1 buf. exact (Fdepot inst ly S W mem md tr regs1 mem1 md1 buf HARX Htr). }
assert (HDAOK : forall z m, dpost inst ly S W tr z m -> aok S1 (KDepot tr) z) by (intros z m H; exact (Fdaok _ _ _ _ _ _ _ H)).
assert (Hmat0 : m_vm_materialized md = m_vm_materialized md) by reflexivity.
(* The walk (AGjg). *)
assert (MAIN : amreal tfibsegs (malloc_join_t stag n tr cl S1) W (cfg_at tfibsegs A_Allocate regs mem md)
(fun r W' c' => exists odd z, r = (ck_user (new_chunk cl off n), st_final S1 cl l off n tr z) /\
(odd = true <-> AGj6.NPv n mod 8 <> 0) /\
at_RETkw W ly regs0 mem md n cl cnt v jb (fun z m => dpost inst ly S W tr z m) odd z W' c')).
{ eapply hitk_inner; try first [exact SEED | exact HDEP | exact HDAOK | exact Hmat0 | eassumption].
  Unshelve. all: try first [exact (m_vm_materialized md) | exact B]. }
(* The model's steps before the pop (shape (b)). *)
assert (MAIN' : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x326a4 regs mem md)
(fun r W' c' => exists odd z, r = (ck_user (new_chunk cl off n), st_final S1 cl l off n tr z) /\
(odd = true <-> AGj6.NPv n mod 8 <> 0) /\
at_RETkw W ly regs0 mem md n cl cnt v jb (fun z m => dpost inst ly S W tr z m) odd z W' c')).
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
destruct (Fpostk inst ly S W mem md n tr l off regs0 jb odd z regs' mem' mat HARX HRP ltac:(lia) Hlive Htr Nrange Hinited Hcache WF Hjb Hjb_def
  HR0 Hodd HPATH)
as [HARX' HLP].
assert (KU : sptr_addr B ly (ck_user (new_chunk cl off n)) = AGj6.Kv ly cl v + AGj6.RZ).
{ unfold new_chunk, ck_user, ck_rz. cbn [ck_beg ck_req padd]. rewrite RS.
  rewrite (AGj6.Kv_is_sptr ly cl v Hcl B off Hoff_def). unfold sptr_addr. cbn. try unfold AGj6.RZ in *. lia. }
(* The raw frame equation at Allocate's ret: from at_RETkw's memory clause (MEQF) and the k owned set (if_owned_k). *)
assert (RAW : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ ascratch B AFSTACK_G regs (bv_unsigned x) ->
  ~ (ck_user (new_chunk cl off n) <> PNull /\ sptr_addr B ly (ck_user (new_chunk cl off n)) <= bv_unsigned x <
     sptr_addr B ly (ck_user (new_chunk cl off n)) + req_size n) ->
  mem' x = mem x).
{ intros x NO NSc NE. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
  assert (OWN : hit_writes_k ly n cl v odd (bv_unsigned x) -> False).
  { intros HW. apply NO. exact (Fownedk inst ly S W mem md n l off odd (bv_unsigned x) HARX HRP Nrange Hinited Hcache Rx (proj1 Hodd) HW). }
  apply MEQF.
  - intros Hw. unfold ImgBaseAG.K6.WIN in Hw. destruct Hw as [Hs|Hw].
    + apply NSc. unfold ascratch. left. unfold spZ, AFSTACK_G. rewrite <- R2. unfold ImgBaseAG.AFSTACK in Hs. exact Hs.
    + apply OWN. unfold hit_writes_k. destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw | right; left; exact Hw | right; right; left; exact Hw].
  - intros Hd. apply OWN. unfold hit_writes_k. right; right; right; left; exact Hd.
  - intros Hu. apply NE. split; [unfold new_chunk, ck_user, padd; cbn; discriminate|]. rewrite KU, RQ. exact Hu.
  - intros Hs. apply OWN. unfold hit_writes_k. right; right; right; right; exact Hs. }
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
{ intros a Ra NO NO' NSc NE. apply aview_same. apply RAW; rewrite unsigned_lit_small by exact Ra; [exact NO | exact NSc | exact NE]. }
split.
{ intros x NO NO' NSc NE. exact (RAW x NO NSc NE). }
intros a Ha. unfold spZ, AFSTACK_G in Ha. rewrite <- R2 in Ha. unfold ImgBaseAG.AFSTACK in PRS. exact (PRS a Ha). }
(* errno kept: at_RETkw's raw frame (MEQF) at errno's bytes, which lie outside its windows (EA_K). *)
split.
{ intros _ i Hi. pose proof Hsp as (Lo0 & _ & Hi0 & _).
  pose proof (EA_K ly regs0 n cl v odd i HLY HIMG Lo0 Hi0 Nrange Hcl (proj1 Hv) Hi) as (N1 & N2 & N3 & N4).
  assert (RE : 0 <= as_errno B + i < 2 ^ 64) by (rewrite (ts_errno B TS); unfold TFIB_ERRNO; lia).
  assert (UX : bv_unsigned (w64 (as_errno B + i)) = as_errno B + i) by (unfold w64; apply unsigned_lit_small; exact RE).
  apply MEQF; rewrite UX; assumption. }
(* memnorm: the same raw MEQF keeps it (memnorm_at_RETkw). *)
assert (MNK : MemnormT.memnorm_keep tfibsegs mem mem').
{ pose proof Hsp as (Lo0 & _ & Hi0 & _).
  exact (memnorm_at_RETkw ly regs0 n cl v odd mem mem' HLY HIMG Lo0 Hi0 Hcl (proj1 Hv) (proj2 Hv) Nrange MEQF). }
split; [exact MNK|].
(* copy of AGil.v:491-497, unchanged *)
split. { cbn [fst]. rewrite R10, KU. reflexivity. }
split; [exact HLP|].
split; [exact HPATH|].
cbn [fst]. unfold new_chunk, ck_user, padd. cbn. intros X; discriminate X.
Qed.
End b.
End a.
