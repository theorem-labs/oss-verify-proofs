(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: pj_free's image-B walk (fuzz_preset asan-ubsan, B 0x86a24, 136 slots of lib/B/Listing_prog.v
   v4 f843fdf7fe2f; lib/B/Prog/pj_free_defs.v), THE TOP: the segments composed, by induction on the depth n (the
   recursive call at B 0x86b10 cites the text at n - 1, pj_free_seg_loop.v), the free order, and the kit's text.
   - tpj_free_specX_B: the kit's OWN text tpj_free_specX (lib/A/PRH_FnPj.v; written against PRH_FnPj.v blob 3a546f3492c6:
     tpj_free_specX CTX0 n, no run words DW, the POST-IMPLICATION form - no position and no run premise at entry, the
     class-24 bound and the hull budget only for v <> 0, the head-width premise prh_head_wide, the post transferring
     every position at S whose run's next events are prhPj_free_evs F to the EXACT advance i + |prhPj_free_evs F|) at
     image B, every n;
     its preset instance tpj_free_specX_B_preset. The order list pj_foR and pj_free_fo are the kit's
     (lib/A/PRH_PjOrder.v blob e5917626b82b), the supply of the run premise too (PRH_FnPj.v prhPj_free_evs_supply /
     prhPj_free_evs_nil).
   THE CALLEE TEXT is the kit's OWN fuzz_free text tfuzz_free_specX (lib/A/PRH_FnAlloc.v, blob 5f50b300eb2c),
   post-implication too: its bulk arm moves a bulk sub-position iface_room_pos_bulk .. L k to .. L (S k), when p <> 0 and L's k-th entry is n + cf_head (PRH_FnAlloc.v:399-404), for every
   run whose event at i is HBulk L, which is what pj_free's second and later frees need (they are at the bulk
   sub-position, lib/Spec/PresetRoomPosKeep.v:287-297). Its trace premise is the engine's `admits (as_universe B)
   (call_trace ..) S` and its post is BUDGETED at that trace (fpostbm ..
   (YCbqGwild.wbudget [call_trace ..] 0) ..); pj_free's four fuzz_free traces are FIXED traces (prh_univ_closure's
   clauses 1-2, prh_univ_closure_lit in pj_free_seg_lk.v / pj_free_seg_tail.v), so pf_ff_of_kit supplies `admits` by
   YCbqG.admits_ct_fix and reads the plain post back by PRH_Base.fpost_of_fpostb_fix. The old STOP (the kit's earlier fuzz_free text
   taking iface_room_pos at every entry) and the earlier tfuzz_free_specX_FIX layer are gone. The image-free
   machinery has ONE home, lib/A/Prog/PjFreeCommon.v (shared with image A's S6 walk): pf_ff_of_kit (the kit's fuzz_free
   text gives the walk's instrumented callee text tfuzz_free_specO at pf_PBk / pf_FXk), pfk_reach_bulk / _nil /
   _ccnt, pfk_safe, and pf_specX_of_walk (the kit's tpj_free_specX from ANY image's instrumented walk text, the walk
   taking the kit's prh_head_wide premise). This file instantiates it at image B's walk (tpj_free_specO_B):
   tpj_free_specX_B.
   THE RE-HIDING MOVE: a free can hide shadow again, so both of the kit's texts conclude SRr' SEGS RZ_cf (YA0nH.v, the zone of
   YGcfRehidePost.v) with their posts at that relation (PRH_Base fpostbm, its budgeted form, / fpostWmR); the walk runs at it
   (pj_free_defs.v), so pf_walk_of_segs and pf_order_fo state SRr' and fpostWmR. THE HULL: the kit's entry budget
   `v <> 0 -> PresetHullBudget.hull_budget S []` and its post's hull use are threaded by PjFreeCommon.v (pf_PBk carries
   the budget to every fuzz_free call, pf_FXk the use back, pfk_safe / pfk_reach_hull), so this file's statements
   carry them as the kit's texts do and need no hull lemma of their own.
   - tpj_free_specO_B (the instrumented walk text at any PB / FX), pj_free_order_fo_B (THE FREE ORDER: for a node read
     back from the writer's text, pj_nodeR v t D with map (fun b => snd b + HEAD) D = PresetReqAtNoMiss.tblk t, the
     run's fuzz_free calls free, in order, a list F of D's blocks with map (fun b => snd b + HEAD) F =
     PresetReqAt.fo t, lib/Spec/PresetReqAt.v:215 blob 379c33e9e482), pf_walk_of_segs, pj_free_frees_fo.
   THE cf_head = 0 HOLE (a finding against the kit's abstract-CfParams text, unchanged at 98f44d272006): at cf_head = 0
   tpj_free_specX is false - v may start a live harness block (a, k) not in D with v = a (v mod 8 = 0, a mod 16 = 0),
   and the memset at B 0x86bc8 zeroes that block's ledger head word val_mem (a - cf_head) 8 k while the post's ledger
   keeps (a, k). The walk takes the prh_head_wide (PRH_Base.v, 8 <= cf_head; 16 at CfParams_preset). The same hole
   and the same hypothesis are in pj_string: lib/B/Prog/pj_string_top.v (blob 25dd88e64c66) :13 / :86-87 HWIDE.
   Pins (vm_compute of B_prog_sigma / B_prog_base / PJF_* / pi_ret_sites against lib/B/Listing_prog.v v4 f843fdf7fe2f
   in this workspace, and the objdump of the unstripped twin): 19 addresses, 0 mismatches - entry 0x86a24; cuts
   0x86acc (+0xa8), 0x86b14 (+0xf0), 0x86b54 (+0x130), 0x86b70 (+0x14c), 0x86bcc (+0x1a8); jal pj_free 0x86b10; jal
   fuzz_free 0x86b50, 0x86b84, 0x86b9c, 0x86bb8; jal __asan_memset 0x86bc8; bltu 0x86b6c; ret 0x86c04; fuzz_free
   return sites 0x86b88, 0x86ba0, 0x86bbc (pi_ret_sites F_pj_free RT_fuzz_free, with 0x86b54); callees fuzz_free
   0x8613c, __asan_memset 0x5296c (printed checked_memset).
   proves pj_free (kind: walk composition; the segment files carry the instructions).
   Section hypotheses (Section top): AR_laws_x at cf_head; ARx_frame_hull_vis (YGcfFsVis.v); PALib (STAND-IN, the
   image binding of B's GOT slot and cell); prh_head_wide (PRH_Base.v). tpj_free_specX_B (Section topX) takes the
   first three and passes the kit's own prh_head_wide premise to the walk. Section inst discharges the three by the
   INSTANCE WITNESSES there (pf_wit_laws, pf_wit_visf, pf_wit_pal, closed at the real image B); pf_wit_head shows the kit's
   prh_head_wide premise holds at CfParams_preset, and the texts' image premise prh_univ_closure has its witness
   pf_wit_univ at the driver context. No ADDRESS numeral in the proofs (the addresses above are comment pins) except
   0x815c8 in pf_wit_univ's statement: the driver context CTX0 = [[0x815c8]], target_run's
   `jal LLVMFuzzerTestOneInput` + 4 (lib/AU/PresetCfnB.v:198 RA_LLVMF, blob 316b293c8f23; the context
   lib/Reusable/YCej.v's universe was generated at, its header). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjFreeCommon PjFreePure.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_free_defs pj_free_lcut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_free_seg_ep pj_free_seg_ent.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_free_seg_lc pj_free_seg_loop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_free_seg_lk pj_free_seg_tail.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnAlloc CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YGcallMxmn YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
(* The kit's B' universe witness (a leaf of the kit tree; it Requires image A's records too, which this file then loads) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Witness.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis VISF : ARx_frame_hull_vis SEGS B ARx.
(* STAND-IN for the unit's image binding of B (TfibSyms analogue; owner a Theorem Labs lane), proved once by the final instance *)
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.
(* the harness head is at least a word (PRH_Base.v:186 prh_head_wide; the preset instance has cf_head = 16) *)
Hypothesis HEAD8 : prh_head_wide.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation RZ_cf := (@YGcfRehidePost.RZ_cf rc).

(* ---- the segments give the text at every depth ---- *)
Theorem pf_walk_of_segs : forall PB FX CTX0,
  pf_texts (SK := SK) B ARx PB FX -> pfs_LX (SK := SK) B ARx PB FX CTX0 ->
  (forall d', pfs_LK (SK := SK) B ARx PB FX CTX0 d') ->
  forall n, tpj_free_specO (PA := PA) B ARx SK PB FX CTX0 n.
Proof.
intros PB FX CTX0 TXT SLX SLK n. induction n as [|d' IH].
- intros most own ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran HFP HU HR H10 HW HC HSF HL.
  set (en := MkPfEnt ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran most own O).
  assert (HPRE : pf_pre B ARx PB FX CTX0 en)
    by exact (conj HFP (conj HU (conj HR (conj H10 (conj HW (conj HC (conj HSF HL))))))).
  refine (pfs_entry_holds B ARx LAWS PAL PB FX CTX0 (pfs_EP_holds B ARx LAWS FX) SLX en HPRE _).
  intros nd d'' ly1 S1 Hp1 W1 regs1 mem1 md1 k1 HND HLH. destruct HLH as (En & _). discriminate En.
- intros most own ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran HFP HU HR H10 HW HC HSF HL.
  set (en := MkPfEnt ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran most own (Datatypes.S d')).
  assert (HPRE : pf_pre B ARx PB FX CTX0 en)
    by exact (conj HFP (conj HU (conj HR (conj H10 (conj HW (conj HC (conj HSF HL))))))).
  refine (pfs_entry_holds B ARx LAWS PAL PB FX CTX0 (pfs_EP_holds B ARx LAWS FX) SLX en HPRE _).
  intros nd d'' ly1 S1 Hp1 W1 regs1 mem1 md1 k1 HND HLH.
  assert (Ed : d'' = d') by (destruct HLH as (En & _); cbn [en fe_n] in En; injection En; auto). subst d''.
  (* the loop: by induction on the slots left *)
  assert (LOOP : forall m i ly2 S2 Hp2 W2 regs2 mem2 md2 k2, Z.to_nat (fn_n nd - i) = m ->
     pf_LH (SK := SK) B ARx FX en nd d' i ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS RZ_cf W2 (pf_cfg PJF_LH regs2 mem2 md2) (pf_FIN (SK := SK) B ARx FX en)).
  { induction m as [|m IHm]; intros i ly2 S2 Hp2 W2 regs2 mem2 md2 k2 Hm HLH2.
    - exfalso. destruct HLH2 as (_ & Hi & _). lia.
    - apply (pfs_LH_holds B ARx LAWS VISF PB FX CTX0 d' TXT IH (SLK d') en nd i ly2 S2 Hp2 W2 regs2 mem2 md2 k2
        HPRE HND HLH2).
      + intros ly3 S3 Hp3 W3 regs3 mem3 md3 k3 HLH3.
        apply (IHm (i + 1) ly3 S3 Hp3 W3 regs3 mem3 md3 k3); [lia | exact HLH3].
      + intros ly3 S3 Hp3 W3 regs3 mem3 md3 k3 HLX3. exact (SLX en nd ly3 S3 Hp3 W3 regs3 mem3 md3 k3 HPRE HND HLX3). }
  exact (LOOP _ 0 ly1 S1 Hp1 W1 regs1 mem1 md1 k1 eq_refl HLH).
Qed.

(* ---- THE FREE ORDER: a node read back from the writer's text is freed in fo's order ---- *)
(* pj_free's run on such a node, as tpj_free_specO with pj_nodeR / tblk in place of pj_foR: its post adds that the
   fuzz_free calls freed, in order, a list F of the node's blocks whose requests are PresetReqAt.fo t. The run crosses
   fuzz_free, so the statement is at SRr' SEGS RZ_cf and its post is fpostWm's R form at wle' SEGS RZ_cf *)
Definition pf_order_fo (PB : astate -> Prop) (FX : pf_obs) (CTX0 : list (list Z)) (n : nat) : Prop :=
  forall ly S Hp W regs mem md ch d v t D Lam peak cnt fail ran most own,
  fpre (PA := PA) B ARx (STK_pj_free n) ly S Hp W regs mem md ch ->
  prh_univ_closure B CTX0 -> room_live_cf S ->
  getr regs 10 = w64 v ->
  fwin (PA := PA) ly W regs mem d ->
  v <> 0 -> v < YM05.alloc_ceiling ->
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam) v t D ->
  map (fun b => snd b + PresetReqAt.HEAD) D = PresetReqAtNoMiss.tblk t ->
  (PjTree.depth t <= n)%nat ->
  prhPj_slot (PA := PA) B (STK_pj_free n) d ly S Lam W regs mem v ->
  (forall F, pj_foR SEGS (rdW W mem) (prh_lin Lam) n v D F -> pf_safe FX PB F ly S) ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr' SEGS RZ_cf W (cfg_at SEGS (SIGMA AS_pj_free) regs mem md)
    (fpostWmR (PA := PA) B ARx SK (wle' SEGS RZ_cf) (STK_pj_free n) d
       (if v =? 0 then [] else (v, v + 56) :: ablocks_fp (prhPj_hbl D))
       regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       pf_K0post (PA := PA) B D v ly S Hp Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' md' /\
       exists F, map (fun b => snd b + PresetReqAt.HEAD) F = PresetReqAt.fo t /\ pf_reach FX F ly S [] ly' S')).

(* the order from pj_free's text: PRH_PjOrder.pj_free_fo gives the node's F (fo's requests) *)
Theorem pj_free_frees_fo : forall PB FX CTX0 n,
  tpj_free_specO (PA := PA) B ARx SK PB FX CTX0 n -> pf_order_fo PB FX CTX0 n.
Proof.
intros PB FX CTX0 n TXT ly S Hp W regs mem md ch d v t D Lam peak cnt fail ran most own HFP HU HR H10 HW Hv0 Hvc HNODE
  HSZ HDEP HSLOT HSAFE HL.
destruct (pj_free_fo SEGS (rdW W mem) (prh_lin Lam) v t D HNODE HSZ n HDEP) as (F & HFO & HFOt).
pose proof (TXT most own ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran HFP HU HR H10 HW
  (or_intror (conj Hv0 (conj Hvc (conj HFO HSLOT)))) (fun _ => HSAFE F HFO) HL) as G.
eapply (SRr'_mono SEGS RZ_cf); [exact G|]. cbv beta.
intros W' c' _ (ly' & S' & Hp' & regs' & mem' & md' & k & Ec & HJ & HWIN & HP & [(HK0 & HRC) HMN]).
exists ly', S', Hp', regs', mem', md', k. split; [exact Ec|]. split; [exact HJ|]. split; [exact HWIN|].
split; [exact HP|]. split; [|exact HMN]. split; [exact HK0|]. exists F. split; [exact HFOt | exact HRC].
Qed.

(* ================================================================ THE THEOREMS AT IMAGE B *)
(* pj_free's walk at image B: the instrumented text at every depth, from the callee texts (pf_texts: fuzz_free's
   instrumented text and __asan_memset's) *)
Theorem tpj_free_specO_B : forall PB FX CTX0, pf_texts (SK := SK) B ARx PB FX ->
  forall n, tpj_free_specO (PA := PA) B ARx SK PB FX CTX0 n.
Proof.
intros PB FX CTX0 TXT. apply (pf_walk_of_segs PB FX CTX0 TXT).
- exact (pfs_LX_holds B ARx LAWS VISF HEAD8 PB FX CTX0 TXT (pfs_EP_holds B ARx LAWS FX)).
- intros d'. exact (pfs_LK_holds B ARx LAWS VISF PB FX CTX0 d' TXT).
Qed.

(* THE FREE ORDER at image B, a proved fact: a node read back from the writer's text is freed in fo's order *)
Theorem pj_free_order_fo_B : forall PB FX CTX0 n, pf_texts (SK := SK) B ARx PB FX -> pf_order_fo PB FX CTX0 n.
Proof.
intros PB FX CTX0 n TXT. exact (pj_free_frees_fo PB FX CTX0 n (tpj_free_specO_B PB FX CTX0 TXT n)).
Qed.

End top.

(* ================================================================ THE KIT'S TEXT AT IMAGE B *)
(* The text from image B's instrumented walk (tpj_free_specO_B, pf_texts = fuzz_free's instrumented text /\
   __asan_memset's), by PjFreeCommon.v pf_specX_of_walk; the callee premises are the fuzz_free text and the memset's
   m-form intrinsic text. The walk's head-width hypothesis (Section top's HEAD8) is the kit's own premise prh_head_wide,
   which pf_specX_of_walk hands to the walk, so this Section takes the other three hypotheses only *)
Section topX. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis VISF : ARx_frame_hull_vis SEGS B ARx.
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.

Theorem tpj_free_specX_B : PRH_FnAlloc.tfuzz_free_specX (PA := PA) B ARx SK ->
  YGcallMxmn.aintrin_realizes_xm SEGS B ARx OSet (@pa_sigma _ B_prog_listing PA AS___asan_memset) ->
  forall CTX0 n, tpj_free_specX (PA := PA) B ARx SK CTX0 n.
Proof.
intros XFF XMS CTX0 n.
exact (pf_specX_of_walk (PA := PA) B ARx SK CTX0 n
  (fun HH PB FX H => tpj_free_specO_B (SK := SK) B ARx LAWS VISF PAL HH PB FX CTX0 (conj H XMS) n) XFF).
Qed.
End topX.

(* ================================================================ THE UNIVERSE CLOSURE AT IMAGE B (a witness) *)
(* The texts take prh_univ_closure B CTX0 (lib/A/PRH_Base.v, six conjuncts: clauses 1-3, 4a, 4b and clause 5, which
   the kit's univc5 restored: a callee without a frame pointer of a frame-pointer caller, over the caller's context), a
   fact about the IMAGE: image B's call graph (prh_img_B's pi_call_rets / pi_fp / pi_ret_sites) against TfibB's universe
   (lib/Reusable/YCej.v Tfib_universe). pf_wit_univ is the kit's own B' witness, CITED: lib/A/PRH_Witness.v
   prh_univ_closure_witness_B (its sound decision procedure prh_univ_closure_of_check, decided by vm_compute over every
   reachable frame-pointer state of image B from the driver context [[0x815c8]]), at B := YD2l.TfibB, whose code and
   universe are YF0l.Tfib_code and YCej.Tfib_universe by definition. The earlier hand split of the closure into its
   clauses is gone: a clause added to the closure changes the kit's witness, not this file. *)
Lemma pf_wit_univ :
  prh_univ_closure (PI := prh_img_B) (ci := CfImgB.CfImg_B) YD2l.TfibB [[0x815c8]].
Proof. exact (PRH_Witness.prh_univ_closure_witness_B YD2l.TfibB eq_refl eq_refl). Qed.

(* ================================================================ AT THE INSTANCE (preset) *)
(* image B's allocator instance ARcf rsegs TfibB at CfParams_preset. The Section topX hypotheses are discharged by the
   INSTANCE WITNESSES below (unit ruling 2026-10-29 16:45Z: an image premise needs a closed lemma at the real image):
   pf_wit_laws (LAWS, PALibB.exvi_eh_laws), pf_wit_visf (VISF, YGcfFsVis.v ARx_frame_hull_vis_cf_ok), pf_wit_pal (PAL,
   PALibB.exvi_eh_palib: each field by vm_compute at TfibB / PI_prog_B). pf_wit_head (a CfParams fact,
   PALibB.exvi_eh_head) witnesses the kit's premise prh_head_wide at CfParams_preset, as pf_wit_univ witnesses the kit's
   prh_univ_closure at the driver context: neither text premise is vacuous at the instance. The callee texts (the kit's
   fuzz_free text tfuzz_free_specX and __asan_memset's m-form) stay premises *)
Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation ARI := (YG0ncf.ARcf (cp := CP) rsegs TB).
Lemma pf_wit_laws : AR_laws_x rsegs TB ARI (@cf_head CP).
Proof. exact PALibB.exvi_eh_laws. Qed.
Lemma pf_wit_visf : ARx_frame_hull_vis rsegs TB ARI.
Proof. exact (ARx_frame_hull_vis_cf_ok rsegs TB (YG0lawscf.AR_laws_ok_cf (cp := CP) rsegs TB)). Qed.
Lemma pf_wit_pal : PALib (L := B_prog_listing) (PI := PI_prog_B) TB.
Proof. exact PALibB.exvi_eh_palib. Qed.
Lemma pf_wit_head : prh_head_wide (cp := CP).
Proof. exact PALibB.exvi_eh_head. Qed.

(* The tpj_free_specX at the preset instance, every depth *)
Theorem tpj_free_specX_B_preset :
  PRH_FnAlloc.tfuzz_free_specX (cp := CP) (PA := PI_prog_B) TB ARI SK ->
  YGcallMxmn.aintrin_realizes_xm rsegs TB ARI OSet (@pa_sigma _ B_prog_listing PI_prog_B AS___asan_memset) ->
  forall CTX0 n, tpj_free_specX (cp := CP) (PA := PI_prog_B) TB ARI SK CTX0 n.
Proof.
intros XFF XMS.
exact (tpj_free_specX_B (cp := CP) TB ARI pf_wit_laws pf_wit_visf pf_wit_pal XFF XMS).
Qed.
End inst.
