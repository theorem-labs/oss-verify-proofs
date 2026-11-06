(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcPrim.v (commit 3d8ad2aeb77e, H4 stage B (slack-indexed post relation; DMrcDefs / DGif1Geo split; re-hide head); file sha256 7a932ed99a6d) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 2 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4; interface DMwalkIF.v at 3e29c198d40): the PRIMARY arm of
   __asan::QuarantineCallback::Recycle (0x33e30) over the opaque cut relation [ARXr] and recycle invariant [DRq],
   in MnRecycle.de_rchunk_m_t's post (raw frame, errno, memnorm keep), from the read fields DMrcReads.rc_prim_reads
   and H3's class-generic CacheDealloc contract DMwalkIF.cdealloc_g_t for the tail call at 0x34234.
   rule 24: proves function __asan::QuarantineCallback::Recycle (primary arm), at cgif_file_fuzzer's asan-ubsan image;
   reuse search LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record) (`proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0), rule-24 check B1LookupCheck CONFIRM.

   HOW.  The machine walk is the released one, unchanged: YFh7.segRC over YFgs.free_hyps (a primary chunk's n is below
   its class size, so the released interval 2 ^ 28 is never reached at any instance).  What cgif derives from ARm
   (YFfr.FH_ok, YFg7.CDPRE's model step, YFf3) comes from the fields; the post is YFg7.tfib_rchunk_prim_arm's
   composition with the raw frame, errno and memnorm keep of DGif1drMr.rchunk_primRm, all over ARXr / AOX. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o YG0k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFew AFeu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFfk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AFgs AFh7 AFf3 AFg0 AFg7.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMspec DMiface DIfaceR DMwalkIF DMrcReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ErrnoG MemnormT MemnormLocG DGif1Geo DMrcConst.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

Section p.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.
Hypothesis RR : rc_prim_reads B ARXr AOX DRq RMAXD.
Hypothesis CDG : cdealloc_g_t B ARXr AOX RMAXD.

(* The machine part of MnRecycle.de_rchunk_m_t's post (its model part, DRq / puser / AOX, rides on rc_model_t). *)
Definition rc_mach (inst : Z) (ly : alayout) (X : astate) (k : chunk) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  ErrnoG.errno_kept B mem mem' /\
  MemnormT.memnorm_keep tfibsegs mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a).

Theorem rchunk_prim_mach : forall inst ly X k ks zs cbp W regs mem md off,
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs -> ck_beg k = PPrim off ->
amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (rc_mach inst ly X k W regs mem md).
Proof.
intros inst ly X k ks zs cbp W regs mem md off PRE RX Hb.
destruct RR as (HHD & HMD & HFH & HST & HROOM).
destruct (HFH inst ly X k ks zs cbp W regs mem md off PRE RX Hb) as (Hinst & HTSD0 & HCONST & hb1 & muc & j1 & j2 & FH).
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite HTSD0; apply (ts_tsd _ TB)).
pose proof (HHD X k ks zs RX) as (Hk & _ & _).
set (c := prim_class off) in *. set (base := ck_base B ly k) in *. set (rz := ck_rz k) in *. set (nn := ck_n k) in *.
pose proof (AFgs.derived_ranges W ly regs mem c base rz nn hb1 cbp muc j1 j2 FH) as DR.
pose proof (AFgs.LYB W ly regs mem c base rz nn hb1 cbp muc j1 j2 FH) as LB.
pose proof PRE as PRE0.
destruct PRE0 as (HAR & Hci & Hra & Hra4 & Hal & Hlo & Hcb1 & Hcb2 & Hcb3 & HPRES & HPRC & HVC & Hgp & Htp & Ha0 & Ha1).
set (sp0 := spZ regs) in *.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0, spZ; apply u64_range).
(* the walk's window lies in YFf3.D *)
assert (WIN_D : forall a, AFgs.WIN ly regs base rz nn a -> AFf3.D B ly k sp0 a).
{ intros a Hw. pose proof DR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & dM & dU & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & dN8 & _).
  unfold AFf3.D, AFf3.DS, AFf3.DK, AFf3.DJ, AFf3.DH, AFf3.Mv.
  unfold AFgs.WIN, AFgs.WINF, AFgs.WINS in Hw. fold sp0 in Hw. unfold spZ in sp0.
  unfold AFgs.Mv, AFgs.SPv, AFgs.CNT8v, AFgs.N8v, AFgs.Uv in *. unfold shadow_addr.
  destruct Hw as [Hw|[[Hw|[[Hne Hw]|Hw]]|Hw]].
  - left. unfold sp0 in Hw. clear - Hw. unfold KSTACK. lia.
  - right; left. left. exact Hw.
  - right; left. right. split; [exact Hne | exact Hw].
  - do 2 right; left. exact Hw.
  - do 3 right. rewrite Z_div_mult in Hw by lia. exact Hw. }
rewrite (AFg7.recycle_chunk_prim k X off (proj2 (mem_chunk_spec _ _) Hk) Hb).
unfold cfg_at, A_RChunk. rewrite <- (AFg0.wvb_self md) at 1.
eapply (amreal_SRr_pre tfibsegs _ _ _ _ (AFgs.at_CD W ly regs mem md c base rz nn hb1)).
{ exact (AFh7.segRC W ly regs mem md c base rz nn hb1 cbp muc j1 j2 (m_vm_materialized md) FH). }
intros W' c' _ HCD.
destruct HCD as (-> & regs' & mem' & mat & -> & CSP & CRA & CS & C10 & C11 & C12 & C13 & MEQ' & PRESW & VALS).
cbv zeta in VALS. destruct VALS as (V1 & V2 & SH).
set (md' := with_vm_backing (m_vm_lazy md) mat md).
assert (SP' : spZ regs' = sp0) by (unfold spZ, sp0; rewrite CSP; reflexivity).
assert (RA' : raZ regs' = raZ regs) by (unfold raZ; rewrite CRA; reflexivity).
assert (WIN_dec : forall a, AFgs.WIN ly regs base rz nn a \/ ~ AFgs.WIN ly regs base rz nn a).
{ intros a. assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
  assert (ER : rz = 16 \/ rz <> 16) by lia.
  unfold AFgs.WIN, AFgs.WINF, AFgs.WINS.
  destruct (EM (bv_unsigned (getr regs 2) - 256) (bv_unsigned (getr regs 2))) as [C0|C0]; [left; left; exact C0|].
  destruct (EM (AFgs.Mv base rz) (AFgs.Mv base rz + 4)) as [C1|C1]; [left; right; left; left; exact C1|].
  destruct (EM (ly_T ly + t_stats + 40) (ly_T ly + t_stats + 56)) as [C3|C3]; [left; right; left; right; right; exact C3|].
  destruct (EM (AFgs.SPv base rz) (AFgs.SPv base rz + AFgs.CNT8v nn)) as [C4|C4]; [left; right; right; exact C4|].
  destruct ER as [ER|ER].
  - right. intros [X0|[[X1'|[[X2 _]|X3]]|X4]]; [exact (C0 X0) | exact (C1 X1') | exact (X2 ER) | exact (C3 X3) | exact (C4 X4)].
  - destruct (EM base (base + 8)) as [C2|C2]; [left; right; left; right; left; split; [exact ER | exact C2]|].
    right. intros [X0|[[X1'|[[_ X2]|X3]]|X4]]; [exact (C0 X0) | exact (C1 X1') | exact (C2 X2) | exact (C3 X3) | exact (C4 X4)]. }
(* the walk's own frame, as the step field reads it *)
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ AFf3.D B ly k sp0 a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha ND. apply aview_same. apply (MEQ' (Z_to_bv 64 a)). rewrite unsigned_lit_small by exact Ha.
  intros Hw. exact (ND (WIN_D a Hw)). }
assert (VIS : forall a, aview tfibsegs (w_H W) mem a <> None -> aview tfibsegs (w_H W) mem' a <> None).
{ intros a Hv HN. unfold aview, mbyte, mrestrict in Hv, HN. set (xw := Z_to_bv 64 a) in *.
  destruct (w_H W xw) eqn:Hx'; [exact (Hv HN)|].
  destruct (seg_rom tfibsegs xw) eqn:ROM; [destruct (mem' xw); discriminate|].
  destruct (mem' xw) as [|] eqn:E'; [discriminate|]. clear HN.
  destruct (mem xw) as [b0|] eqn:E0; [clear Hv | exact (Hv eq_refl)].
  set (a' := bv_unsigned xw). assert (Ex : Z_to_bv 64 a' = xw) by (subst a'; apply Z_to_bv_bv_unsigned).
  destruct (WIN_dec a') as [C|C].
  - destruct (PRESW a' C) as [_ [bb Hbb]]. rewrite Ex in Hbb. congruence.
  - rewrite (MEQ' xw C) in E'. congruence. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb0 Hx'. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (clear - Hb0; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb0.
  unfold w64 in *. set (xw := Z_to_bv 64 a) in *.
  assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
  assert (Ux : bv_unsigned xw = a) by (subst xw; apply unsigned_lit_small; exact Ha').
  destruct (WIN_dec a) as [C|C].
  - exfalso. destruct (PRESW a C) as [Hh _]. change (w_H W xw = false) in Hh. rewrite Hx' in Hh. discriminate.
  - apply (MEQ' xw). rewrite Ux. exact C. }
assert (NEW_sh : forall a, AFf3.DH B ly k a -> aview tfibsegs (w_H W) mem a <> None -> aview tfibsegs (w_H W) mem' a = Some shHeapLeftRz).
{ intros a HD Hv. pose proof DR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & dSP1 & dSP2 & dN8 & dN8b & dC8 & _).
  unfold AFf3.DH, shadow_addr in HD.
  assert (E8 : SHADOW_OFF + (ck_base B ly k + ck_rz k) / 8 = AFgs.SPv base rz) by (unfold AFgs.SPv, AFgs.Uv; reflexivity).
  rewrite E8 in HD. change (ck_n k) with nn in HD. unfold AFgs.CNT8v, AFgs.N8v in SH. rewrite Z_div_mult in SH by lia.
  assert (Ha' : 0 <= a < 2 ^ 64) by (clear - HD dSP1 dSP2 dC8; unfold AFgs.CNT8v, AFgs.N8v in *; rewrite Z_div_mult in * by lia; unfold kHighMemBeg in *; lia).
  unfold aview, mbyte, mrestrict in Hv |- *. replace a with (AFgs.SPv base rz + (a - AFgs.SPv base rz)) in Hv |- * by lia. unfold w64 in SH.
  destruct (w_H W (Z_to_bv 64 (AFgs.SPv base rz + (a - AFgs.SPv base rz)))) eqn:Hh.
  - exfalso. rewrite seg_rom_none_high in Hv by (clear - HD dSP1 dSP2 dC8; unfold AFgs.CNT8v, AFgs.N8v in *; rewrite Z_div_mult in * by lia; unfold TFIB_IMG_END, kHighMemBeg in *; lia). exact (Hv eq_refl).
  - rewrite (SH (a - AFgs.SPv base rz)) by (clear - HD; lia). reflexivity. }
assert (CONST' : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (as_const B ly))
  by exact (DMrcConst.rc_prim_const B TB W ly regs mem c base rz nn hb1 cbp muc j1 j2 mem' FH HTSD HCONST MEQ').
destruct (HST inst ly X k ks zs cbp W regs mem md off mem' md' PRE RX Hb AG VIS NEW_sh HSK CONST'
  (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)) as (AR1 & CDM & DOWN & AOX1 & PUD).
(* the user ranges read only the regions, which the chunk's deletion keeps (review RevRcReads F2) *)
assert (PU1 : forall a, YFeuC.puser ly X a -> YFeuC.puser ly (AFf3.X1 X k) a) by (intros a Ha; destruct X; exact Ha).
set (X1 := AFf3.X1 X k) in *.
(* the window is owned or scratch, so off the owned sets and the scratch the walk wrote nothing *)
assert (WIN_OWN : forall x : word, AFgs.WIN ly regs base rz nn (bv_unsigned x) -> AOX ly X (bv_unsigned x) \/ ascratch B KSTACK_CF regs (bv_unsigned x)).
{ intros x Hw. destruct (DOWN (bv_unsigned x) (u64_range x) (WIN_D _ Hw)) as [O|O]; [left; exact O|].
  right. unfold ascratch. left. unfold AFf3.DS in O. fold sp0. clear - O. unfold KSTACK, KSTACK_CF in *. lia. }
assert (MEQX : forall x : word, ~ AOX ly X (bv_unsigned x) -> ~ ascratch B KSTACK_CF regs (bv_unsigned x) -> mem' x = mem x).
{ intros x NO NS. apply MEQ'. intros Hw. destruct (WIN_OWN x Hw) as [O|O]; [exact (NO O) | exact (NS O)]. }
(* CacheDealloc's call *)
assert (PRE' : cd_pre_cx B ARXr inst ly X1 c off W regs' mem' md').
{ unfold cd_pre_cx. split; [exact AR1|]. split; [exact Hinst|]. split; [exact Hci|].
  split; [rewrite CRA; exact Hra|]. split; [rewrite RA'; exact Hra4|].
  rewrite SP'. split; [exact Hal|]. split; [exact Hlo|]. split; [clear - Hcb1 Hcb2; lia|].
  split.
  { intros a Ha. assert (Ua : 0 <= a < 2 ^ 64).
    { pose proof DR as (_ & _ & _ & _ & _ & dK1 & dK2 & _). unfold sp0, spZ in Ha, Usp.
      clear - Ha Usp dK1. unfold KSTACK_CF, KSTACK, kHighMemBeg in *. lia. }
    destruct (WIN_dec a) as [C|C]; [exact (PRESW a C)|].
    apply (apresent_same (w_H W) mem); [|apply HPRES; exact Ha].
    apply MEQ'. rewrite unsigned_lit_small by exact Ua. exact C. }
  split; [rewrite (CS 3%bv ltac:(cbn; tauto)); exact Hgp|]. split; [rewrite (CS 4%bv ltac:(cbn; tauto)); exact Htp|].
  split; [exact C10|]. split.
  { rewrite C11. rewrite Hinst, (ts_inst _ TB). reflexivity. }
  split; [exact C12|].
  split; [rewrite C13; unfold base, ck_base, sptr_addr; rewrite Hb; reflexivity|].
  (* the growth room: a read of the cut (rc_prim_room_t); X1 keeps the regions, md' the maps and the eager use *)
  intros G. change (reg X1 c) with (reg X c) in G.
  change md' with (with_vm_backing (m_vm_lazy md) mat md). rewrite m_vmmaps_wvb, eager_used_wvb.
  exact (HROOM inst ly X k ks zs cbp W regs mem md off PRE RX Hb G). }
change (with_vm_backing (m_vm_lazy md) mat md) with md'.
eapply amreal_mono; [| exact (CDG inst ly X1 c off W regs' mem' md' PRE' CDM)].
cbv beta. intros [[] S''] W'' c'' (regs'' & mem'' & md'' & Hc'' & AP & RAW & EK & MK & PUF2 & PUG & CI & AOS).
cbn [snd] in *.
destruct AP as (AR'' & LLE & WLE & RP & IO & FRM & PRS).
exists regs'', mem'', md''.
split; [rewrite Hc'', RA'; reflexivity|].
split.
{ split; [exact AR''|]. split; [exact LLE|]. split; [exact WLE|].
  split.
  { intros rr Hr. rewrite (RP rr Hr). unfold acallee_saved in Hr.
    assert (R : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    destruct R as [->|R]; [exact CSP|]. apply CS. clear - R. unfold AFgs.SREGS.
    repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; subst rr; cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]). }
  split. { pose proof (AFg0.same_io_wvb md mat) as IO1. unfold md' in IO. clear - IO IO1. unfold same_io in *. destruct IO as (I1 & I2 & I3 & I4). destruct IO1 as (J1 & J2 & J3 & J4). repeat split; congruence. }
  split.
  { intros a Ha NO NO' NS NE. rewrite (FRM a Ha); [| intros O1; exact (NO (AOX1 a O1)) | exact NO' | unfold ascratch in *; rewrite SP'; exact NS | exact NE].
    apply AG; [exact Ha|]. intros HD. destruct (DOWN a Ha HD) as [O|O]; [exact (NO O)|].
    apply NS. unfold ascratch. left. unfold AFf3.DS in O. fold sp0. clear - O. unfold KSTACK, KSTACK_CF in *. lia. }
  rewrite SP' in PRS. exact PRS. }
split.
{ intros x NO NO' NS NE. rewrite (RAW x); [| intros O1; exact (NO (AOX1 _ O1)) | exact NO' | unfold ascratch in *; rewrite SP'; exact NS | exact NE].
  exact (MEQX x NO NS). }
split.
{ intros i Hi. rewrite (EK i Hi). apply MEQ'. intros Hw.
  assert (Ua : 0 <= as_errno B + i < 2 ^ 64) by (rewrite (ts_errno _ TB); unfold TFIB_ERRNO; lia).
  unfold w64 in Hw. rewrite unsigned_lit_small in Hw by exact Ua.
  apply (AFgs.notWIN_img W ly regs mem c base rz nn hb1 cbp muc j1 j2 FH (as_errno B + i)); [|exact Hw].
  rewrite (ts_errno _ TB). unfold TFIB_ERRNO, TFIB_IMG_LO, TFIB_IMG_END. lia. }
split.
{ apply (MemnormLocG.memnorm_keep_trans tfibsegs mem mem' mem''); [|exact MK].
  apply (MemnormT.memnorm_frame tfibsegs (AFgs.WIN ly regs base rz nn)); [| intros x Hx; exact (MEQ' x Hx)].
  intros x Hw. pose proof (AFgs.fh_LY _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as LY. pose proof (AFgs.fh_IMG _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as IMG.
  pose proof (AFgs.fh_Hsp _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as HSP.
  apply (DGif1Geo.win_zone_mn ly (bv_unsigned (getr regs 2)) x LY IMG HSP).
  pose proof DR as (dT1 & dT2 & dS1 & dS2 & _ & _ & _ & _ & _ & _ & dB1 & dB2 & _ & _ & dM & dU & _ & _ & dBM & dUN & _ & _ & dN1 & dRZ & dSP1 & dSP2 & _ & _ & dC8 & _).
  pose proof LB as (L1 & L2 & L3 & L4 & L5 & L6 & _).
  pose proof (AFgs.class_facts _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as (K1 & _).
  unfold AFgs.WIN, AFgs.WINF, AFgs.WINS in Hw.
  destruct Hw as [Hw|[[Hw|[[_ Hw]|Hw]]|Hw]].
  - left. clear - Hw. unfold KSTACK. lia.
  - do 2 right; left. clear - Hw dS1 dB1 dB2 dM dU dUN dN1 dBM L4 L5. unfold kSpaceSize, kPrimResvSize, AFgs.Mv, AFgs.Uv in *. lia.
  - do 2 right; left. clear - Hw dS1 dB1 dB2 K1 L4 L5. unfold kSpaceSize, kMaxSize, kPrimResvSize in *. lia.
  - right; left. clear - Hw. change kThreadObjSize with 4096. change t_stats with 2800 in Hw. lia.
  - do 3 right. clear - Hw dSP1 dSP2. unfold kImgEnd, TASK_SIZE, kHighMemBeg in *. lia. }
split.
{ intros a Ha PU NK. rewrite (PUF2 a Ha (PU1 a PU)). apply AG; [exact Ha|]. exact (PUD a PU NK). }
split; [intros a PU; exact (PUG a (PU1 a PU))|].
split; [exact CI|].
intros a O. exact (AOX1 a (AOS a O)).
Qed.

(* The primary arm in MnRecycle.de_rchunk_m_t's post: the machine part, and the model part from rc_model_t. *)
Theorem rchunk_prim_m : forall inst ly X k ks zs cbp W regs mem md off,
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs -> ck_beg k = PPrim off ->
amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  ErrnoG.errno_kept B mem mem' /\
  MemnormT.memnorm_keep tfibsegs mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq (snd r) ks zs /\ st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a)).
Proof.
intros inst ly X k ks zs cbp W regs mem md off PRE RX Hb.
pose proof RR as (_ & HMD & _).
pose proof (amreal_apost tfibsegs _ _ W _ _ (HMD X k ks zs RX) (rchunk_prim_mach inst ly X k ks zs cbp W regs mem md off PRE RX Hb)) as A.
eapply amreal_mono; [|exact A]. cbv beta.
intros r W' c' [DQ (regs' & mem' & md' & Hc & HP & HR & HE & HK & HV & PU & CI & AO)].
exists regs', mem', md'. repeat (split; [assumption|]). exact AO.
Qed.
End p.
End d.
