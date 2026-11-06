(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the LOOP's inner cuts of pj_free's image-B walk (lib/B/Prog/pj_free_defs.v):
     pf_LK  at +0xf0 (the return site of the recursive `jal pj_free`): slot i's subtree freed, its key Dk still to free;
     pf_LC  at +0x130 (after slot i's key): slot i done.
   The loop segment (pj_free_seg_loop.v) is pf_LH -> pf_LK (the child, by the depth-d' text) -> pf_LC (pfs_LK, the key's
   fuzz_free) -> pf_LH (i + 1) or pf_LX (pfs_LC, the bound test).
   Both hold the frame at the walk's relation wle' SEGS RZ_cf (pj_free_defs.v pf_frameR), and the segment statements
   conclude SRr' SEGS RZ_cf.
   proves no function (kind: statement text). Numerals: 240 / 304 (DERIVED: listing slot differences times 4, the
   return site 0x86b14 and 0x86b54 less the entry 0x86a24); 56 / 8 (LENGTH). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjFreeCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_free_defs.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

Definition PJF_LK : Z := PJF_PC + 240.     (* +0xf0, the recursive call's return site `lbu a0, 0(s4)` *)
Definition PJF_LC : Z := PJF_PC + 304.     (* +0x130, after the key's fuzz_free `lbu a0, 0(s6)` *)

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation RZ_cf := (@YGcfRehidePost.RZ_cf rc).

(* AFTER SLOT i's SUBTREE: its key Dk (pj_keyR at keys + 8 i) still to free, then the slots i + 1 .. n - 1 *)
Definition pf_LK (FX : pf_obs) (en : PfEnt) (nd : PfNode) (d' : nat) (i : Z) (ly : alayout) (S : astate)
  (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  fe_n en = Datatypes.S d' /\ 0 <= i < fn_n nd /\
  pf_frameR (SK := SK) B ARx (wle' SEGS RZ_cf) en ly S Hp W regs mem md k /\ pf_spill en W mem /\ pf_vregs en regs /\
  pf_lregs en regs i /\
  exists Fd Lam Dk Dr Fr,
    pf_acct B FX en ly S Hp W mem Fd (Dk ++ Fr ++ fn_own nd) Lam /\
    pf_vnode B en nd ly S Lam W mem /\
    Permutation (fe_D en) (Fd ++ Dk ++ Dr ++ fn_own nd) /\
    pj_keyR SEGS (rdW W mem) (prh_lin Lam) (fn_ks nd) (fn_keys nd + 8 * i) Dk /\
    pf_oitemsR SEGS (rdW W mem) (prh_lin Lam) (pj_foR SEGS (rdW W mem) (prh_lin Lam) d') (fn_ks nd)
      (fn_kids nd + 56 * (i + 1)) (fn_keys nd + 8 * (i + 1)) (Z.to_nat (fn_n nd - (i + 1))) Dr Fr.

(* SLOT i DONE: the slots i + 1 .. n - 1 still to free *)
Definition pf_LC (FX : pf_obs) (en : PfEnt) (nd : PfNode) (d' : nat) (i : Z) (ly : alayout) (S : astate)
  (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  fe_n en = Datatypes.S d' /\ 0 <= i < fn_n nd /\
  pf_frameR (SK := SK) B ARx (wle' SEGS RZ_cf) en ly S Hp W regs mem md k /\ pf_spill en W mem /\ pf_vregs en regs /\
  pf_lregs en regs i /\
  exists Fd Lam Dr Fr,
    pf_acct B FX en ly S Hp W mem Fd (Fr ++ fn_own nd) Lam /\
    pf_vnode B en nd ly S Lam W mem /\
    Permutation (fe_D en) (Fd ++ Dr ++ fn_own nd) /\
    pf_oitemsR SEGS (rdW W mem) (prh_lin Lam) (pj_foR SEGS (rdW W mem) (prh_lin Lam) d') (fn_ks nd)
      (fn_kids nd + 56 * (i + 1)) (fn_keys nd + 8 * (i + 1)) (Z.to_nat (fn_n nd - (i + 1))) Dr Fr.

(* the key's free: +0xf0 .. the key's fuzz_free (or none: an array's keys = NULL) .. +0x130 *)
Definition pfs_LK (PB : astate -> Prop) (FX : pf_obs) (CTX0 : list (list Z)) (d' : nat) : Prop :=
  forall en nd i ly S Hp W regs mem md k, pf_pre B ARx PB FX CTX0 en -> pf_node en nd ->
  pf_LK FX en nd d' i ly S Hp W regs mem md k ->
  (forall ly1 S1 Hp1 W1 regs1 mem1 md1 k1, pf_LC FX en nd d' i ly1 S1 Hp1 W1 regs1 mem1 md1 k1 ->
     SRr' SEGS RZ_cf W1 (pf_cfg PJF_LC regs1 mem1 md1) (pf_FIN (SK := SK) B ARx FX en)) ->
  SRr' SEGS RZ_cf W (pf_cfg PJF_LK regs mem md) (pf_FIN (SK := SK) B ARx FX en).

(* the bound test: +0x130 .. `bltu s10, a0` -> pf_LH (i + 1) at +0xa8 or pf_LX at +0x14c *)
Definition pfs_LC (PB : astate -> Prop) (FX : pf_obs) (CTX0 : list (list Z)) (d' : nat) : Prop :=
  forall en nd i ly S Hp W regs mem md k, pf_pre B ARx PB FX CTX0 en -> pf_node en nd ->
  pf_LC FX en nd d' i ly S Hp W regs mem md k ->
  (forall ly1 S1 Hp1 W1 regs1 mem1 md1 k1, pf_LH (SK := SK) B ARx FX en nd d' (i + 1) ly1 S1 Hp1 W1 regs1 mem1 md1 k1 ->
     SRr' SEGS RZ_cf W1 (pf_cfg PJF_LH regs1 mem1 md1) (pf_FIN (SK := SK) B ARx FX en)) ->
  (forall ly1 S1 Hp1 W1 regs1 mem1 md1 k1, pf_LX (SK := SK) B ARx FX en nd ly1 S1 Hp1 W1 regs1 mem1 md1 k1 ->
     SRr' SEGS RZ_cf W1 (pf_cfg PJF_LX regs1 mem1 md1) (pf_FIN (SK := SK) B ARx FX en)) ->
  SRr' SEGS RZ_cf W (pf_cfg PJF_LC regs mem md) (pf_FIN (SK := SK) B ARx FX en).
End c.
