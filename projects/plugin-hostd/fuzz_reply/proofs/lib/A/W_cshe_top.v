(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the function theorem of fuzz_reply's check_shape_ends (0x853b0),
   pb_check_shape_ends : cshe_spec B MT G A_csheP (W_contract.v Section w3e), composed from the walk's segments:
     held.n = 0                      cshe_n0_x                                (W_check_shape_ends.v)
     held.n > 0, entry and loop 1    cshe_to_tst_x, to the 0x85498 state       (W_check_shape_ends.v)
       g_gone <> 0                   cshe_gone_l2_x, then loop 2: cshe_l2_run_x (W_check_shape_ends.v, W_cshe_l2w.v)
       g_gone = 0, want = 0          cshe_want0_x                             (W_check_shape_ends.v)
       g_gone = 0, want > 0          cshe_gone_l3_x, then loop 3: cshe_l3_top_x (W_check_shape_ends.v, W_cshe_l3.v)
   THE GENERIC WALK (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): pb_check_shape_ends_x : cshe_spec_x B PST ARx MT
   G A_csheP over any allocator relation ARx with its laws, in W_check_shape_ends.v's generic Section header plus the
   free rule's caller-context form (CTX_AFREE, one singleton per free site: loop 2's HCTX_cshe_l2, loop 3's
   HCTX_cshe_l3).  THE AR STATEMENT (Section cAR) is re-derived from it at ARx := ARi0, PST := [], its conclusion and
   Section hypotheses byte-identical to the AR walk's but LX0 (the laws at ARi0) in place of LAWS. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_sites W_frame W_check_shape_ends W_cshe_l2w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_contract_x W_sites_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_g6.
(* loop 3's top lemma, cshe_l3_top_x (a Theorem Labs lane, converted).  Require only: its file's loop names stay qualified. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_cshe_l3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* The read-only view across a run that changes no image byte (the image lies below 0x5fb000). *)
Lemma top_rom_view_kept : forall (W W' : world SEGS) mem mem' lo hi,
0x5fb000 <= lo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
rom_view SEGS W mem -> rom_view SEGS W' mem'.
Proof.
intros W W' mem mem' lo hi Hlo Hk Hr a Ha.
assert (Hi : in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hs); exists sg; split; [exact Hsg | exact Hs]).
pose proof (pa_img_range a Hi) as Hb.
rewrite (Hk a ltac:(lia) ltac:(lia)). exact (Hr a Ha).
Qed.

(* ---- THE GENERIC WALK: W_check_shape_ends.v's generic Section header, with the free rule's caller-context form
   and the two free sites' context singletons (W_cshe_l2w.v HCTX_cshe_l2, W_cshe_l3.v HCTX_cshe_l3). ---- *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): cshe_spec_x's room record *)
Variable RP : roomp.
Variable G : list (Z * Z).
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis FRMF : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.
Hypothesis ML : ameter_laws MT.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis TL : PALib B.
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Variable CTX_AFREE : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
(* the two free sites' call contexts: loop 2's free (0x85518, ra 0x8551c), loop 3's (0x85628, ra 0x8562c) *)
Hypothesis HCTX_cshe_l2 : In [BASE + AF_fr_check_shape_ends + 0x16c] CTX_AFREE.
Hypothesis HCTX_cshe_l3 : In [BASE + AF_fr_check_shape_ends + 0x27c] CTX_AFREE.
Hypothesis NL : nl_spec_x B PST ARx (BASE + AF_fr_next_line).
Hypothesis LFIND : lfind_spec_x B PST ARx G (BASE + AF_fr_list_find).
Hypothesis ALDROP : forall ly S W mem ly' S' W' mem' LA l lines i,
alist_at B ly S W mem LA l lines ->
(i < length (HarnessRep.hl_recs l))%nat ->
(exists b1 b2, ablocks B ly S = b1 ++ (fst (nth i (HarnessRep.hl_recs l) (0, [])),
   Z.of_nat (length (snd (nth i (HarnessRep.hl_recs l) (0, [])))) + 1) :: b2 /\ ablocks B ly' S' = b1 ++ b2) ->
(forall a, LA <= a < LA + 8 \/ LA + 12 <= a < LA + 16 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
awr W' mem' LA 16 ->
val_mem SEGS (arm W' mem') (LA + 8) 4 (HarnessRep.hl_n l - 1) ->
(forall k, 0 <= k < AREC * (HarnessRep.hl_n l - 1 - Z.of_nat i) ->
 aview SEGS (w_H W') mem' (HarnessRep.hl_v l + AREC * Z.of_nat i + k) =
 aview SEGS (w_H W) mem (HarnessRep.hl_v l + AREC * Z.of_nat i + AREC + k)) ->
(forall a, HarnessRep.hl_v l <= a < HarnessRep.hl_v l + AREC * Z.of_nat i \/
 HarnessRep.hl_v l + AREC * (HarnessRep.hl_n l - 1) <= a < HarnessRep.hl_v l + AREC * HarnessRep.hl_cap l ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
(forall r, In r (HarnessRep.hl_recs (ldrop_list l i)) -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
alist_at B ly' S' W' mem' LA (ldrop_list l i) lines.
Hypothesis PLACEG0 : VAL A_g_gone + 1 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= VAL A_g_gone.
Hypothesis PLACEG32 : VAL A_g_gone + 1 <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= VAL A_g_gone.
Hypothesis HGR : gx_ok SEGS B cshe_ro.
Hypothesis HGRR : gx_rt B cshe_ro.
Hypothesis ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a).
Hypothesis HEND5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_rom SEGS a.
Hypothesis HEND5S : ashp_x ARx (VAL A_lit_end5) 4.
Hypothesis HGS : forall a, VAL (A_OBJ 22) <= a < VAL (A_OBJ 22) + 384 -> in_img SEGS a /\ ~ in_rom SEGS a /\
  ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\ ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\
  ~ (VAL A_g_out <= a < VAL A_g_out + 8).

(* Loop 3 (0x8559c, the `while (want-- > 0)` loop, through the epilogue) to cshe_post_x's g_gone = 0 case, from
   cshe_spec_x's premises, the branch (g_gone = 0, want > 0) and the state cshe_gone_l3_x leaves at the loop head:
   a Theorem Labs lane's loop 3 (W_cshe_l3.v), converted. *)
Let L3 := W_cshe_l3.cshe_l3_top_x B PST ARx MT RP G LAWS HP0 IMGC BLKN HPST FRMF ML HG TL ASTRLEN ABCMP AMOVE CTX_AFREE AFREE
  HCTX_cshe_l3 NL LFIND ALDROP PLACEG0 PLACEG32 HGR HGRR ROMNS HEND5R HEND5S HGS.

(* The strict proof stays: the R theorem pb_check_shape_ends_xR below takes the loops' R twins as Section hypotheses
   (L2R / L3R, over the free rule at R, AFREE_R), and no strict hypothesis gives them. *)
Theorem pb_check_shape_ends_x : cshe_spec_x B PST ARx MT RP G A_csheP.
Proof.
unfold cshe_spec_x. cbv zeta.
intros W ly S hp regs mem md ch XO AT HA j PF h P A0 gone O OUT ob
  HPRE HXO0 HXO16 HXtop HXp H10 H11 H12 HSRC Hal8 Hlo HAhiK HGin Hzs EHA Hj HAoff HAhome HND HnH
  HVoff HRoff HAT8 HATlo HAThi HATra MAT HPnz HP32 HPF0 HPFk HPby HPnul HPvis HPmr1 HPmr8 HPra1 HPshv1
  HPhome HE5 HROM Mg Rg MO MOUT HOB HOlen HO40 HO32 HOmr HOblk HA0 HFN HMO kr HRM HCNT.
(* the room round: the room budget is one free per held record (MT_rk charges 1 a free), and check_shape_ends' peak
   is 0 (cshe_pk), so its count premise is the one-call count premise cnt_ok *)
assert (Ecost : Z.to_nat (cshe_cost MT_rk (hs_held h)) = length (hl_recs (hs_held h))).
{ unfold cshe_cost, hl_n. cbn [mo_free MT_rk]. rewrite Z.mul_1_r. apply Nat2Z.id. }
rewrite Ecost in HRM.
assert (HCNT0 : cnt_ok RP (ablocks B ly S)) by exact HCNT.
assert (HRMk : rp_RM RP S kr) by exact (RMM_of RP S kr (length (hl_recs (hs_held h)) + kr) ltac:(lia) HRM).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hshlo & Hshhi & H47 & Hbot & Htop & Htop2).
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (HCL0 : alloc_ceiling + CSHE_STK <= spZ regs) by lia.
assert (HCEIL : alloc_ceiling <= spZ regs - 144) by lia.
assert (HSP47 : spZ regs <= 2 ^ 47) by lia.
destruct (Z.eq_dec (hl_n (hs_held h)) 0) as [HN0 | HNn0].
{ (* held.n = 0 *)
  exact (cshe_n0_x B PST ARx MT RP G LAWS IMGC BLKN ML HG TL PLACEG0 PLACEG32 HGR HGRR HGS W ly S hp regs mem md ch XO AT HA j
    PF h P A0 gone ob
    HPRE HXO0 HXO16 HXtop HXp H10 H11 H12 HSRC Hal8 Hlo HGin Hzs EHA Hj HND HnH HAT8 HATlo HAThi MAT Mg Rg HN0 kr HRMk). }
assert (HNp : 0 < hl_n (hs_held h))
  by (pose proof (Zle_0_nat (length (hl_recs (hs_held h)))); unfold hl_n in *; lia).
assert (Hj3 : Z.of_nat j <= 3) by lia.
assert (HAhi96 : HA + 96 <= 0x5fb000).
{ pose proof (pa_img_range (HA + 95) (proj1 (HGS (HA + 95) ltac:(rewrite EHA; unfold ASRC in *; lia)))). lia. }
assert (HAlo10 : 0x10000 <= HA).
{ pose proof (pa_img_range HA (proj1 (HGS HA ltac:(rewrite EHA; unfold ASRC in *; lia)))). lia. }
assert (HROg : inG cshe_ro (VAL A_g_gone)).
{ unfold inG, cshe_ro. apply Exists_exists. exists (VAL A_g_gone, 1).
  split; [cbn [In]; left; reflexivity|]. unfold in_zr. cbn [fst snd]. lia. }
assert (HGrange : 0x10000 <= VAL A_g_gone < 0x5fb000)
  by (pose proof (pa_img_range (VAL A_g_gone) (proj1 (HGR (VAL A_g_gone) HROg))); lia).
(* the entry and loop 1, to the 0x85498 state *)
eapply SRr_bind.
{ exact (cshe_to_tst_x B PST ARx G LAWS HP0 IMGC BLKN HG TL ASTRLEN ABCMP PLACEG0 PLACEG32 HGR HGRR HGS W ly S hp regs mem
    md ch XO AT HA j PF h
    P A0 gone HPRE HXO0 HXO16 HXtop HXp H10 H11 H12 HSRC Hal8 Hlo HGin Hzs EHA Hj HnH HVoff HRoff HATlo HAThi MAT
    HPnz HP32 HPF0 HPFk HPby HPnul HPvis HPmr1 HPmr8 HPra1 HPshv1 HROM Mg Rg HNp). }
cbv beta. intros W1 c1 Hwle1 (regs1 & mem1 & md1 & a0v & s5v & -> & HJ1 & HR & HK & R3 & R4 & HSAV1 & MN1 & M161 & Mg1
  & MAT1 & HFP1 & HSRC1 & KEEPB & PRES1 & HERR1).
pose proof HR as (T2 & T8 & T9 & T10 & T11 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27).
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
assert (HAR1 : ARx ly S hp W1 mem1 md1) by (eapply ajournal_gx_AR_x; exact HJ1).
assert (ROM1 : rom_view SEGS W1 mem1)
  by exact (top_rom_view_kept W W1 mem mem1 (spZ regs - CSHE_STK) (spZ regs) ltac:(lia) KEEPB HROM).
destruct (Z.eq_dec gone 0) as [Hg0 | Hgn0].
2:{ (* g_gone <> 0: the test, then loop 2 *)
  eapply SRr_bind.
  { exact (cshe_gone_l2_x B PST ARx G LAWS HG TL W1 ly S hp regs1 mem1 md1 ly S hp W mem md XO AT _ (spZ regs) 0 HA PF _ _
      _ gone _ a0v s5v _ HR HK MN1 Mg1 HFP1 Hgn0 HXO16 HCL0 HJ1 HERR1). }
  cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJ2 & KEEP2 & PRES2 & S2 & S3 & S4 & S8 & S9 & S11 & S18
    & S19 & S24 & S25 & S26 & S20 & S21 & S22 & S23 & S27 & HERR2).
  assert (SRC2 : asrc_at B ly S W2 mem2 HA h).
  { apply (cshe_src_kept_x B ARx LAWS IMGC BLKN ly S hp W1 W2 mem1 mem2 md1 HA h (spZ regs - 144) HAR1 HSRC1 HAlo10 HAhi96
      HCEIL Hwle2); [intros a Ha; apply KEEP2; lia | exact PRES2]. }
  assert (ROM2 : rom_view SEGS W2 mem2)
    by exact (top_rom_view_kept W1 W2 mem1 mem2 0x5fb000 0x5fb000 ltac:(lia) (fun a Ha _ => KEEP2 a Ha) ROM1).
  assert (SAV2 : cshe_saved W2 mem2 (spZ regs) regs).
  { apply (cshe_saved_kept W1 W2 mem1 mem2 (spZ regs) regs); [|exact HSAV1]. intros a Ha. apply KEEP2. lia. }
  assert (M162 : val_mem SEGS (arm W2 mem2) (spZ regs - 144 + 16) 8 ((HA + 88) / 8 + SB)).
  { replace (spZ regs - 144 + 16) with (spZ regs - 128) by lia.
    apply (cshe_vm_keep W1 W2 mem1 mem2 (spZ regs - 128) 8 ((HA + 88) / 8 + SB)); [|exact M161].
    intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KEEP2. lia. }
  assert (MAT2 : val_mem SEGS (arm W2 mem2) AT 8 A0).
  { apply (cshe_vm_keep W1 W2 mem1 mem2 AT 8 A0); [|exact MAT1].
    intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KEEP2. lia. }
  assert (Mg2 : val_mem SEGS (arm W2 mem2) (VAL A_g_gone) 1 gone).
  { apply (cshe_vm_keep W1 W2 mem1 mem2 (VAL A_g_gone) 1 gone); [|exact Mg1].
    intros x Hx. change (Z.of_nat 1) with 1 in Hx. apply KEEP2. lia. }
  apply (cshe_l2_run_x B PST ARx MT RP G LAWS HP0 IMGC BLKN FRMF ML HG TL ASTRLEN ABCMP AMOVE CTX_AFREE AFREE HCTX_cshe_l2
    ALDROP PLACEG0 PLACEG32 HGR HGRR ROMNS HGS
    regs ly S hp W mem md ch XO AT HA PF A0 gone j h P ob kr
    HPRE HXO16 HXtop HATlo HAThi HSRC Hal8 Hlo HAhiK HGin Hzs EHA Hj HND HnH HPnz HP32 HPF0 HPFk HPby HPnul HPvis
    HPmr1 HPmr8 HPra1 HPhome HROM Hgn0 HMO W2 hp regs2 mem2 md2 0);
  [ exact HJ2 | exact SRC2 | exact ROM2 | exact SAV2 | exact M162 | exact MAT2 | exact Mg2 | exact HERR2 | exact HNp
  | rewrite S2; exact T2 | rewrite S3; exact R3 | rewrite S4; exact R4 | rewrite S8; exact T8
  | rewrite S9; exact T9 | rewrite S18; exact T18 | exact S20 | exact S21 | exact S22 | exact S23
  | rewrite S25; exact T25 | rewrite S26; exact T26 | exact S27 | exact HRM | exact HCNT0 ]. }
destruct (Nat.eq_dec (CheckRep.want_of P (hl_recs (hs_held h))) 0) as [HW0 | HWn0].
{ (* g_gone = 0, want = 0: straight to the epilogue *)
  rewrite HW0 in HR, HK.
  exact (cshe_want0_x B PST ARx MT RP G LAWS ML HG W1 ly S hp regs1 mem1 md1 W regs mem md XO AT HA PF _ _ _ gone _ a0v s5v
    h P A0 ob
    HR HK R3 R4 MN1 Mg1 HFP1 Hg0 HW0 HXO16 HCL0 HSP47 Hal16 Hra HJ1 HSAV1 HSRC1 HND MAT1 HERR1 kr HRMk). }
(* g_gone = 0, want > 0: the test, then loop 3 *)
assert (Hwp : 0 < Z.of_nat (CheckRep.want_of P (hl_recs (hs_held h)))) by lia.
assert (Hwn : Z.of_nat (CheckRep.want_of P (hl_recs (hs_held h))) <> 0) by lia.
eapply SRr_bind.
{ exact (cshe_gone_l3_x B PST ARx G LAWS HG TL W1 ly S hp regs1 mem1 md1 ly S hp W mem md XO AT _ (spZ regs) 0 HA PF _ _ _
    gone _ a0v s5v _ HR HK MN1 Mg1 HFP1 Hg0 Hwn HXO16 HCL0 HJ1 HERR1). }
cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJ2 & KEEP2 & PRES2 & M82 & S2 & S3 & S4 & S8 & S9 & S18
  & S19 & S21 & S22 & S23 & S25 & S26 & S10 & S20 & S24 & S27 & HERR2).
assert (Hwle : wle W W2) by (eapply wle_trans; [exact Hwle1 | exact Hwle2]).
assert (KEEPW2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSHE_STK <= a < spZ regs) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno. rewrite (KEEP2 a Ha ltac:(lia)). exact (KEEPB a Ha Hno). }
assert (PRESW2 : forall a, apresent (w_H W) mem a -> apresent (w_H W2) mem2 a)
  by (intros a Hp; exact (PRES2 a (PRES1 a Hp))).
assert (FP2 : forall a, spZ regs - 144 <= a < spZ regs -> apresent (w_H W2) mem2 a)
  by (intros a Ha; exact (PRES2 a (HFP1 a Ha))).
assert (SRC2 : asrc_at B ly S W2 mem2 HA h).
{ apply (cshe_src_kept_x B ARx LAWS IMGC BLKN ly S hp W1 W2 mem1 mem2 md1 HA h (spZ regs - 144) HAR1 HSRC1 HAlo10 HAhi96
    HCEIL Hwle2); [intros a Ha; apply KEEP2; lia | exact PRES2]. }
assert (ROM2 : rom_view SEGS W2 mem2)
  by exact (top_rom_view_kept W W2 mem mem2 (spZ regs - CSHE_STK) (spZ regs) ltac:(lia) KEEPW2 HROM).
assert (SAV2 : cshe_saved W2 mem2 (spZ regs) regs).
{ apply (cshe_saved_kept W1 W2 mem1 mem2 (spZ regs) regs); [|exact HSAV1]. intros a Ha. apply KEEP2; lia. }
assert (M8 : val_mem SEGS (arm W2 mem2) (spZ regs - 144 + 8) 8 3).
{ replace (spZ regs - 144 + 8) with (spZ regs - 136) by lia. exact M82. }
assert (M162 : val_mem SEGS (arm W2 mem2) (spZ regs - 144 + 16) 8 ((HA + 88) / 8 + SB)).
{ replace (spZ regs - 144 + 16) with (spZ regs - 128) by lia.
  apply (cshe_vm_keep W1 W2 mem1 mem2 (spZ regs - 128) 8 ((HA + 88) / 8 + SB)); [|exact M161].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KEEP2; lia. }
assert (MAT2 : val_mem SEGS (arm W2 mem2) AT 8 A0).
{ apply (cshe_vm_keep W1 W2 mem1 mem2 AT 8 A0); [|exact MAT1].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KEEP2; lia. }
assert (Mg2 : val_mem SEGS (arm W2 mem2) (VAL A_g_gone) 1 gone).
{ apply (cshe_vm_keep W1 W2 mem1 mem2 (VAL A_g_gone) 1 gone); [|exact Mg1].
  intros x Hx. change (Z.of_nat 1) with 1 in Hx. apply KEEP2; lia. }
assert (U2 : getr regs2 2 = w64 (spZ regs - 144)) by (rewrite S2; exact T2).
assert (U3 : getr regs2 3 = getr regs 3) by (rewrite S3; exact R3).
assert (U4 : getr regs2 4 = getr regs 4) by (rewrite S4; exact R4).
assert (U8 : getr regs2 8 = w64 (HA + 88)) by (rewrite S8; exact T8).
assert (U9 : getr regs2 9 = w64 PF) by (rewrite S9; exact T9).
assert (U18 : getr regs2 18 = w64 (HA + 80)) by (rewrite S18; exact T18).
assert (U19 : getr regs2 19 = w64 AT) by (rewrite S19; exact T19).
assert (U21 : getr regs2 21 = w64 s5v) by (rewrite S21; exact T21).
assert (U22 : getr regs2 22 = w64 0) by (rewrite S22; exact T22).
assert (U23 : getr regs2 23 = w64 (SB + (hl_v (hs_held h) + AREC * hl_n (hs_held h)) / 8))
  by (rewrite S23; exact T23).
assert (U25 : getr regs2 25 = w64 SB) by (rewrite S25; exact T25).
assert (U26 : getr regs2 26 = w64 ((HA + 80) / 8 + SB)) by (rewrite S26; exact T26).
pose proof (L3 W ly S hp regs mem md ch XO AT HA j PF h P A0 gone O OUT ob W2 hp regs2 mem2 md2 s5v) as L3i.
cbv zeta in L3i.
assert (Hs5 : 0 <= Z.of_nat (CheckRep.want_of P (hl_recs (hs_held h))) - s5v <= 2) by lia.
apply L3i; assumption.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): pb_check_shape_ends_x at a world relation R, cshe_spec_xR (W_contract_xR_g6.v).
   The free calls are inside loops 2 and 3; their R twins are this Section's hypotheses L2R / L3R: each is the loop's
   strict lemma (W_cshe_l2w.v cshe_l2_run_x, closed over its Section loop and with its notations expanded; W_cshe_l3.v
   cshe_l3_top_x) with ajournal_gx_x -> ajournal_gx_xR R, SRr -> SRrG SEGS R, cshe_post_x -> cshe_post_xR R, and in
   L3R the premise `wle W W1` -> `R W W1` (the loop head is reached by SRrG_bind).  The loops' R proofs use the free
   rule at R (AFREE_R over RO, with RO_ARx); no step of the composition below calls it, so while L2R / L3R are
   hypotheses the theorem does not take AFREE_R, RO or RO_ARx.  The segments between are W_check_shape_ends.v's R
   twins, composed by SRrG_bind; the source is carried over the test segments by cshe_src_kept_xR. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* loop 2 at R: W_cshe_l2w.v cshe_l2_run_x (inside its Section loop), closed over the 19 Section loop variables and the
   29 Section loop hypotheses in their order there *)
Hypothesis L2R : forall (regs0 : bvmap 5 word) (ly : alayout) (S : astate) (hp : list Z) (W : world SEGS)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (XO AT HA PF A0 gone : Z) (j : nat) (h : hsrc)
  (P ob : list byte) (kr : nat),
afn_pre_x SEGS B ARx CSHE_STK ly S hp W regs0 mem md ch ->
XO mod 16 = 0 ->
(spZ regs0) + XO <= ly_top ly ->
(spZ regs0) <= AT ->
AT + 8 <= (spZ regs0) + XO ->
asrc_at B ly S W mem HA h ->
HA mod 8 = 0 ->
4096 <= HA ->
HA + ASRC <= kLowMemEnd ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) ->
azs B (HA + 64) 32 ->
HA = VAL (A_OBJ 22) + ASRC * Z.of_nat j ->
(j < 4)%nat ->
NoDup (CheckRep.texts (hs_held h)) ->
hl_n (hs_held h) < 2 ^ 26 ->
~ In (Z_to_bv 8 0) P ->
Z.of_nat (length P) + 1 < 2 ^ 32 ->
0 < PF ->
PF + Z.of_nat (length P) + 8 <= 2 ^ 63 ->
(forall i, 0 <= i < Z.of_nat (length P) -> aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0)))) ->
aview SEGS (w_H W) mem (PF + Z.of_nat (length P)) = Some 0 ->
(forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> aview SEGS (w_H W) mem a <> None /\ ~ ((spZ regs0) - CSHE_STK <= a < (spZ regs0) + XO)) ->
amem_range PF (Z.of_nat (length P) + 1) ->
amem_range PF 8 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (Z.of_nat (length P) + 1) ->
((forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (Z.of_nat (length P) + 1) \/ exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> in_zr a (frame_rng ly (cid, pos))) ->
rom_view SEGS W mem ->
gone <> 0 ->
mo_ok MT S (cshe_cost MT (hs_held h)) ->
forall W1 hp1 regs1 mem1 md1 kk,
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CSHE_STK (spZ regs0) (blk_FP (list_blks (hs_held h))) ly S hp W mem md [] ly S hp1 W1 mem1 md1 kk ->
asrc_at B ly S W1 mem1 HA h -> rom_view SEGS W1 mem1 -> cshe_saved W1 mem1 (spZ regs0) regs0 ->
val_mem SEGS (arm W1 mem1) ((spZ regs0) - 144 + 16) 8 ((HA + 88) / 8 + SB) ->
val_mem SEGS (arm W1 mem1) AT 8 A0 -> val_mem SEGS (arm W1 mem1) (VAL A_g_gone) 1 gone ->
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) ->
0 < hl_n (hs_held h) ->
getr regs1 2 = w64 ((spZ regs0) - 144) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 8 = w64 (HA + 88) -> getr regs1 9 = w64 PF -> getr regs1 18 = w64 (HA + 80) ->
getr regs1 20 = w64 (hl_n (hs_held h) + 1) -> getr regs1 21 = w64 (- hl_n (hs_held h)) -> getr regs1 22 = w64 1 ->
getr regs1 23 = w64 (AREC * (hl_n (hs_held h) - 1)) -> getr regs1 25 = w64 SB ->
getr regs1 26 = w64 ((HA + 80) / 8 + SB) -> getr regs1 27 = w64 3 ->
(* the room round: one free per held record past the caller's kr, and the live counts at the loop's head *)
rp_RM RP S (length (hl_recs (hs_held h)) + kr) -> cnt_ok RP (ablocks B ly S) ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l2)) mem1 (seg_rom SEGS)) md1) (cshe_post_xR B PST ARx R MT RP G regs0 ly S hp W mem md XO AT HA h P A0 gone ob kr).
(* loop 3 at R: W_cshe_l3.v cshe_l3_top_x *)
Hypothesis L3R : forall W ly S hp regs mem md ch XO AT HA (j : nat) PF h P A0 gone O OUT ob
  (W1 : world SEGS) hp1 regs1 mem1 md1 s5v,
let H := hs_held h in
let PLEN := Z.of_nat (length P) in
let want := Z.of_nat (CheckRep.want_of P (hl_recs H)) in
afn_pre_x SEGS B ARx CSHE_STK ly S hp W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
getr regs 10 = w64 HA -> getr regs 11 = w64 PF -> getr regs 12 = w64 AT ->
asrc_at B ly S W mem HA h ->
HA mod 8 = 0 -> 4096 <= HA -> HA + ASRC <= kLowMemEnd ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
HA = VAL (A_OBJ 22) + ASRC * Z.of_nat j -> (j < 4)%nat ->
(forall a, HA <= a < HA + ASRC -> ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
(forall a, HA <= a < HA + ASRC -> cshe_home B ly S a) ->
NoDup (CheckRep.texts H) ->
hl_n H < 2 ^ 26 ->
(forall a, hl_v H <= a < hl_v H + AREC * hl_cap H -> ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
(forall r, In r (hl_recs H) -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 ->
  ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
AT mod 8 = 0 -> spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF AT 8 ->
val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
~ In (Z_to_bv 8 0) P -> PLEN + 1 < 2 ^ 32 -> 0 < PF -> PF + PLEN + 8 <= 2 ^ 63 ->
(forall i, 0 <= i < PLEN -> aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0)))) ->
aview SEGS (w_H W) mem (PF + PLEN) = Some 0 ->
(forall a, PF <= a < PF + PLEN + 8 -> aview SEGS (w_H W) mem a <> None /\
  ~ (spZ regs - CSHE_STK <= a < spZ regs + XO)) ->
amem_range PF (PLEN + 1) -> amem_range PF 8 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (PLEN + 1) ->
shadow_hull_vis (aview SEGS (w_H W) mem) PF (PLEN + 1) ->
((forall a, PF <= a < PF + PLEN + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (PLEN + 1) \/
 exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + PLEN + 8 -> in_zr a (frame_rng ly (cid, pos))) ->
garr8 SEGS (arm W mem) (VAL A_lit_end5) (bzs END5) -> rom_view SEGS W mem ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_nout) 8 O ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_out) 8 OUT ->
ob_at W mem OUT ob -> Z.of_nat (length ob) = O -> O <= 2 ^ 40 -> (0 < O -> O < 2 ^ 32) -> amem_range OUT (O + 8) ->
(ob = [] \/ exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly S) /\ ~ In OUT (hs_blocks h)) ->
0 <= A0 <= O ->
(gone = 0 -> CheckRep.ends_run P (hl_recs H) (skipn (Z.to_nat A0) ob) (CheckRep.want_of P (hl_recs H)) <> None) ->
mo_ok MT S (cshe_cost MT H) ->
(* the branch *)
gone = 0 -> 0 < want -> 0 < hl_n H ->
(* the state at loop 3's head 0x8559c *)
R W W1 ->
ajournal_gx_xR SEGS B PST ARx R G XO [(AT, AT + 8)] CSHE_STK (spZ regs) (blk_FP (list_blks H)) ly S hp W mem md [] ly S hp1 W1 mem1 md1 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSHE_STK <= a < spZ regs) ->
  aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W1) mem1 a) ->
(forall a, spZ regs - 144 <= a < spZ regs -> apresent (w_H W1) mem1 a) ->
asrc_at B ly S W1 mem1 HA h -> rom_view SEGS W1 mem1 -> cshe_saved W1 mem1 (spZ regs) regs ->
val_mem SEGS (arm W1 mem1) (spZ regs - 144 + 8) 8 3 ->
val_mem SEGS (arm W1 mem1) (spZ regs - 144 + 16) 8 ((HA + 88) / 8 + SB) ->
val_mem SEGS (arm W1 mem1) AT 8 A0 -> val_mem SEGS (arm W1 mem1) (VAL A_g_gone) 1 gone ->
(forall j, 0 <= j < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) ->
(* s5 (x21) still holds loop 1's s5v; 0x8557c computed want = a0 + s5 with 0 <= a0 <= 2 (cshe_tst_ok) *)
0 <= s5v < 2 ^ 26 -> 0 <= want - s5v <= 2 ->
getr regs1 2 = w64 (spZ regs - 144) -> getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
getr regs1 8 = w64 (HA + 88) -> getr regs1 9 = w64 PF -> getr regs1 10 = w64 want ->
getr regs1 18 = w64 (HA + 80) -> getr regs1 19 = w64 AT -> getr regs1 20 = w64 (VAL A_lit_end5) ->
getr regs1 21 = w64 s5v -> getr regs1 22 = w64 0 -> getr regs1 23 = w64 (SB + (hl_v H + AREC * hl_n H) / 8) ->
getr regs1 24 = w64 4 -> getr regs1 25 = w64 SB -> getr regs1 26 = w64 ((HA + 80) / 8 + SB) ->
getr regs1 27 = w64 (want + 1) ->
(* the room round: one free per held record past the caller's kr, and the live counts at the loop's head *)
forall kr : nat, rp_RM RP S (length (hl_recs H) + kr) -> cnt_ok RP (ablocks B ly S) ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cshe_l3)) mem1 (seg_rom SEGS)) md1)
  (cshe_post_xR B PST ARx R MT RP G regs ly S hp W mem md XO AT HA h P A0 gone ob kr).

Theorem pb_check_shape_ends_xR : cshe_spec_xR B PST ARx R MT RP G A_csheP.
Proof.
unfold cshe_spec_xR. cbv zeta.
intros W ly S hp regs mem md ch XO AT HA j PF h P A0 gone O OUT ob
  HPRE HXO0 HXO16 HXtop HXp H10 H11 H12 HSRC Hal8 Hlo HAhiK HGin Hzs EHA Hj HAoff HAhome HND HnH
  HVoff HRoff HAT8 HATlo HAThi HATra MAT HPnz HP32 HPF0 HPFk HPby HPnul HPvis HPmr1 HPmr8 HPra1 HPshv1
  HPhome HE5 HROM Mg Rg MO MOUT HOB HOlen HO40 HO32 HOmr HOblk HA0 HFN HMO kr HRM HCNT.
(* the room round, as in pb_check_shape_ends_x *)
assert (Ecost : Z.to_nat (cshe_cost MT_rk (hs_held h)) = length (hl_recs (hs_held h))).
{ unfold cshe_cost, hl_n. cbn [mo_free MT_rk]. rewrite Z.mul_1_r. apply Nat2Z.id. }
rewrite Ecost in HRM.
assert (HCNT0 : cnt_ok RP (ablocks B ly S)) by exact HCNT.
assert (HRMk : rp_RM RP S kr) by exact (RMM_of RP S kr (length (hl_recs (hs_held h)) + kr) ltac:(lia) HRM).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hshlo & Hshhi & H47 & Hbot & Htop & Htop2).
assert (WS : CSHE_STK = 16528) by reflexivity.
assert (HCL0 : alloc_ceiling + CSHE_STK <= spZ regs) by lia.
assert (HCEIL : alloc_ceiling <= spZ regs - 144) by lia.
assert (HSP47 : spZ regs <= 2 ^ 47) by lia.
destruct (Z.eq_dec (hl_n (hs_held h)) 0) as [HN0 | HNn0].
{ (* held.n = 0 *)
  exact (cshe_n0_xR B PST ARx MT RP G LAWS IMGC BLKN ML HG TL PLACEG0 PLACEG32 HGR HGRR HGS R R_trans WLE_R
    W ly S hp regs mem md ch XO AT HA j PF h P A0 gone ob
    HPRE HXO0 HXO16 HXtop HXp H10 H11 H12 HSRC Hal8 Hlo HGin Hzs EHA Hj HND HnH HAT8 HATlo HAThi MAT Mg Rg HN0 kr HRMk). }
assert (HNp : 0 < hl_n (hs_held h))
  by (pose proof (Zle_0_nat (length (hl_recs (hs_held h)))); unfold hl_n in *; lia).
assert (Hj3 : Z.of_nat j <= 3) by lia.
assert (HAhi96 : HA + 96 <= 0x5fb000).
{ pose proof (pa_img_range (HA + 95) (proj1 (HGS (HA + 95) ltac:(rewrite EHA; unfold ASRC in *; lia)))). lia. }
assert (HAlo10 : 0x10000 <= HA).
{ pose proof (pa_img_range HA (proj1 (HGS HA ltac:(rewrite EHA; unfold ASRC in *; lia)))). lia. }
assert (HROg : inG cshe_ro (VAL A_g_gone)).
{ unfold inG, cshe_ro. apply Exists_exists. exists (VAL A_g_gone, 1).
  split; [cbn [In]; left; reflexivity|]. unfold in_zr. cbn [fst snd]. lia. }
assert (HGrange : 0x10000 <= VAL A_g_gone < 0x5fb000)
  by (pose proof (pa_img_range (VAL A_g_gone) (proj1 (HGR (VAL A_g_gone) HROg))); lia).
(* the entry and loop 1, to the 0x85498 state *)
eapply (SRrG_bind SEGS R R_trans).
{ exact (cshe_to_tst_xR B PST ARx G LAWS HP0 IMGC BLKN HG TL ASTRLEN ABCMP PLACEG0 PLACEG32 HGR HGRR HGS R WLE_R
    W ly S hp regs mem md ch XO AT HA j PF h P A0 gone
    HPRE HXO0 HXO16 HXtop HXp H10 H11 H12 HSRC Hal8 Hlo HGin Hzs EHA Hj HnH HVoff HRoff HATlo HAThi MAT
    HPnz HP32 HPF0 HPFk HPby HPnul HPvis HPmr1 HPmr8 HPra1 HPshv1 HROM Mg Rg HNp). }
cbv beta. intros W1 c1 Hwle1 (regs1 & mem1 & md1 & a0v & s5v & -> & HJ1 & HR & HK & R3 & R4 & HSAV1 & MN1 & M161 & Mg1
  & MAT1 & HFP1 & HSRC1 & KEEPB & PRES1 & HERR1).
pose proof HR as (T2 & T8 & T9 & T10 & T11 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27).
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
assert (HAR1 : ARx ly S hp W1 mem1 md1) by (eapply ajournal_gx_AR_xR; exact HJ1).
assert (ROM1 : rom_view SEGS W1 mem1)
  by exact (top_rom_view_kept W W1 mem mem1 (spZ regs - CSHE_STK) (spZ regs) ltac:(lia) KEEPB HROM).
destruct (Z.eq_dec gone 0) as [Hg0 | Hgn0].
2:{ (* g_gone <> 0: the test, then loop 2 *)
  eapply (SRrG_bind SEGS R R_trans).
  { exact (cshe_gone_l2_xR B PST ARx G LAWS HG TL R WLE_R W1 ly S hp regs1 mem1 md1 ly S hp W mem md XO AT _ (spZ regs) 0
      HA PF _ _ _ gone _ a0v s5v _ HR HK MN1 Mg1 HFP1 Hgn0 HXO16 HCL0 HJ1 HERR1). }
  cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJ2 & KEEP2 & PRES2 & S2 & S3 & S4 & S8 & S9 & S11 & S18
    & S19 & S24 & S25 & S26 & S20 & S21 & S22 & S23 & S27 & HERR2).
  assert (SRC2 : asrc_at B ly S W2 mem2 HA h).
  { apply (cshe_src_kept_xR B ARx LAWS IMGC BLKN R ly S hp W1 W2 mem1 mem2 md1 HA h (spZ regs - 144) HAR1 HSRC1
      HAlo10 HAhi96 HCEIL Hwle2); [intros a Ha; apply KEEP2; lia | exact PRES2]. }
  assert (ROM2 : rom_view SEGS W2 mem2)
    by exact (top_rom_view_kept W1 W2 mem1 mem2 0x5fb000 0x5fb000 ltac:(lia) (fun a Ha _ => KEEP2 a Ha) ROM1).
  assert (SAV2 : cshe_saved W2 mem2 (spZ regs) regs).
  { apply (cshe_saved_kept W1 W2 mem1 mem2 (spZ regs) regs); [|exact HSAV1]. intros a Ha. apply KEEP2. lia. }
  assert (M162 : val_mem SEGS (arm W2 mem2) (spZ regs - 144 + 16) 8 ((HA + 88) / 8 + SB)).
  { replace (spZ regs - 144 + 16) with (spZ regs - 128) by lia.
    apply (cshe_vm_keep W1 W2 mem1 mem2 (spZ regs - 128) 8 ((HA + 88) / 8 + SB)); [|exact M161].
    intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KEEP2. lia. }
  assert (MAT2 : val_mem SEGS (arm W2 mem2) AT 8 A0).
  { apply (cshe_vm_keep W1 W2 mem1 mem2 AT 8 A0); [|exact MAT1].
    intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KEEP2. lia. }
  assert (Mg2 : val_mem SEGS (arm W2 mem2) (VAL A_g_gone) 1 gone).
  { apply (cshe_vm_keep W1 W2 mem1 mem2 (VAL A_g_gone) 1 gone); [|exact Mg1].
    intros x Hx. change (Z.of_nat 1) with 1 in Hx. apply KEEP2. lia. }
  apply (L2R regs ly S hp W mem md ch XO AT HA PF A0 gone j h P ob kr
    HPRE HXO16 HXtop HATlo HAThi HSRC Hal8 Hlo HAhiK HGin Hzs EHA Hj HND HnH HPnz HP32 HPF0 HPFk HPby HPnul HPvis
    HPmr1 HPmr8 HPra1 HPhome HROM Hgn0 HMO W2 hp regs2 mem2 md2 0);
  [ exact HJ2 | exact SRC2 | exact ROM2 | exact SAV2 | exact M162 | exact MAT2 | exact Mg2 | exact HERR2 | exact HNp
  | rewrite S2; exact T2 | rewrite S3; exact R3 | rewrite S4; exact R4 | rewrite S8; exact T8
  | rewrite S9; exact T9 | rewrite S18; exact T18 | exact S20 | exact S21 | exact S22 | exact S23
  | rewrite S25; exact T25 | rewrite S26; exact T26 | exact S27 | exact HRM | exact HCNT0 ]. }
destruct (Nat.eq_dec (CheckRep.want_of P (hl_recs (hs_held h))) 0) as [HW0 | HWn0].
{ (* g_gone = 0, want = 0: straight to the epilogue *)
  rewrite HW0 in HR, HK.
  exact (cshe_want0_xR B PST ARx MT RP G LAWS ML HG R WLE_R W1 ly S hp regs1 mem1 md1 W regs mem md XO AT HA PF _ _ _
    gone _ a0v s5v h P A0 ob
    HR HK R3 R4 MN1 Mg1 HFP1 Hg0 HW0 HXO16 HCL0 HSP47 Hal16 Hra HJ1 HSAV1 HSRC1 HND MAT1 HERR1 kr HRMk). }
(* g_gone = 0, want > 0: the test, then loop 3 *)
assert (Hwp : 0 < Z.of_nat (CheckRep.want_of P (hl_recs (hs_held h)))) by lia.
assert (Hwn : Z.of_nat (CheckRep.want_of P (hl_recs (hs_held h))) <> 0) by lia.
eapply (SRrG_bind SEGS R R_trans).
{ exact (cshe_gone_l3_xR B PST ARx G LAWS HG TL R WLE_R W1 ly S hp regs1 mem1 md1 ly S hp W mem md XO AT _ (spZ regs) 0
    HA PF _ _ _ gone _ a0v s5v _ HR HK MN1 Mg1 HFP1 Hg0 Hwn HXO16 HCL0 HJ1 HERR1). }
cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJ2 & KEEP2 & PRES2 & M82 & S2 & S3 & S4 & S8 & S9 & S18
  & S19 & S21 & S22 & S23 & S25 & S26 & S10 & S20 & S24 & S27 & HERR2).
(* the world fact loop 3's head takes, now at R *)
assert (Hwle : R W W2) by (eapply R_trans; [exact Hwle1 | exact Hwle2]).
assert (KEEPW2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSHE_STK <= a < spZ regs) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno. rewrite (KEEP2 a Ha ltac:(lia)). exact (KEEPB a Ha Hno). }
assert (PRESW2 : forall a, apresent (w_H W) mem a -> apresent (w_H W2) mem2 a)
  by (intros a Hp; exact (PRES2 a (PRES1 a Hp))).
assert (FP2 : forall a, spZ regs - 144 <= a < spZ regs -> apresent (w_H W2) mem2 a)
  by (intros a Ha; exact (PRES2 a (HFP1 a Ha))).
assert (SRC2 : asrc_at B ly S W2 mem2 HA h).
{ apply (cshe_src_kept_xR B ARx LAWS IMGC BLKN R ly S hp W1 W2 mem1 mem2 md1 HA h (spZ regs - 144) HAR1 HSRC1
    HAlo10 HAhi96 HCEIL Hwle2); [intros a Ha; apply KEEP2; lia | exact PRES2]. }
assert (ROM2 : rom_view SEGS W2 mem2)
  by exact (top_rom_view_kept W W2 mem mem2 (spZ regs - CSHE_STK) (spZ regs) ltac:(lia) KEEPW2 HROM).
assert (SAV2 : cshe_saved W2 mem2 (spZ regs) regs).
{ apply (cshe_saved_kept W1 W2 mem1 mem2 (spZ regs) regs); [|exact HSAV1]. intros a Ha. apply KEEP2; lia. }
assert (M8 : val_mem SEGS (arm W2 mem2) (spZ regs - 144 + 8) 8 3).
{ replace (spZ regs - 144 + 8) with (spZ regs - 136) by lia. exact M82. }
assert (M162 : val_mem SEGS (arm W2 mem2) (spZ regs - 144 + 16) 8 ((HA + 88) / 8 + SB)).
{ replace (spZ regs - 144 + 16) with (spZ regs - 128) by lia.
  apply (cshe_vm_keep W1 W2 mem1 mem2 (spZ regs - 128) 8 ((HA + 88) / 8 + SB)); [|exact M161].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KEEP2; lia. }
assert (MAT2 : val_mem SEGS (arm W2 mem2) AT 8 A0).
{ apply (cshe_vm_keep W1 W2 mem1 mem2 AT 8 A0); [|exact MAT1].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KEEP2; lia. }
assert (Mg2 : val_mem SEGS (arm W2 mem2) (VAL A_g_gone) 1 gone).
{ apply (cshe_vm_keep W1 W2 mem1 mem2 (VAL A_g_gone) 1 gone); [|exact Mg1].
  intros x Hx. change (Z.of_nat 1) with 1 in Hx. apply KEEP2; lia. }
assert (U2 : getr regs2 2 = w64 (spZ regs - 144)) by (rewrite S2; exact T2).
assert (U3 : getr regs2 3 = getr regs 3) by (rewrite S3; exact R3).
assert (U4 : getr regs2 4 = getr regs 4) by (rewrite S4; exact R4).
assert (U8 : getr regs2 8 = w64 (HA + 88)) by (rewrite S8; exact T8).
assert (U9 : getr regs2 9 = w64 PF) by (rewrite S9; exact T9).
assert (U18 : getr regs2 18 = w64 (HA + 80)) by (rewrite S18; exact T18).
assert (U19 : getr regs2 19 = w64 AT) by (rewrite S19; exact T19).
assert (U21 : getr regs2 21 = w64 s5v) by (rewrite S21; exact T21).
assert (U22 : getr regs2 22 = w64 0) by (rewrite S22; exact T22).
assert (U23 : getr regs2 23 = w64 (SB + (hl_v (hs_held h) + AREC * hl_n (hs_held h)) / 8))
  by (rewrite S23; exact T23).
assert (U25 : getr regs2 25 = w64 SB) by (rewrite S25; exact T25).
assert (U26 : getr regs2 26 = w64 ((HA + 80) / 8 + SB)) by (rewrite S26; exact T26).
pose proof (L3R W ly S hp regs mem md ch XO AT HA j PF h P A0 gone O OUT ob W2 hp regs2 mem2 md2 s5v) as L3i.
cbv zeta in L3i.
assert (Hs5 : 0 <= Z.of_nat (CheckRep.want_of P (hl_recs (hs_held h))) - s5v <= 2) by lia.
apply L3i; assumption.
Qed.
End wR.
End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.-4.): pb_check_shape_ends' statement is the AR
   walk's, byte-identical, now a corollary of pb_check_shape_ends_x at ARx := ARi0 (cgif's AR with the head set
   empty), PST := [].  Its Section takes LX0 (the laws at ARi0, a Theorem Labs lane's ruling (a)) in place of LAWS: the instance
   builds it once, W_journal_x.AR_laws_x_ARi0.  The bridges are the kit's: W_contract_x cshe_spec_x_AR0 for the
   conclusion; astrlen_realizes_x_of_AR0, nl_spec_x_of_AR0, lfind_spec_x_of_AR0 (W_contract_x), abcmp_realizes_x_of_AR0,
   amemmove_realizes_x_of_AR0 (W_sites_x), and the free rule in its caller-context form at the two free sites' context
   CTX_cshe (W_journal.afree_cf_rule_c_weak, then W_journal_x.afree_cf_rule_c_x_of_AR0); ashp_x_ARi0_of for HEND5S.
   HP0 at ARi0 is ARi0_hp0; IMGC / BLKN are W_kit_x.AR_imgc / AR_blkn; FRMF is W_frame_x.FRMF_AR; HPST holds at
   PST = []. ---- *)
Section cAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable G : list (Z * Z).
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis ML : ameter_laws MT.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis TL : PALib B.
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA WS_bcmp).
Hypothesis AMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis NL : nl_spec B (BASE + AF_fr_next_line).
Hypothesis LFIND : lfind_spec B G (BASE + AF_fr_list_find).
Hypothesis ALDROP : forall ly S W mem ly' S' W' mem' LA l lines i,
alist_at B ly S W mem LA l lines ->
(i < length (HarnessRep.hl_recs l))%nat ->
(exists b1 b2, ablocks B ly S = b1 ++ (fst (nth i (HarnessRep.hl_recs l) (0, [])),
   Z.of_nat (length (snd (nth i (HarnessRep.hl_recs l) (0, [])))) + 1) :: b2 /\ ablocks B ly' S' = b1 ++ b2) ->
(forall a, LA <= a < LA + 8 \/ LA + 12 <= a < LA + 16 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
awr W' mem' LA 16 ->
val_mem SEGS (arm W' mem') (LA + 8) 4 (HarnessRep.hl_n l - 1) ->
(forall k, 0 <= k < AREC * (HarnessRep.hl_n l - 1 - Z.of_nat i) ->
 aview SEGS (w_H W') mem' (HarnessRep.hl_v l + AREC * Z.of_nat i + k) =
 aview SEGS (w_H W) mem (HarnessRep.hl_v l + AREC * Z.of_nat i + AREC + k)) ->
(forall a, HarnessRep.hl_v l <= a < HarnessRep.hl_v l + AREC * Z.of_nat i \/
 HarnessRep.hl_v l + AREC * (HarnessRep.hl_n l - 1) <= a < HarnessRep.hl_v l + AREC * HarnessRep.hl_cap l ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
(forall r, In r (HarnessRep.hl_recs (ldrop_list l i)) -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
alist_at B ly' S' W' mem' LA (ldrop_list l i) lines.
Hypothesis PLACEG0 : VAL A_g_gone + 1 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= VAL A_g_gone.
Hypothesis PLACEG32 : VAL A_g_gone + 1 <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= VAL A_g_gone.
Hypothesis HGR : gx_ok SEGS B cshe_ro.
Hypothesis HGRR : gx_rt B cshe_ro.
Hypothesis ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a).
Hypothesis HEND5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_rom SEGS a.
Hypothesis HEND5S : ashp B (VAL A_lit_end5) 4.
Hypothesis HGS : forall a, VAL (A_OBJ 22) <= a < VAL (A_OBJ 22) + 384 -> in_img SEGS a /\ ~ in_rom SEGS a /\
  ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\ ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\
  ~ (VAL A_g_out <= a < VAL A_g_out + 8).
(* the two free sites' call contexts, each the singleton [its return address] *)
Definition CTX_cshe : list (list Z) := [[BASE + AF_fr_check_shape_ends + 0x16c]; [BASE + AF_fr_check_shape_ends + 0x27c]].

Theorem pb_check_shape_ends : cshe_spec B MT G A_csheP.
Proof.
apply cshe_spec_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (IMGC : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly))
  by (intros ly S Hp W mem md H; destruct H as [HAR _]; exact (AR_imgc B ly S Hp W mem md HAR)).
assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
  by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin)).
assert (HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) ([] : list (Z * Z))) by (intros a _ H; inversion H).
assert (FRMF : forall ly S Hp W mem md cid pos, ARi0 SEGS B ly S Hp W mem md -> In (cid, pos) (frames S) ->
  ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0)
  by (intros ly S Hp W mem md cid pos H Hin; exact (FRMF_AR SEGS B ly S Hp W mem md cid pos (proj1 H) Hin)).
assert (ASTx : astrlen_realizes_x B (ARi0 SEGS B) (SIGMA WS_strlen)) by (apply astrlen_realizes_x_of_AR0; exact ASTRLEN).
assert (ABCx : abcmp_realizes_x SEGS B (ARi0 SEGS B) (SIGMA WS_bcmp)) by (apply abcmp_realizes_x_of_AR0; exact ABCMP).
assert (AMOVEx : amemmove_realizes_x B (ARi0 SEGS B) (SIGMA WS_asan_memmove)) by (apply amemmove_realizes_x_of_AR0; exact AMOVE).
assert (AFREEx : afree_cf_rule_c_x SEGS B [] (ARi0 SEGS B) MT RP_AR CTX_cshe)
  by (apply afree_cf_rule_c_x_of_AR0; apply afree_cf_rule_c_weak; exact AFREE).
assert (HC2 : In [BASE + AF_fr_check_shape_ends + 0x16c] CTX_cshe) by (unfold CTX_cshe; cbn; tauto).
assert (HC3 : In [BASE + AF_fr_check_shape_ends + 0x27c] CTX_cshe) by (unfold CTX_cshe; cbn; tauto).
assert (NLx : nl_spec_x B [] (ARi0 SEGS B) (BASE + AF_fr_next_line)) by (apply nl_spec_x_of_AR0; exact NL).
assert (LFINDx : lfind_spec_x B [] (ARi0 SEGS B) G (BASE + AF_fr_list_find)) by (apply lfind_spec_x_of_AR0; exact LFIND).
assert (HEND5Sx : ashp_x (ARi0 SEGS B) (VAL A_lit_end5) 4) by (apply ashp_x_ARi0_of; exact HEND5S).
exact (pb_check_shape_ends_x B [] (ARi0 SEGS B) MT RP_AR G LX0 HP0 IMGC BLKN HPST FRMF ML HG TL ASTx ABCx AMOVEx CTX_cshe
  AFREEx HC2 HC3 NLx LFINDx ALDROP PLACEG0 PLACEG32 HGR HGRR ROMNS HEND5R HEND5Sx HGS).
Qed.
End cAR.
End b.
End a.
