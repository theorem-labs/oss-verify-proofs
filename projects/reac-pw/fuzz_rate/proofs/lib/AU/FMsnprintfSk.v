(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: relocated to omx-clap-core fuzz_manifest.asan (module paths). kcall generalizes A/AE3h.v vf_icpt_xcall (callee post handed in, regions after the
   stack region constrained by what they must avoid); kentry, kenv, st_ok_pc_mem_out and kstore0 are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSnpK.v, with its module paths and module names changed; 744 of its 847 lines of code are new or changed and 234 lines of the source are left out. *)
(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfSk.v (cold/port-fm-rtprintf-param 3e35620c52e); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/FMsnprintfSk.table). *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/FMsnprintfSk.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* fm's snprintf chain over the shared contracts (FMsnprintfShared.v), kit: the frame invariant of a walk whose stack
   window is [lo, hi), the premise bundles of the vsnprintf entries (sn_pre) and of the vfprintf entries (vf_pre) with
   their posts, the contracts from the bundles, and the bundles at a memory a walk changed only inside its window and
   at the destination's first byte, at a smaller window, and as printf_common's premises. New file. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/FMsnprintfSk.v at 71994ff034c7, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/FMsnprintfSk.v was made and quote that file's image-A values; the code below carries image B's values; a numeral in a comment that quotes the donor's text (lib/A/FMsnprintfSk.v keeps its donor's comment text) is kept as lib/A/FMsnprintfSk.v writes it. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YI00 YI16 YK06.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import YB1v YE34 YF0l YF0m YF0x YE20 YE2y.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import FMH_Base FMsnprintfImg FMsnprintfK.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require YE3g.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import PfFacts SnShared SnSx.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import FMsnprintfGk0 FMsnprintfGt0.
Import ListNotations.
Open Scope Z_scope.

(* ---- intervals ---- *)
Lemma zdisjoint_out : forall x r a, zdisjoint x r -> fst x <= a < fst x + snd x -> ~ (fst r <= a < fst r + snd r).
Proof. intros [x1 x2] [r1 r2] a. unfold zdisjoint. cbn [fst snd]. lia. Qed.
Lemma Forall_vfp : forall (P : Z * Z -> Prop) K sp s0 w fp cp,
  Forall P (vfp_out K sp s0 w fp cp) <-> P (sp - K, K) /\ P (s0, w) /\ P (fp, 232) /\ P (cp, 16).
Proof.
intros P K sp s0 w fp cp. unfold vfp_out. split.
- intros HF. repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end. tauto.
- intros (H1 & H2 & H3 & H4). repeat (apply Forall_cons; [assumption|]). apply Forall_nil.
Qed.
Lemma pairwise_vfp : forall K sp s0 w fp cp, pairwise zdisjoint (vfp_out K sp s0 w fp cp) <->
  zdisjoint (sp - K, K) (s0, w) /\ zdisjoint (sp - K, K) (fp, 232) /\ zdisjoint (sp - K, K) (cp, 16) /\
  zdisjoint (s0, w) (fp, 232) /\ zdisjoint (s0, w) (cp, 16) /\ zdisjoint (fp, 232) (cp, 16).
Proof.
intros K sp s0 w fp cp. unfold vfp_out. cbn [pairwise]. split.
- intros (H1 & H2 & H3 & _). repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end. tauto.
- intros (H1 & H2 & H3 & H4 & H5 & H6).
  split; [repeat (apply Forall_cons; [assumption|]); apply Forall_nil|].
  split; [repeat (apply Forall_cons; [assumption|]); apply Forall_nil|].
  split; [repeat (apply Forall_cons; [assumption|]); apply Forall_nil|]. split; [apply Forall_nil | exact I].
Qed.
Lemma sn_len_pos : forall N T, 1 <= sn_len N T.
Proof. intros N T. unfold sn_len, sn_bytes. rewrite length_app. cbn [length]. lia. Qed.
Lemma sn_len_le : forall N T, 0 <= N -> sn_len N T <= N + 1.
Proof.
intros N T HN. unfold sn_len, sn_bytes. rewrite length_app, length_firstn. cbn [length].
pose proof (Nat.le_min_l (Z.to_nat N) (length T)). lia.
Qed.
Lemma sn_len_full : forall N T, Z.of_nat (length T) <= N -> sn_len N T = Z.of_nat (length T) + 1.
Proof.
intros N T HN. unfold sn_len, sn_bytes. rewrite length_app, firstn_all2 by lia. cbn [length]. lia.
Qed.

(* ---- a call whose callee returns at another FP state (the shared contracts' FP-existential post) ---- *)
(* st_ok reads the FP state only through mkst's own fields *)
Lemma st_ok_fx : forall (fx1 fx2 : YK11.FPState) E ss regs pc mem,
  st_ok (fx:=fx1) tfibsegs E ss (mkst (fx:=fx1) regs pc mem (seg_rom tfibsegs)) ->
  st_ok (fx:=fx2) tfibsegs E ss (mkst (fx:=fx2) regs pc mem (seg_rom tfibsegs)).
Proof.
intros fx1 fx2 E ss regs pc mem (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
split; [reflexivity|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [reflexivity|].
split; [exact H6|]. split; [exact H7|]. split; [exact H8 | exact H9].
Qed.
(* FMsnprintfK's kcall without its SRr: the symbolic state after the call (kafter), at the FP state fx2 the callee
   returned with, from the state before it at fx1 and the callee's post (registers, frame, presence) *)
Lemma kcall_fx : forall (fx1 fx2 : YK11.FPState) (W : world tfibsegs) E ss ms (sp0 K : Z) r0 rest k ra osp xlo xhi
  (BAND : Z) (XW : Z -> Prop) regs2 mem2,
  st_ok (fx:=fx1) tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> bv_unsigned (ew E 2) = sp0 ->
  ss_mem ss = r0 :: rest -> YP09.r_base r0 = Some 2%nat -> YP09.r_lo r0 = - K -> YP09.r_hi r0 = 0 ->
  - K <= YP09.r_wlo r0 -> YP09.r_whi r0 <= 0 ->
  ss_atoms_lt k ss = true ->
  regions_wf (ss_mem (kafter k ss ra osp xlo xhi)) = true ->
  no_cdata (ss_mem (kafter k ss ra osp xlo xhi)) = true ->
  mem_atoms_lt k (ss_mem (kafter k ss ra osp xlo xhi)) = true ->
  forallb (chunk_inside r0) (YP09.r_chunks r0) = true ->
  0 <= BAND -> - K <= osp - BAND -> osp <= 0 -> 0 <= sp0 - K -> sp0 <= 2 ^ 63 ->
  (forall a, XW a -> sp0 - K <= a < sp0 -> sp0 + xlo <= a < sp0 + xhi) ->
  (forall r a, In r rest -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
     0 <= a < 2 ^ 64 /\ ~ (sp0 + osp - BAND <= a < sp0 + osp) /\ ~ XW a) ->
  (forall r a, In r rest ->
     base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
     apresent (w_H W) (ms_mem ms) a) ->
  (forall a, sp0 - K <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
  aregs_preserved (ms_regs ms) regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - BAND <= a < sp0 + osp) -> ~ XW a ->
     aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) (ms_mem ms) a) ->
  (forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem2 a) ->
  st_ok (fx:=fx2) tfibsegs (havoc E k (map (getr regs2) CLOB)) (kafter k ss ra osp xlo xhi)
    (restrict (w_H W) (mkst (fx:=fx2) regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfibsegs))).
Proof.
intros fx1 fx2 W E ss ms sp0 K r0 rest k ra osp xlo xhi BAND XW regs2 mem2 HS Hrv Usp Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
  Hat Hwf2 Hnc2 Hma2 Hci0 HB0 HKB Hosp Hsp0 Hsp63 HXWs Hrest HrestW Hpres HP Hfr Hpres2.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape.
set (regsT := ms_regs ms) in *.
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT.
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0].
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
subst b0 lo0 hi0.
unfold kafter in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ss_mem] in Hwf2, Hnc2, Hma2 |- *.
rewrite restrict_mkst_fx.
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
apply (st_ok_fx fx1 fx2) in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
  pose proof (st_ok_splice_havoc (fx:=fx2) tfibsegs k E ss regsT regs2 (Z_to_bv 64 (ss_pc ss)) ra
    (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. apply SPL; clear SPL.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- reflexivity.
- exact Hma2.
- intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [rewrite !getr_zero; reflexivity|].
  rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hcs.
- constructor.
- split; [exact Hwf2|]. split.
  + constructor.
    * destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *. rewrite Usp in *.
      split; [exact Hlo|]. split; [exact Hhi|]. split.
      { intros off Ho. apply YE2y.apresent_writable. apply Hpres2. apply Hpres. lia. }
      apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk].
      apply andb_prop in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1. unfold YE3g.chunk_out in Hk2.
      pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
      pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
      cbn [YP09.r_lo YP09.r_hi] in Ci1, Ci2.
      intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [exact Hb1|].
      rewrite <- Hb2. apply YE2y.mbyte_of_aview. apply Hfr; [lia | lia |].
      intros Hx. pose proof (HXWs _ Hx ltac:(lia)) as Hxw.
      apply orb_prop in Hk2. destruct Hk2 as [Hk2|Hk2]; apply Z.leb_le in Hk2; lia.
    * apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
      eapply (YI04.region_ok_transport tfibsegs E E); [exact Hokr | reflexivity | | | | ].
      -- intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
         pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
         cbn beta in Hncc. destruct (YP09.c_val c); [reflexivity | exact I | exact I | discriminate].
      -- intros a Ha. apply YE2y.mbyte_of_aview. destruct (Hrest r a Hr Ha) as (Hr64 & Hb & Hx). apply Hfr; assumption.
      -- intros a Ha _. apply YE2y.apresent_writable. apply Hpres2. exact (HrestW r a Hr Ha).
      -- apply regions_wf_In with (r := r) in HwfT; [|right; exact Hr]. apply region_wf_facts in HwfT as (_ & _ & Hci).
         exact Hci.
  + eapply pairwise_disjoint_extents; [|exact HpdT]. reflexivity.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
#[local] Abbreviation H W := (w_H W).

(* ---- the reads of the shadow facts lie in [SHADOW_OFF, kHighMemBeg) ---- *)
Lemma ra_keep : forall (rd rd' : reader) x n, amem_range x n -> 0 <= x ->
  (forall s, SHADOW_OFF <= s < kHighMemBeg -> rd' s = rd s) ->
  range_addressable rd SHADOW_OFF x n -> range_addressable rd' SHADOW_OFF x n.
Proof.
intros rd rd' x n Ham Hx Hk Hra y Hy. destruct (Hra y Hy) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite Hk; [exact Hs|]. unfold shadow_of_addr, amem_range, SHADOW_OFF, kHighMemBeg, kLowMemEnd, kHighMemEnd in *.
pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono y (2 ^ 47) 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma hull_keep : forall (rd rd' : reader) x n, amem_range x n -> 0 <= x -> 1 <= n ->
  (forall s, SHADOW_OFF <= s < kHighMemBeg -> rd' s = rd s) ->
  shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof.
intros rd rd' x n Ham Hx Hn Hk Hh s Hs. rewrite Hk; [exact (Hh s Hs)|].
unfold shadow_addr, amem_range, SHADOW_OFF, kHighMemBeg, kLowMemEnd, kHighMemEnd in *.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono (x + n - 1) (2 ^ 47 - 2) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_mod (2147450880 + x / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 + x / 8) 8 ltac:(lia)).
pose proof (Z.div_mod (2147450880 + (x + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (2147450880 + (x + n - 1) / 8) 8 ltac:(lia)).
lia.
Qed.
Lemma rdword_same : forall (rd rd' : reader) p, (forall k, 0 <= k < 8 -> rd' (p + k) = rd (p + k)) ->
  rdword rd' p = rdword rd p.
Proof.
intros rd rd' p Hk. unfold rdword.
assert (E0 : rd' p = rd p) by (rewrite <- (Z.add_0_r p); apply Hk; lia).
rewrite E0, (Hk 1), (Hk 2), (Hk 3), (Hk 4), (Hk 5), (Hk 6), (Hk 7) by lia. reflexivity.
Qed.
Lemma words_at_keep : forall (rd rd' : reader) p ws,
  (forall a, p <= a < p + 8 * Z.of_nat (length ws) -> rd' a = rd a) -> words_at rd p ws -> words_at rd' p ws.
Proof.
intros rd rd' p ws Hk Hw i Hi. rewrite (rdword_same rd rd'); [exact (Hw i Hi)|].
intros k Hk8. apply Hk. lia.
Qed.
Lemma rdword_keep : forall (rd rd' : reader) p v,
  (forall a, p <= a < p + 8 -> rd' a = rd a) -> rdword rd p = Some v -> rdword rd' p = Some v.
Proof. intros rd rd' p v Hk Hw. rewrite (rdword_same rd rd'); [exact Hw|]. intros k Hk8. apply Hk. lia. Qed.

(* ---- the frame of a walk with stack window [lo, hi) ---- *)
Definition sw_frame (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (mem0 : word -> option byte)
  (md0 : Model) (lo hi : Z) (XW : Z -> Prop) (mem : word -> option byte) (md : Model) : Prop :=
  ARU tfibsegs B ly S U W mem md /\ same_but_materialized md0 md /\
  (forall a, lo <= a < hi -> apresent (H W) mem a) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ XW a ->
     aview tfibsegs (H W) mem a = aview tfibsegs (H W) mem0 a) /\
  (forall a, apresent (H W) mem0 a -> apresent (H W) mem a).
Section f.
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (mem0 : word -> option byte) (md0 : Model)
  (lo hi : Z) (XW : Z -> Prop).
Hypothesis Hlo : ly_stk_lo ly <= lo.
Hypothesis Hhi : hi <= ly_stk_hi ly.
Lemma sw_init : ARU tfibsegs B ly S U W mem0 md0 -> (forall a, lo <= a < hi -> apresent (H W) mem0 a) ->
  sw_frame ly S U W mem0 md0 lo hi XW mem0 md0.
Proof.
intros HA Hp. split; [exact HA|]. split; [apply same_but_materialized_refl|]. split; [exact Hp|].
split; [intros; reflexivity | intros a Ha; exact Ha].
Qed.
Lemma sw_step : forall mem md mem' md',
  sw_frame ly S U W mem0 md0 lo hi XW mem md ->
  ARU tfibsegs B ly S U W mem' md' -> same_but_materialized md md' ->
  (forall a, lo <= a < hi -> apresent (H W) mem' a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ XW a ->
     aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a) ->
  (forall a, apresent (H W) mem a -> apresent (H W) mem' a) ->
  sw_frame ly S U W mem0 md0 lo hi XW mem' md'.
Proof.
intros mem md mem' md' (HA & Hsb & Hp & Hfr & Hpm) HA' Hsb' Hp' Hfr' Hpm'.
split; [exact HA'|]. split; [eapply same_but_materialized_trans; eassumption|]. split; [exact Hp'|].
split; [intros a Hr H1 H2; rewrite Hfr' by assumption; apply Hfr; assumption|].
intros a Ha. apply Hpm'. apply Hpm. exact Ha.
Qed.
(* a run of the walk's own code whose writable windows lie in [lo, hi) *)
Lemma sw_run : forall mem md memB mat E rs,
  sw_frame ly S U W mem0 md0 lo hi XW mem md ->
  (forall a, in_wrange E rs a -> lo <= a < hi) ->
  frame_of E rs mem memB ->
  (forall a, lo <= a < hi -> apresent (H W) memB a) ->
  sw_frame ly S U W mem0 md0 lo hi XW memB (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros mem md memB mat E rs HF Hwin Hfo HpB.
pose proof HF as (HA & Hsb & Hp & Hfr & Hpm).
pose proof (stk_kHighMemBeg B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HA)) as [K1 K2].
unfold kHighMemEnd in K2.
assert (OUT : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> memB (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha Hb. apply Hfo. rewrite unsigned_lit_small by lia. intros Hin. exact (Hb (Hwin a Hin)). }
assert (AVB : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
  aview tfibsegs (H W) memB a = aview tfibsegs (H W) mem a).
{ intros a Ha Hb. apply aview_same. exact (OUT a Ha Hb). }
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat)) as MF.
apply (sw_step mem md memB _ HF).
- apply (ARU_frame tfibsegs B LAWS ly S U W mem md memB _ HA).
  + intros a Hr Hown. apply AVB; [exact Hr|]. intros Hb.
    exact (ARU_stack tfibsegs B LAWS ly S U W mem md a HA ltac:(lia) Hown).
  + intros a Hv. rewrite (SnUpoison.aview_mod tfibsegs (H W) memB a).
    rewrite (SnUpoison.aview_mod tfibsegs (H W) mem a) in Hv.
    assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    destruct (Z_lt_le_dec (a mod 2 ^ 64) lo) as [L1|L1]; [rewrite AVB by lia; exact Hv|].
    destruct (Z_lt_le_dec (a mod 2 ^ 64) hi) as [L2|L2]; [| rewrite AVB by lia; exact Hv].
    apply aview_some_of_apresent. apply HpB. lia.
  + apply MF. + apply MF. + apply MF.
  + intros a Ha Hh. unfold YG0d.w64.
    assert (Har : 0 <= a < kHighMemBeg)
      by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia).
    apply OUT; [unfold kHighMemBeg in *; lia | unfold kHighMemBeg in *; lia].
- apply with_vm_backing_same.
- exact HpB.
- intros a Hr H1 H2. apply AVB; assumption.
- intros a Hpa. rewrite (apresent_mod _ memB a). rewrite (apresent_mod _ mem a) in Hpa.
  assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  destruct (Z_lt_le_dec (a mod 2 ^ 64) lo) as [L1|L1];
    [apply (apresent_same (H W) mem memB _); [exact (OUT _ Hr ltac:(lia)) | exact Hpa]|].
  destruct (Z_lt_le_dec (a mod 2 ^ 64) hi) as [L2|L2]; [apply HpB; lia|].
  apply (apresent_same (H W) mem memB _); [exact (OUT _ Hr ltac:(lia)) | exact Hpa].
Qed.
(* a frame with a larger XW *)
Lemma sw_mono : forall (XW' : Z -> Prop) mem md, sw_frame ly S U W mem0 md0 lo hi XW mem md ->
  (forall a, XW a -> XW' a) -> sw_frame ly S U W mem0 md0 lo hi XW' mem md.
Proof.
intros XW' mem md (HA & Hsb & Hp & Hfr & Hpm) Hx. split; [exact HA|]. split; [exact Hsb|]. split; [exact Hp|].
split; [|exact Hpm]. intros a Hr H1 H2. apply Hfr; [exact Hr | exact H1 | intros X; exact (H2 (Hx a X))].
Qed.
End f.

(* ---- the vsnprintf entries: the premises at a walk's entry sp with window K ---- *)
Definition sn_rs (K sp d n : Z) (T : list Z) : list (Z * Z) := snp_out K sp d (sn_len (n - 1) T).
Definition sn_pre (FF : fmt_fam) (K gc gv : Z) (cr : list (Z * Z)) (ly : alayout) (S : astate) (U : list (Z * Z))
  (W : world tfibsegs) (mem : word -> option byte) (md : Model) (sp d n f ap : Z) (ws T : list Z) (cval : Z) : Prop :=
  ARU tfibsegs B ly S U W mem md /\ ly_stk_lo ly + K <= sp /\ sp <= ly_stk_hi ly /\ sp mod 16 = 0 /\ ESTACK <= K /\
  (forall a, sp - K <= a < sp -> apresent (H W) mem a) /\
  consts_view tfibsegs W mem cr /\ Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr /\
  Forall (fun r => Forall (zdisjoint r) (sn_rs K sp d n T)) cr /\
  rdword (aview tfibsegs (H W) mem) gc = Some gv /\ rdword (aview tfibsegs (H W) mem) gv = Some cval /\
  0 <= gc /\ gc + 8 <= 2 ^ 63 /\ 0 <= gv /\ gv + 8 <= 2 ^ 63 /\
  Forall (zdisjoint (gc, 8)) (sn_rs K sp d n T) /\ Forall (zdisjoint (gv, 8)) (sn_rs K sp d n T) /\
  words_at (aview tfibsegs (H W) mem) ap ws /\ 0 <= ap /\ ap + 8 * Z.of_nat (length ws) < 2 ^ 63 /\
  Forall (zdisjoint (ap, 8 * Z.of_nat (length ws))) (sn_rs K sp d n T) /\
  FF (aview tfibsegs (H W) mem) (sn_rs K sp d n T) f ws T /\
  1 <= n < 2 ^ 31 /\ Z.of_nat (length T) < 2 ^ 31 - 1 /\ 0 < d /\ d + sn_len (n - 1) T <= 2 ^ 63 /\
  pairwise zdisjoint (sn_rs K sp d n T) /\
  (forall a, d <= a < d + sn_len (n - 1) T -> writable_at tfibsegs (mrestrict (H W) mem) a /\ ~ aowned B ly S a) /\
  amem_range d (sn_len (n - 1) T) /\
  range_addressable (aview tfibsegs (H W) mem) SHADOW_OFF d (sn_len (n - 1) T) /\
  shadow_hull_vis (aview tfibsegs (H W) mem) d (sn_len (n - 1) T).
Definition sn_post (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (K d n : Z) (T : list Z) : world tfibsegs -> config -> Prop :=
  fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
    c' = @cfg_at fx' tfibsegs (raZ regs) regs' mem' md' /\
    (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
    Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
    ARU tfibsegs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    getr regs' 10 = w64 (Z.of_nat (length T)) /\
    (forall i, 0 <= i < sn_len (n - 1) T ->
       aview tfibsegs (H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
       ~ (spZ regs - K <= a < spZ regs) -> aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a) /\
    (forall a, apresent (H W) mem a -> apresent (H W) mem' a).
(* a walk proved from the bundle gives both vsnprintf contracts *)
Definition sn_walk (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
  forall ly S U W regs mem md d n f ap ws T cval,
  sn_pre FF K gc gv cr ly S U W mem md (spZ regs) d n f ap ws T cval ->
  zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo) ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f -> getr regs 13 = w64 ap ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) (sn_post ly S U W regs mem md K d n T).
Lemma sn_pre_intro : forall FF K gc gv cr ly S U W regs mem md d n f ap ws T cval,
  ESTACK <= K ->
  ecall_preU tfibsegs B ly S U W regs mem md ->
  ly_stk_lo ly + K <= spZ regs ->
  (forall a, spZ regs - K <= a < spZ regs -> apresent (H W) mem a) ->
  consts_view tfibsegs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
  Forall (fun r => Forall (zdisjoint r) (snp_out K (spZ regs) d (sn_len (n - 1) T))) cr ->
  rdword (aview tfibsegs (H W) mem) gc = Some gv -> rdword (aview tfibsegs (H W) mem) gv = Some cval ->
  0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
  Forall (zdisjoint (gc, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
  Forall (zdisjoint (gv, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
  words_at (aview tfibsegs (H W) mem) ap ws ->
  0 <= ap -> ap + 8 * Z.of_nat (length ws) < 2 ^ 63 ->
  Forall (zdisjoint (ap, 8 * Z.of_nat (length ws))) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
  FF (aview tfibsegs (H W) mem) (snp_out K (spZ regs) d (sn_len (n - 1) T)) f ws T ->
  1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + sn_len (n - 1) T <= 2 ^ 63 ->
  pairwise zdisjoint (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
  dest_ok tfibsegs B ly S W regs mem d (sn_len (n - 1) T) -> amem_range d (sn_len (n - 1) T) ->
  range_addressable (aview tfibsegs (H W) mem) SHADOW_OFF d (sn_len (n - 1) T) ->
  shadow_hull_vis (aview tfibsegs (H W) mem) d (sn_len (n - 1) T) ->
  sn_pre FF K gc gv cr ly S U W mem md (spZ regs) d n f ap ws T cval.
Proof.
intros FF K gc gv cr ly S U W regs mem md d n f ap ws T cval HK ((HAR & Hra & H16 & Hes & Hhi & Hpe & Hgp & Htp) & Hok & Hpo)
  HKlo HKp Hcv Hcb Hcd Hgc Hgv G1 G2 G3 G4 Hgcd Hgvd Hws A1 A2 Ad HFF Hn HT Hd0 Hdw Hpw Hdst Ham Hra' Hhull.
assert (HA : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
unfold sn_pre, sn_rs. repeat (split; [assumption|]).
split; [intros a Ha; destruct (Hdst a Ha) as (X1 & X2 & _); split; assumption|].
split; [exact Ham|]. split; assumption.
Qed.
Lemma sn_ecall : forall FF K gc gv cr ly S U W regs mem md d n f ap ws T cval,
  sn_pre FF K gc gv cr ly S U W mem md (spZ regs) d n f ap ws T cval ->
  YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  ecall_preU tfibsegs B ly S U W regs mem md.
Proof.
intros FF K gc gv cr ly S U W regs mem md d n f ap ws T cval (HA & Hlo & Hhi & H16 & HK & Hp & _) Hra Hgp Htp.
apply (g_ecall_preU B ly S U W regs mem md HA Hra H16); try assumption; [lia|].
intros a Ha. apply Hp. lia.
Qed.
Lemma sn_dest_ok : forall FF K gc gv cr ly S U W regs mem md d n f ap ws T cval,
  sn_pre FF K gc gv cr ly S U W mem md (spZ regs) d n f ap ws T cval ->
  dest_ok tfibsegs B ly S W regs mem d (sn_len (n - 1) T).
Proof.
intros FF K gc gv cr ly S U W regs mem md d n f ap ws T cval Hp a Ha.
pose proof Hp as (_ & _ & _ & _ & HK & _). unfold sn_pre in Hp.
destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  Hpw & Hdst & _).
destruct (Hdst a Ha) as (X1 & X2). split; [exact X1|]. split; [exact X2|].
unfold sn_rs in Hpw. apply pairwise_snp in Hpw. unfold zdisjoint in Hpw. cbn [fst snd] in Hpw. lia.
Qed.
Lemma sn_contract : forall FF K gc gv img_lo img_hi cr pc, ESTACK <= K -> sn_walk FF K gc gv img_lo img_hi cr pc ->
  sh_avsnprintf_realizesU tfibsegs B FF K gc gv img_lo img_hi cr pc /\ sh_avsnprintf_icpt_realizesU tfibsegs B FF K gc gv img_lo img_hi cr pc.
Proof.
intros FF K gc gv img_lo img_hi cr pc HK HW. split;
intros ly S U W regs mem md d n f ap ws T cval Hpre HKlo HKp R10 R11 R12 R13 Hcv Hcb Hcd Hgc Hgv G1 G2 G3 G4 Hgcd Hgvd
  Hws A1 A2 Ad HFF Hn HT Hd0 Hdw Hpw Hdst Ham Hra Hhull Hdog Hfrm;
(pose proof (sn_pre_intro FF K gc gv cr ly S U W regs mem md d n f ap ws T cval HK Hpre HKlo HKp Hcv Hcb Hcd Hgc Hgv
   G1 G2 G3 G4 Hgcd Hgvd Hws A1 A2 Ad HFF Hn HT Hd0 Hdw Hpw Hdst Ham Hra Hhull) as P;
 pose proof Hpre as ((_ & Hret & _ & _ & _ & _ & Hgp & Htp) & _ & _);
 exact (HW ly S U W regs mem md d n f ap ws T cval P Hdog Hfrm Hret Hgp Htp R10 R11 R12 R13)).
Qed.

(* the bundle at a memory that changed only inside the window and at d (to 0), the window and its presence kept *)
Lemma sn_pre_keep : forall FF K gc gv cr ly S U W mem md mem' md' sp d n f ap ws T cval,
  ff_stable64 FF ->
  sn_pre FF K gc gv cr ly S U W mem md sp d n f ap ws T cval ->
  ARU tfibsegs B ly S U W mem' md' ->
  (forall a, sp - K <= a < sp -> apresent (H W) mem' a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - K <= a < sp) -> a <> d ->
     aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a) ->
  (aview tfibsegs (H W) mem' d = aview tfibsegs (H W) mem d \/ aview tfibsegs (H W) mem' d = Some 0) ->
  (forall a, apresent (H W) mem a -> apresent (H W) mem' a) ->
  sn_pre FF K gc gv cr ly S U W mem' md' sp d n f ap ws T cval.
Proof.
intros FF K gc gv cr ly S U W mem md mem' md' sp d n f ap ws T cval STAB
  (HA & Hlo & Hhi & H16 & HK & Hp & Hcv & Hcb & Hcd & Hgc & Hgv & G1 & G2 & G3 & G4 & Hgcd & Hgvd & Hws & A1 & A2 & Ad &
   HFF & Hn & HT & Hd0 & Hdw & Hpw & Hdst & Ham & Hra & Hhull) HA' Hp' KEEP DV PRES.
pose proof (stk_kHighMemBeg B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HA)) as [K1 K2].
pose proof (sn_len_pos (n - 1) T) as Hw1.
unfold sn_rs in *. set (w := sn_len (n - 1) T) in *.
apply pairwise_snp in Hpw.
assert (Hdam : d + w <= kLowMemEnd - 1 \/ kHighMemBeg <= d) by (unfold amem_range in Ham; lia).
(* bytes outside the window and the destination are kept *)
assert (KO : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - K <= a < sp) -> ~ (d <= a < d + w) ->
  aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a).
{ intros a Ha H1 H2. apply KEEP; [exact Ha | exact H1 | intros ->; lia]. }
assert (KZ : forall p l, zdisjoint (p, l) (sp - K, K) -> zdisjoint (p, l) (d, w) -> 0 <= p -> p + l <= 2 ^ 63 ->
  forall a, p <= a < p + l -> aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a).
{ intros p l Z1 Z2 Hp0 Hpl a Ha. unfold zdisjoint in Z1, Z2. cbn [fst snd] in Z1, Z2. apply KO; lia. }
assert (KS : forall s, SHADOW_OFF <= s < kHighMemBeg -> aview tfibsegs (H W) mem' s = aview tfibsegs (H W) mem s).
{ intros s Hs. apply KO; unfold SHADOW_OFF, kHighMemBeg, kLowMemEnd in *; lia. }
apply Forall_snp in Hgcd as [Gc1 Gc2]. apply Forall_snp in Hgvd as [Gv1 Gv2]. apply Forall_snp in Ad as [Ad1 Ad2].
unfold sn_pre, sn_rs. fold w.
split; [exact HA'|]. split; [exact Hlo|]. split; [exact Hhi|]. split; [exact H16|]. split; [exact HK|].
split; [exact Hp'|].
split.
{ intros a Ha. rewrite Exists_exists in Ha. destruct Ha as (r & Hr & Hin).
  rewrite Forall_forall in Hcd, Hcb. pose proof (Hcd r Hr) as Hd. apply Forall_snp in Hd as [D1 D2].
  pose proof (Hcb r Hr) as Hb. unfold in_zr in Hin.
  rewrite (KZ (fst r) (snd r)); [| destruct r; exact D1 | destruct r; exact D2 | lia | lia | exact Hin].
  apply Hcv. rewrite Exists_exists. exists r. split; [exact Hr | exact Hin]. }
split; [exact Hcb|]. split; [exact Hcd|].
split; [apply (rdword_keep (aview tfibsegs (H W) mem)); [|exact Hgc]; intros a Ha; apply (KZ gc 8); auto; lia|].
split; [apply (rdword_keep (aview tfibsegs (H W) mem)); [|exact Hgv]; intros a Ha; apply (KZ gv 8); auto; lia|].
split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
split; [apply Forall_snp; split; assumption|]. split; [apply Forall_snp; split; assumption|].
split; [apply (words_at_keep (aview tfibsegs (H W) mem)); [|exact Hws]; intros a Ha; apply (KZ ap (8 * Z.of_nat (length ws))); auto; lia|].
split; [exact A1|]. split; [exact A2|]. split; [apply Forall_snp; split; assumption|].
split.
{ apply (STAB (aview tfibsegs (H W) mem)); [exact HFF|].
  intros a Ha.
  destruct (Z_lt_le_dec a (sp - K)) as [L1|L1]; [|destruct (Z_lt_le_dec a sp) as [L2|L2]].
  - destruct (Z.eq_dec a d) as [->|Hne]; [destruct DV as [E|E]; [left; exact E|]|left; apply KEEP; [exact Ha | lia | exact Hne]].
    right. split; [apply Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|].
    unfold SHADOW_OFF, kHighMemBeg, kLowMemEnd in *; lia.
  - right. split; [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|].
    unfold SHADOW_OFF, kHighMemBeg in *; lia.
  - destruct (Z.eq_dec a d) as [->|Hne]; [destruct DV as [E|E]; [left; exact E|]|left; apply KEEP; [exact Ha | lia | exact Hne]].
    right. split; [apply Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|].
    unfold SHADOW_OFF, kHighMemBeg, kLowMemEnd in *; lia. }
split; [exact Hn|]. split; [exact HT|]. split; [exact Hd0|]. split; [exact Hdw|].
split; [apply pairwise_snp; exact Hpw|].
split.
{ intros a Ha. destruct (Hdst a Ha) as (X1 & X2). split; [|exact X2].
  exact (writable_xfer (H W) mem mem' a X1 (PRES a)). }
split; [exact Ham|].
split; [exact (ra_keep _ _ d w Ham ltac:(lia) KS Hra)|].
exact (hull_keep _ _ d w Ham ltac:(lia) Hw1 KS Hhull).
Qed.
(* the bundle at a window inside the walk's window (a callee's), with arguments at ap' (words at the same memory) *)
Lemma sn_pre_shrink : forall FF K K' gc gv cr ly S U W mem md sp sp' d n f ap ap' ws T cval,
  ff_mono FF ->
  sn_pre FF K gc gv cr ly S U W mem md sp d n f ap ws T cval ->
  sp - K <= sp' - K' -> sp' <= sp -> ESTACK <= K' -> sp' mod 16 = 0 ->
  words_at (aview tfibsegs (H W) mem) ap' ws -> 0 <= ap' -> ap' + 8 * Z.of_nat (length ws) < 2 ^ 63 ->
  Forall (zdisjoint (ap', 8 * Z.of_nat (length ws))) (sn_rs K' sp' d n T) ->
  sn_pre FF K' gc gv cr ly S U W mem md sp' d n f ap' ws T cval.
Proof.
intros FF K K' gc gv cr ly S U W mem md sp sp' d n f ap ap' ws T cval MONO
  (HA & Hlo & Hhi & H16 & HK & Hp & Hcv & Hcb & Hcd & Hgc & Hgv & G1 & G2 & G3 & G4 & Hgcd & Hgvd & Hws & A1 & A2 & Ad &
   HFF & Hn & HT & Hd0 & Hdw & Hpw & Hdst & Ham & Hra & Hhull) L1 L2 HK' H16' Hws' A1' A2' Ad'.
unfold sn_rs in *. set (w := sn_len (n - 1) T) in *.
assert (SUB : forall x, Forall (zdisjoint x) (snp_out K sp d w) -> Forall (zdisjoint x) (snp_out K' sp' d w)).
{ intros x Hx. apply Forall_snp in Hx as [X1 X2]. apply Forall_snp. split; [|exact X2].
  apply (zdisjoint_sub x (sp - K, K)); [exact X1 | cbn [fst snd]; lia | cbn [fst snd]; lia]. }
unfold sn_pre, sn_rs. fold w.
split; [exact HA|]. split; [lia|]. split; [lia|]. split; [exact H16'|]. split; [exact HK'|].
split; [intros a Ha; apply Hp; lia|].
split; [exact Hcv|]. split; [exact Hcb|].
split; [rewrite Forall_forall in Hcd |- *; intros r Hr; exact (SUB r (Hcd r Hr))|].
split; [exact Hgc|]. split; [exact Hgv|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
split; [exact (SUB _ Hgcd)|]. split; [exact (SUB _ Hgvd)|].
split; [exact Hws'|]. split; [exact A1'|]. split; [exact A2'|]. split; [exact Ad'|].
split.
{ apply (MONO _ (snp_out K sp d w)); [exact HFF|].
  intros r' Hr'. unfold snp_out in Hr'. destruct Hr' as [<-|[<-|[]]].
  - exists (sp - K, K). split; [left; reflexivity | cbn [fst snd]; lia].
  - exists (d, w). split; [right; left; reflexivity | cbn [fst snd]; lia]. }
split; [exact Hn|]. split; [exact HT|]. split; [exact Hd0|]. split; [exact Hdw|].
split; [apply pairwise_snp in Hpw; apply pairwise_snp; unfold zdisjoint in *; cbn [fst snd] in *; lia|].
split; [exact Hdst|]. split; [exact Ham|]. split; assumption.
Qed.
(* printf_common's premises at a callee sp' with window Kp inside the walk's window *)
Lemma sn_pcom : forall FF K Kp gc gv cr ly S U W mem md sp sp' d n f ap ws T cval,
  ff_mono FF ->
  sn_pre FF K gc gv cr ly S U W mem md sp d n f ap ws T cval ->
  sp - K <= sp' - Kp -> sp' <= sp ->
  consts_view tfibsegs W mem cr /\ Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr /\
  Forall (zdisjoint (sp' - Kp, Kp)) cr /\
  words_at (aview tfibsegs (H W) mem) ap ws /\ ap + 8 * Z.of_nat (length ws) < 2 ^ 63 /\
  zdisjoint (ap, 8 * Z.of_nat (length ws)) (sp' - Kp, Kp) /\
  FF (aview tfibsegs (H W) mem) [(sp' - Kp, Kp)] f ws T.
Proof.
intros FF K Kp gc gv cr ly S U W mem md sp sp' d n f ap ws T cval MONO
  (HA & Hlo & Hhi & H16 & HK & Hp & Hcv & Hcb & Hcd & Hgc & Hgv & G1 & G2 & G3 & G4 & Hgcd & Hgvd & Hws & A1 & A2 & Ad &
   HFF & _) L1 L2.
split; [exact Hcv|]. split; [exact Hcb|].
split.
{ rewrite Forall_forall in Hcd |- *. intros r Hr. pose proof (Hcd r Hr) as X. unfold sn_rs in X.
  apply Forall_snp in X as [X1 _]. unfold zdisjoint in *. cbn [fst snd] in *. lia. }
split; [exact Hws|]. split; [exact A2|].
split; [unfold sn_rs in Ad; apply Forall_snp in Ad as [X1 _]; unfold zdisjoint in *; cbn [fst snd] in *; lia|].
apply (MONO _ (sn_rs K sp d n T)); [exact HFF|].
intros r' Hr'. destruct Hr' as [<-|[]]. exists (sp - K, K). split; [left; reflexivity | cbn [fst snd]; lia].
Qed.
(* a vsnprintf contract applied to the bundle *)
Lemma sn_apply : forall FF K gc gv img_lo img_hi cr pc ly S U W regs mem md d n f ap ws T cval,
  (sh_avsnprintf_realizesU tfibsegs B FF K gc gv img_lo img_hi cr pc \/ sh_avsnprintf_icpt_realizesU tfibsegs B FF K gc gv img_lo img_hi cr pc) ->
  sn_pre FF K gc gv cr ly S U W mem md (spZ regs) d n f ap ws T cval ->
  zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo) ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f -> getr regs 13 = w64 ap ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) (sn_post ly S U W regs mem md K d n T).
Proof.
intros FF K gc gv img_lo img_hi cr pc ly S U W regs mem md d n f ap ws T cval HC Hp Hdog Hfrm Hra Hgp Htp R10 R11 R12 R13.
pose proof (sn_ecall FF K gc gv cr ly S U W regs mem md d n f ap ws T cval Hp Hra Hgp Htp) as HE.
pose proof (sn_dest_ok FF K gc gv cr ly S U W regs mem md d n f ap ws T cval Hp) as HD.
destruct Hp as (HA & Hlo & Hhi & H16 & HK & Hp & Hcv & Hcb & Hcd & Hgc & Hgv & G1 & G2 & G3 & G4 & Hgcd & Hgvd & Hws &
  A1 & A2 & Ad & HFF & Hn & HT & Hd0 & Hdw & Hpw & Hdst & Ham & Hra' & Hhull).
destruct HC as [HC|HC];
  exact (HC ly S U W regs mem md d n f ap ws T cval HE Hlo Hp R10 R11 R12 R13 Hcv Hcb Hcd Hgc Hgv G1 G2 G3 G4 Hgcd Hgvd
    Hws A1 A2 Ad HFF Hn HT Hd0 Hdw Hpw HD Ham Hra' Hhull Hdog Hfrm).
Qed.

(* ---- the vfprintf entries (fp, f, ap) on the string FILE fp, cookie cp = {s0, n0} ---- *)
Definition vf_rs (K sp s0 n0 : Z) (T : list Z) (fp cp : Z) : list (Z * Z) := vfp_out K sp s0 (sn_len n0 T) fp cp.
Definition vf_pre (FF : fmt_fam) (K gc gv : Z) (cr : list (Z * Z)) (snw : Z) (ly : alayout) (S : astate)
  (U : list (Z * Z)) (W : world tfibsegs) (mem : word -> option byte) (md : Model) (sp fp f ap bp cp s0 n0 : Z)
  (ws T : list Z) (cval : Z) : Prop :=
  ARU tfibsegs B ly S U W mem md /\ ly_stk_lo ly + K <= sp /\ sp <= ly_stk_hi ly /\ sp mod 16 = 0 /\ ESTACK <= K /\
  (forall a, sp - K <= a < sp -> apresent (H W) mem a) /\
  words_at (aview tfibsegs (H W) mem) fp (sn_file snw bp cp) /\ 0 < bp /\
  words_at (aview tfibsegs (H W) mem) cp [s0; n0] /\
  (forall a, fp <= a < fp + 232 -> writable_at tfibsegs (mrestrict (H W) mem) a /\ ~ aowned B ly S a) /\
  (forall a, cp <= a < cp + 16 -> writable_at tfibsegs (mrestrict (H W) mem) a /\ ~ aowned B ly S a) /\
  0 <= fp /\ fp + 232 <= 2 ^ 63 /\ 0 <= cp /\ cp + 16 <= 2 ^ 63 /\
  consts_view tfibsegs W mem cr /\ Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr /\
  Forall (fun r => Forall (zdisjoint r) (vf_rs K sp s0 n0 T fp cp)) cr /\
  rdword (aview tfibsegs (H W) mem) gc = Some gv /\ rdword (aview tfibsegs (H W) mem) gv = Some cval /\
  0 <= gc /\ gc + 8 <= 2 ^ 63 /\ 0 <= gv /\ gv + 8 <= 2 ^ 63 /\
  Forall (zdisjoint (gc, 8)) (vf_rs K sp s0 n0 T fp cp) /\ Forall (zdisjoint (gv, 8)) (vf_rs K sp s0 n0 T fp cp) /\
  words_at (aview tfibsegs (H W) mem) ap ws /\ 0 <= ap /\ ap + 8 * Z.of_nat (length ws) < 2 ^ 63 /\
  Forall (zdisjoint (ap, 8 * Z.of_nat (length ws))) (vf_rs K sp s0 n0 T fp cp) /\
  FF (aview tfibsegs (H W) mem) (vf_rs K sp s0 n0 T fp cp) f ws T /\
  0 <= n0 < 2 ^ 31 - 1 /\ Z.of_nat (length T) < 2 ^ 31 - 1 /\ 0 < s0 /\ s0 + sn_len n0 T <= 2 ^ 63 /\
  pairwise zdisjoint (vf_rs K sp s0 n0 T fp cp) /\
  (forall a, s0 <= a < s0 + sn_len n0 T -> writable_at tfibsegs (mrestrict (H W) mem) a /\ ~ aowned B ly S a) /\
  amem_range s0 (sn_len n0 T) /\
  range_addressable (aview tfibsegs (H W) mem) SHADOW_OFF s0 (sn_len n0 T) /\
  shadow_hull_vis (aview tfibsegs (H W) mem) s0 (sn_len n0 T).
Definition vf_post (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (K fp cp s0 n0 : Z) (T : list Z) : world tfibsegs -> config -> Prop :=
  fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
    c' = @cfg_at fx' tfibsegs (raZ regs) regs' mem' md' /\
    (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
    Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
    ARU tfibsegs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    getr regs' 10 = w64 (Z.of_nat (length T)) /\
    (forall i, 0 <= i < sn_len n0 T ->
       aview tfibsegs (H W) mem' (s0 + i) = Some (nth (Z.to_nat i) (sn_bytes n0 T) 0)) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (s0 <= a < s0 + sn_len n0 T) ->
       ~ Exists (in_zr a) [(spZ regs - K, K); (fp, 232); (cp, 16)] ->
       aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a) /\
    (forall a, apresent (H W) mem a -> apresent (H W) mem' a).
Definition vf_walk (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (snw pc : Z) : Prop :=
  forall ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval,
  vf_pre FF K gc gv cr snw ly S U W mem md (spZ regs) fp f ap bp cp s0 n0 ws T cval ->
  zdisjoint (s0, sn_len n0 T) (img_lo, img_hi - img_lo) ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 fp -> getr regs 11 = w64 f -> getr regs 12 = w64 ap ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) (vf_post ly S U W regs mem md K fp cp s0 n0 T).
Lemma vf_pre_intro : forall FF K gc gv cr snw ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval,
  ESTACK <= K ->
  ecall_preU tfibsegs B ly S U W regs mem md ->
  ly_stk_lo ly + K <= spZ regs ->
  (forall a, spZ regs - K <= a < spZ regs -> apresent (H W) mem a) ->
  words_at (aview tfibsegs (H W) mem) fp (sn_file snw bp cp) -> 0 < bp ->
  words_at (aview tfibsegs (H W) mem) cp [s0; n0] ->
  dest_ok tfibsegs B ly S W regs mem fp 232 -> dest_ok tfibsegs B ly S W regs mem cp 16 ->
  0 <= fp -> fp + 232 <= 2 ^ 63 -> 0 <= cp -> cp + 16 <= 2 ^ 63 ->
  consts_view tfibsegs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
  Forall (fun r => Forall (zdisjoint r) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp)) cr ->
  rdword (aview tfibsegs (H W) mem) gc = Some gv -> rdword (aview tfibsegs (H W) mem) gv = Some cval ->
  0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
  Forall (zdisjoint (gc, 8)) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) ->
  Forall (zdisjoint (gv, 8)) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) ->
  words_at (aview tfibsegs (H W) mem) ap ws ->
  0 <= ap -> ap + 8 * Z.of_nat (length ws) < 2 ^ 63 ->
  Forall (zdisjoint (ap, 8 * Z.of_nat (length ws))) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) ->
  FF (aview tfibsegs (H W) mem) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) f ws T ->
  0 <= n0 < 2 ^ 31 - 1 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < s0 -> s0 + sn_len n0 T <= 2 ^ 63 ->
  pairwise zdisjoint (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) ->
  dest_ok tfibsegs B ly S W regs mem s0 (sn_len n0 T) -> amem_range s0 (sn_len n0 T) ->
  range_addressable (aview tfibsegs (H W) mem) SHADOW_OFF s0 (sn_len n0 T) ->
  shadow_hull_vis (aview tfibsegs (H W) mem) s0 (sn_len n0 T) ->
  vf_pre FF K gc gv cr snw ly S U W mem md (spZ regs) fp f ap bp cp s0 n0 ws T cval.
Proof.
intros FF K gc gv cr snw ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval HK
  ((HAR & Hra & H16 & Hes & Hhi & Hpe & Hgp & Htp) & Hok & Hpo)
  HKlo HKp Hfile Hbp Hck Hdf Hdc F1 F2 C1 C2 Hcv Hcb Hcd Hgc Hgv G1 G2 G3 G4 Hgcd Hgvd Hws A1 A2 Ad HFF Hn HT Hs0 Hsw Hpw
  Hdst Ham Hra' Hhull.
assert (HA : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
unfold vf_pre, vf_rs. split; [exact HA|]. do 8 (split; [assumption|]).
split; [intros a Ha; destruct (Hdf a Ha) as (X1 & X2 & _); split; assumption|].
split; [intros a Ha; destruct (Hdc a Ha) as (X1 & X2 & _); split; assumption|].
repeat (split; [assumption|]).
split; [intros a Ha; destruct (Hdst a Ha) as (X1 & X2 & _); split; assumption|].
split; [exact Ham|]. split; assumption.
Qed.
Lemma vf_ecall : forall FF K gc gv cr snw ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval,
  vf_pre FF K gc gv cr snw ly S U W mem md (spZ regs) fp f ap bp cp s0 n0 ws T cval ->
  YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  ecall_preU tfibsegs B ly S U W regs mem md.
Proof.
intros FF K gc gv cr snw ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval (HA & Hlo & Hhi & H16 & HK & Hp & _) Hra Hgp Htp.
apply (g_ecall_preU B ly S U W regs mem md HA Hra H16); try assumption; [lia|].
intros a Ha. apply Hp. lia.
Qed.
Lemma vf_contract : forall FF K gc gv img_lo img_hi cr snw pc, ESTACK <= K -> vf_walk FF K gc gv img_lo img_hi cr snw pc ->
  sh_avfprintf_icpt_realizesU tfibsegs B FF K gc gv img_lo img_hi cr snw pc.
Proof.
intros FF K gc gv img_lo img_hi cr snw pc HK HW
  ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval Hpre HKlo HKp R10 R11 R12 Hfile Hbp Hck Hdf Hdc F1 F2 C1 C2
  Hcv Hcb Hcd Hgc Hgv G1 G2 G3 G4 Hgcd Hgvd Hws A1 A2 Ad HFF Hn HT Hs0 Hsw Hpw Hdst Ham Hra Hhull Hdog Hfrm.
pose proof (vf_pre_intro FF K gc gv cr snw ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval HK Hpre HKlo HKp
  Hfile Hbp Hck Hdf Hdc F1 F2 C1 C2 Hcv Hcb Hcd Hgc Hgv G1 G2 G3 G4 Hgcd Hgvd Hws A1 A2 Ad HFF Hn HT Hs0 Hsw Hpw
  Hdst Ham Hra Hhull) as P.
pose proof Hpre as ((_ & Hret & _ & _ & _ & _ & Hgp & Htp) & _ & _).
exact (HW ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval P Hdog Hfrm Hret Hgp Htp R10 R11 R12).
Qed.
(* dest_ok of the FILE, the cookie and the destination at the walk's sp *)
Lemma vf_dest_ok : forall FF K gc gv cr snw ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval,
  vf_pre FF K gc gv cr snw ly S U W mem md (spZ regs) fp f ap bp cp s0 n0 ws T cval ->
  dest_ok tfibsegs B ly S W regs mem fp 232 /\ dest_ok tfibsegs B ly S W regs mem cp 16 /\
  dest_ok tfibsegs B ly S W regs mem s0 (sn_len n0 T).
Proof.
intros FF K gc gv cr snw ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval
  (HA & Hlo & Hhi & H16 & HK & Hp & Hfile & Hbp & Hck & Hdf & Hdc & F1 & F2 & C1 & C2 & Hcv & Hcb & Hcd & Hgc & Hgv &
   G1 & G2 & G3 & G4 & Hgcd & Hgvd & Hws & A1 & A2 & Ad & HFF & Hn & HT & Hs0 & Hsw & Hpw & Hdst & Ham & Hra & Hhull).
unfold vf_rs in Hpw. apply pairwise_vfp in Hpw as (P1 & P2 & P3 & _). unfold zdisjoint in P1, P2, P3. cbn [fst snd] in *.
split; [|split]; intros a Ha.
- destruct (Hdf a Ha) as (X1 & X2). split; [exact X1|]. split; [exact X2 | lia].
- destruct (Hdc a Ha) as (X1 & X2). split; [exact X1|]. split; [exact X2 | lia].
- destruct (Hdst a Ha) as (X1 & X2). split; [exact X1|]. split; [exact X2 | lia].
Qed.
(* the bundle at a memory that changed only inside the window *)
Lemma vf_pre_keep : forall FF K gc gv cr snw ly S U W mem md mem' md' sp fp f ap bp cp s0 n0 ws T cval,
  ff_stable64 FF ->
  vf_pre FF K gc gv cr snw ly S U W mem md sp fp f ap bp cp s0 n0 ws T cval ->
  ARU tfibsegs B ly S U W mem' md' ->
  (forall a, sp - K <= a < sp -> apresent (H W) mem' a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - K <= a < sp) -> aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a) ->
  (forall a, apresent (H W) mem a -> apresent (H W) mem' a) ->
  vf_pre FF K gc gv cr snw ly S U W mem' md' sp fp f ap bp cp s0 n0 ws T cval.
Proof.
intros FF K gc gv cr snw ly S U W mem md mem' md' sp fp f ap bp cp s0 n0 ws T cval STAB
  (HA & Hlo & Hhi & H16 & HK & Hp & Hfile & Hbp & Hck & Hdf & Hdc & F1 & F2 & C1 & C2 & Hcv & Hcb & Hcd & Hgc & Hgv &
   G1 & G2 & G3 & G4 & Hgcd & Hgvd & Hws & A1 & A2 & Ad & HFF & Hn & HT & Hs0 & Hsw & Hpw & Hdst & Ham & Hra & Hhull)
  HA' Hp' KEEP PRES.
pose proof (stk_kHighMemBeg B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HA)) as [K1 K2].
pose proof (sn_len_pos n0 T) as Hw1.
unfold vf_rs in *. set (w := sn_len n0 T) in *.
pose proof Hpw as Hpw'. apply pairwise_vfp in Hpw' as (P1 & P2 & P3 & _).
assert (KZ : forall p l, zdisjoint (p, l) (sp - K, K) -> 0 <= p -> p + l <= 2 ^ 63 ->
  forall a, p <= a < p + l -> aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a).
{ intros p l Z1 Hp0 Hpl a Ha. unfold zdisjoint in Z1. cbn [fst snd] in Z1. apply KEEP; lia. }
assert (KS : forall s, SHADOW_OFF <= s < kHighMemBeg -> aview tfibsegs (H W) mem' s = aview tfibsegs (H W) mem s).
{ intros s Hs. apply KEEP; unfold SHADOW_OFF, kHighMemBeg in *; lia. }
assert (ZS : forall x, zdisjoint (sp - K, K) x -> zdisjoint x (sp - K, K)) by (intros [x1 x2]; unfold zdisjoint; cbn [fst snd]; lia).
pose proof Hgcd as Gc. apply Forall_vfp in Gc as (Gc1 & _). pose proof Hgvd as Gv. apply Forall_vfp in Gv as (Gv1 & _).
pose proof Ad as Ad'. apply Forall_vfp in Ad' as (Ad1 & _).
unfold vf_pre, vf_rs. fold w.
split; [exact HA'|]. do 4 (split; [assumption|]). split; [exact Hp'|].
split; [apply (words_at_keep (aview tfibsegs (H W) mem)); [|exact Hfile]; intros a Ha; apply (KZ fp 232); [exact (ZS _ P2) | lia | lia | unfold sn_file in Ha; cbn [length] in Ha; lia]|].
split; [exact Hbp|].
split; [apply (words_at_keep (aview tfibsegs (H W) mem)); [|exact Hck]; intros a Ha; apply (KZ cp 16); [exact (ZS _ P3) | lia | lia | cbn [length] in Ha; lia]|].
split; [intros a Ha; destruct (Hdf a Ha) as (X1 & X2); split; [exact (writable_xfer (H W) mem mem' a X1 (PRES a)) | exact X2]|].
split; [intros a Ha; destruct (Hdc a Ha) as (X1 & X2); split; [exact (writable_xfer (H W) mem mem' a X1 (PRES a)) | exact X2]|].
do 4 (split; [assumption|]).
split.
{ intros a Ha. rewrite Exists_exists in Ha. destruct Ha as (r & Hr & Hin).
  rewrite Forall_forall in Hcd, Hcb. pose proof (Hcd r Hr) as Hd. apply Forall_vfp in Hd as (D1 & _).
  pose proof (Hcb r Hr) as Hb. unfold in_zr in Hin.
  rewrite (KZ (fst r) (snd r)); [| destruct r; exact D1 | lia | lia | exact Hin].
  apply Hcv. rewrite Exists_exists. exists r. split; [exact Hr | exact Hin]. }
split; [exact Hcb|]. split; [exact Hcd|].
split; [apply (rdword_keep (aview tfibsegs (H W) mem)); [|exact Hgc]; intros a Ha; apply (KZ gc 8); auto; lia|].
split; [apply (rdword_keep (aview tfibsegs (H W) mem)); [|exact Hgv]; intros a Ha; apply (KZ gv 8); auto; lia|].
do 4 (split; [assumption|]).
split; [assumption|]. split; [assumption|].
split; [apply (words_at_keep (aview tfibsegs (H W) mem)); [|exact Hws]; intros a Ha; apply (KZ ap (8 * Z.of_nat (length ws))); auto; lia|].
do 3 (split; [assumption|]).
split.
{ apply (STAB (aview tfibsegs (H W) mem)); [exact HFF|].
  intros a Ha. destruct (Z_lt_le_dec a (sp - K)) as [L1|L1]; [left; apply KEEP; [exact Ha | lia]|].
  destruct (Z_lt_le_dec a sp) as [L2|L2]; [|left; apply KEEP; [exact Ha | lia]].
  right. split; [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|]. unfold SHADOW_OFF, kHighMemBeg in *; lia. }
do 5 (split; [assumption|]).
split; [intros a Ha; destruct (Hdst a Ha) as (X1 & X2); split; [exact (writable_xfer (H W) mem mem' a X1 (PRES a)) | exact X2]|].
assert (Hs0p : 0 <= s0) by lia.
split; [exact Ham|].
split; [exact (ra_keep _ _ s0 w Ham Hs0p KS Hra)|].
exact (hull_keep _ _ s0 w Ham Hs0p Hw1 KS Hhull).
Qed.
(* the bundle at a callee's window inside the walk's window *)
Lemma vf_pre_shrink : forall FF K K' gc gv cr snw ly S U W mem md sp sp' fp f ap bp cp s0 n0 ws T cval,
  ff_mono FF ->
  vf_pre FF K gc gv cr snw ly S U W mem md sp fp f ap bp cp s0 n0 ws T cval ->
  sp - K <= sp' - K' -> sp' <= sp -> ESTACK <= K' -> sp' mod 16 = 0 ->
  vf_pre FF K' gc gv cr snw ly S U W mem md sp' fp f ap bp cp s0 n0 ws T cval.
Proof.
intros FF K K' gc gv cr snw ly S U W mem md sp sp' fp f ap bp cp s0 n0 ws T cval MONO
  (HA & Hlo & Hhi & H16 & HK & Hp & Hfile & Hbp & Hck & Hdf & Hdc & F1 & F2 & C1 & C2 & Hcv & Hcb & Hcd & Hgc & Hgv &
   G1 & G2 & G3 & G4 & Hgcd & Hgvd & Hws & A1 & A2 & Ad & HFF & Hn & HT & Hs0 & Hsw & Hpw & Hdst & Ham & Hra & Hhull)
  L1 L2 HK' H16'.
unfold vf_rs in *. set (w := sn_len n0 T) in *.
assert (SUB : forall x, Forall (zdisjoint x) (vfp_out K sp s0 w fp cp) -> Forall (zdisjoint x) (vfp_out K' sp' s0 w fp cp)).
{ intros x Hx. apply Forall_vfp in Hx as (X1 & X2 & X3 & X4). apply Forall_vfp. split; [|tauto].
  apply (zdisjoint_sub x (sp - K, K)); [exact X1 | cbn [fst snd]; lia | cbn [fst snd]; lia]. }
unfold vf_pre, vf_rs. fold w.
split; [exact HA|]. split; [lia|]. split; [lia|]. split; [exact H16'|]. split; [exact HK'|].
split; [intros a Ha; apply Hp; lia|].
do 9 (split; [assumption|]). split; [exact Hcv|]. split; [exact Hcb|].
split; [rewrite Forall_forall in Hcd |- *; intros r Hr; exact (SUB r (Hcd r Hr))|].
do 6 (split; [assumption|]).
split; [exact (SUB _ Hgcd)|]. split; [exact (SUB _ Hgvd)|].
do 3 (split; [assumption|]). split; [exact (SUB _ Ad)|].
split.
{ apply (MONO _ (vfp_out K sp s0 w fp cp)); [exact HFF|].
  intros r' Hr'. unfold vfp_out in Hr'. destruct Hr' as [<-|[<-|[<-|[<-|[]]]]].
  - exists (sp - K, K). split; [left; reflexivity | cbn [fst snd]; lia].
  - exists (s0, w). split; [right; left; reflexivity | cbn [fst snd]; lia].
  - exists (fp, 232). split; [right; right; left; reflexivity | cbn [fst snd]; lia].
  - exists (cp, 16). split; [right; right; right; left; reflexivity | cbn [fst snd]; lia]. }
do 4 (split; [assumption|]).
split; [apply pairwise_vfp in Hpw; apply pairwise_vfp; unfold zdisjoint in *; cbn [fst snd] in *; lia|].
split; [exact Hdst|]. split; [exact Ham|]. split; assumption.
Qed.
Lemma vf_pcom : forall FF K Kp gc gv cr snw ly S U W mem md sp sp' fp f ap bp cp s0 n0 ws T cval,
  ff_mono FF ->
  vf_pre FF K gc gv cr snw ly S U W mem md sp fp f ap bp cp s0 n0 ws T cval ->
  sp - K <= sp' - Kp -> sp' <= sp ->
  consts_view tfibsegs W mem cr /\ Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr /\
  Forall (zdisjoint (sp' - Kp, Kp)) cr /\
  words_at (aview tfibsegs (H W) mem) ap ws /\ ap + 8 * Z.of_nat (length ws) < 2 ^ 63 /\
  zdisjoint (ap, 8 * Z.of_nat (length ws)) (sp' - Kp, Kp) /\
  FF (aview tfibsegs (H W) mem) [(sp' - Kp, Kp)] f ws T.
Proof.
intros FF K Kp gc gv cr snw ly S U W mem md sp sp' fp f ap bp cp s0 n0 ws T cval MONO
  (HA & Hlo & Hhi & H16 & HK & Hp & Hfile & Hbp & Hck & Hdf & Hdc & F1 & F2 & C1 & C2 & Hcv & Hcb & Hcd & Hgc & Hgv &
   G1 & G2 & G3 & G4 & Hgcd & Hgvd & Hws & A1 & A2 & Ad & HFF & _) L1 L2.
split; [exact Hcv|]. split; [exact Hcb|].
split.
{ rewrite Forall_forall in Hcd |- *. intros r Hr. pose proof (Hcd r Hr) as X. unfold vf_rs in X.
  apply Forall_vfp in X as (X1 & _). unfold zdisjoint in *. cbn [fst snd] in *. lia. }
split; [exact Hws|]. split; [exact A2|].
split; [unfold vf_rs in Ad; apply Forall_vfp in Ad as (X1 & _); unfold zdisjoint in *; cbn [fst snd] in *; lia|].
apply (MONO _ (vf_rs K sp s0 n0 T fp cp)); [exact HFF|].
intros r' Hr'. destruct Hr' as [<-|[]]. exists (sp - K, K). split; [left; reflexivity | cbn [fst snd]; lia].
Qed.
(* the vfprintf contract applied to the bundle *)
Lemma vf_apply : forall FF K gc gv img_lo img_hi cr snw pc ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval,
  sh_avfprintf_icpt_realizesU tfibsegs B FF K gc gv img_lo img_hi cr snw pc ->
  vf_pre FF K gc gv cr snw ly S U W mem md (spZ regs) fp f ap bp cp s0 n0 ws T cval ->
  zdisjoint (s0, sn_len n0 T) (img_lo, img_hi - img_lo) ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 fp -> getr regs 11 = w64 f -> getr regs 12 = w64 ap ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) (vf_post ly S U W regs mem md K fp cp s0 n0 T).
Proof.
intros FF K gc gv img_lo img_hi cr snw pc ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval HC Hp Hdog Hfrm Hra Hgp Htp R10 R11 R12.
pose proof (vf_ecall FF K gc gv cr snw ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval Hp Hra Hgp Htp) as HE.
pose proof (vf_dest_ok FF K gc gv cr snw ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval Hp) as (D1 & D2 & D3).
destruct Hp as (HA & Hlo & Hhi & H16 & HK & Hp & Hfile & Hbp & Hck & Hdf & Hdc & F1 & F2 & C1 & C2 & Hcv & Hcb & Hcd &
  Hgc & Hgv & G1 & G2 & G3 & G4 & Hgcd & Hgvd & Hws & A1 & A2 & Ad & HFF & Hn & HT & Hs0 & Hsw & Hpw & Hdst & Ham &
  Hra' & Hhull).
exact (HC ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval HE Hlo Hp R10 R11 R12 Hfile Hbp Hck D1 D2 F1 F2 C1 C2
  Hcv Hcb Hcd Hgc Hgv G1 G2 G3 G4 Hgcd Hgvd Hws A1 A2 Ad HFF Hn HT Hs0 Hsw Hpw D3 Ham Hra' Hhull Hdog Hfrm).
Qed.
(* ---- the GXA-route forms (FMsnprintfSx: sh_avsnprintf_realizesUa, sh_avsnprintf_icpt_realizesUa,
   sh_avfprintf_icpt_realizesUx): the same walks with the extra premises carried ---- *)
Definition sn_walkA (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
  forall ly S U W regs mem md d n f ap ws T cval,
  sn_pre FF K gc gv cr ly S U W mem md (spZ regs) d n f ap ws T cval ->
  zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo) ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  spZ regs <= ap ->
  (d + sn_len (n - 1) T <= spZ regs - K \/ ap + 8 * Z.of_nat (length ws) <= d) ->
  ap + 8 * Z.of_nat (length ws) <= 2 ^ 47 ->
  amem_range d (sn_len (n - 1) T + 8) ->
  YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f -> getr regs 13 = w64 ap ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) (sn_post ly S U W regs mem md K d n T).
Lemma sn_contractA : forall FF K gc gv img_lo img_hi cr pc, ESTACK <= K -> sn_walkA FF K gc gv img_lo img_hi cr pc ->
  sh_avsnprintf_realizesUa tfibsegs B FF K gc gv img_lo img_hi cr pc /\
  sh_avsnprintf_icpt_realizesUa tfibsegs B FF K gc gv img_lo img_hi cr pc.
Proof.
intros FF K gc gv img_lo img_hi cr pc HK HW. split;
intros ly S U W regs mem md d n f ap ws T cval Hpre HKlo HKp R10 R11 R12 R13 Hcv Hcb Hcd Hgc Hgv G1 G2 G3 G4 Hgcd Hgvd
  Hws A1 A2 Ad HFF Hn HT Hd0 Hdw Hpw Hdst Ham Hra Hhull Hdog Hfrm Hord Hsl H47 Hd8;
(pose proof (sn_pre_intro FF K gc gv cr ly S U W regs mem md d n f ap ws T cval HK Hpre HKlo HKp Hcv Hcb Hcd Hgc Hgv
   G1 G2 G3 G4 Hgcd Hgvd Hws A1 A2 Ad HFF Hn HT Hd0 Hdw Hpw Hdst Ham Hra Hhull) as P;
 pose proof Hpre as ((_ & Hret & _ & _ & _ & _ & Hgp & Htp) & _ & _);
 exact (HW ly S U W regs mem md d n f ap ws T cval P Hdog Hfrm Hord Hsl H47 Hd8 Hret Hgp Htp R10 R11 R12 R13)).
Qed.
Lemma sn_applyA : forall FF K gc gv img_lo img_hi cr pc ly S U W regs mem md d n f ap ws T cval,
  (sh_avsnprintf_realizesUa tfibsegs B FF K gc gv img_lo img_hi cr pc \/
   sh_avsnprintf_icpt_realizesUa tfibsegs B FF K gc gv img_lo img_hi cr pc) ->
  sn_pre FF K gc gv cr ly S U W mem md (spZ regs) d n f ap ws T cval ->
  zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo) ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  spZ regs <= ap ->
  (d + sn_len (n - 1) T <= spZ regs - K \/ ap + 8 * Z.of_nat (length ws) <= d) ->
  ap + 8 * Z.of_nat (length ws) <= 2 ^ 47 ->
  amem_range d (sn_len (n - 1) T + 8) ->
  YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f -> getr regs 13 = w64 ap ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) (sn_post ly S U W regs mem md K d n T).
Proof.
intros FF K gc gv img_lo img_hi cr pc ly S U W regs mem md d n f ap ws T cval HC Hp Hdog Hfrm Hord Hsl H47 Hd8 Hra Hgp Htp
  R10 R11 R12 R13.
pose proof (sn_ecall FF K gc gv cr ly S U W regs mem md d n f ap ws T cval Hp Hra Hgp Htp) as HE.
pose proof (sn_dest_ok FF K gc gv cr ly S U W regs mem md d n f ap ws T cval Hp) as HD.
destruct Hp as (HA & Hlo & Hhi & H16 & HK & Hp & Hcv & Hcb & Hcd & Hgc & Hgv & G1 & G2 & G3 & G4 & Hgcd & Hgvd & Hws &
  A1 & A2 & Ad & HFF & Hn & HT & Hd0 & Hdw & Hpw & Hdst & Ham & Hra' & Hhull).
destruct HC as [HC|HC];
  exact (HC ly S U W regs mem md d n f ap ws T cval HE Hlo Hp R10 R11 R12 R13 Hcv Hcb Hcd Hgc Hgv G1 G2 G3 G4 Hgcd Hgvd
    Hws A1 A2 Ad HFF Hn HT Hd0 Hdw Hpw HD Ham Hra' Hhull Hdog Hfrm Hord Hsl H47 Hd8).
Qed.
Definition vf_walkX (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (snw pc : Z) : Prop :=
  forall ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval,
  vf_pre FF K gc gv cr snw ly S U W mem md (spZ regs) fp f ap bp cp s0 n0 ws T cval ->
  zdisjoint (s0, sn_len n0 T) (img_lo, img_hi - img_lo) ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  aview tfibsegs (H W) mem s0 = Some 0 ->
  spZ regs <= fp -> fp + 232 <= cp -> cp + 16 <= ap ->
  (s0 + sn_len n0 T <= spZ regs - K \/ ap + 8 * Z.of_nat (length ws) <= s0) ->
  ap + 8 * Z.of_nat (length ws) <= 2 ^ 47 ->
  amem_range s0 (sn_len n0 T + 8) ->
  YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 fp -> getr regs 11 = w64 f -> getr regs 12 = w64 ap ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) (vf_post ly S U W regs mem md K fp cp s0 n0 T).
Lemma vf_contractX : forall FF K gc gv img_lo img_hi cr snw pc, ESTACK <= K -> vf_walkX FF K gc gv img_lo img_hi cr snw pc ->
  sh_avfprintf_icpt_realizesUx tfibsegs B FF K gc gv img_lo img_hi cr snw pc.
Proof.
intros FF K gc gv img_lo img_hi cr snw pc HK HW
  ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval Hpre HKlo HKp R10 R11 R12 Hfile Hbp Hck Hdf Hdc F1 F2 C1 C2
  Hcv Hcb Hcd Hgc Hgv G1 G2 G3 G4 Hgcd Hgvd Hws A1 A2 Ad HFF Hn HT Hs0 Hsw Hpw Hdst Ham Hra Hhull Hdog Hfrm
  Hnul Ho1 Ho2 Ho3 Hsl H47 Hd8.
pose proof (vf_pre_intro FF K gc gv cr snw ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval HK Hpre HKlo HKp
  Hfile Hbp Hck Hdf Hdc F1 F2 C1 C2 Hcv Hcb Hcd Hgc Hgv G1 G2 G3 G4 Hgcd Hgvd Hws A1 A2 Ad HFF Hn HT Hs0 Hsw Hpw
  Hdst Ham Hra Hhull) as P.
pose proof Hpre as ((_ & Hret & _ & _ & _ & _ & Hgp & Htp) & _ & _).
exact (HW ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval P Hdog Hfrm Hnul Ho1 Ho2 Ho3 Hsl H47 Hd8 Hret Hgp Htp
  R10 R11 R12).
Qed.
Lemma vf_applyX : forall FF K gc gv img_lo img_hi cr snw pc ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval,
  sh_avfprintf_icpt_realizesUx tfibsegs B FF K gc gv img_lo img_hi cr snw pc ->
  vf_pre FF K gc gv cr snw ly S U W mem md (spZ regs) fp f ap bp cp s0 n0 ws T cval ->
  zdisjoint (s0, sn_len n0 T) (img_lo, img_hi - img_lo) ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  aview tfibsegs (H W) mem s0 = Some 0 ->
  spZ regs <= fp -> fp + 232 <= cp -> cp + 16 <= ap ->
  (s0 + sn_len n0 T <= spZ regs - K \/ ap + 8 * Z.of_nat (length ws) <= s0) ->
  ap + 8 * Z.of_nat (length ws) <= 2 ^ 47 ->
  amem_range s0 (sn_len n0 T + 8) ->
  YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 fp -> getr regs 11 = w64 f -> getr regs 12 = w64 ap ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) (vf_post ly S U W regs mem md K fp cp s0 n0 T).
Proof.
intros FF K gc gv img_lo img_hi cr snw pc ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval HC Hp Hdog Hfrm
  Hnul Ho1 Ho2 Ho3 Hsl H47 Hd8 Hra Hgp Htp R10 R11 R12.
pose proof (vf_ecall FF K gc gv cr snw ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval Hp Hra Hgp Htp) as HE.
pose proof (vf_dest_ok FF K gc gv cr snw ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval Hp) as (D1 & D2 & D3).
destruct Hp as (HA & Hlo & Hhi & H16 & HK & Hp & Hfile & Hbp & Hck & Hdf & Hdc & F1 & F2 & C1 & C2 & Hcv & Hcb & Hcd &
  Hgc & Hgv & G1 & G2 & G3 & G4 & Hgcd & Hgvd & Hws & A1 & A2 & Ad & HFF & Hn & HT & Hs0 & Hsw & Hpw & Hdst & Ham &
  Hra' & Hhull).
exact (HC ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval HE Hlo Hp R10 R11 R12 Hfile Hbp Hck D1 D2 F1 F2 C1 C2
  Hcv Hcb Hcd Hgc Hgv G1 G2 G3 G4 Hgcd Hgvd Hws A1 A2 Ad HFF Hn HT Hs0 Hsw Hpw D3 Ham Hra' Hhull Hdog Hfrm
  Hnul Ho1 Ho2 Ho3 Hsl H47 Hd8).
Qed.
End k.
