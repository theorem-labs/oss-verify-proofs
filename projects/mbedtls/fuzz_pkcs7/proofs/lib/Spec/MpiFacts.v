(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX MpiCoreAux HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MpiFacts () : Init.string Init.list := ["OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "Corelib.Lists.ListDef.Forall"; "OSSVerify.KrLib.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "OSSVerify.KrLib.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.HeapIface.lb_remove"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "OSSVerify.KrLib.Spec.MpiVal.mpd_blk"; "OSSVerify.KrLib.Spec.MpiVal.mpd_out"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.Lib.Frame.disjoint_from"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.Lib.HeapIface.heap_layout"; "OSSVerify.KrLib.Lib.Frame.outside"; "OSSVerify.KrLib.Lib.HeapIface.blocks_apart"; "OSSVerify.KrLib.Lib.HeapIface.heap_iface"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "OSSVerify.KrLib.Lib.HeapIface.client_addr"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.Lib.Cells.C2"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Lib.Mem.ro_bytes"; "OSSVerify.KrLib.Spec.Rep.mpi_cells"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.Spec.MpiVal.md_pad"].


(* [comment removed for export] *)
Lemma heap_presx_frame segs L LB (SP : Z) X m m' (lo' : Z) : ltac2:(CDefT.buildp (gd_tbl_MpiFacts ()) "P,(0.(1.(2.$3.$3.)(4.$3.$3.O1.O5.)(5.(2.$3.$3.)))O3.O2.)P,(6.O8.O3.O2.)P,(7.(2.$3.$3.)Lb,(2.$3.$3.)(8.O7.(9.$3.$3.R1.)(:.$3.$3.R1.))O6.)P,(;.(<.O7.)(=.O7.))P,(;.(=.O7.)O1.)(>.O8.O7.O6.O5.O4.O3.O2.)")
(* [comment removed for export] *).
Proof.
  intros MU WM HBR DHI LO. eapply heap_presx_of_munch; [exact MU| exact WM|].
  intros a Ha Hc Ho. cbn. split; [|exact I].
  destruct Hc as [C|[C|([B k] & Hb & C)]]; [lia| lia|].
  pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (_ & _ & _ & B4 & _). cbn in C, B4. lia.
Qed.

Lemma statics_ok_frame segs L m m' (lo' hi' : Z) :
  statics_ok segs L m -> munch [(lo', hi')] m m' -> hl_data_hi L <= lo' -> statics_ok segs L m'.
Proof.
  intros SOK MU LE. eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Ha _. cbn. split; [lia| exact I].
Qed.

Lemma mpd_out_refl : forall LB d, md_own d <> LStatic -> mpd_out LB d LB d.
Proof. intros LB d H. unfold mpd_out. repeat split; auto. Qed.

(* [comment removed for export] *)
Lemma nodup_fst_neq : ltac2:(CDefT.buildp (gd_tbl_MpiFacts ()) "PLB,(?.$10.)PA,$3.Pn,$3.PB,$3.Pk,$3.P,(11.$3.(12.(2.$3.$3.)$3.(9.$3.$3.)R5.))P,(13.(2.$3.$3.)(4.$3.$3.R5.R4.)R6.)P,(13.(2.$3.$3.)(4.$3.$3.R4.R3.)R7.)P,(14.(15.(2.$3.$3.)(4.$3.$3.R5.R4.)(4.$3.$3.R7.R6.)))(14.(15.$3.R6.R8.))")
(* [comment removed for export] *).
Proof.
  induction LB as [|[C j] r IH]; cbn; intros A n B k ND H1 H2 NE; [destruct H1|].
  inversion ND as [|x l Hni ND']; subst.
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - exfalso. apply NE. congruence.
  - injection E1 as -> ->. intros ->. apply Hni. apply in_map_iff. exists (A, k). split; [reflexivity| exact H2].
  - injection E2 as -> ->. intros ->. apply Hni. apply in_map_iff. exists (A, n). split; [reflexivity| exact H1].
  - eapply IH; eassumption.
Qed.

Lemma lb_remove_notin : forall (l : list blk) P k, List.NoDup (map fst l) -> ~ In (P, k) (lb_remove P l).
Proof.
  induction l as [|[C j] l IH]; cbn; intros P k NDl Hc; [exact Hc|]. apply List.NoDup_cons_iff in NDl as [Hni NDl'].
  destruct (Z.eqb_spec C P) as [->|NE].
  - apply Hni. apply in_map_iff. exists (P, k). split; [reflexivity| exact Hc].
  - destruct Hc as [E|Hc]; [injection E; lia|]. exact (IH _ _ NDl' Hc).
Qed.

(* [comment removed for export] *)
Lemma in_lb_remove_other : ltac2:(CDefT.buildp (gd_tbl_MpiFacts ()) "PLB,(?.$10.)PP,$3.Pn,$3.PB,$3.Pk,$3.P,(11.$3.(12.(2.$3.$3.)$3.(9.$3.$3.)R5.))P,(13.(2.$3.$3.)(4.$3.$3.R5.R4.)R6.)P,(13.(2.$3.$3.)(4.$3.$3.R4.R3.)R7.)P,(14.(15.(2.$3.$3.)(4.$3.$3.R5.R4.)(4.$3.$3.R7.R6.)))(13.(2.$3.$3.)(4.$3.$3.R6.R5.)(16.R8.R9.))")
(* [comment removed for export] *).
Proof.
  intros LB P n B k ND HP HB NE. apply In_lb_remove_keep; [exact HB|]. exact (nodup_fst_neq LB P n B k ND HP HB NE).
Qed.

(* [comment removed for export] *)
Lemma pointwise_apart : ltac2:(CDefT.buildp (gd_tbl_MpiFacts ()) "PX,$3.Pk,$3.PA,$3.Pn,$3.P,(17.=R3.)P,(17.=R2.)P,Pa,$3.P,(18.(;.R7.R1.)(17.R1.(19.R7.R6.)))(14.(18.(;.R6.R2.)(17.R2.(19.R6.R5.))))(1:.(;.(19.R7.R6.)R5.)(;.(19.R5.R4.)R7.))")
(* [comment removed for export] *).
Proof.
  intros X k A n Hk Hn H.
  destruct (Z.le_gt_cases X A); [left; destruct (Z.le_gt_cases (X + k) A); [lia| exfalso; apply (H A); lia]
                                | right; destruct (Z.le_gt_cases (A + n) X); [lia| exfalso; apply (H X); lia]].
Qed.

(* [comment removed for export] *)
Lemma lor_land3_zero : forall a b, 0 <= a -> 0 <= b -> a mod 4 = 0 -> b mod 4 = 0 -> Z.land (Z.lor a b) 3 = 0.
Proof.
  intros a b Ha Hb Ma Mb. rewrite Z.land_lor_distr_l.
  change 3 with (Z.ones 2). rewrite !Z.land_ones by lia. change (2 ^ 2) with 4. rewrite Ma, Mb. reflexivity.
Qed.

Lemma mpd_out_same_blocks : ltac2:(CDefT.buildp (gd_tbl_MpiFacts ()) "PLB,(?.$10.)PdX,$1;.PdX',$1;.P,(15.$3.(1<.R1.)(1<.R2.))P,(14.(15.$1=.(1>.R2.)$1?.))P,(15.(?.$10.)(20.R3.)(20.R4.))(21.R6.R5.R6.R4.)")
(* [comment removed for export] *).
Proof.
  intros LB dX dX' HA HO HB. unfold mpd_out. rewrite HB. repeat split; auto.
Qed.

(* [comment removed for export] *)
Lemma mpd_at_munch : ltac2:(CDefT.buildp (gd_tbl_MpiFacts ()) "Psegs,(?.$22.)Pm,P,(23.&40.)(24.(23.&8.))Pm',P,(23.&40.)(24.(23.&8.))PLB,(?.$10.)Pd,$1;.PW,(?.$25.)P,(26.R6.R5.R3.R2.)P,(14.(15.$1=.(1>.R3.)$1?.))P,(0.R3.R7.R6.)P,(6.R9.R8.R7.)P,(27.R5.(1<.R6.)+10.)P,P,(15.$1=.(1>.R7.)$28.)(27.R7.(29.R8.)(2:.+4.(2;.R8.)))(26.R<.R:.R9.R8.)")
(* [comment removed for export] *).
Proof.
  intros segs m m' LB d W [HA HS] HNS MU WM HD1 HD2. split; [| exact HS].
  destruct HA as (HR & HAL & HPOS & HL & HN & HO).
  split; [| split; [exact HAL| split; [exact HPOS| split; [exact HL| split; [exact HN|]]]]].
  - eapply rw_cells_transport; [exact HR| exact MU| exact WM| exact HD1].
  - destruct (md_own d); [exact HO| | exfalso; exact (HNS eq_refl)].
    destruct HO as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    eapply u32arr_transport; [exact H4| exact MU| exact WM|]. rewrite HL. apply HD2. reflexivity.
Qed.

Lemma heap_presx_weaken : ltac2:(CDefT.buildp (gd_tbl_MpiFacts ()) "Psegs,(?.$22.)PL,$2<.PLB,(?.$10.)PSP,$3.PSP',$3.PX,(?.$25.)PX',(?.$25.)Pm,P,(23.&40.)(24.(23.&8.))Pm',P,(23.&40.)(24.(23.&8.))P,(>.R9.R8.R7.R6.R4.R2.R1.)P,(;.R7.R6.)P,Pa,$3.P,(2=.R6.R1.)(2=.R8.R2.)(>.R<.R;.R:.R8.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros segs L LB SP SP' X X' m m' H HS HX a Ha Hc Ho. apply H; [exact Ha| | apply HX; exact Ho].
  destruct Hc as [Hs|[Hd|Hb]]; [left; lia| right; left; exact Hd| right; right; exact Hb].
Qed.

(* [comment removed for export] *)
Lemma blocks_apart_neq : ltac2:(CDefT.buildp (gd_tbl_MpiFacts ()) "PLB,(?.$10.)Pb1,$10.Pb2,$10.P,(2>.R3.)P,(13.$10.R3.R4.)P,(13.$10.R3.R5.)P,(14.(15.$10.R5.R4.))P,(17.=(:.$3.$3.R6.))P,(17.=(:.$3.$3.R6.))(1:.(;.(19.(9.$3.$3.R8.)(:.$3.$3.R8.))(9.$3.$3.R7.))(;.(19.(9.$3.$3.R7.)(:.$3.$3.R7.))(9.$3.$3.R8.)))")
(* [comment removed for export] *).
Proof.
  induction LB as [|[C j] r IH]; cbn; intros b1 b2 HA H1 H2 HNE P1 P2; [destruct H1|].
  destruct HA as [HC Hr].
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - exfalso. apply HNE. congruence.
  - subst b1. destruct b2 as [B k]. cbn in *. exact (HC B k H2).
  - subst b2. destruct b1 as [B k]. cbn in *. destruct (HC B k H1); lia.
  - apply IH; assumption.
Qed.

(* [comment removed for export] *)
Lemma mpd_out_ext : ltac2:(CDefT.buildp (gd_tbl_MpiFacts ()) "PLB,(?.$10.)PdX,$1;.PLB',(?.$10.)Pd1,$1;.Pd2,$1;.P,(21.R5.R4.R3.R2.)P,(15.$3.(1<.R2.)(1<.R3.))P,(14.(15.$1=.(1>.R3.)$1?.))P,(15.(?.$10.)(20.R4.)(20.R5.))(21.R9.R8.R7.R5.)")
(* [comment removed for export] *).
Proof.
  intros LB dX LB' d1 d2 (A1 & O1 & K1 & K2 & K3) HA HO HB. unfold mpd_out. rewrite HA, HB. repeat split; auto.
Qed.

(* [comment removed for export] *)
Lemma new_limbs_apart : ltac2:(CDefT.buildp (gd_tbl_MpiFacts ()) "Psegs,(?.$22.)PL,$2<.PHI,(2?.R2.R1.)Ph',(30.R3.R2.R1.)PLB,(?.$10.)PLB',(?.$10.)Pm,P,(23.&40.)(24.(23.&8.))Pm',P,(23.&40.)(24.(23.&8.))Pmo',$31.PSP,$3.PdX,$1;.PdX',$1;.Pa,$3.P,(32.R=.R<.R;.R:.R8.R6.R5.)P,(26.R>.R8.R9.R3.)P,(21.R;.R5.R:.R4.)P,Pb,$10.P,(13.$10.R1.(20.R6.))(1:.(13.$10.R2.(20.R8.))(14.(13.$10.R2.R>.)))P,(;.(=.R10.)R8.)P,(;.(33.R11.)(34.R11.))P,(;.(<.R12.)(35.R12.))P,(36.R13.R10.R;.R8.)P,P,(15.$1=.(1>.R;.)$28.)(14.(18.(;.(29.R<.)R:.)(17.R:.(19.(29.R<.)(2:.+4.(2;.R<.))))))P,(15.$1=.(1>.R;.)$28.)(14.(18.(;.(29.R<.)R;.)(17.R;.(19.(29.R<.)(2:.+4.(2;.R<.))))))")
(* [comment removed for export] *).
Proof.
  intros segs L HI h' LB LB' m m' mo' SP dX dX' a HH [HA _] HOUT HF ACL DIM1 DIM2 Hc Ho HO C.
  destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP]. rewrite Forall_forall in HBR.
  destruct HA as (_ & _ & _ & HL & HN & HOWN). rewrite HO in HOWN. destruct HOWN as (HN1 & HIN & _ & _).
  pose proof (HBR _ HIN) as (_ & _ & _ & B4 & B5). cbn [fst snd] in B4, B5.
  destruct (HF (md_p dX', 4 * md_n dX') ltac:(unfold mpd_blk; rewrite HO; left; reflexivity)) as [HOLD|HNEW].
  - (* [comment removed for export] *)
    unfold mpd_blk in HOLD. destruct (md_own dX) eqn:EO; try (destruct HOLD; fail).
    destruct HOLD as [E|[]]. injection E as E1 E2. pose proof (Ho eq_refl). lia.
  - destruct Hc as [Hs|[[Hd _]|([B k] & Hb & R)]]; [lia| lia|].
    destruct HOUT as (_ & _ & _ & HK & _).
    assert (HbLB' : In (B, k) LB').
    { apply HK; [exact Hb|]. unfold mpd_blk. destruct (md_own dX) eqn:EO; try (intros []; fail).
      intros [E|[]]. injection E as <- <-. cbn in R. pose proof (Ho eq_refl). lia. }
    assert (NE : (B, k) <> (md_p dX', 4 * md_n dX')) by (intros E; rewrite E in Hb; exact (HNEW Hb)).
    cbn in R.
    destruct (blocks_apart_neq _ _ _ HAP HbLB' HIN NE ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia.
Qed.

(* [comment removed for export] *)
Lemma new_limbs_apart_range : ltac2:(CDefT.buildp (gd_tbl_MpiFacts ()) "Psegs,(?.$22.)PL,$2<.PHI,(2?.R2.R1.)Ph',(30.R3.R2.R1.)PLB,(?.$10.)PLB',(?.$10.)Pm,P,(23.&40.)(24.(23.&8.))Pm',P,(23.&40.)(24.(23.&8.))Pmo',$31.PSP,$3.PdX,$1;.PdX',$1;.PA,$3.Pn,$3.P,(32.R>.R=.R<.R;.R9.R7.R6.)P,(26.R?.R9.R:.R4.)P,(21.R<.R6.R;.R5.)P,Pb,$10.P,(13.$10.R1.(20.R7.))(1:.(13.$10.R2.(20.R9.))(14.(13.$10.R2.R?.)))P,(;.(=.R11.)R9.)P,(;.(33.R12.)(34.R12.))P,(;.(<.R13.)(35.R13.))P,Pa,$3.P,(18.(;.R:.R1.)(17.R1.(19.R:.R9.)))(36.R16.R13.R>.R2.)P,(17.=R9.)P,P,(15.$1=.(1>.R=.)$28.)(1:.(;.(19.R<.R;.)(29.R>.))(;.(19.(29.R>.)(2:.+4.(2;.R>.)))R<.))P,(15.$1=.(1>.R=.)$28.)(1:.(;.(19.R=.R<.)(29.R>.))(;.(19.(29.R>.)(2:.+4.(2;.R>.)))R=.))")
(* [comment removed for export] *).
Proof.
  intros segs L HI h' LB LB' m m' mo' SP dX dX' A n HH HA HOUT HF ACL DIM1 DIM2 CR Hn D2 HO.
  pose proof HA as [[_ (_ & _ & HL & HN & HOWN)] _]. rewrite HO in HOWN. destruct HOWN as (HN1 & _).
  apply pointwise_apart; [exact Hn| lia|]. intros a Ha.
  eapply (new_limbs_apart segs L HI); try eassumption; [apply CR; exact Ha|].
  intros HOX. destruct (D2 HOX); lia.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_C2_congr : ltac2:(CDefT.buildp (gd_tbl_MpiFacts ()) "Psegs,(?.$22.)Pm,P,(23.&40.)(24.(23.&8.))PA,$3.Ppre,(?.$37.)Pa,$3.Pb,$3.Ppost,(?.$37.)P,(38.R7.R6.R5.(39.$37.R4.(1.$37.(3:.(3;.&40.R3.))R1.)))P,(15.$3.(3<.R4.(3=.+2.+10.))(3<.R3.(3=.+2.+10.)))(38.R9.R8.R7.(39.$37.R6.(1.$37.(3:.(3;.&40.R4.))R3.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A pre a b post H E. eapply rw_cells_reshape; [exact H| |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [H1 [_ H3]].
    apply cells_wf_app. split; [exact H1|]. cbn. split; [exact I| exact H3].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite !le2_of_Z.
    rewrite <- (Z_to_le_bytes_mod 2 a), <- (Z_to_le_bytes_mod 2 b). change (8 * Z.of_nat 2) with 16. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma to_sign_mod16 : forall z, -2^31 <= z < 2^31 ->
  Z.lor ((z mod 2^64) ≫ 30) 1 mod 2^16 = (if z <? 0 then -1 else 1) mod 2^16.
Proof.
  intros z Hz. rewrite Z.shiftr_div_pow2 by lia.
  destruct (Z.ltb_spec z 0) as [Hn|Hp].
  - replace (z mod 2^64) with (2^64 + z) by (replace z with ((2^64 + z) + (-1) * 2^64) at 2 by lia; rewrite Z.mod_add by lia; symmetry; apply Z.mod_small; lia).
    assert (C : (2^64 + z) / 2^30 = 17179869182 \/ (2^64 + z) / 2^30 = 17179869183) by lia.
    destruct C as [-> | ->]; reflexivity.
  - rewrite (Z.mod_small z (2^64)) by lia.
    assert (C : z / 2^30 = 0 \/ z / 2^30 = 1) by lia.
    destruct C as [-> | ->]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_ro_bytes : ltac2:(CDefT.buildp (gd_tbl_MpiFacts ()) "Psegs,(?.$22.)Pm,P,(23.&40.)(24.(23.&8.))PA,$3.Pbs,(?.(23.&8.))P,(3>.R4.R3.)P,(3?.R5.R4.R3.R2.)P,Pi,$3.P,(18.(;.=R1.)(17.R1.(40.(41.(23.&8.)R4.))))(15.$42.(43.R8.(44.(19.R6.R2.)))$45.)(46.R7.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros segs m A bs MI (HA & HL & HB) HR. revert A HA HL HB HR.
  induction bs as [|b bs IH]; intros A HA HL HB HR; cbn; [exact I|]. cbn in HL. split.
  - pose proof (HR 0 ltac:(cbn; lia)) as RA. rewrite Z.add_0_r in RA.
    split; [| exact RA]. pose proof (HB 0%nat ltac:(cbn; lia)) as R0. cbn in R0. rewrite Z.add_0_r in R0.
    unfold mrd in R0. destruct (m (wa A)) eqn:E; [| exact R0].
    exfalso. pose proof (MI _ _ E) as C. congruence.
  - apply IH; [lia| lia| |].
    + intros i Hi. replace (A + 1 + Z.of_nat i) with (A + Z.of_nat (S i)) by lia. apply (HB (S i)). cbn; lia.
    + intros i Hi. replace (A + 1 + i) with (A + (1 + i)) by lia. apply HR. cbn; lia.
Qed.

Lemma static_limbs_any_mem : ltac2:(CDefT.buildp (gd_tbl_MpiFacts ()) "Psegs,(?.$22.)Pm,P,(23.&40.)(24.(23.&8.))Pm',P,(23.&40.)(24.(23.&8.))PA,$3.Pbs,(?.(23.&8.))P,(3>.R5.R4.)P,(3>.R6.R4.)P,(3?.R7.R6.R4.R3.)P,Pi,$3.P,(18.(;.=R1.)(17.R1.(40.(41.(23.&8.)R5.))))(15.$42.(43.R:.(44.(19.R7.R2.)))$45.)(3?.R9.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros segs m m' A bs MI MI' HB HR. pose proof HB as (HA & HL & _).
  apply ro_bytes_at; [exact MI'| lia| lia| exact (bytes_at_ro_bytes segs m A bs MI HB HR)].
Qed.

(* [comment removed for export] *)
Lemma mpd_at_static : ltac2:(CDefT.buildp (gd_tbl_MpiFacts ()) "Psegs,(?.$22.)Pm,P,(23.&40.)(24.(23.&8.))Pm',P,(23.&40.)(24.(23.&8.))PLB,(?.$10.)PLB',(?.$10.)Pd,$1;.P,(26.R6.R5.R3.R1.)P,(15.$1=.(1>.R2.)$1?.)P,(3>.R8.R7.)P,(3>.R9.R7.)P,(38.R:.R8.(1<.R5.)(47.(29.R5.)(3;.&40.(48.R5.))(2;.R5.)(49.R5.)))(26.R;.R9.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros segs m m' LB LB' d [[_ (AL & A0 & HL & HN & HO)] SG] EO MI MI' CH. rewrite EO in HO.
  destruct HO as (N1 & PAL & PP & HB & HR). split; [| exact SG].
  split; [exact CH|]. split; [exact AL|]. split; [exact A0|]. split; [exact HL|]. split; [exact HN|]. rewrite EO.
  split; [exact N1|]. split; [exact PAL|]. split; [exact PP|]. split; [| exact HR].
  eapply static_limbs_any_mem; [exact MI| exact MI'| exact HB|]. rewrite u32s_length. intros i Hi. apply HR. lia.
Qed.
