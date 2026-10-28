(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib MemsetLib.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibSym. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0RegionPoisoned_b Ba0AsanMemset_b Ba0AsanMemcpy_b Ba0MemsetIcpt_b Ba0MemcpyIcpt_b Ba0TlsGetAddr_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import XIcptA_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).

Lemma kept_ok_of_keeps_cs : forall regs regs', keeps_cs regs regs' -> APSX.kept_ok regs regs'.
Proof.
  intros regs regs' Hk r Hr0 Hnin. apply Hk.
  pose proof (AX2S.ridx_range r) as Hrr.
  assert (Hr : AX2.ridx r <> 0%nat).
  { intros X. apply Hr0. rewrite (APSX.reg_of_ridx r 0 X). apply bv_eq. reflexivity. }
  unfold AP.caller_saved in Hnin. cbn [In] in Hnin.
  assert (E : exists k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat /\ AX2.ridx r = k).
  { exists (AX2.ridx r). split; [|reflexivity]. cbn [In]. lia. }
  destruct E as (k & Hink & Hrk). rewrite (APSX.reg_of_ridx r k Hrk).
  cbn [In] in Hink. unfold callee_saved.
  repeat (destruct Hink as [<-|Hink]; [in_list|]). destruct Hink.
Qed.

Lemma cell_of : forall (M : word -> option byte) a w v,
  XIA.cells_ok ASEGS XIA.AS0_CELLS M -> In (a, w, v) XIA.AS0_CELLS ->
  rdn ASEGS M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)).
Proof. intros M a w v H Hin. unfold XIA.cells_ok in H. rewrite Forall_forall in H. exact (H _ Hin). Qed.

(* [comment removed for export] *)
Lemma shadow_facts : forall (mem0 : word -> option byte) p n,
  1 <= n -> 0 <= p -> p + n + 8 <= XIA.HIGHEND -> XIA.shadow_ok mem0 p n ->
  let fD := Ba0RegionPoisoned_b.SB + p / 8 in let lD := Ba0RegionPoisoned_b.SB + (p + n - 1) / 8 in
  exists kD,
    (forall x : word, fD <= bv_unsigned x < lD -> mem0 x = Some (Z_to_bv 8 0)) /\
    mem0 (Z_to_bv 64 lD) = Some (Z_to_bv 8 kD) /\ (kD = 0 \/ (p + n - 1) mod 8 < kD <= 7) /\
    (n <= 64 -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 (fD - fD mod 8)) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 (lD - lD mod 8)) 8%nat = Some w1).
Proof.
  intros mem0 p n Hn Hp Hpn (HZ & (kD & HL & HkD) & HD) fD lD.
  assert (Dv1 : 0 <= p / 8) by (apply Z.div_pos; lia).
  assert (Dv2 : p / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (Dv3 : (p + n - 1) / 8 <= XIA.HIGHEND) by (apply Z.div_le_upper_bound; unfold XIA.HIGHEND in *; lia).
  assert (EfD : fD = XIA.SB + p / 8) by reflexivity. assert (ElD : lD = XIA.SB + (p + n - 1) / 8) by reflexivity.
  pose proof (Z.mod_pos_bound fD 8 ltac:(lia)) as MfD. pose proof (Z.mod_pos_bound lD 8 ltac:(lia)) as MlD.
  pose proof (Z.div_mod fD 8 ltac:(lia)) as DfD. pose proof (Z.div_mod lD 8 ltac:(lia)) as DlD.
  assert (RNG : 2 ^ 20 <= fD /\ fD <= lD /\ lD + 8 < 2 ^ 64) by (unfold XIA.SB, XIA.HIGHEND in *; lia).
  exists kD. split; [intros x Hx; apply HZ; lia|]. split; [exact HL|]. split; [exact HkD|].
  intros Hn64. specialize (HD Hn64). fold fD lD in HD. rewrite <- EfD, <- ElD in HD.
  assert (RD8 : forall a, 8 * (fD / 8) <= a -> a + 8 <= 8 * (lD / 8) + 8 -> exists w, rdn ASEGS mem0 (Z_to_bv 64 a) 8%nat = Some w).
  { intros a Ha1 Ha2.
    destruct (AX2S.rdn_defined ASEGS mem0 8%nat (Z_to_bv 64 a)) as (bs & Hbs & _).
    - rewrite u64_of_Z by lia. cbn. lia.
    - intros j Hj. rewrite u64_of_Z by lia. unfold AX2S.rd1.
      destruct (mem0 (Z_to_bv 64 (a + Z.of_nat j))) eqn:Hm; [discriminate|]. exfalso.
      refine (HD (Z_to_bv 64 (a + Z.of_nat j)) _ Hm). rewrite u64_of_Z by lia. lia.
    - exists bs. exact Hbs. }
  destruct (RD8 (fD - fD mod 8) ltac:(lia) ltac:(lia)) as (w0 & W0). destruct (RD8 (lD - lD mod 8) ltac:(lia) ltac:(lia)) as (w1 & W1).
  exists w0, w1. split; assumption.
Qed.

Lemma layout_of_cells : forall mem0, XIA.cells_ok ASEGS XIA.AS0_CELLS mem0 -> rt_layout_globs mem0.
Proof.
  intros mem0 Hcells. unfold rt_layout_globs. repeat split;
    match goal with |- rdn _ _ ?a ?w = Some (word_to_le_bytes _ (Z_to_bv 64 ?v)) =>
      replace a with (Z_to_bv 64 (bv_unsigned a)) by (apply Z_to_bv_bv_unsigned); apply (cell_of mem0 _ w v Hcells); in_list end.
Qed.

Theorem as0_icpt_fill : XIA.icpt_fill_spec ASEGS XIA.AS0_MSET XIA.AS0_CELLS.
Proof.
  intros fx mem0 c pd n sp regs ret Hn Happ Hs Hs' Hsh Hdj Hok Hdst Hcells Hshz Hret H1 H2 H10 H11 H12.
  unfold XIA.SCR in *.
  assert (Hpd : 0 <= pd /\ pd + n + 8 <= XIA.HIGHEND) by (unfold XIA.app8, XIA.LOWEND, XIA.HIGHBEG, XIA.HIGHEND in *; lia).
  destruct (shadow_facts mem0 pd n ltac:(lia) ltac:(lia) ltac:(lia) Hshz) as (kD & HZD & HLD & HkD & HWD).
  set (fD := Ba0RegionPoisoned_b.SB + pd / 8) in *. set (lD := Ba0RegionPoisoned_b.SB + (pd + n - 1) / 8) in *.
  assert (ElD : lD = XIA.SB + (pd + n - 1) / 8) by reflexivity.
  destruct (@wrap_memset_run fx mem0 (seg_rom ASEGS) (Z_to_bv 64 sp) ret c pd n sp kD fD lD (fD - fD mod 8) (lD - lD mod 8)) with (regs := regs)
    as (regs' & Mj & RUN & Q10 & Q2 & Q1 & KCS & OUT & GR).
  - apply u64_of_Z. lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Happ.
  - lia.
  - lia.
  - lia.
  - apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (sp - 2560)) _ 2560%nat); [rewrite !u64_of_Z by lia; lia | exact Hok | rewrite !u64_of_Z by lia; lia | rewrite !u64_of_Z by lia; cbn; lia].
  - exact Hdst.
  - exact Hret.
  - apply layout_of_cells. exact Hcells.
  - unfold ms_icpt_globs. repeat split.
    + replace (0x138028%bv : word) with (Z_to_bv 64 0x138028) by (apply bv_eq; reflexivity). apply (cell_of mem0 _ 8%nat 0x140919 Hcells). in_list.
    + replace (0x140919%bv : word) with (Z_to_bv 64 0x140919) by (apply bv_eq; reflexivity).
      rewrite (cell_of mem0 0x140919 1%nat 1 Hcells) by in_list. reflexivity.
    + replace (0x1394d0%bv : word) with (Z_to_bv 64 0x1394d0) by (apply bv_eq; reflexivity). apply (cell_of mem0 _ 8%nat 0x129d04 Hcells). in_list.
  - intros _ x Hx. apply HZD. exact Hx.
  - intros _. exact HLD.
  - exact HkD.
  - intros [_ Hn64]. exact (HWD Hn64).
  - exact H10.
  - exact H11.
  - exact H12.
  - rewrite H2. reflexivity.
  - exact H1.
  - exists regs', Mj. split.
    + replace (Z_to_bv 64 XIA.AS0_MSET) with (0x77c88%bv : word) by (apply bv_eq; reflexivity). exact RUN.
    + split; [apply kept_ok_of_keeps_cs; exact KCS|]. split; [exact Q10|]. split; [|exact GR].
      intros x Hx. apply OUT. lia.
Qed.

Theorem as0_icpt_copy : XIA.icpt_copy_spec ASEGS XIA.AS0_MCPY XIA.AS0_CELLS.
Proof.
  intros fx mem0 pd ps n sp bs regs ret Hn Hlbs HappD HappS Hs Hs' HshD HshS HdjD HdjS Hover Hok Hdst Hsrc Hcells HshzD HshzS Hret H1 H2 H10 H11 H12.
  unfold XIA.SCR in *.
  assert (Hpd : 0 <= pd /\ pd + n + 8 <= XIA.HIGHEND) by (unfold XIA.app8, XIA.LOWEND, XIA.HIGHBEG, XIA.HIGHEND in *; lia).
  assert (Hps : 0 <= ps /\ ps + n + 8 <= XIA.HIGHEND) by (unfold XIA.app8, XIA.LOWEND, XIA.HIGHBEG, XIA.HIGHEND in *; lia).
  destruct (shadow_facts mem0 pd n ltac:(lia) ltac:(lia) ltac:(lia) HshzD) as (kD & HZD & HLD & HkD & HWD).
  destruct (shadow_facts mem0 ps n ltac:(lia) ltac:(lia) ltac:(lia) HshzS) as (kS & HZS & HLS & HkS & HWS).
  set (fD := Ba0RegionPoisoned_b.SB + pd / 8) in *. set (lD := Ba0RegionPoisoned_b.SB + (pd + n - 1) / 8) in *.
  set (fS := Ba0RegionPoisoned_b.SB + ps / 8) in *. set (lS := Ba0RegionPoisoned_b.SB + (ps + n - 1) / 8) in *.
  assert (ElD : lD = XIA.SB + (pd + n - 1) / 8) by reflexivity. assert (ElS : lS = XIA.SB + (ps + n - 1) / 8) by reflexivity.
  destruct (@wrap_memcpy_run fx mem0 (seg_rom ASEGS) (Z_to_bv 64 sp) ret pd ps n sp bs kS fS lS (fS - fS mod 8) (lS - lS mod 8) kD fD lD (fD - fD mod 8) (lD - lD mod 8))
    with (regs := regs) as (regs' & Mj & RUN & Q10 & Q2 & Q1 & KCS & OUT & GR).
  - apply u64_of_Z. lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact HappS.
  - exact HappD.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (sp - 2560)) _ 2560%nat); [rewrite !u64_of_Z by lia; lia | exact Hok | rewrite !u64_of_Z by lia; lia | rewrite !u64_of_Z by lia; cbn; lia].
  - exact Hdst.
  - exact Hsrc.
  - exact Hret.
  - apply layout_of_cells. exact Hcells.
  - unfold mc_icpt_globs. repeat split.
    + replace (0x138028%bv : word) with (Z_to_bv 64 0x138028) by (apply bv_eq; reflexivity). apply (cell_of mem0 _ 8%nat 0x140919 Hcells). in_list.
    + replace (0x140919%bv : word) with (Z_to_bv 64 0x140919) by (apply bv_eq; reflexivity).
      rewrite (cell_of mem0 0x140919 1%nat 1 Hcells) by in_list. reflexivity.
    + replace (0x1394c8%bv : word) with (Z_to_bv 64 0x1394c8) by (apply bv_eq; reflexivity). apply (cell_of mem0 _ 8%nat 0x129900 Hcells). in_list.
  - intros _ x Hx. apply HZS. exact Hx.
  - intros _. exact HLS.
  - exact HkS.
  - intros [_ Hn64]. exact (HWS Hn64).
  - intros _ x Hx. apply HZD. exact Hx.
  - intros _. exact HLD.
  - exact HkD.
  - intros [_ Hn64]. exact (HWD Hn64).
  - exact H10.
  - exact H11.
  - exact H12.
  - rewrite H2. reflexivity.
  - exact H1.
  - exists regs', Mj. split.
    + replace (Z_to_bv 64 XIA.AS0_MCPY) with (0x77c90%bv : word) by (apply bv_eq; reflexivity). exact RUN.
    + split; [apply kept_ok_of_keeps_cs; exact KCS|]. split; [exact Q10|]. split; [|exact GR].
      intros x Hx. apply OUT. lia.
Qed.

(* [comment removed for export] *)
Lemma tcell_of : forall (M : word -> option byte) a w v,
  XIA.tcells_ok ASEGS XIA.AS0_TCELLS M -> In (a, w, v) XIA.AS0_TCELLS ->
  rdn ASEGS M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)).
Proof. intros M a w v H Hin. unfold XIA.tcells_ok in H. rewrite Forall_forall in H. exact (H _ Hin). Qed.

Theorem as0_icpt_tls : XIA.icpt_tls_spec ASEGS XIA.AS0_TLSPC XIA.AS0_TCELLS XIA.AS0_TPV XIA.AS0_ENTV XIA.AS0_CTXSLOT XIA.AS0_BLKSLOT.
Proof.
  intros fx mem0 d off ctx th tbv tev blk rec sp regs ret Hs Hs' Hd Hd' Hoff Hctx Hctx' Hth Hth' Htb Hte Hblk Hblk' Hrec Hok Htc
    Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 A1 A2 A3 A4 Hret H1 H2 H4 H10.
  unfold XIA.SCRT, XIA.apartZ, XIA.u64cell in *.
  (* [comment removed for export] *)
  assert (TR : forall (M' : word -> option byte), (forall x : word, bv_unsigned x < sp - 176 \/ sp <= bv_unsigned x -> M' x = mem0 x) ->
               forall a (w : nat) bs, 0 <= a < 2 ^ 64 -> a + Z.of_nat w <= 2 ^ 64 -> (a + Z.of_nat w <= sp - 512 \/ sp <= a) ->
               rdn ASEGS mem0 (Z_to_bv 64 a) w = Some bs -> rdn ASEGS M' (Z_to_bv 64 a) w = Some bs).
  { intros M' HM a w bs Ha Haw Hap Hr. rewrite <- Hr. apply rdn_ext; [rewrite u64_of_Z by lia; lia|].
    intros x Hx. rewrite u64_of_Z in Hx by lia. apply HM. lia. }
  destruct (@wrap_tls_get_addr_run fx mem0 (seg_rom ASEGS) (Z_to_bv 64 sp) ret sp XIA.AS0_TPV d 1 off 0x673d20 XIA.AS0_ENTV 0 0x6951b8 ctx th tbv tev 0x1d1768 0x1cf6d8 0 8 blk rec)
    with (regs := regs) as (regs' & Mj & RUN & Q10 & Q2' & Q1' & KCS & OUT & GR).
  - apply u64_of_Z. lia.
  - exact Hret.
  - lia.
  - apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (sp - 512)) _ 512%nat); [rewrite !u64_of_Z by lia; lia | exact Hok | rewrite !u64_of_Z by lia; lia | rewrite !u64_of_Z by lia; cbn; lia].
  - unfold XIA.AS0_TPV. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - unfold XIA.AS0_ENTV. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - unfold XIA.AS0_TPV. lia.
  - lia.
  - lia.
  - intros M' HM. specialize (TR M' HM). unfold tls_cells, XIA.AS0_TPV, XIA.AS0_ENTV.
    repeat split.
    + replace (0x140918%bv : word) with (Z_to_bv 64 0x140918) by (apply bv_eq; reflexivity).
      apply (TR 0x140918 1%nat); [lia | cbn; lia | cbn; lia |]. rewrite (tcell_of mem0 0x140918 1%nat 1 Htc) by in_list. reflexivity.
    + replace (0x1393c0%bv : word) with (Z_to_bv 64 0x1393c0) by (apply bv_eq; reflexivity).
      apply (TR 0x1393c0 8%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 _ 8%nat 0x12a8e4 Htc). in_list.
    + apply (TR d 8%nat); [lia | cbn; lia | cbn; lia | exact Q1].
    + apply (TR (d + 8) 8%nat); [lia | cbn; lia | cbn; lia | exact Q2].
    + apply (TR (0x673d00 - 8) 8%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 0x673cf8 8%nat 0x673d20 Htc). in_list.
    + apply (TR (0x673d20 + 8 * 1) 8%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 0x673d28 8%nat 0x674500 Htc). in_list.
    + replace (0x13f4a0%bv : word) with (Z_to_bv 64 0x13f4a0) by (apply bv_eq; reflexivity).
      apply (TR 0x13f4a0 1%nat); [lia | cbn; lia | cbn; lia |]. rewrite (tcell_of mem0 0x13f4a0 1%nat 1 Htc) by in_list. reflexivity.
    + replace (0x13f4a4%bv : word) with (Z_to_bv 64 0x13f4a4) by (apply bv_eq; reflexivity).
      apply (TR 0x13f4a4 4%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 0x13f4a4 4%nat 0 Htc). in_list.
    + apply (TR (0x673d00 - 88) 8%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 0x673ca8 8%nat 0x6951b8 Htc). in_list.
    + apply (TR (0x6951b8 + 8 * 0) 8%nat); [lia | cbn; lia | cbn; lia |]. exact Q3.
    + apply (TR (ctx + 152) 8%nat); [lia | cbn; lia | cbn; lia | exact Q4].
    + apply (TR (th + 48) 8%nat); [lia | cbn; lia | cbn; lia | exact Q5].
    + apply (TR (th + 56) 8%nat); [lia | cbn; lia | cbn; lia | exact Q6].
    + replace (0x1374b0%bv : word) with (Z_to_bv 64 0x1374b0) by (apply bv_eq; reflexivity).
      apply (TR 0x1374b0 8%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 _ 8%nat 0x1d1768 Htc). in_list.
    + apply (TR (0x1d1768 + 137) 1%nat); [lia | cbn; lia | cbn; lia |]. change (0x1d1768 + 137) with 0x1d17f1. rewrite (tcell_of mem0 0x1d17f1 1%nat 1 Htc) by in_list. reflexivity.
    + replace (0x137510%bv : word) with (Z_to_bv 64 0x137510) by (apply bv_eq; reflexivity).
      apply (TR 0x137510 8%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 _ 8%nat 0x1cf6d8 Htc). in_list.
    + apply (TR 0x1cf6d8 4%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 0x1cf6d8 4%nat 0 Htc). in_list.
    + replace (0x1382c8%bv : word) with (Z_to_bv 64 0x1382c8) by (apply bv_eq; reflexivity).
      apply (TR 0x1382c8 8%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 _ 8%nat 8 Htc). in_list.
    + apply (TR (8 + 0x673d00) 8%nat); [lia | cbn; lia | cbn; lia |]. exact Q7.
    + apply (TR (blk + 16 * 1 + 8) 8%nat); [lia | cbn; lia | cbn; lia |]. replace (blk + 16 * 1 + 8) with (blk + 24) by lia. exact Q8.
  - exact H10.
  - exact H4.
  - rewrite H2. reflexivity.
  - exact H1.
  - exists regs', Mj. split.
    + replace (Z_to_bv 64 XIA.AS0_TLSPC) with (0x633f0%bv : word) by (apply bv_eq; reflexivity). exact RUN.
    + split; [apply kept_ok_of_keeps_cs; exact KCS|]. split; [exact Q10|]. split; [|exact GR].
      intros x Hx. apply OUT. lia.
Qed.
