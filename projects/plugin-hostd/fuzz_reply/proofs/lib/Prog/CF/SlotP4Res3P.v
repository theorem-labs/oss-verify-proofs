(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 618 of its 664 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass9G.v, with its module names changed; 3419 of its 3513 lines of code are new or changed and 570 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass4.v, with its module paths and module names changed; 412 of its 461 lines of code are new or changed and 3464 lines of the source are left out. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room ContractT AllocPack3Ag.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import StatementKept SlotInv SlotSteps SlotRes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotParse SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotRI3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT RelayRunF RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import HarnessTr send_line_b_c gesture_end_b_c gestures_end_b_c drain_b_c relay_remove_b_c relay_instance_gone_b_c SlotMove SlotNcMove3 SlotRun3 SlotP5R3 SlotP5R3G SlotP5Res3 SlotResR3 SlotReads op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotP4Res3Aux SlotP4Res3 SlotRI3P SlotPeak3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require SlotPass4 SlotDrain3.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition p4_res_cf (F : ResFormT) (RI : res_inv) : Prop :=
  forall E K L A G out es hj q e h i (lv : bool) (MX CAP : Z),
    RI E K (view_of G out es hj) L A -> List.NoDup (map fst (blocks L A)) -> WF A -> slot_cost es hj <= K ->
    stdpp.base.NoDup (target_addrs G out es hj) ->
    nth_error es q = Some e -> nth_error hj q = Some (h, i) ->
    CF.SlotPass4.p4_ent_blk L A e -> CF.SlotPass4.p4_src_blk L A h -> (CAP = 0 \/ In (out, CAP) (blocks L A)) ->
    0 <= MX <= 255 -> 0 <= CAP <= TBBYTES ->
    0 <= re_fd e -> find (fun x => re_fd x =? re_fd e) es = Some e ->
    (re_eof e = 0 -> CF.SlotP5R3G.drain3 e h) ->
    (re_eof e = 0 -> hl_recs (hs_expected h) = [] /\ ecap_ok (hl_cap (hs_expected h)) /\
       Z.of_nat (length (pending_stream h)) < WRITE_MAX * OPS_MAX /\ J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h) /\
       0 <= hs_off h /\ re_nheld e + Z.of_nat (length (pending_stream h)) < 2 ^ 26) ->
    remove_entry_cap lv MX 0 CAP e h <= SlotCaps3.NMAX ->
    (re_hp e <> 0 -> re_kh e <> 0) -> (CAP = 0 -> forall m, ~ In (out, m) (blocks L A)) ->
    (length es <= 4)%nat -> (length hj <= 4)%nat ->
    res_tr F (CF.SlotPass4.p4_lv1 F RI E K L A G out es hj lv MX CAP (remove_entry_cap lv MX 0 CAP e h) e h) A
      (relay_remove_tr lv MX 0 CAP (re_fd e) es h (known_at L A) 0 (known_at L A out)).
Lemma p4_res_cf_of F RI : CF.SlotPass4.p4_res F RI -> p4_res_cf F RI.
Proof.
  intros H. exact H.
Qed.

Lemma p4p_sl_peak f : forall mx no cap rem j o Bd, 0 <= mx -> 0 <= cap ->
  fst (snd (sl_run f mx no cap rem j o)) <= NMAX -> 3 * fst (snd (sl_run f mx no cap rem j o)) <= 2 * (Bd + cap) ->
  tr_peak (fst (sl_run f mx no cap rem j o)) Bd /\
  tr_db (fst (sl_run f mx no cap rem j o)) = fst (snd (sl_run f mx no cap rem j o)) - cap.
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Bd Hm Hc HN HB; cbn [sl_run] in *.
  - cbn [fst snd] in *. split; [apply tr_peak_nil|rewrite tr_db_nil; lia].
  - destruct (rem <=? 0); [cbn [fst snd] in *; split; [apply tr_peak_nil|rewrite tr_db_nil; lia]|].
    set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem) in *.
    destruct (cap <? no + n) eqn:Hlt; cbn [fst snd] in *.
    + apply Z.ltb_lt in Hlt.
      pose proof (sl_mono f mx (no + n) ((no + n) * 2) (rem - n) (Datatypes.S j) (Ret j) ltac:(lia)) as M.
      destruct (IH mx (no + n) ((no + n) * 2) (rem - n) (Datatypes.S j) (Ret j) (Bd - ((no + n) * 2 - cap)) Hm
                  ltac:(lia) HN ltac:(lia)) as [P D].
      destruct (cap =? 0) eqn:Hz.
      * apply Z.eqb_eq in Hz. subst cap. split.
        -- apply tr_peak_cons. cbn [ev_db]. split; [lia|].
           replace (Bd - (no + n) * 2) with (Bd - ((no + n) * 2 - 0)) by lia. exact P.
        -- rewrite tr_db_cons, D. cbn [ev_db]. lia.
      * split.
        -- apply tr_peak_cons. cbn [ev_db]. split; [lia|exact P].
        -- rewrite tr_db_cons, D. cbn [ev_db]. lia.
    + exact (IH mx (no + n) cap (rem - n) j o Bd Hm Hc HN HB).
Qed.

Lemma p4p_send_peak live mx no cap len j o Bd : 0 <= mx -> 0 <= cap -> send_line_cap live mx no cap len <= NMAX ->
  3 * send_line_cap live mx no cap len <= 2 * (Bd + cap) ->
  tr_peak (send_line_tr live mx no cap len j o) Bd /\
  tr_db (send_line_tr live mx no cap len j o) = send_line_cap live mx no cap len - cap.
Proof.
  intros Hm Hc HN HB. unfold send_line_tr, send_line_cap in *. destruct live; cbv beta iota in *.
  - rewrite (sl_capi (Z.to_nat len) mx no cap len 0%nat adr0 j o) in HN, HB |- *.
    exact (p4p_sl_peak _ mx no cap len j o Bd Hm Hc HN HB).
  - split; [apply tr_peak_nil|rewrite tr_db_nil; lia].
Qed.

Lemma p4p_ge_peak live mx no cap xl j o Bd : 0 <= mx -> 0 <= cap -> gesture_end_cap live mx no cap xl <= NMAX ->
  3 * gesture_end_cap live mx no cap xl <= 2 * (Bd + cap) ->
  tr_peak (gesture_end_tr live mx no cap xl j o) Bd /\
  tr_db (gesture_end_tr live mx no cap xl j o) = gesture_end_cap live mx no cap xl - cap.
Proof.
  intros Hm Hc HN HB. unfold gesture_end_tr, gesture_end_cap in *. cbv zeta.
  pose proof (send_mono live mx no cap xl Hc) as M1.
  pose proof (send_mono live mx (no + xl) (send_line_cap live mx no cap xl) 5 ltac:(lia)) as M2.
  destruct (p4p_send_peak live mx no cap xl j o Bd Hm Hc ltac:(lia) ltac:(lia)) as [P1 D1].
  destruct (p4p_send_peak live mx (no + xl) (send_line_cap live mx no cap xl) 5
              (j + nretF (send_line_tr live mx no cap xl j o))%nat (send_line_out live mx no cap xl j o)
              (Bd - (send_line_cap live mx no cap xl - cap)) Hm ltac:(lia) HN ltac:(lia)) as [P2 D2].
  split.
  - apply tr_peak_app; [exact P1|]. rewrite D1. exact P2.
  - rewrite tr_db_app, D1, D2. lia.
Qed.

Lemma p4p_ke_peak xks : forall live mx no cap j o Bd, 0 <= mx -> 0 <= cap -> Forall (fun x => 0 <= fst x) xks ->
  fst (snd (keys_end_run live mx no cap xks j o)) <= NMAX ->
  3 * fst (snd (keys_end_run live mx no cap xks j o)) <= 2 * (Bd + cap) ->
  tr_peak (fst (keys_end_run live mx no cap xks j o)) Bd /\
  tr_db (fst (keys_end_run live mx no cap xks j o)) <= fst (snd (keys_end_run live mx no cap xks j o)) - cap.
Proof.
  induction xks as [|[xl ka] r IH]; intros live mx no cap j o Bd Hm Hc HX HN HB; cbn [keys_end_run fst snd] in *.
  - split; [apply tr_peak_nil|rewrite tr_db_nil; lia].
  - apply Forall_cons_iff in HX as [Hx HX]. cbn [fst] in Hx.
    pose proof (ge_mono live mx no cap xl Hc) as M1.
    pose proof (ke_mono r live mx (no + xl + 5) (gesture_end_cap live mx no cap xl)
                  (j + nretF (gesture_end_tr live mx no cap xl j o))%nat (gesture_end_out live mx no cap xl j o)
                  ltac:(lia)) as M2.
    destruct (p4p_ge_peak live mx no cap xl j o Bd Hm Hc ltac:(lia) ltac:(lia)) as [P1 D1].
    destruct (IH live mx (no + xl + 5) (gesture_end_cap live mx no cap xl)
                (j + nretF (gesture_end_tr live mx no cap xl j o))%nat (gesture_end_out live mx no cap xl j o)
                (Bd - (gesture_end_cap live mx no cap xl - cap) + (xl + 1)) Hm ltac:(lia) HX HN ltac:(lia)) as [P2 D2].
    split.
    + apply tr_peak_app; [exact P1|]. rewrite D1. apply tr_peak_cons. cbn [ev_db]. split; [exact I|].
      replace (Bd - (gesture_end_cap live mx no cap xl - cap) - - (xl + 1)) with
        (Bd - (gesture_end_cap live mx no cap xl - cap) + (xl + 1)) by lia. exact P2.
    + rewrite tr_db_app, D1, tr_db_cons. cbn [ev_db]. lia.
Qed.

Lemma p4p_tail_peak lv mx no cap xks hp kh ha c a j o Bd : 0 <= mx -> 0 <= cap -> Forall (fun x => 0 <= fst x) xks ->
  fst (snd (keys_end_run lv mx no cap xks j o)) <= NMAX ->
  3 * fst (snd (keys_end_run lv mx no cap xks j o)) <= 2 * (Bd + cap) ->
  tr_peak (gestures_end_tr lv mx no cap xks hp kh j o ha ++ (if c =? 0 then [] else [RFree c a])) Bd.
Proof.
  intros Hm Hc HX HN HB. unfold gestures_end_tr. rewrite <- app_assoc.
  destruct (p4p_ke_peak xks lv mx no cap j o Bd Hm Hc HX HN HB) as [P _].
  apply tr_peak_app; [exact P|]. apply tr_peak_frees.
  destruct (hp =? 0); destruct (c =? 0); cbn [app]; repeat first [exact I | constructor].
Qed.

Lemma p4p_rr_ocap lv mx NO CAP e h : 0 <= mx -> 0 <= NO -> 0 <= CAP -> 0 <= re_cap e -> 0 <= ent_ka e ->
  0 <= hl_cap (hs_expected h) ->
  CAP <= ds_ocap (after_drain lv mx NO CAP e h) /\
  ds_ocap (after_drain lv mx NO CAP e h) <= remove_entry_cap lv mx NO CAP e h.
Proof.
  intros Hm Hn Hc Hr Hk He.
  destruct (rr_model lv mx NO CAP e h (fun _ => adr0) adr0 Hm Hn Hc Hr Hk He) as (_ & _ & _ & _ & [Ho _]).
  split; [exact Ho|]. rewrite <- (rr_keys_cap lv mx NO CAP e h (fun _ => adr0) adr0 0%nat adr0). apply ke_mono. lia.
Qed.

Lemma p4p_rr_peak lv mx CAP e h nm o Bd : 0 <= mx -> 0 <= CAP -> 0 <= re_cap e -> 0 <= ent_ka e ->
  0 <= hl_cap (hs_expected h) -> remove_entry_cap lv mx 0 CAP e h <= NMAX ->
  (re_eof e = 0 -> tr_peak (drain_tr lv mx 0 CAP e h 0 (drain_start nm o e h)) Bd /\
     3 * remove_entry_cap lv mx 0 CAP e h <=
       2 * (Bd - tr_db (drain_tr lv mx 0 CAP e h 0 (drain_start nm o e h)) + ds_ocap (after_drain lv mx 0 CAP e h))) ->
  (re_eof e <> 0 -> 3 * remove_entry_cap lv mx 0 CAP e h <= 2 * (Bd + CAP)) ->
  tr_peak (remove_entry_tr lv mx 0 CAP e h 0 (drain_start nm o e h)) Bd.
Proof.
  intros Hm Hc Hr Hk He HN H0 H1.
  destruct (p4p_rr_ocap lv mx 0 CAP e h Hm (Z.le_refl 0) Hc Hr Hk He) as [O1 _].
  pose proof (rr_keys_cap lv mx 0 CAP e h nm o) as KC.
  unfold remove_entry_tr, remove_entry_run. cbv zeta. cbn [fst].
  set (s := after_drain lv mx 0 CAP e h) in *. set (a := drain_start nm o e h) in *.
  set (a1 := after_drain_adr lv mx 0 CAP e h 0 a) in *.
  set (xks := combine (map (fun x => Z.of_nat (length x)) (ds_H s)) (da_keys a1)) in *.
  assert (HX : Forall (fun x => 0 <= fst x) xks) by apply rr_xks_nn.
  destruct (Z.eqb_spec (re_eof e) 0) as [Ee|Ee].
  - cbv beta iota. destruct (H0 Ee) as [P B].
    apply tr_peak_app; [exact P|].
    apply p4p_tail_peak; [exact Hm|lia|exact HX|rewrite KC; exact HN|rewrite KC; exact B].
  - cbv beta iota. cbn [app].
    assert (Es : ds_ocap s = CAP) by (unfold s, after_drain; rewrite (proj2 (Z.eqb_neq _ _) Ee); reflexivity).
    apply p4p_tail_peak; [exact Hm|lia|exact HX|rewrite KC; exact HN|rewrite KC, Es; exact (H1 Ee)].
Qed.

Lemma p4p_bytes_cr NW pl k V L A b al alb : RI3_ledger NW pl k V L A b al alb ->
  p3_bytes b + promb (rv_pend V) <= PB3_MAX.
Proof.
  intros HL. pose proof (ledger3_alsum _ _ _ _ _ _ _ _ _ HL) as HS.
  destruct HL as (_ & _ & _ & _ & _ & _ & HE & HB & HW1 & HW2 & HP & _).
  pose proof (consb_le pl k). pose proof (cdat_le pl k). pose proof (ek_b_nonneg V HE).
  unfold PB3_MAX, NC_PER, DATA_PER in *. lia.
Qed.

Theorem p4_res_cf_RI3P OK RM : RMH RM -> p4_res_cf (pack3P OK RM) (RI3P OK).
Proof.
  intros HRM E K L0 A0 G out es hj q e h i lv MX CAP HRI HND0 HWF Hcost HNT Hqe Hqh HEB HSB HCAP HMX HCR Hfd Hfind Hd3
    Hdf HC1 Hkh HO0 Hes Hhj.
  destruct HRI as ((b & al & alb & HR0 & HL) & HOK0).
  pose proof HL as (HLc & HLm & _ & _ & _ & HLa & HLe & _).
  assert (HMX0 : 0 <= MX) by lia. assert (HCAP0 : 0 <= CAP) by lia.
  assert (Hin : In (h, i) hj) by exact (nth_error_In hj q Hqh).
  assert (Hine : In e es) by exact (nth_error_In es q Hqe).
  pose proof HEB as (HEB1 & HEB2 & _).
  assert (Hrc : 0 <= re_cap e) by (destruct HEB1 as [X|X]; [lia|exact (blk_nonneg _ _ _ _ HWF X)]).
  assert (Hka : 0 <= ent_ka e).
  { unfold ent_ka. destruct (Z.eqb_spec (re_hp e) 0) as [X|X]; [lia|].
    destruct HEB2 as [Y|Y]; [contradiction|exact (blk_nonneg _ _ _ _ HWF Y)]. }
  pose proof HSB as ((HSP & _) & HSPa & (HSE & _) & (HSH & _) & _).
  assert (Hec : 0 <= hl_cap (hs_expected h)) by (destruct HSE as [X|X]; [lia|pose proof (blk_nonneg _ _ _ _ HWF X); lia]).
  assert (NV : SlotCaps3.NMAX = 536879104) by reflexivity.
  assert (E3 : DRAIN_B = 1099511627776) by reflexivity.
  assert (BV : BMAX = 17592186044416) by reflexivity.
  set (nm := known_at L0 A0) in *.
  set (a0 := drain_start nm (nm out) e h).
  set (C1 := remove_entry_cap lv MX 0 CAP e h) in *.
  assert (Etr : relay_remove_tr lv MX 0 CAP (re_fd e) es h nm 0 (nm out) = remove_entry_tr lv MX 0 CAP e h 0 a0).
  { unfold relay_remove_tr. rewrite (proj2 (Z.ltb_ge _ _) Hfd), Hfind. reflexivity. }
  rewrite Etr.
  assert (HP : pk3_ok b) by exact (ledger3_pk3 _ _ _ _ _ _ _ _ _ HL).
  assert (HSl : forall c, 0 <= c < 49 -> znth c (p3_live b) + cred h c + 64 <= znth c (p3_cap b)).
  { intros c Hc. pose proof (ledger3_slack _ _ _ _ _ _ _ _ _ c HL Hc). pose proof (cred_le_prom hj h i c Hin).
    cbn [view_of rv_pend] in *. lia. }
  pose proof (ledger3_bytes _ _ _ _ _ _ _ _ _ HL) as HB0. rewrite PB3_MAX_val in HB0.
  assert (HBy : p3_bytes b + 2 * C1 + 2 * DRAIN_B <= BMAX) by lia.
  assert (Hhc : 0 <= hl_cap (hs_held h)) by (destruct HSH as [X|X]; [lia|pose proof (blk_nonneg _ _ _ _ HWF X); lia]).
  pose proof (credb_le_promb hj h i Hin) as CBP0. pose proof (credb_nonneg h) as CBN0.
  pose proof (p4p_bytes_cr _ _ _ _ _ _ _ _ _ HL) as BCR. cbn [view_of rv_pend] in BCR.
  pose proof PB3_MAX_val as PBV.
  assert (CFV : 4000000000 <= CF_MAX) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (P30 : 2 ^ 30 = 1073741824) by reflexivity. assert (P26 : 2 ^ 26 = 67108864) by reflexivity.
  destruct (p4p_rr_ocap lv MX 0 CAP e h HMX0 (Z.le_refl 0) HCAP0 Hrc Hka Hec) as [OC1 OC2]. fold C1 in OC2.
  assert (DRN : re_eof e = 0 -> tr_peak (drain_tr lv MX 0 CAP e h 0 a0) (CF_MAX - PB3_MAX + credb h) /\
     tr_db (drain_tr lv MX 0 CAP e h 0 a0) <= ds_ocap (after_drain lv MX 0 CAP e h) - CAP + 2 ^ 30 + 32768 + credb h /\
     ecap_ok (ds_ecap (after_drain lv MX 0 CAP e h))).
  { intros Ee. destruct (Hdf Ee) as (X1 & X2 & X3 & X4 & X5 & X6).
    assert (Es : after_drain lv MX 0 CAP e h = drain_fin lv MX 0 CAP e h)
      by (unfold after_drain; rewrite (proj2 (Z.eqb_eq _ _) Ee); reflexivity).
    rewrite Es in OC2 |- *.
    assert (X7 : hl_cap (hs_expected h) = 0 \/ exists k, 0 <= k /\ hl_cap (hs_expected h) = 8 * 2 ^ k).
    { destruct X2 as [X|(k0 & Hk0 & X)]; [left; exact X|right; exists k0; split; [lia|exact X]]. }
    assert (X8 : hl_n (hs_expected h) + Z.of_nat (length (pending_stream h)) < 2 ^ 25).
    { unfold hl_n. rewrite X1. cbn [length Z.of_nat]. assert (P25 : 2 ^ 25 = 33554432) by reflexivity.
      unfold WRITE_MAX, OPS_MAX in X3. lia. }
    destruct (drain_peak3 e h lv MX 0 CAP 0%nat a0 Hrc Hka X4 X5 X6 X7 X8 HMX0 ltac:(lia) ltac:(lia)) as [D1 D2].
    split; [|split; [exact D2|exact (CF.SlotDrain3.drain3_ecap e h X5 X2 X8 lv MX 0 CAP)]].
    apply D1. assert (CFF : PB3_MAX + NMAX / 2 + WRITE_MAX * OPS_MAX + 6000 + 32768 + 2 ^ 30 + NMAX <= CF_MAX)
      by (apply Z.leb_le; vm_compute; reflexivity).
    assert (NH : NMAX / 2 = 268439552) by reflexivity. unfold WRITE_MAX, OPS_MAX in X3, CFF. lia. }
  assert (HEC16 : 16 * (ds_ecap (after_drain lv MX 0 CAP e h) - hl_cap (hs_expected h)) <= 2 ^ 30).
  { destruct (Z.eqb_spec (re_eof e) 0) as [Ee|Ee].
    - destruct (DRN Ee) as (_ & _ & X). pose proof (ecap_ok_lt _ X). lia.
    - assert (Es : ds_ecap (after_drain lv MX 0 CAP e h) = hl_cap (hs_expected h))
        by (unfold after_drain; rewrite (proj2 (Z.eqb_neq _ _) Ee); reflexivity).
      rewrite Es. lia. }
  exists b. split; [exact (conj HR0 HOK0)|]. split.
  - intros qs _. apply (proj2 (roomF_pack3P OK RM qs b _)). split.
    + rewrite roomF3.
    destruct (p4_misT_start (ss_pl E) K L0 A0 b al alb G out es hj q e h i CAP qs HL HR0 HND0 Hqe Hqh Hes Hhj Hkh HO0)
      as (S & HS).
    exact (proj1 (rr3 lv MX 0 CAP e h nm (nm out) qs b S 0 C1 Hd3 HMX0 (Z.le_refl 0) HCAP0 Hrc Hka Hec (Z.le_refl _) HC1
                    HP HSl HBy HS)).
    + apply (RMrun_of_peak RM (ss_pl E) b _ (CF_MAX - PB3_MAX + credb h) HRM HLc HLm); [lia|].
      apply (p4p_rr_peak lv MX CAP e h nm (nm out)); [exact HMX0|exact HCAP0|exact Hrc|exact Hka|exact Hec|exact HC1| |].
      * intros Ee. destruct (DRN Ee) as (D1 & D2 & _). fold a0 C1. split; [exact D1|lia].
      * intros _. fold C1. lia.
  - intros L1 A1 qs1 _ (HR1 & HOK1). rewrite runF_pack3P, runF3 in HR1.
    destruct (p4_misT_start (ss_pl E) K L0 A0 b al alb G out es hj q e h i CAP qs1 HL HR0 HND0 Hqe Hqh Hes Hhj Hkh HO0)
      as (S1 & HS1).
    destruct (rr3 lv MX 0 CAP e h nm (nm out) qs1 b S1 0 C1 Hd3 HMX0 (Z.le_refl 0) HCAP0 Hrc Hka Hec (Z.le_refl _) HC1
                HP HSl HBy HS1)
      as (_ & P1 & Cp1 & Mp1 & (dks & Hdks & Hdc & Hdb & L1e & B1e) & B1c & (S1' & r1' & HS1')).
    destruct (rr_model lv MX 0 CAP e h nm (nm out) HMX0 (Z.le_refl 0) HCAP0 Hrc Hka Hec) as (_ & _ & _ & Hecm & _).
    pose proof (rr_misK (p3_mis b) (slot3 CAP (resolveF qs1 (nm out)) ++ dsl qs1 (drain_init 0 CAP e h) a0 ++ [])
                  lv MX 0 CAP e h nm (nm out) qs1 b [] HMX0 (Z.le_refl 0) HCAP0 Hrc Hka Hec (misK_init _ _)) as K1.
    pose proof (rr_oq lv MX 0 CAP e h nm (nm out) HMX0 (Z.le_refl 0) HCAP0 Hrc Hka Hec) as [_ Hoq].
    fold a0 C1 in Hoq, K1, L1e, B1e, B1c, HS1', P1, Cp1, Mp1.
    set (b1 := run3 qs1 b 0 (remove_entry_tr lv MX 0 CAP e h 0 a0)) in *.
    set (s := after_drain lv MX 0 CAP e h) in *.
    set (a1 := after_drain_adr lv MX 0 CAP e h 0 a0) in *.
    hnf. intros OUT' CAP' olv h1 HQL HQN HSL HB1a HB1b HB1c HND1o HOUT Hh1 Hpend1 Hheld1 Hexp1 HSB1 HY1 HN1 HG7 HG8 HG5.
    fold a0 C1 in HQL, HSL.
    assert (HZR : Forall zrange (CF.SlotPass4.p4_lines e h))
      by (unfold CF.SlotPass4.p4_lines; destruct (re_eof e =? 0); [apply p4x_lines_range|constructor]).
    assert (TX1 : texts (hs_expected h1) = rr_lines e h) by exact (texts_lines _ _ Hexp1 HZR).
    assert (EK1 : ekeys_hl (hs_expected h1) = ekeys (rr_lines e h)).
    { change (ekeys_hl (hs_expected h1)) with (ekeys (texts (hs_expected h1))). rewrite TX1. reflexivity. }
    assert (HE1 : hl_cap (hs_expected h1) = ds_ecap s /\ hl_v (hs_pending h1) = hl_v (hs_pending h) /\
                  hl_cap (hs_pending h1) = hl_cap (hs_pending h) /\ hs_partial h1 = hs_partial h).
    { destruct (Z.eqb_spec (re_eof e) 0) as [Ee|Ee].
      - rewrite (HG8 Ee). unfold s, after_drain. rewrite (proj2 (Z.eqb_eq _ _) Ee). split; [reflexivity|exact (HG5 Ee)].
      - rewrite (Hh1 Ee). unfold s, after_drain. rewrite (proj2 (Z.eqb_neq _ _) Ee). cbn [drain_init ds_ecap].
        split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
    destruct HE1 as (HEc1 & HPv1 & HPc1 & HPa1).
    set (s1 := sh_of (known_at L1 A1) (hs_held h1)) in *.
    set (rs1 := map (shr (known_at L1 A1)) (hl_recs (hs_expected h1))) in *.
    set (ks2 := cnl_keys 0 s1 rs1).
    assert (Hks2 : Forall (fun n => 0 <= n) ks2) by apply cnl_keys_nonneg.
    assert (Kc2 : forall c, bcnt c ks2 <= bcnt c (ekeys (rr_lines e h))) by (intros c; rewrite <- EK1; apply cnl_keys_bcnt_hl).
    assert (Kb2 : zsum (fun n => n) ks2 <= zsum (fun n => n) (ekeys (rr_lines e h))) by (rewrite <- EK1; apply cnl_keys_zsum_hl).
    pose proof P1 as (Hl1 & _).
    pose proof (zsum_id_nonneg _ Hdks) as Zdks. pose proof (zsum_id_nonneg _ Hks2) as Zks2.
    pose proof (credb_le_promb hj h i Hin) as CBP. pose proof (ledger3_creditb _ _ _ _ _ _ _ _ _ HL) as LCB.
    pose proof (ek_b_nonneg _ HLe) as EBN. pose proof (consb_le (ss_pl E) K) as CBM. rewrite CONSB_MAX_v in CBM.
    cbn [view_of rv_pend] in LCB, EBN.
    exists b1. split; [exact (conj HR1 HOK1)|]. split.
    + intros qs2 _.
      assert (SN : sh_n s1 = hl_n (hs_held h1)) by (unfold s1; apply sh_n_of).
      assert (P22 : 2 ^ 22 = 4194304) by reflexivity.
      assert (KL2 : hl_n (hs_held h1) + zlen ks2 < 4194304).
      { pose proof (cnl_keys_len 0 s1 rs1) as X. unfold rs1 in X. rewrite map_snd_shr in X. fold rs1 ks2 in X. lia. }
      apply (proj2 (roomF_pack3P OK RM qs2 b1 _)). split.
      * rewrite roomF3.
        apply (pinv_cnl (ss_pl E) (p3_bytes b1 + zsum (fun n => n) ks2 + 134217728) qs2 rs1 0 s1 b1).
        unfold pinv. fold ks2. split; [rewrite Cp1; exact HLc|]. split; [rewrite Mp1; exact HLm|]. split; [exact Hl1|].
        split; [intros c Hc; exact (misT_count _ _ _ c HS1')|].
        split.
        { intros c Hc. pose proof (L1e c Hc). pose proof (ledger3_slack _ _ _ _ _ _ _ _ _ c HL Hc).
          pose proof (cred_le_prom hj h i c Hin). pose proof (Hdc c Hc). pose proof (Kc2 c).
          pose proof (arr_c_b (sh_cap s1) c). pose proof (ncb_b C1 c). pose proof (ncb_b CAP c).
          pose proof (ncb_b (re_cap e) c). pose proof (ncb_b (ent_ka e) c). pose proof (ncb_b (16 * ds_ecap s) c).
          pose proof (ncb_b (16 * hl_cap (hs_expected h)) c). pose proof (bcnt_nonneg c dks).
          rewrite Cp1. cbn [view_of rv_pend] in *. lia. }
        split; [exact Hks2|]. split; [rewrite SN; unfold hl_n; lia|].
        split; [rewrite SN; exact KL2|].
        split; [lia|]. split; [pose proof (arr_pot_b (sh_cap s1)); lia|]. lia.
      * apply (RMrun_of_peak RM (ss_pl E) b1 _ (zsum (fun n => n) ks2 + 201326592) HRM);
          [rewrite Cp1; exact HLc|rewrite Mp1; exact HLm|lia|].
        apply cnl_peak3; fold ks2.
        -- unfold s1, sh_of. cbn [sh_cap]. rewrite Hheld1. exact Hhc.
        -- rewrite SN. unfold hl_n. lia.
        -- rewrite SN, P22. exact KL2.
        -- lia.
    + intros L2 A2 qs2 _ (HR2 & HOK2). rewrite runF_pack3P, runF3 in HR2.
      pose proof (check_no_loss_effect3 s1 rs1 qs2 b1 Hl1) as X2. cbv zeta in X2. rewrite runF3 in X2.
      fold ks2 in X2. destruct X2 as (C2e & M2e & Hl2 & L2e & B2e & _ & _ & Hfs2).
      pose proof (cnl_misK (p3_mis b1) (slot3 (hl_cap (hs_held h)) (sptr_of L1 A1 (hl_v (hs_held h)))) qs2 [] rs1 0 s1 b1)
        as K2.
      set (b2 := run3 qs2 b1 0 (check_no_loss_tr 0 s1 rs1)) in *.
      set (s' := check_no_loss_sh 0 s1 rs1) in *.
      hnf. intros E' H' HSR HSLV HE'r HE'v HE'c HNDH' HTH' HB2a HB2b HB2c HSB2 HY2 HN2 gone d Hgone.
      exists b2. split; [exact (conj HR2 HOK2)|]. split.
      * intros qs3 _. exact (roomF_frees (pack3P OK RM) qs3 b2 _ (proj1 (ends_free _ _ _ _ _))).
      * intros L3 A3 qs3 _ (HR3 & HOK3). rewrite runF_pack3P, runF3 in HR3.
        pose proof (check_shape_ends_effect3 (known_at L2 A2) gone [] (hl_recs H') d qs3 b2 Hl2) as X3.
        cbv zeta in X3. rewrite runF3 in X3. destruct X3 as (C3e & M3e & Hl3 & L3e & B3e & _ & Hfs3).
        set (b3 := run3 qs3 b2 0 (check_shape_ends_tr (known_at L2 A2) gone [] (hl_recs H') d)) in *.
        hnf. intros H'' ds HH''v HH''c HPerm HB3a HB3b HSB3 HY3 HN3.
        exists b3. split; [exact (conj HR3 HOK3)|]. split.
        -- intros qs4 _. apply roomF_frees, reset_free.
        -- intros L4 A4 qs4 _ (HR4 & HOK4). rewrite runF_pack3P, runF3 in HR4.
           set (h3 := set_held (set_exp_held h1 E' H') H'') in *.
           destruct (frees3 qs4 (source_reset_tr (known_at L3 A3) h3) b3 0 (reset_free _ _) Hl3)
             as (Hl4 & C4e & M4e & L4e & B4e).
           set (b4 := run3 qs4 b3 0 (source_reset_tr (known_at L3 A3) h3)) in *.
           hnf. intros HB4a HB4b HY4. hnf. intros G' out' es' hj' Hcov Hpend Hek Hes' Hhj' HM HND4 HK HWs HWg.
           split; [|exact HOK4].
           fold s1 rs1 in HSR, HSLV. fold s' in HSR, HSLV.
           destruct HSR as (HR'c & HR'v & _). destruct HSLV as (HSL1 & _).
           assert (EH3 : hs_pending h3 = hs_pending h1 /\ hs_partial h3 = hs_partial h1 /\ hs_expected h3 = E' /\
                         hs_held h3 = H'') by (unfold h3; cbn; auto).
           destruct EH3 as (EH3p & EH3a & EH3e & EH3h).
           assert (CH'' : hl_cap H'' = sh_cap s') by (rewrite HH''c; cbn [set_exp_held hs_held]; exact HR'c).
           assert (VH'' : hl_v H'' = hl_v H') by (rewrite HH''v; reflexivity).
           assert (CS1 : sh_cap s1 = hl_cap (hs_held h)) by (unfold s1, sh_of; cbn [sh_cap]; rewrite Hheld1; reflexivity).
           assert (SC3 : forall c, zsum (fun t => one_if c (band (snd t))) (src_dels h3) =
                     arr_c (hl_cap (hs_pending h)) c + one_if c (band PARTIAL_BYTES) + arr_c (ds_ecap s) c +
                     arr_c (sh_cap s') c).
           { intros c. rewrite src_cls, EH3p, EH3e, EH3h, HPc1, HE'c, HEc1, CH''. reflexivity. }
           assert (SZ3 : zsum snd (src_dels h3) =
                     16 * hl_cap (hs_pending h) + PARTIAL_BYTES + 16 * ds_ecap s + 16 * sh_cap s').
           { rewrite src_sz, EH3p, EH3e, EH3h, HPc1, HE'c, HEc1, CH''. reflexivity. }
           apply (p4_close E K G out es hj h b al alb L0 A0 L4 A4 b4 G' out' es' hj'
                    (CF.SlotPass4.p4_dels out CAP OUT' C1 e h) (CF.SlotPass4.p4_adds out CAP OUT' C1) (dks ++ ks2) HL HR0 HR4);
             [congruence|congruence|exact Hl4|apply Forall_app; split; assumption| | | | | |exact Hpend|exact Hek|
              exact Hes'|exact Hhj'|exact HM|exact HND4|exact HK|exact HWs|exact HWg].
           ++ intros c Hc. pose proof (L4e c Hc) as X4. pose proof (L3e c Hc) as X3. pose proof (L2e c Hc) as X2.
              pose proof (L1e c Hc) as X1.
              pose proof (reset_sum (fun n => one_if c (band n)) (known_at L3 A3) h3
                            (fun x _ => proj1 (one_if_b c (band x)))) as RS. cbv beta in RS. rewrite SC3 in RS.
              change (zsum (fun n => one_if c (band n)) (fsz (source_reset_tr (known_at L3 A3) h3))) with
                (bcnt c (fsz (source_reset_tr (known_at L3 A3) h3))) in RS.
              pose proof (p4_dl_le out CAP OUT' C1 e h c Hkh) as DL. rewrite src_cls in DL.
              unfold CF.SlotPass4.p4_dels, CF.SlotPass4.p4_adds. rewrite bcnt_app.
              pose proof (bcnt_nonneg c (map rec_len (cse_ds (known_at L2 A2) gone [] (hl_recs H') d))).
              pose proof (bcnt_nonneg c (cnl_frees 0 s1 rs1)).
              rewrite (ncb16 (ds_ecap s) c), (ncb16 (hl_cap (hs_expected h)) c) in X1. unfold arr_dl in X2.
              rewrite CS1 in X2. lia.
           ++ pose proof (reset_sum (fun n => n) (known_at L3 A3) h3 (fun x Hx => ltac:(lia))) as RS. cbv beta in RS.
              change (zsum (fun t => snd t) (src_dels h3)) with (zsum snd (src_dels h3)) in RS. rewrite SZ3 in RS.
              unfold CF.SlotPass4.p4_dels, CF.SlotPass4.p4_adds. rewrite (p4_db_eq out CAP OUT' C1 e h Hkh), src_sz.
              pose proof (zsum_id_nonneg _ Hfs2). pose proof (zsum_id_nonneg _ Hfs3).
              rewrite zsum_app. rewrite CS1 in B2e. lia.
           ++ intros c Hc. rewrite bcnt_app. pose proof (Hdc c Hc). pose proof (Kc2 c).
              pose proof (bcnt_nonneg c (ekeys_hl (hs_expected h))). lia.
           ++ rewrite zsum_app. pose proof (zsum_id_nonneg _ (ekeys_nonneg (map (fun r => bzs (snd r)) (hl_recs (hs_expected h))))).
              unfold ekeys_hl. lia.
           ++ pose proof HR0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU0 & _) & _).
              pose proof HR1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU1 & _) & _).
              pose proof HR2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU2 & _) & _).
              pose proof HR3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU3 & _) & _).
              pose proof HR4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU4 & _) & _).
              assert (HK2 : misK (p3_mis b1) (slot3 (hl_cap (hs_held h)) (sptr_of L1 A1 (hl_v (hs_held h))))
                              (slot3 (sh_cap s1) (resolveF qs2 (sh_v s1)) ++ []) (p3_mis b1)).
              { eapply misK_S; [|exact (misK_init _ _)]. intros z Hz. rewrite app_nil_r.
                unfold s1, sh_of. cbn [sh_cap sh_v resolve known_at]. rewrite Hheld1. exact Hz. }
              apply (p4_mis_final L0 L1 L2 L3 L4 A0 A1 A2 A3 A4 (p3_mis b) (p3_mis b1) (p3_mis b2) (p3_mis b3) (p3_mis b4)
                       (slot3 CAP (resolveF qs1 (nm out)) ++ dsl qs1 (drain_init 0 CAP e h) a0 ++ [])
                       out CAP OUT' C1 (ds_ecap s) (hl_cap (hs_held h)) (sh_cap s') 0
                       (resolveF qs1 (remove_entry_out lv MX 0 CAP e h 0 a0)) (resolveF qs1 (da_ev a1))
                       (resolveF qs2 (sh_v s')) (sptr_of L1 A1 (hl_v (hs_held h))) e h h3
                       (view_of G out es hj) (view_of G' out' es' hj')
                       (fun e0 He0 => proj2 (HU0 e0 He0)) (fun e0 He0 => proj2 (HU1 e0 He0))
                       (fun e0 He0 => proj2 (HU2 e0 He0)) (fun e0 He0 => proj2 (HU3 e0 He0))
                       (fun e0 He0 => proj2 (HU4 e0 He0)) HND0 HN1 HN3 HY1 HY2 HY3 HY4 K1 (K2 HK2));
                [| | | |reflexivity|reflexivity| | | | |exact HK].
              ** intros e0 He0. destruct (run3_mis_src2 qs3 b2 0 _ e0 He0) as [(X & _)|X]; [exact X|].
                 exfalso. exact (frees_inplace qs3 0 _ _ (proj1 (ends_free _ _ _ _ _)) X).
              ** intros e0 He0. destruct (run3_mis_src2 qs4 b3 0 _ e0 He0) as [(X & Hu)|X];
                   [|exfalso; exact (frees_inplace qs4 0 _ _ (reset_free _ _) X)].
                 split; [exact X|]. intros x Hx Heq. destruct (reset_free_at (known_at L3 A3) h3 x Hx) as (m & Hm).
                 apply Hu. rewrite Heq. exact (touched_free qs4 _ m _ Hm).
              ** intros x Hx. unfold dsl, a0, nm. cbn [drain_init ds_cap ds_ka ds_ecap drain_start da_buf da_hp da_ev
                   resolve known_at].
                 rewrite !map_app, !in_app_iff in Hx. rewrite !in_app_iff.
                 destruct Hx as [Hx|[Hx|Hx]].
                 --- unfold out_move_dels in Hx. destruct (out_same out CAP OUT' C1 || (CAP =? 0)) eqn:Eo; [destruct Hx|].
                     destruct Hx as [<-|[]]. left. apply slot3_mem. apply orb_false_iff in Eo as [_ Eo].
                     apply Z.eqb_neq. exact Eo.
                 --- unfold entry_dels in Hx. rewrite map_app, in_app_iff in Hx. destruct Hx as [Hx|Hx].
                     +++ destruct (Z.eqb_spec (re_cap e) 0) as [Z0|Z0]; [destruct Hx|]. destruct Hx as [<-|[]].
                         right. left. left. apply slot3_mem. exact Z0.
                     +++ destruct (Z.eqb_spec (re_hp e) 0) as [Z0|Z0]; [destruct Hx|]. destruct Hx as [<-|[]].
                         right. left. right. left. apply slot3_mem. unfold ent_ka.
                         rewrite (proj2 (Z.eqb_neq _ _) Z0). exact (Hkh Z0).
                 --- apply arr_sz_in in Hx as (-> & Z0). right. left. right. right. apply slot3_mem. exact Z0.
              ** intros x Hx. unfold src_dels. rewrite EH3p, EH3a. rewrite !map_app, !in_app_iff.
                 apply in_app_or in Hx as [Hx|Hx].
                 --- left. unfold arr_sz in *. rewrite HPc1, HPv1. exact Hx.
                 --- right. left. rewrite HPa1. exact Hx.
              ** intros Hc'. split; [exact (HSL1 Hc')|]. rewrite <- (HR'v Hc').
                 apply src_dels_held; [rewrite EH3h, CH''; exact Hc'|rewrite EH3h, VH''; reflexivity].
              ** intros Hc' Hmem. apply src_dels_exp; [rewrite EH3e, HE'c, HEc1; exact Hc'|]. rewrite EH3e, HE'v.
                 destruct (Z.eqb_spec (re_eof e) 0) as [Ee|Ee].
                 --- pose proof (HSL Ee) as (_ & _ & _ & (HEL & _) & _).
                     assert (Hpos : 0 < hl_cap (hs_expected h1)) by (rewrite HEc1; lia).
                     destruct (HEL Hpos) as (_ & Ha). exact Ha.
                 --- rewrite (Hh1 Ee).
                     assert (Ea1 : a1 = a0) by (unfold a1, after_drain_adr; rewrite (proj2 (Z.eqb_neq _ _) Ee); reflexivity).
                     assert (Es : ds_ecap s = hl_cap (hs_expected h))
                       by (unfold s, after_drain; rewrite (proj2 (Z.eqb_neq _ _) Ee); reflexivity).
                     rewrite Ea1. unfold a0, nm. cbn [drain_start da_ev resolve known_at].
                     destruct HSE as [X|X]; [rewrite Es in Hc'; contradiction|].
                     destruct (sptr_of_spec L0 A0 _ _ (proj2 (stdpp.base.NoDup_ListNoDup _) HND0) X) as (Hu0 & Ha0).
                     destruct Hmem as (n1 & Hn1). rewrite Ea1 in Hn1. unfold a0, nm in Hn1.
                     cbn [drain_start da_ev resolve known_at] in Hn1.
                     rewrite (HY1 _ _ _ Hu0 Hn1). exact Ha0.
              ** intros Hc0 Hne. destruct olv.
                 --- destruct (HQL eq_refl) as (Hu & Ha).
                     change (remove_entry_out lv MX 0 CAP e h 0 (drain_start (known_at L0 A0) (known_at L0 A0 out) e h))
                       with (remove_entry_out lv MX 0 CAP e h 0 a0) in Hu, Ha.
                     split; [exists C1; exact Hu|]. rewrite Ha.
                     apply (nc_move_adds_in _ _ _ _ _ _ _ _ (OUT', C1) HM). unfold CF.SlotPass4.p4_adds, out_move_adds, out_same.
                     rewrite (proj2 (Z.eqb_neq C1 CAP) Hne), andb_false_r. left. reflexivity.
                 --- destruct (HQN eq_refl) as (_ & X). contradiction.
              ** intros Hc0 Heq. pose proof (Hoq Heq) as Eo. rewrite Eo. unfold nm. cbn [resolve known_at].
                 destruct HCAP as [X|X]; [rewrite <- Heq in X; contradiction|].
                 destruct (sptr_of_spec L0 A0 _ _ (proj2 (stdpp.base.NoDup_ListNoDup _) HND0) X) as (Hu0 & Ha0).
                 split; [exists CAP; exact Hu0|]. rewrite Ha0. split; [cbn [view_of rv_nc]; right; left; reflexivity|].
                 assert (EO : OUT' = out).
                 { destruct olv.
                   - destruct (HQL eq_refl) as (Hu & Ha).
                     change (remove_entry_out lv MX 0 CAP e h 0 (drain_start (known_at L0 A0) (known_at L0 A0 out) e h))
                       with (remove_entry_out lv MX 0 CAP e h 0 a0) in Hu, Ha.
                     rewrite Eo in Hu, Ha. unfold nm in Hu, Ha.
                     cbn [resolve known_at] in Hu, Ha. rewrite <- Ha, (HY1 _ _ _ Hu0 Hu). exact Ha0.
                   - exact (proj1 (HQN eq_refl)). }
                 unfold CF.SlotPass4.p4_dels, out_move_dels, out_same. rewrite EO, Z.eqb_refl, Heq, Z.eqb_refl. cbn [andb orb app].
                 intros Hx. unfold target_addrs in HNT. apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HNT.
                 apply List.NoDup_cons_iff in HNT as [_ HNT].
                 apply List.NoDup_cons_iff in HNT as [HNo _]. apply HNo. rewrite map_app, in_app_iff in Hx.
                 apply in_app_iff. destruct Hx as [Hx|Hx].
                 --- left. apply in_concat. exists (entry_blocks e). split; [apply in_map; exact Hine|].
                     exact (entry_dels_sub e out Hx).
                 --- right. apply in_concat. exists (hs_blocks h). split; [exact (in_map (fun p => hs_blocks (fst p)) _ _ Hin)|].
                     exact (src_dels_sub h out Hx).
Qed.
