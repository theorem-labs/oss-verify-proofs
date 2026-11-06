(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 625 of its 671 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/CF/SlotPass9G.v, with its addresses and numbers changed; 514 of its 724 lines of code are new or changed and 461 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/CF/SlotPass1.v, with its module names changed; 292 of its 344 lines of code are new or changed and 672 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack
  AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b_c source_reset_c op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_bounded_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotInv SlotSteps SlotHead SlotHeadP SlotRes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessGlue HarnessFrame SlotReads SlotEntryRun SlotEntry.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotHeadRun SlotHeadPick SlotHeadQ SlotHeadQD SlotPass1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import pthread_mutex_lock_c pthread_mutex_unlock_c pthread_mutex_lock_ro_c pthread_mutex_unlock_ro_c pthread_mutex_lock_ro pthread_mutex_unlock_ro.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotPass9G SlotPass2Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_no_loss_read_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import check_no_loss_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_shape_done_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotPass2Check SlotPass2Aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRunT RelayRunF TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require RelayCap relay_remove_b_aux SlotPass4.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotMove SlotWalk SlotPass2Mv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require SlotRI3 SlotNcWt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Cells.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition p2_dregs (E : sstart) (t K SA HA : Z) (R : bvmap 5 word) : Prop :=
  YK11.getr R 1 = Z_to_bv 64 0x14378 /\ YK11.getr R 2 = Z_to_bv 64 (slot_sp E) /\
  YK11.getr R 3 = YK11.getr (ss_regs E) 3 /\ YK11.getr R 4 = YK11.getr (ss_regs E) 4 /\
  YK11.getr R 8 = Z_to_bv 64 (ss_p E + K) /\ YK11.getr R 9 = Z_to_bv 64 HA /\
  YK11.getr R 10 = Z_to_bv 64 SA /\ YK11.getr R 18 = Z_to_bv 64 SA /\ YK11.getr R 19 = Z_to_bv 64 0x318f8 /\
  YK11.getr R 20 = Z_to_bv 64 G_RELAY_LO /\ YK11.getr R 21 = Z_to_bv 64 10 /\ YK11.getr R 22 = Z_to_bv 64 t /\
  YK11.getr R 23 = Z_to_bv 64 (slot_sp E + 32) /\ YK11.getr R 24 = Z_to_bv 64 1 /\
  YK11.getr R 25 = Z_to_bv 64 DIV10 /\ YK11.getr R 26 = Z_to_bv 64 (ss_n E - K) /\
  YK11.getr R 27 = Z_to_bv 64 (G_S + 4).

Definition p2_drain_st (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (rc : RunCeil) (E : sstart)
    (RI : res_inv) (t K : Z) (c : config) : Prop :=
  exists (fx' : FPState) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
         (cl br gn dd ei G nfd : Z) (mx nout cap out : word) (es : list rentry) (hj : list (hsrc * nat))
         (i : nat) (e : rentry) (h : hsrc) (jj : nat) (R : bvmap 5 word) (m1 : word -> option byte),
    c = mkCfg (@YK11.mkst fx' R (Z_to_bv 64 DRAIN) m1 (seg_rom (ms_segs B))) md /\
    frm_zero (@fp_csr fx') /\ 0 <= t < OPS_MAX /\ 0 <= K <= ss_n E /\ ss_n E < INPUT_MAX /\
    aa_MR (API rc) L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\
    (exists vm, md = with_vmmaps vm (ss_md E)) /\ ro_agree (ms_segs B) mem /\
    image_kept (rc := rc) B E mem /\ stack_mid B E mem /\
    driver_kept B E (target_addrs G (bv_unsigned out) es hj) L A mem /\
    globals_at B mem cl br gn dd ei (Z.of_nat (length es)) G nfd mx nout cap out /\ 0 <= nfd <= t + 1 /\
    output_at (rc := rc) B L A mem nout cap out /\ relay_at (rc := rc) B L A mem t nfd G (bv_unsigned out) es hj /\
    (length es <= 4)%nat /\ slot_cost es hj <= K /\ RI E K (view_of G (bv_unsigned out) es hj) L A /\
    bv_unsigned nout = 0 /\
    nth_error es i = Some e /\ nth_error hj i = Some (h, jj) /\ re_eof e = 0 /\
    p2_dregs E t K (G + 56 * Z.of_nat i) (G_S + SRC_SIZE * Z.of_nat jj) R /\
    munch [(slot_sp E + 40, slot_sp E + 48); (0x318fc, 0x31900)] mem m1 /\ wmono (ms_segs B) mem m1 /\
    ro_agree (ms_segs B) m1 /\
    rw_cells (ms_segs B) m1 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] /\
    rw_cells (ms_segs B) m1 (slot_sp E + 40) [C8 (Z_to_bv 64 0)].

Definition p2_drain_RV_s (RI : res_inv) (E : sstart) (k : Z) (L : layout) (A : astate) (G out : Z)
    (es : list rentry) (hj : list (hsrc * nat)) (e : rentry) (h : hsrc) (CAP : Z) (live : bool) (fin : dstate)
    (fa : dadr) (L' : layout) (A' : astate) (qs : list sptr) : Prop :=
  forall (e' : rentry) (h' : hsrc) (OUT' : Z),
    (live = true -> live_at L' A' (resolveF qs (da_out fa)) OUT' (ds_ocap fin)) ->
    (live = false -> OUT' = out /\ ds_ocap fin = CAP) ->
    entry_links L' A' qs fa e' -> src_links L' A' qs (known_at L A) fa h' ->
    re_cap e' = ds_cap fin -> ent_ka e' = ds_ka fin -> hl_cap (hs_expected h') = ds_ecap fin ->
    forall G' out' es' hj',
      (forall q m, In (q, m) (blocks L' A') -> In (q, m) (blocks L A) \/ In q (target_addrs G' out' es' hj')) ->
      (exists p1 p2, pend_view hj = p1 ++ map snd (hl_recs (hs_pending h)) :: p2 /\ pend_view hj' = p1 ++ [] :: p2) ->
      (exists k1 k2, ek_view hj = k1 ++ ekeys_hl (hs_expected h) ++ k2 /\
         ek_view hj' = k1 ++ ekeys_hl (hs_expected h) ++ ekeys (lines (hs_state h) (bzs (pending_stream h))) ++ k2) ->
      (length es' <= 4)%nat -> (length hj' <= 4)%nat ->
      nc_move (view_of G out es hj) L A (view_of G' out' es' hj') L' A'
        (p2_dr_dels out CAP OUT' (ds_ocap fin) e e' (hs_expected h) (hs_expected h'))
        (p2_dr_adds out CAP OUT' (ds_ocap fin) e e' (hs_expected h) (hs_expected h')) ->
      List.NoDup (map fst (blocks L' A')) ->
      (forall p n n', In (p, n) (user_blocks A) -> In (p, n') (user_blocks A') ->
         In (ptr_addr L p) (rv_nc (view_of G out es hj)) ->
         ~ In (ptr_addr L p) (map fst (p2_dr_dels out CAP OUT' (ds_ocap fin) e e' (hs_expected h) (hs_expected h'))) ->
         In (ptr_addr L' p) (rv_nc (view_of G' out' es' hj'))) ->
      CF.SlotRI3.ncs (view_of G' out' es' hj') L' A' <= nc_wt es' hj' -> nc_wt es' hj' <= drain_wt es hj e h fin ->
      RI E k (view_of G' out' es' hj') L' A'.

Definition p2_drain_res_s (F : ResFormT) (RI : res_inv) : Prop :=
  forall E k L A G out es hj i e h j live mx NO CAP,
    RI E k (view_of G out es hj) L A -> List.NoDup (map fst (blocks L A)) -> 0 <= k <= ss_n E ->
    slot_cost es hj <= k -> pair_cost e (h, j) <= k ->
    NoDup (target_addrs G out es hj) -> nth_error es i = Some e -> nth_error hj i = Some (h, j) -> re_eof e = 0 ->
    CF.SlotPass4.p4_ent_blk L A e -> CF.SlotPass4.p4_src_blk L A h -> (CAP = 0 \/ In (out, CAP) (blocks L A)) ->
    0 <= mx <= 255 -> 0 <= NO <= CAP -> CAP <= TBBYTES ->
    hl_recs (hs_expected h) = [] -> ecap_ok (hl_cap (hs_expected h)) ->
    Z.of_nat (length (pending_stream h)) < WRITE_MAX * OPS_MAX ->
    0 <= re_cap e -> 0 <= ent_ka e -> J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h) -> 0 <= hs_off h ->
    re_nheld e + Z.of_nat (length (pending_stream h)) < 2 ^ 26 -> Z.of_nat (length (re_U e)) <= re_used e ->
    (re_hp e <> 0 -> re_kh e <> 0) -> ds_ocap (drain_fin live mx NO CAP e h) <= SlotCaps3.NMAX ->
    (CAP = 0 -> forall m, ~ In (out, m) (blocks L A)) -> (length es <= 4)%nat -> (length hj <= 4)%nat ->
    ecap_ok (ds_ecap (drain_fin live mx NO CAP e h)) /\
    res_tr F (p2_drain_RV_s RI E k L A G out es hj e h CAP live (drain_fin live mx NO CAP e h)
        (drain_adr live mx NO CAP e h 0 (drain_start (known_at L A) (known_at L A out) e h))) A
      (drain_tr live mx NO CAP e h 0 (drain_start (known_at L A) (known_at L A out) e h)).

Definition p2_cnl_RV_s (RI : res_inv) (E : sstart) (k : Z) (L : layout) (A : astate) (G out : Z)
    (es : list rentry) (hj : list (hsrc * nat)) (h : hsrc) (L' : layout) (A' : astate) (qs : list sptr) : Prop :=
  forall (E' H' : hlist),
    sh_real L' qs (check_no_loss_sh 0 (sh_of (known_at L A) (hs_held h))
      (map (shr (known_at L A)) (hl_recs (hs_expected h)))) H' ->
    sh_live A' qs (check_no_loss_sh 0 (sh_of (known_at L A) (hs_held h))
      (map (shr (known_at L A)) (hl_recs (hs_expected h)))) ->
    hl_recs E' = [] -> hl_v E' = hl_v (hs_expected h) -> hl_cap E' = hl_cap (hs_expected h) ->
    NoDup (texts H') -> texts H' = upds (texts (hs_held h)) (texts (hs_expected h)) ->
    (forall x m, In (x, m) (blocks L' A') ->
       (In (x, m) (blocks L A) /\ (0 < m -> ~ In x (map fst (hl_recs (hs_expected h)) ++ list_blocks (hs_held h)))) \/
       In x (list_blocks H')) ->
    (forall x m, In (x, m) (blocks L A) -> 0 < m ->
       ~ In x (map fst (hl_recs (hs_expected h)) ++ list_blocks (hs_held h)) -> ~ In x (list_blocks H')) ->
    (forall x m, In (x, m) (blocks L A) -> ~ In x (hs_blocks h) -> In (x, m) (blocks L' A')) ->
    CF.SlotPass4.p4_src_blk L' A' (set_exp_held h E' H') ->
    forall G' out' es' hj',
      (forall q m, In (q, m) (blocks L' A') -> In (q, m) (blocks L A) \/ In q (target_addrs G' out' es' hj')) ->
      pend_view hj' = pend_view hj ->
      (exists k1 k2, ek_view hj = k1 ++ ekeys_hl (hs_expected h) ++ k2 /\ ek_view hj' = k1 ++ k2) ->
      (length es' <= 4)%nat -> (length hj' <= 4)%nat ->
      nc_move (view_of G out es hj) L A (view_of G' out' es' hj') L' A'
        (p2_arr_dels (hs_held h) H') (p2_arr_adds (hs_held h) H') ->
      List.NoDup (map fst (blocks L' A')) ->
      (forall p n n', In (p, n) (user_blocks A) -> In (p, n') (user_blocks A') ->
         In (ptr_addr L p) (rv_nc (view_of G out es hj)) ->
         ~ In (ptr_addr L p) (map fst (p2_arr_dels (hs_held h) H')) ->
         In (ptr_addr L' p) (rv_nc (view_of G' out' es' hj'))) ->
      CF.SlotRI3.ncs (view_of G' out' es' hj') L' A' <= nc_wt es' hj' -> nc_wt es' hj' <= cnl_wt es hj h ->
      RI E k (view_of G' out' es' hj') L' A'.

Definition p2_cnl_res_s (F : ResFormT) (RI : res_inv) : Prop :=
  forall E k L A G out es hj i e h j,
    RI E k (view_of G out es hj) L A -> List.NoDup (map fst (blocks L A)) -> 0 <= k <= ss_n E ->
    slot_cost es hj <= k ->
    NoDup (target_addrs G out es hj) -> nth_error es i = Some e -> nth_error hj i = Some (h, j) ->
    CF.SlotPass4.p4_src_blk L A h ->
    hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 ->
    res_tr F (p2_cnl_RV_s RI E k L A G out es hj h) A
      (check_no_loss_tr 0 (sh_of (known_at L A) (hs_held h)) (map (shr (known_at L A)) (hl_recs (hs_expected h)))).

Lemma p2_bzs_map : forall Ls, Forall zrange Ls -> map bzs (map (map (Z_to_bv 8)) Ls) = Ls.
Proof. induction 1 as [|l Ls Hl _ IH]; [reflexivity|]. cbn [map]. rewrite bzs_lits by exact Hl. f_equal. exact IH. Qed.

Lemma p2_ekeys_app : forall (l l' : hlist) Ls,
  map snd (hl_recs l') = map snd (hl_recs l) ++ map (map (Z_to_bv 8)) Ls -> Forall zrange Ls ->
  ekeys_hl l' = ekeys_hl l ++ ekeys Ls.
Proof.
  intros l l' Ls H Z. unfold ekeys_hl, ekeys.
  rewrite <- (map_map snd bzs (hl_recs l')), H, map_app, (map_map snd bzs), (p2_bzs_map Ls Z), map_app, concat_app.
  reflexivity.
Qed.

Lemma p2_ek_split : forall (hj : list (hsrc * nat)) i p,
  ek_view (firstn i hj ++ p :: skipn (S i) hj) =
    ek_view (firstn i hj) ++ ekeys_hl (hs_expected (fst p)) ++ ek_view (skipn (S i) hj).
Proof. intros hj i p. unfold ek_view. rewrite map_app, concat_app. reflexivity. Qed.

Lemma p2_sbs_enc : forall e e', p2_sbs e e' -> entry_nc e' = entry_nc e.
Proof. intros e e' (_ & _ & _ & _ & A5 & _ & A7 & A8 & _). unfold entry_nc. rewrite A5, A7, A8. reflexivity. Qed.

Lemma p2_sbs_cnc : forall l l', Forall2 p2_sbs l l' -> concat (map entry_nc l') = concat (map entry_nc l).
Proof.
  intros l l' H. induction H as [|a b l l' Hab H IH]; [reflexivity|]. cbn [map concat].
  rewrite (p2_sbs_enc a b Hab), IH. reflexivity.
Qed.

Lemma MI_op2_scan : forall B API LS SH SK ra empty rc fx j E CS RI t K s c,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> check_bounded_contract -> pthread_mutex_lock_contract ->
  walk_at (ss_pl E) (t + 1) K ->
  MI (rc := rc) B (API rc) E RI t K 0x14334 (fun _ hj no regs => no = 0 /\ disp_src 2 s hj /\ disp_regs E t K s regs) c ->
  SR (ms_segs B) c (fun c' => LI (rc := rc) B (API rc) E RI (t + 1) K c' \/ p2_drain_st B API rc E RI t K c').
Proof.
  intros B API LS SH SK ra empty rc fx j E CS RI t K s c HF CB LCK HWK HM.
  pose proof (pthread_mutex_lock_ro_of LCK) as LCKR.
  destruct (p2_ff B API LS SH SK ra empty rc fx j E CS HF)
    as (SEG & ERR & ETP & FA & PL & SPLO & SPHI & ALIGN & TP & MR0 & PIN & NI).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  destruct HM as (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & FZ & Ht & Hk & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd & HOUT & HREL &
    Hes & Hcost & HRI).
  replace (t + (if (0x14334 =? TAIL_CHECK) || (0x14334 =? TAIL_STEP) then 1 else 0)) with t in HREL
    by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
  destruct HR as (HNO & DS & (B2 & B3 & B4 & B20) & (F23 & F25 & F21 & F19 & F27 & F24) & R8 & R26 & R22 & R9).
  destruct DS as [(_ & jj & HJJ & OJ & ->)|([HPF|HO1] & _)]; [|vm_compute in HPF; discriminate|discriminate].
  set (HA := G_S + SRC_SIZE * Z.of_nat jj) in *.
  pose proof HREL as ((tail & TL & TB) & GIN & GFR & HES & NDF & FDR & PA & NDH & ZH & NDA).
  assert (SRCI : exists h, In (h, jj) hj /\ src_at (rc := rc) B L A mem HA h).
  { pose proof OJ as OI'. unfold slot_open in OI'. apply existsb_exists in OI'. destruct OI' as (q & HQ & HE).
    apply Nat.eqb_eq in HE. subst q. apply in_map_iff in HQ. destruct HQ as ([h q] & EQ & HQ). cbn in EQ. subst q.
    destruct (pair_find _ _ _ _ _ (h, jj) PA HQ) as [e HP0]. exists h. split; [exact HQ|].
    destruct HP0 as (SRC & _). cbv zeta in SRC. cbn [fst snd] in SRC. exact SRC. }
  destruct SRCI as (h & HIN & SRC). pose proof SRC as (SC1 & _ & _ & _ & FDH & _).
  set (SP := slot_sp E) in *.
  assert (SPB1 : 2 ^ 20 <= SP) by (unfold SP, slot_sp, SLOT_FRAME; unfold SLOT_STACK in SPLO; lia).
  assert (SPB2 : SP + 192 <= 2 ^ 63) by (unfold SP, slot_sp, SLOT_FRAME; lia).
  assert (HKc : @YM05.alloc_ceiling rc <= SP - (SLOT_STACK - SLOT_FRAME))
    by (unfold SP, slot_sp, SLOT_FRAME, SLOT_STACK in *; lia).
  assert (HKc' : @YM05.alloc_ceiling rc + 65344 <= SP) by (unfold SLOT_STACK, SLOT_FRAME in HKc; lia).
  assert (HAB : 0x31920 <= HA /\ HA + 96 <= 0x31aa0) by (unfold HA, G_S, SRC_SIZE; lia).
  assert (HA8 : HA mod 8 = 0) by (unfold HA, G_S, SRC_SIZE; Z.div_mod_to_equations; lia).
  assert (GB : 4096 <= G /\ G + 896 <= @YM05.alloc_ceiling rc) by (destruct GFR as (G0 & G1 & _); split; assumption).
  assert (GAL : G mod 8 = 0).
  { pose proof GIN as GI. unfold blocks in GI. apply in_map_iff in GI as ([p k'] & EG & Hp). cbn [fst snd] in EG.
    injection EG as EG _. rewrite <- EG.
    pose proof (mr_blocks_aligned _ _ (aa_laws (API rc)) L A mem md p k' HMR Hp) as H16.
    Z.div_mod_to_equations. lia. }
  assert (HGP : es <> [] -> 0 < G /\ G mod 8 = 0 /\ (G + 896 <= SP + 40 \/ SP + 48 <= G)).
  { intros _. split; [lia|]. split; [exact GAL|]. left. lia. }
  pose proof HGL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & GER & GRG).
  assert (RN : ov_read_bytes rsegs mem (Z_to_bv 64 0x318b8) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length es))))).
  { pose proof (rw_cells_read _ _ _ _ 0%nat (C4 (Z_to_bv 64 (Z.of_nat (length es)))) G8 eq_refl) as X.
    rewrite SEG in X. exact X. }
  assert (RF : ov_read_bytes rsegs mem (Z_to_bv 64 HA) 4 = Some (le4 (Z_to_bv 64 (hs_fd h)))).
  { pose proof (rw_cells_read _ _ _ _ 0%nat (C4 (Z_to_bv 64 (hs_fd h))) SC1 eq_refl) as X.
    rewrite SEG in X. change (Z.of_nat 0) with 0 in X. rewrite Z.add_0_r in X. exact X. }
  assert (RG : ov_read_bytes rsegs mem (Z_to_bv 64 0x318d0) 8 = Some (le8 (Z_to_bv 64 G))).
  { pose proof (rw_cells_read _ _ _ _ 0%nat (C8 (Z_to_bv 64 G)) G10 eq_refl) as X. rewrite SEG in X. exact X. }
  assert (HW : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) es).
  { eapply Forall_impl; [|exact HES]. intros e0 He0. exact (p2_entry_scan rc B L A mem e0 He0). }
  assert (WSP : forall a, SP + 16 <= a < SP + 88 -> writable_at rsegs mem a).
  { intros a Ha. rewrite <- SEG. apply (proj2 (proj2 (proj2 HIK))). left. unfold SP, slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (PJ : forall i, 0 <= i < Z.of_nat 8 -> present mem (SP + 40 + i)).
  { intros i Hi. cbn in Hi. apply writable_hi_present; [lia|]. apply WSP. lia. }
  destruct (present_rw_cells rsegs mem (SP + 40) 8 ltac:(lia) ltac:(cbn; lia) PJ) as [junk HJ].
  rewrite SEG in TB, G12, HRO.
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & _).
  set (m' := write_to_mem mem (Z_to_bv 64 (SP + 40)) (le8 (Z_to_bv 64 0))).
  assert (MU : munch [(SP + 40, SP + 48)] mem m').
  { unfold m'. change (Z_to_bv 64 (SP + 40)) with (wa (SP + 40)).
    eapply munch_write; [apply munch_refl|lia|rewrite length_le8; lia|cbn [inside]; left; rewrite length_le8; lia]. }
  assert (WM : wmono rsegs mem m') by (unfold m'; apply wmono_write, wmono_refl).
  assert (MU16 : munch [(SP + 32, SP + 32 + 16)] mem m').
  { eapply munch_weaken; [|exact MU]. intros x HX. cbn [outside] in HX |- *. destruct HX as (H1 & _).
    split; [lia|exact I]. }
  assert (RM : rmid B (API rc) (SLOT_STACK - SLOT_FRAME) SP (fun a => SP + 40 <= a < SP + 48) (fun _ => False)
      L A mem md L A m' md).
  { apply (rmid_A B (API rc) _ _ _ _ L A mem md m' [(SP + 40, SP + 48)] HMR HWF HBD (hg_img_low B SEG) HKc).
    - intros a Ha. destruct Ha as [Ha|Ha]; apply (proj2 (proj2 (proj2 HIK))); unfold lib_scratch;
        [left; unfold SP, slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|right; exact Ha].
    - exact MU.
    - rewrite SEG. exact WM.
    - intros x Hx HO. right. cbn [outside] in HO. lia.
    - intros a HO. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HMR HO). cbn [outside]. split; [lia|exact I].
    - intros p n k HP Hk0 HO. exfalso. apply HO. cbn [outside].
      destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p n k HMR HP Hk0) as (_ & _ & X & _). split; [lia|exact I]. }
  assert (KPT : image_kept (rc := rc) B E m' /\ stack_mid B E m' /\
      driver_kept B E (target_addrs G (bv_unsigned out) (map short_entry es) hj) L A m').
  { apply (p2_kept B API LS SH SK ra empty rc fx j E CS L A mem md L A m' md _ _ (target_addrs G (bv_unsigned out) es hj)
      (target_addrs G (bv_unsigned out) (map short_entry es) hj) HF HMR HWF HIK HST HDK RM).
    - intros a Ha. right. left. lia.
    - intros a Ha. destruct (Z_lt_le_dec a (SP + 40)) as [L1|L1]; [left; lia|].
      destruct (Z_lt_le_dec a (SP + 48)) as [L2|L2]; [right|left; lia].
      rewrite SEG. apply WM. apply WSP. lia.
    - intros q [].
    - intros x Hx. left. rewrite short_target in Hx. exact Hx.
    - intros q m Hq. rewrite short_target. destruct (in_dec Z.eq_dec q (target_addrs G (bv_unsigned out) es hj)) as [X|X];
        [right; exact X|left; split; [exact Hq|exact X]]. }
  destruct KPT as (IK' & ST' & DK').
  pose proof RM as (MR' & _).
  assert (RO' : ro_agree (ms_segs B) m').
  { rewrite SEG. apply (g9_ro_munch [(SP + 40, SP + 48)] mem m' MU); [|exact HRO].
    intros a HA0. cbn [outside]. split; [|exact I].
    destruct (Z_lt_le_dec (bv_unsigned a) (2 ^ 20)) as [L1|L1]; [lia|].
    pose proof (bv_unsigned_in_range 64 a) as AR. change (bv_modulus 64) with (2 ^ 64) in AR.
    pose proof (ro_addr_hi (bv_unsigned a) ltac:(lia)) as X. rewrite Z_to_bv_bv_unsigned in X. congruence. }
  assert (S16 : @YM05.alloc_ceiling rc + 8 <= SP + 32) by lia.
  assert (TLC : forall R1, tail_regs E t K R1 ->
    SR (ms_segs B) (mkCfg (@YK11.mkst fx' R1 (Z_to_bv 64 TAIL_CHECK) m' (seg_rom (ms_segs B))) md)
      (fun c' => LI (rc := rc) B (API rc) E RI (t + 1) K c' \/ p2_drain_st B API rc E RI t K c')).
  { intros R1 TR.
    eapply SR_mono; [eapply (MI_tail B API LS SH SK ra empty rc fx j E CS RI t K (fun _ _ _ r => tail_regs E t K r));
      [exact HF|exact CB|intros; assumption|exact HWK|]|intros c' HC; left; exact HC].
    exists fx', L, A, R1, m', md, cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out, (map short_entry es), hj.
    split; [reflexivity|]. split; [exact FZ|]. split; [exact Ht|]. split; [exact Hk|]. split; [exact Hn|].
    split; [exact TR|].
    split; [exact MR'|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HINIT|]. split; [exact HVM|].
    split; [exact RO'|]. split; [exact IK'|]. split; [exact ST'|]. split; [exact DK'|].
    split; [rewrite length_map; eapply tail_globals; [exact S16|lia|rewrite ERR; lia|exact MU16|rewrite SEG; exact WM
      |exact HGL]|].
    split; [(revert Hnfd; cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia)|].
    split; [eapply tail_output; [exact S16|exact MU16|exact HOUT]|].
    split; [eapply relay_at_t; [eapply tail_relay; [exact S16|unfold G_S; lia|exact MU16|rewrite SEG; exact WM|exact HREL]
      |cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia]|].
    split; [rewrite length_map; exact Hes|]. split; [rewrite short_cost; exact Hcost|rewrite short_view; exact HRI]. }
  assert (E2 : reg_get regs 2 = Z_to_bv 64 SP) by exact B2.
  assert (E3 : reg_get regs 3 = getr (ss_regs E) 3) by exact B3.
  assert (E4 : reg_get regs 4 = getr (ss_regs E) 4) by exact B4.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 (ss_p E + K)) by exact R8.
  assert (E9 : reg_get regs 9 = Z_to_bv 64 HA) by exact R9.
  assert (E19 : reg_get regs 19 = Z_to_bv 64 4) by exact F19.
  assert (E20 : reg_get regs 20 = Z_to_bv 64 G_RELAY_LO) by exact B20.
  assert (E21 : reg_get regs 21 = Z_to_bv 64 10) by exact F21.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 t) by exact R22.
  assert (E23 : reg_get regs 23 = Z_to_bv 64 (SP + 32)) by exact F23.
  assert (E24 : reg_get regs 24 = Z_to_bv 64 1) by exact F24.
  assert (E25 : reg_get regs 25 = Z_to_bv 64 DIV10) by exact F25.
  assert (E26 : reg_get regs 26 = Z_to_bv 64 (ss_n E - K)) by exact R26.
  assert (E27 : reg_get regs 27 = Z_to_bv 64 (G_S + 4)) by exact F27.
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2, E3, E4, E8, E9, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    exact (op2_pre LCKR es tail junk G SP HA (hs_fd h) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem
      RN RF RG TB HW Hes FDH HJ SPB1 ltac:(lia) G12 HRO ltac:(lia) HA8 HGP). }
  intros ms1 (can1 & HQ & EQ1).
  destruct HQ as [(HN & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & ->)|(i & e & Hi & Hfe & Hpre &
    [(E1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & ->)|
     (E0 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & -> & MU1 & WM1 & RO1 &
      CK1 & C401)])].
  - destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    rewrite <- SEG. apply TLC. unfold tail_regs, base_regs, fix_regs. repeat split; geq X1.
  - destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    rewrite <- SEG. apply TLC. unfold tail_regs, base_regs, fix_regs. repeat split; geq X1.
  - destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    apply SR_ret. right. unfold p2_drain_st.
    exists fx', L, A, mem, md, cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out, es, hj, i, e, h, jj, R1, m1.
    split; [rewrite SEG; reflexivity|]. split; [exact FZ|]. split; [exact Ht|]. split; [exact Hk|]. split; [exact Hn|].
    split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HINIT|]. split; [exact HVM|].
    split; [rewrite SEG; exact HRO|]. split; [exact HIK|]. split; [exact HST|]. split; [exact HDK|].
    split; [exact HGL|]. split; [exact Hnfd|]. split; [exact HOUT|]. split; [exact HREL|].
    split; [exact Hes|]. split; [exact Hcost|]. split; [exact HRI|]. split; [exact HNO|].
    split; [exact Hi|]. split; [exact (p2_pair_idx rc B L A mem t es hj i e h jj PA NDF Hi HIN (eq_sym Hfe))|].
    split; [exact E0|].
    split; [unfold p2_dregs; repeat split; geq X1|].
    split; [exact MU1|]. split; [rewrite SEG; exact WM1|]. split; [rewrite SEG; exact RO1|].
    split; rewrite SEG; assumption.
Qed.

Ltac p2g ha :=
  let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; cbn in Hk;
  unfold CF.relay_finish_b_c.G_THREAD_UP, CF.SlotInv.G_WAKE0, CheckRep.G_GONE, send_line_c.G_DEAD, CF.relay_add_b_c.G_NSRC,
    CF.op_add_c.G_NFD, CF.relay_add_b_c.G_SRC, relay_event_c.G_LOCK, send_line_c.G_BROKEN, send_line_c.G_EINTR,
    send_line_c.G_OUTV, ha, HarnessRep.G_S, SRC_SIZE;
  split; [first [apply in_G_bss; clear - Hk; lia|apply g9_in_listen; clear - Hk; lia]|repeat split; clear - Hk; lia].

Ltac p2_chain X5 PRc X3 k :=
  etransitivity; [apply (getr_of_eqv _ _ _ X5); reflexivity|];
  etransitivity; [exact (PRc k (p2_cs k eq_refl))|];
  etransitivity; [apply (getr_of_eqv _ _ _ X3); reflexivity|].
