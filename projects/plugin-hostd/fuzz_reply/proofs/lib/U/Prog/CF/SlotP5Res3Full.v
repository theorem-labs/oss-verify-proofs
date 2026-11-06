From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept SlotInv SlotSteps SlotRes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotParse SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotRI3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRunT RelayRunF RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep ListRep CheckRep ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessTr send_line_b_c gesture_end_b_c gestures_end_b_c drain_b_c relay_remove_b_c relay_instance_gone_b_c SlotRun3 SlotP5R3 SlotP5R3G SlotDrain3Aux SlotDrain3 SlotDrainWt3 SlotP5Res3.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition p5c_res3_full : Prop :=
  forall (E : sstart) (K K' : Z) (L : layout) (A : astate) (G OUT : Z) (es : list rentry) (hs : list (hsrc * nat))
         (lv : bool) (mx NO CAP : Z) (pre : list Z),
    let nm := known_at L A in
    let V := view_of G OUT es hs in
    let tr := relay_instance_gone_tr lv mx NO CAP pre es hs nm 0 (nm OUT) in
    RI3_reply E K V L A -> K <= K' ->
    length hs = length es -> (length es <= 4)%nat -> 0 <= mx -> 0 <= CAP ->
    Forall (fun p => re_eof (fst p) = 0 ->
              0 <= re_cap (fst p) /\ 0 <= ent_ka (fst p) /\
              J1 (bzs (re_U (fst p))) (re_skip (fst p) =? 1) (hs_state (fst (snd p))) /\
              0 <= hs_off (fst (snd p)) /\
              re_nheld (fst p) + Z.of_nat (length (pending_stream (fst (snd p)))) < 2 ^ 26 /\
              (hl_cap (hs_expected (fst (snd p))) = 0 \/
               exists k, 0 <= k /\ hl_cap (hs_expected (fst (snd p))) = 8 * 2 ^ k) /\
              hl_n (hs_expected (fst (snd p))) + Z.of_nat (length (pending_stream (fst (snd p)))) < 2 ^ 25 /\
              Z.of_nat (length (re_U (fst p))) <= re_used (fst p)) (combine es hs) ->
    gone_cap lv mx NO CAP pre es hs <= NMAX ->
    Forall (fun p => re_eof (fst p) = 0 -> re_hp (fst p) <> 0 -> re_kh (fst p) <> 0) (combine es hs) ->
    List.NoDup (map fst (blocks L A)) ->
    (CAP = 0 -> forall m, ~ In (OUT, m) (blocks L A)) ->
    exists bnd, res_ok_pack3 A bnd /\
      (forall qs, length qs = nretF tr -> roomF pack3_form qs bnd tr) /\
      forall L' A' qs, length qs = nretF tr -> res_ok_pack3 A' (runF pack3_form qs bnd tr) ->
      forall V', (length (rv_nc V') <= NC_MAX)%nat ->
        (forall c, 0 <= c < 49 -> nc_cnt V L A c + gone_dl lv mx NO CAP pre es hs nm 0 (nm OUT) c <= nc_cnt V' L' A' c) ->
        ncs V L A + gone_db lv mx NO CAP pre es hs nm 0 (nm OUT) <= ncs V' L' A' ->
        ncs V' L' A' <= rv_wt V' ->
        rv_wt V' <= rv_wt V + gone_wd (combine es hs) (gone_states lv mx NO CAP pre es hs) +
                    DATA_PER * (cdat (ss_pl E) K' - cdat (ss_pl E) K) ->
        rv_pend V' = gone_pend es hs ->
        (forall c, 0 <= c < 49 -> ek_c V' c = ek_c V c + bcnt c (gone_ek (combine es hs))) ->
        ek_b V' = ek_b V + zsum (fun n => n) (gone_ek (combine es hs)) ->
        Forall (fun n => 0 <= n) (rv_ek V') ->
        List.NoDup (map fst (blocks L' A')) ->
        (forall p n, In (p, n) (user_blocks A) -> In (ptr_addr L p) (rv_nc V) ->
           ~ In (ptr_addr L p) (gone_tch OUT CAP es hs) -> In (ptr_addr L' p) (rv_nc V')) ->
        (gone_cap lv mx NO CAP pre es hs <> 0 ->
           In (ptr_addr L' (resolveF qs (gone_out lv mx NO CAP pre es hs nm 0 (nm OUT)))) (rv_nc V')) ->
        (forall i, (i < length es)%nat -> re_eof (nth i es no_entry) = 0 ->
           let s := nth i (gone_states lv mx NO CAP pre es hs)
                      (drain_init NO CAP (nth i es no_entry) (fst (nth i hs no_hj))) in
           let a := nth i (gone_adrs lv mx NO CAP pre es hs nm 0 (nm OUT)) dadr0 in
           (ds_cap s <> 0 -> In (ptr_addr L' (resolveF qs (da_buf a))) (rv_nc V')) /\
           (ds_ka s <> 0 -> In (ptr_addr L' (resolveF qs (da_hp a))) (rv_nc V')) /\
           (ds_ecap s <> 0 -> In (ptr_addr L' (resolveF qs (da_ev a))) (rv_nc V'))) ->
        RI3_reply E K' V' L' A'.

Theorem p5c_res3_full_holds : p5c_res3_full.
Proof.
  intros E K K' L A G OUT es hs lv mx NO CAP pre. cbv zeta. intros HRI Hk Hlen Hes Hmx Hc HF HN Hkh HB HO0.
  assert (HD : Forall (fun p => re_eof (fst p) = 0 -> drain3 (fst p) (fst (snd p))) (combine es hs)).
  { eapply Forall_impl; [|exact HF]. intros p Hp E0. destruct (Hp E0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
    exact (drain3_holds _ _ H1 H2 H3 H4 H5 H6 H7). }
  assert (HW : Forall (fun p => re_eof (fst p) = 0 -> drain_wt3 (fst p) (fst (snd p))) (combine es hs)).
  { eapply Forall_impl; [|exact HF]. intros p Hp E0. destruct (Hp E0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    exact (drain_wt3_holds _ _ H1 H2 H3 H4 H5 H6 H7 H8). }
  exact (p5c_res3_holds E K K' L A G OUT es hs lv mx NO CAP pre HRI Hk Hlen Hes Hmx Hc HD HW HN Hkh HB HO0).
Qed.
