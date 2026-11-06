From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes tx_put_c TxCalls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import TvSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import TxRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import PjWriteHyp round_trip_text_c RttDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import
RttGlue RttModel RttBase RttA_Lib RttA_Call.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require RttRunsA.
Import ListNotations.
Local Open Scope Z_scope.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis TXP : forall fx' : YK11.FPState, @tx_put_contract fx' rc B API F.
Hypothesis NEXT : stg_cmp_st B API F.

(* 0x153a0: tx_value returned; beqz pretty (RttRunsA.rtt_seg3).  Compact: on to stg_cmp at 0x153b8.  Pretty:
   tx_put(&t, "\n", 1) (RttA_Call.ra_put), the "\n" byte at .rodata 0x10392 (RttModel.img_nl), returning to 0x153b8. *)
Theorem stg_nl_holds : stg_nl_st B API F.
Proof.
  unfold stg_nl_st. cbv zeta.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 bb0 doc pretty copy t D ro oo fx' L A regs mem md Lam peak q want cap
    ENT FL INV RG RT RH HCAP.
  pose proof ENT as (REN & _ & _ & _ & _ & R10 & R11 & R12 & PR & _ & _ & _ & DOCS & _ & DEP & WL & _ & ROOM).
  pose proof REN as (_ & _ & ERRB & _ & _ & PRE0 & _).
  pose proof PRE0 as (_ & _ & _ & _ & SP16 & SPC & SP63 & _).
  pose proof INV as (RS & _ & _ & RD & _).
  pose proof RS as (MRc & _).
  destruct (kb_md B API L A mem md MRc) as (Hh & Hz).
  pose proof RG as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G3 & G4 & G22).
  pose proof alloc_ceiling_val as HCV.
  eapply (@ra_run fx rc B API F HSEG FA fx' regs _ mem md _ _ Hh Hz).
  { unfold rmk. rewrite G2.
    exact (RttRunsA.rtt_seg3 (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31) (@fp_regs fx') (@fp_csr fx') mem (spZ regs0 - 112)). }
  { intros ms' [(_ & E) | (_ & E)]; eexists _, _, _; exact E. }
  intros R pc' mem1 regs1 HQ HGr.
  destruct HQ as [(HS3 & E) | (HS3 & E)]; ra_inj E R pc' mem1.
  - (* compact (s3 = pretty = 0): rendered() is done *)
    assert (HP0 : pretty = 0).
    { destruct PR as [P0 | P1]; [exact P0|]. exfalso. subst pretty. rewrite G19 in HS3.
      apply (f_equal bv_unsigned) in HS3. rewrite !ra_uns in HS3 by lia. lia. }
    subst pretty.
    assert (EP : negb (0 =? 0) = false) by reflexivity.
    assert (WD : wdoc t false = concat (wvpieces t false 0)) by (rewrite wdoc_split; apply app_nil_r).
    assert (EB : tx_fold F (rtt_bw F bb0 cnt0 t false) 0 0 ([0] ++ tv_calls t false 0) = rtt_bt F bb0 cnt0 t false).
    { unfold rtt_bt, rtt_ns. change (if false then [1] else []) with (@nil Z). rewrite app_nil_r. reflexivity. }
    assert (EC : tx_capf 0 0 ([0] ++ tv_calls t false 0) = tx_capf 0 0 (rtt_ns t false)).
    { unfold rtt_ns. change (if false then [1] else []) with (@nil Z). rewrite app_nil_r. reflexivity. }
    change (negb (0 =? 0)) with false in INV, HCAP. rewrite EB in INV. rewrite EC in HCAP.
    apply (NEXT L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 bb0 doc 0 copy t D ro oo fx' L A regs1 mem md Lam peak q want
      cap (Z_to_bv 64 0) ENT FL INV).
    + split; [rewrite HGr; reflexivity|]. split; [rewrite HGr; exact G8|]. split; [rewrite HGr; exact G9|].
      split; [rewrite HGr; exact G18|]. split; [rewrite HGr; exact G19|]. split; [rewrite HGr; exact G20|].
      split; [rewrite HGr; exact G21|]. split; [rewrite HGr; exact G3|]. split; [rewrite HGr; exact G4|].
      intros r Hr. rewrite HGr, <- (G22 r Hr).
      assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr' as [->|[->|[->|[->|[->| ->]]]]]; reflexivity.
    + exact RT.
    + rewrite EP in RH |- *. unfold wlen. rewrite WD. exact RH.
    + exact HCAP.
  - (* pretty (s3 = pretty = 1): tx_put(&t, "\n", 1) *)
    assert (HP1 : pretty = 1).
    { destruct PR as [P0 | P1]; [|exact P1]. exfalso. subst pretty. apply HS3. rewrite G19. reflexivity. }
    subst pretty.
    assert (EP : negb (1 =? 0) = true) by reflexivity.
    rewrite EP in RT, RH, WL, ROOM, INV, HCAP.
    set (txt := map (Z_to_bv 8) (concat (wvpieces t true 0))) in *.
    set (len := Z.of_nat (length (concat (wvpieces t true 0)))) in *.
    assert (WDT : wdoc t true = concat (wvpieces t true 0) ++ [10]) by (rewrite wdoc_split; reflexivity).
    assert (EWL : wlen t true = len + 1) by (unfold wlen, len; rewrite WDT, length_app; cbn [length]; lia).
    assert (K1 : getr regs1 1 = Z_to_bv 64 0x153b8) by (rewrite HGr; reflexivity).
    assert (K2 : getr regs1 2 = Z_to_bv 64 (spZ regs0 - 112)) by (rewrite HGr; reflexivity).
    assert (K4 : getr regs1 4 = getr regs0 4) by (rewrite HGr; exact G4).
    assert (K10 : getr regs1 10 = Z_to_bv 64 (spZ regs0 - 112)) by (rewrite HGr; reflexivity).
    assert (K11 : getr regs1 11 = Z_to_bv 64 0x10392) by (rewrite HGr; reflexivity).
    assert (K12 : getr regs1 12 = Z_to_bv 64 1) by (rewrite HGr; reflexivity).
    assert (RR1 : rtt_regs regs0 regs1 copy (Z_to_bv 64 q) (Z_to_bv 64 1) (getr regs0 20) (getr regs0 21)).
    { split; [exact K2|]. split; [rewrite HGr; exact G8|]. split; [rewrite HGr; exact G9|].
      split; [rewrite HGr; exact G18|]. split; [rewrite HGr; exact G19|]. split; [rewrite HGr; exact G20|].
      split; [rewrite HGr; exact G21|]. split; [rewrite HGr; exact G3|]. split; [exact K4|].
      intros r Hr. rewrite HGr, <- (G22 r Hr).
      assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr' as [->|[->|[->|[->|[->| ->]]]]]; reflexivity. }
    assert (NLI : in_img B 0x10392).
    { apply (rg_img_range B API HSEG (rtt_AX B API HSEG FA) (rtt_FG B API HSEG FA) 0x10392 (0x10392 + 1));
        [vm_compute; reflexivity | lia]. }
    assert (HZS : zsum ([0] ++ tv_calls t true 0) = len).
    { unfold len. rewrite zsum_app. cbn [zsum]. unfold tv_calls. rewrite zsum_plen, tvp_concat. lia. }
    assert (ROOMN : cap < len + 1 + 1 ->
      rf_room F (tx_fold F (rtt_bw F bb0 cnt0 t true) 0 0 ([0] ++ tv_calls t true 0)) (2 * (len + 1 + 1))).
    { destruct ROOM as (_ & RTX & _). unfold rtt_ns in RTX. change (if true then [1] else []) with [1] in RTX.
      rewrite app_assoc in RTX. apply tx_rooms_app in RTX. destruct RTX as [_ RTX]. cbn [tx_rooms] in RTX.
      rewrite Z.add_0_l, HZS, <- HCAP in RTX. exact (proj1 RTX). }
    assert (EBT : rtt_bt F bb0 cnt0 t true =
      tx_fold F (tx_fold F (rtt_bw F bb0 cnt0 t true) 0 0 ([0] ++ tv_calls t true 0)) len cap [1]).
    { unfold rtt_bt, rtt_ns. change (if true then [1] else []) with [1].
      rewrite app_assoc, tx_fold_app, Z.add_0_l, HZS, <- HCAP. reflexivity. }
    eapply (@ra_put fx rc B API F HSEG FA TXP L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 bb0 doc 1 copy t D fx' L A mem md
      [(q, wcap t true)] Lam peak (cnt0 + wcalls t true) (tx_fold F (rtt_bw F bb0 cnt0 t true) 0 0 ([0] ++ tv_calls t true 0))
      q want len cap txt regs1 0x10392 1 [Z_to_bv 8 10] _ ENT INV RT RH K2 K4).
    + rewrite K1. ra_ret.
    + exact K10.
    + exact K11.
    + exact K12.
    + lia.
    + lia.
    + lia.
    + intros i Hi. assert (i = 0) as -> by lia. rewrite Z.add_0_r. split; [exact NLI|].
      destruct (img_nl (ms_segs B) mem HSEG (proj1 RD)) as [E _]. exact E.
    + intros i Hi. cbn [length Z.of_nat] in Hi. assert (i = 0) as -> by lia.
      destruct (img_nl (ms_segs B) mem HSEG (proj1 RD)) as [_ E]. exact E.
    + reflexivity.
    + rewrite EWL in WL. lia.
    + exact ROOMN.
    + intros L' A' regs' mem' md' want' cap' RP HCJ INV' RT' HARN'.
      rewrite K1.
      assert (INV2 : @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx' L' A' mem' md'
        [(q, wcap t true)] Lam peak (cnt0 + wcalls t true) (rtt_bt F bb0 cnt0 t true)) by (rewrite EBT; exact INV').
      apply (NEXT L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 bb0 doc 1 copy t D ro oo fx' L' A' regs' mem' md' Lam peak
        q want' cap' (Z_to_bv 64 1) ENT FL INV2).
      * exact (@ra_regs_pres fx rc B API F HSEG FA regs0 regs1 regs' copy _ _ _ _ RR1 RP).
      * exact RT'.
      * change (negb (1 =? 0)) with true. rewrite EWL.
        replace (map (Z_to_bv 8) (wdoc t true)) with (txt ++ [Z_to_bv 8 10])
          by (unfold txt; rewrite WDT, map_app; reflexivity).
        exact HARN'.
      * rewrite HCJ. change (negb (1 =? 0)) with true. unfold rtt_ns. change (if true then [1] else []) with [1].
        rewrite app_assoc, tx_capf_app, Z.add_0_l, HZS, <- HCAP. reflexivity.
Qed.

End S.
