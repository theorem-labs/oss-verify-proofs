(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.World Require Import Src_zlib_example_flush_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Frame Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel MemFill DSLayout TreeMem BitsLib STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface DeflateState Trees TreeModel Deflate DeflInitLib HarnessKit HarnessFacts HarnessSmallFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 DS6 Callee6 CalleeKits6 Memset6_run TreesApi6 TrInit6 DInit6_M DInit6_1 DInit6_2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import TFlDfl.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import ZlibStmtBase ExSmallIface FlLibStmt FlLibIface.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.
#[local] Abbreviation RSX := Src_zlib_example_flush_fuzzer_repro.M.loaded_segments.

Definition cs0 : cstrm := cs_init (mkZCall [] 0 zstrm0).

Lemma sLM0_ds0 : DInit6_M.sLM0 2%N 3%N 4%N 5%N 6%N cs0 = ds0.
Proof. rewrite ds0_sLM. reflexivity. Qed.

Lemma DSIZES_ds0 : DSIZES ds0.
Proof.
  unfold DSIZES. rewrite <- sLM0_ds0.
  pose proof (DInit6_M.sLM0_lens 2%N 3%N 4%N 5%N 6%N cs0) as (A1 & A2 & A3 & A4). rewrite A1, A2, A3, A4.
  destruct (DeflInitLib.sizes_LM (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) 2%N 3%N 4%N 5%N 6%N cs0 1 15 8 6 0 8)
    as (W & HS & LB & _).
  split; [etransitivity; [exact W | reflexivity]|]. split; [etransitivity; [exact HS | reflexivity]|].
  split; [etransitivity; [exact LB | reflexivity]|]. repeat split; reflexivity.
Qed.

Lemma zeros_at_holds : forall m a n, zeros_at RSX m a n -> holds RSX m a (repeat 0 (Z.to_nat n)).
Proof. intros m a n Z0. unfold holds, zeros_at in *. rewrite repeat_length, map_repeat. exact Z0. Qed.

Lemma zeros_cells : forall m a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 64 -> zeros_at RSX m a n ->
  cells s6_segs m a 1 1 n (fun _ => 0).
Proof.
  intros m a n Ha Hn Han Z0.
  pose proof (holds_cells m a (repeat 0 (Z.to_nat n)) Ha) as H.
  unfold zlength in H. rewrite repeat_length, Z2Nat.id in H by lia.
  specialize (H Han (zeros_at_holds m a n Z0)).
  eapply cells_extf; [exact H|]. intros i Hi. cbn beta. rewrite nth_repeat. reflexivity.
Qed.

Lemma zeros_at_byte : forall m a n z, 0 <= a -> a + n <= 2 ^ 64 -> zeros_at RSX m a n -> mapped m a n ->
  a <= z < a + n -> m (Z_to_bv 64 z) = Some (Z_to_bv 8 0).
Proof.
  intros m a n z Ha Han Z0 M Hz.
  pose proof (zeros_cells m a n Ha ltac:(lia) Han Z0 (z - a) ltac:(lia)) as C. unfold cell in C.
  replace (a + 1 * (z - a)) with z in C by lia. change (zw z) with (Z_to_bv 64 z) in C. cbn [rdn Z_to_le_bytes] in C.
  assert (Hx : m (Z_to_bv 64 z) <> None).
  { apply M. change (Z_to_bv 64 z) with (zw z). rewrite u_zw_small by lia. lia. }
  destruct (m (Z_to_bv 64 z)) as [b|]; [| exfalso; exact (Hx eq_refl)].
  cbn in C. injection C as ->. reflexivity.
Qed.

Theorem L_DI6_ok : forall (regs : bvmap 5 word) (mem : word -> option byte) (q : dptrs) (zc ra v16 v24 v32 : Z) (sv20 sv21 sv22 sv23 : word) (fa ff : Z),
    let h := dp_strm q - 8 in let s := dp_s q in
    getr regs 2 = Z_to_bv 64 (h - 80) -> getr regs 8 = Z_to_bv 64 (dp_strm q) -> getr regs 9 = Z_to_bv 64 s ->
    getr regs 10 = Z_to_bv 64 (dp_pb q) -> getr regs 20 = Z_to_bv 64 (s + 5888) ->
    getr regs 18 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 6 -> getr regs 21 = Z_to_bv 64 1 -> getr regs 22 = Z_to_bv 64 15 -> getr regs 23 = Z_to_bv 64 8 ->
    h mod 16 = 0 -> zc + FL_FRA <= h -> h + 120 <= 2 ^ 47 -> FL_IMG_TOP <= zc ->
    blocks_ok mem zc (dblocks q) -> all_apart (dblocks q) -> img_clear mem ->
    store_ok RSX mem (Z_to_bv 64 (h - FL_FRA)) (Z.to_nat (FL_FRA + 120)) = true ->
    ra_ok ra -> 0 <= v16 < 2 ^ 63 -> 0 <= v24 < 2 ^ 63 -> 0 <= v32 < 2 ^ 63 ->
    zeros_at RSX mem (dp_wnd q) FL_DBLK_N -> zeros_at RSX mem (dp_prv q) FL_DBLK_N -> zeros_at RSX mem (dp_hd q) FL_DBLK_N -> zeros_at RSX mem (dp_pb q) FL_DBLK_N ->
    zeros_at RSX mem (s + 12) 36 -> zeros_at RSX mem (s + 52) 4 -> zeros_at RSX mem (s + 64) 16 -> zeros_at RSX mem (s + 92) 4 ->
    zeros_at RSX mem (s + 104) 8 -> zeros_at RSX mem (s + 128) 4 -> zeros_at RSX mem (s + 148) 5748 -> zeros_at RSX mem (s + 5900) 52 -> zeros_at RSX mem (s + 5960) 8 ->   (* 1.4: the 5968-byte state's tail around high_water (s + 5952) *)
    cell8 RSX mem s (dp_strm q) -> cell4 RSX mem (s + 8) 42 -> cell4 RSX mem (s + 48) 1 -> cell8 RSX mem (s + 56) 0 ->
    cell4 RSX mem (s + 80) 32768 -> cell4 RSX mem (s + 84) 15 -> cell4 RSX mem (s + 88) 32767 ->
    cell8 RSX mem (s + 96) (dp_wnd q) -> cell8 RSX mem (s + 112) (dp_prv q) -> cell8 RSX mem (s + 120) (dp_hd q) ->
    cell4 RSX mem (s + 132) 32768 -> cell4 RSX mem (s + 136) 15 -> cell4 RSX mem (s + 140) 32767 -> cell4 RSX mem (s + 144) 5 ->
    cell4 RSX mem (s + 5896) 16384 -> cell8 RSX mem (s + 5952) 0 -> (* 1.4: high_water at 5952 *)
    cell8 RSX mem (h - 8) ra -> cell8 RSX mem (h - 16) v16 -> cell8 RSX mem (h - 24) v24 -> cell8 RSX mem (h - 32) v32 -> cell8 RSX mem (h - 40) FL_DATALEN ->
    cellw RSX mem (h - 48) sv20 -> cellw RSX mem (h - 56) sv21 -> cellw RSX mem (h - 64) sv22 -> cellw RSX mem (h - 72) sv23 ->
    cellw RSX mem (h - 80) (getr regs 24) ->   (* 1.4: the prologue also saved s8 (x24) at 0(sp) = h - 80; the epilogue reloads it *)
    cell8 RSX mem (h + 56) 0 -> cell8 RSX mem (h + 64) s -> cell8 RSX mem (h + 72) fa -> cell8 RSX mem (h + 80) ff -> cell8 RSX mem (h + 88) 0 ->
    fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps RSX (mkst regs (Z_to_bv 64 FL_A_DI) mem (seg_rom RSX)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSX))
      /\ frame_mod mem mem' ((Z_to_bv 64 (h - FL_FRA), FL_FRA) :: (Z_to_bv 64 (h + 8), 112) :: wz (dblocks q))
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 h
      /\ getr regs' 8 = Z_to_bv 64 v16 /\ getr regs' 9 = Z_to_bv 64 v24 /\ getr regs' 18 = Z_to_bv 64 v32 /\ getr regs' 19 = Z_to_bv 64 FL_DATALEN
      /\ getr regs' 20 = sv20 /\ getr regs' 21 = sv21 /\ getr regs' 22 = sv22 /\ getr regs' 23 = sv23
      /\ rkeep regs regs' [3; 4; 24; 25; 26; 27]%bv
      /\ cell8 RSX mem' (h + 24) 0 /\ cell8 RSX mem' (h + 48) 0 /\ cell8 RSX mem' (h + 56) 0 /\ cell8 RSX mem' (h + 64) s
      /\ cell8 RSX mem' (h + 72) fa /\ cell8 RSX mem' (h + 80) ff /\ cell8 RSX mem' (h + 88) 0 /\ cell4 RSX mem' (h + 96) 2 /\ cell8 RSX mem' (h + 104) 1
      /\ FL_DREP mem' q FL_DS0.
Proof.
  intros regs mem q zc ra v16 v24 v32 sv20 sv21 sv22 sv23 fa ff. cbv zeta.
  intros P2 P8 P9 P10 P20 P18 P19 P21 P22 P23 H16 ZCL H47 TOP BOK AP IC SOf RA V16 V24 V32
         Zw Zp Zh Zb Zs12 Zs52 Zs64 Zs92 Zs104 Zs128 Zs148 Zs5900 Zs5960
         Cs0 Cs8 Cs48 Cs56 Cs80 Cs84 Cs88 Cs96 Cs112 Cs120 Cs132 Cs136 Cs140 Cs144 Cs5896 Cs5944
         Cra C16 C24 C32 C40 C48 C56 C64 C72 C8s Z48 Z56 Z64 Z72 Z80 FA FF.
  set (h := dp_strm q - 8) in *. set (s := dp_s q) in *.
  set (wnd := dp_wnd q) in *. set (prv := dp_prv q) in *. set (hd := dp_hd q) in *. set (pb := dp_pb q) in *.
  unfold FL_FRA, FL_IMG_TOP, FL_DBLK_N in *.
  unfold blocks_ok, dblocks in BOK. fold s wnd prv hd pb in BOK.
  apply Forall_cons_iff in BOK as [BS BOK]. apply Forall_cons_iff in BOK as [BW BOK]. apply Forall_cons_iff in BOK as [BP BOK].
  apply Forall_cons_iff in BOK as [BH BOK]. apply Forall_cons_iff in BOK as [BB _]. cbn [fst snd] in BS, BW, BP, BH, BB.
  unfold blk_okz, FL_DSTATE_N, FL_DBLK_N, FL_IMG_TOP in BS, BW, BP, BH, BB.
  destruct BS as (AS16 & S1 & SZ & SIM & SOS). destruct BW as (AW16 & W1 & WZ & WIM & SOW). destruct BP as (AP16 & P1 & PZ & PIM & SOP).
  destruct BH as (AH16 & H1 & HZ & HIM & SOH). destruct BB as (AB16 & B1 & BZ & BIM & SOB).
  unfold dblocks in AP. fold s wnd prv hd pb in AP. cbn [all_apart apart_from_all] in AP. unfold ExSmallIface.apart, FL_DSTATE_N, FL_DBLK_N in AP.
  destruct AP as ((DSW & DSQ & DSH & DSB & _) & (DWP & DWH & DWB & _) & (DPH & DPB & _) & (DHB & _) & _).
  assert (MK : mapped mem (h - 1024) (1024 + 120)).
  { apply store_ok_offimg_mapped; [clear - ZCL TOP | clear | clear - H47 | clear - ZCL TOP; unfold FL_RO_LO, FL_IMG_TOP | exact SOf]; lia. }
  assert (MS : mapped mem s 5968).
  { apply store_ok_offimg_mapped; [clear - S1 | clear | clear - SZ ZCL H47 | unfold FL_RO_LO, FL_IMG_TOP; exact SIM | exact SOS]; lia. }
  assert (MW : mapped mem wnd 65536).
  { apply store_ok_offimg_mapped; [clear - W1 | clear | clear - WZ ZCL H47 | unfold FL_RO_LO, FL_IMG_TOP; exact WIM | exact SOW]; lia. }
  assert (MP : mapped mem prv 65536).
  { apply store_ok_offimg_mapped; [clear - P1 | clear | clear - PZ ZCL H47 | unfold FL_RO_LO, FL_IMG_TOP; exact PIM | exact SOP]; lia. }
  assert (MH : mapped mem hd 65536).
  { apply store_ok_offimg_mapped; [clear - H1 | clear | clear - HZ ZCL H47 | unfold FL_RO_LO, FL_IMG_TOP; exact HIM | exact SOH]; lia. }
  assert (MB : mapped mem pb 65536).
  { apply store_ok_offimg_mapped; [clear - B1 | clear | clear - BZ ZCL H47 | unfold FL_RO_LO, FL_IMG_TOP; exact BIM | exact SOB]; lia. }
  clear SOf SOS SOW SOP SOH SOB.
  assert (HROM : forall x : word, 0x10000 <= bv_unsigned x < 0x293d8 -> mem x = None).
  { clear - IC. unfold img_clear, FL_RO_LO, FL_RO_HI in IC. intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply IC. lia. }
  pose proof (zeros_cells mem wnd 65536 ltac:(clear - W1; lia) ltac:(clear; lia) ltac:(clear - WZ ZCL H47; lia) Zw) as ZW.
  pose proof (zeros_cells mem prv 65536 ltac:(clear - P1; lia) ltac:(clear; lia) ltac:(clear - PZ ZCL H47; lia) Zp) as ZPV.
  pose proof (zeros_cells mem hd 65536 ltac:(clear - H1; lia) ltac:(clear; lia) ltac:(clear - HZ ZCL H47; lia) Zh) as ZHD.
  pose proof (zeros_cells mem pb 65536 ltac:(clear - B1; lia) ltac:(clear; lia) ltac:(clear - BZ ZCL H47; lia) Zb) as ZPB.
  assert (Eh8 : h + 8 = dp_strm q) by (subst h; clear; lia).
  assert (HI0 : SIMG s6_segs mem s 5968 (I0 h wnd prv hd)).
  { apply (SIMG_intro s6_segs mem s 5968); [clear - S1; lia | clear - SZ ZCL H47; lia | reflexivity | |].
    - intros z Hz Hc.
      unfold covered, I0 in Hc. cbn in Hc. change (Z.of_nat 8%nat) with 8 in Hc. change (Z.of_nat 4%nat) with 4 in Hc.
      assert (R : s + 12 <= z < s + 12 + 36 \/ s + 52 <= z < s + 52 + 4 \/ s + 64 <= z < s + 64 + 16 \/ s + 92 <= z < s + 92 + 4
                  \/ s + 104 <= z < s + 104 + 8 \/ s + 128 <= z < s + 128 + 4 \/ s + 148 <= z < s + 148 + 5748 \/ s + 5900 <= z < s + 5900 + 52
                  \/ s + 5960 <= z < s + 5960 + 8)
        by (clear - Hz Hc; lia).
      clear Hc.
      destruct R as [R|[R|[R|[R|[R|[R|[R|[R|R]]]]]]]];
        [ exact (zeros_at_byte mem (s + 12) 36 z ltac:(clear - S1; lia) ltac:(clear - SZ ZCL H47; lia) Zs12 ltac:(eapply mapped_sub; [exact MS | clear; lia | clear; lia]) R)
        | exact (zeros_at_byte mem (s + 52) 4 z ltac:(clear - S1; lia) ltac:(clear - SZ ZCL H47; lia) Zs52 ltac:(eapply mapped_sub; [exact MS | clear; lia | clear; lia]) R)
        | exact (zeros_at_byte mem (s + 64) 16 z ltac:(clear - S1; lia) ltac:(clear - SZ ZCL H47; lia) Zs64 ltac:(eapply mapped_sub; [exact MS | clear; lia | clear; lia]) R)
        | exact (zeros_at_byte mem (s + 92) 4 z ltac:(clear - S1; lia) ltac:(clear - SZ ZCL H47; lia) Zs92 ltac:(eapply mapped_sub; [exact MS | clear; lia | clear; lia]) R)
        | exact (zeros_at_byte mem (s + 104) 8 z ltac:(clear - S1; lia) ltac:(clear - SZ ZCL H47; lia) Zs104 ltac:(eapply mapped_sub; [exact MS | clear; lia | clear; lia]) R)
        | exact (zeros_at_byte mem (s + 128) 4 z ltac:(clear - S1; lia) ltac:(clear - SZ ZCL H47; lia) Zs128 ltac:(eapply mapped_sub; [exact MS | clear; lia | clear; lia]) R)
        | exact (zeros_at_byte mem (s + 148) 5748 z ltac:(clear - S1; lia) ltac:(clear - SZ ZCL H47; lia) Zs148 ltac:(eapply mapped_sub; [exact MS | clear; lia | clear; lia]) R)
        | exact (zeros_at_byte mem (s + 5900) 52 z ltac:(clear - S1; lia) ltac:(clear - SZ ZCL H47; lia) Zs5900 ltac:(eapply mapped_sub; [exact MS | clear; lia | clear; lia]) R)
        | exact (zeros_at_byte mem (s + 5960) 8 z ltac:(clear - S1; lia) ltac:(clear - SZ ZCL H47; lia) Zs5960 ltac:(eapply mapped_sub; [exact MS | clear; lia | clear; lia]) R) ].
    - unfold I0. repeat constructor.
      + rewrite Z.add_0_r, Eh8. exact Cs0.
      + exact Cs8. + exact Cs48. + exact Cs56. + exact Cs80. + exact Cs84. + exact Cs88.
      + exact Cs96. + exact Cs112. + exact Cs120. + exact Cs132. + exact Cs136. + exact Cs140. + exact Cs144.
      + exact Cs5896. + exact Cs5944. }
  rewrite FA in Z64. rewrite FF in Z72.
  destruct (DInit6_2.ds_init_run mem h s wnd prv hd pb v16 v24 v32 sv20 sv21 sv22 sv23 (getr regs 24) ra zc
              ltac:(clear - ZCL H47 TOP; lia) ltac:(clear - S1 SZ; lia) ltac:(clear - W1 WZ; lia) ltac:(clear - P1 PZ; lia)
              ltac:(clear - H1 HZ; lia) ltac:(clear - B1 BZ; lia) SIM V16 V24 V32 RA
              DSW DSQ DSH DSB DWP DWH DWB DPH DPB DHB MK MS MH MB HROM
              Cra C16 C24 C32 C40 C48 C56 C64 C72 C8s Z56 Z64 Z72 Z80 HI0 ZW ZPV ZHD ZPB memset_run6_ok
              2%N 3%N 4%N 5%N 6%N cs0 regs P2 ltac:(rewrite Eh8; exact P8) P9 P10 P20 P18 P19 P21 P22 P23 eq_refl)
    as (R & mF & RUN & A10 & A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & Hfr & HIP).
  pose proof HIP as (Hsc & Har & Htl & HwA & HpA & HhA & HbA & (X24 & X48 & X56 & X64 & X72 & X80 & X88 & X96 & X104) & HagI & HgrI & HromI).
  exists R, mF.
  split.
  { replace (Z_to_bv 64 FL_A_DI) with (0x16468%bv : word) by (apply bv_eq; reflexivity). exact RUN. }
  split.
  {
    split; [| exact HgrI].
    intros a Hout. apply HagI. intros Hin.
    unfold DInit6_2.GI in Hin. cbn [in_franges] in Hin.
    unfold dblocks, FL_DSTATE_N, FL_DBLK_N in Hout. fold s wnd prv hd pb in Hout. cbn [outside wz map fst snd] in Hout. unfold in_rng in Hout.
    change (Z_to_bv 64) with zw in Hout.
    rewrite !u_zw_small in Hout by (clear - ZCL TOP H47 S1 SZ W1 WZ P1 PZ H1 HZ B1 BZ; lia).
    clear - Hin Hout ZCL TOP H47 SZ BZ HZ. lia. }
  split; [exact A10|]. split; [exact A2|]. split; [exact A8|]. split; [exact A9|]. split; [exact A18|]. split; [exact A19|].
  split; [exact A20|]. split; [exact A21|]. split; [exact A22|]. split; [exact A23|].
  split.
  { intros r Hr. apply Hfr. cbn in Hr.
    repeat (destruct Hr as [Hr|Hr]; [subst r; reflexivity|]). destruct Hr. }
  split; [exact X24|]. split; [exact X48|]. split; [exact X56|]. split; [exact X64|].
  split; [rewrite FA; exact X72|]. split; [rewrite FF; exact X80|]. split; [exact X88|]. split; [exact X96|]. split; [exact X104|].
  unfold FL_DREP, FL_DS0. rewrite <- sLM0_ds0.
  assert (E6 : DInit6_1.p6 h wnd prv hd pb = fl_dsp q) by (unfold DInit6_1.p6, fl_dsp; rewrite Eh8; reflexivity).
  rewrite <- E6. fold s.
  split; [exact Hsc|]. split; [exact Har|]. split; [exact Htl|]. split; [exact HwA|]. split; [exact HpA|]. split; [exact HhA|]. split; [exact HbA|].
  split; [rewrite sLM0_ds0; exact DSIZES_ds0|].
  unfold DRANGES, FL_DSTATE_N, FL_DBLK_N. fold s wnd prv hd pb. clear - ZCL TOP H47 S1 SZ W1 WZ P1 PZ H1 HZ B1 BZ. lia.
Qed.
End FXG.
