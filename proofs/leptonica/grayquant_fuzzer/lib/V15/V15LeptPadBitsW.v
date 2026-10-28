(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptStderr V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL3a.
Import V15CL3a.V15PadBits.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15_code_15000_16000 V15_code_17000_18000 V15_code_18000_19000.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section PadBitsW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma pb32_run : forall regs m (s pix : Z) (v : pixv) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> PIXat m pix v -> p_d v = 32%Z -> (4096 <= pix)%Z -> (pix + 64 <= s - 48 \/ s <= pix)%Z ->
    (s mod 16 = 0)%Z -> (pix mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs' m',
      msteps SEGS (mkst regs (0x181ac : word) m rom) (mkst regs' ret m' rom)
      /\ (forall x : word, ~ (s - 48 <= u x < s)%Z -> m' x = m x) /\ mem_grows m m'
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs'.
  Proof.
    intros regs m s pix v ret Hs Hs64 Hret PX Hd Hpix DJ Hs16 ALp SOK H2 H1 H10 H11.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh.
    assert (A36 : ((s - 36) mod 4 = 0)%Z) by (replace (s - 36)%Z with (s + (-36))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]).
    assert (A40 : ((s - 40) mod 4 = 0)%Z) by (replace (s - 40)%Z with (s + (-40))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]).
    assert (A44 : ((s - 44) mod 4 = 0)%Z) by (replace (s - 44)%Z with (s + (-44))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity]).
    Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
    eexists. eexists. split; [|split; [|split]].
    - zv F_180a8 D_180a8 (Z_to_bv 64 (s - 48)).
      stepST F_180ac D_180ac (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_180b0 D_180b0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_180b4 D_180b4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_180b8 D_180b8 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepb_ft F_180bc D_180bc ltac:(condZ).
      zv F_180c0 D_180c0 (Z_to_bv 64 0).
      zv F_180c4 D_180c4 (Z_to_bv 64 pix).
      zv F_180c8 D_180c8 (Z_to_bv 64 (s - 36)).
      zv F_180cc D_180cc (Z_to_bv 64 (s - 40)).
      zv F_180d0 D_180d0 (Z_to_bv 64 (s - 44)).
      sn F_180d4 D_180d4.
      (* [comment removed for export] *)
      zand F_171dc D_171dc andi_3 A36.
      stepb_ft F_171e0 D_171e0 ltac:(condZ). stepb_ft F_171e4 D_171e4 ltac:(condZ).
      stepST F_171e8 D_171e8 (Z_to_bv 64 (s - 36)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_171ec D_171ec andi_3 A40.
      stepb_ft F_171f0 D_171f0 ltac:(condZ). stepb_ft F_171f4 D_171f4 ltac:(condZ).
      stepST F_171f8 D_171f8 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_171fc D_171fc andi_3 A44.
      stepb_ft F_17200 D_17200 ltac:(condZ). stepb_ft F_17204 D_17204 ltac:(condZ).
      stepST F_17208 D_17208 (Z_to_bv 64 (s - 44)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_1720c D_1720c ltac:(condZ).
      zand F_17210 D_17210 andi_7 ALp.
      stepb_ft F_17214 D_17214 ltac:(condZ).
      sn F_17218 D_17218. stepb_ft F_1721c D_1721c ltac:(pin; vm_compute; reflexivity).
      stepLD F_17220 D_17220 (Z_to_le_bytes 4 (p_w v)) (Z_to_bv 64 (p_w v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_w SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w v)) by lia.
      stepST F_17224 D_17224 (Z_to_bv 64 (s - 36)) (Z_to_bv 64 (p_w v)) ltac:(sok_in SOK).
      stepb_ft F_17228 D_17228 ltac:(condZ).
      sn F_1722c D_1722c. stepb_ft F_17230 D_17230 ltac:(pin; vm_compute; reflexivity).
      stepLD F_17234 D_17234 (Z_to_le_bytes 4 (p_h v)) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h v)) by lia.
      stepST F_17238 D_17238 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 (p_h v)) ltac:(sok_in SOK).
      stepb_ft F_1723c D_1723c ltac:(condZ).
      sn F_17240 D_17240. stepb_ft F_17244 D_17244 ltac:(pin; vm_compute; reflexivity).
      stepLD F_17248 D_17248 (Z_to_le_bytes 4 (p_d v)) (Z_to_bv 64 (p_d v)) ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_d SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      rewrite Hd. change (v_lw (Z_to_bv 64 32)) with (Z_to_bv 64 32).
      stepST F_1724c D_1724c (Z_to_bv 64 (s - 44)) (Z_to_bv 64 32) ltac:(sok_in SOK).
      sn F_17250 D_17250.
      stepret F_17254 D_17254 (0x181dc : word) ltac:(bveq).
      stepLD F_180d8 D_180d8 (word_to_le_bytes 4 (Z_to_bv 64 32)) (Z_to_bv 64 32)
        ltac:(addr_norm; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 32))); zlen; unorm; lia)
        ltac:(apply bytes_le_to_Z_4; unorm; lia).
      change (v_lw (Z_to_bv 64 32)) with (Z_to_bv 64 32).
      sn F_180dc D_180dc.
      stepb_tk F_180e0 D_180e0 ltac:(condZ).
      sn F_18278 D_18278.
      stepLD8 F_1827c D_1827c ret.
      stepLD8 F_18280 D_18280 (getr regs 8).
      stepLD8 F_18284 D_18284 (getr regs 9).
      stepLD8 F_18288 D_18288 (getr regs 18).
      zv F_1828c D_1828c (Z_to_bv 64 s).
      stepret F_18290 D_18290 ret ltac:(bveq).
      apply mst_refl.
    - intros x Hx. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
    - repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

Lemma str_pixSetPadBits : str16 0x10bec 13. Proof. str16_tac. Qed.
Lemma str_msg_24bpp : str16 0x109e6 26. Proof. str16_tac. Qed.

(* [comment removed for export] *)
Theorem padbits_W : forall C Ar A m md regs (s pix : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 0 ->
  PIXat m pix v -> dval (p_d v) -> (1 <= p_w v <= 20000)%Z -> (1 <= p_h v <= 20000)%Z -> p_wpl v = wpl_of (p_w v) (p_d v) ->
  live A (Z_to_bv 64 pix) = Some 64%Z ->
  live A (Z_to_bv 64 (p_data v)) = Some (4 * (p_wpl v * p_h v))%Z -> live Ar (Z_to_bv 64 (p_data v)) = None ->
  live (c_A0 C) (Z_to_bv 64 (p_data v)) = None -> Z_to_bv 64 pix <> Z_to_bv 64 (p_data v) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
      PIXat m' pix v ->
      (forall a : word, ~ (s - (48 + LSF) <= u a < s)%Z -> ~ (p_data v <= u a < p_data v + 4 * (p_wpl v * p_h v))%Z -> m' a = m a) ->
      (getr regs' 10 = Z_to_bv 64 0 \/ getr regs' 10 = Z_to_bv 64 1) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x181ac : word) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s pix v ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 PX DV Hw Hh Hwpl Lp Ld Ld0 Ld00 NEpd HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rdat.
  pose proof (dval_range _ DV) as Hd32. pose proof (wpl_of_range (p_w v) (p_d v) ltac:(lia) DV) as Hwr. rewrite <- Hwpl in Hwr.
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp16 & _). rewrite u_Z2bv in ALp16 by lia.
  assert (ALp8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALp16 | reflexivity]).
  destruct (Z.eq_dec (p_d v) 32) as [D32|ND32].
  { (* [comment removed for export] *)
    destruct (pb32_run al_rom regs m s pix v ret ltac:(lia) ltac:(lia) Hret PX D32 Gp ltac:(lia) Hs16 ALp8 SOK H2 H1 H10 H11)
      as (r1 & m1 & RUN1 & OUT1 & GR1 & Q2 & Q1 & Q10 & Q8 & Q9 & Q18 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    apply HK.
    - apply (W_local C A m md m1 s CK HW Hhi); [|exact GR1]. intros a NE. left. unfold scratch.
      destruct (Z_lt_ge_dec (u a) (s - 48)); [exfalso; apply NE; apply OUT1; lia|]. destruct (Z_lt_ge_dec (u a) s); [lia|]. exfalso; apply NE; apply OUT1; lia.
    - apply cs_kept_intro; csr; try reflexivity.
    - apply (POSTM_local C Ar A m md m1 s CK HW SUB). intros a NE. left. unfold scratch.
      destruct (Z_lt_ge_dec (u a) (s - 48)); [exfalso; apply NE; apply OUT1; lia|]. destruct (Z_lt_ge_dec (u a) s); [lia|]. exfalso; apply NE; apply OUT1; lia.
    - apply (PIXat_frame m); [exact PX|]. intros x Hx. apply OUT1. lia.
    - intros a Ha Hb. apply OUT1. lia.
    - left. exact Q10. }
  destruct (blk_range C A m md (Z_to_bv 64 (p_data v)) _ CK HW Ld ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lp Ld NEpd) as DJpd. rewrite !u_Z2bv in DJpd by lia.
  pose proof (round16_ge (4 * (p_wpl v * p_h v)) ltac:(lia)) as R16d. unfold round16 in DJpd at 1. change ((64 + 15) / 16)%Z with 4%Z in DJpd.
  assert (SOKd : store_ok SEGS m (Z_to_bv 64 (p_data v)) (Z.to_nat (4 * (p_wpl v * p_h v))) = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
    destruct (blk_byte C A m md (Z_to_bv 64 (p_data v)) _ x CK HW Ld ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D E). }
  destruct (Z.eq_dec (p_d v) 24) as [D24|ND24].
  { (* [comment removed for export] *)
    destruct (canary_any m) as (cv & Hcv & Ccan).
    pose proof (W_sev_got C A m md HW) as Rsg. pose proof (W_sev C A m md HW) as Rsv.
    pose proof (W_hdl16 C A m md HW) as Rh. pose proof (W_can_got C A m md HW) as Rcg.
    assert (PRE : SSP.spec_pre SEGS (SSP.spec_padbits24 0x181ac (48 + 3376) LU16)
                    [pix; 0; p_w v; p_h v; 24; 0x154e8; 0x65828; cv; 0x35268; 3]%Z regs m).
    { unfold SSP.spec_padbits24. SSP.spec_unfold.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ length SSP.ls_handler_cell SSP.ls_devnull SSP.ls_canary_got SSP.ls_canary SSP.ls_img_lo
           SSP.ls_img_hi SSP.ls_sp_lo SSP.ls_sp_hi SSP.ls_frame SSP.ls_sev_got SSP.ls_sev LU16].
      rewrite H1, H2, H10, H11. rewrite !u_Z2bv by lia. pose proof (wf_w _ WF). pose proof (wf_h _ WF).
      split; [|split; [|split; [|exact Hret]]].
      - split; [split; [reflexivity | lia]|]. split; [lia|]. split; [split; [lia | ]|].
        { pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALGN & _). rewrite u_Z2bv in ALGN by lia.
          rewrite <- (Z.add_0_r pix). apply mod16_plus_mod8; [exact ALGN | reflexivity]. }
        split; [split; [reflexivity | lia]|]. split; [reflexivity|].
        split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | rewrite Z.add_0_r; exact (PIX_rd_w SEGS _ _ _ PX)]]]|].
        split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact (PIX_rd_h SEGS _ _ _ PX)]]]|].
        split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | rewrite <- D24; exact (PIX_rd_d SEGS _ _ _ PX)]]]|].
        split; [reflexivity|].
        split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact Rh]]]|]. split; [reflexivity|].
        split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact Rcg]]]|]. split; [reflexivity|].
        split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact Ccan]]]|].
        split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact Rsg]]]|]. split; [reflexivity|].
        split; [split; [cbn; lia | split; [unfold SSP.flatZ; lia | split; [lia | exact Rsv]]]|].
        split; [intros i Hi; exact (W_img16 C A m md i HW Hi)|].
        split; [split; [lia | exact Hs16]|]. split; [lia | exact I].
      - split; [lia|]. split; [unfold SSP.flatZ; lia|]. split; [|exact I].
        apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia].
      - cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. repeat split; try lia. all: exact I. }
    pose proof (padbits24_contract LU16 ltac:(unfold padbits24_L_ok; cbn; repeat split; try lia; repeat (first [left; reflexivity | right])) lept_stderr_s1) as CT.
    unfold SSP.sum_contract in CT.
    destruct (CT [pix; 0; p_w v; p_h v; 24; 0x154e8; 0x65828; cv; 0x35268; 3]%Z regs m al_rom eq_refl PRE) as (outs & R' & M' & _ & RUN & POST).
    unfold SSP.spec_padbits24 in POST. SSP.spec_unfold_in POST. cbn [SSP.ls_frame LU16] in POST.
    destruct POST as (KEPT & A10 & FRMx & GR & _).
    cbn [SSP.su_entry SSP.exit_target SSP.su_exit SSP.spec_padbits24] in RUN. rewrite H1 in RUN. rewrite H2, u_Z2bv in FRMx by lia.
    assert (OUT : forall a : word, ~ (s - 3424 <= u a < s)%Z -> M' a = m a) by (intros a Ha; apply FRMx; split; [lia | exact I]).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | |].
    { lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ => replace pc with (Z_to_bv 64 0x181ac) by (apply bv_eq; reflexivity) end. exact RUN. }
    apply HK.
    - apply (W_local C A m md M' s CK HW Hhi); [|exact GR]. intros a NE. left. unfold scratch.
      destruct (Z_lt_ge_dec (u a) (s - 3424)); [exfalso; apply NE; apply OUT; lia|]. destruct (Z_lt_ge_dec (u a) s); [lia|]. exfalso; apply NE; apply OUT; lia.
    - exact (cs_kept_of_list regs R' KEPT).
    - apply (POSTM_local C Ar A m md M' s CK HW SUB). intros a NE. left. unfold scratch.
      destruct (Z_lt_ge_dec (u a) (s - 3424)); [exfalso; apply NE; apply OUT; lia|]. destruct (Z_lt_ge_dec (u a) s); [lia|]. exfalso; apply NE; apply OUT; lia.
    - apply (PIXat_frame m); [exact PX|]. intros x Hx. apply OUT. lia.
    - intros a Ha Hb. apply OUT. lia.
    - right. exact A10. }
  (* [comment removed for export] *)
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd16 & _). rewrite u_Z2bv in ALd16 by lia.
  assert (ALd4 : is_aligned (p_data v) 4) by (unfold is_aligned; rewrite <- (Z.add_0_r (p_data v)); apply mod16_plus_mod4; [exact ALd16 | reflexivity]).
  destruct (padbits_run m al_rom pix (p_w v) (p_h v) (p_d v) (p_wpl v) (p_data v) s ret (getr regs 8) (getr regs 9) (getr regs 18)
              ltac:(lia) ltac:(lia) ALp8 ltac:(pose proof (wf_w _ WF); lia) ltac:(pose proof (wf_h _ WF); lia) Hw Hh
              ltac:(unfold dval in DV; lia) ltac:(lia) Hs16 Hret
              (PIX_rd_w SEGS _ _ _ PX) (PIX_rd_h SEGS _ _ _ PX) (PIX_rd_d SEGS _ _ _ PX) (PIX_rd_wpl SEGS _ _ _ PX) (PIX_rd_data SEGS _ _ _ PX)
              ltac:(lia) ltac:(lia) ALd4 ltac:(lia) SOKd ltac:(unfold disj_apart; lia) SOK ltac:(unfold disj_apart; lia) ltac:(unfold disj_apart; lia)
              regs ND24 ltac:(rewrite Hwpl; reflexivity) H1 H2 eq_refl eq_refl eq_refl H10 H11)
    as (r1 & m1 & RUN1 & INV1 & Q10 & Q2 & Q8 & Q9 & Q18 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  destruct INV1 as [OUT1 GR1].
  assert (CH : forall a, m1 a <> m a -> scratch C s a \/ (u a = u a /\ (p_data v <= u a < p_data v + 4 * (p_wpl v * p_h v))%Z)).
  { intros a NE. destruct (Z_lt_ge_dec (u a) (p_data v)) as [B1|B1];
      [| destruct (Z_lt_ge_dec (u a) (p_data v + 4 * (p_wpl v * p_h v))) as [B2|B2]; [right; split; [reflexivity | lia] |]];
      (left; unfold scratch; rewrite OUT1 in NE by lia;
       destruct (Z_lt_ge_dec (u a) (s - 48)); [exfalso; apply NE; apply M2g_outside; lia|];
       destruct (Z_lt_ge_dec (u a) s); [lia|]; exfalso; apply NE; apply M2g_outside; lia). }
  apply HK.
  - apply (W_local C A m md m1 s CK HW Hhi).
    + intros a NE. destruct (CH a NE) as [X|[_ R]]; [left; exact X | right].
      exists (Z_to_bv 64 (p_data v)), (4 * (p_wpl v * p_h v))%Z. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld00 | lia]].
    + eapply mem_grows_trans; [apply M2_grows | exact GR1].
  - apply cs_kept_intro; csr; try reflexivity.
  - apply (POSTM_local C Ar A m md m1 s CK HW SUB). intros a NE. destruct (CH a NE) as [X|[_ R]]; [left; exact X | right].
    exists (Z_to_bv 64 (p_data v)), (4 * (p_wpl v * p_h v))%Z. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld0 | lia]].
  - apply (PIXat_frame m); [exact PX|]. intros x Hx. rewrite OUT1 by lia. apply M2g_outside; lia.
  - intros a Ha Hb. rewrite OUT1 by lia. apply M2g_outside; lia.
  - left. exact Q10.
Qed.

End PadBitsW.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
