From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop GrayLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRopClip.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptRop_iface V23LeptCmap2 V23LeptRop V23LeptRopClip.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require V23RopLow.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section RopPre.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma rl_pre_W : forall C Ar A m md regs (s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy op : Z) (ret : word),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROPLOW_STACK <= s)%Z -> (s + 64 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw -> getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 op)) ->
  rdn SEGS m (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)) ->
  rdn SEGS m (Z_to_bv 64 (s + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixw)) ->
  rdn SEGS m (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  rdn SEGS m (Z_to_bv 64 (s + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sx)) ->
  rdn SEGS m (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  (0 <= datad < 2 ^ 64)%Z -> (0 <= datas < 2 ^ 64)%Z ->
  rop_shape dpixw dpixh 1 dwpl -> rop_shape spixw spixh 1 swpl ->
  (- 2 ^ 20 <= dx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= sx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= dy <= 2 ^ 20)%Z -> (- 2 ^ 20 <= sy <= 2 ^ 20)%Z ->
  (0 <= dw <= 2 ^ 20)%Z -> (0 <= dh <= 2 ^ 20)%Z ->
  ((clip_d dx sx) mod 32 = 0)%Z -> ((clip_s dx sx) mod 32 = 0)%Z ->
  live A (Z_to_bv 64 datad) = Some (4 * (dwpl * dpixh))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (swpl * spixh))%Z -> Z_to_bv 64 datas <> Z_to_bv 64 datad ->
  (op = 2 \/ op = 3 \/ op = 8 \/ op = 12 \/ op = 14)%Z ->
  (1 <= clip_w dx sx dw dpixw spixw)%Z -> (1 <= clip_w dy sy dh dpixh spixh)%Z ->
  exists regs1 M2,
    msteps SEGS (mkst regs (Z_to_bv 64 PC_rasteropLow) m al_rom) (mkst regs1 (0x803d8 : word) M2 al_rom)
    /\ (forall a : word, ~ (s - 240 <= u a < s)%Z -> M2 a = m a) /\ mem_grows m M2
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 21))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 22))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 23))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (getr regs 24))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 (getr regs 25))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (getr regs 26))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 (getr regs 27))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (clip_w dy sy dh dpixh spixh)))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl))
    /\ getr regs1 2 = Z_to_bv 64 (s - 240) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4
    /\ getr regs1 5 = Z_to_bv 64 1
    /\ getr regs1 7 = Z_to_bv 64 (datad + 4 * (clip_d dy sy * dwpl) + 4 * (clip_d dx sx / 32))
    /\ getr regs1 8 = Z_to_bv 64 (4 * (clip_s dy sy * swpl))
    /\ getr regs1 9 = Z_to_bv 64 (clip_w dx sx dw dpixw spixw)
    /\ getr regs1 10 = Z_to_bv 64 datad /\ getr regs1 11 = Z_to_bv 64 op
    /\ getr regs1 12 = Z_to_bv 64 (clip_w dx sx dw dpixw spixw mod 32)
    /\ getr regs1 14 = Z_to_bv 64 dwpl /\ getr regs1 16 = Z_to_bv 64 1
    /\ getr regs1 17 = Z_to_bv 64 (datas + 4 * (clip_s dy sy * swpl) + 4 * (clip_s dx sx / 32))
    /\ getr regs1 18 = Z_to_bv 64 (4 * (clip_s dx sx / 32)) /\ getr regs1 19 = Z_to_bv 64 datas
    /\ getr regs1 20 = Z_to_bv 64 sx /\ getr regs1 21 = Z_to_bv 64 dpixw
    /\ getr regs1 22 = Z_to_bv 64 (4 * (clip_d dy sy * dwpl)) /\ getr regs1 23 = Z_to_bv 64 (4 * (clip_d dx sx / 32))
    /\ getr regs1 27 = Z_to_bv 64 (clip_s dx sx) /\ getr regs1 29 = Z_to_bv 64 spixw /\ getr regs1 30 = Z_to_bv 64 dx
    /\ getr regs1 31 = Z_to_bv 64 (clip_d dx sx + clip_w2 dx sx dw - dpixw).
Proof.
  intros C Ar A m md regs s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy op ret
    CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
    Hdd Hds SHd SHs Bdx Bsx Bdy Bsy Bdw Bdh ALd ALs Ld Ld0 Ld00 Ls NEsd Hop NW NH.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *.
  assert (Hlo' : (c_top C - LSTK + 240 <= s)%Z) by exact Hlo.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  pose proof SHd as (_ & Hdpw & Hdph & Ewd & Hszd). pose proof SHs as (_ & Hspw & Hsph & Ews & Hszs).
  pose proof (wpl_bits dpixw 1 ltac:(lia) ltac:(lia)) as WBd. rewrite <- Ewd in WBd.
  pose proof (wpl_bits spixw 1 ltac:(lia) ltac:(lia)) as WBs. rewrite <- Ews in WBs.
  pose proof (wpl_of_range dpixw 1 ltac:(lia) ltac:(left; reflexivity)) as Hwd. rewrite <- Ewd in Hwd.
  pose proof (wpl_of_range spixw 1 ltac:(lia) ltac:(left; reflexivity)) as Hws. rewrite <- Ews in Hws.
  assert (Hnd : (0 < 4 * (dwpl * dpixh))%Z) by (assert (1 * 1 <= dwpl * dpixh)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  assert (Hns : (0 < 4 * (swpl * spixh))%Z) by (assert (1 * 1 <= swpl * spixh)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  destruct (blk_range C A m md (Z_to_bv 64 datad) _ CK HW Ld Hnd) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  destruct (blk_range C A m md (Z_to_bv 64 datas) _ CK HW Ls Hns) as [Gs TOPs]. rewrite u_Z2bv in Gs, TOPs by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & AL16d & _). rewrite u_Z2bv in AL16d by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ls) as (_ & AL16s & _). rewrite u_Z2bv in AL16s by lia.
  assert (SOK : store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true).
  { apply (W_sok_win C A m md (s - 112) 112 CK HW); try change (Z.of_nat 112) with 112%Z; lia. }
  assert (SOKf : store_ok SEGS m (Z_to_bv 64 (s - 240)) 240 = true).
  { apply (W_sok_win C A m md (s - 240) 240 CK HW); try change (Z.of_nat 240) with 240%Z; lia. }
  replace (Z_to_bv 64 PC_rasteropLow) with RLC_P by (apply bv_eq; reflexivity).
  destruct (rl_clip_run al_rom regs m s datad dpixw dpixh dwpl dx dy dw dh op datas spixw spixh swpl sx sy ret
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOK Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
              H2 H1 H10 H11 H12 H13 H14 H15 H16 H17 NW NH)
    as (r1 & S1 & D1 & D2 & D5 & D6 & D7 & D8 & D9 & D11 & D12 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & D26
        & D27 & D28 & D29 & D30 & D31 & AG1).
  carry AG1 H10 (10 : reg) G10. carry AG1 H14 (14 : reg) G14.
  pose proof (clip_facts dx sx dw dpixw spixw ltac:(lia) ltac:(lia) NW) as (CX1 & CX2 & CX3 & CX4 & CX5).
  pose proof (clip_facts dy sy dh dpixh spixh ltac:(lia) ltac:(lia) NH) as (CY1 & CY2 & CY3 & CY4 & CY5).
  set (DX := clip_d dx sx) in *. set (SX := clip_s dx sx) in *. set (DW := clip_w dx sx dw dpixw spixw) in *.
  set (DY := clip_d dy sy) in *. set (SY := clip_s dy sy) in *. set (DH := clip_w dy sy dh dpixh spixh) in *.
  set (nf := (DW / 32)%Z) in *. set (lw := (DW mod 32)%Z) in *. set (cdx := (DX / 32)%Z) in *. set (csx := (SX / 32)%Z) in *.
  pose proof (Z.div_mod DW 32 ltac:(lia)) as EDW. fold nf lw in EDW. pose proof (Z.mod_pos_bound DW 32 ltac:(lia)) as Hlw. fold lw in Hlw.
  pose proof (Z.div_mod DX 32 ltac:(lia)) as EDX. fold cdx in EDX. rewrite ALd in EDX.
  pose proof (Z.div_mod SX 32 ltac:(lia)) as ESX. fold csx in ESX. rewrite ALs in ESX.
  destruct (V23RopLow.rl_A2 m al_rom s dpixh DY DH spixh swpl SY 1 dpixw DX DW spixw SX dpixw DX DW spixw SX cdx csx nf lw
              ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23)
              (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              SOKf r1 D2 D25 D27 D6 D8)
    as (r2 & S2 & E12 & AG2).
  carry AG2 D5 (5 : reg) F5. carry AG2 D6 (6 : reg) F6. carry AG2 D7 (7 : reg) F7. carry AG2 G10 (10 : reg) F10.
  carry AG2 G14 (14 : reg) F14. carry AG2 D19 (19 : reg) F19. carry AG2 D25 (25 : reg) F25. carry AG2 D27 (27 : reg) F27.
  destruct (V23RopLow.rl_A3a m al_rom s datad dpixh dwpl DY DH datas spixh swpl SY 1 dpixw DX DW spixw SX dpixw DX DW spixw SX
              cdx csx nf lw
              ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23)
              (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(split; [lia | split; [lia | apply mod16_mod4; exact AL16d]])
              ltac:(split; [lia | split; [lia | apply mod16_mod4; exact AL16s]])
              r2 F5 F6 F7 F10 F14 F19 F25 F27)
    as (r3 & S3 & Y17 & Y7 & Y16 & Y5 & Y8 & Y18 & Y22 & Y23 & AG3).
  assert (AG23 : regs_agree (fun r : reg => In r [12; 13; 15; 16; 28; 5; 6; 7; 8; 17; 18; 22; 23]%list) r1 r3)
    by (eapply regs_agree_trans; [regs_agree_weaken AG2 | regs_agree_weaken AG3]).
  carry AG23 D2 (2 : reg) X2. carry AG23 D9 (9 : reg) X9. carry AG23 G10 (10 : reg) X10. carry AG23 D11 (11 : reg) X11.
  carry AG23 G14 (14 : reg) X14. carry AG23 D19 (19 : reg) X19. carry AG23 D20 (20 : reg) X20. carry AG23 D21 (21 : reg) X21.
  carry AG23 D27 (27 : reg) X27. carry AG23 D29 (29 : reg) X29. carry AG23 D30 (30 : reg) X30. carry AG23 D31 (31 : reg) X31.
  carry AG3 E12 (12 : reg) X12.
  assert (X3 : getr r3 3 = getr regs 3) by (rewrite (AG23 3 ltac:(notin_list)), (AG1 3 ltac:(notin_list)); reflexivity).
  assert (X4 : getr r3 4 = getr regs 4) by (rewrite (AG23 4 ltac:(notin_list)), (AG1 4 ltac:(notin_list)); reflexivity).
  assert (X7 : getr r3 7 = Z_to_bv 64 (datad + 4 * (DY * dwpl) + 4 * cdx)) by (rewrite Y7; f_equal; ring).
  assert (X8 : getr r3 8 = Z_to_bv 64 (4 * (SY * swpl))) by (rewrite Y8; f_equal; ring).
  assert (X17 : getr r3 17 = Z_to_bv 64 (datas + 4 * (SY * swpl) + 4 * csx)) by (rewrite Y17; f_equal; ring).
  assert (X22 : getr r3 22 = Z_to_bv 64 (4 * (DY * dwpl))) by (rewrite Y22; f_equal; ring).
  do 2 eexists. split; [eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact S2 | exact S3]] |].
  split.
  { intros a Ha. apply (V23RopLow.M2_outside m s datad DH datas swpl ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia)); lia. }
  split; [apply V23RopLow.M2_grows |].
  split; [exact (V23RopLow.F_ra m s datad DH datas swpl ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia)) |].
  split; [exact (V23RopLow.F_s0v m s datad DH datas swpl ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia)) |].
  split; [exact (V23RopLow.F_s1v m s datad DH datas swpl ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia)) |].
  split; [exact (V23RopLow.F_s2v m s datad DH datas swpl ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia)) |].
  split; [exact (V23RopLow.F_s3v m s datad DH datas swpl ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia)) |].
  split; [exact (V23RopLow.F_s4v m s datad DH datas swpl ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia)) |].
  split; [exact (V23RopLow.F_s5v m s datad DH datas swpl ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia)) |].
  split; [exact (V23RopLow.F_s6v m s datad DH datas swpl ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia)) |].
  split; [exact (V23RopLow.F_s7v m s datad DH datas swpl ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia)) |].
  split; [exact (V23RopLow.F_s8v m s datad DH datas swpl ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia)) |].
  split; [exact (V23RopLow.F_s9v m s datad DH datas swpl ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia)) |].
  split; [exact (V23RopLow.F_s10v m s datad DH datas swpl ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia)) |].
  split; [exact (V23RopLow.F_s11v m s datad DH datas swpl ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia)) |].
  split; [exact (V23RopLow.dh_cell m s datad DH datas swpl ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia)) |].
  split; [exact (V23RopLow.swpl_cell m s datad DH datas swpl ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia)) |].
  do 22 (split; [assumption |]). assumption.
Qed.

Lemma rl_empty_W : forall C Ar A m md regs (s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy op : Z) (ret : word),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROPLOW_STACK <= s)%Z -> (s + 64 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw -> getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 op)) ->
  rdn SEGS m (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)) ->
  rdn SEGS m (Z_to_bv 64 (s + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixw)) ->
  rdn SEGS m (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  rdn SEGS m (Z_to_bv 64 (s + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sx)) ->
  rdn SEGS m (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  (0 <= datad < 2 ^ 64)%Z -> (0 <= datas < 2 ^ 64)%Z ->
  rop_shape dpixw dpixh 1 dwpl -> rop_shape spixw spixh 1 swpl ->
  (- 2 ^ 20 <= dx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= sx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= dy <= 2 ^ 20)%Z -> (- 2 ^ 20 <= sy <= 2 ^ 20)%Z ->
  (0 <= dw <= 2 ^ 20)%Z -> (0 <= dh <= 2 ^ 20)%Z ->
  live A (Z_to_bv 64 datad) = Some (4 * (dwpl * dpixh))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (swpl * spixh))%Z -> Z_to_bv 64 datas <> Z_to_bv 64 datad ->
  (op = 2 \/ op = 3 \/ op = 8 \/ op = 12 \/ op = 14)%Z ->
  (clip_w dx sx dw dpixw spixw <= 0 \/ clip_w dy sy dh dpixh spixh <= 0)%Z ->
  exists regs1 M1,
    msteps SEGS (mkst regs (Z_to_bv 64 PC_rasteropLow) m al_rom) (mkst regs1 ret M1 al_rom)
    /\ (forall a : word, ~ (s - 240 <= u a < s)%Z -> M1 a = m a) /\ mem_grows m M1 /\ cs_kept regs regs1.
Proof.
  intros C Ar A m md regs s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy op ret
    CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
    Hdd Hds SHd SHs Bdx Bsx Bdy Bsy Bdw Bdh Ld Ld0 Ld00 Ls NEsd Hop E.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *.
  assert (Hlo' : (c_top C - LSTK + 240 <= s)%Z) by exact Hlo.
  pose proof SHd as (_ & Hdpw & Hdph & Ewd & Hszd). pose proof SHs as (_ & Hspw & Hsph & Ews & Hszs).
  pose proof (wpl_of_range spixw 1 ltac:(lia) ltac:(left; reflexivity)) as Hws. rewrite <- Ews in Hws.
  assert (SOK : store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true).
  { apply (W_sok_win C A m md (s - 112) 112 CK HW); try change (Z.of_nat 112) with 112%Z; lia. }
  replace (Z_to_bv 64 PC_rasteropLow) with RLC_P by (apply bv_eq; reflexivity).
  exact (rl_clip_empty al_rom regs m s datad dpixw dpixh dwpl dx dy dw dh op datas spixw spixh swpl sx sy ret
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOK Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
           H2 H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 E).
Qed.

End RopPre.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
