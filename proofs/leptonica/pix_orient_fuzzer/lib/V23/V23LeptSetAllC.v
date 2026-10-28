(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import MemsetFillLib MemsetFill_iface.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23LeptErr V23MemsetFill V23LeptSetAll V23_code_morphA_setall.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptSetAll.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Lemma str_psa_msg : str16 0x1d5f4 25.
Proof. str16_tac. Qed.     (* [comment removed for export] *)
Lemma str_psa_proc : str16 0x14aef 9.
Proof. str16_tac. Qed.     (* [comment removed for export] *)

Section SetAllC.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma psc_Af : forall regs m (s pix cm : Z) (v : pixv) (cv : cmapv) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix)%Z -> (pix mod 8 = 0)%Z ->
    PIXat (O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)) pix v -> p_cmap v = cm -> (1 <= cm)%Z -> (cm mod 8 = 0)%Z ->
    CMAPat (O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)) cm cv -> (c_nalloc cv <= c_n cv)%Z ->
    (0 <= p_wpl v * p_h v)%Z -> (4 * (p_wpl v * p_h v) < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x6ffb4 : word) m rom) (mkst regs' (0x11e6d4 : word) (O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x70044
      /\ getr regs' 10 = Z_to_bv 64 (p_data v) /\ getr regs' 11 = Z_to_bv 64 255 /\ getr regs' 12 = Z_to_bv 64 (4 * (p_wpl v * p_h v))
      /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m s pix cm v cv ret Hs Hs64 Hpix AL8 PX Hcm Hcm1 ALc CM Hna Hn Hn31 SOK H2 H1 H10.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_wpl _ WF). pose proof (wf_h _ WF). pose proof (wf_data _ WF).
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF). pose proof (cf_nalloc _ CWF).
    unfold O23LeptSetAll.FR3 in *. eexists. split.
    - zv F_6ffb4 D_6ffb4 (Z_to_bv 64 (s - 32)).
      stepST F_6ffb8 D_6ffb8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_6ffbc D_6ffbc (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_6ffc0 D_6ffc0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_6ffc4 D_6ffc4 ltac:(condZ).
      sn F_6ffc8 D_6ffc8. sn F_6ffcc D_6ffcc.
      stepb_ft F_6f238 D_6f238 ltac:(condZ).
      guard8 F_6f23c D_6f23c AL8.
      stepb_ft F_6f240 D_6f240 ltac:(condZ).
      stepLD F_6f244 D_6f244 (Z_to_le_bytes 8 cm) (Z_to_bv 64 cm) ltac:(addr_norm; rewrite <- Hcm; exact (PIX_rd_cmap SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepret F_6f248 D_6f248 (0x6ffd0 : word) ltac:(bveq).
      stepb_ft F_6ffd0 D_6ffd0 ltac:(condZ).
      sn F_6ffd4 D_6ffd4. sn F_6ffd8 D_6ffd8.
      stepb_ft F_7369c D_7369c ltac:(condZ).
      guard8 F_736a0 D_736a0 ALc.
      stepb_ft F_736a4 D_736a4 ltac:(condZ).
      stepLD F_736a8 D_736a8 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact (CMAP_rd_n SEGS _ _ _ CM)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      stepret F_736ac D_736ac (0x6ffdc : word) ltac:(bveq).
      guard8 F_6ffdc D_6ffdc ALc.
      stepb_ft F_6ffe0 D_6ffe0 ltac:(condZ).
      stepLD F_6ffe4 D_6ffe4 (Z_to_le_bytes 4 (c_nalloc cv)) (Z_to_bv 64 (c_nalloc cv)) ltac:(addr_norm; exact (CMAP_rd_nalloc SEGS _ _ _ CM)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_nalloc cv)) by lia.
      stepb_tk F_6ffe8 D_6ffe8 ltac:(condZ).
      guard8 F_70014 D_70014 AL8.
      stepb_ft F_70018 D_70018 ltac:(condZ).
      stepLD F_7001c D_7001c (Z_to_le_bytes 4 (p_wpl v)) (Z_to_bv 64 (p_wpl v)) ltac:(addr_norm; exact (PIX_rd_wpl SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      stepLD F_70020 D_70020 (Z_to_le_bytes 4 (p_h v)) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      stepiv F_70024 D_70024 (Z_to_bv 64 (4 * p_wpl v)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_70028 D_70028. fixv (Z_to_bv 64 0) ltac:(apply v_mulh_small; lia).
      zv F_7002c D_7002c (Z_to_bv 64 (4 * (p_wpl v * p_h v))).
      sn F_70030 D_70030. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srai_small by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_70034 D_70034 ltac:(condZ).
      stepLD F_70038 D_70038 (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v)) ltac:(addr_norm; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      sn F_7003c D_7003c. sn F_70040 D_70040.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma psc_Ae : forall regs m (s pix cm : Z) (v : pixv) (cv : cmapv) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix)%Z -> (pix mod 8 = 0)%Z ->
    PIXat (O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)) pix v -> p_cmap v = cm -> (1 <= cm)%Z -> (cm mod 8 = 0)%Z ->
    CMAPat (O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)) cm cv -> (c_n cv < c_nalloc cv)%Z ->
    rdn SEGS (O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)) (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) ->
    rdn SEGS (O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)) (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x6ffb4 : word) m rom) (mkst regs' (0x63670 : word) (O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ getr regs' 10 = Z_to_bv 64 0x1d5f4 /\ getr regs' 11 = Z_to_bv 64 0x14aef /\ getr regs' 12 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pix cm v cv ret Hs Hs64 Hpix AL8 PX Hcm Hcm1 ALc CM Hna Rg Rs SOK H2 H1 H10.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF). pose proof (cf_nalloc _ CWF).
    unfold O23LeptSetAll.FR3 in *. eexists. split.
    - zv F_6ffb4 D_6ffb4 (Z_to_bv 64 (s - 32)).
      stepST F_6ffb8 D_6ffb8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_6ffbc D_6ffbc (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_6ffc0 D_6ffc0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_6ffc4 D_6ffc4 ltac:(condZ).
      sn F_6ffc8 D_6ffc8. sn F_6ffcc D_6ffcc.
      stepb_ft F_6f238 D_6f238 ltac:(condZ).
      guard8 F_6f23c D_6f23c AL8.
      stepb_ft F_6f240 D_6f240 ltac:(condZ).
      stepLD F_6f244 D_6f244 (Z_to_le_bytes 8 cm) (Z_to_bv 64 cm) ltac:(addr_norm; rewrite <- Hcm; exact (PIX_rd_cmap SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepret F_6f248 D_6f248 (0x6ffd0 : word) ltac:(bveq).
      stepb_ft F_6ffd0 D_6ffd0 ltac:(condZ).
      sn F_6ffd4 D_6ffd4. sn F_6ffd8 D_6ffd8.
      stepb_ft F_7369c D_7369c ltac:(condZ).
      guard8 F_736a0 D_736a0 ALc.
      stepb_ft F_736a4 D_736a4 ltac:(condZ).
      stepLD F_736a8 D_736a8 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact (CMAP_rd_n SEGS _ _ _ CM)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      stepret F_736ac D_736ac (0x6ffdc : word) ltac:(bveq).
      guard8 F_6ffdc D_6ffdc ALc.
      stepb_ft F_6ffe0 D_6ffe0 ltac:(condZ).
      stepLD F_6ffe4 D_6ffe4 (Z_to_le_bytes 4 (c_nalloc cv)) (Z_to_bv 64 (c_nalloc cv)) ltac:(addr_norm; exact (CMAP_rd_nalloc SEGS _ _ _ CM)) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_nalloc cv)) by lia.
      stepb_ft F_6ffe8 D_6ffe8 ltac:(condZ).
      sn F_6ffec D_6ffec.
      stepLD F_6fff0 D_6fff0 (Z_to_le_bytes 8 0x127c60) (Z_to_bv 64 0x127c60) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_6fff4 D_6fff4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      try rewrite (v_lw_small 3) by lia.
      sn F_6fff8 D_6fff8.
      stepb_ft F_6fffc D_6fffc ltac:(condZ).
      sn F_70000 D_70000. sn F_70004 D_70004. sn F_70008 D_70008. sn F_7000c D_7000c.
      sn F_70010 D_70010.
      sn F_70070 D_70070.
      stepLD8 F_70074 D_70074 ret. stepLD8 F_70078 D_70078 (getr regs 8). stepLD8 F_7007c D_7007c (getr regs 9).
      zv F_70080 D_70080 (Z_to_bv 64 s).
      sn F_70084 D_70084.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

(* [comment removed for export] *)
Theorem pixSetAll_W : forall C Ar A m md regs (s pix k : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SETALL_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pix ->
  PIXat m pix v -> live A (Z_to_bv 64 pix) = Some 64%Z -> Z_to_bv 64 pix <> Z_to_bv 64 (p_data v) ->
  (p_cmap v <> 0 -> exists cv, CMAPat m (p_cmap v) cv /\ live A (Z_to_bv 64 (p_cmap v)) = Some 24)%Z ->
  (1 <= p_wpl v * p_h v)%Z -> (4 * (p_wpl v * p_h v) < 2 ^ 31)%Z ->
  live A (Z_to_bv 64 (p_data v)) = Some k -> (4 * (p_wpl v * p_h v) <= k)%Z ->
  live Ar (Z_to_bv 64 (p_data v)) = None -> live (c_A0 C) (Z_to_bv 64 (p_data v)) = None ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' -> PIXat m' pix v ->
     (forall x : word, ~ (p_data v <= u x < p_data v + 4 * (p_wpl v * p_h v))%Z -> ~ scratch C s x -> m' x = m x) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6ffb4 : word) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s pix k v ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 PX Lp NEpd HCM Hn Hn31 Ld Hk Ld0 Ld00 HK.
  destruct (Z.eq_dec (p_cmap v) 0) as [Hc0 | Hc0].
  { apply (pixSetAll_nocmap_W C Ar A m md regs s pix k v ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 PX Lp NEpd Hc0 Hn Hn31 Ld Hk Ld0 Ld00).
    intros m' regs' HW' CS' PM' PX' OUT' _. exact (HK m' regs' HW' CS' PM' PX' OUT'). }
  destruct (HCM Hc0) as (cv & CM & Lcm).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. unfold SETALL_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_wpl _ WF). pose proof (wf_h _ WF). pose proof (wf_data _ WF).
  pose proof (wf_cmap _ WF) as Hcmr.
  pose proof CM as (Hcm0 & Hcm64 & CWF & _). pose proof (cf_n _ CWF). pose proof (cf_nalloc _ CWF).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 (p_data v)) k CK HW Ld ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  destruct (blk_range C A m md (Z_to_bv 64 (p_cmap v)) 24 CK HW Lcm ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALp | reflexivity]).
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lcm) as (_ & ALcm & _). rewrite u_Z2bv in ALcm by lia.
  assert (ALc : (p_cmap v mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r (p_cmap v)); apply mod16_plus_mod8; [exact ALcm | reflexivity]).
  pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lp Ld NEpd) as DJ. rewrite !u_Z2bv in DJ by lia.
  unfold round16 in DJ at 1. change ((64 + 15) / 16)%Z with 4%Z in DJ. pose proof (round16_ge k ltac:(lia)).
  pose proof (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  assert (OUT1 : forall x : word, ~ (s - 24 <= u x < s)%Z -> O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9) x = m x).
  { intros x Hx. unfold O23LeptSetAll.FR3. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PX1 : PIXat (O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)) pix v).
  { apply (PIXat_frame m); [exact PX|]. intros x Hx. apply OUT1. lia. }
  assert (CM1 : CMAPat (O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)) (p_cmap v) cv).
  { apply (CMAPat_frame m); [exact CM|]. intros x Hx. apply OUT1. lia. }
  assert (WP1 : W C A (O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)) md /\ POSTM C Ar s m (O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)))
    by (unfold O23LeptSetAll.FR3; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (cells3_FR3 m s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia)) as (C1 & C2 & C3).
  set (M1 := O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)) in *.
  destruct (Z_le_gt_dec (c_nalloc cv) (c_n cv)) as [Hna | Hna].
  - destruct (psc_Af al_rom regs m s pix (p_cmap v) v cv ret ltac:(lia) ltac:(lia) ltac:(lia) AL8 PX1 eq_refl ltac:(lia) ALc CM1 Hna
                ltac:(lia) Hn31 SOK H2 H1 H10) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    assert (SOKd : store_ok SEGS M1 (Z_to_bv 64 (p_data v)) (Z.to_nat (4 * (p_wpl v * p_h v))) = true).
    { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
      unfold wview. destruct (M1 x) eqn:E; [discriminate|]. exfalso.
      destruct (blk_byte C A M1 _ (Z_to_bv 64 (p_data v)) _ x CK HW1 Ld ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D E). }
    destruct (memset_fill_o14 r1 M1 al_rom (p_data v) (4 * (p_wpl v * p_h v))%Z 255%Z (Z_to_bv 64 0x70044)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOKd ltac:(red; apply bv_eq; reflexivity) Q1 Q10 Q11 Q12)
      as (r2 & M2 & RUN2 & A10 & AG2 & ZO & ZG & ZN).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN2 |].
    replace (Z_to_bv 64 0x70044) with (0x70044 : word) by (apply bv_eq; reflexivity).
    assert (CH : forall a, M2 a <> M1 a -> (p_data v <= u a < p_data v + 4 * (p_wpl v * p_h v))%Z).
    { intros a NE. destruct (Z_lt_ge_dec (u a) (p_data v)) as [Hl|Hl]; [exfalso; apply NE; apply ZO; lia|].
      destruct (Z_lt_ge_dec (u a) (p_data v + 4 * (p_wpl v * p_h v))) as [Hh|Hh]; [lia | exfalso; apply NE; apply ZO; lia]. }
    assert (R8 : rdn SEGS M2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
    { rewrite <- C1. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply ZO. lia. }
    assert (R16 : rdn SEGS M2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
    { rewrite <- C2. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply ZO. lia. }
    assert (R24 : rdn SEGS M2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
    { rewrite <- C3. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply ZO. lia. }
    assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    destruct (psa_B al_rom r2 M2 s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) Hret R8 R16 R24 E2)
      as (r3 & RUN3 & U2 & U1 & U10 & U8 & U9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN3 |].
    apply (HK M2 r3).
    + apply (W_local C A M1 md M2 s CK HW1 Hhi); [| exact ZG].
      intros a NE. right. exists (Z_to_bv 64 (p_data v)), k. rewrite u_Z2bv by lia.
      split; [exact Ld|]. split; [exact Ld00|]. pose proof (CH a NE). lia.
    + apply cs_kept_intro; csr; try reflexivity.
    + eapply POSTM_trans; [exact PM1|]. apply (POSTM_local C Ar A M1 md M2 s CK HW1 SUB).
      intros a NE. right. exists (Z_to_bv 64 (p_data v)), k. rewrite u_Z2bv by lia.
      split; [exact Ld|]. split; [exact Ld0|]. pose proof (CH a NE). lia.
    + apply (PIXat_frame M1); [exact PX1|]. intros x Hx. apply ZO. lia.
    + intros x Hx Hsc. rewrite ZO by lia. apply OUT1. intros Hx'. apply Hsc. unfold scratch. lia.
  - destruct (psc_Ae al_rom regs m s pix (p_cmap v) v cv ret ltac:(lia) ltac:(lia) ltac:(lia) AL8 PX1 eq_refl ltac:(lia) ALc CM1 ltac:(lia)
                (W_sev_got C A M1 md HW1) (W_sev C A M1 md HW1) SOK H2 H1 H10)
      as (r1 & RUN1 & V2 & V1 & V8 & V9 & V10 & V11 & V12 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    apply (returnErrorInt_W C A M1 md r1 s 0x1d5f4 0x14aef 25 9 ret (Z_to_bv 64 1) S CK HW1 V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
             V10 V11 V12 str_psa_msg str_psa_proc).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    apply (HK m4 r5 HW4).
    + apply cs_kept_intro; csr; try reflexivity.
    + eapply POSTM_trans; [exact PM1|]. apply (POSTM_sub C Ar A); [exact SUB|].
      eapply (POSTM_range C A M1 _ m4); [exact CK | exact HW1 | exact OUT4 | lia | lia | lia].
    + apply (PIXat_frame M1); [exact PX1|]. intros x Hx. apply OUT4. lia.
    + intros x Hx Hsc. rewrite OUT4 by (intros Hx'; apply Hsc; unfold scratch; lia). apply OUT1. intros Hx'. apply Hsc. unfold scratch. lia.
Qed.

End SetAllC.
