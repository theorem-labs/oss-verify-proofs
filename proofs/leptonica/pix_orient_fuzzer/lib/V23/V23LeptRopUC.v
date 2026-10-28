(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptRop_iface V23LeptRop V23_code_pixRasterop V23LeptRopUniC.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section RopUC.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Ltac grows_chain := repeat (eapply mem_grows_trans; [| apply wbytes_grows]); apply mem_grows_refl.

(* [comment removed for export] *)
Definition pixRasterop_uniclip_contract : Prop :=
  forall C Ar A m md regs (s pixd dx dy dw dh op : Z) (v : pixv) (syw : word) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROP_STACK <= s)%Z -> (s + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 dx -> getr regs 12 = Z_to_bv 64 dy -> getr regs 13 = Z_to_bv 64 dw ->
  getr regs 14 = Z_to_bv 64 dh -> getr regs 15 = Z_to_bv 64 op ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 syw) ->
  PIXat m pixd v -> p_d v = 1%Z -> rop_shape (p_w v) (p_h v) (p_d v) (p_wpl v) ->
  (- 2 ^ 20 <= dx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= dy <= 2 ^ 20)%Z -> (0 <= dw <= 2 ^ 20)%Z -> (0 <= dh <= 2 ^ 20)%Z -> (op = 0 \/ op = 15)%Z ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> Z_to_bv 64 pixd <> Z_to_bv 64 (p_data v) ->
  live A (Z_to_bv 64 (p_data v)) = Some (4 * (p_wpl v * p_h v))%Z -> live Ar (Z_to_bv 64 (p_data v)) = None ->
  live (c_A0 C) (Z_to_bv 64 (p_data v)) = None ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' -> PIXat m' pixd v ->
      (forall a : word, ~ scratch C s a -> ~ (p_data v <= bv_unsigned a < p_data v + 4 * (p_wpl v * p_h v))%Z -> m' a = m a) ->
      getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixRasterop) m al_rom) md) S.

Theorem pixRasterop_uniclip_W : pixRasterop_uniclip_contract.
Proof.
  unfold pixRasterop_uniclip_contract.
  intros C Ar A m md regs s pixd dx dy dw dh op v syw ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 Rsy
    PX Ed1 SH Bdx Bdy Bdw Bdh Hop Lp NEp Ld Ld0 Ld00 HK.
  unfold PC_pixRasterop. replace (Z_to_bv 64 0x7f13c) with (0x7f13c : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ROP_STACK in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  destruct (pix_facts C A m md pixd v CK HW PX SH Lp) as (Gp & TOPp & Hdata & Hwpl).
  assert (ALd8 : (pixd mod 8 = 0)%Z) by (pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & X16 & _); rewrite u_Z2bv in X16 by lia; apply mod16_mod8; exact X16).
  pose proof SH as (Hd & Hw & Hh & _ & Hsz).
  set (nd := (4 * (p_wpl v * p_h v))%Z) in *.
  assert (Hnd : (0 < nd)%Z) by (subst nd; clear - Hwpl Hh; nia).
  destruct (pr_A al_rom regs m s pixd op v ret syw ltac:(lia) Hs16 ALd8 ltac:(lia) ltac:(lia) ltac:(lia) PX ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 224) 224 CK HW ltac:(lia) ltac:(cbn; lia)) Rsy H2 H1 H10 H15)
    as (r1 & RUN1 & Q2 & Q19 & Q20 & Q21 & Q25 & Q22 & Q27 & Q18 & Q9 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := PRM m s ret regs (p_w v) (p_h v) (p_d v)).
  assert (WP1 : W C A M1 md /\ POSTM C Ar s m M1)
    by (apply (WP_range C Ar A m m M1 md s (s - 224) CK HW (POSTM_refl _ _ _ _) SUB); [lia | lia | intros a Ha; subst M1; apply PRM_outside; lia | subst M1; unfold PRM, RLF; grows_chain]).
  destruct WP1 as [HW1 PM1].
  assert (OUT1 : forall a : word, ~ (s - 224 <= u a < s)%Z -> M1 a = m a) by (intros a Ha; subst M1; apply PRM_outside; lia).
  assert (PX1 : PIXat M1 pixd v) by (apply (PIXat_frame m); [exact PX | intros x Hx; apply OUT1; lia]).
  assert (Rw1 : rdn SEGS M1 (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))))
    by (subst M1; unfold PRM; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_w v)))); zlen; unorm; lia).
  assert (Rh1 : rdn SEGS M1 (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_h v))))
    by (subst M1; unfold PRM; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_h v)))); zlen; unorm; lia).
  assert (Rd1 : rdn SEGS M1 (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_d v))))
    by (subst M1; unfold PRM; repeat rdn_peel1; apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 (p_d v)))); zlen; unorm; lia).
  pose proof (rlcells_RLF m s ret regs ltac:(lia) ltac:(lia)) as CE0.
  assert (CE1 : rlcells M1 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
  { apply (rlcells_frame (RLF m s ret regs) M1 s); [lia | lia | exact CE0 |]. intros x Hx. subst M1. apply PRM_above; lia. }
  destruct (pr_Bu al_rom r1 M1 s pixd op dx dy dw dh v ltac:(lia) Hs16 ALd8 ltac:(lia) ltac:(lia) ltac:(lia) PX1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hdata Hop
              (W_sok_win C A M1 md (s - 224) 16 CK HW1 ltac:(lia) ltac:(cbn; lia)) Rw1 Rh1 Rd1
              Q2 Q19 Q20 ltac:(rewrite Q27; exact H14) ltac:(rewrite Q18; exact H11) ltac:(rewrite Q9; exact H12) ltac:(rewrite Q8; exact H13))
    as (r2 & RUN2 & P2 & P1 & P10 & P11 & P12 & P13 & P14 & P15 & P16' & P17 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  set (M2 := wbytes (wbytes M1 _ _) _ _).
  assert (WP2 : W C A M2 md /\ POSTM C Ar s m M2) by (subst M2; wp_win CK).
  destruct WP2 as [HW2 PM2].
  assert (OUT2 : forall a : word, ~ (s - 224 <= u a < s)%Z -> M2 a = m a).
  { intros a Ha. subst M2. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). apply OUT1. exact Ha. }
  assert (CE2 : rlcells M2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
  { apply (rlcells_frame M1 M2 s); [lia | lia | exact CE1 |]. intros x Hx. subst M2.
    rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity. }
  replace (0x7f3d8 : word) with (Z_to_bv 64 PC_rasteropUniLow) by (apply bv_eq; reflexivity).
  apply (rasteropUniLow_clip_W C Ar A M2 md r2 (s - 224)%Z (p_data v) (p_w v) (p_h v) (p_wpl v) dx dy dw dh op (Z_to_bv 64 0x7f21c) S CK HW2 SUB P2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ROPUNI_STACK; lia) ltac:(lia) P1
           ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 ltac:(rewrite P13, Ed1; reflexivity) P14 P15 P16' P17).
  1-2: repeat match goal with |- context [Z_to_bv 64 (?b - 224 + ?k)%Z] => let c := eval cbv in (224 - k)%Z in replace (b - 224 + k)%Z with (b - c)%Z by lia end;
       subst M2; rdn_chain.
  - exact Hdata. - rewrite <- Ed1. exact SH. - exact Bdx. - exact Bdy. - exact Bdw. - exact Bdh. - exact Hop. - exact Ld. - exact Ld0. - exact Ld00.
  - intros m3 r3 HW3 CS3 PM3 FT3.
    replace (Z_to_bv 64 0x7f21c) with (0x7f21c : word) by (apply bv_eq; reflexivity).
    destruct (blk_range C A m md (Z_to_bv 64 (p_data v)) nd CK HW Ld Hnd) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
    assert (CE3 : rlcells m3 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
    { apply (rlcells_frame M2 m3 s); [lia | lia | exact CE2 |]. intros x Hx. apply FT3; [unfold scratch; lia | lia]. }
    destruct (pr_C al_rom r3 m3 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ltac:(lia) ltac:(lia) Hret CE3 ltac:(csr; reflexivity))
      as (r5 & RUN5 & Z2 & Z1 & Z10 & Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
    apply (HK m3 r5 HW3).
    + apply cs_kept_intro; first [ rewrite Z2; symmetry; exact H2 | assumption | csr; reflexivity ].
    + eapply POSTM_trans; [exact PM2 | eapply POSTM_mono; [| exact PM3]; lia].
    + apply (PIXat_frame m); [exact PX|].
      apply (hdr_kept C A m md (s - 224) pixd (p_data v) nd M2 m3 CK HW Lp Ld NEp ltac:(lia) Hdata Hnd ltac:(lia) FT3).
      intros a NW. apply OUT2. intros X. apply NW. unfold win. lia.
    + intros a Ha Hb. unfold scratch in Ha. rewrite (FT3 a) by (unfold scratch; lia). apply OUT2. lia.
    + exact Z10.
Qed.

End RopUC.
