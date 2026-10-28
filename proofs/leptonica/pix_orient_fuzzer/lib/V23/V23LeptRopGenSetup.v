From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptRop2Segs V23LeptRopGSpec V23LeptRop2Gset.
Import ListNotations.
Open Scope bv_scope.

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac gs_mg := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
Ltac gs_out := repeat (rewrite wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia)).

Section GenSetup.
Context {fx : FPState}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Definition rg_setup_spec : Prop :=
  forall (rom : word -> option byte) regs M
    (s datad dpixh datas spixh dwpl swpl DX SX DW DY SY DH op tv c28 c30 c38 c40 c48 c50 : Z),
  (250000 <= s)%Z -> (s + 64 < 2 ^ 64)%Z ->
  (4096 <= datad)%Z -> (datad + 4 * (dwpl * dpixh) + 2 ^ 27 <= 2 ^ 64)%Z -> (datad mod 4 = 0)%Z ->
  (4096 <= datas)%Z -> (datas + 4 * (swpl * spixh) + 2 ^ 27 <= 2 ^ 64)%Z -> (datas mod 4 = 0)%Z ->
  (1 <= dwpl <= 20000)%Z -> (1 <= swpl <= 20000)%Z -> (1 <= dpixh <= 20000)%Z -> (1 <= spixh <= 20000)%Z ->
  (4 * (dwpl * dpixh) <= 67108864)%Z -> (4 * (swpl * spixh) <= 67108864)%Z ->
  (0 <= DX)%Z -> (0 <= SX)%Z -> (1 <= DW)%Z -> (DX + DW <= 32 * dwpl)%Z -> (SX + DW <= 32 * swpl)%Z ->
  (0 <= DY)%Z -> (0 <= SY)%Z -> (1 <= DH)%Z -> (DY + DH <= dpixh)%Z -> (SY + DH <= spixh)%Z ->
  (DX mod 32 <> SX mod 32)%Z -> (g_smax DX SX DW <= swpl - 1)%Z ->
  (1 <= op <= 14)%Z -> (0 <= tv < 2 ^ 31)%Z -> (tv mod 2 = 0)%Z ->
  rdn SEGS M (Z_to_bv 64 (RG_JT + 4 * (op - 1))) 4 = Some (Z_to_le_bytes 4 tv) ->
  (- 2 ^ 28 <= c28 < 2 ^ 28)%Z -> (- 2 ^ 28 <= c30 < 2 ^ 28)%Z -> (- 2 ^ 28 <= c38 < 2 ^ 28)%Z ->
  (- 2 ^ 28 <= c40 < 2 ^ 28)%Z -> (- 2 ^ 28 <= c48 < 2 ^ 28)%Z -> (- 2 ^ 28 <= c50 < 2 ^ 28)%Z ->
  (c28 - c50 - Z.min 0 (c30 + c38 - c50 - c40 + Z.min 0 c48) = - DH)%Z ->
  store_ok SEGS M (Z_to_bv 64 (s - 240)) 240 = true ->
  rdn SEGS M (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 DH)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) ->
  getr regs 1 = Z_to_bv 64 c28 -> getr regs 26 = Z_to_bv 64 c30 -> getr regs 23 = Z_to_bv 64 c38 ->
  getr regs 16 = Z_to_bv 64 c40 -> getr regs 18 = Z_to_bv 64 c48 -> getr regs 28 = Z_to_bv 64 c50 ->
  getr regs 6 = Z_to_bv 64 swpl -> getr regs 5 = Z_to_bv 64 SY -> getr regs 7 = Z_to_bv 64 DY ->
  getr regs 8 = Z_to_bv 64 DW -> getr regs 9 = Z_to_bv 64 DW -> getr regs 10 = Z_to_bv 64 datad ->
  getr regs 11 = Z_to_bv 64 op -> getr regs 13 = Z_to_bv 64 DX -> getr regs 14 = Z_to_bv 64 dwpl ->
  getr regs 19 = Z_to_bv 64 datas -> getr regs 24 = Z_to_bv 64 SX -> getr regs 25 = Z_to_bv 64 DX ->
  getr regs 27 = Z_to_bv 64 SX ->
  exists regs1 MB (dxb sls nfw psf pdf psF pdF psl pdl : Z) (fw f6 f7 nofull nolast f3 : bool),
    msteps SEGS (mkst regs RG_P0 M rom) (mkst regs1 (Z_to_bv 64 (RG_JT + tv)) MB rom)
    /\ (forall a : word, ~ (s - 240 <= u a < s - 112)%Z -> MB a = M a) /\ mem_grows M MB
    /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4
    /\ rg_geo datad (4 * (dwpl * dpixh)) datas (4 * (swpl * spixh)) DH swpl dwpl dxb sls nfw psf pdf psF pdF psl pdl
         fw f6 f7 nofull nolast f3
    /\ rg_cells MB s DH swpl nfw psl fw f6 nofull nolast f3
    /\ rg_regs regs1 s dxb dwpl sls psf pdf psF pdF pdl fw f7 nofull nolast.

Lemma gs_rdnN : forall (m1 m2 : word -> option byte) (a : Z) (n : nat) (bs : list byte),
  (0 <= a)%Z -> (a + Z.of_nat n < 2 ^ 64)%Z -> (forall x : word, (a <= u x < a + Z.of_nat n)%Z -> m1 x = m2 x) ->
  rdn SEGS m2 (Z_to_bv 64 a) n = Some bs -> rdn SEGS m1 (Z_to_bv 64 a) n = Some bs.
Proof.
  intros m1 m2 a n bs Ha Hn E R. rewrite <- R. apply rdn_ext; rewrite u_Z2bv by lia.
  - lia.
  - intros x Hx. apply E. lia.
Qed.

Lemma gs_rows_agree : forall (m1 m2 : word -> option byte) (s dh : Z), (200 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (forall x : word, (s - 200 <= u x < s - 152)%Z -> m1 x = m2 x) -> rg_rows m2 s dh -> rg_rows m1 s dh.
Proof.
  intros m1 m2 s dh H1 H2 E (c28 & c30 & c38 & c40 & c48 & c50 & R1 & R2 & R3 & R4 & R5 & R6 & Rest).
  exists c28, c30, c38, c40, c48, c50.
  do 6 (split; [apply (gs_rdnN m1 m2); [lia | lia | intros x Hx; apply E; lia | assumption] |]).
  exact Rest.
Qed.

Lemma gs_geo : forall (datad dpixh datas spixh dwpl swpl DX SX DW DY SY DH : Z),
  (4096 <= datad)%Z -> (datad mod 4 = 0)%Z -> (4096 <= datas)%Z -> (datas mod 4 = 0)%Z ->
  (1 <= dwpl <= 20000)%Z -> (1 <= swpl <= 20000)%Z -> (1 <= dpixh <= 20000)%Z -> (1 <= spixh <= 20000)%Z ->
  (0 <= DX)%Z -> (0 <= SX)%Z -> (1 <= DW)%Z -> (DX + DW <= 32 * dwpl)%Z ->
  (0 <= DY)%Z -> (0 <= SY)%Z -> (1 <= DH)%Z -> (DY + DH <= dpixh)%Z -> (SY + DH <= spixh)%Z ->
  (DX mod 32 <> SX mod 32)%Z -> (g_smax DX SX DW <= swpl - 1)%Z ->
  rg_geo datad (4 * (dwpl * dpixh)) datas (4 * (swpl * spixh)) DH swpl dwpl (DX mod 32) (g_sls DX SX) (g_nfw DX DW)
    (datas + 4 * (SY * swpl) + 4 * (SX / 32)) (datad + 4 * (DY * dwpl) + 4 * (DX / 32))
    (datas + 4 * (SY * swpl) + 4 * ((SX + g_hang DX) / 32)) (datad + 4 * (DY * dwpl) + 4 * ((DX + g_hang DX) / 32))
    (datas + 4 * (SY * swpl) + 4 * ((SX + g_hang DX) / 32) + 4 * g_nfw DX DW)
    (datad + 4 * (DY * dwpl) + 4 * ((DX + g_hang DX) / 32) + 4 * g_nfw DX DW)
    (g_fw DX) (g_f6 DX SX) (g_f7 SX DW) (g_nfw DX DW =? 0)%Z (g_nolast DX DW) (g_f3 DX SX DW).
Proof.
  intros datad dpixh datas spixh dwpl swpl DX SX DW DY SY DH Hd1 Hd4 Hs1 Hs4 Hdw Hsw Hdph Hsph HDX HSX HDW HXW
    HDY HSY HDH HDYH HSYH Hne Hsm.
  pose proof (Z.mod_pos_bound DX 32 ltac:(lia)) as HDXm.
  pose proof (LeptRop2Arith.g_hang_range DX) as Hh.
  pose proof (LeptRop2Arith.g_sls_range DX SX Hne) as Hsl.
  pose proof (g_dp_hang DX DW HDW) as Edp.
  assert (Hw32 : (DW / 32 <= dwpl)%Z) by (apply Z.div_le_upper_bound; lia).
  assert (Hnfw : (0 <= g_nfw DX DW <= DW / 32)%Z).
  { unfold g_nfw. rewrite Edp. destruct (Z.ltb_spec DW (g_hang DX)).
    - split; [lia | apply Z.div_pos; lia].
    - split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]. }
  assert (Mrow : forall i, (0 <= i < DH)%Z ->
            (0 <= dwpl * i)%Z /\ (dwpl * (DY + i + 1) <= dwpl * dpixh)%Z /\ (0 <= swpl * i)%Z /\ (swpl * (SY + i + 1) <= swpl * spixh)%Z).
  { intros i Hi. split; [apply Z.mul_nonneg_nonneg; lia|]. split; [apply Z.mul_le_mono_nonneg_l; lia|].
    split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]. }
  assert (HDYp : (0 <= DY * dwpl)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (HSYp : (0 <= SY * swpl)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (NDP : g_dp DX DW = false -> (g_hang DX <= DW /\ g_nfw DX DW = (DW - g_hang DX) / 32)%Z).
  { intros Eb. split; [rewrite Edp in Eb; apply Z.ltb_ge in Eb; lia | exact (g_nfw_nodp DX DW Eb)]. }
  unfold rg_geo. split; [|split; [|split; [|split; [|split]]]].
  - repeat split; lia.
  - split; [lia|]. unfold g_fw. destruct (Z.eqb_spec (DX mod 32) 0); cbn [negb]; lia.
  - intros F. apply Z.eqb_neq in F. lia.
  - intros F. pose proof (g_smax_1 DX SX DW swpl Hsm F) as G1. pose proof (g_col1 DX DW dwpl HDX HDW HXW) as C1.
    split; [split; lia|]. intros i Hi. destruct (Mrow i Hi) as (M1 & M2 & M3 & M4).
    destruct (g_f6 DX SX && negb (g_f7 SX DW)); lia.
  - intros F. apply Z.eqb_neq in F.
    assert (Ed : g_dp DX DW = false).
    { destruct (g_dp DX DW) eqn:E; [|reflexivity]. destruct (g_dp_facts DX DW E) as (_ & X & _). contradiction. }
    destruct (NDP Ed) as [Hhw En].
    pose proof (g_col2 DX DW dwpl HDX Hhw HXW) as (C1 & C2 & C3). pose proof (g_smax_2 DX SX DW swpl Hsm F) as G2.
    split; [split; lia|]. intros i Hi. destruct (Mrow i Hi) as (M1 & M2 & M3 & M4). lia.
  - intros F. pose proof (g_smax_3 DX SX DW swpl Hsm F) as G3.
    assert (Ed : g_dp DX DW = false) by (unfold g_nolast in F; destruct (g_dp DX DW); [cbn in F; discriminate F | reflexivity]).
    destruct (NDP Ed) as [Hhw En].
    rewrite (g_nolast_nodp DX DW Ed) in F. apply Z.eqb_neq in F.
    pose proof (g_col3 DX DW dwpl HDX Hhw HXW F) as C3.
    split; [split; lia|]. intros i Hi. destruct (Mrow i Hi) as (M1 & M2 & M3 & M4).
    destruct (g_f3 DX SX DW); lia.
Qed.

Lemma gs_tail : forall (rom : word -> option byte) regs Mq (s datad datas dwpl swpl DX SX DW DY SY op tv : Z),
  (RG_MASKS + 264 <= s - 240)%Z -> (s + 64 < 2 ^ 64)%Z ->
  (0 <= DX < 2 ^ 30)%Z -> (0 <= SX < 2 ^ 30)%Z -> (0 <= DW < 2 ^ 30)%Z -> (g_hang DX <= DW)%Z ->
  (DX mod 32 <> SX mod 32)%Z ->
  (0 <= DY * dwpl < 2 ^ 31)%Z -> (0 <= SY * swpl < 2 ^ 31)%Z -> (1 <= datad)%Z -> (1 <= datas)%Z ->
  (datad + 4 * (DY * dwpl) + 4 * ((DX + g_hang DX) / 32) + 4 * ((DW - g_hang DX) / 32) < 2 ^ 64)%Z ->
  (datas + 4 * (SY * swpl) + 4 * ((SX + g_hang DX) / 32) + 4 * ((DW - g_hang DX) / 32) < 2 ^ 64)%Z ->
  (0 <= swpl < 2 ^ 63)%Z -> (1 <= op <= 14)%Z -> (0 <= tv < 2 ^ 31)%Z -> (tv mod 2 = 0)%Z ->
  rdn SEGS Mq (Z_to_bv 64 (RG_JT + 4 * (op - 1))) 4 = Some (Z_to_le_bytes 4 tv) ->
  store_ok SEGS Mq (Z_to_bv 64 (s - 240)) 240 = true ->
  rdn SEGS Mq (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 8 = Z_to_bv 64 DW -> getr regs 9 = Z_to_bv 64 DW ->
  getr regs 21 = Z_to_bv 64 (g_hang DX) -> getr regs 23 = Z_to_bv 64 (g_hang DX) -> getr regs 13 = Z_to_bv 64 DX ->
  getr regs 24 = Z_to_bv 64 SX -> getr regs 7 = Z_to_bv 64 DY -> getr regs 5 = Z_to_bv 64 SY ->
  getr regs 14 = Z_to_bv 64 dwpl -> getr regs 10 = Z_to_bv 64 datad -> getr regs 19 = Z_to_bv 64 datas ->
  getr regs 20 = Z_to_bv 64 32 -> getr regs 29 = Z_to_bv 64 (g_sls DX SX) -> getr regs 11 = Z_to_bv 64 op ->
  exists regs' MB,
    msteps SEGS (mkst regs RG_Q4 Mq rom) (mkst regs' (Z_to_bv 64 (RG_JT + tv)) MB rom)
    /\ (forall x : word, ~ (s - 232 <= u x < s - 224)%Z -> ~ (s - 216 <= u x < s - 200)%Z -> ~ (s - 144 <= u x < s - 112)%Z -> MB x = Mq x)
    /\ mem_grows Mq MB
    /\ rdn SEGS MB (Z_to_bv 64 (s - 216)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if g_lwb DX DW =? 0 then 1 else 0)))
    /\ rdn SEGS MB (Z_to_bv 64 (s - 208)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if DW - g_hang DX <? 32 then 1 else 0)))
    /\ rdn SEGS MB (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn SEGS MB (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ((DW - g_hang DX) / 32)))
    /\ ((g_lwb DX DW <> 0)%Z ->
          rdn SEGS MB (Z_to_bv 64 (s - 232)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if g_f3 DX SX DW then 1 else 0)))
          /\ rdn SEGS MB (Z_to_bv 64 (s - 136)) 8 =
               Some (word_to_le_bytes 8 (Z_to_bv 64 (datas + 4 * (SY * swpl) + 4 * ((SX + g_hang DX) / 32) + 4 * ((DW - g_hang DX) / 32))))
          /\ exists mk : word, rdn SEGS MB (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 mk))
    /\ getr regs' 8 = Z_to_bv 64 (32 - g_sls DX SX)
    /\ ((32 <= DW - g_hang DX)%Z -> getr regs' 18 = Z_to_bv 64 (datad + 4 * (DY * dwpl) + 4 * ((DX + g_hang DX) / 32))
                              /\ getr regs' 6 = Z_to_bv 64 (datas + 4 * (SY * swpl) + 4 * ((SX + g_hang DX) / 32)))
    /\ ((g_lwb DX DW <> 0)%Z ->
          getr regs' 10 = Z_to_bv 64 (datad + 4 * (DY * dwpl) + 4 * ((DX + g_hang DX) / 32) + 4 * ((DW - g_hang DX) / 32)))
    /\ regs_agree (fun r => In r [5; 6; 7; 8; 9; 10; 12; 13; 16; 17; 18; 20; 22; 23; 28]%list) regs regs'.
Proof.
  intros rom regs Mq s datad datas dwpl swpl DX SX DW DY SY op tv Hmk Hs64 HDX HSX HDW Hhw Hne Hdy Hsy Hd1 Hs1 Hpd Hps
    Hsw Hop Htv Hev Hjt SOK C152 H2 H8 H9 H21 H23 H13 H24 H7 H5 H14 H10 H19 H20 H29 H11.
  assert (HMK : RG_MASKS = 128064%Z) by reflexivity. assert (HJT : RG_JT = 127896%Z) by reflexivity.
  pose proof (LeptRop2Arith.g_hang_range DX) as Hh. pose proof (LeptRop2Arith.g_sls_range DX SX Hne) as Hsl.
  assert (Hq : (0 <= (DW - g_hang DX) / 32 < 2 ^ 25)%Z) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (Hqa : (0 <= (DX + g_hang DX) / 32)%Z) by (apply Z.div_pos; lia).
  assert (Hqs : (0 <= (SX + g_hang DX) / 32)%Z) by (apply Z.div_pos; lia).
  assert (Q4R : exists r4 M4,
    msteps SEGS (mkst regs RG_Q4 Mq rom) (mkst r4 RG_Q5 M4 rom)
    /\ (forall x : word, ~ (s - 216 <= u x < s - 200)%Z -> ~ (s - 144 <= u x < s - 112)%Z -> M4 x = Mq x)
    /\ mem_grows Mq M4
    /\ rdn SEGS M4 (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ((DW - g_hang DX) / 32)))
    /\ rdn SEGS M4 (Z_to_bv 64 (s - 208)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if DW - g_hang DX <? 32 then 1 else 0)))
    /\ getr r4 16 = Z_to_bv 64 0
    /\ ((32 <= DW - g_hang DX)%Z -> getr r4 18 = Z_to_bv 64 (datad + 4 * (DY * dwpl) + 4 * ((DX + g_hang DX) / 32))
                              /\ getr r4 6 = Z_to_bv 64 (datas + 4 * (SY * swpl) + 4 * ((SX + g_hang DX) / 32)))
    /\ regs_agree (fun r => In r [6; 8; 12; 16; 17; 18; 28]%list) regs r4).
  { destruct (Z_le_gt_dec 32 (DW - g_hang DX)) as [FU|NF].
    - destruct (rg_Q4 rom true regs Mq s DX SX DW DY SY dwpl swpl datad datas ltac:(lia) ltac:(lia) HDX HSX HDW Hhw FU
                  ltac:(intros _; repeat split; lia) SOK C152 H2 H8 H21 H23 H13 H24 H7 H5 H14 H10 H19)
        as (r4 & S4 & G16 & G18 & AG4).
      cbv beta iota in S4.
      eexists r4, _. split; [exact S4|].
      split; [intros x X1 X2; gs_out; reflexivity|].
      split; [gs_mg|].
      split; [rdn_chain|].
      split; [replace (DW - g_hang DX <? 32)%Z with false by (symmetry; apply Z.ltb_ge; lia); rdn_chain|].
      split; [exact G16|]. split; [intros _; exact (G18 eq_refl)|]. exact AG4.
    - destruct (rg_Q4 rom false regs Mq s DX SX DW DY SY dwpl swpl datad datas ltac:(lia) ltac:(lia) HDX HSX HDW Hhw
                  ltac:(cbv beta iota; lia) ltac:(intros F; discriminate F) SOK C152 H2 H8 H21 H23 H13 H24 H7 H5 H14 H10 H19)
        as (r4 & S4 & G16 & _ & AG4).
      cbv beta iota in S4.
      eexists r4, _. split; [exact S4|].
      split; [intros x X1 X2; gs_out; reflexivity|].
      split; [gs_mg|].
      split; [replace ((DW - g_hang DX) / 32)%Z with 0%Z by (symmetry; apply Z.div_small; lia); rdn_chain|].
      split; [replace (DW - g_hang DX <? 32)%Z with true by (symmetry; apply Z.ltb_lt; lia); rdn_chain|].
      split; [exact G16|]. split; [intros F; exfalso; lia|]. exact AG4. }
  destruct Q4R as (r4 & M4 & S4 & P4 & GR4 & C128 & C208 & G16 & G186 & AG4).
  carry AG4 H2 (2 : reg) E2. carry AG4 H13 (13 : reg) E13. carry AG4 H9 (9 : reg) E9. carry AG4 H24 (24 : reg) E24.
  carry AG4 H23 (23 : reg) E23. carry AG4 H20 (20 : reg) E20. carry AG4 H29 (29 : reg) E29. carry AG4 H7 (7 : reg) E7.
  carry AG4 H5 (5 : reg) E5. carry AG4 H14 (14 : reg) E14. carry AG4 H10 (10 : reg) E10. carry AG4 H19 (19 : reg) E19.
  carry AG4 H11 (11 : reg) E11.
  assert (SOK4 : store_ok SEGS M4 (Z_to_bv 64 (s - 240)) 240 = true) by (eapply store_ok_mono; [exact GR4 | exact SOK]).
  assert (C152' : rdn SEGS M4 (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)))
    by (apply (gs_rdnN M4 Mq); [lia | lia | intros x Hx; apply P4; lia | exact C152]).
  assert (JT4 : rdn SEGS M4 (Z_to_bv 64 (RG_JT + 4 * (op - 1))) 4 = Some (Z_to_le_bytes 4 tv))
    by (apply (gs_rdnN M4 Mq); [lia | lia | intros x Hx; apply P4; lia | exact Hjt]).
  assert (Q5R : exists r5 M5,
    msteps SEGS (mkst r4 RG_Q5 M4 rom) (mkst r5 RG_Q6 M5 rom)
    /\ (forall x : word, ~ (s - 232 <= u x < s - 224)%Z -> ~ (s - 216 <= u x < s - 208)%Z -> ~ (s - 144 <= u x < s - 128)%Z -> M5 x = M4 x)
    /\ mem_grows M4 M5
    /\ rdn SEGS M5 (Z_to_bv 64 (s - 216)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if g_lwb DX DW =? 0 then 1 else 0)))
    /\ ((g_lwb DX DW <> 0)%Z ->
          rdn SEGS M5 (Z_to_bv 64 (s - 232)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if g_f3 DX SX DW then 1 else 0)))
          /\ rdn SEGS M5 (Z_to_bv 64 (s - 136)) 8 =
               Some (word_to_le_bytes 8 (Z_to_bv 64 (datas + 4 * (SY * swpl) + 4 * ((SX + g_hang DX) / 32) + 4 * ((DW - g_hang DX) / 32))))
          /\ exists mk : word, rdn SEGS M5 (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 mk))
    /\ getr r5 8 = Z_to_bv 64 (32 - g_sls DX SX)
    /\ ((g_lwb DX DW <> 0)%Z ->
          getr r5 10 = Z_to_bv 64 (datad + 4 * (DY * dwpl) + 4 * ((DX + g_hang DX) / 32) + 4 * ((DW - g_hang DX) / 32)))
    /\ regs_agree (fun r => In r [5; 7; 8; 9; 10; 12; 13; 16; 20; 22; 23; 28]%list) r4 r5).
  { destruct (Z.eq_dec (g_lwb DX DW) 0) as [NL|NNL].
    - destruct (rg_Q5 rom true r4 M4 s DX SX DW DY SY dwpl swpl datad datas ((DW - g_hang DX) / 32) (g_sls DX SX)
                  ltac:(lia) ltac:(lia) Hmk HDX HSX HDW Hhw ltac:(lia) ltac:(lia) NL ltac:(intros F; discriminate F)
                  SOK4 C152' C128 E2 E13 E9 E24 E23 G16 E20 E29 E7 E5 E14 E10 E19)
        as (r5 & mk & S5 & F8 & _ & _ & AG5).
      cbv beta iota in S5.
      eexists r5, _. split; [exact S5|].
      split; [intros x X1 X2 X3; gs_out; reflexivity|].
      split; [gs_mg|].
      split; [replace (g_lwb DX DW =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact NL); rdn_chain|].
      split; [intros F; contradiction|].
      split; [exact F8|]. split; [intros F; contradiction|]. exact AG5.
    - destruct (rg_Q5 rom false r4 M4 s DX SX DW DY SY dwpl swpl datad datas ((DW - g_hang DX) / 32) (g_sls DX SX)
                  ltac:(lia) ltac:(lia) Hmk HDX HSX HDW Hhw ltac:(lia) ltac:(lia) NNL ltac:(intros _; repeat split; lia)
                  SOK4 C152' C128 E2 E13 E9 E24 E23 G16 E20 E29 E7 E5 E14 E10 E19)
        as (r5 & mk & S5 & F8 & _ & F10 & AG5).
      cbv beta iota in S5.
      eexists r5, _. split; [exact S5|].
      split; [intros x X1 X2 X3; gs_out; reflexivity|].
      split; [gs_mg|].
      split; [replace (g_lwb DX DW =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact NNL); rdn_chain|].
      split.
      { intros _. split; [|split].
        - replace (if g_f3 DX SX DW then 1 else 0)%Z with (if (32 - g_sls DX SX <? g_lwb DX DW)%Z then 0 else 1)%Z
            by (unfold g_f3; destruct (32 - g_sls DX SX <? g_lwb DX DW)%Z; reflexivity).
          rdn_chain.
        - rdn_chain.
        - exists mk. rdn_chain. }
      split; [exact F8|]. split; [intros _; exact (F10 eq_refl)|]. exact AG5. }
  destruct Q5R as (r5 & M5 & S5 & P5 & GR5 & C216 & C232 & F8 & F10 & AG5).
  carry AG5 E2 (2 : reg) N2. carry AG5 E11 (11 : reg) N11.
  assert (SOK5 : store_ok SEGS M5 (Z_to_bv 64 (s - 240)) 240 = true) by (eapply store_ok_mono; [exact GR5 | exact SOK4]).
  assert (C152'' : rdn SEGS M5 (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)))
    by (apply (gs_rdnN M5 M4); [lia | lia | intros x Hx; apply P5; lia | exact C152']).
  assert (JT5 : rdn SEGS M5 (Z_to_bv 64 (RG_JT + 4 * (op - 1))) 4 = Some (Z_to_le_bytes 4 tv))
    by (apply (gs_rdnN M5 M4); [lia | lia | intros x Hx; apply P5; lia | exact JT4]).
  destruct (rg_Q6g rom r5 M5 s swpl op tv ltac:(lia) ltac:(lia) Hsw Hop Htv Hev JT5 SOK5 C152'' N2 N11) as (r6 & S6 & AG6).
  exists r6, (wbytes M5 (Z_to_bv 64 (s - 120)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  split; [eapply msteps_trans; [exact S4 | eapply msteps_trans; [exact S5 | exact S6]]|].
  split. { intros x X1 X2 X3. gs_out. rewrite P5 by lia. apply P4; lia. }
  split. { eapply mem_grows_trans; [exact GR4 | eapply mem_grows_trans; [exact GR5 | apply wbytes_grows]]. }
  split. { rdn_chain. exact C216. }
  split. { rdn_chain. apply (gs_rdnN M5 M4); [lia | lia | intros x Hx; apply P5; lia | exact C208]. }
  split. { rdn_chain. }
  split. { rdn_chain. apply (gs_rdnN M5 M4); [lia | lia | intros x Hx; apply P5; lia | exact C128]. }
  split.
  { intros F. destruct (C232 F) as (A1 & A2 & mk & A3).
    split; [rdn_chain; exact A1|]. split; [rdn_chain; exact A2|]. exists mk. rdn_chain. exact A3. }
  split. { carry AG6 F8 (8 : reg) T8. exact T8. }
  split.
  { intros F. destruct (G186 F) as (A18 & A6).
    carry AG5 A18 (18 : reg) B18. carry AG6 B18 (18 : reg) D18. carry AG5 A6 (6 : reg) B6. carry AG6 B6 (6 : reg) D6.
    split; assumption. }
  split. { intros F. pose proof (F10 F) as A10. carry AG6 A10 (10 : reg) B10. exact B10. }
  eapply regs_agree_trans; [eapply regs_agree_trans; [regs_agree_weaken AG4 | regs_agree_weaken AG5] | regs_agree_weaken AG6].
Qed.

Theorem rg_setup_W : rg_setup_spec.
Proof.
  unfold rg_setup_spec.
  intros rom regs M s datad dpixh datas spixh dwpl swpl DX SX DW DY SY DH op tv c28 c30 c38 c40 c48 c50
    Hs Hs64 Hd1 Hd2 Hd4 Hs1 Hs2 Hs4 Hdw Hsw Hdph Hsph Hnd Hns HDX HSX HDW HXW HSXW HDY HSY HDH HDYH HSYH
    Hne Hsm Hop Htv Hev Hjt B28 B30 B38 B40 B48 B50 Hrel SOK RDH
    H2 H1 H26 H23 H16 H18 H28 H6 H5 H7 H8 H9 H10 H11 H13 H14 H19 H24 H25 H27.
  assert (HMK : RG_MASKS = 128064%Z) by reflexivity. assert (HJT : RG_JT = 127896%Z) by reflexivity.
  pose proof (Z.mod_pos_bound DX 32 ltac:(lia)) as HDXm. pose proof (Z.mod_pos_bound SX 32 ltac:(lia)) as HSXm.
  pose proof (LeptRop2Arith.g_hang_range DX) as Hh. pose proof (LeptRop2Arith.g_sls_range DX SX Hne) as Hsl.
  assert (HDYd : (0 <= DY * dwpl <= dpixh * dwpl)%Z) by (split; [apply Z.mul_nonneg_nonneg | apply Z.mul_le_mono_nonneg_r]; lia).
  assert (HSYs : (0 <= SY * swpl <= spixh * swpl)%Z) by (split; [apply Z.mul_nonneg_nonneg | apply Z.mul_le_mono_nonneg_r]; lia).
  assert (HDX30 : (DX < 2 ^ 30)%Z) by lia. assert (HSX30 : (SX < 2 ^ 30)%Z) by lia. assert (HDW30 : (DW < 2 ^ 30)%Z) by lia.
  destruct (rg_P0 rom regs M s DX SX ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hne SOK H2 H25 H27) as (r1 & S1 & E1 & E12 & AG1).
  rewrite H6, H1, H26, H16, H28, H18, H23 in S1.
  set (M1 := wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
               (Z_to_bv 64 (s - 152)) (word_to_le_bytes 8 (Z_to_bv 64 swpl)))
               (Z_to_bv 64 (s - 200)) (word_to_le_bytes 8 (Z_to_bv 64 c28)))
               (Z_to_bv 64 (s - 192)) (word_to_le_bytes 8 (Z_to_bv 64 c30)))
               (Z_to_bv 64 (s - 176)) (word_to_le_bytes 8 (Z_to_bv 64 c40)))
               (Z_to_bv 64 (s - 160)) (word_to_le_bytes 8 (Z_to_bv 64 c50)))
               (Z_to_bv 64 (s - 168)) (word_to_le_bytes 8 (Z_to_bv 64 c48)))
               (Z_to_bv 64 (s - 184)) (word_to_le_bytes 8 (Z_to_bv 64 c38))) in S1.
  assert (GR1 : mem_grows M M1) by (unfold M1; gs_mg).
  assert (SOK1 : store_ok SEGS M1 (Z_to_bv 64 (s - 240)) 240 = true) by (eapply store_ok_mono; [exact GR1 | exact SOK]).
  assert (OUT1 : forall x : word, ~ (s - 200 <= u x < s - 144)%Z -> M1 x = M x) by (intros x Hx; unfold M1; gs_out; reflexivity).
  assert (C152 : rdn SEGS M1 (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl))) by (unfold M1; rdn_chain).
  assert (ROWS1 : rg_rows M1 s DH).
  { exists c28, c30, c38, c40, c48, c50. unfold M1. repeat split; try lia; rdn_chain. }
  assert (RD112 : rdn SEGS M1 (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 DH)))
    by (apply (gs_rdnN M1 M); [lia | lia | intros x Hx; apply OUT1; lia | exact RDH]).
  assert (JT1 : rdn SEGS M1 (Z_to_bv 64 (RG_JT + 4 * (op - 1))) 4 = Some (Z_to_le_bytes 4 tv))
    by (apply (gs_rdnN M1 M); [lia | lia | intros x Hx; apply OUT1; lia | exact Hjt]).
  destruct (rg_Q1 rom r1 M1 DX SX ltac:(lia) ltac:(lia) Hne E1 E12)
    as (r2 & S2 & F23 & F21 & F20 & F17 & F29 & F30 & F16 & F15 & AG2).
  assert (AG12 : regs_agree (fun r => In r [1; 6; 12; 15; 16; 17; 20; 21; 23; 29; 30; 31]%list) regs r2)
    by (eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2]).
  carry AG2 E1 (1 : reg) K1. carry AG2 E12 (12 : reg) K12.
  carry AG12 H2 (2 : reg) K2. carry AG12 H8 (8 : reg) K8. carry AG12 H9 (9 : reg) K9. carry AG12 H13 (13 : reg) K13.
  carry AG12 H24 (24 : reg) K24. carry AG12 H7 (7 : reg) K7. carry AG12 H5 (5 : reg) K5. carry AG12 H14 (14 : reg) K14.
  carry AG12 H10 (10 : reg) K10. carry AG12 H19 (19 : reg) K19. carry AG12 H11 (11 : reg) K11.
  carry AG12 H25 (25 : reg) K25. carry AG12 H27 (27 : reg) K27.
  assert (K3 : getr r2 3 = getr regs 3) by exact (AG12 3 ltac:(notin_list)).
  assert (K4 : getr r2 4 = getr regs 4) by exact (AG12 4 ltac:(notin_list)).
  assert (FIN : exists regs1 MB,
    msteps SEGS (mkst regs RG_P0 M rom) (mkst regs1 (Z_to_bv 64 (RG_JT + tv)) MB rom)
    /\ (forall a : word, ~ (s - 240 <= u a < s - 112)%Z -> MB a = M a) /\ mem_grows M MB
    /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4
    /\ rg_cells MB s DH swpl (g_nfw DX DW) (datas + 4 * (SY * swpl) + 4 * ((SX + g_hang DX) / 32) + 4 * g_nfw DX DW)
         (g_fw DX) (g_f6 DX SX) (g_nfw DX DW =? 0)%Z (g_nolast DX DW) (g_f3 DX SX DW)
    /\ rg_regs regs1 s (DX mod 32) dwpl (g_sls DX SX)
         (datas + 4 * (SY * swpl) + 4 * (SX / 32)) (datad + 4 * (DY * dwpl) + 4 * (DX / 32))
         (datas + 4 * (SY * swpl) + 4 * ((SX + g_hang DX) / 32)) (datad + 4 * (DY * dwpl) + 4 * ((DX + g_hang DX) / 32))
         (datad + 4 * (DY * dwpl) + 4 * ((DX + g_hang DX) / 32) + 4 * g_nfw DX DW)
         (g_fw DX) (g_f7 SX DW) (g_nfw DX DW =? 0)%Z (g_nolast DX DW)).
  { destruct (Z.eq_dec (DX mod 32) 0) as [FW0|FW1].
    - assert (Efw : g_fw DX = false) by (unfold g_fw; rewrite FW0; reflexivity).
      assert (Ehang : g_hang DX = 0%Z) by (apply g_fw_hang; exact Efw).
      assert (Edp : g_dp DX DW = false) by (unfold g_dp; rewrite FW0; reflexivity).
      assert (Hhw : (g_hang DX <= DW)%Z) by lia.
      destruct (rg_Q3b rom r2 M1 DX ltac:(lia) FW0 K1) as (r3 & S3 & G15 & G25 & G21 & G27 & AG3).
      assert (L21 : getr r3 21 = Z_to_bv 64 (g_hang DX)) by (rewrite Ehang; exact G21).
      carry AG3 K2 (2 : reg) L2. carry AG3 K8 (8 : reg) L8. carry AG3 K9 (9 : reg) L9. carry AG3 F23 (23 : reg) L23.
      carry AG3 K13 (13 : reg) L13. carry AG3 K24 (24 : reg) L24. carry AG3 K7 (7 : reg) L7. carry AG3 K5 (5 : reg) L5.
      carry AG3 K14 (14 : reg) L14. carry AG3 K10 (10 : reg) L10. carry AG3 K19 (19 : reg) L19. carry AG3 F20 (20 : reg) L20.
      carry AG3 F29 (29 : reg) L29. carry AG3 K11 (11 : reg) L11. carry AG3 K1 (1 : reg) L1. carry AG3 F30 (30 : reg) L30.
      carry AG3 K3 (3 : reg) L3. carry AG3 K4 (4 : reg) L4.
      destruct (gs_tail rom r3 M1 s datad datas dwpl swpl DX SX DW DY SY op tv ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  Hhw Hne ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hop Htv Hev JT1 SOK1 C152
                  L2 L8 L9 L21 L23 L13 L24 L7 L5 L14 L10 L19 L20 L29 L11)
        as (r4 & MB & S4 & PRES & GR4 & C216 & C208 & C120 & C128 & C232 & T8 & T186 & T10 & AG4).
      exists r4, MB.
      split; [eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact S2 | eapply msteps_trans; [exact S3 | exact S4]]]|].
      split; [intros a Ha; rewrite PRES by lia; apply OUT1; lia|].
      split; [eapply mem_grows_trans; [exact GR1 | exact GR4]|].
      split; [carry AG4 L3 (3 : reg) N3; exact N3|]. split; [carry AG4 L4 (4 : reg) N4; exact N4|].
      split.
      { unfold rg_cells. rewrite (g_nolast_nodp DX DW Edp), <- (nofull_flag DX DW Edp Hhw), (g_nfw_nodp DX DW Edp).
        split; [exact C216|]. split; [exact C208|].
        split; [apply (gs_rdnN MB M1); [lia | lia | intros x Hx; apply PRES; lia | exact C152]|].
        split; [exact C120|].
        split; [apply (gs_rdnN MB M1); [lia | lia | intros x Hx; apply PRES; lia | exact RD112]|].
        split; [intros _; apply (gs_rows_agree MB M1); [lia | lia | intros x Hx; apply PRES; lia | exact ROWS1]|].
        split; [intros F; rewrite Efw in F; discriminate F|].
        split; [intros _; exact C128|].
        split; [intros F; apply Z.eqb_neq in F; exact (proj1 (C232 F))|].
        split; [intros F; apply Z.eqb_neq in F; exact (proj1 (proj2 (C232 F)))|].
        intros F; apply Z.eqb_neq in F; exact (proj2 (proj2 (C232 F))). }
      { unfold rg_regs. rewrite (g_nolast_nodp DX DW Edp), <- (nofull_flag DX DW Edp Hhw), (g_nfw_nodp DX DW Edp).
        carry AG4 L2 (2 : reg) N2. carry AG4 L1 (1 : reg) N1. carry AG4 L14 (14 : reg) N14. carry AG4 L30 (30 : reg) N30.
        split; [exact N2|]. split; [exact N1|]. split; [exact N14|]. split; [exact N30|]. split; [exact T8|].
        split; [intros F; rewrite Efw in F; discriminate F|].
        split; [intros F; apply Z.ltb_ge in F; destruct (T186 F) as [A B]; split; assumption|].
        intros F; apply Z.eqb_neq in F; exact (T10 F). }
    - assert (Efw : g_fw DX = true) by (unfold g_fw; apply negb_true_iff, Z.eqb_neq; exact FW1).
      assert (Ehang : g_hang DX = (32 - DX mod 32)%Z) by (unfold g_hang; rewrite (proj2 (Z.eqb_neq _ _) FW1); reflexivity).
      destruct (rg_Q2 rom r2 M1 s DX SX DW DY SY dwpl swpl datad datas ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FW1
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOK1 C152
                  K2 K1 F21 K12 F17 K9 K25 K27 K7 K5 K14 K10 K19 F16 F15)
        as (r3 & S3 & G25 & G15 & G26 & AG3).
      set (M2 := wbytes M1 (Z_to_bv 64 (s - 224)) (word_to_le_bytes 8 (Z_to_bv 64 (if g_f6 DX SX then 1 else 0)))) in S3.
      assert (GR2 : mem_grows M1 M2) by (unfold M2; apply wbytes_grows).
      assert (SOK2 : store_ok SEGS M2 (Z_to_bv 64 (s - 240)) 240 = true) by (eapply store_ok_mono; [exact GR2 | exact SOK1]).
      assert (OUT2 : forall x : word, ~ (s - 224 <= u x < s - 216)%Z -> M2 x = M1 x) by (intros x Hx; unfold M2; gs_out; reflexivity).
      assert (C152b : rdn SEGS M2 (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)))
        by (apply (gs_rdnN M2 M1); [lia | lia | intros x Hx; apply OUT2; lia | exact C152]).
      assert (RD112b : rdn SEGS M2 (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 DH)))
        by (apply (gs_rdnN M2 M1); [lia | lia | intros x Hx; apply OUT2; lia | exact RD112]).
      assert (JT2 : rdn SEGS M2 (Z_to_bv 64 (RG_JT + 4 * (op - 1))) 4 = Some (Z_to_le_bytes 4 tv))
        by (apply (gs_rdnN M2 M1); [lia | lia | intros x Hx; apply OUT2; lia | exact JT1]).
      assert (ROWS2 : rg_rows M2 s DH) by (apply (gs_rows_agree M2 M1); [lia | lia | intros x Hx; apply OUT2; lia | exact ROWS1]).
      assert (C224 : rdn SEGS M2 (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if g_f6 DX SX then 1 else 0))))
        by (unfold M2; rdn_chain).
      carry AG3 K2 (2 : reg) L2. carry AG3 K8 (8 : reg) L8. carry AG3 K9 (9 : reg) L9. carry AG3 F23 (23 : reg) L23.
      carry AG3 K13 (13 : reg) L13. carry AG3 K24 (24 : reg) L24. carry AG3 K7 (7 : reg) L7. carry AG3 K5 (5 : reg) L5.
      carry AG3 K14 (14 : reg) L14. carry AG3 K10 (10 : reg) L10. carry AG3 K19 (19 : reg) L19. carry AG3 F20 (20 : reg) L20.
      carry AG3 F29 (29 : reg) L29. carry AG3 K11 (11 : reg) L11. carry AG3 K1 (1 : reg) L1. carry AG3 F30 (30 : reg) L30.
      carry AG3 K3 (3 : reg) L3. carry AG3 K4 (4 : reg) L4. carry AG3 F21 (21 : reg) L21.
      destruct (Z_lt_le_dec DW (32 - DX mod 32)) as [DP|NDP].
      + assert (Edp : g_dp DX DW = true)
          by (unfold g_dp; rewrite (proj2 (Z.eqb_neq _ _) FW1); cbn [negb andb]; apply Z.ltb_lt; exact DP).
        destruct (g_dp_facts DX DW Edp) as (_ & Enfw & Enl & _).
        rewrite Enfw, Enl. replace (0 =? 0)%Z with true by reflexivity.
        destruct (rg_Q3 rom r3 M2 s DX SX DW ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) FW1 DP Hne SOK2
                    L2 L8 L9 L13 L21 L20 L29)
          as (r4 & S4 & G8 & G10 & AG4).
        set (M3 := wbytes (wbytes (wbytes (wbytes M2
                     (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                     (Z_to_bv 64 (s - 208)) (word_to_le_bytes 8 (Z_to_bv 64 1)))
                     (Z_to_bv 64 (s - 216)) (word_to_le_bytes 8 (Z_to_bv 64 1)))
                     (Z_to_bv 64 (s - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0))) in S4.
        assert (GR3 : mem_grows M2 M3) by (unfold M3; do 4 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
        assert (SOK3 : store_ok SEGS M3 (Z_to_bv 64 (s - 240)) 240 = true) by (eapply store_ok_mono; [exact GR3 | exact SOK2]).
        assert (OUT3 : forall x : word, ~ (s - 216 <= u x < s - 200)%Z -> ~ (s - 136 <= u x < s - 120)%Z -> M3 x = M2 x)
          by (intros x X1 X2; unfold M3; gs_out; reflexivity).
        assert (C152c : rdn SEGS M3 (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)))
          by (apply (gs_rdnN M3 M2); [lia | lia | intros x Hx; apply OUT3; lia | exact C152b]).
        assert (JT3 : rdn SEGS M3 (Z_to_bv 64 (RG_JT + 4 * (op - 1))) 4 = Some (Z_to_le_bytes 4 tv))
          by (apply (gs_rdnN M3 M2); [lia | lia | intros x Hx; apply OUT3; lia | exact JT2]).
        carry AG4 L2 (2 : reg) N2. carry AG4 L11 (11 : reg) N11.
        destruct (rg_Q6g rom r4 M3 s swpl op tv ltac:(lia) ltac:(lia) ltac:(lia) Hop Htv Hev JT3 SOK3 C152c N2 N11)
          as (r5 & S5 & AG5).
        exists r5, (wbytes M3 (Z_to_bv 64 (s - 120)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
        assert (OUTF : forall x : word, ~ (s - 216 <= u x < s - 200)%Z -> ~ (s - 136 <= u x < s - 112)%Z ->
                         wbytes M3 (Z_to_bv 64 (s - 120)) (word_to_le_bytes 8 (Z_to_bv 64 0)) x = M2 x)
          by (intros x X1 X2; rewrite wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia); apply OUT3; lia).
        split; [eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact S2 | eapply msteps_trans; [exact S3 |
                eapply msteps_trans; [exact S4 | exact S5]]]]|].
        split; [intros a Ha; rewrite OUTF by lia; rewrite OUT2 by lia; apply OUT1; lia|].
        split; [eapply mem_grows_trans; [exact GR1 | eapply mem_grows_trans; [exact GR2 |
                eapply mem_grows_trans; [exact GR3 | apply wbytes_grows]]]|].
        split; [carry AG4 L3 (3 : reg) N3; carry AG5 N3 (3 : reg) P3; exact P3|].
        split; [carry AG4 L4 (4 : reg) N4; carry AG5 N4 (4 : reg) P4; exact P4|].
        split.
        { unfold rg_cells.
          split; [unfold M3; rdn_chain|]. split; [unfold M3; rdn_chain|].
          split; [apply (gs_rdnN _ M2); [lia | lia | intros x Hx; apply OUTF; lia | exact C152b]|].
          split; [rdn_chain|].
          split; [apply (gs_rdnN _ M2); [lia | lia | intros x Hx; apply OUTF; lia | exact RD112b]|].
          split; [intros _; apply (gs_rows_agree _ M2); [lia | lia | intros x Hx; apply OUTF; lia | exact ROWS2]|].
          split; [intros _; apply (gs_rdnN _ M2); [lia | lia | intros x Hx; apply OUTF; lia | exact C224]|].
          split; [intros F; discriminate F|].
          split; [intros F; discriminate F|]. split; [intros F; discriminate F|]. intros F; discriminate F. }
        { unfold rg_regs.
          carry AG4 L1 (1 : reg) N1. carry AG4 L14 (14 : reg) N14. carry AG4 L30 (30 : reg) N30.
          carry AG4 G15 (15 : reg) N15. carry AG4 G25 (25 : reg) N25. carry AG4 G26 (26 : reg) N26.
          carry AG5 N2 (2 : reg) P2. carry AG5 N1 (1 : reg) P1. carry AG5 N14 (14 : reg) P14. carry AG5 N30 (30 : reg) P30.
          carry AG5 G8 (8 : reg) P8. carry AG5 N15 (15 : reg) P15. carry AG5 N25 (25 : reg) P25. carry AG5 N26 (26 : reg) P26.
          split; [exact P2|]. split; [exact P1|]. split; [exact P14|]. split; [exact P30|]. split; [exact P8|].
          split; [intros _; split; [exact P15 | split; [exact P25 | exact P26]]|].
          split; [intros F; discriminate F|]. intros F; discriminate F. }
      + assert (Edp : g_dp DX DW = false)
          by (unfold g_dp; rewrite (proj2 (Z.eqb_neq _ _) FW1); cbn [negb andb]; apply Z.ltb_ge; lia).
        assert (Hhw : (g_hang DX <= DW)%Z) by lia.
        destruct (rg_Q3n rom r3 M2 DX DW ltac:(lia) ltac:(lia) NDP L9 L21) as (r4 & S4 & AG4).
        assert (L21' : getr r3 21 = Z_to_bv 64 (g_hang DX)) by (rewrite Ehang; exact L21).
        carry AG4 L2 (2 : reg) N2. carry AG4 L8 (8 : reg) N8. carry AG4 L9 (9 : reg) N9. carry AG4 L21' (21 : reg) N21.
        carry AG4 L23 (23 : reg) N23. carry AG4 L13 (13 : reg) N13. carry AG4 L24 (24 : reg) N24. carry AG4 L7 (7 : reg) N7.
        carry AG4 L5 (5 : reg) N5. carry AG4 L14 (14 : reg) N14. carry AG4 L10 (10 : reg) N10. carry AG4 L19 (19 : reg) N19.
        carry AG4 L20 (20 : reg) N20. carry AG4 L29 (29 : reg) N29. carry AG4 L11 (11 : reg) N11. carry AG4 L1 (1 : reg) N1.
        carry AG4 L30 (30 : reg) N30. carry AG4 L3 (3 : reg) N3. carry AG4 L4 (4 : reg) N4.
        carry AG4 G15 (15 : reg) N15. carry AG4 G25 (25 : reg) N25. carry AG4 G26 (26 : reg) N26.
        destruct (gs_tail rom r4 M2 s datad datas dwpl swpl DX SX DW DY SY op tv ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    Hhw Hne ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hop Htv Hev JT2 SOK2 C152b
                    N2 N8 N9 N21 N23 N13 N24 N7 N5 N14 N10 N19 N20 N29 N11)
          as (r5 & MB & S5 & PRES & GR5 & C216 & C208 & C120 & C128 & C232 & T8 & T186 & T10 & AG5).
        exists r5, MB.
        split; [eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact S2 | eapply msteps_trans; [exact S3 |
                eapply msteps_trans; [exact S4 | exact S5]]]]|].
        split; [intros a Ha; rewrite PRES by lia; rewrite OUT2 by lia; apply OUT1; lia|].
        split; [eapply mem_grows_trans; [exact GR1 | eapply mem_grows_trans; [exact GR2 | exact GR5]]|].
        split; [carry AG5 N3 (3 : reg) P3; exact P3|]. split; [carry AG5 N4 (4 : reg) P4; exact P4|].
        split.
        { unfold rg_cells. rewrite (g_nolast_nodp DX DW Edp), <- (nofull_flag DX DW Edp Hhw), (g_nfw_nodp DX DW Edp).
          split; [exact C216|]. split; [exact C208|].
          split; [apply (gs_rdnN MB M2); [lia | lia | intros x Hx; apply PRES; lia | exact C152b]|].
          split; [exact C120|].
          split; [apply (gs_rdnN MB M2); [lia | lia | intros x Hx; apply PRES; lia | exact RD112b]|].
          split; [intros _; apply (gs_rows_agree MB M2); [lia | lia | intros x Hx; apply PRES; lia | exact ROWS2]|].
          split; [intros _; apply (gs_rdnN MB M2); [lia | lia | intros x Hx; apply PRES; lia | exact C224]|].
          split; [intros _; exact C128|].
          split; [intros F; apply Z.eqb_neq in F; exact (proj1 (C232 F))|].
          split; [intros F; apply Z.eqb_neq in F; exact (proj1 (proj2 (C232 F)))|].
          intros F; apply Z.eqb_neq in F; exact (proj2 (proj2 (C232 F))). }
        { unfold rg_regs. rewrite (g_nolast_nodp DX DW Edp), <- (nofull_flag DX DW Edp Hhw), (g_nfw_nodp DX DW Edp).
          carry AG5 N2 (2 : reg) P2. carry AG5 N1 (1 : reg) P1. carry AG5 N14 (14 : reg) P14. carry AG5 N30 (30 : reg) P30.
          carry AG5 N15 (15 : reg) P15. carry AG5 N25 (25 : reg) P25. carry AG5 N26 (26 : reg) P26.
          split; [exact P2|]. split; [exact P1|]. split; [exact P14|]. split; [exact P30|]. split; [exact T8|].
          split; [intros _; split; [exact P15 | split; [exact P25 | exact P26]]|].
          split; [intros F; apply Z.ltb_ge in F; destruct (T186 F) as [A B]; split; assumption|].
          intros F; apply Z.eqb_neq in F; exact (T10 F). } }
  destruct FIN as (regs1 & MB & RUN & OUT & GR & R3 & R4 & CELLS & REGS).
  exists regs1, MB, (DX mod 32)%Z, (g_sls DX SX), (g_nfw DX DW),
    (datas + 4 * (SY * swpl) + 4 * (SX / 32))%Z, (datad + 4 * (DY * dwpl) + 4 * (DX / 32))%Z,
    (datas + 4 * (SY * swpl) + 4 * ((SX + g_hang DX) / 32))%Z, (datad + 4 * (DY * dwpl) + 4 * ((DX + g_hang DX) / 32))%Z,
    (datas + 4 * (SY * swpl) + 4 * ((SX + g_hang DX) / 32) + 4 * g_nfw DX DW)%Z,
    (datad + 4 * (DY * dwpl) + 4 * ((DX + g_hang DX) / 32) + 4 * g_nfw DX DW)%Z,
    (g_fw DX), (g_f6 DX SX), (g_f7 SX DW), (g_nfw DX DW =? 0)%Z, (g_nolast DX DW), (g_f3 DX SX DW).
  split; [exact RUN|]. split; [exact OUT|]. split; [exact GR|]. split; [exact R3|]. split; [exact R4|].
  split; [apply gs_geo; lia|]. split; [exact CELLS | exact REGS].
Qed.

End GenSetup.
