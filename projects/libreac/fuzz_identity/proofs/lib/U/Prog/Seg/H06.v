From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Tac_si.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Exec Step Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI KindBGlue MemNorm.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uhj.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Ltac bveq := apply bv_eq; unfold notw in *; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
  change (Z.of_N 64) with 64; unfold spk, fsp, SLOT_FRAME in *; Z.div_mod_to_equations; lia.

Ltac ltu_off := lazymatch goal with |- context [bv_ltu ?a ?b] =>
  replace (bv_ltu a b) with false by (symmetry; unfold bv_ltu, notw; apply Z.ltb_ge; rewrite ?Z_to_bv_unsigned;
    unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64; unfold spk, fsp, SLOT_FRAME in *;
    Z.div_mod_to_equations; lia) end; br_if.

Ltac rg HG := rewrite HG; greg2; first [reflexivity | f_equal; unfold spk, fsp, SLOT_FRAME in *; lia | bveq].

Section H06.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma seg_H06 : Hcut B APIf ra (Inv_U13bc8 B APIf ra empty) -> Hcut B APIf ra (Inv_U13b98 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_U13bc8, Inv_U13bc8_at. exists 0, nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (HN1 & E8 & E10 & HB & HE).
  pose proof HN1 as (HNB & E27 & HSTP & HQ216 & HW4).
  pose proof HNB as (HID & HW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOU).
  pose proof (stem_addr_cases g) as HSA.
  pose proof (n_stem_len (g_in g)) as L16.
  destruct (nzb_W4 _ HW) as [NZW LW].
  pose proof (Tac_si.nzb_nth _ 0 NZW ltac:(lia)) as NZ.
  pose proof (bz_range (RcIdentModel.nthb (n_W4 (g_in g)) 0)) as BR.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HB) as HBn. unfold spk, fsp, SLOT_FRAME in HBn.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HW4) as HW4n. unfold spk, fsp, SLOT_FRAME in HW4n.
  pose proof (cstr_byte _ _ _ 0 HW4n ltac:(lia)) as RD. rewrite Z.add_0_r in RD.
  rewrite Tac_si.nthb_snoc_lt in RD by lia.
  set (a := g_S g - 384 + 242 + Z.of_nat (length (n_stem (g_in g)))).
  unfold zlen in E8. unfold rmk, Frame.mkR. rewrite E2, E8, E10.
  step. ltu_off.
  step. step. rewrite Tac_si.zxb_bz.
  step. step.
  pose proof (st_ok g (normalize rsegs mem) a 1 HWR0 ltac:(unfold a; lia) ltac:(unfold a; lia)) as HSO.
  step.
  change (le1 (Z_to_bv 64 45)) with [dash].
  change (Z_to_bv 64 a) with (wa a).
  pose proof (Frame.munch_write [(a, a + 1)] (normalize rsegs mem) (normalize rsegs mem) a [dash] (Frame.munch_refl _ _)
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia) ltac:(cbn; lia)) as MU1.
  pose proof (Frame.munch_write (SWIN g) (normalize rsegs mem) (normalize rsegs mem) a [dash] (Frame.munch_refl _ _)
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia) ltac:(unfold SWIN, SLOT_K, SLOT_STACK; cbn; unfold a; lia)) as MUS.
  pose proof (Frame.wmono_write rsegs (normalize rsegs mem) (normalize rsegs mem) (wa a) [dash] (Frame.wmono_refl _ _))
    as WM1.
  pose proof (Frame.stk_write rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g) a [dash] HSTK0
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia)) as STK1.
  pose proof (bytes_at_snoc (normalize rsegs mem) (g_S g - 384 + 242) _ dash HBn ltac:(lia)) as HB1.
  fold a in HB1.
  remember (write_to_mem (normalize rsegs mem) (wa a) [dash]) as m1 eqn:Em1.
  step. step.
  rewrite bv_eqb_lit by lia.
  replace (RcIdentModel.bz (RcIdentModel.nthb (n_W4 (g_in g)) 0) =? 0) with false
    by (symmetry; apply Z.eqb_neq; exact NZ).
  br_if.
  step. step. step. step.
  rewrite ?not_lit by lia.
  apply (fin_mem g mem regs 0x13bc8 _ _ m1 MUS WM1 STK1); [rewrite E2; reflexivity | reflexivity | reflexivity |].
  intros R' m' HG HREL. cbv beta.
  assert (KMm : KM [(a, a + 1)] mem m') by exact (KM_of _ mem m1 m' HRO MU1 HREL).
  assert (HO : OUTS g nm tk dp m')
    by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m1 m' HFR HPM MUS HREL HOU).
  assert (D1 : disjoint_from [(a, a + 1)] (spk g 146) 38) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D2 : disjoint_from [(a, a + 1)] (spk g 56) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D3 : disjoint_from [(a, a + 1)] (spk g 48) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D4 : disjoint_from [(a, a + 1)] (spk g 24) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D5 : disjoint_from [(a, a + 1)] (stem_addr g) (zlen (n_stem (g_in g)) + 1))
    by (cbn; unfold zlen, spk, fsp, SLOT_FRAME, a in *; lia).
  assert (D6 : disjoint_from [(a, a + 1)] (spk g 216) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D7 : disjoint_from [(a, a + 1)] (spk g 192) 5) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
  - apply (N1_keep g nm tk dp regs mem R' m' _ HN1 KMm HO D1 D2 D3 D4 D5 D6 D7); kr HG.
  - rg HG.
  - rg HG.
  - exact HE.
  - lia.
  - apply (fin_bytes m' m1 _ _ HREL). unfold spk, fsp, SLOT_FRAME. cbn [Z.to_nat firstn app]. exact HB1.
  - rg HG.
  - rg HG.
  - unfold zlen. rg HG.
  - unfold zlen. rg HG.
  - rg HG.
  - rg HG.
Qed.

End H06.
