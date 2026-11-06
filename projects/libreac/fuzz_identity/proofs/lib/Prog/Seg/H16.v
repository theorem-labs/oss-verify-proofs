From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Exec Step Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue MemNorm.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv memchr_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sh2.
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Lemma find_dash_none : forall l, has_dash l = false -> find_byte 45 l = None.
Proof.
  unfold has_dash. induction l as [|b l IH]; intros H; [reflexivity|].
  cbn [existsb] in H. apply orb_false_iff in H as [H1 H2].
  cbn [find_byte]. unfold RcIdentModel.bz in H1. rewrite H1, (IH H2). reflexivity.
Qed.

Lemma find_dash_some : forall l, has_dash l = true -> exists i, find_byte 45 l = Some i.
Proof.
  unfold has_dash. induction l as [|b l IH]; intros H; [discriminate|].
  cbn [existsb] in H. cbn [find_byte]. unfold RcIdentModel.bz in H.
  destruct (bv_unsigned b =? 45); [exists 0%nat; reflexivity|].
  cbn [orb] in H. destruct (IH H) as (i & E). rewrite E. exists (S i). reflexivity.
Qed.

Lemma firstn_cstr : forall (l : list byte), firstn (Z.to_nat (Z.of_nat (length l))) (l ++ [z8]) = l.
Proof. intros l. rewrite Nat2Z.id, firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Section H16.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MEMCHR : memchr_contract.

Lemma seg_H16 : Hcut B APIf ra (Inv_K13ac8 B APIf ra empty) -> Hcut B APIf ra (Inv_K13af4 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13aac B APIf ra empty).
Proof.
  intros H8 H4 g c (nm & tk & dp & HC).
  eapply (seg_go2 B APIf ra empty FF); [exact H8 | exact H4 | | | exact HC | ].
  { intros c' HC'. unfold Inv_K13ac8. exists nm, tk, dp. exact HC'. }
  { intros c' HC'. unfold Inv_K13af4. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (HBB & HDP & E8 & E27 & E10).
  pose proof HBB as (HNC & E9 & E18 & HLD).
  pose proof HNC as ((HID & HW & E20 & E21 & E22 & E23 & E24 & E25 & HCD & HOU) & E26 & E19 & HROW & HNM).
  destruct (ld_bounds (g_in g) HW) as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (caps_range (g_in g)) as (C1 & C2 & C3 & C4 & C5 & C6).
  pose proof E10 as E10'. unfold spk, fsp, SLOT_FRAME in E10'.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HDP) as HDPn. unfold spk, fsp, SLOT_FRAME in HDPn.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HNM) as HNMn. unfold cstr, spk, fsp, SLOT_FRAME in HNMn.
  set (a := g_S g - 368 + 48 + ld2 (g_in g) + 5).
  assert (Ea : a = g_S g - 368 + 48 + Z.of_nat (length (n_EXP_DP (g_in g)))) by (unfold a, n_ld in *; lia).
  unfold rmk, Frame.mkR. rewrite E2, E10', E26, E24.
  pose proof (st_ok g (normalize rsegs mem) a 1 HWR0 ltac:(unfold a; lia) ltac:(unfold a; lia)) as HSO.
  step.
  try change (le1 (Z_to_bv 64 0)) with [z8].
  pose proof (Mem.mem_inv_store rsegs (normalize rsegs mem) (wa a) [z8] HMI0 HSO) as HMI1.
  pose proof (Frame.munch_write [(a, a + 1)] (normalize rsegs mem) (normalize rsegs mem) a [z8] (Frame.munch_refl _ _)
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia) ltac:(cbn; lia)) as MU1.
  pose proof (Frame.munch_write (SWIN g) (normalize rsegs mem) (normalize rsegs mem) a [z8] (Frame.munch_refl _ _)
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia) ltac:(unfold SWIN, SLOT_K, SLOT_STACK; cbn; unfold a; lia)) as MUS.
  pose proof (Frame.wmono_write rsegs (normalize rsegs mem) (normalize rsegs mem) (wa a) [z8] (Frame.wmono_refl _ _))
    as WM1.
  pose proof (Frame.stk_write rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g) a [z8] HSTK0
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia)) as STK1.
  pose proof (bytes_at_snoc (normalize rsegs mem) (g_S g - 368 + 48) (n_EXP_DP (g_in g)) z8 HDPn
    ltac:(unfold n_ld in *; lia)) as HDP1.
  rewrite <- Ea in HDP1.
  pose proof (Mem.bytes_at_write_other rsegs (normalize rsegs mem) a [z8] (g_S g - 368 + 226) _ HNMn
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia) ltac:(cbn; unfold a; right; lia)) as HNM1.
  change (Z_to_bv 64 a) with (wa a).
  remember (write_to_mem (normalize rsegs mem) (wa a) [z8]) as m1 eqn:Em1.
  assert (D1 : disjoint_from [(a, a + 1)] (spk g 130) 38) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D2 : disjoint_from [(a, a + 1)] (spk g 40) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D3 : disjoint_from [(a, a + 1)] (spk g 32) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D4 : disjoint_from [(a, a + 1)] (spk g 226) (n_ln (g_in g) + 1))
    by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  step. step.
  rewrite bv_ltu_lit by lia.
  destruct (Z.ltb_spec (n_ln (g_in g)) (t_cap_name (g_in g))) as [HLT|HGE]; cbn [negb].
  - step. step. step. step.
    eapply Exec.evt_cut.
    { eapply MEMCHR with (buf := n_EXP_NM (g_in g) ++ [z8]).
      - rewrite MState.unsigned_lit by lia. exact HNM1.
      - rewrite !MState.unsigned_lit by lia. unfold memchr_ok. change (45 mod 256) with 45.
        unfold n_ln. rewrite firstn_cstr. rewrite length_app. cbn [length].
        destruct (find_byte 45 (n_EXP_NM (g_in g))); [left|]; lia.
      - exact HMI1. }
    intros ms' PO. destruct PO as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' &
      -> & MU & WM & _ & _).
    rewrite (MState.ret_pc_even 0x13ac8) by (lia || reflexivity).
    assert (MUa : Frame.munch [(a, a + 1)] (normalize rsegs mem) m')
      by (apply (Frame.munch_trans _ _ m1 m'); [exact MU1 | apply (Frame.munch_weaken []); [intros x _; exact I |
          exact MU]]).
    assert (MUb : Frame.munch (SWIN g) (normalize rsegs mem) m')
      by (apply (Frame.munch_trans _ _ m1 m'); [exact MUS | apply (Frame.munch_weaken []); [intros x _; exact I |
          exact MU]]).
    assert (STK2 : Frame.stk rsegs m' (g_S g - 65536) (g_S g))
      by (apply (Frame.stk_transport rsegs [] m1 m' _ _ STK1 MU WM); intros x _; left; exact I).
    apply (fin_l g mem regs _ _ _ _ _ m' MUb (Frame.wmono_trans _ _ _ _ WM1 WM) STK2);
      [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m'' HG HREL. cbv beta.
    assert (KMm : KM [(a, a + 1)] mem m'') by exact (KM_of _ mem m' m'' HRO MUa HREL).
    assert (HO : OUTS g nm tk dp m'')
      by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m' m'' HFR HPM MUb HREL HOU).
    assert (R10 : YK11.getr R' 10 = Z_to_bv 64 (memchr_res (g_S g - 368 + 226) 45 (n_ln (g_in g))
      (n_EXP_NM (g_in g) ++ [z8]))).
    { rewrite HG. greg2. rewrite !MState.unsigned_lit by lia. reflexivity. }
    unfold memchr_res, n_ln in R10. rewrite firstn_cstr in R10.
    split; [|split; [exact HLT|split]].
    + unfold H17b. split; [|split; [|split; [|split; [|split]]]].
      * apply (NC_keep g nm tk dp regs mem R' m'' _ HNC KMm HO D1 D2 D3 D4); rewrite HG;
          first [reflexivity | rewrite E26; reflexivity | rewrite E24; reflexivity].
      * rewrite HG. exact E9.
      * rewrite HG. exact E9.
      * rewrite HG. exact E8.
      * rewrite HG. exact E27.
      * apply (fin_bytes m'' m' _ _ HREL). unfold cstr, spk, fsp, SLOT_FRAME.
        apply (Frame.bytes_at_transport rsegs [] m1 m' _ _ HDP1 MU). exact I.
    + intros Hd. destruct (find_dash_some _ Hd) as (i & Ei). rewrite R10, Ei.
      destruct (find_byte_Some _ _ _ Ei) as (Hi & _). unfold n_ln in B1.
      intros E. apply (f_equal bv_unsigned) in E. rewrite !MState.unsigned_lit in E by lia. lia.
    + intros Hd. rewrite R10, (find_dash_none _ Hd). reflexivity.
  - apply (fin_r g mem regs _ _ _ _ _ m1 MUS WM1 STK1); [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m'' HG HREL. cbv beta.
    assert (KMm : KM [(a, a + 1)] mem m'') by exact (KM_of _ mem m1 m'' HRO MU1 HREL).
    assert (HO : OUTS g nm tk dp m'')
      by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m1 m'' HFR HPM MUS HREL HOU).
    split; [|exact HGE].
    unfold H17b. split; [|split; [|split; [|split; [|split]]]].
    + apply (NC_keep g nm tk dp regs mem R' m'' _ HNC KMm HO D1 D2 D3 D4); rewrite HG;
        first [reflexivity | rewrite E26; reflexivity | rewrite E24; reflexivity].
    + rewrite HG. exact E9.
    + rewrite HG. exact E9.
    + rewrite HG. exact E8.
    + rewrite HG. exact E27.
    + apply (fin_bytes m'' m1 _ _ HREL). unfold cstr, spk, fsp, SLOT_FRAME. exact HDP1.
Qed.

End H16.
