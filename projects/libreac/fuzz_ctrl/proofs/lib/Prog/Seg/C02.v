(* Segment C02 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13cc0, 0x13cf0]. classify != 0: K13cc0 -> K13d0c.
   classify = 0: the branches #87-#89 (q.src begins 00 40 ab, CLS C1.8) are not taken, then bcmp(q.src, our, 6):
   K13cc0 -> K13cf4.
   libreac v1.9.0 (table 5a S_C02: IDENTICAL-RENUMBER, OLD 0x13c90 .. 0x13cc0): pcs, q.src 1676 .. 1678 ->
   1692 .. 1694, our 60 -> 76, q 1672 -> 1688, frame 1920 -> 1936; cuts K13c90 -> K13cc0, K13cc4 -> K13cf4,
   K13cdc -> K13d0c (SlotInv.v's renames), so seg_C02 is stated on the renamed cuts. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Exec Step Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse RcClassify SlotModel SlotInv
  reac_ctrl_classify_box_frame_c bcmp_c bcmp_ro_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b8 Tac_b8m Tac_b8c.
Import ListNotations.
Open Scope Z_scope.

(* classify != 0 (a0 = -1): the jump to 0x13d0c. *)
Lemma kC02n : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  x10 = Z_to_bv 64 (-1) ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                           x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13d0c) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13cc0) fc None m ro).
Proof.
  intros. subst x10. step.
  first [ if_cases HC; [first [apply evt_done; reflexivity | b8c_bad HC] | first [apply evt_done; reflexivity | b8c_bad HC]]
        | apply evt_done; reflexivity ].
Qed.

(* classify = 0: q.src = 00 40 ab c9 c10 c11 at sp+1692; bcmp(sp+1692, sp+76, 6) returns v. *)
Lemma kC02c : bcmp_ro_contract -> forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (sp0 : Z) (c9 c10 c11 : byte) (rs : list byte) (v : Z),
  x2 = Z_to_bv 64 sp0 -> x10 = Z_to_bv 64 0 -> 0 <= sp0 -> sp0 + 1936 < 2 ^ 64 ->
  bytes_at rsegs m (sp0 + 1692) [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] ->
  bytes_at rsegs m (sp0 + 76) rs ->
  memcmp_model [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11] rs 6 = Some v ->
  MemNorm.ro_agree rsegs m ->
  Exec.evt rsegs
    (fun ms' => exists R pc' m', ms' = MS R F pc' fc None m' (seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x13cf4 /\ getr R 10 = Z_to_bv 64 v /\
        getr R 2 = Z_to_bv 64 sp0 /\ getr R 3 = x3 /\ getr R 4 = x4 /\ getr R 9 = x9 /\
        getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\ getr R 21 = x21 /\ getr R 22 = x22 /\
        getr R 23 = x23 /\ getr R 26 = x26 /\ getr R 27 = x27 /\
        munch [] m m' /\ wmono rsegs m m' /\ MemNorm.ro_agree rsegs m'))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13cc0) fc None m (seg_rom rsegs)).
Proof.
  intros BCMPC x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m sp0 c9 c10 c11 rs v E2 E10 H0 H1 HL HR HM HRO.
  subst x2 x10.
  pose proof (bytes_at_ov_read rsegs m _ _ 0 1 HL ltac:(cbn; lia)) as R0.
  pose proof (bytes_at_ov_read rsegs m _ _ 1 1 HL ltac:(cbn; lia)) as R1.
  pose proof (bytes_at_ov_read rsegs m _ _ 2 1 HL ltac:(cbn; lia)) as R2.
  cbn [firstn skipn] in R0, R1, R2.
  replace (sp0 + 1692 + Z.of_nat 0) with (sp0 + 1692) in R0 by lia.
  replace (sp0 + 1692 + Z.of_nat 1) with (sp0 + 1693) in R1 by lia.
  replace (sp0 + 1692 + Z.of_nat 2) with (sp0 + 1694) in R2 by lia.
  step. b8c_nt.
  step. step. b8c_nt.
  step. step. step. b8c_nt.
  step. step. step. b8c_nt.
  step. step. step. step.
  eapply evt_cut.
  { eapply BCMPC with (ls := [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11]) (rs := rs) (v := v).
    - rewrite unsigned_lit by lia. exact HL.
    - rewrite unsigned_lit by lia. exact HR.
    - rewrite (unsigned_lit 6) by lia. exact HM.
    - exact HRO. }
  intros ms' (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & MU & WM & RO & _ & _).
  subst ms'. apply evt_done. eexists _, _, _. split; [reflexivity|].
  split; [apply b8_ret_pc; lia|].
  repeat (split; [reflexivity|]). split; [exact MU|]. split; [exact WM | exact RO].
Qed.

Section C02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis BCMPC : bcmp_ro_contract.

Lemma seg_C02 : forall j : nat, Hat B APIf ra (Inv_K13cf4_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13d0c_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13cc0_at B APIf ra empty) j.
Proof.
  intros j Hcc4 Hcdc g c (phi & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP (HCC & (HB1 & HB2) & H10).
  pose proof (b8_FR_sp B APIf ra empty g _ L A regs mem md HF) as (Hsp & H16 & HSK & HS47).
  pose proof alloc_ceiling_value as HAC.
  unfold rg in H10.
  destruct (b8_cls_r (t_cls (g_in g) j)) as [Er|Er]; rewrite Er in H10.
  - (* classify = 0 *)
    destruct (b8_cls_none_r _ Er) as (e & Ecl).
    pose proof (b8_cls_B (g_in g) j e Ecl) as EB.
    pose proof (b8_cls_oui (g_in g) j e Ecl) as (O6 & O7 & O8).
    set (g50 := t_g (g_in g) j) in *.
    set (lsc := [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; cp_b g50 9; cp_b g50 10; cp_b g50 11]).
    assert (Els : firstn 6 (skipn 4 (t_B (g_in g) j)) = lsc).
    { rewrite EB, b8_struct_src. unfold lsc.
      rewrite (b8c_cp_b _ _ _ O6), (b8c_cp_b _ _ _ O7), (b8c_cp_b _ _ _ O8) by lia. reflexivity. }
    assert (HLs : bytes_at rsegs mem (g_S g - 1936 + 1692) lsc).
    { rewrite <- Els.
      replace (g_S g - 1936 + 1692) with (spk g 1688 + Z.of_nat 4) by (unfold spk, fsp, SLOT_FRAME; lia).
      apply (b8_ba_sub rsegs mem _ _ 4 6 HB1). rewrite b8_B_length. lia. }
    pose proof HCC as ((HFT & _) & _). pose proof HFT as (_ & _ & _ & _ & _ & HO & _).
    assert (HRs : bytes_at rsegs mem (g_S g - 1936 + 76) (OUR (g_in g))).
    { replace (g_S g - 1936 + 76) with (spk g 76) by (unfold spk, fsp, SLOT_FRAME; lia). exact HO. }
    assert (Hlsc : length lsc = 6%nat) by reflexivity.
    destruct (memcmp_model_total lsc (OUR (g_in g)) 6 ltac:(lia) ltac:(rewrite OUR_length; lia)) as (v & Hv).
    destruct (b8_mm_spec 6 lsc (OUR (g_in g)) v Hlsc (OUR_length _) Hv) as [Hiff Hvr].
    pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & HMR & _).
    unfold MI in HMI. rewrite (b8_segs B APIf ra empty FF) in HMI.
    destruct (b8_md B APIf L A mem md HMR) as [Hh Hz].
    eapply (kb_run B regs (Z_to_bv 64 0x13cc0) mem md _ (Post B APIf ra g) Hh Hz).
    { rewrite (b8_segs B APIf ra empty FF). unfold rmk.
      eapply (kC02c BCMPC) with (sp0 := g_S g - 1936) (c9 := cp_b g50 9) (c10 := cp_b g50 10) (c11 := cp_b g50 11)
        (rs := OUR (g_in g)) (v := v);
        [exact Hsp | exact H10 | lia | lia | exact HLs | exact HRs | exact Hv | exact HMI]. }
    intros R pc' m' regs' (Epc & E10 & E2 & E3 & E4 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E26 & E27 &
      MU & WM & RO) HG.
    subst pc'. apply Hcc4. exists phi.
    assert (MUw : forall W, munch W mem m') by (intros W x _; apply MU; exact I).
    apply (b8_cut_close B APIf ra empty _ _ _ _ L A).
    + apply (b8_FR_frame B APIf ra empty FF g _ L A regs' mem md m').
      * apply (b8_FR_regs B APIf ra empty _ _ _ _ _ _ _ _ HF).
        -- rewrite HG, E2. symmetry. exact Hsp.
        -- rewrite HG, E3. reflexivity.
        -- rewrite HG, E4. reflexivity.
      * exact HP.
      * apply MUw.
      * exact WM.
    + exact HP.
    + split; [|split; [split|split]].
      * pose proof HCC as (HC7 & H23).
        split.
        -- apply (b8_CC7_munch g j phi regs' mem m' []); [| apply MUw | intros; exact I].
           apply (b8_CC7_regs _ _ _ regs); [exact HC7 | rewrite HG; assumption ..].
        -- unfold V7, rg in *. rewrite HG, E23. exact H23.
      * apply (b8_ba_munch rsegs [] mem m' _ _ HB1 MU). intros; exact I.
      * apply (b8_ba_munch rsegs [] mem m' _ _ HB2 MU). intros; exact I.
      * rewrite Ecl. discriminate.
      * rewrite HG, E10. rewrite (b8_lit0 v Hvr), Els. exact Hiff.
  - (* classify != 0: a0 = -1 *)
    eapply (b8_run_to B APIf ra empty FF); [exact HF | unfold rmk; apply kC02n; exact H10 |].
    intros regs' HG. apply Hcdc. exists phi. apply (b8_cut_close B APIf ra empty _ _ _ _ L A).
    + apply (b8_FR_regs B APIf ra empty _ _ _ _ _ _ _ _ HF); b8rg HG.
    + exact HP.
    + apply (b8_CC_regs _ _ _ regs); [exact HCC | b8rg HG ..].
Qed.

End C02.
