(* Segment C03 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13cf4, 0x13d34], two entry cuts.
   K13cf4 (classify = 0): the branches #90 (q.src != our), #91 (TF = 1) and #92 (0 <= ev <= 5) are not taken
   (CLS C1.8), then the run joins K13d0c at 0x13d0c.
   K13d0c: k != 9 or Φ[16 .. 18) != cd ea -> K13d7c (want_m = 0); else reac_box_catalogue(sp+1824) -> K13d38.
   libreac v1.9.0 (table 5a S_C03: IDENTICAL-RENUMBER, OLD 0x13cc4 .. 0x13d04): pcs, TF 48 -> 24 (type_filler),
   ev 1668 -> 1684, the catalogue count 1808 -> 1824, frame 1920 -> 1936; the catalogue address is
   reac_box_catalogue_c's BOX_CATALOGUE (by name); cuts K13cc4 -> K13cf4, K13cdc -> K13d0c, K13d08 -> K13d38,
   K13d4c -> K13d7c (SlotInv.v's renames), so seg_C03 is stated on the renamed cuts. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse RcClassify SlotModel SlotInv
  reac_ctrl_classify_box_frame_c reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b8 Tac_b8m Tac_b8c.
Import ListNotations.
Open Scope Z_scope.

(* K13cf4 -> 0x13d0c: a0 = bcmp != 0, TF = 1 at sp+24, ev = e in 0 .. 5 at sp+1684. *)
Lemma kC03a : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp0 e : Z),
  x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 1936 < 2 ^ 64 ->
  bv_eqb x10 (Z_to_bv 64 0) = false -> bv_unsigned x10 <> 0 ->
  ov_read_bytes rsegs m (wa (sp0 + 24)) 8 = Some (le8 (Z_to_bv 64 1)) ->
  ov_read_bytes rsegs m (wa (sp0 + 1684)) 4 = Some (le4 (Z_to_bv 64 e)) -> 0 <= e <= 5 ->
  Exec.evt rsegs
    (fun ms' => exists R pc' m', ms' = MS R F pc' fc None m' (seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x13d0c /\ m' = m /\ getr R 2 = Z_to_bv 64 sp0 /\ getr R 3 = x3 /\ getr R 4 = x4 /\
        getr R 9 = x9 /\ getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\ getr R 21 = x21 /\
        getr R 22 = x22 /\ getr R 23 = x23 /\ getr R 26 = x26 /\ getr R 27 = x27))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13cf4) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m sp0 e E2 H0 H1 Hne Hne2 R24 R84 He.
  subst x2.
  assert (He' : e = 0 \/ e = 1 \/ e = 2 \/ e = 3 \/ e = 4 \/ e = 5) by lia.
  destruct He' as [->|[->|[->|[->|[->| ->]]]]];
    (step; b8c_nt; step; step; b8c_nt; step; step; step; b8c_nt;
     apply evt_done; eexists _, _, _; split; [reflexivity|];
     repeat (split; [reflexivity|]); reflexivity).
Qed.

(* K13d0c, k != 9: the jump to 0x13d7c. *)
Lemma kC03n : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (k : Z),
  x23 = Z_to_bv 64 k -> 0 <= k <= 13 -> k <> 9 ->
  Exec.evt rsegs
    (fun ms' => exists y, ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
                                  x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13d7c) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13d0c) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro k E23 Hk Hk9.
  subst x23. step. step.
  first [ if_cases HC; [first [apply evt_done; eexists; reflexivity | b8c_bad HC]
                      | first [apply evt_done; eexists; reflexivity | b8c_bad HC]]
        | apply evt_done; eexists; reflexivity ].
Qed.

(* K13d0c, k = 9 and Φ[16 .. 18) != cd ea: the jump to 0x13d7c. *)
Lemma kC03f : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z)
    (b16 b17 : byte),
  x23 = Z_to_bv 64 9 -> x21 = Z_to_bv 64 phi -> 0 <= phi -> phi + 18 <= 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [b16] -> ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [b17] ->
  bv_unsigned b16 <> 205 \/ (bv_unsigned b16 = 205 /\ bv_unsigned b17 <> 234) ->
  Exec.evt rsegs
    (fun ms' => exists R pc' m', ms' = MS R F pc' fc None m' (seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x13d7c /\ m' = m /\ getr R 2 = x2 /\ getr R 3 = x3 /\ getr R 4 = x4 /\
        getr R 9 = x9 /\ getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\ getr R 21 = x21 /\
        getr R 22 = x22 /\ getr R 23 = x23 /\ getr R 26 = x26 /\ getr R 27 = x27))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13d0c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m phi b16 b17 E23 E21 Hp0 Hp1 R16 R17 Hx.
  subst x23 x21. pose proof (b8c_byte_range b16). pose proof (b8c_byte_range b17).
  step. step. b8c_nt.
  step. step. step.
  destruct Hx as [H16|[H16 H17]].
  - b8c_tk.
    apply evt_done. eexists _, _, _. split; [reflexivity|]. repeat (split; [reflexivity|]). reflexivity.
  - b8c_nt.
    step. step. step.
    b8c_tk.
    apply evt_done. eexists _, _, _. split; [reflexivity|]. repeat (split; [reflexivity|]). reflexivity.
Qed.

(* K13d0c, k = 9 and Φ[16 .. 18) = cd ea: c = 0 at sp+1824, then reac_box_catalogue(sp+1824). *)
Lemma kC03c : reac_box_catalogue_contract -> forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
    x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp0 phi : Z) (b16 b17 : byte) (ob : list byte),
  x2 = Z_to_bv 64 sp0 -> x23 = Z_to_bv 64 9 -> x21 = Z_to_bv 64 phi ->
  0 <= sp0 -> sp0 mod 16 = 0 -> sp0 + 1936 < 2 ^ 64 -> 0 <= phi -> phi + 18 <= 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [b16] -> ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [b17] ->
  bv_unsigned b16 = 205 -> bv_unsigned b17 = 234 ->
  rw_cells rsegs m (sp0 + 1824) [CB 8 ob] ->
  Exec.evt rsegs
    (fun ms' => exists R pc' m', ms' = MS R F pc' fc None m' (seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x13d38 /\ getr R 10 = Z_to_bv 64 BOX_CATALOGUE /\
        getr R 2 = Z_to_bv 64 sp0 /\ getr R 3 = x3 /\ getr R 4 = x4 /\ getr R 9 = x9 /\
        getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\ getr R 21 = x21 /\ getr R 22 = x22 /\
        getr R 23 = x23 /\ getr R 26 = x26 /\ getr R 27 = x27 /\
        munch [(sp0 + 1824, sp0 + 1832)] m m' /\ wmono rsegs m m' /\
        bytes_at rsegs m' (sp0 + 1824) (le8 (Z_to_bv 64 11))))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13d0c) fc None m (seg_rom rsegs)).
Proof.
  intros CATC x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m sp0 phi b16 b17 ob E2 E23 E21 Hs0 H16 Hs1 Hp0 Hp1 R16 R17 E16 E17 HO.
  subst x2 x23 x21. pose proof (b8c_byte_range b16). pose proof (b8c_byte_range b17).
  pose proof (munch_refl [(sp0 + 1824, sp0 + 1832)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. b8c_nt.
  step. step. step. b8c_nt.
  step. step. step. b8c_nt.
  step. step. step.
  eapply evt_cut.
  { eapply CATC with (c := sp0 + 1824).
    - first [reflexivity | f_equal; lia].
    - right. split; [Z.div_mod_to_equations; lia|].
      match goal with H : rw_cells rsegs _ (sp0 + 1824) [C8 _] |- _ => exact (b8c_c8_wr _ _ _ H) end. }
  intros ms' (a1' & m' & E & Hc). subst ms'.
  replace (sp0 + 1824 =? 0) with false in Hc by (symmetry; apply Z.eqb_neq; lia).
  destruct Hc as (BA & MUc & WMc & _).
  rewrite (b8_ret_pc 0x13d38) by lia.
  apply evt_done. eexists _, _, _. split; [reflexivity|].
  repeat (split; [reflexivity|]).
  match goal with MU0 : munch _ m ?m0, WM0 : wmono rsegs m ?m0 |- _ =>
    split; [eapply munch_trans; [exact MU0 | eapply munch_weaken; [|exact MUc]]; b8c_sub|];
    split; [exact (wmono_trans _ _ _ _ WM0 WMc) | exact BA]
  end.
Qed.

Section C03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CATC : reac_box_catalogue_contract.

Lemma seg_C03 : forall j : nat,
  Hat B APIf ra (Inv_K13d38_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13d7c_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13cf4_at B APIf ra empty) j /\ Hat B APIf ra (Inv_K13d0c_at B APIf ra empty) j.
Proof.
  intros j H08 H4c.
  assert (Hcdc : Hat B APIf ra (Inv_K13d0c_at B APIf ra empty) j).
  { intros g c (phi & HC).
    eapply (b8_cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP HCC.
    pose proof HCC as (HC7 & H23).
    pose proof HC7 as ((Hj & H26 & (H27 & H32 & H20) & H21 & HBphi & HO & HM7) & H18 & HVC & HI).
    pose proof (b8_FR_sp B APIf ra empty g _ L A regs mem md HF) as (Hsp & H16 & HSK & HS47).
    pose proof alloc_ceiling_value as HAC.
    pose proof (b8c_k_range (g_in g) j) as Hk.
    assert (Hin : In (phi, t_len (g_in g) j) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
    destruct (b8_block_pos B APIf ra empty g _ L A regs mem md _ _ HF Hin) as [Hph1 Hph2].
    unfold V7, rg in H23.
    pose proof HF as (_ & _ & _ & _ & _ & HSTK & HMI & _ & HMR & _).
    unfold SLOT_K, SLOT_STACK in *.
    destruct (b8_md B APIf L A mem md HMR) as [Hh Hz].
    assert (K4c : forall regs', getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 ->
        getr regs' 4 = getr regs 4 -> getr regs' 18 = getr regs 18 ->
        getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 ->
        getr regs' 22 = getr regs 22 -> getr regs' 26 = getr regs 26 -> getr regs' 27 = getr regs 27 ->
        t_rowsel (g_in g) j = false ->
        SR (ms_segs B) (mkCfg (mkst regs' (Z_to_bv 64 0x13d7c) mem (seg_rom (ms_segs B))) md) (Post B APIf ra g)).
    { intros regs' E2 E3 E4 E18 E19 E20 E21 E22 E26 E27 Hrs. apply H4c. exists phi.
      apply (b8_cut_close B APIf ra empty _ _ _ _ L A).
      - exact (b8_FR_regs B APIf ra empty _ _ _ _ _ _ _ _ HF E2 E3 E4).
      - exact HP.
      - split; [exact (b8_CC7_regs _ _ _ regs regs' mem HC7 E18 E19 E20 E21 E22 E26 E27)|].
        unfold t_want_m. rewrite Hrs. reflexivity. }
    destruct (Z.eq_dec (t_k (g_in g) j) 9) as [Ek|Ek].
    - (* k = 9: the tests of Φ[16] = 0xcd and Φ[17] = 0xea *)
      assert (Hbig : 50 <= t_len (g_in g) j) by (apply b8c_k_big; lia).
      pose proof (b8_phi_length (g_in g) j) as Hpl.
      set (ph := t_phi (g_in g) j) in *.
      assert (R16 : ov_read_bytes rsegs mem (wa (phi + 16)) 1 = Some [nth 16 ph cp_z]).
      { rewrite <- (b8c_firstn1 ph 16 cp_z) by lia.
        exact (bytes_at_ov_read rsegs mem phi ph 16 1 HBphi ltac:(lia)). }
      assert (R17 : ov_read_bytes rsegs mem (wa (phi + 17)) 1 = Some [nth 17 ph cp_z]).
      { rewrite <- (b8c_firstn1 ph 17 cp_z) by lia.
        exact (bytes_at_ov_read rsegs mem phi ph 17 1 HBphi ltac:(lia)). }
      assert (C16 : cp_v (t_g (g_in g) j) 16 = bv_unsigned (nth 16 ph cp_z)).
      { unfold cp_v, cp_b, ph. rewrite b8_g_nth by lia. reflexivity. }
      assert (C17 : cp_v (t_g (g_in g) j) 17 = bv_unsigned (nth 17 ph cp_z)).
      { unfold cp_v, cp_b, ph. rewrite b8_g_nth by lia. reflexivity. }
      assert (H23' : getr regs 23 = Z_to_bv 64 9) by (rewrite H23, Ek; reflexivity).
      destruct (Z.eq_dec (bv_unsigned (nth 16 ph cp_z)) 205) as [E16|E16];
        [destruct (Z.eq_dec (bv_unsigned (nth 17 ph cp_z)) 234) as [E17|E17]|].
      + (* cd ea: the catalogue call *)
        destruct (sl_rw_of_stk mem (g_S g - 65536) (g_S g) (g_S g - 1936 + 1824) 8 HSTK ltac:(lia) ltac:(lia))
          as (ob & HOB).
        eapply (kb_run B regs (Z_to_bv 64 0x13d0c) mem md _ (Post B APIf ra g) Hh Hz).
        { rewrite (b8_segs B APIf ra empty FF). unfold rmk.
          eapply (kC03c CATC) with (sp0 := g_S g - 1936) (phi := phi) (ob := ob);
            [exact Hsp | exact H23' | exact H21 | lia | exact H16 | lia | lia | lia | exact R16 | exact R17
            | exact E16 | exact E17 | exact HOB]. }
        intros R pc' m' regs' (Epc & E10 & E2 & E3 & E4 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E26 & E27 &
          MU & WM & BA) HG.
        subst pc'. apply H08. exists phi.
        apply (b8_cut_close B APIf ra empty _ _ _ _ L A).
        * apply (b8_FR_frame B APIf ra empty FF g _ L A regs' mem md m').
          -- apply (b8_FR_regs B APIf ra empty _ _ _ _ _ _ _ _ HF).
             ++ rewrite HG, E2. symmetry. exact Hsp.
             ++ rewrite HG, E3. reflexivity.
             ++ rewrite HG, E4. reflexivity.
          -- exact HP.
          -- eapply munch_weaken; [|exact MU]. unfold SLOT_K, SLOT_STACK. b8c_sub.
          -- exact WM.
        * exact HP.
        * split; [|split; [|split]].
          -- split.
             ++ apply (b8_CC7_munch g j phi regs' mem m' [(g_S g - 1936 + 1824, g_S g - 1936 + 1832)]);
                  [| exact MU |].
                ** apply (b8_CC7_regs _ _ _ regs); [exact HC7 | rewrite HG; assumption ..].
                ** intros x Hx'. unfold spk, fsp, SLOT_FRAME in Hx'. b8c_out.
             ++ unfold V7, rg. rewrite HG, E23. exact H23.
          -- unfold t_rowsel. rewrite Ek, C16, C17, E16, E17. reflexivity.
          -- unfold rg, CAT. rewrite HG, E10. reflexivity.
          -- unfold q64, CAT_N.
             replace (spk g 1824) with (g_S g - 1936 + 1824) by (unfold spk, fsp, SLOT_FRAME; lia). exact BA.
      + (* cd, not ea *)
        eapply (kb_run B regs (Z_to_bv 64 0x13d0c) mem md _ (Post B APIf ra g) Hh Hz).
        { rewrite (b8_segs B APIf ra empty FF). unfold rmk.
          eapply kC03f with (phi := phi);
            [exact H23' | exact H21 | lia | lia | exact R16 | exact R17 | right; split; [exact E16 | exact E17]]. }
        intros R pc' m' regs' (Epc & Em & E2 & E3 & E4 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E26 & E27) HG.
        subst pc' m'. apply K4c; [rewrite HG; assumption .. |].
        unfold t_rowsel. rewrite Ek, C16, C17, E16, (proj2 (Z.eqb_neq _ _) E17). reflexivity.
      + (* not cd *)
        eapply (kb_run B regs (Z_to_bv 64 0x13d0c) mem md _ (Post B APIf ra g) Hh Hz).
        { rewrite (b8_segs B APIf ra empty FF). unfold rmk.
          eapply kC03f with (phi := phi);
            [exact H23' | exact H21 | lia | lia | exact R16 | exact R17 | left; exact E16]. }
        intros R pc' m' regs' (Epc & Em & E2 & E3 & E4 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E26 & E27) HG.
        subst pc' m'. apply K4c; [rewrite HG; assumption .. |].
        unfold t_rowsel. rewrite Ek, C16, (proj2 (Z.eqb_neq _ _) E16). reflexivity.
    - (* k != 9 *)
      eapply (b8_run_ex B APIf ra empty FF); [exact HF | unfold rmk; eapply kC03n with (k := t_k (g_in g) j);
        [exact H23 | lia | exact Ek] |].
      intros y regs' HG. apply K4c; [b8rg HG .. |].
      unfold t_rowsel. rewrite (proj2 (Z.eqb_neq _ _) Ek). reflexivity. }
  split; [|exact Hcdc].
  intros g c (phi & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP (HCC & (HB1 & HB2) & Hcl & Hiff).
  assert (Hcl' : exists e, t_cls (g_in g) j = Some e)
    by (destruct (t_cls (g_in g) j) as [e|]; [exists e; reflexivity | contradiction]).
  destruct Hcl' as (e & Ecl).
  pose proof (b8_cls_k (g_in g) j e Ecl) as (_ & _ & He).
  pose proof (b8_cls_src (g_in g) j e Ecl) as Hsrc.
  pose proof (b8_cls_TF (g_in g) j e Ecl) as HTF.
  pose proof HCC as (HC7 & H23).
  pose proof HC7 as (_ & _ & (_ & HT & _) & _).
  pose proof (b8_FR_sp B APIf ra empty g _ L A regs mem md HF) as (Hsp & H16 & HSK & HS47).
  pose proof alloc_ceiling_value as HAC.
  assert (Hne : getr regs 10 <> Z_to_bv 64 0) by (intros E; apply Hsrc; apply Hiff; exact E).
  assert (Hne' : bv_eqb (getr regs 10) (Z_to_bv 64 0) = false).
  { unfold bv_eqb. apply Z.eqb_neq. intros E. apply Hne. apply bv_eq. exact E. }
  assert (Hne2 : bv_unsigned (getr regs 10) <> 0).
  { intros E. apply Hne. apply bv_eq. rewrite E. rewrite unsigned_lit by lia. reflexivity. }
  assert (R24 : ov_read_bytes rsegs mem (wa (g_S g - 1936 + 24)) 8 = Some (le8 (Z_to_bv 64 1))).
  { replace (g_S g - 1936 + 24) with (spk g 24) by (unfold spk, fsp, SLOT_FRAME; lia).
    apply b8_bytes_le8. unfold q64 in HT. rewrite HTF in HT. exact HT. }
  assert (R84 : ov_read_bytes rsegs mem (wa (g_S g - 1936 + 1684)) 4 = Some (le4 (Z_to_bv 64 e))).
  { replace (g_S g - 1936 + 1684) with (spk g 1684) by (unfold spk, fsp, SLOT_FRAME; lia).
    apply b8_bytes_le4. rewrite Ecl in HB2. exact HB2. }
  pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & HMR & _).
  destruct (b8_md B APIf L A mem md HMR) as [Hh Hz].
  eapply (kb_run B regs (Z_to_bv 64 0x13cf4) mem md _ (Post B APIf ra g) Hh Hz).
  { rewrite (b8_segs B APIf ra empty FF). unfold rmk.
    eapply kC03a with (sp0 := g_S g - 1936) (e := e);
      [exact Hsp | lia | lia | exact Hne' | exact Hne2 | exact R24 | exact R84 | lia]. }
  intros R pc' m' regs' (Epc & Em & E2 & E3 & E4 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E26 & E27) HG.
  subst pc' m'. apply Hcdc. exists phi.
  apply (b8_cut_close B APIf ra empty _ _ _ _ L A).
  - apply (b8_FR_regs B APIf ra empty _ _ _ _ _ _ _ _ HF).
    + rewrite HG, E2. symmetry. exact Hsp.
    + rewrite HG, E3. reflexivity.
    + rewrite HG, E4. reflexivity.
  - exact HP.
  - apply (b8_CC_regs _ _ _ regs); [exact HCC | rewrite HG; assumption ..].
Qed.

End C03.
