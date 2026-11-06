(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module names changed; 256 of its 289 lines of code are new or changed and 363 lines of the source are left out. *)
(* Segment F26 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): 0x825f4-0x82600, through the call.
   0x825f4 mv s4,a0 (s4 = unk, the first count); 0x825f8 mv a0,s6 (a0 = blk = phi + 18); 0x825fc li a1,0;
   0x82600 jal reac_ports_unknown@0x87848.  The callee is composed on its lib/A contract
   (reac_ports_unknown_c.v, a Section Hypothesis) and the segment lands at 0x82604 with a0 = the same count
   (same block, no byte written: a1 = 0).  The run writes only the callee's 16-byte stack window, so every
   carried byte fact, FRA and ENT survive it (F24's b7_fra_run / b7_ent_run).  Plain twin: plain/Q03.v. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib
  reac_ports_unknown_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs B7Cuts F24.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module RL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcLeaf.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcPorts.

Section F26.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PU : reac_ports_unknown_contract.

(* 0x825f4 -> 0x82604 on explicit registers: two moves, a0 = blk, a1 = 0, and the call. *)
Lemma f26_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi uk lo : Z) (bs : list byte),
    sp = Z_to_bv 64 spv -> s6 = Z_to_bv 64 (phi + 18) -> a0 = Z_to_bv 64 uk ->
    0 < phi -> phi + 50 <= 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    stk rsegs m lo spv -> lo + 16 <= spv ->
    length bs = 20%nat -> bytes_at rsegs m (phi + 18) bs ->
    (phi + 38 <= spv - 16 \/ spv <= phi + 18) ->
    asan_cells m -> shadow_rw m -> addressable m (phi + 18) 20 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(spv - 16, spv)] x) ->
    LE.evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (if RP.pu_decl bs then 4 * RP.pu_nunk bs 12 else -1))
                       (Z_to_bv 64 0) a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 uk) s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x82604) fc None m' (seg_rom rsegs) /\
         munch [(spv - 16, spv)] m m' /\ wmono rsegs m m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x825f4) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m spv phi uk lo bs -> -> -> Hphi1 Hphi2 Hspv Hstk Hlo Hlen Hbs Hdjp HAC HSW HADp HOUT.
  assert (Hspu : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  step. step. step. step.
  eapply evt_cut.
  { eapply PU with (p := phi + 18) (c := 0) (bs := bs) (lo := lo).
    - first [rewrite MState.unsigned_lit by lia; lia | reflexivity].
    - first [rewrite MState.unsigned_lit by lia; lia | reflexivity].
    - rewrite Hspu. exact Hstk.
    - rewrite Hspu. unfold REAC_PORTS_UNKNOWN_FRAME. lia.
    - intros _. split; [lia|]. split; [exact Hlen|]. split; [exact Hbs|].
      rewrite Hspu. unfold REAC_PORTS_UNKNOWN_FRAME. lia.
    - intros HC. exfalso. apply HC. reflexivity.
    - exact HAC.
    - exact HSW.
    - intros HC. exfalso. apply HC. reflexivity.
    - intros _. exact HADp.
    - intros x Hx. unfold reac_ports_unknown_W. rewrite Hspu. cbn [Z.eqb app].
      unfold REAC_PORTS_UNKNOWN_FRAME. exact (HOUT x Hx). }
  intros ms' (a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & m' & -> & MUc & WMc & STc & _ & _).
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ ?pcx _ _ _ _) =>
      replace pcx with (Z_to_bv 64 0x82604)
        by (symmetry; first [ rewrite ?MState.ret_pc_fold; apply MState.ret_pc_even; lia
                            | apply bv_eq; vm_compute; reflexivity
                            | vm_compute; reflexivity ])
  end.
  assert (Eok : RP.pu_ok (phi + 18) bs = RP.pu_decl bs) by (apply b7_pu_ok; lia).
  rewrite Eok.
  apply evt_done.
  eexists _, _, _, _, _, _, _, _, _, _, m'. split; [reflexivity|].
  split; [|exact WMc].
  unfold reac_ports_unknown_W in MUc. rewrite Hspu in MUc. cbn [Z.eqb app] in MUc.
  unfold REAC_PORTS_UNKNOWN_FRAME in MUc. exact MUc.
Qed.

Lemma seg_F26 : forall j : nat, Hat B APIf ra (Inv_A82604_at B APIf ra) j ->
  Hat B APIf ra (Inv_A825f4_at B APIf ra) j.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hjle & HHB & HFLSI & HK & Hs9 & Ha0 &
    HPORTS & HFIRST & HADq & HADf).
  subst c. rewrite SEGS.
  pose proof (b7_asize_flen g j phi fr regs mem HK) as Hasz.
  rewrite Hasz in HFRA, HENT.
  pose proof HK as (HLK & Hs7 & Hs6 & Hphi1 & Hphi2 & Hflen & Hblk & Hsum & Hs8 & HSPL).
  destruct (b7_fra_frame B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA)
    as (Happ & HGT & Hfr0 & Hfrhi & Hfr8).
  destruct (b7_fra_win B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hwinlo & Hsphi & Hwin).
  destruct (fra_frame B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (HCK & _ & _ & _).
  assert (HFN : FN_STACK = 1048576 - 4096) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  pose proof (HCK 16 ltac:(lia)) as HC1.
  destruct (b7_hb_apart B APIf ra g fr phi (flen g j) regs mem md HFRA ltac:(lia)) as (Hhb1 & Hhb2).
  pose proof HFRA as HF2.
  destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin0 & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC0.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW0.
  assert (HspA : AC.aspZ regs = sp) by exact Haspz.
  rewrite HspA in HC1, Hwin, Hwinlo, Hsphi, Hhb1.
  assert (HAb : 0 <= A /\ A + 416 <= 2 ^ 64) by (unfold HIGHMEM_BEG, APPMEM_END in *; lia).
  assert (HA9 : forall A2, getr regs 9 = Z_to_bv 64 A2 -> - 408 <= A2 -> A2 < 2 ^ 64 -> A2 = A).
  { intros A2 H2 Hlo2 Hhi2. unfold rg in Hr9. rewrite H2 in Hr9.
    apply (f_equal (@bv_unsigned 64)) in Hr9. rewrite !MState.unsigned_lit_wrap in Hr9.
    Z.div_mod_to_equations. lia. }
  set (W := [(sp - 16, sp)]).
  assert (HWgt : forall lo hi, In (lo, hi) W -> AC.GT <= lo).
  { intros lo hi Hin. unfold W in Hin. cbn [In] in Hin.
    destruct Hin as [E|[]]; injection E as <- <-; unfold AC.GT, HIGHMEM_BEG, AF.SLOT_STACK in *; lia. }
  assert (HBW : B7W fr sp W).
  { split; [exact HWgt|]. intros x Hx. unfold W in Hx. cbn [Frame.outside] in Hx.
    left. unfold AF.SLOT_STACK in *.
    destruct (Z_le_gt_dec (sp - 16) x); [|exfalso; apply Hx; split; [lia | exact I]].
    destruct (Z_lt_ge_dec x sp); [lia | exfalso; apply Hx; split; [lia | exact I]]. }
  assert (Happw : forall x, sp - 16 <= x < sp -> app_mem x).
  { intros x Hx. right. unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia. }
  assert (HADp : addressable mem (phi + 18) 20).
  { destruct HHB as (_ & HADphi). unfold AC.a_size in HADphi.
    apply (addressable_sub mem phi (Z.max (flen g j) 1) 18 20 HADphi); lia. }
  assert (HOUT : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            outside W x).
  { intros x Hx. unfold W. cbn [outside]. destruct Hx as [Hx|[Hx|Hx]].
    - unfold GOT_CELL_K, AC.GT, HIGHMEM_BEG, AF.SLOT_STACK in *. split; [lia | exact I].
    - unfold CELL_K, AC.GT, HIGHMEM_BEG, AF.SLOT_STACK in *. split; [lia | exact I].
    - split; [|exact I]. intros Hin. exact (app_not_shadow x (Happw x Hin) Hx). }
  apply (b7_run_lib regs (Z_to_bv 64 0x825f4) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x82604 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
       getr R0 21 = getr regs 21 /\ getr R0 26 = getr regs 26 /\
       getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\
       getr R0 25 = getr regs 25 /\ getr R0 18 = getr regs 18 /\
       getr R0 20 = Z_to_bv 64 (t_unk (g_in g) j) /\
       getr R0 10 = Z_to_bv 64 (t_unk (g_in g) j) /\
       munch W mem mem' /\ wmono rsegs mem mem')
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite (b7_mkR_of_expand fx regs). unfold rg in Hs6, Ha0.
    rewrite Hs6, Ha0, Hr2.
    eapply LE.evt_mono.
    { eapply f26_evt with (spv := sp) (phi := phi) (uk := t_unk (g_in g) j) (lo := sp - FN_STACK)
        (bs := t_pbs (g_in g) j).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - lia.
      - unfold APPMEM_END, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
      - exact Hwin.
      - lia.
      - apply b7_pbs_length.
      - apply b7_pbs_bytes. exact Hblk.
      - left. lia.
      - exact HAC0.
      - exact HSW0.
      - exact HADp.
      - exact HOUT. }
    { intros ms' (ra' & t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & m' & E & MUc & WMc).
      eexists _, (Z_to_bv 64 0x82604), m'. split; [exact E|].
      split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split.
      { unfold t_unk. reflexivity. }
      split.
      { unfold t_unk. reflexivity. }
      split; [exact MUc | exact WMc]. }
  - intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er21 & Er26 & Er22 & Er23 &
      Er24 & Er25 & Er18 & Er20 & Er10 & MU & WM) Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr20 : getr regs' 20 = Z_to_bv 64 (t_unk (g_in g) j)) by (rewrite Hreg; exact Er20).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 (t_unk (g_in g) j)) by (rewrite Hreg; exact Er10).
    assert (Haspz' : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    assert (HWapp : all_app W).
    { unfold W. cbn [all_app]. split; [|exact I]. intros x Hx. exact (Happw x Hx). }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md).
    { apply (b7_fra_run B APIf ra empty FF g fr (hb1 phi (flen g j)) regs regs' mem mem' md W HFRA MU WM);
        [ rewrite HspA; exact HBW | | | | | | | | | | | | ].
      - intros x Hx. unfold W. cbn [outside]. split; [|exact I]. destruct HC1 as [H|H]; lia.
      - intros A' HA' HA'r x Hx.
        assert (EA : A' = A) by (apply HA9; [exact HA' | lia | lia]). subst A'.
        unfold W. cbn [outside]. split; [|exact I]. lia.
      - intros A' HA' HA'r x Hx.
        assert (EA : A' = A) by (apply HA9; [exact HA' | lia | lia]). subst A'.
        unfold W. cbn [outside]. split; [|exact I]. lia.
      - intros x Hx. unfold W. cbn [outside]. split; [lia | exact I].
      - intros a Hin. exact (b7_addr_keep mem mem' W a 1 (HAG a Hin) MU HWapp).
      - exact Fr2.
      - exact Fr3.
      - exact Fr4.
      - exact Fr8.
      - exact Fr9.
      - exact Fr19.
      - exact Fr26. }
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md').
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs' regs' mem' md md' HFRA');
        try reflexivity; exact Hmat. }
    assert (HENT' : ENT APIf g (hb1 phi (flen g j)) mem' md)
      by (apply (b7_ent_run B APIf ra g fr (hb1 phi (flen g j)) regs mem mem' md W HENT HFRA MU WM);
          rewrite HspA; exact HBW).
    assert (HENT'' : ENT APIf g (hb1 phi (flen g j)) mem' md')
      by (eapply ent_mat; [exact HENT' | exact Hmat]).
    (* FLSI and B7K: the run writes only the callee's 16-byte window (app memory) *)
    assert (HBW' : B7W fr (AC.aspZ regs) W) by (rewrite HspA; exact HBW).
    assert (HC : FLSI g j fr regs' mem' /\ B7K g j phi fr regs' mem').
    { apply (b7_carry B APIf ra g j phi fr regs regs' mem mem' md W HFRA HHB HFLSI HK MU WM HBW').
      - intros x Hx. unfold W. cbn [outside]. split; [|exact I]. destruct HC1 as [H|H]; lia.
      - intros i Hi. apply (b7_app_shadow_out W _ HWapp). apply shadow_of_app. apply Happ. lia.
      - intros i Hi. apply (b7_app_shadow_out W _ HWapp). apply shadow_of_app. apply Happ. lia.
      - intros i Hi. apply (b7_app_shadow_out W _ HWapp). apply shadow_of_app. apply Happ. unfold fragb. lia.
      - intros x Hx. unfold W. cbn [outside]. split; [|exact I]. destruct HC1 as [H|H]; lia.
      - intros i Hi. apply (b7_app_shadow_out W _ HWapp). apply shadow_of_app. apply Happ. lia.
      - exact Fr9.
      - exact Fr18.
      - exact Fr21.
      - exact Fr22.
      - exact Fr23.
      - exact Fr24. }
    destruct HC as (HFLSI' & HK').
    assert (HOUTfr : forall x, fr <= x < fr + FRAME_BYTES -> outside W x).
    { intros x Hx. unfold W. cbn [outside]. split; [|exact I]. destruct HC1 as [H|H]; lia. }
    assert (HKeep : forall a n, (forall x, a <= x < a + n -> outside W x) ->
              forall bs0, Z.of_nat (length bs0) = n -> bytes_at rsegs mem a bs0 -> bytes_at rsegs mem' a bs0).
    { intros a n Hout bs0 Hl Hb. eapply fl_bytes; [exact Hb | exact MU|]. rewrite Hl. exact Hout. }
    assert (HexA : Inv_A82604_at B APIf ra g j
             (mkCfg (mkst regs' (Z_to_bv 64 0x82604) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      rewrite ?Hasz.
      split; [exact HFRA''|].
      split; [exact HENT''|].
      split; [exact Hgn|].
      split; [exact Hjle|].
      split.
      { destruct HHB as (Hnz & HAD). split; [exact Hnz|].
        eapply b7_addr_keep; [exact HAD | exact MU | exact HWapp]. }
      split; [exact HFLSI'|].
      split; [exact HK'|].
      split; [unfold rg in *; rewrite Fr25; exact Hs9|].
      split; [unfold rg; exact Fr20|].
      split; [unfold rg; exact Fr10|].
      split.
      { unfold PORTS in *. destruct HPORTS as (Hz & Hnz). split; intros E.
        - destruct (Hz E) as (Q0 & Q4 & Q8). unfold u32 in *.
          split; [apply (HKeep (fr + 128) 4); [intros x Hx; apply HOUTfr; lia | rewrite length_le4; reflexivity | exact Q0]|].
          split; [apply (HKeep (fr + 132) 4); [intros x Hx; apply HOUTfr; lia | rewrite length_le4; reflexivity | exact Q4]
                 | apply (HKeep (fr + 136) 4); [intros x Hx; apply HOUTfr; lia | rewrite length_le4; reflexivity | exact Q8]].
        - destruct (Hnz E) as (Q0 & Q4 & Q8). unfold u32 in *.
          split; [apply (HKeep (fr + 128) 4); [intros x Hx; apply HOUTfr; lia | rewrite length_le4; reflexivity | exact Q0]|].
          split; [apply (HKeep (fr + 132) 4); [intros x Hx; apply HOUTfr; lia | rewrite length_le4; reflexivity | exact Q4]
                 | apply (HKeep (fr + 136) 4); [intros x Hx; apply HOUTfr; lia | rewrite length_le4; reflexivity | exact Q8]]. }
      split.
      { unfold FIRSTb, b8 in *.
        apply (HKeep (fr + 160) 1); [intros x Hx; apply HOUTfr; lia | reflexivity | exact HFIRST]. }
      split; [eapply b7_addr_keep; [exact HADq | exact MU | exact HWapp]|].
      eapply b7_addr_keep; [exact HADf | exact MU | exact HWapp]. }
    pose proof (Hexit g _ HexA) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End F26.
