(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_pstr_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow Sj_akit Od_defsA Od_tablesA Od_pstr_tabA Od_pstr_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Lemma shz_read_lit : forall (m : mem) a n X adr, shz m a n -> ((a <=? X) && (X <? a + n))%bool = true ->
  adr = wa (X / 8 + 2147450880) -> ov_read_bytes asegs m adr 1 = Some [Z_to_bv 8 0].
Proof.
  intros m a n X adr H HB ->. apply H. apply andb_prop in HB as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Ltac od_lit_hook :=
  match goal with
  | |- context [ov_read_bytes asegs ?m ?a 1] =>
      let Ea := addr_expr a in
      lazymatch Ea with
      | Zpos _ =>
          let X := eval vm_compute in (8 * (Ea - 2147450880))%Z in
          lazymatch goal with
          | MU : munch ?W ?m0 m, WM : wmono asegs ?m0 m |- _ =>
              match goal with
              | SHP : (forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' (Zpos ?p0) (Zpos ?q0)) |- _ =>
                  od_lit_in X (Zpos p0) (Zpos q0);
                  rewrite (shz_read_lit m (Zpos p0) (Zpos q0) X a (SHP m MU WM) eq_refl eq_refl)
              end
          end
      end
  end;
  load_post.
Local Ltac solve_load ::= first [ od_lit_hook | od_load_hook | solve_load_image | solve_load_base ].

Section ArmStr.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Hypothesis HPSTR : pstra_stmt_g OD_PSTR 0x66b000.
  Hypothesis HG : forall m', munch (od_W E) (o_m0 E) m' -> wmono asegs (o_m0 E) m' ->
    ro_cells asegs m' g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] /\
    ro_cells asegs m' g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)].
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Theorem od_arm_string : arm_stmt E 0x973bc.
  Proof using OK HPSTR HG.
    unfold arm_stmt, arm_k. intros Q st HLAST HH HK xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xF xfc m1 FRM INV.
    pose proof HH as (HP & HD & HE & HA & HB).
    od_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_tokT_range E BOK (o_pos st)) as CR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    pose proof (tokB_read m1 E (tokI bs idxs (o_pos st)) BUFRO ltac:(lia)) as RD2.
    fold (tokT bs idxs (o_pos st)) in RD2.
    pose proof (tokT_string bs idxs S1 (o_pos st) ltac:(lia)) as TS.
    destruct HB as [HB0 HB1]. rewrite Z.min_l in HB1 by lia.
    set (c := tokT bs idxs (o_pos st)) in *. set (off := tokI bs idxs (o_pos st)) in *.

    zstep. if_true.
    ostep. ostep. ostep. ostep. ostep. if_true. ostep. zstep. if_true.

    ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. ostep. if_true.
    ostep. odnorm. ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. zstep.
    if_cases K; zify_cond K.
    - apply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
    - destruct (TS ltac:(unfold C_QUOTE; lia)) as (j & CLO & JR & JN).

      ostep. ostep. if_true. ostep. ostep. if_true. ostep. ostep. ostep. ostep. if_true. ostep. ostep.
      rewrite HA in *. rewrite VPT in DPI.

      ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. ostep. ostep. if_true.
      ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. ostep. if_true. ostep.
      ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. ostep.
      zstep.
      replace (ret_pc (Z_to_bv 64 OD_PSTR)) with (Z_to_bv 64 OD_PSTR) by (symmetry; apply ret_pc_even; [unfold OD_PSTR; lia| reflexivity]).
      pose proof HPSTR as HS. unfold pstra_stmt_g in HS.
      destruct (HG m0 MU WM) as [G1 G2].
      assert (SUBW : forall m', munch (psa_W (Z_to_bv 64 (oa_S1 E)) (o_SB E) (o_sbo st) off j) m0 m' ->
                                munch [(o_lo E, oa_S1 E + 352); (oa_F E + 192, oa_F E + 256); (o_SB E, o_SB E + o_CAP E)]%Z (o_m0 E) m').
      { intros m' MU'. eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU'].
        unfold sub_fp, psa_W, PSTR_FRAME. rewrite unsigned_lit by lia. cbn [outside]. clear - LOR HB0 HB1 JR CAPR.
        intros x (H1 & H2 & H3 & _). repeat split; Lia.lia. }
      eapply evt_cut.
      { eapply HS with (BUF := o_BUF E) (SB := o_SB E) (CAP := o_CAP E) (i := off) (j := j) (sbo := o_sbo st) (lo := o_lo E) (bs := bs);
          [ eassumption | rewrite ?unsigned_lit by lia; eassumption | rewrite ?unsigned_lit by lia; unfold PSTR_FRAME; lia | lia | exact BOK | eassumption | lia | exact CLO
          | eassumption | lia | lia | lia | pose proof (oka_sb_buf _ OK) as S_SB; clear - S_SB CPB; Lia.lia | exact G1 | exact G2
          | intros m' MU' WM'; eapply shz_sub; [apply (Z_BUF m' (SUBW m' MU') (wmono_trans asegs _ _ _ WM WM'))| lia| lia]
          | intros m' MU' WM'; apply (Z_SB m' (SUBW m' MU') (wmono_trans asegs _ _ _ WM WM'))
          | intros m' MU' WM'; apply (Z_DIG m' (SUBW m' MU') (wmono_trans asegs _ _ _ WM WM'))
          | intros m' MU' WM'; apply (Z_ESC m' (SUBW m' MU') (wmono_trans asegs _ _ _ WM WM')) ]. }
      cbv beta. intros ms' P. unfold pstr_post_g in P.
      destruct P as (q5 & q6 & q7 & rr & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3 & -> & RES & MUc & WMc & MIc & SBWc & STc).
      rewrite !unsigned_lit in MUc, STc by lia. unfold PSTR_FRAME in MUc.
      clear HS SUBW G1 G2 RD1 RD2.

      assert (T_BUF : bytes_at asegs m3 (o_BUF E) (padded_bytes bs)).
      { apply (bytes_at_transport asegs _ m0 m3 _ _ BUFRO MUc). cbn [disjoint_from]. rewrite PBL.
        pose proof (oka_sb_buf _ OK) as S_SB. clear - S_SB CPB BUFR LOR HB0 HB1 JR CAPR. repeat split; Lia.lia. }
      assert (T_DPI : rw_cells asegs m3 (o_IMPL E) _) by
        (apply (rw_cells_transport asegs _ m0 m3 _ _ DPI MUc WMc); cbn [disjoint_from]; simpl_sizes;
         pose proof (oka_sb_impl _ OK) as S_SM; clear - S_SM IMR LOR HB0 HB1 JR CAPR; repeat split; Lia.lia).
      assert (T_IDX : u32arr asegs m3 (o_IDX E) ws).
      { apply (u32arr_transport asegs _ m0 m3 _ _ IDXA MUc WMc). cbn [disjoint_from].
        pose proof (oka_sb_idx _ OK) as S_SI. rewrite IDXL.
        clear - S_SI IXR LOR HB0 HB1 JR CAPR. repeat split; Lia.lia. }
      assert (T_VT : ro_cells asegs m3 1087552 _) by
        (apply (ro_cells_transport asegs _ m0 m3 _ _ VT MUc); cbn [disjoint_from]; simpl_sizes;
         pose proof (proj2 (proj2 (proj2 (oka_sb _ OK)))) as SBD; clear - SBD LOB LOR HB0 HB1 JR CAPR; repeat split; Lia.lia).
      assert (T_GOT : ro_cells asegs m3 1103992 _) by
        (apply (ro_cells_transport asegs _ m0 m3 _ _ GOT MUc); cbn [disjoint_from]; simpl_sizes;
         pose proof (proj2 (proj2 (proj2 (oka_sb _ OK)))) as SBD; clear - SBD LOB LOR HB0 HB1 JR CAPR; repeat split; Lia.lia).
      clear BUFRO DPI IDXA VT GOT.
      transport_after_call asegs m0 m3 MUc WMc.
      clear MUc WMc. clear MI.
      rename T_BUF into BUFRO, T_DPI into DPI, T_IDX into IDXA, T_VT into VT, T_GOT into GOT.
      replace (ret_pc (Z_to_bv 64 623732)) with (Z_to_bv 64 623732) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      ostep. ostep. ostep. zstep.
      if_cases K3; zify_cond K3.
      +
        apply (HK (consume 1 st)); [| exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_scalar.
      + destruct RES as [R0|(sbo' & Rr & RB)]; [exfalso; subst rr; unfold wz in K3; rewrite unsigned_lit in K3 by lia; lia|].
        subst rr. unfold wz.

        ostep. ostep. if_true. ostep. ostep.
        apply (HK (mkO (o_pos st + 1) 1 (o_err st) (o_alive st) sbo')); [| exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH).
        apply (acc_string bs idxs 1 st j sbo'); [unfold C_QUOTE; fold c; lia| exact CLO| fold off; lia].
  Qed.
End ArmStr.

Theorem od_arm_string_base : forall (E : oaenv), od_oka E -> pstra_stmt_g OD_PSTR 0x66b000 ->
  ro_cells asegs (o_m0 E) g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs (o_m0 E) g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  arm_stmt E 0x973bc.
Proof.
  intros E OK HP G1 G2. apply (od_arm_string E OK HP).
  intros m' MU WM.
  pose proof (proj1 (oka_lo _ OK)) as LOB. pose proof (proj1 (proj2 (oka_F _ OK))) as FB.
  pose proof (proj2 (proj2 (proj2 (oka_sb _ OK)))) as SBD.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  split.
  - apply (ro_cells_transport asegs _ (o_m0 E) m' _ _ G1 MU). unfold od_W. cbn [disjoint_from]. simpl_sizes.
    clear - LOB FB SBD. repeat split; Lia.lia.
  - apply (ro_cells_transport asegs _ (o_m0 E) m' _ _ G2 MU). unfold od_W. cbn [disjoint_from]. simpl_sizes.
    clear - LOB FB SBD. repeat split; Lia.lia.
Qed.
