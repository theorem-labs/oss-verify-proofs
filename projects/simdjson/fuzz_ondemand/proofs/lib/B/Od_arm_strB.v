(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_pstr_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout Sj_akit Od_defsB Od_tablesB Od_pstr_tabB Od_pstr_defsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_base | solve_load_image ].

Section ArmStr.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Hypothesis HPSTR : pstrb_stmt_g OD_PSTR 0x679000.
  Hypothesis HG : od_shb E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Theorem od_arm_string : arm_stmt E 0x97674.
  Proof using OK HPSTR HG.
    unfold arm_stmt, arm_k. intros Q st HLAST HH HK xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1 FRM INV.
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
    ostep. utrap. ostep. ual. ostep. if_false. ostep. ostep. ostep. ostep. ostep. ostep. if_true. ostep.
    zstep. if_false. ostep.

    ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. uok. ostep. if_true. ostep. ostep. ostep. ostep. if_true. ostep. uok. ostep. ual. ostep. if_true.
    ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. uok. ostep. ostep. ostep. unz. ostep. if_true. ostep. uok.
    ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. zstep.
    if_cases K; zify_cond K.
    - destruct (TS ltac:(unfold C_QUOTE; lia)) as (j & CLO & JR & JN).

      ostep. zstep. if_false.
      ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. uok. ostep. if_true. ostep. ostep. ostep. ostep. if_true.
      ostep. ostep. uok. ostep. ostep. if_true. ostep. ostep. ostep. ual. ostep.
      od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RD3).
      fold off in RD3.

      ostep. if_true. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. ostep. uok. ostep. ostep. ostep. unz. ostep. if_true.
      ostep. ostep. if_true. ostep. ostep. if_true. ostep. ostep.
      rewrite HA in *. rewrite VPT in DPI.

      ostep. ostep. uok. ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. uok. ostep. ual. ostep. if_true.
      ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. uok. ostep. ual. ostep. if_true.
      ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. if_true.
      ostep. ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. ostep.
      zstep.
      replace (ret_pc (Z_to_bv 64 OD_PSTR)) with (Z_to_bv 64 OD_PSTR) by (symmetry; apply ret_pc_even; [unfold OD_PSTR; lia| reflexivity]).
      pose proof HPSTR as HS. unfold pstrb_stmt_g in HS.
      od_cur_mem ltac:(fun mm => destruct (HG mm ltac:(eassumption) ltac:(eassumption)) as [G1 G2];
        assert (SUBW : forall m', munch (psb_W (Z_to_bv 64 (oa_S1 E)) (o_SB E) (o_sbo st) off j) mm m' ->
                                  munch [(o_lo E, oa_S1 E + 384); (oa_F E + 192, oa_F E + 256); (o_SB E, o_SB E + o_CAP E)]%Z (o_m0 E) m');
        [ intros m' MU'; eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU'];
          unfold sub_fp, psb_W, PSTR_FRAME; rewrite unsigned_lit by lia; cbn [outside]; clear - LOR HB0 HB1 JR CAPR;
          intros x (H1 & H2 & H3 & _); repeat split; Lia.lia |]).
      eapply evt_cut.
      { eapply evt_eq; [| eapply HS with (BUF := o_BUF E) (SB := o_SB E) (CAP := o_CAP E) (i := off) (j := j) (sbo := o_sbo st) (lo := o_lo E) (bs := bs)];
          [ od_st_eq
          | eassumption | rewrite ?unsigned_lit by lia; eassumption | rewrite ?unsigned_lit by lia; unfold PSTR_FRAME; lia | lia | exact BOK | eassumption | lia | exact CLO
          | eassumption | lia | lia | lia | pose proof (oka_sb_buf _ OK) as S_SB; clear - S_SB CPB; Lia.lia | exact G1 | exact G2
          | intros m' MU' WM'; eapply shz_sub; [apply (Z_BUF m' (SUBW m' MU') (wmono_trans bsegs _ _ _ WM WM'))| lia| lia]
          | intros m' MU' WM'; apply (Z_SB m' (SUBW m' MU') (wmono_trans bsegs _ _ _ WM WM'))
          | intros m' MU' WM'; apply (Z_DIG m' (SUBW m' MU') (wmono_trans bsegs _ _ _ WM WM'))
          | intros m' MU' WM'; apply (Z_ESC m' (SUBW m' MU') (wmono_trans bsegs _ _ _ WM WM'))
          | lia | lia ]. }
      cbv beta. intros ms' P. unfold pstr_post_g in P.
      destruct P as (q5 & q6 & q7 & rr & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3 & -> & RES & MUc & WMc & MIc & SBWc & STc).
      rewrite !unsigned_lit in MUc, STc by lia. unfold PSTR_FRAME in MUc.
      clear HS SUBW G1 G2 RD1 RD2 RD3.

      eapply (bytes_at_transport bsegs) in BUFRO;
        [| exact MUc | cbn [disjoint_from]; rewrite PBL; pose proof (oka_sb_buf _ OK) as S_SB; clear - S_SB CPB BUFR LOR HB0 HB1 JR CAPR; repeat split; Lia.lia].
      eapply (rw_cells_transport bsegs) in DPI;
        [| exact MUc | exact WMc | cbn [disjoint_from]; simpl_sizes; pose proof (oka_sb_impl _ OK) as S_SM; clear - S_SM IMR LOR HB0 HB1 JR CAPR; repeat split; Lia.lia].
      eapply (u32arr_transport bsegs) in IDXA;
        [| exact MUc | exact WMc | cbn [disjoint_from]; pose proof (oka_sb_idx _ OK) as S_SI; rewrite IDXL; clear - S_SI IXR LOR HB0 HB1 JR CAPR; repeat split; Lia.lia].
      eapply (ro_cells_transport bsegs) in VT;
        [| exact MUc | cbn [disjoint_from]; simpl_sizes; pose proof (proj2 (proj2 (proj2 (oka_sb _ OK)))) as SBD; clear - SBD LOB LOR HB0 HB1 JR CAPR; repeat split; Lia.lia].
      eapply (ro_cells_transport bsegs) in GOT;
        [| exact MUc | cbn [disjoint_from]; simpl_sizes; pose proof (proj2 (proj2 (proj2 (oka_sb _ OK)))) as SBD; clear - SBD LOB LOR HB0 HB1 JR CAPR; repeat split; Lia.lia].
      transport_after_call bsegs m0 m3 MUc WMc.
      clear MUc WMc. clear MI.
      replace (ret_pc (Z_to_bv 64 625420)) with (Z_to_bv 64 625420) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      zstep.
      if_cases K3; zify_cond K3.
      + destruct RES as [R0|(sbo' & Rr & RB)]; [exfalso; subst rr; unfold wz in K3; rewrite unsigned_lit in K3 by lia; lia|].
        subst rr. unfold wz.

        ostep. ostep. if_true. ostep. ostep.
        eapply (HK (mkO (o_pos st + 1) 1 (o_err st) (o_alive st) sbo')); [| exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH).
        apply (acc_string bs idxs 1 st j sbo'); [unfold C_QUOTE; fold c; lia| exact CLO| fold off; lia].
      +
        ostep.
        eapply (HK (consume 1 st)); [| exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_scalar.
    -
      zstep.
      eapply (HK st); [| exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
  Qed.
End ArmStr.
