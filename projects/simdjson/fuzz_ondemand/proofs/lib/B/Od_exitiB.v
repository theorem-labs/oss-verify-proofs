(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Sj_num_kit Atp_h_defs Od_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsB Od_hkit0A Od_deldtorA Od_lkitB Od_tailwB Od_bodyB
  Od_tailB Od_exitwB Od_exitB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section ExitInv.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis DELA : del_cps RT e_delarr.
Hypothesis DTOR : deldtor_cps RT.
Hypothesis VDES : vdestroy_cpsA RT.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.

Notation aevt := (aevt RT PMc).

Lemma od_exit_inv : forall (Σ : rts RT) (K : config -> Prop) (E : oaenv) (A cap size IA OC : Z) (els L0 : list (Z * Z))
    (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word)
    st vs v88 v144 v152 v240 v312 v336 v352
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs11 xt3 xt4 xt5 xt6 : word) xF xfc (m1 : mem)
    (j0 j384 j432 h0 pre8 mid rest : list byte),
  od_oka E -> o_tp E = Z_to_bv 64 0x656e70 -> rt_sp0 RT Σ - STACK_WIN <= o_lo E -> frm0 xfc ->
  ART RT Σ m1 -> rt_frames RT Σ = [(oa_F E, 3%nat)] ->
  rt_live RT Σ = (IA, 1024) :: (OC, 8192) :: (o_IDX E, 4 * Z.of_nat (o_icap E)) :: (o_IMPL E, 96) :: (o_SB E, o_CAP E)
                 :: (o_COPY E, o_BUF E - o_COPY E + o_len E + 64) :: vblockA A cap size ++ L0 ->
  (forall p n, In (p, n) L0 -> 0 < n) ->
  ODINVg E vs v88 v144 v152 v240 v312 v336 v352 st m1 ->
  rw_cells bsegs m1 (oa_S1 E) [CB 8 j0] ->
  rw_cells bsegs m1 (oa_S1 E + 384) [CB 48 j384; CB 8 j432] ->
  stk bsegs m1 (oa_S1 E + 440) (oa_USP E - 104) ->
  rw_cells bsegs m1 (oa_USP E - 104) (fa_saved cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11) ->
  rw_cells bsegs m1 (oa_F E) [CB 8 h0] ->
  vrepA m1 (oa_F E + 32) A cap size els -> 1 <= cap -> 1 <= size ->
  wr_at bsegs m1 (oa_F E / 8 + 2147450880) 64 ->
  rw_cells bsegs m1 (oa_F E / 8 + 2147450880 + 4) (map C1 (repeat (Z_to_bv 8 0) 3)) ->
  rw_cells bsegs m1 (oa_F E / 8 + 2147450880 + 12) (map C1 (repeat (Z_to_bv 8 0) 7)) ->
  rw_cells bsegs m1 (oa_F E / 8 + 2147450880 + 24) (map C1 (repeat (Z_to_bv 8 0) 8)) ->
  length pre8 = 8%nat -> length mid = 32%nat -> length rest = 24%nat ->
  cells_bytes (dl_cells (o_vptr E) pre8 (Z_to_bv 64 (o_IDX E)) mid (Z_to_bv 64 OC) (Z_to_bv 64 IA) rest) = cells_bytes (dpi_cells E) ->
  od_ret_k RT PMc K (oa_USP E) (o_lo E) cra (o_gp E) cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 L0 (rt_sp0 RT Σ) (rt_credit RT Σ) m1 ->
  aevt Σ K (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2
                    (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                    xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 2147450880) xs8 xs9 (Z_to_bv 64 (oa_F E + 32)) xs11 xt3 xt4 xt5 xt6)
               xF (Z_to_bv 64 OD_EXIT) xfc None m1 (seg_rom bsegs)).
Proof using AF FDO MST RTF DELA DTOR VDES AFV.
  intros until rest.
  intros OK ETP LOW FRM ART1 FRS LV LPOS INV O0 OHI OPAD OSAV OHDR OVEC CAP1 SZ1 OWRS OSHV OSHP OSHD LPRE LMID LREST ODL HK.
  od_open_inv INV.
  clear ITER IDXA IDXL IDXF BUFRO PBL SBW VT GOT MU WM.
  pose proof OK as [_ S1O _ _ VPT [USP16 USPT] [S32 S1R] [LOB LOR] _ _ [CP0 [_ [CPB _]]] _ CAPR [_ [IM8 _]] _ ICAP
                    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  pose proof (od_n_range E S1O) as NR.
  rewrite ETP.

  pose proof (rw_cells_pick 1 1 m1 _ (oa_F E + 104) _ PARS ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as PIM.
  pose proof (rw_cells_pick 6 1 m1 _ (oa_F E + 144) _ PARS ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as PSB.
  cbn [firstn skipn] in PIM, PSB.
  assert (DPL : rw_cells bsegs m1 (o_IMPL E) (dl_cells (Z_to_bv 64 OD_DPI_VPTR) pre8 (Z_to_bv 64 (o_IDX E)) mid (Z_to_bv 64 OC) (Z_to_bv 64 IA) rest)).
  { rewrite VPT in ODL. apply (rw_cells_recell bsegs m1 (o_IMPL E) _ _ DPI); [| exact ODL| reflexivity].
    unfold dl_cells. cbn [cells_wf cell_wf]. rewrite LPRE, LMID, LREST. repeat split; reflexivity. }

  pose proof (rw_cells_pick 0 8 m1 _ (oa_S1 E + 8) _ FR8 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as P8.
  pose proof (rw_cells_pick 8 1 m1 _ (oa_S1 E + 72) _ FR8 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as P72.
  pose proof (rw_cells_pick 9 2 m1 _ (oa_S1 E + 80) _ FR8 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as P80.
  pose proof (rw_cells_pick 0 2 m1 _ (oa_S1 E + 96) _ FR96 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as P96.
  pose proof (rw_cells_pick 2 4 m1 _ (oa_S1 E + 112) _ FR96 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as P112.
  pose proof (rw_cells_pick 6 3 m1 _ (oa_S1 E + 144) _ FR96 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as P144.
  pose proof (rw_cells_pick 9 1 m1 _ (oa_S1 E + 168) _ FR96 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as P168.
  pose proof (rw_cells_pick 10 8 m1 _ (oa_S1 E + 176) _ FR96 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as P176.
  pose proof (rw_cells_pick 0 1 m1 _ (oa_S1 E + 240) _ FR240 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as P240.
  pose proof (rw_cells_pick 1 1 m1 _ (oa_S1 E + 248) _ FR240 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as P248.
  pose proof (rw_cells_pick 2 16 m1 _ (oa_S1 E + 256) _ FR240 ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as P256.
  pose proof (rw_cells_pick 0 1 m1 _ (oa_S1 E + 384) _ OHI ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as P384.
  pose proof (rw_cells_pick 1 1 m1 _ (oa_S1 E + 432) _ OHI ltac:(cbn [firstn cells_size csize Nat.add]; clear; lia)) as P432.
  cbn [firstn skipn] in P8, P72, P80, P96, P112, P144, P168, P176, P240, P248, P256, P384, P432.
  clear FR8 FR96 FR240 OHI PARS DPI.
  assert (J0 : exists j, rw_cells bsegs m1 (oa_S1 E) [CB 72 j]).
  { refine (rw_cells_junk m1 (oa_S1 E) (_ ++ _) 72%nat _ _);
      [apply Sj_stage1_kit.rw_cells_app; split; [exact O0| cbn [cells_size csize Nat.add]; readdr_ass]| reflexivity]. }
  assert (J80 : exists j, rw_cells bsegs m1 (oa_S1 E + 80) [CB 32 j]).
  { refine (rw_cells_junk m1 (oa_S1 E + 80) (_ ++ _) 32%nat _ _);
      [apply Sj_stage1_kit.rw_cells_app; split; [exact P80| cbn [cells_size csize Nat.add]; readdr_ass]| reflexivity]. }
  destruct (rw_cells_junk m1 (oa_S1 E + 144) _ 24%nat P144 eq_refl) as (j144 & J144).
  assert (J176 : exists j, rw_cells bsegs m1 (oa_S1 E + 176) [CB 72 j]).
  { refine (rw_cells_junk m1 (oa_S1 E + 176) (_ ++ _) 72%nat _ _);
      [apply Sj_stage1_kit.rw_cells_app; split; [exact P176| cbn [cells_size csize Nat.add]; readdr_ass]| reflexivity]. }
  assert (J256 : exists j, rw_cells bsegs m1 (oa_S1 E + 256) [CB 176 j]).
  { refine (rw_cells_junk m1 (oa_S1 E + 256) (_ ++ _) 176%nat _ _);
      [apply Sj_stage1_kit.rw_cells_app; split; [exact P256| cbn [cells_size csize Nat.add]; readdr_ass]| reflexivity]. }
  destruct J0 as (k0 & J0). destruct J80 as (k80 & J80). destruct J176 as (k176 & J176). destruct J256 as (k256 & J256).
  clear O0 P8 P80 P96 P144 P176 P240 P256 P384.
  assert (LOC : rw_cells bsegs m1 (oa_S1 E) (xl_locals (oa_F E) (o_COPY E) k0 k80 j144 k176 k256 j432)).
  { unfold xl_locals.
    change (rw_cells bsegs m1 (oa_S1 E)
              ([CB 72 k0] ++ [C8 (Z_to_bv 64 (oa_F E + 104))] ++ [CB 32 k80]
               ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (oa_F E)); C8 (Z_to_bv 64 (oa_F E)); C8 (Z_to_bv 64 (o_COPY E))]
               ++ [CB 24 j144] ++ [C8 (Z_to_bv 64 (oa_F E + 96))] ++ [CB 72 k176] ++ [C8 (Z_to_bv 64 (oa_F E / 8 + 2147450880))]
               ++ [CB 176 k256] ++ [CB 8 j432])).
    join_cells. }
  clear J0 P72 J80 P112 J144 P168 J176 P248 J256 P432.
  eapply (od_exit_core RT AF PMc FDO MST RTF DELA DTOR VDES AFV Σ K (oa_USP E) (oa_S1 E) (oa_F E) (o_lo E) (o_IMPL E) (o_IDX E) OC IA
            (4 * Z.of_nat (o_icap E)) (o_SB E) (o_CAP E) (o_COPY E) (o_BUF E - o_COPY E + o_len E + 64) A cap size els L0
            cra (o_gp E) cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11);
    [ exact S32 | exact S1R | exact USP16 | exact USPT | exact LOW | exact LOR | exact FRM | exact ART1 | exact MI | exact ST
    | exact FRS | exact LV | clear - ICAP NR; lia | clear - CAPR NR; lia | clear - CPB NR; lia | exact LPOS | exact IM8
    | exact LOC | exact OPAD | exact OSAV | exact OHDR | exact PIM | exact PSB | exact OVEC | exact CAP1 | exact SZ1
    | exact OWRS | exact OSHV | exact OSHP | exact OSHD | exact DPL | exact HK ].
Qed.

End ExitInv.
