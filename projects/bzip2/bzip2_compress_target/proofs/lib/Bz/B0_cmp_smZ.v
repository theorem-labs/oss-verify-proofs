(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpFsKit CmpHmKit CmpCutSmB BzCFactsSmB BzCSmF1 BzCFactsSmB2 CmpSmKit CmpSmKit2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV.   (* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV B0_cmp_sdV B0_cmp_smV B0_cmp_smP B0_cmp_smA B0_cmp_smB B0_cmp_smC B0_cmp_smBz.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section GZA.
  Variables (cx : cctx) (e : est) (g : eg) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (cost0 fave0 heap0 weight0 parent0 : zarr).
  Variables (P SHE FB SHF : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis GM : g_mtf g = true.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1712 <= 18446744073709551616)%Z.
  Hypothesis FBL : (0 < FB)%Z. Hypothesis FBH : (FB + 160 <= CEIL)%Z.
  Hypothesis SHL : (SH_LO <= SHF)%Z. Hypothesis SHH : (SHF + 20 <= SH_HI)%Z.
  Hypothesis AE : sanchor (c_E cx) SHE. Hypothesis AF : sanchor FB SHF.
  Hypothesis SEFB : id ((c_E cx + 55768 <= FB)%Z \/ (FB + 160 <= c_E cx)%Z).
  Hypothesis SA1FB : id ((c_A1 cx + ARR1_SIZE <= FB)%Z \/ (FB + 160 <= c_A1 cx)%Z).
  Hypothesis SESH : id ((c_E cx + 55768 <= SHF)%Z \/ (SHF + 20 <= c_E cx)%Z).
  Hypothesis SA1SH : id ((c_A1 cx + ARR1_SIZE <= SHF)%Z \/ (SHF + 20 <= c_A1 cx)%Z).
  Hypothesis SFSH : id ((FB + 160 <= SHF)%Z \/ (SHF + 20 <= FB)%Z).
  Hypothesis SPSH : id ((SHF + 20 <= P)%Z \/ (P + 1712 <= SHF)%Z).
  Hypothesis OFFE : id ((c_E cx + 55768 <= SH_LO)%Z \/ (SH_HI <= c_E cx)%Z).
  Hypothesis OFFF : id ((FB + 160 <= SH_LO)%Z \/ (SH_HI <= FB)%Z).
  Hypothesis OFFP : (SH_HI <= P)%Z.
  Hypothesis SFA : smA_facts e. Hypothesis FACTS : smB_facts e cost0 fave0 heap0 weight0 parent0.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation mf := (e_mtfFreq e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e). Notation nInUse := (e_nInUse e).
  Notation CO := (FB + 32)%Z. Notation FV := (FB + 64)%Z.
  Notation ITK k := (ITk e cost0 fave0 heap0 weight0 parent0 k).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Ltac openF :=
    let H := fresh "ST0" in pose proof (proj1 FACTS) as H; unfold smB_static in H;
    cps_destruct H as (?HA & ?HNG & ?HM & ?HNI & ?ZB & ?MV & ?HK & ?HK2 & ?HN6).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  Ltac openSF :=
    let H := fresh "SFL" in pose proof SFA as H; unfold smA_facts in H; cbv zeta in H; cps_destruct H as (?NI & ?NM & ?MFD & ?IPK & ?IPT).
  (* [comment removed for export] *)
  Local Ltac simpl_sizes ::=
    rewrite ?length_app;
    cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ EHEAD1 EHEAD2 sd_hi sd_loA sm_set sm_shadow];
    rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_app; cbn [length].

  Notation ITR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t4 :=
    (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 cSB (Z_to_bv 64 (258 * nG)) s4 (Z_to_bv 64 1032) (Z_to_bv 64 1548) (Z_to_bv 64 (4 * A)) (Z_to_bv 64 257)
         (Z_to_bv 64 CO) s10 (Z_to_bv 64 (CO + 12)) t3 t4 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (-9))).
  Notation HIT v32 v48 v56 v88 v20 v28 :=
    (sd_hi cx nG (SDW (Z_to_bv 64 FV) (Z_to_bv 64 (1032 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (E + 37708)) v32 v48 v56 (Z_to_bv 64 (E + 37708)) v88 (NOT (E + 45448)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A) v20 v28)).
  Notation LOWk w104 := (sd_loA cx FB SHF SHE (Z_to_bv 64 (FB + 88)) (Z_to_bv 64 (flag6 nG)) w104).

  (* [comment removed for export] *)
  Definition WsA : list (Z * Z) :=
    [(E + 1704, E + 19706); (E + 37708, E + 39256); (E + 45448, E + 51640); (E + 51640, E + 55768); (P + 24, P + 136); (P + 136, P + 1264); (P + 1264, P + 1576);
     (FB, FB + 24); (CO, CO + 12); (FV, FV + 24); (SHF, SHF + 20)]%Z.
  Ltac hidisj := cbn [disjoint_from]; simpl_sizes; Lib.Step.slia.
  (* [comment removed for export] *)
  Ltac cellv H B k := eapply (frdW_cell_at b0segs _ _ B _ k); [apply frdW_intro; [exact H| hidisj]| reflexivity| lia].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_sm_segA : forall (m : word -> option byte) (Jsp jc jf bs : list byte)
      (w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 : word)
      (w1264 w1272 w1280 w1288 w1296 w1304 w1312 w1320 w1328 w1336 w1344 w1352 w1360 w1368 w1376 : word)
      (w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1440 w1448 w1456 w1464 w1472 w1480 w1488 w1496 w1504 w1512 w1520 w1528 w1536 w1544 w1552 w1560 w1568 : word) (h0 h1 h2 : word)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    length Jsp = 1128%nat -> length jc = 12%nat -> length jf = 24%nat ->
    rw_cells b0segs m E (EHEAD1 cx g e) -> rw_cells b0segs m (E + 640) (EHEAD2 cx g e) ->
    u32arr b0segs m (E + 672) (ovw mf (jseg J 672 1032) 258) ->
    u8arr b0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u8arr b0segs m (E + 37708) (ovb (e_len e) (jseg J 37708 1548) 1548) ->
    u32arr b0segs m (E + 51640) (ovw (e_len_pack e) (jseg J 51640 4128) 1032) ->
    u32arr b0segs m (E + 45448) (ovw (e_rfreq e) (jseg J 45448 6192) 1548) ->
    u8arr b0segs m (E + 1704) (ovb (e_selector e) (jseg J 1704 18002) 18002) ->
    rw_cells b0segs m (P + 24) [C8 w24] ->
    rw_cells b0segs m (P + 32) [C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128] ->
    u8arr b0segs m (P + 136) Jsp ->
    rw_cells b0segs m (P + 1264) [C8 w1264; C8 w1272; C8 w1280; C8 w1288; C8 w1296; C8 w1304; C8 w1312; C8 w1320; C8 w1328; C8 w1336; C8 w1344; C8 w1352; C8 w1360; C8 w1368; C8 w1376] ->
    rw_cells b0segs m (P + 1384) [C8 w1384; C8 w1392; C8 w1400; C8 w1408; C8 w1416; C8 w1424; C8 w1432; C8 w1440; C8 w1448; C8 w1456; C8 w1464; C8 w1472; C8 w1480; C8 w1488; C8 w1496; C8 w1504; C8 w1512; C8 w1520; C8 w1528; C8 w1536; C8 w1544; C8 w1552; C8 w1560; C8 w1568] ->
    rw_cells b0segs m FB [C8 h0; C8 h1; C8 h2] -> u8arr b0segs m CO jc -> u8arr b0segs m FV jf -> rw_cells b0segs m SHF [CB 20 bs] ->
    mem_inv b0segs m ->
    shzW b0segs WsA m A1 (A1 + ARR1_SIZE) -> shzW b0segs WsA m E (E + ESTATE_SIZE) ->
    (forall m' (Jsp' jc' : list byte) (v32' v88' : word) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' : word),
      let s := ITK 0 in
      length Jsp' = 1128%nat -> length jc' = 12%nat ->
      rw_cells b0segs m' E (EHEAD1 cx g e) -> rw_cells b0segs m' (E + 640) (EHEAD2 cx g e) ->
      u32arr b0segs m' (E + 672) (ovw mf (jseg J 672 1032) 258) ->
      u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u8arr b0segs m' (E + 37708) (ovb (it_len s) (jseg J 37708 1548) 1548) ->
      u32arr b0segs m' (E + 51640) (ovw (it_lpk e s) (jseg J 51640 4128) 1032) ->
      u32arr b0segs m' (E + 45448) (ovw (g_rfreq (Gend e s)) (jseg J 45448 6192) 1548) ->
      u8arr b0segs m' (E + 1704) (ovb (g_sel (Gend e s)) (jseg J 1704 18002) 18002) ->
      rw_cells b0segs m' (P + 24) [C8 (Z_to_bv 64 (E + 37450))] ->
      rw_cells b0segs m' (P + 32) (LOWk (Z_to_bv 64 1)) ->
      u8arr b0segs m' (P + 136) Jsp' ->
      rw_cells b0segs m' (P + 1264) (sm_set cx FV) ->
      rw_cells b0segs m' (P + 1384) (HIT v32' (Z_to_bv 64 (g_totc (Gend e s))) (Z_to_bv 64 nMTF) v88' (Z_to_bv 64 (g_nSel (Gend e s))) (Z_to_bv 64 (E + 37708))) ->
      rw_cells b0segs m' (P + 1568) [C8 (Z_to_bv 64 FB)] ->
      rw_cells b0segs m' FB [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x148b3); C8 (Z_to_bv 64 0x8bc40)] ->
      u32arr b0segs m' FV (zw32 (g_fave (Gend e s)) 6) -> u8arr b0segs m' CO jc' ->
      rw_cells b0segs m' SHF sm_shadow ->
      mem_inv b0segs m' -> munch WsA m m' -> wmono b0segs m m' ->
      evt b0segs Q (MS (ITR ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (-1548)) (Z_to_bv 64 0) t3' t4')
                       F (Z_to_bv 64 0x9399c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP (Z_to_bv 64 FB) a1 a2 a3 a4 a5 a6 a7 cSB (Z_to_bv 64 E) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8bcb0) fc None m (seg_rom b0segs)).
  Proof.
    intros m Jsp jc jf bs w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w1264 w1272 w1280 w1288 w1296 w1304 w1312 w1320 w1328 w1336 w1344 w1352 w1360 w1368 w1376
           w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1440 w1448 w1456 w1464 w1472 w1480 w1488 w1496 w1504 w1512 w1520 w1528 w1536 w1544 w1552 w1560 w1568 h0 h1 h2
           ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           LJsp Ljc Ljf EH1 EH2 MTF AR1 LEN LPK RFQ SEL SL24 LOW SPL SETc HI HD COST FAV SH20 MI SHa SHe K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. openF. openSF.
    assert (HAd : A = (nInUse + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    pose proof CEP as CEP'. pose proof FBH as FBH'. unfold CEIL in CEP', FBH'. pose proof SHL as SHL'. pose proof SHH as SHH'. unfold SH_LO, SH_HI in SHL', SHH'.
    pose proof SEP as SP. unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in SP. cbv zeta in SP. destruct SP as (AEA1 & _).
    pose proof (sm_nGroups_range (e_nMTF e)) as NGR. change (sm_nGroups (e_nMTF e)) with nG in NGR.
    cbv zeta in K. unfold WsA in *.
    pose proof (munch_refl [(E + 1704, E + 19706); (E + 37708, E + 39256); (E + 45448, E + 51640); (E + 51640, E + 55768); (P + 24, P + 136); (P + 136, P + 1264); (P + 1264, P + 1576);
                            (FB, FB + 24); (CO, CO + 12); (FV, FV + 24); (SHF, SHF + 20)]%Z m) as MU.
    pose proof (wmono_refl b0segs m) as WM.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply (B0_smA_in2 cx g e Q gp tp s0 F fc P SHE FB SHF CX SFA GM CEP FBL FBH AE AF SEFB SESH SFSH SPSH m
                              w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1440 w1448 w1456 w1464 w1472 w1480 w1488 w1496 w1504 w1512 w1520 w1528 w1536
                              w1544 w1552 w1560 w1568 h0 h1 h2 bs)];
      [st_eq| exact EH1| exact EH2| exact LOW| exact HI| exact HD| exact SH20| exact MI| |].
    { eapply (shzW_sub b0segs _ _ m m); [exact SHe| apply munch_refl| a_sub_fp| lia| lia]. }
    clear EH1 EH2 LOW HI HD SH20 MI. intros m1 EH1 EH2 LOW HI HD SHD MI MU1 WM1.
    transport_after_call b0segs m m1 MU1 WM1. clear MU1 WM1.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply (B0_smA_lenrows cx e Q gp tp s0 F fc P CX SFA CEP PHI _ _ _ _ _ _ _ _ _ _ _ _ _ 6%nat 0 (e_len e) m1 m1)];
      [st_eq| lia| lia| lia| exact LEN| exact MI| apply munch_refl| apply wmono_refl| | cellv HI (P + 1384)%Z 80%nat| cellv HI (P + 1384)%Z 128%nat| cellv HI (P + 1384)%Z 176%nat|].
    { eapply (shzW_sub b0segs _ _ m m1); [exact SHe| exact MU| a_sub_fp| lia| lia]. }
    clear LEN MI. intros m2 yt0 yt1 ya0 ya7 LEN MI MU2 WM2.
    transport_after_call b0segs m1 m2 MU2 WM2. clear MU2 WM2.
    change (sm_len_init 6 (e_len e) A 0) with (smA_len e) in LEN.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply (B0_smA_disp cx e Q gp tp s0 F fc P CX SFA CEP g SHE FB SHF AE GM m2)];
      [st_eq| exact EH2| exact LOW| exact HI| exact MI| |].
    { eapply (shzW_sub b0segs _ _ m m2); [exact SHe| exact MU| a_sub_fp| lia| lia]. }
    clear EH2 LOW HI MI. intros m3 xa4 xa5 xa6 xa7 xs7 EH2 LOW HI MI MU3 WM3.
    transport_after_call b0segs m2 m3 MU3 WM3. clear MU3 WM3.
    (* [comment removed for export] *)
    pose proof (B0_smA_iloop cx g e Q gp tp s0 F fc P SHE (Z_to_bv 64 (FB + 32)) CX SFA CEP PHI AE (Z.to_nat nG) 0%nat m3 m3) as LOOP.
    cbv zeta in LOOP. change (sip_k e 0) with (sip0 e) in LOOP. cbn [ip_nPart ip_remF ip_gs ip_len sip0] in LOOP.
    replace (0 + Z.to_nat nG)%nat with (Z.to_nat nG) in LOOP by lia. rewrite <- IPT in LOOP. change (sm_init_tables 8 mf nG A (sip0 e)) with (smA_ip e) in LOOP.
    eapply evt_eq; [| eapply LOOP];
      [st_eq| lia| lia| lia| exact LEN| exact MTF| exact EH2| exact MI| apply munch_refl| apply wmono_refl|
      | cellv LOW (P + 32)%Z 80%nat| cellv LOW (P + 32)%Z 88%nat| cellv HI (P + 1384)%Z 80%nat| cellv HI (P + 1384)%Z 96%nat| cellv HI (P + 1384)%Z 128%nat
      | cellv HI (P + 1384)%Z 152%nat| cellv HI (P + 1384)%Z 160%nat| cellv HI (P + 1384)%Z 176%nat|].
    { eapply (shzW_sub b0segs _ _ m m3); [exact SHe| exact MU| a_sub_fp| lia| lia]. }
    clear LOOP LEN MTF EH2 MI. intros m4 za0 za1 za2 za3 za4 za5 za6 za7 zs6 zs7 LEN MTF EH2 MI MU4 WM4.
    transport_after_call b0segs m3 m4 MU4 WM4. clear MU4 WM4.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply (B0_smA_setup cx e Q gp tp s0 F fc P SHE FB SHF CX SFA FBL FBH m4)];
      [st_eq| exact SL24| exact LOW| exact SETc| exact HI| exact MI|].
    clear SL24 LOW SETc HI MI. intros m5 yra y0 y1 y2 xa0 xa1 xa2 xa3 ya4 ya5 ya6 xxa7 y3 y4 SL24 LOW SETc HI S1568 MI MU5 WM5.
    transport_after_call b0segs m4 m5 MU5 WM5. clear MU5 WM5.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply (B0_sm_iterA cx e g Q gp tp s0 F fc cost0 fave0 heap0 weight0 parent0 P SHE FB SHF CX SEP GM CEP PHI FBL FBH SHL SHH AE AF SEFB SA1FB SESH SFSH SPSH OFFE OFFF OFFP FACTS
                              0%nat Jsp jc jf _ _ _ _ _ m5 m5)];
      [st_eq| lia| exact LJsp| exact Ljc| exact Ljf| exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact EH2| exact LOW| exact SPL| exact SETc| exact HI| exact FAV| exact COST| exact SHD
      | exact MI| apply munch_refl| apply wmono_refl| | |].
    { eapply (shzW_sub b0segs _ _ m m5); [exact SHa| exact MU| unfold Wit; a_sub_fp| lia| lia]. }
    { eapply (shzW_sub b0segs _ _ m m5); [exact SHe| exact MU| unfold Wit; a_sub_fp| lia| lia]. }
    clear AR1 LEN LPK RFQ SEL EH2 LOW SPL SETc HI FAV COST SHD MI.
    intros m6 Jsp' jc' v32' v88' ura u0 u1 u2 ua0 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4. cbv zeta.
    intros LJsp' Ljc' AR1 LEN LPK RFQ SEL EH2 LOW SPL SETc HI FAVE COST SHD MI MU6 WM6.
    unfold Wit in MU6. transport_after_call b0segs m5 m6 MU6 WM6. clear MU6 WM6.
    enter_with (K m6 Jsp' jc' v32' v88' _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| exact LJsp'| exact Ljc'| exact EH1| exact EH2| exact MTF| exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact SL24| exact LOW| exact SPL| exact SETc| exact HI| exact S1568| exact HD
      | exact FAVE| exact COST| exact SHD| exact MI| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_sm_segC : forall (k : nat) (Jsp jc : list byte) (fv : zarr) (v32 v48 v56 v88 v20 : word) (m me : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t4 : word),
    (1 <= k < 4)%nat -> length Jsp = 1128%nat -> length jc = 12%nat ->
    u8arr b0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u8arr b0segs m (E + 37708) (ovb (it_len (ITK k)) (jseg J 37708 1548) 1548) ->
    u32arr b0segs m (E + 51640) (ovw (it_lp (ITK k)) (jseg J 51640 4128) 1032) ->
    u32arr b0segs m (E + 45448) (ovw (it_rfreq (ITK k)) (jseg J 45448 6192) 1548) ->
    u8arr b0segs m (E + 1704) (ovb (it_sel (ITK k)) (jseg J 1704 18002) 18002) ->
    rw_cells b0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells b0segs m (P + 32) (LOWk (Z_to_bv 64 (Z.of_nat k))) ->
    u8arr b0segs m (P + 136) Jsp ->
    rw_cells b0segs m (P + 1264) (sm_set cx FV) ->
    rw_cells b0segs m (P + 1384) (HIT v32 v48 v56 v88 v20 (Z_to_bv 64 (E + 37708))) ->
    u32arr b0segs m FV (zw32 fv 6) -> u8arr b0segs m CO jc ->
    rw_cells b0segs m SHF sm_shadow ->
    mem_inv b0segs m -> munch (Wit cx P FB) me m -> wmono b0segs me m ->
    shzW b0segs (Wit cx P FB) me A1 (A1 + ARR1_SIZE) -> shzW b0segs (Wit cx P FB) me E (E + ESTATE_SIZE) ->
    (forall m' (Jsp' jc' : list byte) (v32' v88' : word) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' : word),
      let s := ITK k in
      length Jsp' = 1128%nat -> length jc' = 12%nat ->
      u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u8arr b0segs m' (E + 37708) (ovb (it_len s) (jseg J 37708 1548) 1548) ->
      u32arr b0segs m' (E + 51640) (ovw (it_lpk e s) (jseg J 51640 4128) 1032) ->
      u32arr b0segs m' (E + 45448) (ovw (g_rfreq (Gend e s)) (jseg J 45448 6192) 1548) ->
      u8arr b0segs m' (E + 1704) (ovb (g_sel (Gend e s)) (jseg J 1704 18002) 18002) ->
      rw_cells b0segs m' (E + 640) (EHEAD2 cx g e) ->
      rw_cells b0segs m' (P + 32) (LOWk (Z_to_bv 64 (Z.of_nat k + 1))) ->
      u8arr b0segs m' (P + 136) Jsp' ->
      rw_cells b0segs m' (P + 1264) (sm_set cx FV) ->
      rw_cells b0segs m' (P + 1384) (HIT v32' (Z_to_bv 64 (g_totc (Gend e s))) (Z_to_bv 64 nMTF) v88' (Z_to_bv 64 (g_nSel (Gend e s))) (Z_to_bv 64 (E + 37708))) ->
      u32arr b0segs m' FV (zw32 (g_fave (Gend e s)) 6) -> u8arr b0segs m' CO jc' ->
      rw_cells b0segs m' SHF sm_shadow ->
      mem_inv b0segs m' -> munch (Wit cx P FB) me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (ITR ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (-1548)) (Z_to_bv 64 0) t3' t4')
                       F (Z_to_bv 64 0x9399c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (ITR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t4)
                     F (Z_to_bv 64 0x939fc) fc None m (seg_rom b0segs)).
  Proof.
    intros k Jsp jc fv v32 v48 v56 v88 v20 m me ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t4
           Hk LJsp Ljc AR1 LEN LPK RFQ SEL EH2 LOW SPL SETc HI FAVE COST SHD MI MU WM SHa SHe K.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply (B0_sm_itail cx e Q gp tp s0 F fc P SHE CO FV FB SHF CX (Z.of_nat k) (Z_to_bv 64 (flag6 nG)) m)]; [st_eq| lia| | | intros; exfalso; lia].
    { replace (FV + 24)%Z with (FB + 88)%Z by lia. exact LOW. }
    intros _.
    apply (proj1 (u32arr_u8arr' b0segs m FV _)) in FAVE.
    eapply evt_eq; [| eapply (B0_sm_iterA cx e g Q gp tp s0 F fc cost0 fave0 heap0 weight0 parent0 P SHE FB SHF CX SEP GM CEP PHI FBL FBH SHL SHH AE AF SEFB SA1FB SESH SFSH SPSH OFFE OFFF OFFP FACTS
                              k Jsp jc (u32s (zw32 fv 6)) v32 v48 v56 v88 v20 m me)];
      [st_eq| lia| exact LJsp| exact Ljc| rewrite u32s_length, zw32_length_nat; reflexivity| exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact EH2| exact LOW| exact SPL| exact SETc| exact HI
      | exact FAVE| exact COST| exact SHD| exact MI| exact MU| exact WM| exact SHa| exact SHe| exact K].
  Qed.
End GZA.
End ACeilS1.
