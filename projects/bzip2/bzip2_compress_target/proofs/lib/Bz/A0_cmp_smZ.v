(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpFsKit CmpHmKit CmpSmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV A0_cmp_smA A0_cmp_smB.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0SMZ.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE CO FV FB SHF : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis SF : smA_facts e. Hypothesis GM : g_mtf g = true.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1616 <= 18446744073709551616)%Z.
  Hypothesis AE : sanchor (c_E cx) SHE.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation mf := (e_mtfFreq e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e). Notation nInUse := (e_nInUse e).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  Ltac openSF :=
    let H := fresh "SFL" in pose proof SF as H; unfold smA_facts in H; cbv zeta in H; cps_destruct H as (?NI & ?NM & ?MFD & ?IPK & ?IPT).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Notation LOW0 w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w152 w160 w168 w184 w200 w208 w216 :=
    [C8 w16; C8 w24; C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 (FB + 128)); C8 (Z_to_bv 64 SHF); C8 w64; C8 w72;
     C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 (Z_to_bv 64 (SHE + 82)); C8 (Z_to_bv 64 (E + 656)); C8 (Z_to_bv 64 E);
     C8 w152; C8 w160; C8 w168; C8 (Z_to_bv 64 (E + 668)); C8 w184; C8 (Z_to_bv 64 A); C8 w200; C8 w208; C8 w216; C8 (Z_to_bv 64 nInUse)].
  Notation HI0 w1344 w1352 w1360 w1368 w1392 w1400 w1408 w1424 w1432 :=
    [C8 w1344; C8 w1352; C8 w1360; C8 w1368; C8 (Z_to_bv 64 CO); C8 (Z_to_bv 64 FV); C8 w1392; C8 w1400; C8 w1408; C8 (Z_to_bv 64 A); C8 w1424; C8 w1432].
  Notation W3 := [(E + 37708, E + 39256); (P + 16, P + 232); (P + 1344, P + 1440)]%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_smA_in3r : forall (t : Z) (m : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (0 <= t)%Z -> (t + 1 < 6)%Z ->
    frdW a0segs [] m (P + 144) [C8 (Z_to_bv 64 E)] -> frdW a0segs [] m (P + 224) [C8 (Z_to_bv 64 nInUse)] -> frdW a0segs [] m (P + 1416) [C8 (Z_to_bv 64 A)] ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 0x8a5d4) cP gp tp (Z_to_bv 64 E) t1 t2 s0 cP (Z_to_bv 64 (E + 37708 + 258 * (t + 1))) (Z_to_bv 64 15) (Z_to_bv 64 A) a3 a4 a5 a6 (Z_to_bv 64 nInUse)
                          (Z_to_bv 64 (E + 37708 + 258 * (t + 1))) s3 cSB (Z_to_bv 64 (6 - (t + 1))) (Z_to_bv 64 (E + 668)) (Z_to_bv 64 (-1)) s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x52ea0) fc None m (seg_rom a0segs)) ->
    evt a0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7
                          (Z_to_bv 64 (E + 37708 + 258 * t)) s3 cSB (Z_to_bv 64 (6 - t)) (Z_to_bv 64 (E + 668)) (Z_to_bv 64 (-1)) s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8a5d4) fc None m (seg_rom a0segs)).
  Proof.
    intros t m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s8 s9 s10 s11 t3 t4 t5 t6 Ht0 Ht V144 V224 V1416 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. openSF.
    pose proof (munch_refl [] m) as MU.
    (* [comment removed for export] *)
    pose proof (V144 m MU) as RO. wstep. clear RO. pose proof (V224 m MU) as RO. wstep. clear RO.
    wstep. wstep. wstep; if_cases Kr; zify_cond_z Kr; [| exfalso; lia].
    (* [comment removed for export] *)
    wstep; if_cases Kn; zify_cond_z Kn; [exfalso; lia|].
    wstep. wstep. pose proof (V1416 m MU) as RO. wstep. clear RO. wstep.
    enter_with K; [st_eq].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation RI ra a0 a1 a2 a3 a4 a5 a6 s2 s3 s5 s7 s8 s9 s11 t6 :=
    (mkR ra cP gp tp (Z_to_bv 64 E) (Z_to_bv 64 (E + 672)) (Z_to_bv 64 (E + 676)) s0 cP a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 nInUse)
         s2 s3 cSB s5 (Z_to_bv 64 (E + 668)) s7 s8 s9 (Z_to_bv 64 1) s11 (Z_to_bv 64 3) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-2147483647)) t6).
  Notation Ws1 := [(P + 16, P + 232); (P + 1344, P + 1440)]%Z.
  Lemma A0_smA_setup1 : forall (m : word -> option byte)
      (w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w152 w160 w168 w184 w200 w208 w216 : word) (w1344 w1352 w1360 w1368 w1392 w1400 w1408 w1424 w1432 : word)
      (ra t1 t2 a0 a1 a2 a3 a4 a5 a6 s2 s3 s5 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells a0segs m (P + 16) (LOW0 w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w152 w160 w168 w184 w200 w208 w216) ->
    rw_cells a0segs m (P + 1344) (HI0 w1344 w1352 w1360 w1368 w1392 w1400 w1408 w1424 w1432) ->
    ro_cells a0segs m 0xc06b8 [C8 (Z_to_bv 64 0xbf950)] ->
    mem_inv a0segs m -> shzW a0segs Ws1 m E (E + ESTATE_SIZE) ->
    (forall m' (v16 v24 v1400 v1408 : word) (a1 a2 a3 a4 a5 a6 s2 s3 s8' t6' : word),
      rw_cells a0segs m' (E + 640) (EHEAD2 cx g e) ->
      rw_cells a0segs m' (P + 16) (LOW0 v16 v24 (Z_to_bv 64 2147548970) (Z_to_bv 64 784720) w80 w88 w96 w104 w112 w120 w152 (Z_to_bv 64 (E + 37708)) w168 (Z_to_bv 64 (SHE + 83))
                                        (Z_to_bv 64 nG) w208 (Z_to_bv 64 A1)) ->
      rw_cells a0segs m' (P + 1344) (HI0 w1344 w1352 (Z_to_bv 64 37450) (Z_to_bv 64 (flag6 nG)) w1392 v1400 v1408 (Z_to_bv 64 (E + 676)) (Z_to_bv 64 (E + 672))) ->
      mem_inv a0segs m' -> munch Ws1 m m' -> wmono a0segs m m' ->
      evt a0segs Q (MS (RI ra (Z_to_bv 64 nG) a1 a2 a3 a4 a5 a6 s2 s3 (Z_to_bv 64 nMTF) (Z_to_bv 64 (E + 37708 + 258 * (nG - 1))) s8' (Z_to_bv 64 (E + 37708 + 258 * (nG - 1))) (Z_to_bv 64 0) t6')
                       (smF F) (Z_to_bv 64 0x8a720) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra cP gp tp (Z_to_bv 64 E) t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 nInUse)
                          s2 s3 cSB s5 (Z_to_bv 64 (E + 668)) (Z_to_bv 64 (-1)) (Z_to_bv 64 A1) s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8a5e8) fc None m (seg_rom a0segs)).
  Proof.
    intros m w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w152 w160 w168 w184 w200 w208 w216 w1344 w1352 w1360 w1368 w1392 w1400 w1408 w1424 w1432
           ra t1 t2 a0 a1 a2 a3 a4 a5 a6 s2 s3 s5 s9 s10 s11 t3 t4 t5 t6 EH2 LOW HI GOT MI SHe K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. openSF. assert (HA : A = (nInUse + 2)%Z) by reflexivity. assert (HM : nMTF = e_nMTF e) by reflexivity.
    pose proof CEP as CEP'. unfold CEIL in CEP'. unfold ESTATE_SIZE in SHe.
    pose proof (sm_nGroups_range (e_nMTF e)) as NGR. change (sm_nGroups (e_nMTF e)) with nG in NGR.
    pose proof (munch_refl Ws1 m) as MU. pose proof (wmono_refl a0segs m) as WM.
    unfold EHEAD2 in EH2. rewrite GM in EH2.
    (* [comment removed for export] *)
    arun_to 0x8a600%Z. sh_norm.
    wstep. try rewrite (sx32_of_Z (e_nMTF e)) by lia.
    wstep; if_cases Ka; zify_cond_z Ka; [| exfalso; lia].
    (* [comment removed for export] *)
    wstep. (wstep; lit_store). (wstep; lit_store).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (K988 : forall m2 (fl : Z) (xa0' : word), fl = flag6 nG ->
      rw_cells a0segs m2 (P + 1344) (HI0 w1344 w1352 w1360 (Z_to_bv 64 fl) w1392 w1400 w1408 w1424 w1432) ->
      munch [(P + 1344, P + 1440)]%Z mm m2 -> wmono a0segs mm m2 -> mem_inv a0segs m2 ->
      evt a0segs Q (MS (mkR ra cP gp tp (Z_to_bv 64 E) t1 t2 s0 cP xa0' a1 a2 a3 a4 a5 (Z_to_bv 64 nG) (Z_to_bv 64 nInUse)
                            (Z_to_bv 64 (Z.land (E + 668) 7)) s3 cSB (Z_to_bv 64 nMTF) (Z_to_bv 64 (E + 668)) (Z_to_bv 64 (SHE + 83)) (Z_to_bv 64 A1) s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x8a684) fc None m2 (seg_rom a0segs)));
    [| pose proof (munch_refl [(P + 1344, P + 1440)]%Z mm) as MUk; pose proof (wmono_refl a0segs mm) as WMk ]
    end.
    2:{ (* [comment removed for export] *)
        wstep; if_cases K1; zify_cond_z K1.
        - (* [comment removed for export] *)
          wstep. wstep; if_cases K2; zify_cond_z K2.
          + (* [comment removed for export] *)
            wstep. wstep; if_cases K3; zify_cond_z K3.
            * (* [comment removed for export] *)
              pose proof (sm_nGroups_ge1200 (e_nMTF e) ltac:(lia)) as HG. change (sm_nGroups (e_nMTF e)) with nG in HG.
              destruct (Z.ltb_spec (e_nMTF e / 32) 75) as [D|D];
                (wstep; (wstep; flags); wstep; (wstep; lit_store); wstep).
              -- replace (e_nMTF e <? 2400)%Z with true in HG by (symmetry; apply Z.ltb_lt; Z.div_mod_to_equations; lia).
                 enter_with (K988 _ 0%Z _); [st_eq| unfold flag6; rewrite HG; reflexivity| exact HI| assumption| assumption| assumption].
              -- replace (e_nMTF e <? 2400)%Z with false in HG by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
                 enter_with (K988 _ 1%Z _); [st_eq| unfold flag6; rewrite HG; reflexivity| exact HI| assumption| assumption| assumption].
            * (* [comment removed for export] *)
              pose proof (sm_nGroups_lt1200 (e_nMTF e) ltac:(lia)) as HG. change (sm_nGroups (e_nMTF e)) with nG in HG.
              (wstep; lit_store). wstep. wstep.
              enter_with (K988 _ 0%Z _); [st_eq| unfold flag6; rewrite HG; reflexivity| exact HI| assumption| assumption| assumption].
          + pose proof (sm_nGroups_lt600 (e_nMTF e) ltac:(lia)) as HG. change (sm_nGroups (e_nMTF e)) with nG in HG.
            (wstep; lit_store). wstep. wstep.
            enter_with (K988 _ 0%Z _); [st_eq| unfold flag6; rewrite HG; reflexivity| exact HI| assumption| assumption| assumption].
        - pose proof (sm_nGroups_lt200 (e_nMTF e) ltac:(lia)) as HG. change (sm_nGroups (e_nMTF e)) with nG in HG.
          (wstep; lit_store). wstep. wstep.
          enter_with (K988 _ 0%Z _); [st_eq| unfold flag6; rewrite HG; reflexivity| exact HI| assumption| assumption| assumption]. }
    (* [comment removed for export] *)
    intros m2 fl xa0' Hfl HI2 MU2 WM2 MI2. clear HI MI. subst fl.
    lazymatch type of MU2 with munch _ ?mm _ => transport_after_call a0segs mm m2 MU2 WM2 end. clear MU2 WM2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. (wstep; lit_store). wstep. wstep. wstep. wstep. (wstep; lit_store).
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. arun_to 0x8a6d4%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (c100_read mm ltac:(assumption)) as RD end. wstep. clear RD.
    change (bvmap_set 8 (bv_extract 0 64 (le_bytes_to_word c100_bytes)) F) with (smF F).
    (* [comment removed for export] *)
    wstep. (wstep; lit_store). wstep. (wstep; lit_store). wstep. (wstep; lit_store). wstep. (wstep; lit_store). wstep. wstep. (wstep; lit_store).
    (* [comment removed for export] *)
    wstep. wstep. (wstep; lit_store). wstep. (wstep; lit_store). (wstep; lit_store). (wstep; lit_store).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| unfold EHEAD2; rewrite GM; exact EH2| exact LOW| exact HI2| assumption| exact MU| exact WM] end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_smA_setup2 : forall (F' : bvmap 5 word) (m : word -> option byte)
      (v16 v24 w80 w88 w96 w104 w112 w120 w152 w168 w208 : word) (w1344 w1352 w1392 v1400 v1408 : word)
      (ra a1 a2 a3 a4 a5 a6 s2 s3 s5 s8 s11 t6 : word),
    rw_cells a0segs m (P + 16) (LOW0 v16 v24 (Z_to_bv 64 2147548970) (Z_to_bv 64 784720) w80 w88 w96 w104 w112 w120 w152 (Z_to_bv 64 (E + 37708)) w168 (Z_to_bv 64 (SHE + 83))
                                     (Z_to_bv 64 nG) w208 (Z_to_bv 64 A1)) ->
    rw_cells a0segs m (P + 1344) (HI0 w1344 w1352 (Z_to_bv 64 37450) (Z_to_bv 64 (flag6 nG)) w1392 v1400 v1408 (Z_to_bv 64 (E + 676)) (Z_to_bv 64 (E + 672))) ->
    mem_inv a0segs m ->
    (forall m' (t0 t1 a3 a4 a5 a6 a7 : word),
      rw_cells a0segs m' (P + 16) (sm_loA cx e FB SHF SHE v16 v24) -> rw_cells a0segs m' (P + 152) [C8 (Z_to_bv 64 0)] -> rw_cells a0segs m' (P + 160) (sm_loB cx e SHE) ->
      rw_cells a0segs m' (P + 1344) (sm_hi cx e CO FV (Z_to_bv 64 37450) (E + 676) (E + 672)) ->
      mem_inv a0segs m' -> munch Ws1 m m' -> wmono a0segs m m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 0x8a9d8) cP gp tp t0 t1 (Z_to_bv 64 (E + 676)) s0 cP (Z_to_bv 64 FV) (Z_to_bv 64 0) (Z_to_bv 64 24) a3 a4 a5 a6 a7
                            (Z_to_bv 64 (E + 45448)) s3 cSB s5 (Z_to_bv 64 (E + 668)) (Z_to_bv 64 A) (Z_to_bv 64 A1) (Z_to_bv 64 (SHE + 83)) (Z_to_bv 64 nG) s11
                            (Z_to_bv 64 3) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-2147483647)) t6)
                       F' (Z_to_bv 64 0x52ea0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RI ra (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 s2 s3 s5 (Z_to_bv 64 (E + 37708 + 258 * (0 - 1))) s8 (Z_to_bv 64 (E + 37708 + 258 * (0 - 1))) s11 t6)
                     F' (Z_to_bv 64 0x8a914) fc None m (seg_rom a0segs)).
  Proof.
    intros F' m v16 v24 w80 w88 w96 w104 w112 w120 w152 w168 w208 w1344 w1352 w1392 v1400 v1408 ra a1 a2 a3 a4 a5 a6 s2 s3 s5 s8 s11 t6 LOW HI MI K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. openSF. assert (HA : A = (nInUse + 2)%Z) by reflexivity. assert (HM : nMTF = e_nMTF e) by reflexivity.
    pose proof CEP as CEP'. unfold CEIL in CEP'.
    pose proof (sm_nGroups_range (e_nMTF e)) as NGR. change (sm_nGroups (e_nMTF e)) with nG in NGR.
    pose proof (munch_refl Ws1 m) as MU. pose proof (wmono_refl a0segs m) as WM.
    (* [comment removed for export] *)
    (wstep; lit_store). (wstep; flags). wstep. wstep. (wstep; lit_store). wstep. wstep. wstep. (wstep; lit_store).
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. (wstep; lit_store).
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. (wstep; lit_store). wstep. (wstep; lit_store). wstep. (wstep; lit_store). (wstep; lit_store).
    (* [comment removed for export] *)
    wstep. (wstep; lit_store). wstep. wstep. wstep. (wstep; lit_store). (wstep; lit_store). wstep. (wstep; lit_store). wstep.
    (* [comment removed for export] *)
    wstep. wstep. wstep. (wstep; lit_store). (wstep; lit_store). wstep. wstep. wstep. wstep.
    replace (Z.land 18446744073709551615 (flag6 nG mod 18446744073709551616)) with (flag6 nG) in LOW
      by (unfold flag6; destruct (nG =? 6)%Z; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of LOW with rw_cells _ ?mm _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12; ?c13; ?c14; ?c15; ?c16; ?c17; ?c18; ?c19; ?c20; ?c21; ?c22; ?c23; ?c24; ?c25; ?c26] =>
      change (rw_cells a0segs mm (P + 16) ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16] ++ ([c17] ++ [c18; c19; c20; c21; c22; c23; c24; c25; c26]))) in LOW end.
    apply (proj1 (rw_cells_app2 _ _ _ _ _)) in LOW. destruct LOW as [LOA LOW]. apply (proj1 (rw_cells_app2 _ _ _ _ _)) in LOW. destruct LOW as [ITER LOB].
    cbn [cells_size csize Nat.add] in ITER, LOB.
    replace (P + 16 + Z.of_nat 136)%Z with (P + 152)%Z in ITER, LOB by lia. replace (P + 152 + Z.of_nat 8)%Z with (P + 160)%Z in LOB by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _ _ _ _); [st_eq| | exact ITER| | | assumption| exact MU| exact WM] end.
    - lazymatch type of LOA with rw_cells _ _ _ ?L => replace (sm_loA cx e FB SHF SHE v16 v24) with L; [exact LOA| unfold sm_loA; cbv zeta; CmpFast.rlf] end.
    - lazymatch type of LOB with rw_cells _ _ _ ?L => replace (sm_loB cx e SHE) with L; [exact LOB| unfold sm_loB; cbv zeta; CmpFast.rlf] end.
    - lazymatch type of HI with rw_cells _ _ _ ?L => replace (sm_hi cx e CO FV (Z_to_bv 64 37450) (E + 676) (E + 672)) with L; [exact HI| unfold sm_hi; cbv zeta; CmpFast.rlf] end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_smA_in3z : forall (m : word -> option byte)
      (w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w152 w160 w168 w184 w200 w208 w216 : word) (w1344 w1352 w1360 w1368 w1392 w1400 w1408 w1424 w1432 : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 s10 s11 t3 t4 t5 t6 : word),
    u8arr a0segs m (E + 37708) (ovb (smA_len e) (jseg J 37708 1548) 1548) ->
    u32arr a0segs m (E + 672) (ovw mf (jseg J 672 1032) 258) ->
    rw_cells a0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells a0segs m (P + 16) (LOW0 w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w152 w160 w168 w184 w200 w208 w216) ->
    rw_cells a0segs m (P + 1344) (HI0 w1344 w1352 w1360 w1368 w1392 w1400 w1408 w1424 w1432) ->
    ro_cells a0segs m 0xc06b8 [C8 (Z_to_bv 64 0xbf950)] ->
    mem_inv a0segs m -> shzW a0segs W3 m E (E + ESTATE_SIZE) ->
    (forall m' (v16 v24 : word) (t0 t1 a3 a4 a5 a6 a7 s3 s5 s11 t6 : word),
      u8arr a0segs m' (E + 37708) (ovb (ip_len (smA_ip e)) (jseg J 37708 1548) 1548) ->
      u32arr a0segs m' (E + 672) (ovw mf (jseg J 672 1032) 258) ->
      rw_cells a0segs m' (E + 640) (EHEAD2 cx g e) ->
      rw_cells a0segs m' (P + 16) (sm_loA cx e FB SHF SHE v16 v24) -> rw_cells a0segs m' (P + 152) [C8 (Z_to_bv 64 0)] -> rw_cells a0segs m' (P + 160) (sm_loB cx e SHE) ->
      rw_cells a0segs m' (P + 1344) (sm_hi cx e CO FV (Z_to_bv 64 37450) (E + 676) (E + 672)) ->
      mem_inv a0segs m' -> munch W3 m m' -> wmono a0segs m m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 0x8a9d8) cP gp tp t0 t1 (Z_to_bv 64 (E + 676)) s0 cP (Z_to_bv 64 FV) (Z_to_bv 64 0) (Z_to_bv 64 24) a3 a4 a5 a6 a7
                            (Z_to_bv 64 (E + 45448)) s3 cSB s5 (Z_to_bv 64 (E + 668)) (Z_to_bv 64 A) (Z_to_bv 64 A1) (Z_to_bv 64 (SHE + 83)) (Z_to_bv 64 nG) s11
                            (Z_to_bv 64 3) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-2147483647)) t6)
                       (smF F) (Z_to_bv 64 0x52ea0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7
                          (Z_to_bv 64 (E + 37708 + 258 * 5)) s3 cSB (Z_to_bv 64 1) (Z_to_bv 64 (E + 668)) (Z_to_bv 64 (-1)) (Z_to_bv 64 A1) s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8a5d4) fc None m (seg_rom a0segs)).
  Proof.
    intros m w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w152 w160 w168 w184 w200 w208 w216 w1344 w1352 w1360 w1368 w1392 w1400 w1408 w1424 w1432
           ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 s10 s11 t3 t4 t5 t6 LEN MTF EH2 LOW HI GOT MI SHe K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. openSF. assert (HA : A = (nInUse + 2)%Z) by reflexivity. assert (HM : nMTF = e_nMTF e) by reflexivity.
    pose proof CEP as CEP'. unfold CEIL in CEP'.
    pose proof (sm_nGroups_range (e_nMTF e)) as NGR. change (sm_nGroups (e_nMTF e)) with nG in NGR.
    pose proof (munch_refl W3 m) as MU0. pose proof (wmono_refl a0segs m) as WM0.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep; if_cases Kr; zify_cond_z Kr; [exfalso; lia|].
    (* [comment removed for export] *)
    enter_with (A0_smA_setup1 m
                  w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w152 w160 w168 w184 w200 w208 w216 w1344 w1352 w1360 w1368 w1392 w1400 w1408 w1424 w1432);
      [st_eq| exact EH2| exact LOW| exact HI| exact GOT| exact MI| |].
    { eapply (shzW_sub a0segs W3 _ m m); [exact SHe| exact MU0| a_sub_fp| lia| lia]. }
    clear EH2 LOW HI GOT MI. intros m2 v16 v24 v1400 v1408 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs3 xs8 xt6 EH2 LOW HI MI2 MU2 WM2.
    transport_after_call a0segs m m2 MU2 WM2. clear MU2 WM2.
    (* [comment removed for export] *)
    pose proof (A0_smA_iloop cx g e Q gp tp s0 (smF F) fc P SHE CX SF AE (Z.to_nat nG) 0%nat m2 m2) as LOOP.
    cbv zeta in LOOP. change (sip_k e 0) with (sip0 e) in LOOP. cbn [ip_nPart ip_remF ip_gs ip_len sip0] in LOOP.
    replace (0 + Z.to_nat nG)%nat with (Z.to_nat nG) in LOOP by lia. rewrite <- IPT in LOOP. change (sm_init_tables 8 mf nG A (sip0 e)) with (smA_ip e) in LOOP.
    enter_with LOOP;
      [st_eq| lia| lia| lia| exact LEN| exact MTF| exact EH2| exact MI2| apply munch_refl| apply wmono_refl| | | | | |].
    { eapply (shzW_sub a0segs W3 _ m m2); [exact SHe| exact MU0| a_sub_fp| lia| lia]. }
    { eapply (frdW_cell_at a0segs _ _ (P + 16)%Z _ 112%nat); [apply frdW_intro; [exact LOW| cbn [disjoint_from]; simpl_sizes; Lib.Step.slia]| reflexivity| lia]. }
    { eapply (frdW_cell_at a0segs _ _ (P + 16)%Z _ 120%nat); [apply frdW_intro; [exact LOW| cbn [disjoint_from]; simpl_sizes; Lib.Step.slia]| reflexivity| lia]. }
    { eapply (frdW_cell_at a0segs _ _ (P + 16)%Z _ 184%nat); [apply frdW_intro; [exact LOW| cbn [disjoint_from]; simpl_sizes; Lib.Step.slia]| reflexivity| lia]. }
    { eapply (frdW_cell_at a0segs _ _ (P + 1344)%Z _ 72%nat); [apply frdW_intro; [exact HI| cbn [disjoint_from]; simpl_sizes; Lib.Step.slia]| reflexivity| lia]. }
    clear LOOP. intros m3 ya1 ya2 ya3 ya4 ya5 ya6 ys2 ys3 ys8 LEN3 MTF3 EH2' MI3 MU3 WM3.
    clear LEN MTF EH2 MI2. transport_after_call a0segs m2 m3 MU3 WM3. clear MU3 WM3. unfold EHEAD2 in EH2'.
    (* [comment removed for export] *)
    enter_with (A0_smA_setup2 (smF F) m3 v16 v24 w80 w88 w96 w104 w112 w120 w152 w168 w208 w1344 w1352 w1392 v1400 v1408);
      [st_eq| exact LOW| exact HI| exact MI3|].
    clear LOW HI MI3. intros m4 zt0 zt1 za3 za4 za5 za6 za7 LOA ITER LOB HI MI4 MU4 WM4.
    transport_after_call a0segs m3 m4 MU4 WM4. clear MU4 WM4.
    enter_with (K m4 v16 v24 _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact LEN3| exact MTF3| unfold EHEAD2; exact EH2'| exact LOA| exact ITER| exact LOB| exact HI| assumption| exact MU0| exact WM0].
  Qed.
End A0SMZ.
End ACeilS1.
