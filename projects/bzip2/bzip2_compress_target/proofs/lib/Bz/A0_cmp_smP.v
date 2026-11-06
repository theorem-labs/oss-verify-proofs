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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Ltac sb_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) => rewrite (le1_lit w); mem_after_store
  end.
Ltac sb_z :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 0))) _) => change (le1 (Z_to_bv 64 0)) with [z8]; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 0)) _) => change (Z_to_le_bytes 1 0) with [z8]; mem_after_store
  end.
Ltac sb_4 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 4))) _) => change (le1 (Z_to_bv 64 4)) with [Z_to_bv 8 4]; mem_after_store
  end.

(* [comment removed for export] *)
Ltac split_at_cb8 cs :=
  lazymatch cs with
  | CB 8 ?bs :: ?post => constr:((@nil cell, bs, post))
  | ?c :: ?rest => let r := split_at_cb8 rest in lazymatch r with (?pre, ?bs, ?post) => constr:((c :: pre, bs, post)) end
  end.
Ltac cb8_all H :=
  repeat (lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
            let r := split_at_cb8 cs in
            lazymatch r with (?pre, ?bs, ?post) => apply (rw_cells_CB8_C8 segs m A pre bs post) in H; cbn [app] in H end end).

(* [comment removed for export] *)
Lemma ex_words_len : forall n (k : list word -> Prop), ex_words n k -> ex_words n (fun ws => k ws /\ length ws = n).
Proof.
  induction n as [|n IH]; intros k H; cbn in *; [split; [exact H| reflexivity]|].
  destruct H as [w H]. exists w. eapply ex_words_mono; [| exact (IH _ H)]. intros ws [Hk Hl]. split; [exact Hk| cbn; lia].
Qed.
Lemma cells_size_map_C8 : forall ws : list word, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. lia. Qed.
Lemma rw_cells_CB_C8s : forall n segs m A pre bs post,
  rw_cells segs m A (pre ++ CB (8 * n) bs :: post) ->
  ex_words n (fun ws => rw_cells segs m A (pre ++ map C8 ws ++ post)).
Proof.
  intros n segs m A pre bs post H.
  change (pre ++ CB (8 * n) bs :: post) with (pre ++ ([CB (8 * n) bs] ++ post)) in H.
  apply (proj1 (rw_cells_app2 _ _ _ _ _)) in H. destruct H as [Hpre H].
  apply (proj1 (rw_cells_app2 _ _ _ _ _)) in H. destruct H as [Hcb Hpost].
  pose proof (proj1 (proj1 Hcb)) as W. cbn in W. destruct W as [L _].
  pose proof (u8arr_of_rw_cells segs m _ _ _ Hcb) as U.
  eapply ex_words_mono; [| eapply ex_words_len; eapply (u8arr_C8s n); [exact U| exact L]].
  intros ws [Hws Hl]. apply (proj2 (rw_cells_app2 _ _ _ _ _)). split; [exact Hpre|].
  apply (proj2 (rw_cells_app2 _ _ _ _ _)). split; [exact Hws|].
  rewrite cells_size_map_C8, Hl. cbn [cells_size csize Nat.add] in Hpost. rewrite Nat.add_0_r in Hpost. exact Hpost.
Qed.

(* [comment removed for export] *)
Ltac abs_skipn H base :=
  lazymatch type of H with
  | context [skipn ?a base] => let r := fresh "rr" in set (r := skipn a base) in H; abs_skipn H r
  | _ => idtac
  end.

Section A0SMP.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE CO FV FB SHF : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SF : smA_facts e. Hypothesis GM : g_mtf g = true.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1616 <= 18446744073709551616)%Z.
  Hypothesis FBL : (0 < FB)%Z. Hypothesis FBH : (FB + 160 <= CEIL)%Z. Hypothesis ECO : CO = (FB + 32)%Z. Hypothesis EFV : FV = (FB + 64)%Z.
  Hypothesis SHL : (SH_LO <= SHF)%Z. Hypothesis SHH : (SHF + 20 <= SH_HI)%Z.
  Hypothesis AE : sanchor (c_E cx) SHE. Hypothesis AF : sanchor FB SHF.
  (* [comment removed for export] *)
  Hypothesis SEFB : id ((c_E cx + 55768 <= FB)%Z \/ (FB + 160 <= c_E cx)%Z).
  Hypothesis SESH : id ((c_E cx + 55768 <= SHF)%Z \/ (SHF + 20 <= c_E cx)%Z).
  Hypothesis SFSH : id ((FB + 160 <= SHF)%Z \/ (SHF + 20 <= FB)%Z).
  Hypothesis SPSH : id ((SHF + 20 <= P)%Z \/ (P + 1616 <= SHF)%Z).
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e). Notation nInUse := (e_nInUse e).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  Ltac openSF :=
    let H := fresh "SFL" in pose proof SF as H; unfold smA_facts in H; cbv zeta in H; cps_destruct H as (?NI & ?NM & ?MFD & ?IPK & ?IPT).
  (* [comment removed for export] *)

  Notation LOWJ w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 :=
    [C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 w136; C8 (Z_to_bv 64 E);
     C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208; C8 w216; C8 w224].
  Notation LOW0 w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w152 w160 w168 w184 w200 w208 w216 :=
    [C8 w16; C8 w24; C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 (FB + 128)); C8 (Z_to_bv 64 SHF); C8 w64; C8 w72;
     C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 (Z_to_bv 64 (SHE + 82)); C8 (Z_to_bv 64 (E + 656)); C8 (Z_to_bv 64 E);
     C8 w152; C8 w160; C8 w168; C8 (Z_to_bv 64 (E + 668)); C8 w184; C8 (Z_to_bv 64 A); C8 w200; C8 w208; C8 w216; C8 (Z_to_bv 64 nInUse)].
  Notation HI0 w1344 w1352 w1360 w1368 w1392 w1400 w1408 w1424 w1432 :=
    [C8 w1344; C8 w1352; C8 w1360; C8 w1368; C8 (Z_to_bv 64 CO); C8 (Z_to_bv 64 FV); C8 w1392; C8 w1400; C8 w1408; C8 (Z_to_bv 64 A); C8 w1424; C8 w1432].
  Notation Wp2 := [(P + 16, P + 232); (P + 1344, P + 1440); (P + 1464, P + 1472); (FB, FB + 24); (SHF, SHF + 20)]%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_smA_in2 : forall (m : word -> option byte)
      (w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 : word)
      (w1344 w1352 w1360 w1368 w1376 w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1464 h0 h1 h2 : word) (bs : list byte)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m E (EHEAD1 cx g e) -> rw_cells a0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells a0segs m (P + 16) (LOWJ w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224) ->
    rw_cells a0segs m (P + 1344) [C8 w1344; C8 w1352; C8 w1360; C8 w1368; C8 w1376; C8 w1384; C8 w1392; C8 w1400; C8 w1408; C8 w1416; C8 w1424; C8 w1432] ->
    rw_cells a0segs m (P + 1464) [C8 w1464] ->
    rw_cells a0segs m FB [C8 h0; C8 h1; C8 h2] -> rw_cells a0segs m SHF [CB 20 bs] ->
    mem_inv a0segs m -> shzW a0segs Wp2 m E (E + ESTATE_SIZE) ->
    (forall m' (t1 t2 a3 a4 a5 a6 s3' : word),
      rw_cells a0segs m' E (EHEAD1 cx g e) -> rw_cells a0segs m' (E + 640) (EHEAD2 cx g e) ->
      rw_cells a0segs m' (P + 16) (LOW0 w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w152 w160 w168 w184 w200 w208 w216) ->
      rw_cells a0segs m' (P + 1344) (HI0 w1344 w1352 w1360 w1368 w1392 w1400 w1408 w1424 w1432) ->
      rw_cells a0segs m' (P + 1464) [C8 (Z_to_bv 64 FB)] ->
      rw_cells a0segs m' FB [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x148b3); C8 (Z_to_bv 64 0x8a3ac)] -> rw_cells a0segs m' SHF sm_shadow ->
      mem_inv a0segs m' -> munch Wp2 m m' -> wmono a0segs m m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 0x8a5d4) cP gp tp (Z_to_bv 64 E) t1 t2 s0 cP (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 15) (Z_to_bv 64 A) a3 a4 a5 a6 (Z_to_bv 64 nInUse)
                            (Z_to_bv 64 (E + 37708)) s3' cSB (Z_to_bv 64 6) (Z_to_bv 64 (E + 668)) (Z_to_bv 64 (-1)) (Z_to_bv 64 A1) s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x52ea0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP (Z_to_bv 64 FB) a1 a2 a3 a4 a5 a6 a7 s2 s3 cSB s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8a420) fc None m (seg_rom a0segs)).
  Proof.
    intros m w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224
           w1344 w1352 w1360 w1368 w1376 w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1464 h0 h1 h2 bs
           ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 EH1 EH2 LOW HI S1464 HD SH20 MI SHe K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. openSF. assert (HA : A = (nInUse + 2)%Z) by reflexivity.
    pose proof CEP as CEP'. pose proof FBH as FBH'. unfold CEIL in CEP', FBH'. unfold SH_LO, SH_HI in SHL, SHH. unfold ESTATE_SIZE in SHe.
    pose proof (munch_refl Wp2 m) as MU. pose proof (wmono_refl a0segs m) as WM.
    unfold EHEAD1 in EH1. unfold EHEAD2 in EH2. rewrite GM in EH1, EH2.
    apply (rw_cells_split_CB a0segs _ _ [] 20 _ [] [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat) in SH20; [| reflexivity]. cbn [mk_CB_cells app] in SH20.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep; if_cases Kz; zify_cond_z Kz; [| exfalso; lia].
    (* [comment removed for export] *)
    arun_to 0x8a484%Z. wstep. lit_store. wstep. lit_store. wstep. lit_store.
    (* [comment removed for export] *)
    wstep. wstep. sh_norm.
    (* [comment removed for export] *)
    wstep. sb_lit. wstep. sb_lit. wstep. sb_lit. wstep. sb_lit.
    wstep.
    wstep. sb_z. wstep. sb_4. wstep. sb_lit. wstep. sb_lit.
    wstep. sb_lit. wstep. sb_lit. wstep. sb_z. wstep. sb_z.
    wstep. sb_lit. wstep. sb_lit. wstep. sb_z. wstep. sb_lit.
    wstep. sb_lit. wstep. sb_lit. wstep. sb_lit. wstep. sb_lit. wstep. sb_lit. wstep. sb_lit.
    (* [comment removed for export] *)
    arun_to 0x8a500%Z. (wstep; lit_store). arun_to 0x8a50c%Z. (wstep; lit_store).
    (* [comment removed for export] *)
    wstep. wstep. wstep. sh_norm. (wstep; lit_store).
    (* [comment removed for export] *)
    arun_to 0x8a534%Z. (wstep; lit_store). wstep. wstep. wstep. (wstep; lit_store). wstep.
    wstep; if_cases Kv; zify_cond_z Kv; [| exfalso; lia].
    (* [comment removed for export] *)
    arun_to 0x8a568%Z. (wstep; lit_store). wstep. try rewrite (sx32_of_Z nInUse) by lia. wstep. try rewrite (sx32_of_Z (nInUse + 2)) by lia.
    (wstep; lit_store). (wstep; lit_store). wstep; if_cases Kp; zify_cond_z Kp; [| exfalso; lia].
    (* [comment removed for export] *)
    wstep. (wstep; lit_store). wstep. (wstep; lit_store). (wstep; lit_store). wstep. (wstep; lit_store).
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. (wstep; lit_store).
    (* [comment removed for export] *)
    wstep; if_cases Kn; zify_cond_z Kn; [exfalso; lia|].
    wstep. wstep. wstep. wstep.
    rewrite <- HA in LOW, HI |- *. rewrite <- ECO, <- EFV in HI.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _ _ _ _); [st_eq| unfold EHEAD1; rewrite GM; exact EH1| unfold EHEAD2; rewrite GM; exact EH2| exact LOW| exact HI| exact S1464| exact HD| exact SH20| assumption| exact MU| exact WM] end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma land_m32 : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (32 * (x / 32))%Z.
  Proof.
    intros x Hx. change 18446744073709551584%Z with (Z.ldiff (Z.ones 64) (Z.ones 5)).
    rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
    rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
    change (2^5)%Z with 32%Z. lia.
  Qed.
End A0SMP.

Section A0SMP1.
  Variables (cx : cctx) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P lo : Z).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx).
  Hypothesis CEL : (CEIL <= lo)%Z. Hypothesis PLO : (lo <= P)%Z.
  Hypothesis USPQ : exists q, usp = (16 * q)%Z. Hypothesis PQ : exists q, P = (32 * q)%Z.
  Hypothesis PCASE : (P = usp - 1600 \/ P = usp - 1616)%Z.
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).

  (* [comment removed for export] *)
  Ltac in1_walk FR ST ELAND GOT SBV GOTU UARV :=
      cbn [mk_CB_cells app] in FR;
      lazymatch type of FR with context [skipn _ ?base] => is_var base; abs_skipn FR base end;
      repeat lazymatch type of FR with context [CB ?n (firstn ?a ?b)] => let j := fresh "jj" in set (j := firstn a b) in FR; clearbody j end;
      lazymatch type of FR with rw_cells _ _ _ [CB 232 ?b0; ?c1; CB 96 ?b2; ?c3; CB 8 ?b4; ?c5; CB 112 ?b6] =>
        let FR1 := fresh "FR1" in
        destruct (rw_cells_CB_C8s 29 a0segs _ _ [] b0 [c1; CB 96 b2; c3; CB 8 b4; c5; CB 112 b6] FR)
          as (w0 & w8 & w16 & w24 & w32 & w40 & w48 & w56 & w64 & w72 & w80 & w88 & w96 & w104 & w112 & w120 & w128 & w136 & w144 & w152 & w160 & w168 & w176 & w184 & w192 & w200 & w208 & w216 & w224 & FR1);
        clear FR; cbn [map app] in FR1;
        let pre := constr:([C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 w136; C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208; C8 w216; C8 w224; c1]) in
        let FR2 := fresh "FR2" in
        destruct (rw_cells_CB_C8s 12 a0segs _ _ pre b2 [c3; CB 8 b4; c5; CB 112 b6] FR1)
          as (w1344 & w1352 & w1360 & w1368 & w1376 & w1384 & w1392 & w1400 & w1408 & w1416 & w1424 & w1432 & FR2);
        clear FR1; cbn [map app] in FR2;
        let pre2 := constr:([C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 w136; C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208; C8 w216; C8 w224; c1;
                             C8 w1344; C8 w1352; C8 w1360; C8 w1368; C8 w1376; C8 w1384; C8 w1392; C8 w1400; C8 w1408; C8 w1416; C8 w1424; C8 w1432; c3; CB 8 b4; c5]) in
        let FR3 := fresh "FR3" in
        destruct (rw_cells_CB_C8s 14 a0segs _ _ pre2 b6 [] FR2)
          as (v1488 & v1496 & v1504 & v1512 & v1520 & v1528 & v1536 & v1544 & v1552 & v1560 & v1568 & v1576 & v1584 & v1592 & FR3);
        clear FR2; cbn [map app] in FR3; rename FR3 into FR
      end;
      cb8_all FR;
      (* [comment removed for export] *)
      wstep; wstep; lit_store; do 13 wstep; wstep; wstep; wstep;
      rewrite ELAND;
      first [ replace (usp + -1600)%Z with P in FR, ST by lia | replace (usp + -1616)%Z with P in FR, ST by lia ];
      (* [comment removed for export] *)
      wstep; arun_to 0x8a410%Z; wstep;
      (* [comment removed for export] *)
      arun_to 0x3df20%Z.

  Lemma A0_smA_in1 : forall (m : word -> option byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    stk a0segs m lo usp -> mem_inv a0segs m -> aconsts A0C m -> aconsts_uar A0C m ->
    (forall m' (jsp j1440 jg : list byte) (ng : nat) (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 : word)
            (w1344 w1352 w1360 w1368 w1376 w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1464 : word) (a1 a2 : word),
      (P + 1472 + Z.of_nat ng + 112 = usp)%Z ->
      rw_cells a0segs m' P
        [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 w136; C8 (Z_to_bv 64 E);
         C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208; C8 w216; C8 w224; CB 1112 jsp;
         C8 w1344; C8 w1352; C8 w1360; C8 w1368; C8 w1376; C8 w1384; C8 w1392; C8 w1400; C8 w1408; C8 w1416; C8 w1424; C8 w1432; CB 24 j1440; C8 w1464; CB ng jg;
         C8 (reg_get F 8); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk a0segs m' lo P -> mem_inv a0segs m' -> munch [(P, usp)]%Z m m' -> wmono a0segs m m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 0x8a420) cP gp tp t0 t1 t2 sp cP (Z_to_bv 64 160) a1 a2 a3 a4 a5 a6 a7 s2 s3 cSB s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x3df20) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8a3ac) fc None m (seg_rom a0segs)).
  Proof.
    intros m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI AC AU K.
    destruct AC as [GOT SBV]. destruct AU as [GOTU UARV].
    cbn [aci_segs aci_c aci_got_sh aci_shvar aci_got_uar aci_uarvar A0C ci_segs] in GOT, SBV, GOTU, UARV.
    bz_ceil. unfold CEIL in CEL. destruct USPQ as [qu EU]. destruct PQ as [qp EP].
    pose proof (bv_unsigned_in_range _ sp) as RSP. unfold bv_modulus in RSP. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in RSP.
    pose proof (munch_refl [(P, usp)]%Z m) as MU. pose proof (wmono_refl a0segs m) as WM.
    assert (ELAND : Z.land (usp + -1600) 18446744073709551584 = P).
    { rewrite land_m32 by lia. clear - PCASE EU EP. Z.div_mod_to_equations. lia. }
    destruct PCASE as [EPc|EPc].
    - (* [comment removed for export] *)
      carve_frame 1600%nat ST.
      apply (rw_cells_split_CB a0segs _ _ [] 1600 _ [] [232;1112;96;24;8;16;112]%nat) in FR; [| reflexivity].
      in1_walk FR ST ELAND GOT SBV GOTU UARV.
      eapply (K _ _ _ _ 16%nat); [lia| exact FR| exact ST| assumption| exact MU| exact WM].
    - (* [comment removed for export] *)
      carve_frame 1616%nat ST.
      apply (rw_cells_split_CB a0segs _ _ [] 1616 _ [] [232;1112;96;24;8;32;112]%nat) in FR; [| reflexivity].
      in1_walk FR ST ELAND GOT SBV GOTU UARV.
      eapply (K _ _ _ _ 32%nat); [lia| exact FR| exact ST| assumption| exact MU| exact WM].
  Qed.
End A0SMP1.
End ACeilS1.
