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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_cbV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

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

Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)

Lemma land_m32 : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (32 * (x / 32))%Z.
Proof.
  intros x Hx. change 18446744073709551584%Z with (Z.ldiff (Z.ones 64) (Z.ones 5)).
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^5)%Z with 32%Z. lia.
Qed.

Section A0CBP1.
  Variable X : cbenv. Variable P : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : cbenv_ok X.
  (* [comment removed for export] *)
  Hypothesis YPl : (ce_lo X <= P)%Z. Hypothesis YPh : (P + 224 <= bv_unsigned (ce_sp X))%Z. Hypothesis YPa : (bv_unsigned (ce_sp X) <= P + 240)%Z.
  Notation usp := (bv_unsigned (ce_sp X)).
  Notation E := (c_E (ce_cx X)).
  Notation gp := (ce_gp X). Notation tp := (ce_tp X). Notation F := (ce_F X). Notation fc := (ce_fc X). Notation lo := (ce_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_cb_P1 : forall (qP : Z) (m : word -> option byte) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (P = 32 * qP)%Z ->
    stk a0segs m lo usp -> mem_inv a0segs m -> aconsts A0C m -> aconsts_uar A0C m ->
    (forall m' (sl : cbsl) (a1 a2 : word),
      rw_cells a0segs m' P (cbsl_cells sl) ->
      stk a0segs m' (P + 120) (usp + -104) -> rw_cells a0segs m' (usp + -104) (CSAVED X) ->
      stk a0segs m' lo P -> mem_inv a0segs m' -> munch [(P, usp)]%Z m m' -> wmono a0segs m m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 0x88a84) (Z_to_bv 64 P) gp tp t0 t1 t2 (ce_sp X) (Z_to_bv 64 P) (Z_to_bv 64 352) a1 a2 a3 a4 a5 a6 a7
                            (il_w (ce_il X)) cSB (Z_to_bv 64 E) (ce_s5 X) (ce_s6 X) (ce_s7 X) (ce_s8 X) (ce_s9 X) (ce_s10 X) (ce_s11 X) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x3e0bc) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (ce_ra X) (ce_sp X) gp tp t0 t1 t2 (ce_s0 X) (ce_s1 X) (Z_to_bv 64 E) (il_w (ce_il X)) a2 a3 a4
                          a5 a6 a7 (ce_s2 X) (ce_s3 X) (ce_s4 X) (ce_s5 X) (ce_s6 X) (ce_s7 X) (ce_s8 X) (ce_s9 X) (ce_s10 X) (ce_s11 X) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88a10) fc None m (seg_rom a0segs)).
  Proof.
    intros qP m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EqP ST MI AC AU K.
    cbenv_open XOK. clear CX SEP.
    destruct AC as [GOT SBV]. destruct AU as [GOTU UARV].
    cbn [aci_segs aci_c aci_got_sh aci_shvar aci_got_uar aci_uarvar A0C ci_segs] in GOT, SBV, GOTU, UARV.
    pose proof (munch_refl [(P, usp)]%Z m) as MU. pose proof (wmono_refl a0segs m) as WM.
    assert (CASE : (P = usp - 224 \/ P = usp - 240)%Z) by lia.
    assert (ELAND : Z.land (usp + -224) 18446744073709551584 = P).
    { rewrite land_m32 by lia. clear - CASE EqP ALS. Z.div_mod_to_equations. lia. }
    destruct CASE as [EP|EP].
    - (* [comment removed for export] *)
      carve_frame 224%nat ST.
      apply (rw_cells_split_CB a0segs _ _ [] 224 _ [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
      cbn [mk_CB_cells app] in FR.
      (* [comment removed for export] *)
      wstep. wstep. lit_store. do 13 wstep. wstep. wstep.
      rewrite ELAND. replace (usp + -224)%Z with P in FR, ST by lia.
      (* [comment removed for export] *)
      arun_to 0x3e0bc%Z.
      cb8_all FR.
      destruct (rw_cells_cutZ a0segs _ P _ 15%nat FR) as [SLa SVc]. cbn [firstn skipn cells_size csize Nat.add] in SLa, SVc. change (Z.of_nat 120) with 120%Z in SVc.
      replace (P + 120)%Z with (usp + -104)%Z in SVc by lia.
      lazymatch type of SLa with rw_cells _ _ _ [C8 ?c0; C8 ?c1; C8 ?c2; C8 ?c3; C8 ?c4; C8 ?c5; C8 ?c6; C8 ?c7; C8 ?c8; C8 ?c9; C8 ?c10; C8 ?c11; C8 ?c12; C8 ?c13; C8 ?c14] =>
        eapply (K _ (CBSL c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14)); [exact SLa| | exact SVc| exact ST| assumption| exact MU| exact WM] end.
      split; [lia|]. split; [lia|]. intros a Ha. lia.
    - (* [comment removed for export] *)
      carve_frame 240%nat ST.
      apply (rw_cells_split_CB a0segs _ _ [] 240 _ [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8; 8;8; 8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
      cbn [mk_CB_cells app] in FR.
      wstep. wstep. lit_store. do 13 wstep. wstep. wstep.
      rewrite ELAND. replace (usp + -240)%Z with P in FR, ST by lia.
      arun_to 0x3e0bc%Z.
      cb8_all FR.
      destruct (rw_cells_cutZ a0segs _ P _ 15%nat FR) as [SLa R1]. cbn [firstn skipn cells_size csize Nat.add] in SLa, R1. change (Z.of_nat 120) with 120%Z in R1.
      destruct (rw_cells_cutZ a0segs _ _ _ 2%nat R1) as [GAPc SVc]. cbn [firstn skipn cells_size csize Nat.add] in GAPc, SVc. change (Z.of_nat 16) with 16%Z in SVc.
      replace (P + 120 + 16)%Z with (usp + -104)%Z in SVc by lia.
      pose proof (stk_of_rw_cells a0segs _ _ _ GAPc) as GAPs. cbn [cells_size csize Nat.add] in GAPs. change (Z.of_nat 16) with 16%Z in GAPs.
      replace (P + 120 + 16)%Z with (usp + -104)%Z in GAPs by lia.
      lazymatch type of SLa with rw_cells _ _ _ [C8 ?c0; C8 ?c1; C8 ?c2; C8 ?c3; C8 ?c4; C8 ?c5; C8 ?c6; C8 ?c7; C8 ?c8; C8 ?c9; C8 ?c10; C8 ?c11; C8 ?c12; C8 ?c13; C8 ?c14] =>
        eapply (K _ (CBSL c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14)); [exact SLa| exact GAPs| exact SVc| exact ST| assumption| exact MU| exact WM] end.
  Qed.
End A0CBP1.

(* [comment removed for export] *)
Lemma cells_bytes_C1s : forall bs, cells_bytes (map C1 bs) = bs.
Proof. induction bs as [|b bs IH]; [reflexivity| cbn [map cells_bytes cbytes app]; rewrite IH; reflexivity]. Qed.
Lemma cells_size_C1s : forall bs, cells_size (map C1 bs) = length bs.
Proof. induction bs as [|b bs IH]; [reflexivity| cbn [map cells_size csize length Nat.add]; rewrite IH; reflexivity]. Qed.
Lemma cells_wf_C1s : forall bs, cells_wf (map C1 bs).
Proof. induction bs as [|b bs IH]; [exact I| cbn [map cells_wf cell_wf]; split; [exact I| exact IH]]. Qed.
Lemma rw_cells_CB_C1s : forall segs m A n bs, rw_cells segs m A [CB n bs] -> rw_cells segs m A (map C1 bs) /\ length bs = n.
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize Nat.add] in Hw. rewrite Nat.add_0_r in Hw.
  split; [| exact Hl]. split; [split; [apply cells_wf_C1s| rewrite cells_bytes_C1s; exact Hb]| rewrite cells_size_C1s, Hl; exact Hw].
Qed.

Section A0CBP2.
  Variable X : cbenv. Variable Y : acenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : cbenv_ok X. Hypothesis YOK : acenv_ok X Y. Hypothesis YOFF : acenv_offsh X Y.
  Hypothesis AX : sanchor (ac_FB Y) (ac_SHF Y). Hypothesis AE : sanchor (c_E (ce_cx X)) (ac_SHE Y).
  Notation usp := (bv_unsigned (ce_sp X)). Notation P := (ac_P Y). Notation FB := (ac_FB Y). Notation SHF := (ac_SHF Y). Notation SHE := (ac_SHE Y).
  Notation E := (c_E (ce_cx X)).
  Notation gp := (ce_gp X). Notation tp := (ce_tp X). Notation F := (ce_F X). Notation fc := (ce_fc X). Notation lo := (ce_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).

  Ltac sbf8 := wstep; change (le1 (Z_to_bv 64 (-8))) with [cf8b]; mem_after_store.
  Ltac sbf1 := wstep; change (le1 (Z_to_bv 64 (-15))) with [cf1b]; mem_after_store.
  Ltac sbf3 := wstep; change (le1 (Z_to_bv 64 (-13))) with [cf3b]; mem_after_store.
  Ltac sbx := first [sbf8 | sbf1 | sbf3].

  (* [comment removed for export] *)
  Lemma A0_cb_P2sb : forall (me m : word -> option byte) (bs : list byte)
      (ra sp t0 t1 t2 s0 s1 a2 a3 a5 a6 a7 s2 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m SHF [CB 44 bs] -> mem_inv a0segs m -> munch [(SHF, SHF + 44)]%Z me m -> wmono a0segs me m ->
    (forall m', rw_cells a0segs m' (SHF + 4) (yysh cf8b) -> mem_inv a0segs m' -> munch [(SHF, SHF + 44)]%Z me m' -> wmono a0segs me m' ->
       evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SHE + -2147450867)) (Z_to_bv 64 (-13)) a2 (Z_to_bv 64 (E + 108)) (Z_to_bv 64 (-15)) a5 a6 a7
                             s2 cSB (Z_to_bv 64 E) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x88ba4) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-8)) (Z_to_bv 64 (-13)) a2 a3 (Z_to_bv 64 (-15)) a5 a6 a7
                          s2 cSB (Z_to_bv 64 E) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88aec) fc None m (seg_rom a0segs)).
  Proof.
    intros me m bs ra sp t0 t1 t2 s0 s1 a2 a3 a5 a6 a7 s2 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 RZ MI MU WMo K.
    cbenv_open XOK. cb_ranges CX. clear CX SEP.
    destruct (rw_cells_CB_C1s a0segs _ _ _ _ RZ) as [RZc L]. clear RZ. rename RZc into RZ.
    do 44 (destruct bs as [|? bs]; [discriminate L| cbn [length] in L; apply Nat.succ_inj in L]). destruct bs; [clear L| discriminate L].
    cbn [map] in RZ.
    do 4 sbx. wstep. do 32 sbx. wstep. do 8 sbx.
    sh_norm.
    destruct (rw_cells_cutZ a0segs _ _ _ 4 RZ) as [_ RZ1]. cbn [firstn skipn cells_size csize Nat.add] in RZ1. change (Z.of_nat 4) with 4%Z in RZ1.
    destruct (rw_cells_cutZ a0segs _ _ _ 32 RZ1) as [RZ2 _]. cbn [firstn] in RZ2.
    enter_with (K _ RZ2 MI MU WMo). st_eq.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation WP2 := [(FB, FB + 24); (SHF, SHF + 44)]%Z.
  Lemma A0_cb_P2 : forall (m : word -> option byte) (h0 h1 h2 : word) (bs : list byte)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m FB [C8 h0; C8 h1; C8 h2] -> rw_cells a0segs m SHF [CB 44 bs] -> mem_inv a0segs m ->
    (forall m' (y12 : word),
       rw_cells a0segs m' FB [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x19f3e); C8 (Z_to_bv 64 0x88a10)] ->
       rw_cells a0segs m' (SHF + 4) (yysh cf8b) -> mem_inv a0segs m' -> munch WP2 m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (ce_sp X) (Z_to_bv 64 P) (Z_to_bv 64 (SHE + -2147450867)) (Z_to_bv 64 (-13)) y12 (Z_to_bv 64 (E + 108))
                             (Z_to_bv 64 (-15)) a5 a6 a7 (il_w (ce_il X)) cSB (Z_to_bv 64 E) s5 (Z_to_bv 64 SHF) (Z_to_bv 64 FB) (Z_to_bv 64 FB) s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x88ba4) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (ce_sp X) (Z_to_bv 64 P) (Z_to_bv 64 FB) a1 a2 a3 a4 a5 a6 a7
                          (il_w (ce_il X)) cSB (Z_to_bv 64 E) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88a84) fc None m (seg_rom a0segs)).
  Proof.
    intros m h0 h1 h2 bs ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 HD RZ MI K.
    cbenv_open XOK. clear CX SEP. acenv_open YOK.
    pose proof YOFF as YO; unfold acenv_offsh, SH_LO, SH_HI in YO; destruct YO as (_ & _ & _ & YOF).
    assert (AFS : (FB + 512 <= SHF \/ SHF + 64 <= FB)%Z) by lia. box_ors.
    pose proof (munch_refl WP2 m) as MU. pose proof (wmono_refl a0segs m) as WM.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep; if_cases Kz; zify_cond_z Kz; [| exfalso; lia].
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    wstep. lit_store. wstep. lit_store. wstep. lit_store. wstep. wstep.
    rewrite (sanchor_addr0 FB SHF AX).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m1 := mm) in * end.
    enter_with (A0_cb_P2sb m1 m1 bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| exact RZ| exact MI| apply munch_refl| apply wmono_refl|].
    intros m2 RZ2 MI2 MU2 WM2. clear RZ MI. transport_after_call a0segs m1 m2 MU2 WM2. clear MU2 WM2.
    enter_with (K _ _ HD RZ2 MI2 MU WM). st_eq.
  Qed.
End A0CBP2.

End ACeilS1.
