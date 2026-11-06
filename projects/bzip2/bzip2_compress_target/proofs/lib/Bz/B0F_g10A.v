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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasT BzLemmasT2 BzWalkArith BzWalkArith2 BzWalkArith3 BzWalkArith4 BzDU9 DecAux12F BzDU5 BzDUM BzDU11 BzDU12F BzDU12S DecAux12S BzDOKS DecTacF3 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV DecTacSB.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSB.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast FLiaA.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= FLiaA.lia_f.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecTac2.
Local Ltac AsanKit.a_norm ::= DecTac2.lit_store_fix.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
Section ACeilS1. Context {ACEIL__ : ACeil}.

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
Lemma rw_cells_cutZ : forall segs m A cs k, rw_cells segs m A cs ->
  rw_cells segs m A (firstn k cs) /\ rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs)))%Z (skipn k cs).
Proof. intros segs m A cs k H. rewrite <- (firstn_skipn k cs) in H at 1. exact (proj1 (DecTac2.rw_cells_app_iff segs m A _ _) H). Qed.
(* [comment removed for export] *)
Ltac split_at_cb8 cs :=
  lazymatch cs with
  | CB 8 ?bs :: ?post => constr:((@nil cell, bs, post))
  | ?c :: ?rest => let r := split_at_cb8 rest in lazymatch r with (?pre, ?bs, ?post) => constr:((c :: pre, bs, post)) end
  end.
Ltac cb8_all H :=
  repeat (lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
            let r := split_at_cb8 cs in
            lazymatch r with (?pre, ?bs, ?post) => apply (CmpHmKit.rw_cells_CB8_C8 segs m A pre bs post) in H; cbn [app] in H end end).

(* [comment removed for export] *)
Definition W10 (A : act14) : list ivl :=
  [(b_s (a_cx A), b_s (a_cx A) + 68)%Z; (b_s (a_cx A) + 64036, b_s (a_cx A) + 64144)%Z;
   (b_strm (a_cx A), b_strm (a_cx A) + 20)%Z; (a_P A, a_P A + 760)%Z; (a_fb A, a_fb A + 56)%Z; (a_shf A, a_shf A + 8)%Z].
(* [comment removed for export] *)
Definition W10p2 (A : act14) : list ivl :=
  [(b_s (a_cx A) + 64036, b_s (a_cx A) + 64144)%Z; (a_P A, a_P A + 760)%Z; (a_fb A, a_fb A + 56)%Z; (a_shf A, a_shf A + 8)%Z].
(* [comment removed for export] *)
Definition g10_lin (A : act14) : Prop :=
  (0 < b_s (a_cx A) /\ b_s (a_cx A) + 64144 <= alloc_ceiling /\ 0 < b_strm (a_cx A) <= alloc_ceiling - 80 /\
   0 < a_fb A <= alloc_ceiling - 64 /\ 2147450880 <= a_shf A <= 17594333495288 /\
   alloc_ceiling <= a_lo A /\ a_lo A + 256 <= a_P A /\ a_usp A < 18446744073709551616 /\ a_P A + 864 <= a_usp A /\ a_usp A <= a_P A + 880)%Z.
(* [comment removed for export] *)
Definition SAVE0_CELLS : list cell :=
  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Section R.
  Variable A : act14.
  Variable Q : machine_state -> Prop.
  Hypothesis GL : g10_lin A.
  Hypothesis ANS : sanchor (b_s (a_cx A)) (a_shs A).
  Hypothesis ANF : sanchor (a_fb A) (a_shf A).
  Hypothesis SEPfs : (a_fb A + 64 <= b_s (a_cx A) \/ b_s (a_cx A) + 64144 <= a_fb A)%Z.
  Hypothesis SEPfsh : (a_fb A + 64 <= a_shf A \/ a_shf A + 8 <= a_fb A)%Z.
  Hypothesis SEPshs : (a_shf A + 8 <= b_s (a_cx A) \/ b_s (a_cx A) + 64144 <= a_shf A)%Z.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation S := (b_s (a_cx A)).
  Notation P := (a_P A).
  (* [comment removed for export] *)

  Lemma B0F_g10_P2 : forall (m : word -> option byte) (h : dsh) (jb jf js jsv : list byte) (fl : Z) (ng : nat) (jg : list byte) (Fr : bvmap 5 word) (fc : bv 32)
      (x1 gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word),
    shzW b0segs (W10 A) m S (S + 64144) ->
    rw_cells b0segs m S (HEAD_CELLS h) -> sh_state h = 10%Z -> length (sh_p1 h) = 3%nat ->
    rw_cells b0segs m (S + 64036) [CB 108 jsv] ->
    rw_cells b0segs m P [CB 760 jb] ->
    rw_cells b0segs m (P + 760) (CB ng jg :: FT_REGS A) -> (P + 760 + Z.of_nat ng + 104 = usp)%Z -> (ng = 0 \/ ng = 16)%nat ->
    rw_cells b0segs m (a_fb A) [CB 56 jf] -> ro_cells b0segs m (a_fb A + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells b0segs m (a_shf A) [CB 8 js] ->
    stk b0segs m (a_lo A) P -> mem_inv b0segs m ->
    (forall (m' : word -> option byte) (w0 w8 w16 w24 w32 w40 w48 w56 w736 w744 y11 y12 y13 y14 y15 y16 : word),
       rw_cells b0segs m' S (HEAD_CELLS h) -> rw_cells b0segs m' (S + 64036) SAVE0_CELLS ->
       B0FL A m' w0 w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (S + 3176))
            (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (a_fb A + 32)) (Z_to_bv 64 (S + 2047)) ->
       B0FH A m' (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (a_shs A))
            (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
            (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (a_fb A)) (Z_to_bv 64 (S + 7820)) (Z_to_bv 64 0)
            (Z_to_bv 64 (a_shs A + 1)) (Z_to_bv 64 0) (Z_to_bv 64 0) w736 w744 (Z_to_bv 64 (a_fb A)) ->
       aframe A m' ->
       stk b0segs m' (a_lo A) P -> mem_inv b0segs m' -> munch (W10 A) m m' -> wmono b0segs m m' -> munch (W10p2 A) m m' ->
       evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (a_sp A) (Z_to_bv 64 P) (Z_to_bv 64 (sh_strm h)) y11 y12 y13 y14 y15 y16 x17
                             x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
                        Fr (Z_to_bv 64 0xa9d1c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q
      (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (a_sp A) (Z_to_bv 64 P) (Z_to_bv 64 (a_fb A)) x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) x27 x28 x29 x30 x31)
          Fr (Z_to_bv 64 0xa9500) fc None m (seg_rom b0segs)).
  Proof.
    intros until x31. intros SHS HD ST10 LP1 SAV FR FRT GEO NG FF FLP FS ST MI K.
    pose proof GL as LIN. unfold g10_lin in LIN. pose proof alloc_ceiling_range as ACR.
    pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0. pose proof (proj1 ANS) as SAL8.
    pose proof (munch_refl (W10 A) m) as MU. pose proof (wmono_refl b0segs m) as WM. unfold W10 in MU, SHS.
    pose proof (munch_refl (W10p2 A) m) as MUL. unfold W10p2 in MUL.
    pose proof (SEPfs : id _) as BXfs. pose proof (SEPfsh : id _) as BXfsh. pose proof (SEPshs : id _) as BXshs.
    apply (rw_cells_split_CB b0segs _ _ [] 760 _ [] (repeat 8%nat 95)) in FR; [| reflexivity]. cbn [mk_CB_cells app repeat] in FR.
    apply (rw_cells_split_CB b0segs _ _ [] 56 _ [] [8; 8; 8; 8; 6; 18]%nat) in FF; [| reflexivity]. cbn [mk_CB_cells app] in FF.
    apply (rw_cells_split_CB b0segs _ _ [] 108 _ [] [4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 8; 8; 8]%nat) in SAV; [| reflexivity]. cbn [mk_CB_cells app] in SAV.
    destruct (rw_cells_CB_C1s b0segs _ _ _ _ FS) as [FSc LS]. clear FS. rename FSc into FS.
    do 8 (destruct js as [|? js]; [discriminate LS| cbn [length] in LS; apply Nat.succ_inj in LS]). destruct js; [clear LS| discriminate LS].
    cbn [map] in FS.
    rewrite ST10 in HD.
    (* [comment removed for export] *)
    brun; if_cases Kz; zify_cond_z Kz; [| exfalso; lia].
    (* [comment removed for export] *)
    brun. rewrite (sanchor_addr0 (a_fb A) (a_shf A) ANF).
    (* [comment removed for export] *)
    brun_to 0xa9ce8%Z.
    lazymatch goal with MIc : mem_inv b0segs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let obs := eval vm_compute in (image_bytes b0segs 138932 4) in
      lazymatch obs with Some ?bs =>
        assert (ROjt : ro_cells b0segs mm 138932 [CB 4 bs])
          by (apply (ro_cells_image b0segs mm 138932 bs MIc); [vm_compute; reflexivity | lia | cbn; lia]) end end.
    bstep. clear ROjt.
    (* [comment removed for export] *)
    brun_to 0xa9d1c%Z.
    (* [comment removed for export] *)
    cb8_all FR.
    repeat match type of FR with context [((S + ?o) / 8 + 2147450880)%Z] =>
      is_Zlit o; let q := eval vm_compute in (o / 8)%Z in rewrite (sanchor_addr_lit S (a_shs A) o q ANS eq_refl) in FR end.
    rewrite ?(sanchor_addr0 S (a_shs A) ANS) in FR.
    destruct (rw_cells_cutZ b0segs _ _ _ 16%nat FR) as [FRL R1]. cbn [firstn skipn cells_size csize Nat.add] in FRL, R1. change (Z.of_nat 128) with 128%Z in R1.
    destruct (rw_cells_cutZ b0segs _ _ _ 27%nat R1) as [FRM FRH]. cbn [firstn skipn cells_size csize Nat.add] in FRM, FRH. change (Z.of_nat 216) with 216%Z in FRH.
    replace (P + 128 + 216)%Z with (P + 344)%Z in FRH by lia.
    clear FR R1. rewrite <- ST10 in HD.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (AF : aframe A mm) end.
    { unfold aframe, FM_CELLS. exists (Z_to_bv 64 0). do 6 eexists. split; [exact GEO|]. split; [exact NG|]. split; [exact FLP|]. split; [exact FRM|]. split; [exact FRT|]. split; [exact FF| exact FS]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (MUf : munch (W10 A) m mm) by (unfold W10; exact MU) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (MULf : munch (W10p2 A) m mm) by (unfold W10p2; exact MUL) end.
    eapply evt_eq; [ | eapply (K _) ]; [ st_eq | exact HD | unfold SAVE0_CELLS; exact SAV | exact FRL | exact FRH | exact AF | exact ST | assumption | exact MUf | exact WM | exact MULf ].
  Qed.
End R.
End ACeilS1.
