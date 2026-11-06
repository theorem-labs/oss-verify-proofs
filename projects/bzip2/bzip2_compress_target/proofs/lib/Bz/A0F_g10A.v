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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasT BzLemmasT2 BzWalkArith BzWalkArith2 BzWalkArith3 BzWalkArith4 BzDU9 DecAux12F BzDU5 BzDUM BzDU11 BzDU12F BzDU12S DecAux12S BzDOKS DecTacF3 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet A0F_decRet3 DecTacSA A0F_decCutsA.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsA.
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
   (b_strm (a_cx A), b_strm (a_cx A) + 20)%Z; (a_P A, a_P A + 728)%Z; (a_fb A, a_fb A + 56)%Z; (a_shf A, a_shf A + 8)%Z].
(* [comment removed for export] *)
Definition W10p2 (A : act14) : list ivl := [(a_P A, a_P A + 728)%Z; (a_fb A, a_fb A + 56)%Z; (a_shf A, a_shf A + 8)%Z].
Definition W10p3 (A : act14) : list ivl := [(a_P A, a_P A + 728)%Z].
(* [comment removed for export] *)
Definition g10_lin (A : act14) : Prop :=
  (0 < b_s (a_cx A) /\ b_s (a_cx A) + 64144 <= alloc_ceiling /\ 0 < b_strm (a_cx A) <= alloc_ceiling - 80 /\
   0 < a_fb A <= alloc_ceiling - 64 /\ 2147450880 <= a_shf A <= 17594333495288 /\
   alloc_ceiling <= a_lo A /\ a_lo A + 256 <= a_P A /\ a_usp A < 18446744073709551616 /\ a_P A + 832 <= a_usp A /\ a_usp A <= a_P A + 848)%Z.
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

  Lemma A0F_g10_P2 : forall (m : word -> option byte) (h : dsh) (jb jf js : list byte) (Fr : bvmap 5 word) (fc : bv 32)
      (x1 gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    shzW a0segs (W10 A) m S (S + 64144) ->
    rw_cells a0segs m S (HEAD_CELLS h) -> sh_state h = 10%Z -> length (sh_p1 h) = 3%nat ->
    rw_cells a0segs m P [CB 728 jb] -> rw_cells a0segs m (a_fb A) [CB 56 jf] -> rw_cells a0segs m (a_shf A) [CB 8 js] ->
    stk a0segs m (a_lo A) P -> mem_inv a0segs m ->
    (forall (m' : word -> option byte) (jf2 : list byte) (y13 y14 y15 y16 : word)
            (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368 v376 v384 v392 v400 v408 v416 v424 v432 v440 v448 v456 v464 v472 w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w648 w656 w664 w680 w696 w704 w712 : word),
       rw_cells a0segs m' S (HEAD_CELLS h) ->
       rw_cells a0segs m' P [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 (Z_to_bv 64 (S + 8)); C8 w80; C8 w88] ->
       rw_cells a0segs m' (P + 96) [C8 v96; C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176; C8 v184; C8 v192; C8 v200; C8 v208; C8 v216; C8 v224; C8 v232; C8 v240; C8 v248; C8 v256; C8 v264; C8 v272; C8 v280; C8 v288; C8 v296; C8 v304; C8 v312; C8 v320; C8 v328; C8 v336; C8 v344; C8 v352; C8 v360; C8 v368; C8 v376; C8 v384; C8 v392; C8 v400; C8 v408; C8 v416; C8 v424; C8 v432; C8 v440; C8 v448; C8 v456; C8 v464; C8 v472; C8 (Z_to_bv 64 (a_fb A)); C8 (Z_to_bv 64 (a_shf A))] ->
       rw_cells a0segs m' (P + 496) [C8 w496; C8 w504; C8 w512; C8 w520; C8 w528; C8 w536; C8 w544; C8 w552; C8 (Z_to_bv 64 (a_shs A)); C8 w568; C8 w576; C8 w584; C8 w592; C8 w600; C8 w608; C8 w616; C8 w624; C8 w632; C8 w640; C8 w648; C8 w656; C8 w664; C8 (Z_to_bv 64 (a_fb A)); C8 w680; C8 (Z_to_bv 64 (a_shs A + 1)); C8 w696; C8 w704; C8 w712; C8 (Z_to_bv 64 (a_fb A))] ->
       rw_cells a0segs m' (a_fb A) [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 132751); C8 (Z_to_bv 64 648040); CB 32 jf2] -> rw_cells a0segs m' (a_shf A) [C1 df1b; C1 df1b; C1 df1b; C1 df1b; C1 df8b; C1 df3b; C1 df3b; C1 df3b] ->
       stk a0segs m' (a_lo A) P -> mem_inv a0segs m' -> munch (W10 A) m m' -> wmono a0segs m m' -> munch (W10p2 A) m m' ->
       evt a0segs Q (MS (mkR (Z_to_bv 64 0x9e4d8) (Z_to_bv 64 P) gp tp x5 x6 x7 (a_sp A) (Z_to_bv 64 P) (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 0) (Z_to_bv 64 108) y13 y14 y15 y16 x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 10) (Z_to_bv 64 (sh_strm h)) x24 x25 x26 (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31) Fr (Z_to_bv 64 0x52ea0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q
      (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (a_sp A) (Z_to_bv 64 P) (Z_to_bv 64 (a_fb A)) x11 x12 x13 x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Fr (Z_to_bv 64 0x9e3d8) fc None m (seg_rom a0segs)).
  Proof.
    intros until x31. intros SHS HD ST10 LP1 FR FF FS ST MI K.
    pose proof GL as LIN. unfold g10_lin in LIN. pose proof alloc_ceiling_range as ACR.
    pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    pose proof (munch_refl (W10 A) m) as MU. pose proof (wmono_refl a0segs m) as WM. unfold W10 in MU, SHS.
    pose proof (munch_refl (W10p2 A) m) as MUL. unfold W10p2 in MUL.
    pose proof (SEPfs : id _) as BXfs. pose proof (SEPfsh : id _) as BXfsh. pose proof (SEPshs : id _) as BXshs.
    apply (rw_cells_split_CB a0segs _ _ [] 728 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    apply (rw_cells_split_CB a0segs _ _ [] 56 _ [] [8; 8; 8; 32]%nat) in FF; [| reflexivity]. cbn [mk_CB_cells app] in FF.
    destruct (rw_cells_CB_C1s a0segs _ _ _ _ FS) as [FSc LS]. clear FS. rename FSc into FS.
    do 8 (destruct js as [|? js]; [discriminate LS| cbn [length] in LS; apply Nat.succ_inj in LS]). destruct js; [clear LS| discriminate LS].
    cbn [map] in FS.
    rewrite ST10 in HD.
    arun; if_cases Kz; zify_cond_z Kz; [| exfalso; lia].
    arun. rewrite (sanchor_addr0 (a_fb A) (a_shf A) ANF).
    arun_to 0x52ea0%Z.
    (* [comment removed for export] *)
    cb8_all FR.
    repeat match type of FR with context [((S + ?o) / 8 + 2147450880)%Z] =>
      is_Zlit o; let q := eval vm_compute in (o / 8)%Z in rewrite (sanchor_addr_lit S (a_shs A) o q ANS eq_refl) in FR end.
    rewrite ?(sanchor_addr0 S (a_shs A) ANS) in FR.
    destruct (rw_cells_cutZ a0segs _ _ _ 12%nat FR) as [FRL R1]. cbn [firstn skipn cells_size csize Nat.add] in FRL, R1. change (Z.of_nat 96) with 96%Z in R1.
    destruct (rw_cells_cutZ a0segs _ _ _ 50%nat R1) as [FRM FRH]. cbn [firstn skipn cells_size csize Nat.add] in FRM, FRH. change (Z.of_nat 400) with 400%Z in FRH.
    replace (P + 96 + 400)%Z with (P + 496)%Z in FRH by lia.
    clear FR R1. rewrite <- ST10 in HD.
    assert (MUf : munch (W10 A) m m1) by (unfold W10; exact MU).
    assert (MULf : munch (W10p2 A) m m1) by (unfold W10p2; exact MUL).
    eapply evt_eq; [ | eapply (K m1) ]; [ st_eq | exact HD | exact FRL | exact FRM | exact FRH | exact FF | exact FS | exact ST | assumption | exact MUf | exact WM | exact MULf ].
  Qed.

  Lemma A0F_g10_P3 : forall (m : word -> option byte) (h : dsh) (jf2 : list byte) (fl : Z) (ng : nat) (jg : list byte) (Fr : bvmap 5 word) (fc : bv 32)
      (w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368 v376 v384 v392 v400 v408 v416 v424 v432 v440 v448 v456 v464 v472 w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w648 w656 w664 w680 w696 w704 w712 : word)
      (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x24 x25 x26 x28 x29 x30 x31 : word),
    shzW a0segs (W10 A) m S (S + 64144) ->
    rw_cells a0segs m S (HEAD_CELLS h) -> sh_state h = 10%Z -> length (sh_p1 h) = 3%nat ->
    rw_cells a0segs m (S + 64036) SAVE0_CELLS ->
    rw_cells a0segs m P [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 (Z_to_bv 64 (S + 8)); C8 w80; C8 w88] ->
    rw_cells a0segs m (P + 96) [C8 v96; C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176; C8 v184; C8 v192; C8 v200; C8 v208; C8 v216; C8 v224; C8 v232; C8 v240; C8 v248; C8 v256; C8 v264; C8 v272; C8 v280; C8 v288; C8 v296; C8 v304; C8 v312; C8 v320; C8 v328; C8 v336; C8 v344; C8 v352; C8 v360; C8 v368; C8 v376; C8 v384; C8 v392; C8 v400; C8 v408; C8 v416; C8 v424; C8 v432; C8 v440; C8 v448; C8 v456; C8 v464; C8 v472; C8 (Z_to_bv 64 (a_fb A)); C8 (Z_to_bv 64 (a_shf A))] ->
    rw_cells a0segs m (P + 496) [C8 w496; C8 w504; C8 w512; C8 w520; C8 w528; C8 w536; C8 w544; C8 w552; C8 (Z_to_bv 64 (a_shs A)); C8 w568; C8 w576; C8 w584; C8 w592; C8 w600; C8 w608; C8 w616; C8 w624; C8 w632; C8 w640; C8 w648; C8 w656; C8 w664; C8 (Z_to_bv 64 (a_fb A)); C8 w680; C8 (Z_to_bv 64 (a_shs A + 1)); C8 w696; C8 w704; C8 w712; C8 (Z_to_bv 64 (a_fb A))] ->
    rw_cells a0segs m (P + 728) (CB ng jg :: FT_REGS A) -> (P + 728 + Z.of_nat ng + 104 = usp)%Z -> (ng = 0 \/ ng = 16)%nat ->
    rw_cells a0segs m (a_fb A) [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 132751); C8 (Z_to_bv 64 648040); CB 32 jf2] -> ro_cells a0segs m (a_fb A + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells a0segs m (a_shf A) [C1 df1b; C1 df1b; C1 df1b; C1 df1b; C1 df8b; C1 df3b; C1 df3b; C1 df3b] ->
    stk a0segs m (a_lo A) P -> mem_inv a0segs m ->
    (forall (m' : word -> option byte) (w0 w8 w16 w704 w712 y10 y11 y12 y13 y14 y22 : word),
       rw_cells a0segs m' S (HEAD_CELLS h) -> rw_cells a0segs m' (S + 64036) SAVE0_CELLS ->
       rw_cells a0segs m' P [C8 w0; C8 w8; C8 w16; C8 ((Z_to_bv 64 (a_fb A + 32))); C8 ((Z_to_bv 64 (S + 7884))); C8 ((Z_to_bv 64 (S + 2124))); C8 ((Z_to_bv 64 (S + 3192))); C8 ((Z_to_bv 64 (S + 3152))); C8 ((Z_to_bv 64 (S + 2047))); C8 ((Z_to_bv 64 (S + 8))); C8 ((Z_to_bv 64 (S + 3176))); C8 ((Z_to_bv 64 (S + 7820)))] ->
       rw_cells a0segs m' (P + 496) [C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 (a_shs A))); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 (a_fb A))); C8 ((Z_to_bv 64 0)); C8 ((Z_to_bv 64 (a_shs A + 1))); C8 ((Z_to_bv 64 0)); C8 w704; C8 w712; C8 ((Z_to_bv 64 (a_fb A)))] ->
       aframe A m' ->
       stk a0segs m' (a_lo A) P -> mem_inv a0segs m' -> munch (W10 A) m m' -> wmono a0segs m m' -> munch (W10p3 A) m m' ->
       evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (a_sp A) (Z_to_bv 64 P) y10 y11 y12 y13 y14 x15 x16 x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) y22 (Z_to_bv 64 (sh_strm h)) x24 x25 x26 (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
                        Fr (Z_to_bv 64 0x9e908) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q
      (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (a_sp A) (Z_to_bv 64 P) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 10) (Z_to_bv 64 (sh_strm h)) x24 x25 x26 (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          Fr (Z_to_bv 64 0x9e4d8) fc None m (seg_rom a0segs)).
  Proof.
    intros until x31. intros SHS HD ST10 LP1 SAV FRL FRM FRH FRT GEO NG FF FLP FS ST MI K.
    unfold SAVE0_CELLS in SAV.
    pose proof GL as LIN. unfold g10_lin in LIN. pose proof alloc_ceiling_range as ACR.
    pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    pose proof (munch_refl (W10 A) m) as MU. pose proof (wmono_refl a0segs m) as WM. unfold W10 in MU, SHS.
    pose proof (munch_refl (W10p3 A) m) as MUL. unfold W10p3 in MUL.
    pose proof (SEPfs : id _) as BXfs. pose proof (SEPfsh : id _) as BXfsh. pose proof (SEPshs : id _) as BXshs.
    apply (rw_cells_split_CB a0segs _ _ [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 132751); C8 (Z_to_bv 64 648040)] 32 _ [] [8; 6; 18]%nat) in FF; [| reflexivity]. cbn [mk_CB_cells app] in FF.
    rewrite ST10 in HD.
    arun_to 0x9e8d4%Z.
    lazymatch goal with MIc : mem_inv a0segs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let obs := eval vm_compute in (image_bytes a0segs 139236 4) in
      lazymatch obs with Some ?bs =>
        assert (ROjt : ro_cells a0segs mm 139236 [CB 4 bs])
          by (apply (ro_cells_image a0segs mm 139236 bs MIc); [vm_compute; reflexivity | lia | cbn; lia]) end end.
    astep. clear ROjt.
    arun_to 0x9e908%Z.
    (* [comment removed for export] *)
    repeat match type of FRM with context [((S + ?o) / 8 + 2147450880)%Z] =>
      is_Zlit o; let q := eval vm_compute in (o / 8)%Z in rewrite (sanchor_addr_lit S (a_shs A) o q ANS eq_refl) in FRM end.
    rewrite <- ST10 in HD.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (AF : aframe A mm) end.
    { unfold aframe, FM_CELLS. exists (Z_to_bv 64 0). do 6 eexists. split; [exact GEO|]. split; [exact NG|]. split; [exact FLP|]. split; [exact FRM|]. split; [exact FRT|]. split; [exact FF| exact FS]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (MUf : munch (W10 A) m mm) by (unfold W10; exact MU) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (MULf : munch (W10p3 A) m mm) by (unfold W10p3; exact MUL) end.
    eapply evt_eq; [ | eapply (K _) ]; [ st_eq | exact HD | unfold SAVE0_CELLS; exact SAV | exact FRL | exact FRH | exact AF | exact ST | assumption | exact MUf | exact WM | exact MULf ].
  Qed.
End R.
End ACeilS1.
