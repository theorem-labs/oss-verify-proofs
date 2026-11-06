(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module BoAllocM2s.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Section AMS.
  Variable segs : list Segment.
  Variable t : am_tab.
  Hypothesis TOK : am_tab_ok segs t.
  #[local] Abbreviation rb := (am_rb t).
  #[local] Abbreviation INST := (am_inst t).

  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp stk : word) (n : Z).
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 n.
  Hypothesis H11 : getr regs 11 = stk.
  Hypothesis Hs : (64513 <= n <= 2 ^ 34)%Z.
  (* [comment removed for export] *)
  Variable MAG : word.
  Hypothesis Rinited : rdn segs mem (Z_to_bv 64 (am_g_inited t)) 1 = Some [Z_to_bv 8 1].
  Hypothesis Rrss : rdn segs mem (Z_to_bv 64 (am_g_rss t)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rmag : rdn segs mem (Z_to_bv 64 (am_g_magic t)) 8 = Some (LE8 MAGICw).
  Hypothesis Rtbl2 : rdn segs mem (at_ (am_tbl2 t) 4) 1 = Some [Z_to_bv 8 3].     (* [comment removed for export] *)
  Hypothesis Rt16 : rdn segs mem (at_ (am_tbl t) 8) 1 = Some [Z_to_bv 8 4].
  Hypothesis Rt2048 : rdn segs mem (at_ (am_tbl t) 49) 1 = Some [Z_to_bv 8 11].
  Hypothesis Rminrz : rdn segs mem (at_ INST 3624) 2 = Some (LE2 16).
  Hypothesis Rmaxrz : rdn segs mem (at_ INST 3626) 2 = Some (LE2 2048).
  Hypothesis Rmaxsz : rdn segs mem (at_ INST 3616) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 40))).
  Hypothesis Hstk : store_ok segs mem (at_ sp (-160)) 160 = true.
  (* [comment removed for export] *)
  Hypothesis G0 : (0 <= am_g_inited t < 2 ^ 32)%Z /\ (0 <= am_g_rss t < 2 ^ 32)%Z /\ (0 <= am_g_magic t /\ am_g_magic t + 8 <= 2 ^ 32)%Z
            /\ (U (am_tbl2 t) + 64 <= 2 ^ 32)%Z /\ (U (am_tbl t) + 64 <= 2 ^ 32)%Z /\ (U INST + 4096 <= 2 ^ 32)%Z /\ (U stk <> 0)%Z.
  Hypothesis G1 : (2 ^ 32 + 160 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.

  #[local] Abbreviation CLX := (fun r => In r am_clobx).

  #[local] Abbreviation am_m1 := (BoAllocM2.am_m1 t regs mem ra sp).
  #[local] Abbreviation am_m2 := (BoAllocM2.am_m2 t regs mem ra sp).
  #[local] Abbreviation am_m3 := (BoAllocM2.am_m3 t regs mem ra sp).
  #[local] Hint Unfold BoAllocM2.am_m1 BoAllocM2.am_m2 BoAllocM2.am_m3 : asfr.
  Let RETa := BoAllocM2.RETa segs t TOK.
  Let am_m1_outside := BoAllocM2.am_m1_outside t regs mem ra sp G1.
  Let am_m2_outside := BoAllocM2.am_m2_outside t regs mem ra sp G1.
  Let am_m3_outside := BoAllocM2.am_m3_outside t regs mem ra sp G1.
  Let I67568 := BoAllocM2.I67568 segs t TOK.
  Let I675d0 := BoAllocM2.I675d0 segs t TOK.
  Let I675d4 := BoAllocM2.I675d4 segs t TOK.
  Let I675e0 := BoAllocM2.I675e0 segs t TOK.
  Let I675e4 := BoAllocM2.I675e4 segs t TOK.
  Let I675f0 := BoAllocM2.I675f0 segs t TOK.
  Let I675f4 := BoAllocM2.I675f4 segs t TOK.
  Let I675f8 := BoAllocM2.I675f8 segs t TOK.
  Let I67604 := BoAllocM2.I67604 segs t TOK.
  Let I67608 := BoAllocM2.I67608 segs t TOK.
  Let I6760c := BoAllocM2.I6760c segs t TOK.
  Let I67618 := BoAllocM2.I67618 segs t TOK.
  Let I6761c := BoAllocM2.I6761c segs t TOK.
  Let I67620 := BoAllocM2.I67620 segs t TOK.
  Let I6762c := BoAllocM2.I6762c segs t TOK.
  Let I67630 := BoAllocM2.I67630 segs t TOK.
  Let I67634 := BoAllocM2.I67634 segs t TOK.
  Let I67638 := BoAllocM2.I67638 segs t TOK.
  Let I67668 := BoAllocM2.I67668 segs t TOK.
  Let I67684 := BoAllocM2.I67684 segs t TOK.
  Let I67688 := BoAllocM2.I67688 segs t TOK.
  Let I6768c := BoAllocM2.I6768c segs t TOK.
  Let I67690 := BoAllocM2.I67690 segs t TOK.
  Let I67694 := BoAllocM2.I67694 segs t TOK.
  Let I67698 := BoAllocM2.I67698 segs t TOK.
  Let I6769c := BoAllocM2.I6769c segs t TOK.
  Let I676a0 := BoAllocM2.I676a0 segs t TOK.
  Let I676a4 := BoAllocM2.I676a4 segs t TOK.
  Let I676a8 := BoAllocM2.I676a8 segs t TOK.
  Let I676ac := BoAllocM2.I676ac segs t TOK.
  Let I676b0 := BoAllocM2.I676b0 segs t TOK.
  Let I676b4 := BoAllocM2.I676b4 segs t TOK.
  Let I676b8 := BoAllocM2.I676b8 segs t TOK.
  Let I676bc := BoAllocM2.I676bc segs t TOK.
  Let I676c0 := BoAllocM2.I676c0 segs t TOK.
  Let I676c4 := BoAllocM2.I676c4 segs t TOK.
  Let I676c8 := BoAllocM2.I676c8 segs t TOK.
  Let I676cc := BoAllocM2.I676cc segs t TOK.
  Let I676d0 := BoAllocM2.I676d0 segs t TOK.
  Let I676d4 := BoAllocM2.I676d4 segs t TOK.
  Let I676d8 := BoAllocM2.I676d8 segs t TOK.
  Let I67714 := BoAllocM2.I67714 segs t TOK.
  Let I67718 := BoAllocM2.I67718 segs t TOK.
  Let I6771c := BoAllocM2.I6771c segs t TOK.
  Let I67720 := BoAllocM2.I67720 segs t TOK.
  Let I67724 := BoAllocM2.I67724 segs t TOK.
  Let I67728 := BoAllocM2.I67728 segs t TOK.

  Let I676dc := BoAllocM2.I676dc segs t TOK.
  Let I676e0 := BoAllocM2.I676e0 segs t TOK.
  Let I676e4 := BoAllocM2.I676e4 segs t TOK.
  Let I676e8 := BoAllocM2.I676e8 segs t TOK.
  Let I676ec := BoAllocM2.I676ec segs t TOK.
  Let I676f0 := BoAllocM2.I676f0 segs t TOK.

  Lemma rz2048 : rz n = 2048%Z.
  Proof using Hs. apply AsArith3.rz_big. lia. Qed.

  (* [comment removed for export] *)
  Lemma amA2s : forall (M : word -> option byte) r0,
    getr r0 10 = Z_to_bv 64 49 -> getr r0 21 = Z_to_bv 64 n -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4c62c) M rom) (mkst r (at_ rb 0x4c700) M rom)
      /\ getr r 19 = Z_to_bv 64 7
      /\ (forall i : reg, In i [2; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using I67638 I67634 I67630 I6762c I67620 I6761c I67618 I6760c I67608 I67604 I675f8 I675f4 I675f0 I675e4 I675e0 I675d4 I675d0 I67568 Hs TOK.
    intros M r0 R10 R21 AG0.
    wd_eexists. split.
    { ab_tk I67568 D_4c62c ltac:(condz). an I675d0 D_4c694. ab_tk I675d4 D_4c698 ltac:(condz).
      an I675e0 D_4c6a4. ab_tk I675e4 D_4c6a8 ltac:(condz).
      an I675f0 D_4c6b4. an I675f4 D_4c6b8. ab_tk I675f8 D_4c6bc ltac:(condz).
      an I67604 D_4c6c8. an I67608 D_4c6cc. ab_tk I6760c D_4c6d0 ltac:(condz).
      an I67618 D_4c6dc. an I6761c D_4c6e0. ab_tk I67620 D_4c6e4 ltac:(condz).
      an I6762c D_4c6f0. an I67630 D_4c6f4. an I67634 D_4c6f8. rewrite v_sltu_lit by lia. replace (n <? 64513)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      an I67638 D_4c6fc. wd_refl. }
    post; first [ (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
                | intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi
                | idtac ].
  Qed.

  (* [comment removed for export] *)
  Lemma amA3cs : forall (M : word -> option byte) r0,
    getr r0 10 = Z_to_bv 64 7 -> getr r0 9 = Z_to_bv 64 0 -> getr r0 19 = Z_to_bv 64 7 -> getr r0 21 = Z_to_bv 64 n -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4c72c) M rom) (mkst r (at_ rb 0x4c748) M rom)
      /\ getr r 19 = Z_to_bv 64 7 /\ getr r 10 = Z_to_bv 64 n
      /\ (forall i : reg, In i [2; 8; 18; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using I67728 I67724 I67720 I6771c I67718 I67714 I67668 Hs TOK.
    intros M r0 R10 R9 R19 R21 AG0.
    wd_eexists. split.
    { ab_tk I67668 D_4c72c ltac:(condz).                 (* [comment removed for export] *)
      ab_ft I67714 D_4c7d8 ltac:(condz).                 (* [comment removed for export] *)
      an I67718 D_4c7dc.                                  (* [comment removed for export] *)
      an I6771c D_4c7e0.                                  (* [comment removed for export] *)
      an I67720 D_4c7e4.                                  (* [comment removed for export] *)
      ab_ft I67724 D_4c7e8 ltac:(condz).                 (* [comment removed for export] *)
      an I67728 D_4c7ec.                                  (* [comment removed for export] *)
      wd_refl. }
    post.
    all: lazymatch goal with
         | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
         | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
         | |- _ => idtac
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma amA4s : forall r0,
    getr r0 19 = Z_to_bv 64 7 -> getr r0 21 = Z_to_bv 64 n -> getr r0 10 = Z_to_bv 64 n -> getr r0 8 = Z_to_bv 64 8 -> getr r0 18 = Z_to_bv 64 8 ->
    getr r0 20 = Z_to_bv 64 65536 -> getr r0 26 = at_ INST 2047 -> getr r0 2 = at_ sp (-144) -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4c748) am_m3 rom) (mkst r (at_ rb 0x4c814) am_m3 rom)
      /\ getr r 8 = Z_to_bv 64 0 /\ getr r 9 = Z_to_bv 64 n /\ getr r 19 = Z_to_bv 64 (sec_needed n) /\ getr r 20 = Z_to_bv 64 2048
      /\ getr r 24 = Z_to_bv 64 18446744073709551608
      /\ (forall i : reg, In i [2; 18; 21; 22; 23; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using I676f0 I676ec I676e8 I676e4 I676e0 I676dc I676d8 I676d4 I676d0 I676cc I676c8 I676c4 I676c0 I676bc I676b8 I676b4 I676b0 I676ac I676a8 I676a4 I676a0 I6769c I67698 I67694 I67690 I6768c I67688 I67684 G1 G0 Rmaxsz Hs stk TOK.
    intros r0 R19 R21 R10 R8 R18 R20 R26 R2 AG0. destruct G0 as (Ga & Gb & Gc & Gd & Ge & Gf & Gg). destruct G1 as [G1a G1b].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range INST) as HI.
    pose proof rz2048 as Hrz.
    assert (Hrd : (rounded n = RoundUp (Z.max n 8) 8)%Z) by reflexivity.
    rewrite Z.max_l in Hrd by lia.
    assert (Hrd2 : (n <= rounded n <= n + 7 /\ rounded n mod 8 = 0)%Z).
    { rewrite Hrd. (lazymatch goal with |- ?G => let G' := eval unfold RoundUp in G in change_no_check G' end). pose proof (Z.div_mod (n + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 8 - 1) 8 ltac:(lia)).
      split; [lia|]. apply Z_mod_mult. }
    assert (Hnd : (needed n = rounded n + 2048)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold needed in G in change_no_check G' end); rewrite Hrz; reflexivity).
    assert (Hsn : (sec_needed n = rounded n + 4096)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sec_needed in G in change_no_check G' end); rewrite Hrz; lia).
    wd_eexists. split.
    { av I67684 D_4c748 (Z_to_bv 64 (n + 8)) ltac:(valz).   (* [comment removed for export] *)
      an I67688 D_4c74c.                                      (* [comment removed for export] *)
      an I6768c D_4c750.                                      (* [comment removed for export] *)
      av I67690 D_4c754 (Z_to_bv 64 (n + 7)) ltac:(valz).    (* [comment removed for export] *)
      an I67694 D_4c758.                                      (* [comment removed for export] *)
      an I67698 D_4c75c.                                      (* [comment removed for export] *)
      match goal with |- context [v_and ?x ?y] => replace (v_and x y) with (Z_to_bv 64 (rounded n)) by ((lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; rewrite Hrd; symmetry; apply rounded_val; lia) end.
      an I6769c D_4c760.                                      (* [comment removed for export] *)
      av I676a0 D_4c764 (Z_to_bv 64 (rounded n)) ltac:(valz).   (* [comment removed for export] *)
      av I676a4 D_4c768 (Z_to_bv 64 0) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); change (bv_wrap 64 7) with 7%Z; unorm; rewrite land_7 by lia; replace (rounded n mod 8)%Z with 0%Z by lia; reflexivity).   (* [comment removed for export] *)
      ab_ft I676a8 D_4c76c ltac:(condz).                    (* [comment removed for export] *)
      an I676ac D_4c770.                                      (* [comment removed for export] *)
      av I676b0 D_4c774 (Z_to_bv 64 0) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sltiu in G in change_no_check G' end); unorm; change (bv_wrap 64 1) with 1%Z; replace (n <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).   (* [comment removed for export] *)
      an I676b4 D_4c778.                                      (* [comment removed for export] *)
      an I676b8 D_4c77c.                                      (* [comment removed for export] *)   (* [comment removed for export] *)
      an I676bc D_4c780.                                      (* [comment removed for export] *)
      av I676c0 D_4c784 (Z_to_bv 64 n) ltac:(valz).           (* [comment removed for export] *)
      an I676c4 D_4c788.                                      (* [comment removed for export] *)
      av I676c8 D_4c78c (Z_to_bv 64 (needed n)) ltac:(rewrite Hnd; valz).   (* [comment removed for export] *)
      an I676cc D_4c790. rewrite (v_sltu_lit (needed n) 65537) by lia. replace (needed n <? 65537)%Z with false by (symmetry; apply Z.ltb_ge; lia).   (* [comment removed for export] *)
      an I676d0 D_4c794.                                      (* [comment removed for export] *)
      an I676d4 D_4c798.                                      (* [comment removed for export] *)
      an I676d8 D_4c79c.                                      (* [comment removed for export] *)
      an I676dc D_4c7a0.                                      (* [comment removed for export] *)
      av I676e0 D_4c7a4 (Z_to_bv 64 (sec_needed n)) ltac:(rewrite Hsn, Hnd; valz).   (* [comment removed for export] *)
      ab_ft I676e4 D_4c7a8 ltac:(condz).                    (* [comment removed for export] *)
      ab_ft I676e8 D_4c7ac ltac:(condz).                    (* [comment removed for export] *)
      cld8 I676ec D_4c7b0 (Z_to_bv 64 (2 ^ 40)) Rmaxsz.      (* [comment removed for export] *)
      ab_tk I676f0 D_4c7b4 ltac:(condz).                    (* [comment removed for export] *)
      wd_refl. }
    post.
    all: lazymatch goal with
         | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
         | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
         | |- _ => idtac
         end.
  Qed.



  Let amA1a := BoAllocM2.amA1a segs t TOK regs mem rom ra sp stk n H1 H2 H10 H11 Hstk G0 G1.
  Let amA1b := BoAllocM2.amA1b segs t TOK regs rom.
  Let amA1c := BoAllocM2.amA1c segs t TOK regs mem rom ra sp stk Rmag Rtbl2 Hstk G0 G1.
  Let amA3a := BoAllocM2.amA3a segs t TOK regs mem rom ra sp stk Rminrz G0 G1.
  Let amA3b := BoAllocM2.amA3b segs t TOK regs mem rom ra sp stk Rmaxrz G0 G1.

  (* [comment removed for export] *)
  Theorem amA_run_s :
    exists r,
      msteps segs (mkst regs (at_ rb 0x4c538) mem rom) (mkst r (at_ rb 0x4c814) am_m3 rom)
      /\ getr r 2 = at_ sp (-144) /\ getr r 8 = Z_to_bv 64 0 /\ getr r 9 = Z_to_bv 64 n /\ getr r 18 = Z_to_bv 64 8
      /\ getr r 19 = Z_to_bv 64 (sec_needed n) /\ getr r 20 = Z_to_bv 64 2048 /\ getr r 21 = Z_to_bv 64 n /\ getr r 22 = INST
      /\ getr r 23 = stk /\ getr r 24 = Z_to_bv 64 18446744073709551608 /\ getr r 25 = Z_to_bv 64 7 /\ getr r 26 = at_ INST 2047
      /\ getr r 27 = Z_to_bv 64 1
      /\ regs_agree CLX regs r.
  Proof using amA3b amA3a amA1c amA1b amA1a I676f0 I676ec I676e8 I676e4 I676e0 I676dc I67728 I67724 I67720 I6771c I67718 I67714 I676d8 I676d4 I676d0 I676cc I676c8 I676c4 I676c0 I676bc I676b8 I676b4 I676b0 I676ac I676a8 I676a4 I676a0 I6769c I67698 I67694 I67690 I6768c I67688 I67684 I67668 I67638 I67634 I67630 I6762c I67620 I6761c I67618 I6760c I67608 I67604 I675f8 I675f4 I675f0 I675e4 I675e0 I675d4 I675d0 I67568 am_m2_outside am_m1_outside RETa G1 G0 Hstk Rmaxsz Rmaxrz Rminrz Rt2048 Rt16 Rtbl2 Rmag Rrss Rinited Hs H11 H10 H2 H1 TOK.
    pose proof G0 as (Ga & Gb & Gc & Gd & Ge & Gf & Gg). pose proof G1 as [G1a G1b].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range INST) as HI. pose proof (u64_range (am_tbl t)) as HT.
    pose proof TOK as TOK'. destruct TOK' as [_ _ _ _ _ AIN AINB RSS RSSB RZL RZM RZT RB].
    Ltac via AG r H := let T := fresh in pose proof (AG r ltac:(notin_list)) as T; rewrite H in T; exact T.
    Ltac viaK K AG r H := rewrite (K r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); via AG r H.
    (* [comment removed for export] *)
    destruct amA1a as (r1 & RUN1 & A1 & A2 & A9 & A27 & A23 & A18 & A21 & A22 & AG1).
    (* [comment removed for export] *)
    destruct (ain_run segs rb (am_g_inited t) AIN AINB am_m1 rom r1 (at_ rb 0x4c5e8)) as (r2 & RUN2 & B10 & AG2).
    { rewrite <- Rinited. apply rdn_ext; [wd_ulia_c | intros x Hx; apply am_m1_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    { apply RETa; [reflexivity | lia]. }
    { exact A1. }
    (* [comment removed for export] *)
    destruct (amA1b am_m1 r2 B10 ltac:(eapply regs_agree_trans; [exact AG1 | regs_agree_weaken AG2])) as (r3 & RUN3 & C1 & CK & AG3).
    (* [comment removed for export] *)
    destruct (rss_run segs rb (am_g_rss t) RSS RSSB am_m1 rom r3 (at_ rb 0x4c5f0)) as (r4 & RUN4 & D10 & AG4).
    { rewrite <- Rrss. apply rdn_ext; [wd_ulia_c | intros x Hx; apply am_m1_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    { apply RETa; [reflexivity | lia]. }
    { exact C1. }
    (* [comment removed for export] *)
    destruct (amA1c r4 D10) as (r5 & RUN5 & E10 & E8 & E25 & E26 & EK & AG5).
    { rewrite (AG4 2) by notin_list. viaK CK AG2 (2:reg) A2. }
    { rewrite (AG4 23) by notin_list. viaK CK AG2 (23:reg) A23. }
    { rewrite (AG4 18) by notin_list. viaK CK AG2 (18:reg) A18. }
    { rewrite (AG4 22) by notin_list. viaK CK AG2 (22:reg) A22. }
    { rewrite (AG4 9) by notin_list. viaK CK AG2 (9:reg) A9. }
    { eapply regs_agree_trans; [exact AG3 | regs_agree_weaken AG4]. }
    assert (E21 : getr r5 21 = Z_to_bv 64 n). { rewrite (EK 21) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG4 21) by notin_list. viaK CK AG2 (21:reg) A21. }
    Ltac thr5 EK AG4 CK AG2 r A := rewrite (EK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG4 r) by notin_list; rewrite (CK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); let T := fresh in pose proof (AG2 r ltac:(notin_list)) as T; rewrite A in T; exact T.
    assert (E2 : getr r5 2 = at_ sp (-144)) by (thr5 EK AG4 CK AG2 (2:reg) A2).
    assert (E9 : getr r5 9 = Z_to_bv 64 1) by (thr5 EK AG4 CK AG2 (9:reg) A9).
    assert (E18 : getr r5 18 = Z_to_bv 64 8) by (thr5 EK AG4 CK AG2 (18:reg) A18).
    assert (E22 : getr r5 22 = INST) by (thr5 EK AG4 CK AG2 (22:reg) A22).
    assert (E23 : getr r5 23 = stk) by (thr5 EK AG4 CK AG2 (23:reg) A23).
    assert (E27 : getr r5 27 = Z_to_bv 64 1) by (thr5 EK AG4 CK AG2 (27:reg) A27).
    (* [comment removed for export] *)
    destruct (amA2s am_m2 r5 E10 E21 AG5) as (r6 & RUN6 & F19 & FK & AG6).
    (* [comment removed for export] *)
    destruct (amA3a r6 ltac:(rewrite (FK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E26) ltac:(rewrite (FK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E2) AG6) as (r7 & RUN7 & G1' & G10 & G20 & G24 & GK & AG7).
    (* [comment removed for export] *)
    assert (Rm2 : rdn segs am_m2 (Z_to_bv 64 (am_g_magic t)) 8 = Some (LE8 MAGICw)).
    { rewrite <- Rmag. apply rdn_ext; [wd_ulia_c | intros x Hx; apply am_m2_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    assert (Rt2 : rdn segs am_m2 (at_ (am_tbl t) 8) 1 = Some [Z_to_bv 8 4]).
    { rewrite <- Rt16. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply am_m2_outside; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (SOK2 : store_ok segs am_m2 (at_ (at_ sp (-144)) (-8)) 8 = true).
    { rewrite at_at. (lazymatch goal with |- ?G => let G' := eval unfold am_m2, am_m1 in G in change_no_check G' end). repeat (eapply store_ok_mono; [apply wbytes_grows|]).
      eapply (store_ok_sub segs mem (at_ sp (-160)) _ 160); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    destruct (rzl16_run segs rb RB (am_g_magic t) (am_tbl t) RZL RZM RZT am_m2 rom r7 (at_ rb 0x4c718) (at_ sp (-144)) Rm2 ltac:(lia) SOK2
                ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(right; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ])
                (RETa 0x4c718 eq_refl ltac:(lia)) G1' ltac:(rewrite (GK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E2) Rt2 G10)
      as (r8 & RUN8 & H10' & AG8).
    unfold rzM1 in RUN8. rewrite at_at in RUN8. cbn [Z.add] in RUN8.
    (* [comment removed for export] *)
    destruct (amA3b r8 H10') as (r9 & RUN9 & I1 & I10 & I9 & IK & AG9).
    { rewrite (AG8 26) by notin_list. rewrite (GK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E26. }
    { rewrite (AG8 2) by notin_list. rewrite (GK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E2. }
    { rewrite (AG8 24) by notin_list. exact G24. }
    { eapply regs_agree_trans; [exact AG7 | regs_agree_weaken AG8]. }
    (* [comment removed for export] *)
    set (M3a := wbytes am_m2 (at_ sp (-152)) (LE8 (at_ rb 0x4c718))) in *.
    assert (HM3a : forall x : word, (U x < U sp - 152 \/ U sp <= U x)%Z -> M3a x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M3a in G in change_no_check G' end). rewrite wbytes_outside; [apply am_m2_outside; lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (Rm3 : rdn segs M3a (Z_to_bv 64 (am_g_magic t)) 8 = Some (LE8 MAGICw)).
    { rewrite <- Rmag. apply rdn_ext; [wd_ulia_c | intros x Hx; apply HM3a; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    assert (Rt3 : rdn segs M3a (at_ (am_tbl t) 49) 1 = Some [Z_to_bv 8 11]).
    { rewrite <- Rt2048. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM3a; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (SOK3 : store_ok segs M3a (at_ (at_ sp (-144)) (-8)) 8 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold M3a in G in change_no_check G' end). eapply store_ok_mono; [apply wbytes_grows | exact SOK2]. }
    destruct (rzl2048_run segs rb RB (am_g_magic t) (am_tbl t) RZL RZM RZT M3a rom r9 (at_ rb 0x4c72c) (at_ sp (-144)) Rm3 ltac:(lia) SOK3
                ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(right; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ])
                (RETa 0x4c72c eq_refl ltac:(lia)) I1 ltac:(rewrite (IK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG8 2) by notin_list; rewrite (GK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E2) Rt3 I10)
      as (r10 & RUN10 & J10 & AG10).
    unfold rzM1 in RUN10. rewrite at_at in RUN10. cbn [Z.add] in RUN10.
    change (wbytes M3a (at_ sp (-152)) (LE8 (at_ rb 0x4c72c))) with am_m3 in RUN10.
    (* [comment removed for export] *)
    destruct (amA3cs am_m3 r10 J10) as (r11 & RUN11 & K19 & K10 & KK & AG11).
    { rewrite (AG10 9) by notin_list. exact I9. }
    { rewrite (AG10 19) by notin_list. rewrite (IK 19) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 19) by notin_list. rewrite (GK 19) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact F19. }
    { rewrite (AG10 21) by notin_list. rewrite (IK 21) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 21) by notin_list. rewrite (GK 21) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 21) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E21. }
    { eapply regs_agree_trans; [exact AG9 | regs_agree_weaken AG10]. }
    (* [comment removed for export] *)
    Ltac thrB KK AG10 IK AG8 GK FK r H := rewrite (KK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG10 r) by notin_list; rewrite (IK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]);
                                        rewrite (AG8 r) by notin_list; rewrite (GK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H.
    destruct (amA4s r11 K19) as (r12 & RUN12 & L8 & L9 & L19 & L20 & L24 & LK & AG12).
    { thrB KK AG10 IK AG8 GK FK (21:reg) E21. }
    { exact K10. }
    { rewrite (KK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG10 8) by notin_list. rewrite (IK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 8) by notin_list. rewrite (GK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E8. }
    { thrB KK AG10 IK AG8 GK FK (18:reg) E18. }
    { rewrite (KK 20) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG10 20) by notin_list. rewrite (IK 20) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 20) by notin_list. exact G20. }
    { rewrite (KK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG10 26) by notin_list. rewrite (IK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 26) by notin_list. rewrite (GK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E26. }
    { thrB KK AG10 IK AG8 GK FK (2:reg) E2. }
    { eapply regs_agree_trans; [exact AG11 | idtac]. apply regs_agree_refl. }
    exists r12. split.
    { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|].
      eapply msteps_trans; [exact RUN9|]. eapply msteps_trans; [exact RUN10|]. eapply msteps_trans; [exact RUN11 | exact RUN12]. }
    Ltac thrC LK KK AG10 IK AG8 GK FK r H := rewrite (LK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (KK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG10 r) by notin_list; rewrite (IK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]);
                                        rewrite (AG8 r) by notin_list; rewrite (GK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H.
    split; [thrC LK KK AG10 IK AG8 GK FK (2:reg) E2|]. split; [exact L8|]. split; [exact L9|]. split; [thrC LK KK AG10 IK AG8 GK FK (18:reg) E18|].
    split; [exact L19|]. split; [exact L20|]. split; [thrC LK KK AG10 IK AG8 GK FK (21:reg) E21|]. split; [thrC LK KK AG10 IK AG8 GK FK (22:reg) E22|].
    split; [thrC LK KK AG10 IK AG8 GK FK (23:reg) E23|]. split; [exact L24|].
    split; [rewrite (LK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (KK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG10 25) by notin_list; rewrite (IK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG8 25) by notin_list; rewrite (GK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E25|].
    split; [thrC LK KK AG10 IK AG8 GK FK (26:reg) E26|].
    split; [thrC LK KK AG10 IK AG8 GK FK (27:reg) E27|].
    exact AG12.
  Qed.

End AMS.
End FPGen1.
End BoAllocM2s.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7g OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7j OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM7r.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7g OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7j.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Section RFR.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HRF : code_ato segs rb 0x5143c rf_words.
  Hypothesis HGF : code_ato segs rb 0x5153c gf_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Variable gmsk : Z.
  Hypothesis GMSK : gauipc_ld segs rb 0x516e4 0x516f4 14 14 gmsk.
  Hypothesis Ggm : (AIMGLO <= gmsk /\ gmsk + 8 <= AIMGHI)%Z.

  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp cache pc alloc : word) (c mc SPB nf : Z) (msk stv : word) (faf : Z -> Z).
  #[local] Abbreviation RIz := (SPB + 2 ^ 37 + 128 * c)%Z.
  #[local] Abbreviation RI := (Z_to_bv 64 (SPB + 2 ^ 37 + 128 * c)).
  #[local] Abbreviation FABz := (SPB + c * 2 ^ 32 + 3758096384)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = cache.
  Hypothesis H11 : getr regs 11 = pc.
  Hypothesis H12 : getr regs 12 = alloc.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 c.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-160)) 160 = true.          (* [comment removed for export] *)
  Hypothesis G1 : (SPB + 2 ^ 37 + 4096 + 160 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Gpc : (U cache + 2640 <= U sp - 160)%Z /\ (U pc = U cache + 80 * c)%Z /\ (1 <= c <= 30)%Z /\ (U cache mod 4 = 0)%Z.
  (* [comment removed for export] *)
  Hypothesis GcT : (U cache + 2640 <= SPB \/ SPB + 2 ^ 37 + 4096 <= U cache)%Z.
  Hypothesis GcI : (AIMGHI <= U cache \/ U cache + 2640 <= AIMGLO)%Z.
  Hypothesis Galloc : (AIMGLO <= U alloc /\ U alloc + 56 <= AIMGHI)%Z.
  Hypothesis GSPB : (0 <= SPB)%Z /\ (SPB + 2 ^ 37 + 4096 < 2 ^ 47)%Z /\ (SPB mod 2 ^ 16 = 0)%Z /\ (0x10007fff8000 <= SPB)%Z.
  (* [comment removed for export] *)
  Hypothesis Rspb : rdn segs mem (at_ alloc 32) 8 = Some (LE8 (Z_to_bv 64 SPB)).
  Hypothesis Rrib : rdn segs mem (at_ alloc 48) 8 = Some (LE8 (Z_to_bv 64 (SPB + 2 ^ 37))).
  Hypothesis Rmu : rdn segs mem RI 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis SOKmu : store_ok segs mem RI 8 = true.
  Hypothesis Rnf : rdn segs mem (at_ RI 16) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis SOKnf : store_ok segs mem (at_ RI 16) 8 = true.
  Hypothesis Rst : rdn segs mem (at_ RI 72) 8 = Some (LE8 stv).
  Hypothesis SOKst : store_ok segs mem (at_ RI 72) 8 = true.
  Hypothesis Rmsk : rdn segs mem (Z_to_bv 64 gmsk) 8 = Some (LE8 msk).
  Hypothesis SOKpc : store_ok segs mem pc 48 = true.






End RFR.
End FPGen1.
End BoAllocM7r.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM3m.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7g BoAllocM7r.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Definition cbm_words : list (option (bv 32)) :=
  [Some W_50f7c; Some W_50f80; Some W_50f84; Some W_50f88; Some W_50f8c; Some W_50f90; Some W_50f94; Some W_50f98;
   Some W_50f9c; Some W_50fa0; Some W_50fa4; Some W_50fa8; Some W_50fac; Some W_50fb0; Some W_50fb4; Some W_50fb8;
   Some W_50fbc; Some W_50fc0]%list.

(* [comment removed for export] *)
Definition cbm_clob : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30].

Section CBM.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HCB : code_ato segs rb 0x50cec cb_words.
  Hypothesis HCBM : code_ato segs rb 0x50f7c cbm_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.

  Lemma J50e80 : fetch_word segs (at_ rb 0x50e80) = Some W_50e80.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 101 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50e84 : fetch_word segs (at_ rb 0x50e84) = Some W_50e84.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 102 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50e88 : fetch_word segs (at_ rb 0x50e88) = Some W_50e88.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 103 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50e8c : fetch_word segs (at_ rb 0x50e8c) = Some W_50e8c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 104 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50e90 : fetch_word segs (at_ rb 0x50e90) = Some W_50e90.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 105 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50e94 : fetch_word segs (at_ rb 0x50e94) = Some W_50e94.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 106 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50e98 : fetch_word segs (at_ rb 0x50e98) = Some W_50e98.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 107 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50e9c : fetch_word segs (at_ rb 0x50e9c) = Some W_50e9c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 108 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50ea0 : fetch_word segs (at_ rb 0x50ea0) = Some W_50ea0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 109 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50ea4 : fetch_word segs (at_ rb 0x50ea4) = Some W_50ea4.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 110 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50ea8 : fetch_word segs (at_ rb 0x50ea8) = Some W_50ea8.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 111 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50eac : fetch_word segs (at_ rb 0x50eac) = Some W_50eac.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 112 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50eb0 : fetch_word segs (at_ rb 0x50eb0) = Some W_50eb0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 113 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50eb4 : fetch_word segs (at_ rb 0x50eb4) = Some W_50eb4.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 114 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50eb8 : fetch_word segs (at_ rb 0x50eb8) = Some W_50eb8.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 115 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50ebc : fetch_word segs (at_ rb 0x50ebc) = Some W_50ebc.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 116 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50ec0 : fetch_word segs (at_ rb 0x50ec0) = Some W_50ec0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 117 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50ec4 : fetch_word segs (at_ rb 0x50ec4) = Some W_50ec4.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 118 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50ec8 : fetch_word segs (at_ rb 0x50ec8) = Some W_50ec8.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 119 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50ecc : fetch_word segs (at_ rb 0x50ecc) = Some W_50ecc.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 120 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50ed0 : fetch_word segs (at_ rb 0x50ed0) = Some W_50ed0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 121 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50ed4 : fetch_word segs (at_ rb 0x50ed4) = Some W_50ed4.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 122 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50ed8 : fetch_word segs (at_ rb 0x50ed8) = Some W_50ed8.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 123 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50edc : fetch_word segs (at_ rb 0x50edc) = Some W_50edc.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 124 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50ee0 : fetch_word segs (at_ rb 0x50ee0) = Some W_50ee0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 125 _ HCB eq_refl). Qed.


   (* [comment removed for export] *)
  Lemma J50ef0 : fetch_word segs (at_ rb 0x50ef0) = Some W_50ef0.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 129 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50ef4 : fetch_word segs (at_ rb 0x50ef4) = Some W_50ef4.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 130 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50ef8 : fetch_word segs (at_ rb 0x50ef8) = Some W_50ef8.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 131 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50efc : fetch_word segs (at_ rb 0x50efc) = Some W_50efc.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 132 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50f00 : fetch_word segs (at_ rb 0x50f00) = Some W_50f00.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 133 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50f04 : fetch_word segs (at_ rb 0x50f04) = Some W_50f04.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 134 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50f08 : fetch_word segs (at_ rb 0x50f08) = Some W_50f08.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 135 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50f0c : fetch_word segs (at_ rb 0x50f0c) = Some W_50f0c.  Proof using HCB. exact (code_ato_get segs rb 0x50cec cb_words 136 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50f7c : fetch_word segs (at_ rb 0x50f7c) = Some W_50f7c.  Proof using HCBM. exact (code_ato_get segs rb 0x50f7c cbm_words 0 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50f80 : fetch_word segs (at_ rb 0x50f80) = Some W_50f80.  Proof using HCBM. exact (code_ato_get segs rb 0x50f7c cbm_words 1 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50f84 : fetch_word segs (at_ rb 0x50f84) = Some W_50f84.  Proof using HCBM. exact (code_ato_get segs rb 0x50f7c cbm_words 2 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50f88 : fetch_word segs (at_ rb 0x50f88) = Some W_50f88.  Proof using HCBM. exact (code_ato_get segs rb 0x50f7c cbm_words 3 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50f8c : fetch_word segs (at_ rb 0x50f8c) = Some W_50f8c.  Proof using HCBM. exact (code_ato_get segs rb 0x50f7c cbm_words 4 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50f90 : fetch_word segs (at_ rb 0x50f90) = Some W_50f90.  Proof using HCBM. exact (code_ato_get segs rb 0x50f7c cbm_words 5 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50f94 : fetch_word segs (at_ rb 0x50f94) = Some W_50f94.  Proof using HCBM. exact (code_ato_get segs rb 0x50f7c cbm_words 6 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50f98 : fetch_word segs (at_ rb 0x50f98) = Some W_50f98.  Proof using HCBM. exact (code_ato_get segs rb 0x50f7c cbm_words 7 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50f9c : fetch_word segs (at_ rb 0x50f9c) = Some W_50f9c.  Proof using HCBM. exact (code_ato_get segs rb 0x50f7c cbm_words 8 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50fa0 : fetch_word segs (at_ rb 0x50fa0) = Some W_50fa0.  Proof using HCBM. exact (code_ato_get segs rb 0x50f7c cbm_words 9 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50fa4 : fetch_word segs (at_ rb 0x50fa4) = Some W_50fa4.  Proof using HCBM. exact (code_ato_get segs rb 0x50f7c cbm_words 10 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50fa8 : fetch_word segs (at_ rb 0x50fa8) = Some W_50fa8.  Proof using HCBM. exact (code_ato_get segs rb 0x50f7c cbm_words 11 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50fac : fetch_word segs (at_ rb 0x50fac) = Some W_50fac.  Proof using HCBM. exact (code_ato_get segs rb 0x50f7c cbm_words 12 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50fb0 : fetch_word segs (at_ rb 0x50fb0) = Some W_50fb0.  Proof using HCBM. exact (code_ato_get segs rb 0x50f7c cbm_words 13 _ HCBM eq_refl). Qed.



   (* [comment removed for export] *)

  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp cache inst : word) (s : Z).
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = inst.
  Hypothesis H11 : getr regs 11 = cache.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 s.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 8.
  Hypothesis Hs : (24 <= s <= 65536)%Z /\ (s mod 8 = 0)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-48)) 48 = true.
  Hypothesis G1 : (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.

  #[local] Abbreviation CLX := (fun r => In r (2 :: 8 :: cb_clob)).
  (* [comment removed for export] *)
  #[local] Abbreviation CLM := (fun r => In r (1 :: 9 :: 18 :: 19 :: 20 :: 2 :: 8 :: cbm_clob)).
  #[local] Abbreviation CLR := (fun r => In r (2 :: 8 :: cbm_clob)).

  Ltac vz := cbv delta [v_add v_addi v_mul v_slli v_srli v_sub] beta; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; unorm;
             first [reflexivity | f_equal; lia | apply bv_eq; wd_ulia].

  (* [comment removed for export] *)
  Lemma cbM : forall (M : word -> option byte) r0 (c : Z),
    getr r0 8 = Z_to_bv 64 c -> getr r0 2 = at_ sp (-48) -> getr r0 10 = inst -> getr r0 11 = cache -> getr r0 13 = Z_to_bv 64 8 ->
    regs_agree CLX regs r0 ->
    (1 <= c <= 30)%Z ->
    rdn segs M (at_ cache (80 * c)) 4 = Some (LE4 0) ->
    (U cache + 2584 <= U sp - 48)%Z ->
    exists r, msteps segs (mkst r0 (at_ rb 0x50e80) M rom) (mkst r (at_ rb 0x5143c) M rom)
      /\ getr r 1 = at_ rb 0x50f9c /\ getr r 2 = at_ sp (-48) /\ getr r 10 = cache /\ getr r 11 = at_ cache (80 * c) /\ getr r 12 = inst
      /\ getr r 13 = Z_to_bv 64 c /\ getr r 8 = Z_to_bv 64 c /\ getr r 9 = at_ cache (80 * c) /\ getr r 18 = Z_to_bv 64 8
      /\ getr r 19 = cache /\ getr r 20 = inst
      /\ regs_agree CLM regs r.
  Proof using G1 Hs s HCBM HCB.
    intros M r0 c R8 R2 R10 R11 R13 AG0 Hc Rcnt Gcs.
    destruct G1 as [G1a G1b]. pose proof (u64_range sp) as Hspr. pose proof (u64_range cache) as Hcr. pose proof (u64_range inst) as Hir.
    wd_eexists. split.
    - ab_ft J50e80 D_50e80 ltac:(condz).                  (* [comment removed for export] *)
      an J50e84 D_50e84.                                   (* [comment removed for export] *)
      ab_ft J50e88 D_50e88 ltac:(condz).                  (* [comment removed for export] *)
      an J50e8c D_50e8c.                                   (* [comment removed for export] *)
      av J50e90 D_50e90 (Z_to_bv 64 (80 * c)) ltac:(vz).  (* [comment removed for export] *)
      av J50e94 D_50e94 (at_ cache (80 * c)) ltac:(rewrite v_add_at by lia; reflexivity).  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [exact J50e98 | reflexivity | exact D_50e98 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; exact Rcnt | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small 0) by lia; vn.                 (* [comment removed for export] *)
      ab_tk J50e9c D_50e9c ltac:(condz).                  (* [comment removed for export] *)
      an J50f7c D_50f7c.                                   (* [comment removed for export] *)
      an J50f80 D_50f80.                                   (* [comment removed for export] *)
      an J50f84 D_50f84.                                   (* [comment removed for export] *)
      an J50f88 D_50f88.                                   (* [comment removed for export] *)
      an J50f8c D_50f8c.                                   (* [comment removed for export] *)
      an J50f90 D_50f90.                                   (* [comment removed for export] *)
      an J50f94 D_50f94.                                   (* [comment removed for export] *)
      an J50f98 D_50f98.                                   (* [comment removed for export] *)
      wd_refl.
    - post. unfold cbm_clob, cb_clob in *. ra_chain.
  Qed.



  (* [comment removed for export] *)
  Hypothesis HRF : code_ato segs rb 0x5143c rf_words.
  Hypothesis HGF : code_ato segs rb 0x5153c gf_words.
  Variable gmsk : Z.
  Hypothesis GMSK : gauipc_ld segs rb 0x516e4 0x516f4 14 14 gmsk.
  Hypothesis Ggm : (AIMGLO <= gmsk /\ gmsk + 8 <= AIMGHI)%Z.
  Variables (nf : Z) (csz stw sbeg msk stv : word) (faf : Z -> Z).
  #[local] Abbreviation SPB := (U sbeg).
  #[local] Abbreviation cc := (class_of s).
  #[local] Abbreviation RIz := (U sbeg + 2 ^ 37 + 128 * class_of s)%Z.
  #[local] Abbreviation RI := (Z_to_bv 64 (U sbeg + 2 ^ 37 + 128 * class_of s)).
  #[local] Abbreviation FABz := (U sbeg + class_of s * 2 ^ 32 + 3758096384)%Z.
  Hypothesis HstkM : store_ok segs mem (at_ sp (-208)) 208 = true.        (* [comment removed for export] *)
  Hypothesis G1M : (U sbeg + 2 ^ 37 + 4096 + 208 <= U sp)%Z.
  Hypothesis GcM : (U cache + 2640 <= U sp - 208)%Z /\ (U cache mod 8 = 0)%Z.
  Hypothesis GcT : (U cache + 2640 <= U sbeg \/ U sbeg + 2 ^ 37 + 4096 <= U cache)%Z.
  Hypothesis GcI : (AIMGHI <= U cache \/ U cache + 2640 <= AIMGLO)%Z.
  Hypothesis Ginst : (AIMGLO <= U inst /\ U inst + 56 <= AIMGHI)%Z.
  Hypothesis GSPB : (U sbeg + 2 ^ 37 + 4096 < 2 ^ 47)%Z /\ (U sbeg mod 2 ^ 16 = 0)%Z /\ (0x10007fff8000 <= U sbeg)%Z.
  Hypothesis Hnf : (0 <= nf <= 2 ^ 27)%Z.
  Hypothesis Rcnt0 : rdn segs mem (at_ cache (80 * cc)) 4 = Some (LE4 0).
  Hypothesis Rcsz : rdn segs mem (at_ cache (80 * cc + 8)) 8 = Some (LE8 csz).
  Hypothesis Rstw : rdn segs mem (at_ cache 2576) 8 = Some (LE8 stw).
  Hypothesis SOKstw : store_ok segs mem (at_ cache 2576) 8 = true.
  Hypothesis SOKpc : store_ok segs mem (at_ cache (80 * cc)) 48 = true.
  Hypothesis Rsb : rdn segs mem (at_ inst 32) 8 = Some (LE8 sbeg).
  Hypothesis Rrib : rdn segs mem (at_ inst 48) 8 = Some (LE8 (Z_to_bv 64 (U sbeg + 2 ^ 37))).
  Hypothesis Rmu : rdn segs mem RI 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis SOKmu : store_ok segs mem RI 8 = true.
  Hypothesis Rnf : rdn segs mem (at_ RI 16) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis SOKnf : store_ok segs mem (at_ RI 16) 8 = true.
  Hypothesis Rst : rdn segs mem (at_ RI 72) 8 = Some (LE8 stv).
  Hypothesis SOKst : store_ok segs mem (at_ RI 72) 8 = true.
  Hypothesis Rmsk : rdn segs mem (Z_to_bv 64 gmsk) 8 = Some (LE8 msk).
  Hypothesis Hfaf : forall j, (Z.max 0 (nf - 8) <= j < nf)%Z -> rdn segs mem (Z_to_bv 64 (FABz + 4 * j)) 4 = Some (LE4 (faf j)) /\ (0 <= faf j < 2 ^ 32)%Z.




  (* [comment removed for export] *)
  Lemma cb_miss_head :
    exists r3, msteps segs (mkst regs (at_ rb 0x50cec) mem rom) (mkst r3 (at_ rb 0x5143c) (cb_m1 regs mem ra sp) rom)
      /\ getr r3 1 = at_ rb 0x50f9c /\ getr r3 2 = at_ sp (-48) /\ getr r3 10 = cache /\ getr r3 11 = at_ cache (80 * cc) /\ getr r3 12 = inst
      /\ getr r3 13 = Z_to_bv 64 cc /\ getr r3 8 = Z_to_bv 64 cc /\ getr r3 9 = at_ cache (80 * cc) /\ getr r3 18 = Z_to_bv 64 8
      /\ getr r3 19 = cache /\ getr r3 20 = inst /\ regs_agree CLM regs r3.
  Proof using G1 G1M GSPB GcI GcM GcT Ggm Ginst H1 H10 H11 H12 H13 H2 HCB HCBM Hnf Hs Hstk RB Rcnt0.
    destruct G1 as [G1a G1b]. destruct GcM as [Gc1 Gc2]. pose proof Hs as [Hs1 Hs2]. pose proof (u64_range sp) as Hspr. pose proof (u64_range cache).
    pose proof (AsArith3.class_of_range s ltac:(lia)) as Hc.
    destruct (cbP segs rb HCB regs mem rom ra sp cache inst s H1 H2 H10 H11 H12 H13 Hs Hstk G1) as (r1 & RUN1 & A2 & A10 & A11 & A12 & A13 & A14 & A15 & AG1).
    assert (CID : exists r2, msteps segs (mkst r1 (at_ rb 0x50d70) (cb_m1 regs mem ra sp) rom) (mkst r2 (at_ rb 0x50e80) (cb_m1 regs mem ra sp) rom)
              /\ getr r2 8 = Z_to_bv 64 cc /\ (forall i : reg, In i [2; 10; 11; 13] -> getr r2 i = getr r1 i) /\ regs_agree CLX regs r2).
    { destruct (Z.leb_spec s 512).
      - exact (cbLo segs rb HCB regs rom s Hs (cb_m1 regs mem ra sp) r1 ltac:(lia) A12 A14 AG1).
      - exact (cbHi segs rb HCB regs rom s Hs (cb_m1 regs mem ra sp) r1 ltac:(lia) A12 A14 AG1). }
    destruct CID as (r2 & RUN2 & B8 & BK & AG2).
    destruct (cbM (cb_m1 regs mem ra sp) r2 cc B8 ltac:(rewrite (BK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A2) ltac:(rewrite (BK 10) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A10)
                ltac:(rewrite (BK 11) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A11) ltac:(rewrite (BK 13) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A13) AG2 Hc)
      as (r3 & RUN3 & C1 & C2 & C10 & C11 & C12 & C13 & C8 & C9 & C18 & C19 & C20 & AG3).
    { rewrite <- Rcnt0. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; rewrite at_u in Hx by lia; cbn in Hx; apply (cb_m1_outside rb regs mem ra sp s G1); lia]. }
    { lia. }
    exists r3. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2 | exact RUN3]|].
    exact (conj C1 (conj C2 (conj C10 (conj C11 (conj C12 (conj C13 (conj C8 (conj C9 (conj C18 (conj C19 (conj C20 AG3))))))))))).
  Qed.


End CBM.
End FPGen1.
End BoAllocM3m.
Module BoAllocM3n.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7g BoAllocM7r BoAllocM3m.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac ha_prev := tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Section AMBM.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HAL : code_ato segs rb 0x4c594 al_words.
  Hypothesis HCB : code_ato segs rb 0x50cec cb_words.
  Hypothesis HCBM : code_ato segs rb 0x50f7c cbm_words.
  Hypothesis HRF : code_ato segs rb 0x5143c rf_words.
  Hypothesis HGF : code_ato segs rb 0x5153c gf_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Variable gt : gct_tab.
  Hypothesis GTOK : gct_tab_ok segs gt.
  Hypothesis GTRB : gt_rb gt = rb.
  Variable gmsk : Z.
  Hypothesis GMSK : gauipc_ld segs rb 0x516e4 0x516f4 14 14 gmsk.
  Hypothesis Ggm : (AIMGLO <= gmsk /\ gmsk + 8 <= AIMGHI)%Z.

  Lemma J67750 : fetch_word segs (at_ rb 0x4c814) = Some W_4c814.  Proof using HAL. exact (code_ato_get segs rb 0x4c594 al_words 160 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J67754 : fetch_word segs (at_ rb 0x4c818) = Some W_4c818.  Proof using HAL. exact (code_ato_get segs rb 0x4c594 al_words 161 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J67758 : fetch_word segs (at_ rb 0x4c81c) = Some W_4c81c.  Proof using HAL. exact (code_ato_get segs rb 0x4c594 al_words 162 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J6775c : fetch_word segs (at_ rb 0x4c820) = Some W_4c820.  Proof using HAL. exact (code_ato_get segs rb 0x4c594 al_words 163 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J67760 : fetch_word segs (at_ rb 0x4c824) = Some W_4c824.  Proof using HAL. exact (code_ato_get segs rb 0x4c594 al_words 164 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J67764 : fetch_word segs (at_ rb 0x4c828) = Some W_4c828.  Proof using HAL. exact (code_ato_get segs rb 0x4c594 al_words 165 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J67768 : fetch_word segs (at_ rb 0x4c82c) = Some W_4c82c.  Proof using HAL. exact (code_ato_get segs rb 0x4c594 al_words 166 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J6776c : fetch_word segs (at_ rb 0x4c830) = Some W_4c830.  Proof using HAL. exact (code_ato_get segs rb 0x4c594 al_words 167 _ HAL eq_refl). Qed.   (* [comment removed for export] *)

  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (sp tp tsdp tctx thr inst : word) (n : Z).
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 (needed n).
  Hypothesis H22 : getr regs 22 = inst.
  Hypothesis Hn : (1 <= n <= 64512)%Z.
  Hypothesis GH : gctH segs gt mem sp tp tsdp tctx thr.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-208)) 208 = true.
  Hypothesis G1 : (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Gthr : (4096 <= U thr /\ (U thr + 4096 <= AIMGLO \/ AIMGHI <= U thr))%Z /\ (U thr + 4096 <= U sp - 208)%Z /\ (U thr mod 8 = 0)%Z.
  Hypothesis Ginst : (AIMGLO <= U inst /\ U inst + 56 <= AIMGHI)%Z.
  (* [comment removed for export] *)
  Variables (nf : Z) (csz stw sbeg msk stv : word) (faf : Z -> Z).
  #[local] Abbreviation cc := (class_of (needed n)).
  #[local] Abbreviation RIz := (U sbeg + 2 ^ 37 + 128 * class_of (needed n))%Z.
  #[local] Abbreviation RI := (Z_to_bv 64 (U sbeg + 2 ^ 37 + 128 * class_of (needed n))).
  #[local] Abbreviation FABz := (U sbeg + class_of (needed n) * 2 ^ 32 + 3758096384)%Z.
  Hypothesis GTS : (U thr + 4096 <= U sbeg \/ U sbeg + 2 ^ 37 + 4096 <= U thr)%Z.
  Hypothesis G1M : (U sbeg + 2 ^ 37 + 4096 + 208 <= U sp)%Z.
  Hypothesis GSPB : (U sbeg + 2 ^ 37 + 4096 < 2 ^ 47)%Z /\ (U sbeg mod 2 ^ 16 = 0)%Z /\ (0x10007fff8000 <= U sbeg)%Z.
  Hypothesis Hnf : (0 <= nf <= 2 ^ 27)%Z.
  Hypothesis Rcnt0 : rdn segs mem (at_ thr (208 + 80 * cc)) 4 = Some (LE4 0).
  Hypothesis Rcsz : rdn segs mem (at_ thr (208 + 80 * cc + 8)) 8 = Some (LE8 csz).
  Hypothesis Rstw : rdn segs mem (at_ thr 2784) 8 = Some (LE8 stw).
  Hypothesis SOKstw : store_ok segs mem (at_ thr 2784) 8 = true.
  Hypothesis SOKpc : store_ok segs mem (at_ thr (208 + 80 * cc)) 48 = true.
  Hypothesis Rsb : rdn segs mem (at_ inst 32) 8 = Some (LE8 sbeg).
  Hypothesis Rrib : rdn segs mem (at_ inst 48) 8 = Some (LE8 (Z_to_bv 64 (U sbeg + 2 ^ 37))).
  Hypothesis Rmu : rdn segs mem RI 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis SOKmu : store_ok segs mem RI 8 = true.
  Hypothesis Rnf : rdn segs mem (at_ RI 16) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis SOKnf : store_ok segs mem (at_ RI 16) 8 = true.
  Hypothesis Rst : rdn segs mem (at_ RI 72) 8 = Some (LE8 stv).
  Hypothesis SOKst : store_ok segs mem (at_ RI 72) 8 = true.
  Hypothesis Rmsk : rdn segs mem (Z_to_bv 64 gmsk) 8 = Some (LE8 msk).
  Hypothesis Hfaf : forall j, (Z.max 0 (nf - 8) <= j < nf)%Z -> rdn segs mem (Z_to_bv 64 (FABz + 4 * j)) 4 = Some (LE4 (faf j)) /\ (0 <= faf j < 2 ^ 32)%Z.

  #[local] Abbreviation CLBm := (fun r => In r (26 :: 1 :: 5 :: 6 :: 7 :: 10 :: 11 :: 12 :: 13 :: 14 :: 15 :: 16 :: 17 :: 28 :: 29 :: 30 :: nil)).


  (* [comment removed for export] *)
  Ltac nixm Hx Hni Hnin := repeat (destruct Hx as [<-|Hx]; [first [apply Hni; solve [in_list] | apply Hnin; solve [in_list]] |]); destruct Hx.


  (* [comment removed for export] *)
  Lemma ambm_glue :
    exists r2 (M1 : word -> option byte),
      msteps segs (mkst regs (at_ rb 0x4c814) mem rom) (mkst r2 (at_ rb 0x50cec) M1 rom)
      /\ M1 = wbytes mem (at_ sp (-8)) (LE8 (at_ rb 0x4c818))
      /\ getr r2 1 = at_ rb 0x4c834 /\ getr r2 2 = sp /\ getr r2 10 = inst /\ getr r2 11 = at_ thr 208
      /\ getr r2 12 = Z_to_bv 64 (needed n) /\ getr r2 13 = Z_to_bv 64 8 /\ getr r2 26 = thr
      /\ (forall i : reg, In i [4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27; 3] -> getr r2 i = getr regs i)
      /\ (forall i : reg, ~ In i [26; 1; 10; 11; 12; 13] -> getr r2 i = getr regs i).
  Proof using sbeg Gthr G1 GH Hn H22 H19 H4 H2 tctx tsdp tp GTRB GTOK gt HAL.
    pose proof G1 as [G1a G1b]. pose proof Gthr as (Gt1 & Gt2 & Gt3). pose proof (u64_range sp) as Hspr. pose proof (u64_range thr) as Hthr. pose proof (u64_range inst) as Hir.
    pose proof (needed_facts n Hn) as NF. pose proof (AsArith3.class_of_range (needed n) ltac:(lia)) as Hc.
    (* [comment removed for export] *)
    assert (W0 : exists r0, msteps segs (mkst regs (at_ rb 0x4c814) mem rom) (mkst r0 (at_ rb 0x78e2c) mem rom)
                 /\ getr r0 1 = at_ rb 0x4c818 /\ (forall i : reg, i <> 1 -> getr r0 i = getr regs i)).
    { wd_eexists. split; [an J67750 D_4c814; wd_refl|]. split; [gres; reflexivity|]. intros i Hi. rewrite getr_other by (intros E; apply Hi; exact E). reflexivity. }
    destruct W0 as (r0 & RUN0 & A1 & AK).
    destruct (gct_run segs gt GTOK mem rom r0 (at_ rb 0x4c818) sp tp tsdp tctx thr GH) as (r1 & RUN1 & B10 & B11 & AG1).
    { rewrite <- GTRB. pose proof (gto_rb _ _ GTOK) as [E1 E2]. pose proof (u64_range (gt_rb gt)). apply ret_ok_at; [exact E1 | reflexivity | lia]. }
    { exact A1. } { rewrite AK by (intros E; discriminate E). exact H2. } { rewrite AK by (intros E; discriminate E). exact H4. }
    rewrite GTRB in RUN1.
    set (M1 := wbytes mem (at_ sp (-8)) (LE8 (at_ rb 0x4c818))) in RUN1.
    (* [comment removed for export] *)
    Ltac r1eq AG1 AK r H := rewrite (AG1 r) by notin_list; rewrite (AK r) by (intros E; discriminate E); exact H.
    assert (W2 : exists r2, msteps segs (mkst r1 (at_ rb 0x4c818) M1 rom) (mkst r2 (at_ rb 0x50cec) M1 rom)
                 /\ getr r2 1 = at_ rb 0x4c834 /\ getr r2 2 = sp /\ getr r2 10 = inst /\ getr r2 11 = at_ thr 208
                 /\ getr r2 12 = Z_to_bv 64 (needed n) /\ getr r2 13 = Z_to_bv 64 8 /\ getr r2 26 = thr
                 /\ (forall i : reg, In i [4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27; 3] -> getr r2 i = getr regs i)
                 /\ regs_agree (fun r => In r [26; 1; 10; 11; 12; 13]) r1 r2).
    { wd_eexists. split.
      - an J67754 D_4c818.                                   (* [comment removed for export] *)
        ab_ft J67758 D_4c81c ltac:(condz).                  (* [comment removed for export] *)
        an J6775c D_4c820.                                   (* [comment removed for export] *)
        an J67760 D_4c824.                                   (* [comment removed for export] *)
        an J67764 D_4c828.                                   (* [comment removed for export] *)
        an J67768 D_4c82c.                                   (* [comment removed for export] *)
        an J6776c D_4c830.                                   (* [comment removed for export] *)
        wd_refl.
      - post; rewrite ?B10, ?at_0; try reflexivity.
        + r1eq AG1 AK (2:reg) H2.
        + r1eq AG1 AK (22:reg) H22.
        + r1eq AG1 AK (19:reg) H19.
        + intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; rewrite (AG1 _) by notin_list; apply AK; intros E; discriminate E|]); destruct Hi.
        + ra_solve. }
    destruct W2 as (r2 & RUN2 & C1 & C2 & C10 & C11 & C12 & C13 & C26 & CK & AG2).
    exists r2, M1. split; [eapply msteps_trans; [exact RUN0|]; eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    split; [reflexivity|]. split; [exact C1|]. split; [exact C2|]. split; [exact C10|]. split; [exact C11|]. split; [exact C12|]. split; [exact C13|]. split; [exact C26|].
    split; [exact CK|].
    intros i Hni. rewrite (AG2 i Hni). rewrite (AG1 i); [apply AK; intros ->; apply Hni; solve [in_list]|].
    intros Hx. cbn [gct_clob In] in Hx. repeat (destruct Hx as [<-|Hx]; [apply Hni; solve [in_list]|]). destruct Hx.
  Qed.


End AMBM.
End FPGen1.
End BoAllocM3n.
Module BoAllocM3p.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7g BoAllocM7r BoAllocM3m BoAllocM3n.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition amh_M1 (rb : word) (mem : word -> option byte) (sp : word) : word -> option byte := wbytes mem (at_ sp (-8)) (LE8 (at_ rb 0x4c818)).
Definition amh_mem (rb : word) (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) : word -> option byte :=
  cb_m1 regs (amh_M1 rb mem sp) (at_ rb 0x4c834) sp.
Lemma amh_M1_outside : forall rb mem (sp : word), (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z ->
  forall x : word, (U x < U sp - 8 \/ U sp <= U x)%Z -> amh_M1 rb mem sp x = mem x.
Proof using.
  intros rb mem sp [G1a G1b] x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold amh_M1 in G in change_no_check G' end).
  rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
Qed.
Lemma amh_mem_outside : forall rb regs mem (sp : word), (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z ->
  forall x : word, (U x < U sp - 48 \/ U sp <= U x)%Z -> amh_mem rb regs mem sp x = mem x.
Proof using.
  intros rb regs mem sp G1 x Hx. (lazymatch goal with |- ?G => let G' := eval unfold amh_mem in G in change_no_check G' end). rewrite (cb_m1_outside rb regs (amh_M1 rb mem sp) (at_ rb 0x4c834) sp 24 G1) by exact Hx.
  apply amh_M1_outside; [exact G1 | lia].
Qed.
Lemma amh_mem_grows : forall rb regs mem sp, mem_grows mem (amh_mem rb regs mem sp).
Proof using. intros rb regs mem sp. (lazymatch goal with |- ?G => let G' := eval unfold amh_mem in G in change_no_check G' end). eapply mem_grows_trans; [(lazymatch goal with |- ?G => let G' := eval unfold amh_M1 in G in change_no_check G' end); apply wbytes_grows | apply cb_m1_grows]. Qed.
(* [comment removed for export] *)
Lemma amh_mem_slots : forall segs rb regs mem (sp : word), (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z ->
  forall (k : Z) (v : word), In (k, v) [(-8, at_ rb 0x4c834); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20)]%Z ->
  rdn segs (amh_mem rb regs mem sp) (at_ sp k) 8 = Some (LE8 v).
Proof using. intros segs rb regs mem sp G1 k v Hin. (lazymatch goal with |- ?G => let G' := eval unfold amh_mem in G in change_no_check G' end). exact (cb_m1_slots segs rb regs (amh_M1 rb mem sp) (at_ rb 0x4c834) sp 24 G1 k v Hin). Qed.

Section AMBM.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HAL : code_ato segs rb 0x4c594 al_words.
  Hypothesis HCB : code_ato segs rb 0x50cec cb_words.
  Hypothesis HCBM : code_ato segs rb 0x50f7c cbm_words.
  Hypothesis HRF : code_ato segs rb 0x5143c rf_words.
  Hypothesis HGF : code_ato segs rb 0x5153c gf_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Variable gt : gct_tab.
  Hypothesis GTOK : gct_tab_ok segs gt.
  Hypothesis GTRB : gt_rb gt = rb.
  Variable gmsk : Z.
  Hypothesis GMSK : gauipc_ld segs rb 0x516e4 0x516f4 14 14 gmsk.
  Hypothesis Ggm : (AIMGLO <= gmsk /\ gmsk + 8 <= AIMGHI)%Z.


  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (sp tp tsdp tctx thr inst : word) (n : Z).
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 (needed n).
  Hypothesis H22 : getr regs 22 = inst.
  Hypothesis Hn : (1 <= n <= 64512)%Z.
  Hypothesis GH : gctH segs gt mem sp tp tsdp tctx thr.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-208)) 208 = true.
  Hypothesis G1 : (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Gthr : (4096 <= U thr /\ (U thr + 4096 <= AIMGLO \/ AIMGHI <= U thr))%Z /\ (U thr + 4096 <= U sp - 208)%Z /\ (U thr mod 8 = 0)%Z.
  Hypothesis Ginst : (AIMGLO <= U inst /\ U inst + 56 <= AIMGHI)%Z.

  Variables (nf : Z) (sbeg : word).
  #[local] Abbreviation cc := (class_of (needed n)).
  Hypothesis GTS : (U thr + 4096 <= U sbeg \/ U sbeg + 2 ^ 37 + 4096 <= U thr)%Z.
  Hypothesis G1M : (U sbeg + 2 ^ 37 + 4096 + 208 <= U sp)%Z.
  Hypothesis GSPB : (U sbeg + 2 ^ 37 + 4096 < 2 ^ 47)%Z /\ (U sbeg mod 2 ^ 16 = 0)%Z /\ (0x10007fff8000 <= U sbeg)%Z.
  Hypothesis Hnf : (0 <= nf <= 2 ^ 27)%Z.
  Hypothesis Rcnt0 : rdn segs mem (at_ thr (208 + 80 * cc)) 4 = Some (LE4 0).

  Theorem amB_miss_head :
    exists r3, msteps segs (mkst regs (at_ rb 0x4c814) mem rom) (mkst r3 (at_ rb 0x5143c) (amh_mem rb regs mem sp) rom)
      /\ getr r3 1 = at_ rb 0x50f9c /\ getr r3 2 = at_ sp (-48) /\ getr r3 10 = at_ thr 208 /\ getr r3 11 = at_ thr (208 + 80 * cc) /\ getr r3 12 = inst
      /\ getr r3 13 = Z_to_bv 64 cc /\ getr r3 8 = Z_to_bv 64 cc /\ getr r3 9 = at_ thr (208 + 80 * cc) /\ getr r3 18 = Z_to_bv 64 8
      /\ getr r3 19 = at_ thr 208 /\ getr r3 20 = inst /\ getr r3 26 = thr
      /\ (forall i : reg, In i [3; 4; 21; 22; 23; 24; 25; 27] -> getr r3 i = getr regs i).
  Proof using Rcnt0 Hnf GSPB G1M GTS sbeg nf Ginst Gthr G1 Hstk GH Hn H22 H19 H4 H2 tctx tsdp tp Ggm gmsk GTRB GTOK gt RB HCBM HCB HAL.
    pose proof G1 as [G1a G1b]. pose proof Gthr as (Gt1 & Gt2 & Gt3). destruct GSPB as (S2 & S3 & S4). destruct Ginst as [Gi1 Gi2].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range thr) as Hthr. pose proof (u64_range inst) as Hir. pose proof (u64_range sbeg).
    pose proof (needed_facts n Hn) as NF. pose proof (AsArith3.class_of_range (needed n) ltac:(lia)) as Hc.
    destruct (ambm_glue segs rb HAL gt GTOK GTRB regs mem rom sp tp tsdp tctx thr inst n H2 H4 H19 H22 Hn GH G1 Gthr sbeg)
      as (r2 & M1 & RUN12 & EM1 & C1 & C2 & C10 & C11 & C12 & C13 & C26 & CK & AGK).
    assert (EM : M1 = amh_M1 rb mem sp) by exact EM1.
    assert (GRM1 : mem_grows mem M1) by (rewrite EM1; apply wbytes_grows).
    destruct (cb_miss_head segs rb HCB HCBM RB r2 M1 rom (at_ rb 0x4c834) sp (at_ thr 208) inst (needed n)
                C1 C2 C10 C11 C12 C13 NF
                ltac:(eapply store_ok_mono; [exact GRM1|]; eapply (store_ok_sub segs mem (at_ sp (-208)) _ 208); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia])
                G1 gmsk Ggm nf sbeg G1M
                ltac:(rewrite at_u by lia; split; [lia | rewrite <- Zplus_mod_idemp_l, Gt3; reflexivity])
                ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) (conj Gi1 Gi2) (conj S2 (conj S3 S4)) Hnf)
      as (r3 & RUN3 & D1 & D2 & D10 & D11 & D12 & D13 & D8 & D9 & D18 & D19 & D20 & AG3).
    { rewrite at_at. rewrite <- Rcnt0. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
      rewrite EM. apply (amh_M1_outside rb mem sp G1). lia. }
    assert (EMEM : cb_m1 r2 M1 (at_ rb 0x4c834) sp = amh_mem rb regs mem sp).
    { (lazymatch goal with |- ?G => let G' := eval unfold amh_mem, cb_m1 in G in change_no_check G' end). rewrite EM. rewrite !(CK _) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20). reflexivity. }
    rewrite EMEM in RUN3. rewrite !at_at in D11, D9.
    exists r3. split; [eapply msteps_trans; [exact RUN12 | exact RUN3]|].
    split; [exact D1|]. split; [exact D2|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|]. split; [exact D13|]. split; [exact D8|].
    split; [exact D9|]. split; [exact D18|]. split; [exact D19|]. split; [exact D20|]. split.
    - rewrite (AG3 26) by notin. exact C26.
    - intros i Hi. rewrite (AG3 i); [apply CK; cbn [In] in Hi |- *; clear - Hi; tauto|].
      cbn [In] in Hi. intros Hx. unfold cbm_clob in Hx. cbn [In] in Hx.
      repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi.
  Qed.
End AMBM.
End FPGen1.
End BoAllocM3p.
Module BoAllocM3q.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7g BoAllocM7r BoAllocM3m.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.
Section CBM2.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HCB : code_ato segs rb 0x50cec cb_words.
  Hypothesis HCBM : code_ato segs rb 0x50f7c cbm_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Let K50ea0 := J50ea0 segs rb HCB.
  Let K50ea4 := J50ea4 segs rb HCB.
  Let K50ea8 := J50ea8 segs rb HCB.
  Let K50eac := J50eac segs rb HCB.
  Let K50eb0 := J50eb0 segs rb HCB.
  Let K50eb4 := J50eb4 segs rb HCB.
  Let K50eb8 := J50eb8 segs rb HCB.
  Let K50ebc := J50ebc segs rb HCB.
  Let K50ec0 := J50ec0 segs rb HCB.
  Let K50ec4 := J50ec4 segs rb HCB.
  Let K50ec8 := J50ec8 segs rb HCB.
  Let K50ecc := J50ecc segs rb HCB.
  Let K50ed0 := J50ed0 segs rb HCB.
  Let K50ed4 := J50ed4 segs rb HCB.
  Let K50ed8 := J50ed8 segs rb HCB.
  Let K50edc := J50edc segs rb HCB.
  Let K50ee0 := J50ee0 segs rb HCB.
  Let K50ef0 := J50ef0 segs rb HCB.
  Let K50ef4 := J50ef4 segs rb HCB.
  Let K50ef8 := J50ef8 segs rb HCB.
  Let K50efc := J50efc segs rb HCB.
  Let K50f00 := J50f00 segs rb HCB.
  Let K50f04 := J50f04 segs rb HCB.
  Let K50f08 := J50f08 segs rb HCB.
  Let K50f0c := J50f0c segs rb HCB.
  Let K50f9c := J50f9c segs rb HCBM.
  Let K50fa0 := J50fa0 segs rb HCBM.
  Let K50fa4 := J50fa4 segs rb HCBM.
  Let K50fa8 := J50fa8 segs rb HCBM.
  Let K50fac := J50fac segs rb HCBM.
  Let K50fb0 := J50fb0 segs rb HCBM.
  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp cache inst : word).
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis G1 : (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  Definition cb_slots2 : list (Z * word) := [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20)]%Z.

  Ltac vz := cbv delta [v_add v_addi v_mul v_slli v_srli v_sub] beta; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; unorm;
             first [reflexivity | f_equal; lia | apply bv_eq; wd_ulia].

  Lemma cbR2 : forall (M : word -> option byte) r0 (c cnt k : Z) (csz stw sbeg res : word),
    getr r0 8 = Z_to_bv 64 c -> getr r0 2 = at_ sp (-48) -> getr r0 9 = at_ cache (80 * c) -> getr r0 18 = Z_to_bv 64 8 ->
    getr r0 19 = cache -> getr r0 20 = inst -> getr r0 10 = res -> U res <> 0%Z ->
    (1 <= c <= 30)%Z -> (1 <= cnt <= 16)%Z -> (0 <= k < 2 ^ 32)%Z ->
    rdn segs M (at_ cache (80 * c)) 4 = Some (LE4 cnt) ->
    rdn segs M (at_ cache (80 * c + 8)) 8 = Some (LE8 csz) ->
    rdn segs M (at_ cache (80 * c + 16 + 4 * (cnt - 1))) 4 = Some (LE4 k) ->
    rdn segs M (at_ cache 2576) 8 = Some (LE8 stw) ->
    store_ok segs M (at_ cache (80 * c)) 4 = true -> store_ok segs M (at_ cache 2576) 8 = true ->
    rdn segs M (at_ inst 32) 8 = Some (LE8 sbeg) ->
    (forall (o : Z) (v : word), In (o, v) cb_slots2 -> rdn segs M (at_ sp o) 8 = Some (LE8 v)) ->
    (U cache mod 8 = 0)%Z -> (U inst + 40 <= U cache \/ U cache + 2584 <= U inst)%Z -> (U cache + 2584 <= U sp - 48)%Z -> (U inst + 40 <= 2 ^ 32)%Z ->
    (U sbeg + 2 ^ 37 < 2 ^ 64)%Z ->
    let M1 := wbytes M (at_ cache (80 * c)) (LE4 (cnt - 1)) in
    let M' := wbytes M1 (at_ cache 2576) (LE8 (v_add stw csz)) in
    exists r, msteps segs (mkst r0 (at_ rb 0x50f9c) M rom) (mkst r ra M' rom)
      /\ getr r 10 = Z_to_bv 64 (U sbeg + c * 2 ^ 32 + 16 * k)
      /\ getr r 13 = Z_to_bv 64 8
      /\ (forall i : reg, In i [1; 2; 8; 9; 18; 19; 20] -> getr r i = getr regs i)
      /\ (forall i : reg, In i [3; 4; 21; 22; 23; 24; 25; 26; 27] -> getr r i = getr r0 i).
  Proof using G1 H2 H1 Hret mem K50fb0 K50fac K50fa8 K50fa4 K50fa0 K50f9c K50f0c K50f08 K50f04 K50f00 K50efc K50ef8 K50ef4 K50ef0 K50ee0 K50edc K50ed8 K50ed4 K50ed0 K50ecc K50ec8 K50ec4 K50ec0 K50ebc K50eb8 K50eb4 K50eb0 K50eac K50ea8 K50ea4 K50ea0 RB HCBM HCB.
    intros M r0 c cnt k csz stw sbeg res R8 R2 R9 R18 R19 R20 R10 NZ Hc Hcnt Hk Rcnt Rcsz Rk Rst SOKc SOKs Rsb FR AL8 Gc Gcs Gi Gsb M1 M'.
    pose proof (u64_range res) as Hres.
    destruct G1 as [G1a G1b]. pose proof (u64_range sp) as Hspr. pose proof (u64_range cache) as Hcr. pose proof (u64_range inst) as Hir.
    pose proof (u64_range sbeg) as Hsbr.
    assert (M1_out : forall x : word, (U x < U cache + 80 * c \/ U cache + 80 * c + 4 <= U x)%Z -> M1 x = M x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (M'_out : forall x : word, (U x < U cache + 80 * c \/ U cache + 80 * c + 4 <= U x)%Z -> (U x < U cache + 2576 \/ U cache + 2584 <= U x)%Z -> M' x = M x).
    { intros x Hx Hy. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). rewrite wbytes_outside; [apply M1_out; exact Hx | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (Rcsz1 : rdn segs M1 (at_ cache (80 * c + 8)) 8 = Some (LE8 csz)).
    { rewrite <- Rcsz. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply M1_out; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (Rk1 : rdn segs M1 (at_ cache (80 * c + 16 + 4 * (cnt - 1))) 4 = Some (LE4 k)).
    { rewrite <- Rk. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply M1_out; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (Rst1 : rdn segs M1 (at_ cache 2576) 8 = Some (LE8 stw)).
    { rewrite <- Rst. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply M1_out; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (SOKs1 : store_ok segs M1 (at_ cache 2576) 8 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). eapply store_ok_mono; [apply wbytes_grows | exact SOKs]. }
    assert (Rsb' : rdn segs M' (at_ inst 32) 8 = Some (LE8 sbeg)).
    { rewrite <- Rsb. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; rewrite at_u in Hx by lia; cbn in Hx; apply M'_out; lia]. }
    assert (FR' : forall (o : Z) (v : word), In (o, v) cb_slots2 -> rdn segs M' (at_ sp o) 8 = Some (LE8 v)).
    { intros o v Hin. rewrite <- (FR o v Hin).
      assert (Ho : (-48 <= o <= -8)%Z). { cbn [In cb_slots2] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
      apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; rewrite at_u in Hx by lia; cbn in Hx; apply M'_out; lia]. }
    wd_eexists. split; [|split; [|split; [|split]]].
    - ab_ft K50f9c D_50f9c ltac:(condz).                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 cnt)) (v := Z_to_bv 64 cnt);
          [exact K50fa0 | reflexivity | exact D_50fa0 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; exact Rcnt | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small cnt) by lia; vn.                 (* [comment removed for export] *)
      an K50fa4 D_50fa4.                                   (* [comment removed for export] *)
      an K50fa8 D_50fa8.                                   (* [comment removed for export] *)
      an K50fac D_50fac.                                   (* [comment removed for export] *)
      an K50fb0 D_50fb0.                                   (* [comment removed for export] *)
      av K50ea0 D_50ea0 (Z_to_bv 64 (cnt - 1)) ltac:(vz). (* [comment removed for export] *)
      an K50ea4 D_50ea4.                                   (* [comment removed for export] *)
      av K50ea8 D_50ea8 (Z_to_bv 64 ((cnt - 1) * 2 ^ 32)) ltac:(vz).   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sw_at with (a := at_ cache (80 * c));
          [exact K50eac | reflexivity | exact D_50eac
          | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; reflexivity
          | gres; rwH; reflexivity
          | exact SOKc ]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M _ _) with M1.
      an K50eb0 D_50eb0.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 csz) (v := csz);
          [exact K50eb4 | reflexivity | exact D_50eb4 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; exact Rcsz1 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      av K50eb8 D_50eb8 (Z_to_bv 64 (4 * (cnt - 1))) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; f_equal;
            replace ((cnt - 1) * 2 ^ 32)%Z with (4 * (cnt - 1) * 2 ^ 30)%Z by lia; apply Z.div_mul; lia).   (* [comment removed for export] *)
      av K50ebc D_50ebc (at_ cache (80 * c + 4 * (cnt - 1))) ltac:(rewrite v_add_at by lia; rewrite at_at; first [reflexivity | f_equal; lia]).  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lwu with (bs := word_to_le_bytes 4 (Z_to_bv 64 k)) (v := Z_to_bv 64 k);
          [exact K50ec0 | reflexivity | exact D_50ec0
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; rewrite <- Rk1; f_equal; f_equal; lia
          | apply bytes4_small; lia]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_amoadd_d with (bs := LE8 stw) (v := stw);
          [exact K50ec4 | reflexivity | exact D_50ec4
          | gres; rwH; rewrite at_u by lia; rewrite <- Zplus_mod_idemp_l, AL8; reflexivity
          | gres; rwH; exact Rst1
          | apply bytes_le_to_Z_8
          | gres; rwH; exact SOKs1 ]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M1 _ _) with M'.
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 sbeg) (v := sbeg);
          [exact K50ec8 | reflexivity | exact D_50ec8 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; exact Rsb' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      av K50ecc D_50ecc (Z_to_bv 64 (c * 2 ^ 32)) ltac:(vz).        (* [comment removed for export] *)
      av K50ed0 D_50ed0 (Z_to_bv 64 (16 * k)) ltac:(vz).            (* [comment removed for export] *)
      av K50ed4 D_50ed4 (Z_to_bv 64 (U sbeg + c * 2 ^ 32)) ltac:(vz).   (* [comment removed for export] *)
      av K50ed8 D_50ed8 (Z_to_bv 64 (U sbeg + c * 2 ^ 32 + 16 * k)) ltac:(vz).   (* [comment removed for export] *)
      an K50edc D_50edc.                                   (* [comment removed for export] *)
      ab_tk K50ee0 D_50ee0 ltac:(condz).                  (* [comment removed for export] *)
      Ltac cldF F D vv H := chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 vv) (v := vv);
          [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_at; zlit_at; apply H; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
      cldF K50ef0 D_50ef0 ra (FR' (-8)%Z).                        (* [comment removed for export] *)
      cldF K50ef4 D_50ef4 (getr regs 8) (FR' (-16)%Z).             (* [comment removed for export] *)
      cldF K50ef8 D_50ef8 (getr regs 9) (FR' (-24)%Z).             (* [comment removed for export] *)
      cldF K50efc D_50efc (getr regs 18) (FR' (-32)%Z).            (* [comment removed for export] *)
      cldF K50f00 D_50f00 (getr regs 19) (FR' (-40)%Z).            (* [comment removed for export] *)
      cldF K50f04 D_50f04 (getr regs 20) (FR' (-48)%Z).            (* [comment removed for export] *)
      an K50f08 D_50f08.                                   (* [comment removed for export] *)
      aret K50f0c D_50f0c ra.                              (* [comment removed for export] *)
      wd_refl.
    - gres. reflexivity.
    - gres. rwH. reflexivity.
    - intros i Hi; cbn [In] in Hi.
      repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_0; first [reflexivity | symmetry; assumption] |]). destruct Hi.
    - intros i Hi; cbn [In] in Hi.
      repeat (destruct Hi as [<-|Hi]; [gres; reflexivity |]). destruct Hi.
  Qed.
End CBM2.
End FPGen1.
End BoAllocM3q.
Module BoAllocM9e.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7g BoAllocM7r BoAllocM3m.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Section AMBS.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HAL : code_ato segs rb 0x4c594 al_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Variable gt : gct_tab.
  Hypothesis GTOK : gct_tab_ok segs gt.
  Hypothesis GTRB : gt_rb gt = rb.
  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (sp tp tsdp tctx thr inst : word) (sz : Z).
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 sz.
  Hypothesis H22 : getr regs 22 = inst.
  Hypothesis GH : gctH segs gt mem sp tp tsdp tctx thr.
  Hypothesis G1 : (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Gthr : (4096 <= U thr /\ (U thr + 4096 <= AIMGLO \/ AIMGHI <= U thr))%Z /\ (U thr + 4096 <= U sp - 208)%Z /\ (U thr mod 8 = 0)%Z.
  Let J67750 := BoAllocM3.J67750 segs rb HAL.
  Let J67754 := BoAllocM3.J67754 segs rb HAL.
  Let J67758 := BoAllocM3.J67758 segs rb HAL.
  Let J6775c := BoAllocM3.J6775c segs rb HAL.
  Let J67760 := BoAllocM3.J67760 segs rb HAL.
  Let J67764 := BoAllocM3.J67764 segs rb HAL.
  Let J67768 := BoAllocM3.J67768 segs rb HAL.
  Let J6776c := BoAllocM3.J6776c segs rb HAL.

  Lemma ambs_glue :
    exists r2 (M1 : word -> option byte),
      msteps segs (mkst regs (at_ rb 0x4c814) mem rom) (mkst r2 (at_ rb 0x50cec) M1 rom)
      /\ M1 = wbytes mem (at_ sp (-8)) (LE8 (at_ rb 0x4c818))
      /\ getr r2 1 = at_ rb 0x4c834 /\ getr r2 2 = sp /\ getr r2 10 = inst /\ getr r2 11 = at_ thr 208
      /\ getr r2 12 = Z_to_bv 64 sz /\ getr r2 13 = Z_to_bv 64 8 /\ getr r2 26 = thr
      /\ (forall i : reg, In i [4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27; 3] -> getr r2 i = getr regs i)
      /\ (forall i : reg, ~ In i [26; 1; 10; 11; 12; 13] -> getr r2 i = getr regs i).
  Proof using J6776c J67768 J67764 J67760 J6775c J67758 J67754 J67750 Gthr G1 GH H22 H19 H4 H2 tctx tsdp tp GTRB GTOK gt HAL.
    pose proof G1 as [G1a G1b]. pose proof Gthr as (Gt1 & Gt2 & Gt3). pose proof (u64_range sp) as Hspr. pose proof (u64_range thr) as Hthr. pose proof (u64_range inst) as Hir.
    (* [comment removed for export] *)
    assert (W0 : exists r0, msteps segs (mkst regs (at_ rb 0x4c814) mem rom) (mkst r0 (at_ rb 0x78e2c) mem rom)
                 /\ getr r0 1 = at_ rb 0x4c818 /\ (forall i : reg, i <> 1 -> getr r0 i = getr regs i)).
    { wd_eexists. split; [an J67750 D_4c814; wd_refl|]. split; [gres; reflexivity|]. intros i Hi. rewrite getr_other by (intros E; apply Hi; exact E). reflexivity. }
    destruct W0 as (r0 & RUN0 & A1 & AK).
    destruct (gct_run segs gt GTOK mem rom r0 (at_ rb 0x4c818) sp tp tsdp tctx thr GH) as (r1 & RUN1 & B10 & B11 & AG1).
    { rewrite <- GTRB. pose proof (gto_rb _ _ GTOK) as [E1 E2]. pose proof (u64_range (gt_rb gt)). apply ret_ok_at; [exact E1 | reflexivity | lia]. }
    { exact A1. } { rewrite AK by (intros E; discriminate E). exact H2. } { rewrite AK by (intros E; discriminate E). exact H4. }
    rewrite GTRB in RUN1.
    set (M1 := wbytes mem (at_ sp (-8)) (LE8 (at_ rb 0x4c818))) in RUN1.
    (* [comment removed for export] *)
    Ltac r1eq AG1 AK r H := rewrite (AG1 r) by notin_list; rewrite (AK r) by (intros E; discriminate E); exact H.
    assert (W2 : exists r2, msteps segs (mkst r1 (at_ rb 0x4c818) M1 rom) (mkst r2 (at_ rb 0x50cec) M1 rom)
                 /\ getr r2 1 = at_ rb 0x4c834 /\ getr r2 2 = sp /\ getr r2 10 = inst /\ getr r2 11 = at_ thr 208
                 /\ getr r2 12 = Z_to_bv 64 sz /\ getr r2 13 = Z_to_bv 64 8 /\ getr r2 26 = thr
                 /\ (forall i : reg, In i [4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27; 3] -> getr r2 i = getr regs i)
                 /\ regs_agree (fun r => In r [26; 1; 10; 11; 12; 13]) r1 r2).
    { wd_eexists. split.
      - an J67754 D_4c818.                                   (* [comment removed for export] *)
        ab_ft J67758 D_4c81c ltac:(condz).                  (* [comment removed for export] *)
        an J6775c D_4c820.                                   (* [comment removed for export] *)
        an J67760 D_4c824.                                   (* [comment removed for export] *)
        an J67764 D_4c828.                                   (* [comment removed for export] *)
        an J67768 D_4c82c.                                   (* [comment removed for export] *)
        an J6776c D_4c830.                                   (* [comment removed for export] *)
        wd_refl.
      - post; rewrite ?B10, ?at_0; try reflexivity.
        + r1eq AG1 AK (2:reg) H2.
        + r1eq AG1 AK (22:reg) H22.
        + r1eq AG1 AK (19:reg) H19.
        + intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; rewrite (AG1 _) by notin_list; apply AK; intros E; discriminate E|]); destruct Hi.
        + ra_solve. }
    destruct W2 as (r2 & RUN2 & C1 & C2 & C10 & C11 & C12 & C13 & C26 & CK & AG2).
    exists r2, M1. split; [eapply msteps_trans; [exact RUN0|]; eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    split; [reflexivity|]. split; [exact C1|]. split; [exact C2|]. split; [exact C10|]. split; [exact C11|]. split; [exact C12|]. split; [exact C13|]. split; [exact C26|].
    split; [exact CK|].
    intros i Hni. rewrite (AG2 i Hni). rewrite (AG1 i); [apply AK; intros ->; apply Hni; solve [in_list]|].
    intros Hx. cbn [gct_clob In] in Hx. repeat (destruct Hx as [<-|Hx]; [apply Hni; solve [in_list]|]). destruct Hx.
  Qed.

End AMBS.
End FPGen1.
End BoAllocM9e.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMIm.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7g BoAllocM3m OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section FPGen.
Context {fx : FPState}.

Lemma both_HCBM : code_ato BSEGS ARB 0x50f7c cbm_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold cbm_words in G in change_no_check G' end). code_ato_vm. Qed.
Lemma both_HRF : code_ato BSEGS ARB 0x5143c rf_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold rf_words in G in change_no_check G' end). code_ato_vm. Qed.
Lemma both_HGF : code_ato BSEGS ARB 0x5153c gf_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold gf_words in G in change_no_check G' end). code_ato_vm. Qed.
Lemma both_GMSK : gauipc_ld BSEGS ARB 0x516e4 0x516f4 14 14 0x10468.
Proof using. gauipc_ld_tac F_516e4 D_516e4 F_516f4 D_516f4. Qed.

(* [comment removed for export] *)
Lemma rdn_rom_total : forall (M : word -> option byte) (a : word) (n : nat),
  (bv_unsigned a + Z.of_nat n < 2 ^ 64)%Z ->
  (forall i : Z, (bv_unsigned a <= i < bv_unsigned a + Z.of_nat n)%Z -> seg_rom BSEGS (Z_to_bv 64 i) <> None) ->
  exists bs, rdn BSEGS M a n = Some bs /\ length bs = n.
Proof using.
  intros M a n; revert a; induction n as [|n IH]; intros a Hn ROM.
  - exists []%list. split; reflexivity.
  - pose proof (u64_range a) as Ha. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end).
    assert (B : exists b, match M a with Some b => Some b | None => seg_rom BSEGS a end = Some b).
    { destruct (M a) as [b|]; [exists b; reflexivity|].
      destruct (seg_rom BSEGS a) as [b|] eqn:E; [exists b; reflexivity|]. exfalso. apply (ROM (bv_unsigned a) ltac:(lia)). rewrite Z_to_bv_bv_unsigned. exact E. }
    destruct B as [b Eb]. rewrite Eb.
    destruct (IH (a + 1)%bv) as (bs & R & L).
    + rewrite u_add1 by lia. lia.
    + intros i Hi. apply ROM. rewrite u_add1 in Hi by lia. lia.
    + rewrite R. exists (b :: bs)%list. split; [reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
Qed.

Lemma rom_10468 : forall i : Z, (0x10468 <= i < 0x10468 + 8)%Z -> seg_rom BSEGS (Z_to_bv 64 i) <> None.
Proof using.
  intros i Hi.
  assert (C : (i = 0x10468 \/ i = 0x10469 \/ i = 0x1046a \/ i = 0x1046b \/ i = 0x1046c \/ i = 0x1046d \/ i = 0x1046e \/ i = 0x1046f)%Z) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; discriminate.
Qed.

Lemma both_mask_rdn : forall M : word -> option byte, exists msk : word, rdn BSEGS M (Z_to_bv 64 0x10468) 8 = Some (word_to_le_bytes 8 msk).
Proof using.
  intros M. destruct (rdn_rom_total M (Z_to_bv 64 0x10468) 8 ltac:(wd_ulia_c) ltac:(unorm; exact rom_10468)) as (bs & R & L).
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite R. rewrite (word_to_le_bytes_of_bytes8 bs L). reflexivity.
Qed.
End FPGen.
End BoAllocMIm.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMRunP.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7g BoAllocM3m BoAllocM3n BoAllocM3p BoAllocM3q BoAllocMIm OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.BoAllocMTag.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Ltac wm_parts H :=
  let T := type of H in
  lazymatch T with
  | ?A /\ ?B => let H1 := fresh "wmp" in let H2 := fresh "wmp" in
                pose proof (proj1 H) as H1; pose proof (proj2 H) as H2; wm_parts H1; wm_parts H2;
                (lazymatch A with context [or] => clear H1 | _ => idtac end);
                (lazymatch B with context [or] => lazymatch B with _ /\ _ => clear H2 | _ => idtac end | _ => idtac end)
  | _ => idtac
  end.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Lemma at0_lit : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof using. intros c Hc. apply bv_eq. rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]). rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma ARB_lit : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ ARB c = Z_to_bv 64 c.
Proof using. intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold ARB in G in change_no_check G' end). apply at0_lit. exact Hc. Qed.

(* [comment removed for export] *)
Ltac notin' := try (lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); try (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); notin.
Ltac rch := repeat (first [ reflexivity | assumption
                          | match goal with |- getr ?r ?i = _ => match goal with H : getr r i = _ |- _ => rewrite H end end
                          | match goal with |- getr ?r ?i = _ => match goal with AG : regs_agree _ _ r |- _ => rewrite (AG i) by notin' end end ]).

(* [comment removed for export] *)
Lemma rdn1_off : forall (m : mem) (a : word) b,
  (bv_unsigned a + 1 <= 0x10000 \/ 0x663000 <= bv_unsigned a)%Z -> rdn BSEGS m a 1 = Some [b] -> m a = Some b.
Proof using.
  intros m a b Ha R. cbn [rdn] in R. destruct (m a) as [b'|] eqn:E.
  - cbn in R. congruence.
  - unfold seg_rom, memory_read in R. change (Z.of_N 1) with 1%Z in R.
    rewrite (find_segment1_none_outside BSEGS 0x10000 0x663000 (bv_unsigned a) asanF_segs_in_hull) in R; [discriminate R|].
    destruct Ha as [Ha|Ha]; [left | right]; lia.
Qed.

Section RUNP.
  Variables (mem rom : word -> option byte) (R : bvmap 5 word).
  Variables (S ra0 tp tsdp P top bot : word) (T tctx n SPB nf : Z) (D : nat).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  #[local] Abbreviation c := (class_of (needed n)).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HR1 : getr R 1 = ra0.
  Hypothesis HR2 : getr R 2 = S.
  Hypothesis HR4 : getr R 4 = tp.
  Hypothesis HR10 : getr R 10 = Z_to_bv 64 n.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gn : (1 <= n <= 64512)%Z.
  (* [comment removed for export] *)
  Hypothesis GT : ((4096 <= T /\ (T + 4096 <= AIMGLO \/ AIMGHI <= T)) /\ T + 4096 <= U S - 3584 /\ T mod 8 = 0)%Z.
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584 /\ (tctx + 4096 <= T \/ T + 4096 <= tctx))%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  Hypothesis GP : (AIMGLO <= U P /\ U P + 8 <= AIMGHI)%Z.
  Hypothesis Gtop : (4096 <= U top <= 2 ^ 47)%Z.
  Hypothesis Gbot : (U bot < U top)%Z.
  Hypothesis GSPB : (0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis GSPB2 : (SPB + 2 ^ 37 + 4096 < 2 ^ 47)%Z /\ (SPB mod 2 ^ 16 = 0)%Z /\ (0x10007fff8000 <= SPB)%Z.
  Hypothesis GTS : (T + 4096 <= SPB \/ SPB + 2 ^ 37 + 4096 <= T)%Z.
  Hypothesis GctxR : (tctx + 4096 <= SPB + 2 ^ 37 \/ SPB + 2 ^ 37 + 4096 <= tctx)%Z.
  Hypothesis G1M : (SPB + 2 ^ 37 + 4096 + 208 <= U S - 2272)%Z.
  Hypothesis Hnf : (0 <= nf <= 2 ^ 27)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-3584)) 3584 = true.
  (* [comment removed for export] *)
  Hypothesis C_mcs : rdn BSEGS mem (Z_to_bv 64 0x10eebc) 4 = Some (LE4 30).
  Hypothesis C_gcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8)).
  Hypothesis C_fum : rdn BSEGS mem (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_inited : rdn BSEGS mem (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_pg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 P).
  Hypothesis C_P : rdn BSEGS mem P 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_kif : rdn BSEGS mem (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn BSEGS mem (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn BSEGS mem (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn BSEGS mem tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn BSEGS mem (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_rss : rdn BSEGS mem (Z_to_bv 64 0x190422) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_lmag : rdn BSEGS mem (Z_to_bv 64 0x10488) 8 = Some (LE8 MAGICw).
  Hypothesis C_tbl2 : rdn BSEGS mem (at_ (Z_to_bv 64 0x104f8) 4) 1 = Some [Z_to_bv 8 3].
  Hypothesis C_t16 : rdn BSEGS mem (at_ (Z_to_bv 64 0x105f8) 8) 1 = Some [Z_to_bv 8 4].
  Hypothesis C_t2048 : rdn BSEGS mem (at_ (Z_to_bv 64 0x105f8) 49) 1 = Some [Z_to_bv 8 11].
  Hypothesis C_minrz : rdn BSEGS mem (at_ (Z_to_bv 64 0x10ab58) 3624) 2 = Some (LE2 16).
  Hypothesis C_maxrz : rdn BSEGS mem (at_ (Z_to_bv 64 0x10ab58) 3626) 2 = Some (LE2 2048).
  Hypothesis C_maxsz : rdn BSEGS mem (at_ (Z_to_bv 64 0x10ab58) 3616) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 40))).
  Hypothesis C_sbeg : rdn BSEGS mem (at_ (Z_to_bv 64 0x10ab58) 32) 8 = Some (LE8 (Z_to_bv 64 SPB)).
  (* [comment removed for export] *)
  Hypothesis C_Tw : store_ok BSEGS mem thr 4096 = true.
  Hypothesis C_unw : rdn BSEGS mem (at_ thr 3168) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_sw : rdn BSEGS mem (at_ thr 40) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_top : rdn BSEGS mem (at_ thr 8) 8 = Some (LE8 top).
  Hypothesis C_bot : rdn BSEGS mem (at_ thr 16) 8 = Some (LE8 bot).
  Hypothesis C_T0 : rdn BSEGS mem thr 8 = Some (LE8 ctxw).
  Hypothesis C_tid : rdn BSEGS mem (at_ ctxw 8) 4 = Some (LE4 0).
  Hypothesis C_cnt0 : rdn BSEGS mem (at_ thr (208 + 80 * c)) 4 = Some (LE4 0).          (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Abbreviation RIz := (SPB + 2 ^ 37 + 128 * class_of (needed n))%Z.
  #[local] Abbreviation RI := (Z_to_bv 64 (SPB + 2 ^ 37 + 128 * class_of (needed n))).
  #[local] Abbreviation FABz := (SPB + class_of (needed n) * 2 ^ 32 + 3758096384)%Z.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Hfpc : fpc mem (U (getr R 8)) (U S) D.


  Lemma nfacts : (24 <= needed n <= 65536)%Z /\ (needed n mod 8 = 0)%Z /\ (16 <= rz n <= 1024)%Z /\ (needed n = rounded n + rz n)%Z
             /\ (Z.max n 8 <= rounded n <= Z.max n 8 + 7)%Z /\ (1 <= c <= 30)%Z.
  Proof using GSPB Gn GS SPB S.
    pose proof (needed_facts n Gn) as [N1 N2]. pose proof (rz_log_range n) as RL.
    assert (Hrz : (16 <= rz n <= 1024)%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold rz in G in change_no_check G' end). destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E; lia. }
    split; [lia|]. split; [exact N2|]. split; [exact Hrz|]. split; [reflexivity|]. split.
    - (lazymatch goal with |- ?G => let G' := eval unfold rounded, RoundUp in G in change_no_check G' end). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia.
    - apply AsArith3.class_of_range. lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem run_mA_pre :
    exists (r2 r3 : bvmap 5 word) (MP : word -> option byte) (s : Z) (bsz : list byte) (x18 x19 : word),
      let MA := ma_A MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) in
      msteps BSEGS (mkst R (Z_to_bv 64 0x6ef3c) mem rom) (mkst r3 (Z_to_bv 64 0x5143c) (amh_mem ARB r2 MA (at_ S (-2272))) rom)
      (* [comment removed for export] *)
      /\ getr r3 1 = Z_to_bv 64 0x50f9c /\ getr r3 2 = at_ S (-2320) /\ getr r3 10 = at_ thr 208 /\ getr r3 11 = at_ thr (208 + 80 * c)
      /\ getr r3 12 = Z_to_bv 64 0x10ab58 /\ getr r3 13 = Z_to_bv 64 c /\ getr r3 8 = Z_to_bv 64 c /\ getr r3 9 = at_ thr (208 + 80 * c)
      /\ getr r3 18 = Z_to_bv 64 8 /\ getr r3 19 = at_ thr 208 /\ getr r3 20 = Z_to_bv 64 0x10ab58 /\ getr r3 26 = thr
      /\ (forall i : reg, In i [3; 4; 21; 22; 23; 24; 25; 27] -> getr r3 i = getr r2 i)
      (* [comment removed for export] *)
      /\ getr r2 2 = at_ S (-2272) /\ getr r2 3 = getr R 3 /\ getr r2 4 = tp /\ getr r2 8 = Z_to_bv 64 1 /\ getr r2 9 = Z_to_bv 64 n
      /\ getr r2 18 = Z_to_bv 64 8 /\ getr r2 19 = Z_to_bv 64 (needed n) /\ getr r2 20 = Z_to_bv 64 (rz n) /\ getr r2 21 = Z_to_bv 64 n
      /\ getr r2 22 = Z_to_bv 64 0x10ab58 /\ getr r2 23 = at_ S (-2128) /\ getr r2 24 = Z_to_bv 64 18446744073709551608
      /\ getr r2 25 = Z_to_bv 64 7 /\ getr r2 27 = Z_to_bv 64 1
      (* [comment removed for export] *)
      /\ (1 <= s <= 30 /\ bytes_le_to_Z bsz = s)%Z /\ (s <= 2 + Z.of_nat D)%Z
      /\ (forall x : word, MP x <> mem x -> (U S - 2272 <= U x < U S)%Z)
      /\ mem_grows mem MP
      /\ rdn BSEGS MP (at_ S (-2120)) 4 = Some (LE4 s) /\ rdn BSEGS MP (at_ S (-2120)) 8 = Some bsz /\ length bsz = 8%nat
      /\ rdn BSEGS MP (at_ S (-2128)) 8 = Some (LE8 (at_ S (-2112)))
      /\ (forall (kk : Z) (v : word),
            In (kk, v) [(-8, ra0); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
            rdn BSEGS MP (at_ S kk) 8 = Some (LE8 v)).
  Proof using Hfpc C_cnt0 C_bot C_top C_sw C_unw C_Tw C_maxsz C_maxrz C_minrz C_t2048 C_t16 C_tbl2 C_lmag C_rss C_thr C_tctx C_tsdp C_key C_kif C_P C_pg C_inited C_fum C_gcf C_mcs Hstk Hnf G1M GTS GSPB2 GSPB Gbot Gtop GP Gtsdp Gtp Gctx GT Gn GS HR10 HR4 HR2 HR1 nf SPB tctx bot top P tsdp.
    wm_parts GT. wm_parts Gctx.
    pose proof (u64_range S) as HSr. pose proof (u64_range tp) as Htpr. pose proof (u64_range tsdp) as Htsr. pose proof (u64_range P) as HPr.
    destruct GS as (GS1 & GS2 & GS3). destruct GT as (GT1 & GT2 & GT3). destruct Gctx as (Gc1 & Gc2 & Gc3). destruct Gtp as (Gtp1 & Gtp2).
    pose proof nfacts as (NF1 & NF2 & NF3 & NF4 & NF5 & NF6).
    assert (Uthr : U thr = T) by (unorm; reflexivity).
    assert (Uctx : U ctxw = tctx) by (unorm; reflexivity).
    (* [comment removed for export] *)
    assert (MH : mpH BSEGS both_mp_tab mem S (Z_to_bv 64 0x19fce8) thr (Z_to_bv 8 1)).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [mt_rb mt_ui mt_g_cf mt_a_inited mt_g_mcs both_mp_tab] in G in change_no_check G' end).
      - exact C_inited.
      - exact C_gcf.
      - replace (at_ (Z_to_bv 64 0x19fce8) 34) with (Z_to_bv 64 0x19fd0a : word) by (apply bv_eq; reflexivity). exact C_fum.
      - vm_compute. discriminate.
      - exact C_mcs.
      - eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
      - lia.
      - rewrite Uthr. lia. }
    assert (UH : uiH BSEGS both_ui_tab mem (at_ S (-2128)) (at_ S (-2128)) S thr P).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_g_inited ut_g_pgsz ut_img_lo ut_img_hi both_ui_tab] in G in change_no_check G' end).
      - exact C_inited.
      - exact C_unw.
      - eapply (store_ok_sub BSEGS mem thr _ 4096); [rewrite Uthr; lia | exact C_Tw | rewrite at_u, Uthr; lia | rewrite at_u, Uthr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - exact C_pg.
      - exact C_P.
      - rewrite !at_at. eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - rewrite !at_at. eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    assert (GH : gctH BSEGS (ut_gct both_ui_tab) mem (at_ S (-2208)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_gct both_ui_tab gt_tsd both_gct_tab] in G in change_no_check G' end).
      - exact C_kif. - exact C_key. - exact C_tsdp. - exact C_tctx. - exact C_thr.
      - unorm. lia.
      - rewrite !at_at. eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    assert (SH : stkH BSEGS mem thr top bot).
    { split; [exact C_sw | exact C_top | exact C_bot | exact Gbot | wd_ulia]. }
    destruct (mp_run BSEGS both_mp_tab both_mp_tab_ok R mem rom ra0 S tp (Z_to_bv 64 n) (Z_to_bv 64 0x19fce8) thr top bot tsdp ctxw P (Z_to_bv 8 1)
                HR1 HR2 HR4 HR10 MH UH GH SH Gtop D Hfpc)
      as (r1 & MP & s & RUN1 & A1 & A2 & A4 & A10 & A11 & A8 & A9 & A20 & A21 & AG1 & Hs1 & Hs2 & Psz & Ptag & Ptr & Ppc0 & Pslots & Punw & Pfoot & Pgrows).
    cbn [mt_rb both_mp_tab] in RUN1, A1.
    rewrite (ARB_lit 454460) in RUN1 by lia. rewrite (ARB_lit 312632) in RUN1 by lia.
    (* [comment removed for export] *)
    assert (QP : forall x : word, (U x < U S - 2272 \/ U S <= U x)%Z -> MP x = mem x).
    { intros x Hx. destruct (decide (MP x = mem x)) as [E|NE]; [exact E|]. exfalso.
      destruct (Pfoot x NE) as [F|F]; [lia|].
      apply NE. replace x with (at_ thr 3168) by (apply bv_eq; rewrite at_u by (rewrite Uthr; lia); rewrite Uthr; lia).
      rewrite (rdn1_off MP (at_ thr 3168) (Z_to_bv 8 0)); [| rewrite at_u, Uthr by (rewrite Uthr; lia); lia | exact Punw].
      rewrite (rdn1_off mem (at_ thr 3168) (Z_to_bv 8 0)); [reflexivity | rewrite at_u, Uthr by (rewrite Uthr; lia); lia | exact C_unw]. }
    (* [comment removed for export] *)
    Ltac xq Q H :=
      eapply rd_same; [ intros x Hx; apply Q; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
    destruct (amA_run BSEGS both_am_tab both_am_tab_ok r1 MP rom (at_ ARB 0x6f070) (at_ S (-2128)) (at_ S (-2128)) n A1 A2 A10 A11 Gn)
      as (r2 & RUN2 & B2 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & AG2).
    all: (lazymatch goal with |- ?G => let G' := eval cbn [am_rb am_inst am_g_magic am_tbl2 am_tbl am_g_inited am_g_rss both_am_tab] in G in change_no_check G' end).
    { xq QP C_inited. } { xq QP C_rss. } { xq QP C_lmag. } { xq QP C_tbl2. } { xq QP C_t16. } { xq QP C_t2048. }
    { xq QP C_minrz. } { xq QP C_maxrz. } { xq QP C_maxsz. }
    { rewrite at_at. eapply store_ok_mono; [exact Pgrows|].
      eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { unorm. rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    { rewrite at_u by lia. lia. }
    cbn [am_rb am_inst am_g_magic am_tbl2 am_tbl am_g_inited am_g_rss both_am_tab] in RUN2, B22, B26.
    rewrite (ARB_lit 312632) in RUN2 by lia. rewrite (ARB_lit 313364) in RUN2 by lia.
    rewrite (ma_A_eq MP S n r1 A8 A9 A20 A21) in RUN2.
    (* [comment removed for export] *)
    Ltac r1R AG1 k := rewrite (AG1 k) by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    rewrite (AG1 22%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin). rewrite (AG1 23%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    rewrite (AG1 24%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin). rewrite (AG1 25%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    rewrite (AG1 26%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin). rewrite (AG1 27%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    set (MA := ma_A MP S n (getr r1 18) (getr r1 19) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) in RUN2.
    assert (QA : forall x : word, (U x < U S - 2280 \/ U S <= U x)%Z -> MA x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end). rewrite ma_A_outside; [apply QP; lia | lia | lia]. }
    assert (GRA : mem_grows mem MA) by (eapply mem_grows_trans; [exact Pgrows | (lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end); apply ma_A_grows]).
    rewrite at_at in B2. cbn [Z.add Z.opp Pos.add] in B2.
    (* [comment removed for export] *)
    destruct GSPB2 as (S2 & S3 & S4).
    assert (B4 : getr r2 4 = tp) by (rewrite (AG2 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); notin); rewrite (AG1 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin); exact HR4).
    assert (B3 : getr r2 3 = getr R 3) by (rewrite (AG2 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); notin); rewrite (AG1 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin); reflexivity).
    assert (GH2 : gctH BSEGS both_gct_tab MA (at_ S (-2272)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end).
      - xq QA C_kif. - xq QA C_key. - xq QA C_tsdp. - xq QA C_tctx. - xq QA C_thr.
      - unorm. lia.
      - rewrite at_at. eapply store_ok_mono; [exact GRA|].
        eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    Ltac sokA GRA Hstk := rewrite ?at_at; eapply store_ok_mono; [exact GRA|];
      first [ eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia] ].
    destruct (amB_miss_head BSEGS ARB both_HAL both_HCB both_HCBM ARB_ok both_gct_tab both_gct_tab_ok both_GTRB 0x10468
                ltac:(lia) r2 MA rom (at_ S (-2272)) tp tsdp ctxw thr (Z_to_bv 64 0x10ab58) n B2 B4 B19 B22 Gn GH2
                ltac:(sokA GRA Hstk) ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(rewrite Uthr, at_u by lia; lia) ltac:(wd_ulia)
                nf (Z_to_bv 64 SPB)
                ltac:(rewrite Uthr; wd_ulia) ltac:(unorm; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(wd_ulia) Hnf)
      as (r3 & RUN3 & C1 & C2 & C10 & C11 & C12 & C13 & C8 & C9 & C18 & C19 & C20 & C26 & CK).
    { xq QA C_cnt0. }
    rewrite (ARB_lit 313364) in RUN3 by lia. rewrite (ARB_lit 332860) in RUN3 by lia.
    rewrite (ARB_lit 331676) in C1 by lia. rewrite at_at in C2. cbn [Z.add Z.opp Pos.add] in C2.
    exists r2, r3, MP, s.
    destruct (rdn_defined_ex BSEGS MP (at_ S (-2120)) 8) as [bsz [Rsz Lsz]].
    { intros i Hi. rewrite at_u in Hi by lia. apply Pgrows. apply (store_ok1_heap mem); [wd_ulia|].
      eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584 1); [rewrite at_u; lia | exact Hstk | rewrite at_u by lia; wd_ulia | rewrite at_u by lia; wd_ulia_c]. }
    { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    assert (HBSZ : bytes_le_to_Z bsz = s) by (apply (bsz_val BSEGS MP (at_ S (-2120)) bsz s Rsz Psz); [rewrite at_at; exact Ptag | lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]).
    exists bsz, (getr r1 18), (getr r1 19). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold MA.
    split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2 | exact RUN3]|].
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    - intros x NE. destruct (Pfoot x NE) as [F|F]; [exact F|]. exfalso. apply NE. apply QP. rewrite Uthr in F. lia.
  Qed.
End RUNP.
End FPGen.
End BoAllocMRunP.
Module BoAllocMRunS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7g BoAllocM3m BoAllocM3n BoAllocM3p BoAllocM3q BoAllocMIm OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Ltac wm_parts H :=
  let T := type of H in
  lazymatch T with
  | ?A /\ ?B => let H1 := fresh "wmp" in let H2 := fresh "wmp" in
                pose proof (proj1 H) as H1; pose proof (proj2 H) as H2; wm_parts H1; wm_parts H2;
                (lazymatch A with context [or] => clear H1 | _ => idtac end);
                (lazymatch B with context [or] => lazymatch B with _ /\ _ => clear H2 | _ => idtac end | _ => idtac end)
  | _ => idtac
  end.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Lemma at0_lit : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof using. intros c Hc. apply bv_eq. rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]). rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma ARB_lit : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ ARB c = Z_to_bv 64 c.
Proof using. intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold ARB in G in change_no_check G' end). apply at0_lit. exact Hc. Qed.

(* [comment removed for export] *)
Ltac notin' := try (lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); try (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); notin.
Ltac rch := repeat (first [ reflexivity | assumption
                          | match goal with |- getr ?r ?i = _ => match goal with H : getr r i = _ |- _ => rewrite H end end
                          | match goal with |- getr ?r ?i = _ => match goal with AG : regs_agree _ _ r |- _ => rewrite (AG i) by notin' end end ]).



Section RUNS.
  Variables (M4 rom : word -> option byte) (r0 rC : bvmap 5 word).
  Variables (S thr ctxw sbeg csz stw tr szw : word) (n cnt k tid : Z) (b1 : byte) (bsz : list byte).
  #[local] Abbreviation c := (class_of (needed n)).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation cache := (at_ thr 208).
  #[local] Abbreviation inst := (Z_to_bv 64 0x10ab58 : word).
  Definition ms_ab : Z := (U sbeg + c * 2 ^ 32 + 16 * k)%Z.
  #[local] Abbreviation m := (Z_to_bv 64 ms_ab).
  Definition ms_MB : word -> option byte := wbytes (wbytes M4 (at_ thr (208 + 80 * c)) (LE4 (cnt - 1))) (at_ thr 2784) (LE8 (v_add stw csz)).
  (* [comment removed for export] *)
  Hypothesis HC1 : getr rC 1 = at_ ARB 0x4c834.
  Hypothesis HC2 : getr rC 2 = sp2.
  Hypothesis HC9 : getr rC 9 = Z_to_bv 64 n.
  Hypothesis HC19 : getr rC 19 = Z_to_bv 64 (needed n).
  Hypothesis HC20 : getr rC 20 = Z_to_bv 64 (rz n).
  Hypothesis R8 : getr r0 8 = Z_to_bv 64 c.
  Hypothesis R2 : getr r0 2 = at_ sp2 (-48).
  Hypothesis R9 : getr r0 9 = at_ cache (80 * c).
  Hypothesis R18 : getr r0 18 = Z_to_bv 64 8.
  Hypothesis R19 : getr r0 19 = cache.
  Hypothesis R20 : getr r0 20 = inst.
  Hypothesis R10 : getr r0 10 = Z_to_bv 64 1.
  Hypothesis R21 : getr r0 21 = Z_to_bv 64 n.
  Hypothesis R23 : getr r0 23 = at_ S (-2128).
  Hypothesis R25 : getr r0 25 = Z_to_bv 64 7.
  Hypothesis R26 : getr r0 26 = thr.
  Hypothesis R27 : getr r0 27 = Z_to_bv 64 1.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z.
  Hypothesis Gn : (1 <= n <= 64512)%Z.
  Hypothesis Gcnt : (1 <= cnt <= 16)%Z.
  Hypothesis Gk : (0 <= k < 2 ^ 32)%Z.
  Hypothesis Gtid : (0 <= tid < 2 ^ 31)%Z.
  Hypothesis GT : ((4096 <= U thr /\ hideW (U thr + 4096 <= AIMGLO \/ AIMGHI <= U thr)) /\ U thr + 4096 <= U S - 3584 /\ U thr mod 8 = 0)%Z.
  Hypothesis Gctx : (1 <= U ctxw /\ U ctxw + 4096 <= U S - 3584 /\ (U ctxw + 4096 <= U thr \/ U thr + 4096 <= U ctxw))%Z.
  Hypothesis Gsb : (U sbeg + 2 ^ 37 < 2 ^ 64)%Z.
  Hypothesis Gab : (ms_ab mod 16 = 0 /\ 0x10007fff8000 <= ms_ab /\ ms_ab + needed n <= U S - 3584 /\ ms_ab + 2 ^ 17 <= 2 ^ 47)%Z.
  Hypothesis GabT : (ms_ab + needed n <= U thr \/ U thr + 4096 <= ms_ab)%Z.
  Hypothesis Gabctx : (ms_ab + needed n <= U ctxw \/ U ctxw + 4096 <= ms_ab)%Z.
  (* [comment removed for export] *)
  Hypothesis Rcnt : rdn BSEGS M4 (at_ cache (80 * c)) 4 = Some (LE4 cnt).
  Hypothesis Rcsz : rdn BSEGS M4 (at_ cache (80 * c + 8)) 8 = Some (LE8 csz).
  Hypothesis Rk : rdn BSEGS M4 (at_ cache (80 * c + 16 + 4 * (cnt - 1))) 4 = Some (LE4 k).
  Hypothesis Rst : rdn BSEGS M4 (at_ cache 2576) 8 = Some (LE8 stw).
  Hypothesis SOKT : store_ok BSEGS M4 thr 4096 = true.
  Hypothesis Rsb : rdn BSEGS M4 (at_ inst 32) 8 = Some (LE8 sbeg).
  Hypothesis FR : forall (o : Z) (v : word), In (o, v) (cb_slots2 rC (at_ ARB 0x4c834)) -> rdn BSEGS M4 (at_ sp2 o) 8 = Some (LE8 v).
  Hypothesis Rb1 : rdn BSEGS M4 (at_ m (rz n - 15)) 1 = Some [b1].
  Hypothesis SOKh : store_ok BSEGS M4 (at_ m (rz n - 16)) 16 = true.
  Hypothesis R16 : rdn BSEGS M4 (at_ sp2 16) 8 = Some (LE8 (Z_to_bv 64 16)).
  Hypothesis RT0 : rdn BSEGS M4 thr 8 = Some (LE8 ctxw).
  Hypothesis Rtid : rdn BSEGS M4 (at_ ctxw 8) 4 = Some (LE4 tid).
  Hypothesis Rtr : rdn BSEGS M4 (at_ S (-2128)) 8 = Some (LE8 tr).
  Hypothesis Rsz : rdn BSEGS M4 (at_ (at_ S (-2128)) 8) 8 = Some bsz.
  Hypothesis Hsz : lez bsz = U szw /\ length bsz = 8%nat.

  Lemma ms_MB_outside : forall x : word, (U x < U thr + 208 + 80 * c \/ U thr + 208 + 80 * c + 4 <= U x)%Z ->
    (U x < U thr + 2784 \/ U thr + 2792 <= U x)%Z -> ms_MB x = M4 x.
  Proof using Hsz Gab GT Gn GS bsz k szw sbeg S.
    intros x X1 X2. destruct GT as ((T1 & _) & T2 & _). destruct GS as [S1 S2]. pose proof (u64_range thr). pose proof (AsArith3.class_of_range (needed n) ltac:(pose proof (needed_facts n Gn); lia)) as Hc.
    (lazymatch goal with |- ?G => let G' := eval unfold ms_MB in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_at, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma ms_MB_grows : mem_grows M4 ms_MB.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold ms_MB in G in change_no_check G' end). eapply mem_grows_trans; apply wbytes_grows. Qed.

  Theorem run_mA_suf :
    exists r : bvmap 5 word,
      msteps BSEGS (mkst r0 (Z_to_bv 64 0x50f9c) M4 rom) (mkst r (Z_to_bv 64 0x8f4f0) (amC_mem ms_MB m b1 n) rom)
      /\ getr r 1 = Z_to_bv 64 0x4c940 /\ getr r 2 = sp2 /\ getr r 10 = tr /\ getr r 11 = szw
      /\ getr r 8 = getr rC 8 /\ getr r 9 = Z_to_bv 64 n /\ getr r 18 = m /\ getr r 19 = Z_to_bv 64 (needed n)
      /\ getr r 20 = at_ m (rz n) /\ getr r 21 = at_ m (rz n - 16) /\ getr r 24 = Z_to_bv 64 (tid * 2 ^ 32) /\ getr r 25 = at_ m (rz n + n)
      /\ (forall i : reg, In i [3; 4; 22; 23; 26; 27] -> getr r i = getr r0 i).
  Proof using Hsz Rsz Rtr Rtid RT0 R16 SOKh Rb1 FR Rsb SOKT Rst Rk Rcsz Rcnt Gabctx GabT Gab Gsb Gctx GT Gtid Gk Gcnt Gn GS R27 R26 R25 R23 R21 R10 R20 R19 R18 R9 R2 R8 HC20 HC19 HC9 HC2 HC1 bsz ctxw.
    destruct GS as [S1 S2]. destruct GT as ((T1 & T1b) & T2 & T3). destruct Gctx as (C1 & C2 & C3). destruct Gab as (A1 & A2 & A3 & A4).
    pose proof (u64_range S) as HSr. pose proof (u64_range thr) as Hthr. pose proof (u64_range ctxw) as Hcr. pose proof (u64_range sbeg) as Hsr.
    pose proof (needed_facts n Gn) as [NF1 NF2].
    pose proof (AsArith3.class_of_range (needed n) ltac:(lia)) as Hc.
    assert (Um : U m = ms_ab) by (unorm; reflexivity).
    assert (Hrz : (16 <= rz n <= 1024)%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold rz in G in change_no_check G' end). pose proof (rz_log_range n). destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E; lia. }
    assert (Hnd : (needed n = rounded n + rz n)%Z) by reflexivity.
    assert (Hrd2 : (8 <= rounded n)%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold rounded, RoundUp in G in change_no_check G' end). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia. }
    assert (RETC : ret_ok (at_ ARB 0x4c834)) by (rewrite (ARB_lit 0x4c834) by lia; apply ret_ok_lit; [lia | reflexivity]).
    (* [comment removed for export] *)
    destruct (cbR2 BSEGS ARB both_HCB both_HCBM ARB_ok rC M4 rom (at_ ARB 0x4c834) sp2 cache inst RETC HC1 HC2
                ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) M4 r0 c cnt k csz stw sbeg (Z_to_bv 64 1) R8 R2 R9 R18 R19 R20 R10 ltac:(wd_ulia) Hc Gcnt Gk Rcnt Rcsz Rk Rst)
      as (rB & RUNB & B10 & B13 & BK & BK2).
    { eapply (store_ok_sub BSEGS M4 thr _ 4096); [lia | exact SOKT | rewrite !at_at, at_u by lia; lia | rewrite !at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { eapply (store_ok_sub BSEGS M4 thr _ 4096); [lia | exact SOKT | rewrite !at_at, at_u by lia; lia | rewrite !at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { exact Rsb. }
    { exact FR. }
    { rewrite at_u by lia. rewrite <- Zplus_mod_idemp_l, T3. reflexivity. }
    { rewrite at_u by lia. unorm. unfold hideW in T1b. lia. }
    { rewrite !at_u by lia. lia. }
    { unorm. lia. }
    { exact Gsb. }
    cbv zeta in RUNB. rewrite !at_at in RUNB. replace (208 + 2576)%Z with 2784%Z in RUNB by reflexivity.
    change (wbytes (wbytes M4 _ _) _ _) with ms_MB in RUNB.
    (* [comment removed for export] *)
    assert (QB : forall x : word, (U x < U thr \/ U thr + 4096 <= U x)%Z -> ms_MB x = M4 x) by (intros x Hx; apply ms_MB_outside; lia).
    Ltac xqs QB H := eapply rd_same; [ intros x Hx; apply QB; revert Hx; rewrite ?at_at, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                       | rewrite ?at_at, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact H ].
    destruct (amC_run BSEGS ARB both_HAL2 rB ms_MB rom sp2 m (at_ S (-2128)) thr ctxw tr szw bsz b1 n tid)
      as (r4 & RUN4 & E1 & E10 & E11 & E18 & E20 & E21 & E24 & E25 & AG4).
    { rewrite (BK 2%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact HC2. }
    { rewrite (BK 9%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact HC9. }
    { rewrite B10. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold ms_ab in G in change_no_check G' end). unorm. reflexivity. }
    { rewrite (BK 19%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact HC19. }
    { rewrite (BK 20%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact HC20. }
    { rewrite (BK2 21%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact R21. }
    { rewrite (BK2 23%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact R23. }
    { rewrite (BK2 25%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact R25. }
    { rewrite (BK2 26%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact R26. }
    { rewrite (BK2 27%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact R27. }
    { exact Gn. } { exact Gtid. }
    { rewrite Um. lia. } { rewrite at_u by lia. lia. } { split; [split; [exact T1 | exact T1b] | lia]. } { lia. } { rewrite at_u by lia. lia. }
    { assert (Uh : U (at_ m (rz n - 15)) = (ms_ab + rz n - 15)%Z) by (rewrite at_u by (rewrite Um; lia); rewrite Um; lia).
      eapply rd_same; [ | | exact Rb1]; [intros x Hx; apply QB; rewrite Uh in Hx; cbn in Hx; lia | rewrite Uh; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { eapply store_ok_mono; [apply ms_MB_grows | exact SOKh]. }
    { xqs QB R16. }
    { (lazymatch goal with |- ?G => let G' := eval unfold ms_MB in G in change_no_check G' end). rewrite !rdn_wbytes_out; [exact RT0 | ..]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_at, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia. }
    { xqs QB Rtid. }
    { xqs QB Rtr. }
    { xqs QB Rsz. }
    { exact Hsz. }
    { rewrite at_u, Um by lia. lia. }
    { rewrite Um. lia. }
    { rewrite Um. lia. }
    { rewrite at_u, Um by lia. lia. }
    rewrite (ARB_lit 313396) in RUN4 by lia. rewrite (ARB_lit 586992) in RUN4 by lia. rewrite (ARB_lit 331676) in RUNB by lia. rewrite (ARB_lit 313396) in RUNB by lia.
    exists r4. split; [eapply msteps_trans; [exact RUNB | exact RUN4]|].
    split; [rewrite E1; apply ARB_lit; lia|].
    split; [rewrite (AG4 2%bv) by notin; rewrite (BK 2%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact HC2|].
    split; [exact E10|]. split; [exact E11|].
    split; [rewrite (AG4 8%bv) by notin; apply BK; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])|].
    split; [rewrite (AG4 9%bv) by notin; rewrite (BK 9%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact HC9|].
    split; [exact E18|].
    split; [rewrite (AG4 19%bv) by notin; rewrite (BK 19%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact HC19|].
    split; [exact E20|]. split; [exact E21|]. split; [exact E24|]. split; [exact E25|].
    intros i Hi. rewrite (AG4 i); [apply BK2; cbn [In] in Hi |- *; clear - Hi; tauto|].
    cbn [In] in Hi. intros Hx. cbn [In] in Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi.
  Qed.
End RUNS.
End FPGen.
End BoAllocMRunS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA BoAllocMIm OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove BoAllocM2s BoAllocM9e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9d.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.BoAllocMTag.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Ltac wm_parts H :=
  let T := type of H in
  lazymatch T with
  | ?A /\ ?B => let H1 := fresh "wmp" in let H2 := fresh "wmp" in
                pose proof (proj1 H) as H1; pose proof (proj2 H) as H2; wm_parts H1; wm_parts H2;
                (lazymatch A with context [or] => clear H1 | _ => idtac end);
                (lazymatch B with context [or] => lazymatch B with _ /\ _ => clear H2 | _ => idtac end | _ => idtac end)
  | _ => idtac
  end.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Lemma at0_lit : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof using. intros c Hc. apply bv_eq. rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]). rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma ARB_lit : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ ARB c = Z_to_bv 64 c.
Proof using. intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold ARB in G in change_no_check G' end). apply at0_lit. exact Hc. Qed.

(* [comment removed for export] *)
Ltac notin' := try (lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); try (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); notin.
Ltac rch := repeat (first [ reflexivity | assumption
                          | match goal with |- getr ?r ?i = _ => match goal with H : getr r i = _ |- _ => rewrite H end end
                          | match goal with |- getr ?r ?i = _ => match goal with AG : regs_agree _ _ r |- _ => rewrite (AG i) by notin' end end ]).

(* [comment removed for export] *)
Lemma rdn1_off : forall (m : mem) (a : word) b,
  (bv_unsigned a + 1 <= 0x10000 \/ 0x663000 <= bv_unsigned a)%Z -> rdn BSEGS m a 1 = Some [b] -> m a = Some b.
Proof using.
  intros m a b Ha R. cbn [rdn] in R. destruct (m a) as [b'|] eqn:E.
  - cbn in R. congruence.
  - unfold seg_rom, memory_read in R. change (Z.of_N 1) with 1%Z in R.
    rewrite (find_segment1_none_outside BSEGS 0x10000 0x663000 (bv_unsigned a) asanF_segs_in_hull) in R; [discriminate R|].
    destruct Ha as [Ha|Ha]; [left | right]; lia.
Qed.

Section RUNS1.
  Variables (mem rom : word -> option byte) (R : bvmap 5 word).
  Variables (S ra0 tp tsdp P top bot name : word) (T tctx n : Z) (D : nat).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HR1 : getr R 1 = ra0.
  Hypothesis HR2 : getr R 2 = S.
  Hypothesis HR4 : getr R 4 = tp.
  Hypothesis HR10 : getr R 10 = Z_to_bv 64 n.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gn : (64513 <= n <= 2 ^ 34)%Z.
  (* [comment removed for export] *)
  Hypothesis GT : ((4096 <= T /\ (T + 4096 <= AIMGLO \/ AIMGHI <= T)) /\ T + 4096 <= U S - 3584 /\ T mod 8 = 0)%Z.
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584 /\ (tctx + 4096 <= T \/ T + 4096 <= tctx))%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  Hypothesis GP : (AIMGLO <= U P /\ U P + 8 <= AIMGHI)%Z.
  Hypothesis Gtop : (4096 <= U top <= 2 ^ 47)%Z.
  Hypothesis Gbot : (U bot < U top)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-3584)) 3584 = true.
  (* [comment removed for export] *)
  Hypothesis C_mcs : rdn BSEGS mem (Z_to_bv 64 0x10eebc) 4 = Some (LE4 30).
  Hypothesis C_gcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8)).
  Hypothesis C_fum : rdn BSEGS mem (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_inited : rdn BSEGS mem (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_pg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 P).
  Hypothesis C_P : rdn BSEGS mem P 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_kif : rdn BSEGS mem (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn BSEGS mem (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn BSEGS mem (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn BSEGS mem tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn BSEGS mem (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_rss : rdn BSEGS mem (Z_to_bv 64 0x190422) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_lmag : rdn BSEGS mem (Z_to_bv 64 0x10488) 8 = Some (LE8 MAGICw).
  Hypothesis C_tbl2 : rdn BSEGS mem (at_ (Z_to_bv 64 0x104f8) 4) 1 = Some [Z_to_bv 8 3].
  Hypothesis C_t16 : rdn BSEGS mem (at_ (Z_to_bv 64 0x105f8) 8) 1 = Some [Z_to_bv 8 4].
  Hypothesis C_t2048 : rdn BSEGS mem (at_ (Z_to_bv 64 0x105f8) 49) 1 = Some [Z_to_bv 8 11].
  Hypothesis C_minrz : rdn BSEGS mem (at_ (Z_to_bv 64 0x10ab58) 3624) 2 = Some (LE2 16).
  Hypothesis C_maxrz : rdn BSEGS mem (at_ (Z_to_bv 64 0x10ab58) 3626) 2 = Some (LE2 2048).
  Hypothesis C_maxsz : rdn BSEGS mem (at_ (Z_to_bv 64 0x10ab58) 3616) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 40))).
  (* [comment removed for export] *)
  Hypothesis C_ipg : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 64)) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_gnm : rdn BSEGS mem (Z_to_bv 64 0x105f00) 8 = Some (LE8 (Z_to_bv 64 0x107e90)).
  Hypothesis C_nm : rdn BSEGS mem (Z_to_bv 64 0x107e90) 8 = Some (LE8 name).
  (* [comment removed for export] *)
  Hypothesis C_Tw : store_ok BSEGS mem thr 4096 = true.
  Hypothesis C_unw : rdn BSEGS mem (at_ thr 3168) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_sw : rdn BSEGS mem (at_ thr 40) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_top : rdn BSEGS mem (at_ thr 8) 8 = Some (LE8 top).
  Hypothesis C_bot : rdn BSEGS mem (at_ thr 16) 8 = Some (LE8 bot).
  Hypothesis C_T0 : rdn BSEGS mem thr 8 = Some (LE8 ctxw).
  Hypothesis C_tid : rdn BSEGS mem (at_ ctxw 8) 4 = Some (LE4 0).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Hfpc : fpc mem (U (getr R 8)) (U S) D.


  Lemma sfacts : (sec_needed n = rounded n + 4096)%Z /\ (n <= rounded n <= n + 7)%Z /\ (rz n = 2048)%Z.
  Proof using Gn GS S.
    assert (Hrz : (rz n = 2048)%Z) by (apply AsArith3.rz_big; lia).
    split; [(lazymatch goal with |- ?G => let G' := eval unfold sec_needed in G in change_no_check G' end); rewrite Hrz; lia|]. split; [| exact Hrz].
    (lazymatch goal with |- ?G => let G' := eval unfold rounded, RoundUp in G in change_no_check G' end). rewrite Z.max_l by lia. pose proof (Z.div_mod (n + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 8 - 1) 8 ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Definition ms_pre_mem (MA : word -> option byte) : word -> option byte :=
    la_m0 (cbs_m0 (wbytes MA (at_ (at_ S (-2272)) (-8)) (LE8 (Z_to_bv 64 0x4c818)))
                  (at_ S (-2272)) (Z_to_bv 64 0x4c834) (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (sec_needed n)) (Z_to_bv 64 2048))
          (at_ S (-2320)) (Z_to_bv 64 0x50d94) (Z_to_bv 64 8) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (sec_needed n)) (Z_to_bv 64 2048)
          (Z_to_bv 64 n) (Z_to_bv 64 0x10ab58) (at_ S (-2128)) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 7).

  Theorem run_mS_pre :
    exists (r5 : bvmap 5 word) (MP : word -> option byte) (s : Z) (bsz : list byte) (x18 x19 : word),
      let MA := ma_A MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) in
      msteps BSEGS (mkst R (Z_to_bv 64 0x6ef3c) mem rom) (mkst r5 (0x82a74 : word) (ms_pre_mem MA) rom)
      (* [comment removed for export] *)
      /\ la_regs (at_ S (-2320)) (Z_to_bv 64 0x10ae08) (sec_needed n) r5 /\ getr r5 1 = Z_to_bv 64 0x51080 /\ getr r5 21 = Z_to_bv 64 8
      /\ getr r5 10 = Z_to_bv 64 (la_msz (sec_needed n)) /\ getr r5 11 = name
      /\ getr r5 3 = getr R 3 /\ getr r5 4 = tp /\ getr r5 26 = thr /\ getr r5 27 = Z_to_bv 64 1
      (* [comment removed for export] *)
      /\ (1 <= s <= 30 /\ bytes_le_to_Z bsz = s)%Z /\ (s <= 2 + Z.of_nat D)%Z
      /\ (forall x : word, MP x <> mem x -> (U S - 2272 <= U x < U S)%Z)
      /\ mem_grows mem MP
      /\ rdn BSEGS MP (at_ S (-2120)) 4 = Some (LE4 s) /\ rdn BSEGS MP (at_ S (-2120)) 8 = Some bsz /\ length bsz = 8%nat
      /\ rdn BSEGS MP (at_ S (-2128)) 8 = Some (LE8 (at_ S (-2112)))
      /\ (forall (kk : Z) (v : word),
            In (kk, v) [(-8, ra0); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
            rdn BSEGS MP (at_ S kk) 8 = Some (LE8 v)).
  Proof using Hfpc C_bot C_top C_sw C_unw C_Tw C_nm C_gnm C_ipg C_maxsz C_maxrz C_minrz C_t2048 C_t16 C_tbl2 C_lmag C_rss C_thr C_tctx C_tsdp C_key C_kif C_P C_pg C_inited C_fum C_gcf C_mcs Hstk Gbot Gtop GP Gtsdp Gtp Gctx GT Gn GS HR10 HR4 HR2 HR1 tctx bot top P tsdp.
    wm_parts GT. wm_parts Gctx.
    pose proof (u64_range S) as HSr. pose proof (u64_range tp) as Htpr. pose proof (u64_range tsdp) as Htsr. pose proof (u64_range P) as HPr.
    destruct GS as (GS1 & GS2 & GS3). destruct GT as (GT1 & GT2 & GT3). destruct Gctx as (Gc1 & Gc2 & Gc3). destruct Gtp as (Gtp1 & Gtp2).
    pose proof sfacts as (NF1 & NF2 & NF3).
    assert (Uthr : U thr = T) by (unorm; reflexivity).
    assert (Uctx : U ctxw = tctx) by (unorm; reflexivity).
    (* [comment removed for export] *)
    assert (MH : mpH BSEGS both_mp_tab mem S (Z_to_bv 64 0x19fce8) thr (Z_to_bv 8 1)).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [mt_rb mt_ui mt_g_cf mt_a_inited mt_g_mcs both_mp_tab] in G in change_no_check G' end).
      - exact C_inited.
      - exact C_gcf.
      - replace (at_ (Z_to_bv 64 0x19fce8) 34) with (Z_to_bv 64 0x19fd0a : word) by (apply bv_eq; reflexivity). exact C_fum.
      - vm_compute. discriminate.
      - exact C_mcs.
      - eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
      - lia.
      - rewrite Uthr. lia. }
    assert (UH : uiH BSEGS both_ui_tab mem (at_ S (-2128)) (at_ S (-2128)) S thr P).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_g_inited ut_g_pgsz ut_img_lo ut_img_hi both_ui_tab] in G in change_no_check G' end).
      - exact C_inited.
      - exact C_unw.
      - eapply (store_ok_sub BSEGS mem thr _ 4096); [rewrite Uthr; lia | exact C_Tw | rewrite at_u, Uthr; lia | rewrite at_u, Uthr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - exact C_pg.
      - exact C_P.
      - rewrite !at_at. eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - rewrite !at_at. eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    assert (GH : gctH BSEGS (ut_gct both_ui_tab) mem (at_ S (-2208)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_gct both_ui_tab gt_tsd both_gct_tab] in G in change_no_check G' end).
      - exact C_kif. - exact C_key. - exact C_tsdp. - exact C_tctx. - exact C_thr.
      - unorm. lia.
      - rewrite !at_at. eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    assert (SH : stkH BSEGS mem thr top bot).
    { split; [exact C_sw | exact C_top | exact C_bot | exact Gbot | wd_ulia]. }
    destruct (mp_run BSEGS both_mp_tab both_mp_tab_ok R mem rom ra0 S tp (Z_to_bv 64 n) (Z_to_bv 64 0x19fce8) thr top bot tsdp ctxw P (Z_to_bv 8 1)
                HR1 HR2 HR4 HR10 MH UH GH SH Gtop D Hfpc)
      as (r1 & MP & s & RUN1 & A1 & A2 & A4 & A10 & A11 & A8 & A9 & A20 & A21 & AG1 & Hs1 & Hs2 & Psz & Ptag & Ptr & Ppc0 & Pslots & Punw & Pfoot & Pgrows).
    cbn [mt_rb both_mp_tab] in RUN1, A1.
    rewrite (ARB_lit 454460) in RUN1 by lia. rewrite (ARB_lit 312632) in RUN1 by lia.
    (* [comment removed for export] *)
    assert (QP : forall x : word, (U x < U S - 2272 \/ U S <= U x)%Z -> MP x = mem x).
    { intros x Hx. destruct (decide (MP x = mem x)) as [E|NE]; [exact E|]. exfalso.
      destruct (Pfoot x NE) as [F|F]; [lia|].
      apply NE. replace x with (at_ thr 3168) by (apply bv_eq; rewrite at_u by (rewrite Uthr; lia); rewrite Uthr; lia).
      rewrite (rdn1_off MP (at_ thr 3168) (Z_to_bv 8 0)); [| rewrite at_u, Uthr by (rewrite Uthr; lia); lia | exact Punw].
      rewrite (rdn1_off mem (at_ thr 3168) (Z_to_bv 8 0)); [reflexivity | rewrite at_u, Uthr by (rewrite Uthr; lia); lia | exact C_unw]. }
    (* [comment removed for export] *)
    Ltac xq Q H :=
      eapply rd_same; [ intros x Hx; apply Q; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
    destruct (amA_run_s BSEGS both_am_tab both_am_tab_ok r1 MP rom (at_ ARB 0x6f070) (at_ S (-2128)) (at_ S (-2128)) n A1 A2 A10 A11 Gn)
      as (r2 & RUN2 & B2 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & AG2).
    all: (lazymatch goal with |- ?G => let G' := eval cbn [am_rb am_inst am_g_magic am_tbl2 am_tbl am_g_inited am_g_rss both_am_tab] in G in change_no_check G' end).
    { xq QP C_inited. } { xq QP C_rss. } { xq QP C_lmag. } { xq QP C_tbl2. } { xq QP C_t16. } { xq QP C_t2048. }
    { xq QP C_minrz. } { xq QP C_maxrz. } { xq QP C_maxsz. }
    { rewrite at_at. eapply store_ok_mono; [exact Pgrows|].
      eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { unorm. rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    { rewrite at_u by lia. lia. }
    cbn [am_rb am_inst am_g_magic am_tbl2 am_tbl am_g_inited am_g_rss both_am_tab] in RUN2, B22, B26.
    rewrite (ARB_lit 312632) in RUN2 by lia. rewrite (ARB_lit 313364) in RUN2 by lia.
    rewrite (ma_A_eq MP S n r1 A8 A9 A20 A21) in RUN2.
    rewrite (AG1 22%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin). rewrite (AG1 23%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    rewrite (AG1 24%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin). rewrite (AG1 25%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    rewrite (AG1 26%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin). rewrite (AG1 27%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    set (MA := ma_A MP S n (getr r1 18) (getr r1 19) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) in RUN2.
    assert (QA : forall x : word, (U x < U S - 2280 \/ U S <= U x)%Z -> MA x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end). rewrite ma_A_outside; [apply QP; lia | lia | lia]. }
    assert (GRA : mem_grows mem MA) by (eapply mem_grows_trans; [exact Pgrows | (lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end); apply ma_A_grows]).
    rewrite at_at in B2. cbn [Z.add Z.opp Pos.add] in B2.
    (* [comment removed for export] *)
    assert (B4 : getr r2 4 = tp) by (rewrite (AG2 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); notin); rewrite (AG1 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin); exact HR4).
    assert (B3 : getr r2 3 = getr R 3) by (rewrite (AG2 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); notin); rewrite (AG1 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin); reflexivity).
    assert (GH2 : gctH BSEGS both_gct_tab MA (at_ S (-2272)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end).
      - xq QA C_kif. - xq QA C_key. - xq QA C_tsdp. - xq QA C_tctx. - xq QA C_thr.
      - unorm. lia.
      - rewrite at_at. eapply store_ok_mono; [exact GRA|].
        eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    destruct (ambs_glue BSEGS ARB both_HAL both_gct_tab both_gct_tab_ok both_GTRB r2 MA rom (at_ S (-2272)) tp tsdp ctxw thr (Z_to_bv 64 0x10ab58)
                (sec_needed n) B2 B4 B19 B22 GH2 ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(rewrite Uthr, at_u by lia; lia))
      as (r3 & M1 & RUN3 & EM1 & C1 & C2 & C10 & C11 & C12 & C13 & C26 & CK & AGK).
    rewrite (ARB_lit 313364) in RUN3 by lia. rewrite (ARB_lit 330988) in RUN3 by lia.
    rewrite (ARB_lit 313368) in EM1 by lia. rewrite (ARB_lit 313396) in C1 by lia.
    subst M1.
    replace (Z_to_bv 64 330988 : word) with (0x50cec%bv : word) in RUN3 by (apply bv_eq; reflexivity).
    Ltac viaCK CK H := rewrite CK by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20); exact H.
    (* [comment removed for export] *)
    set (M1 := wbytes MA (at_ (at_ S (-2272)) (-8)) (LE8 (Z_to_bv 64 0x4c818))) in *.
    assert (GR1 : mem_grows mem M1) by (eapply mem_grows_trans; [exact GRA | apply wbytes_grows]).
    assert (Q1 : forall x : word, (U x < U S - 2280 \/ U S <= U x)%Z -> M1 x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). rewrite wbytes_outside; [apply QA; exact Hx | rewrite length_N_to_le_bytes, !at_u by (rewrite ?at_u; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, !at_u by (rewrite ?at_u; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    destruct (cbs_pre M1 rom (at_ S (-2272)) (Z_to_bv 64 0x4c834) (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (sec_needed n)) (Z_to_bv 64 2048)
                (sec_needed n) r3 C1 C2 C10 C12 C13 ltac:(viaCK CK B8) ltac:(viaCK CK B9) ltac:(viaCK CK B18) ltac:(viaCK CK B19) ltac:(viaCK CK B20))
      as (r4 & RUN4 & D1 & D2 & D8 & D10 & D11 & D12 & D13 & AG4).
    { rewrite at_u by lia. lia. }
    { lia. }
    { rewrite at_at. eapply store_ok_mono; [exact GR1|].
      eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    rewrite at_at in D2. change (-2272 + -48)%Z with (-2320)%Z in D2.
    set (M2 := cbs_m0 M1 (at_ S (-2272)) (Z_to_bv 64 0x4c834) (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (sec_needed n)) (Z_to_bv 64 2048)) in *.
    assert (GR2 : mem_grows mem M2) by (eapply mem_grows_trans; [exact GR1 | (lazymatch goal with |- ?G => let G' := eval unfold M2, cbs_m0 in G in change_no_check G' end); do 5 (eapply mem_grows_trans; [| apply wbytes_grows]); apply wbytes_grows]).
    assert (Q2 : forall x : word, (U x < U S - 2320 \/ U S <= U x)%Z -> M2 x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M2, cbs_m0 in G in change_no_check G' end). rewrite !wbytes_outside by (rewrite length_N_to_le_bytes, !at_u by (rewrite ?at_u; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia). apply Q1. lia. }
    (* [comment removed for export] *)
    Ltac via4 AG4 CK H := rewrite (AG4 _) by notin; rewrite CK by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20); exact H.
    destruct (la_pre M2 rom (at_ S (-2320)) (Z_to_bv 64 0x50d94) (Z_to_bv 64 8) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (sec_needed n)) (Z_to_bv 64 2048)
                (Z_to_bv 64 n) (Z_to_bv 64 0x10ab58) (at_ S (-2128)) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 7) (Z_to_bv 64 0x10ae08) name
                (sec_needed n) r4 D1 D2 D10 D11 D12 D13 D8 ltac:(via4 AG4 CK B9) ltac:(via4 AG4 CK B18) ltac:(via4 AG4 CK B19) ltac:(via4 AG4 CK B20)
                ltac:(via4 AG4 CK B21) ltac:(via4 AG4 CK B22) ltac:(via4 AG4 CK B23) ltac:(via4 AG4 CK B24) ltac:(via4 AG4 CK B25))
      as (r5 & RUN5 & E_regs & E1 & E21 & E10 & E11 & AG5).
    { rewrite at_u by lia. lia. }
    { lia. }
    { rewrite at_at. eapply store_ok_mono; [exact GR2|].
      eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { xq Q2 C_ipg. } { xq Q2 C_gnm. } { xq Q2 C_nm. }
    exists r5, MP, s.
    destruct (rdn_defined_ex BSEGS MP (at_ S (-2120)) 8) as [bsz [Rsz Lsz]].
    { intros i Hi. rewrite at_u in Hi by lia. apply Pgrows. apply (store_ok1_heap mem); [wd_ulia|].
      eapply (store_ok_sub BSEGS mem (at_ S (-3584)) _ 3584 1); [rewrite at_u; lia | exact Hstk | rewrite at_u by lia; wd_ulia | rewrite at_u by lia; wd_ulia_c]. }
    { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    assert (HBSZ : bytes_le_to_Z bsz = s) by (apply (bsz_val BSEGS MP (at_ S (-2120)) bsz s Rsz Psz); [rewrite at_at; exact Ptag | lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]).
    exists bsz, (getr r1 18), (getr r1 19). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold MA.
    split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; eapply msteps_trans; [exact RUN3|]; eapply msteps_trans; [exact RUN4 | exact RUN5]|].
    split; [exact E_regs|]. split; [exact E1|]. split; [exact E21|]. split; [exact E10|]. split; [exact E11|].
    split; [rewrite (AG5 _) by notin; rewrite (AG4 _) by notin; rewrite CK by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20); exact B3|].
    split; [rewrite (AG5 _) by notin; rewrite (AG4 _) by notin; rewrite CK by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20); exact B4|].
    split; [rewrite (AG5 _) by notin; rewrite (AG4 _) by notin; exact C26|].
    split; [rewrite (AG5 _) by notin; rewrite (AG4 _) by notin; rewrite CK by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20); exact B27|].
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    - intros x NE. destruct (Pfoot x NE) as [F|F]; [exact F|]. exfalso. apply NE. apply QP. rewrite Uthr in F. lia.
  Qed.
End RUNS1.
End FPGen.
