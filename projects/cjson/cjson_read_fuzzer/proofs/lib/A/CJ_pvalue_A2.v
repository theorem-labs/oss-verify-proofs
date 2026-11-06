(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module CJ_pvalue_ctx.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition SHV (a : Z) : word := Z_to_bv 64 (Z.shiftr a 3 + 2147450880).

Section PV.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (g : lghost) (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (np B : Z) (CH : list (Z * Z * Z)).
  Variables (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure (PARSE_STACK depth) sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo.
  Hypothesis BPRE : pv_cost_pre (blen - off) <= B.
  Hypothesis CHOK : chain_ok (bv_unsigned sp + 16) CH (ASTACK_TOP sp0).
  Hypothesis CHL : chain_link (bv_unsigned s0) (bv_unsigned sp) CH.
  Hypothesis RA1 : 4096 <= bv_unsigned ra.
  Hypothesis RA2 : ~ is_pc0 (bv_unsigned ra).

  Notation SP := (bv_unsigned sp).
  Notation POST := (parse_value_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR LF np B CH U P CA blen off depth bs D n lo m g
                      nx pv ty p1 vi p2 vd ky).

  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC)
                 as (HPU & (HD & DCA & CAD) & LEN & BLEN & CEIL & BOT & LO & (PLF & PF1 & PF2 & PF3) & (SP1 & SP2 & SP3 & SP4 & SP5 & SP6)
                     & OFF & DEP & TP & (U1 & U2 & U3 & U4) & (D1 & D2 & D3 & D4) & UD & PU & PD & SPR & TOPR & BOTE);
               unfold PARSE_STACK in LO;
               pose proof (bv_unsigned_in_range 64 ra) as RAR; change (bv_modulus 64) with (2^64) in RAR;
               pose proof (bv_unsigned_in_range 64 s0) as S0R; change (bv_modulus 64) with (2^64) in S0R.
  Ltac alia := unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_END; rewrite ?alloc_ceiling_eq; unfold PARSE_STRING_STACK, DELETE_STACK, POBJ_STACK, PARSE_STACK, ASTKMALLOC_STACK, AINTRIN_STACK, ASTRFN_STACK, AMALLOC_STACK; lia.
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac blia := unfold pv_cost_pre, PV_FRATE, PV_RATE in *; rewrite ?cost_free_eq in *; rewrite ?length_app in *; cbn [length] in *; unfold cblock in *; lia.

  (* [comment removed for export] *)
  Definition SAVEDV : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition VST (SA Fr pc : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word)
      (Fx : bvmap 5 word) (fcx : bv 32) (mm : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 Fr) x19 x20 x21 x22 x23 x24 (SHV Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
       Fx (Z_to_bv 64 pc) fcx None mm (seg_rom asegs).

  (* [comment removed for export] *)
  Definition MIDV (SA Fr : Z) (m1 : word -> option byte) (mo1 : Model) (g1 : lghost) (LB1 : list cblock) (TRS1 : list (list Z)) (B1 : Z) (errv1 : word) : Prop :=
    ART AI sp0 SPB LB1 ((Fr, 2) :: LF) TRS1 B1 m1 mo1 g1 /\ bytes_at asegs m1 CA bs /\ rw_cells asegs m1 AERRNO [C4 errv1]
    /\ mem_inv asegs m1 /\ stk asegs m1 lo SA /\ ppres sp0 LR LF SP P m m1 /\ gmono g g1 /\ TINV TI np TRS1
    /\ pbuf_sh m1 P /\ chain_cells m1 CH.

  (* [comment removed for export] *)
  Definition LOCSV (Fr : Z) (lj : list byte) : list cell :=
    [C8 (SHV (P + 8)); C8 (Z_to_bv 64 (P + 8)); C8 (SHV P); C8 (Z_to_bv 64 (P + 16)); C8 (SHV (P + 16)); C8 (Z_to_bv 64 U); CB 16 lj; C8 (Z_to_bv 64 Fr)].

  Lemma LOCSV_size : forall Fr lj, cells_size (LOCSV Fr lj) = 72%nat.
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition VFR (SA Fr : Z) (m1 : word -> option byte) (shb : list byte) (h : word) (jae jn : list byte) (cs08 : list cell) (lj : list byte) : Prop :=
    SHCW m1 Fr shb /\ length shb = 32%nat /\ rw_cells asegs m1 Fr [C8 h]
    /\ rw_cells asegs m1 (Fr + 32) [CB 8 jae] /\ rw_cells asegs m1 (Fr + 64) [CB 64 jn]
    /\ rw_cells asegs m1 SA cs08 /\ cells_size cs08 = 16%nat /\ rw_cells asegs m1 (SA + 16) (LOCSV Fr lj)
    /\ stk asegs m1 (SA + 88) (SP + -104) /\ rw_cells asegs m1 (SP + -104) SAVEDV.

  (* [comment removed for export] *)
  Lemma VFR_locs : forall SA Fr m1 shb h jae jn cs08 lj,
    VFR SA Fr m1 shb h jae jn cs08 lj -> SA + 88 <= SP - 104 ->
    exists locs, rw_cells asegs m1 SA locs /\ SA + Z.of_nat (cells_size locs) = SP - 104.
  Proof.
    intros SA Fr m1 shb h jae jn cs08 lj (_ & _ & _ & _ & _ & L0 & S0 & L16 & STP & _) HS.
    assert (J : rw_cells asegs m1 SA (cs08 ++ LOCSV Fr lj)).
    { apply (proj2 (rw_cells_split_app _ _ _ _)). split; [exact L0|]. rewrite S0. exact L16. }
    (nelim (frame_join m1 SA _ (SP + -104) J ltac:(rewrite cells_size_app, S0, LOCSV_size; change (Z.of_nat (16 + 72)) with 88; exact STP) ltac:(rewrite cells_size_app, S0, LOCSV_size; change (Z.of_nat (16 + 72)) with 88; lia)) 3%nat; intros locs FRL SZL)
.
    exists locs. split; [exact FRL| lia].
  Qed.

  (* [comment removed for export] *)
  Definition VGEOM (SA Fr : Z) : Prop :=
    SP - 208 <= SA <= SP - 192 /\ SA mod 32 = 0 /\ Fr mod 256 = 0
    /\ (AIMG_HI <= Fr /\ sclr Fr 256)      (* [comment removed for export] *)
    /\ Fr + 256 <= alloc_ceiling
    /\ (forall A n, In (A, n) LB -> A + n <= Fr \/ Fr + 256 <= A) /\ ~ In Fr (map fst LF)
    /\ (Fr + 256 <= P - 32 \/ P - 32 + 128 <= Fr).

  (* [comment removed for export] *)
  Definition VRES (m1 : word -> option byte) (r : Z) (LBX : list cblock) (B1 off' depth' : Z) : Prop :=
    exists X, Permutation ((U, 64) :: X ++ LR) LBX
    /\ ( (r = 0 /\ X = [] /\ rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) /\ B - pv_cost_pre (blen - off) <= B1)
         \/ (r = 1 /\ depth' = depth /\ off <= off' <= blen /\ B - PV_RATE * (off' - off) <= B1
             /\ Z.of_nat (length X) <= off' - off
             /\ exists (ch ty' vs : Z) (vi' vd' : word) (dc : nat) (Bv Bc : list cblock),
                  X = Bv ++ Bc
                  /\ rw_cells asegs m1 U (node_cells nx pv ch ty' p1 vs vi' p2 vd' ky)
                  /\ CJ_PRINTABLE ty' /\ cj_str m1 vs Bv /\ cj_chain CJ_PRINTABLE m1 dc ch Bc /\ Z.of_nat dc + depth <= 1000) ).

  (* [comment removed for export] *)
  Definition flag_apart_stmt : Prop :=
    forall sp0' SPB' LB' LF' TRS' B' m' mo' g' Fr' k fl G k',
      ART AI sp0' SPB' LB' LF' TRS' B' m' mo' g' -> In (Fr', k) LF' -> cells_at asegs m' (Fr' + fsz k - 8) [C8 (wz fl)] -> 0 <= fl < 2^64 ->
      In (G, k') LF' -> fl + 1 <= G.
  Hypothesis FLA : flag_apart_stmt.



  (* [comment removed for export] *)
  Lemma pv_addr_not_frsh : forall Fr LBX m1 mo1 g1 TRS1 B1 SA a,
    VGEOM SA Fr -> ART AI sp0 SPB LBX ((Fr, 2) :: LF) TRS1 B1 m1 mo1 g1 -> (forall b, In b LR -> In b LBX) ->
    0 <= a < 2^64 -> pv_addr sp0 LR LF SP P a -> ~ (SH Fr <= a < SH Fr + 32).
  Proof.
    intros Fr LBX m1 mo1 g1 TRS1 B1 SA a (GSA & GAL & FAL & FLO & FHI & FBLK & FNEW & PFR') HL INLR Ha (Hc & He & Hp) Hin. lits. bandM. sepM.
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI.
    pose proof (SH_bounds Fr ltac:(lia)) as B1'. pose proof (SH_mono (Fr + 256) (@alloc_ceiling ACEIL) ltac:(lia)) as B2.   (* [comment removed for export] *)
    rewrite (SH_aligned_add Fr 256) in B2 by mod8. change (256 / 8) with 32 in B2.
    (* [comment removed for export] *)
    (nelimp SH_ceiling_bounds 3%nat; intros SHC1 SHC2 SHC3).
    assert (ABAND : KLOWSHADOW_BEG <= a < KHIGHMEM_BEG).
    { pose proof (SH_in_band Fr ltac:(lia) ltac:(lia)) as (SB1 & SB2). clear -SB1 SB2 B2 SHC2 Hin. unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in *. lia. }
    destruct Hc as [Hs|[Hi|[(A & n0 & HinA & Hr)|[(G & k & HinG & Hr)|Hsh]]]].
    - lia.
    - pose proof (aclient_image_lt a Hi). unfold SH, SHADOW_OFFSET in *. lia.
    - apply (art_block_clear_band AI _ _ _ _ _ _ _ _ _ _ _ a HL (INLR _ HinA) ABAND). lia.
    - (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(right; exact HinG)) 5%nat; intros Hk GAL' GLO GHI _).
      unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in GLO. bandM. sepM. try rewrite alloc_ceiling_eq in GHI.
      assert (Hfs : fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
      destruct Hr as [Hb|Hshg]; [exact (ablk_clear_band _ _ a (art_frame_band AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(right; exact HinG)) ABAND ltac:(lia))|].
      assert (NE : Fr <> G) by (intros ->; apply FNEW; apply (in_map fst) in HinG; exact HinG).
      destruct (art_frames_disjoint AI _ _ _ _ _ _ _ _ _ Fr 2 G k HL ltac:(left; reflexivity) ltac:(right; exact HinG) NE) as [D1'|D2'];
        change (fsz 2) with 256 in *.
      + pose proof (SH_mono (Fr + 256) G D1') as M1. rewrite (SH_aligned_add Fr 256) in M1 by mod8. change (256 / 8) with 32 in M1. lia.
      + pose proof (SH_mono (G + fsz k) Fr D2') as M1. rewrite (SH_aligned_add G (fsz k)) in M1 by mod8.
        assert (fsz k / 8 = 16 \/ fsz k / 8 = 32) by (destruct Hfs as [-> | ->]; [left| right]; reflexivity). lia.
    - unfold astack_shadow in Hsh. lia.
  Qed.

  Lemma pv_addr_not_flag : forall Fr LBX m1 mo1 g1 TRS1 B1 SA fl a,
    VGEOM SA Fr -> ART AI sp0 SPB LBX ((Fr, 2) :: LF) TRS1 B1 m1 mo1 g1 -> (forall b, In b LR -> In b LBX) ->
    cells_at asegs m1 (Fr + 248) [C8 (wz fl)] -> rw_cells asegs m1 fl [C1 (zb 1)] ->
    (forall A n, In (A, n) LBX -> fl < A - 16 \/ A + n <= fl) -> fl + 1 <= Fr - 8 ->
    0 <= a < 2^64 -> pv_addr sp0 LR LF SP P a -> a <> fl.
  Proof.
    intros Fr LBX m1 mo1 g1 TRS1 B1 SA fl a (GSA & GAL & FAL & FLO & FHI & FBLK & FNEW & PFR') HL INLR FLP FLB FLK FLT Ha (Hc & He & Hp) ->. lits. bandM. sepM.
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI.
    pose proof (rw_cells_bound asegs _ _ _ FLB) as FB. cbn [cells_size Cells.csize Nat.add] in FB.
    pose proof (art_flag_high_holds AI _ _ _ _ _ _ _ _ _ Fr 2 fl HL ltac:(left; reflexivity) ltac:(change (fsz 2) with 256; replace (Fr + 256 - 8) with (Fr + 248) by lia; exact FLP) ltac:(lia)) as FH.
    (* [comment removed for export] *)
    pose proof (ablk_img _ _ FH) as FH1. unfold AIMG_HI in FH1. assert (SHC : SH (2^47) = 17594333495296) by reflexivity.
    (nelimp SH_ceiling_bounds 3%nat; intros SHC1 SHC2 SHC3).
    destruct Hc as [Hs|[Hi|[(A & n0 & HinA & Hr)|[(G & k & HinG & Hr)|Hsh]]]].
    - lia.
    - pose proof (aclient_image_lt fl Hi). lia.
    - destruct (FLK A n0 (INLR _ HinA)); lia.
    - pose proof (FLA _ _ _ _ _ _ _ _ _ Fr 2 fl G k HL ltac:(left; reflexivity) ltac:(change (fsz 2) with 256; replace (Fr + 256 - 8) with (Fr + 248) by lia; exact FLP) ltac:(lia) ltac:(right; exact HinG)) as FG.
      (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(right; exact HinG)) 5%nat; intros Hk GAL' GLO GHI _).
      unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in GLO. bandM. sepM. try rewrite alloc_ceiling_eq in GHI.
      destruct Hr as [Hb|Hshg]; [lia|].
      apply (ablk_clear_band _ _ fl FH); [| lia].
      pose proof (SH_in_band G ltac:(lia) ltac:(destruct Hk as [-> | ->]; [change (fsz 1) with 128 in *| change (fsz 2) with 256 in *]; lia)) as (SB1 & SB2).
      unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in *.
      destruct Hk as [-> | ->]; [change (fsz 1) with 128 in *| change (fsz 2) with 256 in *];
        (pose proof (SH_mono (G + 256) (2^47) ltac:(lia)) as M1;
         rewrite (SH_aligned_add G 256) in M1 by mod8; change (256 / 8) with 32 in M1; rewrite SHC in M1;
         cbn in Hshg; lia).
    - unfold astack_shadow in Hsh. rewrite SHC in Hsh.
      apply (ablk_clear_band _ _ fl FH); [unfold KLOWSHADOW_BEG, KHIGHMEM_BEG; lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma VRES_magree : forall m1 m2 r LBX B1 off' depth',
    VRES m1 r LBX B1 off' depth' -> magree (in_cblock LBX) m1 m2 -> VRES m2 r LBX B1 off' depth'.
  Proof.
    intros m1 m2 r LBX B1 off' depth' (X & HP & RES) MA. exists X. split; [exact HP|].
    assert (INU : In (U, 64) LBX) by (eapply perm_in_head; exact HP).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HP| right; apply in_or_app; left; exact Hb]).
    destruct RES as [(Hr & HX & ND & HB)|(Hr & Hd & Ho & HB & HL' & ch & ty' & vs & vi' & vd' & dc & Bv & Bc & HX & ND & HT & SV & CHN & Hdc)].
    - left. split; [exact Hr|]. split; [exact HX|]. split; [| exact HB].
      eapply rw_cells_magree; [exact MA| exact ND|]. rewrite node_cells_size. intros a Ha. exists U, 64. split; [exact INU| lia].
    - right. split; [exact Hr|]. split; [exact Hd|]. split; [exact Ho|]. split; [exact HB|]. split; [exact HL'|].
      exists ch, ty', vs, vi', vd', dc, Bv, Bc. split; [exact HX|]. split.
      { eapply rw_cells_magree; [exact MA| exact ND|]. rewrite node_cells_size. intros a Ha. exists U, 64. split; [exact INU| lia]. }
      split; [exact HT|]. split.
      { eapply cj_str_magree; [exact MA| exact SV|]. intros a nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Hr'). exists A', n'. split; [apply INX; rewrite HX; apply in_or_app; left; exact Hin| exact Hr']. }
      split; [| exact Hdc].
      eapply cj_chain_magree; [exact CHN| exact MA|]. intros a nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Hr'). exists A', n'. split; [apply INX; rewrite HX; apply in_or_app; right; exact Hin| exact Hr'].
  Qed.

  (* [comment removed for export] *)
  Lemma pv_addr_not_frbody : forall Fr LBX m1 mo1 g1 TRS1 B1 SA a,
    VGEOM SA Fr -> ART AI sp0 SPB LBX ((Fr, 2) :: LF) TRS1 B1 m1 mo1 g1 -> (forall b, In b LR -> In b LBX) ->
    0 <= a < 2^64 -> pv_addr sp0 LR LF SP P a -> ~ (Fr <= a < Fr + 248).
  Proof.
    intros Fr LBX m1 mo1 g1 TRS1 B1 SA a (GSA & GAL & FAL & FLO & FHI & FBLK & FNEW & PFR') HL INLR Ha (Hc & He & Hp) Hin. lits. bandM. sepM.
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI.
    destruct Hc as [Hs|[Hi|[(A & n0 & HinA & Hr)|[(G & k & HinG & Hr)|Hsh]]]].
    - lia.
    - pose proof (aclient_image_lt a Hi). lia.
    - (nelim (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity)) 8%nat; intros _ _ _ _ _ _ _ FD).
      destruct (FD A n0 (INLR _ HinA)); change (fsz 2) with 256 in *; lia.
    - (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(right; exact HinG)) 5%nat; intros Hk GAL' GLO GHI _).
      unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in GLO. bandM. sepM. try rewrite alloc_ceiling_eq in GHI.
      assert (NE : Fr <> G) by (intros ->; apply FNEW; apply (in_map fst) in HinG; exact HinG).
      destruct Hr as [Hb|Hshg].
      + destruct (art_frames_disjoint AI _ _ _ _ _ _ _ _ _ Fr 2 G k HL ltac:(left; reflexivity) ltac:(right; exact HinG) NE); change (fsz 2) with 256 in *;
          destruct Hk as [-> | ->]; cbn in *; lia.
      + (* [comment removed for export] *)
        pose proof (art_frame_band AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity)) as FBND. change (fsz 2) with 256 in FBND.
        apply (ablk_clear_band _ _ a FBND); [| lia].
        assert (Hfs : fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
        sepM. pose proof (SH_in_band G ltac:(lia) ltac:(lia)) as (SB1 & SB2).
        pose proof (SH_mono (G + fsz k) (2^47) ltac:(lia)) as M1. rewrite (SH_aligned_add G (fsz k)) in M1 by mod8.
        assert (SHC : SH (2^47) = 17594333495296) by reflexivity. rewrite SHC in M1.
        clear - SB1 SB2 M1 Hshg. unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in *. lia.
    - unfold astack_shadow in Hsh. assert (SHC : SH (2^47) = 17594333495296) by reflexivity. rewrite SHC in Hsh.
      pose proof (art_frame_band AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity)) as FBND. change (fsz 2) with 256 in FBND.
      (nelimp SH_ceiling_bounds 3%nat; intros SHC1 SHC2 SHC3).
      apply (ablk_clear_band _ _ a FBND); [unfold KLOWSHADOW_BEG, KHIGHMEM_BEG; lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma pv_addr_below : forall LBX LFX m1 mo1 g1 TRS1 B1 a,
    ART AI sp0 SPB LBX LFX TRS1 B1 m1 mo1 g1 -> (forall b, In b LR -> In b LBX) -> (forall f, In f LF -> In f LFX) ->
    0 <= a < 2^64 -> pv_addr sp0 LR LF SP P a -> a < alloc_ceiling \/ SP <= a.
  Proof.
    intros LBX LFX m1 mo1 g1 TRS1 B1 a HL INLR INLF Ha nelH_; (nelim nelH_ 3%nat; intros Hc He Hp). lits. bandM. sepM. try rewrite alloc_ceiling_eq.
    assert (SHC : SH (2^47) = 17594333495296) by reflexivity.
    destruct Hc as [Hs|[Hi|[(A & n0 & HinA & Hr)|[(G & k & HinG & Hr)|Hsh]]]].
    - right. lia.
    - left. pose proof (aclient_image_lt a Hi). lia.
    - left. (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (INLR _ HinA)) 4%nat; intros R1 _ _ R4). try rewrite alloc_ceiling_eq in R4. lia.
    - left. (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL (INLF _ HinG)) 5%nat; intros Hk GAL' GLO GHI _).
      unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in GLO. bandM. sepM. try rewrite alloc_ceiling_eq in GHI.
      assert (Hfs : fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
      destruct Hr as [Hb|Hshg]; [lia|].
      pose proof (SH_bounds G ltac:(lia)). pose proof (SH_bounds (G + fsz k) ltac:(lia)) as M1.
      rewrite (SH_aligned_add G (fsz k)) in M1 by mod8. lia.
    - left. unfold astack_shadow in Hsh. rewrite SHC in Hsh. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma VFR_ppres : forall SA Fr m1 m2 shb h jae jn cs08 lj LR',
    VGEOM SA Fr -> VFR SA Fr m1 shb h jae jn cs08 lj -> ppres sp0 LR' ((Fr, 2) :: LF) SA P m1 m2 ->
    (SP - 208 <= SA) -> VFR SA Fr m2 shb h jae jn cs08 lj.
  Proof.
    intros SA Fr m1 m2 shb h jae jn cs08 lj LR' (GSA & GAL & FAL & FLO & FHI & FBLK & FNEW & PFR') (SHC & L32 & HDR & AE & NC & L0 & S0 & L16 & STP & SAVW) PR _. lits. bandM. sepM.
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI.
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    assert (INF : In (Fr, 2) ((Fr, 2) :: LF)) by (left; reflexivity).
    assert (BODYa : forall a, Fr <= a < Fr + 248 -> pv_addr sp0 LR' ((Fr, 2) :: LF) SA P a).
    { intros a Ha. split; [| unfold AERRNO, ATP; split; lia]. do 3 right. left. exists Fr, 2. split; [exact INF|]. left. change (fsz 2) with 256. lia. }
    assert (SHa : forall a, SH Fr <= a < SH Fr + 32 -> pv_addr sp0 LR' ((Fr, 2) :: LF) SA P a).
    { intros a Ha. pose proof (SH_bounds Fr ltac:(lia)). split; [| unfold AERRNO, ATP; split; lia]. do 3 right. left. exists Fr, 2. split; [exact INF|]. right. change (fsz 2) with 256. cbn. lia. }
    split. { unfold SHCW in *. eapply rw_cells_magree; [exact PR| exact SHC|]. rewrite cells_size_mapC1, L32, SH_shiftr. intros a Ha. apply SHa. lia. }
    split; [exact L32|].
    split. { eapply rw_cells_magree; [exact PR| exact HDR|]. cbn. intros a Ha. apply BODYa. lia. }
    split. { eapply rw_cells_magree; [exact PR| exact AE|]. cbn. intros a Ha. apply BODYa. lia. }
    split. { eapply rw_cells_magree; [exact PR| exact NC|]. cbn. intros a Ha. apply BODYa. lia. }
    split. { eapply (ppres_rw_cells_stack _ _ _ _ _ _ _ _ _ PR); [exact L0| lia| rewrite S0; lia| try rewrite alloc_ceiling_eq; lia| try rewrite alloc_ceiling_eq; lia]. }
    split; [exact S0|].
    split. { eapply (ppres_rw_cells_stack _ _ _ _ _ _ _ _ _ PR); [exact L16| lia| rewrite LOCSV_size; lia| try rewrite alloc_ceiling_eq; lia| try rewrite alloc_ceiling_eq; lia]. }
    split. { eapply (ppres_stk _ _ _ _ _ _ _ _ _ PR); [exact STP| lia| lia| try rewrite alloc_ceiling_eq; lia| try rewrite alloc_ceiling_eq; lia]. }
    eapply (ppres_rw_cells_stack _ _ _ _ _ _ _ _ _ PR); [exact SAVW| lia| unfold SAVEDV; cbn; lia| try rewrite alloc_ceiling_eq; lia| try rewrite alloc_ceiling_eq; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma VFR_cj_pres : forall SA Fr m1 m2 shb h jae jn cs08 lj LBX,
    VGEOM SA Fr -> VFR SA Fr m1 shb h jae jn cs08 lj -> cj_pres sp0 LBX ((Fr, 2) :: LF) SA m1 m2 ->
    VFR SA Fr m2 shb h jae jn cs08 lj.
  Proof.
    intros SA Fr m1 m2 shb h jae jn cs08 lj LBX (GSA & GAL & FAL & FLO & FHI & FBLK & FNEW & PFR') (SHC & L32 & HDR & AE & NC & L0 & S0 & L16 & STP & SAVW) PR. lits. bandM. sepM.
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI.
    assert (INF : In (Fr, 2) ((Fr, 2) :: LF)) by (left; reflexivity).
    split. { unfold SHCW in *. apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR) in SHC; [exact SHC|]. do 5 right. left. exists Fr, 2. split; [exact INF|]. rewrite cells_size_mapC1, L32, SH_shiftr. change (fsz 2) with 256. cbn. lia. }
    split; [exact L32|].
    split. { apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR) in HDR; [exact HDR|]. do 4 right. left. exists Fr, 2. split; [exact INF|]. cbn. change (fsz 2) with 256. lia. }
    split. { apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR) in AE; [exact AE|]. do 4 right. left. exists Fr, 2. split; [exact INF|]. cbn. change (fsz 2) with 256. lia. }
    split. { apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR) in NC; [exact NC|]. do 4 right. left. exists Fr, 2. split; [exact INF|]. cbn. change (fsz 2) with 256. lia. }
    split. { apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR) in L0; [exact L0|]. left. rewrite S0. lia. }
    split; [exact S0|].
    split. { apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR) in L16; [exact L16|]. left. rewrite LOCSV_size. lia. }
    split. { eapply (cj_pres_stk _ _ _ _ _ _ _ _ PR); [exact STP| lia| lia]. }
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR) in SAVW; [exact SAVW|]. left. unfold SAVEDV. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma VFR_below : forall SA Fr m1 m2 shb h jae jn cs08 lj lo' hi',
    VGEOM SA Fr -> VFR SA Fr m1 shb h jae jn cs08 lj -> munch [(lo', hi')] m1 m2 -> wmono asegs m1 m2 ->
    alloc_ceiling <= lo' -> hi' <= SA -> VFR SA Fr m2 shb h jae jn cs08 lj.
  Proof.
    intros SA Fr m1 m2 shb h jae jn cs08 lj lo' hi' (GSA & GAL & FAL & FLO & FHI & FBLK & FNEW & PFR') (SHC & L32 & HDR & AE & NC & L0 & S0 & L16 & STP & SAVW) MU WM Hlo Hhi. lits. bandM. sepM.
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI, Hlo. pose proof (SH_bounds Fr ltac:(lia)).
    split. { unfold SHCW in *. eapply rw_cells_transport; [exact SHC| exact MU| exact WM|]. rewrite cells_size_mapC1, L32, SH_shiftr. cbn. lia. }
    split; [exact L32|].
    split. { eapply rw_cells_transport; [exact HDR| exact MU| exact WM|]. cbn. lia. }
    split. { eapply rw_cells_transport; [exact AE| exact MU| exact WM|]. cbn. lia. }
    split. { eapply rw_cells_transport; [exact NC| exact MU| exact WM|]. cbn. lia. }
    split. { eapply rw_cells_transport; [exact L0| exact MU| exact WM|]. rewrite S0. cbn. lia. }
    split; [exact S0|].
    split. { eapply rw_cells_transport; [exact L16| exact MU| exact WM|]. rewrite LOCSV_size. cbn. lia. }
    split. { eapply stk_transport_disjoint; [exact STP| exact MU| exact WM|]. cbn. lia. }
    eapply rw_cells_transport; [exact SAVW| exact MU| exact WM|]. unfold SAVEDV. cbn. lia.
  Qed.

End PV.


End CeilWrap.
End CJ_pvalue_ctx.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ScWarm.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_pvalue_exit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ScWarm.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas CJ_pvalue_ctx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section PVX.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (g : lghost) (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (np B : Z) (CH : list (Z * Z * Z)).
  Variables (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure (PARSE_STACK depth) sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo.
  Hypothesis BPRE : pv_cost_pre (blen - off) <= B.
  Hypothesis CHOK : chain_ok (bv_unsigned sp + 16) CH (ASTACK_TOP sp0).
  Hypothesis CHL : chain_link (bv_unsigned s0) (bv_unsigned sp) CH.
  Hypothesis RA1 : 4096 <= bv_unsigned ra.
  Hypothesis RA2 : ~ is_pc0 (bv_unsigned ra).

  Notation SP := (bv_unsigned sp).
  Notation POST := (parse_value_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR LF np B CH U P CA blen off depth bs D n lo m g
                      nx pv ty p1 vi p2 vd ky).

  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC)
                 as (HPU & (HD & DCA & CAD) & LEN & BLEN & CEIL & BOT & LO & (PLF & PF1 & PF2 & PF3) & (SP1 & SP2 & SP3 & SP4 & SP5 & SP6)
                     & OFF & DEP & TP & (U1 & U2 & U3 & U4) & (D1 & D2 & D3 & D4) & UD & PU & PD & SPR & TOPR & BOTE);
               unfold PARSE_STACK in LO;
               pose proof (bv_unsigned_in_range 64 ra) as RAR; change (bv_modulus 64) with (2^64) in RAR;
               pose proof (bv_unsigned_in_range 64 s0) as S0R; change (bv_modulus 64) with (2^64) in S0R.
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_END; rewrite ?alloc_ceiling_eq; unfold PARSE_STRING_STACK, DELETE_STACK, POBJ_STACK, PARSE_STACK, ASTKMALLOC_STACK, AINTRIN_STACK, ASTRFN_STACK, AMALLOC_STACK; lia | sclr_tac2 ].
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac blia := unfold pv_cost_pre, PV_FRATE, PV_RATE in *; rewrite ?cost_free_eq in *; rewrite ?length_app in *; cbn [length] in *; unfold cblock in *; lia.

  Notation VSTx := (VST sp gp tp).
  Notation MIDVx := (MIDV AI TI sp m g sp0 SPB LR LF np CH P CA bs lo).
  Notation VGEOMx := (VGEOM sp LB LF P).
  Notation VRESx := (VRES LR B U blen off depth nx pv ty p1 vi p2 vd ky).
  Notation SAVEDVx := (SAVEDV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Hypothesis FLA : flag_apart_stmt AI.
  Notation NOT_FRSH := (pv_addr_not_frsh AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).
  Notation NOT_FLAG := (pv_addr_not_flag AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC FLA).
  Notation NOT_FRBODY := (pv_addr_not_frbody AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC).
  Notation VRES_MAGREE := (VRES_magree LR B U blen off depth nx pv ty p1 vi p2 vd ky).

  (* [comment removed for export] *)
  Lemma pv_exit : forall (SA Fr r : Z) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx (b : list byte) (h : word) (locs : list cell) (off' depth' : Z)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    VGEOMx SA Fr -> MIDVx SA Fr m1 mo1 g1 LBX TRS1 B1 errv1 ->
    SHCW m1 Fr b -> length b = 32%nat ->
    rw_cells asegs m1 Fr [C8 h] ->
    rw_cells asegs m1 SA locs -> SA + Z.of_nat (cells_size locs) = SP - 104 ->
    rw_cells asegs m1 (SP + -104) SAVEDVx ->
    Fagree F Fx -> frm0 fcx ->
    pbuf_at m1 P CA blen off' depth' ->
    VRESx m1 r LBX B1 off' depth' ->
    LSCPS asegs POST (VSTx SA Fr 0x83578 x1 x5 x6 x7 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD SHC LB32 HDR FRL SZL SAVW FA FRM PB RES. lits. bandM. sepM. unfold VST, SHV.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR'). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. unfold AERRNO, ATP in ERR. unfold SAVEDV in SAVW.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB.
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    (nelimp RES 3%nat; intros X HPX _).
    assert (INLR : forall b', In b' LR -> In b' LBX) by (intros b' Hb'; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb']).
    destruct b as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 [|b9 [|b10 [|b11 [|b12 [|b13 [|b14 [|b15
               [|b16 [|b17 [|b18 [|b19 [|b20 [|b21 [|b22 [|b23 [|b24 [|b25 [|b26 [|b27 [|b28 [|b29 [|b30 [|b31 [|? ?]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
      try (cbn in LB32; (cut_to LB32; (cut_to LB32; lia))).
    unfold SHCW in SHC. cbn [map] in SHC. clear LB32.
    (* [comment removed for export] *)
    assert (INF : In (Fr, 2) ((Fr, 2) :: LF)) by (left; reflexivity).
    destruct (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL INF) as (_ & _ & _ & _ & _ & _ & (fl & FLP & FLB & FLK & FLT) & FD).
    change (fsz 2) with 256 in FLP, FLT, FD. replace (Fr + 256 - 8) with (Fr + 248) in FLP by lia.
    pose proof (rw_cells_bound asegs _ _ _ FLB) as FLBB. cbn [cells_size Cells.csize Nat.add] in FLBB.
    pose proof (art_flag_high_holds AI _ _ _ _ _ _ _ _ _ Fr 2 fl HL INF ltac:(change (fsz 2) with 256; replace (Fr + 256 - 8) with (Fr + 248) by lia; exact FLP) ltac:(lia)) as FLHI.
    (* [comment removed for export] *)
    pose proof (ablk_img _ _ FLHI) as FLHIi. pose proof (ablk_top _ _ FLHI) as FLHIt. apply ablk_disj_band in FLHI. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLHIi, FLHI. bandM. sepM.
    pose proof FLP as FLR. change (cells_at asegs m1 (Fr + 248) [C8 (wz fl)]) with (ro_cells asegs m1 (Fr + 248) [C8 (wz fl)]) in FLR.
    eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    pose proof (munch_refl [(Z.shiftr Fr 3 + 2147450880, Z.shiftr Fr 3 + 2147450880 + 32)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    zstep. sepM. do 32 sbstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : ART AI sp0 SPB LBX ((Fr, 2) :: LF) TRS1 B1 m2 mo1 g1).
    { eapply (art_frame AI); [exact HL| exact MU| exact WM|]. constructor; [| constructor].
      do 9 right. exists Fr, 2. cbn. split; [left; reflexivity|]. rewrite <- SH_shiftr. change (fsz 2) with 256. lia. }
    assert (PQ2 : ppres sp0 LR LF SP P m1 m2).
    { eapply ppres_of_munch; [exact MU| exact WM|]. intros a Ha Hp. cbn. split; [| exact I].
      pose proof (NOT_FRSH Fr LBX m1 mo1 g1 TRS1 B1 SA a GE HL INLR Ha Hp) as NF. rewrite SHFR. unfold SH, SHADOW_OFFSET in NF. lia. }
    assert (MAB2 : magree (in_cblock LBX) m1 m2).
    { eapply magree_blocks_of_munch; [exact MU| exact WM|]. intros A n0 Hin. cbn.
      (* [comment removed for export] *)
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) 4%nat; intros _ _ R3 _).
      pose proof (art_block_sclr AI _ _ _ _ _ _ _ _ _ A n0 A (Z.max n0 1) HL Hin ltac:(lia) ltac:(lia)) as SC. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in SC. bandM. sepM.
      (nelimp GE 6%nat; intros _ _ FAL' FLO' FHI' _). unfold AIMG_HI in FLO'.
      pose proof (frame2_sh_band Fr FAL' ltac:(lia) FHI') as (FB1 & FB2).
      split; [clear - R3 SC FB1 FB2; lia| exact I]. }
    unfold pbuf_at in PB. eapply rw_cells_transport in PB; [| exact MU| exact WM| rewrite pbuf_cells_size; cbn [disjoint_from]; unfold SH, SHADOW_OFFSET in *; lia].
    clear MU WM HL.
    (* [comment removed for export] *)
    zstep. unfold wz.
    assert (FLP2 : cells_at asegs m2 (Fr + 248) [C8 (wz fl)]) by exact FLR.
    assert (NFL : forall a, 0 <= a < 2^64 -> pv_addr sp0 LR LF SP P a -> a <> fl).
    { intros a Ha Hp. eapply (NOT_FLAG Fr LBX m2 mo1 g1 TRS1 B1 SA fl a GE HL2 INLR FLP2 FLB FLK FLT Ha Hp). }
    pose proof (FLA _ _ _ _ _ _ _ _ _ Fr 2 fl (P - 32) 1 HL2 INF ltac:(change (fsz 2) with 256; replace (Fr + 256 - 8) with (Fr + 248) by lia; exact FLP2) ltac:(lia) ltac:(right; exact PLF)) as FLPB.
    pose proof (FLK D n (INLR _ HD)) as FLD.
    pose proof (munch_refl [(fl, fl + 1)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    sbstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : ART AI sp0 SPB LBX LF TRS1 B1 m3 mo1 g1).
    { enough (HL3' : ART AI sp0 SPB LBX (lf_remove Fr ((Fr, 2) :: LF)) TRS1 B1 m3 mo1 g1) by (cbn in HL3'; rewrite Z.eqb_refl in HL3'; exact HL3').
      eapply (art_ff_release AI); [exact HL2| exact INF| | exact MU| exact WM|].
      - change (fsz 2) with 256. replace (Fr + 256 - 8) with (Fr + 248) by lia. exact FLP2.
      - lazymatch goal with H : rw_cells asegs m3 fl _ |- _ => exact H end. }
    assert (PQ3 : ppres sp0 LR LF SP P m2 m3).
    { eapply ppres_of_munch; [exact MU| exact WM|]. intros a Ha Hp. cbn. split; [| exact I]. pose proof (NFL a Ha Hp) as NF. lia. }
    assert (MAB3 : magree (in_cblock LBX) m2 m3).
    { eapply magree_blocks_of_munch; [exact MU| exact WM|]. intros A n0 Hin. cbn. destruct (FLK A n0 Hin); (split; [lia| exact I]). }
    pose proof (ppres_trans _ _ _ _ _ _ _ _ PQ2 PQ3) as PQ13.
    clear MU WM HL2 PQ2 PQ3 FLP2 FLR NFL.
    (* [comment removed for export] *)
    zstep. zstep. do 13 zstep. zstep. zstep.
    eapply stk_release in FRL; [| exact ST| lia]. rewrite SZL in FRL.
    replace (SP - 104) with (SP + -104) in FRL by lia.
    release_frame SAVW FRL (bv_unsigned sp).
    apply evt_done. apply lscps_done.
    (* [comment removed for export] *)
    assert (PSH3 : pbuf_sh m3 P) by (eapply ppres_pbuf_sh; [exact PQ13| exact PSH| exact PLF| unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| try rewrite alloc_ceiling_eq; lia| first [unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| sclr_tac2] (* [comment removed for export] *)]).
    assert (CC3 : chain_cells m3 CH).
    { eapply chain_cells_ext; [exact CC| exact CHOK|]. intros a Ha.
      destruct (PQ13 a ltac:(lia)) as [E _]; [| exact E]. split; [left; lia|]. unfold AERRNO, ATP. lia. }
    pose proof (VRES_MAGREE _ _ _ _ _ _ _ (VRES_MAGREE _ _ _ _ _ _ _ RES MAB2) MAB3) as RES3.
    (nelim RES3 3%nat; intros X3 HPX3 RR).
    unfold parse_value_post. nexists 15%nat. exists Fx, fcx, m3, r, off', depth', LBX, X3, TRS1, B1, errv1.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FA|]. split; [exact FRM|].
    split.
    { split; [exact HL3|]. split; [exact HPX3|]. split; [exact HD|]. split; [lia|]. split; [lia|]. split; [exact BY|].
      split; [exact LEN|]. split; [exact BLEN|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI|]. split; [exact FRL|].
      split; [try rewrite alloc_ceiling_eq; lia|]. split; [exact TV|]. split; [exact PLF|]. split; [exact PSH3|]. repeat split; assumption || lia. }
    split; [eapply ppres_trans; [exact PR| exact PQ13]|]. split; [exact GM|]. split; [exact CC3|]. split; [unfold pbuf_at; exact PB|].
    exact RR.
  Qed.

  (* [comment removed for export] *)
  Definition MAGIC_SITES : list Z := [0x82edc; 0x82f24; 0x82f6c; 0x830dc; 0x83140; 0x832a8; 0x833b8; 0x833e0; 0x83568; 0x836a0].

  Lemma magic_exit : forall (pc SA Fr r : Z) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx (b : list byte) (h : word) (locs : list cell) (off' depth' : Z)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    In pc MAGIC_SITES ->
    VGEOMx SA Fr -> MIDVx SA Fr m1 mo1 g1 LBX TRS1 B1 errv1 ->
    SHCW m1 Fr b -> length b = 32%nat ->
    rw_cells asegs m1 Fr [C8 h] ->
    rw_cells asegs m1 SA locs -> SA + Z.of_nat (cells_size locs) = SP - 104 ->
    rw_cells asegs m1 (SP + -104) SAVEDVx ->
    Fagree F Fx -> frm0 fcx ->
    pbuf_at m1 P CA blen off' depth' ->
    VRESx m1 r LBX B1 off' depth' ->
    LSCPS asegs POST (VSTx SA Fr pc x1 x5 x6 x7 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros HPC GE MD SHC LB32 HDR FRL SZL SAVW FA FRM PB RES. lits. bandM. sepM. unfold VST, SHV.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR'). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. unfold AERRNO, ATP in ERR. unfold SAVEDV in SAVW.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. unfold pbuf_at in PB.
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    (nelimp RES 3%nat; intros X HPX _).
    assert (INLR : forall b', In b' LR -> In b' LBX) by (intros b' Hb'; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb']).
    (nelim (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity)) 8%nat; intros _ _ _ _ _ _ _ FD). change (fsz 2) with 256 in FD.
    pose proof (FD D n (INLR _ HD)) as FDD.
    unfold SHCW in SHC. pose proof (rw_cells_bound asegs _ _ _ SHC) as SHB. rewrite cells_size_mapC1, LB32 in SHB.
    assert (GO : forall x11' m2, munch [(Fr, Fr + 8)] m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 ->
      rw_cells asegs m2 Fr [C8 x11'] ->
      LSCPS asegs POST (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 r) x11' x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 Fr) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (Z.shiftr Fr 3 + 2147450880)) (Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
            Fx (Z_to_bv 64 0x83578) fcx None m2 (seg_rom asegs)) mo1 g1).
    { intros x11' m2 MU WM MI2 HDR2.
      pose proof SHC as SHC2. eapply rw_cells_transport in SHC2; [| exact MU| exact WM| rewrite cells_size_mapC1, LB32; cbn [disjoint_from]; unfold SH, SHADOW_OFFSET in *; lia].
      pose proof FRL as FRL2. eapply rw_cells_transport in FRL2; [| exact MU| exact WM| cbn [disjoint_from]; lia].
      pose proof SAVW as SAVW2. eapply rw_cells_transport in SAVW2; [| exact MU| exact WM| cbn [disjoint_from cells_size Cells.csize Nat.add]; lia].
      pose proof PB as PB2. eapply rw_cells_transport in PB2; [| exact MU| exact WM| rewrite pbuf_cells_size; cbn [disjoint_from]; lia].
      pose proof BY as BY2. eapply bytes_at_transport in BY2; [| exact MU| cbn [disjoint_from]; lia].
      pose proof ERR as ERR2. eapply rw_cells_transport in ERR2; [| exact MU| exact WM| cbn [disjoint_from cells_size Cells.csize Nat.add]; lia].
      pose proof ST as ST2. eapply stk_transport_disjoint in ST2; [| exact MU| exact WM| cbn [disjoint_from]; lia].
      assert (HL2 : ART AI sp0 SPB LBX ((Fr, 2) :: LF) TRS1 B1 m2 mo1 g1).
      { eapply (art_frame AI); [exact HL| exact MU| exact WM|]. constructor; [| constructor].
        do 8 right. left. exists Fr, 2. cbn. split; [left; reflexivity|]. change (fsz 2) with 256. lia. }
      assert (PQ : ppres sp0 LR LF SP P m1 m2).
      { eapply ppres_of_munch; [exact MU| exact WM|]. intros a Ha Hp. cbn. split; [| exact I].
        pose proof (NOT_FRBODY Fr LBX m1 mo1 g1 TRS1 B1 SA a GE HL INLR Ha Hp). lia. }
      assert (MAB : magree (in_cblock LBX) m1 m2).
      { eapply magree_blocks_of_munch; [exact MU| exact WM|]. intros A n0 Hin. cbn. destruct (FD A n0 Hin); (split; [lia| exact I]). }
      eapply (pv_exit SA Fr r m2 mo1 g1 LBX TRS1 B1 errv1 Fx fcx b x11' locs off' depth');
        [exact GE| | unfold SHCW; exact SHC2| exact LB32| exact HDR2| exact FRL2| exact SZL| unfold SAVEDV; exact SAVW2| exact FA| exact FRM
        | unfold pbuf_at; exact PB2| eapply VRES_MAGREE; [exact RES| exact MAB]].
      split; [exact HL2|]. split; [exact BY2|]. split; [unfold AERRNO, ATP; exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
      split; [eapply ppres_trans; [exact PR| exact PQ]|]. split; [exact GM|]. split; [exact TV|].
      split; [eapply pbuf_sh_munch; [exact PSH| exact MU| lia| lia| pbuf_dj (* [comment removed for export] *)]|].
      eapply chain_cells_munch; [exact CC| exact CHOK| exact MU| lia| lia|]. intros lo' hi' [E|[]]. inversion E; subst. left. lia. }
    unfold MAGIC_SITES in HPC.
    sc_prewarm HDR.   (* [comment removed for export] *)
    sepM. sepM. destruct HPC as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
      (eapply lscps_step_evt; cbv beta delta [mkR];
       pose proof (munch_refl [(Fr, Fr + 8)] m1) as MU; pose proof (wmono_refl asegs m1) as WM;
       zstep; zstep; zstep; fix_lit_store;
       zstep; (if_cases K; zify_cond K; try (exfalso; (cut_to FLO K; lia)));
       apply evt_done; eapply GO; [exact MU| exact WM| exact MI| exact HDR]).
  Qed.
End PVX.


End CeilWrap.
End CJ_pvalue_exit.

(* [comment removed for export] *)
Module CJ_pvalue_A1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas CJ_pvalue_ctx CJ_pvalue_exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section PVA1.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (g : lghost) (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (np B : Z) (CH : list (Z * Z * Z)).
  Variables (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure (PARSE_STACK depth) sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo.
  Hypothesis BPRE : pv_cost_pre (blen - off) <= B.
  Hypothesis CHOK : chain_ok (bv_unsigned sp + 16) CH (ASTACK_TOP sp0).
  Hypothesis CHL : chain_link (bv_unsigned s0) (bv_unsigned sp) CH.
  Hypothesis RA1 : 4096 <= bv_unsigned ra.
  Hypothesis RA2 : ~ is_pc0 (bv_unsigned ra).
  Hypothesis FLA : flag_apart_stmt AI.
  Hypothesis STPV : forall b, STAT TI (pv_trace (bv_unsigned ra) CH b).
  Hypothesis STPO : forall b, STAT TI (tr_pv_pobj b).
  Hypothesis STC : Forall (STAT TI) (S_PARSE_CONST ++ S_DELETE).
  Hypothesis LFR : lf_room 2 LF (1001 - depth).
  Variable nfuel : nat.
  Hypothesis FUEL : blen - off <= Z.of_nat nfuel.

  Notation SP := (bv_unsigned sp).
  Notation POST := (parse_value_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR LF np B CH U P CA blen off depth bs D n lo m g
                      nx pv ty p1 vi p2 vd ky).
  Notation VSTx := (VST sp gp tp).
  Notation MID := (MIDV AI TI sp m g sp0 SPB LR LF np CH P CA bs lo).
  Notation VFRx := (VFR ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P).
  Notation VGEOMx := (VGEOM sp LB LF P).
  Notation VRESx := (VRES LR B U blen off depth nx pv ty p1 vi p2 vd ky).
  Notation MAGIC_EXIT := (magic_exit AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK FLA).
  Notation DCH := (dch depth).

  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC)
                 as (HPU & (HD & DCA & CAD) & LEN & BLEN & CEIL & BOT & LO & (PLF & PF1 & PF2 & PF3) & (SP1 & SP2 & SP3 & SP4 & SP5 & SP6)
                     & OFF & DEP & TP & (U1 & U2 & U3 & U4) & (D1 & D2 & D3 & D4) & UD & PU & PD & SPR & TOPR & BOTE);
               unfold PARSE_STACK in LO;
               pose proof (bv_unsigned_in_range 64 ra) as RAR; change (bv_modulus 64) with (2^64) in RAR;
               pose proof (bv_unsigned_in_range 64 s0) as S0R; change (bv_modulus 64) with (2^64) in S0R.
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_END; rewrite ?alloc_ceiling_eq; unfold PARSE_STRING_STACK, DELETE_STACK, POBJ_STACK, PARSE_STACK, ASTKMALLOC_STACK, AINTRIN_STACK, ASTRFN_STACK, AMALLOC_STACK; lia | sclr_tac2 ].
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac blia := unfold pv_cost_pre, pstr_cost_pre, pstr_fail_cost, PV_FRATE, PV_RATE in *; rewrite ?cost_free_eq in *; rewrite ?length_app in *; cbn [length] in *; unfold cblock in *; lia.

  Hypothesis DEL : cjson_delete_stmt AI TI.

  Lemma sconst_del : Forall (STAT TI) S_DELETE.
  Proof. pose proof STC as SC. apply Forall_app in SC. destruct SC as [_ SD]. exact SD. Qed.

  (* [comment removed for export] *)
  Lemma arr_fail_delete : forall (SA Fr head : Z) (X : list cblock) (dd : nat) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h jae jn cs08 lj (off1 depth1 : Z)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_ANY m1 dd head X -> Z.of_nat dd <= 1000 - depth ->
    VFRx SA Fr m1 shb h jae jn cs08 lj ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    B - pv_cost_pre (blen - off) + cost_free * Z.of_nat (length X) <= B1 ->
    LSCPS asegs POST (VSTx SA Fr 0x83698 x1 x5 x6 x7 (Z_to_bv 64 head) x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD HPX CHN Hdd VF PB ND FA FRM HB. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    (nelimp VF 3%nat; intros _ L32 _).
    assert (HPX' : Permutation (X ++ (U, 64) :: LR) LBX).
    { eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply Permutation_middle. }
    assert (B0 : 0 <= B - pv_cost_pre (blen - off)) by (clear -BPRE OFF; unfold pv_cost_pre, PV_FRATE, PV_RATE, cost_free in *; lia).
    assert (INL : forall b, In b LR -> In b ((U, 64) :: LR)) by (intros b Hb; right; exact Hb).
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. change (Z_to_bv 64 533880) with (wz DELETE_ENTRY).
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { pose proof (DEL dd) as DS. unfold delete_spec_at in DS.
      eapply DS with (lo := lo); clear DS; rewrite ?unsigned_lit by (lia_on Hdd CEIL LO PF1 SP4 SP5 U1 D1 TOPR GSA FLO);
        first [ exact HL | exact CHN | exact HPX' | exact ST | exact ERR | exact MI | exact TP | exact TV | exact sconst_del | reflexivity
              | rewrite cost_free_eq in *; (cut_to Hdd CEIL LO PF1 SP2 U1 D1 GSA FLO SP5 SP4 DEP GAL BOT HB B0; (cut_to Hdd CEIL LO SP2 GSA SP5 SP4 DEP GAL BOT HB B0; lia))
              | alia
              | Z.div_mod_to_equations; lia ]. }
    cbv beta. intros ms2 mo2 g2 PO'.
    (nelim PO' 27%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LR2 TRS2 -> MI2 ST2 ERR2 HL2 HP2 TV2 GM2 PR2)
.
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x8369c)) with (Z_to_bv 64 0x8369c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (VFR_cj_pres ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC SA Fr m1 m2 shb h jae jn cs08 lj _ GE VF PR2) as VF2.
    (nelim (VFR_locs ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P SA Fr m2 shb h jae jn cs08 lj VF2 ltac:(lia)) 3%nat; intros locs FRL SZL).
    (nelimp VF2 10%nat; intros SHC2 _ HDR2 _ _ _ _ _ _ SAVW2).
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in ND; [| do 3 right; left; exists U, 64; rewrite node_cells_size; split; [left; reflexivity| lia]].
    pose proof PB as PB2. unfold pbuf_at in PB2.
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in PB2; [| do 4 right; left; exists (P - 32), 1; split; [right; exact PLF| rewrite pbuf_cells_size; change (fsz 1) with 128; lia]].
    apply (cj_pres_bytes_at _ _ _ _ _ _ _ _ PR2) in BY; [| do 3 right; left; exists D, n; rewrite LEN; split; [right; exact HD| lia]].
    assert (PSH2 : pbuf_sh m2 P).
    { apply (ppres_pbuf_sh sp0 LR ((Fr, 2) :: LF) SA P m1 m2); [| exact PSH| right; exact PLF| alia| alia| alia (* [comment removed for export] *)].
      eapply ppres_of_cj_pres; [exact PR2| lia| exact INL]. }
    assert (CC2 : chain_cells m2 CH).
    { eapply chain_cells_cj_pres; [exact CC| exact CHOK| exact PR2| lia| lia| lia]. }
    assert (PR3 : ppres sp0 LR LF SP P m m2).
    { eapply ppres_trans; [exact PR|].
      eapply ppres_weaken; [eapply ppres_of_cj_pres; [exact PR2| apply Z.le_refl| exact INL]| lia| intros b' Hb'; exact Hb'| intros f Hf; right; exact Hf]. }
    eapply lscps_step_evt. cbv beta delta [mkR]. zstep.
    apply evt_done. eapply (MAGIC_EXIT 0x836a0 SA Fr 0 m2 mo2 g2 LR2 TRS2 (B1 - cost_free * Z.of_nat (length X)) errv1 Fx fcx shb h locs off1 depth1);
      [cbn; (cut_on [OFF DEP SPR TOPR BOTE RAR S0R BMf BMf0 BMf1 SMf SMf0 SMf1 GSA FLO BMf2 SMf2 PBB NDB] tauto)| exact GE| | exact SHC2| exact L32| exact HDR2| exact FRL| lia| exact SAVW2| exact FA| exact FRM| unfold pbuf_at; exact PB2|].
    - split; [exact HL2|]. split; [exact BY|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
      split; [exact PR3|].
      split; [eapply gmono_trans; [exact GM| exact GM2]|]. split; [exact TV2|]. split; [exact PSH2| exact CC2].
    - exists []. split; [apply Permutation_sym; exact HP2|]. left. split; [reflexivity|]. split; [reflexivity|]. split; [exact ND|].
      rewrite cost_free_eq in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma arr_fail_c8 : forall (SA Fr head : Z) (X : list cblock) (dd : nat) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h jae jn cs08 lj (off1 depth1 : Z)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_ANY m1 dd head X -> Z.of_nat dd <= 1000 - depth ->
    VFRx SA Fr m1 shb h jae jn cs08 lj ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    B - pv_cost_pre (blen - off) + cost_free * Z.of_nat (length X) <= B1 ->
    LSCPS asegs POST (VSTx SA Fr 0x8355c x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 head) x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD HPX CHN Hdd VF PB ND FA FRM HB. lits. bandM. sepM.
    (nelimp (cj_chain_ptr_range _ _ _ _ _ CHN) 3%nat; intros Hh0 _ Hh2).
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. if_cases Kh; zify_cond Kh.
    - apply evt_done. eapply arr_fail_delete; eassumption.
    - (* [comment removed for export] *)
      assert (X = []) as -> by (eapply cj_chain_null_inv; rewrite <- Kh; exact CHN).
      (nelimp VF 10%nat; intros SHC L32 HDR _ _ _ _ _ _ SAVW).
      (nelim (VFR_locs ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P SA Fr m1 shb h jae jn cs08 lj VF ltac:(destruct GE; lia)) 3%nat; intros locs FRL SZL).
      zstep. apply evt_done.
      eapply (MAGIC_EXIT 0x83568 SA Fr 0 m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h locs off1 depth1);
        [cbn; (cut_on [OFF DEP SPR TOPR BOTE RAR S0R BMf BMf0 BMf1 SMf SMf0 SMf1] tauto)| exact GE| exact MD| exact SHC| exact L32| exact HDR| exact FRL| destruct GE; lia| exact SAVW| exact FA| exact FRM| exact PB|].
      exists []. split; [exact HPX|]. left. split; [reflexivity|]. split; [reflexivity|]. split; [exact ND| rewrite cost_free_eq in *; cbn [length Z.of_nat] in HB; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma arr_fail_00 : forall (SA Fr head : Z) (X : list cblock) (dd : nat) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h jae jn cs08 lj (off1 depth1 : Z)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_ANY m1 dd head X -> Z.of_nat dd <= 1000 - depth ->
    VFRx SA Fr m1 shb h jae jn cs08 lj ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    B - pv_cost_pre (blen - off) + cost_free * Z.of_nat (length X) <= B1 ->
    LSCPS asegs POST (VSTx SA Fr 0x83694 x1 x5 x6 x7 x10 x11 x12 x13 x14 (Z_to_bv 64 head) x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD HPX CHN Hdd VF PB ND FA FRM HB.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. apply evt_done. eapply arr_fail_delete; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma arr_fail_74 : forall (SA Fr head : Z) (X : list cblock) (dd : nat) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h jae jn cs08 lj (off1 depth1 : Z)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_ANY m1 dd head X -> Z.of_nat dd <= 1000 - depth ->
    VFRx SA Fr m1 shb h jae jn cs08 lj ->
    pbuf_at m1 P CA blen off1 depth1 ->
    rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    Fagree F Fx -> frm0 fcx ->
    B - pv_cost_pre (blen - off) + cost_free * Z.of_nat (length X) <= B1 ->
    LSCPS asegs POST (VSTx SA Fr 0x83608 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 head) x20 x21 x22 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD HPX CHN Hdd VF PB ND FA FRM HB.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. apply evt_done. eapply arr_fail_delete; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma VFR_munch : forall SA Fr m1 m2 shb h jae jn cs08 lj W,
    VGEOMx SA Fr -> VFRx SA Fr m1 shb h jae jn cs08 lj -> munch W m1 m2 -> wmono asegs m1 m2 ->
    (forall lo' hi', In (lo', hi') W -> (alloc_ceiling <= lo' /\ hi' <= SA) \/ (AIMG_HI <= lo' /\ hi' <= alloc_ceiling /\ (hi' <= Fr \/ Fr + 256 <= lo') /\ sclr lo' (hi' - lo'))) ->   (* [comment removed for export] *)
    VFRx SA Fr m2 shb h jae jn cs08 lj.
  Proof.
    intros SA Fr m1 m2 shb h jae jn cs08 lj W (GSA & GAL & FAL & FLO & FHI & FBLK & FNEW & PFR') (SHC & L32 & HDR & AE & NC & L0 & S0 & L16 & STP & SAVW) MU WM HW. lits. bandM. sepM.
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO, HW. bandM. sepM. try rewrite alloc_ceiling_eq in FHI, HW. pose proof (SH_bounds Fr ltac:(lia)) as SB.
    pose proof (SH_bounds (Fr + 255) ltac:(lia)) as SB2. rewrite (SH_aligned_add Fr 255) in SB2 by first [mod8 | (Z.div_mod_to_equations; lia)]. change (255 / 8) with 31 in SB2.
    assert (DJ : forall A k, 0 <= k -> ((SA <= A /\ A + k <= SP) \/ (Fr <= A /\ A + k <= Fr + 256) \/ (A = SH Fr /\ k = 32)) -> disjoint_from W A k).
    { pose proof (frame2_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2). rewrite SH_shiftr in FB1, FB2.
      clear - HW SB SB2 CEIL LO GSA FHI FLO DEP FB1 FB2. intros A k Hk HA. revert HW. induction W as [|[lo' hi'] W IH]; intros HW; [exact I|]. cbn. split.
      - destruct (HW lo' hi' ltac:(left; reflexivity)) as [[H1 H2]|(H1 & H2 & H3)]; lia.
      - apply IH. intros lo2 hi2 Hin. apply HW. right. exact Hin. }
    split. { unfold SHCW in *. eapply rw_cells_transport; [exact SHC| exact MU| exact WM|]. rewrite cells_size_mapC1, L32, SH_shiftr. apply DJ; [lia|]. right; right. split; [reflexivity| reflexivity]. }
    split; [exact L32|].
    split. { eapply rw_cells_transport; [exact HDR| exact MU| exact WM|]. apply DJ; cbn; lia. }
    split. { eapply rw_cells_transport; [exact AE| exact MU| exact WM|]. apply DJ; cbn; lia. }
    split. { eapply rw_cells_transport; [exact NC| exact MU| exact WM|]. apply DJ; cbn; lia. }
    split. { eapply rw_cells_transport; [exact L0| exact MU| exact WM|]. apply DJ; rewrite ?S0; cbn; lia. }
    split; [exact S0|].
    split. { eapply rw_cells_transport; [exact L16| exact MU| exact WM|]. apply DJ; rewrite LOCSV_size; cbn; lia. }
    split. { eapply stk_transport_disjoint; [exact STP| exact MU| exact WM|]. apply DJ; lia. }
    eapply rw_cells_transport; [exact SAVW| exact MU| exact WM|]. apply DJ; cbn; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma arr_success : forall (SA Fr o2 head : Z) (X : list cblock) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h jae jn cs08 lj
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x19 x22 x23 x24 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((U, 64) :: X ++ LR) LBX ->
    cj_chain CJ_PRINTABLE m1 (S DCH) head X -> depth <= 999 ->
    VFRx SA Fr m1 shb h jae jn cs08 lj ->
    pbuf_at m1 P CA blen o2 depth ->
    rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off <= o2 < blen -> Fagree F Fx -> frm0 fcx ->
    B - PV_RATE * (o2 + 1 - off) <= B1 -> Z.of_nat (length X) <= o2 + 1 - off ->
    LSCPS asegs POST (VSTx SA Fr 0x8309c x1 x5 x6 x7 x10 x11 x12 x13 x14 (Z_to_bv 64 head) x16 x17 x19 (Z_to_bv 64 U) (Z_to_bv 64 P) x22 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD HPX CHN Hd VF PB ND Ho FA FRM HB HX. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    (nelimp VF 10%nat; intros _ L32 _ _ _ _ _ L16 _ _). unfold LOCSV, SHV in L16.
    unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND.
    assert (INU : In (U, 64) LBX) by (eapply perm_in_head; exact HPX).
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]).
    pose proof (FBLK U 64 ltac:(eapply perm_in_head; exact HPU)) as FUU.
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL INU) as SOU.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    pose proof (munch_refl [(U + 16, U + 28)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    zstep. zstep. fix_lit_store.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1a end.
    assert (SOUa : shadow_ok m1a U 64) by (eapply shadow_ok_high_store; [exact SOU| exact MU| lia| alia| lia| alia]).
    pose proof (shadow_ok_shchk m1a U 64 (U + 16) 8 SOUa ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; (lia_on U2 H H0 H24))) as CK8. asan_chk CK8.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : ART AI sp0 SPB LBX ((Fr, 2) :: LF) TRS1 B1 m2 mo1 g1) by (eapply (art_block_store AI); [exact HL| exact INU| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres sp0 LR LF SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply (ppres_weaken sp0 LR LR ((Fr, 2) :: LF) LF SA SP P); [| lia| intros b' Hb'; exact Hb'| intros f Hf; right; exact Hf].
      eapply (ppres_block_store AI); [exact HL| exact HPX| intros b Hb; apply in_or_app; right; exact Hb| alia| lia| exact MU| exact WM| lia| lia]. }
    assert (PSH2 : pbuf_sh m2 P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU| alia| alia| alia]).
    assert (CH2 : cj_chain CJ_PRINTABLE m2 (S DCH) head X).
    { eapply cj_chain_frame; [exact CHN| exact MU| exact WM|].
      intros A k Hin. cbn. split; [|exact I].
      destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL HPX A k ltac:(apply in_or_app; left; exact Hin)) as [_ DJ]. (lia_on DJ). }
    assert (CC2 : chain_cells m2 CH).
    { eapply chain_cells_munch; [exact CC| exact CHOK| exact MU| lia| lia|]. intros lo' hi' [E|[]]. inversion E; subst. left. lia. }
    assert (VF2 : VFRx SA Fr m2 shb h jae jn cs08 lj).
    { eapply VFR_munch; [exact GE| exact VF| exact MU| exact WM|]. intros lo' hi' [E|[]]. inversion E; subst. right. repeat split; alia. }
    clear MU WM HL PR PSH CHN CC SOU SOUa VF.
    (* [comment removed for export] *)
    pose proof (munch_refl [(P + 16, P + 24)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep. pose proof (sh_zero_shb m2 P (P + 56) (P + 16) PSH2 ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : ART AI sp0 SPB LBX ((Fr, 2) :: LF) TRS1 B1 m3 mo1 g1) by (eapply (art_pbuf_store AI); [exact HL2| right; exact PLF| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres sp0 LR LF SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply ppres_pbuf_store; [exact MU| exact WM| lia| lia]. }
    assert (PSH3 : pbuf_sh m3 P) by (eapply pbuf_sh_high_store; [exact PSH2| exact MU| alia| alia| alia]).
    assert (CH3 : cj_chain CJ_PRINTABLE m3 (S DCH) head X).
    { eapply cj_chain_frame; [exact CH2| exact MU| exact WM|].
      intros A k Hin. cbn. split; [|exact I].
      (nelim (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL2 ltac:(right; exact PLF)) 8%nat; intros _ _ _ _ _ _ _ FD).
      destruct (FD A k ltac:(eapply Permutation_in; [exact HPX| right; apply in_or_app; left; exact Hin])); change (fsz 1) with 128 in *; lia. }
    assert (CC3 : chain_cells m3 CH).
    { eapply chain_cells_munch; [exact CC2| exact CHOK| exact MU| lia| lia|]. intros lo' hi' [E|[]]. inversion E; subst. left. lia. }
    assert (VF3 : VFRx SA Fr m3 shb h jae jn cs08 lj).
    { eapply VFR_munch; [exact GE| exact VF2| exact MU| exact WM|]. intros lo' hi' [E|[]]. inversion E; subst. right. repeat split; alia. }
    clear MU WM HL2 PR2 PSH2 CH2 CC2 VF2.
    zstep.
    (nelim (VFR_locs ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P SA Fr m3 shb h jae jn cs08 lj VF3 ltac:(lia)) 3%nat; intros locs FRL SZL).
    (nelim VF3 10%nat; intros SHC3 _ HDR3 _ _ _ _ _ _ SAVW3).
    apply evt_done. eapply (MAGIC_EXIT 0x830dc SA Fr 1 m3 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h locs (o2 + 1) depth);
      [cbn; (cut_on [Ho OFF DEP SPR TOPR BOTE RAR S0R BMf BMf0 BMf1 SMf SMf0 SMf1 GSA FLO BMf2 SMf2 BYB PBB NDB FUU] tauto)| exact GE| | exact SHC3| exact L32| exact HDR3| exact FRL| lia| exact SAVW3| exact FA| exact FRM| unfold pbuf_at, pbuf_cells, wz; eqcells PB|].
    - split; [exact HL3|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI|]. split; [exact ST|].
      split; [exact PR3|]. split; [exact GM|]. split; [exact TV|]. split; [exact PSH3| exact CC3].
    - exists X. split; [exact HPX|]. right. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact HB|]. split; [exact HX|].
      exists head, 32, 0. do 2 eexists. exists (S DCH), [], X. split; [reflexivity|].
      split; [eqcells ND|]. split; [cbn; auto 10|]. split; [apply cj_str_null|]. split; [exact CH3|]. unfold dch. lia.
  Qed.

  (* [comment removed for export] *)
  Definition arr_inv (m1 : word -> option byte) (head cur : Z) (X : list cblock) : Prop :=
    (head = 0 /\ X = [])
    \/ (head <> 0 /\ cur <> 0 /\ exists B1 Bv Bc (chc tyc vsc : Z) (pvc p1c vic p2c vdc : word),
          X = B1 ++ (cur, 64) :: Bv ++ Bc
          /\ cj_lseg CJ_PRINTABLE m1 DCH head cur B1
          /\ rw_cells asegs m1 cur (node_cells 0 pvc chc tyc p1c vsc vic p2c vdc 0)
          /\ CJ_PRINTABLE tyc /\ cj_str m1 vsc Bv /\ cj_chain CJ_PRINTABLE m1 DCH chc Bc).

  Lemma arr_inv_chain : forall m1 head cur X, arr_inv m1 head cur X -> cj_chain CJ_PRINTABLE m1 (S DCH) head X.
  Proof.
    intros m1 head cur X [[-> ->]|(NZ & NZc & B1 & Bv & Bc & chc & tyc & vsc & pvc & p1c & vic & p2c & vdc & -> & SEG & ND & TY & SV & CHc)].
    - apply cj_chain_nil.
    - apply cj_lseg_chain0. replace (Bv ++ Bc) with (Bv ++ [] ++ Bc) by reflexivity.
      eapply cj_lseg_snoc; eauto using cj_str_null. apply CJ_PRINTABLE_range. exact TY.
  Qed.

  Lemma arr_inv_magree : forall m1 m2 head cur X, arr_inv m1 head cur X -> magree (in_cblock X) m1 m2 -> arr_inv m2 head cur X.
  Proof.
    intros m1 m2 head cur X [[-> ->]|(NZ & NZc & B1 & Bv & Bc & chc & tyc & vsc & pvc & p1c & vic & p2c & vdc & -> & SEG & ND & TY & SV & CHc)] MA.
    - left. auto.
    - right. split; [exact NZ|]. split; [exact NZc|]. exists B1, Bv, Bc, chc, tyc, vsc, pvc, p1c, vic, p2c, vdc. split; [reflexivity|].
      split. { eapply cj_lseg_magree; [exact SEG| exact MA|]. intros a Ha. rewrite in_cblock_app. left. exact Ha. }
      split. { eapply rw_cells_magree; [exact MA| exact ND|]. rewrite node_cells_size. intros a Ha. rewrite in_cblock_app, in_cblock_cons. right. left. lia. }
      split; [exact TY|].
      split. { eapply cj_str_magree; [exact MA| exact SV|]. intros a Ha. rewrite in_cblock_app, in_cblock_cons, in_cblock_app. right. right. left. exact Ha. }
      eapply cj_chain_magree; [exact CHc| exact MA|]. intros a Ha. rewrite in_cblock_app, in_cblock_cons, in_cblock_app. right. right. right. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Definition CS08 : list cell := [C8 (SHV (P + 32)); C8 (Z_to_bv 64 (P + 32))].

  (* [comment removed for export] *)
  Definition ALOOP (c : nat) : Prop :=
    forall (SA Fr o head cur : Z) (X : list cblock) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h jae jn lj
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o < blen -> depth <= 999 ->
      VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((U, 64) :: X ++ LR) LBX -> arr_inv m1 head cur X ->
      VFRx SA Fr m1 shb h jae jn CS08 lj ->
      pbuf_at m1 P CA blen o (depth + 1) ->
      rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      B - PV_RATE * (o - off) <= B1 -> Z.of_nat (length X) <= o - off ->
      LSCPS asegs POST (VSTx SA Fr 0x83420 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 head) x20 (Z_to_bv 64 P)
                             (Z_to_bv 64 (P + 24)) (SHV (P + 24)) (Z_to_bv 64 cur) x28 x29 x30 x31 Fx fcx m1) mo1 g1.
End PVA1.


End CeilWrap.
End CJ_pvalue_A1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_conv CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pvalue_lemmas ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_ctx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas.
Import CJ_pvalue_ctx.
Import CJ_pvalue_exit.
Import CJ_pvalue_A1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pstrA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section PVA2.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word).
  Variables (m : word -> option byte) (g : lghost) (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (np B : Z) (CH : list (Z * Z * Z)).
  Variables (U P CA blen off depth : Z) (bs : list byte) (D n lo : Z).
  Variables (nx : Z) (pv : word) (ty : Z) (p1 : word) (vi p2 vd : word) (ky : Z).
  Hypothesis PVC : pv_pure (PARSE_STACK depth) sp tp sp0 SPB LB LR LF U P CA blen off depth bs D n lo.
  Hypothesis BPRE : pv_cost_pre (blen - off) <= B.
  Hypothesis CHOK : chain_ok (bv_unsigned sp + 16) CH (ASTACK_TOP sp0).
  Hypothesis CHL : chain_link (bv_unsigned s0) (bv_unsigned sp) CH.
  Hypothesis RA1 : 4096 <= bv_unsigned ra.
  Hypothesis RA2 : ~ is_pc0 (bv_unsigned ra).
  Hypothesis FLA : flag_apart_stmt AI.
  Hypothesis STPV : forall b, STAT TI (pv_trace (bv_unsigned ra) CH b).
  Hypothesis STPO : forall b, STAT TI (tr_pv_pobj b).
  Hypothesis STC : Forall (STAT TI) (S_PARSE_CONST ++ S_DELETE).
  Hypothesis LFR : lf_room 2 LF (1001 - depth).
  Variable nfuel : nat.
  Hypothesis FUEL : blen - off <= Z.of_nat nfuel.

  Notation SP := (bv_unsigned sp).
  Notation POST := (parse_value_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR LF np B CH U P CA blen off depth bs D n lo m g
                      nx pv ty p1 vi p2 vd ky).
  Notation VSTx := (VST sp gp tp).
  Notation MID := (MIDV AI TI sp m g sp0 SPB LR LF np CH P CA bs lo).
  Notation VFRx := (VFR ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 U P).
  Notation VGEOMx := (VGEOM sp LB LF P).
  Notation VRESx := (VRES LR B U blen off depth nx pv ty p1 vi p2 vd ky).
  Notation DCH := (dch depth).
  Notation CS08x := (CS08 P).

  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC)
                 as (HPU & (HD & DCA & CAD) & LEN & BLEN & CEIL & BOT & LO & (PLF & PF1 & PF2 & PF3) & (SP1 & SP2 & SP3 & SP4 & SP5 & SP6)
                     & OFF & DEP & TP & (U1 & U2 & U3 & U4) & (D1 & D2 & D3 & D4) & UD & PU & PD & SPR & TOPR & BOTE);
               unfold PARSE_STACK in LO;
               pose proof (bv_unsigned_in_range 64 ra) as RAR; change (bv_modulus 64) with (2^64) in RAR;
               pose proof (bv_unsigned_in_range 64 s0) as S0R; change (bv_modulus 64) with (2^64) in S0R.
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_END; rewrite ?alloc_ceiling_eq; unfold PARSE_STRING_STACK, DELETE_STACK, POBJ_STACK, PARSE_STACK, ASTKMALLOC_STACK, AINTRIN_STACK, ASTRFN_STACK, AMALLOC_STACK, SKIPWS_STACK; lia | sclr_tac2 ].
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac steq := unfold VST, SHV, mkR; repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac blia := unfold pv_cost_pre, pstr_cost_pre, pstr_fail_cost, PV_FRATE, PV_RATE in *; rewrite ?cost_free_eq in *; rewrite ?length_app in *; cbn [length] in *; unfold cblock in *; lia.
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length];
             first [lia | split; [lia| exact I] | split; [lia| split; [lia| exact I]]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].

  Hypothesis DEL : cjson_delete_stmt AI TI.

  Notation ALOOPc := (ALOOP AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky).
  Notation ARR_SUCCESS := (arr_success AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK FLA nfuel FUEL).
  Notation ARR_FAIL_00 := (arr_fail_00 AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK FLA STC nfuel DEL).
  Notation ARR_FAIL_74 := (arr_fail_74 AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR LF np B CH U P CA blen off depth bs D n lo nx pv ty p1 vi p2 vd ky PVC BPRE CHOK FLA STC nfuel DEL).
  Notation VFR_MUNCH := (VFR_munch ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC nfuel).


  (* [comment removed for export] *)
  Lemma arr_close : forall (SA Fr o3 hd A : Z) (Xall : list cblock) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h jae jn lj
      x1 x5 x6 x7 x10 x12 x13 x14 x16 x17 x28 x29 x30 x31,
    VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((U, 64) :: Xall ++ LR) LBX ->
    hd <> 0 -> cj_chain CJ_PRINTABLE m1 (S DCH) hd Xall -> depth <= 999 ->
    VFRx SA Fr m1 shb h jae jn CS08x lj ->
    pbuf_at m1 P CA blen o3 (depth + 1) ->
    rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
    off <= o3 < blen -> Fagree F Fx -> frm0 fcx ->
    B - PV_RATE * (o3 - off) + 192 <= B1 -> Z.of_nat (length Xall) <= o3 - off ->
    LSCPS asegs POST (VSTx SA Fr 0x83610 x1 x5 x6 x7 x10 (Z_to_bv 64 o3) x12 x13 x14 (Z_to_bv 64 hd) x16 x17 (Z_to_bv 64 hd) (Z_to_bv 64 A) (Z_to_bv 64 P)
                        (Z_to_bv 64 (P + 24)) (SHV (P + 24)) (Z_to_bv 64 A) x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD HPX HNZ CHN Hd VF PB ND Ho FA FRM HB HX. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b Xall -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; left; exact Hb]).
    assert (INU : In (U, 64) LBX) by (eapply perm_in_head; exact HPX).
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL (INLR _ HD) DCA CAD) as TSH.
    pose proof (cj_chain_head_block _ _ _ _ _ CHN HNZ) as INH.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (INX _ INH)) 4%nat; intros H1 H2 H3 H4). try rewrite alloc_ceiling_eq in H4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in H1. bandM. sepM.
    destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL HPX hd 64 ltac:(apply in_or_app; left; exact INH)) as [_ UH].
    pose proof (art_blocks_high_apart AI _ _ _ _ _ _ _ _ _ P HL ltac:(right; exact PLF)) as BHA. destruct (BHA hd 64 (INX _ INH)) as [_ HPd].
    (nelimp VF 10%nat; intros _ L32 _ _ _ L0 S0 L16 _ _). unfold LOCSV, SHV in L16. unfold CS08 in L0.
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND.
    destruct (nth_error bs (Z.to_nat o3)) as [b|] eqn:Hn; [| apply nth_error_None in Hn; lia].
    pose proof (u8ro_read asegs _ CA bs o3 b _ BY Hn ltac:(lia) eq_refl) as RD. pose proof (byte_range b) as Rb.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    zstep. pose proof (sh_zero_shb m1 P (P + 56) P PSH ltac:(lia)) as Z0. asan_chk Z0. clear Z0.
    zstep. zstep. zstep. zstep.
    pose proof (TSH (CA + o3) ltac:(lia)) as CK. sepM. asan_chk CK.
    zstep. zstep. zstep. if_cases K93; zify_cond K93.
    { (* [comment removed for export] *)
      apply evt_done. eapply (ARR_FAIL_00 SA Fr hd Xall (S DCH) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h jae jn CS08x lj o3 (depth + 1));
        [exact GE| exact MD| exact HPX| eapply cj_chain_any; exact CHN| unfold dch; lia| exact VF| exact PB'| eqcells ND| exact FA| exact FRM
        | clear -HB HX BPRE OFF Ho; blia]. }
    (* [comment removed for export] *)
    pose proof (sh_zero_shb m1 P (P + 56) (P + 24) PSH ltac:(lia)) as Z24. asan_chk Z24. clear Z24.
    pose proof (munch_refl [(P + 24, P + 32)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : ART AI sp0 SPB LBX ((Fr, 2) :: LF) TRS1 B1 m2 mo1 g1) by (eapply (art_pbuf_store AI); [exact HL| right; exact PLF| exact MU| exact WM| lia| lia]).
    assert (PR2 : ppres sp0 LR LF SP P m m2).
    { eapply ppres_trans; [exact PR|]. eapply ppres_pbuf_store; [exact MU| exact WM| lia| lia]. }
    assert (PSH2 : pbuf_sh m2 P) by (eapply pbuf_sh_high_store; [exact PSH| exact MU| alia| alia| alia]).
    assert (CH2 : cj_chain CJ_PRINTABLE m2 (S DCH) hd Xall).
    { eapply cj_chain_frame; [exact CHN| exact MU| exact WM|].
      intros A' k Hin. cbn. split; [|exact I]. destruct (BHA A' k (INX _ Hin)). lia. }
    assert (CC2 : chain_cells m2 CH).
    { eapply chain_cells_munch; [exact CC| exact CHOK| exact MU| lia| lia|]. intros lo' hi' [E|[]]. inversion E; subst. left. lia. }
    assert (VF2 : VFRx SA Fr m2 shb h jae jn CS08x lj).
    { eapply VFR_MUNCH; [exact GE| exact VF| exact MU| exact WM|]. intros lo' hi' [E|[]]. inversion E; subst. right. repeat split; alia. }
    clear MU WM HL PR PSH CHN CC VF.
    (* [comment removed for export] *)
    (nelim (cj_chain_cons_inv _ _ _ _ _ CH2 HNZ) 24%nat; intros d0 nxh pvh chh tyh p1h vsh vih p2h vdh kyh Bvh Bkh Bch Bnh Ed NDH TYH HTh SVh SKh CHCh CHNh EX)
.
    assert (HPh : Permutation ((hd, 64) :: (Bvh ++ Bkh ++ Bch ++ Bnh) ++ (U, 64) :: LR) LBX).
    { rewrite EX in HPX. eapply Permutation_trans; [apply perm_pick_head| exact HPX]. }
    destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL2 HPh D n ltac:(apply in_or_app; right; right; exact HD)) as [_ DH].
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL2 (INX _ INH)) as SOH.
    pose proof (shadow_ok_sh_zero m2 hd 64 hd (hd + 64) SOH ltac:(lia) ltac:(clear -H2; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(replace (hd + 64 - hd) with 64 by lia; reflexivity)) as SZH.
    unfold node_cells, wz in NDH.
    pose proof (munch_refl [(hd + 8, hd + 16)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep. zstep. zstep.
    pose proof (sh_zero_shb m2 hd (hd + 64) (hd + 8) SZH ltac:(lia)) as CKH. asan_chk CKH. clear CKH.
    sepM. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : ART AI sp0 SPB LBX ((Fr, 2) :: LF) TRS1 B1 m3 mo1 g1) by (eapply (art_block_store AI); [exact HL2| exact (INX _ INH)| exact MU| exact WM| lia| lia]).
    assert (PR3 : ppres sp0 LR LF SP P m m3).
    { eapply ppres_trans; [exact PR2|]. eapply (ppres_weaken sp0 LR LR ((Fr, 2) :: LF) LF SA SP P); [| lia| intros b' Hb'; exact Hb'| intros f Hf; right; exact Hf].
      eapply (ppres_block_store AI); [exact HL2| exact HPh| intros bb Hbb; apply in_or_app; right; right; exact Hbb| alia| lia| exact MU| exact WM| lia| lia]. }
    sepM. assert (PSH3 : pbuf_sh m3 P) by (eapply pbuf_sh_high_store; [exact PSH2| exact MU| alia| alia| alia]).
    assert (CH3 : cj_chain CJ_PRINTABLE m3 (S DCH) hd Xall).
    { rewrite EX, Ed. eapply (cj_chain_relink AI); [exact HL2| exact HPh| exact HNZ| exact TYH| exact HTh| exact SVh| exact SKh| exact CHCh| exact CHNh| exact MU| exact WM| eqcells NDH]. }
    assert (CC3 : chain_cells m3 CH).
    { eapply chain_cells_munch; [exact CC2| exact CHOK| exact MU| lia| lia|]. intros lo' hi' [E|[]]. inversion E; subst. left. lia. }
    assert (VF3 : VFRx SA Fr m3 shb h jae jn CS08x lj).
    { eapply VFR_MUNCH; [exact GE| exact VF2| exact MU| exact WM|]. intros lo' hi' [E|[]]. inversion E; subst. right.
      assert (INF2 : In (Fr, 2) ((Fr, 2) :: LF)) by (left; reflexivity).   (* [comment removed for export] *)
      (nelim (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL2 INF2) 8%nat; intros _ _ _ _ _ _ _ FD).
      pose proof (INX _ INH) as INHD. pose_blk_band HL2 INHD.   (* [comment removed for export] *)
      sepM. destruct (FD hd 64 INHD); change (fsz 2) with 256 in *; alia. }
    clear MU WM PR2 PSH2 CH2 CC2 VF2 SVh SKh CHCh CHNh NDH SOH SZH.
    (* [comment removed for export] *)
    pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL3 INU) as SOU.
    pose proof (shadow_ok_sh_zero m3 U 64 U (U + 64) SOU ltac:(lia) ltac:(clear -U2; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(replace (U + 64 - U) with 64 by lia; reflexivity)) as SZU.
    zstep. zstep. zstep. zstep.
    pose proof (sh_zero_shb m3 U (U + 64) (U + 24) SZU ltac:(lia)) as CK4. asan_chk CK4. clear CK4.
    apply evt_done.
    eapply lscps_eq; [| eapply (ARR_SUCCESS SA Fr o3 hd Xall m3 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h jae jn CS08x lj);
      [exact GE| | exact HPX| exact CH3| exact Hd| | unfold pbuf_at, pbuf_cells, wz; eqcells PB| eqcells ND| exact Ho| exact FA| exact FRM
      | clear -HB Ho OFF; unfold PV_RATE in *; lia| lia]].
    { steq. }
    - split; [exact HL3|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI|]. split; [exact ST|].
      split; [exact PR3|]. split; [exact GM|]. split; [exact TV|]. split; [exact PSH3| exact CC3].
    - exact VF3.
  Qed.

  (* [comment removed for export] *)
  Lemma after_elem : forall (c : nat), (forall c', (c' < c)%nat -> ALOOPc c') ->
    forall (SA Fr o o3 hd A : Z) (pvA : word) (chA tyA vsA : Z) (viA vdA : word) (X Bv Bc : list cblock) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h jae jn lj
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o < o3 <= blen -> depth <= 999 ->
      VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((U, 64) :: (X ++ (A, 64) :: Bv ++ Bc) ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 DCH hd A X ->
      rw_cells asegs m1 A (node_cells 0 pvA chA tyA (wz 0) vsA viA (wz 0) vdA 0) ->
      CJ_PRINTABLE tyA -> cj_str m1 vsA Bv -> cj_chain CJ_PRINTABLE m1 DCH chA Bc ->
      VFRx SA Fr m1 shb h jae jn CS08x lj ->
      pbuf_at m1 P CA blen o3 (depth + 1) ->
      rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      B - PV_RATE * (o3 - off) + 192 <= B1 -> Z.of_nat (length (X ++ (A, 64) :: Bv ++ Bc)) <= o3 - off ->
      LSCPS asegs POST (VSTx SA Fr 0x834c4 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 hd) (Z_to_bv 64 A) (Z_to_bv 64 P)
                          (Z_to_bv 64 (P + 24)) (SHV (P + 24)) x24 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho3 Hd GE MD HPX HNZ ANZ SEG NDA HTA SVA CHA VF PB ND FA FRM HB HX. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (rw_cells_bound asegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; exact Hb]).
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL (INLR _ HD) DCA CAD) as TSH.
    assert (CHall : cj_chain CJ_PRINTABLE m1 (S DCH) hd (X ++ (A, 64) :: Bv ++ Bc)).
    { apply cj_lseg_chain0. replace (Bv ++ Bc) with (Bv ++ [] ++ Bc) by reflexivity.
      eapply cj_lseg_snoc; eauto using cj_str_null. apply CJ_PRINTABLE_range. exact HTA. }
    (nelimp VF 10%nat; intros _ L32 _ _ _ L0 S0 L16 _ _). unfold LOCSV, SHV in L16. unfold CS08 in L0.
    pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND.
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    zstep. pose proof (sh_zero_shb m1 P (P + 56) (P + 16) PSH ltac:(lia)) as Z16. asan_chk Z16. clear Z16.
    zstep. pose proof (sh_zero_shb m1 P (P + 56) (P + 8) PSH ltac:(lia)) as Z8. asan_chk Z8. clear Z8.
    zstep. zstep. zstep. zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
    { (* [comment removed for export] *)
      apply evt_done. eapply (ARR_FAIL_00 SA Fr hd (X ++ (A, 64) :: Bv ++ Bc) (S DCH) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h jae jn CS08x lj o3 (depth + 1));
        [exact GE| exact MD| exact HPX| eapply cj_chain_any; exact CHall| unfold dch; lia| exact VF| exact PB'| eqcells ND| exact FA| exact FRM
        | clear -HB HX BPRE OFF Ho Ho3; blia]. }
    (* [comment removed for export] *)
    zstep. pose proof (sh_zero_shb m1 P (P + 56) P PSH ltac:(lia)) as Z0. asan_chk Z0. clear Z0.
    destruct (nth_error bs (Z.to_nat o3)) as [b|] eqn:Hn; [| apply nth_error_None in Hn; lia].
    pose proof (u8ro_read asegs _ CA bs o3 b _ BY Hn ltac:(lia) eq_refl) as RD. pose proof (byte_range b) as Rb.
    zstep. zstep. zstep. zstep.
    pose proof (TSH (CA + o3) ltac:(lia)) as CK. sepM. asan_chk CK.
    zstep. zstep. zstep. zstep. zstep. if_cases K44; zify_cond K44.
    - (* [comment removed for export] *)
      apply evt_done.
      eapply lscps_eq; [| eapply (IHc (Z.to_nat (blen - o3)) ltac:(lia) SA Fr o3 hd A (X ++ (A, 64) :: Bv ++ Bc) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h jae jn lj);
        [lia| lia| exact Hd| exact GE| exact MD| exact HPX| | exact VF| exact PB'| eqcells ND| exact FA| exact FRM
        | clear -HB Ho Ho3 OFF; unfold PV_RATE in *; lia| exact HX]].
      { steq. }
      right. split; [exact HNZ|]. split; [exact ANZ|]. exists X, Bv, Bc, chA, tyA, vsA, pvA, (wz 0), viA, (wz 0), vdA.
      split; [reflexivity|]. split; [exact SEG|]. split; [eqcells NDA|]. split; [exact HTA|]. split; [exact SVA| exact CHA].
    - (* [comment removed for export] *)
      zstep. apply evt_done.
      eapply (arr_close SA Fr o3 hd A (X ++ (A, 64) :: Bv ++ Bc) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h jae jn lj);
        [exact GE| exact MD| exact HPX| exact HNZ| exact CHall| exact Hd| exact VF| exact PB'| eqcells ND| lia| exact FA| exact FRM| exact HB| exact HX].
  Qed.

  (* [comment removed for export] *)
  Lemma after_call : forall (c : nat), (forall c', (c' < c)%nat -> ALOOPc c') ->
    forall (SA Fr o o2 hd A : Z) (pvA : word) (X : list cblock) (r off5 depth5 : Z) (X5 : list cblock) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h jae jn lj
           x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31,
      Z.of_nat c = blen - o -> off <= o -> o < o2 <= blen -> depth <= 999 ->
      VGEOMx SA Fr -> MID SA Fr m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation ((A, 64) :: X5 ++ (U, 64) :: X ++ LR) LBX ->
      hd <> 0 -> A <> 0 -> cj_lseg CJ_PRINTABLE m1 DCH hd A X ->
      VFRx SA Fr m1 shb h jae jn CS08x lj ->
      pbuf_at m1 P CA blen off5 depth5 ->
      rw_cells asegs m1 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      Z.of_nat (length X) <= o - off ->
      ( (r = 0 /\ X5 = [] /\ rw_cells asegs m1 A (node_cells 0 pvA 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0)
          /\ B - PV_RATE * (o - off) - 448 - pv_cost_pre (blen - o2) <= B1)
        \/ (r = 1 /\ depth5 = depth + 1 /\ o2 <= off5 <= blen /\ B - PV_RATE * (off5 - off) + 192 <= B1 /\ Z.of_nat (length X5) <= off5 - o2
             /\ exists (ch ty' vs : Z) (vi' vd' : word) (dc : nat) (Bv Bc : list cblock),
                  X5 = Bv ++ Bc
                  /\ rw_cells asegs m1 A (node_cells 0 pvA ch ty' (wz 0) vs vi' (wz 0) vd' 0)
                  /\ CJ_PRINTABLE ty' /\ cj_str m1 vs Bv /\ cj_chain CJ_PRINTABLE m1 dc ch Bc
                  /\ Z.of_nat dc + (depth + 1) <= 1000) ) ->
      LSCPS asegs POST (VSTx SA Fr 0x834b8 x1 x5 x6 x7 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 hd) (Z_to_bv 64 A) (Z_to_bv 64 P)
                          (Z_to_bv 64 (P + 24)) (SHV (P + 24)) x24 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros c IHc. intros until x31. intros Hc Ho Ho2 Hd GE MD HPX HNZ ANZ SEG VF PB ND FA FRM HXl RES. lits. bandM. sepM.
    (nelimp GE 8%nat; intros GSA GAL FAL FLO FHI FBLK FNEW PFR). (nelimp MD 10%nat; intros HL BY ERR MI ST PR GM TV PSH CC).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    assert (INLR : forall b, In b LR -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; apply in_or_app; right; exact Hb]).
    assert (INX : forall b, In b X -> In b LBX) by (intros b Hb; eapply Permutation_in; [exact HPX| right; apply in_or_app; right; right; apply in_or_app; left; exact Hb]).
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL (INLR _ HD) DCA CAD) as TSH.
    pose proof (art_blocks_high_apart AI _ _ _ _ _ _ _ _ _ P HL ltac:(right; exact PLF)) as BHA.
    assert (INA : In (A, 64) LBX) by (eapply perm_in_head; exact HPX).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL INA) 4%nat; intros A1 A2 A3 A4). try rewrite alloc_ceiling_eq in A4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in A1. bandM. sepM.
    destruct (BHA A 64 INA) as [_ APd].
    unfold VST, SHV. eapply lscps_step_evt. cbv beta delta [mkR].
    destruct RES as [(-> & -> & NDA & HB) | (-> & -> & Ho5 & HB & HX5 & chA & tyA & vsA & viA & vdA & dc & Bv & Bc & -> & NDA & HTA & SVA & CHA & Hdc)].
    - (* [comment removed for export] *)
      zstep. if_true. apply evt_done.
      assert (CHf : cj_chain CJ_ANY m1 (S DCH) hd (X ++ (A, 64) :: [] ++ [] ++ [])).
      { eapply cj_lseg_chain; [eapply cj_lseg_mono; [exact SEG| intros; exact I| lia]|].
        eapply cj_chain_one; [exact ANZ| exact NDA| lia| exact I| apply cj_str_null| apply cj_str_null| apply cj_chain_nil]. }
      cbn [app] in CHf, HPX.
      eapply (ARR_FAIL_74 SA Fr hd (X ++ [(A, 64)]) (S DCH) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h jae jn CS08x lj off5 depth5);
        [exact GE| exact MD| | exact CHf| unfold dch; lia| exact VF| exact PB| exact ND| exact FA| exact FRM
        | clear -HB HXl BPRE OFF Ho Ho2; blia].
      eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply (perm_new_done (U, 64) (A, 64) [] X LR).
    - (* [comment removed for export] *)
      pose proof (rw_cells_bound asegs _ _ _ NDA) as NAB. rewrite node_cells_size in NAB.
      assert (HPX' : Permutation ((U, 64) :: (X ++ (A, 64) :: Bv ++ Bc) ++ LR) LBX).
      { eapply Permutation_trans; [| exact HPX]. apply Permutation_sym. apply perm_new_done. }
      pose proof PB as PB'. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND. unfold node_cells, wz in NDA.
      zstep. if_false. zstep. zstep.
      eapply evt_cut.
      { eapply skipws_spec with (P := P) (content := CA) (len := blen) (offset := off5) (depth := depth + 1) (bs := bs) (lo := lo); rewrite ?unsigned_lit by lia;
          first [ unfold pbuf_at, pbuf_cells, wz; exact PB | reflexivity | exact BY | exact LEN | exact PSH | exact TSH | exact MI | exact ST
                | eapply (art_shbase AI); exact HL
                | alia
                | clear -PF3; Z.div_mod_to_equations; lia ]. }
      intros ms' PO. (nelim PO 18%nat; intros t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' m4 -> MU4 WM4 MI4 ST4 PB4 BY4).
      rewrite ?unsigned_lit in MU4, ST4 by lia.
      replace (ret_pc (Z_to_bv 64 0x834c4)) with (Z_to_bv 64 0x834c4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      trc ND MU4 WM4. trc NDA MU4 WM4. trc ERR MU4 WM4.
      assert (HL4 : ART AI sp0 SPB LBX ((Fr, 2) :: LF) TRS1 B1 m4 mo1 g1).
      { eapply (art_frame AI); [exact HL| exact MU4| exact WM4|]. constructor; [| constructor; [| constructor]].
        - do 8 right. left. exists (P - 32), 1. cbn. split; [right; exact PLF|]. change (fsz 1) with 128. lia.
        - right; left. cbn. alia. }
      assert (PR4 : ppres sp0 LR LF SP P m m4).
      { eapply ppres_trans; [exact PR|]. eapply ppres_of_munch; [exact MU4| exact WM4|]. intros a Ha Hp. cbn.
        pose proof (pv_addr_below AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC LBX ((Fr, 2) :: LF) m1 mo1 g1 TRS1 B1 a HL INLR
                      ltac:(intros f Hf; right; exact Hf) Ha Hp) as BLW.
        (nelim Hp 3%nat; intros _ _ HnP). try rewrite alloc_ceiling_eq in BLW. clear -BLW HnP CEIL LO GSA. lia. }
      assert (PSH4 : pbuf_sh m4 P).
      { eapply pbuf_sh_munch; [exact PSH| exact MU4| lia| lia|]. cbn [disjoint_from]. pose proof (SH_bounds P ltac:(lia)). pose proof (SH_bounds (P + 55) ltac:(lia)).
        unfold SH, SHADOW_OFFSET in *. split; [lia|]. split; [lia| exact I]. }
      assert (CC4 : chain_cells m4 CH).
      { eapply chain_cells_munch; [exact CC| exact CHOK| exact MU4| lia| lia|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; left; lia. }
      assert (VF4 : VFRx SA Fr m4 shb h jae jn CS08x lj).
      { eapply VFR_MUNCH; [exact GE| exact VF| exact MU4| exact WM4|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; [right; repeat split; alia| left; alia]. }
      assert (BLK : forall A' k, In (A', k) LBX -> disjoint_from [(P + 16, P + 24); (lo, SA)] A' k).
      { intros A' k Hin. cbn. destruct (BHA A' k Hin) as [R1 R2].
        (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) 4%nat; intros _ _ _ R4). try rewrite alloc_ceiling_eq in R4.
        split; [lia|]. split; [lia| exact I]. }
      assert (SEG4 : cj_lseg CJ_PRINTABLE m4 DCH hd A X).
      { eapply cj_lseg_frame; [exact SEG| exact MU4| exact WM4|]. intros A' k Hin. apply BLK. apply INX. exact Hin. }
      assert (SVA4 : cj_str m4 vsA Bv).
      { eapply cj_str_frame; [exact SVA| exact MU4| exact WM4|]. intros A' k Hin. apply BLK.
        eapply Permutation_in; [exact HPX|]. right. apply in_or_app. left. apply in_or_app. left. exact Hin. }
      assert (CHA4 : cj_chain CJ_PRINTABLE m4 DCH chA Bc).
      { eapply cj_chain_frame; [eapply cj_chain_mono_d; [exact CHA| unfold dch; lia]| exact MU4| exact WM4|]. intros A' k Hin. apply BLK.
        eapply Permutation_in; [exact HPX|]. right. apply in_or_app. left. apply in_or_app. right. exact Hin. }
      clear MU4 WM4 HL PR PSH CC VF SEG SVA CHA BY MI ST.
      assert (O3 : off5 <= skipws_off bs off5 <= blen).
      { destruct (Z.eq_dec off5 blen) as [E|NE].
        - rewrite skipws_off_noop by lia. lia.
        - pose proof (skipws_off_range bs off5) as OR. rewrite LEN in OR. lia. }
      apply evt_done.
      eapply (after_elem c IHc SA Fr o (skipws_off bs off5) hd A pvA chA tyA vsA viA vdA X Bv Bc m4 mo1 g1 LBX TRS1 B1 errv1 Fx fcx shb h jae jn lj);
        [exact Hc| exact Ho| lia| exact Hd| exact GE| | exact HPX'| exact HNZ| exact ANZ| exact SEG4| eqcells NDA| exact HTA| exact SVA4| exact CHA4
        | exact VF4| exact PB4| eqcells ND| exact FA| exact FRM
        | clear -HB O3 Ho Ho2 Ho5 OFF; unfold PV_RATE in *; lia
        | clear -HXl HX5 O3 Ho Ho2 Ho5 OFF; rewrite ?length_app in *; cbn [length] in *; rewrite ?length_app in *; lia].
      split; [exact HL4|]. split; [exact BY4|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI4|]. split; [exact ST4|].
      split; [exact PR4|]. split; [exact GM|]. split; [exact TV|]. split; [exact PSH4| exact CC4].
  Qed.
End PVA2.


End CeilWrap.
