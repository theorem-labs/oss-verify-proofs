(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells AProto ABase MonadF AMalloc_iface AAtexit_iface ABytes.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma page_round_up_geA : forall x, 0 <= x -> x <= page_round_up_Z x < x + 4096 /\ page_round_up_Z x mod 4096 = 0.
Proof. intros x Hx. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia. Qed.

Lemma harness_top : forall L SP, SP + 208 = al_sp0 L -> 0 <= SP -> SP + 16 <= al_top L < SP + 48 + 4096.      (* [comment removed for export] *)
Proof.
  intros L SP E H0. unfold al_top. rewrite <- E. replace (SP + 208 - 160) with (SP + 48) by lia.
  pose proof (page_round_up_geA (SP + 48) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma byte_of_c1 : forall m s b, rw_cells bsegs m s [C1 b] -> 0x6d4000 <= s -> m (wa s) = Some b.
Proof.
  intros m s b [[_ (A & B & H)] _] Hs. cbn [cells_bytes cbytes app length] in B, H.
  specialize (H 0%nat ltac:(lia)). cbn in H. rewrite Z.add_0_r in H.
  rewrite <- (mrd_no_image bsegs m s (s + 1) s (no_image_asan s (s + 1) Hs)) by lia.
  rewrite H. cbn. reflexivity.
Qed.

Lemma mem_eq_single : forall mp m' A b, 0 <= A -> A + 1 <= 2^64 ->
  munch [(A, A + 1)] mp m' -> m' (wa A) = Some b -> m' = write_to_mem mp (wa A) [b].
Proof.
  intros mp m' A b HA HB MU Hb. apply functional_extensionality. intros x.
  rewrite write_to_mem_spec by (cbn; lia). cbn [length]. change (Z.of_nat 1) with 1.
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
  destruct (Z.eq_dec (bv_unsigned x) A) as [E|NE].
  - replace x with (wa A) by (rewrite <- E; unfold wa; apply Z_to_bv_bv_unsigned). rewrite Hb, wa_unsigned by lia.
    replace (A <=? A) with true by (symmetry; apply Z.leb_le; lia). replace (A <? A + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn. rewrite Z.sub_diag. reflexivity.
  - rewrite MU by (cbn; lia).
    destruct (Z.leb_spec0 A (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (A + 1)); cbn [andb]; try reflexivity. exfalso; lia.
Qed.

(* [comment removed for export] *)
Definition wfar (iv : Z * Z) : Prop := AIMG_HI <= fst iv /\ (snd iv <= KLS \/ 0x800d2800 <= fst iv).
Lemma wfar_of_wclr : forall iv, wclr iv -> wfar iv.
Proof. intros [lo hi] [A B]. unfold wfar, sclr, KLS in *. cbn [fst snd] in *. lia. Qed.
Lemma Forall_wfar_of_wclr : forall W, Forall wclr W -> Forall wfar W.
Proof. intros W FW. eapply Forall_impl; [| exact FW]. intros iv H. apply wfar_of_wclr. exact H. Qed.
Lemma wfar_high : forall lo hi, 0x10007fff8000 <= lo -> wfar (lo, hi).
Proof. intros lo hi H. unfold wfar, AIMG_HI. cbn [fst snd]. lia. Qed.
Lemma wfar_ablk : forall lo hi a b, ablk lo hi -> lo <= a -> b <= hi -> wfar (a, b).
Proof. intros lo hi a b H A B. apply wfar_of_wclr. eapply wclr_ablk; [exact H| exact A| exact B]. Qed.
Lemma wfar_shad : forall lo hi, 0x800d2800 <= lo -> wfar (lo, hi).
Proof. intros lo hi H. unfold wfar, AIMG_HI. cbn [fst snd]. lia. Qed.
Lemma wfar_outside : forall W a, Forall wfar W -> (a < AIMG_HI \/ KLS <= a < 0x800d2800) -> outside W a.
Proof.
  intros W a FW Ha. induction W as [|[wlo whi] W IH]; [exact I|]. inversion FW as [|x l F1 FW']; subst.
  unfold wfar, AIMG_HI, KLS in F1, Ha. cbn in F1 |- *. split; [lia| apply IH; exact FW'].
Qed.
Lemma wfar_disjoint : forall W a n, Forall wfar W -> (a + n <= AIMG_HI \/ (KLS <= a /\ a + n <= 0x800d2800)) -> disjoint_from W a n.
Proof.
  intros W a n FW Ha. induction W as [|[wlo whi] W IH]; [exact I|]. inversion FW as [|x l F1 FW']; subst.
  unfold wfar, AIMG_HI, KLS in F1, Ha. cbn in F1 |- *. split; [lia| apply IH; exact FW'].
Qed.

(* [comment removed for export] *)
Lemma client_sh_munch32 : forall W mx my, client_sh mx -> munch W mx my -> Forall wfar W -> client_sh my.
Proof.
  intros W mx my CS MU FW X HX. rewrite <- (CS X HX). apply MU.
  unfold client_sh_addrs in HX. cbn [In] in HX.
  assert (B : 0x16dce0 <= X < 0x6d4000) by (repeat (destruct HX as [<-|HX]; [lia|]); destruct HX).
  rewrite wa_unsigned by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
  apply wfar_outside; [exact FW|]. right. rewrite shad_div. unfold ASHOFF, KLS. Z.div_mod_to_equations. lia.
Qed.
Lemma client_x_munch32 : forall W mx my, client_x mx -> munch W mx my -> wmono bsegs mx my -> Forall wfar W -> client_x my.   (* [comment removed for export] *)
Proof.
  intros W mx my X MU WM FW. unfold client_x, AMSG_SH, AJT_SH, AJT, AREAL_STRLEN in *.
  destruct X as (X1 & X2 & X3 & X4).
  split; [| split; [| split]].
  - intros i Hi. rewrite <- (X1 i Hi). apply MU. rewrite wa_unsigned by lia. apply wfar_outside; [exact FW|]. right. unfold KLS. lia.
  - intros i Hi. rewrite <- (X2 i Hi). apply MU. rewrite wa_unsigned by lia. apply wfar_outside; [exact FW|]. right. unfold KLS. lia.
  - eapply rw_cells_transport; [exact X3| exact MU| exact WM|]. apply wfar_disjoint; [exact FW|]. left. unfold AIMG_HI. cbn. lia.
  - eapply rw_cells_transport; [exact X4| exact MU| exact WM|]. apply wfar_disjoint; [exact FW|]. left. unfold AIMG_HI. cbn. lia.   (* [comment removed for export] *)
Qed.
Lemma client_img_munch32 : forall W mx my, client_img mx -> munch W mx my -> wmono bsegs mx my -> Forall wfar W -> client_img my.
Proof.
  intros W mx my (I1 & I2 & I3 & I4 & I5 & I6 & X) MU WM FW. unfold client_img, AGOT_SUAR, ASUAR, AVTAB_SRS, AVTAB_VU8, AVTAB_MIN, AGOT_ERRC, AERRC in *.
  split; [| split; [| split; [| split; [| split; [| split; [| exact (client_x_munch32 W mx my X MU WM FW)]]]]]];
    (eapply rw_cells_transport; [eassumption| exact MU| exact WM|]); apply wfar_disjoint; try exact FW; left; unfold AIMG_HI; cbn; lia.
Qed.
Lemma harness_inv_munch32 : forall W mx my, harness_invA mx -> munch W mx my -> wmono bsegs mx my -> Forall wfar W -> harness_invA my.
Proof. intros W mx my [A B] MU WM FW. split; [eapply client_img_munch32| eapply client_sh_munch32]; eassumption. Qed.

Ltac xt_img MU WM FW := eapply rw_cells_transport; [eassumption| exact MU| exact WM|]; apply wfar_disjoint; [exact FW|]; left; unfold AIMG_HI; cbn; lia.

Lemma cells_size_map_C8 : forall ws : list word, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. lia. Qed.

Lemma atexit_rt_munch32 : forall W mx my, atexit_rt mx -> munch W mx my -> wmono bsegs mx my -> Forall wfar W -> atexit_rt my.
Proof.
  intros W mx my (A1 & (cdt & thr & sec & tm1 & A3)) MU WM FW. unfold atexit_rt.
  split; [xt_img MU WM FW|]. exists cdt, thr, sec, tm1; xt_img MU WM FW.
Qed.
(* [comment removed for export] *)
Lemma ATEXIT_transport : forall tbl mx my,
  (forall A cs, 0x6d1ef8 <= A -> A + Z.of_nat (cells_size cs) <= 0x6d2118 -> rw_cells bsegs mx A cs -> rw_cells bsegs my A cs) ->
  ATEXIT tbl mx -> ATEXIT tbl my.
Proof.
  intros tbl mx my T (fj & aj & C1' & C2 & C3 & C4' & C5 & C6 & C7 & L1 & L2). exists fj, aj.
  unfold atexit_cells, ATX_FIN, ATX_LOCK, ATX_SLOT, ATX_HEAD, ATX_BUILTIN, ATX_F, ATX_A in *.
  split; [apply T; [lia| cbn; lia| exact C1']|]. split; [apply T; [lia| cbn; lia| exact C2]|]. split; [apply T; [lia| cbn; lia| exact C3]|].
  split; [apply T; [lia| cbn; lia| exact C4']|]. split; [apply T; [lia| cbn; lia| exact C5]|].
  split; [apply T; [lia| rewrite cells_size_map_C8, L1; lia| exact C6]|]. split; [apply T; [lia| rewrite cells_size_map_C8, L2; lia| exact C7]|].
  split; assumption.
Qed.
Lemma ATEXIT_munch32 : forall W tbl mx my, ATEXIT tbl mx -> munch W mx my -> wmono bsegs mx my -> Forall wfar W -> ATEXIT tbl my.
Proof.
  intros W tbl mx my AT MU WM FW. eapply ATEXIT_transport; [| exact AT]. intros A cs HA HB RW.
  eapply rw_cells_transport; [exact RW| exact MU| exact WM|]. apply wfar_disjoint; [exact FW|]. left. unfold AIMG_HI. lia.
Qed.

(* [comment removed for export] *)
Lemma client_static_munch32 : forall W s LB mx my, client_static s LB mx -> munch W mx my -> wmono bsegs mx my -> Forall wfar W ->
  (forall p V, aps_cl s = Some p -> In (HB p V 8) LB -> disjoint_from W V 8) -> client_static s LB my.
Proof.
  intros W s LB mx my (AR & AT & CS) MU WM FW DV. split; [eapply atexit_rt_munch32; eassumption|]. split; [eapply ATEXIT_munch32; eassumption|].
  unfold AVEC, AVEC_GUARD, AFALLBACK, guard0, guard1 in *.
  destruct (aps_cl s) as [p|].
  - destruct CS as (V & HIN & C0 & C1' & C2 & C3 & C4' & C5 & C6 & C7 & C8'). exists V. split; [exact HIN|].
    split. { eapply rw_cells_transport; [exact C0| exact MU| exact WM|]. exact (DV p V eq_refl HIN). }
    repeat (split; [xt_img MU WM FW|]). xt_img MU WM FW.
  - destruct CS as (C1' & C2 & C3 & C4' & C5 & C6 & C7 & C8' & WSH).
    repeat (split; [xt_img MU WM FW|]). eapply wr_at_transport; [exact WSH| exact WM].
Qed.

(* [comment removed for export] *)
Definition atx_rest (fj aj : list word) (m : amem) : Prop :=
  rw_cells bsegs m ATX_FIN [C1 (Z_to_bv 8 0)] /\ rw_cells bsegs m ATX_LOCK [C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m ATX_HEAD [C8 (Z_to_bv 64 ATX_BUILTIN)] /\ rw_cells bsegs m ATX_BUILTIN [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m ATX_F (map C8 (map (fun e : Z * Z => Z_to_bv 64 (fst e)) (rev TBL_REG)))
  /\ rw_cells bsegs m 0x6d1f48 (map C8 fj)
  /\ rw_cells bsegs m ATX_A (map C8 (map (fun e : Z * Z => Z_to_bv 64 (snd e)) (rev TBL_REG)))
  /\ rw_cells bsegs m 0x6d2048 (map C8 aj)
  /\ length fj = 26%nat /\ length aj = 26%nat.

Lemma atexit_main_split : forall m, ATEXIT TBL_REG m -> exists (f3 f4 a3 a4 : word) (fj aj : list word),
  atx_rest fj aj m /\ rw_cells bsegs m ATX_SLOT [C4 (Z_to_bv 64 4)]
  /\ rw_cells bsegs m 0x6d1f38 [C8 f3; C8 f4] /\ rw_cells bsegs m 0x6d2038 [C8 a3; C8 a4].
Proof.
  intros m (fj0 & aj0 & C1' & C2 & C3 & C4' & C5 & C6 & C7 & L1 & L2).
  rewrite length_app in L1, L2. cbn [TBL_REG TBL_MAIN rev app map length] in L1, L2.
  destruct fj0 as [|f3 [|f4 fj]]; try (cbn in L1; lia). destruct aj0 as [|a3 [|a4 aj]]; try (cbn in L2; lia).
  exists f3, f4, a3, a4, fj, aj.
  rewrite map_app in C6, C7. cbn [map] in C6, C7.
  change (map C8 (map (fun e : Z * Z => Z_to_bv 64 (fst e)) (rev TBL_REG)) ++ C8 f3 :: C8 f4 :: map C8 fj)
    with (map C8 (map (fun e : Z * Z => Z_to_bv 64 (fst e)) (rev TBL_REG)) ++ [C8 f3; C8 f4] ++ map C8 fj) in C6.
  change (map C8 (map (fun e : Z * Z => Z_to_bv 64 (snd e)) (rev TBL_REG)) ++ C8 a3 :: C8 a4 :: map C8 aj)
    with (map C8 (map (fun e : Z * Z => Z_to_bv 64 (snd e)) (rev TBL_REG)) ++ [C8 a3; C8 a4] ++ map C8 aj) in C7.
  apply (proj1 (rw_cells_app _ _ _ _ _)) in C6. destruct C6 as [F0 C6]. apply (proj1 (rw_cells_app _ _ _ _ _)) in C6. destruct C6 as [F1 F2].
  apply (proj1 (rw_cells_app _ _ _ _ _)) in C7. destruct C7 as [A0 C7]. apply (proj1 (rw_cells_app _ _ _ _ _)) in C7. destruct C7 as [A1 A2].
  unfold ATX_F, ATX_A in *. cbn [TBL_REG TBL_MAIN rev app map cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in F1, F2, A1, A2.
  split; [| split; [exact C3| split; [exact F1| exact A1]]].
  unfold atx_rest, ATX_F, ATX_A. split; [exact C1'|]. split; [exact C2|]. split; [exact C4'|]. split; [exact C5|]. split; [exact F0|]. split; [exact F2|]. split; [exact A0|].
  split; [exact A2|]. cbn in L1, L2. split; lia.
Qed.

Lemma atexit_run_join : forall m fj aj f a, atx_rest fj aj m -> rw_cells bsegs m ATX_SLOT [C4 (Z_to_bv 64 6)] ->
  rw_cells bsegs m 0x6d1f38 [C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 0x76be0)] -> rw_cells bsegs m 0x6d2038 [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 0)] ->
  ATEXIT (TBL_RUN f a) m.
Proof.
  intros m fj aj f a (C1' & C2 & C4' & C5 & F0 & F2 & A0 & A2 & L1 & L2) C3 F1 A1. exists fj, aj.
  unfold atexit_cells. split; [exact C1'|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4'|]. split; [exact C5|].
  unfold ATX_F, ATX_A in *.
  split; [| split; [| split; [rewrite length_app; cbn; lia| rewrite length_app; cbn; lia]]].
  - rewrite map_app. cbn [TBL_RUN TBL_REG TBL_MAIN rev app map fst] in *.
    lazymatch goal with |- rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?r) => change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: r) with ([c0; c1; c2; c3] ++ [c4; c5] ++ r) end.
    apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact F0|]. apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact F1| exact F2].
  - rewrite map_app. cbn [TBL_RUN TBL_REG TBL_MAIN rev app map snd] in *.
    lazymatch goal with |- rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?r) => change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: r) with ([c0; c1; c2; c3] ++ [c4; c5] ++ r) end.
    apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact A0|]. apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact A1| exact A2].
Qed.

Lemma disjoint_from_sub' : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros A n A' n' H H1 H2 H3; cbn in *; [exact I|].
  destruct H as [D H]. split; [lia|]. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
Lemma client_sh_munch_gen : forall W mx my, client_sh mx -> munch W mx my -> (forall X, In X client_sh_addrs -> outside W (shad X)) -> client_sh my.
Proof.
  intros W mx my CS MU OW X HX. rewrite <- (CS X HX). apply MU.
  assert (B : 0x16dce0 <= X < 0x6d4000) by (unfold client_sh_addrs in HX; cbn [In] in HX; repeat (destruct HX as [<-|HX]; [lia|]); destruct HX).
  rewrite wa_unsigned by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia). apply OW. exact HX.
Qed.
Lemma client_x_munch_gen : forall W mx my, client_x mx -> munch W mx my -> wmono bsegs mx my ->
  disjoint_from W AMSG_SH 16 -> disjoint_from W AJT_SH 96 -> disjoint_from W AJT 768 -> disjoint_from W AREAL_STRLEN 8 -> client_x my.   (* [comment removed for export] *)
Proof.
  intros W mx my X MU WM D5 D6 D7 DS. unfold client_x, AMSG_SH, AJT_SH, AJT, AREAL_STRLEN in *. destruct X as (X1 & X2 & X3 & X4).
  split; [| split; [| split]].
  - intros i Hi. rewrite <- (X1 i Hi). apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D5| lia].
  - intros i Hi. rewrite <- (X2 i Hi). apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D6| lia].
  - eapply rw_cells_transport; [exact X3| exact MU| exact WM|]. eapply disjoint_from_sub'; [exact D7| cbn; lia| cbn; lia| cbn; lia].
  - eapply rw_cells_transport; [exact X4| exact MU| exact WM| exact DS].   (* [comment removed for export] *)
Qed.
(* [comment removed for export] *)
Lemma client_img_munch_gen : forall W mx my, client_img mx -> munch W mx my -> wmono bsegs mx my ->
  disjoint_from W 0x173d30 8 -> disjoint_from W 0x16e020 32 ->
  disjoint_from W AGOT_ERRC 8 -> disjoint_from W (AERRC + 240) 16 -> disjoint_from W AMSG_SH 16 -> disjoint_from W AJT_SH 96 -> disjoint_from W AJT 768 -> disjoint_from W AREAL_STRLEN 8 -> client_img my.   (* [comment removed for export] *)
Proof.
  intros W mx my (I1 & I2 & I3 & I4 & I5 & I6 & X) MU WM D1 D2 D3 D4 D5 D6 D7 DS. unfold client_img, AGOT_SUAR, AVTAB_SRS, AVTAB_VU8, AVTAB_MIN, AGOT_ERRC, AERRC in *.
  split; [eapply rw_cells_transport; [exact I1| exact MU| exact WM| exact D1]|].
  split; [eapply rw_cells_transport; [exact I2| exact MU| exact WM|]; eapply disjoint_from_sub'; [exact D2| cbn; lia| cbn; lia| cbn; lia]|].
  split; [eapply rw_cells_transport; [exact I3| exact MU| exact WM|]; eapply disjoint_from_sub'; [exact D2| cbn; lia| cbn; lia| cbn; lia]|].
  split; [eapply rw_cells_transport; [exact I4| exact MU| exact WM|]; eapply disjoint_from_sub'; [exact D2| cbn; lia| cbn; lia| cbn; lia]|].
  split; [eapply rw_cells_transport; [exact I5| exact MU| exact WM|]; eapply disjoint_from_sub'; [exact D3| cbn; lia| cbn; lia| cbn; lia]|].
  split; [eapply rw_cells_transport; [exact I6| exact MU| exact WM|]; eapply disjoint_from_sub'; [exact D4| cbn; lia| cbn; lia| cbn; lia]|].
  exact (client_x_munch_gen W mx my X MU WM D5 D6 D7 DS).
Qed.
Lemma ATEXIT_munch_gen : forall W tbl mx my, ATEXIT tbl mx -> munch W mx my -> wmono bsegs mx my -> disjoint_from W 0x6d1ef8 544 -> ATEXIT tbl my.
Proof.
  intros W tbl mx my AT MU WM DJ. eapply ATEXIT_transport; [| exact AT]. intros A cs HA HB RW.
  eapply rw_cells_transport; [exact RW| exact MU| exact WM|]. eapply disjoint_from_sub'; [exact DJ| lia| lia| lia].
Qed.
Lemma atexit_rt_munch_gen : forall W mx my, atexit_rt mx -> munch W mx my -> wmono bsegs mx my ->
  disjoint_from W 0x175cc0 8 -> disjoint_from W 0x6d2138 8 -> atexit_rt my.
Proof.
  intros W mx my (A1 & (cdt & thr & sec & tm1 & A3)) MU WM D1 D3. unfold atexit_rt.
  split; [eapply rw_cells_transport; [exact A1| exact MU| exact WM| exact D1]|].
  exists cdt, thr, sec, tm1. eapply rw_cells_transport; [exact A3| exact MU| exact WM| exact D3].
Qed.

(* [comment removed for export] *)
Lemma client_sh_magree : forall (P : Z -> Prop) mx my, client_sh mx -> magree bsegs P mx my -> (forall X, In X client_sh_addrs -> P (shad X)) -> client_sh my.
Proof.
  intros P mx my CS AG HP X HX. rewrite <- (CS X HX).
  assert (B : 0x16dce0 <= X < 0x6d4000) by (unfold client_sh_addrs in HX; cbn [In] in HX; repeat (destruct HX as [<-|HX]; [lia|]); destruct HX).
  apply AG; [rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia| apply HP; exact HX].
Qed.
Lemma ATEXIT_magree : forall (P : Z -> Prop) tbl mx my, ATEXIT tbl mx -> magree bsegs P mx my -> (forall a, 0x6d1ef8 <= a < 0x6d2118 -> P a) -> ATEXIT tbl my.
Proof.
  intros P tbl mx my AT AG HP. eapply ATEXIT_transport; [| exact AT]. intros A cs HA HB RW.
  eapply rw_cells_magree; [exact AG| exact RW|]. intros a Ha. apply HP. lia.
Qed.
Lemma atexit_rt_magree : forall (P : Z -> Prop) mx my, atexit_rt mx -> magree bsegs P mx my ->
  (forall a, 0x175cc0 <= a < 0x175cc8 \/ 0x6d2138 <= a < 0x6d2140 -> P a) -> atexit_rt my.
Proof.
  intros P mx my (A1 & (cdt & thr & sec & tm1 & A3)) AG HP. unfold atexit_rt.
  split; [eapply rw_cells_magree; [exact AG| exact A1|]; cbn; intros a Ha; apply HP; lia|].
  exists cdt, thr, sec, tm1. eapply rw_cells_magree; [exact AG| exact A3|]. cbn. intros a Ha. apply HP. lia.
Qed.

Lemma atx_rest_transport : forall W fj aj mx my, atx_rest fj aj mx -> munch W mx my -> wmono bsegs mx my ->
  disjoint_from W 0x6d1ef8 8 -> disjoint_from W 0x6d1f08 48 -> disjoint_from W 0x6d1f48 208 -> disjoint_from W 0x6d2018 32 -> disjoint_from W 0x6d2048 208 ->      (* [comment removed for export] *)
  atx_rest fj aj my.
Proof.
  intros W fj aj mx my (C1' & C2 & C4' & C5 & F0 & F2 & A0 & A2 & L1 & L2) MU WM D1 D2 D3 D4 D5.
  unfold atx_rest, ATX_FIN, ATX_LOCK, ATX_HEAD, ATX_BUILTIN, ATX_F, ATX_A in *.
  Ltac dsub D := eapply disjoint_from_sub'; [exact D| lia| lia| lia].
  split; [eapply rw_cells_transport; [exact C1'| exact MU| exact WM| cbn; dsub D1]|].
  split; [eapply rw_cells_transport; [exact C2| exact MU| exact WM| cbn; dsub D1]|].
  split; [eapply rw_cells_transport; [exact C4'| exact MU| exact WM| cbn; dsub D2]|].
  split; [eapply rw_cells_transport; [exact C5| exact MU| exact WM| cbn; dsub D2]|].
  split; [eapply rw_cells_transport; [exact F0| exact MU| exact WM| cbn; dsub D2]|].
  split; [eapply rw_cells_transport; [exact F2| exact MU| exact WM| rewrite cells_size_map_C8, L1; dsub D3]|].
  split; [eapply rw_cells_transport; [exact A0| exact MU| exact WM| cbn; dsub D4]|].
  split; [eapply rw_cells_transport; [exact A2| exact MU| exact WM| rewrite cells_size_map_C8, L2; dsub D5]|].
  split; assumption.
Qed.

(* [comment removed for export] *)
Section Pres.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.

  Ltac pick_in := (left; reflexivity) + (right; pick_in).
  Ltac in_cr := apply IMG_CI; unfold client_ranges; pick_in.
  Ltac xp_img HPR := eapply aheap_pres_rw_cells; [exact HPR| eassumption|]; left; right; left; eexists; split; [in_cr| cbn; lia].

  Lemma client_sh_pres : forall LB SP m m', aheap_pres CI LB SP m m' -> client_sh m -> client_sh m'.
  Proof.
    intros LB SP m m' HPR CS X HX. specialize (CS X HX). unfold client_sh_addrs in HX. cbn [In] in HX.
    destruct HX as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]].      (* [comment removed for export] *)
    - change (shad 0x16e020) with (shad 0x16e010 + 2) in *. eapply (shadow_byte_pres CI LB SP m m' 0x16e010 64 2); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x16e038) with (shad 0x16e010 + 5) in *. eapply (shadow_byte_pres CI LB SP m m' 0x16e010 64 5); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x6afb00) with (shad 0x6afb00 + 0) in *. eapply (shadow_byte_pres CI LB SP m m' 0x6afb00 64 0); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x6afb08) with (shad 0x6afb00 + 1) in *. eapply (shadow_byte_pres CI LB SP m m' 0x6afb00 64 1); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x6afb10) with (shad 0x6afb00 + 2) in *. eapply (shadow_byte_pres CI LB SP m m' 0x6afb00 64 2); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x6afc60) with (shad 0x6afc60 + 0) in *. eapply (shadow_byte_pres CI LB SP m m' 0x6afc60 8 0); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x6afc80) with (shad 0x6afc80 + 0) in *. eapply (shadow_byte_pres CI LB SP m m' 0x6afc80 44 0); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x6afca8) with (shad 0x6afc80 + 5) in *. eapply (shadow_byte_pres CI LB SP m m' 0x6afc80 44 5); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x16e030) with (shad 0x16e010 + 4) in *. eapply (shadow_byte_pres CI LB SP m m' 0x16e010 64 4); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x16de58) with (shad 0x16de50 + 1) in *. eapply (shadow_byte_pres CI LB SP m m' 0x16de50 16 1); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
  Qed.

  Lemma atexit_rt_pres : forall LB SP m m', aheap_pres CI LB SP m m' -> atexit_rt m -> atexit_rt m'.
  Proof.
    intros LB SP m m' HPR (A1 & (cdt & thr & sec & tm1 & A3)). unfold atexit_rt.
    split; [xp_img HPR|]. exists cdt, thr, sec, tm1; xp_img HPR.
  Qed.
  Lemma ATEXIT_pres : forall tbl LB SP m m', aheap_pres CI LB SP m m' -> ATEXIT tbl m -> ATEXIT tbl m'.
  Proof.
    intros tbl LB SP m m' HPR AT. eapply ATEXIT_transport; [| exact AT]. intros A cs HA HB RW.
    eapply aheap_pres_rw_cells; [exact HPR| exact RW|]. left; right; left. eexists. split; [in_cr| cbn; lia].
  Qed.

  Lemma client_static_pres : forall s LB SP m m', aheap_pres CI LB SP m m' -> client_static s LB m -> client_static s LB m'.
  Proof.
    intros s LB SP m m' HPR (AR & AT & CS). split; [eapply atexit_rt_pres; eassumption|]. split; [eapply ATEXIT_pres; eassumption|].
    unfold AVEC, AVEC_GUARD, AFALLBACK, guard0, guard1 in *.
    destruct (aps_cl s) as [p|].
    - destruct CS as (V & HIN & C0 & C1' & C2 & C3 & C4' & C5 & C6 & C7 & C8'). exists V. split; [exact HIN|].
      split. { eapply aheap_pres_rw_cells; [exact HPR| exact C0|]. right; left. exists (HB p V 8). split; [exact HIN| cbn; lia]. }
      split; [xp_img HPR|]. split; [xp_img HPR|]. split; [xp_img HPR|]. split; [xp_img HPR|]. split; [xp_img HPR|].
      split; [xp_img HPR|]. split; [xp_img HPR|]. xp_img HPR.
    - destruct CS as (C1' & C2 & C3 & C4' & C5 & C6 & C7 & C8' & WSH).
      split; [xp_img HPR|]. split; [xp_img HPR|]. split; [xp_img HPR|]. split; [xp_img HPR|]. split; [xp_img HPR|].
      split; [xp_img HPR|]. split; [xp_img HPR|]. split; [xp_img HPR|].
      eapply aheap_pres_wr_at; [exact HPR| exact WSH|]. right; right. right; left. exists (0x6afb00, 0x6afb40). split; [in_cr|].
      cbn [fst snd]. rewrite shad_div. unfold ASHOFF. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma client_static0_pres : forall LB SP m m', aheap_pres CI LB SP m m' -> client_static0 m -> client_static0 m'.
  Proof.
    intros LB SP m m' HPR (AR & AT & CS). split; [eapply atexit_rt_pres; eassumption|]. split; [eapply ATEXIT_pres; eassumption|].
    unfold AVEC, AVEC_GUARD, AFALLBACK, guard0, guard1 in *.
    destruct CS as (C1' & C2 & C3 & C4' & C5 & C6 & C7 & C8' & WSH).
    split; [xp_img HPR|]. split; [xp_img HPR|]. split; [xp_img HPR|]. split; [xp_img HPR|]. split; [xp_img HPR|].
    split; [xp_img HPR|]. split; [xp_img HPR|]. split; [xp_img HPR|].
    eapply aheap_pres_wr_at; [exact HPR| exact WSH|]. right; right. right; left. exists (0x6afb00, 0x6afb40). split; [in_cr|].
    cbn [fst snd]. rewrite shad_div. unfold ASHOFF. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac relro_cell R A v := eapply rw_cells_recast; [apply (rw_cells_image0 bsegs _ A (le8 (Z_to_bv 64 v)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
  (* [comment removed for export] *)
  Lemma client_got_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> mem_inv bsegs m -> rw_cells bsegs m AGOT_SUAR [C8 (Z_to_bv 64 ASUAR)].
  Proof.
    intros L RNG st LB m AH MI. pose proof (AI_relro AI L RNG st LB m AH) as R. unfold ARELRO_LO, ARELRO_HI in R.
    unfold AGOT_SUAR, ASUAR. relro_cell R 0x173d30 0x17d480.
  Qed.
  (* [comment removed for export] *)
  Definition client_x_addr (a : Z) : Prop := (AMSG_SH <= a < AMSG_SH + 16) \/ (AJT_SH <= a < AJT_SH + 96) \/ (AJT <= a < AJT + 768) \/ (AREAL_STRLEN <= a < AREAL_STRLEN + 8).   (* [comment removed for export] *)
  Lemma client_x_magree : forall (P : Z -> Prop) mx my, client_x mx -> magree bsegs P mx my -> (forall a, client_x_addr a -> P a) -> client_x my.
  Proof.
    intros P mx my X AG HP. unfold client_x, client_x_addr, AMSG_SH, AJT_SH, AJT, AREAL_STRLEN in *. destruct X as (X1 & X2 & X3 & X4).
    split; [| split; [| split]].
    - intros i Hi. rewrite <- (X1 i Hi). apply AG; [lia| apply HP; lia].
    - intros i Hi. rewrite <- (X2 i Hi). apply AG; [lia| apply HP; lia].
    - eapply rw_cells_magree; [exact AG| exact X3|]. cbn. intros a Ha. apply HP. lia.
    - eapply rw_cells_magree; [exact AG| exact X4|]. cbn. intros a Ha. apply HP. lia.   (* [comment removed for export] *)
  Qed.
  Lemma client_x_pres : forall LB SP m m', aheap_pres CI LB SP m m' -> client_x m -> client_x m'.
  Proof.
    intros LB SP m m' HPR X. eapply client_x_magree; [exact X| exact HPR|]. unfold client_x_addr, AMSG_SH, AJT_SH, AJT, AREAL_STRLEN. intros a [Ha|[Ha|[Ha|Ha]]].
    - right; right; right. exists (8 * (a - ASHOFF)). split; [| rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia].
      right; left. exists (0x24480, 0x24500). split; [in_cr| cbn [fst snd]; unfold ASHOFF; lia].
    - right; right; right. exists (8 * (a - ASHOFF)). split; [| rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia].
      right; left. exists (0x178460, 0x178760). split; [in_cr| cbn [fst snd]; unfold ASHOFF; lia].
    - right; left. exists (0x178460, 0x178760). split; [in_cr| cbn [fst snd]; lia].
    - right; left. exists (0x175b28, 0x175b30). split; [in_cr| cbn [fst snd]; lia].   (* [comment removed for export] *)
  Qed.
  Lemma client_goterrc_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> mem_inv bsegs m -> rw_cells bsegs m AGOT_ERRC [C8 (Z_to_bv 64 AERRC)].
  Proof.
    intros L RNG st LB m AH MI. pose proof (AI_relro AI L RNG st LB m AH) as R. unfold ARELRO_LO, ARELRO_HI in R.
    unfold AGOT_ERRC, AERRC. relro_cell R 0x174958 0x16dd60.
  Qed.
  Lemma client_img_magree : forall (P : Z -> Prop) L RNG st LB mx my, client_img mx -> magree bsegs P mx my ->
    (forall a, (0x16e020 <= a < 0x16e040) \/ (AERRC + 240 <= a < AERRC + 256) \/ client_x_addr a -> P a) -> AHEAP AI L RNG st LB my -> mem_inv bsegs my -> client_img my.
  Proof.
    intros P L RNG st LB mx my (_ & V1 & V2 & V3 & _ & M1 & X) AG HP AH MI. unfold client_img, AVTAB_SRS, AVTAB_VU8, AVTAB_MIN in *.
    split; [eapply client_got_of_aheap; eassumption|].
    split; [eapply rw_cells_magree; [exact AG| exact V1|]; cbn; intros a Ha; apply HP; left; lia|].
    split; [eapply rw_cells_magree; [exact AG| exact V2|]; cbn; intros a Ha; apply HP; left; lia|].
    split; [eapply rw_cells_magree; [exact AG| exact V3|]; cbn; intros a Ha; apply HP; left; lia|].
    split; [eapply client_goterrc_of_aheap; eassumption|].
    split; [eapply rw_cells_magree; [exact AG| exact M1|]; cbn; intros a Ha; apply HP; right; left; lia|].
    eapply client_x_magree; [exact X| exact AG|]. intros a Ha. apply HP. right; right. exact Ha.
  Qed.
  Lemma client_img_pres : forall L RNG st LB' LB SP mx my, client_img mx -> aheap_pres CI LB SP mx my ->
    AHEAP AI L RNG st LB' my -> mem_inv bsegs my -> client_img my.
  Proof.
    intros L RNG st LB' LB SP mx my IG HPR AH MI. eapply (client_img_magree _ _ _ _ _ mx my IG HPR); [| exact AH| exact MI].
    intros a [Ha|[Ha|Ha]].
    - right; left. exists (0x16e010, 0x16e050). split; [in_cr| cbn; lia].
    - right; left. exists (0x16de50, 0x16de60). split; [in_cr| unfold AERRC in Ha; cbn; lia].
    - unfold client_x_addr, AMSG_SH, AJT_SH, AJT, AREAL_STRLEN in Ha. destruct Ha as [Ha|[Ha|[Ha|Ha]]].
      + right; right; right. exists (8 * (a - ASHOFF)). split; [| rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia].
        right; left. exists (0x24480, 0x24500). split; [in_cr| cbn [fst snd]; unfold ASHOFF; lia].
      + right; right; right. exists (8 * (a - ASHOFF)). split; [| rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia].
        right; left. exists (0x178460, 0x178760). split; [in_cr| cbn [fst snd]; unfold ASHOFF; lia].
      + right; left. exists (0x178460, 0x178760). split; [in_cr| cbn [fst snd]; lia].
      + right; left. exists (0x175b28, 0x175b30). split; [in_cr| cbn [fst snd]; lia].   (* [comment removed for export] *)
  Qed.

  Lemma atexit_got_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> mem_inv bsegs m -> rw_cells bsegs m 0x174938 [C8 (Z_to_bv 64 16)].
  Proof.
    intros L RNG st LB m AH MI. pose proof (AI_relro AI L RNG st LB m AH) as R. unfold ARELRO_LO, ARELRO_HI in R. relro_cell R 0x174938 16.
  Qed.

  (* [comment removed for export] *)
  Lemma client_rt_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m ->
    rt_got m /\ rt_got_ric m /\ rt_real_mem m /\ rt_shbase m /\ rt_suar m /\ rt_inited m /\ rt_layout m.
  Proof.
    intros L RNG st LB m AH. pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & A & B & C & D & E & F & G & _).
    split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [exact E|]. split; [exact F| exact G].
  Qed.
End Pres.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma unpoisoned_fake_pres : forall CI LB SP m m' lo hi cls FA FN,
  aheap_pres CI LB SP m m' -> unpoisoned m lo hi ->
  In (mkABlock (ABFake cls) FA FN) LB -> FA <= lo -> hi <= FA + FN -> lo mod 8 = 0 -> 0 <= FA -> FA + FN <= KEND ->
  unpoisoned m' lo hi.
Proof.
  intros CI LB SP m m' lo hi cls FA FN HP U HIN H1 H2 L8 F0 FK.
  eapply unpoisoned_agree; [exact U|]. intros s Hs.
  rewrite !shad_div in Hs. unfold ASHOFF, KEND in *.
  rewrite <- (shad_unshad s).
  apply (aheap_pres_shadow CI LB SP m m' (8 * (s - ASHOFF)) HP).
  - right; right. exists cls, FA, FN. split; [exact HIN|]. unfold ASHOFF. clear - Hs H1 H2 L8. Z.div_mod_to_equations. lia.
  - rewrite shad_unshad. unfold ASHOFF. clear - Hs H1 H2 F0 FK. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma aclient_addr_mono_sp : forall CI LB SP SP' a, aclient_addr CI LB SP a -> SP' <= SP -> aclient_addr CI LB SP' a.
Proof.
  intros CI LB SP SP' a Hc HS.
  destruct Hc as [Hc|[Hc|[Hc|(a' & Ha' & ->)]]]; [left; lia| right; left; exact Hc| right; right; left; exact Hc|].
  right; right; right. exists a'. split; [| reflexivity]. destruct Ha' as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
Qed.

Lemma aclient_addr_mono_lb : forall CI LB LB' SP a, aclient_addr CI LB SP a -> (forall b, In b LB -> In b LB') -> aclient_addr CI LB' SP a.
Proof.
  intros CI LB LB' SP a Hc HL.
  destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|(a' & Ha' & ->)]]]; [left; exact Hc| right; left; exact Hc| |].
  - right; right; left. exists b. split; [apply HL; exact Hb| exact Hr].
  - right; right; right. exists a'. split; [| reflexivity]. destruct Ha' as [H|[H|(c & A & n & Hin & Hr)]]; [left; exact H| right; left; exact H|].
    right; right. exists c, A, n. split; [apply HL; exact Hin| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma unpoisoned_client_pres : forall CI LB SP m m' lo hi,
  aheap_pres CI LB SP m m' -> unpoisoned m lo hi ->
  (forall a', lo <= a' < hi -> (ATOP <= a' < 2^47) \/ in_ranges CI a' \/ in_fake LB a') ->   (* [comment removed for export] *)
  lo mod 8 = 0 -> 0 <= lo -> hi <= KEND ->
  unpoisoned m' lo hi.
Proof.
  intros CI LB SP m m' lo hi HP U HC L8 L0 HK.
  eapply unpoisoned_agree; [exact U|]. intros s Hs.
  rewrite !shad_div in Hs. unfold ASHOFF, KEND in *.
  rewrite <- (shad_unshad s).
  apply (aheap_pres_shadow CI LB SP m m' (8 * (s - ASHOFF)) HP).
  - apply HC. unfold ASHOFF. clear - Hs L8 L0 HK. Z.div_mod_to_equations. lia.
  - rewrite shad_unshad. unfold ASHOFF. clear - Hs L0 HK. Z.div_mod_to_equations. lia.
Qed.

Lemma implMA_bind_assoc : forall {X Y W} RNG (ma : Monad.M APS X) (g : X -> Monad.M APS Y) (f : Y -> Monad.M APS W) s Q ms,
  implMA RNG (Monad.mbind ma (fun a => Monad.mbind (g a) f)) s Q ms -> implMA RNG (Monad.mbind (Monad.mbind ma g) f) s Q ms.
Proof.
  intros X Y W RNG ma g f s Q ms H. unfold implMA, Monad.mbind, ebind in *.
  apply implF_bind_assoc. eapply implF_bind_cong; [| exact H].
  intros [|[a s']] RNG' ms'; cbn [ITree.bind fst snd]; intros H'; exact H'.
Qed.
Lemma implMA_updb : forall {B} RNG f (k : unit -> Monad.M APS B) (s : APS) Q ms,
  implMA RNG (k tt) (f s) Q ms -> implMA RNG (Monad.mbind (Monad.mupd f) k) s Q ms.
Proof. intros B RNG f k s Q ms H. exact H. Qed.
End CANSEC1.

(* [comment removed for export] *)
Ltac wfar1 :=
  cbn [fst snd];
  first [ apply wfar_high; unfold KHIGH in *; lia
        | apply wfar_shad; rewrite ?Z.shiftr_div_pow2 by lia; rewrite ?shad_div; unfold ASHOFF, AIMG_HI in *; Z.div_mod_to_equations; lia
        | match goal with H : ablk _ _ |- _ => eapply (wfar_ablk _ _ _ _ H); lia end
        | match goal with H : ablock_range _ _ |- _ => eapply (wfar_ablk _ _ _ _ (proj1 H)); lia end
        | apply wfar_of_wclr; match goal with H : Forall wclr _ |- _ => eapply (proj1 (Forall_forall wclr _) H); cbn; tauto end ].
Ltac fw_far :=
  lazymatch goal with
  | |- Forall wfar (_ ++ _) => apply Forall_app; split; fw_far
  | |- Forall wfar (_ :: _) => constructor; [wfar1| fw_far]
  | |- Forall wfar [] => constructor
  | |- Forall wfar ?W => first [assumption| apply Forall_wfar_of_wclr; assumption| fail 1 "fw_far: abstract write set" W]
  end.
