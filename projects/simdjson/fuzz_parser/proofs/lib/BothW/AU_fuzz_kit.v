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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells AProto ABase MonadF AMalloc_iface ABytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma page_round_up_geA : forall x, 0 <= x -> x <= page_round_up_Z x < x + 4096 /\ page_round_up_Z x mod 4096 = 0.
Proof. intros x Hx. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia. Qed.

Lemma harness_top : forall L SP, SP + 208 = al_sp0 L -> 0 <= SP -> SP + 16 <= al_top L < SP + 48 + 4096.
Proof.
  intros L SP E H0. unfold al_top. rewrite <- E. replace (SP + 208 - 160) with (SP + 48) by lia.
  pose proof (page_round_up_geA (SP + 48) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma byte_of_c1 : forall m s b, rw_cells bsegs m s [C1 b] -> 0x671000 <= s -> m (wa s) = Some b.
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
Definition wfar (iv : Z * Z) : Prop := AIMG_HI <= fst iv /\ (snd iv <= KLS \/ 0x800c6200 <= fst iv).
Lemma wfar_of_wclr : forall iv, wclr iv -> wfar iv.
Proof. intros [lo hi] [A B]. unfold wfar, sclr, KLS in *. cbn [fst snd] in *. lia. Qed.
Lemma Forall_wfar_of_wclr : forall W, Forall wclr W -> Forall wfar W.
Proof. intros W FW. eapply Forall_impl; [| exact FW]. intros iv H. apply wfar_of_wclr. exact H. Qed.
Lemma wfar_high : forall lo hi, 0x10007fff8000 <= lo -> wfar (lo, hi).
Proof. intros lo hi H. unfold wfar, AIMG_HI. cbn [fst snd]. lia. Qed.
Lemma wfar_ablk : forall lo hi a b, ablk lo hi -> lo <= a -> b <= hi -> wfar (a, b).
Proof. intros lo hi a b H A B. apply wfar_of_wclr. eapply wclr_ablk; [exact H| exact A| exact B]. Qed.
Lemma wfar_shad : forall lo hi, 0x800c6200 <= lo -> wfar (lo, hi).
Proof. intros lo hi H. unfold wfar, AIMG_HI. cbn [fst snd]. lia. Qed.
Lemma wfar_outside : forall W a, Forall wfar W -> (a < AIMG_HI \/ KLS <= a < 0x800c6200) -> outside W a.
Proof.
  intros W a FW Ha. induction W as [|[wlo whi] W IH]; [exact I|]. inversion FW as [|x l F1 FW']; subst.
  unfold wfar, AIMG_HI, KLS in F1, Ha. cbn in F1 |- *. split; [lia| apply IH; exact FW'].
Qed.
Lemma wfar_disjoint : forall W a n, Forall wfar W -> (a + n <= AIMG_HI \/ (KLS <= a /\ a + n <= 0x800c6200)) -> disjoint_from W a n.
Proof.
  intros W a n FW Ha. induction W as [|[wlo whi] W IH]; [exact I|]. inversion FW as [|x l F1 FW']; subst.
  unfold wfar, AIMG_HI, KLS in F1, Ha. cbn in F1 |- *. split; [lia| apply IH; exact FW'].
Qed.

(* [comment removed for export] *)
Lemma client_sh_munch32 : forall W mx my, client_sh mx -> munch W mx my -> Forall wfar W -> client_sh my.
Proof.
  intros W mx my CS MU FW X HX. rewrite <- (CS X HX). apply MU.
  unfold client_sh_addrs in HX. cbn [In] in HX.
  assert (B : 0x10f580 <= X < 0x671000) by (repeat (destruct HX as [<-|HX]; [lia|]); destruct HX).
  rewrite wa_unsigned by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
  apply wfar_outside; [exact FW|]. right. rewrite shad_div. unfold ASHOFF, KLS. Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma client_x_munch32 : forall W mx my, client_x mx -> munch W mx my -> wmono bsegs mx my -> Forall wfar W -> client_x my.
Proof.
  intros W mx my (X1 & X2 & X3 & X4 & X5) MU WM FW.
  assert (X5' : img_sh my).
  { unfold img_sh in *. apply Forall_forall. intros [lo hi] Hin. pose proof (proj1 (Forall_forall _ _) X5 _ Hin) as T.
    unfold tab_sh in T |- *. cbn [fst snd] in T |- *. pose proof (img_tabs_bounds lo hi Hin) as (B1 & B2 & B3 & B4 & B5).
    eapply rw_cells_transport; [exact T| exact MU| exact WM|]. apply wfar_disjoint; [exact FW|]. right.
    cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; lia). rewrite shad_div. unfold ASHOFF, KLS. Z.div_mod_to_equations. lia. }
  unfold client_x, rt_real_mc, rt_fmin, rt_bom_sh, rt_ctab_sh in *.
  split; [| split; [| split; [| split; [| exact X5']]]]; (eapply rw_cells_transport; [eassumption| exact MU| exact WM|]); apply wfar_disjoint; try exact FW;
    [ left; unfold AREAL_MC, AIMG_HI; cbn; lia | left; unfold AFMIN, AIMG_HI; cbn; lia
    | right; rewrite shad_div; unfold ABOM, ASHOFF, KLS; cbn [cells_size csize]; Z.div_mod_to_equations; lia
    | right; rewrite shad_div; unfold ACTAB, ASHOFF, KLS; cbn [cells_size csize]; Z.div_mod_to_equations; lia ].
Qed.
Lemma client_img_munch32 : forall W mx my, client_img mx -> munch W mx my -> wmono bsegs mx my -> Forall wfar W -> client_img my.
Proof.
  intros W mx my (I1 & I2 & I3 & IX) MU WM FW. unfold client_img, AGOT_SUAR, ASUAR, AVTAB_IMPL, AVTAB_DOM, vtab_impl_cells, vtab_dom_cells in *.
  split; [| split; [| split]]; [ .. | exact (client_x_munch32 W mx my IX MU WM FW)];
    (eapply rw_cells_transport; [eassumption| exact MU| exact WM|]); apply wfar_disjoint; try exact FW; left; unfold AIMG_HI; cbn; lia.
Qed.
Lemma harness_inv_munch32 : forall W mx my, harness_invA mx -> munch W mx my -> wmono bsegs mx my -> Forall wfar W -> harness_invA my.
Proof. intros W mx my [A B] MU WM FW. split; [eapply client_img_munch32| eapply client_sh_munch32]; eassumption. Qed.

Ltac xt_img MU WM FW := eapply rw_cells_transport; [eassumption| exact MU| exact WM|]; apply wfar_disjoint; [exact FW|]; left; unfold AIMG_HI; cbn; lia.

Lemma cells_size_map_C8 : forall ws : list word, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. lia. Qed.

(* [comment removed for export] *)
Lemma client_static_munch32 : forall W s LB mx my, client_static s LB mx -> munch W mx my -> wmono bsegs mx my -> Forall wfar W ->
  client_static s LB my.
Proof.
  intros W s LB mx my CS MU WM FW. unfold client_static, client_static0, client_static1, AACTIVE, AACTIVE_GUARD, AFALLBACK, AFALLBACK_GUARD, fallback_cells, guard0, guard1 in *.
  destruct CS as [CL [(C1' & C2 & C3 & C4') | (C1' & C2 & C3 & C4')]]; (split; [exact CL|]); [left| right]; repeat (split; [xt_img MU WM FW|]); xt_img MU WM FW.
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
  assert (B : 0x10f580 <= X < 0x671000) by (unfold client_sh_addrs in HX; cbn [In] in HX; repeat (destruct HX as [<-|HX]; [lia|]); destruct HX).
  rewrite wa_unsigned by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia). apply OW. exact HX.
Qed.
Lemma client_x_munch_gen : forall W mx my, client_x mx -> munch W mx my -> wmono bsegs mx my ->
  disjoint_from W AREAL_MC 16 -> disjoint_from W AFMIN 4 -> disjoint_from W (shad ABOM) 8 -> disjoint_from W (shad ACTAB) 32 ->
  (forall lo hi, In (lo, hi) IMG_TABS -> disjoint_from W (shad lo) ((hi - lo) / 8)) ->
  client_x my.
Proof.
  intros W mx my (X1 & X2 & X3 & X4 & X5) MU WM D1 D2 D3 D4 D5. unfold client_x, rt_real_mc, rt_fmin, rt_bom_sh, rt_ctab_sh in *.
  split; [eapply rw_cells_transport; [exact X1| exact MU| exact WM| exact D1]|].
  split; [eapply rw_cells_transport; [exact X2| exact MU| exact WM| exact D2]|].
  split; [eapply rw_cells_transport; [exact X3| exact MU| exact WM| exact D3]|].
  split; [eapply rw_cells_transport; [exact X4| exact MU| exact WM| exact D4]|].
  unfold img_sh in *. apply Forall_forall. intros [lo hi] Hin. pose proof (proj1 (Forall_forall _ _) X5 _ Hin) as T.
  unfold tab_sh in T |- *. cbn [fst snd] in T |- *. pose proof (img_tabs_bounds lo hi Hin) as (B1 & B2 & B3 & B4 & B5).
  eapply rw_cells_transport; [exact T| exact MU| exact WM|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; lia).
  exact (D5 lo hi Hin).
Qed.
Lemma client_img_munch_gen : forall W mx my, client_img mx -> munch W mx my -> wmono bsegs mx my ->
  disjoint_from W 0x112ad8 8 -> disjoint_from W 0x10f610 48 -> disjoint_from W 0x10f6d0 80 ->
  disjoint_from W AREAL_MC 16 -> disjoint_from W AFMIN 4 -> disjoint_from W (shad ABOM) 8 -> disjoint_from W (shad ACTAB) 32 ->
  (forall lo hi, In (lo, hi) IMG_TABS -> disjoint_from W (shad lo) ((hi - lo) / 8)) ->
  client_img my.
Proof.
  intros W mx my (I1 & I2 & I3 & IX) MU WM D1 D2 D3 D4 D5 D6 D7 D8. unfold client_img, AGOT_SUAR, AVTAB_IMPL, AVTAB_DOM, vtab_impl_cells, vtab_dom_cells in *.
  split; [eapply rw_cells_transport; [exact I1| exact MU| exact WM| exact D1]|].
  split; [eapply rw_cells_transport; [exact I2| exact MU| exact WM| exact D2]|].
  split; [eapply rw_cells_transport; [exact I3| exact MU| exact WM| exact D3]| exact (client_x_munch_gen W mx my IX MU WM D4 D5 D6 D7 D8)].
Qed.
(* [comment removed for export] *)
Lemma client_sh_magree : forall (P : Z -> Prop) mx my, client_sh mx -> magree bsegs P mx my -> (forall X, In X client_sh_addrs -> P (shad X)) -> client_sh my.
Proof.
  intros P mx my CS AG HP X HX. rewrite <- (CS X HX).
  assert (B : 0x10f580 <= X < 0x671000) by (unfold client_sh_addrs in HX; cbn [In] in HX; repeat (destruct HX as [<-|HX]; [lia|]); destruct HX).
  apply AG; [rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia| apply HP; exact HX].
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
    destruct HX as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]]]]]]]]]].
    - change (shad 0x10f610) with (shad 0x10f610 + 0) in *. eapply (shadow_byte_pres CI LB SP m m' 0x10f610 48 0); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x10f618) with (shad 0x10f610 + 1) in *. eapply (shadow_byte_pres CI LB SP m m' 0x10f610 48 1); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x10f620) with (shad 0x10f610 + 2) in *. eapply (shadow_byte_pres CI LB SP m m' 0x10f610 48 2); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x10f628) with (shad 0x10f610 + 3) in *. eapply (shadow_byte_pres CI LB SP m m' 0x10f610 48 3); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x10f630) with (shad 0x10f610 + 4) in *. eapply (shadow_byte_pres CI LB SP m m' 0x10f610 48 4); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x10f638) with (shad 0x10f610 + 5) in *. eapply (shadow_byte_pres CI LB SP m m' 0x10f610 48 5); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x10f6d0) with (shad 0x10f6d0 + 0) in *. eapply (shadow_byte_pres CI LB SP m m' 0x10f6d0 80 0); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x10f6d8) with (shad 0x10f6d0 + 1) in *. eapply (shadow_byte_pres CI LB SP m m' 0x10f6d0 80 1); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x10f6e0) with (shad 0x10f6d0 + 2) in *. eapply (shadow_byte_pres CI LB SP m m' 0x10f6d0 80 2); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x10f6e8) with (shad 0x10f6d0 + 3) in *. eapply (shadow_byte_pres CI LB SP m m' 0x10f6d0 80 3); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x10f6f0) with (shad 0x10f6d0 + 4) in *. eapply (shadow_byte_pres CI LB SP m m' 0x10f6d0 80 4); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x10f6f8) with (shad 0x10f6d0 + 5) in *. eapply (shadow_byte_pres CI LB SP m m' 0x10f6d0 80 5); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x10f700) with (shad 0x10f6d0 + 6) in *. eapply (shadow_byte_pres CI LB SP m m' 0x10f6d0 80 6); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x10f708) with (shad 0x10f6d0 + 7) in *. eapply (shadow_byte_pres CI LB SP m m' 0x10f6d0 80 7); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x10f710) with (shad 0x10f6d0 + 8) in *. eapply (shadow_byte_pres CI LB SP m m' 0x10f6d0 80 8); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x10f718) with (shad 0x10f6d0 + 9) in *. eapply (shadow_byte_pres CI LB SP m m' 0x10f6d0 80 9); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x64dd80) with (shad 0x64dd80 + 0) in *. eapply (shadow_byte_pres CI LB SP m m' 0x64dd80 8 0); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x64dda0) with (shad 0x64dda0 + 0) in *. eapply (shadow_byte_pres CI LB SP m m' 0x64dda0 2 0); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x64de20) with (shad 0x64de20 + 0) in *. eapply (shadow_byte_pres CI LB SP m m' 0x64de20 48 0); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x64de28) with (shad 0x64de20 + 1) in *. eapply (shadow_byte_pres CI LB SP m m' 0x64de20 48 1); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x64de30) with (shad 0x64de20 + 2) in *. eapply (shadow_byte_pres CI LB SP m m' 0x64de20 48 2); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x64de38) with (shad 0x64de20 + 3) in *. eapply (shadow_byte_pres CI LB SP m m' 0x64de20 48 3); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x64de40) with (shad 0x64de20 + 4) in *. eapply (shadow_byte_pres CI LB SP m m' 0x64de20 48 4); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x64de48) with (shad 0x64de20 + 5) in *. eapply (shadow_byte_pres CI LB SP m m' 0x64de20 48 5); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
    - change (shad 0x64de80) with (shad 0x64de80 + 0) in *. eapply (shadow_byte_pres CI LB SP m m' 0x64de80 2 0); [exact HPR| in_cr| reflexivity| lia| lia| lia| lia| exact CS].
  Qed.

  Lemma client_static_pres : forall s LB SP m m', aheap_pres CI LB SP m m' -> client_static s LB m -> client_static s LB m'.
  Proof.
    intros s LB SP m m' HPR CS. unfold client_static, client_static0, client_static1, AACTIVE, AACTIVE_GUARD, AFALLBACK, AFALLBACK_GUARD, fallback_cells, guard0, guard1 in *.
    destruct CS as [CL [(C1' & C2 & C3 & C4') | (C1' & C2 & C3 & C4')]]; (split; [exact CL|]); [left| right];
      (split; [xp_img HPR|]); (split; [xp_img HPR|]); (split; [xp_img HPR|]); xp_img HPR.
  Qed.

  (* [comment removed for export] *)
  Ltac relro_cell R A v := eapply rw_cells_recast; [apply (rw_cells_image0 bsegs _ A (le8 (Z_to_bv 64 v)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
  (* [comment removed for export] *)
  Lemma client_got_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> mem_inv bsegs m -> rw_cells bsegs m AGOT_SUAR [C8 (Z_to_bv 64 ASUAR)].
  Proof.
    intros L RNG st LB m AH MI. pose proof (AI_relro AI L RNG st LB m AH) as R. unfold ARELRO_LO, ARELRO_HI in R.
    unfold AGOT_SUAR, ASUAR. relro_cell R 0x112ad8 0x11b680.
  Qed.
  Lemma client_img_magree : forall (P : Z -> Prop) L RNG st LB mx my, client_img mx -> magree bsegs P mx my ->
    (forall a, (0x10f610 <= a < 0x10f640) \/ (0x10f6d0 <= a < 0x10f720) \/ client_x_addr a -> P a) -> AHEAP AI L RNG st LB my -> mem_inv bsegs my ->
    client_img my.
  Proof.
    intros P L RNG st LB mx my (_ & V1 & V2 & VX) AG HP AH MI. unfold client_img, AVTAB_IMPL, AVTAB_DOM, vtab_impl_cells, vtab_dom_cells in *.
    split; [eapply client_got_of_aheap; eassumption|].
    split; [eapply rw_cells_magree; [exact AG| eassumption|]; cbn; intros a Ha; apply HP; lia|].
    split; [eapply rw_cells_magree; [exact AG| eassumption|]; cbn; intros a Ha; apply HP; lia|].
    eapply client_x_magree; [exact VX| exact AG|]. intros a Ha. apply HP. right; right; exact Ha.
  Qed.
  (* [comment removed for export] *)
  Lemma client_sh_addr_of_range : forall LB SP lo hi a, In (lo, hi) client_ranges -> shad lo <= a < shad lo + (hi - lo) / 8 -> lo mod 8 = 0 ->
    (hi - lo) mod 8 = 0 -> aclient_addr CI LB SP a.
  Proof.
    intros LB SP lo hi a HIN Ha L8 H8. right; right; right. exists (8 * (a - ASHOFF)). split.
    - right; left. exists (lo, hi). split; [apply IMG_CI; exact HIN|]. cbn. rewrite shad_div in Ha. unfold ASHOFF in *. Z.div_mod_to_equations. lia.
    - rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
  Qed.
  Lemma client_img_pres : forall L RNG st LB' LB SP mx my, client_img mx -> aheap_pres CI LB SP mx my ->
    AHEAP AI L RNG st LB' my -> mem_inv bsegs my -> client_img my.
  Proof.
    intros L RNG st LB' LB SP mx my IG HPR AH MI. eapply (client_img_magree _ _ _ _ _ mx my IG HPR); [| exact AH| exact MI].
    intros a [Ha|[Ha|Ha]]; [right; left; exists (0x10f610, 0x10f640); (split; [in_cr| cbn; lia])
                           | right; left; exists (0x10f6d0, 0x10f720); (split; [in_cr| cbn; lia]) |].
    unfold client_x_addr, AREAL_MC, AFMIN in Ha.
    destruct Ha as [Ha|[Ha|[Ha|[Ha|(lo & hi & Hin & Ha)]]]];
      [ right; left; exists (0x114860, 0x114870); (split; [in_cr| cbn; lia])
      | right; left; exists (0x1174c0, 0x1174c4); (split; [in_cr| cbn; lia])
      | apply (client_sh_addr_of_range LB SP 0x22f40 0x22f80);
          [unfold client_ranges; pick_in| unfold ABOM in Ha; replace ((0x22f80 - 0x22f40) / 8) with 8 by reflexivity; exact Ha| reflexivity| reflexivity]
      | apply (client_sh_addr_of_range LB SP 0x27e00 0x27f00);
          [unfold client_ranges; pick_in| unfold ACTAB in Ha; replace ((0x27f00 - 0x27e00) / 8) with 32 by reflexivity; exact Ha| reflexivity| reflexivity]
      | pose proof (img_tabs_bounds lo hi Hin) as (B1 & B2 & B3 & B4 & B5);
        apply (client_sh_addr_of_range LB SP lo hi); [unfold client_ranges; apply in_or_app; right; exact Hin| exact Ha| exact B4| exact B5] ].
  Qed.

  (* [comment removed for export] *)
  Lemma client_rt_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m ->
    rt_got m /\ rt_got_ric m /\ rt_real_mem m /\ rt_shbase m /\ rt_suar m /\ rt_inited m /\ rt_layout m.
  Proof.
    intros L RNG st LB m AH. pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & A & B & C & D & E & F & G & _).
    split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [exact E|]. split; [exact F| exact G].
  Qed.
  (* [comment removed for export] *)
  Lemma rt_flags_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rt_flags m.
  Proof. intros L RNG st LB m AH. exact (rt_flags_of_artcells m (AI_rtcells AI _ _ _ _ _ AH)). Qed.
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
