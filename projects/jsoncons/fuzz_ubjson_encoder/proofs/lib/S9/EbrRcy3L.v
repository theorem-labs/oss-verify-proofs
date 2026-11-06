(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac EbtLeaf EbtAllocG EbtPoison EbtInitCache ArtRuns ArtRunsMem EbtFp EbtRefill1 EbtPopulate1 EbtCellEx EbtCls EbtClsRep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import EbtRecycle3 EbtRecycle3D EbtRecycle3R EbtRecycle3L EbrRcyTac EbrRcy3R EbrRcy3D.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r3ef18_4052c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_cls_return (h : nat) (cl : art_cls) : art_cls :=
  let k := (length (cl_cache cl) - h)%nat in
  CLS (firstn k (cl_cache cl)) (cl_free cl ++ skipn k (cl_cache cl)) (cl_au cl) (cl_mu cl)
      (art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + Z.of_nat h)) (cl_na cl) (cl_nfr cl + Z.of_nat h).
Definition art_cls_dealloc (c w : Z) (cl : art_cls) : art_cls :=
  if art_cls_full c cl then art_cls_push w (art_cls_return (Z.to_nat (art_ic_mc c / 2)) cl) else art_cls_push w cl.

Definition art_cls_events (spb c : Z) (cl : art_cls) : list aev :=
  if art_cls_full c cl then art_rta_events spb c (Z.of_nat (length (cl_free cl))) (art_ic_mc c / 2) (cl_mfa cl) else [].

Definition art_lcd_fp (sp t spb ris qs c nf mfa : Z) : list (Z * Z) :=
  [ (sp - 688, 688); (t + 208 + 80 * c, 4); (t + 208 + 80 * c + 16, 64); (t + 208 + 2576, 8); (ris + 128 * c, 128); (spb + c * 2 ^ 32 + 3758096384 + 4 * nf, 32);
    (spb + c * 2 ^ 32 + 3758096384 + mfa, 536870912 - mfa); (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048, 67108864); (t + 2872, 16) ].

Lemma art_cls_dealloc_mfa : forall c w cl, cl_mfa cl <= cl_mfa (art_cls_dealloc c w cl).
Proof.
  intros c w cl. unfold art_cls_dealloc. destruct (art_cls_full c cl); cbn; [|apply Z.le_refl].
  unfold art_cls_mfa'. destruct (_ <=? _) eqn:E; [apply Z.le_refl|]. apply Z.leb_gt in E.
  pose proof (Z.div_mod (4 * (Z.of_nat (length (cl_free cl)) + Z.of_nat (Z.to_nat (art_ic_mc c / 2))) + 262143) 262144 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (4 * (Z.of_nat (length (cl_free cl)) + Z.of_nat (Z.to_nat (art_ic_mc c / 2))) + 262143) 262144 ltac:(lia)) as R.
  set (q := (_ + 262143) / 262144) in *. set (rr := (_ + 262143) mod 262144) in *. clearbody q rr. lia.
Qed.

Lemma art_cls_dealloc_ok : forall c w cl, 1 <= c <= 30 -> art_cls_ok c cl -> Z.of_nat (length (cl_cache cl)) <= art_ic_mc c ->
  art_cptr_ok (AsanTab.class_size c) (cl_au cl) w -> ~ In w (cl_cache cl ++ cl_free cl) ->
  (art_cls_full c cl = true -> 4 * (Z.of_nat (length (cl_free cl)) + art_ic_mc c / 2) <= 2 ^ 29) ->
  art_cls_ok c (art_cls_dealloc c w cl).
Proof.
  intros c w cl Hc OK Hlen Hw Hnin Hroom.
  destruct OK as (L16 & Hau & Hcarve & Hmu & Hauk & Hmu' & Hmfa & Hmfa' & Hfree & Hall & Hnd).
  apply NoDup_ListNoDup in Hnd.
  destruct (art_ic_mc_half c ltac:(lia)) as (Emc & Hh). pose proof (art_ic_mc_range c ltac:(lia)) as Rmc.
  unfold art_cls_dealloc. destruct (art_cls_full c cl) eqn:EF.
  -
    unfold art_cls_full in EF. apply Z.eqb_eq in EF. specialize (Hroom eq_refl).
    set (h := Z.to_nat (art_ic_mc c / 2)). set (k := (length (cl_cache cl) - h)%nat).
    assert (Hk : (k + h = length (cl_cache cl))%nat) by (unfold k, h; lia).
    assert (PERM : Permutation (w :: cl_cache cl ++ cl_free cl) ((firstn k (cl_cache cl) ++ [w]) ++ (cl_free cl ++ skipn k (cl_cache cl)))).
    { rewrite <- (firstn_skipn k (cl_cache cl)) at 1. rewrite <- !app_assoc. cbn [app].
      eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head. apply perm_skip. apply Permutation_app_comm. }
    destruct Hmfa as (km & Ekm).
    assert (Eh : Z.of_nat h = art_ic_mc c / 2) by (unfold h; lia).
    destruct (art_mfa_grow_facts (cl_mfa cl) (Z.of_nat (length (cl_free cl)) + Z.of_nat h) km Ekm ltac:(lia) ltac:(lia)) as (Hg1 & Hg2 & Hg3).
    pose proof (art_mfa_grow_le (cl_mfa cl) (Z.of_nat (length (cl_free cl)) + Z.of_nat h) km Ekm ltac:(lia) ltac:(lia) ltac:(lia)) as Hg4.
    unfold art_cls_ok, art_cls_push, art_cls_return. cbn [cl_cache cl_free cl_au cl_mu cl_mfa]. fold h k. rewrite art_cls_mfa'_grow.
    split. { rewrite length_app, length_firstn. cbn [length]. lia. }
    split; [exact Hau|]. split; [exact Hcarve|]. split; [exact Hmu|]. split; [exact Hauk|]. split; [exact Hmu'|]. split; [exact Hg3|]. split; [lia|].
    split. { rewrite length_app, length_skipn. unfold k. lia. }
    split.
    + eapply Permutation_Forall; [exact PERM|]. constructor; assumption.
    + apply NoDup_ListNoDup. eapply Permutation_NoDup; [exact PERM|]. constructor; assumption.
  - unfold art_cls_full in EF. apply Z.eqb_neq in EF.
    assert (PERM : Permutation (w :: cl_cache cl ++ cl_free cl) ((cl_cache cl ++ [w]) ++ cl_free cl)).
    { rewrite <- app_assoc. cbn [app]. apply Permutation_middle. }
    unfold art_cls_ok, art_cls_push. cbn [cl_cache cl_free cl_au cl_mu cl_mfa].
    split. { rewrite length_app. cbn [length]. pose proof (art_ic_mc_range c ltac:(lia)). lia. }
    split; [exact Hau|]. split; [exact Hcarve|]. split; [exact Hmu|]. split; [exact Hauk|]. split; [exact Hmu'|]. split; [exact Hmfa|]. split; [exact Hmfa'|].
    split; [exact Hfree|].
    split.
    + eapply Permutation_Forall; [exact PERM|]. constructor; assumption.
    + apply NoDup_ListNoDup. eapply Permutation_NoDup; [exact PERM|]. constructor; assumption.
Qed.

Lemma art_region_rep_ret : forall spb ris c mx mx' (cl cl' : art_cls) (M M' : word -> option byte) (W : list (Z * Z)) (ws : list Z),
  let fa := spb + c * 2 ^ 32 + 3758096384 in
  let r := ris + 128 * c in
  let nf := Z.of_nat (length (cl_free cl)) in
  0 <= r -> r + 128 < 2 ^ 64 -> 0 <= fa -> fa + 2 ^ 29 < 2 ^ 64 -> 4 * nf <= 2 ^ 29 ->
  cl_free cl' = cl_free cl ++ ws -> cl_au cl' = cl_au cl -> cl_mu cl' = cl_mu cl -> cl_na cl' = cl_na cl ->
  art_region_rep spb ris c mx cl M -> mem_grows M M' -> art_agree W M M' ->
  art_gap W (r + 32) 48 -> art_gap W fa (4 * nf) ->
  cellA M' r 8 mx' -> cellA M' (r + 16) 8 (nf + Z.of_nat (length ws)) -> cellA M' (r + 24) 8 (cl_mfa cl') -> cellA M' (r + 80) 8 (cl_nfr cl') ->
  wrA M' fa (cl_mfa cl') ->
  (forall j, (j < length ws)%nat -> cellA M' (fa + 4 * (nf + Z.of_nat j)) 4 (nth j ws 0)) ->
  art_region_rep spb ris c mx' cl' M'.
Proof.
  intros spb ris c mx mx' cl cl' M M' W ws fa r nf Hr Hr' Hfa Hfa' Hnf Efree Eau Emu Ena RR G A G24 GFA Cmx Cnf Cmfa Cnfr Wfa' Cws.
  destruct RR as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
  fold r in Rmx, Rnf, Rmfa, Rau, Ram, Rmu, Rmm, Rna, Rnfr, Wr. fold fa in Rfa, Wfa. fold nf in Rnf.
  assert (Hnf0 : 0 <= nf) by (unfold nf; lia).
  unfold art_region_rep. fold r fa. rewrite Eau, Emu, Ena, Efree.
  assert (T : forall a (n : nat) v, r + 32 <= a -> a + Z.of_nat n <= r + 80 -> cellA M a n v -> cellA M' a n v).
  { intros a n v Ha Hn C. apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact G24|lia|lia]|lia|lia|exact C]. }
  split; [exact Cmx|].
  split. { rewrite length_app, Nat2Z.inj_add. exact Cnf. }
  split; [exact Cmfa|]. split; [apply T; [lia|cbn; lia|exact Rau]|]. split; [apply T; [lia|cbn; lia|exact Ram]|].
  split; [apply T; [lia|cbn; lia|exact Rmu]|]. split; [apply T; [lia|cbn; lia|exact Rmm]|]. split; [apply T; [lia|cbn; lia|exact Rna]|].
  split; [exact Cnfr|].
  split. { intros j Hj. rewrite length_app in Hj. destruct (Nat.lt_ge_cases j (length (cl_free cl))) as [Lt|Ge].
           - rewrite app_nth1 by exact Lt. pose proof (proj1 (Nat2Z.inj_lt _ _) Lt) as Hj'. fold nf in Hj'.
             apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact GFA|lia|cbn; lia]|lia|cbn; lia|apply Rfa; exact Lt].
           - rewrite app_nth2 by exact Ge. replace (Z.of_nat j) with (nf + Z.of_nat (j - length (cl_free cl))) by (unfold nf; lia). apply Cws. lia. }
  split; [eapply wr_grows; [exact G|exact Wr]|]. split; [exact Wfa'|eapply wr_grows; [exact G|exact Wu]].
Qed.

Definition art_lcd_fpF (sp ca t spb ris qs c nf h mfa : Z) : list (Z * Z) :=
  [ (sp - 688, 688); (ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8); (spb + c * 2 ^ 32 + 3758096384 + 4 * nf, 4 * h);
    (ris + 128 * c, 8); (ris + 128 * c + 16, 16); (ris + 128 * c + 80, 8);
    (spb + c * 2 ^ 32 + 3758096384 + mfa, 536870912 - mfa); (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048, 67108864); (t + 2872, 16) ].
Lemma art_lcd_fpF_sub1 : forall sp ca t spb ris qs c nf h mfa, ca = t + 208 ->
  forall z, 0 <= z < 2 ^ 64 -> art_out (art_lcd_fpF sp ca t spb ris qs c nf h mfa) z ->
  art_out ([(sp - 48, 48)] ++ [ (sp - 688, 640); (ca + 80 * c, 4); (ris + 128 * c, 8); (ris + 128 * c + 16, 16); (ris + 128 * c + 80, 8);
                                 (spb + c * 2 ^ 32 + 3758096384 + 4 * nf, 4 * h); (spb + c * 2 ^ 32 + 3758096384 + mfa, 536870912 - mfa);
                                 (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048, 67108864); (t + 2872, 16) ]
                            ++ [(ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8)]) z.
Proof. intros sp ca t spb ris qs c nf h mfa Eca. unfold art_lcd_fpF. zsubf. Qed.
Lemma art_lcd_fpF_sub2 : forall sp ca t spb ris qs c nf h mfa, ca = t + 208 -> 0 <= h <= 8 ->
  forall z, 0 <= z < 2 ^ 64 -> art_out (art_lcd_fp sp t spb ris qs c nf mfa) z -> art_out (art_lcd_fpF sp ca t spb ris qs c nf h mfa) z.
Proof. intros sp ca t spb ris qs c nf h mfa Eca Hh. unfold art_lcd_fpF, art_lcd_fp. zsubf. Qed.
Lemma art_lcd_fpF_sub3 : forall sp ca t spb ris qs c nf mfa, ca = t + 208 ->
  forall z, 0 <= z < 2 ^ 64 -> art_out (art_lcd_fp sp t spb ris qs c nf mfa) z -> art_out [(sp - 48, 48); (ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8)] z.
Proof. intros sp ca t spb ris qs c nf mfa Eca. unfold art_lcd_fp. zsubf. Qed.

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_lcd_aruns :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M rom : word -> option byte) (raw : word)
         (sp HI t ctx tp key tsd c p spb ris qs qris w sv : Z) (cl : art_cls),
    getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 (t + 208) -> getr regs 11 = Z_to_bv 64 1321624 ->
    getr regs 12 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 p ->
    art_geo HI t ctx tp tsd spb ris qs -> HI <= sp - 688 -> sp < 2 ^ 47 -> 1 <= c <= 30 -> ris = 128 * qris ->
    wrA M (sp - 688) 688 -> wrA M t 4096 -> wrA M (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048) 67108864 ->
    art_prim_consts spb ris M -> art_layout M -> art_tsd M tp key tsd ctx t ->
    art_pc_hdr (t + 208) true M -> art_cls_rep (t + 208) spb ris c cl M -> art_cls_ok c cl ->
    Z.of_nat (length (cl_cache cl)) <= art_ic_mc c ->
    p = spb + c * 2 ^ 32 + 16 * w -> 0 <= w < 2 ^ 28 ->
    cellA M (t + 208 + 2576) 8 sv ->
    (art_cls_full c cl = true -> 4 * (Z.of_nat (length (cl_free cl)) + art_ic_mc c / 2) <= 2 ^ 29) ->
    art_evok_list EVOK log (art_cls_events spb c cl) ->
    (forall regs' (M' : word -> option byte),
        getr regs' 2 = Z_to_bv 64 sp ->
        (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x) ->
        mem_grows M M' ->
        art_agree (art_lcd_fp sp t spb ris qs c (Z.of_nat (length (cl_free cl))) (cl_mfa cl)) M M' ->
        art_cls_rep (t + 208) spb ris c (art_cls_dealloc c w cl) M' ->
        cellA M' (t + 208 + 2576) 8 (sv - art_ic_size c) ->
        Q (log ++ art_cls_events spb c cl) (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst regs (0x55d08 : word) M rom).
Proof.
  intros Q log regs M rom raw sp HI t ctx tp key tsd c p spb ris qs qris w sv cl H1 Hret H2 H4 H10 H11 H12 H13 GEO HHI Hsp' Hc Eq
    W Wt Wsh PC L T PH [CR RR] OK Hlen Ep Hw Csv Hroom EV K.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
  clear G10 G15 G16. unfold apart in G11, At_s.
  pose proof PC as (Cspb & Cris & Crel & _ & Crd & Cpc & Cpg & _ & _).
  set (ca := t + 208) in *. assert (Eca : ca = t + 208) by reflexivity. clearbody ca.
  assert (Hca8 : ca mod 8 = 0). { rewrite Eca, Et. replace (4096 * qt + 208) with (26 * 8 + qt * 512 * 8) by lia. rewrite Z_mod_plus_full. reflexivity. }
  assert (Hcai : ca + 2592 <= 0x10000 \/ 0x69c000 <= ca) by lia.
  assert (Wca : wrA M ca 2592) by (eapply wr_sub; [exact Wt|lia|lia]).
  destruct (PH c ltac:(lia)) as [Cmc Ccsz].
  destruct CR as [Ccnt Cch].
  pose proof RR as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
  pose proof OK as (L16 & Hau & Hcarve & Hmu & Hauk & Hmu' & (kf & Emfa) & Hmfa' & Hfree & Hall & Hnd).
  destruct (art_ic_mc_half c ltac:(lia)) as (Emc & Hh). pose proof (art_ic_mc_range c ltac:(lia)) as Rmc. pose proof (art_ic_size_pos c ltac:(lia)) as Rsz.
  pose proof (art_cell_norm _ _ _ _ Csv) as Csvn. pose proof (art_mod64_range sv) as Hsvn.
  pose proof (art_cell_norm _ _ _ _ Rnfr) as Rnfrn. pose proof (art_mod64_range (cl_nfr cl)) as Hnfrn.
  set (cnt := Z.of_nat (length (cl_cache cl))) in *. set (nf := Z.of_nat (length (cl_free cl))) in *.
  set (r := ris + 128 * c) in *. set (fa := spb + c * 2 ^ 32 + 3758096384) in *.
  assert (Er : r = ris + 128 * c) by reflexivity. assert (Efa : fa = spb + c * 2 ^ 32 + 3758096384) by reflexivity.
  assert (Hcnt0 : 0 <= cnt) by (unfold cnt; lia). assert (Hnf0 : 0 <= nf) by (unfold nf; lia).
  unfold art_cls_events in EV, K.
  unfold art_cls_dealloc in K. destruct (art_cls_full c cl) eqn:EF; unfold art_cls_full in EF; fold cnt in EF.
  -
    apply Z.eqb_eq in EF. specialize (Hroom eq_refl).
    set (h := art_ic_mc c / 2) in *. set (hn := Z.to_nat h). set (k := (length (cl_cache cl) - hn)%nat).
    assert (Ehn : Z.of_nat hn = h) by (unfold hn; lia).
    assert (Ek : Z.of_nat k = cnt - h) by (unfold k, cnt in *; lia).
    set (ws := skipn k (cl_cache cl)).
    assert (Lws : length ws = hn) by (unfold ws; rewrite length_skipn; unfold k; unfold cnt in *; lia).
    assert (Nws : forall j, nth j ws 0 = nth (k + j) (cl_cache cl) 0) by (intros j; unfold ws; apply nth_skipn).
    pose proof (art_mfa_grow_le (cl_mfa cl) (nf + h) kf Emfa ltac:(lia) ltac:(lia) Hroom) as Room.
    destruct (art_mfa_grow_facts (cl_mfa cl) (nf + h) kf Emfa ltac:(lia) ltac:(lia)) as (Hg1 & Hg2 & _).
    set (mfa' := art_mfa_grow (cl_mfa cl) (nf + h)) in *.
    destruct (art_cell_exists M (t + 2872) 8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(eapply wr_sub; [exact Wt|lia|cbn; lia])) as (m1 & Hm1 & Cm1).
    destruct (art_cell_exists M (t + 2880) 8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(eapply wr_sub; [exact Wt|lia|cbn; lia])) as (m2 & Hm2 & Cm2).
    rewrite EF in Ccnt.
    pose proof (art_lcd_full_a_fn regs M rom raw sp ca 1321624 c p (art_ic_mc c) H1 H2 H10 H11 H12 H13 ltac:(lia) ltac:(lia) ltac:(eapply wr_sub; [exact W|lia|lia])
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ccnt Cmc) as RUN1.
    destruct (art_f48_facts M sp raw regs ltac:(lia) ltac:(lia)) as (G1x & AG1).
    destruct (art_f48_cells M sp raw regs ltac:(lia) ltac:(lia)) as (E1 & E8 & E9 & E18 & E19 & E20).
    match type of RUN1 with msteps _ _ (mkst ?R1 _ _ _) => set (Ra := R1) in * end.
    set (Xa := art_f48 M sp raw regs) in *.
    assert (T1 : forall a (n : nat) v, apart a (Z.of_nat n) (sp - 48) 48 -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> cellA M a n v -> cellA Xa a n v).
    { intros a n v Ap Ha Hn C. apply (art_cell_tr _ M Xa a n v AG1); [cbn [art_gap fst snd]; split; [exact Ap|exact I]|exact Ha|exact Hn|exact C]. }
    assert (PCa : art_prim_consts spb ris Xa).
    { destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      unfold art_prim_consts. repeat split; (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|assumption]). }
    assert (La : art_layout Xa). { eapply art_layout_fp; [exact AG1| |exact L]. intros z Hz. cbn. repeat split; lia. }
    assert (Ta : art_tsd Xa tp key tsd ctx t).
    { eapply art_tsd_fp; [exact AG1| | |exact G19|exact G20|exact G21|exact G22|exact T].
      - intros z Hz. cbn. repeat split; lia.
      - intros z Hz. pose proof G17 as X1. pose proof G18 as X2. unfold apart in X1, X2. cbn. repeat split; lia. }
    assert (Cmx1 : cellA Xa r 8 0) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Rmx]).
    assert (Cnf1 : cellA Xa (r + 16) 8 nf) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Rnf]).
    assert (Cmfa1 : cellA Xa (r + 24) 8 (cl_mfa cl)) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Rmfa]).
    assert (Cnfr1 : cellA Xa (r + 80) 8 (cl_nfr cl mod 2 ^ 64)) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Rnfrn]).
    assert (Ccnt1 : cellA Xa (ca + 80 * c) 4 (art_ic_mc c)) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Ccnt]).
    assert (Cmc1 : cellA Xa (ca + 80 * c + 4) 4 (2 * h)) by (rewrite <- Emc; apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Cmc]).
    assert (Cm1a : cellA Xa (t + 2872) 8 m1) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Cm1]).
    assert (Cm2a : cellA Xa (t + 2880) 8 m2) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Cm2]).
    clearbody Xa.
    assert (Cws1 : forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA Xa (ca + 80 * c + 16 + 4 * (art_ic_mc c - h) + 4 * Z.of_nat j) 4 (nth j ws 0)).
    { intros j Hj. rewrite Lws in Hj. rewrite (Nws j).
      assert (Lt : (k + j < length (cl_cache cl))%nat) by (unfold k; unfold cnt in *; lia).
      split.
      - assert (X : art_cptr_ok (AsanTab.class_size c) (cl_au cl) (nth (k + j) (cl_cache cl) 0)).
        { apply (proj1 (Forall_forall _ _) Hall). apply in_or_app. left. apply nth_In. exact Lt. }
        pose proof (art_class_size_facts c Hc) as (Hsz & _).
        pose proof (art_cptr_lt (AsanTab.class_size c) (cl_au cl) _ ltac:(lia) ltac:(lia) X). lia.
      - pose proof (Cch (k + j)%nat Lt) as Cj. rewrite <- EF.
        replace (ca + 80 * c + 16 + 4 * (cnt - h) + 4 * Z.of_nat j) with (ca + 80 * c + 16 + 4 * Z.of_nat (k + j)) by lia.
        pose proof (proj1 (Nat2Z.inj_lt _ _) Lt) as Hj'. fold cnt in Hj'.
        apply (art_cell_tr _ M Xa _ _ _ AG1); [zgap|lia|cbn; lia|exact Cj]. }
    apply (ar_steps ASEGS EVOK GR Q log _ _ RUN1).
    apply (aruns_bind ASEGS EVOK GR (fun lg s1 => aruns ASEGS EVOK GR Q lg s1) Q); [|intros lg s1 X; exact X].
    rewrite Eca in Ccnt1, Cmc1, Cws1.
    apply (art_lcdrain_aruns EVOK GR (fun lg s1 => aruns ASEGS EVOK GR Q lg s1) log ws Ra Xa rom (0x55eb8 : bv 64)%bv (sp - 48) HI t ctx tp key tsd spb ris qs qris c
             (art_ic_mc c) h nf (cl_mfa cl) kf (cl_nfr cl mod 2 ^ 64) m1 m2);
      [unfold Ra; gres; bveq|unfold ret_ok; bveq|unfold Ra; gres; reflexivity|unfold Ra; gres; exact H4|unfold Ra; gres; rewrite H10, Eca; reflexivity
      |unfold Ra; gres; rewrite Eca; reflexivity|unfold Ra; gres; reflexivity|unfold Ra; gres; reflexivity
      |exact GEO|lia|lia|exact Hc|exact Eq|rewrite Lws; lia|lia|lia|lia|lia|lia|exact Emfa|exact Room|exact Hnfrn
      |eapply wr_grows; [exact G1x|]; eapply wr_sub; [exact W|lia|lia]|eapply wr_grows; [exact G1x|exact Wt]|eapply wr_grows; [exact G1x|exact Wr]
      |eapply wr_grows; [exact G1x|exact Wfa]|eapply wr_grows; [exact G1x|exact Wsh]|exact PCa|exact La|exact Ta
      |exact Ccnt1|exact Cmc1|exact Cmx1|exact Cnf1|exact Cmfa1|exact Cnfr1|exact Cm1a|exact Cm2a|exact Cws1|exact EV|].
    intros r2 M2 B2 BK G2x AG2 Ccnt2 Cmx2 Cnf2 Cmfa2 Cnfr2 Cfa2 Wfa2 _.
    unfold art_lcdrain_fp in AG2. rewrite <- Eca in AG2, Ccnt2. fold r fa in AG2, Cmx2, Cnf2, Cmfa2, Cnfr2, Cfa2, Wfa2.
    replace (sp - 48 - 640) with (sp - 688) in AG2 by lia.
    pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Q8. pose proof (bv_unsigned_in_range 64 (getr regs 9)) as Q9. pose proof (bv_unsigned_in_range 64 (getr regs 18)) as Q18.
    pose proof (bv_unsigned_in_range 64 (getr regs 19)) as Q19. pose proof (bv_unsigned_in_range 64 (getr regs 20)) as Q20.
    change (bv_modulus 64) with (2 ^ 64) in Q8, Q9, Q18, Q19, Q20.
    assert (Csz2 : cellA M2 (ca + 80 * c + 8) 8 (art_ic_size c)) by ztr.
    assert (Cspb2 : cellA M2 (1321624 + 32) 8 spb) by ztr.
    assert (Csv2 : cellA M2 (ca + 2576) 8 (sv mod 2 ^ 64)) by ztr.
    assert (D1 : cellA M2 (sp - 8) 8 (U raw)) by ztr. assert (D8 : cellA M2 (sp - 16) 8 (U (getr regs 8))) by ztr. assert (D9 : cellA M2 (sp - 24) 8 (U (getr regs 9))) by ztr.
    assert (D18 : cellA M2 (sp - 32) 8 (U (getr regs 18))) by ztr. assert (D19 : cellA M2 (sp - 40) 8 (U (getr regs 19))) by ztr. assert (D20 : cellA M2 (sp - 48) 8 (U (getr regs 20))) by ztr.
    pose proof (art_lcd_full_b_fn r2 M2 rom raw sp ca 1321624 c p spb w (art_ic_mc c - h) (art_ic_size c) (sv mod 2 ^ 64)
                  (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))
                  B2 ltac:(rewrite BK by inl; unfold Ra; gres; reflexivity) ltac:(rewrite BK by inl; unfold Ra; gres; reflexivity) ltac:(rewrite BK by inl; unfold Ra; gres; reflexivity)
                  ltac:(rewrite BK by inl; unfold Ra; gres; reflexivity) ltac:(rewrite BK by inl; unfold Ra; gres; reflexivity)
                  Hret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hca8 Hcai ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ep Hw ltac:(lia) ltac:(lia) Hsvn Q8 Q9 Q18 Q19 Q20
                  ltac:(eapply wr_grows; [exact G2x|]; eapply wr_grows; [exact G1x|exact Wca]) Ccnt2 Csz2 Cspb2 Csv2 D1 D8 D9 D18 D19 D20) as RUN3.
    match type of RUN3 with msteps _ _ (mkst ?R3 _ ?X3 _) => set (Rf := R3) in *; set (Mf := X3) in * end.
    assert (G3 : mem_grows M2 Mf) by (unfold Mf; zgrows).
    assert (AG3 : art_agree [(ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8)] M2 Mf).
    { unfold Mf. eapply art_agree_sub; [zagree|]. zsubf. }
    assert (Gf : mem_grows M Mf) by (eapply mem_grows_trans; [exact G1x|]; eapply mem_grows_trans; [exact G2x|exact G3]).
    assert (Af : art_agree [(sp - 688, 688); (ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8); (fa + 4 * nf, 4 * h); (r, 8); (r + 16, 16); (r + 80, 8);
                            (fa + cl_mfa cl, 536870912 - cl_mfa cl); (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048, 67108864); (t + 2872, 16)] M Mf).
    { eapply art_agree_sub; [eapply art_agree_trans; [exact AG1|]; eapply art_agree_trans; [exact AG2|exact AG3]|].
      exact (art_lcd_fpF_sub1 sp ca t spb ris qs c nf h (cl_mfa cl) Eca). }
    eapply ar_steps; [exact RUN3|]. apply ar_done.
    apply K.
    + unfold Rf; gres; reflexivity.
    + intros x Hx. cbn [In] in Hx.
      repeat (destruct Hx as [<-|Hx]; [unfold Rf; gres; first [reflexivity | apply Z_to_bv_bv_unsigned | rewrite BK by inl; unfold Ra; gres; reflexivity]|]). destruct Hx.
    + exact Gf.
    + eapply art_agree_sub; [exact Af|]. exact (art_lcd_fpF_sub2 sp ca t spb ris qs c nf h (cl_mfa cl) Eca ltac:(clear - Hh; Lia.lia)).
    + split.
      *
        unfold art_cls_push, art_cls_return. cbn [cl_cache]. fold hn k. split.
        -- rewrite length_app, length_firstn. cbn [length].
           replace (Z.of_nat (Nat.min k (length (cl_cache cl)) + 1)) with (art_ic_mc c - h + 1) by (unfold cnt in *; lia). unfold Mf. zcell.
        -- intros j Hj. rewrite length_app, length_firstn in Hj. cbn [length] in Hj.
           destruct (Nat.lt_ge_cases j k) as [Lt|Ge].
           ++ rewrite app_nth1 by (rewrite length_firstn; unfold cnt in *; lia). rewrite nth_firstn. replace (j <? k)%nat with true by (symmetry; apply Nat.ltb_lt; exact Lt).
              assert (Ltc : (j < length (cl_cache cl))%nat) by (unfold k in Lt; lia).
              pose proof (Cch j Ltc) as Cj. pose proof (proj1 (Nat2Z.inj_lt _ _) Lt) as Hj'.
              assert (Cj2 : cellA M2 (ca + 80 * c + 16 + 4 * Z.of_nat j) 4 (nth j (cl_cache cl) 0)) by ztr.
              unfold Mf. zcell.
           ++ assert (Ej : j = k) by (unfold cnt in *; lia). subst j. rewrite app_nth2 by (rewrite length_firstn; unfold cnt in *; lia).
              rewrite length_firstn. replace (k - Nat.min k (length (cl_cache cl)))%nat with O by (unfold cnt in *; lia). cbn [nth].
              replace (Z.of_nat k) with (art_ic_mc c - h) by lia. unfold Mf. zcell.
      *
        apply (art_region_rep_ret spb ris c 0 0 cl (art_cls_push w (art_cls_return hn cl)) M Mf
                 [(sp - 688, 688); (ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8); (fa + 4 * nf, 4 * h); (r, 8); (r + 16, 16); (r + 80, 8);
                  (fa + cl_mfa cl, 536870912 - cl_mfa cl); (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048, 67108864); (t + 2872, 16)] ws);
          try reflexivity; fold r fa nf; first [ lia | exact RR | exact Gf | exact Af | idtac ].
        -- zgap.
        -- zgap.
        -- unfold Mf. zcell.
        -- rewrite Lws, Ehn. unfold Mf. zcell.
        -- cbn [art_cls_push art_cls_return cl_mfa]. rewrite art_cls_mfa'_grow. fold nf. rewrite Ehn. fold mfa'. unfold Mf. zcell.
        -- cbn [art_cls_push art_cls_return cl_nfr]. rewrite Ehn. apply art_cell_mod_add. unfold Mf. zcell.
        -- cbn [art_cls_push art_cls_return cl_mfa]. rewrite art_cls_mfa'_grow. fold nf. rewrite Ehn. fold mfa'. eapply wr_grows; [exact G3|exact Wfa2].
        -- intros j Hj. pose proof (Cfa2 j Hj) as Cj. rewrite Lws in Hj. unfold Mf. zcell.
    + replace (sv - art_ic_size c) with (sv + (0 - art_ic_size c)) by lia. apply art_cell_mod_add. unfold Mf. zcell.
  -
    apply Z.eqb_neq in EF. clear Hroom.
    pose proof (art_lcd_push_fn regs M rom raw sp ca 1321624 c p spb w (art_ic_mc c) cnt (art_ic_size c) (sv mod 2 ^ 64) H1 Hret H2 H10 H11 H12 H13
                  ltac:(lia) ltac:(lia) ltac:(eapply wr_sub; [exact W|lia|lia]) ltac:(lia) ltac:(lia) ltac:(lia) Hca8 Hcai ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ep Hw
                  ltac:(lia) ltac:(lia) ltac:(lia) Hsvn Wca Ccnt Cmc Ccsz Cspb Csvn) as RUN.
    match type of RUN with msteps _ _ (mkst ?R _ ?X _) => set (Rf := R) in *; set (Mf := X) in * end.
    assert (G : mem_grows M Mf) by (unfold Mf, art_f48; zgrows).
    assert (A : art_agree [(sp - 48, 48); (ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8)] M Mf).
    { unfold Mf, art_f48. eapply art_agree_sub; [zagree|]. zsubf. }
    eapply ar_steps; [exact RUN|]. apply ar_done. rewrite <- (app_nil_r log).
    apply K.
    + unfold Rf; gres; reflexivity.
    + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [unfold Rf; gres; reflexivity|]). destruct Hx.
    + exact G.
    + eapply art_agree_sub; [exact A|]. exact (art_lcd_fpF_sub3 sp ca t spb ris qs c nf (cl_mfa cl) Eca).
    + split.
      *
        unfold art_cls_push. cbn [cl_cache]. split.
        -- rewrite length_app. cbn [length]. replace (Z.of_nat (length (cl_cache cl) + 1)) with (cnt + 1) by (unfold cnt; lia). unfold Mf. zcell.
        -- intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
           destruct (Nat.lt_ge_cases j (length (cl_cache cl))) as [Lt|Ge].
           ++ rewrite app_nth1 by exact Lt. pose proof (Cch j Lt) as Cj. pose proof (proj1 (Nat2Z.inj_lt _ _) Lt) as Hj'. fold cnt in Hj'.
              unfold Mf, art_f48. zcell.
           ++ assert (Ej : j = length (cl_cache cl)) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. fold cnt.
              unfold Mf. zcell.
      *
        apply (art_region_rep_ret spb ris c 0 0 cl (art_cls_push w cl) M Mf [(sp - 48, 48); (ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8)] []);
          try reflexivity; fold r fa nf; first [ lia | exact RR | exact G | exact A | idtac ].
        -- cbn [art_cls_push cl_free]. symmetry. apply app_nil_r.
        -- zgap.
        -- zgap.
        -- ztr.
        -- cbn [length]. replace (nf + Z.of_nat 0) with nf by lia. ztr.
        -- cbn [art_cls_push cl_mfa]. ztr.
        -- cbn [art_cls_push cl_nfr]. ztr.
        -- cbn [art_cls_push cl_mfa]. eapply wr_grows; [exact G|exact Wfa].
        -- intros j Hj. cbn [length] in Hj. lia.
    + replace (sv - art_ic_size c) with (sv + (0 - art_ic_size c)) by lia. apply art_cell_mod_add. unfold Mf. zcell.
Qed.

End Spec.
