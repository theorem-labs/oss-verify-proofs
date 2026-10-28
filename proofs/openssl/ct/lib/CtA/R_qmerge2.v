(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Walk Image. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_cache_defs R_prim_defs R_asan_defs R_prim_kit R_glue_defs R_depot_defs R_quar_defs R_qrec_defs R_qmerge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
(* [comment removed for export] *)
Module DJR.
  Import Ltac2.
  Ltac2 is_hidden (t : constr) : constr option := lazy_match! t with sf_hide ?p => Some p | _ => None end.
  Ltac2 unhide_rel () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    let rm := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None =>
          match is_hidden ty with
          | Some p => if SF2.meets (SF2.vars_of [] p) gv
                      then (let c := Control.hyp id in ltac1:(c |- unfold sf_hide in c) (Ltac1.of_constr c); None)
                      else Some id
          | None => None
          end
      end) (Control.hyps ()) in
    match rm with [] => () | _ :: _ => Std.clear rm end.
  Ltac2 unhide_rel1 () : unit := Control.enter unhide_rel.
End DJR.
Local Ltac dj_unhide_rel := ltac2:(DJR.unhide_rel1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | dj_unhide_rel; Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].

(* [comment removed for export] *)
Definition merge_mem (m : mem) (FROM TO B0 : Z) (L X : list batch) : Prop :=
  rw_cells ctasegs m FROM [C8 (Z_to_bv 64 (Z.of_nat (length L))); C8 (Z_to_bv 64 (qfirst L)); C8 (Z_to_bv 64 (qlast L));
                         C8 (Z_to_bv 64 B0)]
  /\ qchain_to m L 0
  /\ rw_cells ctasegs m TO [C8 (Z_to_bv 64 (Z.of_nat (length X))); C8 (Z_to_bv 64 (qfirst X)); C8 (Z_to_bv 64 (qlast X));
                         C8 (Z_to_bv 64 (8192 * Z.of_nat (length X)))]
  /\ qchain_to m X 0.

(* [comment removed for export] *)
Lemma qbytes_empty_ents : forall X, Forall (fun e => snd e = []) X -> qbytes X = (8192 * Z.of_nat (length X))%Z.
Proof.
  intros X H. induction H as [|[b e] X He HX IH]; [reflexivity|]. cbn [snd] in He. subst e.
  change (qbytes ((b, []) :: X)) with (8192 + bsum [] + qbytes X)%Z. rewrite IH. cbn [length bsum fold_right]. lia.
Qed.

(* [comment removed for export] *)
Definition ewords (ents : list (Z * Z)) : list word := map (fun e => Z_to_bv 64 (fst e)) ents.

(* [comment removed for export] *)
Lemma merge_fb1 : forall (P : machine_state -> Prop) ra sp gp tp t1 t2 s0 s1 a0 a1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (b b' nb nb' : Z) (e e' : list (Z * Z)) (wc wn : list word),
  (Z.of_nat (length e + length e') <= 1021)%Z -> (b + 8192 <= b' \/ b' + 8192 <= b)%Z ->
  (0 < b /\ b + 8192 <= 2^47)%Z -> (0 < b' /\ b' + 8192 <= 2^47)%Z ->
  (0 <= bsum e < 2^56)%Z ->
  rw_cells ctasegs m b [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 (8192 + bsum e)); C8 (Z_to_bv 64 (Z.of_nat (length e)))] ->
  rw_cells ctasegs m b' [C8 (Z_to_bv 64 nb'); C8 (Z_to_bv 64 (8192 + bsum e')); C8 (Z_to_bv 64 (Z.of_nat (length e')))] ->
  u64arr ctasegs m (b + 24) wc -> length wc = 1021%nat -> firstn (length e) wc = ewords e ->
  u64arr ctasegs m (b' + 24) wn -> length wn = 1021%nat -> firstn (length e') wn = ewords e' ->
  mem_inv ctasegs m ->
  (forall (m' : mem) (wc' : list word) (t2' t3' t4' t5' : word),
     munch [(b + 24, b + 8192)]%Z m m' -> wmono ctasegs m m' -> mem_inv ctasegs m' ->
     u64arr ctasegs m' (b + 24) wc' -> length wc' = 1021%nat -> firstn (length (e ++ e')) wc' = ewords (e ++ e') ->
     evt ctasegs P (MS (mkR ra sp gp tp (Z_to_bv 64 b') (Z_to_bv 64 (Z.of_nat (length e') + Z.of_nat (length e))) t2' s0 s1 a0 a1 a2
                          (Z_to_bv 64 (8192 + bsum e)) (Z_to_bv 64 b) (Z_to_bv 64 1021) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3' t4' t5' t6)
                     F (Z_to_bv 64 0x19defc) fc None m' (seg_rom ctasegs))) ->
  evt ctasegs P (MS (mkR ra sp gp tp (Z_to_bv 64 b') t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 b) (Z_to_bv 64 1021) a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x19deb0) fc None m (seg_rom ctasegs)).
Proof.
  intros until wn. intros Hfit Hbb Hb Hb' Hbs BH BH' BA BL BP BA' BL' BP' MI K.
  pose proof (u64arr_bound ctasegs m (b + 24) wc BA) as HBA. pose proof (u64arr_bound ctasegs m (b' + 24) wn BA') as HBA'.
  do 4 zstep. ifF.
  do 2 zstep.
  assert (E13 : Z.shiftr (8192 + bsum e) 13 = ((8192 + bsum e) / 8192)%Z) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  rewrite E13. assert (H13 : (1 <= (8192 + bsum e) / 8192)%Z) by (apply Z.div_le_lower_bound; lia).
  zstep. ifF.
  zstep.
  destruct e' as [|x e''].
  - ifT. rewrite app_nil_r in K.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => apply (K mm wc) end.
    + apply munch_refl. + apply wmono_refl. + exact MI. + exact BA. + exact BL. + exact BP.
  - ifF.
    do 6 zstep.
    remember (x :: e'') as e' eqn:Ee'.
    assert (He' : (1 <= Z.of_nat (length e'))%Z) by (subst e'; cbn [length]; lia).
    replace (Z_to_bv 64 (b' + 24)) with (Z_to_bv 64 (b' + 24 + 8 * 0)) by (f_equal; lia).
    replace (Z_to_bv 64 (b + Z.shiftl (Z.of_nat (length e)) 3 + 24)) with (Z_to_bv 64 (b + 24 + 8 * (Z.of_nat (length e) + 0)))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace (Z_to_bv 64 (b' + 24 + Z.shiftl (Z.of_nat (length e')) 3)) with (Z_to_bv 64 (b' + 24 + 8 * Z.of_nat (length e')))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    eapply evt_cut; [eapply copy_loop with (CUR := b) (NXT := b') (t4c := Z.of_nat (length e)) (t3c := Z.of_nat (length e'))
                                          (wc0 := wc) (wn := wn) (j := 0%Z) (k := (length e' - 1)%nat); try eassumption; try lia|].
    + rewrite Z.add_0_r, Nat2Z.id, firstn_O, app_nil_r. reflexivity.
    + intros ms' (t5' & m' & wc' & E & MU & WM & MI' & BA1 & BL1 & BP1). subst ms'.
      apply (K m' wc'); try assumption.
      unfold ewords in *. rewrite app_length, map_app. rewrite <- BP, <- BP'.
      replace (length e + length e')%nat with (Z.to_nat (Z.of_nat (length e) + Z.of_nat (length e'))) by lia.
      rewrite BP1. rewrite !Nat2Z.id. reflexivity.
Qed.

Lemma bsum_app' : forall l1 l2, bsum (l1 ++ l2) = (bsum l1 + bsum l2)%Z.
Proof. intros. apply bsum_app. Qed.

(* [comment removed for export] *)
Lemma merge_fb2 : forall (P : machine_state -> Prop) ra sp gp tp t2 s0 s1 a1 a2 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (FROM n0 f0 l0 B0 b b' nb nb' : Z) (e e' : list (Z * Z)),
  (b + 8192 <= b' \/ b' + 8192 <= b)%Z -> (0 < b /\ b + 8192 <= 2^47)%Z -> (0 < b' /\ b' + 8192 <= 2^47)%Z ->
  (0 <= bsum e)%Z -> (0 <= bsum e')%Z -> (bsum e + bsum e' < 2^56)%Z -> (Z.of_nat (length e + length e') <= 1021)%Z ->
  (1 <= n0 < 2^63)%Z -> (0 < FROM)%Z -> (FROM + 32 <= b \/ b + 8192 <= FROM)%Z -> (FROM + 32 <= b' \/ b' + 8192 <= FROM)%Z ->
  rw_cells ctasegs m FROM [C8 (Z_to_bv 64 n0); C8 (Z_to_bv 64 f0); C8 (Z_to_bv 64 l0); C8 (Z_to_bv 64 B0)] ->
  rw_cells ctasegs m b [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 (8192 + bsum e)); C8 (Z_to_bv 64 (Z.of_nat (length e)))] ->
  rw_cells ctasegs m b' [C8 (Z_to_bv 64 nb'); C8 (Z_to_bv 64 (8192 + bsum e')); C8 (Z_to_bv 64 (Z.of_nat (length e')))] ->
  mem_inv ctasegs m ->
  (forall (m' : mem) (t2' : word),
     munch [(b, b + 24); (b', b' + 24)]%Z m m' -> wmono ctasegs m m' -> mem_inv ctasegs m' ->
     rw_cells ctasegs m' FROM [C8 (Z_to_bv 64 n0); C8 (Z_to_bv 64 f0); C8 (Z_to_bv 64 l0); C8 (Z_to_bv 64 B0)] ->
     rw_cells ctasegs m' b [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 (8192 + bsum (e ++ e'))); C8 (Z_to_bv 64 (Z.of_nat (length (e ++ e'))))] ->
     rw_cells ctasegs m' b' [C8 (Z_to_bv 64 nb'); C8 (Z_to_bv 64 8192); C8 (Z_to_bv 64 0)] ->
     evt ctasegs P (MS (mkR ra sp gp tp (Z_to_bv 64 b') (Z_to_bv 64 (Z.of_nat (length e') + Z.of_nat (length e))) t2' s0 s1
                          (Z_to_bv 64 FROM) a1 a2 (Z_to_bv 64 n0) (Z_to_bv 64 b) a5 (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192)
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x19df20) fc None m' (seg_rom ctasegs))) ->
  evt ctasegs P (MS (mkR ra sp gp tp (Z_to_bv 64 b') (Z_to_bv 64 (Z.of_nat (length e') + Z.of_nat (length e))) t2 s0 s1
                       (Z_to_bv 64 FROM) a1 a2 (Z_to_bv 64 (8192 + bsum e)) (Z_to_bv 64 b) a5 (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192)
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x19defc) fc None m (seg_rom ctasegs)).
Proof.
  intros until e'. intros Hbb Hb Hb' Hs1 Hs2 Hs12 Hfit Hn0 HF0 HFb HFb' FH BH BH' MI K.
  pose proof (munch_refl [(b, b + 24); (b', b' + 24)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  do 4 zstep.
  replace (8192 + bsum e + (8192 + bsum e') + -8192)%Z with (8192 + bsum (e ++ e'))%Z by (rewrite bsum_app; lia).
  zstep.
  replace (Z_to_bv 64 (Z.of_nat (length e') + Z.of_nat (length e))) with (Z_to_bv 64 (Z.of_nat (length (e ++ e'))))
    by (f_equal; rewrite app_length; lia).
  zstep. zstep; fix_lit_store. zstep; fix_lit_store.
  zstep. ifF.
  replace (Z_to_bv 64 (Z.of_nat (length (e ++ e')))) with (Z_to_bv 64 (Z.of_nat (length e') + Z.of_nat (length e)))
    by (f_equal; rewrite app_length; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => apply (K mm) end; eassumption.
Qed.

Ltac qfb3_fin := match goal with K : forall (m' : mem) (t1' t2' : word), _ |- _ =>
  eapply K; try eassumption; try (intros; congruence) end.

(* [comment removed for export] *)
Lemma merge_fb3 : forall (P : machine_state -> Prop) ra sp gp tp t1 t2 s0 s1 a2 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (FROM TO n0 f0 l0 B0 b b' nb' sz cnt xn xf xl xb : Z),
  (0 < FROM)%Z -> (FROM + 32 <= TO \/ TO + 32 <= FROM)%Z ->
  (b + 8192 <= b' \/ b' + 8192 <= b)%Z -> (0 < b /\ b + 8192 <= 2^47)%Z -> (0 < b' /\ b' + 8192 <= 2^47)%Z ->
  (FROM + 32 <= b \/ b + 8192 <= FROM)%Z -> (FROM + 32 <= b' \/ b' + 8192 <= FROM)%Z ->
  (TO + 32 <= b \/ b + 8192 <= TO)%Z -> (TO + 32 <= b' \/ b' + 8192 <= TO)%Z -> (0 <= TO /\ TO + 32 <= 2^64)%Z ->
  (2 <= n0 < 2^63)%Z -> (0 <= l0 < 2^64)%Z -> (0 <= nb' < 2^64)%Z -> (0 <= xn < 2^63)%Z ->
  (xn <> 0 -> (0 < xl /\ xl + 8192 <= 2^47) /\ (xl + 8192 <= b \/ b + 8192 <= xl) /\ (xl + 8192 <= b' \/ b' + 8192 <= xl)
              /\ (FROM + 32 <= xl \/ xl + 8192 <= FROM) /\ (TO + 32 <= xl \/ xl + 8192 <= TO))%Z ->
  rw_cells ctasegs m FROM [C8 (Z_to_bv 64 n0); C8 (Z_to_bv 64 f0); C8 (Z_to_bv 64 l0); C8 (Z_to_bv 64 B0)] ->
  rw_cells ctasegs m TO [C8 (Z_to_bv 64 xn); C8 (Z_to_bv 64 xf); C8 (Z_to_bv 64 xl); C8 (Z_to_bv 64 xb)] ->
  rw_cells ctasegs m b [C8 (Z_to_bv 64 b'); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 cnt)] ->
  rw_cells ctasegs m b' [C8 (Z_to_bv 64 nb'); C8 (Z_to_bv 64 8192); C8 (Z_to_bv 64 0)] ->
  (xn <> 0 -> rw_cells ctasegs m xl [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 8192); C8 (Z_to_bv 64 0)])%Z ->
  mem_inv ctasegs m ->
  (forall (m' : mem) (t1' t2' : word),
     munch [(FROM, FROM + 32); (TO, TO + 32); (b, b + 8); (b', b' + 8); (if xn =? 0 then b' else xl, (if xn =? 0 then b' else xl) + 8)]%Z
       m m' -> wmono ctasegs m m' -> mem_inv ctasegs m' ->
     rw_cells ctasegs m' FROM [C8 (Z_to_bv 64 (n0 - 1)); C8 (Z_to_bv 64 f0); C8 (Z_to_bv 64 (if l0 =? b' then b else l0));
                             C8 (Z_to_bv 64 B0)] ->
     rw_cells ctasegs m' TO [C8 (Z_to_bv 64 xn); C8 (Z_to_bv 64 (if xn =? 0 then b' else xf)); C8 (Z_to_bv 64 xl); C8 (Z_to_bv 64 xb)] ->
     rw_cells ctasegs m' b [C8 (Z_to_bv 64 nb'); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 cnt)] ->
     rw_cells ctasegs m' b' [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 8192); C8 (Z_to_bv 64 0)] ->
     (xn <> 0 -> rw_cells ctasegs m' xl [C8 (Z_to_bv 64 b'); C8 (Z_to_bv 64 8192); C8 (Z_to_bv 64 0)])%Z ->
     evt ctasegs P (MS (mkR ra sp gp tp (Z_to_bv 64 b') t1' t2' s0 s1 (Z_to_bv 64 FROM) (Z_to_bv 64 TO) a2 (Z_to_bv 64 (xn + 1))
                          (Z_to_bv 64 b) a5 (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x19df74) fc None m' (seg_rom ctasegs))) ->
  evt ctasegs P (MS (mkR ra sp gp tp (Z_to_bv 64 b') t1 t2 s0 s1 (Z_to_bv 64 FROM) (Z_to_bv 64 TO) a2 (Z_to_bv 64 n0)
                       (Z_to_bv 64 b) a5 (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x19df20) fc None m (seg_rom ctasegs)).
Proof.
  intros until xb. intros HF0 HFT Hbb Hb Hb' HFb HFb' HTb HTb' HT0 Hn0 Hl0 Hnb Hxn HXS FH TH BH BH' XL MI K.
  pose proof (munch_refl [(FROM, FROM + 32); (TO, TO + 32); (b, b + 8); (b', b' + 8); (if xn =? 0 then b' else xl, (if xn =? 0 then b' else xl) + 8)]%Z m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
  destruct (Z.eq_dec xn 0) as [Hx|Hx];
    [subst xn; rewrite Z.eqb_refl in K, MU; clear XL HXS| rewrite (proj2 (Z.eqb_neq xn 0) Hx) in K, MU; pose proof (XL Hx) as XLc; clear XL;
     pose proof (HXS Hx) as (HX1 & HX2 & HX3 & HX4 & HX5); clear HXS]; cbv iota in K, MU.
  all: do 3 zstep.
  all: destruct (Z.eq_dec l0 b') as [Hl|Hl]; [subst l0; rewrite Z.eqb_refl in K|rewrite (proj2 (Z.eqb_neq l0 b') Hl) in K]; cbv iota in K.
  - (* [comment removed for export] *)
    zstep. ifT. zstep. zstep. zstep. zstep. zstep; fix_lit_store. zstep. ifF. zstep. zstep. qfb3_fin.
  - (* [comment removed for export] *)
    zstep. ifF. zstep. zstep. zstep. zstep; fix_lit_store. zstep. ifT. zstep. zstep. qfb3_fin.
  - (* [comment removed for export] *)
    zstep. ifT. zstep. zstep. zstep. zstep. zstep; fix_lit_store. zstep. ifT. zstep. zstep. zstep. zstep. qfb3_fin.
  - zstep. ifF. zstep. zstep. zstep. zstep; fix_lit_store. zstep. ifF. zstep. zstep. zstep. zstep. qfb3_fin.
Qed.

(* [comment removed for export] *)
Lemma merge_fb4 : forall (P : machine_state -> Prop) ra sp gp tp t1 t2 s0 s1 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (FROM TO ax b b' nb' sz cnt xn xf xl xb : Z),
  (0 <= TO /\ TO + 32 <= 2^64)%Z -> (0 < b /\ b + 8192 <= 2^47)%Z -> (TO + 32 <= b \/ b + 8192 <= TO)%Z ->
  rw_cells ctasegs m TO [C8 (Z_to_bv 64 xn); C8 (Z_to_bv 64 xf); C8 (Z_to_bv 64 xl); C8 (Z_to_bv 64 xb)] ->
  rw_cells ctasegs m b [C8 (Z_to_bv 64 nb'); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 cnt)] ->
  mem_inv ctasegs m ->
  (forall (m' : mem),
     munch [(TO, TO + 32)]%Z m m' -> wmono ctasegs m m' -> mem_inv ctasegs m' ->
     rw_cells ctasegs m' TO [C8 (Z_to_bv 64 (xn + 1)); C8 (Z_to_bv 64 xf); C8 (Z_to_bv 64 b'); C8 (Z_to_bv 64 (xb + 8192))] ->
     rw_cells ctasegs m' b [C8 (Z_to_bv 64 nb'); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 cnt)] ->
     evt ctasegs P (MS (mkR ra sp gp tp (Z_to_bv 64 nb') t1 t2 s0 s1 (Z_to_bv 64 FROM) (Z_to_bv 64 TO) (Z_to_bv 64 (ax + 8192))
                          (Z_to_bv 64 (xb + 8192)) (Z_to_bv 64 b) a5 (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192)
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x19df90) fc None m' (seg_rom ctasegs))) ->
  evt ctasegs P (MS (mkR ra sp gp tp (Z_to_bv 64 b') t1 t2 s0 s1 (Z_to_bv 64 FROM) (Z_to_bv 64 TO) (Z_to_bv 64 ax) (Z_to_bv 64 (xn + 1))
                       (Z_to_bv 64 b) a5 (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x19df74) fc None m (seg_rom ctasegs)).
Proof.
  intros until xb. intros HT0 Hb HTb TH BH MI K.
  pose proof (munch_refl [(TO, TO + 32)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  do 7 zstep.
  eapply K; eassumption.
Qed.


