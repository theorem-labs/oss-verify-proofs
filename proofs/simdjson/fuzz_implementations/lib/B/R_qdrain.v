(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout R_small R_m2s R_cache_defs R_prim_defs R_asan_defs R_prim_kit R_glue_defs R_depot_defs R_quar_defs R_qput R_deallocate.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).

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

Notation q_lockw := (1599112%Z) (only parsing).
Notation QG := (1599120%Z) (only parsing).

Definition q_lock (m : mem) (cmu rmu : Z) : Prop :=
  rw_cells bsegs m q_lockw [C1 (Z_to_bv 8 cmu); C1 (Z_to_bv 8 rmu); C2 (Z_to_bv 64 0)].

Definition qdrain_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (W : list (Z * Z)) (Q : Z) (gl' : list batch) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ qcache_rep m' QG gl' /\ qcache_rep m' Q [] /\ q_lock m' 0 0
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma qdrain_ret_empty_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Q SB cache stack lo : Z) (tl : list batch),
  tl <> [] -> qcache_rep m QG [] -> qcache_rep m Q tl -> qwf SB tl ->
  (qbytes tl <= 0x10000000)%Z ->
  q_lock m 0 0 -> rw_cells bsegs m q_max [C8 (Z_to_bv 64 0x10000000)] ->
  (0 < Q)%Z -> (Q + 32 <= 0x10000 \/ 0x6e0000 <= Q)%Z -> (Q + 32 <= r24 SB \/ r24 SB + 2^32 <= Q)%Z -> (0 < SB)%Z ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48)%Z -> (Q + 32 <= lo)%Z -> (r24 SB + 2^32 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (qdrain_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(q_lockw, q_lockw + 4); (QG, QG + 32); (Q, Q + 32); (bv_unsigned sp - 48, bv_unsigned sp)]%Z Q tl lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 Q) (Z_to_bv 64 cache) (Z_to_bv 64 stack) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qdrain_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until tl. intros Hne QRG QRT WF HBY LK QM HQ0 HQ HQS HSB ST HLO HQl HRl HSP MI.
  pose proof (qbytes_ge _ _ WF) as QGE.
  apply (proj1 (qcache_rep_iff _ _ _)) in QRG. destruct QRG as (QHG & _). cbn [length qfirst qlast qbytes map last fold_right] in QHG.
  apply (proj1 (qcache_rep_iff _ _ _)) in QRT. destruct QRT as (QHT & QCT). apply box in QCT.
  unfold q_lock, qdrain_entry, kHighShadowEnd, r24 in *.
  assert (RNT1 : (1 <= Z.of_nat (length tl))%Z) by (destruct tl as [|x tl']; [congruence| cbn [length]; lia]).
  assert (RNT2 : (Z.of_nat (length tl) < 2^50)%Z) by lia.
  assert (RBT : (8192 <= qbytes tl)%Z) by lia. clear QGE.
  remember (Z.of_nat (length tl)) as NT eqn:ENT.
  remember (qfirst tl) as FT eqn:EFT. remember (qlast tl) as LT eqn:ELT. remember (qbytes tl) as BT eqn:EBT.
  move QHG at bottom. move LK at bottom. move QM at bottom.
  pose proof (munch_refl [(1599112, 1599112 + 4); (1599120, 1599120 + 32); (Q, Q + 32); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  zhide.
  zidle_begin sp 48%Z MUz WMz.
  do 6 zstep.
  zidle_end MUz WMz.
  do 4 zstep.
  apply (hdr3_to_c4 _ _ 0 0 []) in LK; [| lia| lia]. change (0 + 256 * 0)%Z with 0%Z in LK.
  assert (AMO : amo_aligned AW (Z_to_bv 64 1599112) = true) by (vm_compute; reflexivity).
  amo_step AMO. rewrite (sx32_small_A 0) by lia.
  do 4 zstep. fold_reg 6%Z.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  zstep. zstep. ifF.
  zstep. zstep. ifF.
  zstep. zstep. ifF.
  zstep. zstep. first [ifT| dIf_closed].
  do 6 zstep.
  zstep; fix_lit_store. zstep; fix_lit_store. zstep; fix_lit_store.
  do 4 zstep. zstep; fix_lit_store. zstep.
  lazymatch goal with H : rw_cells bsegs _ 1599112 [C4 _] |- _ =>
    change (Z_to_bv 64 1) with (Z_to_bv 64 (1 + 256 * 0)) in H; apply (c4_to_hdr3 _ _ 1 0 []) in H; [| lia| lia] end.
  zstep; fix_lit_store.
  zstep. zstep. zstep. ifT.
  do 6 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk bsegs mm _ _ |- _ => release_frame FR H (bv_unsigned sp) end end.
  zstep.
  apply evt_done. unfold qdrain_ret_post, q_lock.
  do 16 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| eassumption]; unfold sub_fp; cbn [outside]; intros; lia|].
  split; [eassumption|]. split; [eassumption|].
  split; [| split; [| split; [eassumption| eassumption]]].
  - apply (proj2 (qcache_rep_iff _ _ _)). rewrite <- ENT, <- EFT, <- ELT, <- EBT. split.
    + replace BT with (0 + BT)%Z at 4 by lia. eassumption.
    + apply (proj2 (qchain_to_0 _ _)).
      lazymatch goal with |- qchain_to ?mm _ _ =>
        apply (qchain_to_frame _ m mm _ _ (proj1 (qchain_to_0 _ _) (unbox _ QCT)) MU WM) end.
      pose proof (qwf_region _ _ WF) as RG. apply Forall_forall. intros e He.
      pose proof (proj1 (Forall_forall _ _) RG e He) as (E1 & E2). unfold r24 in E1, E2.
      cbn [disjoint_from]. repeat split; lia.
  - apply (proj2 (qcache_rep_iff _ _ _)). cbn [length qfirst qlast qbytes map last fold_right Z.of_nat]. split; [| exact I].
    eassumption.
Qed.

Lemma qwf_suffix : forall SB l1 l2, qwf SB (l1 ++ l2) -> qwf SB l2.
Proof.
  intros SB l1 l2 (ND & HF). split.
  - rewrite map_app in ND. apply NoDup_app_remove_l in ND. exact ND.
  - apply Forall_app in HF. exact (proj2 HF).
Qed.

Lemma nodup_app_disj : forall {X} (l1 l2 : list X) a, List.NoDup (l1 ++ l2) -> In a l1 -> ~ In a l2.
Proof.
  intros X l1. induction l1 as [|x l1 IH]; intros l2 a ND Hin; [destruct Hin|].
  cbn in ND. inversion ND as [|y l HNI ND']; subst.
  destruct Hin as [->|Hin].
  - intros H. apply HNI. apply in_or_app. right. exact H.
  - apply (IH l2 a ND' Hin).
Qed.

Lemma qwf_app_disj : forall SB l1 l2 x y, qwf SB (l1 ++ l2) -> In x l1 -> In y l2 ->
  (fst x + 8192 <= fst y \/ fst y + 8192 <= fst x)%Z.
Proof.
  intros SB l1 l2 x y (ND & HF) Hx Hy.
  pose proof (proj1 (Forall_forall _ _) HF x ltac:(apply in_or_app; left; exact Hx)) as (A1 & _).
  pose proof (proj1 (Forall_forall _ _) HF y ltac:(apply in_or_app; right; exact Hy)) as (A2 & _).
  apply align_disj; [exact A1| exact A2|]. intros E.
  rewrite map_app in ND. apply (nodup_app_disj (map fst l1) (map fst l2) (fst x) ND); [apply in_map; exact Hx|].
  rewrite E. apply in_map. exact Hy.
Qed.

Lemma qdrain_ret_app_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Q SB cache stack lo : Z) (pre tl : list batch) (bl : Z) (el : list (Z * Z)),
  tl <> [] -> qcache_rep m QG (pre ++ [(bl, el)]) -> qcache_rep m Q tl -> qwf SB ((pre ++ [(bl, el)]) ++ tl) ->
  (qbytes (pre ++ [(bl, el)]) + qbytes tl <= 0x10000000)%Z ->
  q_lock m 0 0 -> rw_cells bsegs m q_max [C8 (Z_to_bv 64 0x10000000)] ->
  (0 < Q)%Z -> (Q + 32 <= 0x10000 \/ 0x6e0000 <= Q)%Z -> (Q + 32 <= r24 SB \/ r24 SB + 2^32 <= Q)%Z -> (0 < SB)%Z ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48)%Z -> (Q + 32 <= lo)%Z -> (r24 SB + 2^32 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (qdrain_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(q_lockw, q_lockw + 4); (QG, QG + 32); (Q, Q + 32); (bl, bl + 8); (bv_unsigned sp - 48, bv_unsigned sp)]%Z
               Q ((pre ++ [(bl, el)]) ++ tl) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 Q) (Z_to_bv 64 cache) (Z_to_bv 64 stack) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qdrain_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until el. intros Hne QRG QRT WF HBY LK QM HQ0 HQ HQS HSB ST HLO HQl HRl HSP MI.
  pose proof (qbytes_ge _ _ WF) as QGE. rewrite qbytes_app, app_length, Nat2Z.inj_add in QGE.
  pose proof (qbytes_ge _ _ (qwf_prefix _ _ _ WF)) as QGE1. pose proof (qbytes_ge _ _ (qwf_suffix _ _ _ WF)) as QGE2.
  pose proof (qbytes_nonneg _ _ (qwf_prefix _ _ _ (qwf_prefix _ _ _ WF))) as QPN.
  assert (RNT1 : (1 <= Z.of_nat (length tl))%Z) by (destruct tl as [|x tl']; [congruence| cbn [length]; lia]).
  assert (RNG1 : (1 <= Z.of_nat (length (pre ++ [(bl, el)])))%Z) by (rewrite app_length; cbn [length]; lia).
  assert (RNT2 : (Z.of_nat (length tl) + Z.of_nat (length (pre ++ [(bl, el)])) < 2^50)%Z) by lia.
  assert (RBT : (8192 <= qbytes tl)%Z) by lia. assert (RBG : (8192 <= qbytes (pre ++ [(bl, el)]))%Z) by lia. clear QGE QGE1 QGE2.
  pose proof (qwf_region _ _ WF) as RG. apply box in RG.
  pose proof WF as WFx. apply box in WFx.
  pose proof (qwf_last _ _ _ _ (qwf_prefix _ _ _ WF)) as (Hbl8 & Hbl1 & Hbl2 & _ & _).
  apply (proj1 (qcache_rep_iff _ _ _)) in QRG. destruct QRG as (QHG & QCG).
  apply (proj1 (qchain_to_0 _ _)) in QCG. apply (proj1 (qchain_to_snoc _ _ _ _ _)) in QCG. destruct QCG as (QPG & QBL).
  apply box in QPG. apply (proj1 (qbatch_iff _ _ _ _)) in QBL. destruct QBL as (QBLH & QBLA & QBLe). apply box in QBLA.
  apply (proj1 (qcache_rep_iff _ _ _)) in QRT. destruct QRT as (QHT & QCT). apply box in QCT.
  rewrite qlast_snoc in QHG.
  unfold q_lock, qdrain_entry, kHighShadowEnd, r24 in *.
  remember (Z.of_nat (length tl)) as NT eqn:ENT.
  remember (Z.of_nat (length (pre ++ [(bl, el)]))) as NG eqn:ENG.
  remember (qfirst tl) as FT eqn:EFT. remember (qlast tl) as LT eqn:ELT. remember (qbytes tl) as BT eqn:EBT.
  remember (qfirst (pre ++ [(bl, el)])) as FG eqn:EFG. remember (qbytes (pre ++ [(bl, el)])) as BG eqn:EBG.
  remember (bsum el) as BSL eqn:EBSL.
  move LK at bottom. move QM at bottom.
  pose proof (munch_refl [(1599112, 1599112 + 4); (1599120, 1599120 + 32); (Q, Q + 32); (bl, bl + 8); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m)
    as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  zhide.
  zidle_begin sp 48%Z MUz WMz.
  do 6 zstep.
  zidle_end MUz WMz.
  do 4 zstep.
  apply (hdr3_to_c4 _ _ 0 0 []) in LK; [| lia| lia]. change (0 + 256 * 0)%Z with 0%Z in LK.
  assert (AMO : amo_aligned AW (Z_to_bv 64 1599112) = true) by (vm_compute; reflexivity).
  amo_step AMO. rewrite (sx32_small_A 0) by lia.
  do 4 zstep. fold_reg 6%Z.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  zstep. zstep. ifF.
  zstep. zstep. ifF.
  zstep. zstep. ifF.
  zstep. zstep. ifF.
  do 8 zstep.
  zstep; fix_lit_store. zstep; fix_lit_store. zstep; fix_lit_store.
  do 4 zstep. zstep; fix_lit_store. zstep.
  lazymatch goal with H : rw_cells bsegs _ 1599112 [C4 _] |- _ =>
    change (Z_to_bv 64 1) with (Z_to_bv 64 (1 + 256 * 0)) in H; apply (c4_to_hdr3 _ _ 1 0 []) in H; [| lia| lia] end.
  zstep; fix_lit_store.
  zstep. zstep. zstep. ifT.
  do 6 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk bsegs mm _ _ |- _ => release_frame FR H (bv_unsigned sp) end end.
  zstep.
  pose proof (qwf_snoc_disj _ _ _ _ (qwf_prefix _ _ _ WF)) as DJP.
  apply evt_done. unfold qdrain_ret_post, q_lock.
  do 16 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
  split; [eassumption|]. split; [eassumption|].
  split; [| split; [| split; [eassumption| eassumption]]].
  - apply (proj2 (qcache_rep_iff _ _ _)).
    rewrite app_length, Nat2Z.inj_add, <- ENT, <- ENG. rewrite (qfirst_app_ne _ _ (snoc_ne _ _)), <- EFG.
    rewrite (qlast_app_ne _ _ Hne), <- ELT, qbytes_app, <- EBT, <- EBG. split.
    + eassumption.
    + apply (proj2 (qchain_to_0 _ _)). apply (proj2 (qchain_to_app _ _ _ _ Hne)). split.
      * apply (proj2 (qchain_to_snoc _ _ _ _ _)). split.
        -- lazymatch goal with |- qchain_to ?mm _ _ =>
             apply (qchain_to_frame _ m mm _ _ (unbox _ QPG) MU WM) end.
           apply Forall_forall. intros e He.
           pose proof (proj1 (Forall_forall _ _) (unbox _ RG) e ltac:(apply in_or_app; left; apply in_or_app; left; exact He))
             as (E1 & E2).
           pose proof (proj1 (Forall_forall _ _) DJP e He) as E3.
           unfold r24 in E1, E2. cbv beta in E3. cbn [disjoint_from]. repeat split; lia.
        -- apply (proj2 (qbatch_iff _ _ _ _)). split; [| split; [| exact QBLe]].
           ++ rewrite <- EFT, <- EBSL. eassumption.
           ++ destruct (unbox _ QBLA) as (bws0 & BA0 & BL0 & BP0).
              exists bws0. split; [| split; [exact BL0| exact BP0]].
              lazymatch goal with |- u64arr bsegs ?mm _ _ =>
                apply (u64arr_transport bsegs _ m mm _ _ BA0 MU WM) end.
              rewrite BL0. cbn [disjoint_from]. lia.
      * lazymatch goal with |- qchain_to ?mm _ _ =>
          apply (qchain_to_frame _ m mm _ _ (proj1 (qchain_to_0 _ _) (unbox _ QCT)) MU WM) end.
        apply Forall_forall. intros e He.
        pose proof (proj1 (Forall_forall _ _) (unbox _ RG) e ltac:(apply in_or_app; right; exact He)) as (E1 & E2).
        pose proof (qwf_app_disj _ _ _ (bl, el) e (unbox _ WFx) ltac:(apply in_or_app; right; left; reflexivity) He) as E3.
        unfold r24 in E1, E2. cbn [fst] in E3. cbn [disjoint_from]. repeat split; lia.
  - apply (proj2 (qcache_rep_iff _ _ _)). cbn [length qfirst qlast qbytes map last fold_right Z.of_nat]. split; [| exact I].
    eassumption.
Qed.

Definition qrecycle_entry : Z := 0x60cf4.

Definition qdrain_rec_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (W : list (Z * Z)) (Q cache stack : Z) (gl' : list batch) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 0xE666661) (Z_to_bv 64 cache) (Z_to_bv 64 stack)
                  a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 qrecycle_entry) fc None m' (seg_rom bsegs)
    /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ qcache_rep m' QG gl' /\ qcache_rep m' Q [] /\ q_lock m' 0 1
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma qdrain_rec_app_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Q SB cache stack lo : Z) (pre tl : list batch) (bl : Z) (el : list (Z * Z)),
  tl <> [] -> qcache_rep m QG (pre ++ [(bl, el)]) -> qcache_rep m Q tl -> qwf SB ((pre ++ [(bl, el)]) ++ tl) ->
  (0x10000000 < qbytes (pre ++ [(bl, el)]) + qbytes tl < 2^56)%Z ->
  q_lock m 0 0 -> rw_cells bsegs m q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661)] ->
  (0 < Q)%Z -> (Q + 32 <= 0x10000 \/ 0x6e0000 <= Q)%Z -> (Q + 32 <= r24 SB \/ r24 SB + 2^32 <= Q)%Z -> (0 < SB)%Z ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48)%Z -> (Q + 32 <= lo)%Z -> (r24 SB + 2^32 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (qdrain_rec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(q_lockw, q_lockw + 4); (QG, QG + 32); (Q, Q + 32); (bl, bl + 8); (bv_unsigned sp - 48, bv_unsigned sp)]%Z
               Q cache stack ((pre ++ [(bl, el)]) ++ tl) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 Q) (Z_to_bv 64 cache) (Z_to_bv 64 stack) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qdrain_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until el. intros Hne QRG QRT WF HBY LK QM HQ0 HQ HQS HSB ST HLO HQl HRl HSP MI.
  pose proof (qbytes_ge _ _ WF) as QGE. rewrite qbytes_app, app_length, Nat2Z.inj_add in QGE.
  pose proof (qbytes_ge _ _ (qwf_prefix _ _ _ WF)) as QGE1. pose proof (qbytes_ge _ _ (qwf_suffix _ _ _ WF)) as QGE2.
  pose proof (qbytes_nonneg _ _ (qwf_prefix _ _ _ (qwf_prefix _ _ _ WF))) as QPN.
  assert (RNT1 : (1 <= Z.of_nat (length tl))%Z) by (destruct tl as [|x tl']; [congruence| cbn [length]; lia]).
  assert (RNG1 : (1 <= Z.of_nat (length (pre ++ [(bl, el)])))%Z) by (rewrite app_length; cbn [length]; lia).
  assert (RNT2 : (Z.of_nat (length tl) + Z.of_nat (length (pre ++ [(bl, el)])) < 2^50)%Z) by lia.
  assert (RBT : (8192 <= qbytes tl)%Z) by lia. assert (RBG : (8192 <= qbytes (pre ++ [(bl, el)]))%Z) by lia. clear QGE QGE1 QGE2.
  pose proof (qwf_region _ _ WF) as RG. apply box in RG.
  pose proof WF as WFx. apply box in WFx.
  pose proof (qwf_last _ _ _ _ (qwf_prefix _ _ _ WF)) as (Hbl8 & Hbl1 & Hbl2 & _ & _).
  apply (proj1 (qcache_rep_iff _ _ _)) in QRG. destruct QRG as (QHG & QCG).
  apply (proj1 (qchain_to_0 _ _)) in QCG. apply (proj1 (qchain_to_snoc _ _ _ _ _)) in QCG. destruct QCG as (QPG & QBL).
  apply box in QPG. apply (proj1 (qbatch_iff _ _ _ _)) in QBL. destruct QBL as (QBLH & QBLA & QBLe). apply box in QBLA.
  apply (proj1 (qcache_rep_iff _ _ _)) in QRT. destruct QRT as (QHT & QCT). apply box in QCT.
  rewrite qlast_snoc in QHG.
  unfold q_lock, qdrain_entry, kHighShadowEnd, r24 in *.
  remember (Z.of_nat (length tl)) as NT eqn:ENT.
  remember (Z.of_nat (length (pre ++ [(bl, el)]))) as NG eqn:ENG.
  remember (qfirst tl) as FT eqn:EFT. remember (qlast tl) as LT eqn:ELT. remember (qbytes tl) as BT eqn:EBT.
  remember (qfirst (pre ++ [(bl, el)])) as FG eqn:EFG. remember (qbytes (pre ++ [(bl, el)])) as BG eqn:EBG.
  remember (bsum el) as BSL eqn:EBSL.
  move LK at bottom. move QM at bottom.
  pose proof (munch_refl [(1599112, 1599112 + 4); (1599120, 1599120 + 32); (Q, Q + 32); (bl, bl + 8); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m)
    as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  zhide.
  zidle_begin sp 48%Z MUz WMz.
  do 6 zstep.
  zidle_end MUz WMz.
  do 4 zstep.
  apply (hdr3_to_c4 _ _ 0 0 []) in LK; [| lia| lia]. change (0 + 256 * 0)%Z with 0%Z in LK.
  assert (AMO : amo_aligned AW (Z_to_bv 64 1599112) = true) by (vm_compute; reflexivity).
  amo_step AMO. rewrite (sx32_small_A 0) by lia.
  do 4 zstep. fold_reg 6%Z.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  zstep. zstep. ifF.
  zstep. zstep. ifF.
  zstep. zstep. ifF.
  zstep. zstep. ifF.
  do 8 zstep.
  zstep; fix_lit_store. zstep; fix_lit_store. zstep; fix_lit_store.
  do 4 zstep. zstep; fix_lit_store. zstep.
  lazymatch goal with H : rw_cells bsegs _ 1599112 [C4 _] |- _ =>
    change (Z_to_bv 64 1) with (Z_to_bv 64 (1 + 256 * 0)) in H; apply (c4_to_hdr3 _ _ 1 0 []) in H; [| lia| lia] end.
  zstep; fix_lit_store.
  zstep. zstep. zstep. ifF.
  do 8 zstep.
  lazymatch goal with H : rw_cells bsegs _ 1599112 [C1 _; C1 _; C2 _] |- _ =>
    apply (hdr3_to_c4 _ _ 0 0 []) in H; [change (0 + 256 * 0)%Z with 0%Z in H| lia| lia] end.
  amo_step AMO. rewrite (sx32_small_A 0) by lia.
  do 4 zstep. fold_reg 5%Z.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  do 2 zstep. fold_reg 11%Z. zstep. first [ifT| dIf_closed].
  lazymatch goal with H : rw_cells bsegs _ 1599112 [C4 _] |- _ =>
    change (Z_to_bv 64 256) with (Z_to_bv 64 (0 + 256 * 1)) in H; apply (c4_to_hdr3 _ _ 0 1 []) in H; [| lia| lia] end.
  do 7 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk bsegs mm _ _ |- _ => release_frame FR H (bv_unsigned sp) end end.
  zstep.
  pose proof (qwf_snoc_disj _ _ _ _ (qwf_prefix _ _ _ WF)) as DJP.
  apply evt_done. unfold qdrain_rec_post, q_lock, qrecycle_entry.
  do 12 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
  split; [eassumption|]. split; [eassumption|].
  split; [| split; [| split; [eassumption| eassumption]]].
  - apply (proj2 (qcache_rep_iff _ _ _)).
    rewrite app_length, Nat2Z.inj_add, <- ENT, <- ENG. rewrite (qfirst_app_ne _ _ (snoc_ne _ _)), <- EFG.
    rewrite (qlast_app_ne _ _ Hne), <- ELT, qbytes_app, <- EBT, <- EBG. split.
    + eassumption.
    + apply (proj2 (qchain_to_0 _ _)). apply (proj2 (qchain_to_app _ _ _ _ Hne)). split.
      * apply (proj2 (qchain_to_snoc _ _ _ _ _)). split.
        -- lazymatch goal with |- qchain_to ?mm _ _ =>
             apply (qchain_to_frame _ m mm _ _ (unbox _ QPG) MU WM) end.
           apply Forall_forall. intros e He.
           pose proof (proj1 (Forall_forall _ _) (unbox _ RG) e ltac:(apply in_or_app; left; apply in_or_app; left; exact He))
             as (E1 & E2).
           pose proof (proj1 (Forall_forall _ _) DJP e He) as E3.
           unfold r24 in E1, E2. cbv beta in E3. cbn [disjoint_from]. repeat split; lia.
        -- apply (proj2 (qbatch_iff _ _ _ _)). split; [| split; [| exact QBLe]].
           ++ rewrite <- EFT, <- EBSL. eassumption.
           ++ destruct (unbox _ QBLA) as (bws0 & BA0 & BL0 & BP0).
              exists bws0. split; [| split; [exact BL0| exact BP0]].
              lazymatch goal with |- u64arr bsegs ?mm _ _ =>
                apply (u64arr_transport bsegs _ m mm _ _ BA0 MU WM) end.
              rewrite BL0. cbn [disjoint_from]. lia.
      * lazymatch goal with |- qchain_to ?mm _ _ =>
          apply (qchain_to_frame _ m mm _ _ (proj1 (qchain_to_0 _ _) (unbox _ QCT)) MU WM) end.
        apply Forall_forall. intros e He.
        pose proof (proj1 (Forall_forall _ _) (unbox _ RG) e ltac:(apply in_or_app; right; exact He)) as (E1 & E2).
        pose proof (qwf_app_disj _ _ _ (bl, el) e (unbox _ WFx) ltac:(apply in_or_app; right; left; reflexivity) He) as E3.
        unfold r24 in E1, E2. cbn [fst] in E3. cbn [disjoint_from]. repeat split; lia.
  - apply (proj2 (qcache_rep_iff _ _ _)). cbn [length qfirst qlast qbytes map last fold_right Z.of_nat]. split; [| exact I].
    eassumption.
Qed.

Lemma qdrain_rec_empty_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Q SB cache stack lo : Z) (tl : list batch),
  tl <> [] -> qcache_rep m QG [] -> qcache_rep m Q tl -> qwf SB tl ->
  (0x10000000 < qbytes tl < 2^56)%Z ->
  q_lock m 0 0 -> rw_cells bsegs m q_max [C8 (Z_to_bv 64 0x10000000); C8 (Z_to_bv 64 0xE666661)] ->
  (0 < Q)%Z -> (Q + 32 <= 0x10000 \/ 0x6e0000 <= Q)%Z -> (Q + 32 <= r24 SB \/ r24 SB + 2^32 <= Q)%Z -> (0 < SB)%Z ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48)%Z -> (Q + 32 <= lo)%Z -> (r24 SB + 2^32 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (qdrain_rec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(q_lockw, q_lockw + 4); (QG, QG + 32); (Q, Q + 32); (bv_unsigned sp - 48, bv_unsigned sp)]%Z Q cache stack tl lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 Q) (Z_to_bv 64 cache) (Z_to_bv 64 stack) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qdrain_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until tl. intros Hne QRG QRT WF HBY LK QM HQ0 HQ HQS HSB ST HLO HQl HRl HSP MI.
  pose proof (qbytes_ge _ _ WF) as QGE.
  apply (proj1 (qcache_rep_iff _ _ _)) in QRG. destruct QRG as (QHG & _). cbn [length qfirst qlast qbytes map last fold_right] in QHG.
  apply (proj1 (qcache_rep_iff _ _ _)) in QRT. destruct QRT as (QHT & QCT). apply box in QCT.
  unfold q_lock, qdrain_entry, kHighShadowEnd, r24 in *.
  assert (RNT1 : (1 <= Z.of_nat (length tl))%Z) by (destruct tl as [|x tl']; [congruence| cbn [length]; lia]).
  assert (RNT2 : (Z.of_nat (length tl) < 2^50)%Z) by lia.
  assert (RBT : (8192 <= qbytes tl)%Z) by lia. clear QGE.
  remember (Z.of_nat (length tl)) as NT eqn:ENT.
  remember (qfirst tl) as FT eqn:EFT. remember (qlast tl) as LT eqn:ELT. remember (qbytes tl) as BT eqn:EBT.
  move QHG at bottom. move LK at bottom. move QM at bottom.
  pose proof (munch_refl [(1599112, 1599112 + 4); (1599120, 1599120 + 32); (Q, Q + 32); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  zhide.
  zidle_begin sp 48%Z MUz WMz.
  do 6 zstep.
  zidle_end MUz WMz.
  do 4 zstep.
  apply (hdr3_to_c4 _ _ 0 0 []) in LK; [| lia| lia]. change (0 + 256 * 0)%Z with 0%Z in LK.
  assert (AMO : amo_aligned AW (Z_to_bv 64 1599112) = true) by (vm_compute; reflexivity).
  amo_step AMO. rewrite (sx32_small_A 0) by lia.
  do 4 zstep. fold_reg 6%Z.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  zstep. zstep. ifF.
  zstep. zstep. ifF.
  zstep. zstep. ifF.
  zstep. zstep. first [ifT| dIf_closed].
  do 6 zstep.
  zstep; fix_lit_store. zstep; fix_lit_store. zstep; fix_lit_store.
  do 4 zstep. zstep; fix_lit_store. zstep.
  lazymatch goal with H : rw_cells bsegs _ 1599112 [C4 _] |- _ =>
    change (Z_to_bv 64 1) with (Z_to_bv 64 (1 + 256 * 0)) in H; apply (c4_to_hdr3 _ _ 1 0 []) in H; [| lia| lia] end.
  zstep; fix_lit_store.
  zstep. zstep. zstep. ifF.
  do 8 zstep.
  lazymatch goal with H : rw_cells bsegs _ 1599112 [C1 _; C1 _; C2 _] |- _ =>
    apply (hdr3_to_c4 _ _ 0 0 []) in H; [change (0 + 256 * 0)%Z with 0%Z in H| lia| lia] end.
  amo_step AMO. rewrite (sx32_small_A 0) by lia.
  do 4 zstep. fold_reg 5%Z.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  do 2 zstep. fold_reg 11%Z. zstep. first [ifT| dIf_closed].
  lazymatch goal with H : rw_cells bsegs _ 1599112 [C4 _] |- _ =>
    change (Z_to_bv 64 256) with (Z_to_bv 64 (0 + 256 * 1)) in H; apply (c4_to_hdr3 _ _ 0 1 []) in H; [| lia| lia] end.
  do 7 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk bsegs mm _ _ |- _ => release_frame FR H (bv_unsigned sp) end end.
  zstep.
  apply evt_done. unfold qdrain_rec_post, q_lock, qrecycle_entry.
  do 12 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| eassumption]; unfold sub_fp; cbn [outside]; intros; lia|].
  split; [eassumption|]. split; [eassumption|].
  split; [| split; [| split; [eassumption| eassumption]]].
  - apply (proj2 (qcache_rep_iff _ _ _)). rewrite <- ENT, <- EFT, <- ELT, <- EBT. split.
    + replace BT with (0 + BT)%Z at 4 by lia. eassumption.
    + apply (proj2 (qchain_to_0 _ _)).
      lazymatch goal with |- qchain_to ?mm _ _ =>
        apply (qchain_to_frame _ m mm _ _ (proj1 (qchain_to_0 _ _) (unbox _ QCT)) MU WM) end.
      pose proof (qwf_region _ _ WF) as RG. apply Forall_forall. intros e He.
      pose proof (proj1 (Forall_forall _ _) RG e He) as (E1 & E2). unfold r24 in E1, E2.
      cbn [disjoint_from]. repeat split; lia.
  - apply (proj2 (qcache_rep_iff _ _ _)). cbn [length qfirst qlast qbytes map last fold_right Z.of_nat]. split; [| exact I].
    eassumption.
Qed.
