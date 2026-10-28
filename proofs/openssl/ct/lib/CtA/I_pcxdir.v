(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac SysStep. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_thread I_qck X_atexit D_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import I_pck I_pcbits I_pcseg I_pcdint.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import I_pcxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call ctasegs m mm MU WM end end.


(* [comment removed for export] *)
Definition DIRX (fw : word) (bg en ws lm cv : Z) : list cell :=
  [C4 fw; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C8 (Z_to_bv 64 bg); C8 (Z_to_bv 64 en);
   C1 (Z_to_bv 8 ws); C1 z8; C1 (Z_to_bv 8 lm); C1 z8; C1 (Z_to_bv 8 cv); CB 3 (repeat z8 3)].

Lemma dir0_x : forall m q, rw_cells ctasegs m (q + -2216) DIR0 -> rw_cells ctasegs m (q + -2216) (DIRX (Z_to_bv 64 0) 0 0 0 0 0).
Proof.
  intros m q H. apply (rw_cells_recast m _ DIR0 _ H); [cbn; tauto | apply map_unsigned_inj; vm_compute; reflexivity | reflexivity].
Qed.

Lemma dirx_forget : forall m q fw bg en ws lm cv, rw_cells ctasegs m (q + -2216) (DIRX fw bg en ws lm cv) ->
  exists junk, rw_cells ctasegs m (q + -2216) [CB 40 junk].
Proof. intros m q fw bg en ws lm cv H. apply rw_forget in H. cbn [cells_size csize Nat.add] in H. eexists. exact H. Qed.

(* [comment removed for export] *)
Lemma strchr_res_none : forall s c l, Forall (fun x => x <> c) l -> Forall (fun x => 0 <= x < 256) l -> strchr_res s c (zb8 l) = 0.
Proof.
  intros s c l H R. unfold strchr_res.
  assert (E : find_byte c (zb8 l) = None).
  { induction l as [|x l IH]; [reflexivity|]. apply Forall_cons_iff in H. destruct H as [Hx H]. apply Forall_cons_iff in R. destruct R as [Rx R].
    cbn [zb8 map find_byte]. rewrite (u8_lit x Rx). destruct (Z.eqb_spec x c); [lia|]. fold (zb8 l). rewrite (IH H R). reflexivity. }
  rewrite E. reflexivity.
Qed.

Definition notin_flags (g : Z) : Prop := g <> 39 /\ g <> 45 /\ g <> 43 /\ g <> 32 /\ g <> 35 /\ g <> 48.
Definition notin_qual (g : Z) : Prop := g <> 106 /\ g <> 122 /\ g <> 116 /\ g <> 76 /\ g <> 113.

Lemma strchr_flags_none : forall s g, notin_flags g -> strchr_res s g (zb8 S_FLAGS) = 0.
Proof. intros s g (A1 & A2 & A3 & A4 & A5 & A6). apply strchr_res_none; unfold S_FLAGS; repeat constructor; lia. Qed.
Lemma strchr_qual_none : forall s g, notin_qual g -> strchr_res s g (zb8 S_QUAL) = 0.
Proof. intros s g (A1 & A2 & A3 & A4 & A5). apply strchr_res_none; unfold S_QUAL; repeat constructor; lia. Qed.

(* [comment removed for export] *)
Ltac strchr_call_none NONE :=
  call internal_strchr_spec';
  [ reflexivity | rewrite ?u8_lit by lia; rewrite unsigned_lit by lia; reflexivity | lia
  | first [ apply cstr_s_flags | apply cstr_s_qual ]; assumption
  | assumption | ];
  match goal with |- context [strchr_res ?a ?c ?l] => rewrite (NONE a c) by assumption end.

(* [comment removed for export] *)

Section WithQ.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pcx_p1_spec : forall (q p : Z) (ds : list Z) (g : Z) (fw : word) (en ws lm cv : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 (q + -2240) -> s0 = Z_to_bv 64 q -> s2 = Z_to_bv 64 10 -> s3 = Z_to_bv 64 p -> s7 = Z_to_bv 64 9 ->
  s8 = Z_to_bv 64 (q + -2184) -> s11 = Z_to_bv 64 37 ->
  Forall is_digit ds -> 0 < g < 256 -> ~ is_digit g -> g <> 37 -> (ds <> [] -> g <> 36) ->
  bytes_at ctasegs m p (zb8 (37 :: ds ++ [g])) ->
  rw_cells ctasegs m (q + -2216) (DIRX fw 0 en ws lm cv) ->
  p + Z.of_nat (length ds) + 2 <= q - 2320 -> 2320 <= q -> q <= 2^47 -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' (Z_to_bv 64 p) a3' a4' a5' a6' a7' s2 (Z_to_bv 64 (p + 1)) s4 s5 s6 s7 s8 s9
                    s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x1b1b08) fc None m' (seg_rom ctasegs)
      /\ munch [(q + -2216, q + -2176)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ rw_cells ctasegs m' (q + -2216) (DIRX fw p en ws lm cv))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b1a98) fc None m (seg_rom ctasegs)).
Proof.
  intros until m. intros -> -> -> -> -> -> -> DS Hg NDg G37 G36 BY DIR PLO QLO QHI MI.
  unfold DIRX in DIR. unfold is_digit in NDg.
  pose proof (bytes_at_bound _ _ _ _ BY) as PB. rewrite length_zb8 in PB. cbn [length] in PB. rewrite length_app in PB. cbn [length] in PB.
  destruct (bytes_uncons m p 37 (ds ++ [g]) BY) as [CB0 BY1].
  pose proof (munch_refl [(q + -2216, q + -2176)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUp1 : bv_unsigned (Z_to_bv 64 (p + 1)) = p + 1) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  zhide.
  destruct ds as [|d1 ds'].
  - (* [comment removed for export] *)
    cbn [app] in BY1. destruct (bytes_uncons m (p + 1) g [] BY1) as [CB1 _]. clear BY BY1.
    pose proof (u8_lit g ltac:(lia)) as EUg.
    (* [comment removed for export] *)
    lstep. lstep. br2 K0. lstep.
    lstep. lstep. br2 K1. lstep. br2 K2. lstep. lstep. lstep. br2 K3. lstep.
    lazymatch goal with H : rw_cells ctasegs ?mm (?qq + -2216) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into DIR' end.
    setreg 12%Z (Z_to_bv 64 p) ltac:(f_equal; lia).
    apply evt_done. do 16 eexists. split; [| split; [exact MU| split; [exact WM| split; [assumption| exact DIR']]]]. reflexivity.
  - (* [comment removed for export] *)
    apply Forall_cons_iff in DS. destruct DS as [D1 DS']. unfold is_digit in D1. cbn [length] in PLO. specialize (G36 ltac:(discriminate)).
    pose proof BY1 as BYd. cbn [app] in BY1. destruct (bytes_uncons m (p + 1) d1 (ds' ++ [g]) BY1) as [CB1 _]. clear BY BY1. zidle1 BYd.
    pose proof (u8_lit d1 ltac:(lia)) as EUd.
    lstep. lstep. br2 K0. lstep.
    lstep. lstep. br2 K1. lstep. br2 K2. lstep. lstep. lstep. br2 K3.
    lstep. lstep.
    unfold zidle in BYd.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (BYd' : bytes_at ctasegs mm (p + 1) (zb8 (d1 :: ds' ++ [g])))
        by (apply (bytes_at_agree ctasegs m mm _ _ BYd); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx;
            rewrite length_zb8 in Hx; cbn [length] in Hx; rewrite length_app in Hx; cbn [length] in Hx; out_lia) end.
    call (atoll_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (p + 1) d1 g ds');
      [ reflexivity | (unfold is_digit; lia) | exact DS' | lia | (unfold is_digit; lia) | exact BYd' | lia | assumption | ].
    (* [comment removed for export] *)
    lstep.
    assert (SCAN : forall (rest : list Z) (pk : Z) ra' x12 x13 t0' t1' t2' a0' a4' a5' a6' a7' t3' t4' t5' t6' (mm : mem),
      Forall is_digit rest -> bytes_at ctasegs mm pk (zb8 (rest ++ [g])) -> pk + Z.of_nat (length rest) + 1 < 2^63 -> mem_inv ctasegs mm ->
      evt ctasegs (fun ms' => exists x13' : word,
          ms' = MS (mkR ra' (Z_to_bv 64 (q + -2240)) gp tp t0' t1' t2' (Z_to_bv 64 q) s1 a0' (Z_to_bv 64 (pk + Z.of_nat (length rest) + 1))
                        (Z_to_bv 64 g) x13' a4' a5' a6' a7' (Z_to_bv 64 10) (Z_to_bv 64 (p + 1)) s4 s5 s6 (Z_to_bv 64 9) (Z_to_bv 64 (q + -2184)) s9
                        s10 (Z_to_bv 64 37) t3' t4' t5' t6') F (Z_to_bv 64 0x1b1af4) fc None mm (seg_rom ctasegs))
        (MS (mkR ra' (Z_to_bv 64 (q + -2240)) gp tp t0' t1' t2' (Z_to_bv 64 q) s1 a0' (Z_to_bv 64 pk) x12 x13 a4' a5' a6' a7'
                 (Z_to_bv 64 10) (Z_to_bv 64 (p + 1)) s4 s5 s6 (Z_to_bv 64 9) (Z_to_bv 64 (q + -2184)) s9 s10 (Z_to_bv 64 37) t3' t4' t5' t6')
            F (Z_to_bv 64 0x1b1ae4) fc None mm (seg_rom ctasegs))).
    { clear - QLO QHI Hg NDg. intro rest. induction rest as [|r1 rest' IH]; intros pk ra' x12 x13 t0' t1' t2' a0' a4' a5' a6' a7' t3' t4' t5' t6' mm RS BYr PK MIr.
      - cbn [app] in BYr. destruct (bytes_uncons mm pk g [] BYr) as [CBg _].
        pose proof (bytes_at_bound _ _ _ _ BYr) as PBr. cbn [length zb8 map] in PBr.
        pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ctasegs mm) as WM.
        assert (EUk : bv_unsigned (Z_to_bv 64 pk) = pk) by (apply unsigned_lit; lia).
        pose proof (u8_lit g ltac:(lia)) as EUg.
        lstep. lstep. lstep. lstep. br2 K.
        apply evt_done. eexists. cbn [length Z.of_nat]. rewrite Z.add_0_r. rewrite EUg. reflexivity.
      - apply Forall_cons_iff in RS. destruct RS as [R1 RS']. unfold is_digit in R1.
        cbn [app] in BYr. destruct (bytes_uncons mm pk r1 (rest' ++ [g]) BYr) as [CBr BYr'].
        pose proof (bytes_at_bound _ _ _ _ BYr) as PBr. rewrite length_zb8 in PBr. cbn [length] in PBr. rewrite length_app in PBr. cbn [length] in PBr.
        pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ctasegs mm) as WM.
        assert (EUk : bv_unsigned (Z_to_bv 64 pk) = pk) by (apply unsigned_lit; lia).
        pose proof (u8_lit r1 ltac:(lia)) as EUr. cbn [length] in PK.
        lstep. lstep. lstep. lstep. br2 K.
        eapply evt_mono; [apply (IH (pk + 1)); try assumption; lia|].
        intros ms (x13' & ->). exists x13'. cbn [length]. rewrite Nat2Z.inj_succ.
        replace (pk + Z.succ (Z.of_nat (length rest')) + 1) with (pk + 1 + Z.of_nat (length rest') + 1) by lia. reflexivity. }
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (BYd2 : bytes_at ctasegs mm (p + 1) (zb8 ((d1 :: ds') ++ [g])))
        by (apply (bytes_at_agree ctasegs m mm _ _ BYd); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx;
            rewrite length_zb8 in Hx; cbn [length] in Hx; rewrite length_app in Hx; cbn [length] in Hx; out_lia) end.
    eapply evt_cut.
    { apply (SCAN (d1 :: ds') (p + 1)); [constructor; [unfold is_digit; lia | exact DS'] | exact BYd2 | cbn [length]; lia | assumption]. }
    cbv beta. intros ms' (x13' & ->). cbn [length] in *.
    assert (EUe : bv_unsigned (Z_to_bv 64 (p + 1 + Z.of_nat (S (length ds')) + 1)) = p + 1 + Z.of_nat (S (length ds')) + 1) by (apply unsigned_lit; lia).
    pose proof (u8_lit g ltac:(lia)) as EUg.
    lstep. lstep. br2 K4. lstep.
    lazymatch goal with H : rw_cells ctasegs ?mm (?qq + -2216) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into DIR' end.
    setreg 12%Z (Z_to_bv 64 p) ltac:(f_equal; lia).
    apply evt_done. do 16 eexists. split; [| split; [exact MU| split; [exact WM| split; [assumption| exact DIR']]]]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pcx_flags_spec : forall (fs : list Z) (q cur g : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 (q + -2240) -> s3 = Z_to_bv 64 cur -> a2 = Z_to_bv 64 (cur + -1) -> s4 = Z_to_bv 64 134456 ->
  Forall (fun f => f = 45 \/ f = 48) fs -> 0 < g < 256 -> notin_flags g ->
  bytes_at ctasegs m cur (zb8 (fs ++ [g])) -> cur + Z.of_nat (length fs) + 1 < 2^63 -> 1 <= cur -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (ra' t0' t1' t2' a1' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 (cur + Z.of_nat (length fs) + -1)) (Z_to_bv 64 0) a1'
                    (Z_to_bv 64 (cur + Z.of_nat (length fs))) a3' a4' a5' a6' a7' s2 (Z_to_bv 64 (cur + Z.of_nat (length fs) + 1)) s4 s5 s6 s7 s8 s9
                    s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x1b1b24) fc None m' (seg_rom ctasegs)
      /\ munch [] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b1b08) fc None m (seg_rom ctasegs)).
Proof.
  induction fs as [|f fs IH]; intros q cur g ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    -> -> -> -> FS Hg NF BY PH C1 MI.
  - cbn [app] in BY. destruct (bytes_uncons m cur g [] BY) as [CB0 _].
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 cur) = cur) by (apply unsigned_lit; lia).
    pose proof (u8_lit g ltac:(lia)) as EUg. pose proof NF as NF'. unfold notin_flags in NF'.
    xsteps_to 0x1d5ff0%Z. strchr_call_none strchr_flags_none.
    lstep. lstep. lstep. br2 K.
    setreg 9%Z (Z_to_bv 64 (cur + Z.of_nat (@length Z []) + -1)) ltac:(f_equal; cbn [length]; lia).
    setreg 12%Z (Z_to_bv 64 (cur + Z.of_nat (@length Z []))) ltac:(f_equal; cbn [length]; lia).
    setreg 19%Z (Z_to_bv 64 (cur + Z.of_nat (@length Z []) + 1)) ltac:(f_equal; cbn [length]; lia).
    apply evt_done. do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM| assumption].
  - apply Forall_cons_iff in FS. destruct FS as [Ff FS].
    cbn [app] in BY. destruct (bytes_uncons m cur f (fs ++ [g]) BY) as [CB0 BY'].
    pose proof (bytes_at_bound _ _ _ _ BY) as PB. rewrite length_zb8 in PB. cbn [length] in PB. rewrite length_app in PB. cbn [length] in PB.
    cbn [length] in PH.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 cur) = cur) by (apply unsigned_lit; lia).
    destruct Ff as [-> | ->].
    all: xsteps_to 0x1d5ff0%Z.
    all: strchr_call.
    all: lstep. all: lstep. all: lstep. all: br2 K.
    all: setreg 12%Z (Z_to_bv 64 (cur + 1 + -1)) ltac:(f_equal; lia).
    all: eapply evt_mono; [eapply (IH q (cur + 1) g); try reflexivity; try assumption; lia |].
    all: intros ms (ra' & t0' & t1' & t2' & a1' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU2 & WM2 & MI2).
    all: exists ra', t0', t1', t2', a1', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    all: split; [| split; [| split; [exact (wmono_trans ctasegs _ _ _ WM WM2)| exact MI2]]].
    all: try (cbn [length]; rewrite !Nat2Z.inj_succ;
              replace (cur + 1 + Z.of_nat (length fs) + -1) with (cur + Z.succ (Z.of_nat (length fs)) + -1) by lia;
              replace (cur + 1 + Z.of_nat (length fs) + 1) with (cur + Z.succ (Z.of_nat (length fs)) + 1) by lia;
              replace (cur + 1 + Z.of_nat (length fs)) with (cur + Z.succ (Z.of_nat (length fs))) by lia; reflexivity).
    all: lazymatch type of MU with munch _ ?m0 ?m1 => exact (munch_trans [] m0 m1 m' MU MU2) end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pcw_post (q x19v hv : Z) (gp tp s0 s2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (fw : word) (bg en ws lm cv : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra' (Z_to_bv 64 (q + -2240)) gp tp t0' t1' t2' s0 s1' (Z_to_bv 64 hv) a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 x19v)
                  s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x1b1b80) fc None m' (seg_rom ctasegs)
    /\ munch [(q + -2216, q + -2176)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ rw_cells ctasegs m' (q + -2216) (DIRX fw bg en ws lm cv).

(* [comment removed for export] *)
Lemma pcx_wstar_spec : forall (q e g2 : Z) (fw : word) (bg en ws lm cv : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 (q + -2240) -> s3 = Z_to_bv 64 (e + 1) -> s8 = Z_to_bv 64 (q + -2184) ->
  0 <= g2 < 256 -> bytes_at ctasegs m e (zb8 [42; g2]) ->
  rw_cells ctasegs m (q + -2216) (DIRX fw bg en ws lm cv) ->
  e + 2 <= q - 2320 -> 2320 <= q -> q <= 2^47 -> mem_inv ctasegs m ->
  evt ctasegs (pcw_post q (e + 1) g2 gp tp s0 s2 s4 s5 s6 s7 s8 s9 s10 s11 F fc fw bg en 1 lm cv m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b1b24) fc None m (seg_rom ctasegs)).
Proof.
  intros until m. intros -> -> -> Hg BY DIR ELO QLO QHI MI. unfold DIRX in DIR.
  pose proof (bytes_at_bound _ _ _ _ BY) as PB. rewrite length_zb8 in PB. cbn [length] in PB.
  destruct (bytes_uncons m e 42 [g2] BY) as [CB0 BY1]. destruct (bytes_uncons m (e + 1) g2 [] BY1) as [CB1 _]. clear BY BY1.
  pose proof (munch_refl [(q + -2216, q + -2176)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUe : bv_unsigned (Z_to_bv 64 (e + 1)) = e + 1) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  pose proof (u8_lit g2 Hg) as EUg.
  zhide.
  lstep. lstep. lstep. br2 K. lstep. lstep. lstep. lstep.
  lazymatch goal with H : rw_cells ctasegs ?mm (?qq + -2216) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into DIR' end.
  rewrite EUg.
  apply evt_done. unfold pcw_post. do 17 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact DIR'].
Qed.

(* [comment removed for export] *)
Lemma pcx_wnone_spec : forall (q e g : Z) (fw : word) (bg en ws lm cv : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 (q + -2240) -> s3 = Z_to_bv 64 (e + 1) -> s7 = Z_to_bv 64 9 -> s8 = Z_to_bv 64 (q + -2184) ->
  0 <= g < 256 -> g <> 42 -> ~ is_digit g -> bytes_at ctasegs m e (zb8 [g]) ->
  rw_cells ctasegs m (q + -2216) (DIRX fw bg en ws lm cv) ->
  e + 1 <= q - 2320 -> 2320 <= q -> q <= 2^47 -> mem_inv ctasegs m ->
  evt ctasegs (pcw_post q e g gp tp s0 s2 s4 s5 s6 s7 s8 s9 s10 s11 F fc fw bg en 0 lm cv m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b1b24) fc None m (seg_rom ctasegs)).
Proof.
  intros until m. intros -> -> -> -> Hg G42 NDg BY DIR ELO QLO QHI MI. unfold DIRX in DIR. unfold is_digit in NDg.
  pose proof (bytes_at_bound _ _ _ _ BY) as PB. rewrite length_zb8 in PB. cbn [length] in PB.
  destruct (bytes_uncons m e g [] BY) as [CB0 _]. clear BY.
  pose proof (munch_refl [(q + -2216, q + -2176)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUe : bv_unsigned (Z_to_bv 64 (e + 1)) = e + 1) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  pose proof (u8_lit g Hg) as EUg.
  zhide.
  lstep. lstep. lstep. br2 K.
  lstep. setreg 19%Z (Z_to_bv 64 e) ltac:(f_equal; lia).
  assert (EUe0 : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
  lstep. lstep. lstep. lstep. br2 K1.
  lazymatch goal with H : rw_cells ctasegs ?mm (?qq + -2216) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into DIR' end.
  rewrite EUg.
  apply evt_done. unfold pcw_post. do 17 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  change (Z_to_bv 8 0) with z8. exact DIR'.
Qed.

(* [comment removed for export] *)
Lemma pcx_wdig_spec : forall (q e g h : Z) (ds' : list Z) (fw : word) (bg en ws lm cv : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 (q + -2240) -> s1 = Z_to_bv 64 (e + -1) -> s2 = Z_to_bv 64 10 -> s3 = Z_to_bv 64 (e + 1) -> s7 = Z_to_bv 64 9 ->
  s8 = Z_to_bv 64 (q + -2184) ->
  is_digit g -> Forall is_digit ds' -> 0 <= h < 256 -> ~ is_digit h -> bytes_at ctasegs m e (zb8 (g :: ds' ++ [h])) ->
  rw_cells ctasegs m (q + -2216) (DIRX fw bg en ws lm cv) ->
  e + Z.of_nat (length ds') + 2 <= q - 2320 -> 2320 <= q -> q <= 2^47 -> 1 <= e -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists fw', pcw_post q (e + 1 + Z.of_nat (length ds')) h gp tp s0 s2 s4 s5 s6 s7 s8 s9 s10 s11 F fc fw' bg en 0 lm cv m ms')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b1b24) fc None m (seg_rom ctasegs)).
Proof.
  intros until m. intros -> -> -> -> -> -> Dg DS Hh NDh BY DIR ELO QLO QHI E1 MI. unfold DIRX in DIR. unfold is_digit in Dg, NDh.
  pose proof BY as BYd. zidle1 BYd.
  destruct (bytes_uncons m e g (ds' ++ [h]) BY) as [CB0 _]. clear BY.
  pose proof (munch_refl [(q + -2216, q + -2176)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUe : bv_unsigned (Z_to_bv 64 (e + 1)) = e + 1) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  pose proof (u8_lit g ltac:(lia)) as EUg.
  zhide.
  lstep. lstep. lstep. br2 K.
  lstep. setreg 19%Z (Z_to_bv 64 e) ltac:(f_equal; lia).
  assert (EUe0 : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
  lstep. lstep. lstep. lstep. br2 K1.
  lstep. lstep.
  unfold zidle in BYd.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BYd' : bytes_at ctasegs mm e (zb8 (g :: ds' ++ [h])))
      by (apply (bytes_at_agree ctasegs m mm _ _ BYd); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx;
          rewrite length_zb8 in Hx; cbn [length] in Hx; rewrite length_app in Hx; cbn [length] in Hx; out_lia) end.
  call (atoll_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e g h ds');
    [ reflexivity | (unfold is_digit; lia) | exact DS | lia | (unfold is_digit; lia) | exact BYd' | lia | assumption | ].
  (* [comment removed for export] *)
  lstep.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells ctasegs ?mm (?qq + -2216) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into DIR' end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BYd2 : bytes_at ctasegs mm e (zb8 ((g :: ds') ++ [h])))
      by (apply (bytes_at_agree ctasegs m mm _ _ BYd); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx;
          rewrite length_zb8 in Hx; cbn [length] in Hx; rewrite length_app in Hx; cbn [length] in Hx; out_lia) end.
  assert (SCAN : forall (rest : list Z) (pk : Z) ra' x10 x11 x19 t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (mm : mem),
    Forall is_digit rest -> bytes_at ctasegs mm pk (zb8 (rest ++ [h])) -> pk + Z.of_nat (length rest) + 1 < 2^63 -> 1 <= pk -> mem_inv ctasegs mm ->
    evt ctasegs (fun ms' => exists x11' : word,
        ms' = MS (mkR ra' (Z_to_bv 64 (q + -2240)) gp tp t0' t1' t2' s0 (Z_to_bv 64 (pk + Z.of_nat (length rest))) (Z_to_bv 64 h) x11' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 10) (Z_to_bv 64 (pk + Z.of_nat (length rest))) s4 s5 s6 (Z_to_bv 64 9) (Z_to_bv 64 (q + -2184)) s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x1b1b80) fc None mm (seg_rom ctasegs))
      (MS (mkR ra' (Z_to_bv 64 (q + -2240)) gp tp t0' t1' t2' s0 (Z_to_bv 64 (pk + -1)) x10 x11 a2' a3' a4' a5' a6' a7'
               (Z_to_bv 64 10) x19 s4 s5 s6 (Z_to_bv 64 9) (Z_to_bv 64 (q + -2184)) s9 s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x1b1b6c) fc None mm (seg_rom ctasegs))).
  { clear - QLO QHI Hh NDh. intro rest. induction rest as [|r1 rest' IH]; intros pk ra' x10 x11 x19 t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mm RS BYr PK PK1 MIr.
    - cbn [app] in BYr. destruct (bytes_uncons mm pk h [] BYr) as [CBh _].
      pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ctasegs mm) as WM.
      assert (EUk : bv_unsigned (Z_to_bv 64 (pk + -1)) = pk + -1) by (apply unsigned_lit; lia).
      pose proof (u8_lit h ltac:(lia)) as EUh.
      lstep. lstep. lstep. lstep. lstep. br2 K.
      setreg 9%Z (Z_to_bv 64 (pk + Z.of_nat (@length Z []))) ltac:(f_equal; cbn [length]; lia).
      setreg 19%Z (Z_to_bv 64 (pk + Z.of_nat (@length Z []))) ltac:(f_equal; cbn [length]; lia).
      rewrite EUh. apply evt_done. eexists. reflexivity.
    - apply Forall_cons_iff in RS. destruct RS as [R1 RS']. unfold is_digit in R1.
      cbn [app] in BYr. destruct (bytes_uncons mm pk r1 (rest' ++ [h]) BYr) as [CBr BYr'].
      pose proof (bytes_at_bound _ _ _ _ BYr) as PBr. rewrite length_zb8 in PBr. cbn [length] in PBr. rewrite length_app in PBr. cbn [length] in PBr.
      pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ctasegs mm) as WM.
      assert (EUk : bv_unsigned (Z_to_bv 64 (pk + -1)) = pk + -1) by (apply unsigned_lit; lia).
      pose proof (u8_lit r1 ltac:(lia)) as EUr. cbn [length] in PK.
      lstep. lstep. lstep. lstep. lstep. br2 K.
      setreg 9%Z (Z_to_bv 64 (pk + 1 + -1)) ltac:(f_equal; lia).
      eapply evt_mono; [apply (IH (pk + 1)); try assumption; lia|].
      intros ms (x11' & ->). exists x11'. cbn [length]. rewrite Nat2Z.inj_succ.
      replace (pk + Z.succ (Z.of_nat (length rest'))) with (pk + 1 + Z.of_nat (length rest')) by lia. reflexivity. }
  eapply evt_cut.
  { apply (SCAN (g :: ds') e); [constructor; [unfold is_digit; lia | exact DS] | exact BYd2 | cbn [length]; lia | lia | assumption]. }
  cbv beta. intros ms' (x11' & ->). cbn [length]. rewrite Nat2Z.inj_succ.
  replace (e + Z.succ (Z.of_nat (length ds'))) with (e + 1 + Z.of_nat (length ds')) by lia.
  apply evt_done. eexists. unfold pcw_post. do 17 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  change (Z_to_bv 8 0) with z8. exact DIR'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pcl_post (q x19v cvv : Z) (gp tp s0 s2 s4 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (fw : word) (bg ws lm cv : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra' (Z_to_bv 64 (q + -2240)) gp tp t0' t1' t2' s0 s1' (Z_to_bv 64 cvv) a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 x19v)
                  s4 s5 (Z_to_bv 64 (x19v + -1)) s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x1b1c14) fc None m' (seg_rom ctasegs)
    /\ munch [(q + -2216, q + -2176)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ rw_cells ctasegs m' (q + -2216) (DIRX fw bg x19v ws lm cv).

Definition pcx_cconv (c : Z) : Prop := c = 100 \/ c = 105 \/ c = 117 \/ c = 120 \/ c = 88 \/ c = 99 \/ c = 115.

Lemma pcx_len_spec : forall (lmb : bool) (q r c : Z) (fw : word) (bg en ws lm0 cv0 : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  let h := (if lmb then 108 else c) in
  let ll := (if lmb then 1 else 0) in
  sp = Z_to_bv 64 (q + -2240) -> s3 = Z_to_bv 64 r -> a0 = Z_to_bv 64 h -> s8 = Z_to_bv 64 (q + -2184) ->
  pcx_cconv c -> (lm0 = 0 \/ lm0 = 108) ->
  bytes_at ctasegs m r (zb8 ((if lmb then [108] else []) ++ [c])) ->
  rw_cells ctasegs m (q + -2216) (DIRX fw bg en ws lm0 cv0) ->
  r + 2 <= q - 2320 -> 2320 <= q -> q <= 2^47 -> mem_inv ctasegs m ->
  evt ctasegs (pcl_post q (r + ll + 1) c gp tp s0 s2 s4 s5 s7 s8 s9 s10 s11 F fc fw bg ws (if lmb then 108 else lm0) c m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b1b80) fc None m (seg_rom ctasegs)).
Proof.
  intros until m. cbv zeta. intros -> -> -> -> CC LM0 BY DIR RLO QLO QHI MI. unfold DIRX in DIR.
  pose proof (bytes_at_bound _ _ _ _ BY) as PB. rewrite length_zb8 in PB. rewrite length_app in PB. cbn [length] in PB.
  pose proof (munch_refl [(q + -2216, q + -2176)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (r + 1)) = r + 1) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  destruct lmb.
  - cbn [app] in BY. destruct (bytes_uncons m r 108 [c] BY) as [CB0 BY1]. destruct (bytes_uncons m (r + 1) c [] BY1) as [CB1 _]. clear BY BY1.
    zhide.
    destruct CC as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]].
    all: lstep; lstep; br2 K0.
    all: xsteps_to 0x1d5ff0%Z.
    all: strchr_call.
    all: lstep. all: lstep. all: br2 K1. all: lstep. all: lstep. all: br2 K2.
    all: lstep. all: lstep. all: lstep. all: br2 K3. all: lstep.
    all: lstep. all: lstep. all: lstep. all: lstep. all: lstep. all: br2 K4.
    all: lazymatch goal with H : rw_cells ctasegs ?mm (?qq + -2216) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into DIR' end.
    all: lazymatch goal with |- evt _ (pcl_post _ ?xv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ =>
           setreg 19%Z (Z_to_bv 64 xv) ltac:(f_equal; lia); setreg 22%Z (Z_to_bv 64 (xv + -1)) ltac:(f_equal; lia) end.
    all: apply evt_done; unfold pcl_post; do 17 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|].
    all: revert DIR'; match goal with |- rw_cells _ _ _ ?A -> rw_cells _ _ _ ?B => replace A with B; [intros X; exact X|] end.
    all: unfold DIRX; repeat f_equal; try lia.
    all: try (apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia).
    all: try reflexivity.
  - cbn [app] in BY. destruct (bytes_uncons m r c [] BY) as [CB0 _]. clear BY.
    zhide.
    destruct CC as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]].
    all: lstep; lstep; br2 K0.
    all: xsteps_to 0x1d5ff0%Z.
    all: strchr_call.
    all: lstep. all: lstep. all: br2 K1. all: lstep. all: lstep. all: br2 K2. all: lstep. all: lstep. all: br2 K2'.
    all: lstep. all: lstep. all: lstep. all: lstep. all: lstep. all: br2 K4.
    all: lazymatch goal with H : rw_cells ctasegs ?mm (?qq + -2216) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into DIR' end.
    all: lazymatch goal with |- evt _ (pcl_post _ ?xv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ =>
           setreg 19%Z (Z_to_bv 64 xv) ltac:(f_equal; lia); setreg 22%Z (Z_to_bv 64 (xv + -1)) ltac:(f_equal; lia) end.
    all: apply evt_done; unfold pcl_post; do 17 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|].
    all: revert DIR'; match goal with |- rw_cells _ _ _ ?A -> rw_cells _ _ _ ?B => replace A with B; [intros X; exact X|] end.
    all: unfold DIRX; repeat f_equal; try lia.
    all: try (apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia).
    all: try reflexivity.
Qed.
End WithQ.
