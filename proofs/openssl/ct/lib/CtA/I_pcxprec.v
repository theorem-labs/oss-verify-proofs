(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import I_pcxa I_pcxdir.
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
Definition DIRXP (fw fp : word) (bg en ws sp lm cv : Z) : list cell :=
  [C4 fw; C4 fp; C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C8 (Z_to_bv 64 bg); C8 (Z_to_bv 64 en);
   C1 (Z_to_bv 8 ws); C1 (Z_to_bv 8 sp); C1 (Z_to_bv 8 lm); C1 z8; C1 (Z_to_bv 8 cv); CB 3 (repeat z8 3)].

Lemma DIRX_P : forall fw bg en ws lm cv, DIRX fw bg en ws lm cv = DIRXP fw (Z_to_bv 64 0) bg en ws 0 lm cv.
Proof. intros. reflexivity. Qed.

Lemma dirxp_forget : forall m q fw fp bg en ws sp lm cv, rw_cells ctasegs m (q + -2216) (DIRXP fw fp bg en ws sp lm cv) ->
  exists junk, rw_cells ctasegs m (q + -2216) [CB 40 junk].
Proof. intros m q fw fp bg en ws sp lm cv H. apply rw_forget in H. cbn [cells_size csize Nat.add] in H. eexists. exact H. Qed.

Lemma zb8_split : forall m p l1 l2, bytes_at ctasegs m p (zb8 (l1 ++ l2)) ->
  bytes_at ctasegs m p (zb8 l1) /\ bytes_at ctasegs m (p + Z.of_nat (length l1)) (zb8 l2).
Proof. intros m p l1 l2 BY. rewrite zb8_app in BY. apply (proj1 (bytes_at_app ctasegs m p _ _)) in BY. rewrite length_zb8 in BY. exact BY. Qed.
Lemma zb8_prefix : forall m p l1 l2, bytes_at ctasegs m p (zb8 (l1 ++ l2)) -> bytes_at ctasegs m p (zb8 l1).
Proof. intros m p l1 l2 H. exact (proj1 (zb8_split m p l1 l2 H)). Qed.

Section WithQ.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pclp_post (q x19v cvv : Z) (gp tp s0 s2 s4 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (fw fp : word) (bg ws sp lm cv : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra' (Z_to_bv 64 (q + -2240)) gp tp t0' t1' t2' s0 s1' (Z_to_bv 64 cvv) a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 x19v)
                  s4 s5 (Z_to_bv 64 (x19v + -1)) s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x1b1c14) fc None m' (seg_rom ctasegs)
    /\ munch [(q + -2216, q + -2176)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ rw_cells ctasegs m' (q + -2216) (DIRXP fw fp bg x19v ws sp lm cv).

Lemma pcx_lm_spec : forall (lmb : bool) (q r c : Z) (fw fp : word) (bg en ws sp lm0 cv0 : Z)
    ra spr gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  let ll := (if lmb then 1 else 0) in
  spr = Z_to_bv 64 (q + -2240) -> s6 = Z_to_bv 64 r -> s8 = Z_to_bv 64 (q + -2184) ->
  pcx_cconv c -> (lm0 = 0 \/ lm0 = 108) -> 0 <= sp < 256 ->
  bytes_at ctasegs m r (zb8 ((if lmb then [108] else []) ++ [c])) ->
  rw_cells ctasegs m (q + -2216) (DIRXP fw fp bg en ws sp lm0 cv0) ->
  r + 2 <= q - 2320 -> 2320 <= q -> q <= 2^47 -> mem_inv ctasegs m ->
  evt ctasegs (pclp_post q (r + ll + 1) c gp tp s0 s2 s4 s5 s7 s8 s9 s10 s11 F fc fw fp bg ws sp (if lmb then 108 else lm0) c m)
    (MS (mkR ra spr gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b1be0) fc None m (seg_rom ctasegs)).
Proof.
  intros until m. cbv zeta. intros -> -> -> CC LM0 SPR BY DIR RLO QLO QHI MI. unfold DIRXP in DIR.
  pose proof (bytes_at_bound _ _ _ _ BY) as PB. rewrite length_zb8 in PB. rewrite length_app in PB. cbn [length] in PB.
  pose proof (munch_refl [(q + -2216, q + -2176)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (r + 1)) = r + 1) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  pose proof (u8_lit sp SPR) as EUsp.
  destruct lmb.
  - cbn [app] in BY. destruct (bytes_uncons m r 108 [c] BY) as [CB0 BY1]. destruct (bytes_uncons m (r + 1) c [] BY1) as [CB1 _]. clear BY BY1.
    zhide.
    destruct CC as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]].
    all: xsteps_to 0x1d5ff0%Z.
    all: strchr_call.
    all: lstep. all: lstep. all: br2 K1. all: lstep. all: lstep. all: br2 K2.
    all: lstep. all: lstep. all: lstep. all: br2 K3. all: lstep.
    all: lstep. all: lstep. all: lstep. all: lstep. all: lstep. all: br2 K4.
    all: lazymatch goal with H : rw_cells ctasegs ?mm (?qq + -2216) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into DIR' end.
    all: lazymatch goal with |- evt _ (pclp_post _ ?xv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ =>
           setreg 19%Z (Z_to_bv 64 xv) ltac:(f_equal; lia); setreg 22%Z (Z_to_bv 64 (xv + -1)) ltac:(f_equal; lia) end.
    all: apply evt_done; unfold pclp_post; do 17 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|].
    all: revert DIR'; match goal with |- rw_cells _ _ _ ?A -> rw_cells _ _ _ ?B => replace A with B; [intros X; exact X|] end.
    all: unfold DIRXP; repeat f_equal; try lia.
    all: try (apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia).
    all: try reflexivity.
  - cbn [app] in BY. destruct (bytes_uncons m r c [] BY) as [CB0 _]. clear BY.
    zhide.
    destruct CC as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]].
    all: xsteps_to 0x1d5ff0%Z.
    all: strchr_call.
    all: lstep. all: lstep. all: br2 K1. all: lstep. all: lstep. all: br2 K2. all: lstep. all: lstep. all: br2 K2'.
    all: lstep. all: lstep. all: lstep. all: lstep. all: lstep. all: br2 K4.
    all: lazymatch goal with H : rw_cells ctasegs ?mm (?qq + -2216) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into DIR' end.
    all: lazymatch goal with |- evt _ (pclp_post _ ?xv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ =>
           setreg 19%Z (Z_to_bv 64 xv) ltac:(f_equal; lia); setreg 22%Z (Z_to_bv 64 (xv + -1)) ltac:(f_equal; lia) end.
    all: apply evt_done; unfold pclp_post; do 17 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|].
    all: revert DIR'; match goal with |- rw_cells _ _ _ ?A -> rw_cells _ _ _ ?B => replace A with B; [intros X; exact X|] end.
    all: unfold DIRXP; repeat f_equal; try lia.
    all: try (apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia).
    all: try reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pcx_pstar_spec : forall (lmb : bool) (q r c : Z) (fw : word) (bg en ws lm0 cv0 : Z)
    ra spr gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  let ll := (if lmb then 1 else 0) in
  spr = Z_to_bv 64 (q + -2240) -> s3 = Z_to_bv 64 r -> a0 = Z_to_bv 64 46 -> s7 = Z_to_bv 64 9 -> s8 = Z_to_bv 64 (q + -2184) ->
  pcx_cconv c -> (lm0 = 0 \/ lm0 = 108) ->
  bytes_at ctasegs m r (zb8 (46 :: 42 :: (if lmb then [108] else []) ++ [c])) ->
  rw_cells ctasegs m (q + -2216) (DIRX fw bg en ws lm0 cv0) ->
  r + 4 <= q - 2320 -> 2320 <= q -> q <= 2^47 -> mem_inv ctasegs m ->
  evt ctasegs (pclp_post q (r + 2 + ll + 1) c gp tp s0 s2 s4 s5 s7 s8 s9 s10 s11 F fc fw (Z_to_bv 64 0) bg ws 1 (if lmb then 108 else lm0) c m)
    (MS (mkR ra spr gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b1b80) fc None m (seg_rom ctasegs)).
Proof.
  intros until m. cbv zeta. intros -> -> -> -> -> CC LM0 BY DIR RLO QLO QHI MI. rewrite DIRX_P in DIR. unfold DIRXP in DIR.
  pose proof (bytes_at_bound _ _ _ _ BY) as PB. rewrite length_zb8 in PB. cbn [length] in PB. rewrite length_app in PB. cbn [length] in PB.
  assert (G2 : exists g2 tl, (if lmb then [108] else []) ++ [c] = g2 :: tl /\ 0 <= g2 < 256 /\ ~ is_digit g2).
  { destruct lmb; cbn [app]; eexists _, _; (split; [reflexivity|]); unfold is_digit, pcx_cconv in *; lia. }
  destruct G2 as (g2 & tl & EG & G2R & G2N).
  pose proof BY as BYall. zidle1 BYall. rewrite EG in BY.
  assert (LENL : Z.of_nat (length (zb8 (46 :: 42 :: (if lmb then [108] else []) ++ [c]))) <= 4) by (rewrite length_zb8; destruct lmb; cbn; lia).
  destruct (bytes_uncons m r 46 _ BY) as [CB0 BY1]. destruct (bytes_uncons m (r + 1) 42 _ BY1) as [CB1 BY2].
  destruct (bytes_uncons m (r + 1 + 1) g2 tl BY2) as [CB2 _]. clear BY BY1 BY2. replace (r + 1 + 1) with (r + 2) in CB2 by lia.
  pose proof (munch_refl [(q + -2216, q + -2176)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  pose proof (u8_lit g2 G2R) as EUg. unfold is_digit in G2N.
  zhide.
  lstep. lstep. br2 K0.
  lstep. lstep. lstep. br2 K1.
  lstep. lstep.
  lstep. lstep. lstep. lstep. br2 K2.
  all: lazymatch goal with H : rw_cells ctasegs ?mm (?qq + -2216) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into DIR1 end.
  all: setreg 22%Z (Z_to_bv 64 (r + 2)) ltac:(first [reflexivity | f_equal; lia | apply bv_eq; rewrite ?bv_add_unsigned, ?unsigned_lit by lia; reflexivity]).
  all: unfold zidle in BYall.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BYm : bytes_at ctasegs mm r (zb8 (46 :: 42 :: (if lmb then [108] else []) ++ [c])))
      by (apply (bytes_at_agree ctasegs m mm _ _ BYall); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; out_lia) end.
  all: destruct (bytes_uncons _ r 46 _ BYm) as [_ BYm1]; destruct (bytes_uncons _ (r + 1) 42 _ BYm1) as [_ BYt];
       replace (r + 1 + 1) with (r + 2) in BYt by lia; clear BYm BYm1 BYall.
  all: eapply evt_cut; [ eapply (pcx_lm_spec lmb q (r + 2) c fw (Z_to_bv 64 0) bg en ws 1 lm0 cv0); try reflexivity; try eassumption; try lia |].
  all: try (unfold DIRXP; exact DIR1).
  all: cbv beta; intros ms' (ra' & t0' & t1' & t2' & s1' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU2 & WM2 & MI2 & DIR2).
  all: apply evt_done; unfold pclp_post; do 17 eexists; split; [reflexivity|].
  all: split; [exact (munch_trans _ _ _ _ MU MU2)|]; split; [exact (wmono_trans ctasegs _ _ _ WM WM2)|]; split; [exact MI2| exact DIR2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pcx_pscan_spec : forall (q h : Z) (rest : list Z) (pk : Z)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (mm : mem),
  0 <= h < 256 -> ~ is_digit h -> Forall is_digit rest -> bytes_at ctasegs mm (pk + 1) (zb8 (rest ++ [h])) ->
  pk + Z.of_nat (length rest) + 2 < 2^63 -> 1 <= pk -> mem_inv ctasegs mm ->
  evt ctasegs (fun ms' => exists a0',
      ms' = MS (mkR ra (Z_to_bv 64 (q + -2240)) gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 10) (Z_to_bv 64 (pk + Z.of_nat (length rest) + 1)) s4 s5 (Z_to_bv 64 (pk + Z.of_nat (length rest) + 1)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1b1be0) fc None mm (seg_rom ctasegs))
    (MS (mkR ra (Z_to_bv 64 (q + -2240)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 10) (Z_to_bv 64 pk) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b1d14) fc None mm (seg_rom ctasegs)).
Proof.
  intros q h rest. induction rest as [|r1 rest' IH]; intros pk ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm
    HR HN RS BYr PK PK1 MIr.
  - cbn [app] in BYr. destruct (bytes_uncons mm (pk + 1) h [] BYr) as [CBh _].
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ctasegs mm) as WM.
    assert (EUk : bv_unsigned (Z_to_bv 64 pk) = pk) by (apply unsigned_lit; lia).
    pose proof (u8_lit h ltac:(lia)) as EUh. unfold is_digit in HN.
    lstep. lstep. lstep. lstep. lstep. br2 K. all: lstep.
    all: setreg 19%Z (Z_to_bv 64 (pk + Z.of_nat (@length Z []) + 1)) ltac:(f_equal; cbn [length]; lia).
    all: setreg 22%Z (Z_to_bv 64 (pk + Z.of_nat (@length Z []) + 1)) ltac:(f_equal; cbn [length]; lia).
    all: apply evt_done; eexists; reflexivity.
  - apply Forall_cons_iff in RS. destruct RS as [R1' RS']. unfold is_digit in R1'.
    cbn [app] in BYr. destruct (bytes_uncons mm (pk + 1) r1 (rest' ++ [h]) BYr) as [CBr BYr'].
    pose proof (bytes_at_bound _ _ _ _ BYr) as PBr. rewrite length_zb8 in PBr. cbn [length] in PBr. rewrite length_app in PBr. cbn [length] in PBr.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ctasegs mm) as WM.
    assert (EUk : bv_unsigned (Z_to_bv 64 pk) = pk) by (apply unsigned_lit; lia).
    pose proof (u8_lit r1 ltac:(lia)) as EUr. cbn [length] in PK.
    lstep. lstep. lstep. lstep. lstep. br2 K.
    all: setreg 19%Z (Z_to_bv 64 (pk + 1)) ltac:(f_equal; lia).
    all: replace (pk + 1 + 1) with (pk + 2) in BYr' by lia.
    all: eapply evt_mono; [apply (IH (pk + 1)); try assumption; try lia; replace (pk + 1 + 1) with (pk + 2) by lia; exact BYr'|].
    all: intros ms (a0' & ->); exists a0'; cbn [length]; rewrite Nat2Z.inj_succ.
    all: replace (pk + Z.succ (Z.of_nat (length rest')) + 1) with (pk + 1 + Z.of_nat (length rest') + 1) by lia; reflexivity.
Qed.

Lemma pcx_pnum_spec : forall (lmb : bool) (q r c d0 : Z) (ds' : list Z) (fw : word) (bg en ws lm0 cv0 : Z)
    ra spr gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  let ll := (if lmb then 1 else 0) in
  spr = Z_to_bv 64 (q + -2240) -> s2 = Z_to_bv 64 10 -> s3 = Z_to_bv 64 r -> a0 = Z_to_bv 64 46 -> s7 = Z_to_bv 64 9 -> s8 = Z_to_bv 64 (q + -2184) ->
  pcx_cconv c -> (lm0 = 0 \/ lm0 = 108) -> is_digit d0 -> Forall is_digit ds' ->
  bytes_at ctasegs m r (zb8 (46 :: d0 :: ds' ++ (if lmb then [108] else []) ++ [c])) ->
  rw_cells ctasegs m (q + -2216) (DIRX fw bg en ws lm0 cv0) ->
  r + Z.of_nat (length ds') + 5 <= q - 2320 -> 2320 <= q -> q <= 2^47 -> 1 <= r -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists fp', pclp_post q (r + Z.of_nat (length (d0 :: ds')) + 1 + ll + 1) c gp tp s0 s2 s4 s5 s7 s8 s9 s10 s11 F fc
                                               fw fp' bg ws 0 (if lmb then 108 else lm0) c m ms')
    (MS (mkR ra spr gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b1b80) fc None m (seg_rom ctasegs)).
Proof.
  intros until m. cbv zeta. intros -> -> -> -> -> -> CC LM0 D0 DS BY DIR RLO QLO QHI R1 MI. rewrite DIRX_P in DIR. unfold DIRXP in DIR.
  unfold is_digit in D0.
  assert (G2 : exists h tl, (if lmb then [108] else []) ++ [c] = h :: tl /\ 0 <= h < 256 /\ ~ is_digit h /\ (length tl <= 1)%nat).
  { destruct lmb; cbn [app]; eexists _, _; (split; [reflexivity|]); unfold is_digit, pcx_cconv in *; cbn [length]; lia. }
  destruct G2 as (h & tl & EG & HR & HN & TL). rewrite EG in BY.
  assert (LENL : Z.of_nat (length (zb8 ((if lmb then [108] else []) ++ [c]))) <= 2) by (rewrite length_zb8; destruct lmb; cbn; lia).
  pose proof (bytes_at_bound _ _ _ _ BY) as PB. rewrite length_zb8 in PB. cbn [length] in PB. rewrite length_app in PB. cbn [length] in PB.
  (* [comment removed for export] *)
  destruct (bytes_uncons m r 46 _ BY) as [CB0 BYd].
  pose proof (zb8_prefix m (r + 1) (d0 :: ds' ++ [h]) tl ltac:(cbn [app]; rewrite <- app_assoc; cbn [app]; exact BYd)) as BYp.
  pose proof (proj2 (zb8_split m (r + 1) (d0 :: ds') (h :: tl) BYd)) as BYh. rewrite <- EG in BYh.
  replace (r + 1 + Z.of_nat (length (d0 :: ds'))) with (r + Z.of_nat (length (d0 :: ds')) + 1) in BYh by lia.
  destruct (bytes_uncons m (r + 1) d0 _ BYd) as [CB1 _]. clear BY BYd.
  zidle1 BYp. zidle1 BYh.
  pose proof (munch_refl [(q + -2216, q + -2176)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (r + 1)) = r + 1) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2184)) = q + -2184) by (apply unsigned_lit; lia).
  pose proof (u8_lit d0 ltac:(lia)) as EUd.
  zhide.
  lstep. lstep. br2 K0.                 (* [comment removed for export] *)
  lstep. lstep. lstep. br2 K1.          (* [comment removed for export] *)
  all: lstep; lstep.                    (* [comment removed for export] *)
  all: setreg 22%Z (Z_to_bv 64 (r + 1)) ltac:(first [reflexivity | f_equal; lia]).
  all: lstep; lstep; lstep; br2 K2.     (* [comment removed for export] *)
  all: lstep; lstep.                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: unfold zidle in BYp.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BYp1 : bytes_at ctasegs mm (r + 1) (zb8 ((d0 :: ds') ++ [h])))
      by (apply (bytes_at_agree ctasegs m mm _ _ BYp); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx;
          rewrite length_zb8 in Hx; cbn [length] in Hx; rewrite length_app in Hx; cbn [length] in Hx; out_lia) end.
  all: zidle1 BYp.
  all: call (atoll_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (r + 1) d0 h ds');
    [ reflexivity | (unfold is_digit; lia) | exact DS | lia | exact HN | exact BYp1 | lia | assumption | ].
  all: try clear BYp1.
  (* [comment removed for export] *)
  all: lstep.
  all: unfold zidle in BYp, BYh.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BYp' : bytes_at ctasegs mm (r + 1) (zb8 ((d0 :: ds') ++ [h])))
      by (apply (bytes_at_agree ctasegs m mm _ _ BYp); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx;
          rewrite length_zb8 in Hx; cbn [length] in Hx; rewrite length_app in Hx; cbn [length] in Hx; out_lia);
    assert (BYh' : bytes_at ctasegs mm (r + Z.of_nat (length (d0 :: ds')) + 1) (zb8 ((if lmb then [108] else []) ++ [c])))
      by (apply (bytes_at_agree ctasegs m mm _ _ BYh); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [length] in Hx; out_lia);
    clear BYp BYh end.
  (* [comment removed for export] *)
  all: eapply evt_cut; [ apply (pcx_pscan_spec q h (d0 :: ds') r); [exact HR | exact HN | constructor; [unfold is_digit; lia | exact DS] | exact BYp' | cbn [length]; lia | lia | assumption] |].
  all: cbv beta; intros ms' (a0' & ->).
  all: lazymatch goal with H : rw_cells ctasegs ?mm (?qq + -2216) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into DIR1 end.
  (* [comment removed for export] *)
  all: lazymatch type of DIR1 with rw_cells _ _ _ (C4 _ :: C4 ?fpv :: _) =>
    eapply evt_cut; [ eapply (pcx_lm_spec lmb q (r + Z.of_nat (length (d0 :: ds')) + 1) c fw fpv bg en ws 0 lm0 cv0);
                      try reflexivity; try eassumption; try (cbn [length] in *; lia) |] end.
  all: try (unfold DIRXP; first [exact DIR1 | revert DIR1; match goal with |- rw_cells _ _ _ ?A -> rw_cells _ _ _ ?B => replace A with B; [intros X; exact X| repeat f_equal] end]).
  all: cbv beta; intros ms2 (ra' & t0' & t1' & t2' & s1' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU2 & WM2 & MI2 & DIR2).
  all: apply evt_done; eexists; unfold pclp_post; do 17 eexists.
  all: split; [reflexivity|].
  all: split; [exact (munch_trans _ _ _ _ MU MU2)|]; split; [exact (wmono_trans ctasegs _ _ _ WM WM2)|]; split; [exact MI2| exact DIR2].
Qed.
End WithQ.
