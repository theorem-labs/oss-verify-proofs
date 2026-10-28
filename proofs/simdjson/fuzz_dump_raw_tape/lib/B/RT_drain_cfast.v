(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_glue_defs R_m2s R_thread R_poison R_prim_kit R_depot_defs R_quar_defs R_cdealloc R_return R_return_T R_return_A R_prim_lists RT_freeA RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_maltail RT_freeA2 RT_drain_defs RT_drain_pure RT_drain_kit RT_drain_art RT_drain_art3 RT_drain_geo RT_drain_cdk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

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

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Lemma ri_tail_norm : forall (m : mem) R rand exh pad nal nfr r0 r1 r2 r3, ri_tail m R rand exh pad nal nfr r0 r1 r2 r3 ->
  ri_tail m R rand exh pad (bv_unsigned (Z_to_bv 64 nal)) (bv_unsigned (Z_to_bv 64 nfr)) (bv_unsigned (Z_to_bv 64 r0))
    (bv_unsigned (Z_to_bv 64 r1)) (bv_unsigned (Z_to_bv 64 r2)) (bv_unsigned (Z_to_bv 64 r3)).
Proof. intros. unfold ri_tail in *. rewrite !Z_to_bv_bv_unsigned. exact H. Qed.

Lemma bv64_range : forall z, 0 <= bv_unsigned (Z_to_bv 64 z) < 2 ^ 64.
Proof. intros z. pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 z)) as X. unfold bv_modulus in X. cbn [Z.of_N] in X. lia. Qed.

Definition dh_reg (c : Z) (r : regst) (l : list Z) (mfa' : Z) : regst :=
  mkReg (r_muser r) mfa' (r_st r) (r_fl r ++ skipn (dh_keep c) l).

Lemma cdeal_reg_full : forall c r l, cdeal_full c l = true -> cdeal_reg c r l = dh_reg c r l (dh_mfa c r).
Proof. intros c r l H. unfold cdeal_reg, dh_reg. rewrite H. reflexivity. Qed.
Lemma cdeal_ca_full : forall c i l, cdeal_full c l = true -> cdeal_ca c i l = firstn (dh_keep c) l ++ [Z.of_nat i].
Proof. intros c i l H. unfold cdeal_ca. rewrite H. reflexivity. Qed.

Lemma dh_keep_eq : forall c, 1 <= c <= 31 -> Z.of_nat (dh_keep c) = MaxCount c - MaxCount c / 2 /\ (dh_keep c + Z.to_nat (MaxCount c / 2) = Z.to_nat (MaxCount c))%nat.
Proof.
  intros c Hc. pose proof (MaxCount_range c Hc) as (M1 & M2). unfold dh_keep.
  assert (0 <= MaxCount c / 2 <= MaxCount c) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  split; [rewrite Z2Nat.id by lia; reflexivity | lia].
Qed.

Section RegDrain.
Variables (Σ : rtsA) (m m' : mem) (c : Z) (W : list ivl) (mfa' : Z) (ws' : list word).
Hypothesis HG : geo_ok Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis HR0 : reg_rep (l_SB (lay Σ)) c (pr Σ c) m.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis HWs : disjoint_from W (shad (rb (l_SB (lay Σ)) c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))))
                   ((r_muser (pr Σ c) - ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) / 8).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation R := (rinfo (RIS_of (l_SB (lay Σ))) c).
#[local] Notation r := (pr Σ c).
#[local] Notation au := (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).

Lemma cd_reg_drain : forall (l : list Z),
  ri_lock m' R 0 -> ri_core m' R (Z.of_nat (length (r_fl r ++ skipn (dh_keep c) l))) mfa' au (r_muser r) ->
  (exists rand exh pad nal nfr r0 r1 r2 r3, ri_tail m' R rand exh pad nal nfr r0 r1 r2 r3) ->
  fl_arr m' SB c ws' -> 4 * Z.of_nat (length ws') = mfa' -> firstn (length (r_fl r ++ skipn (dh_keep c) l)) ws' = map (cpw c) (r_fl r ++ skipn (dh_keep c) l) ->
  reg_rep SB c (dh_reg c r l mfa') m'.
Proof using HG Hc HR0 MU WM HWs.
  intros l LK RC RT FL Hws Hfw. pose proof HR0 as (_ & _ & _ & _ & STU & SHU & STSH).
  pose proof (dk_rb Σ HG c Hc) as (B1 & B2 & B3 & B4). pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  pose proof HG as (_ & (HR & _) & _). pose proof (HR c Hc) as (W1 & _ & W3 & _).
  pose proof (Z.mul_nonneg_nonneg (ClassSize c) (Z.of_nat (length (r_st r))) ltac:(pose proof (ClassSize_range c Hc); lia) (Nat2Z.is_nonneg _)) as AU0.
  unfold reg_rep, dh_reg. cbn [r_muser r_mfa r_st r_fl].
  split; [exact LK|]. split; [exact RC|]. split; [exact RT|]. split; [exists ws'; split; [exact FL | split; [exact Hws | exact Hfw]]|].
  split; [apply (dk_stk_wmono m m' _ _ STU WM); unfold img_hull_hi, SEGTOP_A in *; lia|].
  split; [|apply (dk_stk_wmono m m' _ _ STSH WM); unfold img_hull_hi, shad, SHB, SEGTOP_A in *;
           pose proof (Z.div_pos (rb SB c) 8 ltac:(lia) ltac:(lia)); lia].
  apply (bytes_at_transport bsegs W m m' _ _ SHU MU). rewrite farun_lenZ; [exact HWs|]. apply Z.div_pos; lia.
Qed.

End RegDrain.

Section CFast.
Variables (Σ : rtsA) (m : mem) (c : Z) (i : nat) (st : ckst) (lo : Z)
  (ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis HG : geo_ok Σ.
Hypothesis HA : ARTc (set_st Σ c i CkIdle) m.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hi : nth_error (r_st (pr Σ c)) i = Some st.
Hypothesis Hinit : ca_init Σ = true.
Hypothesis HRW : reg_wf c (pr Σ c).
Hypothesis Hcl : Forall (fun x => 0 <= x < Z.of_nat (length (r_st (pr Σ c)))) (ca Σ c).
Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x400 <= bv_unsigned sp.
Hypothesis HSP : bv_unsigned sp <= 2 ^ 47.
Hypothesis MI : mem_inv bsegs m.
Hypothesis Hlive : live_wf Σ.
Hypothesis Hdep : depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis HQB : Forall (fun b => exists j, nth_error (r_st (pr Σ 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 j) (ql Σ ++ qg Σ).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) c i).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation P := (pc_addr (l_T (lay Σ)) c).
#[local] Notation R := (rinfo (RIS_of (l_SB (lay Σ))) c).
#[local] Notation r := (pr Σ c).
#[local] Notation mc := (MaxCount c).
#[local] Notation nf := (Z.of_nat (length (r_fl (pr Σ c)))).
#[local] Notation cd_ms := (cd_msD Σ c i ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
#[local] Notation cd_post := (cd_postD Σ m c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc).

Lemma cf_small : forall x, In x (ca Σ c) -> 0 <= x * ClassSize c / 16 < 2 ^ 31.
Proof using Hc HRW Hcl.
  intros x Hx. clear - Hc HRW Hcl Hx. pose proof (proj1 (Forall_forall _ _) Hcl x Hx) as (X1 & X2). cbv beta in X1, X2.
  pose proof HRW as (_ & _ & W3 & _ & _ & _ & _ & _ & _ & _ & W11). pose proof (ClassSize_range c Hc) as ((CS1 & CS2) & _).
  assert (x * ClassSize c < 2 ^ 31).
  { assert (x * ClassSize c <= (Z.of_nat (length (r_st r)) - 1) * ClassSize c) by (apply Z.mul_le_mono_nonneg_r; lia). nia. }
  split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Theorem cd_fast_evt : Z.of_nat (length (ca Σ c)) = mc -> 4 * (nf + mc / 2) <= r_mfa r -> evt bsegs (cd_post (recp Σ c i)) cd_ms.
Proof using HG HA Hc Hi Hinit HRW Hcl ST HLO HLO2 HSP MI Hlive Hdep HQB.
  intros Hfull Hfast.
  pose proof (cd_geo Σ HG) as (HT & HSB & TSEP & G1 & G2 & G3 & G4). unfold SHB in G1. unfold kHighShadowEnd in G4.
  pose proof (cd_slot Σ c i st HG Hc Hi) as (P1 & P2 & P3).
  pose proof (MaxCount_range c Hc) as (MC1 & MC2). pose proof (ClassSize_range c Hc) as ((CS1 & CS2) & CS3).
  pose proof (dh_keep_eq c Hc) as (KP1 & KP2).
  assert (Hmc2 : 1 <= mc / 2 /\ mc / 2 <= 8 /\ mc - mc / 2 + mc / 2 = mc).
  { clear - MC1 MC2. split; [apply Z.div_le_lower_bound; lia|]. split; [apply Z.div_le_upper_bound; lia | lia]. }
  pose proof HRW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11). unfold kFaCap, kUMap, kUserCap in *.
  pose proof (dg_consts L m (proj1 HA)) as (IC & MMG & TC & PS & STS & UB).
  pose proof IC as (IC1 & IC2).
  apply (proj1 (rwc_app bsegs m _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC1.
  destruct IC1 as (SBC & _). cbn [cells_size csize Nat.add Z.of_nat] in SBC.
  pose proof (cd_pc Σ m c i HA Hc Hinit) as (chs & PC & CHS & Hchs & Hfch). rewrite Hfull in PC.
  destruct (fl_c8_of_stk m (cstat_alloc T) ltac:(apply (dk_stk_within m _ _ _ _ STS); unfold cstat_alloc; [lia | lia | pose proof HT as (X & _); lia]))
    as (stj & STJ).
  pose proof (cd_reg Σ m c i HA Hc) as (LK & RC & (rand & exh & pad & nal & nfr & q0 & q1 & q2 & q3 & RT) & (ws & FL & Hws & Hfw) & STU & SHU & STSH).
  apply ri_tail_norm in RT.
  pose proof (dk_rb Σ HG c Hc) as (B1 & B2 & B3 & B4).
  pose proof (dk_auser Σ HG c Hc) as AU.
  assert (HTT : T + 4096 <= SB \/ SB + 2 ^ 37 + 4096 <= T) by (destruct TSEP as (_ & _ & _ & _ & X & _); exact X).
  pose proof HT as (T1 & T2 & T3 & T4 & T5). unfold img_hull_lo, img_hull_hi in T5.
  assert (HTS : T + 4096 <= SHB \/ 2 ^ 44 + SHB <= T) by (destruct TSEP as (_ & _ & _ & _ & _ & _ & _ & X & _); unfold kHighShadowEnd, SHB in *; lia).
  unfold cd_msD.

  eapply evt_cut; [apply (cdealloc_drain_A_spec ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                             F fc m (l_ACEIL L) T c AB mc (ClassSize c) lo)|].
  1: exact Hc. 1: exact PC. 1: lia. 1: lia. 1: exact HT. 1: exact ST. 1: exact HLO. 1: clear - G3 G4 HLO; unfold kHighShadowEnd in *; lia.
  1: clear - HLO2; lia. 1: exact HSP. 1: clear - P1 P3 G3 G2 Hc; lia. 1: exact MI.
  intros ms1 (t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & junk & -> & MU1 & WM1 & MI1 & PC1 & FR1 & FR2 & ST1).
  assert (Esp1 : bv_unsigned (Z_to_bv 64 (usp - 112)) = usp - 112) by (apply unsigned_lit; lia).

  assert (DJ1 : forall a n, 0 <= n -> (a + n <= P \/ P + 4 <= a) -> (a + n <= usp - 112 \/ usp <= a) -> disjoint_from [(P, P + 4); (usp - 112, usp)] a n).
  { intros a n Hn X1 X2. cbn [disjoint_from]. first [ clear - Hn X1 X2; repeat split; lia | split; [lia|]; split; [lia | exact I] ]. }
  assert (Hsp48 : lo <= usp - 1024) by lia.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ LK MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as LK1.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ RC MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as RC1.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ RT MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as RT1.
  pose proof (u32arr_transport bsegs _ m m1 _ _ FL MU1 WM1 ltac:(apply DJ1; [lia | unfold pc_addr, fa, rb in *; lia | unfold fa, rb in *; lia])) as FL1.
  pose proof (u32arr_transport bsegs _ m m1 _ _ CHS MU1 WM1 ltac:(apply DJ1; [lia | rewrite Hchs; cbn; lia | unfold pc_addr in *; rewrite Hchs; cbn; lia])) as CHS1.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ STJ MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr, cstat_alloc in *; lia)) as STJ1.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ (proj1 IC) MU1 WM1 ltac:(apply DJ1; cbn; unfold i_spacebeg, g_instance, pc_addr in *; lia)) as IC11.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ (proj2 IC) MU1 WM1 ltac:(apply DJ1; cbn; unfold i_premapped, g_instance, pc_addr in *; lia)) as IC21.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ SBC MU1 WM1 ltac:(apply DJ1; cbn; unfold i_spacebeg, g_instance, pc_addr in *; lia)) as SBC1.
  assert (MMG1 : mm_gcells m1).
  { destruct MMG as (X1 & X2 & X3 & X4 & X5).
    split; [exact (rw_cells_transport bsegs _ m m1 _ _ X1 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia))|].
    split; [exact (rw_cells_transport bsegs _ m m1 _ _ X2 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia))|].
    split; [exact (rw_cells_transport bsegs _ m m1 _ _ X3 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia))|].
    split; [exact (rw_cells_transport bsegs _ m m1 _ _ X4 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia))|].
    exact (rw_cells_transport bsegs _ m m1 _ _ X5 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia)). }

  eapply evt_cut; [apply (rta_fast_spec (Z_to_bv 64 drainhalf_retB) (Z_to_bv 64 (usp - 112)) gp (Z_to_bv 64 tpA) t0a t1a t2a (Z_to_bv 64 P)
                             (Z_to_bv 64 (cacheT T)) a6a a7a (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 AB) s5 s6 s7 s8 s9 s10 s11
                             t3a t4a t5a t6a F fc m1 (l_ACEIL L) SB c R (usp - 104) (cstats T) (P + 16) (mc - mc / 2) (mc / 2) nf (r_mfa r)
                             (ClassSize c * Z.of_nat (length (r_st r))) (r_muser r) ws chs rand exh pad (bv_unsigned (Z_to_bv 64 nal))
                             (bv_unsigned (Z_to_bv 64 nfr)) (bv_unsigned (Z_to_bv 64 q0)) (bv_unsigned (Z_to_bv 64 q1))
                             (bv_unsigned (Z_to_bv 64 q2)) (bv_unsigned (Z_to_bv 64 q3)) lo)|].
  1: exact HSB. 1: exact Hc. 1: reflexivity. 1: lia. 1: lia. 1: lia. 1: exact Hfast. 1: exact Hws. 1: lia. 1: exact Hchs.
  1: unfold pc_addr in *; lia.
  1: pose proof (bv64_range nfr); pose proof (bv64_range q0); lia.
  1: exact (conj IC11 IC21). 1: exact MMG1. 1: exact LK1. 1: exact RC1. 1: exact RT1. 1: exact FL1. 1: exact CHS1.
  1: rewrite Esp1; exact ST1. 1: exact HLO. 1: clear - G3 G4 HLO; unfold kHighShadowEnd in *; lia. 1: rewrite Esp1; lia.
  1: rewrite Esp1; lia. 1: exact MI1.
  intros ms2 (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & -> & MU2 & WM2 & MI2
              & LK2 & RC2 & RT2 & FL2 & ST2).
  rewrite Esp1 in ST2.
  rewrite (ret_pc_even drainhalf_retB); [| unfold drainhalf_retB; lia | reflexivity].

  assert (DJ2 : forall a n, 0 <= n -> (a + n <= R \/ R + 128 <= a) -> (a + n <= fa SB c \/ fa SB c + kFaCap <= a) ->
            (a + n <= usp - 320 \/ usp - 112 <= a) -> disjoint_from (rta_tail_W (Z_to_bv 64 (usp - 112)) SB c R nf (mc / 2)) a n).
  { intros a n Hn X1 X2 X3. unfold rta_tail_W. rewrite Esp1. cbn [disjoint_from].
    assert (4 * (nf + mc / 2) <= kFaCap) by (unfold kFaCap; lia). unfold kFaCap in *.
    first [ clear - Hn X1 X2 X3; repeat split; lia | split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia | exact I] ]. }
  assert (HPT : P + 80 <= R \/ R + 128 <= P) by (unfold pc_addr, rinfo, RIS_of in *; lia).
  assert (HPF : P + 80 <= fa SB c \/ fa SB c + kFaCap <= P) by (unfold pc_addr, fa, rb, kFaCap in *; lia).
  pose proof (rw_cells_transport bsegs _ m1 m2 _ _ PC1 MU2 WM2 ltac:(apply DJ2; cbn; unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap in *; lia)) as PC2.
  pose proof (u32arr_transport bsegs _ m1 m2 _ _ CHS1 MU2 WM2 ltac:(apply DJ2; rewrite ?Hchs; cbn; unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap in *; lia)) as CHS2.
  pose proof (rw_cells_transport bsegs _ m1 m2 _ _ STJ1 MU2 WM2 ltac:(apply DJ2; cbn; unfold cstat_alloc, rinfo, RIS_of, fa, rb, kFaCap in *; lia)) as STJ2.
  pose proof (rw_cells_transport bsegs _ m1 m2 _ _ SBC1 MU2 WM2 ltac:(apply DJ2; cbn; unfold i_spacebeg, g_instance, rinfo, RIS_of, fa, rb, kFaCap in *; lia)) as SBC2.
  pose proof (rw_cells_transport bsegs _ m1 m2 _ _ FR1 MU2 WM2 ltac:(apply DJ2; cbn; unfold rinfo, RIS_of, fa, rb, kFaCap in *; lia)) as FR12.
  pose proof (rw_cells_transport bsegs _ m1 m2 _ _ FR2 MU2 WM2 ltac:(apply DJ2; cbn; unfold rinfo, RIS_of, fa, rb, kFaCap in *; lia)) as FR22.

  eapply evt_mono; [apply (cdealloc_drain_B_spec sp gp (Z_to_bv 64 tpA) t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b s5 s6 s7 s8 s9 s10 s11
                             t3b t4b t5b t6b F fc m2 s0 s1 s2 s3 s4 ra junk (l_ACEIL L) T SB c AB (mc - mc / 2) mc (ClassSize c) lo chs stj)|].
  1: exact Hc. 1: exact P1. 1: exact P2. 1: exact SBC2. 1: exact PC2. 1: lia. 1: lia. 1: lia. 1: exact CHS2. 1: exact Hchs. 1: exact STJ2.
  1: exact HT. 1: exact HSB. 1: exact FR12. 1: exact FR22. 1: exact ST2. 1: exact HLO. 1: clear - G3 G4 HLO; unfold kHighShadowEnd in *; lia.
  1: clear - HLO2; lia. 1: exact HSP. 1: exact MI2.
  intros ms3 (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & stj' & -> & MU3 & WM3 & MI3
              & PC3 & CHS3 & _ & _ & ST3).
  unfold cd_postD. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m3. split; [reflexivity|].

  assert (MU : munch (W_CD T SB c usp) m m3).
  { apply (munch_trans _ m m1 m3); [eapply munch_weaken; [|exact MU1] | apply (munch_trans _ m1 m2 m3); eapply munch_weaken; [|exact MU2| |exact MU3]].
    - unfold sub_fp, W_CD. cbn [outside]. intros x Hx. clear - Hx HLO2. repeat split; lia.
    - unfold sub_fp, W_CD, rta_tail_W. rewrite Esp1. cbn [outside]. intros x Hx.
      assert (4 * (nf + mc / 2) <= kFaCap) by (unfold kFaCap; lia). clear - Hx HLO2 H. unfold kFaCap in *. repeat split; lia.
    - unfold sub_fp, W_CD, cstat_alloc. cbn [outside]. intros x Hx. clear - Hx HLO2. repeat split; lia. }
  assert (WM : wmono bsegs m m3) by exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3)).
  assert (DJ3 : forall a n, 0 <= n -> (a + n <= P \/ P + 80 <= a) -> (a + n <= T + 2768 \/ T + 3168 <= a) ->
            (a + n <= usp - 160 \/ usp <= a) ->
            disjoint_from [(P, P + 4); (P + 16, P + 80); (cstat_alloc T, cstat_alloc T + 8); (usp - 160, usp)] a n).
  { intros a n Hn X1 X2 X3. cbn [disjoint_from]. unfold cstat_alloc.
    first [ clear - Hn X1 X2 X3; repeat split; lia | split; [lia|]; split; [lia|]; split; [lia|]; split; [lia | exact I] ]. }
  assert (HTR : T + 4096 <= R \/ R + 128 <= T) by (unfold rinfo, RIS_of in *; lia).
  assert (HTF : T + 4096 <= fa SB c \/ fa SB c + kFaCap <= T) by (unfold fa, rb, kFaCap in *; lia).
  pose proof (rw_cells_transport bsegs _ m2 m3 _ _ LK2 MU3 WM3 ltac:(apply DJ3; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as LK3.
  pose proof (rw_cells_transport bsegs _ m2 m3 _ _ RC2 MU3 WM3 ltac:(apply DJ3; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as RC3.
  pose proof (rw_cells_transport bsegs _ m2 m3 _ _ RT2 MU3 WM3 ltac:(apply DJ3; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as RT3.
  pose proof (u32arr_transport bsegs _ m2 m3 _ _ FL2 MU3 WM3 ltac:(apply DJ3; rewrite ?dest2_length, ?Hws; unfold pc_addr, fa, rb in *; lia)) as FL3.

  assert (Hk : (dh_keep c + Z.to_nat (mc / 2) = length (ca Σ c))%nat) by (rewrite KP2; lia).
  assert (Hfl : length (r_fl r ++ skipn (dh_keep c) (ca Σ c)) = (length (r_fl r) + Z.to_nat (mc / 2))%nat) by (rewrite length_app, length_skipn; lia).
  zhide.
  assert (HWs : disjoint_from (W_CD T SB c usp) (shad (rb SB c + ClassSize c * Z.of_nat (length (r_st r))))
                 ((r_muser r - ClassSize c * Z.of_nat (length (r_st r))) / 8)).
  { pose proof (shad_len (rb SB c + ClassSize c * Z.of_nat (length (r_st r))) (r_muser r - ClassSize c * Z.of_nat (length (r_st r)))
                  ltac:(unfold rb in *; lia) ltac:(lia) ltac:(unfold rb in *; lia)) as (SL1 & SL2).
    pose proof (fk_shad_le2 (rb SB c + ClassSize c * Z.of_nat (length (r_st r))) (r_muser r - ClassSize c * Z.of_nat (length (r_st r)))
                  ltac:(unfold rb in *; lia) ltac:(lia)) as SL3.
    pose proof (fk_shad_mono (rb SB c + ClassSize c * Z.of_nat (length (r_st r)) + (r_muser r - ClassSize c * Z.of_nat (length (r_st r))))
                  (rb SB c + kUserCap) ltac:(unfold kUserCap; lia)) as SL4.
    assert (Z.max 0 ((r_muser r - ClassSize c * Z.of_nat (length (r_st r))) / 8) = (r_muser r - ClassSize c * Z.of_nat (length (r_st r))) / 8)
      by (apply Z.max_r; apply Z.div_pos; lia).
    unfold W_CD. cbn [disjoint_from]. unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, kUserCap, SHB in *.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (RR : reg_rep SB c (cdeal_reg c (ureg r i CkIdle) (ca Σ c)) m3).
  { rewrite (cdeal_reg_full c _ (ca Σ c) (cd_full_true c (ca Σ c) Hfull)).
    assert (Edh : dh_mfa c (ureg r i CkIdle) = r_mfa r).
    { unfold dh_mfa, dh_grow, dh_nf, ureg. cbn [r_mfa r_fl].
      destruct (Z.ltb_spec (r_mfa r) (4 * (Z.of_nat (length (r_fl r)) + MaxCount c / 2))); [lia | reflexivity]. }
    rewrite Edh. refine (reg_rep_ureg' _ c (dh_reg c r (ca Σ c) (r_mfa r)) i CkIdle m3 _).
    apply (cd_reg_drain Σ m m3 c (W_CD T SB c usp) (r_mfa r) (dest2 ws chs nf (mc - mc / 2) (Z.to_nat (mc / 2))) HG Hc
             (cd_reg Σ m c i HA Hc) MU WM HWs (ca Σ c)).
    - exact LK3.
    - rewrite Hfl. replace (Z.of_nat (length (r_fl r) + Z.to_nat (mc / 2))) with (nf + mc / 2) by lia. exact RC3.
    - exists rand, exh, pad, (bv_unsigned (Z_to_bv 64 nal)), (bv_unsigned (Z_to_bv 64 nfr) + mc / 2), (bv_unsigned (Z_to_bv 64 q0)),
        (bv_unsigned (Z_to_bv 64 q1)), (bv_unsigned (Z_to_bv 64 q2)), (bv_unsigned (Z_to_bv 64 q3)). exact RT3.
    - exact FL3.
    - rewrite dest2_length. exact Hws.
    - rewrite Hfl. rewrite <- KP1. apply (dest2_prefix (r_fl r) (ca Σ c) ws chs c (dh_keep c) (Z.to_nat (mc / 2)) Hfw Hfch Hk).
      + apply (Nat2Z.inj_le). rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia.
      + exact cf_small. }
  assert (HP : pclass_rep T c (ca_init Σ) (cdeal_ca c i (ca Σ c)) m3).
  { rewrite Hinit. rewrite (cdeal_ca_full c i (ca Σ c) (cd_full_true c (ca Σ c) Hfull)). split.
    - rewrite length_app, firstn_length_le by lia. cbn [length]. replace (Z.of_nat (dh_keep c + 1)) with (mc - mc / 2 + 1) by lia. exact PC3.
    - exists (upd chs (Z.to_nat (mc - mc / 2)) (Z_to_bv 64 (compact_of SB c AB))). split; [exact CHS3|]. split; [rewrite upd_length; exact Hchs|].
      rewrite length_app, firstn_length_le by lia. cbn [length]. rewrite Nat.add_1_r.
      replace (Z.to_nat (mc - mc / 2)) with (dh_keep c) by (apply Nat2Z.inj; rewrite KP1, Z2Nat.id by lia; reflexivity).
      rewrite firstn_upd_snoc by lia. rewrite (cache_keep (ca Σ c) chs c (dh_keep c) Hfch ltac:(lia)), cpw_compact, map_app. reflexivity. }
  rewrite recp_set_rc, set_st_pr_same'.
  split; [exact (artc_rc Σ m m3 (W_CD T SB c usp) c i st (TZ_CD T c) lo usp HG Hc Hi (cd_TZ T c Hc) (cd_TZd T c Hc) HLO
                  (cd_cert Σ c lo sp HG Hc HLO2) HA Hdep HQB MU WM (cdeal_reg c (ureg r i CkIdle) (ca Σ c)) (cdeal_ca c i (ca Σ c))
                  ltac:(rewrite cdeal_reg_st; reflexivity) RR HP)|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST3|].
  exact (client_rc Σ m m3 (W_CD T SB c usp) c (TZ_CD T c) lo usp HG Hc (cd_TZ T c Hc) HLO ltac:(lia) (cd_cert Σ c lo sp HG Hc HLO2) Hlive MU).
Qed.

End CFast.

End GWIN.
