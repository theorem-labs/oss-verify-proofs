(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState ITree Nodes.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface R_cache_defs R_prim_defs R_glue_defs R_m2s R_thread R_poison R_prim_kit R_depot_defs R_quar_defs R_cdealloc R_mmapfixed R_ensurefa R_ensurefa_B R_return R_return_T R_return_A R_return_B R_prim_lists R_prim_poison RT_freeA RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_maltail RT_freeA2 RT_freeE RT_sys_stmt RT_drain_defs RT_drain_pure RT_drain_led RT_drain_kit RT_drain_art RT_drain_art3 RT_drain_geo RT_drain_cdk RT_drain_cfast RT_drain_cslow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
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
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.

Section CSlowB.
Variables (Σ : rtsA) (m : mem) (c : Z) (i : nat) (st : ckst) (lo : Z)
  (ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis HG : geo_ok Σ.
Hypothesis HA : ARTc (set_st Σ c i CkIdle) m.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hi : nth_error (r_st (pr Σ c)) i = Some st.
Hypothesis Hinit : ca_init Σ = true.
Hypothesis HRW : reg_wf c (pr Σ c).
Hypothesis Hcl : Forall (fun x => 0 <= x < Z.of_nat (length (r_st (pr Σ c)))) (ca Σ c).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x400 <= bv_unsigned sp.
Hypothesis HSP : bv_unsigned sp <= 2 ^ 47.
Hypothesis MI : mem_inv asegs m.
Hypothesis Hlive : live_wf Σ.
Hypothesis Hdep : depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis HQB : Forall (fun b => exists j, nth_error (r_st (pr Σ 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 j) (ql Σ ++ qg Σ).
Hypothesis Hfull : Z.of_nat (length (ca Σ c)) = MaxCount c.
Hypothesis Hgrow : r_mfa (pr Σ c) < 4 * (Z.of_nat (length (r_fl (pr Σ c))) + MaxCount c / 2).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation TCX := (l_TCX (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) c i).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation P := (pc_addr (l_T (lay Σ)) c).
#[local] Notation R := (rinfo (RIS_of (l_SB (lay Σ))) c).
#[local] Notation r := (pr Σ c).
#[local] Notation mc := (MaxCount c).
#[local] Notation nf := (Z.of_nat (length (r_fl (pr Σ c)))).
#[local] Notation mfa := (r_mfa (pr Σ c)).
#[local] Notation au := (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
#[local] Notation new := (round_fa (4 * (Z.of_nat (length (r_fl (pr Σ c))) + MaxCount c / 2))).
#[local] Notation sp1 := (Z_to_bv 64 (bv_unsigned sp - 112)).
#[local] Notation cd_ms := (cd_msD Σ c i ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
#[local] Notation cd_post := (cd_postD Σ m c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc).

#[local] Notation svc := (cs_svc Σ m c i lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc).
#[local] Notation eff := (cs_eff Σ c).

(* [comment removed for export] *)
Theorem cs_B : forall ms, svc ms -> evt asegs (cd_post (recp Σ c i)) (nretA ms eff).
Proof using HG HA Hc Hi Hinit HRW Hcl ST HLO HLO2 HSP MI Hlive Hdep HQB Hfull Hgrow.
  intros ms (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & m1 & jr & junk & shj & mm0 & md0 & stj & ws & chs & rand & exh & pad
             & nal & nfr & q0 & q1 & q2 & q3 & -> & MU1 & WM1 & MI1 & EFS & FR3 & LK1 & RC1 & RT1 & Hnfr & Hq0 & FL1 & Hws & Hfw
             & CHS1 & Hchs & Hfch & IC1 & TC1 & MM1 & SHJ1 & PS1 & PC1 & STJ1 & FR11 & FR21 & SBC1).
  pose proof (cd_geo Σ HG) as (HT & HSB & TSEP & G1 & G2 & G3 & G4). unfold SHB in G1. unfold kHighShadowEnd in G4.
  pose proof (cd_slot Σ c i st HG Hc Hi) as (P1 & P2 & P3).
  pose proof (cs_nums Σ c Hc HRW Hgrow) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14).
  pose proof (ClassSize_range c Hc) as ((CS1 & CS2) & CS3).
  pose proof HRW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & _). unfold kFaCap, kUMap, kUserCap in W1, W2, W5, W6.
  pose proof HT as (T1 & T2 & T3 & T4 & T5). unfold img_hull_lo, img_hull_hi in T5.
  pose proof (dk_rb Σ HG c Hc) as (B1 & B2 & B3 & B4).
  pose proof (dk_auser Σ HG c Hc) as AU.
  pose proof (dh_keep_eq c Hc) as (KP1 & KP2).
  assert (HTS : T + 4096 <= SHB \/ 2 ^ 44 + SHB <= T) by (destruct TSEP as (_ & _ & _ & _ & _ & _ & _ & X & _); unfold kHighShadowEnd, SHB in *; lia).
  assert (HTT : T + 4096 <= SB \/ SB + 2 ^ 37 + 4096 <= T) by (destruct TSEP as (_ & _ & _ & _ & X & _); exact X).
  assert (HSH : SHB <= shad (fa SB c + mfa) /\ shad (fa SB c + mfa) + (new - mfa) / 8 <= shad (rb SB c + 2 ^ 32)
                /\ shad (rb SB c + kUserCap) <= shad (fa SB c + mfa) /\ 0 <= (new - mfa) / 8 /\ shad (rb SB c + 2 ^ 32) <= 2 ^ 44 + SHB).
  { pose proof (fk_shad_le2 (fa SB c + mfa) (new - mfa) ltac:(unfold fa, rb in *; lia) ltac:(lia)) as X1.
    pose proof (fk_shad_mono (fa SB c + mfa + (new - mfa)) (rb SB c + 2 ^ 32) ltac:(unfold fa, rb, kFaCap in *; lia)) as X2.
    pose proof (fk_shad_mono (rb SB c + kUserCap) (fa SB c + mfa) ltac:(unfold fa, rb, kUserCap in *; lia)) as X3.
    pose proof (fk_shad_mono (rb SB c + 2 ^ 32) (2 ^ 47) ltac:(unfold rb in *; lia)) as X4.
    assert (X5 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
    pose proof (Z.div_pos (fa SB c + mfa) 8 ltac:(unfold fa, rb in *; lia) ltac:(lia)).
    split; [unfold shad; lia|]. split; [lia|]. split; [lia|]. split; [apply Z.div_pos; lia|]. lia. }
  assert (Esp1 : bv_unsigned sp1 = usp - 112) by (apply unsigned_lit; lia).
  unfold nretA, cs_eff.
  (* [comment removed for export] *)
  eapply evt_cut; [apply (rta_B_spec PCP PCP_stmt PCP_framed (Z_to_bv 64 drainhalf_retB) sp1 gp t0' t1' t2' a6' (Z_to_bv 64 P)
                             (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 AB) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'
                             F fc m1 (l_ACEIL L) SB c R (usp - 104) (P + 16) (mc - mc / 2) (mc / 2) nf mfa new au (r_muser r)
                             (shad (fa SB c + mfa)) ((new - mfa) / 8) T TCX mm0 md0 shj ws chs rand exh pad nal nfr q0 q1 q2 q3 lo jr)|].
  1: exact HSB. 1: exact Hc. 1: reflexivity. 1: lia. 1: lia. 1: lia. 1: lia. 1: exact N6. 1: exact Hws. 1: exact Hgrow. 1: reflexivity.
  1: exact N9. 1: reflexivity. 1: reflexivity. 1: exact TSEP. 1: unfold pc_addr; lia. 1: exact Hchs. 1: lia.
  1: exact EFS. 1: exact FR3. 1: exact LK1. 1: exact RC1. 1: exact RT1. 1: exact FL1. 1: exact CHS1. 1: exact IC1. 1: exact TC1.
  1: exact MM1. 1: exact SHJ1. 1: exact PS1. 1: exact HLO. 1: clear - G3 G4 HLO; unfold kHighShadowEnd in *; lia.
  1: rewrite Esp1; lia. 1: rewrite Esp1; lia. 1: exact MI1.
  intros ms2 (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & -> & MU2 & WM2 & MI2
              & LK2 & RC2 & RT2 & FL2 & _ & _ & _ & _ & _ & ST2).
  rewrite Esp1 in ST2.
  rewrite (ret_pc_even drainhalf_retB); [| unfold drainhalf_retB; lia | reflexivity].
  (* [comment removed for export] *)
  assert (DJ2 : forall a n, 0 <= n -> (a + n <= R \/ R + 128 <= a) -> (a + n <= fa SB c \/ fa SB c + kFaCap <= a) ->
            (a + n <= shad (fa SB c + mfa) \/ shad (fa SB c + mfa) + (new - mfa) / 8 <= a) -> (a + n <= T + 2872 \/ T + 2888 <= a) ->
            (a + n <= usp - 688 \/ usp - 112 <= a) ->
            disjoint_from (rta_B_W sp1 SB c R new (shad (fa SB c + mfa)) ((new - mfa) / 8) T) a n).
  { intros a n Hn X1 X2 X3 X4 X5. unfold rta_B_W. rewrite Esp1. cbn [disjoint_from]. unfold kFaCap in *.
    first [ clear - Hn X1 X2 X3 X4 X5 N9; repeat split; lia | split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia | exact I] ]. }
  pose proof (rw_cells_transport asegs _ m1 m2 _ _ PC1 MU2 WM2 ltac:(apply DJ2; cbn; unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, SHB in *; lia)) as PC2.
  pose proof (u32arr_transport asegs _ m1 m2 _ _ CHS1 MU2 WM2 ltac:(apply DJ2; rewrite ?Hchs; cbn; unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, SHB in *; lia)) as CHS2.
  pose proof (rw_cells_transport asegs _ m1 m2 _ _ STJ1 MU2 WM2 ltac:(apply DJ2; cbn; unfold cstat_alloc, rinfo, RIS_of, fa, rb, kFaCap, SHB in *; lia)) as STJ2.
  pose proof (rw_cells_transport asegs _ m1 m2 _ _ SBC1 MU2 WM2 ltac:(apply DJ2; cbn; unfold i_spacebeg, g_instance, rinfo, RIS_of, fa, rb, kFaCap, SHB in *; lia)) as SBC2.
  pose proof (rw_cells_transport asegs _ m1 m2 _ _ FR11 MU2 WM2 ltac:(apply DJ2; cbn; unfold rinfo, RIS_of, fa, rb, kFaCap, SHB in *; lia)) as FR12.
  pose proof (rw_cells_transport asegs _ m1 m2 _ _ FR21 MU2 WM2 ltac:(apply DJ2; cbn; unfold rinfo, RIS_of, fa, rb, kFaCap, SHB in *; lia)) as FR22.
  (* [comment removed for export] *)
  eapply evt_mono; [apply (cdealloc_drain_B_spec sp gp (Z_to_bv 64 tpA) t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b s5 s6 s7 s8 s9 s10 s11
                             t3b t4b t5b t6b F fc m2 s0 s1 s2 s3 s4 ra junk (l_ACEIL L) T SB c AB (mc - mc / 2) mc (ClassSize c) lo chs stj)|].
  1: exact Hc. 1: exact P1. 1: exact P2. 1: exact SBC2. 1: exact PC2. 1: lia. 1: lia. 1: lia. 1: exact CHS2. 1: exact Hchs. 1: exact STJ2.
  1: exact HT. 1: exact HSB. 1: exact FR12. 1: exact FR22. 1: exact ST2. 1: exact HLO. 1: clear - G3 G4 HLO; unfold kHighShadowEnd in *; lia.
  1: clear - HLO2; lia. 1: exact HSP. 1: exact MI2.
  intros ms3 (t0c & t1c & t2c & a0c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m3 & stj' & -> & MU3 & WM3 & MI3
              & PC3 & CHS3 & _ & _ & ST3).
  unfold cd_postD. exists t0c, t1c, t2c, a0c, a1c, a2c, a3c, a4c, a5c, a6c, a7c, t3c, t4c, t5c, t6c, m3. split; [reflexivity|].
  (* [comment removed for export] *)
  assert (MU : munch (W_CD T SB c usp) m m3).
  { apply (munch_trans _ m m1 m3); [exact MU1 | apply (munch_trans _ m1 m2 m3); eapply munch_weaken; [|exact MU2| |exact MU3]].
    - unfold sub_fp, W_CD, rta_B_W. rewrite Esp1. cbn [outside]. intros x Hx.
      assert (new <= kFaCap) by (unfold kFaCap; lia). clear - Hx HLO2 HSH H. unfold kFaCap in *. repeat split; lia.
    - unfold sub_fp, W_CD, cstat_alloc. cbn [outside]. intros x Hx. clear - Hx HLO2. repeat split; lia. }
  assert (WM : wmono asegs m m3) by exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3)).
  assert (DJ3 : forall a n, 0 <= n -> (a + n <= P \/ P + 80 <= a) -> (a + n <= T + 2768 \/ T + 3168 <= a) ->
            (a + n <= usp - 160 \/ usp <= a) ->
            disjoint_from [(P, P + 4); (P + 16, P + 80); (cstat_alloc T, cstat_alloc T + 8); (usp - 160, usp)] a n).
  { intros a n Hn X1 X2 X3. cbn [disjoint_from]. unfold cstat_alloc.
    first [ clear - Hn X1 X2 X3; repeat split; lia | split; [lia|]; split; [lia|]; split; [lia|]; split; [lia | exact I] ]. }
  assert (HTR : T + 4096 <= R \/ R + 128 <= T) by (unfold rinfo, RIS_of in *; lia).
  assert (HTF : T + 4096 <= fa SB c \/ fa SB c + kFaCap <= T) by (unfold fa, rb, kFaCap in *; lia).
  pose proof (rw_cells_transport asegs _ m2 m3 _ _ LK2 MU3 WM3 ltac:(apply DJ3; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as LK3.
  pose proof (rw_cells_transport asegs _ m2 m3 _ _ RC2 MU3 WM3 ltac:(apply DJ3; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as RC3.
  pose proof (rw_cells_transport asegs _ m2 m3 _ _ RT2 MU3 WM3 ltac:(apply DJ3; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as RT3.
  assert (Hz : (4 * Z.of_nat (length (ws ++ repeat (Z_to_bv 64 0) (Z.to_nat ((new - mfa) / 4)))) = new)%Z).
  { rewrite length_app, repeat_length. pose proof (Z.div_mod (new - mfa) 4 ltac:(lia)) as X. rewrite N13 in X.
    assert (0 <= (new - mfa) / 4) by (apply Z.div_pos; lia). lia. }
  pose proof (u32arr_transport asegs _ m2 m3 _ _ FL2 MU3 WM3 ltac:(apply DJ3; rewrite ?dest2_length, ?Hz; unfold pc_addr, fa, rb in *; lia)) as FL3.
  (* [comment removed for export] *)
  assert (Hk : (dh_keep c + Z.to_nat (mc / 2) = length (ca Σ c))%nat) by (rewrite KP2; lia).
  assert (Hfl : length (r_fl r ++ skipn (dh_keep c) (ca Σ c)) = (length (r_fl r) + Z.to_nat (mc / 2))%nat) by (rewrite length_app, length_skipn; lia).
  zhide.  (* [comment removed for export] *)
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
    assert (Edh : dh_mfa c (ureg r i CkIdle) = new).
    { unfold dh_mfa, dh_grow, dh_nf, ureg. cbn [r_mfa r_fl]. rewrite (proj2 (Z.ltb_lt _ _) Hgrow). reflexivity. }
    rewrite Edh. refine (reg_rep_ureg' _ c (dh_reg c r (ca Σ c) new) i CkIdle m3 _).
    apply (cd_reg_drain Σ m m3 c (W_CD T SB c usp) new
             (dest2 (ws ++ repeat (Z_to_bv 64 0) (Z.to_nat ((new - mfa) / 4))) chs nf (mc - mc / 2) (Z.to_nat (mc / 2)))
             HG Hc (cd_reg Σ m c i HA Hc) MU WM HWs (ca Σ c)).
    - exact LK3.
    - rewrite Hfl. replace (Z.of_nat (length (r_fl r) + Z.to_nat (mc / 2))) with (nf + mc / 2) by lia. exact RC3.
    - exists rand, exh, pad, nal, (nfr + mc / 2), q0, q1, q2, q3. exact RT3.
    - exact FL3.
    - rewrite dest2_length. exact Hz.
    - rewrite Hfl. rewrite <- KP1. apply (dest2_prefix (r_fl r) (ca Σ c) _ chs c (dh_keep c) (Z.to_nat (mc / 2))).
      + rewrite firstn_app. replace (length (r_fl r) - length ws)%nat with 0%nat by (apply Nat2Z.inj; lia). rewrite firstn_O, app_nil_r. exact Hfw.
      + exact Hfch.
      + exact Hk.
      + apply (Nat2Z.inj_le). rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia.
      + exact (cf_small Σ c Hc HRW Hcl). }
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

End CSlowB.
