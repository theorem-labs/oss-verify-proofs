(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState ITree Nodes.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface R_sizeclass R_cache_defs R_prim_defs R_glue_defs R_m2s R_thread R_poison R_prim_kit R_depot_defs R_quar_defs R_cdealloc R_mmapfixed R_ensurefa R_ensurefa_B R_return R_return_T R_return_A R_return_B R_prim_lists R_prim_poison RT_freeA RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_maltail RT_freeA2 RT_freeE RT_sys_stmt RT_drain_defs RT_drain_pure RT_drain_led RT_drain_kit RT_drain_art RT_drain_art3 RT_drain_geo RT_drain_cdk RT_drain_cfast.
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
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.

Section CSlow.
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

(* [comment removed for export] *)
Lemma cs_nums : 1 <= mc / 2 <= 8 /\ mc - mc / 2 + mc / 2 = mc /\ 2 <= mc <= 16 /\ 0 <= nf < 2 ^ 27 /\ 0 <= mfa <= 2 ^ 29
  /\ mfa mod 2 ^ 18 = 0 /\ 4 * (nf + mc / 2) <= new < 4 * (nf + mc / 2) + 0x40000 /\ new mod 2 ^ 18 = 0 /\ new <= 2 ^ 29
  /\ mfa < new /\ (new - mfa) mod 4096 = 0 /\ (new - mfa) mod 8 = 0 /\ (new - mfa) mod 4 = 0 /\ 4 * Z.of_nat (length (r_fl r)) <= mfa.
Proof using Hc HRW Hgrow.
  pose proof (MaxCount_range c Hc) as (MC1 & MC2).
  pose proof HRW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11). unfold kFaCap, kUMap in *.
  assert (Hfl : Z.of_nat (length (r_fl r)) <= Z.of_nat (length (r_st r))).
  { apply nodup_len_bound; [lia | apply NoDup_ListNoDup; exact W8 |]. eapply Forall_impl; [|exact W9]. intros x (X & _). exact X. }
  assert (Hst : Z.of_nat (length (r_st r)) <= 2 ^ 26).
  { pose proof (ClassSize_range c Hc) as ((CS1 & _) & _).
    assert (32 * Z.of_nat (length (r_st r)) <= ClassSize c * Z.of_nat (length (r_st r))) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  clear W8 W9 W10.
  assert (H2 : 1 <= mc / 2 <= 8 /\ mc - mc / 2 + mc / 2 = mc).
  { clear - MC1 MC2. split; [split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia] | lia]. }
  pose proof (round_fa_ge (4 * (nf + mc / 2)) ltac:(lia)) as RG.
  assert (HN : new mod 2 ^ 18 = 0) by (unfold round_fa; change (2 ^ 18) with 0x40000; apply Z.mod_mul; lia).
  assert (Hnew : new <= 2 ^ 29).
  { unfold round_fa. apply Z.le_trans with (((2 ^ 29 + 0x3ffff) / 0x40000) * 0x40000); [|reflexivity].
    apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. lia. }
  assert (Hmod : forall x, x mod 2 ^ 18 = 0 -> x mod 4096 = 0 /\ x mod 8 = 0 /\ x mod 4 = 0).
  { intros x Hx. apply Z.mod_divide in Hx; [|lia]. destruct Hx as (q & ->).
    split; [|split]; apply Z.mod_divide; [lia | exists (q * 64); lia | lia | exists (q * 32768); lia | lia | exists (q * 65536); lia]. }
  assert (HD : (new - mfa) mod 2 ^ 18 = 0) by (rewrite Zminus_mod, HN, W6; reflexivity).
  destruct (Hmod _ HD) as (D1 & D2 & D3).
  assert (W6' : mfa mod 2 ^ 18 = 0) by exact W6.
  repeat split; lia.
Qed.

Lemma cs_eager : rt_eager (recp Σ c i) = rt_eager Σ + (new - mfa).
Proof using Hc Hfull Hgrow.
  rewrite (rt_eager_recp Σ c i Hc). rewrite recp_mfa. rewrite Z.eqb_refl. rewrite (cd_full_true c (ca Σ c) Hfull).
  unfold dh_mfa, dh_grow, dh_nf, ureg. cbn [r_mfa r_fl]. rewrite (proj2 (Z.ltb_lt _ _) Hgrow). lia.
Qed.

(* [comment removed for export] *)
Definition cs_eff : SyscallEffect :=
  mkEffect (Z_to_bv 64 (fa SB c + mfa)) [] [(Z_to_bv 64 (fa SB c + mfa), Z_to_bv 64 (new - mfa))].

(* [comment removed for export] *)
Definition cs_svc (ms : machine_state) : Prop :=
  exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (m1 : mem) (jr junk : list byte) (shj : list byte) (mm0 md0 stj : word)
         (ws chs : list word) (rand : word) (exh : byte) (pad : list byte) (nal nfr q0 q1 q2 q3 : Z),
    ms = MSsvc (mfi_regs (Z_to_bv 64 efs_retB) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp1 - 128)) - 48)) gp (Z_to_bv 64 tpA)
                         t0' t1' t2' a6' (fa SB c + mfa) (new - mfa) (Z_to_bv 64 str_freearray) (Z_to_bv 64 (mc / 2))
                         (Z_to_bv 64 (P + 16 + 4 * (mc - mc / 2))) (Z_to_bv 64 (nf + mc / 2)) (Z_to_bv 64 2305843009213693952)
                         (Z_to_bv 64 (fa SB c)) (Z_to_bv 64 1152921504607895551) (Z_to_bv 64 1152921504606846976) t3' t4' t5' t6') F
               (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m1 (seg_rom bsegs)
    /\ munch (W_CD T SB c usp) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
    /\ efs_A_cells m1 (Z_to_bv 64 (bv_unsigned sp1 - 128)) (Z_to_bv 64 rta_retE) (Z_to_bv 64 R) (Z_to_bv 64 nf)
         (Z_to_bv 64 c) (Z_to_bv 64 (usp - 104)) (Z_to_bv 64 INST) R (fa SB c + mfa) (new - mfa) new lo
    /\ rw_cells bsegs m1 (bv_unsigned sp1 - 128)
         [CB 16 jr; C8 (Z_to_bv 64 (R + 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 (Z_to_bv 64 AB); C8 (Z_to_bv 64 c);
          C8 (Z_to_bv 64 INST); C8 (Z_to_bv 64 (cacheT T)); C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 drainhalf_retB)]
    /\ ri_lock m1 R 1152921504606846976 /\ ri_core m1 R nf mfa au (r_muser r)
    /\ ri_tail m1 R rand exh pad nal nfr q0 q1 q2 q3 /\ 0 <= nfr < 2 ^ 64 /\ 0 <= q0 < 2 ^ 64
    /\ fl_arr m1 SB c ws /\ 4 * Z.of_nat (length ws) = mfa /\ firstn (length (r_fl r)) ws = map (cpw c) (r_fl r)
    /\ u32arr bsegs m1 (P + 16) chs /\ length chs = 16%nat /\ firstn (length (ca Σ c)) chs = map (cpw c) (ca Σ c)
    /\ inst_cells SB m1 /\ thread_cells TCX T m1 /\ rw_cells bsegs m1 (T + 2872) [C8 mm0; C8 md0]
    /\ rw_cells bsegs m1 (shad (fa SB c + mfa)) [CB (Z.to_nat ((new - mfa) / 8)) shj] /\ ps_cells m1
    /\ pc_cells m1 P (mc - mc / 2) mc (ClassSize c) /\ rw_cells bsegs m1 (cstat_alloc T) [C8 stj]
    /\ rw_cells bsegs m1 (usp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m1 (usp - 112) [CB 8 junk; C8 (Z_to_bv 64 INST); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 cdealloc_retD)]
    /\ rw_cells bsegs m1 i_spacebeg [C8 (Z_to_bv 64 SB)].

(* [comment removed for export] *)
Theorem cs_A : evt bsegs cs_svc cd_ms.
Proof using HG HA Hc Hi Hinit HRW Hcl ST HLO HLO2 HSP MI Hfull Hgrow.
  pose proof (cd_geo Σ HG) as (HT & HSB & TSEP & G1 & G2 & G3 & G4). unfold SHB in G1. unfold kHighShadowEnd in G4.
  pose proof (cd_slot Σ c i st HG Hc Hi) as (P1 & P2 & P3).
  pose proof cs_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14).
  pose proof (ClassSize_range c Hc) as ((CS1 & CS2) & CS3).
  pose proof HRW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & _). unfold kFaCap, kUMap, kUserCap in W1, W2, W5, W6.
  pose proof (dg_consts L m (proj1 HA)) as (IC & MMG & TC & PS & STS & UB).
  pose proof IC as (IC1 & IC2).
  apply (proj1 (rwc_app bsegs m _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC1.
  destruct IC1 as (SBC & _). cbn [cells_size csize Nat.add Z.of_nat] in SBC.
  pose proof (cd_pc Σ m c i HA Hc Hinit) as (chs & PC & CHS & Hchs & Hfch). rewrite Hfull in PC.
  pose proof HT as (T1 & T2 & T3 & T4 & T5). unfold img_hull_lo, img_hull_hi in T5.
  destruct (fl_c8_of_stk m (cstat_alloc T) ltac:(apply (dk_stk_within m _ _ _ _ STS); unfold cstat_alloc; lia)) as (stj & STJ).
  destruct (fl_two_c8 m (T + 2872) ltac:(apply (dk_stk_within m _ _ _ _ STS); lia)) as (mm0 & md0 & MM).
  pose proof (cd_reg Σ m c i HA Hc) as (LK & RC & (rand & exh & pad & nal & nfr & q0 & q1 & q2 & q3 & RT) & (ws & FL & Hws & Hfw) & STU & SHU & STSH).
  apply ri_tail_norm in RT.
  pose proof (dk_rb Σ HG c Hc) as (B1 & B2 & B3 & B4).
  pose proof (dk_auser Σ HG c Hc) as AU.
  assert (HTT : T + 4096 <= SB \/ SB + 2 ^ 37 + 4096 <= T) by (destruct TSEP as (_ & _ & _ & _ & X & _); exact X).
  assert (HTS : T + 4096 <= SHB \/ 2 ^ 44 + SHB <= T) by (destruct TSEP as (_ & _ & _ & _ & _ & _ & _ & X & _); unfold kHighShadowEnd, SHB in *; lia).
  assert (HTX : (TCX + 0xa0 <= T \/ T + 4096 <= TCX) /\ (TCX + 0xa0 <= SB \/ SB + 2 ^ 37 + 4096 <= TCX) /\ 0 < TCX /\ TCX + 0xa0 <= l_ACEIL L)
    by (destruct TSEP as (_ & X1 & X2 & _ & _ & X3 & X4 & _); repeat split; assumption).
  (* [comment removed for export] *)
  assert (HSH : SHB <= shad (fa SB c + mfa) /\ shad (fa SB c + mfa) + (new - mfa) / 8 <= shad (rb SB c + 2 ^ 32)
                /\ shad (rb SB c) <= shad (fa SB c + mfa) /\ 0 <= (new - mfa) / 8 /\ shad (rb SB c + 2 ^ 32) <= 2 ^ 44 + SHB).
  { pose proof (fk_shad_le2 (fa SB c + mfa) (new - mfa) ltac:(unfold fa, rb in *; lia) ltac:(lia)) as X1.
    pose proof (fk_shad_mono (fa SB c + mfa + (new - mfa)) (rb SB c + 2 ^ 32) ltac:(unfold fa, rb, kFaCap in *; lia)) as X2.
    pose proof (fk_shad_mono (rb SB c) (fa SB c + mfa) ltac:(unfold fa, rb in *; lia)) as X3.
    pose proof (fk_shad_mono (rb SB c + 2 ^ 32) (2 ^ 47) ltac:(unfold rb in *; lia)) as X4.
    assert (X5 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
    pose proof (Z.div_pos (fa SB c + mfa) 8 ltac:(unfold fa, rb in *; lia) ltac:(lia)).
    split; [unfold shad; lia|]. split; [lia|]. split; [lia|]. split; [apply Z.div_pos; lia | lia]. }
  destruct (stk_CB m (shad (fa SB c + mfa)) ((new - mfa) / 8) ltac:(apply (dk_stk_within m _ _ _ _ STSH); unfold SHB in *; lia) ltac:(lia)) as (shj & SHJ).
  unfold cd_msD.
  (* [comment removed for export] *)
  eapply evt_cut; [apply (cdealloc_drain_A_spec ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                             F fc m (l_ACEIL L) T c AB mc (ClassSize c) lo)|].
  1: exact Hc. 1: exact PC. 1: lia. 1: lia. 1: exact HT. 1: exact ST. 1: exact HLO. 1: clear - G3 G4 HLO; unfold kHighShadowEnd in *; lia.
  1: clear - HLO2; lia. 1: exact HSP. 1: clear - P1 P3 G3 G2 Hc; lia. 1: exact MI.
  intros ms1 (t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & junk & -> & MU1 & WM1 & MI1 & PC1 & FR1 & FR2 & ST1).
  assert (Esp1 : bv_unsigned sp1 = usp - 112) by (apply unsigned_lit; lia).
  assert (DJ1 : forall a n, 0 <= n -> (a + n <= P \/ P + 4 <= a) -> (a + n <= usp - 112 \/ usp <= a) -> disjoint_from [(P, P + 4); (usp - 112, usp)] a n).
  { intros a n Hn X1 X2. cbn [disjoint_from]. first [ clear - Hn X1 X2; repeat split; lia | split; [lia|]; split; [lia | exact I] ]. }
  pose proof (rw_cells_transport bsegs _ m m1 _ _ (proj1 IC) MU1 WM1 ltac:(apply DJ1; cbn; unfold i_spacebeg, g_instance, pc_addr in *; lia)) as IC11.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ (proj2 IC) MU1 WM1 ltac:(apply DJ1; cbn; unfold i_premapped, g_instance, pc_addr in *; lia)) as IC21.
  assert (MMG1 : mm_gcells m1).
  { destruct MMG as (X1 & X2 & X3 & X4 & X5).
    split; [exact (rw_cells_transport bsegs _ m m1 _ _ X1 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia))|].
    split; [exact (rw_cells_transport bsegs _ m m1 _ _ X2 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia))|].
    split; [exact (rw_cells_transport bsegs _ m m1 _ _ X3 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia))|].
    split; [exact (rw_cells_transport bsegs _ m m1 _ _ X4 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia))|].
    exact (rw_cells_transport bsegs _ m m1 _ _ X5 MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr in *; lia)). }
  pose proof (rw_cells_transport bsegs _ m m1 _ _ LK MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as LK1.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ RC MU1 WM1 ltac:(apply DJ1; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)) as RC1.
  (* [comment removed for export] *)
  eapply evt_mono; [apply (rta_A_spec (Z_to_bv 64 drainhalf_retB) sp1 gp (Z_to_bv 64 tpA) t0a t1a t2a (Z_to_bv 64 P) (Z_to_bv 64 (cacheT T))
                             a6a a7a (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 AB) s5 s6 s7 s8 s9 s10 s11 t3a t4a t5a t6a F fc m1
                             (l_ACEIL L) SB c R (usp - 104) (cstats T) (P + 16) (mc - mc / 2) (mc / 2) nf mfa au (r_muser r) lo)|].
  1: exact HSB. 1: exact Hc. 1: reflexivity. 1: lia. 1: lia. 1: exact Hgrow. 1: lia. 1: exact N6. 1: exact N9. 1: lia. 1: lia.
  1: exact (conj IC11 IC21). 1: exact MMG1. 1: exact LK1. 1: exact RC1.
  1: rewrite Esp1; exact ST1. 1: exact HLO. 1: clear - G3 G4 HLO; unfold kHighShadowEnd in *; lia. 1: rewrite Esp1; lia.
  1: rewrite Esp1; lia. 1: exact MI1.
  intros ms2 (t0b & t1b & t2b & a6b & t3b & t4b & t5b & t6b & m2 & jr & -> & MU2 & WM2 & MI2 & EFS & FR3 & LK2).
  rewrite Esp1 in MU2.
  (* [comment removed for export] *)
  assert (MU01 : munch [(P, P + 4); (R, R + 8); (usp - 688, usp)] m m2).
  { apply (munch_trans _ m m1 m2); eapply munch_weaken; [|exact MU1| |exact MU2].
    - unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx HLO2. repeat split; lia.
    - unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx HLO2. repeat split; lia. }
  assert (WM01 : wmono bsegs m m2) by exact (wmono_trans _ _ _ _ WM1 WM2).
  assert (DJ : forall a n, 0 <= n -> (a + n <= P \/ P + 4 <= a) -> (a + n <= R \/ R + 8 <= a) -> (a + n <= usp - 688 \/ usp <= a) ->
            disjoint_from [(P, P + 4); (R, R + 8); (usp - 688, usp)] a n).
  { intros a n Hn X1 X2 X3. cbn [disjoint_from]. first [ clear - Hn X1 X2 X3; repeat split; lia | split; [lia|]; split; [lia|]; split; [lia | exact I] ]. }
  zhide.  (* [comment removed for export] *)
  assert (HRL : lo <= usp - 688 /\ l_ACEIL L <= lo) by lia.
  unfold cs_svc.
  exists t0b, t1b, t2b, a6b, t3b, t4b, t5b, t6b, m2, jr, junk, shj, mm0, md0, stj, ws, chs, rand, exh, pad,
    (bv_unsigned (Z_to_bv 64 nal)), (bv_unsigned (Z_to_bv 64 nfr)), (bv_unsigned (Z_to_bv 64 q0)), (bv_unsigned (Z_to_bv 64 q1)),
    (bv_unsigned (Z_to_bv 64 q2)), (bv_unsigned (Z_to_bv 64 q3)).
  split; [reflexivity|].
  split; [eapply munch_weaken; [|exact MU01]; unfold sub_fp, W_CD; cbn [outside]; intros x Hx; clear - Hx HLO2; repeat split; lia|].
  split; [exact WM01|]. split; [exact MI2|]. split; [exact EFS|]. split; [exact FR3|]. split; [exact LK2|].
  split; [exact (rw_cells_transport bsegs _ m m2 _ _ RC MU01 WM01 ltac:(apply DJ; cbn; unfold pc_addr, rinfo, RIS_of in *; lia))|].
  split; [exact (rw_cells_transport bsegs _ m m2 _ _ RT MU01 WM01 ltac:(apply DJ; cbn; unfold pc_addr, rinfo, RIS_of in *; lia))|].
  split; [exact (bv64_range nfr)|]. split; [exact (bv64_range q0)|].
  split; [exact (u32arr_transport bsegs _ m m2 _ _ FL MU01 WM01 ltac:(apply DJ; [lia | unfold pc_addr, fa, rb in *; lia | unfold fa, rb, rinfo, RIS_of in *; lia | unfold fa, rb in *; lia]))|].
  split; [exact Hws|]. split; [exact Hfw|].
  split; [exact (u32arr_transport bsegs _ m m2 _ _ CHS MU01 WM01 ltac:(apply DJ; rewrite ?Hchs; cbn; unfold pc_addr, rinfo, RIS_of in *; lia))|].
  split; [exact Hchs|]. split; [exact Hfch|].
  split; [split; [exact (rw_cells_transport bsegs _ m m2 _ _ (proj1 IC) MU01 WM01 ltac:(apply DJ; cbn; unfold i_spacebeg, g_instance, pc_addr, rinfo, RIS_of in *; lia))
                 | exact (rw_cells_transport bsegs _ m m2 _ _ (proj2 IC) MU01 WM01 ltac:(apply DJ; cbn; unfold i_premapped, g_instance, pc_addr, rinfo, RIS_of in *; lia))]|].
  split.
  { destruct TC as ((X1 & X2 & X3 & X4) & X5). split; [split; [|split; [|split]]|].
    - exact (rw_cells_transport bsegs _ m m2 _ _ X1 MU01 WM01 ltac:(apply DJ; cbn; unfold g_tsd_key_inited, pc_addr, rinfo, RIS_of in *; lia)).
    - exact (rw_cells_transport bsegs _ m m2 _ _ X2 MU01 WM01 ltac:(apply DJ; cbn; unfold g_tsd_key, pc_addr, rinfo, RIS_of in *; lia)).
    - exact (rw_cells_transport bsegs _ m m2 _ _ X3 MU01 WM01 ltac:(apply DJ; cbn; unfold pth_tsd, pc_addr, rinfo, RIS_of in *; lia)).
    - exact (rw_cells_transport bsegs _ m m2 _ _ X4 MU01 WM01 ltac:(apply DJ; cbn; unfold g_pthread_tsd_main, pc_addr, rinfo, RIS_of in *; lia)).
    - exact (rw_cells_transport bsegs _ m m2 _ _ X5 MU01 WM01 ltac:(apply DJ; cbn; unfold pc_addr, rinfo, RIS_of in *; lia)). }
  split; [exact (rw_cells_transport bsegs _ m m2 _ _ MM MU01 WM01 ltac:(apply DJ; cbn; unfold pc_addr, rinfo, RIS_of in *; lia))|].
  split; [exact (rw_cells_transport bsegs _ m m2 _ _ SHJ MU01 WM01 ltac:(apply DJ; cbn; rewrite ?Z2Nat.id by lia; unfold pc_addr, rinfo, RIS_of, SHB in *; lia))|].
  split; [exact (PCP_framed m m2 _ PS MU01 WM01 ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi, pc_addr, rinfo, RIS_of, SEGTOP_A in *; lia))|].
  split; [exact (rw_cells_transport bsegs _ m1 m2 _ _ PC1 MU2 WM2 ltac:(cbn; unfold pc_addr, rinfo, RIS_of in *; lia))|].
  split; [exact (rw_cells_transport bsegs _ m m2 _ _ STJ MU01 WM01 ltac:(apply DJ; cbn; unfold cstat_alloc, pc_addr, rinfo, RIS_of in *; lia))|].
  split; [exact (rw_cells_transport bsegs _ m1 m2 _ _ FR1 MU2 WM2 ltac:(cbn; unfold rinfo, RIS_of in *; lia))|].
  split; [exact (rw_cells_transport bsegs _ m1 m2 _ _ FR2 MU2 WM2 ltac:(cbn; unfold rinfo, RIS_of in *; lia))|].
  exact (rw_cells_transport bsegs _ m m2 _ _ SBC MU01 WM01 ltac:(apply DJ; cbn; unfold i_spacebeg, g_instance, pc_addr, rinfo, RIS_of in *; lia)).
Qed.

End CSlow.
