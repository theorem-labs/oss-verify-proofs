(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ PEnv F_poison F_mm_D F_prim_L0 APrimSpec APrimLem AFrame F_prim_efa APrimPop.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma m_divu_lit : forall x y, 0 <= x < 2^64 -> 0 < y < 2^64 ->
  mul_div M_DIVU (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x / y).
Proof.
  intros x y Hx Hy. unfold mul_div. rewrite Z_to_bv_unsigned. rewrite bv_wrap_small by (change (bv_modulus 64) with (2^64); lia).
  replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_divu_unsigned, !Z_to_bv_unsigned. change (bv_modulus 64) with (2^64).
  rewrite !bv_wrap_small; [reflexivity| ..]; change (bv_modulus 64) with (2^64); try lia.
  all: split; [apply Z.div_pos; lia|]; apply Z.div_lt_upper_bound; [lia|]; nia.
Qed.

Lemma lxor_ones64 : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx.
  assert (E : 18446744073709551615 - x = (Z.lnot x) mod 2^64).
  { unfold Z.lnot. replace (Z.pred (- x)) with ((18446744073709551615 - x) + (-1) * 2^64) by lia.
    rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
  rewrite E. apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec.
  destruct (Z.lt_ge_cases i 64) as [LT|GE].
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia.
    replace 18446744073709551615 with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_low by lia. apply Bool.xorb_true_r.
  - rewrite Z.mod_pow2_bits_high by lia.
    assert (B1 : Z.testbit x i = false). { destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia| lia]. }
    assert (B2 : Z.testbit 18446744073709551615 i = false). { apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [| lia]. apply Z.log2_lt_pow2; lia. }
    rewrite B1, B2. reflexivity.
Qed.

Lemma msz_code : forall t mu, 0 <= mu < t -> t < 2^62 ->
  Z.land ((t + Z.lxor mu 18446744073709551615) mod 18446744073709551616) 18446744073709289472 + 262144 = rup (t - mu) 262144.
Proof.
  intros t mu H1 H2. rewrite lxor_ones64 by lia.
  replace (t + (18446744073709551615 - mu)) with ((t - mu - 1) + 1 * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full, Z.mod_small by lia.
  rewrite land_alignK by lia. unfold rup. Z.div_mod_to_equations. nia.
Qed.

Definition csz_mid (c : Z) : Z :=
  Z.land ((bv_signed (Z_to_bv 64 (Z.shiftl c 63)) ≫ 63) mod 18446744073709551616)
         (((512 ≪ (((c + -16) ≫ 1) mod 64)) mod 18446744073709551616) ≫ 1)
  + 512 ≪ (((c + -16) ≫ 1) mod 64).
Lemma csz_mid_ok : forall c, 17 <= c <= 30 -> csz_mid c = class_size c.
Proof.
  intros c Hc. pose proof (range_check (fun c => csz_mid c =? class_size c) 17 14 ltac:(vm_compute; reflexivity) c ltac:(lia)) as H.
  cbn beta in H. apply Z.eqb_eq in H. exact H.
Qed.

Section POPA.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Hypothesis AO : alayout_ok AL.
  Notation THR := (at_thr (al_thread AL)).
  Notation STAT := (at_thr (al_thread AL) + CSTATS_OFF).

  Variables (ra gp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo c r : Z) (k : pclass) (mtx : Z) (m0 : mem).
  Notation RI := (ri_addr AL c).
  Notation FA := (fa_base AL c).
  Notation SZ := (class_size c).

  Definition popA_post (t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    : machine_state -> Prop :=
    fun ms' => exists a5 a6 m',
      ms' = MS (mkR ra (wz (q - 64)) gp (wz A0_TP) t0 t1 t2 (wz RI) (wz STAT) (wz INSTANCE) (wz (c * 4294967296)) (wz c) (wz (p_au k)) (wz r) a5 a6 a7
                    (wz (al_space AL + c * 4294967296)) (wz (p_au k + SZ * r)) (wz (p_mu k)) (wz SZ) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (wz (if p_mu k <? p_au k + SZ * r then 0x388d8 else 0x389ac)) fc None m' (seg_rom asegs)
      /\ munch [(q - 64, q)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (q - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ stk asegs m' lo (q - 64).

  Ltac popA_done ria :=
    apply evt_done; unfold popA_post; subst ria; eexists _, _, _;
    split; [ first [ replace (p_mu k <? p_au k + class_size c * r) with true by (symmetry; apply Z.ltb_lt; lia)
                   | replace (p_mu k <? p_au k + class_size c * r) with false by (symmetry; apply Z.ltb_ge; lia) ]; reflexivity
           | split; [ eassumption | split; [ eassumption | split; [ assumption | split; [ eassumption | eassumption ]]]]].
  Ltac popA_tail ria := do 5 zstep; zstep; let KT := fresh "KT" in if_cases KT; zify_cond KT; first [ popA_done ria | zstep; popA_done ria | match goal with |- ?G => idtac "POPFAIL" G end ].

  #[using="AO"] Lemma pop_A : forall (t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) j8 j64 j88 j96 j104 j112 jpad,
    mem_inv asegs m0 -> prim_env AL m0 ->
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q - 64 -> q <= 2^47 ->
    1 <= c <= 31 -> 1 <= r <= 8 -> 0 <= p_au k -> p_au k + SZ * r <= FA_OFF -> 0 <= p_mu k <= FA_OFF ->
    rw_cells asegs m0 RI (ri_cells mtx k j8 j64 j88 j96 j104 j112 jpad) ->
    evt asegs (popA_post t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz INSTANCE) (wz STAT) (wz c) (wz RI) (wz r) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz populate_entry) fc None m0 (seg_rom asegs)).
  Proof.
    intros until jpad. intros MI PRE ST CLO LO QH Hc Hr AU0 TOT MU0 RIC.
    unfold populate_entry. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _ & _ & SP5 & _ & _).
    pose proof (region_range AL c Hc) as RR. pose proof (class_size_pos c Hc) as CS.
    assert (Hreg : region AL c = al_space AL + c * K_REGION) by reflexivity.
    unfold ri_cells in RIC. unfold ri_addr, RIB in *. unfold prim_env in PRE.
    pose proof (munch_refl [(q - 64, q)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    set (ria := al_space AL + K_SPACE + 128 * c) in *. assert (Hria : ria = al_space AL + K_SPACE + 128 * c) by reflexivity. clearbody ria.
    assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- Eq in ST. carve_frame 64%nat ST. rewrite !Eq in *. clear Eq.
    do 9 sstep.
    do 3 zstep.
    zstep. zstep.
    replace (Z.shiftl c 32) with (c * 4294967296) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    zstep. if_cases K31; zify_cond K31.
    -
      zstep.   replace 64 with SZ at 1 by (rewrite K31; reflexivity).
      popA_tail ria.
    - zstep. zstep. if_cases K16; zify_cond K16.
      +   do 9 zstep.
        match goal with |- context [Z_to_bv 64 (Z.land ?a ?b + ?t)] =>
          replace (Z.land a b + t) with SZ by (rewrite <- (csz_mid_ok c) by lia; reflexivity) end.
        popA_tail ria.
      +
        zstep.   replace (Z.shiftl c 5) with SZ by (unfold class_size; replace (c =? 31) with false by (symmetry; apply Z.eqb_neq; lia);
          replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia); rewrite Z.shiftl_mul_pow2 by lia; lia).
        popA_tail ria.
  Qed.
End POPA.

Section POPB.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Hypothesis AO : alayout_ok AL.
  Notation THR := (at_thr (al_thread AL)).
  Notation STAT := (at_thr (al_thread AL) + CSTATS_OFF).
  Variables (gp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo c r : Z) (k : pclass) (mtx : Z) (m0 : mem) (H : word -> bool).
  Notation RI := (ri_addr AL c).
  Notation FA := (fa_base AL c).
  Notation SZ := (class_size c).
  Notation REG := (al_space AL + c * 4294967296).

  Definition popB0_post (ra t0 t1 t2 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) : machine_state -> Prop :=
    fun ms' => exists a1,
      ms' = MS (mkR ra (wz (q - 64)) gp (wz A0_TP) t0 t1 t2 (wz RI) (wz STAT) (wz INSTANCE) a1 (wz c) (wz (p_au k)) (wz r) a5 a6 a7
                    (wz REG) (wz (p_au k + SZ * r)) (wz (p_mu k)) (wz SZ) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (wz 0x388dc) fc None m0 (seg_rom asegs)
      /\ munch [] m0 m0 /\ wmono asegs m0 m0 /\ mem_inv asegs m0.

  #[using="Type"] Lemma pop_B0 : forall (ra t0 t1 t2 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    mem_inv asegs m0 -> prim_env AL m0 -> 0 <= p_mu k <= FA_OFF ->
    evt asegs (popB0_post ra t0 t1 t2 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      (MS (mkR ra (wz (q - 64)) gp (wz A0_TP) t0 t1 t2 (wz RI) (wz STAT) (wz INSTANCE) (wz (c * 4294967296)) (wz c) (wz (p_au k)) (wz r) a5 a6 a7
               (wz REG) (wz (p_au k + SZ * r)) (wz (p_mu k)) (wz SZ) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x388d8) fc None m0 (seg_rom asegs)).
  Proof.
    intros. rename H0 into MI. rename H1 into PRE. rename H2 into MUB. unfold prim_env in PRE.
    pose proof (munch_refl [] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    zstep. if_cases K0; zify_cond K0.
    -
      zstep.
      replace (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity).
      zstep. if_cases KN; zify_cond KN; [| exfalso; revert KN; clear; intros KN; cbn in KN; lia].
      zstep. zstep.
      apply evt_done. unfold popB0_post. eexists. split; [| split; [exact MU| split; [exact WM| exact MI]]].
      rewrite K0. reflexivity.
    - apply evt_done. unfold popB0_post. eexists. split; [reflexivity| split; [exact MU| split; [exact WM| exact MI]]].
  Qed.

  Definition popB_W (beg msz : Z) : list (Z * Z) :=
    [(lo, q - 64); (RI + 48, RI + 56); (beg, beg + msz); (sh beg, sh beg + msz / 8); (swlo beg, swhi beg msz);
     (STAT + 24, STAT + 32); (THR + TSTATS_OFF, THR + TSTATS_OFF + 368)].

  Definition popB_WG (beg msz : Z) : list (Z * Z) :=
    [(lo, q - 64); (RI + 48, RI + 56); (beg, beg + msz); (sh beg, sh beg + msz / 8);
     (STAT + 24, STAT + 32); (THR + TSTATS_OFF, THR + TSTATS_OFF + 368)].

  Definition popB_post (s7 s8 s9 s10 s11 : word) (j8 j64 j88 j96 j104 j112 : word) (jpad jt : list byte) (calloc cmapped msz : Z)
    : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists x1 t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR x1 (wz (q - 64)) gp (wz A0_TP) t0 t1 t2 (wz RI) (wz (THR + 2792)) (wz INSTANCE) a1 a2 (wz (p_au k)) a4 a5 a6 a7
                    (wz REG) (wz msz) (wz (p_mu k + msz)) (wz SZ) (wz INSTANCE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (wz 0x389ac) fc None m' (seg_rom asegs)
      /\ H' = H_commit (REG + p_mu k) msz H
      /\ munch [(lo, q - 64); (RI + 48, RI + 56); (REG + p_mu k, REG + p_mu k + msz); (sh (REG + p_mu k), sh (REG + p_mu k) + msz / 8);
                (swlo (REG + p_mu k), swhi (REG + p_mu k) msz); (STAT + 24, STAT + 32); (THR + TSTATS_OFF, THR + TSTATS_OFF + 368)] m0 m'
      /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (q - 64) /\ poison_env E m' /\ thread_env (al_thread AL) m' /\ prim_env AL m' /\ shvis H' m'
      /\ rw_cells asegs m' RI (ri_cells mtx (mkPCL (p_nf k) (p_mfa k) (p_au k) (p_mu k + msz) (p_nalloc k) (p_nfreed k) (p_fa k) (p_cnt k) (p_chunks k))
                                      j8 j64 j88 j96 j104 j112 jpad)
      /\ rw_cells asegs m' (STAT + 16) [C8 (wz calloc); C8 (wz (cmapped + msz))]
      /\ (exists ts, rw_cells asegs m' (THR + TSTATS_OFF) [CB 368 ts])
      /\ rw_cells asegs m' (REG + p_au k) [CB (Z.to_nat (p_mu k + msz - p_au k)) (jt ++ repeat (Z_to_bv 8 0) (Z.to_nat msz))]
      /\ rw_cells asegs m' (sh (REG + p_au k)) [CB (Z.to_nat ((p_mu k + msz - p_au k) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((p_mu k + msz - p_au k) / 8)))]
      /\ gmunch [(lo, q - 64); (RI + 48, RI + 56); (REG + p_mu k, REG + p_mu k + msz); (sh (REG + p_mu k), sh (REG + p_mu k) + msz / 8);
                 (STAT + 24, STAT + 32); (THR + TSTATS_OFF, THR + TSTATS_OFF + 368)] m0 m'.

  #[using="AO"] Lemma pop_B : forall (ra t0 t1 t2 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) j8 j64 j88 j96 j104 j112 jpad jt (calloc cmapped msz : Z) ts,
    mem_inv asegs m0 -> mclean H m0 -> shvis H m0 -> poison_env E m0 -> thread_env (al_thread AL) m0 -> prim_env AL m0 ->
    stk asegs m0 lo (q - 64) -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - 64 - 400 -> q <= 2^47 -> q mod 16 = 0 ->
    1 <= c <= 31 -> 1 <= r <= 8 ->
    0 <= p_au k <= p_mu k -> p_au k mod 16 = 0 -> p_mu k mod K_MAP = 0 -> p_mu k < p_au k + SZ * r -> p_mu k + SZ * r + K_MAP <= FA_OFF ->
    msz = rup (p_au k + SZ * r - p_mu k) K_MAP ->
    0 <= calloc -> 0 <= cmapped -> cmapped + K_REGION < 2^63 ->
    rw_cells asegs m0 RI (ri_cells mtx k j8 j64 j88 j96 j104 j112 jpad) ->
    rw_cells asegs m0 (STAT + 16) [C8 (wz calloc); C8 (wz cmapped)] ->
    rw_cells asegs m0 (THR + TSTATS_OFF) [CB 368 ts] ->
    rw_cells asegs m0 (REG + p_au k) [CB (Z.to_nat (p_mu k - p_au k)) jt] ->
    rw_cells asegs m0 (sh (REG + p_au k)) [CB (Z.to_nat ((p_mu k - p_au k) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((p_mu k - p_au k) / 8)))] ->
    implA H (t_commit (REG + p_mu k) msz) (popB_post s7 s8 s9 s10 s11 j8 j64 j88 j96 j104 j112 jpad jt calloc cmapped msz)
      (MS (mkR ra (wz (q - 64)) gp (wz A0_TP) t0 t1 t2 (wz RI) (wz STAT) (wz INSTANCE) (wz (c * 4294967296)) (wz c) (wz (p_au k)) (wz r) a5 a6 a7
               (wz REG) (wz (p_au k + SZ * r)) (wz (p_mu k)) (wz SZ) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x388d8) fc None m0 (seg_rom asegs)).
  Proof.
    intros until ts. intros MI MC SV PE TE PRE ST LOH CLO LO QH AL16 Hc Hr AU AU16 MUK LT BUD Hmsz CA0 CM0 CMB RIC STC TS TL TSH.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    layout_facts AO 0%nat SPF. layout_facts AO 3%nat THF.
    destruct SPF as (SP1 & SP2 & SP3 & _ & SP5 & _ & _). destruct THF as (TH1 & TH2 & TH3 & _ & TH5 & _ & _).
    pose proof AO as AO'. destruct AO' as (_ & _ & SPAL & TLO & _ & _).
    pose proof (region_range AL c Hc) as RR. pose proof (class_size_pos c Hc) as CS. pose proof (class_size_mod16 c Hc) as CS16.
    assert (Hreg : region AL c = REG) by reflexivity.
    layout_apart_fact AO 0%nat 3%nat AP03.
    unfold ri_cells in RIC. unfold ri_addr, RIB in *. unfold prim_env in PRE.
    replace (at_thr (al_thread AL) + CSTATS_OFF + 16) with (at_thr (al_thread AL) + 2784) in STC by lia.
    demod SP3. demod SPAL. demod AL16. demod TH3. demod CS16. demod AU16. demod MUK.
    pose proof (rup_ge (p_au k + SZ * r - p_mu k) K_MAP ltac:(lia)) as RG. pose proof (rup_lt (p_au k + SZ * r - p_mu k) K_MAP ltac:(lia)) as RLT.
    pose proof (rup_mod (p_au k + SZ * r - p_mu k) K_MAP ltac:(lia)) as RM. rewrite <- Hmsz in RG, RLT, RM. demod RM.
    set (beg := REG + p_mu k). assert (Hbeg : beg = REG + p_mu k) by reflexivity. clearbody beg.
    assert (B8a : beg mod 4096 = 0) by lia. demod B8a. assert (B8b : msz mod 4096 = 0) by lia. demod B8b.
    assert (SHE : sh (beg + msz) = sh beg + msz / 8) by (unfold sh; Z.div_mod_to_equations; nia).
    assert (SHA : sh beg = sh (REG + p_au k) + (p_mu k - p_au k) / 8) by (rewrite Hbeg; unfold sh; Z.div_mod_to_equations; nia).
    pose proof (sw_bounds beg msz ltac:(lia) ltac:(lia)) as SWB. pose proof (sw_range beg msz ltac:(lia) ltac:(lia) ltac:(lia)) as SWR.
    destruct SWB as (SW1 & SW2 & _ & _ & SW5 & _).
    set (W2 := [(lo, q - 64); (al_space AL + K_SPACE + 128 * c + 48, al_space AL + K_SPACE + 128 * c + 56); (beg, beg + msz); (sh beg, sh beg + msz / 8); (swlo beg, swhi beg msz);
                (at_thr (al_thread AL) + 2792, at_thr (al_thread AL) + 2800); (at_thr (al_thread AL) + 2800, at_thr (al_thread AL) + 3168)]).
    set (WG := [(lo, q - 64); (al_space AL + K_SPACE + 128 * c + 48, al_space AL + K_SPACE + 128 * c + 56); (beg, beg + msz); (sh beg, sh beg + msz / 8);
                (at_thr (al_thread AL) + 2792, at_thr (al_thread AL) + 2800); (at_thr (al_thread AL) + 2800, at_thr (al_thread AL) + 3168)]).
    assert (AI2 : above_img W2) by (subst W2; env_clear).
    assert (TC2 : thread_clear (al_thread AL) W2).
    { subst W2. pose proof TLO as TL'. unfold thread_layout_ok in TL'. layout_apart_fact AO 0%nat 2%nat AP02.
      clear RIC PRE TS TL TSH STC ST MI MC SV PE TE.
      destruct TL' as (CX1 & CX2 & _ & _ & CXT & _). clear AI2. env_clear. }
    pose proof (munch_refl W2 m0) as MU. pose proof (gmunch_refl WG m0) as GM. pose proof (wmono_refl asegs m0) as WM. subst W2 WG.
    hide TL. hide TSH.
    rewrite <- (ebind_ret_r (t_commit _ _)).
    lz_go.
    call (pop_B0 ra t0 t1 t2 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6); [assumption| exact PRE| lia|].
    unfold ri_addr, RIB.
    do 5 zstep.
    zstep.
    zstep.
    match goal with |- context [Z_to_bv 64 (Z.land ?x ?mk + 262144)] =>
      replace (Z.land x mk + 262144) with msz by (rewrite Hmsz; symmetry; apply msz_code; lia) end.
    do 2 zstep.
    zstep. zstep.
    zstep.
    zstep. if_cases KX; zify_cond KX. { exfalso. lia. } clear KX.
    zstep.
    zstep.   replace (p_mu k + REG) with beg by lia.
    zstep. if_cases KZ; zify_cond KZ; [| exfalso; lia]. clear KZ.
    do 2 zstep.
    do 3 zstep.
    zstep.
    idtac "MARK1".
    callA (rar_map_spec E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q - 64) lo beg msz);
      [ assumption | assumption
      | eapply shvis_wmono; [exact SV| exact WM]
      | eapply poison_env_frame; [exact PE| exact MU| exact WM| exact AI2]
      | exact ST | lia | lia | lia | reflexivity | reflexivity | lia | lia | lia | lia | lia
      | unfold app_mem; right; lia | lia |].
    cbv beta. try clear SWR0; try clear SWB0; try clear SWB.
    idtac "MARK2".
    match goal with P : stk asegs _ lo _, Z0 : rw_cells asegs _ beg _, Wn : stk asegs _ (swlo beg) _, E0 : poison_env E _, S0 : shvis _ _ |- _ =>
      rename P into ST1; rename Z0 into ZNEW; rename Wn into WIN; rename E0 into PE1; rename S0 into SV1 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (wmono_refl asegs mX) as WMa;
      pose proof (munch_refl [(lo, q - 64); (al_space AL + K_SPACE + 128 * c + 48, al_space AL + K_SPACE + 128 * c + 56); (sh beg, sh beg + msz / 8);
                              (at_thr (al_thread AL) + 2792, at_thr (al_thread AL) + 2800); (at_thr (al_thread AL) + 2800, at_thr (al_thread AL) + 3168)] mX) as MUr end.
    hide ZNEW.
    zstep. if_cases K0; zify_cond K0. { exfalso. lia. } clear K0.
    zstep.
    zstep. if_cases K1; zify_cond K1. { exfalso. lia. } clear K1.
    do 3 zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      destruct (stk_mid_chunk mX (swlo beg) (swhi beg msz) (sh beg) (Z.to_nat (msz / 8)) WIN ltac:(lia) ltac:(lia)) as [sj SHC] end.
    clear WIN.
    idtac "MARK3".
    call (poison_shadow_spec E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q - 64) lo beg msz 250);
      [ assumption | lia | unfold poison_range; lia | exact PE1 | exact ST1 | lia | exact SHC |].
    match goal with P : stk asegs _ lo _, E0 : poison_env E _, Sp : rw_cells asegs _ (sh beg) _ |- _ => rename P into ST2; rename E0 into PE2; rename Sp into SHP end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (wmono_refl asegs mX) as WMp;
      pose proof (munch_refl [(lo, q - 64); (al_space AL + K_SPACE + 128 * c + 48, al_space AL + K_SPACE + 128 * c + 56);
                              (at_thr (al_thread AL) + 2792, at_thr (al_thread AL) + 2800); (at_thr (al_thread AL) + 2800, at_thr (al_thread AL) + 3168)] mX) as MUp end.
    hide SHP.
    idtac "MARK4".
    zstep.
    call (gcts_spec (al_thread AL) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q - 64) _ lo);
      [ exact ST2 | lia | lia | lia | lia
      | eapply thread_env_frame; [exact TE| exact MU| exact WM| exact TC2]
      | exact TLO | assumption |].
    match goal with P : stk asegs _ lo _ |- _ => rename P into ST3 end.
    idtac "MARK5".
    zstep. zstep.
    zstep. zstep.
    zstep. zstep.
    zstep.
    zstep.
    idtac "MARK6".
    assert (AMO : amo_aligned AD (Z_to_bv 64 (at_thr (al_thread AL) + 2792)) = true) by (apply amo_aligned_intro_d; lia).
    amo_step_h AMO.
    match goal with Hs : rw_cells asegs _ (at_thr (al_thread AL) + 2784) _ |- _ => cbn [amo_val] in Hs; rewrite ?lit_add_lit in Hs; rename Hs into STC2 end.
    idtac "MARK7".
    zstep. zstep.
    zstep.
    zstep.
    idtac "MARK8".
    lz_ret. unfold popB_post. finish.
    + unfold H_commit. rewrite <- Hbeg. reflexivity.
    + unfold ri_addr, RIB. rewrite <- Hbeg. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
    + eapply poison_env_frame; [exact PE| exact MU| exact WM| exact AI2].
    + eapply thread_env_frame; [exact TE| exact MU| exact WM| exact TC2].
    + eapply shvis_wmono; [exact SV1| exact WMa].
    + replace (at_thr (al_thread AL) + CSTATS_OFF + 16) with (at_thr (al_thread AL) + 2784) by lia. assumption.
    + eapply rw_cells_ex_CB; [exact TS| reflexivity].
    + unhide TL. unhide ZNEW.
      eapply rw_cells_gtransport in TL; [| exact GM| exact WM| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn [disjoint_from]; lia].
      eapply rw_cells_transport in ZNEW; [| exact MUr| exact WMa| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn [disjoint_from]; lia].
      replace beg with (REG + p_au k + Z.of_nat (Z.to_nat (p_mu k - p_au k))) in ZNEW by lia.
      pose proof (CB_join2 _ _ _ _ _ _ TL ZNEW) as TJ.
      replace (Z.to_nat (p_mu k + msz - p_au k)) with (Z.to_nat (p_mu k - p_au k) + Z.to_nat msz)%nat by lia. exact TJ.
    + unhide TSH. unhide SHP.
      pose proof (sh_mono 0 (REG + p_au k) ltac:(lia)) as SHLO1. pose proof (sh_mono 0 beg ltac:(lia)) as SHLO2. change (sh 0) with 2147450880 in SHLO1, SHLO2.
      eapply rw_cells_gtransport in TSH; [| exact GM| exact WM| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn [disjoint_from]; lia].
      eapply rw_cells_transport in SHP; [| exact MUp| exact WMp| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn [disjoint_from]; lia].
      replace (sh beg) with (sh (REG + p_au k) + Z.of_nat (Z.to_nat ((p_mu k - p_au k) / 8))) in SHP by lia.
      pose proof (CB_join2 _ _ _ _ _ _ TSH SHP) as SJ. rewrite <- repeat_app in SJ.
      replace (Z.to_nat ((p_mu k + msz - p_au k) / 8)) with (Z.to_nat ((p_mu k - p_au k) / 8) + Z.to_nat (msz / 8))%nat by (Z.div_mod_to_equations; lia).
      exact SJ.
    + unfold ri_addr, RIB. rewrite <- Hbeg. eapply gmunch_weaken; [| exact GM]. unfold sub_fp; cbn [outside]; intros; lia.
  Qed.
End POPB.
