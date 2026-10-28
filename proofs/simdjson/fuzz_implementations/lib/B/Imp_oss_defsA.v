(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel ImpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface Sj_akit Sj_acps Sj_hkit Sj_num_akit Pj_defsA Pj_os_defsA Imp_hdefsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition OSS_CTOR_A : Z := 0xb57f0.
Definition OSS_SB_CTOR_A : Z := 0xbf908.
Definition OSS_INIT_BUF_A : Z := 0xbfab8.
Definition OSS_IOS_INIT_A : Z := 0x11f64c.
Definition OSS_PUT_A : Z := 0xbdeb4.
Definition OSS_PADOUT_A : Z := 0xbe53c.
Definition OSS_XSPUTN_A : Z := 0x12081c.
Definition OSS_OVERFLOW_A : Z := 0x1213f0.
Definition OSS_PUSH_BACK_A : Z := 0x11be80.
Definition OSS_APPEND_A : Z := 0x11bfcc.
Definition OSS_RESIZE_A : Z := 0x11c2b4.
Definition OSS_STR_A : Z := 0x121214.
Definition OSS_IOS_DTOR_A : Z := 0x120610.
Definition OSS_SENTRY_CTOR_A : Z := 0x120afc.
Definition OSS_SENTRY_DTOR_A : Z := 0x120b58.
Definition OSS_GETLOC_A : Z := 0x11f450.
Definition OSS_USE_FACET_A : Z := 0x1475f4.
Definition OSS_OPNEW_A : Z := 0x17888c.
Definition OSS_OPDEL_SZ_A : Z := 0x119d50.
Definition OSS_MEMMOVE_A : Z := 0x84720.
Definition OSS_MEMSET_A : Z := 0x8471c.
Definition OSS_AMEMSET_A : Z := 0x84bc4.
Definition OSS_SM1_A : Z := 0x6a4cc.

Definition OSS_OS_VPTR_A : Z := 0x17d8d0.
Definition OSS_OS_CVPTR_A : Z := 0x17d940.
Definition OSS_SB_VPTR_A : Z := 0x17d740.
Definition OSS_SBB_VPTR_A : Z := 0x17d500.
Definition OSS_IOS_VPTR_A : Z := 0x17d8f8.
Definition OSS_IOS_CVPTR_A : Z := 0x17d968.
Definition OSS_CLASSIC_A : Z := PJ_LOC_IMP_A.
Definition OSS_GOT_VT_A : Z := 0x180b50.
Definition OSS_VTT_A : Z := 0x17d908.
Definition OSS_VBOFF_A : Z := 0x17d8b8.
Definition OSS_SBVT_A : Z := 0x17d7a0.

Definition imp_rowsA (m : mem) : Prop :=
  ro_cells bsegs m OSS_GOT_VT_A [C8 (Z_to_bv 64 OSS_VTT_A); C8 (Z_to_bv 64 (OSS_SB_VPTR_A - 16)); C8 (Z_to_bv 64 (OSS_SBB_VPTR_A - 16)); C8 (Z_to_bv 64 OSS_VBOFF_A)]
  /\ ro_cells bsegs m OSS_VTT_A [C8 (Z_to_bv 64 OSS_OS_VPTR_A); C8 (Z_to_bv 64 OSS_OS_CVPTR_A); C8 (Z_to_bv 64 OSS_IOS_CVPTR_A); C8 (Z_to_bv 64 OSS_IOS_VPTR_A); C8 (Z_to_bv 64 0x70)]
  /\ ro_cells bsegs m OSS_VBOFF_A [C8 (Z_to_bv 64 0x70)]
  /\ ro_cells bsegs m OSS_SBVT_A [C8 (Z_to_bv 64 OSS_XSPUTN_A); C8 (Z_to_bv 64 OSS_OVERFLOW_A)]
  /\ ro_cells bsegs m PJ_WIDEN_SLOT_A [C8 (Z_to_bv 64 PJ_DO_WIDEN_A)]
  /\ ro_cells bsegs m PJ_GOT_CTYPE_ID_A [C8 (Z_to_bv 64 PJ_CTYPE_ID_A)].

Definition OSS_PB_STACK_A : Z := 64 + 16 + RT_STACK.
Definition OSS_OV_STACK_A : Z := 80 + OSS_PB_STACK_A.
Definition OSS_XSPUTN_STACK_A : Z := 64 + OSS_OV_STACK_A.
Definition OSS_PUT_STACK_A : Z := 192 + 16 + 192 + 16 + OSS_XSPUTN_STACK_A.
Definition OSS_CTOR_STACK_A : Z := 96 + 80 + 80 + 80 + PJ_LOC_STACK_A.
Definition OSS_STR_STACK_A : Z := 64 + 16 + RT_STACK.
Definition OSS_IOS_DTOR_STACK_A : Z := PJ_IOS_DTOR_STACK_A.

Record ossA : Type := mkOssA { oa_data : Z; oa_cap : Z; oa_heap : bool; oa_k : Z; oa_w : Z }.

Definition oa_lim (st : ossA) : Z := if oa_heap st then oa_cap st - 1 else 22.

Definition oachunk (st : ossA) : list (Z * Z) := if oa_heap st then [(oa_data st, oa_cap st)] else [].
Definition ossA0 (O : Z) : ossA := mkOssA (O + 73) IMP_SCAP0 false 0 0.
Definition oa_grown (st : ossA) (NEW : Z) : ossA := mkOssA NEW (2 * oa_cap st) true (oa_k st + 1) (oa_w st + 1).
Definition oa_adv (st : ossA) (n : Z) : ossA := mkOssA (oa_data st) (oa_cap st) (oa_heap st) (oa_k st) (oa_w st + n).

Definition STRREPA (m : mem) (O : Z) (st : ossA) : Prop :=
  if oa_heap st
  then rw_cells bsegs m (O + 72) [C8 (Z_to_bv 64 (oa_cap st + 1)); C8 (Z_to_bv 64 (oa_cap st - 1)); C8 (Z_to_bv 64 (oa_data st))]
       /\ (exists bs, rw_cells bsegs m (oa_data st) [CB (Z.to_nat (oa_cap st)) bs])
       /\ 0 < oa_data st /\ oa_data st mod 16 = 0 /\ oa_cap st mod 16 = 0
  else rw_cells bsegs m (O + 72) [C1 (Z_to_bv 8 44)] /\ (exists bs, rw_cells bsegs m (O + 73) [CB 23 bs]) /\ oa_data st = O + 73.

Definition sb_cellsA (st : ossA) : list cell :=
  [C8 (Z_to_bv 64 OSS_SB_VPTR_A); C8 (Z_to_bv 64 OSS_CLASSIC_A); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 (oa_data st)); C8 (Z_to_bv 64 (oa_data st + oa_w st)); C8 (Z_to_bv 64 (oa_data st + oa_lim st))].
Definition mode16 : list byte := [Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].

Definition PUTCELLSA (m : mem) (O : Z) (st : ossA) : Prop :=
  rw_cells bsegs m (O + 8) (sb_cellsA st)
  /\ (exists hm, rw_cells bsegs m (O + 96) [C8 (Z_to_bv 64 hm)] /\ oa_data st <= hm <= oa_data st + oa_w st)
  /\ (exists j108, rw_cells bsegs m (O + 104) [CB 4 mode16; CB 4 j108]).

Definition OSNUMA (len : Z) (st : ossA) : Prop :=
  0 <= oa_w st <= oa_lim st /\ 0 <= oa_k st /\ 24 * 2 ^ (oa_k st) <= oa_cap st <= PJ_CAPMAX len
  /\ (if oa_heap st then True else oa_cap st = IMP_SCAP0 /\ oa_k st = 0).

Definition OSHADOWA (m : mem) (O : Z) : Prop := bytes_at bsegs m (shad O) (repeat z8 33).

Definition SBINVA' (m : mem) (O len : Z) (st : ossA) : Prop := PUTCELLSA m O st /\ STRREPA m O st /\ OSNUMA len st.

Definition ios_cellsI (O fill : Z) (j124 j260 : list byte) : list cell :=
  [C8 (Z_to_bv 64 OSS_IOS_VPTR_A); C4 (Z_to_bv 64 0x1002); CB 4 j124; C8 (Z_to_bv 64 6); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 (O + 8)); C8 (Z_to_bv 64 OSS_CLASSIC_A);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fill); CB 4 j260].
Lemma ios_cellsI_size : forall O fill j124 j260, cells_size (ios_cellsI O fill j124 j260) = 152%nat.
Proof. intros. reflexivity. Qed.
Lemma sb_cellsA_size : forall st, cells_size (sb_cellsA st) = 64%nat.
Proof. intros. reflexivity. Qed.

Definition IOSINVA (m : mem) (O fill : Z) : Prop :=
  rw_cells bsegs m O [C8 (Z_to_bv 64 OSS_OS_VPTR_A)] /\ exists j124 j260, rw_cells bsegs m (O + 112) (ios_cellsI O fill j124 j260).

Definition OSSINVA (m : mem) (O len : Z) (st : ossA) (fill : Z) : Prop := SBINVA' m O len st /\ IOSINVA m O fill.

Definition oss_inA (fO : Z) (kO : nat) (O : Z) : Prop := fO <= O /\ O + 264 <= fO + fs_size kO - 8 /\ O mod 16 = 0.

Definition os_psi (len : Z) (st : ossA) : Z := 4 * (PJ_CAPMAX len - oa_cap st) + (24 - oa_k st) * PJ_GROWC.

Definition imp_S (L : Z) : Z := if Z.lor L 7 =? 23 then 26 else Z.lor L 7 + 1.
Definition str_costA (L : Z) : Z := if L <=? 22 then 0 else mcost (imp_S L).

Definition strresA (m : mem) (R L : Z) (ocp : option (Z * Z)) : Prop :=
  match ocp with
  | None => L <= 22 /\ exists j23, rw_cells bsegs m R [C1 (Z_to_bv 8 (2 * L)); CB 23 j23]
  | Some (DATA, SZ) => 23 <= L /\ SZ = imp_S L /\ rw_cells bsegs m R [C8 (Z_to_bv 64 (SZ + 1)); C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 DATA)]
                      /\ (exists bs, rw_cells bsegs m DATA [CB (Z.to_nat SZ) bs]) /\ 0 < DATA /\ DATA mod 16 = 0
  end.

Lemma OSNUMA_cap24 : forall len st, OSNUMA len st -> 24 <= oa_cap st.
Proof. intros len st (_ & K0 & (HC & _) & _). assert (0 < 2 ^ oa_k st) by (apply Z.pow_pos_nonneg; lia). lia. Qed.

Lemma OSNUMA_k : forall len st, 0 <= len <= SJ_PADMAX -> OSNUMA len st -> 0 <= oa_k st < 23.
Proof.
  intros len st HL (_ & K0 & (HC & HM) & _). split; [exact K0|]. eapply (schain_fuel len (oa_cap st)); [exact HL| exact K0| exact HC| exact HM].
Qed.

Lemma os_psi_nonneg : forall len st, 0 <= len <= SJ_PADMAX -> OSNUMA len st -> 0 <= os_psi len st.
Proof. intros len st HL N. pose proof (OSNUMA_k len st HL N). pose proof N as (_ & _ & (_ & HM) & _). unfold os_psi. rewrite PJ_GROWC_val. lia. Qed.

Lemma os_psi_grow : forall len st NEW, 0 <= oa_k st < 23 -> 24 <= oa_cap st -> 2 * oa_cap st <= PJ_CAPMAX len ->
  mcost (2 * oa_cap st) <= os_psi len st - os_psi len (oa_grown st NEW).
Proof.
  intros len st NEW K C Z1. pose proof (mcost_le_growc (2 * oa_cap st) ltac:(lia)) as M. unfold os_psi, oa_grown. cbn [oa_cap oa_k]. rewrite PJ_GROWC_val in *. lia.
Qed.

Lemma os_psi_adv : forall len st n, os_psi len (oa_adv st n) = os_psi len st.
Proof. intros. reflexivity. Qed.

Lemma os_psi_root : forall len O, 0 <= len <= SJ_PADMAX -> os_psi len (ossA0 O) <= 2^30.
Proof. intros len O HL. pose proof (PJ_CAPMAX_bound len HL). unfold os_psi, ossA0, IMP_SCAP0. cbn [oa_cap oa_k]. rewrite PJ_GROWC_val. lia. Qed.

Lemma os_grow_okA : forall len st more, 0 <= len -> OSNUMA len st -> oa_w st = oa_lim st -> 1 <= more ->
  oa_w st + more <= PJ_OUTMAX len -> 2 * oa_cap st <= PJ_CAPMAX len.
Proof.
  intros len st more HL (W & _ & (HC & HM) & HH) FULL M1 OUT. unfold oa_lim in FULL. unfold PJ_CAPMAX in *.
  destruct (oa_heap st); [lia|]. destruct HH as (-> & _). unfold IMP_SCAP0, PJ_OUTMAX in *. lia.
Qed.

Lemma OSNUMA_grown : forall len st NEW, 0 <= len <= SJ_PADMAX -> OSNUMA len st -> oa_w st = oa_lim st -> 2 * oa_cap st <= PJ_CAPMAX len ->
  (oa_heap st = true -> oa_cap st mod 16 = 0) -> OSNUMA len (oa_grown st NEW).
Proof.
  intros len st NEW HL N FULL CM M16. pose proof (OSNUMA_k len st HL N) as K. pose proof (OSNUMA_cap24 len st N) as C24.
  destruct N as (W & K0 & (HC & HM) & HH). unfold OSNUMA, oa_grown, oa_lim in *. cbn [oa_w oa_k oa_cap oa_heap].
  split; [destruct (oa_heap st); lia|]. split; [lia|]. split; [| exact I].
  rewrite Z.pow_add_r, Z.pow_1_r by lia. lia.
Qed.

Lemma OSNUMA_adv : forall len st n, OSNUMA len st -> 0 <= n -> oa_w st + n <= oa_lim st -> OSNUMA len (oa_adv st n).
Proof.
  intros len st n (W & K0 & HC & HH) N0 NB. unfold OSNUMA, oa_adv, oa_lim in *. cbn [oa_w oa_k oa_cap oa_heap]. destruct (oa_heap st); repeat split; lia.
Qed.

Lemma land1_mod2 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. pose proof (Z.land_ones x 1 ltac:(lia)) as H. change (Z.ones 1) with 1 in H. change (2 ^ 1) with 2 in H. exact H. Qed.
Lemma long_byte0 : forall cap, cap mod 2 = 0 -> Z.land ((cap + 1) mod 256) 1 = 1.
Proof. intros cap HE. rewrite land1_mod2. Z.div_mod_to_equations. lia. Qed.
Lemma short_byte0 : forall sz, Z.land (2 * sz) 1 = 0.
Proof. intros sz. rewrite land1_mod2. Z.div_mod_to_equations. lia. Qed.
Lemma short_size : forall sz, 0 <= sz -> Z.shiftr (2 * sz) 1 = sz.
Proof. intros sz H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. Z.div_mod_to_equations. lia. Qed.
Lemma testbit_capmask : forall n, 0 <= n -> Z.testbit 18446744073709551614 n = ((1 <=? n) && (n <? 64))%bool.
Proof.
  intros n Hn. change 18446744073709551614 with (2 * Z.ones 63).
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) at 1 by lia. rewrite Z.testbit_even_succ by lia.
    destruct (Z.lt_ge_cases (n - 1) 63).
    + rewrite Z.ones_spec_low by lia. symmetry. apply andb_true_intro. split; [apply Z.leb_le; lia| apply Z.ltb_lt; lia].
    + rewrite Z.ones_spec_high by lia. symmetry. apply Bool.andb_false_intro2. apply Z.ltb_ge. lia.
Qed.
Lemma long_capmask : forall cap, cap mod 2 = 0 -> 0 <= cap -> cap < 2^63 -> Z.land (cap + 1) 18446744073709551614 = cap.
Proof.
  intros cap HE H0 H1. set (h := cap / 2). assert (EC : cap = 2 * h) by (subst h; Z.div_mod_to_equations; lia). rewrite EC.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, testbit_capmask by lia.
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
    destruct (Z.lt_ge_cases (n - 1) 63).
    + replace ((1 <=? Z.succ (n - 1)) && (Z.succ (n - 1) <? 64))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; lia| apply Z.ltb_lt; lia]). apply Bool.andb_true_r.
    + replace ((1 <=? Z.succ (n - 1)) && (Z.succ (n - 1) <? 64))%bool with false
        by (symmetry; apply Bool.andb_false_intro2; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r.
      destruct (Z.eq_dec h 0) as [->|HZ]; [rewrite Z.bits_0; reflexivity|].
      symmetry. apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 62); [| lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma lor_low3 : forall L, 0 <= L -> Z.lor L 7 = 8 * (L / 8) + 7.
Proof.
  intros L HL. change 7 with (Z.ones 3).
  rewrite <- (Z.lor_ldiff_and L (Z.ones 3)) at 1.
  rewrite <- Z.lor_assoc.
  assert (R : Z.lor (Z.land L (Z.ones 3)) (Z.ones 3) = Z.ones 3).
  { rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    destruct (Z.eq_dec (L mod 8) 0) as [E|NE]; [rewrite E; apply Z.lor_0_l|].
    apply Z.lor_ones_low; [Z.div_mod_to_equations; lia|]. apply Z.log2_lt_pow2; [Z.div_mod_to_equations; lia|]. change (2 ^ 3) with 8. Z.div_mod_to_equations; lia. }
  rewrite R.
  assert (D : Z.ldiff L (Z.ones 3) = 8 * (L / 8)).
  { rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia. }
  assert (NC : Z.land (Z.ldiff L (Z.ones 3)) (Z.ones 3) = 0) by apply Z.land_ldiff.
  rewrite <- Z.lxor_lor by exact NC. rewrite <- Z.add_nocarry_lxor by exact NC. rewrite D. reflexivity.
Qed.
Lemma lor1_even : forall z, z mod 2 = 0 -> Z.lor z 1 = z + 1.
Proof.
  intros z HE. assert (NC : Z.land z 1 = 0) by (rewrite land1_mod2; exact HE).
  rewrite <- Z.lxor_lor by exact NC. symmetry. apply Z.add_nocarry_lxor. exact NC.
Qed.
Lemma lor7_alloc : forall a, 0 < a -> a mod 4 = 0 -> Z.lor (2 * (a - 1)) 7 + 1 = 2 * a.
Proof. intros a Ha HM. rewrite lor_low3 by lia. Z.div_mod_to_equations. lia. Qed.

Lemma imp_S_range : forall L, 23 <= L -> L + 1 <= imp_S L <= L + 8 /\ imp_S L mod 2 = 0 /\ imp_S L < L + 9.
Proof.
  intros L HL. unfold imp_S. rewrite lor_low3 by lia.
  destruct (Z.eqb_spec (8 * (L / 8) + 7) 23) as [E|NE]; Z.div_mod_to_equations; lia.
Qed.

Lemma imp_S_machine : forall L, 0 <= L -> imp_S L = (if Z.lor L 7 =? 23 then 26 else Z.lor L 7 + 1).
Proof. intros L HL. reflexivity. Qed.

Definition strrep_rng (O : Z) (st : ossA) (x : Z) : Prop :=
  (O + 72 <= x < O + 96) \/ (oa_heap st = true /\ oa_data st <= x < oa_data st + oa_cap st).
Lemma STRREPA_agree : forall m m' O st, STRREPA m O st -> 0 <= oa_cap st -> agree_on (strrep_rng O st) m m' -> STRREPA m' O st.
Proof.
  intros m m' O st H HC AG. unfold STRREPA, strrep_rng in *. destruct (oa_heap st).
  - destruct H as (H1 & (bs & H2) & H3). split; [| split; [| exact H3]].
    + eapply rw_cells_agree_nw; [exact H1|]. intros a Ha. apply AG. cbn in Ha. left. lia.
    + exists bs. eapply rw_cells_agree_nw; [exact H2|]. intros a Ha. apply AG. cbn [cells_size csize] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. right. split; [reflexivity| lia].
  - destruct H as (H1 & (bs & H2) & H3). split; [| split; [| exact H3]].
    + eapply rw_cells_agree_nw; [exact H1|]. intros a Ha. apply AG. cbn in Ha. lia.
    + exists bs. eapply rw_cells_agree_nw; [exact H2|]. intros a Ha. apply AG. cbn in Ha. lia.
Qed.

Lemma PUTCELLSA_agree : forall m m' O st, PUTCELLSA m O st -> agree_on (fun x => O + 8 <= x < O + 72 \/ O + 96 <= x < O + 112) m m' -> PUTCELLSA m' O st.
Proof.
  intros m m' O st (H1 & (hm & H2 & H3) & (j & H4)) AG. split; [| split].
  - eapply rw_cells_agree_nw; [exact H1|]. intros a Ha. apply AG. cbn in Ha. lia.
  - exists hm. split; [| exact H3]. eapply rw_cells_agree_nw; [exact H2|]. intros a Ha. apply AG. cbn in Ha. lia.
  - exists j. eapply rw_cells_agree_nw; [exact H4|]. intros a Ha. apply AG. cbn in Ha. lia.
Qed.

Definition sbinv_rngI (O : Z) (st : ossA) (x : Z) : Prop := (O + 8 <= x < O + 112) \/ (oa_heap st = true /\ oa_data st <= x < oa_data st + oa_cap st).
Lemma SBINVA'_agree : forall m m' O len st, SBINVA' m O len st -> agree_on (sbinv_rngI O st) m m' -> SBINVA' m' O len st.
Proof.
  intros m m' O len st (P & S & N) AG. pose proof (OSNUMA_cap24 len st N). split; [| split; [| exact N]].
  - apply (PUTCELLSA_agree m m' O st P). intros a Ha. apply AG. left. lia.
  - apply (STRREPA_agree m m' O st S); [lia|]. intros a [Ha|Ha]; apply AG; [left; lia| right; exact Ha].
Qed.

Lemma IOSINVA_agree : forall m m' O fill, IOSINVA m O fill -> agree_on (fun x => O <= x < O + 8 \/ O + 112 <= x < O + 264) m m' -> IOSINVA m' O fill.
Proof.
  intros m m' O fill (H1 & j1 & j2 & H2) AG. split.
  - eapply rw_cells_agree_nw; [exact H1|]. intros a Ha. apply AG. cbn in Ha. lia.
  - exists j1, j2. eapply rw_cells_agree_nw; [exact H2|]. intros a Ha. apply AG. cbn in Ha. lia.
Qed.

Lemma OSHADOWA_agree : forall m m' O, OSHADOWA m O -> agree_on (fun x => shad O <= x < shad O + 33) m m' -> OSHADOWA m' O.
Proof.
  intros m m' O H AG. unfold OSHADOWA in *. eapply bytes_at_agree; [exact H|]. intros a Ha. apply AG. rewrite repeat_length in Ha. lia.
Qed.

Lemma signed_lit : forall x, 0 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite ZBridge.zb_signed, unsigned_lit by lia.
  destruct (Z.ltb_spec x (2^63)); lia.
Qed.

Lemma acc_agree_at : forall (m m' : mem) a n, acc bsegs m a n -> 0 <= a -> agree_on (fun x => shad a <= x <= shad (a + n)) m m' -> acc bsegs m' a n.
Proof.
  intros m m' a n H A0 AG i Hi. destruct (H i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok].
  apply (bytes_at_agree bsegs m m' _ _ Hb). intros x Hx. cbn [length] in Hx. apply AG. unfold shad in *. Z.div_mod_to_equations. lia.
Qed.

Lemma imp_rowsA_agree : forall m m', imp_rowsA m -> (forall a, m' a = m a) -> imp_rowsA m'.
Proof.
  intros m m' (R1 & R2 & R3 & R4 & R5 & R6) AG.
  repeat split; (eapply ro_cells_agree; [eassumption| intros a _; apply AG]).
Qed.

Lemma rw_cells_recastI : forall (m : mem) A cs cs', rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells bsegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
Lemma rw_cells_CB_split2A : forall (m : mem) A (n1 n2 : nat) (bs : list byte), rw_cells bsegs m A [CB (n1 + n2) bs] ->
  rw_cells bsegs m A [CB n1 (firstn n1 bs)] /\ rw_cells bsegs m (A + Z.of_nat n1) [CB n2 (skipn n1 bs)].
Proof.
  intros m A n1 n2 bs H.
  assert (L : length bs = (n1 + n2)%nat) by (destruct H as [[[HL _] _] _]; exact HL).
  assert (H2 : rw_cells bsegs m A ([CB n1 (firstn n1 bs)] ++ [CB n2 (skipn n1 bs)])).
  { eapply rw_cells_recastI; [exact H| | |].
    - cbn. rewrite firstn_length, skipn_length. repeat split; lia.
    - cbn [app cells_bytes cbytes]. rewrite !app_nil_r. apply firstn_skipn.
    - cbn. lia. }
  apply (proj1 (Sj_stage1_kit.rw_cells_app bsegs m A _ _)) in H2. cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r in H2. exact H2.
Qed.

Lemma rw_cells_CB_atA : forall (m : mem) A (n : nat) (bs : list byte) (k : Z), rw_cells bsegs m A [CB n bs] -> 0 <= k <= Z.of_nat n ->
  rw_cells bsegs m A [CB (Z.to_nat k) (firstn (Z.to_nat k) bs)] /\ rw_cells bsegs m (A + k) [CB (n - Z.to_nat k) (skipn (Z.to_nat k) bs)].
Proof.
  intros m A n bs k H K. replace n with (Z.to_nat k + (n - Z.to_nat k))%nat in H by lia.
  apply rw_cells_CB_split2A in H. rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma rw_cells_joinA : forall (m : mem) A cs1 A' cs2, rw_cells bsegs m A cs1 -> rw_cells bsegs m A' cs2 -> A' = A + Z.of_nat (cells_size cs1) ->
  rw_cells bsegs m A (cs1 ++ cs2).
Proof. intros m A cs1 A' cs2 H1 H2 ->. apply Sj_stage1_kit.rw_cells_app. split; assumption. Qed.

Lemma rw_cells_CB_join2A : forall (m : mem) A (n1 n2 : nat) (b1 b2 : list byte) A',
  rw_cells bsegs m A [CB n1 b1] -> rw_cells bsegs m A' [CB n2 b2] -> A' = A + Z.of_nat n1 ->
  rw_cells bsegs m A [CB (n1 + n2) (b1 ++ b2)].
Proof.
  intros m A n1 n2 b1 b2 A' H1 H2 E.
  assert (L1 : length b1 = n1) by (destruct H1 as [[[HL _] _] _]; exact HL).
  assert (L2 : length b2 = n2) by (destruct H2 as [[[HL _] _] _]; exact HL).
  pose proof (rw_cells_joinA m A [CB n1 b1] A' [CB n2 b2] H1 H2) as J. cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r in J.
  specialize (J E). eapply rw_cells_recastI; [exact J| | |].
  - cbn. rewrite length_app. repeat split; lia.
  - cbn [app cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
  - cbn. lia.
Qed.

Section Stmts.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition push_backA_cps : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (L : list (Z * Z)) (st : ossA) (len lo O q fO : Z) (kO : nat)
         (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  rt_live RT Σ = oachunk st ++ L -> (forall p n, In (p, n) L -> 0 < n) -> In (fO, kO) (rt_frames RT Σ) -> oss_inA fO kO O -> rt_sp0 RT Σ - STACK_WIN <= lo -> 0x7fff7f800000 <= lo ->
  STRREPA m O st -> OSNUMA len st -> OSHADOWA m O -> oa_w st = oa_lim st -> 0 <= len <= SJ_PADMAX -> 2 * oa_cap st <= PJ_CAPMAX len ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> lo + OSS_PB_STACK_A <= q -> q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX -> mcost (2 * oa_cap st) <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) (NEW : Z) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q ->
     rw_cells bsegs m' (O + 72) [C8 (wz (2 * oa_cap st + 1)); C8 (wz (oa_lim st + 1)); C8 (wz NEW)] ->
     (exists bs, rw_cells bsegs m' NEW [CB (Z.to_nat (2 * oa_cap st)) bs]) -> 0 < NEW -> NEW mod 16 = 0 -> NEW + 2 * oa_cap st <= rt_sp0 RT Σ - STACK_WIN ->
     (2 * oa_cap st) mod 16 = 0 -> OSHADOWA m' O ->
     rt_live RT Σ' = (NEW, 2 * oa_cap st) :: L -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - mcost (2 * oa_cap st) <= rt_credit RT Σ' ->
     rt_pres_fp L (rt_frames RT Σ) q [(O + 72, O + 96)] m m' ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (O + 72)) (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz OSS_PUSH_BACK_A) fc None m (seg_rom bsegs)).

Definition overflowA_cps : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (L : list (Z * Z)) (st : ossA) (len lo O q c fO : Z) (kO : nat)
         (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  rt_live RT Σ = oachunk st ++ L -> (forall p n, In (p, n) L -> 0 < n) -> In (fO, kO) (rt_frames RT Σ) -> oss_inA fO kO O -> rt_sp0 RT Σ - STACK_WIN <= lo -> 0x7fff7f800000 <= lo ->
  SBINVA' m O len st -> OSHADOWA m O -> oa_w st = oa_lim st -> 0 <= len <= SJ_PADMAX -> 2 * oa_cap st <= PJ_CAPMAX len -> 0 <= c < 256 ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> lo + OSS_OV_STACK_A <= q -> q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX -> mcost (2 * oa_cap st) <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) (NEW : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q ->
     SBINVA' m' O len (oa_grown st NEW) -> OSHADOWA m' O -> NEW + 2 * oa_cap st <= rt_sp0 RT Σ - STACK_WIN ->
     rt_live RT Σ' = (NEW, 2 * oa_cap st) :: L -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - mcost (2 * oa_cap st) <= rt_credit RT Σ' ->
     rt_pres_fp L (rt_frames RT Σ) q [(O + 8, O + 112)] m m' ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz c) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (O + 8)) (wz c) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz OSS_OVERFLOW_A) fc None m (seg_rom bsegs)).

Definition xsputnA_cps : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (L : list (Z * Z)) (st : ossA) (len lo O q S N CAP fO : Z) (kO : nat) (bs : list byte)
         (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  rt_live RT Σ = oachunk st ++ L -> (forall p n, In (p, n) L -> 0 < n) -> In (fO, kO) (rt_frames RT Σ) -> oss_inA fO kO O -> rt_sp0 RT Σ - STACK_WIN <= lo -> 0x7fff7f800000 <= lo ->
  SBINVA' m O len st -> OSHADOWA m O -> 0 <= len <= SJ_PADMAX ->
  rw_cells bsegs m S [CB (Z.to_nat CAP) bs] -> 1 <= N <= CAP -> 0 < S -> S + CAP <= lo -> acc bsegs m S N ->
  ((exists p k, In (p, k) L /\ p <= S /\ S + CAP <= p + k) \/ (fO <= S /\ S + CAP <= fO + fs_size kO - 8)) -> (S + CAP <= O \/ O + 264 <= S) ->
  oa_w st + N <= PJ_OUTMAX len ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> lo + OSS_XSPUTN_STACK_A <= q -> q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  Z.of_nat (length L) + 2 <= LIVE_MAX -> os_psi len st <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) (st' : ossA) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q ->
     SBINVA' m' O len st' -> oa_w st' = oa_w st + N -> OSHADOWA m' O ->
     rt_live RT Σ' = oachunk st' ++ L -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - os_psi len st + os_psi len st' <= rt_credit RT Σ' ->
     rt_pres_fp L (rt_frames RT Σ) q [(O + 8, O + 112)] m m' ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz N) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (O + 8)) (wz S) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz OSS_XSPUTN_A) fc None m (seg_rom bsegs)).

Definition putA_cps : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (L : list (Z * Z)) (st : ossA) (len lo O q BUF N CAP fO : Z) (kO : nat) (bs : list byte)
         (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  rt_live RT Σ = oachunk st ++ L -> (forall p n, In (p, n) L -> 0 < n) -> In (fO, kO) (rt_frames RT Σ) -> oss_inA fO kO O -> rt_sp0 RT Σ - STACK_WIN <= lo -> 0x7fff7f800000 <= lo ->
  OSSINVA m O len st 0xFFFFFFFF -> OSHADOWA m O -> LOCBA m -> 0 <= len <= SJ_PADMAX ->
  rw_cells bsegs m BUF [CB (Z.to_nat CAP) bs] -> 0 <= N <= CAP -> 0 < BUF -> BUF + CAP <= lo -> acc bsegs m BUF N ->
  ((exists p k, In (p, k) L /\ p <= BUF /\ BUF + CAP <= p + k) \/ (fO <= BUF /\ BUF + CAP <= fO + fs_size kO - 8)) -> (BUF + CAP <= O \/ O + 264 <= BUF) ->
  oa_w st + N <= PJ_OUTMAX len ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> lo + OSS_PUT_STACK_A <= q -> q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  (length (rt_frames RT Σ) + 2 <= FRAMES_MAX2)%nat -> rt_frames RT Σ <> [] ->
  Z.of_nat (length L) + 2 <= LIVE_MAX -> 2 + os_psi len st <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) (st' : ossA) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q ->
     OSSINVA m' O len st' 0x20 -> oa_w st' = oa_w st + N -> OSHADOWA m' O -> LOCBA m' ->
     rt_live RT Σ' = oachunk st' ++ L -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - 2 - os_psi len st + os_psi len st' <= rt_credit RT Σ' ->
     rt_pres_fp L (rt_frames RT Σ) q [(O, O + 264)] m m' ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz O) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz O) (wz BUF) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz OSS_PUT_A) fc None m (seg_rom bsegs)).

Definition oss_ctorA_cps : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (len lo O q fO : Z) (kO : nat) (junk : list byte)
         (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> oss_inA fO kO O -> rt_sp0 RT Σ - STACK_WIN <= lo -> 0x7fff7f800000 <= lo ->
  rw_cells bsegs m O [CB 264 junk] -> OSHADOWA m O -> LOCBA m -> 0 <= len <= SJ_PADMAX ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> lo + OSS_CTOR_STACK_A <= q -> q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  (forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ m' -> mem_inv bsegs m' -> stk bsegs m' lo q ->
     OSSINVA m' O len (ossA0 O) 0xFFFFFFFF -> OSHADOWA m' O -> LOCBA m' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(O, O + 264)] m m' ->
     aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz O) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz OSS_CTOR_A) fc None m (seg_rom bsegs)).

Definition strA_cps : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (L : list (Z * Z)) (st : ossA) (len lo O q R fO : Z) (kO : nat) (junk : list byte)
         (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  rt_live RT Σ = oachunk st ++ L -> (forall p n, In (p, n) L -> 0 < n) -> In (fO, kO) (rt_frames RT Σ) -> oss_inA fO kO O -> rt_sp0 RT Σ - STACK_WIN <= lo -> 0x7fff7f800000 <= lo ->
  SBINVA' m O len st -> OSHADOWA m O -> 0 <= len <= SJ_PADMAX -> oa_w st <= PJ_OUTMAX len ->
  fO <= R -> R + 24 <= fO + fs_size kO - 8 -> R mod 8 = 0 -> (R + 24 <= O \/ O + 264 <= R) ->
  rw_cells bsegs m R [CB 24 junk] -> bytes_at bsegs m (shad R) [z8; z8; z8] ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> lo + OSS_STR_STACK_A <= q -> q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX -> str_costA (oa_w st) <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) (ocp : option (Z * Z)) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q ->
     strresA m' R (oa_w st) ocp -> (forall DATA SZ, ocp = Some (DATA, SZ) -> DATA + SZ <= rt_sp0 RT Σ - STACK_WIN) ->
     rw_cells bsegs m' (O + 96) [C8 (wz (oa_data st + oa_w st))] -> bytes_at bsegs m' (shad R) [z8; z8; z8] -> OSHADOWA m' O ->
     rt_live RT Σ' = ocp_chunks ocp ++ rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - str_costA (oa_w st) <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(R, R + 24); (O + 96, O + 104)] m m' ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz R) (wz (O + 8)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz OSS_STR_A) fc None m (seg_rom bsegs)).

Definition ios_dtorA_cps : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (lo O q fO fill : Z) (kO : nat) (j124 j260 : list byte)
         (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> oss_inA fO kO O -> rt_sp0 RT Σ - STACK_WIN <= lo -> 0x7fff7f800000 <= lo ->
  rw_cells bsegs m (O + 112) (ios_cellsI O fill j124 j260) -> OSHADOWA m O -> LOCBA m -> unwind_ok ra s0 (wz q) ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> lo + OSS_IOS_DTOR_STACK_A <= q -> q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  (forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ m' -> mem_inv bsegs m' -> stk bsegs m' lo q -> OSHADOWA m' O ->
     (exists j152, rw_cells bsegs m' (O + 112) [CB 152 j152]) ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(O + 112, O + 120)] m m' ->
     aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (O + 112)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz OSS_IOS_DTOR_A) fc None m (seg_rom bsegs)).

End Stmts.
