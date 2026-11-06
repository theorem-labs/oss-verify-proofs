(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutOpsD.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import DecLemTacM.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DRL.
Definition W32 : Z := 4294967296.
Definition H32 : Z := 2147483648.
Lemma sx32_small : forall r, 0 <= r < H32 -> sx32 r = r.
Proof. intros r H. unfold sx32, H32 in *. destruct (Z.ltb_spec r 2147483648); lia. Qed.
Lemma sx32_mod : forall r, 0 <= r < W32 -> sx32 r mod W32 = r.
Proof.
  intros r H. unfold sx32, W32 in *. destruct (Z.ltb_spec r 2147483648); [apply Z.mod_small; lia|].
  replace (r + 18446744069414584320) with (r + 4294967295 * 4294967296) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma sx32_range : forall r, 0 <= r < W32 -> 0 <= sx32 r < 2 ^ 64.
Proof. intros r H. unfold sx32, W32 in *. destruct (Z.ltb_spec r 2147483648); lia. Qed.
Lemma sx32_pos : forall r, 0 <= r < W32 -> (sx32 r = 0 <-> r = 0).
Proof. intros r H. unfold sx32, W32 in *. destruct (Z.ltb_spec r 2147483648); lia. Qed.

(* [comment removed for export] *)
Lemma u_addw : forall x y : word, bv_unsigned (sext 64 (alu32 ALU_ADD (low32 x) (low32 y)) : word) = sx32 ((bv_unsigned x + bv_unsigned y) mod W32).
Proof. intros. rewrite w_addw. unfold v_addw. apply u_swrap32. Qed.
Lemma u_subw : forall x y : word, bv_unsigned (sext 64 (alu32 ALU_SUB (low32 x) (low32 y)) : word) = sx32 ((bv_unsigned x - bv_unsigned y) mod W32).
Proof. intros. rewrite w_subw. unfold v_subw. apply u_swrap32. Qed.
Lemma u_mulw : forall x y : word, bv_unsigned (sext 64 (mul_div M_MUL (low32 x) (low32 y)) : word) = sx32 ((bv_unsigned x * bv_unsigned y) mod W32).
Proof. intros. rewrite w_mulw. unfold v_mulw. apply u_swrap32. Qed.
Lemma u_divuw : forall x y : word, bv_unsigned y mod W32 <> 0 ->
  bv_unsigned (sext 64 (mul_div M_DIVU (low32 x) (low32 y)) : word) = sx32 (((bv_unsigned x mod W32) / (bv_unsigned y mod W32)) mod W32).
Proof.
  intros x y Hy. rewrite w_divuw. unfold v_divuw. rewrite !bv_wrap32_mod. change (2 ^ 32) with W32.
  destruct (Z.eqb_spec (bv_unsigned y mod W32) 0) as [E0|_]; [contradiction|]. apply u_swrap32.
Qed.
Lemma u_sext4 : forall v : word, bv_unsigned (ext_val true 0 4 v) = sx32 (bv_unsigned v mod W32).
Proof.
  intros v. unfold ext_val, ext_Z. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r. change (8 * N.of_nat 4)%N with 32%N.
  change (2 ^ (8 * Z.of_nat 4)) with W32. rewrite u_swrap32. change 4294967296 with W32. rewrite Z.mod_mod by (unfold W32; lia). reflexivity.
Qed.
Lemma u_lit_small : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z H. rewrite u_lit64. apply Z.mod_small. unfold two64. lia. Qed.
Lemma u64 : forall x : word, 0 <= bv_unsigned x < 2 ^ 64. Proof. exact DLT.u_range. Qed.

(* [comment removed for export] *)
Section L5Z.
Variables (p c : Z).
Hypothesis Hp : 10 <= p <= 100000000.
Hypothesis Hpc : p * c = 1000000000.
Lemma c_pos : 10 <= c <= 100000000. Proof. nia. Qed.
(* [comment removed for export] *)
Definition dv (ux : Z) : Z := sx32 (((ux mod W32) / (p mod W32)) mod W32).
Lemma p_mod : p mod W32 = p. Proof. apply Z.mod_small. unfold W32. lia. Qed.
Lemma dv_eq : forall ux, dv ux = (ux mod W32) / p /\ 0 <= (ux mod W32) / p <= 429496729.
Proof.
  intros ux. unfold dv. rewrite p_mod. pose proof (Z.mod_pos_bound ux W32 ltac:(unfold W32; lia)) as B. set (x := ux mod W32) in *.
  assert (Q : 0 <= x / p <= 429496729).
  { split; [apply Z.div_pos; lia|]. unfold W32 in B.
    assert (A1 : x / p <= x / 10) by (apply Z.div_le_compat_l; lia).
    assert (A2 : x / 10 <= 4294967295 / 10) by (apply Z.div_le_mono; lia). change (4294967295 / 10) with 429496729 in A2. lia. }
  split; [|exact Q]. rewrite (Z.mod_small (x / p)) by (unfold W32; lia). apply sx32_small. unfold H32. lia.
Qed.
(* [comment removed for export] *)
Definition cyv (ux : Z) : Z := sx32 ((sx32 ((ux - (p * dv ux) mod 2 ^ 64) mod W32) * c) mod W32).
Lemma cyv_eq : forall ux, cyv ux = ((ux mod W32) mod p) * c.
Proof.
  intros ux. unfold cyv. destruct (dv_eq ux) as [-> Q]. pose proof (Z.mod_pos_bound ux W32 ltac:(unfold W32; lia)) as B. set (x := ux mod W32) in *.
  pose proof (Z.div_mod x p ltac:(lia)) as DM. pose proof (Z.mod_pos_bound x p ltac:(lia)) as RB.
  assert (PQ : 0 <= p * (x / p) <= x) by nia.
  rewrite (Z.mod_small (p * (x / p))) by (unfold W32 in B; lia).
  rewrite Zminus_mod. fold x. rewrite (Z.mod_small (p * (x / p)) W32) by lia.
  replace (x - p * (x / p)) with (x mod p) by lia. rewrite (Z.mod_small (x mod p)) by lia.
  rewrite (sx32_small (x mod p)) by (unfold H32; lia).
  pose proof c_pos as CB. assert (RC : 0 <= (x mod p) * c < 1000000000) by nia.
  rewrite (Z.mod_small ((x mod p) * c)) by (unfold W32; lia). apply sx32_small. unfold H32. lia.
Qed.
Lemma cyv_range : forall ux, 0 <= cyv ux <= 1000000000 - c.
Proof.
  intros ux. rewrite cyv_eq. pose proof (Z.mod_pos_bound (ux mod W32) p ltac:(lia)) as RB. pose proof c_pos as CB. set (r := (ux mod W32) mod p) in *.
  assert (A1 : 0 <= r * c) by (apply Z.mul_nonneg_nonneg; lia).
  assert (A2 : r * c <= (p - 1) * c) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (A3 : (p - 1) * c = 1000000000 - c) by (rewrite Z.mul_sub_distr_r; lia). lia.
Qed.
(* [comment removed for export] *)
Definition t3v (ux ucy : Z) : Z := sx32 ((dv ux + ucy) mod W32).
Lemma t3v_eq : forall ux ucy, 0 <= ucy <= 999999999 -> t3v ux ucy = (ux mod W32) / p + ucy.
Proof.
  intros ux ucy Hc. unfold t3v. destruct (dv_eq ux) as [-> Q]. rewrite (Z.mod_small ((ux mod W32) / p + ucy)) by (unfold W32 in *; lia). apply sx32_small. unfold H32. lia.
Qed.
End L5Z.

(* [comment removed for export] *)
Definition probe0 (e : expr) : expr := EAlu ALU_SLTU (EAlu ALU_SUB e (ELit 0)) (ELit 1).
Lemma probe0_u : forall E e, bv_unsigned (edenot E (probe0 e)) = if bv_unsigned (edenot E e) <? 1 then 1 else 0.
Proof.
  intros E e. unfold probe0. cbn [edenot]. rewrite u_sltu64, u_sub64, !u_lit64. pose proof (u64 (edenot E e)) as B. change two64 with (2 ^ 64).
  rewrite Z.mod_0_l by lia. rewrite Z.sub_0_r. rewrite (Z.mod_small (bv_unsigned (edenot E e))) by lia. rewrite (Z.mod_small 1) by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma L_probe1 : forall segs e, CXD.lemma_ok segs [KRange (probe0 e) 1 1] (KRange e 0 0).
Proof.
  intros segs e E M HP. apply Forall_cons_iff in HP as [H _]. cbn [kentry_ok] in *. rewrite probe0_u in H. pose proof (u64 (edenot E e)).
  destruct (Z.ltb_spec (bv_unsigned (edenot E e)) 1); lia.
Qed.
(* [comment removed for export] *)
Lemma L_probe_eq : forall segs x y, CXD.lemma_ok segs [KRange (EAlu ALU_SLTU (EAlu ALU_SUB x y) (ELit 1)) 1 1] (KRange (APC.esub x y) 0 0).
Proof.
  intros segs x y E M HP. apply Forall_cons_iff in HP as [H _]. unfold APC.esub. cbn [kentry_ok edenot] in *. rewrite mkAlu_denot.
  rewrite u_sltu64, u_lit64 in H. change two64 with (2 ^ 64) in H. rewrite (Z.mod_small 1) in H by lia.
  pose proof (u64 (alu64 ALU_SUB (edenot E x) (edenot E y))) as B. destruct (Z.ltb_spec (bv_unsigned (alu64 ALU_SUB (edenot E x) (edenot E y))) 1); lia.
Qed.
Definition side4 (p c : Z) : bool := ((10 <=? p) && (p <=? 100000000) && (p * c =? 1000000000))%bool.
Lemma side4_ok : forall p c, side4 p c = true -> 10 <= p <= 100000000 /\ p * c = 1000000000.
Proof. intros p c H. unfold side4 in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. apply Z.eqb_eq in H3. lia. Qed.
Definition e_dv (x : expr) (p : Z) : expr := EMdw M_DIVU x (ELit p).
Definition e_cy (x : expr) (p c : Z) : expr := EMdw M_MUL (EAluw ALU_SUB x (EMd M_MUL (ELit p) (e_dv x p))) (ELit c).
Definition e_t3 (x : expr) (p : Z) (cy : expr) : expr := EAluw ALU_ADD (e_dv x p) cy.
Definition sideP (p : Z) : bool := ((10 <=? p) && (p <=? 100000000))%bool.
Lemma sideP_ok : forall p, sideP p = true -> 10 <= p <= 100000000.
Proof. intros p H. unfold sideP in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia. Qed.
Lemma side4_P : forall p c, side4 p c = true -> sideP p = true.
Proof. intros p c H. unfold side4 in H. apply andb_prop in H as [H _]. exact H. Qed.
Lemma u_e_dv : forall E x p, sideP p = true -> bv_unsigned (edenot E (e_dv x p)) = dv p (bv_unsigned (edenot E x)).
Proof.
  intros E x p S. apply sideP_ok in S as Hp. unfold e_dv. cbn [edenot]. rewrite u_divuw; rewrite u_lit_small by lia; [reflexivity|].
  rewrite (p_mod p Hp). lia.
Qed.
Lemma u_e_cy : forall E x p c, side4 p c = true -> bv_unsigned (edenot E (e_cy x p c)) = cyv p c (bv_unsigned (edenot E x)).
Proof.
  intros E x p c S. pose proof (u_e_dv E x p (side4_P p c S)) as D. apply side4_ok in S as [Hp Hpc]. pose proof (c_pos p c Hp Hpc) as CB. unfold e_cy. cbn [edenot] in *.
  rewrite u_mulw, u_subw, u_mul64. rewrite D. rewrite !u_lit_small by lia. reflexivity.
Qed.
Lemma u_e_t3 : forall E x p cy, sideP p = true -> bv_unsigned (edenot E (e_t3 x p cy)) = t3v p (bv_unsigned (edenot E x)) (bv_unsigned (edenot E cy)).
Proof. intros E x p cy S. pose proof (u_e_dv E x p S) as D. unfold e_t3. cbn [edenot] in *. rewrite u_addw. rewrite D. reflexivity. Qed.
(* [comment removed for export] *)
Lemma L_cy : forall segs Ps x p c hi, (side4 p c && (hi =? 1000000000 - c))%bool = true -> CXD.lemma_ok segs Ps (KRange (e_cy x p c) 0 hi).
Proof.
  intros segs Ps x p c hi S E M _. apply andb_prop in S as [S Hh]. apply Z.eqb_eq in Hh. cbn [kentry_ok]. rewrite (u_e_cy E x p c S).
  apply side4_ok in S as [Hp Hpc]. pose proof (cyv_range p c Hp Hpc (bv_unsigned (edenot E x))). lia.
Qed.
(* [comment removed for export] *)
Lemma L_cy_adv : forall segs v p c hi, (side4 p c && (hi =? 1000000000 - c))%bool = true ->
  CXD.lemma_ok segs [KRange (e_t3 (EExt true 0 4 (EVar v)) p (ELit 0)) 0 0; KRange (EVar v) 1 4294967295] (KRange (e_cy (EExt true 0 4 (EVar v)) p c) c hi).
Proof.
  intros segs v p c hi S E M HP. apply andb_prop in S as [S Hh]. apply Z.eqb_eq in Hh.
  apply Forall_cons_iff in HP as [H1 HP]. apply Forall_cons_iff in HP as [H2 _]. cbn [kentry_ok] in *.
  rewrite (u_e_cy E _ p c S). rewrite (u_e_t3 E _ p _ (side4_P p c S)) in H1. cbn [edenot] in H1, H2 |- *. rewrite u_sext4 in *. rewrite u_lit_small in H1 by lia.
  apply side4_ok in S as [Hp Hpc]. rewrite (t3v_eq p Hp) in H1 by lia. rewrite (cyv_eq p c Hp Hpc).
  set (x := bv_unsigned (ev E v)) in *. rewrite (Z.mod_small x) in H1 by (unfold W32; lia). rewrite (Z.mod_small x) by (unfold W32; lia).
  rewrite sx32_mod in H1 |- * by (unfold W32; lia).
  assert (Q0 : x / p = 0) by (pose proof (Z.div_pos x p ltac:(lia) ltac:(lia)); lia).
  assert (XP : x < p) by (apply Z.div_small_iff in Q0; lia). rewrite (Z.mod_small x p) by lia. pose proof (c_pos p c Hp Hpc). nia.
Qed.
(* [comment removed for export] *)
Lemma L_t3_probe : forall segs Ps x p, sideP p = true ->
  CXD.lemma_ok segs (KRange (probe0 (e_t3 x p (ELit 0))) 0 0 :: Ps) (KRange (e_t3 x p (ELit 0)) 1 2147483647).
Proof.
  intros segs Ps x p S E M HP. apply Forall_cons_iff in HP as [H1 _]. cbn [kentry_ok] in *. rewrite probe0_u in H1.
  rewrite (u_e_t3 E x p _ S) in *. cbn [edenot] in *. rewrite u_lit_small in * by lia. apply sideP_ok in S as Hp. rewrite (t3v_eq p Hp) in * by lia.
  destruct (dv_eq p Hp (bv_unsigned (edenot E x))) as [_ Q]. destruct (Z.ltb_spec ((bv_unsigned (edenot E x) mod W32) / p + 0) 1); lia.
Qed.
(* [comment removed for export] *)
Lemma L_t3_cy : forall segs x p cy l h, (sideP p && (1 <=? l) && (h <=? 999999999))%bool = true ->
  CXD.lemma_ok segs [KRange cy l h] (KRange (e_t3 x p cy) 1 2147483647).
Proof.
  intros segs x p cy l h S E M HP. apply andb_prop in S as [S H2]. apply andb_prop in S as [S H1]. apply Z.leb_le in H1, H2.
  apply Forall_cons_iff in HP as [HC _]. cbn [kentry_ok] in *. rewrite (u_e_t3 E x p _ S). apply sideP_ok in S as Hp. rewrite (t3v_eq p Hp) by lia.
  destruct (dv_eq p Hp (bv_unsigned (edenot E x))) as [_ Q]. lia.
Qed.
(* [comment removed for export] *)
Lemma L_or : forall segs k a t l h, ((0 <=? a) && (a <? l) && (a <? 2 ^ 64))%bool = true ->
  CXD.lemma_ok segs [KRange k l h] (KRange (EAlu ALU_OR (EAlu ALU_XOR k (ELit a)) t) 1 18446744073709551615).
Proof.
  intros segs k a t l h S E M HP. apply andb_prop in S as [S H3]. apply andb_prop in S as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2, H3.
  apply Forall_cons_iff in HP as [HK _]. cbn [kentry_ok edenot] in *. rewrite u_or64, u_xor64, u_lit_small by lia.
  pose proof (u64 (edenot E k)) as Bk. pose proof (u64 (edenot E t)) as Bt. set (uk := bv_unsigned (edenot E k)) in *. set (ut := bv_unsigned (edenot E t)) in *.
  assert (NX : Z.lxor uk a <> 0) by (rewrite Z.lxor_eq_0_iff; lia).
  assert (N0 : Z.lor (Z.lxor uk a) ut <> 0) by (rewrite Z.lor_eq_0_iff; tauto).
  assert (P0 : 0 <= Z.lor (Z.lxor uk a) ut) by (apply Z.lor_nonneg; split; [apply Z.lxor_nonneg|]; lia).
  pose proof (u64 (alu64 ALU_OR (alu64 ALU_XOR (edenot E k) (Z_to_bv 64 a)) (edenot E t))) as BB. rewrite u_or64, u_xor64, u_lit_small in BB by lia. fold uk ut in BB. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u_srlw : forall (x y : word) s, bv_unsigned y mod 32 = s -> 0 <= s ->
  bv_unsigned (sext 64 (alu32 ALU_SRL (low32 x) (low32 y)) : word) = sx32 (((bv_unsigned x mod W32) / 2 ^ s) mod W32).
Proof. intros x y s Hs H0. rewrite w_srlw. unfold v_srlw. rewrite Hs, bv_wrap32_mod, Z.shiftr_div_pow2 by lia. change (2 ^ 32) with W32. apply u_swrap32. Qed.
Lemma u_zx4 : forall v : word, bv_unsigned (ext_val false 0 4 v) = bv_unsigned v mod W32.
Proof. intros v. destruct (u_ext_zx 0 4 v) as (H & _ & _). rewrite H. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r. reflexivity. Qed.
Lemma u_aluw_sx : forall op (x y : word), exists r, 0 <= r < W32 /\ bv_unsigned (sext 64 (alu32 op (low32 x) (low32 y)) : word) = sx32 r.
Proof.
  intros op x y. exists (bv_unsigned (alu32 op (low32 x) (low32 y))). pose proof (bv_unsigned_in_range _ (alu32 op (low32 x) (low32 y))) as B.
  change (bv_modulus 32) with W32 in B. split; [exact B|]. rewrite sext32_unsigned. rewrite bv_wrap64_mod. change (2 ^ 64) with two64. rewrite <- u_lit64.
  rewrite u_swrap32. change 4294967296 with W32. rewrite Z.mod_small by exact B. reflexivity.
Qed.
Lemma land_mask : forall a sh, 0 <= sh -> Z.land a (2 ^ sh - 1) = a mod 2 ^ sh.
Proof. intros a sh H. replace (2 ^ sh - 1) with (Z.ones sh) by (rewrite Z.ones_equiv; lia). apply Z.land_ones. exact H. Qed.
Definition sideS (sh : Z) : bool := ((1 <=? sh) && (sh <=? 9))%bool.
Lemma sideS_ok : forall sh, sideS sh = true -> 1 <= sh <= 9.
Proof. intros sh H. unfold sideS in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia. Qed.
Definition e_sr (x : expr) (sh : Z) : expr := EAluw ALU_SRL x (ELit sh).
Definition e_t6 (x : expr) (sh : Z) (cy : expr) : expr := EAluw ALU_ADD (e_sr x sh) cy.
Definition e_dcy (x : expr) (m c : Z) : expr := EMdw M_MUL (EAlu ALU_AND x (ELit m)) (ELit c).
Definition zx4 (e : expr) : expr := EExt false 0 4 e.
Lemma pow_sh : forall sh, 1 <= sh <= 9 -> 2 <= 2 ^ sh <= 512.
Proof. intros sh H. split; [change 2 with (2 ^ 1) at 1 | change 512 with (2 ^ 9)]; apply Z.pow_le_mono_r; lia. Qed.
Lemma u_e_sr : forall E x sh, sideS sh = true ->
  bv_unsigned (edenot E (e_sr x sh)) = (bv_unsigned (edenot E x) mod W32) / 2 ^ sh /\ 0 <= (bv_unsigned (edenot E x) mod W32) / 2 ^ sh < H32.
Proof.
  intros E x sh S. apply sideS_ok in S. unfold e_sr. cbn [edenot]. pose proof (pow_sh sh S) as P.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E x)) W32 ltac:(unfold W32; lia)) as B. set (X := bv_unsigned (edenot E x) mod W32) in *.
  assert (Q : 0 <= X / 2 ^ sh < H32).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. unfold W32, H32 in *. nia. }
  split; [|exact Q]. rewrite (u_srlw _ _ sh); [| rewrite u_lit_small by lia; apply Z.mod_small; lia | lia].
  fold X. rewrite (Z.mod_small (X / 2 ^ sh)) by (unfold W32, H32 in *; lia). apply sx32_small. exact Q.
Qed.
Lemma u_e_t6 : forall E x sh cy, sideS sh = true -> 0 <= bv_unsigned (edenot E cy) <= 999999999 ->
  exists s, s = (bv_unsigned (edenot E x) mod W32) / 2 ^ sh + bv_unsigned (edenot E cy) /\ 0 <= s < W32 /\ bv_unsigned (edenot E (e_t6 x sh cy)) = sx32 s.
Proof.
  intros E x sh cy S C. destruct (u_e_sr E x sh S) as [D Q]. unfold e_t6. cbn [edenot]. rewrite u_addw. rewrite D.
  eexists. split; [reflexivity|]. unfold H32, W32 in *. split; [lia|]. rewrite Z.mod_small by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma L_sext_ge : forall segs x c, ((0 <=? c) && (c <? 2147483648))%bool = true ->
  CXD.lemma_ok segs [KRange (EAlu ALU_SLTU (EExt true 0 4 x) (ELit c)) 0 0] (KRange (zx4 x) c 4294967295).
Proof.
  intros segs x c S E M HP. apply andb_prop in S as [S1 S2]. apply Z.leb_le in S1. apply Z.ltb_lt in S2. apply Forall_cons_iff in HP as [H _].
  unfold zx4. cbn [kentry_ok edenot] in *. rewrite u_sltu64, u_sext4, u_lit_small in H by lia. rewrite u_zx4.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E x)) W32 ltac:(unfold W32; lia)) as B. set (r := bv_unsigned (edenot E x) mod W32) in *.
  destruct (Z.ltb_spec (sx32 r) c) as [L|G]; [lia|]. unfold sx32 in G. unfold W32 in *. destruct (Z.ltb_spec r 2147483648); lia.
Qed.
(* [comment removed for export] *)
Lemma L_ds_rel : forall segs xa sh l h, (sideS sh && (1 <=? l))%bool = true ->
  CXD.lemma_ok segs [KRange (zx4 xa) l h] (KRange (APC.esub (zx4 xa) (zx4 (e_t6 (EExt true 0 4 xa) sh (ELit 0)))) 1 4294967295).
Proof.
  intros segs xa sh l h S E M HP. apply andb_prop in S as [S L1]. apply Z.leb_le in L1. apply Forall_cons_iff in HP as [H _].
  unfold APC.esub. cbn [kentry_ok] in *. rewrite mkAlu_denot. unfold zx4 in *. cbn [edenot] in H. rewrite u_zx4 in H.
  destruct (u_e_t6 E (EExt true 0 4 xa) sh (ELit 0) S) as (s & Hs & Bs & Ht); [cbn [edenot]; rewrite u_lit_small by lia; lia|].
  cbn [edenot] in Hs. rewrite u_sext4, u_lit_small in Hs by lia.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E xa)) W32 ltac:(unfold W32; lia)) as B. set (r := bv_unsigned (edenot E xa) mod W32) in *.
  rewrite sx32_mod in Hs by exact B. apply sideS_ok in S. pose proof (pow_sh sh S) as P.
  assert (Q : 0 <= r / 2 ^ sh <= r - 1).
  { split; [apply Z.div_pos; lia|]. assert (r / 2 ^ sh <= r / 2) by (apply Z.div_le_compat_l; lia). assert (r / 2 <= r - 1) by (Z.div_mod_to_equations; lia). lia. }
  rewrite u_sub64. change (edenot E (EExt false 0 4 xa)) with (ext_val false 0 4 (edenot E xa)). rewrite u_zx4. fold r.
  change (edenot E (EExt false 0 4 (e_t6 (EExt true 0 4 xa) sh (ELit 0)))) with (ext_val false 0 4 (edenot E (e_t6 (EExt true 0 4 xa) sh (ELit 0)))).
  rewrite u_zx4, Ht, sx32_mod by exact Bs. change two64 with (2 ^ 64). unfold W32 in *. rewrite Z.mod_small by lia. lia.
Qed.
(* [comment removed for export] *)
Lemma L_dcy_adv : forall segs xa sh m c l h hi, (sideS sh && (m =? 2 ^ sh - 1) && (1 <=? c) && (m * c <? 2147483648) && (hi =? m * c) && (1 <=? l))%bool = true ->
  CXD.lemma_ok segs [KRange (e_t6 (EExt true 0 4 xa) sh (ELit 0)) 0 0; KRange (zx4 xa) l h] (KRange (e_dcy (EExt true 0 4 xa) m c) c hi).
Proof.
  intros segs xa sh m c l h hi S E M HP. do 5 (apply andb_prop in S as [S ?X]). apply Z.eqb_eq in X3, X0. apply Z.leb_le in X2, X. apply Z.ltb_lt in X1.
  apply Forall_cons_iff in HP as [H1 HP]. apply Forall_cons_iff in HP as [H2 _]. unfold zx4 in *. cbn [kentry_ok] in *. cbn [edenot] in H2. rewrite u_zx4 in H2.
  destruct (u_e_t6 E (EExt true 0 4 xa) sh (ELit 0) S) as (s & Hs & Bs & Ht); [cbn [edenot]; rewrite u_lit_small by lia; lia|].
  cbn [edenot] in Hs. rewrite u_sext4, u_lit_small in Hs by lia.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E xa)) W32 ltac:(unfold W32; lia)) as B. set (r := bv_unsigned (edenot E xa) mod W32) in *.
  rewrite sx32_mod in Hs by exact B. rewrite Ht in H1. apply sideS_ok in S. pose proof (pow_sh sh S) as P.
  assert (S0 : s = 0) by (apply (proj1 (sx32_pos s Bs)); lia).
  assert (RS : r < 2 ^ sh).
  { assert (D0 : r / 2 ^ sh = 0) by lia. apply Z.div_small_iff in D0; lia. }
  assert (CB : c < 2147483648) by nia.
  unfold e_dcy. cbn [edenot]. rewrite u_mulw, u_and64, u_sext4, !u_lit_small by lia. fold r. rewrite (sx32_small r) by (unfold H32; lia).
  subst m. rewrite land_mask by lia. rewrite (Z.mod_small r) by lia. rewrite (Z.mod_small (r * c)) by (unfold W32; nia). rewrite sx32_small by (unfold H32; nia). nia.
Qed.
(* [comment removed for export] *)
Lemma L_dcy : forall segs Ps x sh m c hi, (sideS sh && (m =? 2 ^ sh - 1) && (1 <=? c) && (m * c <? 2147483648) && (hi =? m * c))%bool = true ->
  CXD.lemma_ok segs Ps (KRange (e_dcy x m c) 0 hi).
Proof.
  intros segs Ps x sh m c hi S E M _. do 4 (apply andb_prop in S as [S ?X]). apply Z.eqb_eq in X2, X. apply Z.leb_le in X1. apply Z.ltb_lt in X0.
  apply sideS_ok in S. pose proof (pow_sh sh S) as P. assert (CB : c < 2147483648) by nia. unfold e_dcy. cbn [kentry_ok edenot]. rewrite u_mulw, u_and64, !u_lit_small by lia.
  subst m. rewrite land_mask by lia. pose proof (Z.mod_pos_bound (bv_unsigned (edenot E x)) (2 ^ sh) ltac:(lia)) as B. set (t := bv_unsigned (edenot E x) mod 2 ^ sh) in *.
  rewrite (Z.mod_small (t * c)) by (unfold W32; nia). rewrite sx32_small by (unfold H32; nia). nia.
Qed.
(* [comment removed for export] *)
Lemma L_probe_nz : forall segs e, CXD.lemma_ok segs [KRange (probe0 e) 0 0] (KRange e 1 18446744073709551615).
Proof.
  intros segs e E M HP. apply Forall_cons_iff in HP as [H _]. cbn [kentry_ok] in *. rewrite probe0_u in H. pose proof (u64 (edenot E e)).
  destruct (Z.ltb_spec (bv_unsigned (edenot E e)) 1); lia.
Qed.
Lemma L_probe_nz_zx : forall segs op a b, CXD.lemma_ok segs [KRange (probe0 (EAluw op a b)) 0 0] (KRange (zx4 (EAluw op a b)) 1 4294967295).
Proof.
  intros segs op a b E M HP. apply Forall_cons_iff in HP as [H _]. unfold zx4. cbn [kentry_ok] in *. rewrite probe0_u in H.
  change (edenot E (EExt false 0 4 (EAluw op a b))) with (ext_val false 0 4 (edenot E (EAluw op a b))). rewrite u_zx4.
  cbn [edenot] in *. destruct (u_aluw_sx op (edenot E a) (edenot E b)) as (r & Br & Hr). rewrite Hr in *. rewrite sx32_mod by exact Br.
  destruct (Z.ltb_spec (sx32 r) 1); [lia|]. pose proof (sx32_pos r Br). unfold W32 in *. lia.
Qed.
(* [comment removed for export] *)
Lemma L_ds_t6_ge : forall segs xa sh l h, (sideS sh && (2 ^ sh <=? l))%bool = true ->
  CXD.lemma_ok segs [KRange (zx4 xa) l h] (KRange (e_t6 (EExt true 0 4 xa) sh (ELit 0)) 1 2147483647).
Proof.
  intros segs xa sh l h S E M HP. apply andb_prop in S as [S L1]. apply Z.leb_le in L1. apply Forall_cons_iff in HP as [H _].
  unfold zx4 in *. cbn [kentry_ok] in *. cbn [edenot] in H. rewrite u_zx4 in H.
  destruct (u_e_sr E (EExt true 0 4 xa) sh S) as [D Q]. destruct (u_e_t6 E (EExt true 0 4 xa) sh (ELit 0) S) as (s & Hs & Bs & Ht); [cbn [edenot]; rewrite u_lit_small by lia; lia|].
  cbn [edenot] in Hs, Q. rewrite u_sext4, u_lit_small in Hs by lia. rewrite u_sext4 in Q.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E xa)) W32 ltac:(unfold W32; lia)) as B. set (r := bv_unsigned (edenot E xa) mod W32) in *.
  rewrite sx32_mod in Hs, Q by exact B. apply sideS_ok in S. pose proof (pow_sh sh S) as P.
  assert (G : 1 <= r / 2 ^ sh) by (apply Z.div_le_lower_bound; lia).
  rewrite Ht. rewrite sx32_small by (unfold H32 in *; lia). unfold H32 in *. lia.
Qed.
(* [comment removed for export] *)
Lemma L_ds_t6_cy : forall segs x sh cy l h, (sideS sh && (1 <=? l) && (h <=? 999999999))%bool = true ->
  CXD.lemma_ok segs [KRange cy l h] (KRange (e_t6 x sh cy) 1 18446744073709551615).
Proof.
  intros segs x sh cy l h S E M HP. apply andb_prop in S as [S H2]. apply andb_prop in S as [S H1]. apply Z.leb_le in H1, H2. apply Forall_cons_iff in HP as [HC _].
  cbn [kentry_ok] in *. destruct (u_e_sr E x sh S) as [_ Q]. destruct (u_e_t6 E x sh cy S ltac:(lia)) as (s & Hs & Bs & Ht). rewrite Ht.
  pose proof (sx32_range s Bs). pose proof (sx32_pos s Bs). lia.
Qed.
Lemma L_ds_t6_cy_zx : forall segs x sh cy l h, (sideS sh && (1 <=? l) && (h <=? 999999999))%bool = true ->
  CXD.lemma_ok segs [KRange cy l h] (KRange (zx4 (e_t6 x sh cy)) 1 4294967295).
Proof.
  intros segs x sh cy l h S E M HP. apply andb_prop in S as [S H2]. apply andb_prop in S as [S H1]. apply Z.leb_le in H1, H2. apply Forall_cons_iff in HP as [HC _].
  unfold zx4. cbn [kentry_ok] in *. change (edenot E (EExt false 0 4 (e_t6 x sh cy))) with (ext_val false 0 4 (edenot E (e_t6 x sh cy))). rewrite u_zx4.
  destruct (u_e_sr E x sh S) as [_ Q]. destruct (u_e_t6 E x sh cy S ltac:(lia)) as (s & Hs & Bs & Ht). rewrite Ht, sx32_mod by exact Bs. unfold W32 in *. lia.
Qed.
(* [comment removed for export] *)
Lemma L_or_ord : forall segs k a t x y l h, ((1 <=? l) && ((expr_eqb x k && expr_eqb y a) || (expr_eqb x a && expr_eqb y k)))%bool = true ->
  CXD.lemma_ok segs [KRange (APC.esub x y) l h] (KRange (EAlu ALU_OR (EAlu ALU_XOR k a) t) 1 18446744073709551615).
Proof.
  intros segs k a t x y l h S E M HP. apply andb_prop in S as [L1 S]. apply Z.leb_le in L1. apply Forall_cons_iff in HP as [HK _].
  unfold APC.esub in HK. cbn [kentry_ok edenot] in *. rewrite mkAlu_denot, u_sub64 in HK. rewrite u_or64, u_xor64.
  pose proof (u64 (edenot E k)) as Bk. pose proof (u64 (edenot E a)) as Ba. pose proof (u64 (edenot E t)) as Bt.
  assert (NE : bv_unsigned (edenot E k) <> bv_unsigned (edenot E a)).
  { intros EQ. apply orb_prop in S as [S|S]; apply andb_prop in S as [S1 S2]; apply expr_eqb_eq in S1, S2; subst x y; rewrite EQ, Z.sub_diag, Z.mod_0_l in HK by (unfold two64; lia); lia. }
  set (uk := bv_unsigned (edenot E k)) in *. set (ua := bv_unsigned (edenot E a)) in *. set (ut := bv_unsigned (edenot E t)) in *.
  assert (NX : Z.lxor uk ua <> 0) by (rewrite Z.lxor_eq_0_iff; exact NE).
  assert (N0 : Z.lor (Z.lxor uk ua) ut <> 0) by (rewrite Z.lor_eq_0_iff; tauto).
  assert (P0 : 0 <= Z.lor (Z.lxor uk ua) ut) by (apply Z.lor_nonneg; split; [apply Z.lxor_nonneg|]; lia).
  pose proof (u64 (alu64 ALU_OR (alu64 ALU_XOR (edenot E k) (edenot E a)) (edenot E t))) as BB. rewrite u_or64, u_xor64 in BB. fold uk ua ut in BB. lia.
Qed.

(* [comment removed for export] *)
Ltac side := vm_compute; reflexivity.
Ltac ring_lem :=
  lazymatch goal with
  | |- CXD.lemma_ok _ [KRange (EAlu ALU_SLTU (EAlu ALU_SUB ?e (ELit 0)) (ELit 1)) 1 1] (KRange ?e 0 0) => apply L_probe1
  | |- CXD.lemma_ok _ [KRange (EAlu ALU_SLTU (EAlu ALU_SUB ?x ?y) (ELit 1)) 1 1] (KRange _ 0 0) => exact (L_probe_eq _ x y)
  | |- CXD.lemma_ok _ _ (KRange (EMdw M_MUL (EAluw ALU_SUB _ _) _) 0 _) => apply L_cy; side
  | |- CXD.lemma_ok _ _ (KRange (EMdw M_MUL (EAluw ALU_SUB _ _) _) _ _) => apply L_cy_adv; side
  | |- CXD.lemma_ok _ (KRange (EAlu ALU_SLTU _ _) 0 0 :: _) (KRange (EAluw ALU_ADD (EMdw M_DIVU _ _) (ELit 0)) 1 _) => apply L_t3_probe; side
  | |- CXD.lemma_ok _ _ (KRange (EAluw ALU_ADD (EMdw M_DIVU _ _) _) 1 _) => apply L_t3_cy; side
  | |- CXD.lemma_ok _ _ (KRange (EAlu ALU_OR (EAlu ALU_XOR _ (ELit _)) _) 1 _) => apply L_or; side
  | |- CXD.lemma_ok _ [KRange ?p ?l ?h] (KRange (EAlu ALU_OR (EAlu ALU_XOR ?k ?a) ?t) 1 _) =>
      first [ exact (L_or_ord _ k a t k a l h eq_refl) | exact (L_or_ord _ k a t a k l h eq_refl) ]
  | |- CXD.lemma_ok _ [KRange (EAlu ALU_SLTU (EExt true 0 4 _) (ELit _)) 0 0] (KRange (EExt false 0 4 _) _ 4294967295) => apply L_sext_ge; side
  | |- CXD.lemma_ok _ [KRange (EExt false 0 4 ?xa) ?l ?h] (KRange (EAlu ALU_ADD _ _) 1 4294967295) =>
      first [ exact (L_ds_rel _ xa 9 l h eq_refl) | exact (L_ds_rel _ xa 1 l h eq_refl) ]
  | |- CXD.lemma_ok _ [KRange (EAluw ALU_ADD (EAluw ALU_SRL _ (ELit ?sh)) (ELit 0)) 0 0; _] (KRange (EMdw M_MUL (EAlu ALU_AND _ _) _) _ _) => apply (L_dcy_adv _ _ sh); side
  | |- CXD.lemma_ok _ _ (KRange (EMdw M_MUL (EAlu ALU_AND _ (ELit 511)) _) 0 _) => apply (L_dcy _ _ _ 9); side
  | |- CXD.lemma_ok _ _ (KRange (EMdw M_MUL (EAlu ALU_AND _ (ELit 1)) _) 0 _) => apply (L_dcy _ _ _ 1); side
  | |- CXD.lemma_ok _ [KRange (EAlu ALU_SLTU (EAlu ALU_SUB ?e (ELit 0)) (ELit 1)) 0 0] (KRange ?e 1 18446744073709551615) => apply L_probe_nz
  | |- CXD.lemma_ok _ [KRange (EAlu ALU_SLTU (EAlu ALU_SUB (EAluw _ _ _) (ELit 0)) (ELit 1)) 0 0] (KRange (EExt false 0 4 (EAluw _ _ _)) 1 4294967295) => apply L_probe_nz_zx
  | |- CXD.lemma_ok _ [KRange (EExt false 0 4 _) _ _] (KRange (EAluw ALU_ADD (EAluw ALU_SRL _ _) (ELit 0)) 1 2147483647) => apply L_ds_t6_ge; side
  | |- CXD.lemma_ok _ [KRange _ _ _] (KRange (EAluw ALU_ADD (EAluw ALU_SRL _ _) _) 1 18446744073709551615) => apply L_ds_t6_cy; side
  | |- CXD.lemma_ok _ [KRange _ _ _] (KRange (EExt false 0 4 (EAluw ALU_ADD (EAluw ALU_SRL _ _) _)) 1 4294967295) => apply L_ds_t6_cy_zx; side
  | |- _ => first [ DLT.lem_enum | unfold CXD.lemma_ok; DLT.lem | unfold CXD.lemma_ok; DLT.lem_sext ]
  end.
End DRL.
