(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Walk. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_thread R_cache_defs F_memset R_setshadow R_poison.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition ps0_ok (a : Z) : Prop :=
  (a mod 8 = 0)%Z /\ ((8 <= a /\ a <= kLowMemEnd) \/ (kHighShadowEnd + 8 < a /\ a <= kHighMemEnd))%Z.

(* [comment removed for export] *)
Lemma ps0_j54ad0 : forall ra ra' sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m0 m : mem) (s0o s1o s2o s3o s4o s5o : word) (a v lo : Z) (junk : list byte),
  ps0_ok a -> (0 < v < 256)%Z ->
  ps_cells m ->
  rw_cells ctasegs m (bv_unsigned sp - 64) [CB 8 junk; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra] ->
  stk ctasegs m lo (bv_unsigned sp - 64) -> (lo <= bv_unsigned sp - 64)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  munch [(shad a, shad a + 0 / 8); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m0 m -> wmono ctasegs m0 m -> mem_inv ctasegs m ->
  evt ctasegs (poison_small_post ra sp gp tp s0o s1o s2o s3o s4o s5o s6 s7 s8 s9 s10 s11 F fc a 0 v lo m0)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 2147450880) (Z_to_bv 64 a)
             (Z_to_bv 64 (a + 0 - 8)) (Z_to_bv 64 v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c5884) fc None m (seg_rom ctasegs)).
Proof.
  intros until junk. intros HA Hv PS FR ST HLO HLOH MU WM MI.
  destruct HA as (Ha & HR).
  ps_cells_destr PS.
  do 4 zstep. ifF.
  do 5 zstep.
  pose proof (Z.div_mod a 8 ltac:(lia)) as D1.
  assert (E1 : (2147450880 + a ≫ 3)%Z = shad a) by (unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; cbn; lia).
  assert (E2 : (((a + 0 - 8) ≫ 3 + 1) mod 18446744073709551616 - a ≫ 3)%Z = 0%Z).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
    replace (a + 0 - 8)%Z with ((a / 8 - 1) * 8)%Z by lia. rewrite Z.div_mul by lia.
    rewrite Z.mod_small by (pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)); lia). lia. }
  rewrite E1, E2.
  zstep. ifT.
  do 11 zstep.
  replace (bv_unsigned sp - 64 + 64)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  assert (SR : (0x7fff8000 <= shad a <= kHighShadowEnd + 1)%Z).
  { unfold shad, SHB, kHighShadowEnd. pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound a 8 (2^44) ltac:(lia) ltac:(lia)). lia. }
  unfold kHighShadowEnd in SR.
  eapply evt_mono; [eapply memset_callZ with (junk := []); [apply rw_cells_CB0; lia| exact MI| lia| lia| lia| lia] |].
  intros ms' PO. unfold memset_postZ in PO.
  destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & E & MU2 & WM2 & MI2 & RW).
  subst ms'. unfold poison_small_post.
  do 16 eexists. split; [reflexivity|].
  split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros; lia]|].
  split; [eapply wmono_trans; eassumption|].
  split; [exact MI2|].
  split; [exact RW|].
  eapply stk_transport_disjoint; [exact ST| exact MU2| exact WM2|]. cbn [disjoint_from]. destruct ST as [? _].
  split; [right; lia| exact I].
Qed.

(* [comment removed for export] *)
Lemma ps0_j54a7c_k : forall (Q : machine_state -> Prop) ra' sp gp tp t0 t1 t2 a3 a5 a6 a7 s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (a v : Z),
  ps0_ok a -> ps_cells m -> mem_inv ctasegs m ->
  ps_K54ad0 Q ra' sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a 0 v ->
  evt ctasegs Q
    (MS (mkR ra' sp gp tp t0 t1 t2 s0 (Z_to_bv 64 2147450880) (Z_to_bv 64 a)
             (Z_to_bv 64 0) (Z_to_bv 64 v) a3 (Z_to_bv 64 2147450879) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c5830) fc None m (seg_rom ctasegs)).
Proof.
  intros until v. intros HA PS MI K.
  destruct HA as (Ha & HR).
  ps_cells_destr PS.
  zstep. try rewrite land7_ps by lia. zstep. ifF.
  do 2 zstep.
  replace (a + -8)%Z with (a + 0 - 8)%Z by lia.
  zstep.
  destruct HR as [HL|HH].
  - ifT. apply K.
  - ifF.
    do 8 zstep.
    assert (C1 : negb (bv_ltu (Z_to_bv 64 (-1)) (Z_to_bv 64 (a + 0 - 8))) = true).
    { unfold bv_ltu. rewrite (unsigned_lit_wrap (-1)), (unsigned_lit (a + 0 - 8)) by lia.
      change ((-1) mod 2^64)%Z with 18446744073709551615%Z. apply negb_true_iff, Z.ltb_ge. lia. }
    rewrite C1; cbv iota.
    do 5 zstep.
    zstep. ifF. zstep. ifF.
    apply K.
Qed.

(* [comment removed for export] *)


Lemma poison0_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (a v lo : Z),
  ps0_ok a -> (0 < v < 256)%Z ->
  ps_cells m ->
  stk ctasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (poison_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a 0 v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 0) (Z_to_bv 64 v) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ps_entry) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros HA Hv PS ST HLO HLOH MI.
  pose proof PS as PS0.
  destruct HA as (Ha & HR).
  ps_cells_destr PS.
  unfold ps_entry.
  pose proof (munch_refl [(shad a, shad a + 0 / 8); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
  carve_frame 64%nat ST.
  zidle_begin sp 64%Z MUz WMz.
  do 8 zstep.
  zidle_end MUz WMz.
  do 1 zstep. ifF.
  do 4 zstep. ifF.
  zstep. rewrite land7_ps by lia. zstep. ifF.
  do 8 zstep.
  replace (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879)%Z with 2147450879%Z
    by reflexivity.
  replace (bv_unsigned sp + -64)%Z with (bv_unsigned sp - 64)%Z in * by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (PSm : ps_cells mm) by (unfold ps_cells, m2s_cells, setshadow_cells, g_got_common_flags, g_can_poison,
      g_cf_clear_shadow_mmap_threshold, g_got_real_memset, g_real_memset, musl_memset_entry, SHB, kHighMemEnd;
      refine (conj _ (conj (conj _ (conj _ _)) (conj (conj _ _) (conj _ _)))); assumption) end.
  assert (HA0 : ps0_ok a) by (split; assumption).
  assert (K : ps_K54ad0 (poison_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a 0 v lo m)
                ra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 a 0 v).
  { intros t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6'. eapply ps0_j54ad0; try eassumption. }
  destruct HR as [HL|HH].
  - ifT. eapply ps0_j54a7c_k; eassumption.
  - ifF.
    do 8 zstep.
    assert (C1 : negb (bv_ltu (Z_to_bv 64 (-1)) (Z_to_bv 64 a)) = true).
    { unfold bv_ltu. rewrite (unsigned_lit_wrap (-1)), (unsigned_lit a) by lia.
      change ((-1) mod 2^64)%Z with 18446744073709551615%Z. apply negb_true_iff, Z.ltb_ge. lia. }
    rewrite C1; cbv iota.
    do 5 zstep.
    zstep. ifF. zstep. ifT.
    do 3 zstep.
    zstep. ifF. zstep. ifT.
    eapply ps0_j54a7c_k; eassumption.
Qed.

(* [comment removed for export] *)
Lemma poison_fa_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (a n lo : Z) (shj : list byte),
  ((n = 0 /\ ps0_ok a) \/ ps_args_ok a n)%Z ->
  rw_cells ctasegs m (shad a) [CB (Z.to_nat (n / 8)) shj] ->
  ps_cells m ->
  stk ctasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (poison_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a n 250 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 n) (Z_to_bv 64 250) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ps_entry) fc None m (seg_rom ctasegs)).
Proof.
  intros until shj. intros [[-> H0]|H1] SH PS ST HLO HLOH MI.
  - eapply poison0_spec; try eassumption. lia.
  - eapply poison_small_spec; try eassumption; lia.
Qed.
