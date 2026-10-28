(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac SysStep. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface R_small R_m2s R_thread I_consts I_qck X_atexit D_defs D_kit I_ikit I_pck I_strnlenw I_strlenw I_strlen I_strncmpw.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRtA Require Import F_strcpyA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition i_strcpy : Z := 0x1b7be8.          (* [comment removed for export] *)
Definition i_strcpy_real : Z := 0x1b7cec.     (* [comment removed for export] *)
Notation ISTRCPY_DEPTH := 2224%Z (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition icells_cp (m : mem) : Prop :=
  ro_cells ctasegs m 0x5ac450 [C8 (Z_to_bv 64 0x52b730)]     (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x5a9230 [C8 (Z_to_bv 64 0x66f838)]  (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x66f855 [C1 (Z_to_bv 8 1)].        (* [comment removed for export] *)

Lemma icells_cp_agree : forall m m', icells_cp m -> agree_on (fun x => 0 <= x < 0x1000000) m m' -> icells_cp m'.
Proof.
  intros m m' (C1 & C2 & C3) AG.
  Ltac one AG C := apply (ro_cells_agree ctasegs _ _ _ _ C); eapply agree_sub; [exact AG|]; intros y Hy; cbv beta in *; cbn in Hy; lia.
  split; [one AG C1|]. split; [one AG C2| one AG C3].
Qed.

(* [comment removed for export] *)
Lemma iscpy_loopR : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at ctasegs m x [b]) -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1b7f40) fc None m (seg_rom ctasegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b7f30) fc None m (seg_rom ctasegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

(* [comment removed for export] *)
Lemma iscpy_loopW : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at ctasegs m x [b]) -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (a2' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 e) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1b8020) fc None m (seg_rom ctasegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b8010) fc None m (seg_rom ctasegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Definition chkR_post (sp p L : Z) (gp tp s2 s5 s6 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' (Z_to_bv 64 sp) (Z_to_bv 64 p) (Z_to_bv 64 L) a1' a2' a3' a4' a5' a6' a7'
                    s2 (Z_to_bv 64 (L + 1)) s4' s5 s6 s7' s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1b7ca4) fc None m' (seg_rom ctasegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (sp + -2144).

Lemma iscpy_ripR : forall (sp p L : Z) (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk ctasegs m lo (sp + -2144) -> lo <= sp - 2224 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 <= L -> p + L + 1 < 2^63 ->
  acc ctasegs m p (L + 1) -> rng_ok p (L + 1) -> m2s_cells m -> mem_inv ctasegs m ->
  evt ctasegs (chkR_post sp p L gp tp s2 s5 s6 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 p) (Z_to_bv 64 L) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 (L + 1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b7f48) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2144)) = sp + -2144) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  assert (EUL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  destruct (RO ltac:(lia)) as (RIM & N40).
  do 4 lstep. (* [comment removed for export] *)
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk ctasegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. lstep. lstep. if_true.
  apply evt_done. unfold chkR_post. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma iscpy_chkR : forall (sp p L : Z) (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk ctasegs m lo (sp + -2144) -> lo <= sp - 2224 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 <= L -> p + L + 1 < 2^63 ->
  chk_ok m p (L + 1) -> m2s_cells m -> mem_inv ctasegs m ->
  evt ctasegs (chkR_post sp p L gp tp s2 s5 s6 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 p) (Z_to_bv 64 L) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 (L + 1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b7c5c) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN (AC & QW & RO) (G2 & SHC & HM) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (M2S : m2s_cells m) by (split; [exact G2| split; [exact SHC| exact HM]]). unfold SHB in SHC.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUr : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (L + 1)) = L + 1) by (apply unsigned_lit; lia).
  assert (EUsp : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  lstep. if_false. lstep. lstep.
  destruct (Z_lt_le_dec L 64) as [SMALL|BIG].
  - if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 10 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (L + p) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((p + (L + 1) - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + (L + 1) - 1) with (L + p) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (L + p) / 8) with ((p + (L + 1) - 1) / 8 + 2147450880) by (replace (p + (L + 1) - 1) with (L + p) by lia; lia).
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p (L + 1) AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + (L + 1) - 1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * lstep. lstep. if_cases K3.
        -- apply evt_done. unfold chkR_post. do 18 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (iscpy_ripR sp p L); try assumption; unfold kHighShadowEnd; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (iscpy_loopR (Z.to_nat ((p + (L + 1) - 1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a3' & a4' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold chkR_post. do 18 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (iscpy_ripR sp p L); try assumption; unfold kHighShadowEnd; lia.
    + apply evt_done. unfold chkR_post. do 18 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - if_true. lstep. if_true.
    apply (iscpy_ripR sp p L); try assumption; unfold kHighShadowEnd; lia.
Qed.

(* [comment removed for export] *)
Definition chkW_post (sp p q : Z) (gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' (Z_to_bv 64 sp) (Z_to_bv 64 q) a0' a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 p) s3' s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 i_strcpy_real) fc None m' (seg_rom ctasegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (sp + -2144).

Lemma iscpy_ripW : forall (sp p q L : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk ctasegs m lo (sp + -2144) -> lo <= sp - 2224 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 <= L -> p + L + 1 < 2^63 -> 0 <= q < 2^64 ->
  acc ctasegs m p (L + 1) -> rng_ok p (L + 1) -> m2s_cells m -> mem_inv ctasegs m ->
  evt ctasegs (chkW_post sp p q gp tp s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) (Z_to_bv 64 (L + 1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b8028) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN Q0 AC RO M2S MI. unfold i_strcpy_real.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2144)) = sp + -2144) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO ltac:(lia)) as (RIM & N40).
  do 3 lstep. (* [comment removed for export] *)
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk ctasegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. if_true.
  apply evt_done. unfold chkW_post. do 19 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma iscpy_chkW : forall (sp p q L : Z) (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk ctasegs m lo (sp + -2144) -> lo <= sp - 2224 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 <= L -> p + L + 1 < 2^63 -> 0 <= q < 2^64 ->
  chk_ok m p (L + 1) -> m2s_cells m -> mem_inv ctasegs m ->
  evt ctasegs (chkW_post sp p q gp tp s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 q) (Z_to_bv 64 L) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) (Z_to_bv 64 (L + 1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b7ca4) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN Q0 (AC & QW & RO) (G2 & SHC & HM) MI.
  unfold kHighShadowEnd, i_strcpy_real in *.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (M2S : m2s_cells m) by (split; [exact G2| split; [exact SHC| exact HM]]). unfold SHB in SHC.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (EUr : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (L + 1)) = L + 1) by (apply unsigned_lit; lia).
  assert (EUsp : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  lstep. if_false. lstep. lstep.
  destruct (Z_lt_le_dec L 64) as [SMALL|BIG].
  - if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 10 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (L + p) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((p + (L + 1) - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + (L + 1) - 1) with (L + p) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (L + p) / 8) with ((p + (L + 1) - 1) / 8 + 2147450880) by (replace (p + (L + 1) - 1) with (L + p) by lia; lia).
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p (L + 1) AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + (L + 1) - 1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * lstep. lstep. if_cases K3.
        -- apply evt_done. unfold chkW_post. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (iscpy_ripW sp p q L); try assumption; unfold kHighShadowEnd; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (iscpy_loopW (Z.to_nat ((p + (L + 1) - 1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a2' & a3' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold chkW_post. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (iscpy_ripW sp p q L); try assumption; unfold kHighShadowEnd; lia.
    + apply evt_done. unfold chkW_post. do 19 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - if_true. lstep. if_true.
    apply (iscpy_ripW sp p q L); try assumption; unfold kHighShadowEnd; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition iscpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d : Z) (str : list byte) (W : list (Z * Z)) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctasegs)
    /\ munch W m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ rw_cells ctasegs m' d [CB (length str + 1)%nat (str ++ [Z_to_bv 8 0])].

Lemma iscpy_back : forall (sp d s : Z) (str slack junk : list byte)
    (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 : word) F fc (m : mem) (lo : Z) (fjunk : list byte),
  stk ctasegs m lo (sp + -2144) -> lo <= sp - 2224 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 < s -> 0 < d -> s + Z.of_nat (length str) + 1 <= 2^47 -> d + Z.of_nat (length str) + 1 <= 2^47 ->
  bytes_at ctasegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  rw_cells ctasegs m d [CB (length str + 1)%nat junk] ->
  (d + Z.of_nat (length str) + 1 <= s \/ s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= d) ->
  (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ sp <= s) -> (d + Z.of_nat (length str) + 1 <= lo \/ sp <= d) ->
  chk_ok m s (Z.of_nat (length str) + 1) -> chk_ok m d (Z.of_nat (length str) + 1) -> m2s_cells m ->
  ro_cells ctasegs m 0x5ac450 [C8 (Z_to_bv 64 0x52b730)] -> mem_inv ctasegs m ->
  rw_cells ctasegs m (sp + -72) [C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra] ->
  rw_cells ctasegs m (sp + -2144) [CB 2072 fjunk] ->
  evt ctasegs (iscpy_post vra (Z_to_bv 64 sp) gp tp vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 s8 s9 s10 s11 F fc d str
                 [(d, d + Z.of_nat (length str) + 1); (sp - 2224, sp)] lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 s) (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 d) (Z_to_bv 64 (Z.of_nat (length str) + 1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b7c5c) fc None m (seg_rom ctasegs)).
Proof.
  intros until fjunk. intros ST LO LOLO SPH S0 D0 SH DH STR NZ PAD DST OV SEPS SEPD CSS CSD M2S RCP MI FRs FR. unfold kHighShadowEnd in *.
  set (len := Z.of_nat (length str)) in *.
  assert (FL : length (str ++ Z_to_bv 8 0 :: slack) = (length str + S (length slack))%nat) by (rewrite length_app; cbn; lia).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(d, d + len + 1); (sp - 2224, sp)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  pose proof (munch_refl [(sp - 2224, sp)] m) as MUs.   (* [comment removed for export] *)
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EU2144 : bv_unsigned (Z_to_bv 64 (sp + -2144)) = sp + -2144) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  call (iscpy_chkR sp s len); try eassumption; try (unfold kHighShadowEnd; lia).
  lazymatch goal with H : stk ctasegs _ lo (sp + -2144) |- _ => rename H into ST1 end.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGL : agree_on (fun x => 0 <= x < 0x1000000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8007) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    pose proof (m2s_cells_agree m mm M2S AGL ltac:(assumption)) as M2S1;
    pose proof (chk_ok_agree m mm d _ CSD ltac:(lia) ltac:(lia) AGS) as CSD1; clear AGL AGS
  end.
  call (iscpy_chkW sp d s len); try eassumption; try (unfold kHighShadowEnd; lia).
  lazymatch goal with H : stk ctasegs _ lo (sp + -2144) |- _ => rename H into ST2 end.
  clear MUs M2S1 CSD1. unfold i_strcpy_real.
  (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply (F_strcpyA.strcpy_spec) with (str := str) (slack := slack) (junk := junk) (lo := lo);
      [assumption| rewrite EUs; eassumption| exact NZ| rewrite EUs; exact PAD| rewrite EUd; eassumption| rewrite EU2144; exact ST2| lia| rewrite EU2144; lia
      | rewrite EUs, EUd; clear - OV; lia| rewrite EUs, EU2144; lia| rewrite EUd, EU2144; lia]
    | post_call ctasegs mm ] end.
  rewrite EU2144 in *. rewrite EUd in *. lazymatch goal with H : stk ctasegs _ lo (sp + -2144) |- _ => rename H into ST3 end.
  do 10 lstep. release_frame FR ST3 (sp + -72). release_frame FRs ST3 sp. lstep. lstep.
  unfold iscpy_post. sys_finish. all: rewrite ?EU; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Definition parked (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nspz H A SP := lazymatch A with context [SP] => fail | _ => zidle1 H end.
Local Ltac zidle_beginz SP n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(SP - n, SP)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : ro_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : bytes_at segs m ?A _ |- _ => zidle_nspz H A SP
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Theorem iscpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (d s : Z) (str slack junk : list byte) (lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s ->
  stk ctasegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRCPY_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  0 < s -> 0 < d -> s + Z.of_nat (length str) + 1 <= 2^47 -> d + Z.of_nat (length str) + 1 <= 2^47 -> Z.of_nat (length str) < 2^40 ->
  bytes_at ctasegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  rw_cells ctasegs m d [CB (length str + 1)%nat junk] ->
  (d + Z.of_nat (length str) + 1 <= s \/ s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= d) ->
  (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= s) ->
  (d + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= d) ->
  chk_ok m s (Z.of_nat (length str) + 1) -> chk_ok m d (Z.of_nat (length str) + 1) -> m2s_cells m -> icells_sn m -> icells_cp m -> mem_inv ctasegs m ->
  evt ctasegs (iscpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d str
                 [(d, d + Z.of_nat (length str) + 1); (bv_unsigned sp - ISTRCPY_DEPTH, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 i_strcpy) fc None m (seg_rom ctasegs)).
Proof using RIP.
  intros until lo. intros -> -> ST LO LOLO SPH S0 D0 SH DH L40 STR NZ PAD DST OV SEPS SEPD CSS CSD M2S IC ICP MI.
  unfold kHighShadowEnd, i_strcpy in *.
  set (len := Z.of_nat (length str)) in *.
  assert (FL : length (str ++ Z_to_bv 8 0 :: slack) = (length str + S (length slack))%nat) by (rewrite length_app; cbn; lia).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof IC as (G28 & G38 & RMC & RSN & SHC & AI & ISLEN). pose proof ICP as (RCP & GFL & RPS).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EU2144 : bv_unsigned (Z_to_bv 64 (usp + -2144)) = usp + -2144) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(d, d + len + 1); (usp - 2224, usp)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  pose proof (munch_refl [(usp - 2224, usp)] m) as MUs.
  pose proof STR as STRm. change (parked (bytes_at ctasegs m s (str ++ Z_to_bv 8 0 :: slack))) in STRm.
  pose proof DST as DSTm. change (parked (rw_cells ctasegs m d [CB (length str + 1)%nat junk])) in DSTm.
  carve_frame 72%nat ST. rename FR into FRs. carve_frame 2072%nat ST.
  zidle_beginz usp 2144%Z MUz1 WMz1.
  xsteps_to 0x1cb8c8%Z.
  zidle_end MUz1 WMz1.
  call try_init_spec; [exact AI| rewrite EU2144; exact ST| lia| lia| assumption|].
  rewrite EU2144 in *. lazymatch goal with H : stk ctasegs _ lo (usp + -2144) |- _ => rename H into ST1 end.
  xsteps_to 0x1d6090%Z. (* [comment removed for export] *)
  try clear STR. try clear DST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (bytes_at_transport ctasegs _ m mm _ _ STRm MUs) as STR1; cbn [disjoint_from] in STR1; specialize (STR1 ltac:(split; [lia| exact I]));
    pose proof (rw_cells_transport ctasegs _ m mm _ _ DSTm MUs ltac:(assumption)) as DST1; cbn [disjoint_from cells_size csize Nat.add] in DST1;
    specialize (DST1 ltac:(split; [lia| exact I]))
  end.
  call internal_strlen_spec; [reflexivity| split; [| exact NZ]| assumption|].
  { apply (proj1 (proj1 (bytes_at_app ctasegs _ s (str ++ [Z_to_bv 8 0]) slack) ltac:(rewrite <- app_assoc; exact STR1))). }
  fold len. lstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGL : agree_on (fun x => 0 <= x < 0x1000000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8007) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    pose proof (m2s_cells_agree m mm M2S AGL ltac:(assumption)) as M2S1;
    pose proof (chk_ok_agree m mm s _ CSS ltac:(lia) ltac:(lia) AGS) as CSS1;
    pose proof (chk_ok_agree m mm d _ CSD ltac:(lia) ltac:(lia) AGS) as CSD1; clear AGL AGS
  end.
  clear MUs.
  Local Ltac finish_back usp d s str slack junk :=
    lazymatch goal with H : stk ctasegs _ _ (usp + -2144) |- _ =>
      call (iscpy_back usp d s str slack junk); try eassumption; try (unfold kHighShadowEnd; lia) end;
    unfold iscpy_post; sys_finish.
  lstep. lstep. if_cases K1; zify_cond K1.
  - finish_back usp d s str slack junk.
  - lstep. lstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K1, K2 by lia; clear - K1 K2 OV S0 D0 SH DH; lia|].
    finish_back usp d s str slack junk.
Qed.
End WithRIP.
