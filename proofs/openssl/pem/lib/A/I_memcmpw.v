(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_thread I_consts I_qck X_atexit I_pck D_kit I_ikit I_strncmpw Str_memcmp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation MCC_FRAME := 2192%Z (only parsing).

(* [comment removed for export] *)
Fixpoint mcmp_res (b1 b2 : list byte) : Z :=
  match b1, b2 with
  | x :: r1, y :: r2 => if bv_unsigned x =? bv_unsigned y then mcmp_res r1 r2 else bv_unsigned x - bv_unsigned y
  | _, _ => 0
  end.

Lemma mcmp_walk_res : forall b1 b2, length b1 = length b2 -> memcmp_walk b1 b2 (length b1) = Some (mcmp_res b1 b2).
Proof.
  induction b1 as [|x r1 IH]; intros [|y r2] HL; cbn in HL; try discriminate; [reflexivity|].
  cbn [length memcmp_walk mcmp_res]. destruct (bv_unsigned x =? bv_unsigned y); [apply IH; lia| reflexivity].
Qed.

(* [comment removed for export] *)
Definition icells_mcmp (m : mem) : Prop :=
  ro_cells asegs m 0x5a45a8 [C8 (Z_to_bv 64 0x6fe668)]           (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5a45b8 [C8 (Z_to_bv 64 0x66cb38)]         (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5a7600 [C8 (Z_to_bv 64 0x5264b0); C8 (Z_to_bv 64 0x5263dc)]   (* [comment removed for export] *)
  /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)]      (* [comment removed for export] *)
  /\ rw_cells asegs m 0x66d818 [C1 (Z_to_bv 8 1)]                (* [comment removed for export] *)
  /\ ro_cells asegs m 0x6fe766 [C1 (Z_to_bv 8 1)]               (* [comment removed for export] *)
  /\ ro_cells asegs m 0x6fe767 [C1 (Z_to_bv 8 1)].              (* [comment removed for export] *)

Lemma icells_mcmp_agree : forall m m', icells_mcmp m -> agree_on (fun x => 0 <= x < 0x1000000) m m' -> wmono asegs m m' -> icells_mcmp m'.
Proof.
  intros m m' (C1 & C2 & C3 & C4 & C5 & C6 & C7) AG WM.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply (ro_cells_agree asegs m m' _ _ C1). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C2). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C3). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C4). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (rw_cells_agree asegs m m' _ _ C5); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C6). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C7). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
Qed.

(* [comment removed for export] *)
Lemma mcc_loop1 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1aea00) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ae9f0) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Lemma mcc_loop2 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1aeb0c) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1aeafc) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

(* [comment removed for export] *)
Lemma mcc_prologue : forall (sp p1 p2 n : Z) (fn : word) (ra gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo sp -> lo <= sp - MCC_FRAME -> kHighShadowEnd + 8 <= lo -> sp < 2^63 -> icells_mcmp m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (junk : list byte) (a1' : word),
      ms' = MS (mkR ra (Z_to_bv 64 (sp + -2192)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 n)
                    a0 a1' (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 n) a5 a6 a7 (Z_to_bv 64 p2) ra (Z_to_bv 64 p1) fn
                    s6 (Z_to_bv 64 (sp + -2176)) (Z_to_bv 64 0x6fe668) s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1ae5e8) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2192, sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m' (sp + -2192) [CB 2088 junk]
      /\ stk asegs m' lo (sp + -2192))
    (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 a0 fn (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 n) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ae574) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH (G70 & G2 & RP & SHC & AI & F1 & F2) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2192, sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  carve_frame 104%nat ST. rename FR into FRs. carve_frame 2088%nat ST.
  do 22 lstep.
  do 2 lstep. lstep. if_false. do 3 lstep. lstep. if_false.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRs|]. split; [exact FR| exact ST].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Lemma mcc_rip1 : forall (sp p n : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2192) -> lo <= sp - 2272 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 < n -> p + n < 2^63 ->
  acc asegs m p n -> rng_ok p n -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s6' s10' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2192)) gp tp t0' t1' t2' s0 (Z_to_bv 64 n) a0 a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 (Z_to_bv 64 p) s5 s6' s7 s8 s9 s10' s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1ae638) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2272, sp - 2192)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2192))
    (MS (mkR ra (Z_to_bv 64 (sp + -2192)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1aea08) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH P0 N0 PN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2272, sp - 2192)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2192)) = sp + -2192) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 4 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  do 2 lstep. lstep. if_true.
  apply evt_done. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* [comment removed for export] *)
Lemma mcc_chk1 : forall (sp p n : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2192) -> lo <= sp - 2272 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 <= n -> p + n < 2^63 ->
  chk_ok m p n -> m2s_cells m -> icells_mcmp m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s6' s10' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2192)) gp tp t0' t1' t2' s0 (Z_to_bv 64 n) a0 a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 (Z_to_bv 64 p) s5 s6' s7 s8 (Z_to_bv 64 (n + -65)) s10' s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1ae638) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2272, sp - 2192)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2192))
    (MS (mkR ra (Z_to_bv 64 (sp + -2192)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ae5e8) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH P0 N0 PN (AC & QW & RO) M2S (G70 & G2 & RP & SHC & AI & F1 & F2) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2272, sp - 2192)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  lstep. if_false.
  lstep. lstep. lstep.
  destruct (Z_lt_le_dec 64 n) as [BIG|SMALL]; [| destruct (Z.eq_dec n 0) as [Z0|NZ]].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65) by (apply unsigned_lit; lia).
    if_true. lstep. if_true.
    apply (mcc_rip1 sp p n); try assumption; lia.
  - (* [comment removed for export] *)
    subst n. if_true. lstep. if_false. lstep.
    apply evt_done. do 18 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (p + n + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((p + n - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + n + -1) with (p + n - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + (* [comment removed for export] *)
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (p + n + -1) / 8) with ((p + n + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p n AC ltac:(lia) P0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + n + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * (* [comment removed for export] *)
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 18 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (mcc_rip1 sp p n); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (mcc_loop1 (Z.to_nat ((p + n + -1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a3' & a4' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 18 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (mcc_rip1 sp p n); try assumption; lia.
    + apply evt_done. do 18 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

(* [comment removed for export] *)
Lemma mcc_rip2 : forall (sp p n : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2192) -> lo <= sp - 2272 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 < n -> p + n < 2^63 ->
  acc asegs m p n -> rng_ok p n -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s9' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2192)) gp tp t0' t1' t2' s0 (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 p) s3 s4 s5 s6' s7 s8 s9' s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1ae684) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2272, sp - 2192)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2192))
    (MS (mkR ra (Z_to_bv 64 (sp + -2192)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1aeb14) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH P0 N0 PN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2272, sp - 2192)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2192)) = sp + -2192) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 4 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. lstep. if_true.
  apply evt_done. do 19 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* [comment removed for export] *)
Lemma mcc_chk2 : forall (sp p n : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2192) -> lo <= sp - 2272 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 <= n -> p + n < 2^63 ->
  chk_ok m p n -> m2s_cells m -> icells_mcmp m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s9' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2192)) gp tp t0' t1' t2' s0 (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 p) s3 s4 s5 s6' s7 s8 s9' s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1ae684) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2272, sp - 2192)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2192))
    (MS (mkR ra (Z_to_bv 64 (sp + -2192)) gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (n + -65)) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ae638) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH P0 N0 PN (AC & QW & RO) M2S (G70 & G2 & RP & SHC & AI & F1 & F2) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2272, sp - 2192)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  lstep. if_false.
  lstep. lstep.
  destruct (Z_lt_le_dec 64 n) as [BIG|SMALL]; [| destruct (Z.eq_dec n 0) as [Z0|NZ]].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65) by (apply unsigned_lit; lia).
    if_true. lstep. if_true.
    apply (mcc_rip2 sp p n); try assumption; lia.
  - (* [comment removed for export] *)
    subst n. if_true. lstep. if_false. lstep.
    apply evt_done. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (p + n + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((p + n - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + n + -1) with (p + n - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + (* [comment removed for export] *)
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (p + n + -1) / 8) with ((p + n + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p n AC ltac:(lia) P0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + n + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * (* [comment removed for export] *)
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (mcc_rip2 sp p n); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (mcc_loop2 (Z.to_nat ((p + n + -1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a3' & a4' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (mcc_rip2 sp p n); try assumption; lia.
    + apply evt_done. do 19 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

End WithRIP.

(* [comment removed for export] *)
Definition cmp_pre (m : mem) (p1 p2 : Z) (b1 b2 : list byte) (usp lo : Z) : Prop :=
  length b1 = length b2 /\ Z.of_nat (length b1) < 2^31 /\ 0 <= p1 /\ 0 <= p2
  /\ p1 + Z.of_nat (length b1) <= 2^47 /\ p2 + Z.of_nat (length b1) <= 2^47
  /\ bytes_at asegs m p1 b1 /\ bytes_at asegs m p2 b2
  /\ (Z.of_nat (length b1) = 0 \/ p1 + Z.of_nat (length b1) <= lo \/ usp <= p1)
  /\ (Z.of_nat (length b1) = 0 \/ p2 + Z.of_nat (length b1) <= lo \/ usp <= p2)
  /\ chk_ok m p1 (Z.of_nat (length b1)) /\ chk_ok m p2 (Z.of_nat (length b1)) /\ m2s_cells m /\ icells_mcmp m.

Lemma bytes_at_nil_any : forall (m m' : mem) a, bytes_at asegs m a [] -> bytes_at asegs m' a [].
Proof. intros m m' a (H1 & H2 & _). split; [exact H1|]. split; [exact H2|]. intros i Hi. cbn in Hi. lia. Qed.

(* [comment removed for export] *)
Lemma cmp_pre_munch : forall (m m' : mem) p1 p2 b1 b2 usp usp' lo l h,
  cmp_pre m p1 p2 b1 b2 usp lo -> munch [(l, h)] m m' -> wmono asegs m m' ->
  lo <= l -> h <= usp -> usp' <= usp -> kHighShadowEnd + 8 <= lo ->
  cmp_pre m' p1 p2 b1 b2 usp' lo.
Proof.
  intros m m' p1 p2 b1 b2 usp usp' lo l h (HL & NB & P1 & P2 & R1 & R2 & B1 & B2 & S1 & S2 & C1 & C2 & M2S & IC) MU WM L1 L2 L3 LOLO.
  unfold kHighShadowEnd in *.
  assert (AGs : forall P : Z -> Prop, (forall x, P x -> x < l \/ h <= x) -> agree_on P m m').
  { intros P HP. apply (agree_of_munch _ _ _ _ MU). intros y Hy. cbn [outside]. split; [specialize (HP y Hy); lia| exact I]. }
  split; [exact HL|]. split; [exact NB|]. split; [exact P1|]. split; [exact P2|]. split; [exact R1|]. split; [exact R2|].
  split.
  { destruct (Z.eq_dec (Z.of_nat (length b1)) 0) as [E|NE].
    - assert (b1 = []) by (destruct b1; [reflexivity| cbn in E; lia]). subst b1. exact (bytes_at_nil_any m m' p1 B1).
    - apply (bytes_at_agree asegs m m' _ _ B1). apply AGs. intros x Hx. lia. }
  split.
  { destruct (Z.eq_dec (Z.of_nat (length b1)) 0) as [E|NE].
    - assert (b2 = []) by (destruct b2; [reflexivity| cbn [length] in HL; lia]). subst b2. exact (bytes_at_nil_any m m' p2 B2).
    - apply (bytes_at_agree asegs m m' _ _ B2). apply AGs. intros x Hx. rewrite <- HL in Hx. lia. }
  split; [lia|]. split; [lia|].
  split; [apply (chk_ok_agree m m' p1 _ C1 P1 R1); apply AGs; intros x Hx; lia|].
  split; [apply (chk_ok_agree m m' p2 _ C2 P2 R2); apply AGs; intros x Hx; lia|].
  split; [apply (m2s_cells_agree m m' M2S); [apply AGs; intros x Hx; lia| exact WM]|].
  apply (icells_mcmp_agree m m' IC); [apply AGs; intros x Hx; lia| exact WM].
Qed.

(* [comment removed for export] *)
Definition real_cmp_stmt (fn D : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem)
         (p1 p2 : Z) (b1 b2 : list byte) (lo : Z),
  a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 (Z.of_nat (length b1)) ->
  cmp_pre m p1 p2 b1 b2 (bv_unsigned sp) lo ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - D -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 -> mem_inv asegs m ->
  evt asegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (mcmp_res b1 b2) [(bv_unsigned sp - D, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 fn) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition mcc_stmt (fn D : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem)
         (p1 p2 : Z) (b1 b2 : list byte) (lo : Z),
  a1 = Z_to_bv 64 fn -> a2 = Z_to_bv 64 p1 -> a3 = Z_to_bv 64 p2 -> a4 = Z_to_bv 64 (Z.of_nat (length b1)) ->
  cmp_pre m p1 p2 b1 b2 (bv_unsigned sp) lo ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - D -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 -> mem_inv asegs m ->
  evt asegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (mcmp_res b1 b2) [(bv_unsigned sp - D, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ae574) fc None m (seg_rom asegs)).

Section Common.
Hypothesis RIP : rip_stmt.
Variables (fn D : Z).
Hypothesis FN : 0 <= fn < 2^47 /\ fn mod 2 = 0.
Hypothesis D0 : 0 <= D.
Hypothesis REALF : real_cmp_stmt fn D.

Theorem mcc_spec : mcc_stmt fn (MCC_FRAME + Z.max 80 D).
Proof using RIP FN D0 REALF.
  unfold mcc_stmt. intros until lo. intros -> -> -> -> PRE ST LO LOLO SPH MI.
  unfold kHighShadowEnd in *.
  set (n := Z.of_nat (length b1)) in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - (2192 + Z.max 80 D), usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -2192)) = usp + -2192) by (apply unsigned_lit; lia).
  pose proof PRE as (HL & NB & P1 & P2 & R1 & R2 & B1 & B2 & S1 & S2 & C1 & C2 & M2S & IC).
  assert (PRE0 : keep (cmp_pre m p1 p2 b1 b2 usp lo)) by exact PRE. clear PRE B1 B2 C1 C2 M2S.
  call (mcc_prologue usp p1 p2 n (Z_to_bv 64 fn)); [exact ST| lia| unfold kHighShadowEnd; lia| lia| exact IC| exact MI|].
  rename PC into FRs. rename PC0 into FR. rename POST into ST1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (cmp_pre_munch m mm p1 p2 b1 b2 usp (usp - 2192) lo _ _ PRE0 MU WM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold kHighShadowEnd; lia)) as PRE1 end.
  destruct PRE1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C1 & _ & M2S & IC1).
  call (mcc_chk1 RIP usp p1 n); [exact ST1| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact C1| exact M2S| exact IC1| assumption|].
  clear C1 M2S IC1.
  lazymatch goal with H : stk asegs _ lo (usp + -2192) |- _ => rename H into ST2 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (cmp_pre_munch m mm p1 p2 b1 b2 usp (usp - 2192) lo _ _ PRE0 MU WM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold kHighShadowEnd; lia)) as PRE1 end.
  destruct PRE1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C2 & M2S & IC1).
  call (mcc_chk2 RIP usp p2 n); [exact ST2| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact C2| exact M2S| exact IC1| assumption|].
  clear C2 M2S IC1.
  lazymatch goal with H : stk asegs _ lo (usp + -2192) |- _ => rename H into ST3 end.
  do 3 lstep.
  lstep. rewrite (ret_pc_even fn) by (destruct FN; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (cmp_pre_munch m mm p1 p2 b1 b2 usp (usp + -2192) lo _ _ PRE0 MU WM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold kHighShadowEnd; lia)) as PRE1 end.
  rewrite <- EU2 in PRE1.
  pose proof REALF as RF. unfold real_cmp_stmt in RF.
  call RF; [reflexivity| reflexivity| reflexivity| exact PRE1| rewrite EU2; exact ST3| rewrite EU2; lia| unfold kHighShadowEnd; lia| rewrite EU2; lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2 in H; rename H into ST4 end.
  do 25 lstep.
  release_frame FR ST4 (usp + -104). release_frame FRs ST4 usp.
  lstep.
  unfold frame_post. sys_finish.
  rewrite ?EU.
  exact ST4.
Qed.
End Common.
