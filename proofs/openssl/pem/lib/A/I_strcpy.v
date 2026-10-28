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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_thread I_consts I_qck X_atexit I_pck D_kit I_ikit I_strncmpw Str_stpcpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation ISTRCPY_DEPTH := 2224%Z (only parsing).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition icells_scpy (m : mem) : Prop :=
  ro_cells asegs m 0x5a45b0 [C8 (Z_to_bv 64 0x66a338)]           (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5a45b8 [C8 (Z_to_bv 64 0x66cb38)]         (* [comment removed for export] *)
  /\ ro_cells asegs m 0x5a7790 [C8 (Z_to_bv 64 0x526b64)]         (* [comment removed for export] *)
  /\ ro_cells asegs m 0x66a355 [C1 (Z_to_bv 8 1)]                (* [comment removed for export] *)
  /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)]      (* [comment removed for export] *)
  /\ rw_cells asegs m 0x66d818 [C1 (Z_to_bv 8 1)].               (* [comment removed for export] *)

Lemma icells_scpy_agree : forall m m', icells_scpy m -> agree_on (fun x => 0 <= x < 0x1000000) m m' -> wmono asegs m m' -> icells_scpy m'.
Proof.
  intros m m' (C1 & C2 & C3 & C4 & C5 & C6) AG WM.
  split; [| split; [| split; [| split; [| split]]]].
  - apply (ro_cells_agree asegs m m' _ _ C1). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C2). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C3). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C4). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ C5). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (rw_cells_agree asegs m m' _ _ C6); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
Qed.

(* [comment removed for export] *)
Lemma scpy_loop1 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1b6e90) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b6e80) fc None m (seg_rom asegs)).
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

Lemma scpy_loop2 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a2' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 e) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1b6f70) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b6f60) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
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
Lemma musl_strcpy : forall (d s : Z) (str slack junk : list byte) (lo : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  0 <= d < 2^63 -> 0 <= s < 2^63 ->
  bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  rw_cells asegs m d [CB (S (length str)) junk] ->
  (s + (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) <= d \/ d + Z.of_nat (length str) + 1 <= s) ->
  stk asegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 ->
  (s + (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) <= lo \/ bv_unsigned sp <= s) ->
  (d + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= d) ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists a1' a2' a3' a4' a5' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(d, d + Z.of_nat (length str) + 1); (bv_unsigned sp - 16, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' d [CB (S (length str)) (str ++ [Z_to_bv 8 0])])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x526b64) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros D0 S0 SRC NZ SLK DST OV ST L0 LO SEPS SEPD MI.
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { apply (strcpy_proof ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m str slack junk lo); rewrite ?EUd, ?EUs; assumption. }
  intros ms' (a1' & a2' & a3' & a4' & a5' & m' & -> & MU & WM & MI' & ST' & DC & _).
  rewrite EUd in MU, DC.
  exists a1', a2', a3', a4', a5', m'. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'| exact DC].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Lemma scpy_rip1 : forall (sp p n : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - ISTRCPY_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 < n -> p + n < 2^63 ->
  acc asegs m p n -> rng_ok p n -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 (Z_to_bv 64 p) a0 a1' a2' a3' a4' a5' a6' a7'
                    s2 (Z_to_bv 64 n) s4' s5 s6 s7' s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1b6bf4) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b6e98) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH P0 N0 PN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2144)) = sp + -2144) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
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
Lemma scpy_chk1 : forall (sp p len : Z) (ra gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - ISTRCPY_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 <= len -> p + len + 1 < 2^63 ->
  chk_ok m p (len + 1) -> m2s_cells m -> icells_scpy m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 (Z_to_bv 64 p) (Z_to_bv 64 len) a1' a2' a3' a4' a5' a6' a7'
                    s2 (Z_to_bv 64 (len + 1)) s4' s5 s6 s7' s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1b6bf4) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 p) (Z_to_bv 64 len) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 (len + 1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b6bac) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH P0 N0 PN (AC & QW & RO) M2S (G88 & G2 & RC & RS & SHC & AI) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 (len + 1)) = len + 1) by (apply unsigned_lit; lia).
  lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  lstep. if_false.
  lstep. lstep.
  destruct (Z_lt_le_dec len 64) as [SMALL|BIG].
  2:{ (* [comment removed for export] *)
    if_true. lstep. if_true.
    apply (scpy_rip1 sp p (len + 1)); try assumption; lia. }
  (* [comment removed for export] *)
  if_false.
  destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
  do 10 lstep.
  unfold al8, shad, SHB in W1, W2.
  assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
    rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
  assert (E2 : Z.land ((2147450880 + (len + p) ≫ 3) mod 18446744073709551616) 18446744073709551608
               = 8 * (((p + (len + 1) - 1) / 8 + 2147450880) / 8)).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
    rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + (len + 1) - 1) with (len + p) by lia. lia. }
  rewrite E1, E2. clear E1 E2.
  lstep. lstep. lstep. lstep.
  if_cases K.
  - (* [comment removed for export] *)
    rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    replace (2147450880 + (len + p) / 8) with ((len + p) / 8 + 2147450880) by lia.
    replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
    pose proof (acc_shadow_bytes m p (len + 1) AC ltac:(lia) P0) as SB. unfold shad, SHB in SB.
    replace (p + (len + 1) - 1) with (len + p) in SB by lia.
    destruct (SB ((len + p) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
    pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
    do 6 lstep. lstep.
    if_cases K2.
    + (* [comment removed for export] *)
      lstep. lstep. if_cases K3.
      * apply evt_done. do 18 eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
      * apply (scpy_rip1 sp p (len + 1)); try assumption; lia.
    + zify_cond K2.
      eapply evt_cut.
      { eapply (scpy_loop1 (Z.to_nat ((len + p) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
        - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
        - Z.div_mod_to_equations; lia.
        - Z.div_mod_to_equations; lia.
        - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
        - assumption. }
      intros ms' (a3' & a4' & ->).
      lstep. lstep. if_cases K3.
      * apply evt_done. do 18 eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
      * apply (scpy_rip1 sp p (len + 1)); try assumption; lia.
  - apply evt_done. do 18 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

(* [comment removed for export] *)
Lemma scpy_rip2 : forall (sp p n : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - ISTRCPY_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 < n -> p + n < 2^63 ->
  acc asegs m p n -> rng_ok p n -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 p) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1b6c3c) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b6f78) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH P0 N0 PN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2144)) = sp + -2144) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 3 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. if_true.
  apply evt_done. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* [comment removed for export] *)
Lemma scpy_chk2 : forall (sp p len : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - ISTRCPY_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 <= len -> p + len + 1 < 2^63 ->
  chk_ok m p (len + 1) -> m2s_cells m -> icells_scpy m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 p) (Z_to_bv 64 (len + 1)) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1b6c3c) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 len) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) (Z_to_bv 64 (len + 1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b6bf4) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH P0 N0 PN (AC & QW & RO) M2S (G88 & G2 & RC & RS & SHC & AI) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 (len + 1)) = len + 1) by (apply unsigned_lit; lia).
  lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  lstep. if_false.
  lstep. lstep.
  destruct (Z_lt_le_dec len 64) as [SMALL|BIG].
  2:{ (* [comment removed for export] *)
    if_true. lstep. if_true.
    apply (scpy_rip2 sp p (len + 1)); try assumption; lia. }
  (* [comment removed for export] *)
  if_false.
  destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
  do 10 lstep.
  unfold al8, shad, SHB in W1, W2.
  assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
    rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
  assert (E2 : Z.land ((2147450880 + (len + p) ≫ 3) mod 18446744073709551616) 18446744073709551608
               = 8 * (((p + (len + 1) - 1) / 8 + 2147450880) / 8)).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
    rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + (len + 1) - 1) with (len + p) by lia. lia. }
  rewrite E1, E2. clear E1 E2.
  lstep. lstep. lstep. lstep.
  if_cases K.
  - (* [comment removed for export] *)
    rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    replace (2147450880 + (len + p) / 8) with ((len + p) / 8 + 2147450880) by lia.
    replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
    pose proof (acc_shadow_bytes m p (len + 1) AC ltac:(lia) P0) as SB. unfold shad, SHB in SB.
    replace (p + (len + 1) - 1) with (len + p) in SB by lia.
    destruct (SB ((len + p) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
    pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
    do 6 lstep. lstep.
    if_cases K2.
    + (* [comment removed for export] *)
      lstep. lstep. if_cases K3.
      * apply evt_done. do 17 eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
      * apply (scpy_rip2 sp p (len + 1)); try assumption; lia.
    + zify_cond K2.
      eapply evt_cut.
      { eapply (scpy_loop2 (Z.to_nat ((len + p) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
        - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
        - Z.div_mod_to_equations; lia.
        - Z.div_mod_to_equations; lia.
        - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
        - assumption. }
      intros ms' (a2' & a3' & ->).
      lstep. lstep. if_cases K3.
      * apply evt_done. do 17 eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
      * apply (scpy_rip2 sp p (len + 1)); try assumption; lia.
  - apply evt_done. do 17 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

Definition istrcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d : Z) (str : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(d, d + Z.of_nat (length str) + 1); (bv_unsigned sp - ISTRCPY_DEPTH, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' d [CB (S (length str)) (str ++ [Z_to_bv 8 0])].

(* [comment removed for export] *)
Lemma scpy_tail : forall (usp d s : Z) (str slack junk fjunk : list byte)
    (ra ra' gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0' s4' s5' s6' s7' : word) F fc (m0 m : mem) (lo : Z),
  stk asegs m lo (usp + -2144) -> lo <= usp - ISTRCPY_DEPTH -> kHighShadowEnd + 8 <= lo -> usp < 2^63 ->
  rw_cells asegs m (usp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m (usp + -2144) [CB 2072 fjunk] ->
  munch [(d, d + Z.of_nat (length str) + 1); (usp - 2224, usp)] m0 m -> wmono asegs m0 m ->
  0 <= d -> 0 <= s -> d + Z.of_nat (length str) + 1 <= 2^47 -> s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= 2^47 ->
  bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^31 ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  rw_cells asegs m d [CB (S (length str)) junk] ->
  (d + Z.of_nat (length str) + 1 <= s \/ s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= d) ->
  (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ usp <= s) ->
  (d + Z.of_nat (length str) + 1 <= lo \/ usp <= d) ->
  chk_ok m s (Z.of_nat (length str) + 1) -> chk_ok m d (Z.of_nat (length str) + 1) -> m2s_cells m -> icells_scpy m -> mem_inv asegs m ->
  evt asegs (istrcpy_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d str lo m0)
    (MS (mkR ra' (Z_to_bv 64 (usp + -2144)) gp tp t0 t1 t2 s0' (Z_to_bv 64 s) (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 d) (Z_to_bv 64 (Z.of_nat (length str) + 1)) s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b6bac) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros ST LO LOLO SPH FRs FR MU WM D0 S0 DH SH SRC NZ LH SLK DST OV SEPS SEPD CS CD M2S IC MI.
  unfold kHighShadowEnd in *.
  set (len := Z.of_nat (length str)) in *.
  pose proof (munch_refl [(usp - 2224, usp - 2144)] m) as MUl. pose proof (wmono_refl asegs m) as WMl.
  pose proof IC as (G88 & G2 & RC & RS & SHC & AI).
  assert (SRC0 : keep (bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack))) by exact SRC. clear SRC.
  assert (DST0 : keep (rw_cells asegs m d [CB (S (length str)) junk])) by exact DST. clear DST.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -2144)) = usp + -2144) by (apply unsigned_lit; lia).
  assert (OFF : forall mm, munch [(usp - 2224, usp - 2144)] m mm -> wmono asegs m mm ->
            bytes_at asegs mm s (str ++ Z_to_bv 8 0 :: slack) /\ rw_cells asegs mm d [CB (S (length str)) junk]
            /\ chk_ok mm d (len + 1) /\ m2s_cells mm /\ icells_scpy mm).
  { intros mm MU' WM'.
    assert (AGs : forall P : Z -> Prop, (forall x, P x -> x < usp - 2224 \/ usp - 2144 <= x) -> agree_on P m mm).
    { intros P HP. apply (agree_of_munch _ _ _ _ MU'). intros y Hy. cbn [outside]. split; [specialize (HP y Hy); lia| exact I]. }
    split; [unfold keep in SRC0; apply (bytes_at_agree asegs m mm _ _ SRC0); apply AGs; intros x Hx;
            rewrite length_app in Hx; cbn [length] in Hx; fold len in Hx; lia|].
    split; [unfold keep in DST0; apply (rw_cells_agree asegs m mm _ _ DST0); [| exact WM']; apply AGs; intros x Hx;
            cbn [cells_size csize] in Hx; fold len in Hx; lia|].
    split; [apply (chk_ok_agree m mm d _ CD D0 ltac:(lia)); apply AGs; intros x Hx; lia|].
    split; [apply (m2s_cells_agree m mm M2S); [apply AGs; intros x Hx; lia| exact WM']|].
    apply (icells_scpy_agree m mm IC); [apply AGs; intros x Hx; lia| exact WM']. }
  call (scpy_chk1 usp s len); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CS| exact M2S| exact IC| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2144) |- _ => rename H into ST2 end.
  clear CS CD M2S IC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (OFF mm MUl WMl) as (_ & _ & CD2 & M2S2 & IC2) end.
  call (scpy_chk2 usp d len); [exact ST2| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CD2| exact M2S2| exact IC2| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2144) |- _ => rename H into ST3 end.
  clear CD2 M2S2 IC2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (OFF mm MUl WMl) as (SRC & DST & _ & _ & _) end.
  clear OFF SRC0 DST0 MUl WMl.
  do 4 lstep. lstep.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (usp + -2144)) = usp + -2144) by exact EU2.
  call (musl_strcpy d s str slack junk lo); [lia| lia| exact SRC| exact NZ| exact SLK| exact DST| fold len; lia| rewrite EU2; exact ST3| lia| rewrite EU2; lia
        | rewrite EU2; fold len; lia| rewrite EU2; fold len; lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2 in H; rename H into ST4 end.
  do 11 lstep.
  release_frame FR ST4 (usp + -72). release_frame FRs ST4 usp.
  lstep.
  unfold istrcpy_post. sys_finish.
  - rewrite (unsigned_lit usp) by lia. fold len. exact MU.
  - rewrite (unsigned_lit usp) by lia. exact ST4.
Qed.

Theorem istrcpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (d s : Z) (str slack junk : list byte) (lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRCPY_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  0 <= d -> 0 <= s -> d + Z.of_nat (length str) + 1 <= 2^47 -> s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= 2^47 ->
  bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^31 ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  rw_cells asegs m d [CB (S (length str)) junk] ->
  (d + Z.of_nat (length str) + 1 <= s \/ s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= d) ->
  (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= s) ->
  (d + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= d) ->
  chk_ok m s (Z.of_nat (length str) + 1) -> chk_ok m d (Z.of_nat (length str) + 1) -> m2s_cells m -> icells_scpy m -> mem_inv asegs m ->
  evt asegs (istrcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d str lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b6b38) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros -> -> ST LO LOLO SPH D0 S0 DH SH SRC NZ LH SLK DST OV SEPS SEPD CS CD M2S IC MI.
  unfold kHighShadowEnd in *.
  set (len := Z.of_nat (length str)) in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(d, d + len + 1); (usp - 2224, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(usp - 2224, usp)] m) as MUf.
  pose proof IC as (G88 & G2 & RC & RS & SHC & AI).
  assert (SRC0 : keep (bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack))) by exact SRC. clear SRC.
  assert (DST0 : keep (rw_cells asegs m d [CB (S (length str)) junk])) by exact DST. clear DST.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -2144)) = usp + -2144) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  assert (OFF : forall mm, munch [(usp - 2224, usp)] m mm -> wmono asegs m mm ->
            bytes_at asegs mm s (str ++ Z_to_bv 8 0 :: slack) /\ rw_cells asegs mm d [CB (S (length str)) junk]
            /\ chk_ok mm s (len + 1) /\ chk_ok mm d (len + 1) /\ m2s_cells mm /\ icells_scpy mm).
  { intros mm MU' WM'.
    assert (AGs : forall P : Z -> Prop, (forall x, P x -> x < usp - 2224 \/ usp <= x) -> agree_on P m mm).
    { intros P HP. apply (agree_of_munch _ _ _ _ MU'). intros y Hy. cbn [outside]. split; [specialize (HP y Hy); lia| exact I]. }
    split; [unfold keep in SRC0; apply (bytes_at_agree asegs m mm _ _ SRC0); apply AGs; intros x Hx;
            rewrite length_app in Hx; cbn [length] in Hx; fold len in Hx; lia|].
    split; [unfold keep in DST0; apply (rw_cells_agree asegs m mm _ _ DST0); [| exact WM']; apply AGs; intros x Hx;
            cbn [cells_size csize] in Hx; fold len in Hx; lia|].
    split; [apply (chk_ok_agree m mm s _ CS S0 ltac:(lia)); apply AGs; intros x Hx; lia|].
    split; [apply (chk_ok_agree m mm d _ CD D0 ltac:(lia)); apply AGs; intros x Hx; lia|].
    split; [apply (m2s_cells_agree m mm M2S); [apply AGs; intros x Hx; lia| exact WM']|].
    apply (icells_scpy_agree m mm IC); [apply AGs; intros x Hx; lia| exact WM']. }
  clear CS CD M2S IC.
  carve_frame 72%nat ST. rename FR into FRs. carve_frame 2072%nat ST.
  do 12 lstep. do 3 lstep.
  call try_init_spec; [exact AI| rewrite EU2; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2 in H; rename H into ST1 end.
  lstep. if_false.
  do 3 lstep. lstep. if_false.
  do 4 lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (OFF mm MUf WM) as (SRC1 & _ & _ & _ & _ & _);
    assert (CSTR : cstr_at mm s str)
      by (split; [| exact NZ]; change (str ++ Z_to_bv 8 0 :: slack) with (str ++ [z8] ++ slack) in SRC1; rewrite app_assoc in SRC1;
          apply bytes_at_app in SRC1; exact (proj1 SRC1)) end.
  clear SRC1.
  call internal_strlen_spec; [reflexivity| exact CSTR| assumption|].
  clear CSTR.
  fold len.
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (EUl1 : bv_unsigned (Z_to_bv 64 (len + 1)) = len + 1) by (apply unsigned_lit; lia).
  assert (EUdl : bv_unsigned (Z_to_bv 64 (d + (len + 1))) = d + (len + 1)) by (apply unsigned_lit; lia).
  assert (EUsl : bv_unsigned (Z_to_bv 64 (s + (len + 1))) = s + (len + 1)) by (apply unsigned_lit; lia).
  do 2 lstep. lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (OFF mm MUf WM) as (SRC & DST & CS1 & CD1 & M2S1 & IC1) end.
  if_cases KO; zify_cond KO.
  - eapply (scpy_tail usp d s str slack junk); try eassumption; fold len; lia.
  - lstep. lstep. if_false.
    eapply (scpy_tail usp d s str slack junk); try eassumption; fold len; lia.
Qed.

End WithRIP.
