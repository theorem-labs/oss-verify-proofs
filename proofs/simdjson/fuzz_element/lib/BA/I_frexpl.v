(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s R_thread I_consts I_qck. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import X_atexit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import I_ikit I_memchrw I_memcmpw I_memcpyw I_memsetw I_strnlenw. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import I_lkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_achk F_frexpl Fe_icalls R_strncasecmp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation mem := (word -> option byte).
Notation IFX_FRAME := 2144%Z (only parsing).

Lemma ifx_sloop : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a2' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 e) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x6eaf8) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6eae8) fc None m (seg_rom asegs)).
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

Section WithRIP.
Hypothesis RIP : rip_stmt.

Lemma ifx_rip : forall (sp p : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - IFREXPL_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> p + 4 < 2^63 ->
  acc asegs m p 4 -> rng_ok p 4 -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 (Z_to_bv 64 p) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x6e9e0) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2240, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6eb00) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 DN AC RO M2S MI.
  unfold IFREXPL_DEPTH in LO.
  pose proof (munch_refl [(sp - 2240, sp - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2144)) = sp + -2144) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  destruct (RO ltac:(lia)) as (RIM & N40).
  do 3 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. if_true.
  apply evt_done. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma ifx_chk : forall (sp p : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - IFREXPL_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> p + 4 < 2^63 ->
  chk_ok m p 4 -> m2s_cells m -> icells_cq m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 (Z_to_bv 64 p) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x6e9e0) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2240, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6e9a8) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 DN (AC & QW & RO) M2S (G2 & SHC) MI.
  unfold kHighShadowEnd in *. unfold IFREXPL_DEPTH in LO.
  pose proof (munch_refl [(sp - 2240, sp - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
  do 10 lstep.
  unfold al8, shad, SHB in W1, W2.
  assert (E1 : Z.land (Z.land (2147450880 + p ≫ 3) 18446744073709551615) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by (Z.div_mod_to_equations; lia).
    rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
    rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
  assert (E2 : Z.land (Z.land (2147450880 + (p + 3) ≫ 3) 18446744073709551615) 18446744073709551608 = 8 * (((p + 3) / 8 + 2147450880) / 8)).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by (Z.div_mod_to_equations; lia).
    rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
    rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
  rewrite E1, E2. clear E1 E2.
  replace (p + 4 - 1) with (p + 3) in W2 by lia.
  lstep. lstep. lstep. lstep.
  if_cases K.
  +
    rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    replace (2147450880 + (p + 3) / 8) with ((p + 3) / 8 + 2147450880) by lia.
    replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
    pose proof (acc_shadow_bytes m p 4 AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
    destruct (SB ((p + 3) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
    pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
    do 6 lstep. lstep.
    if_cases K2.
    *
      lstep. lstep. if_cases K3.
      -- apply evt_done. do 17 eexists. split; [reflexivity|].
         split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
      -- apply (ifx_rip sp p); try assumption; try lia.
    * zify_cond K2.
      eapply evt_cut.
      { eapply (ifx_sloop (Z.to_nat ((p + 3) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
        - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
        - Z.div_mod_to_equations; lia.
        - Z.div_mod_to_equations; lia.
        - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
        - assumption. }
      intros ms' (a2' & a3' & ->).
      lstep. lstep. if_cases K3.
      -- apply evt_done. do 17 eexists. split; [reflexivity|].
         split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
      -- apply (ifx_rip sp p); try assumption; try lia.
  + apply evt_done. do 17 eexists. split; [reflexivity|].
         split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

Lemma ifx_stk_wmono : forall (m m' : mem) lo hi, stk asegs m lo hi -> wmono asegs m m' -> stk asegs m' lo hi.
Proof.
  intros m m' lo hi (S1 & S2 & S3) WM. split; [exact S1|]. split; [exact S2|]. intros a Ha. destruct (S3 a Ha) as [V _].
  pose proof (WM _ V) as V'. split; [exact V'| exact (wview_mrd_A m' _ V')].
Qed.

Theorem ifrexpl_proof : ifrexpl_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m E lo
    ST LO LOLO SPH MI CE SEP CHK (IC & IMS & ISN & M2S) IFX PRE.
  pose proof IC as (G2 & _ & _ & SHC & _). pose proof ISN as (_ & _ & _ & _ & _ & AI & _). unfold ifx_real in IFX.
  pose proof M2S as (M2a & M2b & M2c).
  unfold IFREXPL_DEPTH, kHighShadowEnd, e_frexpl_stub in *.
  set (usp := bv_unsigned sp) in *. set (p := bv_unsigned a2) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (EA2 : a2 = Z_to_bv 64 p) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range 64 a2) as RP. unfold bv_modulus in RP. change (2 ^ Z.of_N 64) with (2 ^ 64) in RP. fold p in RP.
  pose proof (chkr_bound m p 4 CHK) as (P0 & P4). unfold kHighMemEnd in P4. pose proof (chkr_chk_ok m p 4 CHK) as CK.
  pose proof CHK as (_ & _ & RIM & _). unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM.
  rewrite ESP, EA2.
  pose proof (munch_refl [(usp - 2240, usp); (p, p + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2144 : bv_unsigned (Z_to_bv 64 (usp + -2144)) = usp + -2144) by (apply unsigned_lit; lia).
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (STK : keep (stk asegs m lo usp)) by exact ST.
  lstep.
  carve_frame 64%nat ST. rename FR into FRs. carve_frame 2080%nat ST.
  do 9 lstep. lstep. lstep. do 3 lstep. lstep.
  call try_init_spec; [exact AI| rewrite EU2144; exact ST| rewrite EU2144; lia| rewrite ?EU2144; lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2144 in H; rename H into ST2 end.
  lstep. if_false.
  lstep. lstep. lstep.
  assert (EUm4 : bv_unsigned (Z_to_bv 64 (-4)) = 2^64 - 4) by reflexivity.
  lstep. if_false.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CK1 : chk_ok mm p 4)
      by (apply (chk_ok_agree m mm p 4 CK ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| split; [lia| exact I]]);
    assert (M2S1 : m2s_cells mm) by (split; [| split]; assumption);
    assert (ICQ1 : icells_cq mm) by (split; assumption)
  end.
  call (ifx_chk usp p); [exact ST2| unfold IFREXPL_DEPTH; lia| unfold kHighShadowEnd; lia| lia| lia| lia| exact CK1| exact M2S1| exact ICQ1| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2144) |- _ => rename H into ST3 end.
  clear CK1 M2S1 ICQ1.

  lstep. lstep. lstep. lstep. lstep. lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (STf : stk asegs mm (bv_unsigned (Z_to_bv 64 (usp + -2144)) - 32) (bv_unsigned (Z_to_bv 64 (usp + -2144))))
      by (rewrite EU2144; destruct ST3 as (S1 & S2 & S3); split; [lia|]; split; [lia|]; intros a Ha; apply S3; lia);
    call (frexpl_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm E STf);
    [assumption| rewrite EUp; exact CE| rewrite EUp, EU2144; lia| rewrite EU2144; lia| exact PRE|] end.
  rewrite EUp in *.
  lazymatch goal with H : stk asegs _ (bv_unsigned _ - 32) _ |- _ => clear H end.

  lstep. do 8 lstep. lstep. lstep.
  apply evt_done. unfold ifrexpl_post, IFREXPL_DEPTH. rewrite !EU.
  lazymatch goal with P : frexpl FREXPL_FUEL _ E = Some (?xr, ?er) |- _ => exists xr, er end.
  do 13 eexists. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [unfold keep in STK; exact (ifx_stk_wmono m _ lo usp STK WM)|].
  split; [assumption|]. assumption.
Qed.

End WithRIP.

Definition ifrexpl_of_rip : rip_stmt -> ifrexpl_stmt := ifrexpl_proof.
