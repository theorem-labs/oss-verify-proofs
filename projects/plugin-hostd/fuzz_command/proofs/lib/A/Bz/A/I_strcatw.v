(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated unchanged from an earlier relocation of this file for fuzz_command, for the image this tree pins (fuzz_command.asan sha256 c0661b96). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Bz/A/I_strcpyw.v, with its addresses and numbers changed; 503 of its 733 lines of code are new or changed and 217 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A Require Import Shadow IcptSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A Require Import R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit I_pck I_strncmpw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition i_strcat : Z := 0x4c060.

Lemma asan_init_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  rw_cells asegs m 0xb1d98 [C1 (Z_to_bv 8 1)] ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0x5f7000 <= lo ->
  mem_inv asegs m ->
  evt asegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 [(bv_unsigned sp - 16, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5f2fc) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros AI ST LO LOLO MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  do 9 lstep. if_false.
  do 3 lstep.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  unfold frame_post. sys_finish.
Qed.

Lemma catloop1 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a2' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 e) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x4c3c0) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4c3b0) fc None m (seg_rom asegs)).
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

Lemma catloop2 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x4c488) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4c478) fc None m (seg_rom asegs)).
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

Lemma catloop3 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x4c560) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4c550) fc None m (seg_rom asegs)).
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
Definition icells_cat (m : mem) : Prop :=
  ro_cells asegs m 0xa8248 [C8 (Z_to_bv 64 0x9f038)]
  /\ ro_cells asegs m 0xa63e8 [C8 (Z_to_bv 64 0xae8b8)]
  /\ ro_cells asegs m 0xae8d5 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0xa63e0 [C8 (Z_to_bv 64 0x142be8)]
  /\ ro_cells asegs m 0x142cdd [C1 (Z_to_bv 8 0)]
  /\ ro_cells asegs m 0x142ce3 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0xa8110 [C8 (Z_to_bv 64 0x9f3cc)]
  /\ ro_cells asegs m 0xa8250 [C8 (Z_to_bv 64 0x9f1cc)].

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

Section WithRIP.
Hypothesis RIP : rip_stmt.

Definition cat_chk1_post (sp p L : Z) (gp tp s2 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2176)) gp tp t0' t1' t2' (Z_to_bv 64 sp) (Z_to_bv 64 p) a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 (Z_to_bv 64 (L + 1)) (Z_to_bv 64 L) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x4c118) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2256, sp - 2176)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2176).

Lemma cat_rip1 : forall (sp p L : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2176) -> lo <= sp - 2256 -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 <= L -> p + L + 1 < 2^63 ->
  acc asegs m p (L + 1) -> rng_ok p (L + 1) -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (cat_chk1_post sp p L gp tp s2 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2176)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 (L + 1)) (Z_to_bv 64 L) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4c3c8) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2256, sp - 2176)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2176)) = sp + -2176) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO ltac:(lia)) as (RIM & N40).
  do 3 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. if_true.
  apply evt_done. unfold cat_chk1_post. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma cat_chk1 : forall (sp p L : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2176) -> lo <= sp - 2256 -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 <= L -> p + L + 1 < 2^63 ->
  chk_ok m p (L + 1) -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (cat_chk1_post sp p L gp tp s2 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2176)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 (L + 1)) (Z_to_bv 64 L) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4c0d0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN (AC & QW & RO) (G2 & SHC & HM) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2256, sp - 2176)] m) as MU. pose proof (wmono_refl asegs m) as WM.
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
        -- apply evt_done. unfold cat_chk1_post. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (cat_rip1 sp p L); try assumption; unfold kHighShadowEnd; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (catloop1 (Z.to_nat ((p + (L + 1) - 1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a2' & a3' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold cat_chk1_post. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (cat_rip1 sp p L); try assumption; unfold kHighShadowEnd; lia.
    + apply evt_done. unfold cat_chk1_post. do 17 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - if_true. lstep. if_true.
    apply (cat_rip1 sp p L); try assumption; unfold kHighShadowEnd; lia.
Qed.

Definition cat_chk3_post (sp p L : Z) (gp tp s1 va0 s2 s6 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2176)) gp tp t0' t1' t2' (Z_to_bv 64 sp) s1 va0 a1' a2' a3' a4' a5' a6' a7'
                    s2 (Z_to_bv 64 (L + 1)) (Z_to_bv 64 L) s5' s6 s7' s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x4c1cc) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2256, sp - 2176)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2176).

Lemma cat_rip3 : forall (sp p L : Z) (ra gp tp t0 t1 t2 va0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2176) -> lo <= sp - 2256 -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 <= L -> p + L + 1 < 2^63 ->
  acc asegs m p (L + 1) -> rng_ok p (L + 1) -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (cat_chk3_post sp p L gp tp s1 va0 s2 s6 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2176)) gp tp t0 t1 t2 (Z_to_bv 64 sp) s1 va0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 (L + 1)) (Z_to_bv 64 L) (Z_to_bv 64 p) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4c568) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2256, sp - 2176)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2176)) = sp + -2176) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO ltac:(lia)) as (RIM & N40).
  do 4 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. lstep. lstep. if_true.
  apply evt_done. unfold cat_chk3_post. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma cat_chk3 : forall (sp p L : Z) (ra gp tp t0 t1 t2 va0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2176) -> lo <= sp - 2256 -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 <= L -> p + L + 1 < 2^63 ->
  chk_ok m p (L + 1) -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (cat_chk3_post sp p L gp tp s1 va0 s2 s6 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2176)) gp tp t0 t1 t2 (Z_to_bv 64 sp) s1 va0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 (L + 1)) (Z_to_bv 64 L) (Z_to_bv 64 p) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4c184) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN (AC & QW & RO) (G2 & SHC & HM) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2256, sp - 2176)] m) as MU. pose proof (wmono_refl asegs m) as WM.
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
        -- apply evt_done. unfold cat_chk3_post. do 18 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (cat_rip3 sp p L); try assumption; unfold kHighShadowEnd; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (catloop3 (Z.to_nat ((p + (L + 1) - 1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a3' & a4' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold cat_chk3_post. do 18 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (cat_rip3 sp p L); try assumption; unfold kHighShadowEnd; lia.
    + apply evt_done. unfold cat_chk3_post. do 18 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - if_true. lstep. if_true.
    apply (cat_rip3 sp p L); try assumption; unfold kHighShadowEnd; lia.
Qed.

Lemma cat_sub65_false : forall n, 1 <= n <= 64 -> negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (n + -65))) = false.
Proof.
  intros n Hn. apply Bool.negb_false_iff. unfold bv_ltu.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  apply Z.ltb_lt. rewrite !Z.mod_eq by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma cat_sub65_true : forall n, (n = 0 \/ 64 < n) -> n < 2^63 -> negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (n + -65))) = true.
Proof.
  intros n Hn Hn'. apply Bool.negb_true_iff. unfold bv_ltu.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  apply Z.ltb_ge. rewrite !Z.mod_eq by lia. Z.div_mod_to_equations. lia.
Qed.

Definition cat_chk2_post (sp p n : Z) (gp tp va0 s1 s3 s4 s7 s8 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s6' s10' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2176)) gp tp t0' t1' t2' (Z_to_bv 64 sp) s1 va0 a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 p) s3 s4 (Z_to_bv 64 n) s6' s7 s8 s9 s10' s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x4c180) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2256, sp - 2176)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2176).

Lemma cat_rip2 : forall (sp p n : Z) (ra gp tp t0 t1 t2 va0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2176) -> lo <= sp - 2256 -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 < n -> p + n < 2^63 ->
  acc asegs m p n -> rng_ok p n -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (cat_chk2_post sp p n gp tp va0 s1 s3 s4 s7 s8 s9 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2176)) gp tp t0 t1 t2 (Z_to_bv 64 sp) s1 va0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4c490) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2256, sp - 2176)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2176)) = sp + -2176) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO ltac:(lia)) as (RIM & N40).
  do 4 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. lstep. lstep. if_true.
  apply evt_done. unfold cat_chk2_post. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma cat_chk2 : forall (sp p n : Z) (ra gp tp t0 t1 t2 va0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2176) -> lo <= sp - 2256 -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 <= n -> p + n < 2^63 ->
  chk_ok m p n -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (cat_chk2_post sp p n gp tp va0 s1 s3 s4 s7 s8 s9 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2176)) gp tp t0 t1 t2 (Z_to_bv 64 sp) s1 va0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4c130) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN (AC & QW & RO) (G2 & SHC & HM) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2256, sp - 2176)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (M2S : m2s_cells m) by (split; [exact G2| split; [exact SHC| exact HM]]). unfold SHB in SHC.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EUsp : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  lstep. if_false. lstep. lstep. lstep.
  destruct (Z_lt_le_dec n 65) as [LE64|GE65].
  - destruct (Z.eq_dec n 0) as [NZ0|NN0].
    + subst n. if_true. lstep. if_false. lstep.
      apply evt_done. unfold cat_chk2_post. do 18 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
    + if_false_by (cat_sub65_false n ltac:(lia)).
      destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
      do 11 lstep.
      unfold al8, shad, SHB in W1, W2.
      assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
      { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
        rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
      assert (E2 : Z.land ((2147450880 + (p + n + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                   = 8 * (((p + n - 1) / 8 + 2147450880) / 8)).
      { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
        rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
      rewrite E1, E2. clear E1 E2.
      lstep. lstep. lstep. lstep.
      if_cases K.
      * rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
        replace (2147450880 + (p + n + -1) / 8) with ((p + n - 1) / 8 + 2147450880) by lia.
        replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
        pose proof (acc_shadow_bytes m p n AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
        destruct (SB ((p + n - 1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
        pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
        do 6 lstep. lstep.
        if_cases K2.
        -- lstep. lstep. if_cases K3.
           ++ apply evt_done. unfold cat_chk2_post. do 18 eexists. split; [reflexivity|].
              split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
           ++ apply (cat_rip2 sp p n); try assumption; unfold kHighShadowEnd; lia.
        -- zify_cond K2.
           eapply evt_cut.
           { eapply (catloop2 (Z.to_nat ((p + n - 1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
             - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
             - Z.div_mod_to_equations; lia.
             - Z.div_mod_to_equations; lia.
             - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
             - assumption. }
           intros ms' (a3' & a4' & ->).
           lstep. lstep. if_cases K3.
           ++ apply evt_done. unfold cat_chk2_post. do 18 eexists. split; [reflexivity|].
              split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
           ++ apply (cat_rip2 sp p n); try assumption; unfold kHighShadowEnd; lia.
      * apply evt_done. unfold cat_chk2_post. do 18 eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - assert (HB65 : n = 0 \/ 64 < n) by lia.
    if_true_by (cat_sub65_true n HB65 ltac:(lia)). lstep. if_true.
    apply (cat_rip2 sp p n); try assumption; unfold kHighShadowEnd; lia.
Qed.

End WithRIP.

Definition iscat_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d p : Z) (dstr str slack : list byte) (W : list (Z * Z)) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ bytes_at asegs m' d (dstr ++ str ++ [z8])
    /\ rw_cells asegs m' (d + Z.of_nat (length dstr)) [CB (S (length str)) (str ++ [z8])]
    /\ bytes_at asegs m' p (str ++ z8 :: slack).

Definition strcat_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (dstr str slack : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2256, bv_unsigned sp);
              (bv_unsigned a0 + Z.of_nat (length dstr), bv_unsigned a0 + Z.of_nat (length dstr) + Z.of_nat (length str) + 1)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ bytes_at asegs m' (bv_unsigned a0) (dstr ++ str ++ [z8])
    /\ rw_cells asegs m' (bv_unsigned a0 + Z.of_nat (length dstr)) [CB (S (length str)) (str ++ [z8])]
    /\ bytes_at asegs m' (bv_unsigned a1) (str ++ z8 :: slack).

Definition strcat_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (dstr dslack str slack junk : list byte) (lo : Z),
  let D := bv_unsigned a0 in let P := bv_unsigned a1 in
  let k := Z.of_nat (length dstr) in let N := Z.of_nat (length str) in
  bytes_at asegs m D (dstr ++ z8 :: dslack) -> ~ In z8 dstr ->
  rw_cells asegs m (D + k) [CB (S (length str)) junk] ->
  bytes_at asegs m P (str ++ z8 :: slack) -> ~ In z8 str ->
  (P + (N + 1 + Z.of_nat (length slack)) <= D + k \/ D + k + N + 1 <= P) ->
  stk asegs m lo (bv_unsigned sp) -> lo + 2256 <= bv_unsigned sp ->
  kHighShadowEnd < lo -> bv_unsigned sp <= 2^47 ->
  (D + (k + 1 + Z.of_nat (length dslack)) <= lo \/ bv_unsigned sp <= D) ->
  (D + k + N + 1 <= lo \/ bv_unsigned sp <= D + k) ->
  (P + (N + 1 + Z.of_nat (length slack)) <= lo \/ bv_unsigned sp <= P) ->
  (P + N + 1 <= D \/ D + k + N + 1 <= P) ->
  (- (D + k + 1)) mod 8 <= Z.of_nat (length dslack) ->
  (- (P + N + 1)) mod 8 <= Z.of_nat (length slack) ->
  mem_inv asegs m ->
  k + N + 1 <= 2^40 ->
  chk_ok m D (k + 1) -> chk_ok m P (N + 1) -> chk_ok m (D + k) (N + 1) ->
  m2s_cells m ->
  rw_cells asegs m 0xb1d98 [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0xa8110 [C8 (Z_to_bv 64 0x9f3cc)] ->
  ro_cells asegs m 0xa63e0 [C8 (Z_to_bv 64 0x142be8)] ->
  ro_cells asegs m 0x142ce3 [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0xa8250 [C8 (Z_to_bv 64 0x9f1cc)] ->
  ro_cells asegs m 0xa63e8 [C8 (Z_to_bv 64 0xae8b8)] ->
  ro_cells asegs m 0xae8d5 [C1 (Z_to_bv 8 1)] ->
  evt asegs (strcat_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 dstr str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9f038) fc None m (seg_rom asegs)).

Section WithRIPSC.
Hypothesis RIP : rip_stmt.
Hypothesis SC : strcat_stmt.
Lemma iscat_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (d p : Z) (dstr dslack str slack junk : list byte) (lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 p ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 4432 -> kHighShadowEnd < lo -> bv_unsigned sp <= 2^47 ->
  0 <= p -> 0 <= d ->
  p + Z.of_nat (length str) + 1 <= 2^47 ->
  d + Z.of_nat (length dstr) + Z.of_nat (length str) + 1 <= 2^47 ->
  Z.of_nat (length dstr) + Z.of_nat (length str) + 1 <= 2^40 ->
  bytes_at asegs m d (dstr ++ z8 :: dslack) -> ~ In z8 dstr ->
  bytes_at asegs m p (str ++ z8 :: slack) -> ~ In z8 str ->
  rw_cells asegs m (d + Z.of_nat (length dstr)) [CB (S (length str)) junk] ->
  (p + (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) <= lo \/ bv_unsigned sp <= p) ->
  (d + (Z.of_nat (length dstr) + 1 + Z.of_nat (length dslack)) <= lo \/ bv_unsigned sp <= d) ->
  (d + Z.of_nat (length dstr) + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= d + Z.of_nat (length dstr)) ->
  (p + (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) <= d + Z.of_nat (length dstr)
   \/ d + Z.of_nat (length dstr) + Z.of_nat (length str) + 1 <= p) ->
  (p + Z.of_nat (length str) + 1 <= d \/ d + Z.of_nat (length dstr) + Z.of_nat (length str) + 1 <= p) ->
  (- (d + Z.of_nat (length dstr) + 1)) mod 8 <= Z.of_nat (length dslack) ->
  (- (p + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  chk_ok m p (Z.of_nat (length str) + 1) ->
  chk_ok m d (Z.of_nat (length dstr)) ->
  chk_ok m d (Z.of_nat (length dstr) + 1) ->
  chk_ok m (d + Z.of_nat (length dstr)) (Z.of_nat (length str) + 1) ->
  rw_cells asegs m 0xb1d98 [C1 (Z_to_bv 8 1)] -> icells_cat m -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (iscat_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d p dstr str slack
                 [(d + Z.of_nat (length dstr), d + Z.of_nat (length dstr) + Z.of_nat (length str) + 1);
                  (bv_unsigned sp - 4432, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 i_strcat) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros -> -> ST LO LOLO SPH P0 D0 PB DB KN DS DNZ SRC NZ WR SEPsrc SEPdst SEPdk OVL SEPpd DPAD PAD CKS CKD CKDk CKW AI ICP M2S MI.
  unfold kHighShadowEnd, i_strcat in *.
  set (N := Z.of_nat (length str)) in *.
  set (k := Z.of_nat (length dstr)) in *.
  set (usp := bv_unsigned sp) in *.
  assert (FL : length (str ++ z8 :: slack) = (length str + S (length slack))%nat) by (rewrite length_app; cbn [length]; lia).
  assert (FLd : length (dstr ++ z8 :: dslack) = (length dstr + S (length dslack))%nat) by (rewrite length_app; cbn [length]; lia).
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof ICP as (RSCAT & RGAF & RAF & RGCF & RCF245 & RCF251 & RSLEN & RSCPY).
  assert (EUs : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EU2176 : bv_unsigned (Z_to_bv 64 (usp + -2176)) = usp + -2176) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(usp - 4432, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(usp - 4432, usp)] m) as MUs.
  pose proof SRC as SRCm. change (parked (bytes_at asegs m p (str ++ z8 :: slack))) in SRCm.
  pose proof DS as DSm. change (parked (bytes_at asegs m d (dstr ++ z8 :: dslack))) in DSm.
  carve_frame 96%nat ST. rename FR into FRs. carve_frame 2080%nat ST.
  zidle_beginz usp 2176%Z MUz1 WMz1.
  xsteps_to 0x5f2fc%Z.
  zidle_end MUz1 WMz1.
  call asan_init_spec; [exact AI| rewrite EU2176; exact ST| lia| lia| assumption|].
  rewrite EU2176 in *. lazymatch goal with H : stk asegs _ lo (usp + -2176) |- _ => rename H into ST1 end.
  xsteps_to 0x69b10%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (bytes_at_transport asegs _ m mm _ _ SRCm MUs) as SRC1; cbn [disjoint_from] in SRC1; specialize (SRC1 ltac:(split; [lia| exact I]))
  end.
  call internal_strlen_spec; [reflexivity| split; [| exact NZ]| assumption|].
  { apply (proj1 (proj1 (bytes_at_app asegs _ p (str ++ [z8]) slack) ltac:(rewrite <- app_assoc; exact SRC1))). }
  fold N. do 2 lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGL : agree_on (fun x => 0 <= x < 0x1000000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    pose proof (m2s_cells_agree m mm M2S AGL ltac:(assumption)) as M2S1;
    pose proof (chk_ok_agree m mm p _ CKS ltac:(lia) ltac:(lia) AGS) as CKS1; clear AGL AGS
  end.
  call (cat_chk1 RIP usp p N); try exact CKS1; try exact M2S1; try eassumption; try (unfold kHighShadowEnd; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (bytes_at_transport asegs _ m mm _ _ DSm MUs) as DS1; cbn [disjoint_from] in DS1; specialize (DS1 ltac:(split; [lia| exact I]))
  end.
  xsteps_to 0x69b10%Z.
  call internal_strlen_spec; [reflexivity| split; [| exact DNZ]| assumption|].
  { apply (proj1 (proj1 (bytes_at_app asegs _ d (dstr ++ [z8]) dslack) ltac:(rewrite <- app_assoc; exact DS1))). }
  fold k. do 4 lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGL : agree_on (fun x => 0 <= x < 0x1000000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    pose proof (m2s_cells_agree m mm M2S AGL ltac:(assumption)) as M2Sb;
    pose proof (chk_ok_agree m mm d _ CKD ltac:(lia) ltac:(lia) AGS) as CKDb; clear AGL AGS
  end.
  call (cat_chk2 RIP usp d k); try exact CKDb; try exact M2Sb; try eassumption; try (unfold kHighShadowEnd; lia).
  lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGL : agree_on (fun x => 0 <= x < 0x1000000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
    pose proof (m2s_cells_agree m mm M2S AGL ltac:(assumption)) as M2Sc;
    pose proof (chk_ok_agree m mm (d + k) _ CKW ltac:(lia) ltac:(lia) AGS) as CKWb; clear AGL AGS
  end.
  call (cat_chk3 RIP usp (d + k) N); try exact CKWb; try exact M2Sc; try eassumption; try (unfold kHighShadowEnd; lia).
  lstep. if_cases KB0.
  - do 5 lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGL : agree_on (fun x => 0 <= x < 0x1000000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
      assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
      pose proof (m2s_cells_agree m mm M2S AGL ltac:(assumption)) as M2Sf;
      pose proof (chk_ok_agree m mm d _ CKDk ltac:(lia) ltac:(lia) AGS) as CKDkf;
      pose proof (chk_ok_agree m mm p _ CKS ltac:(lia) ltac:(lia) AGS) as CKSf;
      pose proof (chk_ok_agree m mm (d + k) _ CKW ltac:(lia) ltac:(lia) AGS) as CKWf; clear AGL AGS
    end.
    pose proof SC as SCs. unfold strcat_stmt in SCs. cbv zeta in SCs.
    eapply evt_cut;
      [ eapply SCs;
        (rewrite ?EUd, ?EUs, ?EU2176;
         try exact DS; try exact SRC; try exact WR; try exact DNZ; try exact NZ;
         try exact M2Sf; try exact CKDkf; try exact CKSf; try exact CKWf;
         try eassumption; try assumption; try (unfold kHighShadowEnd in *; lia);
         try (destruct OVL as [HH|HH]; solve [left; lia | right; lia]);
         try (destruct SEPdst as [HH|HH]; solve [left; lia | right; lia]);
         try (destruct SEPdk as [HH|HH]; solve [left; lia | right; lia]);
         try (destruct SEPsrc as [HH|HH]; solve [left; lia | right; lia]);
         try (destruct SEPpd as [HH|HH]; solve [left; lia | right; lia]);
         try lia)
      | intros msSC POSTsc;
        destruct POSTsc as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MUsc & WMsc & MIsc & STsc & DSTb & RWc & SRCb);
        subst msSC; rewrite EU2176 in STsc; rewrite ?EUd, ?EU2176 in MUsc;
        replace (ret_pc (Z_to_bv 64 311800)) with (Z_to_bv 64 311800) by (symmetry; apply ret_pc_even; [lia | reflexivity]);
        pose proof (rw_cells_transport asegs _ _ m' _ _ FRs MUsc WMsc) as FRsM;
          cbn [disjoint_from cells_size csize Nat.add] in FRsM;
          specialize (FRsM ltac:(split; [ lia | split; [ destruct SEPdk as [HH|HH]; lia | exact I ] ]));
        do 13 lstep;
        pose proof (rw_cells_transport asegs _ _ m' _ _ FR MUsc WMsc) as FRM;
          cbn [disjoint_from cells_size csize Nat.add] in FRM;
          specialize (FRM ltac:(split; [ lia | split; [ destruct SEPdk as [HH|HH]; lia | exact I ] ]));
        release_frame FRM STsc (usp + -96);
        release_frame FRsM STsc usp;
        lstep; lstep;
        unfold iscat_post; sys_finish;
        [ lazymatch type of MU with munch _ _ ?mpre => eapply munch_trans with (m2 := mpre) end;
          [ eapply munch_weaken; [ | exact MU ]; unfold sub_fp; cbn [outside]; intros xx Hxx; repeat split; try exact I; lia
          | eapply munch_weaken; [ | exact MUsc ]; unfold sub_fp; cbn [outside]; intros xx Hxx; repeat split; try exact I; lia ]
        | eapply wmono_trans; [ exact WM | exact WMsc ]
        | assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia); rewrite EU; exact STsc
        | rewrite EUd in DSTb; exact DSTb
        | rewrite EUd in RWc; exact RWc
        | rewrite EUs in SRCb; exact SRCb ] ].
  - do 2 lstep. lstep. if_cases KB1.
    + do 5 lstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGL : agree_on (fun x => 0 <= x < 0x1000000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
        assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
        pose proof (m2s_cells_agree m mm M2S AGL ltac:(assumption)) as M2Sf;
        pose proof (chk_ok_agree m mm d _ CKDk ltac:(lia) ltac:(lia) AGS) as CKDkf;
        pose proof (chk_ok_agree m mm p _ CKS ltac:(lia) ltac:(lia) AGS) as CKSf;
        pose proof (chk_ok_agree m mm (d + k) _ CKW ltac:(lia) ltac:(lia) AGS) as CKWf; clear AGL AGS
      end.
      pose proof SC as SCs. unfold strcat_stmt in SCs. cbv zeta in SCs.
      eapply evt_cut;
        [ eapply SCs;
          (rewrite ?EUd, ?EUs, ?EU2176;
           try exact DS; try exact SRC; try exact WR; try exact DNZ; try exact NZ;
           try exact M2Sf; try exact CKDkf; try exact CKSf; try exact CKWf;
           try eassumption; try assumption; try (unfold kHighShadowEnd in *; lia);
           try (destruct OVL as [HH|HH]; solve [left; lia | right; lia]);
           try (destruct SEPdst as [HH|HH]; solve [left; lia | right; lia]);
           try (destruct SEPdk as [HH|HH]; solve [left; lia | right; lia]);
           try (destruct SEPsrc as [HH|HH]; solve [left; lia | right; lia]);
           try (destruct SEPpd as [HH|HH]; solve [left; lia | right; lia]);
           try lia)
        | intros msSC POSTsc;
          destruct POSTsc as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MUsc & WMsc & MIsc & STsc & DSTb & RWc & SRCb);
          subst msSC; rewrite EU2176 in STsc; rewrite ?EUd, ?EU2176 in MUsc;
          replace (ret_pc (Z_to_bv 64 311800)) with (Z_to_bv 64 311800) by (symmetry; apply ret_pc_even; [lia | reflexivity]);
          pose proof (rw_cells_transport asegs _ _ m' _ _ FRs MUsc WMsc) as FRsM;
            cbn [disjoint_from cells_size csize Nat.add] in FRsM;
            specialize (FRsM ltac:(split; [ lia | split; [ destruct SEPdk as [HH|HH]; lia | exact I ] ]));
          do 13 lstep;
          pose proof (rw_cells_transport asegs _ _ m' _ _ FR MUsc WMsc) as FRM;
            cbn [disjoint_from cells_size csize Nat.add] in FRM;
            specialize (FRM ltac:(split; [ lia | split; [ destruct SEPdk as [HH|HH]; lia | exact I ] ]));
          release_frame FRM STsc (usp + -96);
          release_frame FRsM STsc usp;
          lstep; lstep;
          unfold iscat_post; sys_finish;
          [ lazymatch type of MU with munch _ _ ?mpre => eapply munch_trans with (m2 := mpre) end;
            [ eapply munch_weaken; [ | exact MU ]; unfold sub_fp; cbn [outside]; intros xx Hxx; repeat split; try exact I; lia
            | eapply munch_weaken; [ | exact MUsc ]; unfold sub_fp; cbn [outside]; intros xx Hxx; repeat split; try exact I; lia ]
          | eapply wmono_trans; [ exact WM | exact WMsc ]
          | assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia); rewrite EU; exact STsc
          | rewrite EUd in DSTb; exact DSTb
          | rewrite EUd in RWc; exact RWc
          | rewrite EUs in SRCb; exact SRCb ] ].
    + lstep. lstep. if_cases KB2.
      * exfalso. zify_cond KB1. zify_cond KB2. rewrite ?EUd, ?EUs in *. destruct SEPpd as [HH|HH]; lia.
      * do 5 lstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGL : agree_on (fun x => 0 <= x < 0x1000000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
          assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm) by (apply (agree_of_munch _ _ _ _ MUs); intros y Hy; cbn [outside]; lia);
          pose proof (m2s_cells_agree m mm M2S AGL ltac:(assumption)) as M2Sf;
          pose proof (chk_ok_agree m mm d _ CKDk ltac:(lia) ltac:(lia) AGS) as CKDkf;
          pose proof (chk_ok_agree m mm p _ CKS ltac:(lia) ltac:(lia) AGS) as CKSf;
          pose proof (chk_ok_agree m mm (d + k) _ CKW ltac:(lia) ltac:(lia) AGS) as CKWf; clear AGL AGS
        end.
        pose proof SC as SCs. unfold strcat_stmt in SCs. cbv zeta in SCs.
        eapply evt_cut;
          [ eapply SCs;
            (rewrite ?EUd, ?EUs, ?EU2176;
             try exact DS; try exact SRC; try exact WR; try exact DNZ; try exact NZ;
             try exact M2Sf; try exact CKDkf; try exact CKSf; try exact CKWf;
             try eassumption; try assumption; try (unfold kHighShadowEnd in *; lia);
             try (destruct OVL as [HH|HH]; solve [left; lia | right; lia]);
             try (destruct SEPdst as [HH|HH]; solve [left; lia | right; lia]);
             try (destruct SEPdk as [HH|HH]; solve [left; lia | right; lia]);
             try (destruct SEPsrc as [HH|HH]; solve [left; lia | right; lia]);
             try (destruct SEPpd as [HH|HH]; solve [left; lia | right; lia]);
             try lia)
          | intros msSC POSTsc;
            destruct POSTsc as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MUsc & WMsc & MIsc & STsc & DSTb & RWc & SRCb);
            subst msSC; rewrite EU2176 in STsc; rewrite ?EUd, ?EU2176 in MUsc;
            replace (ret_pc (Z_to_bv 64 311800)) with (Z_to_bv 64 311800) by (symmetry; apply ret_pc_even; [lia | reflexivity]);
            pose proof (rw_cells_transport asegs _ _ m' _ _ FRs MUsc WMsc) as FRsM;
              cbn [disjoint_from cells_size csize Nat.add] in FRsM;
              specialize (FRsM ltac:(split; [ lia | split; [ destruct SEPdk as [HH|HH]; lia | exact I ] ]));
            do 13 lstep;
            pose proof (rw_cells_transport asegs _ _ m' _ _ FR MUsc WMsc) as FRM;
              cbn [disjoint_from cells_size csize Nat.add] in FRM;
              specialize (FRM ltac:(split; [ lia | split; [ destruct SEPdk as [HH|HH]; lia | exact I ] ]));
            release_frame FRM STsc (usp + -96);
            release_frame FRsM STsc usp;
            lstep; lstep;
            unfold iscat_post; sys_finish;
            [ lazymatch type of MU with munch _ _ ?mpre => eapply munch_trans with (m2 := mpre) end;
              [ eapply munch_weaken; [ | exact MU ]; unfold sub_fp; cbn [outside]; intros xx Hxx; repeat split; try exact I; lia
              | eapply munch_weaken; [ | exact MUsc ]; unfold sub_fp; cbn [outside]; intros xx Hxx; repeat split; try exact I; lia ]
            | eapply wmono_trans; [ exact WM | exact WMsc ]
            | assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia); rewrite EU; exact STsc
            | rewrite EUd in DSTb; exact DSTb
            | rewrite EUd in RWc; exact RWc
            | rewrite EUs in SRCb; exact SRCb ] ].
Qed.

End WithRIPSC.
