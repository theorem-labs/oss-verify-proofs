(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow IcptSpec2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout R_small R_m2s R_thread I_consts I_qck D_kit I_ikit.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow IcptSpec2.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_small.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_consts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_qck.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_ikit.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition icells_cmp (m : mem) : Prop :=
  ro_cells bsegs m 0xcce28 [C8 (Z_to_bv 64 0x168068)]                                  (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xcce38 [C8 (Z_to_bv 64 0xd6538)]                                (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xceb60 [C8 (Z_to_bv 64 0xc6134); C8 (Z_to_bv 64 0xc6064)]       (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xd6538 [C8 (Z_to_bv 64 0x7fff8000)]                             (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd7218 [C1 (Z_to_bv 8 1)]                                       (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x168166 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].                   (* [comment removed for export] *)

Notation CMN_FRAME := 2192%Z (only parsing).

(* [comment removed for export] *)
Lemma cmn_loop1 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at bsegs m x [b]) -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x4447c) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4446c) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

(* [comment removed for export] *)
Lemma cmn_loop2 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at bsegs m x [b]) -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x44588) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44578) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Lemma cmn_rip1 : forall (sp p len : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk bsegs m lo (sp + -2192) -> lo <= sp - 2272 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 < len -> p + len < 2^63 ->
  acc bsegs m p len -> rng_ok p len -> m2s_cells m -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s10' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2192)) gp tp t0' t1' t2' s0 (Z_to_bv 64 len) a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 (Z_to_bv 64 p) s5 s6' s7 s8 s9 s10' s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x440b4) fc None m' (seg_rom bsegs)
      /\ munch [(sp - 2272, sp - 2192)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (sp + -2192))
    (MS (mkR ra (Z_to_bv 64 (sp + -2192)) gp tp t0 t1 t2 s0 (Z_to_bv 64 len) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44484) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2272, sp - 2192)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2192)) = sp + -2192) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 4 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  do 2 lstep. lstep. if_true.
  apply evt_done. do 19 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* [comment removed for export] *)
Lemma cmn_rip2 : forall (sp p len : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk bsegs m lo (sp + -2192) -> lo <= sp - 2272 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 < len -> p + len < 2^63 ->
  acc bsegs m p len -> rng_ok p len -> m2s_cells m -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s9' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2192)) gp tp t0' t1' t2' s0 (Z_to_bv 64 len) a0' a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 p) s3 s4 s5 s6' s7 s8 s9' s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x44100) fc None m' (seg_rom bsegs)
      /\ munch [(sp - 2272, sp - 2192)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (sp + -2192))
    (MS (mkR ra (Z_to_bv 64 (sp + -2192)) gp tp t0 t1 t2 s0 (Z_to_bv 64 len) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44590) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2272, sp - 2192)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2192)) = sp + -2192) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 4 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. lstep. if_true.
  apply evt_done. do 19 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* [comment removed for export] *)
Lemma cmn_chk1 : forall (sp p len : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk bsegs m lo (sp + -2192) -> lo <= sp - 2272 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 <= len -> p + len < 2^63 ->
  chk_ok m p len -> m2s_cells m -> icells_cmp m -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s10' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2192)) gp tp t0' t1' t2' s0 (Z_to_bv 64 len) a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 (Z_to_bv 64 p) s5 s6' s7 s8 (Z_to_bv 64 (len + -65)) s10' s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x440b4) fc None m' (seg_rom bsegs)
      /\ munch [(sp - 2272, sp - 2192)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (sp + -2192))
    (MS (mkR ra (Z_to_bv 64 (sp + -2192)) gp tp t0 t1 t2 s0 (Z_to_bv 64 len) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44064) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN (AC & QW & RO) M2S (GCF & G2 & RL & SHC & AI & FLG) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2272, sp - 2192)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  lstep. lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUns : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  if_false.
  lstep. lstep.
  destruct (Z_lt_le_dec 64 len) as [BIG|SMALL]; [| destruct (Z.eq_dec len 0) as [Z0|NZ]].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (len + -65)) = len - 65) by (apply unsigned_lit; lia).
    lstep. if_true. lstep. if_true.
    apply (cmn_rip1 sp p len); try assumption; lia.
  - (* [comment removed for export] *)
    subst len. lstep. if_true. lstep. if_false. lstep.
    apply evt_done. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (len + -65)) = len - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    lstep. if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (p + len + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((p + len - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + len + -1) with (p + len - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + (* [comment removed for export] *)
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (p + len + -1) / 8) with ((p + len + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p len AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + len + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * (* [comment removed for export] *)
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (cmn_rip1 sp p len); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (cmn_loop1 (Z.to_nat ((p + len + -1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a3' & a4' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (cmn_rip1 sp p len); try assumption; lia.
    + apply evt_done. do 19 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.


(* [comment removed for export] *)
Lemma cmn_chk2 : forall (sp p len : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s3 s5 s6 s7 s8  s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk bsegs m lo (sp + -2192) -> lo <= sp - 2272 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 <= len -> p + len < 2^63 ->
  chk_ok m p len -> m2s_cells m -> icells_cmp m -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s9' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2192)) gp tp t0' t1' t2' s0 (Z_to_bv 64 len) a0' a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 p) s3 s4 s5 s6' s7 s8 s9' s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x44100) fc None m' (seg_rom bsegs)
      /\ munch [(sp - 2272, sp - 2192)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (sp + -2192))
    (MS (mkR ra (Z_to_bv 64 (sp + -2192)) gp tp t0 t1 t2 s0 (Z_to_bv 64 len) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (len + -65)) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x440b4) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN (AC & QW & RO) M2S (GCF & G2 & RL & SHC & AI & FLG) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2272, sp - 2192)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  lstep. lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUns : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  if_false.
  lstep.
  destruct (Z_lt_le_dec 64 len) as [BIG|SMALL]; [| destruct (Z.eq_dec len 0) as [Z0|NZ]].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (len + -65)) = len - 65) by (apply unsigned_lit; lia).
    lstep. if_true. lstep. if_true.
    apply (cmn_rip2 sp p len); try assumption; lia.
  - (* [comment removed for export] *)
    subst len. lstep. if_true. lstep. if_false. lstep.
    apply evt_done. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (len + -65)) = len - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    lstep. if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (p + len + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((p + len - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + len + -1) with (p + len - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + (* [comment removed for export] *)
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (p + len + -1) / 8) with ((p + len + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p len AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + len + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * (* [comment removed for export] *)
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (cmn_rip2 sp p len); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (cmn_loop2 (Z.to_nat ((p + len + -1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a3' & a4' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (cmn_rip2 sp p len); try assumption; lia.
    + apply evt_done. do 19 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.


End WithRIP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cmp_args (m : mem) (usp lo p1 p2 : Z) (b1 b2 : list byte) : Prop :=
  length b2 = length b1 /\ Z.of_nat (length b1) < 2^40
  /\ 0 <= p1 /\ p1 + Z.of_nat (length b1) <= 2^47 /\ 0 <= p2 /\ p2 + Z.of_nat (length b1) <= 2^47
  /\ bytes_at bsegs m p1 b1 /\ bytes_at bsegs m p2 b2
  /\ (p1 + Z.of_nat (length b1) <= lo \/ usp <= p1) /\ (p2 + Z.of_nat (length b1) <= lo \/ usp <= p2)
  /\ chk_ok m p1 (Z.of_nat (length b1)) /\ chk_ok m p2 (Z.of_nat (length b1)) /\ m2s_cells m /\ icells_cmp m.

(* [comment removed for export] *)
Definition cmp_stmt (E D : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 lo : Z) (b1 b2 : list byte),
  cmp_args m (bv_unsigned sp) lo p1 p2 b1 b2 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - D -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 -> mem_inv bsegs m ->
  evt bsegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res b1 b2) [(bv_unsigned sp - D, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 (Z.of_nat (length b1))) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 E) fc None m (seg_rom bsegs)).

Lemma classic_outside : forall (W : list (Z * Z)) x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[l h] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [O|NO]; [|right; tauto].
  destruct (Z_le_dec l x) as [L|L]; [destruct (Z_lt_dec x h) as [H|H]; [right; tauto | left; split; [lia | exact O]] | left; split; [lia | exact O]].
Qed.

(* [comment removed for export] *)
Lemma cmp_args_stack : forall (m m' : mem) W usp usp' lo p1 p2 b1 b2,
  cmp_args m usp lo p1 p2 b1 b2 -> munch W m m' -> wmono bsegs m m' ->
  (forall x, ~ outside W x -> lo <= x < usp) -> kHighShadowEnd + 8 <= lo -> usp' <= usp -> usp <= 2^63 ->
  cmp_args m' usp' lo p1 p2 b1 b2.
Proof.
  intros m m' W usp usp' lo p1 p2 b1 b2 (HL & HN & P1 & P1h & P2 & P2h & B1 & B2 & S1 & S2 & C1 & C2 & (M1 & M2 & M3) & (I1 & I2 & I3 & I4 & I5 & I6))
    MU WM HW LOLO Hu Hu63. unfold kHighShadowEnd in LOLO.
  assert (AG : forall (P : Z -> Prop), (forall x, P x -> x < lo \/ usp <= x) -> agree_on P m m').
  { intros P HP. apply (agree_of_munch _ _ _ _ MU). intros y Hy. destruct (HP y Hy) as [L|G].
    - destruct (classic_outside W y) as [O|NO]; [exact O|]. specialize (HW y NO). lia.
    - destruct (classic_outside W y) as [O|NO]; [exact O|]. specialize (HW y NO). lia. }
  assert (T1 : forall A cs, rw_cells bsegs m A cs -> A + Z.of_nat (cells_size cs) <= lo -> rw_cells bsegs m' A cs).
  { intros A cs H HA. apply (rw_cells_agree bsegs m m' _ _ H); [|exact WM]. apply AG. intros x Hx. lia. }
  assert (T2 : forall A cs, ro_cells bsegs m A cs -> A + Z.of_nat (cells_size cs) <= lo -> ro_cells bsegs m' A cs).
  { intros A cs H HA. apply (ro_cells_agree bsegs m m' _ _ H). apply AG. intros x Hx. lia. }
  split; [exact HL|]. split; [exact HN|]. split; [exact P1|]. split; [exact P1h|]. split; [exact P2|]. split; [exact P2h|].
  split; [apply (bytes_at_agree bsegs m m' _ _ B1); apply AG; intros x Hx; lia|].
  split; [apply (bytes_at_agree bsegs m m' _ _ B2); apply AG; intros x Hx; rewrite HL in Hx; lia|].
  split; [lia|]. split; [lia|].
  split; [apply (chk_ok_agree m m' p1 _ C1 P1 P1h); apply AG; intros x Hx; lia|].
  split; [apply (chk_ok_agree m m' p2 _ C2 P2 P2h); apply AG; intros x Hx; lia|].
  split; [split; [apply (T1 _ _ M1); cbn; lia | split; [apply (T1 _ _ M2); cbn; lia | apply (T1 _ _ M3); cbn; lia]]|].
  split; [apply (T2 _ _ I1); cbn; lia|]. split; [apply (T2 _ _ I2); cbn; lia|]. split; [apply (T2 _ _ I3); cbn; lia|].
  split; [apply (T2 _ _ I4); cbn; lia|]. split; [apply (T1 _ _ I5); cbn; lia | apply (T2 _ _ I6); cbn; lia].
Qed.

Section Common.
Variables (E D : Z).
Hypothesis HE : 0 <= E < 2^62 /\ E mod 2 = 0.
Hypothesis HD : 80 <= D.
Hypothesis REALF : cmp_stmt E D.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Theorem common_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 lo : Z) (b1 b2 : list byte),
  cmp_args m (bv_unsigned sp) lo p1 p2 b1 b2 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - (2192 + D) -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 -> mem_inv bsegs m ->
  evt bsegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res b1 b2) [(bv_unsigned sp - (2192 + D), bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 E) (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 (Z.of_nat (length b1))) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x43ff0) fc None m (seg_rom bsegs)).
Proof using HE HD REALF RIP.
  intros until b2. intros CA ST LO LOLO SPH MI.
  pose proof CA as (HL & HN & P1 & P1h & P2 & P2h & B1 & B2 & SEP1 & SEP2 & CS1 & CS2 & M2S & IC).
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *. set (n := Z.of_nat (length b1)) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - (2192 + D), usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof IC as (GCF & G2 & RL & SHC & AI & FLG).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; unfold n; lia).
  assert (EUspc : bv_unsigned (Z_to_bv 64 (usp + -2192)) = usp + -2192) by (apply unsigned_lit; lia).
  carve_frame 104%nat ST. rename FR into FRs. carve_frame 2088%nat ST.
  do 21 lstep.
  do 3 lstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1. lstep. if_false.
  do 3 lstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1. lstep. if_false.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CA1 : cmp_args mm usp lo p1 p2 b1 b2)
      by (apply (cmp_args_stack m mm _ usp usp lo p1 p2 b1 b2 CA MU WM); [cbn [outside]; intros yy Hyy; lia | unfold kHighShadowEnd; lia | lia | lia]) end.
  destruct CA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CS1a & CS2a & M2Sa & ICa).
  call (cmn_chk1 RIP usp p1 n); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| unfold n; lia| unfold n in *; lia
        | exact CS1a| exact M2Sa| exact ICa| assumption|].
  lazymatch goal with H : stk bsegs _ lo (usp + -2192) |- _ => rename H into ST3 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CA2 : cmp_args mm usp lo p1 p2 b1 b2)
      by (apply (cmp_args_stack m mm _ usp usp lo p1 p2 b1 b2 CA MU WM); [cbn [outside]; intros yy Hyy; lia | unfold kHighShadowEnd; lia | lia | lia]) end.
  destruct CA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CS2b & M2Sb & ICb).
  call (cmn_chk2 RIP usp p2 n); [exact ST3| lia| unfold kHighShadowEnd; lia| lia| lia| unfold n; lia| unfold n in *; lia
        | exact CS2b| exact M2Sb| exact ICb| assumption|].
  lazymatch goal with H : stk bsegs _ lo (usp + -2192) |- _ => rename H into ST4 end.
  do 3 lstep. lstep.
  rewrite (ret_pc_even E) by (destruct HE as (HE1 & HE2); first [lia | exact HE2]).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CA3 : cmp_args mm (usp + -2192) lo p1 p2 b1 b2)
      by (apply (cmp_args_stack m mm _ usp (usp + -2192) lo p1 p2 b1 b2 CA MU WM); [cbn [outside]; intros yy Hyy; lia | unfold kHighShadowEnd; lia | lia | lia]) end.
  pose proof REALF as RF. unfold cmp_stmt in RF.
  call RF; [rewrite EUspc; exact CA3| rewrite EUspc; exact ST4| rewrite EUspc; lia| unfold kHighShadowEnd; lia| rewrite EUspc; lia| assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUspc in H; rename H into ST5 end.
  do 2 lstep. do 5 lstep. do 2 lstep.
  do 16 lstep.
  release_frame FR ST5 (usp + -104). release_frame FRs ST5 usp.
  lstep.
  unfold frame_post. sys_finish.
  all: rewrite ?EU; first [assumption | eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia].
Qed.

End Common.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow R_small R_m2s R_thread I_consts I_qck D_kit I_ikit IcptSpec2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition icells_cmp (m : mem) : Prop :=
  ro_cells asegs m 0xbfa48 [C8 (Z_to_bv 64 0x15ac68)]                                  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xbfa58 [C8 (Z_to_bv 64 0xc9138)]                                (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc1780 [C8 (Z_to_bv 64 0xb8d54); C8 (Z_to_bv 64 0xb8c84)]       (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc9138 [C8 (Z_to_bv 64 0x7fff8000)]                             (* [comment removed for export] *)
  /\ rw_cells asegs m 0xc9e18 [C1 (Z_to_bv 8 1)]                                       (* [comment removed for export] *)
  /\ ro_cells asegs m 0x15ad66 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].                   (* [comment removed for export] *)

Notation CMN_FRAME := 2192%Z (only parsing).

(* [comment removed for export] *)
Lemma cmn_loop1 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x44594) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44584) fc None m (seg_rom asegs)).
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
Lemma cmn_loop2 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x446a0) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44690) fc None m (seg_rom asegs)).
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

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Lemma cmn_rip1 : forall (sp p len : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2192) -> lo <= sp - 2272 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 < len -> p + len < 2^63 ->
  acc asegs m p len -> rng_ok p len -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s10' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2192)) gp tp t0' t1' t2' s0 (Z_to_bv 64 len) a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 (Z_to_bv 64 p) s5 s6' s7 s8 s9 s10' s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x441cc) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2272, sp - 2192)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2192))
    (MS (mkR ra (Z_to_bv 64 (sp + -2192)) gp tp t0 t1 t2 s0 (Z_to_bv 64 len) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4459c) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2272, sp - 2192)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2192)) = sp + -2192) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 4 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  do 2 lstep. lstep. if_true.
  apply evt_done. do 19 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* [comment removed for export] *)
Lemma cmn_rip2 : forall (sp p len : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2192) -> lo <= sp - 2272 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 < len -> p + len < 2^63 ->
  acc asegs m p len -> rng_ok p len -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s9' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2192)) gp tp t0' t1' t2' s0 (Z_to_bv 64 len) a0' a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 p) s3 s4 s5 s6' s7 s8 s9' s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x44218) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2272, sp - 2192)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2192))
    (MS (mkR ra (Z_to_bv 64 (sp + -2192)) gp tp t0 t1 t2 s0 (Z_to_bv 64 len) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x446a8) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
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
Lemma cmn_chk1 : forall (sp p len : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2192) -> lo <= sp - 2272 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 <= len -> p + len < 2^63 ->
  chk_ok m p len -> m2s_cells m -> icells_cmp m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s10' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2192)) gp tp t0' t1' t2' s0 (Z_to_bv 64 len) a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 (Z_to_bv 64 p) s5 s6' s7 s8 (Z_to_bv 64 (len + -65)) s10' s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x441cc) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2272, sp - 2192)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2192))
    (MS (mkR ra (Z_to_bv 64 (sp + -2192)) gp tp t0 t1 t2 s0 (Z_to_bv 64 len) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4417c) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN (AC & QW & RO) M2S (GCF & G2 & RL & SHC & AI & FLG) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2272, sp - 2192)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  lstep. lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUns : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  if_false.
  lstep. lstep.
  destruct (Z_lt_le_dec 64 len) as [BIG|SMALL]; [| destruct (Z.eq_dec len 0) as [Z0|NZ]].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (len + -65)) = len - 65) by (apply unsigned_lit; lia).
    lstep. if_true. lstep. if_true.
    apply (cmn_rip1 sp p len); try assumption; lia.
  - (* [comment removed for export] *)
    subst len. lstep. if_true. lstep. if_false. lstep.
    apply evt_done. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (len + -65)) = len - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    lstep. if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (p + len + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((p + len - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + len + -1) with (p + len - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + (* [comment removed for export] *)
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (p + len + -1) / 8) with ((p + len + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p len AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + len + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * (* [comment removed for export] *)
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (cmn_rip1 sp p len); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (cmn_loop1 (Z.to_nat ((p + len + -1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a3' & a4' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (cmn_rip1 sp p len); try assumption; lia.
    + apply evt_done. do 19 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.


(* [comment removed for export] *)
Lemma cmn_chk2 : forall (sp p len : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s3 s5 s6 s7 s8  s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2192) -> lo <= sp - 2272 -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 <= len -> p + len < 2^63 ->
  chk_ok m p len -> m2s_cells m -> icells_cmp m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s9' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2192)) gp tp t0' t1' t2' s0 (Z_to_bv 64 len) a0' a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 p) s3 s4 s5 s6' s7 s8 s9' s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x44218) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2272, sp - 2192)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2192))
    (MS (mkR ra (Z_to_bv 64 (sp + -2192)) gp tp t0 t1 t2 s0 (Z_to_bv 64 len) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (len + -65)) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x441cc) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN (AC & QW & RO) M2S (GCF & G2 & RL & SHC & AI & FLG) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2272, sp - 2192)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  lstep. lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUns : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  if_false.
  lstep.
  destruct (Z_lt_le_dec 64 len) as [BIG|SMALL]; [| destruct (Z.eq_dec len 0) as [Z0|NZ]].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (len + -65)) = len - 65) by (apply unsigned_lit; lia).
    lstep. if_true. lstep. if_true.
    apply (cmn_rip2 sp p len); try assumption; lia.
  - (* [comment removed for export] *)
    subst len. lstep. if_true. lstep. if_false. lstep.
    apply evt_done. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (len + -65)) = len - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    lstep. if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (p + len + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((p + len - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + len + -1) with (p + len - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + (* [comment removed for export] *)
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (p + len + -1) / 8) with ((p + len + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p len AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + len + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * (* [comment removed for export] *)
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (cmn_rip2 sp p len); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (cmn_loop2 (Z.to_nat ((p + len + -1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a3' & a4' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (cmn_rip2 sp p len); try assumption; lia.
    + apply evt_done. do 19 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.


End WithRIP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cmp_args (m : mem) (usp lo p1 p2 : Z) (b1 b2 : list byte) : Prop :=
  length b2 = length b1 /\ Z.of_nat (length b1) < 2^40
  /\ 0 <= p1 /\ p1 + Z.of_nat (length b1) <= 2^47 /\ 0 <= p2 /\ p2 + Z.of_nat (length b1) <= 2^47
  /\ bytes_at asegs m p1 b1 /\ bytes_at asegs m p2 b2
  /\ (p1 + Z.of_nat (length b1) <= lo \/ usp <= p1) /\ (p2 + Z.of_nat (length b1) <= lo \/ usp <= p2)
  /\ chk_ok m p1 (Z.of_nat (length b1)) /\ chk_ok m p2 (Z.of_nat (length b1)) /\ m2s_cells m /\ icells_cmp m.

(* [comment removed for export] *)
Definition cmp_stmt (E D : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 lo : Z) (b1 b2 : list byte),
  cmp_args m (bv_unsigned sp) lo p1 p2 b1 b2 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - D -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 -> mem_inv asegs m ->
  evt asegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res b1 b2) [(bv_unsigned sp - D, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 (Z.of_nat (length b1))) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 E) fc None m (seg_rom asegs)).

Lemma classic_outside : forall (W : list (Z * Z)) x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[l h] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [O|NO]; [|right; tauto].
  destruct (Z_le_dec l x) as [L|L]; [destruct (Z_lt_dec x h) as [H|H]; [right; tauto | left; split; [lia | exact O]] | left; split; [lia | exact O]].
Qed.

(* [comment removed for export] *)
Lemma cmp_args_stack : forall (m m' : mem) W usp usp' lo p1 p2 b1 b2,
  cmp_args m usp lo p1 p2 b1 b2 -> munch W m m' -> wmono asegs m m' ->
  (forall x, ~ outside W x -> lo <= x < usp) -> kHighShadowEnd + 8 <= lo -> usp' <= usp -> usp <= 2^63 ->
  cmp_args m' usp' lo p1 p2 b1 b2.
Proof.
  intros m m' W usp usp' lo p1 p2 b1 b2 (HL & HN & P1 & P1h & P2 & P2h & B1 & B2 & S1 & S2 & C1 & C2 & (M1 & M2 & M3) & (I1 & I2 & I3 & I4 & I5 & I6))
    MU WM HW LOLO Hu Hu63. unfold kHighShadowEnd in LOLO.
  assert (AG : forall (P : Z -> Prop), (forall x, P x -> x < lo \/ usp <= x) -> agree_on P m m').
  { intros P HP. apply (agree_of_munch _ _ _ _ MU). intros y Hy. destruct (HP y Hy) as [L|G].
    - destruct (classic_outside W y) as [O|NO]; [exact O|]. specialize (HW y NO). lia.
    - destruct (classic_outside W y) as [O|NO]; [exact O|]. specialize (HW y NO). lia. }
  assert (T1 : forall A cs, rw_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= lo -> rw_cells asegs m' A cs).
  { intros A cs H HA. apply (rw_cells_agree asegs m m' _ _ H); [|exact WM]. apply AG. intros x Hx. lia. }
  assert (T2 : forall A cs, ro_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= lo -> ro_cells asegs m' A cs).
  { intros A cs H HA. apply (ro_cells_agree asegs m m' _ _ H). apply AG. intros x Hx. lia. }
  split; [exact HL|]. split; [exact HN|]. split; [exact P1|]. split; [exact P1h|]. split; [exact P2|]. split; [exact P2h|].
  split; [apply (bytes_at_agree asegs m m' _ _ B1); apply AG; intros x Hx; lia|].
  split; [apply (bytes_at_agree asegs m m' _ _ B2); apply AG; intros x Hx; rewrite HL in Hx; lia|].
  split; [lia|]. split; [lia|].
  split; [apply (chk_ok_agree m m' p1 _ C1 P1 P1h); apply AG; intros x Hx; lia|].
  split; [apply (chk_ok_agree m m' p2 _ C2 P2 P2h); apply AG; intros x Hx; lia|].
  split; [split; [apply (T1 _ _ M1); cbn; lia | split; [apply (T1 _ _ M2); cbn; lia | apply (T1 _ _ M3); cbn; lia]]|].
  split; [apply (T2 _ _ I1); cbn; lia|]. split; [apply (T2 _ _ I2); cbn; lia|]. split; [apply (T2 _ _ I3); cbn; lia|].
  split; [apply (T2 _ _ I4); cbn; lia|]. split; [apply (T1 _ _ I5); cbn; lia | apply (T2 _ _ I6); cbn; lia].
Qed.

Section Common.
Variables (E D : Z).
Hypothesis HE : 0 <= E < 2^62 /\ E mod 2 = 0.
Hypothesis HD : 80 <= D.
Hypothesis REALF : cmp_stmt E D.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Theorem common_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 lo : Z) (b1 b2 : list byte),
  cmp_args m (bv_unsigned sp) lo p1 p2 b1 b2 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - (2192 + D) -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 -> mem_inv asegs m ->
  evt asegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res b1 b2) [(bv_unsigned sp - (2192 + D), bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 E) (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 (Z.of_nat (length b1))) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44108) fc None m (seg_rom asegs)).
Proof using HE HD REALF RIP.
  intros until b2. intros CA ST LO LOLO SPH MI.
  pose proof CA as (HL & HN & P1 & P1h & P2 & P2h & B1 & B2 & SEP1 & SEP2 & CS1 & CS2 & M2S & IC).
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *. set (n := Z.of_nat (length b1)) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - (2192 + D), usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof IC as (GCF & G2 & RL & SHC & AI & FLG).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; unfold n; lia).
  assert (EUspc : bv_unsigned (Z_to_bv 64 (usp + -2192)) = usp + -2192) by (apply unsigned_lit; lia).
  carve_frame 104%nat ST. rename FR into FRs. carve_frame 2088%nat ST.
  do 21 lstep.
  do 3 lstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1. lstep. if_false.
  do 3 lstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1. lstep. if_false.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CA1 : cmp_args mm usp lo p1 p2 b1 b2)
      by (apply (cmp_args_stack m mm _ usp usp lo p1 p2 b1 b2 CA MU WM); [cbn [outside]; intros yy Hyy; lia | unfold kHighShadowEnd; lia | lia | lia]) end.
  destruct CA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CS1a & CS2a & M2Sa & ICa).
  call (cmn_chk1 RIP usp p1 n); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| unfold n; lia| unfold n in *; lia
        | exact CS1a| exact M2Sa| exact ICa| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2192) |- _ => rename H into ST3 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CA2 : cmp_args mm usp lo p1 p2 b1 b2)
      by (apply (cmp_args_stack m mm _ usp usp lo p1 p2 b1 b2 CA MU WM); [cbn [outside]; intros yy Hyy; lia | unfold kHighShadowEnd; lia | lia | lia]) end.
  destruct CA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CS2b & M2Sb & ICb).
  call (cmn_chk2 RIP usp p2 n); [exact ST3| lia| unfold kHighShadowEnd; lia| lia| lia| unfold n; lia| unfold n in *; lia
        | exact CS2b| exact M2Sb| exact ICb| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2192) |- _ => rename H into ST4 end.
  do 3 lstep. lstep.
  rewrite (ret_pc_even E) by (destruct HE as (HE1 & HE2); first [lia | exact HE2]).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CA3 : cmp_args mm (usp + -2192) lo p1 p2 b1 b2)
      by (apply (cmp_args_stack m mm _ usp (usp + -2192) lo p1 p2 b1 b2 CA MU WM); [cbn [outside]; intros yy Hyy; lia | unfold kHighShadowEnd; lia | lia | lia]) end.
  pose proof REALF as RF. unfold cmp_stmt in RF.
  call RF; [rewrite EUspc; exact CA3| rewrite EUspc; exact ST4| rewrite EUspc; lia| unfold kHighShadowEnd; lia| rewrite EUspc; lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUspc in H; rename H into ST5 end.
  do 2 lstep. do 5 lstep. do 2 lstep.
  do 16 lstep.
  release_frame FR ST5 (usp + -104). release_frame FRs ST5 usp.
  lstep.
  unfold frame_post. sys_finish.
  all: rewrite ?EU; first [assumption | eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia].
Qed.

End Common.
