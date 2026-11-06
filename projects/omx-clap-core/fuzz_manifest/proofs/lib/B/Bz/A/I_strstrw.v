(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated unchanged from an earlier relocation of this file for fuzz_command, for the image this tree pins (fuzz_command.asan sha256 c0661b96). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Bz/A/I_strspnw.v, with its module paths, addresses and numbers changed; 312 of its 447 lines of code are new or changed and 302 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Bz/A/I_strstrw.v: ported from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/Bz/A/I_strstrw.v, which equals the A->B relocation (Theorem Labs tools) of lib/A/Bz/A/I_strstrw.v at a working branch 5d8d8a15571 modulo module paths; module paths for this tree. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit IcptSpec
  D_kit I_ikit I_tramp I_strchrw.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A Require I_memcmpw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation ISTRSTR_DEPTH := 4608%Z (only parsing).

Lemma tramp_strstr : tramp_step 0x4133c 0x429bc. Proof. tramp_proof. Qed.

Definition sck_n1 (H r : Z) (hb nb : list byte) : Z :=
  if r =? 0 then Z.of_nat (length hb) + 1 else r - H + Z.of_nat (length nb).

Definition icells_ss (m : mem) : Prop :=
  ro_cells asegs m 0x99c88 [C8 (Z_to_bv 64 0x133ba8)]
  /\ ro_cells asegs m 0x99c98 [C8 (Z_to_bv 64 0xa2078)]
  /\ ro_cells asegs m 0xa2078 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells asegs m 0xa2d58 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x9b9c8 [C8 (Z_to_bv 64 0x93294)]
  /\ ro_cells asegs m 0x133c9d [C1 (Z_to_bv 8 0)]
  /\ ro_cells asegs m 0x133c9e [C1 (Z_to_bv 8 1)].

Definition chk1_post (q : Z) (gp tp s2 s3 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s7' s8' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra' (Z_to_bv 64 (q + -2160)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4' s5' s6' s7' s8' s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x42b88) fc None m' (seg_rom asegs)
    /\ munch [(q - 2240, q - 2160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (q + -2160).

Definition chk2_post (q : Z) (gp tp s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (m' : mem)
      (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra' (Z_to_bv 64 (q + -2160)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                  s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x42bd4) fc None m' (seg_rom asegs)
    /\ munch [(q - 2240, q - 2160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (q + -2160).

Definition sck_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 2240, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q.

Definition ss_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 4560, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q.

Definition ss_stmt (m0 : mem) (usp H ND r lo : Z) : Prop :=
  forall (gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : mem),
  munch [(usp - 4608, usp)] m0 mm -> wmono asegs m0 mm -> mem_inv asegs mm -> stk asegs mm lo (usp + -48) ->
  evt asegs (ss_post (Z_to_bv 64 0x42a08) (usp + -48) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r lo mm)
    (MS (mkR (Z_to_bv 64 0x42a08) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 H) (Z_to_bv 64 ND)
             a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x93294) fc None mm (seg_rom asegs)).

Definition istrstr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ISTRSTR_DEPTH, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma sck_loop : forall (lp ex : Z), (lp = 0x42d14 /\ ex = 0x42d24) \/ (lp = 0x42dd0 /\ ex = 0x42de0) ->
  forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a2' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 e) a2' a3' a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 ex) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 lp) fc None m (seg_rom asegs)).
Proof.
  intros lp ex HP.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI;
  destruct (HB c ltac:(lia)) as (b & Hb); pose proof (ro_C1_of_bytes m c b Hb) as CB0;
  pose proof (munch_refl [] m) as MU; pose proof (wmono_refl asegs m) as WM;
  assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia);
  assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia);
  assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia);
  destruct HP as [[-> ->]|[-> ->]].
  1-2: do 3 lstep; lstep; if_false; apply evt_done; do 2 eexists; replace e with (c + 1) by lia; reflexivity.
  all: do 3 lstep; lstep; if_true; apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Lemma sck_rip1 : forall (q p n : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (q + -2160) -> lo <= q - 2240 -> kHighShadowEnd < lo -> q < 2^63 ->
  0 <= p -> 0 < n -> p + n < 2^63 ->
  acc asegs m p n -> rng_ok p n -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (chk1_post q gp tp s2 s3 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (q + -2160)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 n) (Z_to_bv 64 p) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x42d2c) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO QH P0 N0 PN AC RO M2S MI.
  pose proof (munch_refl [(q - 2240, q - 2160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (q + -2160)) = q + -2160) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 3 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. if_true.
  apply evt_done. unfold chk1_post. do 24 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma sck_chk1 : forall (q p n : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (q + -2160) -> lo <= q - 2240 -> kHighShadowEnd < lo -> q < 2^63 ->
  0 <= p -> 0 <= n -> p + n < 2^63 ->
  chk_ok m p n -> m2s_cells m -> ro_cells asegs m 0x99c98 [C8 (Z_to_bv 64 0xa2078)] ->
  ro_cells asegs m 0xa2078 [C8 (Z_to_bv 64 0x7fff8000)] -> mem_inv asegs m ->
  evt asegs (chk1_post q gp tp s2 s3 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (q + -2160)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 n) (Z_to_bv 64 p) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x42b40) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO QH P0 N0 PN (AC & QW & RO) M2S G2 SHC MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(q - 2240, q - 2160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  lstep. lstep. lstep.
  destruct (Z_lt_le_dec 64 n) as [BIG|SMALL]; [| destruct (Z.eq_dec n 0) as [Z0|NZ]].
  - assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65) by (apply unsigned_lit; lia).
    if_true. lstep. if_true.
    apply (sck_rip1 q p n); try assumption; lia.
  - subst n. if_true. lstep. if_false. lstep.
    apply evt_done. unfold chk1_post. do 24 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65 + 2^64)
      by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
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
    + rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (p + n + -1) / 8) with ((p + n + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p n AC ltac:(lia) P0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + n + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * lstep. lstep. if_cases K3.
        -- apply evt_done. unfold chk1_post. do 24 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (sck_rip1 q p n); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (sck_loop 0x42d14 0x42d24 (or_introl (conj eq_refl eq_refl))
                    (Z.to_nat ((p + n + -1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a2' & a3' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold chk1_post. do 24 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (sck_rip1 q p n); try assumption; lia.
    + apply evt_done. unfold chk1_post. do 24 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

Lemma sck_mid : forall (q H r lh ln : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (q + -2160) -> lo <= q - 2240 -> kHighShadowEnd < lo -> q < 2^63 ->
  0 <= H -> 0 <= lh -> 0 <= ln -> 0 <= r < 2^64 -> H + lh + 1 <= 2^47 ->
  (r = 0 \/ (H <= r /\ r - H + ln <= lh)) ->
  chk_ok m H (if r =? 0 then lh + 1 else r - H + ln) -> m2s_cells m ->
  ro_cells asegs m 0x99c98 [C8 (Z_to_bv 64 0xa2078)] -> ro_cells asegs m 0xa2078 [C8 (Z_to_bv 64 0x7fff8000)] ->
  mem_inv asegs m ->
  evt asegs (chk1_post q gp tp s2 (Z_to_bv 64 ln) s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (q + -2160)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 ln) (Z_to_bv 64 r) (Z_to_bv 64 H) (Z_to_bv 64 lh) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x42b24) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO QH H0 L0 N0 R0 HL RR CH M2S G2 SHC MI.
  assert (EUH : bv_unsigned (Z_to_bv 64 H) = H) by (apply unsigned_lit; lia).
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  assert (EUlh : bv_unsigned (Z_to_bv 64 lh) = lh) by (apply unsigned_lit; lia).
  assert (EUnH : bv_unsigned (Z_to_bv 64 (18446744073709551615 - H)) = 18446744073709551615 - H)
    by (apply unsigned_lit; lia).
  destruct (Z.eq_dec r 0) as [Er|Ern].
  - subst r. rewrite Z.eqb_refl in CH.
    assert (EU1 : bv_unsigned (Z_to_bv 64 (lh + 1)) = lh + 1) by (apply unsigned_lit; lia).
    lstep. if_true.
    lstep. lstep. rewrite (lxor_ones64 H) by lia.
    lstep. lstep. lstep. if_true.
    apply (sck_chk1 q H (lh + 1)); try assumption; lia.
  - rewrite (proj2 (Z.eqb_neq r 0) Ern) in CH.
    destruct RR as [R00|(RL & RH)]; [contradiction|].
    assert (EUln : bv_unsigned (Z_to_bv 64 ln) = ln) by (apply unsigned_lit; lia).
    assert (EUd : bv_unsigned (Z_to_bv 64 (r - H)) = r - H) by (apply unsigned_lit; lia).
    assert (EUn1 : bv_unsigned (Z_to_bv 64 (r - H + ln)) = r - H + ln) by (apply unsigned_lit; lia).
    lstep. if_false.
    lstep. lstep. lstep. rewrite (lxor_ones64 H) by lia.
    lstep. lstep. lstep. if_false.
    apply (sck_chk1 q H (r - H + ln)); try assumption; lia.
Qed.

Lemma sck_rip2 : forall (q p r : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (q + -2160) -> lo <= q - 2240 -> kHighShadowEnd < lo -> q < 2^63 ->
  0 <= p -> 0 <= r -> p + r + 1 < 2^63 ->
  acc asegs m p (r + 1) -> rng_ok p (r + 1) -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (chk2_post q gp tp s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (q + -2160)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 (Z_to_bv 64 (r + 1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x42de8) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO QH P0 N0 PN AC RO M2S MI.
  pose proof (munch_refl [(q - 2240, q - 2160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (q + -2160)) = q + -2160) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO ltac:(lia)) as (RIM & N40).
  do 3 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. if_true.
  apply evt_done. unfold chk2_post. do 26 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma sck_chk2 : forall (q p r : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (q + -2160) -> lo <= q - 2240 -> kHighShadowEnd < lo -> q < 2^63 ->
  0 <= p -> 0 <= r -> p + r + 1 < 2^63 ->
  chk_ok m p (r + 1) -> m2s_cells m -> ro_cells asegs m 0x99c98 [C8 (Z_to_bv 64 0xa2078)] ->
  ro_cells asegs m 0xa2078 [C8 (Z_to_bv 64 0x7fff8000)] -> mem_inv asegs m ->
  evt asegs (chk2_post q gp tp s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (q + -2160)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) (Z_to_bv 64 r) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x42b88) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO QH P0 N0 PN (AC & QW & RO) M2S G2 SHC MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(q - 2240, q - 2160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (r + 1)) = r + 1) by (apply unsigned_lit; lia).
  lstep. lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  lstep. if_false. lstep. lstep.
  destruct (Z_lt_le_dec r 64) as [SMALL|BIG].
  - if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 10 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (r + p) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((p + (r + 1) - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + (r + 1) - 1) with (r + p) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (r + p) / 8) with ((p + (r + 1) - 1) / 8 + 2147450880)
        by (replace (p + (r + 1) - 1) with (r + p) by lia; lia).
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p (r + 1) AC ltac:(lia) P0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + (r + 1) - 1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * lstep. lstep. if_cases K3.
        -- apply evt_done. unfold chk2_post. do 26 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (sck_rip2 q p r); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (sck_loop 0x42dd0 0x42de0 (or_intror (conj eq_refl eq_refl))
                    (Z.to_nat ((p + (r + 1) - 1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a2' & a3' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold chk2_post. do 26 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (sck_rip2 q p r); try assumption; lia.
    + apply evt_done. unfold chk2_post. do 26 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - if_true. lstep. if_true.
    apply (sck_rip2 q p r); try assumption; lia.
Qed.

Lemma sck_spec : forall (q H ND r : Z) (hb nb : list byte)
    (ra gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo : Z),
  stk asegs m lo q -> lo <= q - 2240 -> kHighShadowEnd < lo -> q <= 2^47 ->
  bytes_at asegs m H (hb ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) hb ->
  bytes_at asegs m ND (nb ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) nb ->
  0 <= H -> H + Z.of_nat (length hb) + 1 <= 2^47 -> 0 <= ND -> ND + Z.of_nat (length nb) + 1 <= 2^47 ->
  (H + Z.of_nat (length hb) + 1 <= q - 2240 \/ q <= H) ->
  (ND + Z.of_nat (length nb) + 1 <= q - 2240 \/ q <= ND) ->
  0 <= r < 2^64 -> (r = 0 \/ (H <= r /\ r - H + Z.of_nat (length nb) <= Z.of_nat (length hb))) ->
  chk_ok m H (sck_n1 H r hb nb) -> chk_ok m ND (Z.of_nat (length nb) + 1) -> m2s_cells m -> icells_ss m -> mem_inv asegs m ->
  evt asegs (sck_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 r) (Z_to_bv 64 H) (Z_to_bv 64 ND) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x42a98) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros ST LO LOLO QH BH NZH BN NZN H0 HL N0 NL SEPH SEPN R0 RR CH CN M2S IC MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(q - 2240, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof IC as (G70 & G2 & SHC & AI & RS & F5 & F6).
  assert (N1B : 0 <= sck_n1 H r hb nb /\ H + sck_n1 H r hb nb <= 2^47)
    by (unfold sck_n1; destruct (Z.eqb_spec r 0); lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (EUH : bv_unsigned (Z_to_bv 64 H) = H) by (apply unsigned_lit; lia).
  assert (EUN : bv_unsigned (Z_to_bv 64 ND) = ND) by (apply unsigned_lit; lia).
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (q + -2160)) = q + -2160) by (apply unsigned_lit; lia).
  carve_frame 80%nat ST. rename FR into FRs. carve_frame 2080%nat ST.
  xsteps_to 0x63fa8.
  call iislen_spec; [reflexivity| exact BH| lia| exact NZH| assumption|].
  xsteps_to 0x63fa8.
  call iislen_spec; [reflexivity| exact BN| lia| exact NZN| assumption|].
  xsteps_to 0x42b24.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CH1 : chk_ok mm H (sck_n1 H r hb nb))
      by (apply (chk_ok_agree m mm H _ CH ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy;
          cbn [outside]; split; [lia| exact I]);
    assert (M2S1 : m2s_cells mm)
      by (apply (I_memcmpw.m2s_cells_agree m mm M2S); [| assumption];
          apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I])
  end.
  call (sck_mid q H r (Z.of_nat (length hb)) (Z.of_nat (length nb)));
    [ exact ST | lia | unfold kHighShadowEnd; lia | lia | lia | lia | lia | lia | lia | exact RR | exact CH1 | exact M2S1
    | assumption | assumption | assumption |].
  lazymatch goal with H : stk asegs _ lo (q + -2160) |- _ => rename H into ST2 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CN1 : chk_ok mm ND (Z.of_nat (length nb) + 1))
      by (apply (chk_ok_agree m mm ND _ CN ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy;
          cbn [outside]; split; [lia| exact I]);
    assert (M2S2 : m2s_cells mm)
      by (apply (I_memcmpw.m2s_cells_agree m mm M2S); [| assumption];
          apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I])
  end.
  call (sck_chk2 q ND (Z.of_nat (length nb)));
    [ exact ST2 | lia | unfold kHighShadowEnd; lia | lia | lia | lia | lia | exact CN1 | exact M2S2
    | assumption | assumption | assumption |].
  lazymatch goal with H : stk asegs _ lo (q + -2160) |- _ => rename H into ST3 end.
  do 12 lstep.
  release_frame FR ST3 (q + -80). release_frame FRs ST3 q.
  lstep.
  unfold sck_post. sys_finish.
Qed.

Theorem istrstr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (H ND r : Z) (hb nb : list byte) (lo : Z),
  a0 = Z_to_bv 64 H -> a1 = Z_to_bv 64 ND ->
  ss_stmt m (bv_unsigned sp) H ND r lo ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRSTR_DEPTH -> kHighShadowEnd < lo -> bv_unsigned sp <= 2^47 ->
  bytes_at asegs m H (hb ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) hb ->
  bytes_at asegs m ND (nb ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) nb ->
  0 <= H -> H + Z.of_nat (length hb) + 1 <= 2^47 -> 0 <= ND -> ND + Z.of_nat (length nb) + 1 <= 2^47 ->
  (H + Z.of_nat (length hb) + 1 <= bv_unsigned sp - ISTRSTR_DEPTH \/ bv_unsigned sp <= H) ->
  (ND + Z.of_nat (length nb) + 1 <= bv_unsigned sp - ISTRSTR_DEPTH \/ bv_unsigned sp <= ND) ->
  0 <= r < 2^64 -> (r = 0 \/ (H <= r /\ r - H + Z.of_nat (length nb) <= Z.of_nat (length hb))) ->
  chk_ok m H (sck_n1 H r hb nb) -> chk_ok m ND (Z.of_nat (length nb) + 1) -> m2s_cells m -> icells_ss m -> mem_inv asegs m ->
  evt asegs (istrstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4133c) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros -> -> SS ST LO LOLO SPH BH NZH BN NZN H0 HL N0 NL SEPH SEPN R0 RR CH CN M2S IC MI.
  apply tramp_strstr.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 4608, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof IC as (G70 & G2 & SHC & AI & RS & F5 & F6).
  assert (N1B : 0 <= sck_n1 H r hb nb /\ H + sck_n1 H r hb nb <= 2^47)
    by (unfold sck_n1; destruct (Z.eqb_spec r 0); lia).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  assert (EUH : bv_unsigned (Z_to_bv 64 H) = H) by (apply unsigned_lit; lia).
  assert (EUN : bv_unsigned (Z_to_bv 64 ND) = ND) by (apply unsigned_lit; lia).
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  unfold ss_stmt in SS.
  carve_frame 48%nat ST.
  xsteps_to 0x58bc8.
  call asan_inited_spec; [exact AI| assumption|].
  xsteps_to 0x59ad8.
  call try_init_spec; [exact AI| rewrite EU48; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST2 end.
  xsteps_to 0x93294.
  call SS; [exact MU| exact WM| assumption| exact ST2|].
  lazymatch goal with H : stk asegs _ lo (usp + -48) |- _ => rename H into ST3 end.
  xsteps_to 0x42a98.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CH1 : chk_ok mm H (sck_n1 H r hb nb))
      by (apply (chk_ok_agree m mm H _ CH ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy;
          cbn [outside]; split; [lia| exact I]);
    assert (CN1 : chk_ok mm ND (Z.of_nat (length nb) + 1))
      by (apply (chk_ok_agree m mm ND _ CN ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy;
          cbn [outside]; split; [lia| exact I]);
    assert (M2S1 : m2s_cells mm)
      by (apply (I_memcmpw.m2s_cells_agree m mm M2S); [| assumption];
          apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]);
    assert (IC1 : icells_ss mm) by (unfold icells_ss;
      split; [exact G70| split; [exact G2| split; [exact SHC| split; [exact AI| split; [exact RS| split; [exact F5| exact F6]]]]]])
  end.
  call (sck_spec (usp + -48) H ND r hb nb);
    [ exact ST3 | lia | unfold kHighShadowEnd; lia | lia | exact BH | exact NZH | exact BN | exact NZN | lia | lia | lia | lia
    | lia | lia | lia | exact RR | exact CH1 | exact CN1 | exact M2S1 | exact IC1 | assumption |].
  lazymatch goal with H : stk asegs _ lo (usp + -48) |- _ => rename H into ST4 end.
  xsteps_to 0x429b8.
  lstep.
  do 8 lstep.
  release_frame FR ST4 usp.
  lstep.
  unfold istrstr_post. sys_finish.
  - rewrite EU. assumption.
  - rewrite EU. assumption.
Qed.

End WithRIP.
