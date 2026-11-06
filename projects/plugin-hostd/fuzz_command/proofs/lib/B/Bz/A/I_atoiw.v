(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated unchanged from an earlier relocation of this file for fuzz_command, for the image this tree pins (fuzz_command.asan sha256 c0661b96). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Bz/A/I_strcpyw.v, with its module paths, addresses and numbers changed; 300 of its 376 lines of code are new or changed and 371 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A Require Import Shadow IcptSpec R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit I_init I_strtolfix I_strtolw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Definition parked (P : Prop) : Prop := P.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.


Lemma rwc_split : forall segs m A B cs1 cs2, rw_cells segs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells segs m A cs1 /\ rw_cells segs m B cs2.
Proof.
  intros segs m A B cs1 cs2 [[Hwf Hb] (H0 & H1 & H2)] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app in H1, H2.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply H2. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H2. lia.
Qed.
Definition IATOI_DEPTH : Z := 2640.

Lemma atoi_ws : forall (n i : nat) (A : Z) (str : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  bytes_at asegs m A (str ++ [Z_to_bv 8 0]) -> 0 <= A -> A + Z.of_nat (length str) + 1 < 2^64 ->
  (i <= length str)%nat -> nblank (skipn i (str ++ [Z_to_bv 8 0])) = n -> (nblank (str ++ [Z_to_bv 8 0]) = i + n)%nat ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (a0' a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (A + fix_off (str ++ [Z_to_bv 8 0]))) (Z_to_bv 64 32) a3' a4' a5 a6 a7
                    (Z_to_bv 64 A) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x4d274) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 5) (Z_to_bv 64 (A + Z.of_nat i)) (Z_to_bv 64 32) a3 a4 a5 a6 a7
             (Z_to_bv 64 A) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4d250) fc None m (seg_rom asegs)).
Proof.
  induction n as [|n IH]; intros i A str ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    STR A0 AN Hi Hn Hnb MI;
    set (LL := str ++ [Z_to_bv 8 0]) in *;
    (destruct (nth_error LL i) as [b|] eqn:Eb; [| exfalso; apply nth_error_None in Eb; unfold LL in Eb; rewrite length_app in Eb; cbn in Eb; lia]);
    pose proof (bv_unsigned_in_range 8 b) as Rb; unfold bv_modulus in Rb; cbn in Rb;
    pose proof (bytes_at_nth1 asegs m A LL i b STR Eb) as Bb;
    pose proof (ro_C1_of_bytes _ _ _ Bb) as CB;
    assert (SK : skipn i LL = b :: skipn (Datatypes.S i) LL)
      by (clear - Eb; revert i Eb; induction LL as [|x l IHl]; intros [|i] E; cbn in *; try discriminate; [injection E as ->; reflexivity | apply IHl; exact E]);
    rewrite SK in Hn; cbn [nblank] in Hn; pose proof (blank_code _ Rb) as BC;
    assert (EUi : bv_unsigned (Z_to_bv 64 (A + Z.of_nat i)) = A + Z.of_nat i) by (apply unsigned_lit; lia);
    assert (EUi1 : bv_unsigned (Z_to_bv 64 (A + Z.of_nat i + 1)) = A + Z.of_nat i + 1) by (apply unsigned_lit; lia);
    pose proof (munch_refl [] m) as MU; pose proof (wmono_refl asegs m) as WM;
    remember (A + Z.of_nat i)%Z as ci eqn:Eci.
  - destruct (is_blank (bv_unsigned b)) eqn:EB; [discriminate Hn|]. symmetry in BC. apply orb_false_iff in BC. destruct BC as [BC1 BC2].
    apply Z.ltb_ge in BC1. apply Z.eqb_neq in BC2.
    assert (FO : fix_off LL = if ((bv_unsigned b =? 43) || (bv_unsigned b =? 45))%bool then Z.of_nat i + 1 else Z.of_nat i).
    { unfold fix_off. replace (nblank LL) with i by lia. rewrite Eb. reflexivity. }
    lstep. lstep. lstep. if_cases Kbl; [ zify_cond Kbl; exfalso; lia | ]. lstep. if_cases Kbe; [ zify_cond Kbe; exfalso; lia | ].
    lstep. lstep. if_cases K3.
    + lstep. zify_cond K3. apply evt_done. do 3 eexists.
      rewrite FO, (proj2 (Z.eqb_eq _ _) K3). cbn [orb]. rewrite Eci. replace (A + (Z.of_nat i + 1)) with (A + Z.of_nat i + 1) by lia. reflexivity.
    + lstep. lstep. if_cases K4.
      * zify_cond K3. zify_cond K4. apply evt_done. do 3 eexists.
        rewrite FO, (proj2 (Z.eqb_neq _ _) K3), (proj2 (Z.eqb_neq _ _) K4). cbn [orb]. rewrite Eci. reflexivity.
      * lstep. zify_cond K3. zify_cond K4. apply evt_done. do 3 eexists.
        rewrite FO, (proj2 (Z.eqb_neq _ _) K3), (proj2 (Z.eqb_eq _ _) K4), orb_true_r. rewrite Eci. replace (A + (Z.of_nat i + 1)) with (A + Z.of_nat i + 1) by lia. reflexivity.
  - destruct (is_blank (bv_unsigned b)) eqn:EB; [| discriminate Hn]. injection Hn as Hn.
    symmetry in BC. apply orb_true_iff in BC.
    assert (ILT : (i < length str)%nat).
    { destruct (Nat.eq_dec i (length str)) as [EQ|]; [|lia]. exfalso. unfold LL in Eb. rewrite EQ, nth_error_app2, Nat.sub_diag in Eb by lia. cbn in Eb. injection Eb as <-. vm_compute in EB. discriminate. }
    lstep. lstep. lstep. if_cases K1.
    + lstep. replace (ci + 1) with (A + Z.of_nat (Datatypes.S i)) by (rewrite Eci; lia).
      eapply (IH (Datatypes.S i)); [exact STR| lia| lia| lia| exact Hn| unfold LL in *; lia| exact MI].
    + lstep. if_cases K2.
      * lstep. replace (ci + 1) with (A + Z.of_nat (Datatypes.S i)) by (rewrite Eci; lia).
        eapply (IH (Datatypes.S i)); [exact STR| lia| lia| lia| exact Hn| unfold LL in *; lia| exact MI].
      * exfalso. zify_cond K1. zify_cond K2. destruct BC as [BC|BC]; [apply Z.ltb_lt in BC| apply Z.eqb_eq in BC]; lia.
Qed.

Lemma atoi_loop : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a2' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 e) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x4d3c4) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4d3b4) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI;
    destruct (HB c ltac:(lia)) as (b & Hb); pose proof (ro_C1_of_bytes _ _ _ Hb) as CB0;
    pose proof (munch_refl [] m) as MU; pose proof (wmono_refl asegs m) as WM;
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia);
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
  - do 3 lstep. lstep. if_cases Kb.
    + zify_cond Kb. exfalso. lia.
    + apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - do 3 lstep. lstep. if_cases Kb.
    + apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
    + zify_cond Kb. exfalso. lia.
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Definition atoi_prepi (gp tp s1 s9 s10 s11 : word) F fc (usp lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (usp + -2160)) gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x4d2ec) fc None m' (seg_rom asegs)
      /\ munch [(usp - 2240, usp - 2160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -2160).

Lemma atoi_rip : forall (p N : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo usp : Z),
  stk asegs m lo (usp + -2160) -> lo <= usp - 2240 -> kHighShadowEnd < lo -> usp < 2^63 ->
  0 <= p -> 1 <= N -> p + N < 2^63 ->
  acc asegs m p N -> rng_ok p N -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (atoi_prepi gp tp s1 s9 s10 s11 F fc usp lo m)
    (MS (mkR ra (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) (Z_to_bv 64 N) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4d3cc) fc None m (seg_rom asegs)).
Proof.
  intros p N ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp
    ST LO LOLO SPH D0 N1 DN AC RO M2S MI.
  pose proof (munch_refl [(usp - 2240, usp - 2160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO ltac:(lia)) as (RIM & N40).
  do 3 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. if_true.
  apply evt_done. unfold atoi_prepi. do 25 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma atoi_chk : forall (q p L : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo usp : Z),
  stk asegs m lo (usp + -2160) -> lo + 2640 <= usp -> kHighShadowEnd < lo -> usp <= 2 ^ 47 ->
  q = p + L -> 0 <= p -> 0 <= L -> p + L + 1 < 2 ^ 63 ->
  chk_ok m p (L + 1) -> icells_sx m -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (atoi_prepi gp tp s1 s9 s10 s11 F fc usp lo m)
    (MS (mkR ra (Z_to_bv 64 (usp + -2160)) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4d278) fc None m (seg_rom asegs)).
Proof.
  intros q p L ra gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo usp
    ST LO LOLO SPH EQ D0 N0 DN (AC & QW & RO) (IC1 & IC2) M2S MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(usp - 2240, usp - 2160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (L + 1)) = L + 1) by (apply unsigned_lit; lia).
  assert (EUe : bv_unsigned (Z_to_bv 64 (p + L)) = p + L) by (apply unsigned_lit; lia).
  subst q.
  lstep. lstep. lstep. lstep. if_true. lstep. lstep.
  lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  lstep. lstep. replace (p + L - p) with L in * by lia. lstep. if_false. lstep.
  destruct M2S as (MG & MSHB & MHI). assert (M2Sc : m2s_cells m) by (split; [exact MG | split; [exact MSHB | exact MHI]]). unfold SHB in MSHB.
  destruct (Z_lt_le_dec L 64) as [SMALL|BIG].
  - lstep.
    assert (Cbg : negb (bv_ltu (Z_to_bv 64 L) (Z_to_bv 64 64)) = false).
    { unfold bv_ltu. apply negb_false_iff, Z.ltb_lt. rewrite (unsigned_lit L) by lia. rewrite (unsigned_lit 64) by lia. lia. }
    rewrite Cbg; cbv iota.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    unfold al8, shad, SHB in W1, W2.
    replace (p + (L + 1) - 1) with (p + L) in W2 by lia.
    do 8 lstep.
    rewrite ?Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    assert (E1 : Z.land (2147450880 + p / 8) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land (2147450880 + (L + p) / 8) 18446744073709551608 = 8 * (((p + L) / 8 + 2147450880) / 8)).
    { replace (L + p) with (p + L) by lia. rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    lstep. lstep. rewrite E1, E2.
    lstep. lstep. lstep. lstep. if_cases K.
    + pose proof (acc_shadow_bytes m p (L + 1) AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + L) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      replace (2147450880 + (L + p) / 8) with ((p + L) / 8 + 2147450880) by (replace (L + p) with (p + L) by lia; lia).
      assert (EUsh : bv_unsigned (Z_to_bv 64 ((p + L) / 8 + 2147450880)) = (p + L) / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
      do 6 lstep. lstep. if_cases K2.
      * lstep. lstep. if_cases K3.
        -- apply evt_done. unfold atoi_prepi. do 25 eexists.
           split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (atoi_rip p (L + 1)); try assumption; try (unfold kHighShadowEnd; lia).
      * zify_cond K2.
        eapply evt_cut.
        { eapply (atoi_loop (Z.to_nat ((p + L) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a2' & a3' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold atoi_prepi. do 25 eexists.
           split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (atoi_rip p (L + 1)); try assumption; try (unfold kHighShadowEnd; lia).
    + apply evt_done. unfold atoi_prepi. do 25 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - lstep.
    assert (Cbg : negb (bv_ltu (Z_to_bv 64 L) (Z_to_bv 64 64)) = true).
    { unfold bv_ltu. apply negb_true_iff, Z.ltb_ge. rewrite (unsigned_lit L) by lia. rewrite (unsigned_lit 64) by lia. lia. }
    rewrite Cbg; cbv iota. lstep. if_true.
    apply (atoi_rip p (L + 1)); try assumption; try (unfold kHighShadowEnd; lia).
Qed.

End WithRIP.

Definition iatoi_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rv erw : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - IATOI_DEPTH, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned tp + -164) [C4 erw].

Theorem iatoi_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (A : Z) (str : list byte)
    (fv : list byte -> word) (fe : list byte -> Z) (fr : list byte -> word -> word) (ev can : word) (lo : Z),
  rip_stmt -> strtol_body_stmt fv fe fr ->
  bytes_at asegs m A (str ++ [Z_to_bv 8 0]) -> A + Z.of_nat (length str) + 1 <= 2^47 -> Z.of_nat (length str) + 1 <= 2^40 ->
  rw_cells asegs m (bv_unsigned tp + -164) [C4 ev] ->
  bytes_at asegs m STRTOL_SSP_GOT (le8 (Z_to_bv 64 STRTOL_SSP_GUARD)) -> bytes_at asegs m STRTOL_SSP_GUARD (le8 can) ->
  stk asegs m lo (bv_unsigned sp) -> lo + IATOI_DEPTH <= bv_unsigned sp -> kHighShadowEnd < lo -> bv_unsigned sp <= 2^47 ->
  0 <= A -> (forall nn, 1 <= nn <= Z.of_nat (length str) + 1 -> chk_ok m A nn) ->
  (A + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= A) ->
  (bv_unsigned tp + -164 + 4 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -164) ->
  (STRTOL_SSP_GOT + 8 <= lo \/ bv_unsigned sp <= STRTOL_SSP_GOT) ->
  (STRTOL_SSP_GUARD + 8 <= lo \/ bv_unsigned sp <= STRTOL_SSP_GUARD) ->
  (STRTOL_SSP_GUARD + 8 <= bv_unsigned tp + -164 \/ bv_unsigned tp + -164 + 4 <= STRTOL_SSP_GUARD) ->
  (bv_unsigned tp + -164 + 4 <= A \/ A + Z.of_nat (length str) + 1 <= bv_unsigned tp + -164) ->
  m2s_cells m -> icells_sx m -> rw_cells asegs m 0xb1918 [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  bytes_at asegs m 0xa7de8 (le8 (wa STRTOL)) ->
  bytes_at asegs m 0xa5f48 (le8 (wa 0xae438)) -> bytes_at asegs m (0xae438 + 29) [Z_to_bv 8 1] ->
  0 <= fe str <= Z.of_nat (length str) ->
  (bv_unsigned tp + -164 + 4 <= 0x7fff8000 \/ 0x10007fff8000 <= bv_unsigned tp + -164) ->
  (bv_unsigned tp + -164 + 4 <= 0xa5f40 \/ 0x14285e <= bv_unsigned tp + -164) ->
  evt asegs (iatoi_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (sx32 (fv str)) (fr str ev) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x45230) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A str fv fe fr ev can lo.
  intros RIP SB STR A47 N40 ERR GOT CAN ST LO LOLO SPH A0 CHK
    SEPS SEPT SEPG SEPGU SEPGT SEPTA M2S ICX AI MI RSLOT AFSLOT AF29 HEEND TPSH TPMETA.
  unfold kHighShadowEnd, IATOI_DEPTH in *.
  pose proof (bv_unsigned_in_range 64 sp) as HSPR. unfold bv_modulus in HSPR. cbn [Z.of_N] in HSPR.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(usp - 2640, usp); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m) as MU.
  pose proof (munch_refl [(usp - 2640, usp); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m) as MUm.
  pose proof (wmono_refl asegs m) as WM.
  pose proof STR as STRm. change (parked (bytes_at asegs m A (str ++ [Z_to_bv 8 0]))) in STRm.
  lstep.
  carve_frame 2160%nat ST.
  do 15 lstep.
  call asan_init_spec; [exact AI| rewrite EU2160; exact ST| lia| lia| assumption|].
  rewrite EU2160 in *.
  lazymatch goal with H : stk asegs _ lo (usp + -2160) |- _ => rename H into ST1 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AF0c : ro_cells asegs mm 0xa5f48 [C8 (wa 0xae438)]) by (split; [cbn; tauto| cbn [cells_bytes cbytes app]; exact AFSLOT]);
    assert (AF1c : ro_cells asegs mm (bv_unsigned (wa 0xae438) + 29) [C1 (Z_to_bv 8 1)]) by (rewrite wa_unsigned by lia; exact (ro_C1_of_bytes _ _ _ AF29));
    assert (RS0c : ro_cells asegs mm 0xa7de8 [C8 (Z_to_bv 64 0x9e4e0)]) by (split; [cbn; tauto| cbn [cells_bytes cbytes app]; exact RSLOT])
  end.
  do 4 lstep. if_false. do 9 lstep.
  assert (EU96 : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; lia).
  lazymatch type of FR with rw_cells _ ?mm _ (CB 2064 ?j0 :: C8 ?v :: ?rest) =>
    destruct (rwc_split asegs mm (usp + -2160) (usp + -96) [CB 2064 j0] (C8 v :: rest) FR ltac:(cbn; lia)) as [FRL FR2];
    destruct (rwc_split asegs mm (usp + -96) (usp + -88) [C8 v] rest FR2 ltac:(cbn; lia)) as [FRE FRH];
    clear FR FR2
  end.
  pose proof SB as SBs. unfold strtol_body_stmt in SBs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply SBs with (A:=A)(Ep:=(usp+-96))(str:=str)(lo:=lo)(can:=can)(ev:=ev);
      rewrite ?EU96; rewrite ?EU2160;
      [exact STR|lia|lia|exact FRE|exact ERR|exact GOT|exact CAN|exact ST1|lia
      |(destruct SEPS;lia)|lia|(destruct SEPT;lia)|(destruct SEPT;lia)|lia|lia
      |(destruct SEPGT;lia)|lia|assumption|lia]
    | post_call asegs mm ] end.
  rewrite ?EU96 in *. rewrite ?EU2160 in *.
  lazymatch goal with H : rw_cells asegs _ (usp + -96) [C8 (Z_to_bv 64 (A + fe str))] |- _ => rename H into LE end.
  do 3 lstep.
  lazymatch goal with H : stk asegs _ lo (usp + -2160) |- _ => rename H into STq end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm)
      by (apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn [outside]; destruct TPSH as [T|T]; lia);
    assert (M2S1 : m2s_cells mm) by (destruct M2S as (M2a & M2b & M2c); split; [| split];
      [ apply (rw_cells_agree asegs m mm _ _ M2a); [| exact WM]; apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia
      | apply (rw_cells_agree asegs m mm _ _ M2b); [| exact WM]; apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia
      | apply (rw_cells_agree asegs m mm _ _ M2c); [| exact WM]; apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia ]);
    assert (CHK1 : forall nn, 1 <= nn <= Z.of_nat (length str) + 1 -> chk_ok mm A nn)
      by (intros nn Hnn; apply (chk_ok_agree m mm A nn (CHK nn Hnn) ltac:(lia) ltac:(lia) AGS));
    assert (ICX1 : icells_sx mm) by (destruct ICX as (ICc1 & ICc2); split;
      [ apply (ro_cells_agree asegs m mm _ _ ICc1); apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia
      | apply (ro_cells_agree asegs m mm _ _ ICc2); apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia ]);
    assert (STR1 : bytes_at asegs mm A (str ++ [Z_to_bv 8 0]))
      by (unfold parked in STRm; refine (bytes_at_transport asegs _ m mm _ _ STRm MUm _);
          cbn [disjoint_from]; rewrite length_app; cbn [length Nat.add];
          split; [destruct SEPS; lia| split; [destruct SEPTA; lia| exact I]]);
    clear AGS
  end.
  lazymatch goal with H : mem_inv asegs ?mm |- _ => rename H into MIq end.
  destruct (Z_le_dec 1 (fe str)) as [Ene | E0].
  - assert (Cbeq : bv_eqb (Z_to_bv 64 A) (Z_to_bv 64 (A + fe str)) = false)
    by (unfold bv_eqb; apply Z.eqb_neq; rewrite (unsigned_lit A) by lia; rewrite (unsigned_lit (A + fe str)) by lia; lia).
  rewrite Cbeq; cbv iota. lstep.
  assert (Cbgeu : negb (bv_ltu (Z_to_bv 64 (A + fe str)) (Z_to_bv 64 A)) = true)
    by (unfold bv_ltu; apply negb_true_iff, Z.ltb_ge; rewrite (unsigned_lit A) by lia; rewrite (unsigned_lit (A + fe str)) by lia; lia).
  rewrite Cbgeu; cbv iota.
  eapply evt_cut.
  { eapply (atoi_chk RIP (A + fe str) A (fe str));
      [ exact STq | lia | unfold kHighShadowEnd; lia | lia | reflexivity | lia | lia | lia
      | exact (CHK1 (fe str + 1) ltac:(lia)) | exact ICX1 | exact M2S1 | exact MIq ]. }
  intros ms' Hpre. unfold atoi_prepi in Hpre.
  destruct Hpre as (m2 & ra2 & t0b & t1b & t2b & s0b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & s2b & s3b & s4b & s5b & s6b & s7b & s8b & t3b & t4b & t5b & t6b & -> & MUc & WMc & MIc & STc).
  lazymatch type of FRL with rw_cells _ ?xmm _ ?csL => assert (FRL2 : rw_cells asegs m2 (usp + -2160) csL) by (apply (rw_cells_agree asegs xmm m2 (usp + -2160) csL FRL); [| exact WMc]; apply (agree_of_munch _ _ _ _ MUc); intros y Hy; cbn in Hy |- *; lia) end.
  lazymatch type of LE with rw_cells _ ?xmm _ ?csE => assert (LE2 : rw_cells asegs m2 (usp + -96) csE) by (apply (rw_cells_agree asegs xmm m2 (usp + -96) csE LE); [| exact WMc]; apply (agree_of_munch _ _ _ _ MUc); intros y Hy; cbn in Hy |- *; lia) end.
  lazymatch type of FRH with rw_cells _ ?xmm _ ?csH => assert (FRH2 : rw_cells asegs m2 (usp + -88) csH) by (apply (rw_cells_agree asegs xmm m2 (usp + -88) csH FRH); [| exact WMc]; apply (agree_of_munch _ _ _ _ MUc); intros y Hy; cbn in Hy |- *; lia) end.
  do 2 lstep. do 10 lstep. lstep. lstep.
  release_frame FRL2 STc (usp + -96). release_frame LE2 STc (usp + -88). release_frame FRH2 STc (usp).
  rewrite ?Z.add_0_r. unfold iatoi_post, sx32. sys_finish.
  + rewrite ?EU. eapply munch_trans; [exact MU | ].
    intros xx Hxx. apply (MUc xx). cbn [outside] in Hxx |- *. destruct Hxx as (Hb1 & _). refine (conj _ I). intro Hc. apply Hb1. unfold IATOI_DEPTH in *. lia.
  + rewrite ?EU. eapply wmono_trans; [exact WM | exact WMc].
  + rewrite EU; assumption.
  + lazymatch goal with H : rw_cells asegs _ (bv_unsigned tp + -164) [C4 (fr str ev)] |- _ =>
      eapply (rw_cells_transport _ _ _ _ _ _ H MUc WMc); cbn [disjoint_from cells_size csize]; destruct SEPT as [T|T]; lia end.
  - assert (E0' : fe str = 0) by lia.
    assert (Cbeq : bv_eqb (Z_to_bv 64 A) (Z_to_bv 64 (A + fe str)) = true)
      by (rewrite E0', Z.add_0_r; unfold bv_eqb; apply Z.eqb_refl).
    rewrite Cbeq; cbv iota.
    do 4 lstep.
    assert (Haeq : Z_to_bv 64 A = Z_to_bv 64 (A + Z.of_nat 0)) by (f_equal; lia).
    rewrite Haeq at 1. clear Haeq.
    eapply evt_cut.
    { eapply (atoi_ws (nblank (str ++ [Z_to_bv 8 0])) 0%nat A str);
        [ exact STR1 | lia | lia | lia | reflexivity | rewrite Nat.add_0_l; reflexivity | exact MIq ]. }
    intros ms' (a0' & a3' & a4' & ->).
    lstep.
    pose proof (fix_off_range str) as FOR.
    lazymatch goal with H : mem_inv asegs m0 |- _ => rename H into MI0 end.
    lazymatch goal with H : stk asegs m0 lo (usp + -2160) |- _ => rename H into STq0 end.
    assert (AGS0 : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m m0)
      by (apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn [outside]; destruct TPSH as [T|T]; lia).
    assert (CHK0 : chk_ok m0 A (fix_off (str ++ [Z_to_bv 8 0]) + 1))
      by (apply (chk_ok_agree m m0 A _ (CHK (fix_off (str ++ [Z_to_bv 8 0]) + 1) ltac:(lia)) ltac:(lia) ltac:(lia) AGS0)).
    assert (M2S0 : m2s_cells m0) by (destruct M2S as (M2a & M2b & M2c); split; [|split];
      [ apply (rw_cells_agree asegs m m0 _ _ M2a); [| exact WM]; apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia
      | apply (rw_cells_agree asegs m m0 _ _ M2b); [| exact WM]; apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia
      | apply (rw_cells_agree asegs m m0 _ _ M2c); [| exact WM]; apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia ]).
    assert (ICX0 : icells_sx m0) by (destruct ICX as (ICc1 & ICc2); split;
      [ apply (ro_cells_agree asegs m m0 _ _ ICc1); apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia
      | apply (ro_cells_agree asegs m m0 _ _ ICc2); apply (agree_of_munch _ _ _ _ MUm); intros y Hy; cbn in Hy |- *; destruct TPMETA as [T|T]; lia ]).
    eapply evt_cut.
    { eapply (atoi_chk RIP (A + fix_off (str ++ [Z_to_bv 8 0])) A (fix_off (str ++ [Z_to_bv 8 0])));
        [ exact STq0 | lia | unfold kHighShadowEnd; lia | lia | reflexivity | lia | lia | lia
        | exact CHK0 | exact ICX0 | exact M2S0 | exact MI0 ]. }
    intros ms' Hpre. unfold atoi_prepi in Hpre.
    destruct Hpre as (m2 & ra2 & t0b & t1b & t2b & s0b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & s2b & s3b & s4b & s5b & s6b & s7b & s8b & t3b & t4b & t5b & t6b & -> & MUc & WMc & MIc & STc).
    lazymatch type of FRL with rw_cells _ ?xmm _ ?csL => assert (FRL2 : rw_cells asegs m2 (usp + -2160) csL) by (apply (rw_cells_agree asegs xmm m2 (usp + -2160) csL FRL); [| exact WMc]; apply (agree_of_munch _ _ _ _ MUc); intros y Hy; cbn in Hy |- *; lia) end.
    lazymatch goal with HE : rw_cells asegs m0 (usp + -96) ?csE |- _ => assert (LE2 : rw_cells asegs m2 (usp + -96) csE) by (apply (rw_cells_agree asegs m0 m2 (usp + -96) csE HE); [| exact WMc]; apply (agree_of_munch _ _ _ _ MUc); intros y Hy; cbn in Hy |- *; lia) end.
    lazymatch type of FRH with rw_cells _ ?xmm _ ?csH => assert (FRH2 : rw_cells asegs m2 (usp + -88) csH) by (apply (rw_cells_agree asegs xmm m2 (usp + -88) csH FRH); [| exact WMc]; apply (agree_of_munch _ _ _ _ MUc); intros y Hy; cbn in Hy |- *; lia) end.
    do 2 lstep. do 10 lstep. lstep. lstep.
    release_frame FRL2 STc (usp + -96). release_frame LE2 STc (usp + -88). release_frame FRH2 STc (usp).
    rewrite ?Z.add_0_r. unfold iatoi_post, sx32. sys_finish.
    + rewrite ?EU. eapply munch_trans; [exact MUm | ].
      intros xx Hxx. apply (MUc xx). cbn [outside] in Hxx |- *. destruct Hxx as (Hb1 & _). refine (conj _ I). intro Hc. apply Hb1. unfold IATOI_DEPTH in *. lia.
    + rewrite ?EU. eapply wmono_trans; [exact WM | exact WMc].
    + rewrite EU; assumption.
    + lazymatch goal with H : rw_cells asegs _ (bv_unsigned tp + -164) [C4 (fr str ev)] |- _ =>
        eapply (rw_cells_transport _ _ _ _ _ _ H MUc WMc); cbn [disjoint_from cells_size csize]; destruct SEPT as [T|T]; lia end.
Qed.
