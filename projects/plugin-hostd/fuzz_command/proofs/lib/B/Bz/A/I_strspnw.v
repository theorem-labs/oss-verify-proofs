(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated unchanged from an earlier relocation of this file for fuzz_command, for the image this tree pins (fuzz_command.asan-ubsan sha256 bbe55d24). *)
(* [comment removed for export] *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A Require Import Shadow IcptSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A Require Import R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit I_pck I_strncmpw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* The strspn wrapper of fuzz_command.asan: the exported symbol at 0x45194 is a one-instruction jump to the
   interceptor body at 0x4685c.  The body calls TryAsanInitFromRtl (0x5f68c), then REAL(strspn) through the slot
   0xa7c98 (musl strspn at 0x9f268), then, with common_flags()->intercept_strspn set (byte 247 of the flags record
   whose address is in 0xa5f40), checks [s2, s2 + internal_strlen(s2) + 1) and then [s1, s1 + r + 1)
   (strict_string_checks, byte 245, clear) with the quick shadow check and __asan_region_is_poisoned (0x5a1f8).
   Ported from openssl/echconfiglist_parser lib/As/N6_strspn.v (body 0x1aea48, stub 0x1ad368): the same code
   modulo relocation; the library call is the section hypothesis SS. *)

Definition i_strspn_wrap : Z := 0x45194.
Notation ISTRSPN_DEPTH := 2240%Z (only parsing).

(* The cells the walk reads: the REAL(strspn) slot, the common_flags pointer, intercept_strspn and
   strict_string_checks. *)
Definition icells_sp (m : mem) : Prop :=
  ro_cells asegs m 0xa7c98 [C8 (Z_to_bv 64 0x9f268)]
  /\ ro_cells asegs m 0xa5f40 [C8 (Z_to_bv 64 0x142768)]
  /\ ro_cells asegs m 0x14285f [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x14285d [C1 (Z_to_bv 8 0)].

(* The span length, as lib/B/Prog/strspn_c.v states it. *)
Definition in_set (set : list byte) (x : byte) : bool :=
  existsb (fun c => Z.eqb (bv_unsigned c) (bv_unsigned x)) set.

Fixpoint spn_len (set s : list byte) : nat :=
  match s with
  | [] => O
  | x :: s' => if in_set set x then S (spn_len set s') else O
  end.

(* musl strspn at 0x9f268, stated as lib/B/Prog/strspn_c.v states strspn_contract. *)
Definition strspn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (str set : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (spn_len set str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition strspn_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str set : list byte) (lo : Z) (can : word),
  bytes_at asegs m (bv_unsigned a0) (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str ->
  bytes_at asegs m (bv_unsigned a1) (set ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) set ->
  bytes_at asegs m 0xa6bf8 (le8 (Z_to_bv 64 0x604158)) -> bytes_at asegs m 0x604158 (le8 can) ->
  stk asegs m lo (bv_unsigned sp) -> (lo + 48 <= bv_unsigned sp)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 + Z.of_nat (length set) + 1 <= lo \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (0xa6bf8 + 8 <= lo \/ bv_unsigned sp <= 0xa6bf8)%Z ->
  (0x604158 + 8 <= lo \/ bv_unsigned sp <= 0x604158)%Z ->
  mem_inv asegs m ->
  evt asegs (strspn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc str set lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9f268) fc None m (seg_rom asegs)).

(* The slow shadow scan after the quick check of [s2, s2 + n). *)
Lemma isspn_loop1 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x46ae8) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x46ad8) fc None m (seg_rom asegs)).
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

(* The slow shadow scan after the quick check of [s1, s1 + n). *)
Lemma isspn_loop2 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x46bbc) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x46bac) fc None m (seg_rom asegs)).
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
Hypothesis SS : strspn_stmt.

(* After the check of [p, p + L + 1) (p = s2, L = internal_strlen(s2)): back at 0x4692c with a0 = s5. *)
Definition chk1_post (sp p L : Z) (gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2160)) gp tp t0' t1' t2' (Z_to_bv 64 sp) s1 s5 a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 (L + 1)) s3' s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x4692c) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2240, sp - 2160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2160).

Lemma isspn_rip1 : forall (sp p L : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2160) -> lo <= sp - ISTRSPN_DEPTH -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 <= L -> p + L + 1 < 2^63 ->
  acc asegs m p (L + 1) -> rng_ok p (L + 1) -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (chk1_post sp p L gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 sp) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (L + 1)) (Z_to_bv 64 p) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x46af0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2240, sp - 2160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2160)) = sp + -2160) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO ltac:(lia)) as (RIM & N40).
  do 3 lstep. (* mv a0,s3; mv a1,s2; jal __asan_region_is_poisoned *)
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. lstep. lstep. if_true.
  apply evt_done. unfold chk1_post. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma isspn_chk1 : forall (sp p L : Z) (ra gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2160) -> lo <= sp - ISTRSPN_DEPTH -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 <= L -> p + L + 1 < 2^63 ->
  chk_ok m p (L + 1) -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (chk1_post sp p L gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 sp) s1 (Z_to_bv 64 L) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 p) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x468dc) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN (AC & QW & RO) (G2 & SHC & HM) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2240, sp - 2160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (M2S : m2s_cells m) by (split; [exact G2| split; [exact SHC| exact HM]]). unfold SHB in SHC.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUr : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (L + 1)) = L + 1) by (apply unsigned_lit; lia).
  assert (EUsp : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  lstep. (* addi s2,a0,1 *)
  lstep. rewrite (lxor_ones64 p) by lia. (* not a1,s3 *)
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
    do 5 lstep. (* ld; ld; or; mv a0,s5; bnez *)
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
        -- apply evt_done. unfold chk1_post. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (isspn_rip1 sp p L); try assumption; unfold kHighShadowEnd; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (isspn_loop1 (Z.to_nat ((p + (L + 1) - 1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a3' & a4' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold chk1_post. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (isspn_rip1 sp p L); try assumption; unfold kHighShadowEnd; lia.
    + apply evt_done. unfold chk1_post. do 17 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - if_true. lstep. lstep. if_true. (* mv a0,s5; bnez s2 *)
    apply (isspn_rip1 sp p L); try assumption; unfold kHighShadowEnd; lia.
Qed.

(* After the check of [p, p + L + 1) (p = s1, L = r): at the epilogue 0x46984 with a0 = r. *)
Definition chk2_post (sp L : Z) (gp tp s4 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2160)) gp tp t0' t1' t2' (Z_to_bv 64 sp) s1' (Z_to_bv 64 L) a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 (L + 1)) s3' s4 (Z_to_bv 64 L) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x46984) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2240, sp - 2160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2160).

Lemma isspn_rip2 : forall (sp p L : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2160) -> lo <= sp - ISTRSPN_DEPTH -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 <= L -> p + L + 1 < 2^63 ->
  acc asegs m p (L + 1) -> rng_ok p (L + 1) -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (chk2_post sp L gp tp s4 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (L + 1)) s3 s4 (Z_to_bv 64 L) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x46bc4) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2240, sp - 2160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2160)) = sp + -2160) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO ltac:(lia)) as (RIM & N40).
  do 3 lstep. (* mv a0,s1; mv a1,s2; jal __asan_region_is_poisoned *)
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. lstep. lstep. if_true.
  apply evt_done. unfold chk2_post. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma isspn_chk2 : forall (sp p L : Z) (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2160) -> lo <= sp - ISTRSPN_DEPTH -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 <= L -> p + L + 1 < 2^63 ->
  ro_cells asegs m 0x14285d [C1 (Z_to_bv 8 0)] ->
  chk_ok m p (L + 1) -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (chk2_post sp L gp tp s4 s6 (Z_to_bv 64 0x142768) s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 p) (Z_to_bv 64 L) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 L) s6 (Z_to_bv 64 0x142768) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4692c) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN SF (AC & QW & RO) (G2 & SHC & HM) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2240, sp - 2160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (M2S : m2s_cells m) by (split; [exact G2| split; [exact SHC| exact HM]]). unfold SHB in SHC.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUr : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (L + 1)) = L + 1) by (apply unsigned_lit; lia).
  assert (EUsp : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  lstep. lstep. lstep. if_false. (* lbu a1,245(s7); mv s3,a0; bnez a1 *)
  lstep. (* addi s2,s3,1 *)
  lstep. rewrite (lxor_ones64 p) by lia. (* not a1,s1 *)
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
    do 4 lstep. (* ld; ld; or; bnez *)
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
        -- apply evt_done. unfold chk2_post. do 18 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (isspn_rip2 sp p L); try assumption; unfold kHighShadowEnd; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (isspn_loop2 (Z.to_nat ((p + (L + 1) - 1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a3' & a4' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. unfold chk2_post. do 18 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (isspn_rip2 sp p L); try assumption; unfold kHighShadowEnd; lia.
    + apply evt_done. unfold chk2_post. do 18 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - if_true. lstep. if_true. (* bnez s2 *)
    apply (isspn_rip2 sp p L); try assumption; unfold kHighShadowEnd; lia.
Qed.

Definition isspn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ISTRSPN_DEPTH, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

(* From the return of REAL(strspn) at 0x468b4 (a0 = r, s1 = s1, s2 = 1 from TryAsanInitFromRtl, s3 = s2) to the
   return of the wrapper. *)
Lemma isspn_back : forall (sp s c : Z) (str cset : list byte)
    (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 : word) F fc (m : mem) (lo : Z) (fjunk : list byte),
  stk asegs m lo (sp + -2160) -> lo <= sp - ISTRSPN_DEPTH -> kHighShadowEnd < lo -> sp <= 2^47 ->
  0 <= s -> 0 <= c -> s + Z.of_nat (spn_len cset str) + 1 <= 2^47 -> c + Z.of_nat (length cset) + 1 <= 2^47 ->
  bytes_at asegs m c (cset ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) cset ->
  chk_ok m c (Z.of_nat (length cset) + 1) -> chk_ok m s (Z.of_nat (spn_len cset str) + 1) -> m2s_cells m ->
  ro_cells asegs m 0xa5f40 [C8 (Z_to_bv 64 0x142768)] -> ro_cells asegs m 0x14285f [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x14285d [C1 (Z_to_bv 8 0)] -> mem_inv asegs m ->
  rw_cells asegs m (sp + -80) [C8 vs8; C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra] ->
  rw_cells asegs m (sp + -2160) [CB 2080 fjunk] ->
  evt asegs (isspn_post vra (Z_to_bv 64 sp) gp tp vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 s9 s10 s11 F fc
                 (Z.of_nat (spn_len cset str)) lo m)
    (MS (mkR ra (Z_to_bv 64 (sp + -2160)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 s)
             (Z_to_bv 64 (Z.of_nat (spn_len cset str))) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 1) (Z_to_bv 64 c) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x468b4) fc None m (seg_rom asegs)).
Proof.
  intros until fjunk. intros ST LO LOLO SPH S0 C0 SH CH SET CNZ CSC CSS M2S GCF IFL SFL MI FRs FR.
  unfold kHighShadowEnd in *.
  assert (LO0 : 0 <= lo) by lia.
  pose proof (munch_refl [(sp - 2240, sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
  assert (EUR : bv_unsigned (Z_to_bv 64 (Z.of_nat (spn_len cset str))) = Z.of_nat (spn_len cset str)) by (apply unsigned_lit; lia).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (sp + -2160)) = sp + -2160) by (apply unsigned_lit; lia).
  lstep. if_false. (* beqz s2 *)
  lstep. lstep. lstep. lstep. if_false. (* auipc; ld s7 <- 0xa5f40; lbu a1,247(s7); beqz a1 *)
  do 5 lstep. (* mv s5,a0; addi s6,s0,-2048; addi s6,s6,-104; mv a0,s3; jal internal_strlen *)
  call internal_strlen_spec; [reflexivity| split; [exact SET| exact CNZ]| assumption|].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGL : agree_on (fun x => 0 <= x < 0x1000000) m mm) by (apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; lia);
    assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm) by (apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; lia);
    pose proof (m2s_cells_agree m mm M2S AGL ltac:(assumption)) as M2S1;
    pose proof (chk_ok_agree m mm c _ CSC ltac:(lia) ltac:(lia) AGS) as CSC1; clear AGL AGS
  end.
  call (isspn_chk1 sp c (Z.of_nat (length cset))); try eassumption; try (unfold kHighShadowEnd; lia).
  lazymatch goal with H : stk asegs _ lo (sp + -2160) |- _ => rename H into ST1 end.
  clear M2S1 CSC1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGL : agree_on (fun x => 0 <= x < 0x1000000) m mm) by (apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; lia);
    assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm) by (apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; lia);
    pose proof (m2s_cells_agree m mm M2S AGL ltac:(assumption)) as M2S2;
    pose proof (chk_ok_agree m mm s _ CSS ltac:(lia) ltac:(lia) AGS) as CSS2; clear AGL AGS
  end.
  call (isspn_chk2 sp s (Z.of_nat (spn_len cset str))); try eassumption; try (unfold kHighShadowEnd; lia).
  lazymatch goal with H : stk asegs _ lo (sp + -2160) |- _ => rename H into ST2 end.
  clear M2S2 CSS2.
  do 11 lstep. (* addi sp,sp,128; ld ra, s0 .. s8 *)
  release_frame FR ST2 (sp + -80). release_frame FRs ST2 sp.
  lstep. lstep. (* addi sp,sp,2032; ret *)
  unfold isspn_post. sys_finish.
  all: rewrite ?EU; assumption.
Qed.

(* Hides the string facts from the per-step transport; they are carried over the steps by MU. *)
Local Definition parked (P : Prop) : Prop := P.

(* From the wrapper entry 0x45194 (the jump to the body) to its return. *)
Theorem isspn_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s c : Z) (str cset : list byte) (lo : Z) (can : word),
  a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 c ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRSPN_DEPTH -> kHighShadowEnd < lo -> bv_unsigned sp <= 2^47 ->
  0 <= s -> 0 <= c -> s + Z.of_nat (spn_len cset str) + 1 <= 2^47 -> c + Z.of_nat (length cset) + 1 <= 2^47 ->
  bytes_at asegs m s (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str ->
  bytes_at asegs m c (cset ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) cset ->
  bytes_at asegs m 0xa6bf8 (le8 (Z_to_bv 64 0x604158)) -> bytes_at asegs m 0x604158 (le8 can) ->
  (s + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= s) ->
  (c + Z.of_nat (length cset) + 1 <= lo \/ bv_unsigned sp <= c) ->
  chk_ok m c (Z.of_nat (length cset) + 1) -> chk_ok m s (Z.of_nat (spn_len cset str) + 1) -> m2s_cells m ->
  rw_cells asegs m 0xb1918 [C1 (Z_to_bv 8 1)] -> icells_sp m -> mem_inv asegs m ->
  evt asegs (isspn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.of_nat (spn_len cset str)) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 i_strspn_wrap) fc None m (seg_rom asegs)).
Proof using RIP SS.
  intros until can. intros -> -> ST LO LOLO SPH S0 C0 SH CH STR SNZ SET CNZ GOT CAN SEPS SEPC CSC CSS M2S AI ICP MI.
  unfold kHighShadowEnd, i_strspn_wrap in *.
  assert (FLs : length (str ++ [Z_to_bv 8 0]) = (length str + 1)%nat) by (rewrite length_app; reflexivity).
  assert (FLc : length (cset ++ [Z_to_bv 8 0]) = (length cset + 1)%nat) by (rewrite length_app; reflexivity).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (LO0 : 0 <= lo) by lia.
  pose proof ICP as (RSP & GCF & IFL & SFL).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
  assert (EU2160 : bv_unsigned (Z_to_bv 64 (usp + -2160)) = usp + -2160) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(usp - 2240, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof STR as STRm. change (parked (bytes_at asegs m s (str ++ [Z_to_bv 8 0]))) in STRm.
  pose proof SET as SETm. change (parked (bytes_at asegs m c (cset ++ [Z_to_bv 8 0]))) in SETm.
  clear STR SET ICP.
  lstep. (* j 0x4685c *)
  carve_frame 80%nat ST. rename FR into FRs. carve_frame 2080%nat ST.
  do 16 lstep. (* the prologue; mv s3,a1; mv s1,a0; jal TryAsanInitFromRtl *)
  call try_init_spec; [exact AI| rewrite EU2160; exact ST| lia| lia| assumption|].
  rewrite EU2160 in *. lazymatch goal with H : stk asegs _ lo (usp + -2160) |- _ => rename H into ST1 end.
  do 6 lstep. (* auipc; ld a2 <- 0xa7c98; mv s2,a0; mv a0,s1; mv a1,s3; jalr a2 *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (bytes_at_transport asegs _ m mm _ _ STRm MU) as STR1; cbn [disjoint_from] in STR1;
    specialize (STR1 ltac:(split; [lia| exact I]));
    pose proof (bytes_at_transport asegs _ m mm _ _ SETm MU) as SET1; cbn [disjoint_from] in SET1;
    specialize (SET1 ltac:(split; [lia| exact I]))
  end.
  pose proof SS as SSs. unfold strspn_stmt in SSs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply SSs with (str := str) (set := cset) (lo := lo) (can := can);
      [ rewrite EUs; exact STR1| exact SNZ| rewrite EUc; exact SET1| exact CNZ| assumption| assumption
      | rewrite EU2160; exact ST1| rewrite EU2160; lia| rewrite EUs, EU2160; lia| rewrite EUc, EU2160; lia| lia| lia
      | assumption ]
    | post_call asegs mm ] end.
  try rewrite EU2160 in *.
  lazymatch goal with H : stk asegs _ lo (usp + -2160) |- _ => rename H into ST2 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AGL : agree_on (fun x => 0 <= x < 0x1000000) m mm) by (apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; lia);
    assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm) by (apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; lia);
    pose proof (m2s_cells_agree m mm M2S AGL ltac:(assumption)) as M2S1;
    pose proof (chk_ok_agree m mm c _ CSC ltac:(lia) ltac:(lia) AGS) as CSC1;
    pose proof (chk_ok_agree m mm s _ CSS ltac:(lia) ltac:(lia) AGS) as CSS1;
    pose proof (bytes_at_transport asegs _ m mm _ _ SETm MU) as SET2; cbn [disjoint_from] in SET2;
    specialize (SET2 ltac:(split; [lia| exact I])); clear AGL AGS
  end.
  call (isspn_back usp s c str cset); try eassumption; try (unfold kHighShadowEnd; lia).
  unfold isspn_post. sys_finish.
  all: rewrite ?EU; assumption.
Qed.

End WithRIP.
