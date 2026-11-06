(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new for plugin-hostd/fuzz_reply.asan (R2Cmp, port-reply): the body walk of the
   strrchr interceptor, in the tree's own words (lib/A/Bz), composed from I_pck.v internal_strlen_spec, I_strlen.v
   istrlen_spec, R_small.v / I_ikit.v (the init gate) and I_consts.v rip_stmt. No other pinned binary has this code
   (EvBound), so it is written new, in the form of I_strlen.v / I_strlenw.v. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/Bz/A/I_strrchr.v at commit debcdf3fa6a, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (46 numerals; per-numeral report). *)
(* The code (fuzz_reply.asan-ubsan, objdump of fuzz_reply.debug):
   - __interceptor_trampoline_strrchr 0x421fc: `j 0x438b0`;
   - ___interceptor_strrchr 0x438b0 (184 insns, frame 2032 + 112, ra and s0..s7 saved at sp-8 .. sp-72): AsanInited,
     TryAsanInitFromRtl, then common_flags()->intercept_strchr (byte +0xfd of 0x138168, 1 at run time) set, so
     COMMON_INTERCEPTOR_READ_STRING (s, internal_strlen (s) + 1): internal_strlen 0x653b0, the size test against 64
     (0x43928), the two-shadow-word quick check (0x4392c-0x43960), its byte loop (0x43a94-0x43ac4) or
     __asan_region_is_poisoned 0x559b4 (0x43ac8); then REAL(strrchr) through the slot 0x9fc90 (= musl strrchr 0x9740c),
     the epilogue and `ret` (0x43978-0x439a4);
   - musl strrchr 0x9740c (frame 32, ra/s0/s1 at sp-8 .. sp-24): `__memrchr (s, c, strlen (s) + 1)`, its strlen
     through the strlen TRAMPOLINE 0x421e4 (so the strlen interceptor, I_strlen.v istrlen_spec) and memrchr 0x96e50
     as a tail call (a byte loop from the end, no frame).
   Stack: 2144 (interceptor) + max (80 (region_is_poisoned), 32 (musl strrchr) + ISTRLEN_DEPTH 2224) = 4400. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck
  X_atexit IcptSpec D_kit I_ikit I_musl I_strnlenw I_strlenw I_strlen.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A Require I_pck.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* I_strlen.v's local helpers, copied: park the facts a frame's stores cannot touch, and move them across in one step. *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
Local Ltac zidle_nspz H A SP := lazymatch A with context [SP] => fail | _ => zidle1 H end.
Local Ltac zidle_beginz SP n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(SP - n, SP)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : ro_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u8arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u32arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u64arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : bytes_at segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u8ro segs m ?A _ |- _ => zidle_nspz H A SP
    end
  end.

Notation ISTRRCHR_DEPTH := 4400%Z (only parsing).

(* The interceptor's own fixed cells: common_flags()->intercept_strchr (0x138168 + 0xfd) and REAL(strrchr). *)
Definition icells_srr (m : mem) : Prop :=
  ro_cells asegs m 0x138265 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x9fc90 [C8 (Z_to_bv 64 0x9740c)].

(* ---- the answer ---- *)
(* the last index below j at which bs holds the byte value c *)
Fixpoint rchr_idx (c : Z) (bs : list byte) (j : nat) : option nat :=
  match j with
  | O => None
  | S j' => match nth_error bs j' with
            | Some b => if bv_unsigned b =? c then Some j' else rchr_idx c bs j'
            | None => rchr_idx c bs j'
            end
  end.
Definition rchr_res (x c : Z) (bs : list byte) (j : nat) : Z :=
  match rchr_idx c bs j with Some i => x + Z.of_nat i | None => 0 end.

(* ---- musl memrchr 0x96e50: the loop from the end ---- *)
Lemma mrr_loop : forall (j : nat) (x cz : Z) (bs : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= x -> x + Z.of_nat (length bs) < 2^64 -> (j <= length bs)%nat -> 0 <= cz < 256 ->
  bytes_at asegs m x bs -> mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (rchr_res x cz bs j) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 cz) (Z_to_bv 64 (x + Z.of_nat j)) (Z_to_bv 64 (- Z.of_nat j))
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x96e5c) fc None m (seg_rom asegs)).
Proof.
  induction j as [|j IH]; intros x cz bs ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    X0 XB JB CZ BY MI.
  - pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    change (- Z.of_nat 0) with 0. rewrite Z.add_0_r.
    lstep. if_true. lstep. lstep.
    unfold rchr_res; cbn [rchr_idx]. finish.
  - destruct (nth_error bs j) as [b|] eqn:EB; [| apply nth_error_None in EB; lia].
    pose proof (bytes_at_nth1 asegs m x bs j b BY EB) as B1. pose proof (ro_C1_of_bytes m _ _ B1) as CB.
    pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. change (2 ^ Z.of_N 8) with 256 in BR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    set (q := x + Z.of_nat j) in *.
    replace (x + Z.of_nat (S j)) with (q + 1) by (subst q; lia).
    replace (- Z.of_nat (S j)) with (- Z.of_nat j - 1) by lia.
    assert (EUj : bv_unsigned (Z_to_bv 64 (- Z.of_nat j - 1)) = 2^64 - Z.of_nat j - 1).
    { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
      rewrite <- (Z.mod_add (- Z.of_nat j - 1) 1 (2^64)) by lia. rewrite Z.mod_small; lia. }
    assert (EUx : bv_unsigned (Z_to_bv 64 (q + 1)) = q + 1) by (apply unsigned_lit; subst q; lia).
    assert (EUq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; subst q; lia).
    assert (EUcz : bv_unsigned (Z_to_bv 64 cz) = cz) by (apply unsigned_lit; lia).
    lstep. if_false.
    lstep. lstep. lstep. lstep. lstep.
    if_cases K.
    + zify_cond K.
      replace (- Z.of_nat j - 1 + 1) with (- Z.of_nat j) by lia.
      unfold rchr_res at 1. cbn [rchr_idx]. rewrite EB.
      destruct (Z.eqb_spec (bv_unsigned b) cz) as [Ecz|Ncz]; [exfalso; lia|].
      apply (IH x cz bs); try assumption; lia.
    + zify_cond K.
      lstep.
      unfold rchr_res. cbn [rchr_idx]. rewrite EB.
      destruct (Z.eqb_spec (bv_unsigned b) cz) as [Ecz|Ncz]; [|exfalso; lia].
      finish.
Qed.

(* ---- the interceptor's range check, READ_STRING (s, len + 1): 0x43918 .. 0x43964 ---- *)
(* the shadow byte loop 0x43ab0 - 0x43abc (the same loop as I_strncmpw.v isc_loop1, at strrchr's pcs) *)
Lemma isr_loop1 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a2' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 e) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x43ac0) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x43ab0) fc None m (seg_rom asegs)).
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

(* the slow arm 0x43ac8: __asan_region_is_poisoned (s, len + 1) answers 0 on an addressable range *)
Lemma isr_rip : forall (sp p n : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - 2224 -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 < n -> p + n < 2^63 ->
  acc asegs m p n -> rng_ok p n -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 p) s3' s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x43964) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x43ac8) fc None m (seg_rom asegs)).
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
  apply evt_done. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* the whole check, from internal_strlen's return (a0 = len) to the REAL call at 0x43964 *)
Lemma isr_chk : forall (sp p r : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - 2224 -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 <= r -> p + r + 1 < 2^63 ->
  chk_ok m p (r + 1) -> m2s_cells m -> icells_sn m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 p) s3' s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x43964) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x43918) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN (AC & QW & RO) M2S (G70 & G2 & SHC & AI & ISL) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
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
      replace (2147450880 + (r + p) / 8) with ((p + (r + 1) - 1) / 8 + 2147450880) by (replace (p + (r + 1) - 1) with (r + p) by lia; lia).
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p (r + 1) AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + (r + 1) - 1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * lstep. lstep. if_cases K3.
        -- apply evt_done. do 18 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (isr_rip sp p (r + 1)); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (isr_loop1 (Z.to_nat ((p + (r + 1) - 1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a2' & a3' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 18 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (isr_rip sp p (r + 1)); try assumption; lia.
    + apply evt_done. do 18 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - if_true. lstep. if_true.
    apply (isr_rip sp p (r + 1)); try assumption; lia.
Qed.
End WithRIP.

(* ---- musl strrchr 0x9740c: __memrchr (s, c, strlen (s) + 1), strlen through the trampoline ---- *)
Section WithRIPSL.
Hypothesis RIP : rip_stmt.
Hypothesis SL : strlen_stmt.

Definition mstrrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2256, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma mstrrchr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s c : Z) (str slack : list byte) (lo : Z),
  a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 c -> 0 <= c < 256 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2256 -> kHighShadowEnd < lo -> bv_unsigned sp < 2^63 ->
  0 <= s <= 2^47 -> Z.of_nat (length str) < 2^40 -> s + Z.of_nat (length str) + 1 <= 2^47 ->
  bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 2256 \/ bv_unsigned sp <= s) ->
  chk_ok m s (Z.of_nat (length str) + 1) -> m2s_cells m -> icells_sn m -> icells_sl m -> mem_inv asegs m ->
  evt asegs (mstrrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (rchr_res s c (str ++ [Z_to_bv 8 0]) (S (length str))) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9740c) fc None m (seg_rom asegs)).
Proof using RIP SL.
  intros until lo. intros -> -> C0 ST LO LOLO SPH S0 L40 SH BUF NZ PAD SEPS CS M2S IC RSL MI.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 2256, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof IC as (G70 & G2 & SHC & AI & ISL). unfold icells_sl in RSL.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
  assert (EU32 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; lia).
  assert (BUF1 : bytes_at asegs m s (str ++ [Z_to_bv 8 0])).
  { pose proof BUF as B. replace (str ++ Z_to_bv 8 0 :: slack) with ((str ++ [Z_to_bv 8 0]) ++ slack) in B
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in B. destruct B as [B _]. exact B. }
  carve_frame 24%nat ST. rename FR into FRs. carve_frame 8%nat ST.
  zidle_beginz usp 32%Z MUz1 WMz1.
  xsteps_to 0x42288%Z.
  zidle_end MUz1 WMz1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CS2 : chk_ok mm s (Z.of_nat (length str) + 1))
      by (apply (chk_ok_agree m mm s _ CS ltac:(lia) ltac:(lia));
          apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]);
    assert (M2S2 : m2s_cells mm) by (destruct M2S as (M1 & M2 & M3); split; [| split];
      [ apply (rw_cells_agree asegs m mm _ _ M1); [| assumption]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree asegs m mm _ _ M2); [| assumption]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree asegs m mm _ _ M3); [| assumption]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia ]);
    assert (IC2 : icells_sn mm) by (split; [exact G70| split; [exact G2| split; [exact SHC| split; [exact AI| exact ISL]]]])
  end.
  call (istrlen_spec RIP SL);
    try solve [ reflexivity | exact BUF | exact NZ | exact PAD | exact CS2 | exact M2S2 | exact IC2 | exact RSL
              | exact L40 | exact SH | assumption | rewrite ?EU32; first [exact ST | lia] ].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU32 in H; rename H into ST end.
  do 8 lstep.
  release_frame FR ST (usp + -24). release_frame FRs ST usp.
  do 3 lstep.
  replace (Z.land c 255) with c by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small; lia).
  replace (s + (Z.of_nat (length str) + 1)) with (s + Z.of_nat (S (length str))) by lia.
  replace (0 - (Z.of_nat (length str) + 1)) with (- Z.of_nat (S (length str))) by lia.
  call (mrr_loop (S (length str)) s c (str ++ [Z_to_bv 8 0]));
    try solve [ exact BUF1 | assumption | rewrite ?length_app; cbn [length]; lia ].
  unfold mstrrchr_post. sys_finish.
  + rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  + rewrite EU. assumption.
Qed.

(* ---- the whole entry: trampoline 0x421fc .. the interceptor's `ret` ---- *)
Definition istrrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ISTRRCHR_DEPTH, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Theorem istrrchr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s c : Z) (str slack : list byte) (lo : Z),
  a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 c -> 0 <= c < 256 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRRCHR_DEPTH -> kHighShadowEnd < lo -> bv_unsigned sp < 2^63 ->
  0 <= s <= 2^47 -> Z.of_nat (length str) < 2^40 -> s + Z.of_nat (length str) + 1 <= 2^47 ->
  bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - ISTRRCHR_DEPTH \/ bv_unsigned sp <= s) ->
  chk_ok m s (Z.of_nat (length str) + 1) -> m2s_cells m -> icells_sn m -> icells_sl m -> icells_srr m -> mem_inv asegs m ->
  evt asegs (istrrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (rchr_res s c (str ++ [Z_to_bv 8 0]) (S (length str))) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x421fc) fc None m (seg_rom asegs)).
Proof using RIP SL.
  intros until lo. intros -> -> C0 ST LO LOLO SPH S0 L40 SH BUF NZ PAD SEPS CS M2S IC RSL ISR MI.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 4400, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof IC as (G70 & G2 & SHC & AI & ISL). pose proof ISR as (FLG & RSR). unfold icells_sl in RSL.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
  assert (EU2144 : bv_unsigned (Z_to_bv 64 (usp + -2144)) = usp + -2144) by (apply unsigned_lit; lia).
  assert (BUF1 : bytes_at asegs m s (str ++ [Z_to_bv 8 0])).
  { pose proof BUF as B. replace (str ++ Z_to_bv 8 0 :: slack) with ((str ++ [Z_to_bv 8 0]) ++ slack) in B
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in B. destruct B as [B _]. exact B. }
  carve_frame 72%nat ST. rename FR into FRs. carve_frame 2072%nat ST.
  zidle_beginz usp 2144%Z MUz1 WMz1.
  xsteps_to 0x59f38%Z.
  zidle_end MUz1 WMz1.
  call asan_inited_spec; [exact AI| assumption|].
  xsteps_to 0x5ae48%Z.
  call try_init_spec; [exact AI| rewrite EU2144; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2144 in H; rename H into ST end.
  xsteps_to 0x653b0%Z.
  call I_pck.internal_strlen_spec; [reflexivity| split; [exact BUF1| exact NZ]| assumption|].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CS2 : chk_ok mm s (Z.of_nat (length str) + 1))
      by (apply (chk_ok_agree m mm s _ CS ltac:(lia) ltac:(lia));
          apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]);
    assert (M2S2 : m2s_cells mm) by (destruct M2S as (M1 & M2 & M3); split; [| split];
      [ apply (rw_cells_agree asegs m mm _ _ M1); [| assumption]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree asegs m mm _ _ M2); [| assumption]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree asegs m mm _ _ M3); [| assumption]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia ]);
    assert (IC2 : icells_sn mm) by (split; [exact G70| split; [exact G2| split; [exact SHC| split; [exact AI| exact ISL]]]])
  end.
  call (isr_chk RIP usp s (Z.of_nat (length str)));
    try solve [ exact ST | exact CS2 | exact M2S2 | exact IC2 | assumption | unfold kHighShadowEnd; lia | lia ].
  lazymatch goal with H : stk asegs _ lo (usp + -2144) |- _ => rename H into ST end.
  xsteps_to 0x9740c%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CS3 : chk_ok mm s (Z.of_nat (length str) + 1))
      by (apply (chk_ok_agree m mm s _ CS ltac:(lia) ltac:(lia));
          apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]);
    assert (M2S3 : m2s_cells mm) by (destruct M2S as (M1 & M2 & M3); split; [| split];
      [ apply (rw_cells_agree asegs m mm _ _ M1); [| assumption]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree asegs m mm _ _ M2); [| assumption]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree asegs m mm _ _ M3); [| assumption]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia ]);
    assert (IC3 : icells_sn mm) by (split; [exact G70| split; [exact G2| split; [exact SHC| split; [exact AI| exact ISL]]]])
  end.
  call mstrrchr_spec;
    try solve [ reflexivity | exact BUF | exact NZ | exact PAD | exact CS3 | exact M2S3 | exact IC3 | exact RSL
              | exact L40 | exact SH | assumption | rewrite ?EU2144; first [exact ST | lia] ].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2144 in H; rename H into ST end.
  do 11 lstep.
  release_frame FR ST (usp + -72). release_frame FRs ST usp.
  lstep.
  unfold istrrchr_post. sys_finish.
  + rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  + rewrite EU. assumption.
Qed.
End WithRIPSL.
