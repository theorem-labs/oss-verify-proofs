(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bndiv/lib/A/I_memchrw.v, with its module paths and addresses changed; 39 of its 277 lines of code are new or changed and 16 lines of the source are left out. *)
(* Port-from: origin/cold/c-asan-rt-stateio-n 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Bz/A/I_memchrw.v.
   Changes (R1Str, 2026-10-29): module path fuzz_state -> fuzz_reply; 13 fuzz_state.asan address numerals moved to fuzz_reply.asan, each paired by code (instruction by instruction, relocation fields masked) or, for a data cell, by the instruction that loads it (table: lib/A/RT_kit.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit IcptSpec D_kit I_ikit I_musl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.



Notation IMEMCHR_DEPTH := 2208%Z (only parsing).

(* [comment removed for export] *)
Definition icells_mc (m : mem) : Prop :=
  ro_cells asegs m 0x9d9d0 [C8 (Z_to_bv 64 0xa60b8)]            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x9f728 [C8 (Z_to_bv 64 0x963d0)]         (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa60b8 [C8 (Z_to_bv 64 0x7fff8000)]      (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa6d98 [C1 (Z_to_bv 8 1)].              (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma imemchr_loop : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x44724) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44714) fc None m (seg_rom asegs)).
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

(* The length the interceptor checks after the call: up to and including the match, or the whole count when the
   result is the null pointer. *)
Definition memchr_len (s c n : Z) (buf : list byte) : Z :=
  if memchr_res s c n buf =? 0 then n else memchr_res s c n buf - s + 1.

Lemma memchr_len_chk : forall s c n buf, 0 < s -> memchr_len s c n buf = memchr_chk c n buf.
Proof.
  intros s c n buf Hs. unfold memchr_len, memchr_res, memchr_chk.
  destruct (find_byte c (firstn (Z.to_nat n) buf)) as [i|]; [| reflexivity].
  destruct (Z.eqb_spec (s + Z.of_nat i) 0); lia.
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.
Hypothesis MCH : memchr_stmt.

(* [comment removed for export] *)
Lemma imemchr_rip : forall (sp p len : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2128) -> lo <= sp - IMEMCHR_DEPTH -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 < len -> p + len < 2^63 ->
  acc asegs m p len -> rng_ok p len -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s4' s5' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2128)) gp tp t0' t1' t2' s0 s1' a0 a1' a2' a3' a4' a5' a6' a7'
                    s2' s3 s4' s5' s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x44604) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2208, sp - 2128)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2128))
    (MS (mkR ra (Z_to_bv 64 (sp + -2128)) gp tp t0 t1 t2 s0 (Z_to_bv 64 len) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4472c) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  idtac.
  pose proof (munch_refl [(sp - 2208, sp - 2128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2128)) = sp + -2128) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 4 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  do 2 lstep. lstep. if_true.
  apply evt_done. do 20 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* [comment removed for export] *)
Lemma imemchr_chk : forall (sp p len : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2128) -> lo <= sp - IMEMCHR_DEPTH -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 <= len -> p + len < 2^63 ->
  chk_ok m p len -> m2s_cells m -> icells_mc m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s4' s5' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2128)) gp tp t0' t1' t2' s0 s1' a0 a1' a2' a3' a4' a5' a6' a7'
                    s2' s3 s4' s5' s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x44604) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2208, sp - 2128)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2128))
    (MS (mkR ra (Z_to_bv 64 (sp + -2128)) gp tp t0 t1 t2 s0 (Z_to_bv 64 len) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x445bc) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN (AC & QW & RO) M2S (G2 & RM & SHC & AI) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2208, sp - 2128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  lstep. lstep.
  destruct (Z_lt_le_dec 64 len) as [BIG|SMALL]; [| destruct (Z.eq_dec len 0) as [Z0|NZ]].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (len + -65)) = len - 65) by (apply unsigned_lit; lia).
    lstep. if_true. lstep. if_true.
    apply (imemchr_rip sp p len); try assumption; lia.
  - (* [comment removed for export] *)
    subst len. lstep. if_true. lstep. if_false. lstep.
    apply evt_done. do 20 eexists. split; [reflexivity|].
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
        -- apply evt_done. do 20 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (imemchr_rip sp p len); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (imemchr_loop (Z.to_nat ((p + len + -1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a3' & a4' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 20 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (imemchr_rip sp p len); try assumption; lia.
    + apply evt_done. do 20 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

Definition imemchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - IMEMCHR_DEPTH, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Theorem imemchr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s cz n : Z) (buf : list byte) (lo : Z),
  a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 cz -> a2 = Z_to_bv 64 n ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - IMEMCHR_DEPTH -> kHighShadowEnd < lo -> bv_unsigned sp < 2^63 ->
  0 <= s <= 2^47 -> 0 <= cz < 2^64 -> 0 <= n < 2^64 -> s + memchr_len s (cz mod 256) n buf <= 2^47 ->
  bytes_at asegs m s buf -> memchr_ok s (cz mod 256) n buf ->
  (s + Z.of_nat (length buf) <= bv_unsigned sp - IMEMCHR_DEPTH \/ bv_unsigned sp <= s) ->
  chk_ok m s (memchr_len s (cz mod 256) n buf) -> m2s_cells m -> icells_mc m -> mem_inv asegs m ->
  evt asegs (imemchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memchr_res s (cz mod 256) n buf) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44548) fc None m (seg_rom asegs)).
Proof using RIP MCH.
  intros until lo. intros -> -> -> ST LO LOLO SPH S0 HC N0 SH BUF OK SEPS CS M2S IC MI.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 2208, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof IC as (G2 & RM & SHC & AI).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUc : bv_unsigned (Z_to_bv 64 cz) = cz) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EU2128 : bv_unsigned (Z_to_bv 64 (usp + -2128)) = usp + -2128) by (apply unsigned_lit; lia).
  carve_frame 56%nat ST. rename FR into FRs. carve_frame 2072%nat ST.
  do 14 lstep.
  call asan_inited_spec; [exact AI| assumption|].
  lstep. if_false. lstep.
  call try_init_spec; [exact AI| rewrite EU2128; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2128 in H; rename H into ST2 end.
  do 7 lstep.
  call MCH; [rewrite EUs; exact BUF| rewrite EUs, EUc, EUn; exact OK| assumption|].
  rewrite EUs, EUc, EUn in *.
  set (c8 := cz mod 256) in *.
  assert (C8 : 0 <= c8 < 256) by (unfold c8; apply Z.mod_pos_bound; lia).
  clearbody c8.
  lstep. if_false.
  pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  unfold memchr_len in CS, SH.
  destruct (Z.eq_dec (memchr_res s c8 n buf) 0) as [Er|Ern].
  2:{
  destruct (find_byte c8 (firstn (Z.to_nat n) buf)) as [i|] eqn:FB;
    [| exfalso; apply Ern; unfold memchr_res; rewrite FB; reflexivity].
    destruct (find_byte_Some _ _ _ FB) as (Hi & _ & _). rewrite length_firstn in Hi.
    assert (Er : memchr_res s c8 n buf = s + Z.of_nat i) by (unfold memchr_res; rewrite FB; reflexivity).
    assert (NZ : s + Z.of_nat i <> 0) by congruence.
    assert (EL : (if memchr_res s c8 n buf =? 0 then n else memchr_res s c8 n buf - s + 1) = Z.of_nat i + 1)
      by (rewrite Er, (proj2 (Z.eqb_neq _ _) NZ); lia).
    rewrite EL in CS, SH. clear EL.
    rewrite Er.
    assert (EUr : bv_unsigned (Z_to_bv 64 (s + Z.of_nat i)) = s + Z.of_nat i) by (apply unsigned_lit; lia).
    lstep. if_true.
    do 5 lstep. rewrite (lxor_ones64 s) by lia.
    replace (s + Z.of_nat i - s + 1) with (Z.of_nat i + 1) by lia.
    assert (EUns : bv_unsigned (Z_to_bv 64 (18446744073709551615 - s)) = 18446744073709551615 - s) by (apply unsigned_lit; lia).
    assert (EUi : bv_unsigned (Z_to_bv 64 (Z.of_nat i + 1)) = Z.of_nat i + 1) by (apply unsigned_lit; lia).
    lstep. if_true.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (CS1 : chk_ok mm s (Z.of_nat i + 1))
        by (apply (chk_ok_agree m mm s _ CS ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside];
            split; [lia| exact I]);
      assert (M2S1 : m2s_cells mm) by (destruct M2S as (M1 & M2 & M3); split; [| split];
        [ apply (rw_cells_agree asegs m mm _ _ M1); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
        | apply (rw_cells_agree asegs m mm _ _ M2); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
        | apply (rw_cells_agree asegs m mm _ _ M3); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia ]);
      assert (IC1 : icells_mc mm) by (split; [exact G2| split; [exact RM| split; [exact SHC| exact AI]]])
    end.
    call (imemchr_chk usp s (Z.of_nat i + 1)); [exact ST2| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia
          | exact CS1| exact M2S1| exact IC1| assumption|].
    lazymatch goal with H : stk asegs _ lo (usp + -2128) |- _ => rename H into ST3 end.
    do 9 lstep.
    release_frame FR ST3 (usp + -56). release_frame FRs ST3 usp.
    lstep.
    unfold imemchr_post. sys_finish.
    + rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
    + rewrite EU. assumption.
  }
  - (* [comment removed for export] *)
    assert (EL : (if memchr_res s c8 n buf =? 0 then n else memchr_res s c8 n buf - s + 1) = n)
      by (rewrite Er; reflexivity).
    rewrite EL in CS, SH. clear EL.
    rewrite Er.
    lstep. if_false.
    do 3 lstep. lstep. rewrite (lxor_ones64 s) by lia.
    assert (EUns : bv_unsigned (Z_to_bv 64 (18446744073709551615 - s)) = 18446744073709551615 - s) by (apply unsigned_lit; lia).
    if_false.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (CS1 : chk_ok mm s n)
        by (apply (chk_ok_agree m mm s _ CS ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside];
            split; [lia| exact I]);
      assert (M2S1 : m2s_cells mm) by (destruct M2S as (M1 & M2 & M3); split; [| split];
        [ apply (rw_cells_agree asegs m mm _ _ M1); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
        | apply (rw_cells_agree asegs m mm _ _ M2); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
        | apply (rw_cells_agree asegs m mm _ _ M3); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia ]);
      assert (IC1 : icells_mc mm) by (split; [exact G2| split; [exact RM| split; [exact SHC| exact AI]]])
    end.
    call (imemchr_chk usp s n); [exact ST2| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia
          | exact CS1| exact M2S1| exact IC1| assumption|].
    lazymatch goal with H : stk asegs _ lo (usp + -2128) |- _ => rename H into ST3 end.
    do 9 lstep.
    release_frame FR ST3 (usp + -56). release_frame FRs ST3 usp.
    lstep.
    unfold imemchr_post. sys_finish.
    + rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
    + rewrite EU. assumption.
Qed.

End WithRIP.
