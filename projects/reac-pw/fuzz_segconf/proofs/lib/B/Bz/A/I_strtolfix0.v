(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/I_strlen.v, with its module paths, module names, addresses and numbers changed; 110 of its 158 lines of code are new or changed and 217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Bz/A/I_strtolfix0.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* StrtolFixAndCheck (0x554a4, 1216 B) with endptr = NULL, on reac-pw/fuzz_segconf's ASan+UBSan image B: the NULL arm.
   Port of pupnp/FuzzHttp lib/A0/ICP/I_strtolfix.v:311 sfix0_spec (origin/ossv/recipes 501c0d516c69): with a2 = 0
   the branch `beqz a2` at 0x554e4 is taken, no end pointer is stored, and the code joins at 0x5552c the tail it
   runs for a live end pointer (base check, the blank / sign skip when nothing was parsed, the range check of
   (end - x) + 1 string bytes, the return). pupnp's proof is stated over its own kit; here the same steps are stated
   over the Bz kit of I_strtolfix.v, whose tail lemmas carry the end-pointer cell, so the three tail entries are
   restated without it (sfix0_from_55518, sfix0_from_554b4, sfix0_tail, each the body of its I_strtolfix.v twin
   minus that cell) and close on I_strtolfix.v sfix_back / sfix_ws, as pupnp's sfix0_spec closes on its sfix_tail. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A Require Import Shadow IcptSpec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A Require Import R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A Require Import I_strtolfix.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Definition zidle (P : Prop) : Prop := P.
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

(* 0x555a4: the strict-string flag (common_flags + 0xf5) is 0, so the size is (end - x) + 1; then the range check
   and the return (I_strtolfix.v sfix_from_57268 without the end-pointer cell) *)
Lemma sfix0_from_55518 : forall (q A lo fo : Z) (ra gp tp t0 t1 t2 s1 a1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 : word) F fc (m : mem) (str fjunk : list byte),
  stk asegs m lo (q + -2144) -> lo <= q - 2224 -> kHighShadowEnd < lo -> q < 2^63 ->
  0 <= A -> A + Z.of_nat (length str) + 1 <= 2^47 -> Z.of_nat (length str) + 1 <= 2^40 ->
  bytes_at asegs m A (str ++ [Z_to_bv 8 0]) -> (A + Z.of_nat (length str) + 1 <= q + -2224 \/ q <= A) ->
  (forall nn, 1 <= nn <= Z.of_nat (length str) + 1 -> chk_ok m A nn) -> 0 <= fo <= Z.of_nat (length str) ->
  m2s_cells m -> icells_sx m -> mem_inv asegs m ->
  rw_cells asegs m (q + -72) [C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra] ->
  rw_cells asegs m (q + -2144) [CB 2072 fjunk] ->
  evt asegs (sfix_tpost vra q gp tp vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 s8 s9 s10 s11 F fc A str lo m)
    (MS (mkR ra (Z_to_bv 64 (q + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 1) a1 a2 (Z_to_bv 64 (A + fo)) a4 a5 a6 a7
             (Z_to_bv 64 A) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x555a4) fc None m (seg_rom asegs)).
Proof.
  intros until fjunk. intros ST LO LOLO SPH A0 A47 N40 STR SEPS CHK FO M2S (IC1 & IC2) MI FRs FR.
  unfold kHighShadowEnd in *.
  do 2 lstep. lstep. lstep. if_true. do 4 lstep.
  replace (Z.land 18446744073709551615 (A + fo - A + 1)) with (fo + 1)
    by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; rewrite Z.mod_small by lia; lia).
  eapply (sfix_back RIP q A fo); try eassumption; try (apply (CHK (fo + 1)); lia); try (unfold kHighShadowEnd; lia); try lia.
Qed.

(* 0x55540: nothing parsed (end = x) skips the blanks and one sign (sfix_ws); else end > x (I_strtolfix.v
   sfix_from_57204 without the end-pointer cell) *)
Lemma sfix0_from_554b4 : forall (q A k lo : Z) (ra gp tp t0 t1 t2 s1 a1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 : word) F fc (m : mem) (str fjunk : list byte),
  stk asegs m lo (q + -2144) -> lo <= q - 2224 -> kHighShadowEnd < lo -> q < 2^63 ->
  0 <= A -> A + Z.of_nat (length str) + 1 <= 2^47 -> Z.of_nat (length str) + 1 <= 2^40 ->
  bytes_at asegs m A (str ++ [Z_to_bv 8 0]) -> (A + Z.of_nat (length str) + 1 <= q + -2224 \/ q <= A) ->
  (forall nn, 1 <= nn <= Z.of_nat (length str) + 1 -> chk_ok m A nn) -> 0 <= k <= Z.of_nat (length str) ->
  m2s_cells m -> icells_sx m -> mem_inv asegs m ->
  rw_cells asegs m (q + -72) [C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra] ->
  rw_cells asegs m (q + -2144) [CB 2072 fjunk] ->
  evt asegs (sfix_tpost vra q gp tp vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 s8 s9 s10 s11 F fc A str lo m)
    (MS (mkR ra (Z_to_bv 64 (q + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 1) a1 a2 (Z_to_bv 64 (A + k)) a4 a5 a6 a7
             (Z_to_bv 64 A) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x55540) fc None m (seg_rom asegs)).
Proof.
  intros until fjunk. intros ST LO LOLO SPH A0 A47 N40 STR SEPS CHK HK M2S ICX MI FRs FR.
  lstep. if_cases Kbe.
  - assert (KZ : k = 0). { zify_cond Kbe. rewrite ?(unsigned_lit A), ?(unsigned_lit (A + k)) in Kbe by lia. lia. }
    subst k. do 3 lstep. lstep.
    replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + Z.of_nat 0)) at 1 by (f_equal; lia).
    eapply evt_cut.
    { eapply (sfix_ws (nblank (str ++ [Z_to_bv 8 0])) 0%nat A str);
        [exact STR| lia| lia| lia| rewrite skipn_O; reflexivity| lia| exact MI]. }
    intros ms' (a1' & a4' & a5' & ->).
    eapply (sfix0_from_55518 q A lo (fix_off (str ++ [Z_to_bv 8 0])));
      try eassumption; try (pose proof (fix_off_range str); lia); try (unfold kHighShadowEnd; lia).
  - lstep. if_cases Kg; zify_cond Kg;
    [ eapply (sfix0_from_55518 q A lo k); try eassumption; try lia; try (unfold kHighShadowEnd; lia)
    | exfalso; rewrite ?(unsigned_lit A), ?(unsigned_lit (A + k)) in Kg by lia; lia ].
Qed.

(* 0x5552c: base 10 or 16 passes the base check (I_strtolfix.v sfix_tail without the end-pointer cell; a2 is
   whatever the entry left there) *)
Lemma sfix0_tail : forall (q A k base lo : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a2 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 : word) F fc (m : mem) (str fjunk : list byte),
  stk asegs m lo (q + -2144) -> lo <= q - 2224 -> kHighShadowEnd < lo -> q < 2^63 ->
  0 <= A -> A + Z.of_nat (length str) + 1 <= 2^47 -> Z.of_nat (length str) + 1 <= 2^40 ->
  bytes_at asegs m A (str ++ [Z_to_bv 8 0]) -> (A + Z.of_nat (length str) + 1 <= q + -2224 \/ q <= A) ->
  (forall nn, 1 <= nn <= Z.of_nat (length str) + 1 -> chk_ok m A nn) -> 0 <= k <= Z.of_nat (length str) ->
  (base = 10 \/ base = 16) -> m2s_cells m -> icells_sx m -> mem_inv asegs m ->
  rw_cells asegs m (q + -72) [C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra] ->
  rw_cells asegs m (q + -2144) [CB 2072 fjunk] ->
  evt asegs (sfix_tpost vra q gp tp vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 s8 s9 s10 s11 F fc A str lo m)
    (MS (mkR ra (Z_to_bv 64 (q + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 a0 a1 a2 (Z_to_bv 64 (A + k)) (Z_to_bv 64 base) a5 a6 a7
             (Z_to_bv 64 A) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5552c) fc None m (seg_rom asegs)).
Proof.
  intros until fjunk. intros ST LO LOLO SPH A0 A47 N40 STR SEPS CHK HK HB M2S ICX MI FRs FR.
  destruct HB as [HB|HB]; subst base; do 4 lstep; lstep; if_false;
    eapply (sfix0_from_554b4 q A k lo); try eassumption; try lia; try (unfold kHighShadowEnd; lia).
Qed.

(* the entry, endptr (a2) = 0: the prologue, `beqz a2` at 0x554e4 taken, then the tail; no end-pointer cell is
   read or written, so the post is I_strtolfix.v sfix_tpost (pupnp: sfix_post with W = []) *)
Lemma sfix0_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (A k base lo : Z) (str : list byte),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2144 - 80 -> kHighShadowEnd < lo -> bv_unsigned sp <= 2^47 ->
  0 <= A -> A + Z.of_nat (length str) + 1 <= 2^47 -> Z.of_nat (length str) + 1 <= 2^40 ->
  bytes_at asegs m A (str ++ [Z_to_bv 8 0]) -> (A + Z.of_nat (length str) + 1 <= bv_unsigned sp + -2224 \/ bv_unsigned sp <= A) ->
  (forall nn, 1 <= nn <= Z.of_nat (length str) + 1 -> chk_ok m A nn) -> 0 <= k <= Z.of_nat (length str) ->
  (base = 10 \/ base = 16) -> m2s_cells m -> icells_sx m -> mem_inv asegs m ->
  a3' = Z_to_bv 64 (A + k) -> a4' = Z_to_bv 64 base ->
  evt asegs (sfix_tpost ra (bv_unsigned sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A str lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 A) (Z_to_bv 64 0) a3' a4' a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x554a4) fc None m (seg_rom asegs)).
Proof.
  intros until str.
  intros ST LO LOLO SPH A0 A47 N40 STR SEPS CHK HK HB M2S ICX MI HA3 HA4.
  subst a3' a4'.
  pose proof (bv_unsigned_in_range 64 sp) as HSPR. unfold bv_modulus in HSPR. cbn [Z.of_N] in HSPR.
  unfold kHighShadowEnd in LOLO.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2144 : bv_unsigned (Z_to_bv 64 (usp + -2144)) = usp + -2144) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(usp + -2224, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 72%nat ST. rename FR into FRs. carve_frame 2072%nat ST.
  zidle_beginz usp 2144%Z MUz1 WMz1.
  xsteps_to 0x554e4%Z.
  zidle_end MUz1 WMz1.
  lstep. first [ if_true | (if_cases Kz; zify_cond Kz; [| exfalso; lia]) ].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with HMU : munch _ m mm |- _ =>
      assert (AGS : agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8000) m mm)
        by (apply (agree_of_munch _ _ _ _ HMU); intros y Hy; cbn in Hy |- *; refine (conj _ I); lia);
      assert (CHK1 : forall nn, 1 <= nn <= Z.of_nat (length str) + 1 -> chk_ok mm A nn)
        by (intros nn Hnn; apply (chk_ok_agree m mm A nn (CHK nn Hnn) ltac:(lia) ltac:(lia) AGS));
      assert (M2S1 : m2s_cells mm) by (destruct M2S as (M1 & M2 & M3); split; [| split];
        [ apply (rw_cells_agree asegs m mm _ _ M1); [| assumption]; apply (agree_of_munch _ _ _ _ HMU); intros y Hy; cbn in Hy |- *; refine (conj _ I); lia
        | apply (rw_cells_agree asegs m mm _ _ M2); [| assumption]; apply (agree_of_munch _ _ _ _ HMU); intros y Hy; cbn in Hy |- *; refine (conj _ I); lia
        | apply (rw_cells_agree asegs m mm _ _ M3); [| assumption]; apply (agree_of_munch _ _ _ _ HMU); intros y Hy; cbn in Hy |- *; refine (conj _ I); lia ]);
      assert (ICX1 : icells_sx mm) by (destruct ICX as (I1 & I2); split;
        [ apply (ro_cells_agree asegs m mm _ _ I1); apply (agree_of_munch _ _ _ _ HMU); intros y Hy; cbn in Hy |- *; refine (conj _ I); lia
        | apply (ro_cells_agree asegs m mm _ _ I2); apply (agree_of_munch _ _ _ _ HMU); intros y Hy; cbn in Hy |- *; refine (conj _ I); lia ])
    end
  end.
  eapply evt_mono.
  { eapply (sfix0_tail usp A k base lo); try eassumption; try (unfold kHighShadowEnd; lia); try lia. }
  intros ms' Hpost. unfold sfix_tpost in Hpost |- *.
  destruct Hpost as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Heq & Hmunch1 & Hwm1 & Hmi & Hstk & Hba).
  do 16 eexists. split; [exact Heq|].
  split; [eapply munch_trans; [exact MU| exact Hmunch1]|].
  split; [eapply wmono_trans; [exact WM| exact Hwm1]|].
  split; [exact Hmi|]. split; [exact Hstk| exact Hba].
Qed.

End WithRIP.
