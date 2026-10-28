(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel BzLemmasHb BzHbW. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel BzLemmasHb BzHbW. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require RelLiaR.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.
Module S0_hbCreateB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasHb OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzHbW OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac lia ::= RelLia.lia_rf3.
Local Ltac StoreFast.tlia ::= RelLiaR.tlia_rr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)

Definition S0_hbCreate_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (DS t : Z) (lws bws pws : list word) (lbs : list byte) (minLen maxLen alpha lo : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' lws' bws' pws',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom s0segs)
    /\ munch [(DS + 45436 + 1032 * t, DS + 45436 + 1032 * t + 1032);
              (DS + 51628 + 1032 * t, DS + 51628 + 1032 * t + 1032);
              (DS + 57820 + 1032 * t, DS + 57820 + 1032 * t + 1032);
              (bv_unsigned sp + -64, bv_unsigned sp)]%Z m m'
    /\ wmono s0segs m m' /\ mem_inv s0segs m'
    /\ u32arr s0segs m' (DS + 45436 + 1032 * t) lws' /\ length lws' = 258%nat
    /\ u32arr s0segs m' (DS + 51628 + 1032 * t) bws' /\ length bws' = 258%nat
    /\ u32arr s0segs m' (DS + 57820 + 1032 * t) pws' /\ length pws' = 258%nat
    /\ u8arr s0segs m' (DS + 43888 + 258 * t) lbs
    /\ stk s0segs m' lo (bv_unsigned sp)
    /\ (let '(limit, base, perm) := hb_create (sv32 lws) (sv32 bws) (sv32 pws) (uv8 lbs) minLen maxLen alpha in
        ag32s lws' limit 258 /\ ag32s bws' base 258 /\ ag32s pws' perm 258).

Section P.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : word -> option byte).
  Variables (DS t : Z) (lws bws pws : list word) (lbs : list byte) (minLen maxLen alpha lo : Z).
  Hypothesis LENl : length lws = 258%nat.
  Hypothesis LENb : length bws = 258%nat.
  Hypothesis LENp : length pws = 258%nat.
  Hypothesis LEN8 : length lbs = 258%nat.
  Hypothesis HS : (0 <= DS)%Z /\ (DS mod 16 = 0)%Z /\ (0 <= t < 6)%Z.
  Hypothesis HLO : (DS + 64144 <= lo)%Z /\ (lo + 64 <= bv_unsigned sp)%Z.
  Hypothesis Halpha : (1 <= alpha <= 258)%Z.
  Hypothesis Hmm : (1 <= minLen /\ minLen <= maxLen <= 20)%Z.
  Hypothesis Hlen : forall j, (0 <= j < alpha)%Z -> (minLen <= uv8 lbs j <= maxLen)%Z.

  Notation usp := (bv_unsigned sp).
  Notation LIM := (DS + 45436 + 1032 * t)%Z.
  Notation BASE := (DS + 51628 + 1032 * t)%Z.
  Notation PERM := (DS + 57820 + 1032 * t)%Z.
  Notation LEN := (DS + 43888 + 258 * t)%Z.
  Notation limit0 := (sv32 lws). Notation base0 := (sv32 bws). Notation perm0 := (sv32 pws). Notation len := (uv8 lbs).
  Notation W := ([(LIM, LIM + 1032); (BASE, BASE + 1032); (PERM, PERM + 1032); (usp + -64, usp)])%Z.
  Notation POST := (S0_hbCreate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DS t lws bws pws lbs minLen maxLen alpha lo m).
  Notation base1 := (hbm_base1 base0).
  Notation base2 := (hbm_base2 len alpha base0).
  Notation base3 := (hbm_base3 len alpha base0).
  Notation limit1 := (hbm_limit1 limit0).
  Notation limitF := (hbm_limit len alpha minLen maxLen limit0 base0).
  Notation baseF := (hbm_base len alpha minLen maxLen limit0 base0).
  Notation permF := (hbm_perm len alpha minLen maxLen perm0).
  (* [comment removed for export] *)
  Notation FRAME mm := (rw_cells s0segs mm (usp + -32) [C8 s3; C8 s2; C8 s1; C8 s0]).
  Notation cSP := (Z_to_bv 64 (usp + -32)).

  (* [comment removed for export] *)
  Ltac u32_store_done ARR i :=
    lazymatch goal with
    | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?mm _ (le4 ?v)) _) =>
        lazymatch type of ARR with u32arr _ _ ?A ?ws =>
          let H := fresh "ARR" in
          pose proof (u32arr_write segs mm A ws i v ARR ltac:(lia)) as H; clear ARR; store_done; rename H into ARR
        end
    end.

  Lemma sp_range : (0 <= usp < 2^64)%Z.
  Proof using sp DS lws bws pws lbs LENl LENb LENp LEN8. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R. lia. Qed.
  Lemma ds_al4 : (DS mod 4 = 0)%Z.
  Proof. destruct HS as (_ & A16 & _). clear - A16. Z.div_mod_to_equations; lia. Qed.
  (* [comment removed for export] *)
  Lemma S0_hb_loopB : forall (k d : nat) (x5 x6 x7 x8 x9 x12 x14 x16 x17 x18 x19 x28 x29 x30 x31 : word) m1 lwsF bwsc pwsF,
    let i := (minLen + 1 + Z.of_nat d)%Z in
    (Z.of_nat k = maxLen + 1 - i)%Z -> (i <= maxLen + 1)%Z ->
    u32arr s0segs m1 LIM lwsF -> length lwsF = 258%nat -> ag32s lwsF limitF 258 ->
    u32arr s0segs m1 BASE bwsc -> length bwsc = 258%nat -> ag32s bwsc (hb_base limitF (minLen + 1) d base3) 258 ->
    u32arr s0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr s0segs m1 LEN lbs -> FRAME m1 -> stk s0segs m1 lo (usp + -32) ->
    munch W m m1 -> wmono s0segs m m1 -> mem_inv s0segs m1 ->
    evt s0segs POST
      (MS (mkR ra cSP gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) x12 (Z_to_bv 64 i) x14 (Z_to_bv 64 maxLen)
              x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x2458c) fc None m1 (seg_rom s0segs)).
  Proof.
    induction k as [|k IH]; intros d x5 x6 x7 x8 x9 x12 x14 x16 x17 x18 x19 x28 x29 x30 x31 m1 lwsF bwsc pwsF i HK Hi
      ARL LENL AGL ARB LENB AGB ARP LENP AGP AR8 FR ST MU WM MI; subst i.
    - (* [comment removed for export] *)
      assert (HX : (maxLen < minLen + 1 + Z.of_nat d)%Z) by lia.
      pose proof sp_range as SPR.
      wstep. if_true_z.
      wstep. wstep. wstep. wstep. wstep.
      release_frame FR ST (bv_unsigned sp).
      replace (Z_to_bv 64 (usp + -32 + 32)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
      wstep.
      unfold S0_hbCreate_post. rewrite hb_create_pieces by assumption.
      finish; [exact ARL | exact LENL | exact ARB | exact LENB | exact ARP | exact LENP | exact AGL | | exact AGP].
      unfold hbm_base. replace (span (minLen + 1) maxLen) with d by (unfold span; lia). exact AGB.
    - assert (Hi2 : (minLen + 1 + Z.of_nat d <= maxLen)%Z) by lia.
      pose proof sp_range as SPR. pose proof ds_al4 as AL4.
      pose proof (hbw_base_step len alpha minLen maxLen Halpha Hmm Hlen limit0 base0 d Hi2) as BF. cbn zeta in BF.
      cps_destruct BF as (BF1 & BF2 & BF3 & BF4).
      set (i := (minLen + 1 + Z.of_nat d)%Z) in *.
      pose proof (u32arr_bound _ _ _ _ ARL) as BL. rewrite LENL in BL.
      pose proof (u32arr_bound _ _ _ _ ARB) as BB. rewrite LENB in BB.
      wstep. if_false_z.
      urun_to 0x245bc%Z.
      destruct (nth_error_ok lwsF (i - 1) 258 LENL ltac:(lia)) as [wl NTHl].
      pose proof (u32arr_read s0segs m1 LIM lwsF (i - 1) wl _ ARL NTHl ltac:(lia) eq_refl) as RD.
      wstep. clear RD.
      pose proof (AGL (i - 1)%Z ltac:(lia)) as VL. rewrite (sv32_nth _ _ _ NTHl) in VL. rewrite BF1 in VL.
      cbv beta delta [sx32]. rewrite VL.
      set (L := (first len alpha minLen (i - 1) + cnt_eq len alpha (i - 1))%Z) in *.
      urun_to 0x245f0%Z.
      destruct (nth_error_ok bwsc i 258 LENB ltac:(lia)) as [wb NTHb].
      pose proof (u32arr_read s0segs m1 BASE bwsc i wb _ ARB NTHb ltac:(lia) eq_refl) as RD.
      wstep. clear RD.
      pose proof (AGB i ltac:(lia)) as VB. rewrite (sv32_nth _ _ _ NTHb) in VB. rewrite BF3 in VB.
      cbv beta delta [sx32]. rewrite VB.
      set (C := cnt_lt len alpha i) in *.
      urun_to 0x24608%Z.
      pose proof (u32arr_store_ok s0segs m1 BASE bwsc i _ ARB ltac:(lia) eq_refl) as SO.
      wstep.
      u32_store_done ARB i. rename ARB into ARB'.
      urun_to 0x2458c%Z.
      enter_with (IH (S d) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lwsF _ pwsF);
        [ st_eq | lia | lia | exact ARL | exact LENL | exact AGL | exact ARB' | rewrite upd_length; exact LENB | | exact ARP | exact LENP | exact AGP
        | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      rewrite hb_base_snoc. cbn zeta. fold i.
      apply ag32s_upd_w; [exact AGB | lia | rewrite LENB; lia |].
      rewrite sv32_lit by lia. rewrite BF1, Z.shiftl_mul_pow2 by lia. subst C. lia.
  Qed.


  Notation STL pc i vec x8 x9 x18 x19 x28 x29 x30 x31 mm :=
      (MS (mkR ra cSP gp tp (Z_to_bv 64 (BASE + 4 * i)) (Z_to_bv 64 i) (Z_to_bv 64 vec) x8 x9
              (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) (Z_to_bv 64 (BASE + 4 * i)) (Z_to_bv 64 (LIM + 4 * i))
              (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 i) (Z_to_bv 64 (LIM + 4 * i))
              x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 pc) fc None mm (seg_rom s0segs)).

  Lemma S0_hb_bodyL : forall (d : nat) (x8 x9 x18 x19 x28 x29 x30 x31 : word) m1 lwsc bws3 pwsF (vec : Z) (Q : machine_state -> Prop),
    let i := (minLen + Z.of_nat d)%Z in
    (i <= maxLen)%Z ->
    vec = snd (hb_limit base3 minLen d limit1 0) ->
    u32arr s0segs m1 LIM lwsc -> length lwsc = 258%nat -> ag32s lwsc (fst (hb_limit base3 minLen d limit1 0)) 258 ->
    u32arr s0segs m1 BASE bws3 -> length bws3 = 258%nat -> ag32s bws3 base3 258 ->
    u32arr s0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr s0segs m1 LEN lbs -> FRAME m1 -> stk s0segs m1 lo (usp + -32) ->
    munch W m m1 -> wmono s0segs m m1 -> mem_inv s0segs m1 ->
    (forall (y28 y29 y30 y31 : word) m2 lwsc' (vec' : Z),
       vec' = snd (hb_limit base3 minLen (S d) limit1 0) ->
       u32arr s0segs m2 LIM lwsc' -> length lwsc' = 258%nat -> ag32s lwsc' (fst (hb_limit base3 minLen (S d) limit1 0)) 258 ->
       u32arr s0segs m2 BASE bws3 -> u32arr s0segs m2 PERM pwsF -> u8arr s0segs m2 LEN lbs -> FRAME m2 ->
       stk s0segs m2 lo (usp + -32) -> munch W m m2 -> wmono s0segs m m2 -> mem_inv s0segs m2 ->
       evt s0segs Q (STL 0x24580 (i + 1) vec' x8 x9 x18 x19 y28 y29 y30 y31 m2)) ->
    evt s0segs Q (STL 0x244d4 i vec x8 x9 x18 x19 x28 x29 x30 x31 m1).
  Proof.
    intros d x8 x9 x18 x19 x28 x29 x30 x31 m1 lwsc bws3 pwsF vec Q i Hi Hvec
      ARL LENL AGL ARB LENB AGB ARP LENP AGP AR8 FR ST MU WM MI HQ; subst i.
    pose proof sp_range as SPR. pose proof ds_al4 as AL4.
    pose proof (hbw_limit_step len alpha minLen maxLen Halpha Hmm Hlen limit0 base0 d ltac:(lia)) as LF. cbn zeta in LF.
    rewrite <- Hvec in LF.
    cps_destruct LF as (LF1 & LF2 & LF3 & LF4 & LF5 & LF6 & LF7 & LF8 & LF9).
    set (i := (minLen + Z.of_nat d)%Z) in *.
    set (V := first len alpha minLen i) in *.
    set (C0 := cnt_lt len alpha i) in *. set (C1 := cnt_lt len alpha (i + 1)) in *. set (E := cnt_eq len alpha i) in *.
    pose proof (u32arr_bound _ _ _ _ ARL) as BL. rewrite LENL in BL.
    pose proof (u32arr_bound _ _ _ _ ARB) as BB. rewrite LENB in BB.
    urun_to 0x24518%Z.
    destruct (nth_error_ok bws3 (i + 1) 258 LENB ltac:(lia)) as [w1 NTH1].
    pose proof (u32arr_read s0segs m1 BASE bws3 (i + 1) w1 _ ARB NTH1 ltac:(lia) eq_refl) as RD.
    wstep. clear RD.
    pose proof (AGB (i + 1)%Z ltac:(lia)) as V1. rewrite (sv32_nth _ _ _ NTH1) in V1. rewrite LF4 in V1.
    cbv beta delta [sx32]. rewrite V1.
    destruct (nth_error_ok bws3 i 258 LENB ltac:(lia)) as [w2 NTH2].
    pose proof (u32arr_read s0segs m1 BASE bws3 i w2 _ ARB NTH2 ltac:(lia) eq_refl) as RD.
    wstep. clear RD.
    pose proof (AGB i ltac:(lia)) as V2. rewrite (sv32_nth _ _ _ NTH2) in V2. rewrite LF3 in V2.
    cbv beta delta [sx32]. rewrite V2.
    urun_to 0x24560%Z.
    pose proof (u32arr_store_ok s0segs m1 LIM lwsc i _ ARL ltac:(lia) eq_refl) as SO.
    wstep.
    u32_store_done ARL i. rename ARL into ARL'.
    urun_to 0x24580%Z.
    eapply evt_eq; [| eapply (HQ _ _ _ _ _ _ ((vec + (C1 - C0)) * 2)%Z) ];
      [ st_eq | | exact ARL' | rewrite upd_length; exact LENL | | exact ARB | exact ARP | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
    - rewrite hb_limit_snoc. cbn zeta. cbn [fst snd]. fold i. rewrite <- Hvec, LF4, LF3, Z.shiftl_mul_pow2 by lia. lia.
    - rewrite hb_limit_snoc. cbn zeta. cbn [fst snd]. fold i.
      apply ag32s_upd_w; [exact AGL | lia | rewrite LENL; lia |].
      rewrite sv32_lit by lia. rewrite <- Hvec, LF4, LF3. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma S0_hb_loopL : forall (k d : nat) (x8 x9 x18 x19 x28 x29 x30 x31 : word) m1 lwsc bws3 pwsF (vec : Z),
    let i := (minLen + Z.of_nat d)%Z in
    (Z.of_nat k = maxLen - i)%Z -> (i <= maxLen)%Z ->
    vec = snd (hb_limit base3 minLen d limit1 0) ->
    u32arr s0segs m1 LIM lwsc -> length lwsc = 258%nat -> ag32s lwsc (fst (hb_limit base3 minLen d limit1 0)) 258 ->
    u32arr s0segs m1 BASE bws3 -> length bws3 = 258%nat -> ag32s bws3 base3 258 ->
    u32arr s0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr s0segs m1 LEN lbs -> FRAME m1 -> stk s0segs m1 lo (usp + -32) ->
    munch W m m1 -> wmono s0segs m m1 -> mem_inv s0segs m1 ->
    evt s0segs POST (STL 0x244d4 i vec x8 x9 x18 x19 x28 x29 x30 x31 m1).
  Proof.
    induction k as [|k IH]; intros d x8 x9 x18 x19 x28 x29 x30 x31 m1 lwsc bws3 pwsF vec i HK Hi Hvec
      ARL LENL AGL ARB LENB AGB ARP LENP AGP AR8 FR ST MU WM MI; subst i;
      pose proof sp_range as SPR;
      (eapply S0_hb_bodyL;
       [ exact Hi | exact Hvec | exact ARL | exact LENL | exact AGL | exact ARB | exact LENB | exact AGB
       | exact ARP | exact LENP | exact AGP | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI | ]);
      clear ARL LENL AGL ARB ARP AR8 FR ST MU WM MI;
      intros y28 y29 y30 y31 m2 lwsc' vec' Hvec' ARL LENL' AGL' ARB ARP AR8 FR ST MU WM MI.
    - (* [comment removed for export] *)
      wstep. if_false_z. urun_to 0x2458c%Z.
      enter_with (S0_hb_loopB (Z.to_nat (maxLen - minLen)) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 lwsc' bws3 pwsF);
        [ st_eq | lia | lia | exact ARL | exact LENL' | | exact ARB | exact LENB | | exact ARP | exact LENP | exact AGP
        | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      + unfold hbm_limit, hbm_lv. replace (span minLen maxLen) with (S d) by (unfold span; lia). exact AGL'.
      + cbn [hb_base]. exact AGB.
    - (* [comment removed for export] *)
      wstep. if_true_z.
      enter_with (IH (S d) _ _ _ _ _ _ _ _ m2 lwsc' bws3 pwsF vec');
        [ st_eq | lia | lia | exact Hvec' | exact ARL | exact LENL' | exact AGL' | exact ARB | exact LENB | exact AGB
        | exact ARP | exact LENP | exact AGP | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
  Qed.

  Lemma S0_hb_partC : forall (x5 x6 x7 x8 x9 x12 x13 x16 x17 x18 x19 x28 x29 x30 x31 : word) m1 lws1 bws3 pwsF,
    u32arr s0segs m1 LIM lws1 -> length lws1 = 258%nat -> ag32s lws1 limit1 258 ->
    u32arr s0segs m1 BASE bws3 -> length bws3 = 258%nat -> ag32s bws3 base3 258 ->
    u32arr s0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr s0segs m1 LEN lbs -> FRAME m1 -> stk s0segs m1 lo (usp + -32) ->
    munch W m m1 -> wmono s0segs m m1 -> mem_inv s0segs m1 ->
    evt s0segs POST
      (MS (mkR ra cSP gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) x12 x13
              (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x244b0) fc None m1 (seg_rom s0segs)).
  Proof.
    intros x5 x6 x7 x8 x9 x12 x13 x16 x17 x18 x19 x28 x29 x30 x31 m1 lws1 bws3 pwsF
      ARL LENL AGL ARB LENB AGB ARP LENP AGP AR8 FR ST MU WM MI.
    pose proof sp_range as SPR.
    wstep. if_false_z. urun_to 0x244d4%Z.
    enter_with (S0_hb_loopL (Z.to_nat (maxLen - minLen)) 0 x8 x9 x18 x19 x28 x29 x30 x31 m1 lws1 bws3 pwsF 0);
      [ st_eq | lia | lia | reflexivity | exact ARL | exact LENL | exact AGL | exact ARB | exact LENB | exact AGB
      | exact ARP | exact LENP | exact AGP | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
  Qed.

  Lemma S0_hb_loopZ2 : forall (k : nat) (j : Z) (x6 x7 x8 x9 x18 x19 x28 x29 x30 x31 : word) m1 lwsc bws3 pwsF,
    (Z.of_nat k = 23 - j)%Z -> (0 <= j < 23)%Z ->
    u32arr s0segs m1 LIM lwsc -> length lwsc = 258%nat -> ag32s lwsc (fill0 limit0 0 (Z.to_nat j)) 258 ->
    u32arr s0segs m1 BASE bws3 -> length bws3 = 258%nat -> ag32s bws3 base3 258 ->
    u32arr s0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr s0segs m1 LEN lbs -> FRAME m1 -> stk s0segs m1 lo (usp + -32) ->
    munch W m m1 -> wmono s0segs m m1 -> mem_inv s0segs m1 ->
    evt s0segs POST
      (MS (mkR ra cSP gp tp (Z_to_bv 64 (LIM + 4 * j)) x6 x7 x8 x9
              (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen)
              (Z_to_bv 64 (23 - j)) (Z_to_bv 64 (LIM + 4 * j)) x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x24488) fc None m1 (seg_rom s0segs)).
  Proof.
    induction k as [|k IH]; intros j x6 x7 x8 x9 x18 x19 x28 x29 x30 x31 m1 lwsc bws3 pwsF HK Hj
      ARL LENL AGL ARB LENB AGB ARP LENP AGP AR8 FR ST MU WM MI; [lia|].
    pose proof sp_range as SPR. pose proof ds_al4 as AL4.
    pose proof (u32arr_bound _ _ _ _ ARL) as BL. rewrite LENL in BL.
    urun_to 0x2449c%Z.
    pose proof (u32arr_store_ok s0segs m1 LIM lwsc j _ ARL ltac:(lia) eq_refl) as SO.
    wstep.
    u32_store_done ARL j. rename ARL into ARL'.
    urun. if_cases K; zify_cond K.
    - enter_with (IH (j + 1)%Z _ _ _ _ _ _ _ _ _ _ _ (upd lwsc (Z.to_nat j) (Z_to_bv 64 0)) bws3 pwsF);
        [ st_eq | lia | lia | exact ARL' | rewrite upd_length; exact LENL | | exact ARB | exact LENB | exact AGB
        | exact ARP | exact LENP | exact AGP | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. rewrite fill0_snoc.
      replace (0 + Z.of_nat (Z.to_nat j))%Z with j by lia.
      apply ag32s_upd; [exact AGL | lia | rewrite LENL; lia | lia].
    - enter_with (S0_hb_partC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (upd lwsc (Z.to_nat j) (Z_to_bv 64 0)) bws3 pwsF);
        [ st_eq | exact ARL' | rewrite upd_length; exact LENL | | exact ARB | exact LENB | exact AGB
        | exact ARP | exact LENP | exact AGP | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      unfold hbm_limit1. replace 23%nat with (S (Z.to_nat j)) by lia. rewrite fill0_snoc.
      replace (0 + Z.of_nat (Z.to_nat j))%Z with j by lia.
      apply ag32s_upd; [exact AGL | lia | rewrite LENL; lia | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma S0_hb_loopA : forall (k mI : nat) (x5 x6 x7 x8 x9 x18 x19 x28 x29 x30 x31 : word) m1 bwsc pwsF,
    let i := (1 + Z.of_nat mI)%Z in
    (Z.of_nat k = 23 - i)%Z -> (1 <= i <= 22)%Z ->
    u32arr s0segs m1 LIM lws ->
    u32arr s0segs m1 BASE bwsc -> length bwsc = 258%nat -> ag32s bwsc (hb_accum 1 mI base2) 258 ->
    u32arr s0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr s0segs m1 LEN lbs -> FRAME m1 -> stk s0segs m1 lo (usp + -32) ->
    munch W m m1 -> wmono s0segs m m1 -> mem_inv s0segs m1 ->
    evt s0segs POST
      (MS (mkR ra cSP gp tp x5 x6 x7 x8 x9
              (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) (Z_to_bv 64 (18446744073709551615 - BASE)) (Z_to_bv 64 (BASE + 4 * i))
              (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 (4 * i)) (Z_to_bv 64 92)
              x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x24444) fc None m1 (seg_rom s0segs)).
  Proof.
    induction k as [|k IH]; intros mI x5 x6 x7 x8 x9 x18 x19 x28 x29 x30 x31 m1 bwsc pwsF i HK Hi
      ARL ARB LENB AGB ARP LENP AGP AR8 FR ST MU WM MI; subst i; [lia|].
    pose proof sp_range as SPR. pose proof ds_al4 as AL4.
    pose proof (u32arr_bound _ _ _ _ ARB) as BB. rewrite LENB in BB.
    pose proof (hbw_accum_step len alpha minLen maxLen Halpha Hmm Hlen base0 (Z.of_nat mI) ltac:(lia)) as AF. cbn zeta in AF.
    rewrite Nat2Z.id in AF. cps_destruct AF as (AF1 & AF2 & AF3).
    set (i := (1 + Z.of_nat mI)%Z) in *.
    urun_to 0x24448%Z.
    destruct (nth_error_ok bwsc (i - 1) 258 LENB ltac:(lia)) as [w1 NTH1].
    pose proof (u32arr_read s0segs m1 BASE bwsc (i - 1) w1 _ ARB NTH1 ltac:(lia) eq_refl) as RD.
    wstep. clear RD.
    pose proof (AGB (i - 1)%Z ltac:(lia)) as V1. rewrite (sv32_nth _ _ _ NTH1) in V1.
    destruct (nth_error_ok bwsc i 258 LENB ltac:(lia)) as [w2 NTH2].
    pose proof (u32arr_read s0segs m1 BASE bwsc i w2 _ ARB NTH2 ltac:(lia) eq_refl) as RD.
    wstep. clear RD.
    pose proof (AGB i ltac:(lia)) as V2. rewrite (sv32_nth _ _ _ NTH2) in V2.
    cbv beta delta [sx32]. rewrite V1, V2.
    set (P1 := hb_accum 1 mI base2 (i - 1)) in *. set (P2 := hb_accum 1 mI base2 i) in *.
    urun_to 0x2445c%Z.
    pose proof (u32arr_store_ok s0segs m1 BASE bwsc i _ ARB ltac:(lia) eq_refl) as SO.
    wstep.
    u32_store_done ARB i. rename ARB into ARB'.
    urun. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      enter_with (IH (S mI) _ _ _ _ _ _ _ _ _ _ _ _ (upd bwsc (Z.to_nat i) (Z_to_bv 64 (P2 + P1))) pwsF);
        [ st_eq | lia | lia | exact ARL | exact ARB' | rewrite upd_length; exact LENB | | exact ARP | exact LENP | exact AGP
        | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      rewrite hb_accum_snoc. cbn zeta. fold i. replace (1 + Z.of_nat mI)%Z with i by lia.
      apply ag32s_upd; [exact AGB | lia | rewrite LENB; lia | lia].
    - (* [comment removed for export] *)
      pose proof (u32arr_bound _ _ _ _ ARL) as BL. rewrite LENl in BL.
      urun_to 0x24488%Z.
      enter_with (S0_hb_loopZ2 23 0 _ _ _ _ _ _ _ _ _ _ _ lws (upd bwsc (Z.to_nat i) (Z_to_bv 64 (P2 + P1))) pwsF);
        [ st_eq | lia | lia | exact ARL | exact LENl | | exact ARB' | rewrite upd_length; exact LENB | | exact ARP | exact LENP | exact AGP
        | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      + cbn [fill0 Z.to_nat]. apply ag32s_refl.
      + unfold hbm_base3. replace 22%nat with (S mI) by lia. rewrite hb_accum_snoc. cbn zeta.
        replace (1 + Z.of_nat mI)%Z with i by lia.
        apply ag32s_upd; [exact AGB | lia | rewrite LENB; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma S0_hb_loopC : forall (k : nat) (j : Z) (x7 x8 x9 x18 x19 x28 x29 x30 x31 : word) m1 bwsc pwsF,
    (Z.of_nat k = alpha - j)%Z -> (0 <= j < alpha)%Z ->
    u32arr s0segs m1 LIM lws ->
    u32arr s0segs m1 BASE bwsc -> length bwsc = 258%nat -> ag32s bwsc (hb_count len 0 (Z.to_nat j) base1) 258 ->
    u32arr s0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr s0segs m1 LEN lbs -> FRAME m1 -> stk s0segs m1 lo (usp + -32) ->
    munch W m m1 -> wmono s0segs m m1 -> mem_inv s0segs m1 ->
    evt s0segs POST
      (MS (mkR ra cSP gp tp (Z_to_bv 64 (LEN + j)) (Z_to_bv 64 (LEN + j)) x7 x8 x9
              (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) (Z_to_bv 64 (18446744073709551615 - BASE)) (Z_to_bv 64 LEN)
              (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 (alpha - j)) (Z_to_bv 64 1)
              x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x243f0) fc None m1 (seg_rom s0segs)).
  Proof.
    induction k as [|k IH]; intros j x7 x8 x9 x18 x19 x28 x29 x30 x31 m1 bwsc pwsF HK Hj
      ARL ARB LENB AGB ARP LENP AGP AR8 FR ST MU WM MI; [lia|].
    pose proof sp_range as SPR. pose proof ds_al4 as AL4.
    pose proof (u32arr_bound _ _ _ _ ARB) as BB. rewrite LENB in BB.
    pose proof (u8arr_bound _ _ _ _ AR8) as B8. rewrite LEN8 in B8.
    pose proof (hbw_count_step len alpha minLen maxLen Halpha Hmm Hlen base0 j ltac:(lia)) as CF. cbn zeta in CF.
    destruct CF as [CF1 CF2].
    urun_to 0x24404%Z.
    destruct (nth_error_ok lbs j 258 LEN8 ltac:(lia)) as [b NTH].
    pose proof (u8arr_read s0segs m1 LEN lbs j b _ AR8 NTH ltac:(lia) eq_refl) as RD.
    wstep. clear RD.
    pose proof (uv8_nth _ _ _ NTH) as VB. cbv beta delta [zxb]. rewrite <- VB.
    set (q := (len j + 1)%Z) in *.
    pose proof (Hlen j ltac:(lia)) as LJ.
    urun_to 0x24418%Z.
    destruct (nth_error_ok bwsc q 258 LENB ltac:(lia)) as [w NTHw].
    pose proof (u32arr_read s0segs m1 BASE bwsc q w _ ARB NTHw ltac:(lia) eq_refl) as RD.
    wstep. clear RD.
    pose proof (AGB q ltac:(lia)) as V1. rewrite (sv32_nth _ _ _ NTHw) in V1.
    cbv beta delta [sx32]. rewrite V1.
    set (P := hb_count len 0 (Z.to_nat j) base1 q) in *.
    urun_to 0x24424%Z.
    pose proof (u32arr_store_ok s0segs m1 BASE bwsc q _ ARB ltac:(lia) eq_refl) as SO.
    wstep.
    u32_store_done ARB q. rename ARB into ARB'.
    assert (AGB' : ag32s (upd bwsc (Z.to_nat q) (Z_to_bv 64 (P + 1))) (hb_count len 0 (S (Z.to_nat j)) base1) 258).
    { rewrite hb_count_snoc. cbn zeta. replace (0 + Z.of_nat (Z.to_nat j))%Z with j by lia. fold q. fold P.
      apply ag32s_upd; [exact AGB | lia | rewrite LENB; lia | lia]. }
    urun. if_cases K; zify_cond K.
    - enter_with (IH (j + 1)%Z _ _ _ _ _ _ _ _ _ _ (upd bwsc (Z.to_nat q) (Z_to_bv 64 (P + 1))) pwsF);
        [ st_eq | lia | lia | exact ARL | exact ARB' | rewrite upd_length; exact LENB | | exact ARP | exact LENP | exact AGP
        | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. exact AGB'.
    - (* [comment removed for export] *)
      urun_to 0x24444%Z.
      enter_with (S0_hb_loopA 22 0 _ _ _ _ _ _ _ _ _ _ _ _ (upd bwsc (Z.to_nat q) (Z_to_bv 64 (P + 1))) pwsF);
        [ st_eq | lia | lia | exact ARL | exact ARB' | rewrite upd_length; exact LENB | | exact ARP | exact LENP | exact AGP
        | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      cbn [hb_accum]. unfold hbm_base2. replace (Z.to_nat alpha) with (S (Z.to_nat j)) by lia. exact AGB'.
  Qed.

  Lemma S0_hb_loopZ1 : forall (k : nat) (j : Z) (x8 x9 x18 x19 x28 x29 x30 x31 : word) m1 bwsc pwsF,
    (Z.of_nat k = 23 - j)%Z -> (0 <= j < 23)%Z ->
    u32arr s0segs m1 LIM lws ->
    u32arr s0segs m1 BASE bwsc -> length bwsc = 258%nat -> ag32s bwsc (fill0 base0 0 (Z.to_nat j)) 258 ->
    u32arr s0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr s0segs m1 LEN lbs -> FRAME m1 -> stk s0segs m1 lo (usp + -32) ->
    munch W m m1 -> wmono s0segs m m1 -> mem_inv s0segs m1 ->
    evt s0segs POST
      (MS (mkR ra cSP gp tp (Z_to_bv 64 (23 - j)) (Z_to_bv 64 (BASE + 4 * j)) (Z_to_bv 64 (BASE + 4 * j)) x8 x9
              (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) (Z_to_bv 64 1) (Z_to_bv 64 LEN)
              (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 alpha) (Z_to_bv 64 1)
              x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x243b4) fc None m1 (seg_rom s0segs)).
  Proof.
    induction k as [|k IH]; intros j x8 x9 x18 x19 x28 x29 x30 x31 m1 bwsc pwsF HK Hj
      ARL ARB LENB AGB ARP LENP AGP AR8 FR ST MU WM MI; [lia|].
    pose proof sp_range as SPR. pose proof ds_al4 as AL4.
    pose proof (u32arr_bound _ _ _ _ ARB) as BB. rewrite LENB in BB.
    urun_to 0x243c8%Z.
    pose proof (u32arr_store_ok s0segs m1 BASE bwsc j _ ARB ltac:(lia) eq_refl) as SO.
    wstep.
    u32_store_done ARB j. rename ARB into ARB'.
    urun. if_cases K; zify_cond K.
    - enter_with (IH (j + 1)%Z _ _ _ _ _ _ _ _ _ (upd bwsc (Z.to_nat j) (Z_to_bv 64 0)) pwsF);
        [ st_eq | lia | lia | exact ARL | exact ARB' | rewrite upd_length; exact LENB | | exact ARP | exact LENP | exact AGP
        | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. rewrite fill0_snoc.
      replace (0 + Z.of_nat (Z.to_nat j))%Z with j by lia.
      apply ag32s_upd; [exact AGB | lia | rewrite LENB; lia | lia].
    - pose proof (u8arr_bound _ _ _ _ AR8) as B8. rewrite LEN8 in B8.
      urun_to 0x243e0%Z. wstep. if_false_z. urun_to 0x243f0%Z.
      enter_with (S0_hb_loopC (Z.to_nat alpha) 0 _ _ _ _ _ _ _ _ _ _ (upd bwsc (Z.to_nat j) (Z_to_bv 64 0)) pwsF);
        [ st_eq | lia | lia | exact ARL | exact ARB' | rewrite upd_length; exact LENB | | exact ARP | exact LENP | exact AGP
        | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      cbn [hb_count Z.to_nat]. unfold hbm_base1. replace 23%nat with (S (Z.to_nat j)) by lia. rewrite fill0_snoc.
      replace (0 + Z.of_nat (Z.to_nat j))%Z with j by lia.
      apply ag32s_upd; [exact AGB | lia | rewrite LENB; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma S0_hb_partB : forall (x5 x6 x7 x8 x9 x12 x17 x18 x19 x28 x29 x30 x31 : word) m1 pwsF,
    u32arr s0segs m1 LIM lws ->
    u32arr s0segs m1 BASE bws ->
    u32arr s0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr s0segs m1 LEN lbs -> FRAME m1 -> stk s0segs m1 lo (usp + -32) ->
    munch W m m1 -> wmono s0segs m m1 -> mem_inv s0segs m1 ->
    evt s0segs POST
      (MS (mkR ra cSP gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) x12 (Z_to_bv 64 LEN)
              (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 alpha) x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x24398) fc None m1 (seg_rom s0segs)).
  Proof.
    intros x5 x6 x7 x8 x9 x12 x17 x18 x19 x28 x29 x30 x31 m1 pwsF ARL ARB ARP LENP AGP AR8 FR ST MU WM MI.
    pose proof sp_range as SPR. pose proof ds_al4 as AL4.
    pose proof (u32arr_bound _ _ _ _ ARB) as BB. rewrite LENb in BB.
    urun_to 0x243b4%Z.
    enter_with (S0_hb_loopZ1 23 0 _ _ _ _ _ _ _ _ _ bws pwsF);
      [ st_eq | lia | lia | exact ARL | exact ARB | exact LENb | | exact ARP | exact LENP | exact AGP
      | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
    cbn [fill0 Z.to_nat]. apply ag32s_refl.
  Qed.
End P.

End ACeilS1.
End S0_hbCreateB.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasHb OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzHbW OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_hbCreate.S0_hbCreateB.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require RelLiaR.
Local Ltac lia ::= RelLia.lia_rf3.
Local Ltac StoreFast.tlia ::= RelLiaR.tlia_rr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Section P.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : word -> option byte).
  Variables (DS t : Z) (lws bws pws : list word) (lbs : list byte) (minLen maxLen alpha lo : Z).
  Hypothesis LENl : length lws = 258%nat.
  Hypothesis LENb : length bws = 258%nat.
  Hypothesis LENp : length pws = 258%nat.
  Hypothesis LEN8 : length lbs = 258%nat.
  Hypothesis HS : (0 <= DS)%Z /\ (DS mod 16 = 0)%Z /\ (0 <= t < 6)%Z.
  Hypothesis HLO : (DS + 64144 <= lo)%Z /\ (lo + 64 <= bv_unsigned sp)%Z.
  Hypothesis Halpha : (1 <= alpha <= 258)%Z.
  Hypothesis Hmm : (1 <= minLen /\ minLen <= maxLen <= 20)%Z.
  Hypothesis Hlen : forall j, (0 <= j < alpha)%Z -> (minLen <= uv8 lbs j <= maxLen)%Z.

  Notation usp := (bv_unsigned sp).
  Notation LIM := (DS + 45436 + 1032 * t)%Z.
  Notation BASE := (DS + 51628 + 1032 * t)%Z.
  Notation PERM := (DS + 57820 + 1032 * t)%Z.
  Notation LEN := (DS + 43888 + 258 * t)%Z.
  Notation limit0 := (sv32 lws). Notation base0 := (sv32 bws). Notation perm0 := (sv32 pws). Notation len := (uv8 lbs).
  Notation W := ([(LIM, LIM + 1032); (BASE, BASE + 1032); (PERM, PERM + 1032); (usp + -64, usp)])%Z.
  Notation POST := (S0_hbCreate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DS t lws bws pws lbs minLen maxLen alpha lo m).
  Notation base1 := (hbm_base1 base0).
  Notation base2 := (hbm_base2 len alpha base0).
  Notation base3 := (hbm_base3 len alpha base0).
  Notation limit1 := (hbm_limit1 limit0).
  Notation limitF := (hbm_limit len alpha minLen maxLen limit0 base0).
  Notation baseF := (hbm_base len alpha minLen maxLen limit0 base0).
  Notation permF := (hbm_perm len alpha minLen maxLen perm0).
  (* [comment removed for export] *)
  Notation FRAME mm := (rw_cells s0segs mm (usp + -32) [C8 s3; C8 s2; C8 s1; C8 s0]).

  (* [comment removed for export] *)
  Ltac u32_store_done ARR i :=
    lazymatch goal with
    | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?mm _ (le4 ?v)) _) =>
        lazymatch type of ARR with u32arr _ _ ?A ?ws =>
          let H := fresh "ARR" in
          pose proof (u32arr_write segs mm A ws i v ARR ltac:(lia)) as H; clear ARR; store_done; rename H into ARR
        end
    end.

  Lemma sp_range : (0 <= usp < 2^64)%Z.
  Proof using sp DS lws bws pws lbs LENl LENb LENp LEN8. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R. lia. Qed.
  Lemma ds_al4 : (DS mod 4 = 0)%Z.
  Proof. destruct HS as (_ & A16 & _). clear - A16. Z.div_mod_to_equations; lia. Qed.

  Notation pstate i j := (hb_perm_state len alpha minLen perm0 i j).
  Local Ltac feed H := repeat first [ specialize (H Halpha) | specialize (H Hmm) | specialize (H Hlen) ].

  (* [comment removed for export] *)
  Lemma S0_hb_permJ : forall (k : nat) (i j : Z) (x9 x18 x19 : word) m1 pwsc (Q : machine_state -> Prop),
    (Z.of_nat k = alpha - j)%Z -> (0 <= j < alpha)%Z -> (minLen <= i <= maxLen)%Z ->
    u32arr s0segs m1 LIM lws -> u32arr s0segs m1 BASE bws ->
    u32arr s0segs m1 PERM pwsc -> length pwsc = 258%nat -> ag32s pwsc (fst (pstate i j)) 258 ->
    u8arr s0segs m1 LEN lbs -> FRAME m1 -> stk s0segs m1 lo (usp + -32) ->
    munch W m m1 -> wmono s0segs m m1 -> mem_inv s0segs m1 ->
    (forall (y9 y18 y19 : word) m2 pwsc',
       u32arr s0segs m2 LIM lws -> u32arr s0segs m2 BASE bws ->
       u32arr s0segs m2 PERM pwsc' -> length pwsc' = 258%nat -> ag32s pwsc' (fst (pstate i alpha)) 258 ->
       u8arr s0segs m2 LEN lbs -> FRAME m2 -> stk s0segs m2 lo (usp + -32) ->
       munch W m m2 -> wmono s0segs m m2 -> mem_inv s0segs m2 ->
       evt s0segs Q
         (MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 alpha) (Z_to_bv 64 1) (Z_to_bv 64 (LEN + alpha)) y9
                 (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) (Z_to_bv 64 PERM) (Z_to_bv 64 LEN)
                 (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 alpha) (Z_to_bv 64 (snd (pstate i alpha)))
                 y18 y19 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 i) (Z_to_bv 64 alpha) (Z_to_bv 64 0) (Z_to_bv 64 (LEN + alpha)))
             F (Z_to_bv 64 0x24388) fc None m2 (seg_rom s0segs))) ->
    evt s0segs Q
      (MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 alpha) (Z_to_bv 64 1) (Z_to_bv 64 (LEN + j)) x9
              (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) (Z_to_bv 64 PERM) (Z_to_bv 64 LEN)
              (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 alpha) (Z_to_bv 64 (snd (pstate i j)))
              x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 i) (Z_to_bv 64 j) (Z_to_bv 64 (alpha - j)) (Z_to_bv 64 (LEN + j)))
          F (Z_to_bv 64 0x24318) fc None m1 (seg_rom s0segs)).
  Proof.
    induction k as [|k IH]; intros i j x9 x18 x19 m1 pwsc Q HK Hj Hi
      ARL ARB ARP LENP AGP AR8 FR ST MU WM MI HQ; [lia|].
    pose proof sp_range as SPR. pose proof ds_al4 as AL4.
    pose proof (u32arr_bound _ _ _ _ ARP) as BP. rewrite LENP in BP.
    pose proof (u8arr_bound _ _ _ _ AR8) as B8. rewrite LEN8 in B8.
    pose proof (hbw_perm_pp_range len alpha minLen maxLen) as PPR. feed PPR. specialize (PPR perm0 i j ltac:(lia) ltac:(lia)).
    set (pp := snd (pstate i j)) in *.
    urun_to 0x2432c%Z.
    destruct (nth_error_ok lbs j 258 LEN8 ltac:(lia)) as [b NTH].
    pose proof (u8arr_read s0segs m1 LEN lbs j b _ AR8 NTH ltac:(lia) eq_refl) as RD.
    wstep. clear RD.
    pose proof (uv8_nth _ _ _ NTH) as VB. cbv beta delta [zxb]. rewrite <- VB.
    pose proof (Hlen j ltac:(lia)) as LJ.
    assert (STEP : pstate i (j + 1) = (if (len j =? i)%Z then (zfupd (fst (pstate i j)) pp j, (pp + 1)%Z) else pstate i j)).
    { unfold hb_perm_state. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. rewrite hb_permJ_snoc. cbn zeta.
      replace (0 + Z.of_nat (Z.to_nat j))%Z with j by lia. fold (pstate i j). fold pp.
      destruct (pstate i j); reflexivity. }
    wstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      replace (len j =? i)%Z with false in STEP by (symmetry; apply Z.eqb_neq; lia).
      urun. if_cases K2; zify_cond K2.
      + enter_with (IH i (j + 1)%Z _ _ _ m1 pwsc Q);
          [ st_eq | lia | lia | lia | exact ARL | exact ARB | exact ARP | exact LENP | | exact AR8 | exact FR | exact ST
          | exact MU | exact WM | exact MI | exact HQ ].
        * rewrite STEP. reflexivity.
        * rewrite STEP. exact AGP.
      + enter_with (HQ _ _ _ m1 pwsc); [ st_eq | exact ARL | exact ARB | exact ARP | exact LENP | | exact AR8 | exact FR | exact ST
          | exact MU | exact WM | exact MI ].
        * replace (pstate i alpha) with (pstate i (j + 1)) by (f_equal; lia). rewrite STEP. reflexivity.
        * replace (pstate i alpha) with (pstate i (j + 1)) by (f_equal; lia). rewrite STEP. exact AGP.
    - (* [comment removed for export] *)
      replace (len j =? i)%Z with true in STEP by (symmetry; apply Z.eqb_eq; lia).
      pose proof (hbw_perm_store len alpha minLen maxLen) as PPS. feed PPS. specialize (PPS perm0 i j ltac:(lia) ltac:(lia) ltac:(lia)).
      fold pp in PPS.
      urun_to 0x24368%Z.
      pose proof (u32arr_store_ok s0segs m1 PERM pwsc pp _ ARP ltac:(lia) eq_refl) as SO.
      wstep. u32_store_done ARP pp. rename ARP into ARP'.
      urun. if_cases K2; zify_cond K2.
      + enter_with (IH i (j + 1)%Z _ _ _ _ (upd pwsc (Z.to_nat pp) (Z_to_bv 64 j)) Q);
          [ st_eq | lia | lia | lia | exact ARL | exact ARB | exact ARP' | rewrite upd_length; exact LENP | | exact AR8 | exact FR | exact ST
          | exact MU | exact WM | exact MI | exact HQ ].
        * rewrite STEP. reflexivity.
        * rewrite STEP. cbn [fst]. apply ag32s_upd; [exact AGP | lia | rewrite LENP; lia | lia].
      + enter_with (HQ _ _ _ _ (upd pwsc (Z.to_nat pp) (Z_to_bv 64 j)));
          [ st_eq | exact ARL | exact ARB | exact ARP' | rewrite upd_length; exact LENP | | exact AR8 | exact FR | exact ST
          | exact MU | exact WM | exact MI ].
        * replace (pstate i alpha) with (pstate i (j + 1)) by (f_equal; lia). rewrite STEP. reflexivity.
        * replace (pstate i alpha) with (pstate i (j + 1)) by (f_equal; lia). rewrite STEP. cbn [fst]. apply ag32s_upd; [exact AGP | lia | rewrite LENP; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma S0_hb_permI : forall (k : nat) (i : Z) (x8 x9 x18 x19 x29 x30 x31 : word) m1 pwsc,
    (Z.of_nat k = maxLen + 1 - i)%Z -> (minLen <= i <= maxLen)%Z ->
    u32arr s0segs m1 LIM lws -> u32arr s0segs m1 BASE bws ->
    u32arr s0segs m1 PERM pwsc -> length pwsc = 258%nat -> ag32s pwsc (fst (pstate i 0)) 258 ->
    u8arr s0segs m1 LEN lbs -> FRAME m1 -> stk s0segs m1 lo (usp + -32) ->
    munch W m m1 -> wmono s0segs m m1 -> mem_inv s0segs m1 ->
    evt s0segs POST
      (MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 alpha) (Z_to_bv 64 1) x8 x9
              (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) (Z_to_bv 64 PERM) (Z_to_bv 64 LEN)
              (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 alpha) (Z_to_bv 64 (snd (pstate i 0)))
              x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 i) x29 x30 x31)
          F (Z_to_bv 64 0x24304) fc None m1 (seg_rom s0segs)).
  Proof.
    induction k as [|k IH]; intros i x8 x9 x18 x19 x29 x30 x31 m1 pwsc HK Hi
      ARL ARB ARP LENP AGP AR8 FR ST MU WM MI; [lia|].
    pose proof sp_range as SPR.
    wstep. if_false_z. urun_to 0x24318%Z.
    eapply evt_eq; [ | eapply (S0_hb_permJ (Z.to_nat alpha) i 0 _ _ _ m1 pwsc);
      [ lia | lia | lia | exact ARL | exact ARB | exact ARP | exact LENP | exact AGP | exact AR8 | exact FR | exact ST
      | exact MU | exact WM | exact MI | ] ]; [ st_eq |].
    clear ARL ARB ARP LENP AGP AR8 FR ST MU WM MI m1 pwsc.
    intros y9 y18 y19 m2 pwsc' ARL ARB ARP LENP AGP AR8 FR ST MU WM MI.
    assert (NXT : pstate (i + 1) 0 = pstate i alpha).
    { unfold hb_perm_state. replace (Z.to_nat (i + 1 - minLen)) with (S (Z.to_nat (i - minLen))) by lia.
      rewrite hb_permI_snoc. cbn zeta. replace (minLen + Z.of_nat (Z.to_nat (i - minLen)))%Z with i by lia.
      cbn [hb_permJ Z.to_nat]. destruct (hb_permJ len i 0 (Z.to_nat alpha) _ _); reflexivity. }
    urun. if_cases K; zify_cond K; bz32_in K.
    - (* [comment removed for export] *)
      enter_with (IH (i + 1)%Z _ _ _ _ _ _ _ m2 pwsc');
        [ st_eq | lia | lia | exact ARL | exact ARB | exact ARP | exact LENP | | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      + rewrite NXT. reflexivity.
      + rewrite NXT. exact AGP.
    - (* [comment removed for export] *)
      enter_with (S0_hb_partB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DS t lws bws pws lbs minLen maxLen alpha lo
                    LENl LENb LENp LEN8 HS HLO Halpha Hmm Hlen _ _ _ _ _ _ _ _ _ _ _ _ _ m2 pwsc');
        [ st_eq | exact ARL | exact ARB | exact ARP | exact LENP | | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      unfold hbm_perm. replace (span minLen maxLen) with (Z.to_nat (i + 1 - minLen)) by (unfold span; lia).
      change (ag32s pwsc' (fst (pstate i alpha)) 258) in AGP. rewrite <- NXT in AGP.
      unfold hb_perm_state in AGP. cbn [hb_permJ Z.to_nat] in AGP.
      destruct (hb_permI len alpha minLen (Z.to_nat (i + 1 - minLen)) perm0 0) eqn:E. cbn [fst snd] in AGP. cbn [fst]. exact AGP.
  Qed.
End P.

(* [comment removed for export] *)
Lemma S0_hbCreate_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (DS t : Z) (lws bws pws : list word) (lbs : list byte) (minLen maxLen alpha lo : Z),
  u32arr s0segs m (DS + 45436 + 1032 * t) lws -> length lws = 258%nat ->
  u32arr s0segs m (DS + 51628 + 1032 * t) bws -> length bws = 258%nat ->
  u32arr s0segs m (DS + 57820 + 1032 * t) pws -> length pws = 258%nat ->
  u8arr s0segs m (DS + 43888 + 258 * t) lbs -> length lbs = 258%nat ->
  (0 <= DS)%Z /\ (DS mod 16 = 0)%Z /\ (0 <= t < 6)%Z ->
  (DS + 64144 <= lo)%Z /\ (lo + 64 <= bv_unsigned sp)%Z ->
  stk s0segs m lo (bv_unsigned sp) -> mem_inv s0segs m ->
  (1 <= alpha <= 258)%Z -> (1 <= minLen /\ minLen <= maxLen <= 20)%Z ->
  (forall j, (0 <= j < alpha)%Z -> (minLen <= uv8 lbs j <= maxLen)%Z) ->
  a0 = Z_to_bv 64 (DS + 45436 + 1032 * t) -> a1 = Z_to_bv 64 (DS + 51628 + 1032 * t) ->
  a2 = Z_to_bv 64 (DS + 57820 + 1032 * t) -> a3 = Z_to_bv 64 (DS + 43888 + 258 * t) ->
  a4 = Z_to_bv 64 minLen -> a5 = Z_to_bv 64 maxLen -> a6 = Z_to_bv 64 alpha ->
  evt s0segs (S0_hbCreate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DS t lws bws pws lbs minLen maxLen alpha lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x242d4) fc None m (seg_rom s0segs)).
Proof.
  intros until lo. intros ARL LENl ARB LENb ARP LENp AR8 LEN8 HS HLO ST MI Halpha Hmm Hlen -> -> -> -> -> -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl ([(DS + 45436 + 1032 * t, DS + 45436 + 1032 * t + 1032); (DS + 51628 + 1032 * t, DS + 51628 + 1032 * t + 1032);
                           (DS + 57820 + 1032 * t, DS + 57820 + 1032 * t + 1032); (bv_unsigned sp + -64, bv_unsigned sp)])%Z m) as MU.
  pose proof (wmono_refl s0segs m) as WM.
  pose proof (u8arr_bound _ _ _ _ AR8) as B8. rewrite LEN8 in B8.
  carve_frame 32%nat ST.
  urun_to 0x242e8%Z. wstep. if_false_z. urun_to 0x24304%Z.
  enter_with (S0_hb_permI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DS t lws bws pws lbs minLen maxLen alpha lo
                LENl LENb LENp LEN8 HS HLO Halpha Hmm Hlen (Z.to_nat (maxLen + 1 - minLen)) minLen _ _ _ _ _ _ _ _ pws);
    [ st_eq | lia | lia | exact ARL | exact ARB | exact ARP | exact LENp | | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
  - unfold hb_perm_state. rewrite Z.sub_diag. cbn [hb_permI hb_permJ Z.to_nat fst snd]. reflexivity.
  - unfold hb_perm_state. rewrite Z.sub_diag. cbn [hb_permI hb_permJ Z.to_nat fst snd]. apply ag32s_refl.
Qed.

End ACeilS1.
