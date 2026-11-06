(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzLemmasHb BzHbW BzTac CmpCut AsanKit AsanCut.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia RelLiaR.
Local Ltac lia ::= RelLia.lia_rf3.
Local Ltac StoreFast.tlia ::= RelLiaR.tlia_rr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section P.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (DS t : Z) (lws bws pws : list word) (lbs : list byte) (minLen maxLen alpha lo : Z).
  Variable Q : machine_state -> Prop.
  Hypothesis LENl : length lws = 258%nat.
  Hypothesis LENb : length bws = 258%nat.
  Hypothesis LENp : length pws = 258%nat.
  Hypothesis LEN8 : length lbs = 258%nat.
  Hypothesis HS : (0x61e000 <= DS)%Z /\ (DS mod 16 = 0)%Z /\ (0 <= t < 6)%Z.
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
  Notation base1 := (hbm_base1 base0).
  Notation base2 := (hbm_base2 len alpha base0).
  Notation base3 := (hbm_base3 len alpha base0).
  Notation limit1 := (hbm_limit1 limit0).
  Notation limitF := (hbm_limit len alpha minLen maxLen limit0 base0).
  Notation baseF := (hbm_base len alpha minLen maxLen limit0 base0).
  Notation permF := (hbm_perm len alpha minLen maxLen perm0).
  Notation cSB := (Z_to_bv 64 2147450880).
  (* [comment removed for export] *)
  Notation FRAME mm := (rw_cells a0segs mm (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

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
  Proof using sp. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

  Notation pstate i j := (hb_perm_state len alpha minLen perm0 i j).
  Local Ltac feed H := repeat first [ specialize (H Halpha) | specialize (H Hmm) | specialize (H Hlen) ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section S1.
    Variable m : word -> option byte.
    Notation W1 := ([(PERM, PERM + 1032); (usp + -64, usp)])%Z.
    Hypothesis SH : shzW a0segs W1 m DS (DS + 64144).

    (* [comment removed for export] *)
    Definition K1 : Prop :=
      forall (m1 : word -> option byte) (pwsF : list word) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
        u32arr a0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
        u8arr a0segs m1 LEN lbs -> FRAME m1 -> stk a0segs m1 lo (usp + -64) ->
        munch W1 m m1 -> wmono a0segs m m1 -> mem_inv a0segs m1 ->
        evt a0segs Q
          (MS (mkR (Z_to_bv 64 0x9e0cc) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 maxLen) (Z_to_bv 64 minLen)
                  (Z_to_bv 64 BASE) (Z_to_bv 64 0) (Z_to_bv 64 92) a3 a4 a5 a6 a7
                  (Z_to_bv 64 BASE) (Z_to_bv 64 LIM) (Z_to_bv 64 alpha) (Z_to_bv 64 LEN) cSB s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x52ea0) fc None m1 (seg_rom a0segs)).

    (* [comment removed for export] *)
    Lemma A0_hb_permJ : forall (k : nat) (i j : Z) (x6 x7 x11 x28 x29 x30 x31 : word) m1 pwsc (Q' : machine_state -> Prop),
      (Z.of_nat k = alpha - j)%Z -> (0 <= j < alpha)%Z -> (minLen <= i <= maxLen)%Z ->
      u32arr a0segs m1 PERM pwsc -> length pwsc = 258%nat -> ag32s pwsc (fst (pstate i j)) 258 ->
      u8arr a0segs m1 LEN lbs -> FRAME m1 -> stk a0segs m1 lo (usp + -64) ->
      munch W1 m m1 -> wmono a0segs m m1 -> mem_inv a0segs m1 ->
      (forall (y6 y11 : word) m2 pwsc',
         u32arr a0segs m2 PERM pwsc' -> length pwsc' = 258%nat -> ag32s pwsc' (fst (pstate i alpha)) 258 ->
         u8arr a0segs m2 LEN lbs -> FRAME m2 -> stk a0segs m2 lo (usp + -64) ->
         munch W1 m m2 -> wmono a0segs m m2 -> mem_inv a0segs m2 ->
         evt a0segs Q'
           (MS (mkR ra (Z_to_bv 64 (usp + -64)) gp tp (Z_to_bv 64 (LEN + alpha)) y6 x7 (Z_to_bv 64 maxLen) (Z_to_bv 64 minLen)
                   (Z_to_bv 64 (LEN + alpha)) y11 (Z_to_bv 64 PERM) (Z_to_bv 64 (snd (pstate i alpha))) (Z_to_bv 64 alpha)
                   (Z_to_bv 64 i) (Z_to_bv 64 alpha) (Z_to_bv 64 0)
                   (Z_to_bv 64 BASE) (Z_to_bv 64 LIM) (Z_to_bv 64 alpha) (Z_to_bv 64 LEN) cSB s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 0x9e0b4) fc None m2 (seg_rom a0segs))) ->
      evt a0segs Q'
        (MS (mkR ra (Z_to_bv 64 (usp + -64)) gp tp (Z_to_bv 64 (LEN + j)) x6 x7 (Z_to_bv 64 maxLen) (Z_to_bv 64 minLen)
                (Z_to_bv 64 (LEN + j)) x11 (Z_to_bv 64 PERM) (Z_to_bv 64 (snd (pstate i j))) (Z_to_bv 64 alpha)
                (Z_to_bv 64 i) (Z_to_bv 64 j) (Z_to_bv 64 (alpha - j))
                (Z_to_bv 64 BASE) (Z_to_bv 64 LIM) (Z_to_bv 64 alpha) (Z_to_bv 64 LEN) cSB s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9e048) fc None m1 (seg_rom a0segs)).
    Proof.
      induction k as [|k IH]; intros i j x6 x7 x11 x28 x29 x30 x31 m1 pwsc Q' HK Hj Hi
        ARP LENP AGP AR8 FR ST MU WM MI HQ; [lia|].
      pose proof sp_range as SPR.
      pose proof (u32arr_bound _ _ _ _ ARP) as BP. rewrite LENP in BP.
      pose proof (u8arr_bound _ _ _ _ AR8) as B8. rewrite LEN8 in B8.
      pose proof (hbw_perm_pp_range len alpha minLen maxLen) as PPR. feed PPR. specialize (PPR perm0 i j ltac:(lia) ltac:(lia)).
      set (pp := snd (pstate i j)) in *.
      destruct (nth_error_ok lbs j 258 LEN8 ltac:(lia)) as [b NTH].
      (* [comment removed for export] *)
      arun_to 0x9e058%Z.
      pose proof (u8arr_read a0segs m1 LEN lbs j b _ AR8 NTH ltac:(lia) eq_refl) as RD.
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
        wstep. wstep. wstep. wstep. wstep. if_cases K2; zify_cond K2.
        + enter_with (IH i (j + 1)%Z _ _ _ _ _ _ _ m1 pwsc Q');
            [ st_eq | lia | lia | lia | exact ARP | exact LENP | | exact AR8 | exact FR | exact ST
            | exact MU | exact WM | exact MI | exact HQ ].
          * rewrite STEP. reflexivity.
          * rewrite STEP. exact AGP.
        + wstep. enter_with (HQ _ _ m1 pwsc); [ st_eq | exact ARP | exact LENP | | exact AR8 | exact FR | exact ST
            | exact MU | exact WM | exact MI ].
          * replace (pstate i alpha) with (pstate i (j + 1)) by (f_equal; lia). rewrite STEP. reflexivity.
          * replace (pstate i alpha) with (pstate i (j + 1)) by (f_equal; lia). rewrite STEP. exact AGP.
      - (* [comment removed for export] *)
        replace (len j =? i)%Z with true in STEP by (symmetry; apply Z.eqb_eq; lia).
        pose proof (hbw_perm_store len alpha minLen maxLen) as PPS. feed PPS. specialize (PPS perm0 i j ltac:(lia) ltac:(lia) ltac:(lia)).
        fold pp in PPS.
        (* [comment removed for export] *)
        arun_to 0x9e078%Z.
        pose proof (u32arr_store_ok a0segs m1 PERM pwsc pp _ ARP ltac:(lia) eq_refl) as SO.
        wstep. u32_store_done ARP pp. rename ARP into ARP'.
        wstep. wstep. wstep. wstep. wstep. wstep. if_cases K2; zify_cond K2.
        + enter_with (IH i (j + 1)%Z _ _ _ _ _ _ _ _ (upd pwsc (Z.to_nat pp) (Z_to_bv 64 j)) Q');
            [ st_eq | lia | lia | lia | exact ARP' | rewrite upd_length; exact LENP | | exact AR8 | exact FR | exact ST
            | exact MU | exact WM | exact MI | exact HQ ].
          * rewrite STEP. reflexivity.
          * rewrite STEP. cbn [fst]. apply ag32s_upd; [exact AGP | lia | rewrite LENP; lia | lia].
        + wstep. enter_with (HQ _ _ _ (upd pwsc (Z.to_nat pp) (Z_to_bv 64 j)));
            [ st_eq | exact ARP' | rewrite upd_length; exact LENP | | exact AR8 | exact FR | exact ST
            | exact MU | exact WM | exact MI ].
          * replace (pstate i alpha) with (pstate i (j + 1)) by (f_equal; lia). rewrite STEP. reflexivity.
          * replace (pstate i alpha) with (pstate i (j + 1)) by (f_equal; lia). rewrite STEP. cbn [fst]. apply ag32s_upd; [exact AGP | lia | rewrite LENP; lia | lia].
    Qed.

    (* [comment removed for export] *)
    Lemma A0_hb_permI : forall (k : nat) (i : Z) (x5 x6 x7 x11 x15 x16 x17 x28 x29 x30 x31 : word) m1 pwsc,
      (Z.of_nat k = maxLen + 1 - i)%Z -> (minLen <= i <= maxLen)%Z ->
      u32arr a0segs m1 PERM pwsc -> length pwsc = 258%nat -> ag32s pwsc (fst (pstate i 0)) 258 ->
      u8arr a0segs m1 LEN lbs -> FRAME m1 -> stk a0segs m1 lo (usp + -64) ->
      munch W1 m m1 -> wmono a0segs m m1 -> mem_inv a0segs m1 ->
      K1 ->
      evt a0segs Q
        (MS (mkR ra (Z_to_bv 64 (usp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 maxLen) (Z_to_bv 64 minLen)
                (Z_to_bv 64 i) x11 (Z_to_bv 64 PERM) (Z_to_bv 64 (snd (pstate i 0))) (Z_to_bv 64 alpha) x15 x16 x17
                (Z_to_bv 64 BASE) (Z_to_bv 64 LIM) (Z_to_bv 64 alpha) (Z_to_bv 64 LEN) cSB s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9e030) fc None m1 (seg_rom a0segs)).
    Proof.
      induction k as [|k IH]; intros i x5 x6 x7 x11 x15 x16 x17 x28 x29 x30 x31 m1 pwsc HK Hi
        ARP LENP AGP AR8 FR ST MU WM MI HK1; [lia|].
      pose proof sp_range as SPR.
      (* [comment removed for export] *)
      wstep. wstep. if_false_z. wstep. wstep. wstep. wstep.
      eapply evt_eq; [ | eapply (A0_hb_permJ (Z.to_nat alpha) i 0 _ _ _ _ _ _ _ m1 pwsc);
        [ lia | lia | lia | exact ARP | exact LENP | exact AGP | exact AR8 | exact FR | exact ST
        | exact MU | exact WM | exact MI | ] ]; [ st_eq |].
      clear ARP LENP AGP AR8 FR ST MU WM MI m1 pwsc.
      intros y6 y11 m2 pwsc' ARP LENP AGP AR8 FR ST MU WM MI.
      assert (NXT : pstate (i + 1) 0 = pstate i alpha).
      { unfold hb_perm_state. replace (Z.to_nat (i + 1 - minLen)) with (S (Z.to_nat (i - minLen))) by lia.
        rewrite hb_permI_snoc. cbn zeta. replace (minLen + Z.of_nat (Z.to_nat (i - minLen)))%Z with i by lia.
        cbn [hb_permJ Z.to_nat]. destruct (hb_permJ len i 0 (Z.to_nat alpha) _ _); reflexivity. }
      (* [comment removed for export] *)
      wstep. wstep. if_cases K; zify_cond K; bz32_in K.
      - (* [comment removed for export] *)
        enter_with (IH (i + 1)%Z _ _ _ _ _ _ _ _ _ _ _ m2 pwsc');
          [ st_eq | lia | lia | exact ARP | exact LENP | | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI | exact HK1 ].
        + rewrite NXT. reflexivity.
        + rewrite NXT. exact AGP.
      - (* [comment removed for export] *)
        wstep. wstep. wstep. wstep.
        enter_with (HK1 m2 pwsc' _ _ _ _ _ _ _ _ _ _ _ _);
          [ st_eq | exact ARP | exact LENP | | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
        unfold hbm_perm. replace (span minLen maxLen) with (Z.to_nat (i + 1 - minLen)) by (unfold span; lia).
        change (ag32s pwsc' (fst (pstate i alpha)) 258) in AGP. rewrite <- NXT in AGP.
        unfold hb_perm_state in AGP. cbn [hb_permJ Z.to_nat] in AGP.
        destruct (hb_permI len alpha minLen (Z.to_nat (i + 1 - minLen)) perm0 0) eqn:E. cbn [fst snd] in AGP. cbn [fst]. exact AGP.
    Qed.

    (* [comment removed for export] *)
    Lemma A0_hbc_seg1 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      u32arr a0segs m PERM pws -> u8arr a0segs m LEN lbs ->
      stk a0segs m lo usp -> mem_inv a0segs m -> aconsts A0C m ->
      a0 = Z_to_bv 64 LIM -> a1 = Z_to_bv 64 BASE -> a2 = Z_to_bv 64 PERM -> a3 = Z_to_bv 64 LEN ->
      a4 = Z_to_bv 64 minLen -> a5 = Z_to_bv 64 maxLen -> a6 = Z_to_bv 64 alpha ->
      K1 ->
      evt a0segs Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9dfd4) fc None m (seg_rom a0segs)).
    Proof.
      intros until t6. intros ARP AR8 ST MI AC -> -> -> -> -> -> -> HK1.
      pose proof sp_range as SPR.
      destruct AC as [GOT SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar A0C ci_segs] in GOT, SBV.
      pose proof (munch_refl W1 m) as MU. pose proof (wmono_refl a0segs m) as WM.
      pose proof (u8arr_bound _ _ _ _ AR8) as B8. rewrite LEN8 in B8.
      pose proof (u32arr_bound _ _ _ _ ARP) as BP. rewrite LENp in BP.
      carve_frame 64%nat ST.
      do 9 wstep. do 9 wstep.
      (* [comment removed for export] *)
      wstep. if_false_z. wstep. wstep. wstep. wstep.
      enter_with (A0_hb_permI (Z.to_nat (maxLen + 1 - minLen)) minLen _ _ _ _ _ _ _ _ _ _ _ _ pws);
        [ st_eq | lia | lia | exact ARP | exact LENp | | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI | exact HK1 ].
      - unfold hb_perm_state. rewrite Z.sub_diag. cbn [hb_permI hb_permJ Z.to_nat fst snd]. reflexivity.
      - unfold hb_perm_state. rewrite Z.sub_diag. cbn [hb_permI hb_permJ Z.to_nat fst snd]. apply ag32s_refl.
    Qed.
  End S1.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section S2.
    Variable m : word -> option byte.
    Notation W2 := ([(BASE, BASE + 1032)])%Z.
    Hypothesis SH : shzW a0segs W2 m DS (DS + 64144).

    Definition K2 : Prop :=
      forall (m1 : word -> option byte) (bws3 : list word) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
        u32arr a0segs m1 BASE bws3 -> length bws3 = 258%nat -> ag32s bws3 base3 258 ->
        u8arr a0segs m1 LEN lbs ->
        munch W2 m m1 -> wmono a0segs m m1 -> mem_inv a0segs m1 ->
        evt a0segs Q
          (MS (mkR (Z_to_bv 64 0x9e1b0) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 maxLen) (Z_to_bv 64 minLen)
                  (Z_to_bv 64 LIM) (Z_to_bv 64 0) (Z_to_bv 64 92) a3 a4 a5 a6 a7
                  (Z_to_bv 64 BASE) (Z_to_bv 64 LIM) (Z_to_bv 64 0) (Z_to_bv 64 (LEN + alpha)) cSB s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x52ea0) fc None m1 (seg_rom a0segs)).

    (* [comment removed for export] *)
    Lemma A0_hb_loopA : forall (k mI : nat) (x1 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 : word) m1 bwsc (P : Z),
      let i := (1 + Z.of_nat mI)%Z in
      (Z.of_nat k = 23 - i)%Z -> (1 <= i <= 22)%Z ->
      P = hb_accum 1 mI base2 (i - 1) ->
      u32arr a0segs m1 BASE bwsc -> length bwsc = 258%nat -> ag32s bwsc (hb_accum 1 mI base2) 258 ->
      u8arr a0segs m1 LEN lbs ->
      munch W2 m m1 -> wmono a0segs m m1 -> mem_inv a0segs m1 ->
      K2 ->
      evt a0segs Q
        (MS (mkR x1 (Z_to_bv 64 (usp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 maxLen) (Z_to_bv 64 minLen)
                (Z_to_bv 64 (BASE + 4 * i)) (Z_to_bv 64 P) (Z_to_bv 64 (BASE + 4 * i)) (Z_to_bv 64 (23 - i)) x14 x15 x16 x17
                (Z_to_bv 64 BASE) (Z_to_bv 64 LIM) (Z_to_bv 64 0) (Z_to_bv 64 (LEN + alpha)) cSB s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9e160) fc None m1 (seg_rom a0segs)).
    Proof.
      induction k as [|k IH]; intros mI x1 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 m1 bwsc P i HK Hi HP
        ARB LENB AGB AR8 MU WM MI HK2; subst i; [lia|].
      pose proof sp_range as SPR.
      pose proof (u32arr_bound _ _ _ _ ARB) as BB. rewrite LENB in BB.
      pose proof (hbw_accum_step len alpha minLen maxLen Halpha Hmm Hlen base0 (Z.of_nat mI) ltac:(lia)) as AF. cbn zeta in AF.
      rewrite Nat2Z.id in AF. cps_destruct AF as (AF1 & AF2 & AF3).
      set (i := (1 + Z.of_nat mI)%Z) in *.
      destruct (nth_error_ok bwsc i 258 LENB ltac:(lia)) as [w2 NTH2].
      (* [comment removed for export] *)
      arun_to 0x9e170%Z.
      pose proof (u32arr_read a0segs m1 BASE bwsc i w2 _ ARB NTH2 ltac:(lia) eq_refl) as RD.
      wstep. clear RD.
      pose proof (AGB i ltac:(lia)) as V2. rewrite (sv32_nth _ _ _ NTH2) in V2.
      cbv beta delta [sx32]. rewrite V2.
      set (P2 := hb_accum 1 mI base2 i) in *. rewrite HP.
      set (P1 := hb_accum 1 mI base2 (i - 1)) in *.
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      pose proof (u32arr_store_ok a0segs m1 BASE bwsc i _ ARB ltac:(lia) eq_refl) as SO.
      wstep. u32_store_done ARB i. rename ARB into ARB'.
      assert (AGB' : ag32s (upd bwsc (Z.to_nat i) (Z_to_bv 64 (P2 + P1))) (hb_accum 1 (S mI) base2) 258).
      { rewrite hb_accum_snoc. cbn zeta. fold i. replace (1 + Z.of_nat mI)%Z with i by lia.
        apply ag32s_upd; [exact AGB | lia | rewrite LENB; lia | lia]. }
      (* [comment removed for export] *)
      wstep. wstep. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        enter_with (IH (S mI) _ _ _ _ _ _ _ _ _ _ _ _ _ (upd bwsc (Z.to_nat i) (Z_to_bv 64 (P2 + P1))) (P2 + P1)%Z);
          [ st_eq | lia | lia | | exact ARB' | rewrite upd_length; exact LENB | exact AGB'
          | exact AR8 | exact MU | exact WM | exact MI | exact HK2 ].
        rewrite hb_accum_snoc. cbn zeta. replace (1 + Z.of_nat (S mI) - 1)%Z with i by lia. replace (1 + Z.of_nat mI)%Z with i by lia.
        rewrite zfupd_same. lia.
      - (* [comment removed for export] *)
        wstep. wstep. wstep. wstep. wstep.
        enter_with (HK2 _ (upd bwsc (Z.to_nat i) (Z_to_bv 64 (P2 + P1))) _ _ _ _ _ _ _ _ _ _ _ _);
          [ st_eq | exact ARB' | rewrite upd_length; exact LENB | | exact AR8 | exact MU | exact WM | exact MI ].
        unfold hbm_base3. replace 22%nat with (S mI) by lia. exact AGB'.
    Qed.

    (* [comment removed for export] *)
    Lemma A0_hb_loopC : forall (k : nat) (j : Z) (x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m1 bwsc,
      (Z.of_nat k = alpha - j)%Z -> (0 <= j < alpha)%Z ->
      u32arr a0segs m1 BASE bwsc -> length bwsc = 258%nat -> ag32s bwsc (hb_count len 0 (Z.to_nat j) base1) 258 ->
      u8arr a0segs m1 LEN lbs ->
      munch W2 m m1 -> wmono a0segs m m1 -> mem_inv a0segs m1 ->
      K2 ->
      evt a0segs Q
        (MS (mkR x1 (Z_to_bv 64 (usp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 maxLen) (Z_to_bv 64 minLen)
                (Z_to_bv 64 (LEN + j)) x11 (Z_to_bv 64 (BASE + 4)) x13 x14 x15 x16 x17
                (Z_to_bv 64 BASE) (Z_to_bv 64 LIM) (Z_to_bv 64 (alpha - j)) (Z_to_bv 64 (LEN + j)) cSB s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9e0d8) fc None m1 (seg_rom a0segs)).
    Proof.
      induction k as [|k IH]; intros j x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1 bwsc HK Hj
        ARB LENB AGB AR8 MU WM MI HK2; [lia|].
      pose proof sp_range as SPR.
      pose proof (u32arr_bound _ _ _ _ ARB) as BB. rewrite LENB in BB.
      pose proof (u8arr_bound _ _ _ _ AR8) as B8. rewrite LEN8 in B8.
      pose proof (hbw_count_step len alpha minLen maxLen Halpha Hmm Hlen base0 j ltac:(lia)) as CF. cbn zeta in CF.
      destruct CF as [CF1 CF2].
      destruct (nth_error_ok lbs j 258 LEN8 ltac:(lia)) as [b NTH].
      (* [comment removed for export] *)
      arun_to 0x9e0e8%Z.
      pose proof (u8arr_read a0segs m1 LEN lbs j b _ AR8 NTH ltac:(lia) eq_refl) as RD.
      wstep. clear RD.
      pose proof (uv8_nth _ _ _ NTH) as VB. cbv beta delta [zxb]. rewrite <- VB.
      set (q := (len j + 1)%Z) in *.
      destruct (nth_error_ok bwsc q 258 LENB ltac:(lia)) as [w NTHw].
      (* [comment removed for export] *)
      arun_to 0x9e104%Z.
      pose proof (u32arr_read a0segs m1 BASE bwsc q w _ ARB NTHw ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD.
      pose proof (AGB q ltac:(lia)) as V1. rewrite (sv32_nth _ _ _ NTHw) in V1.
      cbv beta delta [sx32]. rewrite V1.
      set (P := hb_count len 0 (Z.to_nat j) base1 q) in *.
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      pose proof (u32arr_store_ok a0segs m1 BASE bwsc q _ ARB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SO.
      wstep. u32_store_done ARB q. rename ARB into ARB'.
      assert (AGB' : ag32s (upd bwsc (Z.to_nat q) (Z_to_bv 64 (P + 1))) (hb_count len 0 (S (Z.to_nat j)) base1) 258).
      { rewrite hb_count_snoc. cbn zeta. replace (0 + Z.of_nat (Z.to_nat j))%Z with j by lia. fold q. fold P.
        apply ag32s_upd; [exact AGB | lia | rewrite LENB; lia | lia]. }
      (* [comment removed for export] *)
      wstep. wstep. if_cases K; zify_cond K.
      - enter_with (IH (j + 1)%Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (upd bwsc (Z.to_nat q) (Z_to_bv 64 (P + 1))));
          [ st_eq | lia | lia | exact ARB' | rewrite upd_length; exact LENB | | exact AR8 | exact MU | exact WM | exact MI | exact HK2 ].
        replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. exact AGB'.
      - (* [comment removed for export] *)
        destruct (nth_error_ok (upd bwsc (Z.to_nat q) (Z_to_bv 64 (P + 1))) 0 258 ltac:(rewrite upd_length; exact LENB) ltac:(lia)) as [w0' NTH0].
        arun_to 0x9e154%Z.
        pose proof (u32arr_read a0segs _ BASE _ 0 w0' _ ARB' NTH0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
        wstep. clear RD.
        pose proof (AGB' 0%Z ltac:(lia)) as V0. rewrite (sv32_nth _ _ _ NTH0) in V0.
        cbv beta delta [sx32]. rewrite V0.
        pose proof (hbw_accum_step len alpha minLen maxLen Halpha Hmm Hlen base0 0 ltac:(lia)) as AF. cbn zeta in AF. cbn [hb_accum Z.to_nat] in AF.
        wstep. wstep.
        enter_with (A0_hb_loopA 22 0 _ _ _ _ _ _ _ _ _ _ _ _ _ (upd bwsc (Z.to_nat q) (Z_to_bv 64 (P + 1))) _);
          [ st_eq | lia | lia | | exact ARB' | rewrite upd_length; exact LENB | | exact AR8 | exact MU | exact WM | exact MI | exact HK2 ].
        + cbn [hb_accum]. unfold hbm_base2. replace (Z.to_nat alpha) with (S (Z.to_nat j)) by lia.
          replace (1 + Z.of_nat 0 - 1)%Z with 0%Z by lia. reflexivity.
        + cbn [hb_accum]. unfold hbm_base2. replace (Z.to_nat alpha) with (S (Z.to_nat j)) by lia. exact AGB'.
    Qed.

    (* [comment removed for export] *)
    Lemma A0_hbc_seg2 : forall (bws1 : list word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      u32arr a0segs m BASE bws1 -> length bws1 = 258%nat -> ag32s bws1 base1 258 ->
      u8arr a0segs m LEN lbs -> mem_inv a0segs m ->
      K2 ->
      evt a0segs Q
        (MS (mkR x1 (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 maxLen) (Z_to_bv 64 minLen) a0 a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 BASE) (Z_to_bv 64 LIM) (Z_to_bv 64 alpha) (Z_to_bv 64 LEN) cSB s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9e0cc) fc None m (seg_rom a0segs)).
    Proof.
      intros until t6. intros ARB LENB AGB AR8 MI HK2.
      pose proof sp_range as SPR.
      pose proof (munch_refl W2 m) as MU. pose proof (wmono_refl a0segs m) as WM.
      (* [comment removed for export] *)
      wstep. wstep. if_false_z. wstep.
      enter_with (A0_hb_loopC (Z.to_nat alpha) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ m bws1);
        [ st_eq | lia | lia | exact ARB | exact LENB | | exact AR8 | exact MU | exact WM | exact MI | exact HK2 ].
      cbn [hb_count Z.to_nat]. exact AGB.
    Qed.
  End S2.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section S3.
    Variable m : word -> option byte.
    Notation W3 := ([(LIM, LIM + 1032); (BASE, BASE + 1032); (usp + -64, usp)])%Z.
    Hypothesis SH : shzW a0segs W3 m DS (DS + 64144).

    Definition K3 : Prop :=
      forall (m1 : word -> option byte) (lws' bws' : list word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
        u32arr a0segs m1 LIM lws' -> length lws' = 258%nat -> ag32s lws' limitF 258 ->
        u32arr a0segs m1 BASE bws' -> length bws' = 258%nat -> ag32s bws' baseF 258 ->
        stk a0segs m1 lo usp ->
        munch W3 m m1 -> wmono a0segs m m1 -> mem_inv a0segs m1 ->
        evt a0segs Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom a0segs)).

    (* [comment removed for export] *)
    Lemma A0_hb_epi : forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word) m1 lwsF bwsF,
      u32arr a0segs m1 LIM lwsF -> length lwsF = 258%nat -> ag32s lwsF limitF 258 ->
      u32arr a0segs m1 BASE bwsF -> length bwsF = 258%nat -> ag32s bwsF baseF 258 ->
      FRAME m1 -> stk a0segs m1 lo (usp + -64) ->
      munch W3 m m1 -> wmono a0segs m m1 -> mem_inv a0segs m1 ->
      K3 ->
      evt a0segs Q
        (MS (mkR x1 (Z_to_bv 64 (usp + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9e248) fc None m1 (seg_rom a0segs)).
    Proof.
      intros until bwsF. intros ARL LENL AGL ARB LENB AGB FR ST MU WM MI HK3.
      pose proof sp_range as SPR.
      do 8 wstep. wstep.
      release_frame FR ST (bv_unsigned sp).
      replace (Z_to_bv 64 (usp + -64 + 64)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
      wstep.
      enter_with (HK3 _ lwsF bwsF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [ st_eq | exact ARL | exact LENL | exact AGL | exact ARB | exact LENB | exact AGB | exact ST | exact MU | exact WM | exact MI ].
    Qed.

    (* [comment removed for export] *)
    Lemma A0_hb_loopB : forall (k d : nat) (x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31 : word) m1 lwsF bwsc,
      let i := (minLen + 1 + Z.of_nat d)%Z in
      (Z.of_nat k = maxLen - i)%Z -> (i <= maxLen)%Z ->
      u32arr a0segs m1 LIM lwsF -> length lwsF = 258%nat -> ag32s lwsF limitF 258 ->
      u32arr a0segs m1 BASE bwsc -> length bwsc = 258%nat -> ag32s bwsc (hb_base limitF (minLen + 1) d base3) 258 ->
      FRAME m1 -> stk a0segs m1 lo (usp + -64) ->
      munch W3 m m1 -> wmono a0segs m m1 -> mem_inv a0segs m1 ->
      K3 ->
      evt a0segs Q
        (MS (mkR x1 (Z_to_bv 64 (usp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 (maxLen - i + 1)) (Z_to_bv 64 minLen)
                (Z_to_bv 64 (BASE + 4 * i)) (Z_to_bv 64 (LIM + 4 * (i - 1))) (Z_to_bv 64 (BASE + 4 * i)) x13 x14 x15 x16 x17
                (Z_to_bv 64 BASE) (Z_to_bv 64 (LIM + 4 * (i - 1))) x20 x21 cSB s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9e1d4) fc None m1 (seg_rom a0segs)).
    Proof.
      induction k as [|k IH]; intros d x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31 m1 lwsF bwsc i HK Hi
        ARL LENL AGL ARB LENB AGB FR ST MU WM MI HK3; subst i.
      all: pose proof sp_range as SPR.
      all: pose proof (u32arr_bound _ _ _ _ ARB) as BB; rewrite LENB in BB.
      all: pose proof (u32arr_bound _ _ _ _ ARL) as BL; rewrite LENL in BL.
      all: assert (Hi2 : (minLen + 1 + Z.of_nat d <= maxLen)%Z) by lia.
      all: pose proof (hbw_base_step len alpha minLen maxLen Halpha Hmm Hlen limit0 base0 d Hi2) as BF; cbn zeta in BF;
        cps_destruct BF as (BF1 & BF2 & BF3 & BF4).
      all: set (i := (minLen + 1 + Z.of_nat d)%Z) in *.
      all: destruct (nth_error_ok lwsF (i - 1) 258 LENL ltac:(lia)) as [wl NTHl];
        pose proof (AGL (i - 1)%Z ltac:(lia)) as VL; rewrite (sv32_nth _ _ _ NTHl) in VL; rewrite BF1 in VL.
      all: destruct (nth_error_ok bwsc i 258 LENB ltac:(lia)) as [wb NTHb];
        pose proof (AGB i ltac:(lia)) as VB; rewrite (sv32_nth _ _ _ NTHb) in VB; rewrite BF3 in VB.
      all: set (L := (first len alpha minLen (i - 1) + cnt_eq len alpha (i - 1))%Z) in *;
        set (C := cnt_lt len alpha i) in *.
      (* [comment removed for export] *)
      all: arun_to 0x9e1f0%Z.
      all: pose proof (u32arr_read a0segs m1 LIM lwsF (i - 1) wl _ ARL NTHl ltac:(lia) eq_refl) as RD1.
      all: wstep; clear RD1; cbv beta delta [sx32]; rewrite VL.
      all: arun_to 0x9e1fc%Z.
      all: pose proof (u32arr_read a0segs m1 BASE bwsc i wb _ ARB NTHb ltac:(lia) eq_refl) as RD2.
      all: wstep; clear RD2; cbv beta delta [sx32]; rewrite VB.
      (* [comment removed for export] *)
      all: wstep; wstep; wstep; wstep; wstep; wstep.
      all: pose proof (u32arr_store_ok a0segs m1 BASE bwsc i _ ARB ltac:(lia) eq_refl) as SO.
      all: wstep.
      all: u32_store_done ARB i; rename ARB into ARB'.
      (* [comment removed for export] *)
      all: wstep; wstep.
      - (* [comment removed for export] *)
        if_false_z.
        wstep.
        lazymatch type of ARB' with u32arr _ ?mm _ ?bw =>
          enter_with (A0_hb_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm lwsF bw);
            [ st_eq | exact ARL | exact LENL | exact AGL | exact ARB' | rewrite upd_length; exact LENB | | exact FR | exact ST | exact MU | exact WM | exact MI | exact HK3 ] end.
        unfold hbm_base. replace (span (minLen + 1) maxLen) with (S d) by (unfold span; lia).
        rewrite hb_base_snoc. cbn zeta. fold i.
        apply ag32s_upd_w; [exact AGB | lia | rewrite LENB; lia |].
        rewrite sv32_lit by lia. rewrite BF1, Z.shiftl_mul_pow2 by lia. lia.
      - if_true_z.
        lazymatch type of ARB' with u32arr _ ?mm _ ?bw =>
          enter_with (IH (S d) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm lwsF bw);
            [ st_eq | lia | lia | exact ARL | exact LENL | exact AGL | exact ARB' | rewrite upd_length; exact LENB | | exact FR | exact ST | exact MU | exact WM | exact MI | exact HK3 ] end.
        rewrite hb_base_snoc. cbn zeta. fold i.
        apply ag32s_upd_w; [exact AGB | lia | rewrite LENB; lia |].
        rewrite sv32_lit by lia. rewrite BF1, Z.shiftl_mul_pow2 by lia. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma A0_hb_loopL : forall (k d : nat) (x1 x5 x6 x7 x16 x17 x20 x21 x28 x29 x30 x31 : word) m1 lwsc bws3 (vec : Z),
      let i := (minLen + Z.of_nat d)%Z in
      (Z.of_nat k = maxLen - i)%Z -> (i <= maxLen)%Z ->
      vec = snd (hb_limit base3 minLen d limit1 0) ->
      u32arr a0segs m1 LIM lwsc -> length lwsc = 258%nat -> ag32s lwsc (fst (hb_limit base3 minLen d limit1 0)) 258 ->
      u32arr a0segs m1 BASE bws3 -> length bws3 = 258%nat -> ag32s bws3 base3 258 ->
      FRAME m1 -> stk a0segs m1 lo (usp + -64) ->
      munch W3 m m1 -> wmono a0segs m m1 -> mem_inv a0segs m1 ->
      K3 ->
      evt a0segs Q
        (MS (mkR x1 (Z_to_bv 64 (usp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 maxLen) (Z_to_bv 64 minLen)
                (Z_to_bv 64 (LIM + 4 * i)) (Z_to_bv 64 (BASE + 4 * i)) (Z_to_bv 64 vec) (Z_to_bv 64 (LIM + 4 * i))
                (Z_to_bv 64 (BASE + 4 * (i + 1))) (Z_to_bv 64 (maxLen - i + 1)) x16 x17
                (Z_to_bv 64 BASE) (Z_to_bv 64 LIM) x20 x21 cSB s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9e290) fc None m1 (seg_rom a0segs)).
    Proof.
      induction k as [|k IH]; intros d x1 x5 x6 x7 x16 x17 x20 x21 x28 x29 x30 x31 m1 lwsc bws3 vec i HK Hi Hvec
        ARL LENL AGL ARB LENB AGB FR ST MU WM MI HK3; subst i.
      all: pose proof sp_range as SPR.
      all: pose proof (u32arr_bound _ _ _ _ ARB) as BB; rewrite LENB in BB.
      all: pose proof (u32arr_bound _ _ _ _ ARL) as BL; rewrite LENL in BL.
      all: pose proof (hbw_limit_step len alpha minLen maxLen Halpha Hmm Hlen limit0 base0 d ltac:(lia)) as LF; cbn zeta in LF;
        rewrite <- Hvec in LF; cps_destruct LF as (LF1 & LF2 & LF3 & LF4 & LF5 & LF6 & LF7 & LF8 & LF9).
      all: set (i := (minLen + Z.of_nat d)%Z) in *.
      all: set (V := first len alpha minLen i) in *;
        set (C0 := cnt_lt len alpha i) in *; set (C1 := cnt_lt len alpha (i + 1)) in *; set (E := cnt_eq len alpha i) in *.
      all: destruct (nth_error_ok bws3 i 258 LENB ltac:(lia)) as [w1 NTH1];
        pose proof (AGB i ltac:(lia)) as V1; rewrite (sv32_nth _ _ _ NTH1) in V1; rewrite LF3 in V1.
      all: destruct (nth_error_ok bws3 (i + 1) 258 LENB ltac:(lia)) as [w2 NTH2];
        pose proof (AGB (i + 1)%Z ltac:(lia)) as V2; rewrite (sv32_nth _ _ _ NTH2) in V2; rewrite LF4 in V2.
      (* [comment removed for export] *)
      all: arun_to 0x9e2b0%Z.
      all: pose proof (u32arr_read a0segs m1 BASE bws3 (i + 1) w2 _ ARB NTH2 ltac:(lia) eq_refl) as RD2.
      all: wstep; clear RD2; cbv beta delta [sx32]; rewrite V2.
      (* [comment removed for export] *)
      all: arun_to 0x9e2c4%Z.
      all: pose proof (u32arr_read a0segs m1 BASE bws3 i w1 _ ARB NTH1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD1.
      all: wstep; clear RD1; cbv beta delta [sx32]; rewrite V1.
      (* [comment removed for export] *)
      all: arun_to 0x9e2e8%Z.
      all: pose proof (u32arr_store_ok a0segs m1 LIM lwsc i _ ARL ltac:(lia) eq_refl) as SO.
      all: wstep.
      all: u32_store_done ARL i; rename ARL into ARL'.
      (* [comment removed for export] *)
      all: wstep; wstep; wstep.
      all: assert (AGL' : ag32s (upd lwsc (Z.to_nat i) (Z_to_bv 64 (C1 - C0 + vec + -1))) (fst (hb_limit base3 minLen (S d) limit1 0)) 258)
        by (rewrite hb_limit_snoc; cbn zeta; cbn [fst snd]; fold i;
            apply ag32s_upd_w; [exact AGL | lia | rewrite LENL; lia |];
            rewrite sv32_lit by lia; rewrite <- Hvec, LF4, LF3; lia).
      - (* [comment removed for export] *)
        if_false_z. wstep. wstep. if_cases K; zify_cond K; bz32_in K.
        + (* [comment removed for export] *)
          enter_with (A0_hb_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bws3);
            [ st_eq | exact ARL' | rewrite upd_length; exact LENL | | exact ARB | exact LENB | | exact FR | exact ST | exact MU | exact WM | exact MI | exact HK3 ].
          * unfold hbm_limit, hbm_lv. replace (span minLen maxLen) with (S d) by (unfold span; lia). exact AGL'.
          * unfold hbm_base. replace (span (minLen + 1) maxLen) with 0%nat by (unfold span; lia). cbn [hb_base]. exact AGB.
        + (* [comment removed for export] *)
          wstep. wstep. wstep. wstep. wstep. wstep. wstep.
          enter_with (A0_hb_loopB (Z.to_nat (maxLen - minLen - 1)) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bws3);
            [ st_eq | lia | lia | exact ARL' | rewrite upd_length; exact LENL | | exact ARB | exact LENB | | exact FR | exact ST | exact MU | exact WM | exact MI | exact HK3 ].
          * unfold hbm_limit, hbm_lv. replace (span minLen maxLen) with (S d) by (unfold span; lia). exact AGL'.
          * cbn [hb_base]. exact AGB.
      - (* [comment removed for export] *)
        if_true_z.
        enter_with (IH (S d) _ _ _ _ _ _ _ _ _ _ _ _ _ _ bws3 ((C1 - C0 + vec) * 2)%Z);
          [ st_eq | lia | lia | | exact ARL' | rewrite upd_length; exact LENL | exact AGL' | exact ARB | exact LENB | exact AGB
          | exact FR | exact ST | exact MU | exact WM | exact MI | exact HK3 ].
        rewrite hb_limit_snoc. cbn zeta. cbn [fst snd]. fold i. rewrite <- Hvec, LF4, LF3, Z.shiftl_mul_pow2 by lia. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma A0_hbc_seg3 : forall (lws1 bws3 : list word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 t3 t4 t5 t6 : word),
      u32arr a0segs m LIM lws1 -> length lws1 = 258%nat -> ag32s lws1 limit1 258 ->
      u32arr a0segs m BASE bws3 -> length bws3 = 258%nat -> ag32s bws3 base3 258 ->
      FRAME m -> stk a0segs m lo (usp + -64) -> mem_inv a0segs m ->
      K3 ->
      evt a0segs Q
        (MS (mkR x1 (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 maxLen) (Z_to_bv 64 minLen) a0 a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 BASE) (Z_to_bv 64 LIM) x20 x21 cSB s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9e1b0) fc None m (seg_rom a0segs)).
    Proof.
      intros until t6. intros ARL LENL AGL ARB LENB AGB FR ST MI HK3.
      pose proof sp_range as SPR.
      pose proof (munch_refl W3 m) as MU. pose proof (wmono_refl a0segs m) as WM.
      (* [comment removed for export] *)
      wstep. if_true_z. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
      enter_with (A0_hb_loopL (Z.to_nat (maxLen - minLen)) 0 _ _ _ _ _ _ _ _ _ _ _ _ m lws1 bws3 0);
        [ st_eq | lia | lia | reflexivity | exact ARL | exact LENL | exact AGL | exact ARB | exact LENB | exact AGB
        | exact FR | exact ST | exact MU | exact WM | exact MI | exact HK3 ].
    Qed.
  End S3.
End P.
End ACeilS1.
