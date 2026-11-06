(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzLemmasHb BzHbW BzTac BzTac2 CmpCut AsanKit AsanCut AsanCutB0 AsanKitB0 B0F_leafCut.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section P.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : word -> option byte).
  Variables (DS t : Z) (lws bws pws : list word) (lbs : list byte) (minLen maxLen alpha lo : Z).
  Hypothesis LENl : length lws = 258%nat.
  Hypothesis LENb : length bws = 258%nat.
  Hypothesis LENp : length pws = 258%nat.
  Hypothesis LEN8 : length lbs = 258%nat.
  Hypothesis HS : (0 < DS)%Z /\ (DS mod 16 = 0)%Z /\ (0 <= t < 6)%Z.
  Hypothesis DSH : (DS + 64144 <= 18446744073709551616)%Z.
  Hypothesis SPd : (bv_unsigned sp <= DS \/ DS + 64144 <= bv_unsigned sp - 48)%Z.
  Hypothesis HLO : (lo + 48 <= bv_unsigned sp)%Z.
  Hypothesis Halpha : (1 <= alpha <= 258)%Z.
  Hypothesis Hmm : (1 <= minLen /\ minLen <= maxLen <= 20)%Z.
  Hypothesis Hlen : forall j, (0 <= j < alpha)%Z -> (minLen <= uv8 lbs j <= maxLen)%Z.
  Hypothesis Himg : (0x62b000 <= lo)%Z. Hypothesis HimgD : (0x62b000 <= DS)%Z.

  Notation usp := (bv_unsigned sp).
  Notation LIM := (DS + 45436 + 1032 * t)%Z.
  Notation BASE := (DS + 51628 + 1032 * t)%Z.
  Notation PERM := (DS + 57820 + 1032 * t)%Z.
  Notation LEN := (DS + 43888 + 258 * t)%Z.
  Notation limit0 := (sv32 lws). Notation base0 := (sv32 bws). Notation perm0 := (sv32 pws). Notation len := (uv8 lbs).
  Notation W := ([(LIM, LIM + 1032); (BASE, BASE + 1032); (PERM, PERM + 1032); (usp - 48, usp)])%Z.
  Hypothesis SHd : shzW b0segs W m DS (DS + 64144).
  Notation POST := (hbCreateDecodeTables_apostF 48 b0segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DS t lws bws pws lbs minLen maxLen alpha lo m).
  Notation base3 := (hbm_base3 len alpha base0).
  Notation limit1 := (hbm_limit1 limit0).
  Notation limitF := (hbm_limit len alpha minLen maxLen limit0 base0).
  Notation baseF := (hbm_base len alpha minLen maxLen limit0 base0).
  Notation permF := (hbm_perm len alpha minLen maxLen perm0).
  Notation base1 := (hbm_base1 base0).
  Notation base2 := (hbm_base2 len alpha base0).
  (* [comment removed for export] *)
  Notation FRAME mm := (rw_cells b0segs mm (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation cSP := (Z_to_bv 64 (usp + -48)). Notation cSB := (Z_to_bv 64 2147450880).

  Lemma sp_range : (0 <= usp < 2^64)%Z.
  Proof. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R. lia. Qed.
  Lemma ds_al4 : (DS mod 4 = 0)%Z.
  Proof. destruct HS as (_ & A16 & _). clear - A16. Z.div_mod_to_equations; lia. Qed.

  (* [comment removed for export] *)
  Lemma B0_hb_loopB : forall (k d : nat) (x5 x7 x8 x9 x12 x13 x14 x17 x18 x19 x20 x28 x29 x30 x31 : word) m1 lwsF bwsc pwsF,
    let i := (minLen + 1 + Z.of_nat d)%Z in
    (Z.of_nat k = maxLen + 1 - i)%Z \/ (maxLen < i /\ k = 0%nat)%Z ->
    (i <= maxLen + 1)%Z ->
    u32arr b0segs m1 LIM lwsF -> length lwsF = 258%nat -> ag32s lwsF limitF 258 ->
    u32arr b0segs m1 BASE bwsc -> length bwsc = 258%nat ->
    ag32s bwsc (hb_base limitF (minLen + 1) d base3) 258 ->
    u32arr b0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr b0segs m1 LEN lbs -> FRAME m1 -> stk b0segs m1 lo (usp + -48) ->
    munch W m m1 -> wmono b0segs m m1 -> mem_inv b0segs m1 ->
    evt b0segs POST
      (MS (mkR ra cSP gp tp x5 cSB x7 x8 x9 (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) x12 x13 x14 (Z_to_bv 64 maxLen) (Z_to_bv 64 i) x17
              x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9200) fc None m1 (seg_rom b0segs)).
  Proof.
    induction k as [|k IH]; intros d x5 x7 x8 x9 x12 x13 x14 x17 x18 x19 x20 x28 x29 x30 x31 m1 lwsF bwsc pwsF i HK Hi
      ARL LENL AGL ARB LENB AGB ARP LENP AGP AR8 FR ST MU WM MI; subst i.
    - (* [comment removed for export] *)
      assert (HX : (maxLen < minLen + 1 + Z.of_nat d)%Z) by lia.
      pose proof sp_range as SPR.
      wstep. if_true_z.
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep. wstep. wstep.
      release_frame FR ST (bv_unsigned sp).
      replace (Z_to_bv 64 (usp + -48 + 48)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
      wstep.
      unfold hbCreateDecodeTables_apostF, hbCreate_W. rewrite hb_create_pieces by assumption.
      finish; [exact ARL | exact LENL | exact ARB | exact LENB | exact ARP | exact LENP | exact AGL | | exact AGP].
      unfold hbm_base. replace (span (minLen + 1) maxLen) with d by (unfold span; lia). exact AGB.
    - (* [comment removed for export] *)
      assert (Hi2 : (minLen + 1 + Z.of_nat d <= maxLen)%Z) by lia.
      pose proof sp_range as SPR. pose proof ds_al4 as AL4.
      pose proof (hbw_base_step len alpha minLen maxLen Halpha Hmm Hlen limit0 base0 d Hi2) as BF. cbn zeta in BF.
      cps_destruct BF as (BF1 & BF2 & BF3 & BF4).
      set (i := (minLen + 1 + Z.of_nat d)%Z) in *.
      pose proof (u32arr_bound _ _ _ _ ARL) as BL. rewrite LENL in BL.
      pose proof (u32arr_bound _ _ _ _ ARB) as BB. rewrite LENB in BB.
      (* [comment removed for export] *)
      wstep. if_false_z.
      brun_to 0xa9240%Z.
      destruct (nth_error_ok lwsF (i - 1) 258 LENL ltac:(lia)) as [wl NTHl].
      pose proof (u32arr_read b0segs m1 LIM lwsF (i - 1) wl _ ARL NTHl ltac:(lia) eq_refl) as RD.
      wstep. clear RD.
      pose proof (AGL (i - 1)%Z ltac:(lia)) as VL. rewrite (sv32_nth _ _ _ NTHl) in VL. rewrite BF1 in VL.
      cbv beta delta [sx32]. rewrite VL.
      set (L := (first len alpha minLen (i - 1) + cnt_eq len alpha (i - 1))%Z) in *.
      (* [comment removed for export] *)
      brun_to 0xa9284%Z.
      destruct (nth_error_ok bwsc i 258 LENB ltac:(lia)) as [wb NTHb].
      pose proof (u32arr_read b0segs m1 BASE bwsc i wb _ ARB NTHb ltac:(lia) eq_refl) as RD.
      wstep. clear RD.
      pose proof (AGB i ltac:(lia)) as VB. rewrite (sv32_nth _ _ _ NTHb) in VB. rewrite BF3 in VB.
      cbv beta delta [sx32]. rewrite VB.
      set (C := cnt_lt len alpha i) in *.
      (* [comment removed for export] *)
      brun_to 0xa92a4%Z.
      pose proof (u32arr_store_ok b0segs m1 BASE bwsc i _ ARB ltac:(lia) eq_refl) as SO.
      wstep.
      pose proof (u32arr_write b0segs m1 BASE bwsc i (Z_to_bv 64 ((L - 1 + 1) * 2 - C)) ARB ltac:(lia)) as ARB'.
      clear ARB. store_done.
      (* [comment removed for export] *)
      brun_to 0xa9200%Z.
      replace (Z_to_bv 64 (i + 1)) with (Z_to_bv 64 (minLen + 1 + Z.of_nat (S d))) by (f_equal; lia).
      eapply (IH (S d));
        [ lia | lia | exact ARL | exact LENL | exact AGL | exact ARB' | | | exact ARP | exact LENP | exact AGP
        | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      + rewrite upd_length. exact LENB.
      + rewrite hb_base_snoc. cbn zeta. fold i.
        apply ag32s_upd_w; [exact AGB | lia | rewrite LENB; lia |].
        rewrite sv32_lit by lia. rewrite BF1, Z.shiftl_mul_pow2 by lia. subst C. lia.
  Qed.

  Notation STL pc i vec x8 x9 x16 x18 x19 x20 x30 x31 mm :=
      (MS (mkR ra cSP gp tp (Z_to_bv 64 (LIM + 4 * i)) cSB (Z_to_bv 64 i) x8 x9
              (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) (Z_to_bv 64 (LIM + 4 * i)) (Z_to_bv 64 (BASE + 4 * i))
              (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) x16 (Z_to_bv 64 (BASE + 4 * i))
              x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 i) (Z_to_bv 64 vec) x30 x31)
          F (Z_to_bv 64 pc) fc None mm (seg_rom b0segs)).

  (* [comment removed for export] *)
  Lemma B0_hb_bodyL : forall (d : nat) (x8 x9 x16 x18 x19 x20 x30 x31 : word) m1 lwsc bws3 pwsF (vec : Z) (Q : machine_state -> Prop),
    let i := (minLen + Z.of_nat d)%Z in
    (i <= maxLen)%Z ->
    vec = snd (hb_limit base3 minLen d limit1 0) ->
    u32arr b0segs m1 LIM lwsc -> length lwsc = 258%nat -> ag32s lwsc (fst (hb_limit base3 minLen d limit1 0)) 258 ->
    u32arr b0segs m1 BASE bws3 -> length bws3 = 258%nat -> ag32s bws3 base3 258 ->
    u32arr b0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr b0segs m1 LEN lbs -> FRAME m1 -> stk b0segs m1 lo (usp + -48) ->
    munch W m m1 -> wmono b0segs m m1 -> mem_inv b0segs m1 ->
    (forall (y8 y16 y30 y31 : word) m2 lwsc' (vec' : Z),
       vec' = snd (hb_limit base3 minLen (S d) limit1 0) ->
       u32arr b0segs m2 LIM lwsc' -> length lwsc' = 258%nat -> ag32s lwsc' (fst (hb_limit base3 minLen (S d) limit1 0)) 258 ->
       u32arr b0segs m2 BASE bws3 -> u32arr b0segs m2 PERM pwsF -> u8arr b0segs m2 LEN lbs -> FRAME m2 ->
       stk b0segs m2 lo (usp + -48) -> munch W m m2 -> wmono b0segs m m2 -> mem_inv b0segs m2 ->
       evt b0segs Q (STL 0xa9400 (i + 1) vec' y8 x9 y16 x18 x19 x20 y30 y31 m2)) ->
    evt b0segs Q (STL 0xa9324 i vec x8 x9 x16 x18 x19 x20 x30 x31 m1).
  Proof.
    intros d x8 x9 x16 x18 x19 x20 x30 x31 m1 lwsc bws3 pwsF vec Q i Hi Hvec
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
    (* [comment removed for export] *)
    brun_to 0xa9384%Z.
    destruct (nth_error_ok bws3 (i + 1) 258 LENB ltac:(lia)) as [w1 NTH1].
    pose proof (u32arr_read b0segs m1 BASE bws3 (i + 1) w1 _ ARB NTH1 ltac:(lia) eq_refl) as RD.
    wstep. clear RD.
    pose proof (AGB (i + 1)%Z ltac:(lia)) as V1. rewrite (sv32_nth _ _ _ NTH1) in V1. rewrite LF4 in V1.
    cbv beta delta [sx32]. rewrite V1.
    brun_to 0xa938c%Z.
    destruct (nth_error_ok bws3 i 258 LENB ltac:(lia)) as [w2 NTH2].
    pose proof (u32arr_read b0segs m1 BASE bws3 i w2 _ ARB NTH2 ltac:(lia) eq_refl) as RD.
    wstep. clear RD.
    pose proof (AGB i ltac:(lia)) as V2. rewrite (sv32_nth _ _ _ NTH2) in V2. rewrite LF3 in V2.
    cbv beta delta [sx32]. rewrite V2.
    brun_to 0xa93e0%Z.
    pose proof (u32arr_store_ok b0segs m1 LIM lwsc i _ ARL ltac:(lia) eq_refl) as SO.
    wstep.
    pose proof (u32arr_write b0segs m1 LIM lwsc i (Z_to_bv 64 (vec + (C1 - C0) + -1)) ARL ltac:(lia)) as ARL'.
    clear ARL. store_done.
    (* [comment removed for export] *)
    brun_to 0xa9400%Z.
    replace (BASE + 4 * i + 4)%Z with (BASE + 4 * (i + 1))%Z by lia.
    replace (LIM + 4 * i + 4)%Z with (LIM + 4 * (i + 1))%Z by lia.
    eapply evt_eq; [| eapply (HQ _ _ _ _ _ (upd lwsc (Z.to_nat i) (Z_to_bv 64 (vec + (C1 - C0) + -1))) ((vec + (C1 - C0)) * 2)%Z) ];
      [ st_eq | | exact ARL' | rewrite upd_length; exact LENL | | exact ARB | exact ARP | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
    - rewrite hb_limit_snoc. cbn zeta. cbn [fst snd]. fold i. rewrite <- Hvec, LF4, LF3, Z.shiftl_mul_pow2 by lia. lia.
    - rewrite hb_limit_snoc. cbn zeta. cbn [fst snd]. fold i.
      apply ag32s_upd_w; [exact AGL | lia | rewrite LENL; lia |].
      rewrite sv32_lit by lia. rewrite <- Hvec, LF4, LF3. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_hb_loopL : forall (k d : nat) (x8 x9 x16 x18 x19 x20 x30 x31 : word) m1 lwsc bws3 pwsF (vec : Z),
    let i := (minLen + Z.of_nat d)%Z in
    (Z.of_nat k = maxLen - i)%Z -> (i <= maxLen)%Z ->
    vec = snd (hb_limit base3 minLen d limit1 0) ->
    u32arr b0segs m1 LIM lwsc -> length lwsc = 258%nat -> ag32s lwsc (fst (hb_limit base3 minLen d limit1 0)) 258 ->
    u32arr b0segs m1 BASE bws3 -> length bws3 = 258%nat -> ag32s bws3 base3 258 ->
    u32arr b0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr b0segs m1 LEN lbs -> FRAME m1 -> stk b0segs m1 lo (usp + -48) ->
    munch W m m1 -> wmono b0segs m m1 -> mem_inv b0segs m1 ->
    evt b0segs POST (STL 0xa9324 i vec x8 x9 x16 x18 x19 x20 x30 x31 m1).
  Proof.
    induction k as [|k IH]; intros d x8 x9 x16 x18 x19 x20 x30 x31 m1 lwsc bws3 pwsF vec i HK Hi Hvec
      ARL LENL AGL ARB LENB AGB ARP LENP AGP AR8 FR ST MU WM MI; subst i;
      pose proof sp_range as SPR;
      (eapply B0_hb_bodyL;
       [ exact Hi | exact Hvec | exact ARL | exact LENL | exact AGL | exact ARB | exact LENB | exact AGB
       | exact ARP | exact LENP | exact AGP | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI | ]);
      clear ARL LENL AGL ARB ARP AR8 FR ST MU WM MI;
      intros y8 y16 y30 y31 m2 lwsc' vec' Hvec' ARL LENL' AGL' ARB ARP AR8 FR ST MU WM MI.
    - (* [comment removed for export] *)
      wstep. if_true_z. brun_to 0xa9200%Z.
      replace (Z_to_bv 64 (minLen + 1)) with (Z_to_bv 64 (minLen + 1 + Z.of_nat 0)) by (f_equal; lia).
      eapply (B0_hb_loopB (Z.to_nat (maxLen - minLen)) 0);
        [ lia | lia | exact ARL | exact LENL' | | exact ARB | exact LENB | | exact ARP | exact LENP | exact AGP
        | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      + unfold hbm_limit, hbm_lv. replace (span minLen maxLen) with (S d) by (unfold span; lia). exact AGL'.
      + cbn [hb_base]. exact AGB.
    - (* [comment removed for export] *)
      wstep. if_false_z. wstep.
      replace (minLen + Z.of_nat d + 1)%Z with (minLen + Z.of_nat (S d))%Z by lia.
      eapply (IH (S d));
        [ lia | lia | exact Hvec' | exact ARL | exact LENL' | exact AGL' | exact ARB | exact LENB | exact AGB
        | exact ARP | exact LENP | exact AGP | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_hb_partC : forall (x5 x7 x8 x9 x12 x13 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word) m1 lws1 bws3 pwsF,
    u32arr b0segs m1 LIM lws1 -> length lws1 = 258%nat -> ag32s lws1 limit1 258 ->
    u32arr b0segs m1 BASE bws3 -> length bws3 = 258%nat -> ag32s bws3 base3 258 ->
    u32arr b0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr b0segs m1 LEN lbs -> FRAME m1 -> stk b0segs m1 lo (usp + -48) ->
    munch W m m1 -> wmono b0segs m m1 -> mem_inv b0segs m1 ->
    evt b0segs POST
      (MS (mkR ra cSP gp tp x5 cSB x7 x8 x9 (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) x12 x13
              (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xa91f4) fc None m1 (seg_rom b0segs)).
  Proof.
    intros x5 x7 x8 x9 x12 x13 x16 x17 x18 x19 x20 x28 x29 x30 x31 m1 lws1 bws3 pwsF
      ARL LENL AGL ARB LENB AGB ARP LENP AGP AR8 FR ST MU WM MI.
    pose proof sp_range as SPR.
    (* [comment removed for export] *)
    wstep. if_true_z. brun_to 0xa9324%Z.
    enter_with (B0_hb_loopL (Z.to_nat (maxLen - minLen)) 0 x8 x9 _ x18 x19 x20 _ _ m1 lws1 bws3 pwsF 0);
      [ st_eq | lia | lia | reflexivity | exact ARL | exact LENL | exact AGL | exact ARB | exact LENB | exact AGB
      | exact ARP | exact LENP | exact AGP | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_hb_loopZ2 : forall (k : nat) (j : Z) (x7 x8 x9 x18 x19 x20 x28 x29 x30 x31 : word) m1 lwsc bws3 pwsF,
    (Z.of_nat k = 23 - j)%Z -> (0 <= j < 23)%Z ->
    u32arr b0segs m1 LIM lwsc -> length lwsc = 258%nat -> ag32s lwsc (fill0 limit0 0 (Z.to_nat j)) 258 ->
    u32arr b0segs m1 BASE bws3 -> length bws3 = 258%nat -> ag32s bws3 base3 258 ->
    u32arr b0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr b0segs m1 LEN lbs -> FRAME m1 -> stk b0segs m1 lo (usp + -48) ->
    munch W m m1 -> wmono b0segs m m1 -> mem_inv b0segs m1 ->
    evt b0segs POST
      (MS (mkR ra cSP gp tp (Z_to_bv 64 (LIM + 4 * j)) cSB x7 x8 x9
              (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) (Z_to_bv 64 (LIM + 4 * j)) (Z_to_bv 64 1) (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen)
              (Z_to_bv 64 1) (Z_to_bv 64 (23 - j)) x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xa91a4) fc None m1 (seg_rom b0segs)).
  Proof.
    induction k as [|k IH]; intros j x7 x8 x9 x18 x19 x20 x28 x29 x30 x31 m1 lwsc bws3 pwsF HK Hj
      ARL LENL AGL ARB LENB AGB ARP LENP AGP AR8 FR ST MU WM MI; [lia|].
    pose proof sp_range as SPR. pose proof ds_al4 as AL4.
    pose proof (u32arr_bound _ _ _ _ ARL) as BL. rewrite LENL in BL.
    (* [comment removed for export] *)
    brun_to 0xa91c8%Z.
    pose proof (u32arr_store_ok b0segs m1 LIM lwsc j _ ARL ltac:(lia) eq_refl) as SO.
    wstep.
    pose proof (u32arr_write b0segs m1 LIM lwsc j (Z_to_bv 64 0) ARL ltac:(lia)) as ARL'.
    clear ARL. store_done.
    brun. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      enter_with (IH (j + 1)%Z _ _ _ _ _ _ _ _ _ _ _ (upd lwsc (Z.to_nat j) (Z_to_bv 64 0)) bws3 pwsF);
        [ st_eq | lia | lia | exact ARL' | rewrite upd_length; exact LENL | | exact ARB | exact LENB | exact AGB
        | exact ARP | exact LENP | exact AGP | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. rewrite fill0_snoc.
      replace (0 + Z.of_nat (Z.to_nat j))%Z with j by lia.
      apply ag32s_upd; [exact AGL | lia | rewrite LENL; lia | lia].
    - (* [comment removed for export] *)
      wstep.
      enter_with (B0_hb_partC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (upd lwsc (Z.to_nat j) (Z_to_bv 64 0)) bws3 pwsF);
        [ st_eq | exact ARL' | rewrite upd_length; exact LENL | | exact ARB | exact LENB | exact AGB
        | exact ARP | exact LENP | exact AGP | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      unfold hbm_limit1. replace 23%nat with (S (Z.to_nat j)) by lia. rewrite fill0_snoc.
      replace (0 + Z.of_nat (Z.to_nat j))%Z with j by lia.
      apply ag32s_upd; [exact AGL | lia | rewrite LENL; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_hb_loopA : forall (k mI : nat) (x7 x8 x9 x18 x19 x20 x28 x29 x30 x31 : word) m1 bwsc pwsF,
    let i := (1 + Z.of_nat mI)%Z in
    (Z.of_nat k = 23 - i)%Z -> (1 <= i <= 22)%Z ->
    u32arr b0segs m1 LIM lws ->
    u32arr b0segs m1 BASE bwsc -> length bwsc = 258%nat -> ag32s bwsc (hb_accum 1 mI base2) 258 ->
    u32arr b0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr b0segs m1 LEN lbs -> FRAME m1 -> stk b0segs m1 lo (usp + -48) ->
    munch W m m1 -> wmono b0segs m m1 -> mem_inv b0segs m1 ->
    evt b0segs POST
      (MS (mkR ra cSP gp tp (Z_to_bv 64 (18446744073709551615 - BASE)) cSB x7 x8 x9
              (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) (Z_to_bv 64 (BASE + 4 * (i - 1))) (Z_to_bv 64 (BASE + 4 * i))
              (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 (4 * i)) (Z_to_bv 64 92) x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xa90f8) fc None m1 (seg_rom b0segs)).
  Proof.
    induction k as [|k IH]; intros mI x7 x8 x9 x18 x19 x20 x28 x29 x30 x31 m1 bwsc pwsF i HK Hi
      ARL ARB LENB AGB ARP LENP AGP AR8 FR ST MU WM MI; subst i; [lia|].
    pose proof sp_range as SPR. pose proof ds_al4 as AL4.
    pose proof (u32arr_bound _ _ _ _ ARB) as BB. rewrite LENB in BB.
    pose proof (hbw_accum_step len alpha minLen maxLen Halpha Hmm Hlen base0 (Z.of_nat mI) ltac:(lia)) as AF. cbn zeta in AF.
    rewrite Nat2Z.id in AF. cps_destruct AF as (AF1 & AF2 & AF3).
    set (i := (1 + Z.of_nat mI)%Z) in *.
    (* [comment removed for export] *)
    brun_to 0xa911c%Z.
    destruct (nth_error_ok bwsc (i - 1) 258 LENB ltac:(lia)) as [w1 NTH1].
    pose proof (u32arr_read b0segs m1 BASE bwsc (i - 1) w1 _ ARB NTH1 ltac:(lia) eq_refl) as RD.
    wstep. clear RD.
    pose proof (AGB (i - 1)%Z ltac:(lia)) as V1. rewrite (sv32_nth _ _ _ NTH1) in V1.
    brun_to 0xa9124%Z.
    destruct (nth_error_ok bwsc i 258 LENB ltac:(lia)) as [w2 NTH2].
    pose proof (u32arr_read b0segs m1 BASE bwsc i w2 _ ARB NTH2 ltac:(lia) eq_refl) as RD.
    wstep. clear RD.
    pose proof (AGB i ltac:(lia)) as V2. rewrite (sv32_nth _ _ _ NTH2) in V2.
    cbv beta delta [sx32]. rewrite V1, V2.
    set (P1 := hb_accum 1 mI base2 (i - 1)) in *. set (P2 := hb_accum 1 mI base2 i) in *.
    (* [comment removed for export] *)
    brun_to 0xa913c%Z.
    pose proof (u32arr_store_ok b0segs m1 BASE bwsc i _ ARB ltac:(lia) eq_refl) as SO.
    wstep.
    pose proof (u32arr_write b0segs m1 BASE bwsc i (Z_to_bv 64 (P2 + P1)) ARB ltac:(lia)) as ARB'.
    clear ARB. store_done.
    brun. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      enter_with (IH (S mI) _ _ _ _ _ _ _ _ _ _ _ (upd bwsc (Z.to_nat i) (Z_to_bv 64 (P2 + P1))) pwsF);
        [ st_eq | lia | lia | exact ARL | exact ARB' | rewrite upd_length; exact LENB | | exact ARP | exact LENP | exact AGP
        | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      rewrite hb_accum_snoc. cbn zeta. fold i. replace (1 + Z.of_nat mI)%Z with i by lia.
      apply ag32s_upd; [exact AGB | lia | rewrite LENB; lia | lia].
    - (* [comment removed for export] *)
      pose proof (u32arr_bound _ _ _ _ ARL) as BL. rewrite LENl in BL.
      brun_to 0xa91a4%Z.
      enter_with (B0_hb_loopZ2 23 0 _ _ _ _ _ _ _ _ _ _ _ lws (upd bwsc (Z.to_nat i) (Z_to_bv 64 (P2 + P1))) pwsF);
        [ st_eq | lia | lia | exact ARL | exact LENl | | exact ARB' | rewrite upd_length; exact LENB | | exact ARP | exact LENP | exact AGP
        | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      + cbn [fill0 Z.to_nat]. apply ag32s_refl.
      + unfold hbm_base3. replace 22%nat with (S mI) by lia. rewrite hb_accum_snoc. cbn zeta.
        replace (1 + Z.of_nat mI)%Z with i by lia.
        apply ag32s_upd; [exact AGB | lia | rewrite LENB; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_hb_loopC : forall (k : nat) (j : Z) (x17 x8 x9 x18 x19 x20 x29 x30 x31 : word) m1 bwsc pwsF,
    (Z.of_nat k = alpha - j)%Z -> (0 <= j < alpha)%Z ->
    u32arr b0segs m1 LIM lws ->
    u32arr b0segs m1 BASE bwsc -> length bwsc = 258%nat -> ag32s bwsc (hb_count len 0 (Z.to_nat j) base1) 258 ->
    u32arr b0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr b0segs m1 LEN lbs -> FRAME m1 -> stk b0segs m1 lo (usp + -48) ->
    munch W m m1 -> wmono b0segs m m1 -> mem_inv b0segs m1 ->
    evt b0segs POST
      (MS (mkR ra cSP gp tp (Z_to_bv 64 (18446744073709551615 - BASE)) cSB (Z_to_bv 64 1) x8 x9
              (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) (Z_to_bv 64 (LEN + j)) (Z_to_bv 64 LEN)
              (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 (alpha - j)) x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11
              (Z_to_bv 64 (LEN + j)) x29 x30 x31)
          F (Z_to_bv 64 0xa9044) fc None m1 (seg_rom b0segs)).
  Proof.
    induction k as [|k IH]; intros j x17 x8 x9 x18 x19 x20 x29 x30 x31 m1 bwsc pwsF HK Hj
      ARL ARB LENB AGB ARP LENP AGP AR8 FR ST MU WM MI; [lia|].
    pose proof sp_range as SPR. pose proof ds_al4 as AL4.
    pose proof (u32arr_bound _ _ _ _ ARB) as BB. rewrite LENB in BB.
    pose proof (u8arr_bound _ _ _ _ AR8) as B8. rewrite LEN8 in B8.
    pose proof (hbw_count_step len alpha minLen maxLen Halpha Hmm Hlen base0 j ltac:(lia)) as CF. cbn zeta in CF.
    destruct CF as [CF1 CF2].
    (* [comment removed for export] *)
    brun_to 0xa9068%Z.
    destruct (nth_error_ok lbs j 258 LEN8 ltac:(lia)) as [b NTH].
    pose proof (u8arr_read b0segs m1 LEN lbs j b _ AR8 NTH ltac:(lia) eq_refl) as RD.
    wstep. clear RD.
    pose proof (uv8_nth _ _ _ NTH) as VB. (* [comment removed for export] *)
    cbv beta delta [zxb]. rewrite <- VB.
    set (q := (uv8 lbs j + 1)%Z) in *.
    pose proof (Hlen j ltac:(lia)) as LJ.
    (* [comment removed for export] *)
    brun_to 0xa908c%Z.
    destruct (nth_error_ok bwsc q 258 LENB ltac:(lia)) as [w NTHw].
    pose proof (u32arr_read b0segs m1 BASE bwsc q w _ ARB NTHw ltac:(lia) eq_refl) as RD.
    wstep. clear RD.
    pose proof (AGB q ltac:(lia)) as V1. rewrite (sv32_nth _ _ _ NTHw) in V1.
    cbv beta delta [sx32]. rewrite V1.
    set (P := hb_count len 0 (Z.to_nat j) base1 q) in *.
    (* [comment removed for export] *)
    brun_to 0xa90a0%Z.
    pose proof (u32arr_store_ok b0segs m1 BASE bwsc q _ ARB ltac:(lia) eq_refl) as SO.
    wstep.
    pose proof (u32arr_write b0segs m1 BASE bwsc q (Z_to_bv 64 (P + 1)) ARB ltac:(lia)) as ARB'.
    clear ARB. store_done.
    (* [comment removed for export] *)
    brun. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      brun_to 0xa90f8%Z.
      enter_with (B0_hb_loopA 22 0 _ _ _ _ _ _ _ _ _ _ _ (upd bwsc (Z.to_nat q) (Z_to_bv 64 (P + 1))) pwsF);
        [ st_eq | lia | lia | exact ARL | exact ARB' | rewrite upd_length; exact LENB | | exact ARP | exact LENP | exact AGP
        | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      cbn [hb_accum]. unfold hbm_base2. replace (Z.to_nat alpha) with (S (Z.to_nat j)) by lia.
      rewrite hb_count_snoc. cbn zeta. replace (0 + Z.of_nat (Z.to_nat j))%Z with j by lia. fold q. fold P.
      apply ag32s_upd; [exact AGB | lia | rewrite LENB; lia | lia].
    - (* [comment removed for export] *)
      wstep.
      enter_with (IH (j + 1)%Z _ _ _ _ _ _ _ _ _ _ (upd bwsc (Z.to_nat q) (Z_to_bv 64 (P + 1))) pwsF);
        [ st_eq | lia | lia | exact ARL | exact ARB' | rewrite upd_length; exact LENB | | exact ARP | exact LENP | exact AGP
        | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. rewrite hb_count_snoc. cbn zeta.
      replace (0 + Z.of_nat (Z.to_nat j))%Z with j by lia. fold q. fold P.
      apply ag32s_upd; [exact AGB | lia | rewrite LENB; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_hb_loopZ1 : forall (k : nat) (j : Z) (x8 x9 x18 x19 x20 x29 x30 x31 : word) m1 bwsc pwsF,
    (Z.of_nat k = 23 - j)%Z -> (0 <= j < 23)%Z ->
    u32arr b0segs m1 LIM lws ->
    u32arr b0segs m1 BASE bwsc -> length bwsc = 258%nat -> ag32s bwsc (fill0 base0 0 (Z.to_nat j)) 258 ->
    u32arr b0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr b0segs m1 LEN lbs -> FRAME m1 -> stk b0segs m1 lo (usp + -48) ->
    munch W m m1 -> wmono b0segs m m1 -> mem_inv b0segs m1 ->
    evt b0segs POST
      (MS (mkR ra cSP gp tp (Z_to_bv 64 1) cSB (Z_to_bv 64 (23 - j)) x8 x9
              (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) (Z_to_bv 64 (BASE + 4 * j)) (Z_to_bv 64 LEN)
              (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 alpha) (Z_to_bv 64 1) x18 x19 x20 s5 s6 s7 s8 s9 s10 s11
              (Z_to_bv 64 (BASE + 4 * j)) x29 x30 x31)
          F (Z_to_bv 64 0xa8fe0) fc None m1 (seg_rom b0segs)).
  Proof.
    induction k as [|k IH]; intros j x8 x9 x18 x19 x20 x29 x30 x31 m1 bwsc pwsF HK Hj
      ARL ARB LENB AGB ARP LENP AGP AR8 FR ST MU WM MI; [lia|].
    pose proof sp_range as SPR. pose proof ds_al4 as AL4.
    pose proof (u32arr_bound _ _ _ _ ARB) as BB. rewrite LENB in BB.
    brun_to 0xa9004%Z.
    pose proof (u32arr_store_ok b0segs m1 BASE bwsc j _ ARB ltac:(lia) eq_refl) as SO.
    wstep.
    pose proof (u32arr_write b0segs m1 BASE bwsc j (Z_to_bv 64 0) ARB ltac:(lia)) as ARB'.
    clear ARB. store_done.
    brun. if_cases K; zify_cond K.
    - enter_with (IH (j + 1)%Z _ _ _ _ _ _ _ _ _ (upd bwsc (Z.to_nat j) (Z_to_bv 64 0)) pwsF);
        [ st_eq | lia | lia | exact ARL | exact ARB' | rewrite upd_length; exact LENB | | exact ARP | exact LENP | exact AGP
        | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. rewrite fill0_snoc.
      replace (0 + Z.of_nat (Z.to_nat j))%Z with j by lia.
      apply ag32s_upd; [exact AGB | lia | rewrite LENB; lia | lia].
    - (* [comment removed for export] *)
      pose proof (u8arr_bound _ _ _ _ AR8) as B8. rewrite LEN8 in B8.
      brun_to 0xa9034%Z. wstep. if_false_z. brun_to 0xa9044%Z.
      enter_with (B0_hb_loopC (Z.to_nat alpha) 0 _ _ _ _ _ _ _ _ _ _ (upd bwsc (Z.to_nat j) (Z_to_bv 64 0)) pwsF);
        [ st_eq | lia | lia | exact ARL | exact ARB' | rewrite upd_length; exact LENB | | exact ARP | exact LENP | exact AGP
        | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      cbn [hb_count Z.to_nat]. unfold hbm_base1. replace 23%nat with (S (Z.to_nat j)) by lia. rewrite fill0_snoc.
      replace (0 + Z.of_nat (Z.to_nat j))%Z with j by lia.
      apply ag32s_upd; [exact AGB | lia | rewrite LENB; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_hb_partB : forall (x5 x7 x8 x9 x12 x17 x18 x19 x20 x28 x29 x30 x31 : word) m1 pwsF,
    u32arr b0segs m1 LIM lws ->
    u32arr b0segs m1 BASE bws ->
    u32arr b0segs m1 PERM pwsF -> length pwsF = 258%nat -> ag32s pwsF permF 258 ->
    u8arr b0segs m1 LEN lbs -> FRAME m1 -> stk b0segs m1 lo (usp + -48) ->
    munch W m m1 -> wmono b0segs m m1 -> mem_inv b0segs m1 ->
    evt b0segs POST
      (MS (mkR ra cSP gp tp x5 cSB x7 x8 x9 (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) x12 (Z_to_bv 64 LEN)
              (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 alpha) x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xa8fc4) fc None m1 (seg_rom b0segs)).
  Proof.
    intros x5 x7 x8 x9 x12 x17 x18 x19 x20 x28 x29 x30 x31 m1 pwsF ARL ARB ARP LENP AGP AR8 FR ST MU WM MI.
    pose proof sp_range as SPR. pose proof ds_al4 as AL4.
    pose proof (u32arr_bound _ _ _ _ ARB) as BB. rewrite LENb in BB.
    (* [comment removed for export] *)
    brun_to 0xa8fe0%Z.
    enter_with (B0_hb_loopZ1 23 0 _ _ _ _ _ _ _ _ _ bws pwsF);
      [ st_eq | lia | lia | exact ARL | exact ARB | exact LENb | | exact ARP | exact LENP | exact AGP
      | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
    cbn [fill0 Z.to_nat]. apply ag32s_refl.
  Qed.

  Notation pstate i j := (hb_perm_state len alpha minLen perm0 i j).
  Local Ltac feed H := repeat first [ specialize (H Halpha) | specialize (H Hmm) | specialize (H Hlen) ].

  (* [comment removed for export] *)
  Lemma B0_hb_permJ : forall (k : nat) (i j : Z) (x5 x19 x20 : word) m1 pwsc (Q : machine_state -> Prop),
    (Z.of_nat k = alpha - j)%Z -> (0 <= j < alpha)%Z -> (minLen <= i <= maxLen)%Z ->
    u32arr b0segs m1 LIM lws -> u32arr b0segs m1 BASE bws ->
    u32arr b0segs m1 PERM pwsc -> length pwsc = 258%nat -> ag32s pwsc (fst (pstate i j)) 258 ->
    u8arr b0segs m1 LEN lbs -> FRAME m1 -> stk b0segs m1 lo (usp + -48) ->
    munch W m m1 -> wmono b0segs m m1 -> mem_inv b0segs m1 ->
    (forall (y5 y19 y20 : word) m2 pwsc',
       u32arr b0segs m2 LIM lws -> u32arr b0segs m2 BASE bws ->
       u32arr b0segs m2 PERM pwsc' -> length pwsc' = 258%nat -> ag32s pwsc' (fst (pstate i alpha)) 258 ->
       u8arr b0segs m2 LEN lbs -> FRAME m2 -> stk b0segs m2 lo (usp + -48) ->
       munch W m m2 -> wmono b0segs m m2 -> mem_inv b0segs m2 ->
       evt b0segs Q
         (MS (mkR ra cSP gp tp y5 cSB (Z_to_bv 64 (snd (pstate i alpha))) (Z_to_bv 64 alpha) (Z_to_bv 64 0)
                 (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) (Z_to_bv 64 PERM) (Z_to_bv 64 LEN)
                 (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 alpha) (Z_to_bv 64 (LEN + alpha))
                 (Z_to_bv 64 (LEN + alpha)) y19 y20 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) (Z_to_bv 64 alpha) (Z_to_bv 64 1) (Z_to_bv 64 i))
             F (Z_to_bv 64 0xa8fb4) fc None m2 (seg_rom b0segs))) ->
    evt b0segs Q
      (MS (mkR ra cSP gp tp x5 cSB (Z_to_bv 64 (snd (pstate i j))) (Z_to_bv 64 j) (Z_to_bv 64 (alpha - j))
              (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) (Z_to_bv 64 PERM) (Z_to_bv 64 LEN)
              (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 alpha) (Z_to_bv 64 (LEN + j))
              (Z_to_bv 64 (LEN + j)) x19 x20 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) (Z_to_bv 64 alpha) (Z_to_bv 64 1) (Z_to_bv 64 i))
          F (Z_to_bv 64 0xa8f04) fc None m1 (seg_rom b0segs)).
  Proof.
    induction k as [|k IH]; intros i j x5 x19 x20 m1 pwsc Q HK Hj Hi
      ARL ARB ARP LENP AGP AR8 FR ST MU WM MI HQ; [lia|].
    pose proof sp_range as SPR. pose proof ds_al4 as AL4.
    pose proof (u32arr_bound _ _ _ _ ARP) as BP. rewrite LENP in BP.
    pose proof (u8arr_bound _ _ _ _ AR8) as B8. rewrite LEN8 in B8.
    pose proof (hbw_perm_pp_range len alpha minLen maxLen) as PPR. feed PPR. specialize (PPR perm0 i j ltac:(lia) ltac:(lia)).
    set (pp := snd (pstate i j)) in *.
    (* [comment removed for export] *)
    brun_to 0xa8f28%Z.
    destruct (nth_error_ok lbs j 258 LEN8 ltac:(lia)) as [b NTH].
    pose proof (u8arr_read b0segs m1 LEN lbs j b _ AR8 NTH ltac:(lia) eq_refl) as RD.
    wstep. clear RD.
    pose proof (uv8_nth _ _ _ NTH) as VB. cbv beta delta [zxb]. rewrite <- VB.
    pose proof (Hlen j ltac:(lia)) as LJ.
    (* [comment removed for export] *)
    assert (STEP : pstate i (j + 1) = (if (len j =? i)%Z then (zfupd (fst (pstate i j)) pp j, (pp + 1)%Z) else pstate i j)).
    { unfold hb_perm_state. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. rewrite hb_permJ_snoc. cbn zeta.
      replace (0 + Z.of_nat (Z.to_nat j))%Z with j by lia. fold (pstate i j). fold pp.
      destruct (pstate i j); reflexivity. }
    (* [comment removed for export] *)
    wstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      replace (len j =? i)%Z with false in STEP by (symmetry; apply Z.eqb_neq; lia).
      brun. if_cases K2; zify_cond K2.
      + enter_with (IH i (j + 1)%Z _ _ _ m1 pwsc Q);
          [ st_eq | lia | lia | lia | exact ARL | exact ARB | exact ARP | exact LENP | | exact AR8 | exact FR | exact ST
          | exact MU | exact WM | exact MI | exact HQ ].
        * rewrite STEP. reflexivity.
        * rewrite STEP. exact AGP.
      + (* [comment removed for export] *)
        wstep.
        enter_with (HQ _ _ _ m1 pwsc); [ st_eq | exact ARL | exact ARB | exact ARP | exact LENP | | exact AR8 | exact FR | exact ST
          | exact MU | exact WM | exact MI ].
        * replace (pstate i alpha) with (pstate i (j + 1)) by (f_equal; lia). rewrite STEP. reflexivity.
        * replace (pstate i alpha) with (pstate i (j + 1)) by (f_equal; lia). rewrite STEP. exact AGP.
    - (* [comment removed for export] *)
      replace (len j =? i)%Z with true in STEP by (symmetry; apply Z.eqb_eq; lia).
      pose proof (hbw_perm_store len alpha minLen maxLen) as PPS. feed PPS. specialize (PPS perm0 i j ltac:(lia) ltac:(lia) ltac:(lia)).
      fold pp in PPS.
      (* [comment removed for export] *)
      brun_to 0xa8f74%Z.
      pose proof (u32arr_store_ok b0segs m1 PERM pwsc pp _ ARP ltac:(lia) eq_refl) as SO.
      wstep.
      pose proof (u32arr_write b0segs m1 PERM pwsc pp (Z_to_bv 64 j) ARP ltac:(lia)) as ARP'.
      clear ARP. store_done.
      (* [comment removed for export] *)
      brun. if_cases K2; zify_cond K2.
      + enter_with (IH i (j + 1)%Z _ _ _ _ (upd pwsc (Z.to_nat pp) (Z_to_bv 64 j)) Q);
          [ st_eq | lia | lia | lia | exact ARL | exact ARB | exact ARP' | rewrite upd_length; exact LENP | | exact AR8 | exact FR | exact ST
          | exact MU | exact WM | exact MI | exact HQ ].
        * rewrite STEP. reflexivity.
        * rewrite STEP. cbn [fst]. apply ag32s_upd; [exact AGP | lia | rewrite LENP; lia | lia].
      + wstep.
        enter_with (HQ _ _ _ _ (upd pwsc (Z.to_nat pp) (Z_to_bv 64 j)));
          [ st_eq | exact ARL | exact ARB | exact ARP' | rewrite upd_length; exact LENP | | exact AR8 | exact FR | exact ST
          | exact MU | exact WM | exact MI ].
        * replace (pstate i alpha) with (pstate i (j + 1)) by (f_equal; lia). rewrite STEP. reflexivity.
        * replace (pstate i alpha) with (pstate i (j + 1)) by (f_equal; lia). rewrite STEP. cbn [fst]. apply ag32s_upd; [exact AGP | lia | rewrite LENP; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_hb_permI : forall (k : nat) (i : Z) (x5 x8 x9 x17 x18 x19 x20 : word) m1 pwsc,
    (Z.of_nat k = maxLen + 1 - i)%Z -> (minLen <= i <= maxLen)%Z ->
    u32arr b0segs m1 LIM lws -> u32arr b0segs m1 BASE bws ->
    u32arr b0segs m1 PERM pwsc -> length pwsc = 258%nat -> ag32s pwsc (fst (pstate i 0)) 258 ->
    u8arr b0segs m1 LEN lbs -> FRAME m1 -> stk b0segs m1 lo (usp + -48) ->
    munch W m m1 -> wmono b0segs m m1 -> mem_inv b0segs m1 ->
    evt b0segs POST
      (MS (mkR ra cSP gp tp x5 cSB (Z_to_bv 64 (snd (pstate i 0))) x8 x9
              (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) (Z_to_bv 64 PERM) (Z_to_bv 64 LEN)
              (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 alpha) x17
              x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) (Z_to_bv 64 alpha) (Z_to_bv 64 1) (Z_to_bv 64 i))
          F (Z_to_bv 64 0xa8ef0) fc None m1 (seg_rom b0segs)).
  Proof.
    induction k as [|k IH]; intros i x5 x8 x9 x17 x18 x19 x20 m1 pwsc HK Hi
      ARL ARB ARP LENP AGP AR8 FR ST MU WM MI; [lia|].
    pose proof sp_range as SPR.
    (* [comment removed for export] *)
    wstep. if_false_z. brun_to 0xa8f04%Z.
    eapply evt_eq; [ | eapply (B0_hb_permJ (Z.to_nat alpha) i 0 _ _ _ m1 pwsc);
      [ lia | lia | lia | exact ARL | exact ARB | exact ARP | exact LENP | exact AGP | exact AR8 | exact FR | exact ST
      | exact MU | exact WM | exact MI | ] ]; [ st_eq |].
    clear ARL ARB ARP LENP AGP AR8 FR ST MU WM MI m1 pwsc.
    intros y5 y19 y20 m2 pwsc' ARL ARB ARP LENP AGP AR8 FR ST MU WM MI.
    (* [comment removed for export] *)
    assert (NXT : pstate (i + 1) 0 = pstate i alpha).
    { unfold hb_perm_state. replace (Z.to_nat (i + 1 - minLen)) with (S (Z.to_nat (i - minLen))) by lia.
      rewrite hb_permI_snoc. cbn zeta. replace (minLen + Z.of_nat (Z.to_nat (i - minLen)))%Z with i by lia.
      cbn [hb_permJ Z.to_nat]. destruct (hb_permJ len i 0 (Z.to_nat alpha) _ _); reflexivity. }
    brun. if_cases K; zify_cond K; bz32_in K.
    - (* [comment removed for export] *)
      enter_with (IH (i + 1)%Z _ _ _ _ _ _ _ m2 pwsc');
        [ st_eq | lia | lia | exact ARL | exact ARB | exact ARP | exact LENP | | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      + rewrite NXT. reflexivity.
      + rewrite NXT. exact AGP.
    - (* [comment removed for export] *)
      enter_with (B0_hb_partB _ _ _ _ _ _ _ _ _ _ _ _ _ m2 pwsc');
        [ st_eq | exact ARL | exact ARB | exact ARP | exact LENP | | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
      unfold hbm_perm. replace (span minLen maxLen) with (Z.to_nat (i + 1 - minLen)) by (unfold span; lia).
      change (ag32s pwsc' (fst (pstate i alpha)) 258) in AGP. rewrite <- NXT in AGP.
      unfold hb_perm_state in AGP. cbn [hb_permJ Z.to_nat] in AGP.
      destruct (hb_permI len alpha minLen (Z.to_nat (i + 1 - minLen)) perm0 0) eqn:E. cbn [fst snd] in AGP. cbn [fst]. exact AGP.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_hbCreate_walk : forall (t0 t1 t2 a7 t3 t4 t5 t6 : word),
    u32arr b0segs m LIM lws -> u32arr b0segs m BASE bws -> u32arr b0segs m PERM pws -> u8arr b0segs m LEN lbs ->
    stk b0segs m lo usp -> mem_inv b0segs m -> aconsts B0C m ->
    evt b0segs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LIM) (Z_to_bv 64 BASE) (Z_to_bv 64 PERM) (Z_to_bv 64 LEN)
               (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 alpha) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa8eac) fc None m (seg_rom b0segs)).
  Proof.
    intros t0 t1 t2 a7 t3 t4 t5 t6 ARL ARB ARP AR8 ST MI AC.
    destruct AC as [GOT SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar B0C ci_segs] in GOT, SBV.
    pose proof sp_range as SPR. pose proof ds_al4 as AL4.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl b0segs m) as WM.
    pose proof (u32arr_bound _ _ _ _ ARL) as BL. rewrite LENl in BL.
    pose proof (u32arr_bound _ _ _ _ ARB) as BB. rewrite LENb in BB.
    pose proof (u32arr_bound _ _ _ _ ARP) as BP. rewrite LENp in BP.
    pose proof (u8arr_bound _ _ _ _ AR8) as B8. rewrite LEN8 in B8.
    carve_frame 48%nat ST.
    (* [comment removed for export] *)
    brun_to 0xa8ed4%Z. wstep. if_false_z.
    (* [comment removed for export] *)
    brun_to 0xa8ef0%Z.
    enter_with (B0_hb_permI (Z.to_nat (maxLen + 1 - minLen)) minLen _ _ _ _ _ _ _ _ pws);
      [ st_eq | lia | lia | exact ARL | exact ARB | exact ARP | exact LENp | | exact AR8 | exact FR | exact ST | exact MU | exact WM | exact MI ].
    - unfold hb_perm_state. rewrite Z.sub_diag. cbn [hb_permI hb_permJ Z.to_nat fst snd]. reflexivity.
    - unfold hb_perm_state. rewrite Z.sub_diag. cbn [hb_permI hb_permJ Z.to_nat fst snd]. apply ag32s_refl.
  Qed.
End P.

Theorem B0_hbCreateDecodeTables : hbCreateDecodeTables_aspecF B0C B0_hbCreate_pc B0_FR_hbCreate.
Proof.
  unfold hbCreateDecodeTables_aspecF, B0_FR_hbCreate, hbCreate_W. cbn [aci_segs aci_hi aci_c ci_segs ci_hi B0C].
  intros until lo. intros ARL LENl ARB LENb ARP LENp AR8 LEN8 HS DSH SPd ST HLO MI Halpha Hmm Hlen -> -> -> -> -> -> -> AC Himg HimgD SHd.
  eapply (B0_hbCreate_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DS t lws bws pws lbs minLen maxLen alpha lo); try eassumption; try lia.
Qed.

End ACeilS1.
