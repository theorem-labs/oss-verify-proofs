(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U1A Require Import ItA_base ItA_ldefs ItA_here ItA_fill.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP SPA S F PB top : Z) (m1 : amem).
  Variables (ty : codetype) (lf wf cf : Z -> Z) (lo codes nx bits : Z).
  Hypothesis CX : itb_ctx RNG SP SPA S F PB top m1.
  Hypothesis C : itc ty lf lo codes nx bits cf wf.

  Notation LP := (S + 168 + 2 * lo).
  Notation cntAr := (cntA lf lo codes).
  Notation mx := (mxA lf lo codes).
  Notation mn := (mnA lf lo codes).
  Notation rt := (rootA lf lo codes bits).
  Notation work1Ar := (work1A lf lo codes wf).
  Notation w1 := (arr_get (work1A lf lo codes wf)).
  Notation X := (itm_ctx ty (lensA lf) lo nx rt mx).
  Notation MST := (mst SP SPA S F PB LP gp tp FR fc rt mx).
  Notation MINV := (fun m st => minv SPA S F PB m1 m ty rt nx bits lf w1 st).

  (* the 1.3.1 register homes of ALL moved to 1.4 by tools/regmap_text_gr.py (t0>a7 t1>t2 t2>t1 a7>t0) *)
  Definition incr_post (st : ItSt) (incr : Z) (m : amem) (x1 x6 x7 x17 x25 x28 x29 : word) : machine_state -> Prop :=
    fun ms' => exists (q10 q16 : word),
      ms' = MST st x1 x6 x7 q10 (Z_to_bv 64 incr) q16 x17 x25 x28 x29 0x9606c m.

  Lemma it_incr_loop : forall (k : nat) (c n : Z) (st : ItSt) (m : amem) (x1 x6 x7 x11 x16 x17 x25 x28 x29 : word),
    0 <= c < 2 ^ Z.of_nat k -> Z.of_nat k < n -> c < 65536 -> 0 <= t_huff st < 65536 ->
    evtF asegs RNG (incr_post st (loopZ n (incr_body (t_huff st)) c) m x1 x6 x7 x17 x25 x28 x29)
      (MST st x1 x6 x7 (Z_to_bv 64 c) x11 x16 x17 x25 x28 x29 0x96058 m).
  Proof using All.
    induction k as [|k IH]; intros c n st m x1 x6 x7 x11 x16 x17 x25 x28 x29 Hc Hn Hc2 Hhuff.
    - cbn [Z.of_nat Z.pow] in Hc. assert (E : c = 0) by lia. subst c. unfold mst, bst.
      zs. zs. zs. setreg 16 (Z_to_bv 64 0) ltac:(reflexivity).
      zs. zs.
      apply evtF_done. unfold incr_post. do 2 eexists.
      rewrite incr_last by (first [lia | apply Z.land_0_r]). reflexivity.
    - unfold mst, bst.
      assert (HA : 0 <= Z.land c (t_huff st) <= c) by (split; [apply Z.land_nonneg; lia | apply land_le_l; lia]).
      pose proof (shiftr1_half c k Hc) as HH.
      assert (HH2 : Z.shiftr c 1 <= c) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 1) with 2; apply Z.div_le_upper_bound; lia).
      zs. zs. zs. setreg 16 (Z_to_bv 64 (Z.land c (t_huff st))) ltac:(rewrite Z.add_0_r; rewrite swrap32_small by lia; reflexivity).
      zs. setreg 10 (Z_to_bv 64 (Z.shiftr c 1))
            ltac:(unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296; rewrite (Z.mod_small c) by lia; rewrite swrap32_small by lia; reflexivity).
      zs. zbr0 KZ.
      +
        rewrite incr_more by (first [lia | rewrite Z.land_comm; exact KZ]).
        eapply (IH (Z.shiftr c 1) (n - 1)); lia.
      + apply evtF_done. unfold incr_post. do 2 eexists.
        rewrite incr_last by (first [lia | rewrite Z.land_comm; exact KZ]). reflexivity.
  Qed.

  Definition stF (st : ItSt) : ItSt :=
    mkItSt (t_huff st) (t_sym st) (t_len st) (t_next st) (t_curr st) (t_drop st) (t_low st) (t_used st) (t_min st)
           (t_count st) (tr_tbl1 X st) (t_work st).

  Definition cnt2_post (st : ItSt) (x7 : word) (v0 v96 v104 v112 : word) (of : Z -> Z) : machine_state -> Prop :=
    fun ms' =>
      (* 1.4 keeps the constant 1 in s9 (0x96000 li s9,1; 1.3.1: t3) and has reloaded match
         into t4 (0x96034 ld t4,72(s1)) *)
      (exists (m : amem) (q1 q6 q10 q11 q16 q17 q28 : word),
         ms' = MST (tr_st1 X st) q1 q6 x7 q10 q11 q16 q17 (Z_to_bv 64 1) q28 (Z_to_bv 64 (it_match ty)) 0x96108 m
         /\ MINV m (tr_st1 X st) v0 v96 v104 v112 of /\ tr_brk X st = false)
      \/ (exists (m : amem) (q1 q6 q10 q11 q16 q17 q28 : word),
            ms' = MST (tr_st1 X st) q1 q6 x7 q10 q11 q16 q17 (Z_to_bv 64 1) q28 (Z_to_bv 64 (it_match ty)) 0x962d0 m
            /\ MINV m (tr_st1 X st) v0 v96 v104 v112 of /\ tr_brk X st = true).

  Lemma le2_congr : forall a b, (a - b) mod 65536 = 0 -> le2 (Z_to_bv 64 a) = le2 (Z_to_bv 64 b).
  Proof.
    intros a b H. unfold le2. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    cbn [Z_to_le_bytes]. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    f_equal; [| f_equal]; apply zbv8_congr; Z.div_mod_to_equations; lia.
  Qed.
  Lemma sx16_swrap : forall c, 0 <= c < 18446744073709551616 -> sx16 (Z_to_bv 64 c) = Z_to_bv 64 (bv_swrap 16 c).
  Proof. intros c Hc. unfold sx16. rewrite unsigned_lit by lia. reflexivity. Qed.

  Lemma it_count2 : forall (st : ItSt) (m : amem) (v0 v96 v104 v112 : word) (of : Z -> Z)
      (x1 x6 x7 x10 x11 x16 x17 x25 x28 x29 : word),
    MINV m (stF st) v0 v96 v104 v112 of -> t_work st = work1Ar ->
    1 <= t_len st <= 15 -> 0 <= t_huff st < 65536 -> 0 <= t_sym st < 288 -> 0 <= mx <= 15 ->
    (forall j, 0 <= j < 16 -> 0 <= arr_get (t_count st) j < 65536) -> arr_len (t_count st) = 16 ->
    (tr_c st = 0 -> t_len st <> mx ->
       t_sym st + 1 < 288 /\ 0 <= w1 (t_sym st + 1) /\ 0 <= lo + w1 (t_sym st + 1) < 320 /\ 1 <= lf (lo + w1 (t_sym st + 1)) <= 15) ->
    evtF asegs RNG (cnt2_post st x7 v0 v96 v104 v112 of)
      (MST st x1 x6 x7 x10 x11 x16 x17 x25 x28 x29 0x9604c m).
  Proof using All.
    intros until x29. intros INV WK Flen Fhuff Fsym MXR HCr CL Flook.
    pose proof (pow2_le15 (t_len st - 1) ltac:(lia)) as PL.
    assert (I14 : 2 ^ (t_len st - 1) <= 16384) by (change 16384 with (2 ^ 14); apply Z.pow_le_mono_r; lia).
    unfold mst, bst.
    zs. zs. zs. setreg 10 (Z_to_bv 64 (2 ^ (t_len st - 1))) ltac:(replace (t_len st + -1) with (t_len st - 1) by lia; rewrite sllw_1 by lia; reflexivity).
    eapply evtF_cut; [eapply (it_incr_loop (Z.to_nat (t_len st)) (2 ^ (t_len st - 1)) 32 st m)|].
    { rewrite Z2Nat.id by lia. split; [lia|]. apply Z.pow_lt_mono_r; lia. }
    { lia. }
    { lia. }
    { exact Fhuff. }
    cbv beta. intros ms1 (q10 & q16 & ->).
    assert (EI : loopZ 32 (incr_body (t_huff st)) (2 ^ (t_len st - 1)) = tr_incr2 st).
    { unfold tr_incr2. rewrite it_incr_back_eq, shl32_1 by lia. reflexivity. }
    pose proof (incr_range (t_huff st) 32 (2 ^ (t_len st - 1)) ltac:(lia)) as IR.
    rewrite EI in *. clear EI.
    set (v1 := Z.land (tr_incr2 st - 1) (t_huff st) + tr_incr2 st).
    assert (HL : 0 <= Z.land (tr_incr2 st - 1) (t_huff st) <= t_huff st).
    { destruct (Z.eq_dec (tr_incr2 st) 0) as [E0|NE0].
      - rewrite E0. change (0 - 1) with (-1). rewrite Z.land_m1_l. lia.
      - split; [apply Z.land_nonneg; lia | apply land_le_r; lia]. }
    assert (EH : tr_huff st = Z.land (Z.b2z (tr_incr2 st =? 0) + -1) v1).
    { unfold tr_huff, v1. destruct (Z.eqb_spec (tr_incr2 st) 0) as [E0|NE0]; cbn [Z.b2z negb Z.add].
      - symmetry. apply Z.land_0_l.
      - rewrite Z.land_m1_l. rewrite Z.land_comm. reflexivity. }
    set (c0 := arr_get (t_count st) (t_len st)).
    pose proof (HCr (t_len st) ltac:(lia)) as HC0. fold c0 in HC0.
    assert (ESY : tr_sym st = t_sym st + 1) by (unfold tr_sym; apply wrap32_small; lia).
    pose proof INV as INV0. open_ctx CX. unfold minv in INV. open_inv INV. cbn [t_count t_tbl t_used t_low t_curr stF] in *.
    unfold mst, bst.
    zs. zs. setreg 10 (Z_to_bv 64 (2 * t_len st)) ltac:(rewrite zext32_x2 by lia; reflexivity).
    zs. do 4 zs.
    (* 1.4 reloads match into t4 here (0x96034 ld t4,72(s1)), one instruction more than 1.3.1 *)
    zs. zs. zs. zs. zs.
    setreg 5 (Z_to_bv 64 (Z.land (tr_incr2 st - 1) (t_huff st)))
      ltac:(change 18446744073709551616 with (2 ^ 64); rewrite (Z.land_comm ((tr_incr2 st + -1) mod 2 ^ 64)), (land_mod_pow2_r (t_huff st) (tr_incr2 st + -1) 64) by lia;
            rewrite Z.land_comm; replace (tr_incr2 st + -1) with (tr_incr2 st - 1) by lia; reflexivity).
    f16_open_at CNT (t_len st) D ED CH CC. fold c0 in CC.
    zs. rewrite (sx16_swrap c0) by lia.
    set (c0s := bv_swrap 16 c0) in *.
    pose proof (swrap16_cases c0 HC0) as HS16. fold c0s in HS16.
    assert (HSR : -32768 <= c0s <= c0) by (destruct HS16; lia). box HS16.
    zs. zs. setreg 11 (Z_to_bv 64 v1) ltac:(unfold v1; rewrite (Z.mod_small (Z.land (tr_incr2 st - 1) (t_huff st))) by lia; rewrite swrap32_small by lia; reflexivity).
    zs.
    assert (EH' : Z_to_bv 64 (tr_huff st) = Z_to_bv 64 (Z.land ((Z.b2z (tr_incr2 st <? 1) + -1) mod 18446744073709551616) v1)).
    { f_equal. rewrite EH. destruct (Z.eq_dec (tr_incr2 st) 0) as [E0|NE0].
      - rewrite E0. reflexivity.
      - replace (tr_incr2 st =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (tr_incr2 st <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
        cbn [Z.b2z]. change (0 + -1) with (-1). change ((-1) mod 18446744073709551616) with (Z.ones 64).
        rewrite Z.land_m1_l, (Z.land_comm (Z.ones 64) v1), Z.land_ones by lia. symmetry. apply Z.mod_small. unfold v1. change (2 ^ 64) with 18446744073709551616. lia. }
    rewrite <- EH'. clear EH'.
    zs. zs. zs. zs. zs.
    setreg 11 (Z_to_bv 64 ((c0s + -1) * 281474976710656))
      ltac:(apply zbv_congr; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 48) with 281474976710656;
            rewrite (Z.mod_eq c0s 18446744073709551616) by lia;
            replace ((c0s + -1) * 281474976710656 - ((c0s - 18446744073709551616 * (c0s / 18446744073709551616)) * 281474976710656 + 18446462598732840960))
              with ((c0s / 18446744073709551616 * 281474976710656 - 1) * 18446744073709551616) by lia;
            apply Z.mod_mul; lia).
    zs.
    f16_close_at CH CC ED (tr_c st) CNT.
    { apply le2_congr. unfold tr_c. fold c0. rewrite wrap16_mod. unbox HS16.
      destruct HS16 as [[A B]|[A B]]; rewrite B; Z.div_mod_to_equations; lia. }
    subst D.
    assert (HLEN : 0 <= t_len st < arr_len (t_count st)) by (rewrite CL; lia).
    apply (fun H => f16arr_ext asegs _ _ _ _ (arr_get (tr_count st)) H
                      (fun j _ => fupd_arr_set (t_count st) _ _ j HLEN)) in CNT.
    assert (EC : tr_c st = (c0 - 1) mod 65536) by (unfold tr_c; fold c0; apply wrap16_mod).
    assert (DONE : forall (pc : Z) (brk : bool) (mm : amem) (lenv : Z) (y1 y6 y10 y11 y16 y17 y28 : word),
              tr_len X st = lenv -> tr_brk X st = brk ->
              itb_inv SPA S F PB m1 mm v0 (Z_to_bv 64 (isD ty)) (Z_to_bv 64 (isL ty)) (Z_to_bv 64 (Z.shiftr (S + 160) 3 + 2147450880))
                (Z_to_bv 64 (t_used st)) (Z_to_bv 64 (EXA ty S)) (Z_to_bv 64 (BSA ty S)) (Z_to_bv 64 (2 ^ rt - 1))   (* [P14] 1.4: extra in slot 40, base in 48 *)
                (Z_to_bv 64 (lowS (t_low st))) (Z_to_bv 64 (it_match ty)) (Z_to_bv 64 (2 ^ t_curr st)) (Z_to_bv 64 (S + 160))
                v96 v104 v112 (arr_get (tr_count st)) of lf w1 (arr_get (tr_tbl1 X st))
                (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits) ->
              (pc = 0x96108 /\ brk = false) \/ (pc = 0x962d0 /\ brk = true) ->   (* [P14] 1.4's beq a5,a4 targets 0x96280 (ld a6,32(s1)), one before the tail's beqz *)
              cnt2_post st x7 v0 v96 v104 v112 of
                (bst SP SPA S F PB LP gp tp FR fc y1 y17 x7 y6 y10 y11 (Z_to_bv 64 (Z.shiftr PB 3 + 2147450880))
                     (Z_to_bv 64 rt) (Z_to_bv 64 mx) (Z_to_bv 64 lenv) y16 (Z_to_bv 64 (t_drop st)) (Z_to_bv 64 (tr_huff st))
                     (Z_to_bv 64 1) y28 (Z_to_bv 64 (it_match ty))   (* [P14] s9 = 1, t4 = match at 1.4 *)
                     (Z_to_bv 64 (S + 1384 + 4 * t_next st)) (Z_to_bv 64 (t_sym st + 1)) pc mm)).
    { intros pc brk mm lenv y1 y6 y10 y11 y16 y17 y28 EL EB INVm [[-> ->]|[-> ->]]; unfold cnt2_post; [left|right];
        (exists mm; do 7 eexists; split; [unfold mst; cbn [t_drop t_len t_huff t_next t_sym tr_st1]; rewrite EL, ESY; reflexivity|];
         split; [unfold minv; cbn [t_used t_low t_curr t_count t_tbl tr_st1]; exact INVm | exact EB]). }
    zs.
    destruct (Z.eq_dec c0 1) as [C1|NC1].
    - assert (C1s : c0s = 1) by (unbox HS16; destruct HS16; lia).
      assert (EC0 : tr_c st = 0) by (rewrite EC, C1; reflexivity).
      zbr K1. zs. zbr0 KM.
      +
        apply evtF_done. eapply (DONE 0x962d0 true); [| | close_inv | right; split; reflexivity].
        * unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx]. rewrite EC0. destruct (Z.eqb_spec (t_len st) mx); [reflexivity | lia].
        * unfold tr_brk. cbn [x_max itm_ctx]. rewrite EC0. cbn [Z.eqb andb]. apply Z.eqb_eq. exact KM.
      +
        destruct (Flook EC0 KM) as (W1 & W2 & W3 & W4).
        pose proof (work1_range ty lf wf cf lo codes nx bits C (t_sym st + 1) ltac:(lia)) as WR.
        zs. zs. setreg 10 (Z_to_bv 64 (2 * (t_sym st + 1))) ltac:(rewrite zext32_x2 by lia; reflexivity).
        zs. do 4 zs.
        pose proof (f16arr_read asegs _ (S + 808) 288 _ (t_sym st + 1) _ WORK ltac:(lia) eq_refl) as RD.
        zs. rewrite (zx16_small (w1 (t_sym st + 1))) by lia. clear RD.
        zs. zs. setreg 10 (Z_to_bv 64 (S + 168 + 2 * (lo + w1 (t_sym st + 1)))) ltac:(rewrite shl1_2x; f_equal; lia).
        do 4 zs.
        pose proof (f16arr_read asegs _ (S + 168) 320 lf (lo + w1 (t_sym st + 1)) _ LENS ltac:(lia) eq_refl) as RD.
        zs. rewrite (zx16_small (lf (lo + w1 (t_sym st + 1)))) by lia. clear RD.
        apply evtF_done. eapply (DONE 0x96108 false); [| | close_inv | left; split; reflexivity].
        * unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx]. rewrite EC0. destruct (Z.eqb_spec (t_len st) mx); [lia|].
          cbn [Z.eqb andb negb]. rewrite WK, ESY. apply lensA_get.
        * unfold tr_brk. cbn [x_max itm_ctx]. rewrite EC0. cbn [Z.eqb andb]. apply Z.eqb_neq. exact KM.
    - assert (HNZ : ((c0s + -1) * 281474976710656) mod 18446744073709551616 <> 0).
      { unbox HS16. destruct HS16 as [[A B]|[A B]]; rewrite B.
        - destruct (Z.eq_dec c0 0) as [E0|NE0]; [rewrite E0; cbv; discriminate | rewrite Z.mod_small by lia; lia].
        - rewrite negshift48_mod by lia. lia. }
      zbr K1.
      assert (ECN : tr_c st <> 0).
      { rewrite EC. destruct (Z.eq_dec c0 0) as [E0|NE0]; [rewrite E0; cbv; discriminate | rewrite Z.mod_small by lia; lia]. }
      apply evtF_done. eapply (DONE 0x96108 false); [| | close_inv | left; split; reflexivity].
      * unfold tr_len. destruct (Z.eqb_spec (tr_c st) 0); [lia | reflexivity].
      * unfold tr_brk. destruct (Z.eqb_spec (tr_c st) 0); [lia | reflexivity].
  Qed.
End P.
End CANSEC1.
