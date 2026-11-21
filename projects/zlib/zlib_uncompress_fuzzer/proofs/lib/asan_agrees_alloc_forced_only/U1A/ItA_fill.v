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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U1A Require Import ItA_base ItA_ldefs ItA_here.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

  (* the 1.3.1 register homes of ALL moved to 1.4 by tools/regmap_text_gr.py (t0>a7 t1>t2 t2>t1 a7>t0) *)
Lemma zbv8_congr : forall x y, (x - y) mod 256 = 0 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  apply Z.mod_divide in H; [|lia]. destruct H as [q Hq]. replace x with (y + q * 256) by lia. apply Z.mod_add. lia.
Qed.
Lemma entry_bytes : forall opw hb val, 0 <= opw < 65536 -> 0 <= hb < 256 -> 0 <= val < 65536 ->
  cells_bytes [C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 opw))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 hb))); C2 (Z_to_bv 64 val)]
  = le4 (Z_to_bv 64 (code_pack (wrap8 opw) hb val)).
Proof.
  intros opw hb val Ho Hh Hv. unfold code_pack. rewrite !wrap8_mod, wrap16_mod.
  rewrite (Z.mod_small (opw mod 256)) by (apply Z.mod_pos_bound; lia).
  rewrite (Z.mod_small hb 256), (Z.mod_small val 65536) by lia.
  pose proof (Z.mod_pos_bound opw 256 ltac:(lia)) as HM.
  cbn [cells_bytes cbytes app]. unfold le4, le2. rewrite !unsigned_lit by lia.
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  cbn [app].
  f_equal; [apply zbv8_congr; Z.div_mod_to_equations; lia|].
  f_equal; [apply zbv8_congr; Z.div_mod_to_equations; lia|].
  f_equal; [apply zbv8_congr; Z.div_mod_to_equations; lia|].
  f_equal. apply zbv8_congr; Z.div_mod_to_equations; lia.
Qed.

Lemma swrap32_add_negmod : forall a b, 0 < b < 18446744073709551616 -> -2147483648 <= a - b < 2147483648 ->
  bv_swrap 32 (a + (- b) mod 18446744073709551616) = a - b.
Proof.
  intros a b Hb H. replace ((- b) mod 18446744073709551616) with (18446744073709551616 - b).
  - apply swrap32_sublit. exact H.
  - symmetry. rewrite <- (Z.mod_add (- b) 1 18446744073709551616) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma sllw_m1u : forall k, 0 <= k <= 15 -> bv_swrap 32 (Z.shiftl 18446744073709551615 (k mod 32)) = - 2 ^ k.
Proof.
  intros k Hk. rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. pose proof (pow2_le15 k Hk) as P.
  replace (18446744073709551615 * 2 ^ k) with (- 2 ^ k + 4294967296 * (4294967296 * 2 ^ k)) by lia.
  rewrite swrap32_shift. apply swrap32_small. lia.
Qed.

Lemma srlw_small' : forall a b, 0 <= a < 2147483648 -> 0 <= b < 32 ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 a) (b mod 32)) = Z.shiftr a b.
Proof. intros a b Ha Hb. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. apply srlw_small; assumption. Qed.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

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

  Definition fill_post (st : ItSt) (t' : arr)
      (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 : word) (cnt of : Z -> Z) (next bitsw : word)
      (opw : Z) : machine_state -> Prop :=
    fun ms' => exists (m : amem) (q10 q11 q16 q17 q29 : word),
      ms' = MST st (Z_to_bv 64 opw) (Z_to_bv 64 (tr_hd st - 2 ^ tr_hb st)) (Z_to_bv 64 (tr_hb st)) q10 q11 q16 q17
                (Z_to_bv 64 (- 2 ^ tr_hb st)) (Z_to_bv 64 (tr_val X st)) q29 0x9604c m
      /\ itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 cnt of lf w1 (arr_get t') next bitsw.

  Lemma it_fill_loop : forall (trips : nat) (st : ItSt) (f : Z) (t : arr) (n : Z) (m : amem)
      (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 : word) (cnt of : Z -> Z) (next bitsw : word)
      (opw : Z) (x10 x11 x16 x17 : word),
    f = 2 ^ tr_hb st * Z.of_nat trips -> (1 <= trips)%nat -> Z.of_nat trips <= n ->
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 cnt of lf w1 (arr_get t) next bitsw ->
    arr_len t = 1444 ->
    0 <= tr_hb st <= 15 -> 0 <= t_next st -> 0 <= tr_hd st -> f <= 32768 ->
    t_next st + tr_hd st + f - 2 ^ tr_hb st < 1444 ->
    0 <= opw < 65536 -> 0 <= tr_val X st < 65536 ->
    evtF asegs RNG
      (fill_post st (snd (loopZ n (fill_body (code_pack (wrap8 opw) (tr_hb st) (tr_val X st)) (2 ^ tr_hb st) (tr_hd st) (t_next st)) (f, t)))
                 v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 cnt of next bitsw opw)
      (MST st (Z_to_bv 64 opw) (Z_to_bv 64 (tr_hd st - 2 ^ tr_hb st)) (Z_to_bv 64 (tr_hb st)) x10 x11 x16 x17
           (Z_to_bv 64 (- 2 ^ tr_hb st)) (Z_to_bv 64 (tr_val X st)) (Z_to_bv 64 f) 0x95fc4 m).
  Proof using All.
    induction trips as [|trips IH]; intros st f t n m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 cnt of next bitsw
      opw x10 x11 x16 x17 Hf Htr Hn INV TL Hhb Hnx Hhd Hf2 Hfit Rop Rval; [exfalso; lia|].
    open_ctx CX. open_inv INV. unfold mst, bst.
    pose proof (pow2_le15 (tr_hb st) Hhb) as PI. set (I := 2 ^ tr_hb st) in *.
    assert (Hf1 : I <= f) by (rewrite Hf; rewrite Nat2Z.inj_succ; nia).
    assert (W1 : wrap32 (f - I) = f - I) by (apply wrap32_small; lia).
    zs. zs. zs. setreg 10 (Z_to_bv 64 (4 * (tr_hd st - I + f))) ltac:(rewrite zext32_x4 by lia; reflexivity).
    zs. setreg 10 (Z_to_bv 64 (S + 1384 + 4 * (t_next st + (tr_hd st + (f - I))))) ltac:(f_equal; lia).
    f32_open_at CDS (t_next st + (tr_hd st + (f - I))) D ED CH CC.
    do 4 zs. zs. do 5 zs. zs. do 5 zs.
    zs. setreg 29 (Z_to_bv 64 (f - I)) ltac:(rewrite swrap32_add_negmod by lia; reflexivity).
    zs.
    f32_close_at CH CC ED (code_pack (wrap8 opw) (tr_hb st) (tr_val X st)) CDS; [apply entry_bytes; lia|]. subst D.
    assert (HIDX : 0 <= t_next st + (tr_hd st + (f - I)) < arr_len t) by (rewrite TL; lia).
    apply (fun H => f32arr_ext asegs _ _ _ _ (arr_get (arr_set t (t_next st + (tr_hd st + (f - I))) (code_pack (wrap8 opw) (tr_hb st) (tr_val X st)))) H
                      (fun j _ => fupd_arr_set t _ _ j HIDX)) in CDS.
    rewrite <- W1 in CDS.
    zs. zbr0 KF.
    -
      rewrite fill_more by first [lia | rewrite W1; exact KF]. rewrite W1 in *.
      eapply (IH st (f - I) _ (n - 1)); [ | | lia | | | exact Hhb | exact Hnx | exact Hhd | lia | lia | exact Rop | exact Rval].
      + rewrite Hf, Nat2Z.inj_succ. fold I. ring.
      + destruct trips; [cbn in Hf; exfalso; lia | lia].
      + close_inv.
      + rewrite arr_len_set. exact TL.
    -
      zs. rewrite fill_last by first [lia | rewrite W1; exact KF]. cbn [snd].
      rewrite W1, KF in CDS.
      apply evtF_done. unfold fill_post. eexists. do 5 eexists. split; [reflexivity|]. close_inv.
  Qed.

  Notation MINV := (fun m st => minv SPA S F PB m1 m ty rt nx bits lf w1 st).

  Definition fill_post1 (st : ItSt) (v0 v96 v104 v112 : word) (of : Z -> Z) : machine_state -> Prop :=
    fun ms' => exists (m : amem) (q1 q6 q10 q11 q16 q17 q25 q28 q29 : word),
      ms' = MST st q1 q6 (Z_to_bv 64 (tr_hb st)) q10 q11 q16 q17 q25 q28 q29 0x9604c m
      /\ MINV m (mkItSt (t_huff st) (t_sym st) (t_len st) (t_next st) (t_curr st) (t_drop st) (t_low st) (t_used st) (t_min st)
                        (t_count st) (tr_tbl1 X st) (t_work st)) v0 v96 v104 v112 of.

  Lemma it_fill : forall (st : ItSt) (m : amem) (v0 v96 v104 v112 : word) (of : Z -> Z)
      (x6 x7 x10 x11 x16 x17 x25 x29 : word),
    MINV m st v0 v96 v104 v112 of -> arr_len (t_tbl st) = 1444 ->
    1 <= t_len st <= 15 -> 0 <= t_drop st <= t_len st -> t_len st - t_drop st <= t_curr st <= 15 ->
    0 <= t_huff st < 65536 -> 0 <= t_next st ->
    t_next st + Z.shiftr (t_huff st) (t_drop st) + 2 ^ t_curr st - 2 ^ (t_len st - t_drop st) < 1444 ->
    0 <= tr_opw ty st < 65536 -> 0 <= tr_val X st < 65536 ->
    evtF asegs RNG (fill_post1 st v0 v96 v104 v112 of)
      (MST st (Z_to_bv 64 (tr_opw ty st)) x6 x7 x10 x11 x16 x17 x25 (Z_to_bv 64 (tr_val X st)) x29 0x95fac m).
  Proof using All.
    intros until x29. intros INV TL Flen Fdrop Fcurr Fhuff Fnext Ffit Rop Rval.
    assert (Ehb : tr_hb st = t_len st - t_drop st) by reflexivity.
    assert (Hhb : 0 <= tr_hb st <= 15) by lia.
    assert (Hhd : 0 <= tr_hd st <= t_huff st).
    { unfold tr_hd. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (t_drop st) ltac:(lia) ltac:(lia)).
      split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | nia]]. }
    pose proof (pow2_le15 (tr_hb st) Hhb) as PI. pose proof (pow2_le15 (t_curr st) ltac:(lia)) as PF.
    pose proof (pow2_le15 (t_curr st - tr_hb st) ltac:(lia)) as PQ.
    assert (EQ : 2 ^ t_curr st = 2 ^ tr_hb st * 2 ^ (t_curr st - tr_hb st)).
    { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    pose proof INV as INV0. open_ctx CX. unfold minv in INV. open_inv INV. unfold mst, bst.
    zs. setreg 6 (Z_to_bv 64 (tr_hb st)) ltac:(rewrite Ehb; rewrite swrap32_small by lia; reflexivity).
    zs. zs. setreg 25 (Z_to_bv 64 (- 2 ^ tr_hb st)) ltac:(rewrite sllw_m1u by lia; reflexivity).
    zs. setreg 7 (Z_to_bv 64 (tr_hd st)) ltac:(unfold tr_hd; rewrite srlw_small' by lia; reflexivity).
    zs. zs.
    pose proof (it_fill_loop (Z.to_nat (2 ^ (t_curr st - tr_hb st))) st (2 ^ t_curr st) (t_tbl st) (2 ^ t_curr st) m) as HL.
    eapply evtF_mono; [eapply HL|]; clear HL.
    - rewrite Z2Nat.id by lia. exact EQ.
    - lia.
    - rewrite Z2Nat.id by lia. apply Z.pow_le_mono_r; lia.
    - unfold itb_inv, itb_W, frm15. do 10 (split; [eassumption|]). eassumption.
    - exact TL.
    - exact Hhb.
    - exact Fnext.
    - lia.
    - lia.
    - unfold tr_hd. rewrite Ehb. lia.
    - exact Rop.
    - exact Rval.
    - cbv beta. intros ms' (m' & q10 & q11 & q16 & q17 & q29 & -> & INV').
      unfold fill_post1. exists m'. do 9 eexists. split; [reflexivity|].
      unfold minv. cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_count t_tbl t_work].
      replace (tr_tbl1 X st) with (snd (loopZ (2 ^ t_curr st) (fill_body (code_pack (wrap8 (tr_opw ty st)) (tr_hb st) (tr_val X st)) (2 ^ tr_hb st) (tr_hd st) (t_next st)) (2 ^ t_curr st, t_tbl st))); [exact INV'|].
      unfold tr_tbl1. rewrite it_fill_eq. unfold tr_incr, tr_fill. rewrite !shl32_1 by lia.
      unfold tr_here. rewrite (tr_op_wrap8 ty lf lo codes nx bits st). rewrite (wrap8_mod (tr_hb st)), Z.mod_small by lia. reflexivity.
  Qed.
End P.
End CANSEC1.
