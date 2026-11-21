(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure UbFit2.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import ItBTac ItB_base ItB_ldefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Section CANSEC1. Context {rc : runConstT}.

Lemma zx8_wrap8 : forall e, 0 <= e < 18446744073709551616 -> zx8 (Z_to_bv 64 e) = Z_to_bv 64 (wrap8 e).
Proof.
  intros e H. unfold zx8, wrap8. rewrite unsigned_lit by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity.
Qed.
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
  Notation MST := (mst SP SPA S F PB LP (cty ty) gp tp FR fc rt mx).
  Notation MINV := (fun m st => minv SPA S F PB m1 m ty rt nx bits lf w1 st).

  Definition tr_opw (st : ItSt) : Z :=
    let w := tr_w st in
    if w + 1 <? it_match ty then 0
    else if it_match ty <=? w then it_extra ty (t_work st) (w - it_match ty) else 96.
  Lemma tr_op_opw : forall st, tr_op X st = (if (tr_w st + 1 <? it_match ty) then 0 else if (it_match ty <=? tr_w st) then wrap8 (tr_opw st) else 96).
  Proof.
    intros st. unfold tr_op, tr_ov, tr_opw. cbn [x_ty itm_ctx]. cbv zeta.
    destruct (tr_w st + 1 <? it_match ty); [reflexivity|]. destruct (it_match ty <=? tr_w st); reflexivity.
  Qed.

  Lemma tr_op_wrap8 : forall st, tr_op X st = wrap8 (tr_opw st).
  Proof.
    intros st. rewrite tr_op_opw. unfold tr_opw. cbv zeta.
    destruct (tr_w st + 1 <? it_match ty); [reflexivity|]. destruct (it_match ty <=? tr_w st); reflexivity.
  Qed.

  Definition here_post (st : ItSt) (m : amem) (x7 x29 x30 x31 : word) : machine_state -> Prop :=
    fun ms' => exists (q5 q11 q16 : word),
      (* [U14B] A2 2026-11-12: the 1.4 homes (see mst in ItB_ldefs): drop t0, len t1, op t2 (0x97480 li t2,0; 0x97504 lbu
         t2,0(a0); 1.3.1 t1), huff t4; the scratch q5 is a7 (1.3.1 t0); x7 / x29 / x30 / x31 are t3 / t5 / t6 / s9. *)
      ms' = bst SP SPA S F PB LP (cty ty) gp tp FR fc (Z_to_bv 64 (S + 1384 + 4 * t_next st)) (Z_to_bv 64 (t_drop st)) (Z_to_bv 64 (t_len st))
                (Z_to_bv 64 (tr_op X st)) (Z_to_bv 64 (tr_val X st)) q11
                (Z_to_bv 64 (t_len st - t_drop st)) (Z_to_bv 64 (Z.shiftr PB 3 + 2147450880)) (Z_to_bv 64 rt) (Z_to_bv 64 mx) q16
                q5 x31 x7 (Z_to_bv 64 (t_huff st)) x29 x30 0x974d8 m.

  Lemma work1_range : forall j, 0 <= j < 288 -> 0 <= w1 j < 65536.
  Proof.
    intros j Hj. pose proof C as C'. open_itc C'. unfold work1A. rewrite itm_work_eq.
    apply (sort_k_work_range (lensA lf) lo codes (offsA lf lo codes) (workA wf) 288); [|exact Hj].
    intros i Hi. rewrite workA_get. apply Hwf. exact Hi.
  Qed.

  Lemma it_here : forall (st : ItSt) (m : amem) (v0 v8 v16 v56 v128 v136 : word) (of : Z -> Z)
      (x5 x6 x7 x11 x16 x29 x30 x31 : word),
    MINV m st v0 v8 v16 v56 v128 v136 of -> spure work1Ar rt nx st ->
    0 <= t_sym st < 288 -> 0 <= tr_w st < 65536 ->
    (it_match ty <= tr_w st -> tr_w st - it_match ty < NE ty) ->
    (* [U14B] A2 2026-11-12: zlib 1.4 stores null base / extra for CODES, and the combined code traps on the null flag
       (0x974c4 beqz a7,0x97c30), so here needs the CODES bound "the symbol is below match = 20" (G's U1A cure C48) *)
    (ty = CODES -> tr_w st < 20) ->
    evtF bsegs RNG (here_post st m x7 x29 x30 x31)
      (MST st x5 x6 x7 x11 x16 x29 x30 x31 0x97420 m).
  Proof using All.
    intros until x31. intros INV HU Hsym Hw Hwm Hw20. open_ctx CX. unfold minv in INV. open_inv INV. open_spure HU. unfold mst, bst.
    pose proof C as C'. open_itc C'.
    assert (MT : 0 <= it_match ty <= 257) by (clear; destruct ty; cbn; lia).
    unfold tr_w in Hw, Hwm, Hw20. rewrite WK in Hw, Hwm, Hw20. box Hwm. box Hw20. clear HtyC HtyD LOWR DROPR.
    zs. zs. ubg.
    do 4 zs.
    pose proof (f16arr_read bsegs m (S + 808) 288 _ (t_sym st) _ WORK ltac:(lia) eq_refl) as RD.
    zs. rewrite (zx16_small (w1 (t_sym st))) by lia. clear RD.
    zs. zs. zs. zbr0 K1.
    2:{
      zs. zs.
      apply evtF_done. unfold here_post. do 3 eexists.
      unfold tr_op, tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. cbv zeta. rewrite WK.
      destruct (Z.ltb_spec (w1 (t_sym st) + 1) (it_match ty)); [| lia]. cbn [fst snd]. reflexivity. }
    zs. zbr0 K2.
    2:{
      zs. zs. zs.
      apply evtF_done. unfold here_post. do 3 eexists.
      unfold tr_op, tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. cbv zeta. rewrite WK.
      destruct (Z.ltb_spec (w1 (t_sym st) + 1) (it_match ty)); [lia|].
      destruct (Z.leb_spec (it_match ty) (w1 (t_sym st))); [lia|]. cbn [fst snd]. reflexivity. }
    unbox Hwm. specialize (Hwm ltac:(lia)).
    zs. setreg 11 (Z_to_bv 64 (w1 (t_sym st) - it_match ty)) ltac:(rewrite swrap32_small by lia; f_equal; lia).
    zs. zs. setreg 16 (Z_to_bv 64 (2 * (w1 (t_sym st) - it_match ty))) ltac:(rewrite zext32_shift31 by lia; reflexivity).
    pose proof (it_tabsh_mu _ m1 m SHT MU DJT) as (TSH1 & TSH2 & TSH3 & TSH4).
    destruct (ty_cases ty S) as [(ET & ECT & EM & EEX & EBS & ENE & EL & ED) | [(ET & ECT & EM & EEX & EBS & ENE & EL & ED) | (ET & ECT & EM & EEX & EBS & ENE & EL & ED)]];
      rewrite ?EEX, ?EBS, ?EM in *; rewrite ENE in Hwm.
    - (* [U14B] A2 2026-11-12: CODES never reaches the extra / base arm at 1.4: the symbol is below 20 = match *)
      exfalso. unbox Hw20. specialize (Hw20 ET). lia.
    -
      replace (XFL ty) with 1 in * by (rewrite ET; reflexivity).
      pose proof (lext_range (w1 (t_sym st) - 257) ltac:(lia)) as XR. pose proof (lbase_range (w1 (t_sym st) - 257) ltac:(lia)) as BR.
      pose proof (f16ro_read_lo bsegs m A_LEXT 31 (arr_get lext_a) (w1 (t_sym st) - 257) _ (lext_bytes m MI) ltac:(lia) eq_refl) as RDX.
      change A_LEXT with 149312 in RDX.
      pose proof (lbase_read m (w1 (t_sym st) - 257) _ MI ltac:(lia) eq_refl) as RDB.
      (* [U14B] A2 2026-11-12: the 1.4 combined arm (0x974a4 .. 0x9750c): extra from slot 16, the flag from slot 56, base
         from slot 48; the UBSan pointer checks are bltu / seqz-xor-flag / flag / bltu / beqz; no alignment checks *)
      zs. zs. zs. ubg.                 (* ld a7,16(s1); add a0,a7,a6; bltu a0,a7 *)
      zs. seqz0 17. zs. zs. zs. ubg.   (* seqz a7,a0; ld t2,56(s1); xor a7,t2,a7; beqz a7 *)
      zs. zs. ubg.                     (* ld a7,56(s1); beqz a7 *)
      zs. zs. zs. ubg.                 (* ld a7,48(s1); add a6,a6,a7; bltu a6,a7 *)
      zs. ubg.                         (* beqz a6 *)
      destruct (tab62_check m 149312 2147469544 (w1 (t_sym st) - 257) TSH2 eq_refl ltac:(lia) eq_refl ltac:(lia)) as (b1 & RD1 & CK1).
      zs. zs. zs. rewrite sxb_sval. clear RD1.
      ck_branchJ 17 0x974b0 CK1.
      zs. zs. setreg 11 (Z_to_bv 64 (2 * (w1 (t_sym st) - 257))) ltac:(rewrite Z.mod_small by lia; rewrite shl1_2x; reflexivity).
      zs. zs.                          (* ld a6,48(s1); add a1,a6,a1 *)
      destruct (tab62_check m 149216 2147469532 (w1 (t_sym st) - 257) TSH1 eq_refl ltac:(lia) eq_refl ltac:(lia)) as (b2 & RD2 & CK2).
      zs. zs. zs. rewrite sxb_sval. clear RD2.
      zs. rewrite (zx8_wrap8 (arr_get lext_a (w1 (t_sym st) - 257))) by lia.
      ck_branchJ 10 0x974d4 CK2.
      zs. rewrite (zx16_small (arr_get lbase_a (w1 (t_sym st) - 257))) by lia.
      apply evtF_done. unfold here_post. do 3 eexists.
      unfold tr_op, tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. cbv zeta. rewrite WK, ET. cbn [it_match it_extra it_base].
      destruct (Z.ltb_spec (w1 (t_sym st) + 1) 257); [lia|].
      destruct (Z.leb_spec 257 (w1 (t_sym st))); [|lia]. cbn [fst snd]. reflexivity.
    -
      replace (XFL ty) with 1 in * by (rewrite ET; reflexivity).
      pose proof (dext_range (w1 (t_sym st) - 0) ltac:(lia)) as XR. pose proof (dbase_range (w1 (t_sym st) - 0) ltac:(lia)) as BR.
      pose proof (f16ro_read_lo bsegs m A_DEXT 32 (arr_get dext_a) (w1 (t_sym st) - 0) _ (dext_bytes m MI) ltac:(lia) eq_refl) as RDX.
      change A_DEXT with 149504 in RDX.
      pose proof (dbase_read m (w1 (t_sym st) - 0) _ MI ltac:(lia) eq_refl) as RDB.
      (* [U14B] A2 2026-11-12: the 1.4 combined arm, as LENS above *)
      zs. zs. zs. ubg.
      zs. seqz0 17. zs. zs. zs. ubg.
      zs. zs. ubg.
      zs. zs. zs. ubg.
      zs. ubg.
      pose proof (tab64_check m 149504 2147469568 (w1 (t_sym st) - 0) TSH4 eq_refl ltac:(lia) eq_refl ltac:(lia)) as RD1.
      zs. zs. zs. zs. clear RD1.
      zs. zs. setreg 11 (Z_to_bv 64 (2 * (w1 (t_sym st) - 0))) ltac:(rewrite Z.mod_small by lia; rewrite shl1_2x; reflexivity).
      zs. zs.
      pose proof (tab64_check m 149408 2147469556 (w1 (t_sym st) - 0) TSH3 eq_refl ltac:(lia) eq_refl ltac:(lia)) as RD2.
      zs. zs. zs. clear RD2.
      zs. rewrite (zx8_wrap8 (arr_get dext_a (w1 (t_sym st) - 0))) by lia.
      zs.
      zs. rewrite (zx16_small (arr_get dbase_a (w1 (t_sym st) - 0))) by lia.
      apply evtF_done. unfold here_post. do 3 eexists.
      unfold tr_op, tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. cbv zeta. rewrite WK, ET. cbn [it_match it_extra it_base].
      destruct (Z.ltb_spec (w1 (t_sym st) + 1) 0); [lia|].
      destruct (Z.leb_spec 0 (w1 (t_sym st))); [|lia]. cbn [fst snd]. reflexivity.
  Qed.
End P.
End CANSEC1.
