(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U3A Require Import ItA_base ItA_ldefs ItA_switch ItA_here ItA_fill ItA_cnt2 ItA_sub.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U3A Require Import ItA_safe20.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
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
  Notation HEAD := (head_post FR fc gp tp SP SPA S F PB m1 ty lf wf lo codes nx bits).
  Notation RET1 cfx := (ret_pre SP SPA S F PB LP gp tp FR fc m1 1 lf w1 cfx (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits)).
  Notation SPU := (spure work1Ar rt nx).

  (* the 1.3.1 register homes of ALL moved to 1.4 by tools/regmap_text_gr.py (t0>a7 t1>t2 t2>t1 a7>t0) *)
  Lemma base_range : forall j, 0 <= j < NE ty -> 0 <= it_base ty work1Ar j < 65536.
  Proof.
    intros j Hj. pose proof (work1_range ty lf wf cf lo codes nx bits C j) as W.
    destruct ty; cbn [it_base NE] in *; [apply W; lia | apply lbase_range; lia | apply dbase_range; lia].
  Qed.
  Lemma ext_range : forall j, 0 <= j < NE ty -> 0 <= it_extra ty work1Ar j < 65536.
  Proof.
    intros j Hj. pose proof (work1_range ty lf wf cf lo codes nx bits C j) as W.
    destruct ty; cbn [it_extra NE] in *; [apply W; lia | apply lext_range; lia | apply dext_range; lia].
  Qed.
  Lemma opw_val_range : forall st, t_work st = work1Ar -> 0 <= tr_w st < 65536 ->
    (it_match ty <= tr_w st -> tr_w st - it_match ty < NE ty) ->
    0 <= tr_opw ty st < 65536 /\ 0 <= tr_val X st < 65536.
  Proof.
    intros st WK Fw Fwm. assert (MT : 0 <= it_match ty <= 257) by (clear; destruct ty; cbn; lia).
    unfold tr_opw, tr_val, tr_ov. cbn [x_ty itm_ctx]. cbv zeta. unfold tr_w in *. rewrite WK in Fw, Fwm. rewrite WK.
    destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [cbn [fst snd]; lia|].
    destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); cbn [fst snd]; [|lia].
    split; [apply ext_range; lia | apply base_range; lia].
  Qed.

  Definition break_post (st' : ItSt) (v0 v96 v104 v112 : word) (of : Z -> Z) : machine_state -> Prop :=
    fun ms' => exists (m : amem) (q1 q6 q10 q11 q16 q17 q25 q29 : word),
      (* 1.4 keeps the constant 1 in s9 (1.3.1: t3; 0x960cc li s9,1) *)
      ms' = MST st' q1 q6 (Z_to_bv 64 (t_len st' - t_drop st')) q10 q11 q16 q17 (Z_to_bv 64 1) q25 q29 0x96630 m   (* [P14] 1.4: the beq target *)
      /\ MINV m st' v0 v96 v104 v112 of /\ SPU st'
      /\ 0 <= t_len st' - t_drop st' <= 15 /\ 0 <= t_used st' < 65536 /\ 0 <= t_huff st' < 81920.
      (* 81920 = 65536 + 16384 (tr_huff_range); the mover had moved it as an address
         (0x14000 -> 0x13ff4 = 81908), which no huff bound proves *)

  Definition trip_post (st : ItSt) (v0 v96 v104 v112 : word) (of : Z -> Z) : machine_state -> Prop :=
    fun ms' => (exists st', it_step X st = ItCont st' /\ HEAD st' v0 v96 v104 v112 of ms' /\ SPU st')
               \/ (exists st', it_step X st = ItBreak st' /\ break_post st' v0 v96 v104 v112 of ms')
               \/ (exists st', it_step X st = ItFail st' /\ RET1 (arr_get (t_tbl st')) ms' /\ t_work st' = work1Ar).

  Lemma it_trip : forall (st : ItSt) (m : amem) (v0 v96 v104 v112 : word) (of : Z -> Z)
      (x1 x6 x7 x10 x11 x16 x17 x25 x28 : word),
    MINV m st v0 v96 v104 v112 of -> SPU st -> it_trip_ok X 288 320 1444 st = true -> 1 <= mx ->
    (* one step's CODES bound (U1A/ItA_safe20), for here's NULL-table arm *)
    it_w20 X st = true ->
    (* 1.4's loop head keeps match in t4 *)
    evtF asegs RNG (trip_post st v0 v96 v104 v112 of)
      (MST st x1 x6 x7 x10 x11 x16 x17 x25 x28 (Z_to_bv 64 (it_match ty)) 0x96280 m).
  Proof using All.
    intros until x28. intros INV HP TOK Hmx W20.
    assert (Fw20 : ty = CODES -> tr_w st < 20) by (intros ET; unfold tr_w; exact (it_w20_codes _ _ _ _ _ _ st W20 ET)).
    pose proof HP as HP'. open_spure HP'.
    pose proof TOK as TOK'. trip_facts TOK'. unbox Fwm. unbox Flook.
    pose proof (mx_range cntAr) as MXR. fold mx in MXR.
    eapply evtF_cut; [eapply (it_here RNG FR fc gp tp SP SPA S F PB top m1 ty lf wf cf lo codes nx bits CX C st m v0 v96 v104 v112 of); [exact INV | exact HP | exact Fsym | exact Fw | exact Fwm | exact Fw20]|].
    cbv beta. intros ms1 (q6 & q7 & q10 & q11 & q16 & q17 & ->).
    clear Fw20 W20.   (* [P14] used by here only; a codetype premise in the context defeats U2AShadow's lia below *)
    destruct (opw_val_range st WK Fw Fwm) as [Rop Rval].
    eapply evtF_cut; [eapply (it_fill RNG FR fc gp tp SP SPA S F PB top m1 ty lf wf cf lo codes nx bits CX C st m v0 v96 v104 v112 of);
                       [exact INV | exact TL | exact Flen | exact Fdrop | exact Fcurr | exact Fhuff | exact Fnext | exact Ffit | exact Rop | exact Rval]|].
    cbv beta. intros ms2 (m2 & r1 & r6 & r10 & r11 & r16 & r17 & r25 & r28 & r29 & -> & INV2).
    eapply evtF_cut; [eapply (it_count2 RNG FR fc gp tp SP SPA S F PB top m1 ty lf wf cf lo codes nx bits CX C st m2 v0 v96 v104 v112 of);
                       [exact INV2 | exact WK | exact Flen | exact Fhuff | exact Fsym | lia | exact HCr | exact CL | ]|].
    { intros E0 NEM. destruct (Flook E0 NEM) as (W1 & W2 & W3 & W4). rewrite WK in W2, W3, W4. rewrite lensA_get in W4. repeat split; lia. }
    cbv beta. intros ms3 [(m3 & s1 & s6 & s10 & s11 & s16 & s17 & s28 & -> & INV3 & Hbrk) | (m3 & s1 & s6 & s10 & s11 & s16 & s17 & s28 & -> & INV3 & Hbrk)].
    -
      eapply evtF_mono; [eapply (it_sub RNG FR fc gp tp SP SPA S F PB top m1 ty lf wf cf lo codes nx bits CX C st m3 v0 v96 v104 v112 of);
                         [exact INV3 | exact HP | exact TOK | exact Hbrk | exact Hmx]|].
      cbv beta. intros ms4 [[HH Hsub] | [[(HH & Hne & HSP3) | (HR & Hne)] Hsub]].
      + left. exists (tr_st1 X st). split; [rewrite it_step_eq, Hbrk, Hsub; reflexivity|]. split; [exact HH | apply spure_st1; exact HP].
      + left. exists (tr_st3 X st). split; [rewrite it_step_eq, Hbrk, Hsub; cbn [x_ty itm_ctx]; rewrite Hne; reflexivity|]. split; [exact HH | exact HSP3].
      + right. right. exists (tr_st2 X st). split; [rewrite it_step_eq, Hbrk, Hsub; cbn [x_ty itm_ctx]; rewrite Hne; reflexivity|].
        cbn [t_tbl t_work tr_st2]. split; [exact HR | exact WK].
    -
      apply evtF_done. right. left. exists (tr_st1 X st). split; [rewrite it_step_eq, Hbrk; reflexivity|].
      assert (EL : tr_len X st = t_len st).
      { unfold tr_brk in Hbrk. apply andb_prop in Hbrk as [B1 B2]. unfold tr_len. rewrite B1.
        cbn [x_max itm_ctx] in *. rewrite B2. reflexivity. }
      pose proof (tr_huff_range st Flen Fhuff) as HHF.
      unfold break_post. exists m3. do 8 eexists. cbn [t_len t_drop t_used t_huff tr_st1]. rewrite EL.
      split; [unfold mst; cbn [t_len t_drop t_huff t_next t_sym tr_st1]; rewrite EL; reflexivity|].
      split; [exact INV3|]. split; [apply spure_st1; exact HP|]. lia.
  Qed.

  Definition loop_post (n : Z) (st : ItSt) (v0 v96 v104 v112 : word) (of : Z -> Z) : machine_state -> Prop :=
    fun ms' => (exists st', it_loop_n X n st = inl st' /\ break_post st' v0 v96 v104 v112 of ms'
                            /\ (t_huff st' <> 0 -> 0 <= t_next st' + t_huff st' < 1444))
               \/ (exists st', it_loop_n X n st = inr st' /\ RET1 (arr_get (t_tbl st')) ms' /\ t_work st' = work1Ar).

  Lemma it_main_loop : forall (k : nat) (st : ItSt) (m : amem) (v0 v96 v104 v112 : word) (of : Z -> Z)
      (x1 x6 x7 x10 x11 x16 x17 x25 x28 : word),
    it_loop_ok k X 288 320 1444 st = true -> 1 <= mx ->
    (* the loop's CODES bound (U1A/ItA_safe20) *)
    it_loop20 k X st = true ->
    MINV m st v0 v96 v104 v112 of -> SPU st ->
    evtF asegs RNG (loop_post (Z.of_nat k) st v0 v96 v104 v112 of)
      (MST st x1 x6 x7 x10 x11 x16 x17 x25 x28 (Z_to_bv 64 (it_match ty)) 0x96280 m).
  Proof using All.
    induction k as [|k IH]; intros st m v0 v96 v104 v112 of x1 x6 x7 x10 x11 x16 x17 x25 x28 HOK Hmx H20 INV HP.
    { cbn [it_loop_ok] in HOK. discriminate. }
    rewrite it_loop_ok_S in HOK. apply andb_prop in HOK as [TOK REST].
    rewrite it_loop20_S in H20. apply andb_prop in H20 as [W20 REST20].
    eapply evtF_cut; [eapply (it_trip st m v0 v96 v104 v112 of); [exact INV | exact HP | exact TOK | exact Hmx | exact W20]|].
    cbv beta. intros ms1 [(st' & Hstep & HH & HSP) | [(st' & Hstep & HB) | (st' & Hstep & HR & HW)]].
    - destruct HH as (m' & q1 & q6 & q7 & q10 & q11 & q16 & q17 & q25 & q28 & -> & INV'). rewrite Hstep in REST, REST20.
      eapply evtF_mono; [eapply (IH st' m' v0 v96 v104 v112 of); [exact REST | exact Hmx | exact REST20 | exact INV' | exact HSP]|].
      cbv beta. intros ms2 [(st'' & Hl & HB2) | (st'' & Hl & HR2)].
      + left. exists st''. split; [|exact HB2]. rewrite it_loop_n_step by lia. rewrite Hstep.
        replace (Z.of_nat (Datatypes.S k) - 1) with (Z.of_nat k) by lia. exact Hl.
      + right. exists st''. split; [|exact HR2]. rewrite it_loop_n_step by lia. rewrite Hstep.
        replace (Z.of_nat (Datatypes.S k) - 1) with (Z.of_nat k) by lia. exact Hl.
    - apply evtF_done. left. exists st'. rewrite Hstep in REST.
      split; [rewrite it_loop_n_step by lia; rewrite Hstep; reflexivity|]. split; [exact HB|].
      intros Hne. destruct (Z.eqb_spec (t_huff st') 0); [lia|]. cbn [negb] in REST.
      apply andb_prop in REST as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
    - apply evtF_done. right. exists st'. split; [rewrite it_loop_n_step by lia; rewrite Hstep; reflexivity|]. split; [exact HR | exact HW].
  Qed.
End P.
End CANSEC1.
