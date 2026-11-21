(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure UbFit2.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import ItBTac ItB_base ItB_ldefs ItB_switch ItB_here ItB_fill ItB_cnt2 ItB_sub.
(* [U14B] A2 2026-11-12: the CODES bound of zlib 1.4's table loop (NEW text, the U3B twin of G's U1A/ItA_safe20) *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import ItB_safe20.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
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
  Notation BST := (bst SP SPA S F PB LP (cty ty) gp tp FR fc).
  Notation MST := (mst SP SPA S F PB LP (cty ty) gp tp FR fc rt mx).
  Notation MINV := (fun m st => minv SPA S F PB m1 m ty rt nx bits lf w1 st).
  Notation SHPB := (Z_to_bv 64 (Z.shiftr PB 3 + 2147450880)).
  Notation HEAD := (head_post FR fc gp tp SP SPA S F PB m1 ty lf wf lo codes nx bits).
  Notation RET1 cfx := (ret_pre SP SPA S F PB LP (cty ty) gp tp FR fc m1 1 lf w1 cfx (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits)).
  Notation SPU := (spure work1Ar rt nx).

  Lemma base_range : forall j, 0 <= j < NE ty -> 0 <= it_base ty work1Ar j < 65536.
  Proof.
    intros j Hj. pose proof (work1_range ty lf wf cf lo codes nx bits C j) as W.
    destruct ty; cbn [it_base NE] in *; [apply W; lia | apply lbase_range; lia | apply dbase_range; lia].
  Qed.
  Lemma op_val_range : forall st, t_work st = work1Ar -> 0 <= tr_w st < 65536 ->
    (it_match ty <= tr_w st -> tr_w st - it_match ty < NE ty) ->
    0 <= tr_op X st < 256 /\ 0 <= tr_val X st < 65536.
  Proof.
    intros st WK Fw Fwm. assert (MT : 0 <= it_match ty <= 257) by (clear; destruct ty; cbn; lia).
    unfold tr_op, tr_val, tr_ov. cbn [x_ty itm_ctx]. cbv zeta. unfold tr_w in *. rewrite WK in Fw, Fwm. rewrite WK.
    destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [cbn [fst snd]; lia|].
    destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); cbn [fst snd]; [|lia].
    split; [rewrite wrap8_mod; apply Z.mod_pos_bound; lia | apply base_range; lia].
  Qed.

  Definition break_post (st' : ItSt) (v0 v8 v16 v128 v136 : word) (of : Z -> Z) : machine_state -> Prop :=
    fun ms' => exists (m : amem) (q5 q6 q7 q10 q11 q12 q16 q17 q25 q29 q30 q31 : word),
      (* [U14B] A2 2026-11-12: huff is in t4 (x29) at 1.4 (1.3.1 t3 = x28).  The bound is 81920 = 65536 + 16384
         (tr_huff_range), as at 1.3.1: the mover had moved it as an address (0x14000 -> 0x13ff4 = 81908; G's U1A note). *)
      ms' = BST (Z_to_bv 64 (S + 1384 + 4 * t_next st')) q5 q6 q7 q10 q11 q12 SHPB (Z_to_bv 64 rt) (Z_to_bv 64 mx) q16 q17 q25
                q29 (Z_to_bv 64 (t_huff st')) q30 q31 0x979b8 m
      /\ MINV m st' v0 v8 v16 (Z_to_bv 64 (Z.shiftl (t_len st' - t_drop st') 8)) v128 v136 of /\ SPU st'
      /\ 0 <= t_len st' - t_drop st' <= 15 /\ 0 <= t_used st' < 65536 /\ 0 <= t_huff st' < 81920.

  Definition trip_post (st : ItSt) (v0 v8 v16 v128 v136 : word) (of : Z -> Z) : machine_state -> Prop :=
    fun ms' => (exists st', it_step X st = ItCont st' /\ HEAD st' v0 v8 v16 v128 v136 of ms' /\ SPU st')
               \/ (exists st', it_step X st = ItBreak st' /\ break_post st' v0 v8 v16 v128 v136 of ms')
               \/ (exists st', it_step X st = ItFail st' /\ RET1 (arr_get (t_tbl st')) ms' /\ t_work st' = work1Ar).

  Lemma it_trip : forall (st : ItSt) (m : amem) (v0 v8 v16 v56 v128 v136 : word) (of : Z -> Z)
      (x5 x6 x7 x11 x16 x29 x30 x31 : word),
    MINV m st v0 v8 v16 v56 v128 v136 of -> SPU st -> it_trip_ok X 288 320 1444 st = true -> 1 <= mx ->
    (* [U14B] A2 2026-11-12: one step's CODES bound (U3B/ItB_safe20), for here's null-table arm (G's U1A cure C48) *)
    it_w20 X st = true ->
    evtF bsegs RNG (trip_post st v0 v8 v16 v128 v136 of)
      (MST st x5 x6 x7 x11 x16 x29 x30 x31 0x9750c m).
  Proof using All.
    intros until x31. intros INV HP TOK Hmx W20.
    assert (Fw20 : ty = CODES -> tr_w st < 20) by (intros ET; unfold tr_w; exact (it_w20_codes _ _ _ _ _ _ st W20 ET)).
    pose proof HP as HP'. open_spure HP'.
    pose proof TOK as TOK'. trip_facts TOK'. unbox Fwm. unbox Flook.
    pose proof (mx_range cntAr) as MXR. fold mx in MXR.
    eapply evtF_cut; [eapply (it_here RNG FR fc gp tp SP SPA S F PB top m1 ty lf wf cf lo codes nx bits CX C st m v0 v8 v16 v56 v128 v136 of); [exact INV | exact HP | exact Fsym | exact Fw | exact Fwm | exact Fw20]|].
    clear Fw20 W20.   (* used by here only; a codetype premise in the context defeats lia below (G's U1A note) *)
    cbv beta. intros ms1 (q5 & q11 & q16 & ->).
    destruct (op_val_range st WK Fw Fwm) as [Rop Rval].
    eapply evtF_cut; [eapply (it_fill RNG FR fc gp tp SP SPA S F PB top m1 ty lf wf cf lo codes nx bits CX C st m v0 v8 v16 v56 v128 v136 of);
                       [exact INV | exact TL | exact Flen | exact Fdrop | exact Fcurr | exact Fhuff | exact Fnext | exact Ffit | exact Rop | exact Rval]|].
    cbv beta. intros ms2 (m2 & r6 & r11 & r7 & r10 & r12 & r16 & -> & INV2).
    unfold FST.
    eapply evtF_cut; [eapply (it_count2 RNG FR fc gp tp SP SPA S F PB top m1 ty lf wf cf lo codes nx bits CX C st m2 v0 v8 v16 (Z_to_bv 64 (Z.shiftl (tr_hb st) 8)) v128 v136 of);
                       [exact INV2 | exact WK | exact Flen | exact Fhuff | exact Fsym | lia | exact HCr | exact CL | ]|].
    { intros E0 NEM. destruct (Flook E0 NEM) as (W1 & W2 & W3 & W4). rewrite WK in W2, W3, W4. rewrite lensA_get in W4. repeat split; lia. }
    cbv beta. intros ms3 [(m3 & s6 & s7 & s10 & s11 & s12 & s16 & s30 & s31 & -> & INV3 & Hbrk) | (m3 & s6 & s7 & s10 & s11 & s12 & s16 & s30 & s31 & -> & INV3 & Hbrk)].
    -
      unfold C2ST.
      eapply evtF_mono; [eapply (it_sub RNG FR fc gp tp SP SPA S F PB top m1 ty lf wf cf lo codes nx bits CX C st m3 v0 v8 v16 (Z_to_bv 64 (Z.shiftl (tr_hb st) 8)) v128 v136 of);
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
      unfold break_post. exists m3. do 12 eexists. cbn [t_len t_drop t_used t_huff t_next tr_st1]. rewrite EL.
      split; [unfold C2ST; reflexivity|].
      split; [exact INV3|]. split; [apply spure_st1; exact HP|]. lia.
  Qed.

  Definition loop_post (n : Z) (st : ItSt) (v0 v8 v16 v128 v136 : word) (of : Z -> Z) : machine_state -> Prop :=
    fun ms' => (exists st', it_loop_n X n st = inl st' /\ break_post st' v0 v8 v16 v128 v136 of ms'
                            /\ (t_huff st' <> 0 -> 0 <= t_next st' + t_huff st' < 1444))
               \/ (exists st', it_loop_n X n st = inr st' /\ RET1 (arr_get (t_tbl st')) ms' /\ t_work st' = work1Ar).

  Lemma it_main_loop : forall (k : nat) (st : ItSt) (m : amem) (v0 v8 v16 v56 v128 v136 : word) (of : Z -> Z)
      (x5 x6 x7 x11 x16 x29 x30 x31 : word),
    it_loop_ok k X 288 320 1444 st = true -> 1 <= mx ->
    (* [U14B] A2 2026-11-12: the loop's CODES bound (U3B/ItB_safe20) *)
    it_loop20 k X st = true ->
    MINV m st v0 v8 v16 v56 v128 v136 of -> SPU st ->
    evtF bsegs RNG (loop_post (Z.of_nat k) st v0 v8 v16 v128 v136 of)
      (MST st x5 x6 x7 x11 x16 x29 x30 x31 0x9750c m).
  Proof using All.
    induction k as [|k IH]; intros st m v0 v8 v16 v56 v128 v136 of x5 x6 x7 x11 x16 x29 x30 x31 HOK Hmx H20 INV HP.
    { cbn [it_loop_ok] in HOK. discriminate. }
    rewrite it_loop_ok_S in HOK. apply andb_prop in HOK as [TOK REST].
    rewrite it_loop20_S in H20. apply andb_prop in H20 as [W20 REST20].
    eapply evtF_cut; [eapply (it_trip st m v0 v8 v16 v56 v128 v136 of); [exact INV | exact HP | exact TOK | exact Hmx | exact W20]|].
    cbv beta. intros ms1 [(st' & Hstep & HH & HSP) | [(st' & Hstep & HB) | (st' & Hstep & HR & HW)]].
    - destruct HH as (m' & q5 & q6 & q7 & q11 & q16 & q29 & q30 & q31 & u56 & -> & INV'). rewrite Hstep in REST, REST20.
      eapply evtF_mono; [eapply (IH st' m' v0 v8 v16 u56 v128 v136 of); [exact REST | exact Hmx | exact REST20 | exact INV' | exact HSP]|].
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
