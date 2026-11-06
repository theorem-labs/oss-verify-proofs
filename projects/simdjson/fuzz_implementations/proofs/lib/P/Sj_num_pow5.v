(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_num_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition P5_ENTRY : Z := 0x56728.
Definition LM_ENTRY : Z := 0x56884.
Definition NUM_GTOP : Z := 0x10b000.
Definition lm_stmt : Prop := lm_stmt_g psegs LM_ENTRY.

Section POW5.
  Hypothesis HLM : lm_stmt.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Hypothesis ROOM : (lo + P5_STACK <= SP)%Z.
  Hypothesis GTOP : (NUM_GTOP <= lo)%Z.
  Hypothesis XHI : (SP <= X)%Z.

  Notation W := [(SP - P5_STACK, SP); (X, X + 498)]%Z.
  Notation POST := (p5_post_g psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m0).

  Notation P5 pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 (SP + -48)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3
             s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  Definition P5INV (mm : mem) (len : Z) : Prop :=
    (exists j, rw_cells psegs mm (SP + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
    (exists ws, u64arr psegs mm X ws /\ length ws = 62%nat) /\
    rw_cells psegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    mem_inv psegs mm /\ munch W m0 mm /\ wmono psegs m0 mm /\ stk psegs mm lo (SP + -48).

  Ltac p5_open H :=
    let j := fresh "j" in let ws := fresh "ws" in
    destruct H as ((j & FR) & (ws & XA & XL) & XN & LEN & MI & MU & WM & ST).
  Ltac p5_forget := repeat match goal with
    | H : rw_cells _ _ _ _ |- _ => clear H | H : u64arr _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
    | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H
    | H : length _ = 62%nat |- _ => clear H | H : (0 <= _ <= 62)%Z |- _ => clear H
    | H : (0 <= _ /\ _ + 8 * Z.of_nat 62 <= 2 ^ 64)%Z |- _ => clear H end.
  Ltac p5_close :=
    lazymatch goal with
    | |- P5INV _ _ =>
        split; [eexists; eassumption|]; split; [eexists; split; [eassumption| rewrite ?upd_length; assumption]|];
        split; [eassumption|]; split; [lia|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
    end.

  Lemma p5_exit : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    P5INV mm len ->
    evt psegs POST (P5 0x56868 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI.
    intros until len. intros INV. p5_open INV.
    unfold P5_STACK, LM_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    do 5 zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold p5_post_g. do 15 eexists. exists mm, ws, len.
    split; [cbv delta [mkR]; reflexivity|].
    unfold P5_STACK, LM_STACK, bigint_at.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [split; [exact XA| split; [exact XL| split; [exact XN| exact LEN]]] | exact ST].
  Qed.

  Lemma p5_mulA : forall (Q : machine_state -> Prop) (f : nat) (i n : Z) xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa5 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm,
    P5INV mm n -> (0 <= i < n)%Z -> (n - i <= Z.of_nat f)%Z ->
    (forall xt0' xa5' xa6' xa7' mm', P5INV mm' n ->
       evt psegs Q (P5 0x567d8 xra xt0' xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xa1 xa2 xa3 (Z_to_bv 64 (X + 8 * n)) xa5' xa6' xa7' xs2 xs3 xt3 xt4 xt5 xt6 mm')) ->
    evt psegs Q (P5 0x567b4 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xa1 xa2 xa3 (Z_to_bv 64 (X + 8 * n)) xa5 (Z_to_bv 64 (X + 8 * i)) xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI.
    intros Q f. induction f as [|f IH]; intros i n xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa5 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm INV Hi Hf HK; [exfalso; lia|].
    p5_open INV. unfold P5_STACK, LM_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (u64arr_bound _ _ _ _ XA) as XB. rewrite XL in XB.
    u64_read XA i w.
    zstep. zstep. zstep. zstep. zstep.
    u64_store XA i.
    zstep. zstep. zstep.
    if_cases K; zify_cond K.
    -
      eapply evt_eq; [| eapply (IH (i + 1)%Z n); [p5_close | lia | lia | exact HK]].
      num_st_eq.
    - apply HK. p5_close.
  Qed.

  Lemma p5_mulB : forall (Q : machine_state -> Prop) (f : nat) (i n : Z) xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa4 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm,
    P5INV mm n -> (0 <= i < n)%Z -> (n - i <= Z.of_nat f)%Z ->
    (forall xa2' xa5' xa6' xa7' mm', P5INV mm' n ->
       evt psegs Q (P5 0x56848 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xa1 xa2' (Z_to_bv 64 (X + 8 * n)) xa4 xa5' xa6' xa7' xs2 xs3 xt3 xt4 xt5 xt6 mm')) ->
    evt psegs Q (P5 0x56824 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xa1 xa2 (Z_to_bv 64 (X + 8 * n)) xa4 (Z_to_bv 64 (X + 8 * i)) xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI.
    intros Q f. induction f as [|f IH]; intros i n xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa4 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm INV Hi Hf HK; [exfalso; lia|].
    p5_open INV. unfold P5_STACK, LM_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (u64arr_bound _ _ _ _ XA) as XB. rewrite XL in XB.
    u64_read XA i w.
    zstep. zstep. zstep. zstep. zstep.
    u64_store XA i.
    zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - eapply evt_eq; [| eapply (IH (i + 1)%Z n); [p5_close | lia | lia | exact HK]].
      num_st_eq.
    - apply HK. p5_close.
  Qed.

  Lemma p5_false : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    P5INV mm len ->
    evt psegs POST (P5 0x56864 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI. intros. zstep. eapply p5_exit. eassumption. Qed.

  Lemma p5_tail : forall (e n : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm,
    P5INV mm n -> (0 <= e < 27)%Z ->
    evt psegs POST (P5 0x567f0 xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI GTOP.
    intros until mm. intros INV He.
    pose proof INV as INV0.
    p5_open INV. unfold P5_STACK, LM_STACK, NUM_GTOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (u64arr_bound _ _ _ _ XA) as XB. rewrite XL in XB.
    zstep. zstep.
    if_cases K0; zify_cond K0.
    { eapply p5_exit. exact INV0. }
    zstep. rewrite zx16_small by lia. zstep.
    if_cases K1; zify_cond K1.
    { eapply p5_exit. exact INV0. }
    destruct (image_readable_b psegs mm 224 0x1d698 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (tb & TL & TB).
    destruct (bytes_u64_read psegs mm 0x1d698 tb (8 * e) TB ltac:(lia) ltac:(rewrite TL; lia)) as [pw RDT].
    zstep. zstep. nnorm. zstep. zstep. zstep. zstep.
    clear RDT TB TL tb.
    zstep. nnorm. zstep. zstep.
    eapply evt_eq; [| eapply (p5_mulB POST (Z.to_nat n) 0 n); [exact INV0 | lia | lia |]]; [num_st_eq|].
    p5_forget. clear INV0. intros xa2' xa5' xa6' xa7' mm1 INV.
    pose proof INV as INV0.
    p5_open INV.
    pose proof (u64arr_bound _ _ _ _ XA) as XB. rewrite XL in XB.
    zstep.
    if_cases K2; zify_cond K2.
    { eapply p5_exit. exact INV0. }
    zstep. zstep.
    if_cases K3; zify_cond K3.
    { eapply p5_false. exact INV0. }
    u64_store XA n.
    zstep. zstep. zstep.
    eapply p5_exit with (len := (n + 1)%Z). p5_close.
  Qed.

  Lemma p5_L2 : forall (f : nat) (e n : Z) xra xt0 xt1 xt2 xa0 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm,
    P5INV mm n -> (27 <= e < 2147483648)%Z -> (e <= 27 * Z.of_nat f)%Z ->
    evt psegs POST (P5 0x567a0 xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) xa0 (Z_to_bv 64 n) (Z_to_bv 64 26) (Z_to_bv 64 61)
                       xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI GTOP.
    intros f. induction f as [|f IH]; intros e n xra xt0 xt1 xt2 xa0 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm INV He Hf; [exfalso; lia|].
    assert (KBOT : forall xt0' xa4' xa5' xa6' xa7' n' mm', P5INV mm' n' ->
              evt psegs POST (P5 0x56798 xra xt0' xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) xa0 (Z_to_bv 64 n') (Z_to_bv 64 26) (Z_to_bv 64 61)
                                 xa4' xa5' xa6' xa7' xs2 xs3 xt3 xt4 xt5 xt6 mm')).
    { intros xt0' xa4' xa5' xa6' xa7' n' mm' INV'.
      zstep. rewrite swrap32_id by lia. zstep.
      if_cases K; zify_cond K.
      - eapply p5_tail; [exact INV'| lia].
      - eapply IH; [exact INV' | lia | lia]. }
    pose proof INV as INV0.
    p5_open INV. unfold P5_STACK, LM_STACK, NUM_GTOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (u64arr_bound _ _ _ _ XA) as XB. rewrite XL in XB.
    zstep.
    if_cases K0; zify_cond K0.
    { eapply KBOT. exact INV0. }
    zstep. zstep. nnorm. zstep. zstep.
    eapply evt_eq; [| eapply (p5_mulA POST (Z.to_nat n) 0 n); [exact INV0 | lia | lia |]]; [num_st_eq|].
    p5_forget. clear INV0. intros xt0' xa5' xa6' xa7' mm1 INV.
    pose proof INV as INV0.
    p5_open INV.
    pose proof (u64arr_bound _ _ _ _ XA) as XB. rewrite XL in XB.
    zstep.
    if_cases K2; zify_cond K2.
    { eapply KBOT. exact INV0. }
    zstep.
    if_cases K3; zify_cond K3.
    { eapply p5_false. exact INV0. }
    u64_store XA n.
    zstep. zstep. zstep.
    eapply KBOT with (n' := (n + 1)%Z). p5_close.
  Qed.

  Lemma p5_mid : forall (e n : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm,
    P5INV mm n -> (0 <= e < 135)%Z ->
    evt psegs POST (P5 0x56778 xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI GTOP.
    intros until mm. intros INV He.
    pose proof INV as INV0.
    p5_open INV. unfold P5_STACK, LM_STACK, NUM_GTOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    zstep. zstep.
    if_cases K; zify_cond K.
    { eapply p5_tail; [exact INV0| lia]. }
    zstep. nnorm. zstep. zstep. zstep. zstep. zstep.
    eapply (p5_L2 5); [exact INV0 | lia | lia].
  Qed.

  Lemma p5_L1 : forall (f : nat) (e n : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm,
    P5INV mm n -> (-2147483648 <= e < 2147483648)%Z -> (e < 0 \/ 135 <= e)%Z -> (e mod 4294967296 <= 135 * Z.of_nat f)%Z ->
    evt psegs POST (P5 0x5675c xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 0x1d670) (Z_to_bv 64 134) xt3 xt4 xt5 xt6 mm).
  Proof using HLM ROOM XHI GTOP.
    intros f. induction f as [|f IH]; intros e n xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm INV He Hout Hf.
    { exfalso. lia. }
    p5_open INV. unfold P5_STACK, LM_STACK, NUM_GTOP in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct (image_readable_b psegs mm 40 0x1d670 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (yb & YL & YB).
    zstep. zstep. zstep. zstep.
    pose proof HLM as HM. unfold lm_stmt, lm_stmt_g in HM.
    eapply evt_cut.
    { eapply HM with (X := X) (Y := 0x1d670%Z) (ny := 5%Z) (lo := lo) (ws := ws) (len := n) (ybs := yb);
        rewrite ?unsigned_lit by lia; unfold LM_STACK;
        [ exact MI | exact ST | lia | unfold bigint_at; split; [exact XA| split; [exact XL| split; [exact XN| exact LEN]]] | lia
        | exact YB | rewrite YL; reflexivity | lia ]. }
    cbv beta. intros ms' P. unfold lm_post_g in P.
    destruct P as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3 & ws3 & len3
                   & -> & MUc & WMc & MIc & BIG & STc).
    rewrite !unsigned_lit in MUc, STc by lia. unfold LM_STACK in MUc.
    transport_after_call psegs mm m3 MUc WMc.
    clear MUc WMc MI HM YB. destruct BIG as (XA3 & XL3 & XN3 & LEN3).
    replace (ret_pc (Z_to_bv 64 354156)) with (Z_to_bv 64 354156) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear XL LEN ws.
    assert (INV3 : P5INV m3 len3).
    { split; [eexists; eassumption|]. split; [eexists; split; eassumption|]. split; [eassumption|]. split; [lia|].
      split; [eassumption|]. split; [eassumption|]. split; eassumption. }
    zstep.
    if_cases K0.
    { eapply p5_exit. exact INV3. }
    clear K0.
    zstep. rewrite bv_swrap32, swrap32_mod64.
    replace (e + -135)%Z with (e - 135)%Z by lia.
    pose proof (pow5_large_step e He Hout) as [STEP GE].
    pose proof (swrap32_range (e - 135)) as ER.
    set (e' := swrap32 (e - 135)) in *. clearbody e'.
    zstep.
    if_cases K; zify_cond K.
    - apply (s32_gtu e' 134 ER ltac:(lia)) in K.
      eapply IH; [exact INV3 | exact ER | lia | lia].
    - assert (K' : (0 <= e' <= 134)%Z) by (apply (s32_leu e' 134 ER ltac:(lia)); lia).
      eapply p5_mid; [exact INV3 | lia].
  Qed.

  Lemma p5_body : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (e : Z) ws len,
    mem_inv psegs m0 -> stk psegs m0 lo SP -> bigint_at psegs m0 X ws len ->
    (-2147483648 <= e < 2147483648)%Z ->
    evt psegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 P5_ENTRY) fc None m0 (seg_rom psegs)).
  Proof using HLM ROOM XHI GTOP.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 e ws len MI ST (XA & XL & XN & LEN) He.
    unfold P5_ENTRY.
    pose proof ROOM as ROOM'. unfold P5_STACK, LM_STACK in ROOM'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl psegs m0) as WM. unfold P5_STACK, LM_STACK in MU.
    set (m := m0) in MI, ST, XA, XN, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 48%nat ST.
    apply (rw_cells_split_CB psegs m _ [] 48 junk [] [8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 5 step. zstep. zstep. zstep. zstep.
    num_cur_mem ltac:(fun mm => assert (INV : P5INV mm len) by p5_close).
    if_cases K; zify_cond K.
    - assert (K' : (0 <= e <= 134)%Z) by (apply (s32_leu e 134 He ltac:(lia)); lia).
      eapply p5_mid; [exact INV | lia].
    - zstep. zstep. zstep.
      eapply (p5_L1 (Z.to_nat (e mod 4294967296))); [exact INV | exact He | | ].
      + assert (K' : (134 < e mod 18446744073709551616)%Z) by lia. apply (s32_gtu e 134 He ltac:(lia)) in K'. lia.
      + pose proof (Z.mod_pos_bound e 4294967296 ltac:(lia)). lia.
  Qed.
End POW5.

Theorem p5_spec : lm_stmt -> p5_stmt_g psegs P5_ENTRY NUM_GTOP.
Proof.
  intros HLM. unfold p5_stmt_g. intros until len. intros MI ST ROOM GTOP BIG XHI He.
  eapply p5_body; eassumption.
Qed.
