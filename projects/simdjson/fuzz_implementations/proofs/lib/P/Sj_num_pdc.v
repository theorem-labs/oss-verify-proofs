(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_num_kit Sj_num_walk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Definition PDC_ENTRY : Z := 0x55ff8.
Definition PDC_GTOP : Z := 0x10b000.
Definition pdc_p5_stmt : Prop := p5_stmt_g psegs 0x56728 PDC_GTOP.
Definition pdc_memmove_stmt : Prop := memmove_stmt_g psegs 0xca990.
Definition pdc_memset_stmt : Prop := memsetZ_stmt_g psegs 0xcab0c.

Section PDC.
  Hypothesis HP5 : pdc_p5_stmt.
  Hypothesis HMOVE : pdc_memmove_stmt.
  Hypothesis HSET : pdc_memset_stmt.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Hypothesis ROOM : (lo + PDC_STACK <= SP)%Z.
  Hypothesis GTOP : (PDC_GTOP <= lo)%Z.
  Hypothesis XHI : (SP <= X)%Z.

  Notation W := [(SP - PDC_STACK, SP); (X, X + 498)]%Z.
  Notation POST := (pdc_post_g psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m0).
  Notation PD pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 (SP + -32)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2
             s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  Definition PDINV (mm : mem) (len : Z) : Prop :=
    rw_cells psegs mm (SP + -32) [C8 s2; C8 s1; C8 s0; C8 ra] /\
    (exists bs, u8arr psegs mm X bs /\ length bs = 496%nat) /\
    rw_cells psegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    mem_inv psegs mm /\ munch W m0 mm /\ wmono psegs m0 mm /\ stk psegs mm lo (SP + -32).

  Ltac pd_open H :=
    let bs := fresh "bs" in
    destruct H as (FR & (bs & XA & ?XL) & XN & ?LEN & MI & MU & WM & ST); unfold PDC_STACK, P5_STACK, LM_STACK in MU.
  Ltac pd_close :=
    lazymatch goal with
    | |- PDINV _ _ =>
        split; [eassumption|]; split; [eexists; split; [eassumption| lia]|]; split; [eassumption|]; split; [lia|];
        split; [eassumption|]; split; [eassumption|]; split; eassumption
    end.
  Ltac pd_env :=
    pose proof ROOM as ROOM'; pose proof GTOP as GTOP'; unfold PDC_STACK, P5_STACK, LM_STACK, PDC_GTOP in ROOM', GTOP';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR.

  Lemma pd_exit : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mm len,
    PDINV mm len ->
    evt psegs POST (PD 0x56344 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI GTOP.
    intros until len. intros INV. pd_open INV. pd_env.
    do 4 zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    destruct (u64arr_of_u8arr psegs mm X bs XA XL) as (ws & WL & WA).
    apply evt_done. unfold pdc_post_g. do 15 eexists. exists mm, ws, len.
    split; [cbv delta [mkR]; reflexivity|].
    unfold PDC_STACK, P5_STACK, LM_STACK, bigint_at.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [split; [exact WA| split; [exact WL| split; [exact XN| lia]]] | exact ST].
  Qed.

  Lemma pd_nz : forall (f : nat) (k : Z) xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mm len,
    PDINV mm len -> (0 <= k <= 59)%Z -> (k <= Z.of_nat f)%Z ->
    evt psegs POST (PD 0x56298 xra xt0 xt1 xt2 (Z_to_bv 64 (X + 8 * k)) xs1 xa0 xa1 xa2 xa3 (Z_to_bv 64 k) xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI GTOP.
    intros f. induction f as [|f IH]; intros until len; intros INV Hk Hf.
    - pose proof INV as INV0. pd_open INV. pd_env. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x56344%Z => first [ eapply pd_exit; exact INV0 | fail 100 "cut" pc ]
        end).
    - pose proof INV as INV0. pd_open INV. pd_env. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x56344%Z => first [ eapply pd_exit; exact INV0 | fail 100 "cut" pc ]
        | 0x56298%Z => first [ eapply evt_eq; [| eapply (IH (k - 1)%Z)]; [num_st_eq | exact INV0 | lia | lia] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma pd_hi64 : forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mm len,
    PDINV mm len ->
    evt psegs POST (PD 0x560d0 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI GTOP.
    intros until len. intros INV.
    pose proof INV as INV0. pd_open INV. pd_env.
    walk ltac:(fun pc => lazymatch pc with
      | 0x56344%Z => first [ eapply pd_exit; exact INV0 | fail 100 "cut" pc ]
      | 0x56298%Z => first [ eapply evt_eq; [| eapply (pd_nz 62 (len - 3)%Z)]; [num_st_eq | exact INV0 | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pd_80c : forall (e : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mm len,
    PDINV mm len -> (-2147483648 <= e < 2147483648)%Z ->
    evt psegs POST (PD 0x56080 xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mm).
  Proof using HMOVE HSET ROOM XHI GTOP.
    intros until len. intros INV He.
    pose proof INV as INV0. pd_open INV. pd_env.
    walk ltac:(fun pc => lazymatch pc with
      | 0x560d0%Z => first [ eapply pd_hi64; exact INV0 | fail 100 "cut" pc ]
      | 0xca990%Z => idtac
      end).

    set (d := Z.shiftr (bv_wrap 32 (e mod 18446744073709551616)) 6) in *.
    assert (Hd : (0 <= d < 67108864)%Z) by (unfold d, bv_wrap, bv_modulus; apply srliw6_range).
    rewrite (swrap32_id d) in * by lia.
    rewrite (Z.mod_small (d + len)) in * by lia.
    pose proof (u8arr_bound _ _ _ _ XA) as XB. rewrite XL in XB.
    pose proof HMOVE as HM. unfold pdc_memmove_stmt, memmove_stmt_g in HM.
    eapply evt_cut.
    { eapply evt_eq; [| eapply HM with (D := (X + 8 * d)%Z) (S := X) (N := (8 * len)%Z) (U := X) (bs := bs);
                        [exact XA | lia | lia | lia | lia | | exact MI]]; [num_st_eq|].
      replace (X + 8 * d - X)%Z with (d * 8)%Z by lia. apply Z.mod_mul. lia. }
    cbv beta. intros ms' P. unfold memmove_post_g in P.
    destruct P as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3 & bs3 & -> & MUc & WMc & MIc & XA3 & XL3).
    clear XA.
    transport_after_call psegs mm m3 MUc WMc.
    clear MUc WMc MI HM. rewrite XL in XL3.
    replace (ret_pc (Z_to_bv 64 352436)) with (Z_to_bv 64 352436) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep. zstep. zstep. zstep.
    destruct (u8arr_range_split psegs m3 X bs3 0 (Z.to_nat (8 * d)) XA3 ltac:(lia) ltac:(lia))
      as (b1 & mid & b3 & L1 & LMID & L3 & U1 & MID & U3).
    clear XA3.
    replace (X + Z.of_nat 0)%Z with X in MID by lia.
    replace (Z.to_nat (8 * d) - 0)%nat with (Z.to_nat (8 * d)) in MID by lia.
    pose proof HSET as HS. unfold pdc_memset_stmt, memsetZ_stmt_g in HS.
    eapply evt_cut.
    { eapply evt_eq; [| eapply HS with (D := X) (C := 0%Z) (N := (8 * d)%Z) (junk := mid); [exact MID | exact MIc | lia | lia | lia | lia]].
      num_st_eq. }
    cbv beta. intros ms' P. unfold memsetZ_post_g in P.
    destruct P as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m4 & -> & MUc & WMc & MI4 & DSTc).
    transport_after_call psegs m3 m4 MUc WMc.
    clear MUc WMc MIc HS.
    replace (ret_pc (Z_to_bv 64 352452)) with (Z_to_bv 64 352452) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    replace X with (X + Z.of_nat (length b1))%Z in DSTc at 1 by lia.
    replace (X + Z.of_nat (Z.to_nat (8 * d)))%Z with (X + Z.of_nat (length b1) + Z.of_nat (Z.to_nat (8 * d)))%Z in U3 by lia.
    destruct (u8arr_range_join psegs m4 X b1 _ _ b3 U1 DSTc U3) as (bs4 & LB4 & XA).
    assert (XL4 : length bs4 = 496%nat) by lia.
    clear U1 U3 DSTc INV0.
    walk ltac:(fun pc => lazymatch pc with
      | 0x560d0%Z => first [ eapply pd_hi64; pd_close | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pd_shl : forall (f : nat) (i e : Z) xra xt0 xt1 xt2 xa1 xa3 xa4 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mm len,
    PDINV mm len -> (0 <= i < len)%Z -> (len - i <= Z.of_nat f)%Z -> (-2147483648 <= e < 2147483648)%Z ->
    evt psegs POST (PD 0x56044 xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) (Z_to_bv 64 len) xa1 (Z_to_bv 64 (X + 8 * len)) xa3 xa4 (Z_to_bv 64 (X + 8 * i))
                       xa6 xa7 xs2 xt3 xt4 xt5 xt6 mm).
  Proof using HMOVE HSET ROOM XHI GTOP.
    intros f. induction f as [|f IH]; intros until len; intros INV Hi Hf He; [exfalso; lia|].
    pd_open INV. pd_env. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x56044%Z => first [ eapply evt_eq; [| eapply (IH (i + 1)%Z e)]; [num_st_eq | pd_close | lia | lia | lia] | fail 100 "cut" pc ]
      | 0x56080%Z => first [ eapply (pd_80c e); [pd_close | lia] | fail 100 "cut" pc ]
      | 0x560d0%Z => first [ eapply pd_hi64; pd_close | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pd_body : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (e : Z) ws len,
    mem_inv psegs m0 -> stk psegs m0 lo SP -> bigint_at psegs m0 X ws len ->
    (-2147483648 <= e < 2147483648)%Z ->
    evt psegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PDC_ENTRY) fc None m0 (seg_rom psegs)).
  Proof using HP5 HMOVE HSET ROOM XHI GTOP.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 e ws len MI ST (WA & WL & XN0 & LEN0) He.
    unfold PDC_ENTRY. pd_env.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl psegs m0) as WM. unfold PDC_STACK, P5_STACK, LM_STACK in MU.
    set (m := m0) in MI, ST, WA, XN0, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 32%nat ST.
    apply (rw_cells_split_CB psegs m _ [] 32 junk [] [8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 4 step. zstep. zstep. zstep.

    pose proof HP5 as HP. unfold pdc_p5_stmt, p5_stmt_g in HP.
    eapply evt_cut.
    { eapply HP with (X := X) (e := e) (lo := lo) (ws := ws) (len := len);
        rewrite ?unsigned_lit by lia; unfold P5_STACK, LM_STACK, PDC_GTOP in *;
        [ exact MI | exact ST | lia | lia | split; [exact WA| split; [exact WL| split; [exact XN0| exact LEN0]]] | lia | exact He ]. }
    cbv beta. intros ms' P. unfold p5_post_g in P.
    destruct P as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3 & ws3 & len3
                   & -> & MUc & WMc & MIc & BIG3 & STc).
    rewrite !unsigned_lit in MUc, STc by lia. unfold P5_STACK, LM_STACK in MUc.
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call psegs mo mn MUc WMc end.
    clear MUc WMc MI HP. destruct BIG3 as (WA3 & WL3 & XN & LEN3).
    replace (ret_pc (Z_to_bv 64 352280)) with (Z_to_bv 64 352280) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct (u8arr_of_u64arr psegs m3 X ws3 WA3 WL3) as (bs & XL & XA). clear WA3 WL3.
    assert (INV : PDINV m3 len3) by pd_close.
    walk ltac:(fun pc => lazymatch pc with
      | 0x560d0%Z => first [ eapply pd_hi64; exact INV | fail 100 "cut" pc ]
      | 0x56080%Z => first [ eapply (pd_80c e); [exact INV | lia] | fail 100 "cut" pc ]
      | 0x56044%Z => first [ eapply evt_eq; [| eapply (pd_shl (Z.to_nat len3) 0%Z e)]; [num_st_eq | exact INV | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End PDC.

Theorem pdc_spec : pdc_p5_stmt -> pdc_memmove_stmt -> pdc_memset_stmt -> pdc_stmt_g psegs PDC_ENTRY PDC_GTOP.
Proof.
  intros H5 HMV HST. unfold pdc_stmt_g. intros until len. intros MI ST ROOM GTOP BIG XHI He.
  eapply pd_body; eassumption.
Qed.
