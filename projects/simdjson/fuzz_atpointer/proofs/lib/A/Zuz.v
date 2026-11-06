(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpe.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks D_defs D_kit D_clx Zpm Zpl Zq2 Sj_rtf
  Zqc Zqd Zsl Zqa Zq7.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section P5A.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Hypothesis ROOM : (lo + P5A_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis X0 : (0x669000 <= X)%Z.
  Hypothesis XLO : (X + 504 <= lo)%Z.
  Hypothesis XSH : (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)%Z.
  Hypothesis XS0 : (0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.

  Notation W := [(SP - 48, SP); (X, X + 504)]%Z.

  Hypothesis SHPL : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' 0x2af20 640.
  Variable Q : machine_state -> Prop.

  Notation P5A pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 (SP + -48)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4
             s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Definition P5AINV (mm : mem) (len : Z) : Prop :=
    rw_cells asegs mm (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    (exists bs, u8arr asegs mm X bs /\ length bs = 496%nat) /\
    rw_cells asegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    bytes_at asegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) /\
    mem_inv asegs mm /\ munch W m0 mm /\ wmono asegs m0 mm /\ stk asegs mm lo (SP + -48).

  Ltac p5a_open H :=
    let bs := fresh "bs" in
    destruct H as (FR & (bs & XA & XL) & XN & LEN & ZR & MI & MU & WM & ST);
    unfold P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in *;
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    let RL := fresh "RL" in pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
  Ltac p5a_forget := repeat match goal with
    | H : rw_cells _ _ _ _ |- _ => clear H | H : u8arr _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
    | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H
    | H : bytes_at _ _ _ _ |- _ => clear H
    | H : length _ = 496%nat |- _ => clear H | H : length _ = length _ |- _ => clear H | H : length (repeat _ _) = _ |- _ => clear H
    | H : (0 <= _ <= 62)%Z |- _ => clear H | H : (0 <= bv_unsigned sp < _)%Z |- _ => clear H end.
  Ltac p5a_close :=
    lazymatch goal with
    | |- P5AINV _ _ =>
        split; [eassumption|]; split; [eexists; split; [eassumption| lia]|];
        split; [eassumption|]; split; [lia|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
    end.

  Lemma p5a_mulA : forall (f : nat) (i n : Z) xra xt0 xt1 xs1 xa2 xa5 xs2 xs4 xt5 xt6 mm,
    P5AINV mm n -> (0 <= i < n)%Z -> (n - i <= Z.of_nat f)%Z ->
    (forall xt1' xt2' xa1' xt3' xt5' xt6' mm', P5AINV mm' n ->
       evt asegs Q (P5A 0xc95a8 xra xt0 xt1' xt2' (Z_to_bv 64 X) xs1 (Z_to_bv 64 (X + 496)) xa1' xa2 (Z_to_bv 64 n) (Z_to_bv 64 (X / 8 + 2147450880)) xa5
                        (Z_to_bv 64 26) (Z_to_bv 64 61) xs2 (Z_to_bv 64 2147450880) xs4 xt3' (Z_to_bv 64 0) xt5' xt6' mm')) ->
    evt asegs Q (P5A 0xc9570 xra xt0 xt1 (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 X) xs1 (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (X + 8 * i)) xa2 (Z_to_bv 64 n)
                     (Z_to_bv 64 (X / 8 + 2147450880)) xa5 (Z_to_bv 64 26) (Z_to_bv 64 61) xs2 (Z_to_bv 64 2147450880) xs4
                     (Z_to_bv 64 (X / 8 + 2147450880 + i)) (Z_to_bv 64 (n - i)) xt5 xt6 mm).
  Proof using ROOM TOP X8 X0 XLO XSH XS0.
    intros f. induction f as [|f IH]; intros i n xra xt0 xt1 xs1 xa2 xa5 xs2 xs4 xt5 xt6 mm INV Hi Hf HK; [exfalso; lia|].
    p5a_open INV.
    astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xc9570%Z => first [ eapply evt_eq; [| eapply (IH (i + 1)%Z n); [p5a_close | lia | lia | exact HK]]; num_st_eq | fail 100 "cut" pc ]
      | 0xc95a8%Z => first [ eapply evt_eq; [| eapply HK; p5a_close]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma p5a_mulB : forall (f : nat) (i n : Z) xra xt2 xs1 xa1 xa5 xa6 xs2 xs4 xt3 xt4 xt5 xt6 mm,
    P5AINV mm n -> (0 <= i < n)%Z -> (n - i <= Z.of_nat f)%Z ->
    (forall xt0' xt2' xa2' xa5' xa7' xt3' mm', P5AINV mm' n ->
       evt asegs Q (P5A 0xc966c xra xt0' (Z_to_bv 64 0) xt2' (Z_to_bv 64 X) xs1 (Z_to_bv 64 (X + 496)) xa1 xa2' (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 n) xa5'
                        xa6 xa7' xs2 (Z_to_bv 64 2147450880) xs4 xt3' xt4 xt5 xt6 mm')) ->
    evt asegs Q (P5A 0xc9634 xra (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 (n - i)) xt2 (Z_to_bv 64 X) xs1 (Z_to_bv 64 (X + 496)) xa1 (Z_to_bv 64 (X + 8 * i))
                     (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 n) xa5 xa6 (Z_to_bv 64 (X / 8 + 2147450880 + i)) xs2 (Z_to_bv 64 2147450880) xs4
                     xt3 xt4 xt5 xt6 mm).
  Proof using ROOM TOP X8 X0 XLO XSH XS0.
    intros f. induction f as [|f IH]; intros i n xra xt2 xs1 xa1 xa5 xa6 xs2 xs4 xt3 xt4 xt5 xt6 mm INV Hi Hf HK; [exfalso; lia|].
    p5a_open INV.
    astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xc9634%Z => first [ eapply evt_eq; [| eapply (IH (i + 1)%Z n); [p5a_close | lia | lia | exact HK]]; num_st_eq | fail 100 "cut" pc ]
      | 0xc966c%Z => first [ eapply evt_eq; [| eapply HK; p5a_close]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Definition p5a_exit_k : Prop :=
    forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 mm len,
      P5AINV mm len ->
      evt asegs Q (P5A 0xc96ac xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 mm).
  Hypothesis KX : p5a_exit_k.

  Ltac p5a_cut_exit pc :=
    lazymatch pc with
    | 0xc96ac%Z => first [ eapply KX; p5a_close | fail 100 "cut" pc ]
    end.

  Lemma p5a_tail : forall (e n : Z) xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xt3 xt4 xt5 xt6 mm,
    P5AINV mm n -> (0 <= e < 27)%Z ->
    evt asegs Q (P5A 0xc95dc xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) (Z_to_bv 64 (X + 496)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 2147450880) xs4
                     xt3 xt4 xt5 xt6 mm).
  Proof using ROOM TOP X8 X0 XLO XSH XS0 SHPL KX.
    intros until mm. intros INV He.
    pose proof INV as INV0. p5a_open INV.
    destruct (image_readable_b asegs mm 224 0x2af48 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (tb & TL & TB).
    awalk ltac:(fun pc => lazymatch pc with
      | 0xc9634%Z => first [ eapply evt_eq; [| eapply (p5a_mulB (Z.to_nat n) 0 n); [p5a_close | lia | lia |]]; [num_st_eq|] | fail 100 "cut" pc ]
      | _ => p5a_cut_exit pc
      end).

    clear INV0. p5a_forget.
    intros xt0' xt2' xa2' xa5' xa7' xt3' mm' INV. p5a_open INV.
    awalk p5a_cut_exit.
  Qed.

  Lemma p5a_L2 : forall (f : nat) (e n : Z) xra xt0 xt1 xt2 xa1 xa5 xs2 xs4 xt3 xt4 xt5 xt6 mm,
    P5AINV mm n -> (27 <= e < 2147483648)%Z -> (e <= 27 * Z.of_nat f)%Z ->
    evt asegs Q (P5A 0xc9558 xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) (Z_to_bv 64 (X + 496)) xa1 (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 n)
                     (Z_to_bv 64 (X / 8 + 2147450880)) xa5 (Z_to_bv 64 26) (Z_to_bv 64 61) xs2 (Z_to_bv 64 2147450880) xs4 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM TOP X8 X0 XLO XSH XS0 SHPL KX.
    intros f. induction f as [|f IH]; intros e n xra xt0 xt1 xt2 xa1 xa5 xs2 xs4 xt3 xt4 xt5 xt6 mm INV He Hf; [exfalso; lia|].
    assert (KBOT : forall xt1' xt2' xa1' xt3' xt4' xt5' xt6' n' mm', P5AINV mm' n' ->
              evt asegs Q (P5A 0xc9550 xra xt0 xt1' xt2' (Z_to_bv 64 X) (Z_to_bv 64 e) (Z_to_bv 64 (X + 496)) xa1' (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 n')
                               (Z_to_bv 64 (X / 8 + 2147450880)) xa5 (Z_to_bv 64 26) (Z_to_bv 64 61) xs2 (Z_to_bv 64 2147450880) xs4 xt3' xt4' xt5' xt6' mm')).
    { intros xt1' xt2' xa1' xt3' xt4' xt5' xt6' n' mm' INV'. p5a_open INV'.
      astep. astep.
      if_cases K; zify_cond K.
      - eapply evt_eq; [| eapply (p5a_tail (e - 27)%Z n'); [p5a_close | lia]]. num_st_eq.
      - eapply evt_eq; [| eapply (IH (e - 27)%Z n'); [p5a_close | lia | lia]]. num_st_eq. }
    pose proof INV as INV0. p5a_open INV.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xc9550%Z => first [ eapply evt_eq; [| eapply KBOT; p5a_close]; num_st_eq | fail 100 "cut" pc ]
      | 0xc9570%Z => first [ eapply evt_eq; [| eapply (p5a_mulA (Z.to_nat n) 0 n); [p5a_close | lia | lia |]]; [num_st_eq|] | fail 100 "cut" pc ]
      | _ => p5a_cut_exit pc
      end).
    clear INV0. p5a_forget.
    intros xt1' xt2' xa1' xt3' xt5' xt6' mm' INV. p5a_open INV.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xc9550%Z => first [ eapply evt_eq; [| eapply KBOT; p5a_close]; num_st_eq | fail 100 "cut" pc ]
      | _ => p5a_cut_exit pc
      end).
  Qed.

  Lemma p5a_mid : forall (e n : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xt3 xt4 xt5 xt6 mm,
    P5AINV mm n -> (0 <= e < 135)%Z ->
    evt asegs Q (P5A 0xc9504 xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 2147450880) xs4 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM TOP X8 X0 XLO XSH XS0 SHPL KX.
    intros until mm. intros INV He.
    pose proof INV as INV0. p5a_open INV.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xc95dc%Z => first [ eapply evt_eq; [| eapply (p5a_tail e n); [exact INV0 | lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xc9558%Z => first [ eapply evt_eq; [| eapply (p5a_L2 5 e n); [exact INV0 | lia | lia]]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.
End P5A.

Section P5TOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis NLA : num_lits_acc RT.
  Hypothesis HLM : lma_stmt RT PMc.

  Variables (Σ0 : rts RT) (K : config -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (X lo cr0 : Z) (me : mem).
  Notation SP := (bv_unsigned sp).
  Hypothesis ETP : tp = Z_to_bv 64 0x646eb0.
  Hypothesis ROOM : (lo + P5A_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis FRL : (length (rt_frames RT Σ0) < FRAMES_MAX)%nat.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XFR : exists f c, In (f, c) (rt_frames RT Σ0) /\ (f <= X)%Z /\ (X + 504 <= f + fs_size c - 8)%Z.
  Hypothesis XNUM : (0x669000 <= X /\ X + 504 <= lo
                     /\ (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)
                     /\ 0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis HK : forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after RT Σ' SP lo me m' -> rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) SP [(X, X + 504)%Z] me m' ->
     abig RT Σ' m' X ->
     rt_frames RT Σ' = rt_frames RT Σ0 -> rt_live RT Σ' = rt_live RT Σ0 -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 ->
     (rt_credit RT Σ0 - cr0 <= rt_credit RT Σ')%Z ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (ret_pc ra) fc' None m' (seg_rom asegs)).

  Hypothesis CR0 : (cr0 <= rt_credit RT Σ0)%Z.
  Collection P5H := ETP ROOM TOP SP16 LOR FRL X8 XFR XNUM CR0.

  Definition p5_srel (Σ : rts RT) (used : Z) : Prop :=
    rt_frames RT Σ = rt_frames RT Σ0 /\ rt_live RT Σ = rt_live RT Σ0 /\ rt_sp0 RT Σ = rt_sp0 RT Σ0 /\ (rt_credit RT Σ0 - used <= rt_credit RT Σ)%Z.

  Definition p5_mrel (mm : mem) : Prop :=
    wmono asegs me mm /\ rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) SP [(X, X + 504)%Z] me mm.

  Notation W := [(SP - 48, SP); (X, X + 504)]%Z.

  Lemma p5_fpok : forall Σ used, p5_srel Σ used -> fp_ok RT Σ lo W.
  Proof using P5H.
    intros Σ used (EF & _). unfold P5A_STACK, LMA_STACK, RT_STACK in ROOM.
    constructor; [left; cbn [fst snd]; lia|]. constructor; [| constructor].
    right; right; left. destruct XFR as (f & c & Hin & F1 & F2). exists f, c. rewrite EF. cbn [fst snd]. split; [exact Hin| lia].
  Qed.

  Lemma p5_mrel_step : forall Σ used mb mm, p5_srel Σ used -> ART RT Σ mb -> p5_mrel mb -> munch W mb mm -> wmono asegs mb mm -> p5_mrel mm.
  Proof using AF P5H.
    intros Σ used mb mm (EF & EL & ES & _) HA [WM0 PR0] MU WM. split; [exact (wmono_trans asegs _ _ _ WM0 WM)|].
    eapply pres_fp_trans; [exact PR0|]. apply (pres_fp_of_munch _ _ _ _ W _ _ MU).
    intros a Ha Hd. rewrite <- EL, <- EF in Ha. pose proof (aclient_split_c RT AF Σ mb _ a HA Ha) as SPL. rewrite ES in SPL.
    unfold P5A_STACK, LMA_STACK, RT_STACK in ROOM. cbn [outside] in Hd |- *. destruct Hd as [Hd _].
    split; [lia|]. split; [exact Hd| exact I].
  Qed.

  Lemma p5_exit : forall Σ used F fc mb, p5_srel Σ used -> (used <= cr0)%Z -> frm0 fc -> ART RT Σ mb -> p5_mrel mb ->
    p5a_exit_k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo mb (fun ms' => aevt RT PMc Σ K ms').
  Proof using AF P5H HK.
    intros Σ used F fc mb SR HU FRM HA MR. unfold p5a_exit_k. intros until len. intros INV.
    destruct INV as (FR & (bs & XA & XL) & XN & LEN & ZR & MI & MU & WM & ST).
    pose proof SR as (EF & EL & ES & EC).
    destruct XNUM as (XN0 & XN1 & XN2 & XN3 & XN4).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in ROOM, TOP.
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
    do 8 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done.
    eapply HK; [exact FRM | | | | exact EF | exact EL | exact ES | lia].
    - split; [exact (art_of_munch RT AF Σ mb _ lo W HA ltac:(rewrite ES; exact LOR) (p5_fpok Σ used SR) MU WM)|].
      split; [exact MI|]. split; [exact (wmono_trans asegs _ _ _ (proj1 MR) WM)| exact ST].
    - exact (proj2 (p5_mrel_step Σ used mb _ SR HA MR MU WM)).
    - apply (abig_intro RT _ _ X bs len). split; [exact XA|]. split; [exact XL|]. split; [exact XN|]. split; [exact LEN|].
      split; [exact ZR|]. split; [exact X8|]. rewrite EF. exact XFR.
  Qed.

  Lemma p5_shpl : forall Σ used mb, p5_srel Σ used -> ART RT Σ mb ->
    forall m', munch W mb m' -> wmono asegs mb m' -> shz m' 0x2af20 640.
  Proof using AF NLA P5H.
    intros Σ used mb SR HA. pose proof SR as (_ & _ & ES & _).
    exact (shzp_lits RT AF Σ mb lo W 0x2af20 640 NLA HA ltac:(rewrite ES; exact LOR) (p5_fpok Σ used SR) ltac:(right; left; reflexivity)).
  Qed.

  Lemma p5_mid : forall Σ used F fc mb (e n : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xt3 xt4 xt5 xt6 mm,
    p5_srel Σ used -> (used <= cr0)%Z -> frm0 fc -> ART RT Σ mb -> p5_mrel mb ->
    P5AINV ra sp s0 s1 s2 s3 s4 X lo mb mm n -> (0 <= e < 135)%Z ->
    evt asegs (fun ms' => aevt RT PMc Σ K ms')
      (MS (mkR xra (Z_to_bv 64 (SP + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 2147450880) xs4
               s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0xc9504) fc None mm (seg_rom asegs)).
  Proof using AF NLA P5H HK.
    intros Σ used F fc mb e n xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xt3 xt4 xt5 xt6 mm SR HU FRM HA MR INV He.
    destruct XNUM as (XN0 & XN1 & XN2 & XN3 & XN4).
    exact (p5a_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo mb ROOM TOP X8 XN0 XN1 XN2 (conj XN3 XN4) (p5_shpl Σ used mb SR HA) _
             (p5_exit Σ used F fc mb SR HU FRM HA MR) e n xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xt3 xt4 xt5 xt6 mm INV He).
  Qed.

  Lemma p5_L1 : forall (f : nat) (e cr n : Z) Σ used F fc mb xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    p5_srel Σ used -> (used + cr <= cr0)%Z -> frm0 fc -> ART RT Σ mb -> p5_mrel mb ->
    P5AINV ra sp s0 s1 s2 s3 s4 X lo mb mb n ->
    (135 <= e < 135 * (cr + 1))%Z -> (e < 2147483648)%Z -> (e <= 135 * Z.of_nat f)%Z ->
    aevt RT PMc Σ K
      (MS (mkR xra (Z_to_bv 64 (SP + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 0x2af20) (Z_to_bv 64 2147450880) (Z_to_bv 64 134)
               s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0xc94e8) fc None mb (seg_rom asegs)).
  Proof using AF RTF FDO MST NLA HLM P5H HK.
    intros f. induction f as [|f IH]; intros e cr n Σ used F fc mb xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 SR HU FRM HA MR INV He He31 Hf; [exfalso; lia|].
    pose proof SR as (EF & EL & ES & EC).
    destruct INV as (FR & (bs & XA & XL) & XN & LEN & ZR & MI & MU & WM & ST).
    pose proof XNUM as (XN0 & XN1 & XN2 & XN3 & XN4).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof ROOM as ROOM'. pose proof TOP as TOP'. unfold P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in ROOM', TOP'.
    apply (aevt_evt RT AF PMc MST).
    do 4 zstep. apply evt_done.
    eapply (HLM Σ) with (X := X) (lo := lo); rewrite ?unsigned_lit by lia; unfold LMA_STACK, RT_STACK, USTACK_TOP;
      [ exact ETP | exact FRM | rewrite EF; exact FRL | lia | exact HA | exact MI | exact ST | rewrite ES; exact LOR | lia | lia
      | Z.div_mod_to_equations; lia
      | apply (abig_intro RT _ _ X bs n); split; [exact XA|]; split; [exact XL|]; split; [exact XN|]; split; [exact LEN|];
        split; [exact ZR|]; split; [exact X8|]; rewrite EF; exact XFR
      | ].

    intros Σ' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' RA PR AB EF' EL' ES' EC'.
    rewrite ?unsigned_lit in RA, PR by lia.
    destruct RA as (ART' & MI' & WM' & ST').
    assert (SR' : p5_srel Σ' (used + 1)) by (unfold p5_srel; rewrite EF', EL', ES'; repeat split; try assumption; lia).
    destruct (abig_elim RT _ _ _ AB) as (bs' & n' & XA' & XL' & XN' & LEN' & ZR' & _ & _).
    pose proof (agree_pres_fp _ _ _ _ mb m' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) (SP + -48) x /\ outside [(X, (X + 504)%Z)] x) PR (fun x H => H)) as AG.
    clear XA XN ZR.
    rt_transport_with mb m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; split; [aclient_tac| cbn [outside]; lia]).
    assert (MR' : p5_mrel m').
    { destruct MR as [WM0 PR0]. split; [exact (wmono_trans asegs _ _ _ WM0 WM')|].
      eapply pres_fp_trans; [exact PR0|]. rewrite <- EL, <- EF. eapply pres_fp_sp; [exact PR| lia]. }
    assert (INV' : P5AINV ra sp s0 s1 s2 s3 s4 X lo m' m' n').
    { split; [exact FR|]. split; [exists bs'; split; [exact XA'| exact XL']|]. split; [exact XN'|]. split; [exact LEN'|]. split; [exact ZR'|].
      split; [exact MI'|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact ST']. }
    clear MU WM MI ST.
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    zstep.
    if_cases K0.
    {
      zstep. eapply (p5_exit Σ' (used + 1) F' fc' m' SR' ltac:(lia) FRM' ART' MR'). exact INV'. }
    clear K0.
    zstep. nnorm.
    zstep.
    if_cases K1; zify_cond K1.
    - apply evt_done. eapply (IH (e - 135)%Z (cr - 1)%Z n' Σ' (used + 1)%Z F' fc' m'); [exact SR' | lia | exact FRM' | exact ART' | exact MR' | | lia | lia | lia].
      exact INV'.
    - eapply evt_eq; [| eapply (p5_mid Σ' (used + 1)%Z F' fc' m' (e - 135)%Z n'); [exact SR' | lia | exact FRM' | exact ART' | exact MR' | exact INV' | lia]].
      num_st_eq.
  Qed.

  Lemma p5_entry : forall (e n : Z) F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 bs,
    frm0 fc -> ART RT Σ0 me -> mem_inv asegs me -> stk asegs me lo SP ->
    u8arr asegs me X bs -> length bs = 496%nat -> rw_cells asegs me (X + 496) [C2 (Z_to_bv 64 n)] -> (0 <= n <= 62)%Z ->
    bytes_at asegs me (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    (0 <= e < 135 * (cr0 + 1))%Z -> (0 <= cr0)%Z -> (e < 2147483648)%Z ->
    aevt RT PMc Σ0 K
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc94a4) fc None me (seg_rom asegs)).
  Proof using AF RTF FDO MST NLA HLM P5H HK.
    intros e n F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 bs FRM HA MI ST XA XL XN LEN ZR He Hcr He31.
    pose proof XNUM as (XN0 & XN1 & XN2 & XN3 & XN4).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof ROOM as ROOM'. pose proof TOP as TOP'. unfold P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in ROOM', TOP'.
    pose proof (af_sp0_range RT AF Σ0 me HA) as SP0R. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in SP0R. pose proof LOR as LOR'. unfold STACK_WIN in LOR'.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
    destruct (af_client_consts RT AF Σ0 me HA) as (G1 & G2 & _). unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in G1, G2.
    assert (SR0 : p5_srel Σ0 0) by (unfold p5_srel; repeat split; lia).
    assert (MR0 : p5_mrel me) by (split; [apply wmono_refl| apply pres_fp_refl]).
    apply (aevt_evt RT AF PMc MST).
    pose proof (munch_refl W me) as MU. pose proof (wmono_refl asegs me) as WM.
    set (mb := me) in MU at 1, WM at 1.
    step.
    carve_frame 48%nat ST.
    apply (rw_cells_split_CB asegs me _ [] 48 junk [] [8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 6 step. do 7 zstep.
    clear G1 G2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => assert (INV : P5AINV ra sp s0 s1 s2 s3 s4 X lo mb m1 n) by
      (split; [eassumption|]; split; [eexists; split; eassumption|]; split; [eassumption|]; split; [lia|]; split; [eassumption|];
       split; [eassumption|]; split; [eassumption|]; split; eassumption) end.
    if_cases K0; zify_cond K0.
    - eapply evt_eq; [| eapply (p5_mid Σ0 0%Z F fc mb e n); [exact SR0 | lia | exact FRM | exact HA | exact MR0 | exact INV | lia]]. num_st_eq.
    - do 3 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
        assert (ART1 : ART RT Σ0 m1) by exact (art_of_munch RT AF Σ0 mb m1 lo W HA LOR (p5_fpok Σ0 0%Z SR0) MU WM);
        assert (MR1 : p5_mrel m1) by exact (p5_mrel_step Σ0 0%Z mb m1 SR0 HA MR0 MU WM);
        assert (INV1 : P5AINV ra sp s0 s1 s2 s3 s4 X lo m1 m1 n) by
          (destruct INV as (I1 & I2 & I3 & I4 & I5 & I6 & _ & _ & I9);
           split; [exact I1|]; split; [exact I2|]; split; [exact I3|]; split; [exact I4|]; split; [exact I5|]; split; [exact I6|];
           split; [apply munch_refl|]; split; [apply wmono_refl| exact I9])
      end.
      apply evt_done.
      eapply (p5_L1 (Z.to_nat e) e cr0 n Σ0 0%Z); [exact SR0 | lia | exact FRM | exact ART1 | exact MR1 | exact INV1 | lia | lia | lia].
  Qed.
End P5TOP.

Theorem p5a_ok : forall RT, art_facts RT -> rt_contracts_f RT -> num_lits_acc RT ->
  forall PMc, fdfs_only PMc -> mat_stable PMc -> lma_stmt RT PMc -> p5a_stmt RT PMc.
Proof.
  intros RT AF RTF NLA PMc FDO MST HLM. unfold p5a_stmt.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X e cr lo
    ETP FRM FRL He Hcr He31 CR ART0 MI ST LOR ROOM TOP SP16 AB HK.
  destruct (abig_elim RT _ _ _ AB) as (bs & n & RAW).
  pose proof (abig_facts RT AF Σ m X bs n lo ART0 LOR RAW) as XNUM.
  destruct RAW as (XA & XL & XN & LEN & ZR & X8 & XFR).
  eapply (p5_entry RT AF RTF PMc FDO MST NLA HLM Σ K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo cr m ETP ROOM TOP SP16 LOR FRL X8 XFR XNUM HK CR
            e n F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 bs); try eassumption; lia.
Qed.
