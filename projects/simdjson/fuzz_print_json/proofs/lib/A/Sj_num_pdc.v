(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section PDCA.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Hypothesis ROOM : (lo + PDCA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis X0 : (0x6c9000 <= X)%Z.
  Hypothesis XLO : (X + 504 <= lo)%Z.
  Hypothesis XSH : (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)%Z.
  Hypothesis XS0 : (0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Variable Q : machine_state -> Prop.

  Notation W := [(SP - 64, SP); (X, X + 504)]%Z.

  Notation PD pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 (SP + -64)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5
             s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Definition PDINV (mm : mem) (len : Z) : Prop :=
    (exists j0, rw_cells asegs mm (SP + -64) [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
    (exists bs, u8arr asegs mm X bs /\ length bs = 496%nat) /\
    rw_cells asegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    bytes_at asegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) /\
    mem_inv asegs mm /\ munch W m0 mm /\ wmono asegs m0 mm /\ stk asegs mm lo (SP + -64).

  Ltac pd_open H :=
    let bs := fresh "bs" in let j0 := fresh "j0" in
    destruct H as ((j0 & FR) & (bs & XA & XL) & XN & LEN & ZR & MI & MU & WM & ST);
    unfold PDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in *;
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    let RL := fresh "RL" in pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
  Ltac pd_forget := repeat match goal with
    | H : rw_cells _ _ _ _ |- _ => clear H | H : u8arr _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
    | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H
    | H : bytes_at _ _ _ _ |- _ => clear H
    | H : length _ = 496%nat |- _ => clear H | H : length _ = length _ |- _ => clear H | H : length (repeat _ _) = _ |- _ => clear H
    | H : (0 <= _ <= 62)%Z |- _ => clear H | H : (0 <= bv_unsigned sp < _)%Z |- _ => clear H end.
  Ltac pd_close :=
    lazymatch goal with
    | |- PDINV _ _ =>
        split; [eexists; eassumption|]; split; [eexists; split; [eassumption| lia]|];
        split; [eassumption|]; split; [lia|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
    end.

  Definition pd_exit_k : Prop :=
    forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6 mm len,
      PDINV mm len ->
      evt asegs Q (PD 0xe8644 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6 mm).
  Hypothesis KX : pd_exit_k.

  Lemma pd_nz : forall (f : nat) (j n : Z) xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa7 xs2 xs4 xs5 xt3 xt4 xt5 xt6 mm,
    PDINV mm n -> (0 <= j <= 59)%Z -> (j <= Z.of_nat f)%Z ->
    (forall xt0' xa0' xa5' xa6' xa7',
       evt asegs Q (PD 0xe84e8 xra xt0' xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 (X + 496)) xa0' xa1 xa2 xa3 xa4 xa5' xa6' xa7' xs2 (Z_to_bv 64 2147450880) xs4 xs5 xt3 xt4 xt5 xt6 mm)) ->
    evt asegs Q (PD 0xe84bc xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (X + 8 * j)) xa1 xa2 xa3 xa4 (Z_to_bv 64 (X + 8 * j)) (Z_to_bv 64 j) xa7
                     xs2 (Z_to_bv 64 2147450880) xs4 xs5 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM TOP X8 X0 XLO XSH XS0.
    intros f. induction f as [|f IH]; intros j n xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa7 xs2 xs4 xs5 xt3 xt4 xt5 xt6 mm INV Hj Hf HK.
    all: pose proof INV as INV0; pd_open INV0.
    all: astep.
    - awalk ltac:(fun pc => lazymatch pc with
        | 0xe84e8%Z => first [ eapply evt_eq; [| eapply HK]; num_st_eq | fail 100 "cut" pc ]
        end).
    - awalk ltac:(fun pc => lazymatch pc with
        | 0xe84bc%Z => first [ eapply evt_eq; [| eapply (IH (j - 1)%Z n); [exact INV | lia | lia | exact HK]]; num_st_eq | fail 100 "cut" pc ]
        | 0xe84e8%Z => first [ eapply evt_eq; [| eapply HK]; num_st_eq | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma pd_hi : forall n xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xt3 xt4 xt5 xt6 mm,
    PDINV mm n ->
    evt asegs Q (PD 0xe82ac xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 (X + 496)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 2147450880) xs4 xs5 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM TOP X8 X0 XLO XSH XS0 KX.
    intros until mm. intros INV. pose proof INV as INV0. pd_open INV0.
    assert (KOUT : (3 <= n)%Z -> forall xra' xt0' xt1' xt2' xa0' xa1' xa3' xa5' xa6' xa7' xs2' xs4' xs5' xt3' xt4' xt5' xt6',
              evt asegs Q (PD 0xe84e8 xra' xt0' xt1' xt2' (Z_to_bv 64 X) (Z_to_bv 64 (X + 496)) xa0' xa1' (Z_to_bv 64 n) xa3' (Z_to_bv 64 (n + -1)) xa5' xa6' xa7' xs2' (Z_to_bv 64 2147450880) xs4' xs5' xt3' xt4' xt5' xt6' mm)).
    { intros N3. intros. awalk ltac:(fun pc => lazymatch pc with 0xe8644%Z => first [ eapply KX; exact INV | fail 100 "cut" pc ] end). }
    awalk ltac:(fun pc => lazymatch pc with
      | 0xe84bc%Z => first [ eapply evt_eq; [| eapply (pd_nz (Z.to_nat (n - 3)) (n - 3)%Z n); [exact INV | lia | lia | intros; eapply KOUT; lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xe8644%Z => first [ eapply KX; exact INV | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pd_shl : forall (f : nat) (i n : Z) xra xt0 xt1 xt2 xa3 xa4 xs2 xs4 xs5 xt3 xt4 xt5 xt6 mm,
    PDINV mm n -> (0 <= i < n)%Z -> (n - i <= Z.of_nat f)%Z ->
    (forall xt0' xt1' xt2' xa0' xa5' xa6' mm', PDINV mm' n ->
       evt asegs Q (PD 0xe8208 xra xt0' xt1' xt2' (Z_to_bv 64 X) (Z_to_bv 64 (X + 496)) xa0' (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 n) xa3 xa4 xa5' xa6' (Z_to_bv 64 0)
                       xs2 (Z_to_bv 64 2147450880) xs4 xs5 xt3 xt4 xt5 xt6 mm')) ->
    evt asegs Q (PD 0xe81d4 xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 n) xa3 xa4
                     (Z_to_bv 64 (2147450880 + X / 8 + i)) (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 (n - i)) xs2 (Z_to_bv 64 2147450880) xs4 xs5 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM TOP X8 X0 XLO XSH XS0.
    intros f. induction f as [|f IH]; intros i n xra xt0 xt1 xt2 xa3 xa4 xs2 xs4 xs5 xt3 xt4 xt5 xt6 mm INV Hi Hf HK; [exfalso; lia|].
    pd_open INV.
    astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xe81d4%Z => first [ eapply evt_eq; [| eapply (IH (i + 1)%Z n); [pd_close | lia | lia | exact HK]]; num_st_eq | fail 100 "cut" pc ]
      | 0xe8208%Z => first [ eapply evt_eq; [| eapply HK; pd_close]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ksh_norm : forall e, (0 <= e < 2147483648)%Z -> bv_swrap 32 (Z.shiftr (bv_wrap 32 e) 6) = (e / 64)%Z.
  Proof.
    intros e He. unfold bv_wrap. change (bv_modulus 32) with 4294967296%Z. rewrite Z.mod_small by lia.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6)%Z with 64%Z.
    apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32 / 2)%Z with 2147483648%Z.
    assert (0 <= e / 64 <= e)%Z by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). lia.
  Qed.

  Definition pd_move_k : Prop :=
    forall (k n : Z) xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm,
      PDINV mm n -> (0 <= k)%Z -> (1 <= n)%Z -> (k + n <= 62)%Z ->
      evt asegs Q (PD 0x81ef8 (Z_to_bv 64 0xe8288) xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (X + 8 * k)) (Z_to_bv 64 X) (Z_to_bv 64 (8 * n)) xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (8 * k)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 k) xt3 xt4 xt5 xt6 mm).
  Hypothesis KMV : pd_move_k.

  Lemma pd_b1 : forall (e n : Z) xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xt3 xt4 xt5 xt6 mm,
    PDINV mm n -> (0 <= e < 2147483648)%Z ->
    evt asegs Q (PD 0xe818c xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 e) (Z_to_bv 64 2147450880) xs4 xs5 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM TOP X8 X0 XLO XSH XS0 KX KMV.
    intros until mm. intros INV He. pose proof INV as INV0. pd_open INV0.
    pose proof (ksh_norm e He) as KE.
    assert (KR : (0 <= e / 64 <= e)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    awalk ltac:(fun pc => lazymatch pc with
      | 0xe81d4%Z => first [ eapply evt_eq; [| eapply (pd_shl (Z.to_nat n) 0 n); [exact INV | lia | lia |]]; [num_st_eq|] | fail 100 "cut" pc ]
      | 0x81ef8%Z => first [ rewrite ?KE; rewrite ?(Z.mod_small (e / 64) 18446744073709551616) by lia;
                             eapply evt_eq; [| eapply (KMV (e / 64)%Z n); [exact INV | lia | lia | rewrite ?KE in *; lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xe82ac%Z => first [ eapply evt_eq; [| eapply (pd_hi n); exact INV]; num_st_eq | fail 100 "cut" pc ]
      end).

    clear INV. pd_forget.
    intros xt0' xt1' xt2' xa0' xa5' xa6' mm' INV. pose proof INV as INV0. pd_open INV0.
    awalk ltac:(fun pc => lazymatch pc with
      | 0x81ef8%Z => first [ rewrite ?KE; rewrite ?(Z.mod_small (e / 64) 18446744073709551616) by lia;
                             eapply evt_eq; [| eapply (KMV (e / 64)%Z); [pd_close | lia | lia | rewrite ?KE in *; lia]]; num_st_eq | fail 100 "cut" pc ]
      | 0xe82ac%Z => first [ eapply evt_eq; [| eapply pd_hi; pd_close]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma pd_b2 : forall (k n : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mm,
    PDINV mm n -> (0 <= k)%Z -> (k + n <= 62)%Z ->
    evt asegs Q (PD 0xe8298 xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 (X + 496)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 2147450880)
                     (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 k) xt3 xt4 xt5 xt6 mm).
  Proof using ROOM TOP X8 X0 XLO XSH XS0 KX.
    intros until mm. intros INV Hk Hkn. pd_open INV.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xe82ac%Z => first [ eapply evt_eq; [| eapply (pd_hi (n + k)%Z); pd_close]; num_st_eq | fail 100 "cut" pc ]
      end).
  Qed.
End PDCA.
