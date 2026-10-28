(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Definition SHLU_ENTRY : Z := 0x5ef9c.
Definition shlu_memmove_stmt : Prop := memmove_stmt_g usegs 0xd027c.

Section SHLU.
  Hypothesis HMOVE : shlu_memmove_stmt.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo : Z) (xn : word) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation N := (bv_unsigned xn).
  Hypothesis ROOM : (lo + SHLU_STACK <= SP)%Z.
  Hypothesis XLO : (SP <= X)%Z.
  Hypothesis XHI : (X + 498 <= 2^64)%Z.
  Hypothesis X0 : (0 < X)%Z.

  Notation W := [(SP - SHLU_STACK, SP); (X, X + 498)]%Z.
  Notation POST := (bigu_post_g SHLU_STACK usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m0).
  Notation SH pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 (SP + -48)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3
             s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition SHINV (mm : mem) (len : Z) : Prop :=
    (exists j, rw_cells usegs mm (SP + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
    (exists bs, u8arr usegs mm X bs /\ length bs = 496%nat) /\
    rw_cells usegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    mem_inv usegs mm /\ munch W m0 mm /\ wmono usegs m0 mm /\ stk usegs mm lo (SP + -48).

  Ltac sh_open H :=
    let j := fresh "j" in let bs := fresh "bs" in
    destruct H as ((j & FR) & (bs & XA & ?XL) & XN & ?LEN & MI & MU & WM & ST); unfold SHLU_STACK in MU.
  Ltac sh_close :=
    lazymatch goal with
    | |- SHINV _ _ =>
        split; [eexists; eassumption|]; split; [eexists; split; [eassumption| lia]|]; split; [eassumption|]; split; [lia|];
        split; [eassumption|]; split; [eassumption|]; split; eassumption
    end.
  Ltac sh_env :=
    pose proof ROOM as ROOM'; unfold SHLU_STACK in ROOM';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof XHI as XHI'; change (2 ^ 64)%Z with 18446744073709551616%Z in XHI';
    pose proof XLO as XLO'; pose proof X0 as X0'.

  Ltac sh_nr := pose proof (bv_unsigned_in_range 64 xn) as NR; unfold bv_modulus in NR; cbn in NR.

  Lemma sh_exit : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    SHINV mm len ->
    evt usegs POST (SH 0x5f0e4 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XLO XHI X0.
    intros until len. intros INV. sh_open INV. sh_env.
    do 5 zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    destruct (u64arr_of_u8arr usegs mm X bs XA XL) as (ws & WL & WA).
    apply evt_done. unfold bigu_post_g. do 15 eexists. exists mm, ws, len.
    split; [cbv delta [mkR]; reflexivity|].
    unfold SHLU_STACK, bigint_at.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [split; [exact WA| split; [exact WL| split; [exact XN| lia]]] | exact ST].
  Qed.

  Lemma sh_074 : forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    SHINV mm len ->
    evt usegs POST (SH 0x5f0d0 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XLO XHI X0.
    intros until len. intros INV. assert (IsData xs2) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5f0e4%Z => first [ eapply sh_exit; exact INV | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sh_Z : forall (f : nat) (i k : Z) xra xt0 xt1 xt2 xs1 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mm len,
    SHINV mm len -> (0 <= i < k)%Z -> (k + len <= 62)%Z -> (k - i <= Z.of_nat f)%Z ->
    evt usegs POST (SH 0x5f0b0 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 (Z_to_bv 64 (k + 1 - i)) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 1) (Z_to_bv 64 (X + 8 * i))
                       xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 k) xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XLO XHI X0.
    intros f. induction f as [|f IH]; intros until len; intros INV Hi Hk Hf; [exfalso; lia|].
    pose proof INV as INV0. sh_open INV0. sh_env.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5f100%Z => u_trap pc
      | 0x5f0d0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 (len + k)) by sh_close);
                             eapply evt_eq; [| eapply sh_074]; [num_st_eq | exact INV1] | fail 100 "cut" pc ]
      | 0x5f0b0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 len) by sh_close);
                             eapply evt_eq; [| eapply (IH (i + 1)%Z k)]; [num_st_eq | exact INV1 | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sh_fec : forall xra xt0 xt1 xt2 xs1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    SHINV mm len ->
    evt usegs POST (SH 0x5f048 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xn xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using HMOVE ROOM XLO XHI X0 xn.
    intros until len. intros INV. pose proof INV as INV0. sh_open INV0. sh_env. sh_nr.
    rewrite <- (Z_to_bv_bv_unsigned xn).
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5f100%Z => u_trap pc
      | 0x5f0e4%Z => first [ eapply sh_exit; exact INV | fail 100 "cut" pc ]
      | 0x5f0d0%Z => first [ eapply evt_eq; [| eapply sh_074]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0xd027c%Z => idtac
      end).
    pose proof (u8arr_bound _ _ _ _ XA) as XB. rewrite XL in XB.
    num_call_memmove HMOVE XA (X + 8 * (N / 64))%Z X (8 * len)%Z.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5f100%Z => u_trap pc
      | 0x5f0b0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 len) by sh_close);
                             eapply evt_eq; [| eapply (sh_Z (Z.to_nat 62) 0%Z (N / 64)%Z)]; [num_st_eq | exact INV1 | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sh_B : forall (f : nat) (i : Z) xra xt0 xt1 xt2 xs1 xa2 xa4 xa6 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    SHINV mm len -> (0 <= i < len)%Z -> (len - i <= Z.of_nat f)%Z ->
    evt usegs POST (SH 0x5eff4 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 (Z_to_bv 64 len) xn xa2 (Z_to_bv 64 (63 - i)) xa4 (Z_to_bv 64 (X + 8 * len)) xa6
                       (Z_to_bv 64 (X + 8 * i)) xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using HMOVE ROOM XLO XHI X0 xn.
    intros f. induction f as [|f IH]; intros until len; intros INV Hi Hf; [exfalso; lia|].
    pose proof INV as INV0. sh_open INV0. sh_env.
    assert (DA2 : IsData xa2) by exact I. assert (DA4 : IsData xa4) by exact I. assert (DA6 : IsData xa6) by exact I.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5f100%Z => u_trap pc
      | 0x5f0e0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 len) by sh_close); zstep; eapply sh_exit; exact INV1 | fail 100 "cut" pc ]
      | 0x5f048%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 len) by sh_close);
                             eapply evt_eq; [| eapply sh_fec]; [num_st_eq | exact INV1]
                           | num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 (len + 1)) by sh_close);
                             eapply evt_eq; [| eapply sh_fec]; [num_st_eq | exact INV1]
                           | fail 100 "cut" pc ]
      | 0x5eff4%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 len) by sh_close);
                             eapply evt_eq; [| eapply (IH (i + 1)%Z)]; [num_st_eq | exact INV1 | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sh_body : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ws len,
    mem_inv usegs m0 -> stk usegs m0 lo SP -> bigint_at usegs m0 X ws len ->
    evt usegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) xn a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SHLU_ENTRY) fc None m0 (seg_rom usegs)).
  Proof using HMOVE ROOM XLO XHI X0 xn.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ws len MI ST (WA & WL & XN & LEN).
    unfold SHLU_ENTRY. sh_env.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl usegs m0) as WM. unfold SHLU_STACK in MU.
    set (m := m0) in MI, ST, WA, XN, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 48%nat ST.
    apply (rw_cells_split_CB usegs m _ [] 48 junk [] [8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 5 step.
    destruct (u8arr_of_u64arr usegs _ X ws WA WL) as (bs & XL & XA). clear WA WL.
    num_cur_mem ltac:(fun mm => assert (INV : SHINV mm len) by sh_close).
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5f100%Z => u_trap pc
      | 0x5f048%Z => first [ eapply evt_eq; [| eapply sh_fec]; [num_st_eq | exact INV] | fail 100 "cut" pc ]
      | 0x5eff4%Z => first [ eapply evt_eq; [| eapply (sh_B (Z.to_nat len) 0%Z)]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End SHLU.

Theorem shlu_spec : shlu_memmove_stmt -> shlu_stmt_g usegs SHLU_ENTRY.
Proof.
  intros HM. unfold shlu_stmt_g. intros until len. intros MI ST ROOM BIG XLO XHI X0.
  eapply sh_body; eassumption.
Qed.
