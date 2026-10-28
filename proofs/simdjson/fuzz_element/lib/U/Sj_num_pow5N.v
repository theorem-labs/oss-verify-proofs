(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_kitn2.
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

Definition P5N_ENTRY : Z := 0x5e570.
Definition p5N_lm_stmt : Prop := lmuN_stmt_g usegs 0x5e768.

Section P5N.
  Hypothesis HLM : p5N_lm_stmt.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo len0 e0 : Z) (m0 : mem) (C : Prop).
  Notation SP := (bv_unsigned sp).
  Hypothesis ROOM : (lo + P5U_STACK <= SP)%Z.
  Hypothesis GTOP : (NUMU_GTOP <= lo)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis XLO : (SP <= X)%Z.
  Hypothesis XHI : (X + 498 <= 2^64)%Z.
  Hypothesis HCL : C -> (len0 + 15 <= 62 /\ 0 <= e0 <= 328)%Z.

  Notation W := [(SP - P5U_STACK, SP); (X, X + 498)]%Z.
  Notation GP := (fun (a0 : word) (ws' : list word) (len' : Z) => C -> a0 = Z_to_bv 64 1 /\ bignorm ws' len' /\ (len' <= len0 + 15)%Z).
  Notation POST := (biguN_post_g P5U_STACK GP usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m0).
  Notation P5 pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 (SP + -48)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3
             s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Notation POT len e := (C -> 0 <= e <= e0 /\ 135 * len + 6 * e <= 135 * len0 + 6 * e0)%Z.

  Definition P5INV (mm : mem) (len : Z) : Prop :=
    (exists j, rw_cells usegs mm (SP + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
    (exists bs, u8arr usegs mm X bs /\ length bs = 496%nat /\ (C -> bignorm_b bs len)) /\
    rw_cells usegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    mem_inv usegs mm /\ munch W m0 mm /\ wmono usegs m0 mm /\ stk usegs mm lo (SP + -48).

  Ltac p5_open H :=
    let j := fresh "j" in let bs := fresh "bs" in
    destruct H as ((j & FR) & (bs & XA & ?XL & NB) & XN & ?LEN & MI & MU & WM & ST); unfold P5U_STACK, LMU_STACK, LAFU_STACK in MU.
  Ltac p5_close_with nb :=
    lazymatch goal with
    | |- P5INV _ _ =>
        split; [eexists; eassumption|]; split; [eexists; split; [eassumption| split; [lia | nb]]|]; split; [eassumption|]; split; [lia|];
        split; [eassumption|]; split; [eassumption|]; split; eassumption
    end.
  Ltac p5_env :=
    pose proof ROOM as ROOM'; pose proof GTOP as GTOP'; unfold P5U_STACK, LMU_STACK, LAFU_STACK, NUMU_GTOP in ROOM', GTOP';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof XHI as XHI'; change (2 ^ 64)%Z with 18446744073709551616%Z in XHI';
    pose proof XLO as XLO'; pose proof SP16 as SP16'; pose proof HCL as HCL'.

  Ltac cl := let HC := fresh "HC" in intros HC; repeat match goal with H : C -> _ |- _ => specialize (H HC) end; lia.
  Ltac nb_other := let HC := fresh "HC" in intros HC; apply bignorm_b_upd_other; [lazymatch goal with NB : C -> bignorm_b _ _ |- _ => apply NB; exact HC end | lia | rewrite ?length_le8; lia | lia].

  Lemma p5_exit : forall (r : Z) xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    P5INV mm len -> (C -> r = 1 /\ len <= len0 + 15)%Z ->
    evt usegs POST (P5 0x5e748 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM GTOP SP16 XLO XHI HCL.
    intros until len. intros INV HR. p5_open INV. p5_env.
    do 5 zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    destruct (u64arr_of_u8arr_s usegs mm X bs XA XL) as (ws & WL & EW & WA).
    apply evt_done. unfold biguN_post_g. do 15 eexists. exists mm, ws, len.
    split; [cbv delta [mkR]; reflexivity|].
    unfold P5U_STACK, LMU_STACK, LAFU_STACK, bigint_at.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [split; [exact WA| split; [exact WL| split; [exact XN| lia]]] |]. split; [exact ST|].
    intros HC. destruct (HR HC) as [-> HL]. split; [reflexivity|]. split; [|exact HL].
    apply bignorm_of_b; [rewrite EW; apply NB; exact HC | lia].
  Qed.

  Ltac sm_last lenv next :=
    fold_limbz;
    lazymatch goal with
    | XA : u8arr _ _ _ (upd_bytes (upd_bytes _ _ _) _ _) |- _ =>
        num_cur_mem ltac:(fun m1 => assert (INV1 : P5INV m1 (lenv + 1)) by
          (p5_close_with ltac:(intros _; apply bignorm_b_push; [lia | lia | lia |]; rewrite unsigned_lit_wrap; change (2 ^ 64)%Z with 18446744073709551616%Z; assumption)));
        next (lenv + 1)%Z
    | _ =>
        num_cur_mem ltac:(fun m1 => assert (INV1 : P5INV m1 lenv) by
          (p5_close_with ltac:(let HC := fresh "HC" in intros HC;
             first [ apply bignorm_b_mul_nocarry; [lazymatch goal with NB0 : C -> bignorm_b _ _ |- _ => apply NB0; exact HC end | lia | lia | lia | assumption | assumption]
                   | apply bignorm_b_mul_nocarry_z; [lazymatch goal with NB0 : C -> bignorm_b _ _ |- _ => apply NB0; exact HC end | lia | lia | lia | lia | assumption] ])));
        next lenv
    end.

  Lemma p5_M2 : forall (f : nat) (i : Z) xra xt0 xt1 xt2 xs1 xa2 (ys : word) xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    P5INV mm len -> (0 <= i < len)%Z -> (len - i <= Z.of_nat f)%Z -> (0 < bv_unsigned ys)%Z -> (C -> len <= len0 + 14)%Z ->
    evt usegs POST (P5 0x5e6bc xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 (Z_to_bv 64 1) (Z_to_bv 64 len) xa2 (Z_to_bv 64 (63 - i)) ys (Z_to_bv 64 (X + 8 * len))
                       (Z_to_bv 64 (X + 8 * i)) xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM GTOP SP16 XLO XHI HCL.
    intros f. induction f as [|f IH]; intros until len; intros INV Hi Hf HY HB; [exfalso; lia|].
    destruct (Z.eq_dec i (len - 1)) as [IT|IT].
    - pose proof INV as INV0. p5_open INV0. p5_env. ukstep.
      ukwalk ltac:(fun pc => lazymatch pc with
        | 0x5e764%Z => u_trap pc
        | 0x5e6bc%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0x5e714%Z => first [ fold_limbz; num_cur_mem ltac:(fun m1 => assert (INV1 : P5INV m1 len) by (p5_close_with ltac:(cl)));
                               zstep; zstep; eapply evt_eq; [| eapply p5_exit with (r := 0%Z)]; [num_st_eq | exact INV1 | cl] | fail 100 "cut" pc ]
        | 0x5e748%Z => first [ sm_last len ltac:(fun l => eapply evt_eq; [| eapply p5_exit with (r := 1%Z) (len := l)]; [num_st_eq | exact INV1 | cl]) | fail 100 "cut" pc ]
        end).
    - pose proof INV as INV0. p5_open INV0. p5_env.
      assert (DA2 : IsData xa2) by exact I.
      nstep.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5e764%Z => u_trap pc
        | 0x5e714%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0x5e748%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0x5e6bc%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : P5INV m1 len) by (p5_close_with nb_other));
                               eapply evt_eq; [| eapply (IH (i + 1)%Z)]; [num_st_eq | exact INV1 | lia | lia | exact HY | exact HB] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma p5_928 : forall (e : Z) xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    P5INV mm len -> (0 <= e < 256)%Z -> (len = 0 \/ e < 27)%Z -> (C -> len <= len0 + 14)%Z ->
    evt usegs POST (P5 0x5e674 xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM GTOP SP16 XLO XHI HCL.
    intros until len. intros INV He Hl HB. pose proof INV as INV0. p5_open INV0. p5_env.
    pose proof (p5u_small_at _ MI) as TBL. unfold P5U_SMALL in TBL. pose proof p5u_small_len as TBLL.
    ukwalk ltac:(fun pc => lazymatch pc with
      | 0x5e764%Z => u_trap pc
      | 0x5e748%Z => first [ eapply evt_eq; [| eapply p5_exit with (r := 1%Z)]; [num_st_eq | exact INV | cl] | fail 100 "cut" pc ]
      | 0x5e6bc%Z => first [ fold_limbz; eapply evt_eq; [| eapply (p5_M2 (Z.to_nat len) 0%Z) with (len := len)];
                             [num_st_eq | exact INV | lia | lia | replace (109664 + 8 * e - 109664)%Z with (8 * e)%Z by lia; apply p5u_small_nz; lia | exact HB] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma p5_920 : forall (e : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    P5INV mm len -> (0 <= e < 27)%Z -> (C -> len <= len0 + 14)%Z ->
    evt usegs POST (P5 0x5e66c xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM GTOP SP16 XLO XHI HCL.
    intros until len. intros INV He HB. p5_env.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e748%Z => first [ eapply evt_eq; [| eapply p5_exit with (r := 1%Z)]; [num_st_eq | exact INV | cl] | fail 100 "cut" pc ]
      | 0x5e674%Z => first [ eapply evt_eq; [| eapply (p5_928 e)]; [num_st_eq | exact INV | lia | lia | exact HB] | fail 100 "cut" pc ]
      end).
  Qed.

  Notation P27 pc e xra xt0 xt1 xt2 xa1 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm :=
    (P5 pc xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) (Z_to_bv 64 (18446744073709551615 - X)) xa1 (Z_to_bv 64 7450580596923828125)
        (Z_to_bv 64 (X + 8)) (Z_to_bv 64 26) (Z_to_bv 64 61) xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).

  Section L2BODY.
    Variable e : Z.
    Hypothesis He : (27 <= e < 2147483648)%Z.

    Hypothesis K918 : forall xra xt0 xt1 xt2 xa1 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
      P5INV mm len -> (C -> e <= e0 /\ 135 * len + 6 * e <= 135 * len0 + 6 * e0 + 135)%Z -> evt usegs POST (P27 0x5e664 e xra xt0 xt1 xt2 xa1 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).

    Lemma p5_M1 : forall (f : nat) (i : Z) xra xt2 xa6 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
      P5INV mm len -> (0 <= i < len)%Z -> (len - i <= Z.of_nat f)%Z -> POT len e ->
      evt usegs POST (P27 0x5e618 e xra (Z_to_bv 64 (X + 8 * len)) (Z_to_bv 64 (X + 8 * i)) xt2 (Z_to_bv 64 len) xa6 (Z_to_bv 64 (63 - i)) xs2 xs3 xt3 xt4 xt5 xt6 mm).
    Proof using ROOM GTOP SP16 XLO XHI HCL He K918.
      intros f. induction f as [|f IH]; intros until len; intros INV Hi Hf HP; [exfalso; lia|].
      destruct (Z.eq_dec i (len - 1)) as [IT|IT].
      - pose proof INV as INV0. p5_open INV0. p5_env. pose proof He as He'. ukstep.
        ukwalk ltac:(fun pc => lazymatch pc with
          | 0x5e764%Z => u_trap pc
          | 0x5e618%Z => first [ exfalso; lia | fail 100 "cut" pc ]
          | 0x5e714%Z => first [ fold_limbz; num_cur_mem ltac:(fun m1 => assert (INV1 : P5INV m1 len) by (p5_close_with ltac:(cl)));
                                 zstep; zstep; eapply evt_eq; [| eapply p5_exit with (r := 0%Z)]; [num_st_eq | exact INV1 | cl] | fail 100 "cut" pc ]
          | 0x5e664%Z => first [ sm_last len ltac:(fun l => eapply evt_eq; [| eapply K918 with (len := l)]; [num_st_eq | exact INV1 | cl]) | fail 100 "cut" pc ]
          end).
      - pose proof INV as INV0. p5_open INV0. p5_env.
        assert (DA6 : IsData xa6) by exact I.
        nstep.
        uwalk ltac:(fun pc => lazymatch pc with
          | 0x5e764%Z => u_trap pc
          | 0x5e714%Z => first [ exfalso; lia | fail 100 "cut" pc ]
          | 0x5e664%Z => first [ exfalso; lia | fail 100 "cut" pc ]
          | 0x5e618%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : P5INV m1 len) by (p5_close_with nb_other));
                                 eapply evt_eq; [| eapply (IH (i + 1)%Z)]; [num_st_eq | exact INV1 | lia | lia | exact HP] | fail 100 "cut" pc ]
          end).
    Qed.

    Lemma p5_8a4 : forall xra xt0 xt1 xt2 xa1 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
      P5INV mm len -> POT len e -> evt usegs POST (P27 0x5e5f0 e xra xt0 xt1 xt2 xa1 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
    Proof using ROOM GTOP SP16 XLO XHI HCL He K918.
      intros until len. intros INV HP. pose proof INV as INV0. p5_open INV0. p5_env.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5e764%Z => u_trap pc
        | 0x5e664%Z => first [ eapply evt_eq; [| eapply K918]; [num_st_eq | exact INV | cl] | fail 100 "cut" pc ]
        | 0x5e618%Z => first [ eapply evt_eq; [| eapply (p5_M1 (Z.to_nat len) 0%Z) with (len := len)]; [num_st_eq | exact INV | lia | lia | exact HP] | fail 100 "cut" pc ]
        end).
    Qed.
  End L2BODY.

  Lemma p5_918 : forall (f : nat) (e : Z), (27 <= e < 2147483648)%Z -> (e <= 27 * Z.of_nat f)%Z ->
    forall xra xt0 xt1 xt2 xa1 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    P5INV mm len -> (C -> e <= e0 /\ 135 * len + 6 * e <= 135 * len0 + 6 * e0 + 135)%Z -> evt usegs POST (P27 0x5e664 e xra xt0 xt1 xt2 xa1 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM GTOP SP16 XLO XHI HCL.
    intros f. induction f as [|f IH]; intros e He Hf; [exfalso; lia|].
    intros until len. intros INV HP. p5_env.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e66c%Z => first [ eapply evt_eq; [| eapply (p5_920 (e - 27)%Z)]; [num_st_eq | exact INV | lia | cl] | fail 100 "cut" pc ]
      | 0x5e5f0%Z => first [ eapply evt_eq; [| eapply (p5_8a4 (e - 27)%Z ltac:(lia))]; [num_st_eq | | exact INV | cl];
                             intros; eapply (IH (e - 27)%Z); [lia | lia | eassumption | eassumption] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma p5_874 : forall (e : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    P5INV mm len -> (0 <= e < 135)%Z -> POT len e ->
    evt usegs POST (P5 0x5e5c0 xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM GTOP SP16 XLO XHI HCL.
    intros until len. intros INV He HP. pose proof INV as INV0. p5_open INV0. p5_env.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e764%Z => u_trap pc
      | 0x5e748%Z => first [ eapply evt_eq; [| eapply p5_exit with (r := 1%Z)]; [num_st_eq | exact INV | cl] | fail 100 "cut" pc ]
      | 0x5e66c%Z => first [ eapply evt_eq; [| eapply (p5_920 e)]; [num_st_eq | exact INV | lia | cl] | fail 100 "cut" pc ]
      | 0x5e674%Z => first [ eapply evt_eq; [| eapply (p5_928 _)]; [num_st_eq | exact INV | | left; lia | cl];
                             lazymatch goal with |- (0 <= Z.land ?x 255 < 256)%Z =>
                               change 255%Z with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia end
                           | fail 100 "cut" pc ]
      | 0x5e664%Z => first [ eapply evt_eq; [| eapply (p5_918 (Z.to_nat e) e)]; [num_st_eq | lia | lia | exact INV | cl] | fail 100 "cut" pc ]
      | 0x5e618%Z => first [ eapply evt_eq; [| eapply (p5_M1 e ltac:(lia) (p5_918 (Z.to_nat e) e ltac:(lia) ltac:(lia)) (Z.to_nat len) 0%Z) with (len := len)];
                             [num_st_eq | exact INV | lia | lia | exact HP] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma p5_L1 : forall (f : nat) (e : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm len,
    P5INV mm len -> (-2147483648 <= e < 2147483648)%Z -> (e < 0 \/ 135 <= e)%Z -> (e mod 4294967296 <= 135 * Z.of_nat f)%Z -> POT len e ->
    evt usegs POST (P5 0x5e5a4 xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 0x1ac38) (Z_to_bv 64 134) xt3 xt4 xt5 xt6 mm).
  Proof using HLM ROOM GTOP SP16 XLO XHI HCL.
    intros f. induction f as [|f IH]; intros until len; intros INV He Hout Hf HP.
    { exfalso. lia. }
    p5_open INV. p5_env.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    destruct (image_readable_b usegs mm 40 0x1ac38 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (yb & YL & YB).
    zstep. zstep. zstep. zstep.
    destruct (u64arr_of_u8arr usegs mm X bs XA XL) as (ws & WL & WA).
    pose proof HLM as HM. unfold p5N_lm_stmt, lmuN_stmt_g in HM.
    eapply evt_cut.
    { eapply HM with (X := X) (Y := 0x1ac38%Z) (ny := 5%Z) (lo := lo) (ws := ws) (len := len) (ybs := yb);
        rewrite ?unsigned_lit by lia; unfold LMU_STACK, LAFU_STACK;
        [ exact MI | exact ST | lia | Z.div_mod_to_equations; lia | split; [exact WA| split; [exact WL| split; [exact XN| lia]]] | lia | lia
        | exact YB | rewrite YL; reflexivity | lia | lia | reflexivity | lia ]. }
    cbv beta. intros ms' P. unfold biguN_post_g in P.
    destruct P as (? & ? & ? & r0 & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & ws3 & len3 & -> & MUc & WMc & MIc & BIG & STc & G).
    rewrite !unsigned_lit in MUc, STc by lia. unfold LMU_STACK, LAFU_STACK in MUc.
    assert (G' : C -> (bv_unsigned r0 = 1 /\ len3 <= len + 6)%Z /\ bignorm ws3 len3).
    { intros HC. destruct (HP HC) as (HP1 & HP2). destruct (HCL' HC) as (HC1 & HC2). unfold lmuN_G in G.
      destruct (G ltac:(lia)) as (-> & GN & GL). rewrite unsigned_lit by lia. split; [lia | exact GN]. }
    clear G XA XN WA NB.
    transport_after_call usegs mm m3 MUc WMc.
    clear MUc WMc MI HM YB. destruct BIG as (WA3 & WL3 & XN & LEN3).
    num_ret_pc.
    pose proof (u8arr_of_u64arr_s usegs m3 X ws3 WA3) as XA. assert (XL3 : length (u64s ws3) = 496%nat) by (rewrite u64s_length, WL3; reflexivity).
    assert (NB : C -> bignorm_b (u64s ws3) len3) by (intros HC; apply bignorm_b_of; [apply G'; exact HC | lia]).
    clear WA3.
    rename MIc into MI. rename STc into ST.
    assert (INV3 : P5INV m3 len3) by (p5_close_with ltac:(exact NB)).
    assert (GL : (C -> bv_unsigned r0 = 1 /\ len3 <= len + 6)%Z) by (intros HC; apply G'; exact HC).
    clear G'.
    zstep.
    if_cases K0; zify_cond K0.
    { rewrite <- (Z_to_bv_bv_unsigned r0). eapply evt_eq; [| eapply p5_exit with (r := bv_unsigned r0)]; [num_st_eq | exact INV3 | cl]. }
    zstep. rewrite bv_swrap32, swrap32_mod64.
    replace (e + -135)%Z with (e - 135)%Z by lia.
    pose proof (pow5_large_step e He Hout) as [STEP GE].
    pose proof (swrap32_range (e - 135)) as ER.
    assert (EE : C -> swrap32 (e - 135) = (e - 135)%Z).
    { intros HC. destruct (HP HC) as (HP1 & HP2). destruct (HCL' HC) as (HC1 & HC2). apply swrap32_small. lia. }
    set (e' := swrap32 (e - 135)) in *. clearbody e'.
    zstep.
    if_cases K; zify_cond K.
    - apply (s32_gtu e' 134 ER ltac:(lia)) in K.
      eapply IH; [exact INV3 | exact ER | lia | lia | cl].
    - assert (K' : (0 <= e' <= 134)%Z) by (apply (s32_leu e' 134 ER ltac:(lia)); lia).
      eapply p5_874; [exact INV3 | lia | cl].
  Qed.

  Lemma p5_body : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ws,
    mem_inv usegs m0 -> stk usegs m0 lo SP -> bigint_at usegs m0 X ws len0 -> (C -> bignorm ws len0) ->
    (-2147483648 <= e0 < 2147483648)%Z ->
    evt usegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 e0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 P5N_ENTRY) fc None m0 (seg_rom usegs)).
  Proof using HLM ROOM GTOP SP16 XLO XHI HCL.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ws MI ST (WA & WL & XN & LEN) NORM He.
    unfold P5N_ENTRY. p5_env.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl usegs m0) as WM. unfold P5U_STACK, LMU_STACK, LAFU_STACK in MU.
    set (m := m0) in MI, ST, WA, XN, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 48%nat ST.
    apply (rw_cells_split_CB usegs m _ [] 48 junk [] [8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 5 step. zstep. zstep. zstep. zstep.
    pose proof (u8arr_of_u64arr_s usegs _ X ws WA) as XA. assert (XL : length (u64s ws) = 496%nat) by (rewrite u64s_length, WL; reflexivity).
    assert (NB : C -> bignorm_b (u64s ws) len0) by (intros HC; apply bignorm_b_of; [apply NORM; exact HC | lia]).
    clear WA.
    num_cur_mem ltac:(fun mm => assert (INV : P5INV mm len0) by (p5_close_with ltac:(exact NB))).
    assert (HP0 : POT len0 e0) by cl.
    if_cases K; zify_cond K.
    - assert (K' : (0 <= e0 <= 134)%Z) by (apply (s32_leu e0 134 He ltac:(lia)); lia).
      eapply p5_874; [exact INV | lia | exact HP0].
    - assert (K1 : (134 < e0 mod 18446744073709551616)%Z) by lia.
      assert (K' : (e0 < 0 \/ 135 <= e0)%Z) by (apply (s32_gtu e0 134 He ltac:(lia)) in K1; lia).
      zstep. zstep. zstep.
      eapply evt_eq; [| eapply (p5_L1 (Z.to_nat 4294967296) e0)]; [num_st_eq | exact INV | exact He | exact K' | | exact HP0].
      pose proof (Z.mod_pos_bound e0 4294967296 ltac:(lia)). lia.
  Qed.
End P5N.

Theorem p5uN_spec : p5N_lm_stmt -> p5uN_stmt_g usegs P5N_ENTRY NUMU_GTOP.
Proof.
  intros HL. unfold p5uN_stmt_g. intros until len. intros MI ST ROOM GTOP SP16 BIG XLO XHI He.
  eapply evt_mono.
  { eapply (p5_body HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo len e m (bignorm ws len /\ len + 15 <= 62 /\ 0 <= e <= 328)%Z);
      try eassumption; intros (HA & HB & HD); first [exact HA | split; assumption]. }
  cbv beta. intros ms' P. unfold biguN_post_g in *.
  destruct P as (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & q14 & m' & ws' & len' & E & H1 & H2 & H3 & H4 & H5 & G).
  exists q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, m', ws', len'.
  repeat (split; [assumption|]). unfold p5uN_G. intros HN HCAP HE. apply G. split; [exact HN|]. split; [exact HCAP | exact HE].
Qed.
