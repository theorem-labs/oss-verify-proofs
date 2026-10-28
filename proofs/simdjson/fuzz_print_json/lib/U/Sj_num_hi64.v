(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu Sj_num_kitn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.
Local Ltac num_abstract_data ::= num_abstract_data_u.

Definition HI64U_ENTRY : Z := 0x5e634.

Section HI64.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X T len : Z) (m0 : mem).
  Hypothesis XHI : (X + 498 <= 2^64)%Z.
  Hypothesis TX : (T + 1 <= X)%Z.
  Hypothesis T0 : (0 <= T)%Z.

  Notation POST := (hi64u_post_g usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T m0).
  Notation HI pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition HIINV (mm : mem) : Prop :=
    (exists b, rw_cells usegs mm T [C1 b]) /\
    (exists bs, u8arr usegs mm X bs /\ length bs = 496%nat /\ bignorm_b bs len) /\
    rw_cells usegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    mem_inv usegs mm /\ munch [(T, T + 1)]%Z m0 mm /\ wmono usegs m0 mm.

  Ltac hi_open H :=
    let bs := fresh "bs" in
    let b := fresh "b" in destruct H as ((b & TC) & (bs & XA & ?XL & NB) & XN & ?LEN & MI & MU & WM).
  Ltac hi_close :=
    lazymatch goal with
    | |- HIINV _ =>
        split; [eexists; eassumption|]; split; [eexists; split; [eassumption| split; [lia | eassumption]]|]; split; [eassumption|]; split; [lia|];
        split; [eassumption|]; split; eassumption
    end.
  Ltac hi_env :=
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof XHI as XHI'; change (2 ^ 64)%Z with 18446744073709551616%Z in XHI';
    pose proof TX as TX'; pose proof T0 as T0'.

  Ltac hi_done :=
    zstep; apply evt_done; unfold hi64u_post_g; do 15 eexists;
    lazymatch goal with
    | TC : rw_cells usegs ?m T [C1 (Z_to_bv 8 ?tb)] |- _ =>
        exists m, tb; split; [cbv delta [mkR]; reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [exact TC|]
    end.

  Lemma hi_800 : forall xt0 xt1 xt2 xa0 xa2 xa3 xa6 xa7 xt3 xt4 xt5 xt6 mm t4 t5,
    HIINV mm -> (0 <= t4 <= 1)%Z -> (0 <= t5 <= 1)%Z ->
    evt usegs POST (HI 0x5e85c xt0 xt1 xt2 xa0 (Z_to_bv 64 T) xa2 xa3 (Z_to_bv 64 t4) (Z_to_bv 64 t5) xa6 xa7 xt3 xt4 xt5 xt6 mm).
  Proof using XHI TX T0.
    intros until t5. intros INV H4 H5. hi_open INV. hi_env.
    pose proof (lor_bit t4 t5 H4 H5) as HB.
    ukstep. ukstep. ukstep. hi_done. rewrite unsigned_lit by lia. lia.
  Qed.

  Lemma hi_L : forall (f : nat) (k : Z) xt0 xt1 xt2 xa2 xa5 xa6 xt3 xt4 xt5 xt6 mm t4,
    HIINV mm -> (0 <= t4 <= 1)%Z -> (0 <= k <= len - 3)%Z -> (k <= Z.of_nat f)%Z ->
    evt usegs POST (HI 0x5e83c xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 T) xa2 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 t4) xa5 xa6
                       (Z_to_bv 64 (8 * k)) xt3 xt4 xt5 xt6 mm).
  Proof using XHI TX T0.
    intros f. induction f as [|f IH]; intros until t4; intros INV H4 Hk Hf.
    - assert (k = 0)%Z by lia. subst k. pose proof INV as INV0. hi_open INV0. hi_env.
      nstep.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5e87c%Z => u_trap pc
        | 0x5e85c%Z => first [ eapply evt_eq; [| eapply hi_800]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
        end).
    - pose proof INV as INV0. hi_open INV0. hi_env.
      nstep.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5e87c%Z => u_trap pc
        | 0x5e85c%Z => first [ eapply evt_eq; [| eapply hi_800]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
        | 0x5e83c%Z => first [ eapply evt_eq; [| eapply (IH (k - 1)%Z)]; [num_st_eq | exact INV | lia | lia | lia] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma hi_7c0 : forall xt0 xt1 xt2 xa2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm t4,
    HIINV mm -> (0 <= t4 <= 1)%Z ->
    evt usegs POST (HI 0x5e81c xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 T) xa2 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 t4) xa5 xa6 xa7
                       xt3 xt4 xt5 xt6 mm).
  Proof using XHI TX T0.
    intros until t4. intros INV H4. pose proof INV as INV0. hi_open INV0. hi_env.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e87c%Z => u_trap pc
      | 0x5e878%Z => first [ hi_done; rewrite Z.lor_0_r; rewrite unsigned_lit by lia; lia | fail 100 "cut" pc ]
      | 0x5e83c%Z => first [ eapply evt_eq; [| eapply (hi_L (Z.to_nat len) (len - 3)%Z)]; [num_st_eq | exact INV | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma hi_body : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm,
    HIINV mm ->
    evt usegs POST (HI HI64U_ENTRY t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 T) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm).
  Proof using XHI TX T0.
    intros until mm. intros INV. unfold HI64U_ENTRY.
    hi_open INV. hi_env.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5e650%Z => idtac
      | 0x5e71c%Z => idtac
      | 0x5e64c%Z => first [ hi_done; rewrite unsigned_lit by lia; lia | fail 100 "cut" pc ]
      end).
    -
      ukwalk ltac:(fun pc => lazymatch pc with 0x5e87c%Z => u_trap pc | 0x5e66c%Z => idtac end).
      zstep. if_cases KB1; zify_cond KB1; [u_clz_dead NB KB1|].
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5e718%Z => first [ hi_done; rewrite unsigned_lit by lia; lia | fail 100 "cut" pc ]
        end).
    -
      ukwalk ltac:(fun pc => lazymatch pc with 0x5e87c%Z => u_trap pc | 0x5e748%Z => idtac end).
      zstep. if_cases KBz; zify_cond KBz; [u_clz_dead NB KBz|].
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5e87c%Z => u_trap pc
        | 0x5e81c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : HIINV m1) by hi_close);
                               eapply evt_eq; [| eapply hi_7c0]; [num_st_eq | exact INV1 | lia] | fail 100 "cut" pc ]
        end).
  Qed.
End HI64.

Theorem hi64u_spec : hi64u_stmt_g usegs HI64U_ENTRY.
Proof.
  unfold hi64u_stmt_g. intros until tb0. intros MI (WA & WL & XN & LEN) NORM XHI TC T0 TX.
  pose proof (u8arr_of_u64arr_s usegs m X ws WA) as XA.
  eapply hi_body; try eassumption.
  split; [exists tb0; exact TC|]. split.
  { exists (u64s ws). split; [exact XA|]. split; [rewrite u64s_length, WL; reflexivity|]. apply bignorm_b_of; [exact NORM | lia]. }
  split; [exact XN|]. split; [exact LEN|]. split; [exact MI|]. split; [apply munch_refl | apply wmono_refl].
Qed.
