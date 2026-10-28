(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_hi64.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.
Local Ltac num_abstract_data ::= num_abstract_data_u.

Section PDC.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation W := [(SP - 64, SP); (X, X + 504)]%Z.
  Hypothesis ROOM : (lo + 64 <= SP)%Z.
  Hypothesis TOP : (SP <= USTACK_TOP)%Z.
  Hypothesis X0 : (0x6ce000 <= X)%Z.
  Hypothesis XLO : (X + 504 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis SHPX : forall m', munch W m0 m' -> wmono bsegs m0 m' -> shz m' X 504.
  Hypothesis SHPS : forall m', munch W m0 m' -> wmono bsegs m0 m' -> shz m' (SP - 64) 64.
  Variable Q : machine_state -> Prop.

  Notation PD pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 (SP + -48)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Definition PDINV (mm : mem) (len : Z) (tb : byte) : Prop :=
    (exists j, rw_cells bsegs mm (SP + -48) [CB 15 j]) /\ rw_cells bsegs mm (SP + -33) [C1 tb] /\
    rw_cells bsegs mm (SP + -32) [C8 s2; C8 s1; C8 s0; C8 ra] /\
    (exists bs, u8arr bsegs mm X bs /\ length bs = 496%nat /\ bignorm_b bs len) /\
    rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    mem_inv bsegs mm /\ munch W m0 mm /\ wmono bsegs m0 mm /\ stk bsegs mm lo (SP + -48).

  Ltac pd_open H :=
    let j := fresh "j" in let bs := fresh "bs" in
    destruct H as ((j & PAD) & TC & FR & (bs & XA & ?XL & NB) & XN & ?LEN & MI & MU & WM & ST).
  Ltac pd_close :=
    lazymatch goal with
    | |- PDINV _ _ _ =>
        split; [eexists; eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eexists; split; [eassumption| split; [lia | eassumption]]|];
        split; [eassumption|]; split; [lia|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
    end.
  Ltac pd_env :=
    pose proof ROOM as ROOM'; pose proof TOP as TOP'; unfold USTACK_TOP in TOP';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof X0 as X0'; pose proof XLO as XLO'; pose proof X8 as X8'.

  Definition pd_ret_k : Prop :=
    forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm bs len,
      u8arr bsegs mm X bs -> length bs = 496%nat -> rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 len)] -> (0 <= len <= 62)%Z ->
      mem_inv bsegs mm -> munch W m0 mm -> wmono bsegs m0 mm -> stk bsegs mm lo SP ->
      Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None mm (seg_rom bsegs)).
  Hypothesis KRET : pd_ret_k.

  Lemma pd_exit : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mm len tb,
    PDINV mm len tb ->
    evt bsegs Q (PD 0xec260 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM TOP X0 XLO X8 SHPX SHPS KRET.
    intros until tb. intros INV. pd_open INV. pd_env.
    do 4 zstep. zstep. zstep.
    release_frame PAD ST (SP + -33)%Z.
    release_frame TC ST (SP + -32)%Z.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. eapply KRET; eassumption.
  Qed.

  Lemma pd_cb4 : forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm len t,
    PDINV mm len (Z_to_bv 8 t) -> (0 <= t <= 1)%Z ->
    evt bsegs Q (PD 0xec0b8 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 2147450880) xt3 xt4 xt5 xt6 mm).
  Proof using ROOM TOP X0 XLO X8 SHPX SHPS KRET.
    intros until t. intros INV Ht. pose proof INV as INV0. pd_open INV. pd_env.
    assert (DA0 : IsData xa0) by exact I.
    pose proof (unsigned_lit8 t ltac:(lia)) as HT8.
    bkwalk ltac:(fun pc => lazymatch pc with 0xec1fc%Z => u_trap pc | 0xec104%Z => idtac | 0xec1ec%Z => idtac end).
    -
      bwalk ltac:(fun pc => lazymatch pc with
        | 0xec1fc%Z => u_trap pc
        | 0xec260%Z => first [ eapply pd_exit; exact INV0 | fail 100 "cut" pc ]
        end).
    - zstep. if_cases KCLZ; zify_cond KCLZ; [u_clz_dead NB KCLZ|].
      bwalk ltac:(fun pc => lazymatch pc with
        | 0xec1fc%Z => u_trap pc
        | 0xec260%Z => first [ eapply pd_exit; exact INV0 | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma pd_ca8 : forall xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm len tb,
    PDINV mm len tb -> b_consts mm ->
    evt bsegs Q (PD 0xec0ac xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 2147450880) xt3 xt4 xt5 xt6 mm).
  Proof using ROOM TOP X0 XLO X8 SHPX SHPS KRET.
    intros until tb. intros INV GC. pd_open INV. pd_env.
    bstep. bstep. bstep.
    eapply evt_cut.
    { eapply evt_eq; [| eapply hi64b_spec with (X := X) (T := (SP + -33)%Z) (len := len) (lo := lo) (tc0 := tb) (bs := bs)];
        [num_st_eq | ..]; rewrite ?unsigned_lit by lia; unfold HI64B_STACK, USTACK_TOP;
        [ lia | lia | lia | lia | lia
        | intros m' MU' WM'; apply SHPX; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU']; intros x; cbn [outside]; lia | eapply wmono_trans; eassumption]
        | intros m' MU' WM'; eapply shz_sub; [apply SHPS; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU']; intros x; cbn [outside]; lia | eapply wmono_trans; eassumption]| lia | lia]
        | exact MI | exact ST | exact GC | exact TC | exact XA | exact XL | exact NB | exact XN | lia ]. }
    cbv beta. intros ms' P. unfold hi64b_post in P.
    destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & tb5 & -> & MUc & WMc & MIc & STc & TC5 & TB).
    rewrite ?unsigned_lit in MUc, STc by lia. unfold HI64B_STACK in MUc.
    clear TC GC.
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call bsegs mo mn MUc WMc end.
    clear MUc WMc MI. rename MIc into MI. rename STc into ST.
    num_ret_pc.
    assert (INV : PDINV m5 len (Z_to_bv 8 tb5)) by pd_close.
    eapply evt_eq; [| eapply pd_cb4 with (len := len)]; [num_st_eq | exact INV | lia].
  Qed.
End PDC.
