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
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs.
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

Definition hi64b_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (T lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' tb,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - HI64B_STACK, bv_unsigned sp); (T, T + 1)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' T [C1 (Z_to_bv 8 tb)] /\ (0 <= tb <= 1)%Z.

Section HI64.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X T len lo : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation W := [(SP - HI64B_STACK, SP); (T, T + 1)]%Z.
  Hypothesis ROOM : (lo + HI64B_STACK <= SP)%Z.
  Hypothesis X0 : (0x6ce000 <= X)%Z.
  Hypothesis XLO : (X + 504 <= lo)%Z.
  Hypothesis TLO : (SP <= T)%Z.
  Hypothesis THI : (T + 1 <= USTACK_TOP)%Z.

  Hypothesis SHPX : forall m', munch W m0 m' -> wmono bsegs m0 m' -> shz m' X 504.
  Hypothesis SHPT : forall m', munch W m0 m' -> wmono bsegs m0 m' -> shz m' T 1.

  Notation POST := (hi64b_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T lo m0).
  Notation HI pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Definition HIINV (mm : mem) (tc : byte) : Prop :=
    (exists j0, rw_cells bsegs mm (SP + -16) [CB 8 j0; C8 ra]) /\
    rw_cells bsegs mm T [C1 tc] /\
    (exists bs, u8arr bsegs mm X bs /\ length bs = 496%nat /\ bignorm_b bs len) /\
    rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    mem_inv bsegs mm /\ munch W m0 mm /\ wmono bsegs m0 mm /\ stk bsegs mm lo (SP + -16).

  Ltac hi_open H :=
    let bs := fresh "bs" in let j0 := fresh "j0" in
    destruct H as ((j0 & FR) & TC & (bs & XA & ?XL & NB) & XN & ?LEN & MI & MU & WM & ST); unfold HI64B_STACK in MU.
  Ltac hi_close :=
    lazymatch goal with
    | |- HIINV _ _ =>
        split; [eexists; eassumption|]; split; [eassumption|]; split; [eexists; split; [eassumption| split; [lia | eassumption]]|];
        split; [eassumption|]; split; [lia|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
    end.
  Ltac hi_env :=
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof ROOM as ROOM'; unfold HI64B_STACK in ROOM'; pose proof X0 as X0'; pose proof XLO as XLO'; pose proof TLO as TLO';
    pose proof THI as THI'; unfold USTACK_TOP in THI'.

  Ltac hi_done :=
    zstep; zstep; zstep;
    lazymatch goal with FRh : rw_cells bsegs _ _ [CB 8 _; C8 _], STh : stk bsegs _ _ _ |- _ => release_frame FRh STh (bv_unsigned sp) end;
    apply evt_done; unfold hi64b_post; do 15 eexists;
    lazymatch goal with
    | TC : rw_cells bsegs ?m T [C1 (Z_to_bv 8 ?tb)] |- _ =>
        exists m, tb; split; [cbv delta [mkR]; reflexivity|]; unfold HI64B_STACK;
        split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [exact TC|]
    end.

  Lemma hi_904 : forall xt0 xt1 xt2 xa2 xa4 xa5 xa6 xt3 xt4 xt5 xt6 mm tc t3v t0v,
    HIINV mm tc -> (0 <= t3v <= 1)%Z -> (0 <= t0v <= 1)%Z ->
    evt bsegs POST (HI 0xecd08 xt0 xt1 xt2 (Z_to_bv 64 t0v) (Z_to_bv 64 T) xa2 (Z_to_bv 64 t3v) xa4 xa5 xa6 (Z_to_bv 64 (T / 8 + 2147450880)) xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO TLO THI SHPX SHPT.
    intros until t0v. intros INV H3 H0. hi_open INV. hi_env.
    pose proof (lor_bit t3v t0v H3 H0) as HB.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xecd1c%Z => first [ hi_done; rewrite unsigned_lit by lia; lia | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma hi_8e4 : forall xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xt3 xt4 xt5 xt6 mm t4v,
    HIINV mm (Z_to_bv 8 t4v) -> (0 <= t4v <= 1)%Z -> IsData xa6 ->
    evt bsegs POST (HI 0xecce8 xt0 xt1 xt2 xa0 (Z_to_bv 64 T) xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (T / 8 + 2147450880)) xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO TLO THI SHPX SHPT.
    intros until t4v. intros INV H4 DM. pose proof INV as INV0. hi_open INV0. hi_env.
    bstep. bstep. if_cases KA; zify_cond KA; [exfalso; lia|].
    bkstep. rewrite (unsigned_lit8 t4v) by lia.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xecd28%Z => u_trap pc
      | 0xecd08%Z => first [ eapply evt_eq; [| eapply hi_904]; [num_st_eq | exact INV | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma hi_L : forall (f : nat) (k : Z) xt0 xt1 xt2 xa2 xa6 xt3 xt4 xt5 xt6 mm t4v,
    HIINV mm (Z_to_bv 8 t4v) -> (0 <= t4v <= 1)%Z -> (0 <= k <= len - 3)%Z -> (k <= Z.of_nat f)%Z ->
    evt bsegs POST (HI 0xeccbc xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 T) xa2 (Z_to_bv 64 (8 * k)) (Z_to_bv 64 2147450880)
                       (Z_to_bv 64 (18446744073709551615 - X)) xa6 (Z_to_bv 64 (T / 8 + 2147450880)) xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO TLO THI SHPX SHPT.
    intros f. induction f as [|f IH]; intros until t4v; intros INV H4 Hk Hf.
    - assert (k = 0)%Z by lia. subst k. pose proof INV as INV0. hi_open INV0. hi_env.
      bstep.
      bwalk ltac:(fun pc => lazymatch pc with
        | 0xecd28%Z => u_trap pc
        | 0xecce8%Z => first [ eapply evt_eq; [| eapply hi_8e4]; [num_st_eq | exact INV | lia | assumption] | fail 100 "cut" pc ]
        end).
    - pose proof INV as INV0. hi_open INV0. hi_env.
      bstep.
      bwalk ltac:(fun pc => lazymatch pc with
        | 0xecd28%Z => u_trap pc
        | 0xecce8%Z => first [ eapply evt_eq; [| eapply hi_8e4]; [num_st_eq | exact INV | lia | assumption] | fail 100 "cut" pc ]
        | 0xeccbc%Z => first [ eapply evt_eq; [| eapply (IH (k - 1)%Z)]; [num_st_eq | exact INV | lia | lia | lia] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma hi_body : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 tc0 (bs0 : list byte),
    mem_inv bsegs m0 -> stk bsegs m0 lo SP -> b_consts m0 ->
    rw_cells bsegs m0 T [C1 tc0] -> u8arr bsegs m0 X bs0 -> length bs0 = 496%nat -> bignorm_b bs0 len ->
    rw_cells bsegs m0 (X + 496) [C2 (Z_to_bv 64 len)] -> (0 <= len <= 62)%Z ->
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 T) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 B_HI64) fc None m0 (seg_rom bsegs)).
  Proof using ROOM X0 XLO TLO THI SHPX SHPT.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 tc0 bs0 MI ST (G1 & G2) TC XA XL NB XN LEN.
    unfold B_HI64. hi_env.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl bsegs m0) as WM. unfold HI64B_STACK in MU.
    set (m := m0) in MI, ST, G1, G2, TC, XA, XN, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 16%nat ST.
    apply (rw_cells_split_CB bsegs m _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    step. bstep. bstep. bstep. clear G1 G2.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xecd28%Z => u_trap pc
      | 0xeca88%Z => idtac
      | 0xecb7c%Z => idtac
      | 0xeca7c%Z => first [ hi_done; rewrite unsigned_lit by lia; lia | fail 100 "cut" pc ]
      end).
    -
      bkwalk ltac:(fun pc => lazymatch pc with 0xecd28%Z => u_trap pc | 0xecac4%Z => idtac end).
      zstep. if_cases KCLZ1; zify_cond KCLZ1; [u_clz_dead NB KCLZ1|].
      bwalk ltac:(fun pc => lazymatch pc with
        | 0xecb70%Z => first [ hi_done; rewrite unsigned_lit by lia; lia | fail 100 "cut" pc ]
        end).
    -
      bkwalk ltac:(fun pc => lazymatch pc with 0xecd28%Z => u_trap pc | 0xecbcc%Z => idtac end).
      zstep. if_cases KCLZ2; zify_cond KCLZ2; [u_clz_dead NB KCLZ2|].
      bwalk ltac:(fun pc => lazymatch pc with
        | 0xecd28%Z => u_trap pc
        | 0xeccbc%Z => first [ rewrite (unsigned_lit tb) in TC by lia;
                               num_cur_mem ltac:(fun m1 => assert (INV1 : HIINV m1 (Z_to_bv 8 tb)) by hi_close);
                               eapply evt_eq; [| eapply (hi_L (Z.to_nat len) (len - 3)%Z)]; [num_st_eq | exact INV1 | lia | lia | lia] | fail 100 "cut" pc ]
        | 0xecd04%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : HIINV m1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 tb)))) by hi_close);
                               bstep; eapply evt_eq; [| eapply (hi_904 _ _ _ _ _ _ _ _ _ _ _ _ _ tb 0%Z)]; [num_st_eq | exact INV1 | lia | lia] | fail 100 "cut" pc ]
        end).
  Qed.
End HI64.

Definition hi64b_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X T len lo : Z) (tc0 : byte) (bs : list byte),
  (lo + HI64B_STACK <= bv_unsigned sp)%Z -> (0x6ce000 <= X)%Z -> (X + 504 <= lo)%Z -> (bv_unsigned sp <= T)%Z -> (T + 1 <= USTACK_TOP)%Z ->
  (forall m', munch [(bv_unsigned sp - HI64B_STACK, bv_unsigned sp); (T, T + 1)]%Z m m' -> wmono bsegs m m' -> shz m' X 504) ->
  (forall m', munch [(bv_unsigned sp - HI64B_STACK, bv_unsigned sp); (T, T + 1)]%Z m m' -> wmono bsegs m m' -> shz m' T 1) ->
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> b_consts m ->
  rw_cells bsegs m T [C1 tc0] -> u8arr bsegs m X bs -> length bs = 496%nat -> bignorm_b bs len ->
  rw_cells bsegs m (X + 496) [C2 (Z_to_bv 64 len)] -> (0 <= len <= 62)%Z ->
  evt bsegs (hi64b_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 T) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 B_HI64) fc None m (seg_rom bsegs)).

Theorem hi64b_spec : hi64b_stmt.
Proof.
  unfold hi64b_stmt. intros until bs. intros ROOM X0 XLO TLO THI SHPX SHPT MI ST GC TC XA XL NB XN LEN.
  eapply hi_body; eassumption.
Qed.
