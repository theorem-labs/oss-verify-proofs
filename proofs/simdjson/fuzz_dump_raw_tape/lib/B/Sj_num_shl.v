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
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_ptr_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Lemma shiftr_word_small : forall (w : word) k, (0 <= k)%Z -> (0 <= Z.shiftr (bv_unsigned w) k < 18446744073709551616)%Z.
Proof.
  intros w k Hk. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R.
  rewrite Z.shiftr_div_pow2 by lia. assert (P : (0 < 2 ^ k)%Z) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Section SHL.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo n : Z) (m0 : mem) (len0 : Z) (C : Prop).
  Notation SP := (bv_unsigned sp).
  Notation W := [(SP - 64, SP); (X, X + 504)]%Z.
  Hypothesis ROOM : (lo + 64 <= SP)%Z.
  Hypothesis X0 : (0x6ce000 <= X)%Z.
  Hypothesis XLO : (X + 504 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis NR : (0 <= n < 18446744073709551616)%Z.
  Hypothesis HCAP : C -> (len0 + n / 64 + 1 <= 62)%Z.
  Hypothesis SHPX : forall m', munch W m0 m' -> wmono bsegs m0 m' -> shz m' X 504.
  Variable Q : machine_state -> Prop.

  Notation SH pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 (SP + -64)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6
             s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Definition SHINV (mm : mem) (len tl : Z) (P : Prop) : Prop :=
    rw_cells bsegs mm (SP + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    (exists bs, u8arr bsegs mm X bs /\ length bs = 496%nat /\ (P -> bignorm_b bs tl)) /\
    rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    mem_inv bsegs mm /\ munch W m0 mm /\ wmono bsegs m0 mm /\ stk bsegs mm lo (SP + -64).

  Ltac sh_open H :=
    let bs := fresh "bs" in
    destruct H as (FR & (bs & XA & ?XL & NB) & XN & ?LEN & MI & MU & WM & ST).
  Ltac sh_close_with nb :=
    lazymatch goal with
    | |- SHINV _ _ _ _ =>
        split; [eassumption|]; split; [eexists; split; [eassumption| split; [lia | nb]]|]; split; [eassumption|]; split; [lia|];
        split; [eassumption|]; split; [eassumption|]; split; eassumption
    end.
  Ltac sh_env :=
    pose proof ROOM as ROOM'; pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof X0 as X0'; pose proof XLO as XLO'; pose proof X8 as X8'; pose proof NR as NR'; pose proof HCAP as HCAP'.

  Ltac sh_st_eq_leaf :=
    lazymatch goal with
    | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia | f_equal; Z.div_mod_to_equations; lia | word_eq_tac]
    | |- _ => reflexivity
    end.
  Ltac sh_st_eq_tree :=
    lazymatch goal with
    | |- TNode _ _ _ = TNode _ _ _ => f_equal; sh_st_eq_tree
    | |- Some _ = Some _ => f_equal; sh_st_eq_leaf
    | |- _ => reflexivity
    end.
  Ltac sh_st_eq := cbv delta [mkR]; lazymatch goal with |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; sh_st_eq_tree end.

  Definition sh_ret_k : Prop :=
    forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm bs len (r : Z),
      u8arr bsegs mm X bs -> length bs = 496%nat -> rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 len)] -> (0 <= len <= 62)%Z ->
      mem_inv bsegs mm -> munch W m0 mm -> wmono bsegs m0 mm -> stk bsegs mm lo SP ->
      (C -> r = 1 /\ bignorm_b bs len /\ len <= len0 + n / 64 + 1)%Z ->
      Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None mm (seg_rom bsegs)).
  Hypothesis KRET : sh_ret_k.

  Lemma sh_exit : forall (r : Z) xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm len,
    SHINV mm len len C -> (C -> r = 1 /\ len <= len0 + n / 64 + 1)%Z ->
    evt bsegs Q (SH 0xee440 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO X8 NR HCAP SHPX KRET.
    intros until len. intros INV HR. sh_open INV. sh_env.
    do 8 zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. eapply KRET; try eassumption.
    intros HC. destruct (HR HC) as [-> HL]. split; [reflexivity|]. split; [exact (NB HC)| exact HL].
  Qed.

  Lemma sh_028 : forall (sv : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xt3 xt4 xt5 xt6 mm len,
    SHINV mm len len C -> (0 <= sv < 2^60)%Z -> (C -> sv <= 62 /\ len <= len0 + n / 64 + 1)%Z ->
    evt bsegs Q (SH 0xee42c xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 sv) xs5 xs6 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO X8 NR HCAP SHPX KRET.
    intros until len. intros INV Hsv HR.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xee440%Z => first [ eapply evt_eq; [| eapply sh_exit with (len := len)]; [num_st_eq | exact INV | intros HC; specialize (HR HC); lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Ltac nb_other := intros HC; apply bignorm_b_upd_other; [lazymatch goal with NB : _ -> bignorm_b _ _ |- _ => apply NB; exact HC end | lia | rewrite ?length_le8, ?length_Z_to_le_bytes; cbn [length]; lia | lia].

  Lemma sh_Z : forall (f : nat) (i k : Z) xra xt0 xt1 xt2 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 mm lb,
    SHINV mm lb (lb + k) C -> (0 <= i < k)%Z -> (1 <= lb)%Z -> (k + lb <= 62)%Z -> (k - i <= Z.of_nat f)%Z -> (C -> lb <= len0 + 1)%Z -> (k = n / 64)%Z ->
    evt bsegs Q (SH 0xee3f4 xra xt0 xt1 xt2 (Z_to_bv 64 (X + 496)) (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 (k + 1 - i)) (Z_to_bv 64 (-8)) (Z_to_bv 64 1)
                    xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (2147450880 + X / 8 + i)) (Z_to_bv 64 (k + lb)) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 k) xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO X8 NR HCAP SHPX KRET.
    intros f. induction f as [|f IH]; intros until lb; intros INV Hi Hlb Hk Hf HL HKN; [exfalso; lia|].
    pose proof INV as INV0. sh_open INV0. sh_env.
    bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xee468%Z => u_trap pc
      | 0xee42c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 (lb + k) (lb + k) C) by (sh_close_with nb_other));
                             eapply evt_eq; [| eapply sh_028 with (sv := (k + lb)%Z) (len := (lb + k)%Z)]; [num_st_eq | exact INV1 | lia | intros HC; specialize (HL HC); lia] | fail 100 "cut" pc ]
      | 0xee3f4%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 lb (lb + k) C) by (sh_close_with nb_other));
                             eapply evt_eq; [| eapply (IH (i + 1)%Z k) with (lb := lb)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | exact HL | exact HKN] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sh_fd4 : forall (k : Z) xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm len,
    SHINV mm len (len + k) C -> (1 <= k)%Z -> (1 <= len)%Z -> (k + len <= 62)%Z -> (C -> len <= len0 + 1)%Z -> (k = n / 64)%Z ->
    evt bsegs Q (SH 0xee3d8 xra xt0 xt1 xt2 (Z_to_bv 64 (X + 496)) (Z_to_bv 64 X) (Z_to_bv 64 (X + 8 * k)) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                    (Z_to_bv 64 (X + 8 * k)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (k + len)) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 k) xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO X8 NR HCAP SHPX KRET.
    intros until len. intros INV Hk Hlen Hkl HL HKN. pose proof INV as INV0. sh_open INV0. sh_env.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xee468%Z => u_trap pc
      | 0xee3f4%Z => first [ eapply evt_eq; [| eapply (sh_Z (Z.to_nat 62) 0%Z k) with (lb := len)]; [sh_st_eq | exact INV | lia | lia | lia | lia | exact HL | exact HKN] | fail 100 "cut" pc ]
      end).
  Qed.

  Definition sh_move_k : Prop :=
    forall (k len : Z) xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm,
      SHINV mm len len C -> (1 <= k)%Z -> (1 <= len)%Z -> (k + len <= 62)%Z -> (C -> len <= len0 + 1)%Z -> (k = n / 64)%Z ->
      evt bsegs Q (SH 0x7f578 (Z_to_bv 64 0xee3d8) xt0 xt1 xt2 (Z_to_bv 64 (X + 496)) (Z_to_bv 64 X) (Z_to_bv 64 (X + 8 * k)) (Z_to_bv 64 X) (Z_to_bv 64 (8 * len))
                      xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (X + 8 * k)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (k + len)) (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 k)
                      xt3 xt4 xt5 xt6 mm).
  Hypothesis KMV : sh_move_k.

  Lemma sh_f70 : forall xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm len,
    SHINV mm len len C -> (C -> len <= len0 + 1)%Z ->
    evt bsegs Q (SH 0xee374 xra xt0 xt1 xt2 (Z_to_bv 64 (X + 496)) (Z_to_bv 64 X) xa0 (Z_to_bv 64 n) xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 2147450880) xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO X8 NR HCAP SHPX KRET KMV.
    intros until len. intros INV HL. pose proof INV as INV0. sh_open INV0. sh_env.
    assert (NQ : (0 <= n / 64 < 288230376151711744)%Z) by (Z.div_mod_to_equations; lia).
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xee468%Z => u_trap pc
      | 0xee440%Z => first [ eapply evt_eq; [| eapply sh_exit with (len := len)]; [num_st_eq | exact INV | intros HC; specialize (HL HC); specialize (HCAP' HC); Z.div_mod_to_equations; lia] | fail 100 "cut" pc ]
      | 0xee42c%Z => first [ eapply evt_eq; [| eapply sh_028 with (sv := (n / 64 + len)%Z) (len := len)]; [num_st_eq | exact INV | lia | intros HC; specialize (HL HC); specialize (HCAP' HC); lia] | fail 100 "cut" pc ]
      | 0x7f578%Z => first [ eapply evt_eq; [| eapply (KMV (n / 64)%Z len)]; [num_st_eq | exact INV | Z.div_mod_to_equations; lia | lia | lia | exact HL | reflexivity] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sh_B : forall (f : nat) (i sh : Z) xra xt1 xt2 xs2 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm len,
    SHINV mm len len C -> (0 <= i < len)%Z -> (1 <= sh <= 63)%Z -> (len - i <= Z.of_nat f)%Z -> (C -> len <= len0)%Z ->
    evt bsegs Q (SH 0xee2f0 xra (Z_to_bv 64 (len - i)) xt1 xt2 (Z_to_bv 64 (X + 496)) (Z_to_bv 64 X) (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 n)
                    (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 len) (Z_to_bv 64 sh) (Z_to_bv 64 (64 - sh)) (Z_to_bv 64 (63 - i)) (Z_to_bv 64 (X + 8 * i))
                    xs2 (Z_to_bv 64 2147450880) xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO X8 NR HCAP SHPX KRET KMV.
    intros f. induction f as [|f IH]; intros until len; intros INV Hi Hsh Hf HL; [exfalso; lia|].
    destruct (Z.eq_dec i (len - 1)) as [IT|IT].
    - pose proof INV as INV0. sh_open INV0. sh_env. assert (NQ : (0 <= n / 64)%Z) by (apply Z.div_pos; lia).
      bkstep.
      bkwalk ltac:(fun pc => lazymatch pc with
        | 0xee468%Z => u_trap pc
        | 0xee43c%Z => first [ fold_limbz; num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 len len C) by (sh_close_with ltac:(intros HC; exfalso; specialize (HL HC); specialize (HCAP' HC); lia)));
                               zstep; eapply evt_eq; [| eapply sh_exit with (r := 0%Z) (len := len)]; [num_st_eq | exact INV1 | intros HC; exfalso; specialize (HL HC); specialize (HCAP' HC); lia] | fail 100 "cut" pc ]
        | 0xee374%Z => first [ fold_limbz; lazymatch goal with
                               | XA : u8arr _ _ _ (upd_bytes (upd_bytes _ _ _) _ _) |- _ =>
                                   num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 (len + 1) (len + 1) C) by
                                     (sh_close_with ltac:(intros _; apply bignorm_b_push; [lia | lia | lia |]; rewrite unsigned_lit_wrap; change (2 ^ 64)%Z with 18446744073709551616%Z;
                                                          rewrite Z.mod_small by (apply shiftr_word_small; lia); assumption)));
                                   eapply evt_eq; [| eapply sh_f70 with (len := (len + 1)%Z)]; [num_st_eq | exact INV1 | intros HC; specialize (HL HC); lia]
                               | _ =>
                                   num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 len len C) by
                                     (sh_close_with ltac:(intros HC; apply bignorm_b_shl_nocarry; [apply NB; exact HC | lia | lia | lia | lia | assumption])));
                                   eapply evt_eq; [| eapply sh_f70 with (len := len)]; [num_st_eq | exact INV1 | intros HC; specialize (HL HC); lia]
                               end | fail 100 "cut" pc ]
        | 0xee2f0%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        end).
    - pose proof INV as INV0. sh_open INV0. sh_env.
      assert (DT1 : IsData xt1) by exact I.
      bstep.
      bwalk ltac:(fun pc => lazymatch pc with
        | 0xee468%Z => u_trap pc
        | 0xee43c%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0xee374%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0xee2f0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 len len C) by (sh_close_with nb_other));
                               eapply evt_eq; [| eapply (IH (i + 1)%Z sh) with (len := len)]; [num_st_eq | exact INV1 | lia | lia | lia | exact HL] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma sh_entry : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (bs0 : list byte),
    mem_inv bsegs m0 -> stk bsegs m0 lo SP -> b_consts m0 ->
    u8arr bsegs m0 X bs0 -> length bs0 = 496%nat -> (C -> bignorm_b bs0 len0) -> rw_cells bsegs m0 (X + 496) [C2 (Z_to_bv 64 len0)] -> (0 <= len0 <= 62)%Z ->
    evt bsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 B_SHL) fc None m0 (seg_rom bsegs)).
  Proof using ROOM X0 XLO X8 NR HCAP SHPX KRET KMV.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 bs0 MI ST (G1 & G2) XA XL NB XN LEN.
    unfold B_SHL. sh_env.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl bsegs m0) as WM.
    set (m := m0) in MI, ST, G1, G2, XA, XN, MU at 2, WM at 2 |- *. clearbody m.
    step.
    carve_frame 64%nat ST.
    apply (rw_cells_split_CB bsegs m _ [] 64 junk [] [8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 8 step. bstep. bstep. bstep. bstep. clear G1 G2.
    num_cur_mem ltac:(fun mm => assert (INV : SHINV mm len0 len0 C) by (sh_close_with ltac:(exact NB))).
    assert (SHR : (0 <= Z.land n 63 < 64)%Z).
    { change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
    bkwalk ltac:(fun pc => lazymatch pc with
      | 0xee468%Z => u_trap pc
      | 0xee374%Z => first [ eapply evt_eq; [| eapply sh_f70 with (len := len0)]; [num_st_eq | exact INV | intros; lia] | fail 100 "cut" pc ]
      | 0xee2f0%Z => first [ eapply evt_eq; [| eapply (sh_B (Z.to_nat len0) 0%Z (Z.land n 63)) with (len := len0)]; [num_st_eq | exact INV | lia | lia | lia | intros; lia] | fail 100 "cut" pc ]
      end).
  Qed.
End SHL.
