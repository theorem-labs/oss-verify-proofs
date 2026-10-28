(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumN.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_num_kitu Sj_num_kitn Sj_num_memmoveN.
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

Lemma shiftr_word_small : forall (w : word) k, (0 <= k)%Z -> (0 <= Z.shiftr (bv_unsigned w) k < 18446744073709551616)%Z.
Proof.
  intros w k Hk. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R.
  rewrite Z.shiftr_div_pow2 by lia. assert (P : (0 < 2 ^ k)%Z) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Definition SHLN_ENTRY : Z := 0x5ef9c.
Definition shlN_memmove_stmt : Prop := memmoveN_stmt_g usegs 0xd027c.

Section SHLN.
  Hypothesis HMOVE : shlN_memmove_stmt.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo : Z) (xn : word) (m0 : mem) (len0 : Z) (C : Prop).
  Notation SP := (bv_unsigned sp).
  Notation N := (bv_unsigned xn).
  Hypothesis ROOM : (lo + SHLU_STACK <= SP)%Z.
  Hypothesis XLO : (SP <= X)%Z.
  Hypothesis XHI : (X + 498 <= 2^64)%Z.
  Hypothesis X0 : (0 < X)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis HCAP : C -> (len0 + N / 64 + 1 <= 62)%Z.

  Notation W := [(SP - SHLU_STACK, SP); (X, X + 498)]%Z.
  Notation GN := (fun (a0 : word) (ws' : list word) (len' : Z) => C -> a0 = Z_to_bv 64 1 /\ bignorm ws' len' /\ (len' <= len0 + N / 64 + 1)%Z).
  Notation POST := (biguN_post_g SHLU_STACK GN usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m0).
  Notation SH pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 (SP + -48)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3
             s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition SHINV (mm : mem) (len tl : Z) (P : Prop) : Prop :=
    (exists j, rw_cells usegs mm (SP + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
    (exists bs, u8arr usegs mm X bs /\ length bs = 496%nat /\ (P -> bignorm_b bs tl)) /\
    rw_cells usegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    mem_inv usegs mm /\ munch W m0 mm /\ wmono usegs m0 mm /\ stk usegs mm lo (SP + -48).

  Ltac sh_open H :=
    let j := fresh "j" in let bs := fresh "bs" in
    destruct H as ((j & FR) & (bs & XA & ?XL & NB) & XN & ?LEN & MI & MU & WM & ST); unfold SHLU_STACK in MU.
  Ltac sh_close_with nb :=
    lazymatch goal with
    | |- SHINV _ _ _ _ =>
        split; [eexists; eassumption|]; split; [eexists; split; [eassumption| split; [lia | nb]]|]; split; [eassumption|]; split; [lia|];
        split; [eassumption|]; split; [eassumption|]; split; eassumption
    end.
  Ltac sh_env :=
    pose proof ROOM as ROOM'; unfold SHLU_STACK in ROOM';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof XHI as XHI'; change (2 ^ 64)%Z with 18446744073709551616%Z in XHI';
    pose proof XLO as XLO'; pose proof X0 as X0'; pose proof X8 as X8'; pose proof HCAP as HCAP'.
  Ltac sh_nr := pose proof (bv_unsigned_in_range 64 xn) as NR; unfold bv_modulus in NR; cbn in NR.

  Lemma sh_exit : forall (r : Z) xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    SHINV mm len len C -> (C -> r = 1 /\ len <= len0 + N / 64 + 1)%Z ->
    evt usegs POST (SH 0x5f0e4 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XLO XHI X0 X8 HCAP.
    intros until len. intros INV HR. sh_open INV. sh_env.
    do 5 zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    destruct (u64arr_of_u8arr_s usegs mm X bs XA XL) as (ws & WL & EW & WA).
    apply evt_done. unfold biguN_post_g. do 15 eexists. exists mm, ws, len.
    split; [cbv delta [mkR]; reflexivity|].
    unfold SHLU_STACK, bigint_at.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [split; [exact WA| split; [exact WL| split; [exact XN| lia]]] |]. split; [exact ST|].
    intros HC. destruct (HR HC) as [-> HL]. split; [reflexivity|]. split; [|exact HL].
    apply bignorm_of_b; [rewrite EW; apply NB; exact HC | lia].
  Qed.

  Lemma sh_074 : forall (sv : Z) xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 mm len,
    SHINV mm len len C -> (0 <= sv < 2^60)%Z -> (C -> sv <= 62 /\ len <= len0 + N / 64 + 1)%Z ->
    evt usegs POST (SH 0x5f0d0 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 sv) xs3 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XLO XHI X0 X8 HCAP.
    intros until len. intros INV Hsv HR.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5f0e4%Z => first [ eapply evt_eq; [| eapply sh_exit]; [num_st_eq | exact INV | intros HC; specialize (HR HC); lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Ltac nb_other := intros HC; apply bignorm_b_upd_other; [lazymatch goal with NB : _ -> bignorm_b _ _ |- _ => apply NB; exact HC end | lia | rewrite ?length_le8, ?length_Z_to_le_bytes; cbn [length]; lia | lia].

  Lemma sh_Z : forall (f : nat) (i k : Z) xra xt0 xt1 xt2 xs1 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm lb,
    SHINV mm lb (lb + k) C -> (0 <= i < k)%Z -> (1 <= lb)%Z -> (k + lb <= 62)%Z -> (k - i <= Z.of_nat f)%Z -> (C -> lb <= len0 + 1)%Z -> (k = N / 64)%Z ->
    evt usegs POST (SH 0x5f0b0 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 (Z_to_bv 64 (k + 1 - i)) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 1) (Z_to_bv 64 (X + 8 * i))
                       xa4 xa5 xa6 xa7 (Z_to_bv 64 (k + lb)) (Z_to_bv 64 k) xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XLO XHI X0 X8 HCAP.
    intros f. induction f as [|f IH]; intros until lb; intros INV Hi Hlb Hk Hf HL HKN; [exfalso; lia|].
    pose proof INV as INV0. sh_open INV0. sh_env.
    nstep.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5f100%Z => u_trap pc
      | 0x5f0d0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 (lb + k) (lb + k) C) by (sh_close_with nb_other));
                             eapply evt_eq; [| eapply sh_074 with (sv := (k + lb)%Z)]; [num_st_eq | exact INV1 | lia | intros HC; specialize (HL HC); lia] | fail 100 "cut" pc ]
      | 0x5f0b0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 lb (lb + k) C) by (sh_close_with nb_other));
                             eapply evt_eq; [| eapply (IH (i + 1)%Z k)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | exact HL | exact HKN] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sh_fec : forall xra xt0 xt1 xt2 xs1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    SHINV mm len len C -> (C -> len <= len0 + 1)%Z ->
    evt usegs POST (SH 0x5f048 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 xn xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using HMOVE ROOM XLO XHI X0 X8 HCAP xn.
    intros until len. intros INV HL. pose proof INV as INV0. sh_open INV0. sh_env. sh_nr.
    lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end. rewrite <- (Z_to_bv_bv_unsigned xn). subst QQ.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5f100%Z => u_trap pc
      | 0x5f0e4%Z => first [ eapply evt_eq; [| eapply sh_exit]; [num_st_eq | exact INV | intros HC; specialize (HL HC); specialize (HCAP' HC); Z.div_mod_to_equations; lia] | fail 100 "cut" pc ]
      | 0x5f0d0%Z => first [ eapply evt_eq; [| eapply sh_074 with (sv := (N / 64 + len)%Z)]; [num_st_eq | exact INV | Z.div_mod_to_equations; lia | intros HC; specialize (HL HC); specialize (HCAP' HC); lia] | fail 100 "cut" pc ]
      | 0xd027c%Z => idtac
      end).
    pose proof (u8arr_bound _ _ _ _ XA) as XB. rewrite XL in XB.
    pose proof HMOVE as HM. unfold shlN_memmove_stmt, memmoveN_stmt_g in HM.
    eapply evt_cut.
    { eapply evt_eq; [| eapply HM with (D := (X + 8 * (N / 64))%Z) (S := X) (N := (8 * len)%Z) (U := X) (bs := bs)]; [num_st_eq | ..];
        [ exact XA | lia | lia | lia | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | exact MI ]. }
    cbv beta. intros ms' P. unfold memmoveN_post_g in P.
    destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & bs3 & -> & MUc & WMc & MIc & XA3 & XL3 & TOP3).
    clear XA. lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call usegs mo mn MUc WMc end.
    clear MUc WMc MI. rename MIc into MI. num_ret_pc.
    assert (NB3 : C -> bignorm_b bs3 (len + N / 64)).
    { intros HC. right. specialize (TOP3 ltac:(lia)).
      replace (8 * (len + N / 64 - 1))%Z with (X + 8 * (N / 64) - X + 8 * len - 8)%Z by lia. rewrite TOP3.
      destruct (NB HC) as [?|NZ]; [exfalso; lia|]. replace (X - X + 8 * len - 8)%Z with (8 * (len - 1))%Z by lia. exact NZ. }
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x5f100%Z => u_trap pc
      | 0x5f0b0%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 len (len + N / 64) C) by (sh_close_with ltac:(exact NB3)));
                             eapply evt_eq; [| eapply (sh_Z (Z.to_nat 62) 0%Z (N / 64)%Z) with (lb := len)]; [num_st_eq | exact INV1 | lia | lia | lia | lia | exact HL | reflexivity] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sh_B : forall (f : nat) (i sh : Z) xra xt0 xt1 xt2 xs1 xa6 xs2 xs3 xt3 xt4 xt5 xt6 mm len,
    SHINV mm len len C -> (0 <= i < len)%Z -> (1 <= sh <= 63)%Z -> (len - i <= Z.of_nat f)%Z -> (C -> len <= len0)%Z ->
    evt usegs POST (SH 0x5eff4 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 (Z_to_bv 64 len) xn (Z_to_bv 64 sh) (Z_to_bv 64 (63 - i)) (Z_to_bv 64 (64 - sh)) (Z_to_bv 64 (X + 8 * len)) xa6
                       (Z_to_bv 64 (X + 8 * i)) xs2 xs3 xt3 xt4 xt5 xt6 mm).
  Proof using HMOVE ROOM XLO XHI X0 X8 HCAP xn.
    intros f. induction f as [|f IH]; intros until len; intros INV Hi Hsh Hf HL; [exfalso; lia|].
    destruct (Z.eq_dec i (len - 1)) as [IT|IT].
    - pose proof INV as INV0. sh_open INV0. sh_env. sh_nr. assert (NQ : (0 <= N / 64)%Z) by (apply Z.div_pos; lia).
      ukstep.
      ukwalk ltac:(fun pc => lazymatch pc with
        | 0x5f100%Z => u_trap pc
        | 0x5f0e0%Z => first [ fold_limbz; num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 len len C) by (sh_close_with ltac:(intros HC; exfalso; specialize (HL HC); specialize (HCAP' HC); lia)));
                               zstep; eapply evt_eq; [| eapply sh_exit with (r := 0%Z)]; [num_st_eq | exact INV1 | intros HC; exfalso; specialize (HL HC); specialize (HCAP' HC); lia] | fail 100 "cut" pc ]
        | 0x5f048%Z => first [ fold_limbz; lazymatch goal with
                               | XA : u8arr _ _ _ (upd_bytes (upd_bytes _ _ _) _ _) |- _ =>
                                   num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 (len + 1) (len + 1) C) by
                                     (sh_close_with ltac:(intros _; apply bignorm_b_push; [lia | lia | lia |]; rewrite unsigned_lit_wrap; change (2 ^ 64)%Z with 18446744073709551616%Z;
                                                          rewrite Z.mod_small by (apply shiftr_word_small; lia); assumption)));
                                   eapply evt_eq; [| eapply sh_fec]; [num_st_eq | exact INV1 | intros HC; specialize (HL HC); lia]
                               | _ =>
                                   num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 len len C) by
                                     (sh_close_with ltac:(intros HC; apply bignorm_b_shl_nocarry; [apply NB; exact HC | lia | lia | lia | lia | assumption])));
                                   eapply evt_eq; [| eapply sh_fec]; [num_st_eq | exact INV1 | intros HC; specialize (HL HC); lia]
                               end | fail 100 "cut" pc ]
        | 0x5eff4%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        end).
    - pose proof INV as INV0. sh_open INV0. sh_env.
      assert (DA6 : IsData xa6) by exact I.
      nstep.
      uwalk ltac:(fun pc => lazymatch pc with
        | 0x5f100%Z => u_trap pc
        | 0x5f0e0%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0x5f048%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0x5eff4%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SHINV m1 len len C) by (sh_close_with nb_other));
                               eapply evt_eq; [| eapply (IH (i + 1)%Z sh)]; [num_st_eq | exact INV1 | lia | lia | lia | exact HL] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma sh_body : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ws,
    mem_inv usegs m0 -> stk usegs m0 lo SP -> bigint_at usegs m0 X ws len0 -> (C -> bignorm ws len0) ->
    evt usegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) xn a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SHLN_ENTRY) fc None m0 (seg_rom usegs)).
  Proof using HMOVE ROOM XLO XHI X0 X8 HCAP xn.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ws MI ST (WA & WL & XN & LEN) NORM.
    unfold SHLN_ENTRY. sh_env. sh_nr.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl usegs m0) as WM. unfold SHLU_STACK in MU.
    set (m := m0) in MI, ST, WA, XN, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 48%nat ST.
    apply (rw_cells_split_CB usegs m _ [] 48 junk [] [8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 5 step.
    pose proof (u8arr_of_u64arr_s usegs _ X ws WA) as XA. assert (XL : length (u64s ws) = 496%nat) by (rewrite u64s_length, WL; reflexivity).
    assert (NB : C -> bignorm_b (u64s ws) len0) by (intros HC; apply bignorm_b_of; [apply NORM; exact HC | lia]).
    clear WA.
    num_cur_mem ltac:(fun mm => assert (INV : SHINV mm len0 len0 C) by (sh_close_with ltac:(exact NB))).
    assert (SHR : (0 <= Z.land N 63 < 64)%Z).
    { change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
    ukwalk ltac:(fun pc => lazymatch pc with
      | 0x5f100%Z => u_trap pc
      | 0x5f048%Z => first [ eapply evt_eq; [| eapply sh_fec]; [num_st_eq | exact INV | intros; lia] | fail 100 "cut" pc ]
      | 0x5eff4%Z => first [ eapply evt_eq; [| eapply (sh_B (Z.to_nat len0) 0%Z (Z.land N 63)) with (len := len0)]; [num_st_eq | exact INV | lia | lia | lia | intros; lia] | fail 100 "cut" pc ]
      end).
  Qed.
End SHLN.

Theorem shluN_spec : shlN_memmove_stmt -> shluN_stmt_g usegs SHLN_ENTRY.
Proof.
  intros HM. unfold shluN_stmt_g. intros until len. intros MI ST ROOM BIG XLO XHI X0 X8.
  eapply evt_mono.
  { eapply (sh_body HM ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo a1 m len (bignorm ws len /\ len + bv_unsigned a1 / 64 + 1 <= 62)%Z);
      try eassumption; [intros [_ H]; exact H | intros [H _]; exact H]. }
  cbv beta. intros ms' P. unfold biguN_post_g in *.
  destruct P as (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & q14 & m' & ws' & len' & E & H1 & H2 & H3 & H4 & H5 & G).
  exists q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, m', ws', len'.
  repeat (split; [assumption|]). unfold shluN_G. intros HN HCAP. apply G. split; assumption.
Qed.
