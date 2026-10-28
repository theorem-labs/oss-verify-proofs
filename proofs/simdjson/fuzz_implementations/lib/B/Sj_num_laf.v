(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
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

Definition lafb_post (G : word -> Z -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' bs' len',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - LAFB_STACK, bv_unsigned sp); (X, X + 498)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ u8arr bsegs m' X bs' /\ length bs' = 496%nat /\ rw_cells bsegs m' (X + 496) [C2 (Z_to_bv 64 len')] /\ (0 <= len' <= 62)%Z
    /\ G a0 len'.

Section LAF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X Y ny st lo len0 : Z) (ybs : list byte) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation W := [(SP - LAFB_STACK, SP); (X, X + 498)]%Z.
  Hypothesis ROOM : (lo + LAFB_STACK <= SP)%Z.
  Hypothesis X0 : (0x6e0000 <= X)%Z.
  Hypothesis XLO : (X + 504 <= lo)%Z.
  Hypothesis YL : Z.of_nat (length ybs) = (8 * ny)%Z.
  Hypothesis Y0 : (0x6e0000 <= Y)%Z.
  Hypothesis YLO : (Y + 8 * ny <= lo)%Z.
  Hypothesis YX : (Y + 8 * ny <= X \/ X + 504 <= Y)%Z.
  Hypothesis Y8 : (Y mod 8 = 0)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis NY : (0 <= ny <= 62)%Z.
  Hypothesis ST0 : (0 <= st <= 62)%Z.
  Hypothesis SHPX : forall m', munch W m0 m' -> wmono bsegs m0 m' -> shz m' X 504.
  Hypothesis SHPY : forall m', munch W m0 m' -> wmono bsegs m0 m' -> shz m' Y (8 * ny).

  Notation GL := (fun (a0 : word) (len' : Z) => (len0 <= 61 -> ny + st <= 61 -> a0 = Z_to_bv 64 1 /\ len' <= Z.max len0 (ny + st) + 1 /\ Z.max len0 (ny + st) <= len')%Z).
  Notation POST := (lafb_post GL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m0).
  Notation LA pc xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR ra (Z_to_bv 64 (SP + -80)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7
             s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Definition LAINV (mm : mem) (len : Z) : Prop :=
    (exists j0, rw_cells bsegs mm (SP + -80) [CB 8 j0; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
    (exists bs, u8arr bsegs mm X bs /\ length bs = 496%nat) /\
    rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    bytes_at bsegs mm Y ybs /\
    mem_inv bsegs mm /\ munch W m0 mm /\ wmono bsegs m0 mm /\ stk bsegs mm lo (SP + -80).

  Ltac la_open H :=
    let bs := fresh "bs" in let j0 := fresh "j0" in
    destruct H as ((j0 & FR) & (bs & XA & ?XL) & XN & ?LEN & YA & MI & MU & WM & ST); unfold LAFB_STACK in MU.
  Ltac la_close :=
    lazymatch goal with
    | |- LAINV _ _ =>
        split; [eexists; eassumption|]; split; [eexists; split; [eassumption| lia]|]; split; [eassumption|]; split; [lia|];
        split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
    end.
  Ltac la_env :=
    pose proof ROOM as ROOM'; unfold LAFB_STACK in ROOM';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof X0 as X0'; pose proof XLO as XLO'; pose proof YL as YL'; pose proof Y0 as Y0'; pose proof YLO as YLO'; pose proof YX as YX';
    pose proof NY as NY'; pose proof ST0 as ST0'; pose proof X8 as X8'; pose proof Y8 as Y8'.

  Ltac la_trap pc := first [ exfalso; lia | exfalso; Z.div_mod_to_equations; lia | u_trap_b pc ].

  Ltac la_st_eq_leaf :=
    lazymatch goal with
    | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia | f_equal; Z.div_mod_to_equations; lia | word_eq_tac]
    | |- _ => reflexivity
    end.
  Ltac la_st_eq_tree :=
    lazymatch goal with
    | |- TNode _ _ _ = TNode _ _ _ => f_equal; la_st_eq_tree
    | |- Some _ = Some _ => f_equal; la_st_eq_leaf
    | |- _ => reflexivity
    end.
  Ltac la_st_eq := cbv delta [mkR]; lazymatch goal with |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; la_st_eq_tree end.

  Notation LAC pc xt2 xs0 xs1 xa1 xa2 xa3 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm :=
    (LA pc (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 2147450880) xt2 xs0 xs1 (Z_to_bv 64 (X + 496)) xa1 xa2 xa3 (Z_to_bv 64 X)
        xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm).

  Lemma la_exit : forall (r : Z) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm len,
    LAINV mm len -> (len0 <= 61 -> ny + st <= 61 -> r = 1 /\ len <= Z.max len0 (ny + st) + 1 /\ Z.max len0 (ny + st) <= len)%Z ->
    evt bsegs POST (LA 0xfcf34 xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 (Z_to_bv 64 r) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO YL Y0 YLO YX Y8 X8 NY ST0 SHPX SHPY.
    intros until len. intros INV HR. la_open INV. la_env.
    zstep. do 9 zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold lafb_post. do 15 eexists. exists mm, bs, len.
    split; [cbv delta [mkR]; reflexivity|].
    unfold LAFB_STACK.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact XA|]. split; [exact XL|]. split; [exact XN|]. split; [lia|].
    intros H1 H2. destruct (HR H1 H2) as (-> & H3 & H4). split; [reflexivity|]. split; assumption.
  Qed.

  Lemma la_false : forall xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm len,
    LAINV mm len -> (len0 <= 61 -> ny + st <= 61 -> False)%Z ->
    evt bsegs POST (LA 0xfcf30 xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO YL Y0 YLO YX Y8 X8 NY ST0 SHPX SHPY.
    intros until len. intros INV HF. zstep. eapply evt_eq; [| eapply la_exit with (r := 0%Z)]; [num_st_eq | exact INV | intros H1 H2; exfalso; exact (HF H1 H2)].
  Qed.

  Lemma la_push : forall xs0 xs1 xa1 xa2 xa3 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm len,
    LAINV mm len -> (len = Z.max len0 (ny + st))%Z ->
    evt bsegs POST (LAC 0xfcef0 (Z_to_bv 64 (18446744073709551615 - X)) xs0 xs1 xa1 xa2 xa3 (Z_to_bv 64 1) (Z_to_bv 64 len) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO YL Y0 YLO YX Y8 X8 NY ST0 SHPX SHPY.
    intros until len. intros INV HLEN. pose proof INV as INV0. la_open INV0. la_env.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfcf64%Z => la_trap pc
      | 0xfcf30%Z => first [ eapply la_false; [exact INV | intros; lia] | fail 100 "cut" pc ]
      | 0xfcf34%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LAINV m1 (len + 1)) by la_close); eapply evt_eq; [| eapply la_exit with (r := 1%Z)]; [num_st_eq | exact INV1 | intros; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma la_C : forall (f : nat) (k : Z) xs0 xs1 xa1 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm len,
    LAINV mm len -> (len = Z.max len0 (ny + st))%Z -> (0 <= k <= len)%Z -> (len - k <= Z.of_nat f)%Z ->
    evt bsegs POST (LAC 0xfcea4 (Z_to_bv 64 (18446744073709551615 - X)) xs0 xs1 xa1 (Z_to_bv 64 (8 * k)) (Z_to_bv 64 (18446744073709551552 + k))
                        (Z_to_bv 64 1) (Z_to_bv 64 len) (Z_to_bv 64 (len - k)) xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO YL Y0 YLO YX Y8 X8 NY ST0 SHPX SHPY.
    intros f. induction f as [|f IH]; intros until len; intros INV HLEN Hk Hf.
    - pose proof INV as INV0. la_open INV0. la_env. bstep.
      bwalk ltac:(fun pc => lazymatch pc with
        | 0xfcf64%Z => la_trap pc
        | 0xfcef0%Z => first [ eapply evt_eq; [| eapply la_push with (len := len)]; [num_st_eq | exact INV | exact HLEN] | fail 100 "cut" pc ]
        end).
    - pose proof INV as INV0. la_open INV0. la_env. bstep.
      bwalk ltac:(fun pc => lazymatch pc with
        | 0xfcf64%Z => la_trap pc
        | 0xfcef0%Z => first [ eapply evt_eq; [| eapply la_push with (len := len)]; [num_st_eq | exact INV | exact HLEN] | fail 100 "cut" pc ]
        | 0xfcf34%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LAINV m1 len) by la_close); eapply evt_eq; [| eapply la_exit with (r := 1%Z)]; [num_st_eq | exact INV1 | intros; lia] | fail 100 "cut" pc ]
        | 0xfcea4%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LAINV m1 len) by la_close);
                               eapply evt_eq; [| eapply (IH (k + 1)%Z) with (len := len)]; [num_st_eq | exact INV1 | exact HLEN | lia | lia] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma la_cfc : forall xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm len,
    LAINV mm len -> (len = Z.max len0 (ny + st))%Z -> (st + ny <= len)%Z -> IsData xt4 ->
    evt bsegs POST (LAC 0xfce64 (Z_to_bv 64 (18446744073709551615 - X)) xs0 xs1 (Z_to_bv 64 Y) (Z_to_bv 64 ny) (Z_to_bv 64 st) (Z_to_bv 64 1) xa6 xa7
                        xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO YL Y0 YLO YX Y8 X8 NY ST0 SHPX SHPY.
    intros until len. intros INV HLEN HL DT4. pose proof INV as INV0. la_open INV0. la_env.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfcf64%Z => la_trap pc
      | 0xfcf34%Z => first [ eapply evt_eq; [| eapply la_exit with (r := 1%Z)]; [num_st_eq | exact INV | intros; lia] | fail 100 "cut" pc ]
      | 0xfcea4%Z => first [ eapply evt_eq; [| eapply (la_C (Z.to_nat len) (st + ny)%Z) with (len := len)]; [num_st_eq | exact INV | exact HLEN | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma la_A : forall (f : nat) (j : Z) xa6 xa7 xs3 xs4 xs5 xs6 xs7 xt4 mm len,
    LAINV mm len -> (len = Z.max len0 (ny + st))%Z -> (st + ny <= len)%Z -> (0 <= j < ny)%Z -> (ny - j <= Z.of_nat f)%Z -> IsData xt4 ->
    evt bsegs POST (LAC 0xfcdc8 (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 (X + 8 * st)) (Z_to_bv 64 1) (Z_to_bv 64 Y) (Z_to_bv 64 ny) (Z_to_bv 64 st)
                        (Z_to_bv 64 1) xa6 xa7 (Z_to_bv 64 (ny - j)) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (8 * j)) xt4 (Z_to_bv 64 (8 * st)) (Z_to_bv 64 (8 * st + -504)) mm).
  Proof using ROOM X0 XLO YL Y0 YLO YX Y8 X8 NY ST0 SHPX SHPY.
    intros f. induction f as [|f IH]; intros until len; intros INV HLEN HL Hj Hf DT4; [exfalso; lia|].
    pose proof INV as INV0. la_open INV0. la_env.
    bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfcf64%Z => la_trap pc
      | 0xfce64%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LAINV m1 len) by la_close);
                             eapply evt_eq; [| eapply la_cfc with (len := len)]; [num_st_eq | exact INV1 | exact HLEN | lia | assumption] | fail 100 "cut" pc ]
      | 0xfcdc8%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LAINV m1 len) by la_close);
                             eapply evt_eq; [| eapply (IH (j + 1)%Z) with (len := len)]; [num_st_eq | exact INV1 | exact HLEN | lia | lia | lia | assumption] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma la_c2c : forall xt2 xs0 xs1 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm len,
    LAINV mm len -> (len = Z.max len0 (ny + st))%Z -> (st + ny <= len)%Z -> (0 < ny)%Z ->
    evt bsegs POST (LAC 0xfcd94 xt2 xs0 xs1 (Z_to_bv 64 Y) (Z_to_bv 64 ny) (Z_to_bv 64 st) (Z_to_bv 64 1) xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO YL Y0 YLO YX Y8 X8 NY ST0 SHPX SHPY.
    intros until len. intros INV HLEN HL Hn. pose proof INV as INV0. la_open INV0. la_env.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfcf64%Z => la_trap pc
      | 0xfcdc8%Z => first [ replace (0 <? Y)%Z with true by (symmetry; apply Z.ltb_lt; lia); cbn [Z.b2z];
                             eapply evt_eq; [| eapply (la_A (Z.to_nat ny) 0%Z) with (len := len)]; [num_st_eq | exact INV | exact HLEN | lia | lia | lia | exact I] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma la_Z : forall (f : nat) (i : Z) xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xt6 mm len,
    LAINV mm len -> (len0 <= ny + st)%Z -> (0 <= i < ny + st)%Z -> (ny + st <= 62)%Z -> (ny + st - i <= Z.of_nat f)%Z ->
    evt bsegs POST (LAC 0xfcd5c (Z_to_bv 64 (ny + st - i + 1)) xs0 xs1 (Z_to_bv 64 Y) (Z_to_bv 64 ny) (Z_to_bv 64 st) (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 (ny + st))
                        (Z_to_bv 64 (X + 8 * i)) xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 (-8)) (Z_to_bv 64 (2147450880 + X / 8 + i)) (Z_to_bv 64 1) xt6 mm).
  Proof using ROOM X0 XLO YL Y0 YLO YX Y8 X8 NY ST0 SHPX SHPY.
    intros f. induction f as [|f IH]; intros until len; intros INV HL0 Hi Hn Hf; [exfalso; lia|].
    pose proof INV as INV0. la_open INV0. la_env.
    bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfcf64%Z => la_trap pc
      | 0xfcf34%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LAINV m1 (ny + st)) by la_close); eapply evt_eq; [| eapply la_exit with (r := 1%Z) (len := (ny + st)%Z)]; [num_st_eq | exact INV1 | intros; lia] | fail 100 "cut" pc ]
      | 0xfcd94%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LAINV m1 (ny + st)) by la_close);
                             eapply evt_eq; [| eapply la_c2c with (len := (ny + st)%Z)]; [num_st_eq | exact INV1 | lia | lia | lia] | fail 100 "cut" pc ]
      | 0xfcd5c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : LAINV m1 len) by la_close);
                             eapply evt_eq; [| eapply (IH (i + 1)%Z) with (len := len)]; [la_st_eq | exact INV1 | exact HL0 | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma la_body : forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (bs0 : list byte),
    mem_inv bsegs m0 -> stk bsegs m0 lo SP -> b_consts m0 ->
    u8arr bsegs m0 X bs0 -> length bs0 = 496%nat -> rw_cells bsegs m0 (X + 496) [C2 (Z_to_bv 64 len0)] -> (0 <= len0 <= 62)%Z ->
    bytes_at bsegs m0 Y ybs ->
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 ny) (Z_to_bv 64 st) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 B_LAF) fc None m0 (seg_rom bsegs)).
  Proof using ROOM X0 XLO YL Y0 YLO YX Y8 X8 NY ST0 SHPX SHPY.
    intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 bs0 MI ST (G1 & G2) XA XL XN0 LEN0 YA.
    pose (len := len0). assert (ELEN : len = len0) by reflexivity. change len0 with len in XN0, LEN0. clearbody len.
    unfold B_LAF. la_env.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl bsegs m0) as WM. unfold LAFB_STACK in MU.
    set (m := m0) in MI, ST, G1, G2, XA, XN0, YA, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 80%nat ST.
    apply (rw_cells_split_CB bsegs m _ [] 80 junk [] [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 9 step. bstep. bstep. bstep. clear G1 G2.
    rename XN0 into XN.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => assert (INV : LAINV m1 len) by la_close end.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xfcf64%Z => la_trap pc
      | 0xfcf30%Z => first [ eapply la_false; [exact INV | intros; lia] | fail 100 "cut" pc ]
      | 0xfcf34%Z => first [ eapply evt_eq; [| eapply la_exit with (r := 1%Z) (len := len)]; [num_st_eq | exact INV | intros; lia] | fail 100 "cut" pc ]
      | 0xfcd94%Z => first [ eapply evt_eq; [| eapply la_c2c with (len := len)]; [num_st_eq | exact INV | lia | lia | lia] | fail 100 "cut" pc ]
      | 0xfcd5c%Z => first [ eapply evt_eq; [| eapply (la_Z (Z.to_nat 62) len) with (len := len)]; [la_st_eq | exact INV | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End LAF.

Definition lafb_G (len ny st : Z) : word -> Z -> Prop :=
  fun a0 len' => (len <= 61 -> ny + st <= 61 -> a0 = Z_to_bv 64 1 /\ len' <= Z.max len (ny + st) + 1 /\ Z.max len (ny + st) <= len')%Z.
Definition lafb_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X Y ny st lo len : Z) (ybs bs : list byte),
  (lo + LAFB_STACK <= bv_unsigned sp)%Z -> (0x6e0000 <= X)%Z -> (X + 504 <= lo)%Z ->
  Z.of_nat (length ybs) = (8 * ny)%Z -> (0x6e0000 <= Y)%Z -> (Y + 8 * ny <= lo)%Z -> (Y + 8 * ny <= X \/ X + 504 <= Y)%Z ->
  (Y mod 8 = 0)%Z -> (X mod 8 = 0)%Z -> (0 <= ny <= 62)%Z -> (0 <= st <= 62)%Z ->
  (forall m', munch [(bv_unsigned sp - LAFB_STACK, bv_unsigned sp); (X, X + 498)]%Z m m' -> wmono bsegs m m' -> shz m' X 504) ->
  (forall m', munch [(bv_unsigned sp - LAFB_STACK, bv_unsigned sp); (X, X + 498)]%Z m m' -> wmono bsegs m m' -> shz m' Y (8 * ny)) ->
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> b_consts m ->
  u8arr bsegs m X bs -> length bs = 496%nat -> rw_cells bsegs m (X + 496) [C2 (Z_to_bv 64 len)] -> (0 <= len <= 62)%Z ->
  bytes_at bsegs m Y ybs ->
  evt bsegs (lafb_post (lafb_G len ny st) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 ny) (Z_to_bv 64 st) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 B_LAF) fc None m (seg_rom bsegs)).

Theorem lafb_spec : lafb_stmt.
Proof.
  unfold lafb_stmt, lafb_G. intros until bs. intros ROOM X0 XLO YL Y0 YLO YX Y8 X8 NY ST0 SHPX SHPY MI ST GC XA XL XN LEN YA.
  eapply la_body; eassumption.
Qed.
