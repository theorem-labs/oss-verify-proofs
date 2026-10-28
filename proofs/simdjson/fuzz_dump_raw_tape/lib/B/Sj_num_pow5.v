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
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.U Require Import Sj_num_kitn2.
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

Definition P5B_SMALL : Z := 0x2b5c8.
Definition p5b_small_tbl : list byte :=
  Eval vm_compute in match image_bytes bsegs P5B_SMALL 216 with Some bs => bs | None => [] end.
Lemma p5b_small_len : length p5b_small_tbl = 216%nat.
Proof. reflexivity. Qed.
Lemma p5b_small_at : forall m, mem_inv bsegs m -> bytes_at bsegs m P5B_SMALL p5b_small_tbl.
Proof.
  intros m MI.
  assert (RO : ro_cells bsegs m P5B_SMALL [CB (length p5b_small_tbl) p5b_small_tbl]).
  { apply (ro_cells_image bsegs m P5B_SMALL p5b_small_tbl MI); [vm_compute; reflexivity | unfold P5B_SMALL; lia | unfold P5B_SMALL; cbn; lia]. }
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma p5b_small_nz : forall e, (0 <= e <= 26)%Z -> (0 < bv_unsigned (limbz p5b_small_tbl (8 * e)))%Z.
Proof.
  intros e H.
  assert (C : (e = 0 \/ e = 1 \/ e = 2 \/ e = 3 \/ e = 4 \/ e = 5 \/ e = 6 \/ e = 7 \/ e = 8 \/ e = 9 \/ e = 10 \/ e = 11 \/ e = 12 \/ e = 13 \/
               e = 14 \/ e = 15 \/ e = 16 \/ e = 17 \/ e = 18 \/ e = 19 \/ e = 20 \/ e = 21 \/ e = 22 \/ e = 23 \/ e = 24 \/ e = 25 \/ e = 26)%Z) by lia.
  repeat (destruct C as [->|C]; [vm_compute; reflexivity|]). subst e. vm_compute. reflexivity.
Qed.

Section P5.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo len0 e0 : Z) (m0 : mem) (C : Prop).
  Notation SP := (bv_unsigned sp).
  Notation W := [(SP - 48, SP); (X, X + 504)]%Z.
  Hypothesis ROOM : (lo + 48 <= SP)%Z.
  Hypothesis X0 : (0x6ce000 <= X)%Z.
  Hypothesis XLO : (X + 504 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis HCL : C -> (len0 + 15 <= 62 /\ 0 <= e0 <= 328)%Z.
  Hypothesis SHPX : forall m', munch W m0 m' -> wmono bsegs m0 m' -> shz m' X 504.
  Hypothesis SHPL : forall m', munch W m0 m' -> wmono bsegs m0 m' -> shz m' 0x2b5a0 640.
  Variable Q : machine_state -> Prop.

  Notation P5 pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 (SP + -48)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4
             s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Notation POT len e := (C -> 0 <= e <= e0 /\ 135 * len + 6 * e <= 135 * len0 + 6 * e0)%Z.

  Definition P5INV (mm : mem) (len : Z) : Prop :=
    rw_cells bsegs mm (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    (exists bs, u8arr bsegs mm X bs /\ length bs = 496%nat /\ (C -> bignorm_b bs len)) /\
    rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
    mem_inv bsegs mm /\ munch W m0 mm /\ wmono bsegs m0 mm /\ stk bsegs mm lo (SP + -48).

  Ltac p5_open H :=
    let bs := fresh "bs" in
    destruct H as (FR & (bs & XA & ?XL & NB) & XN & ?LEN & MI & MU & WM & ST).
  Ltac p5_close_with nb :=
    lazymatch goal with
    | |- P5INV _ _ =>
        split; [eassumption|]; split; [eexists; split; [eassumption| split; [lia | nb]]|]; split; [eassumption|]; split; [lia|];
        split; [eassumption|]; split; [eassumption|]; split; eassumption
    end.
  Ltac p5_env :=
    pose proof ROOM as ROOM'; pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof X0 as X0'; pose proof XLO as XLO'; pose proof X8 as X8'; pose proof HCL as HCL'.

  Ltac cl := let HC := fresh "HC" in intros HC; repeat match goal with H : C -> _ |- _ => specialize (H HC) end; lia.
  Ltac nb_other := let HC := fresh "HC" in intros HC; apply bignorm_b_upd_other; [lazymatch goal with NB : C -> bignorm_b _ _ |- _ => apply NB; exact HC end | lia | rewrite ?length_le8; lia | lia].

  Definition p5_ret_k : Prop :=
    forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm bs len (r : Z),
      u8arr bsegs mm X bs -> length bs = 496%nat -> rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 len)] -> (0 <= len <= 62)%Z ->
      mem_inv bsegs mm -> munch W m0 mm -> wmono bsegs m0 mm -> stk bsegs mm lo SP ->
      (C -> r = 1 /\ bignorm_b bs len /\ len <= len0 + 15)%Z ->
      Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None mm (seg_rom bsegs)).
  Hypothesis KRET : p5_ret_k.

  Lemma p5_exit : forall (r : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 mm len,
    P5INV mm len -> (C -> r = 1 /\ len <= len0 + 15)%Z ->
    evt bsegs Q (P5 0xecfdc xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 r) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO X8 HCL SHPX SHPL KRET.
    intros until len. intros INV HR. p5_open INV. p5_env.
    zstep. do 6 zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. eapply KRET; try eassumption.
    intros HC. destruct (HR HC) as [-> HL]. split; [reflexivity|]. split; [exact (NB HC)| exact HL].
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

  Lemma p5_M2 : forall (f : nat) (i : Z) xra xt2 xs1 xa5 (ys : word) xs2 xs4 xt3 xt4 xt5 xt6 mm len,
    P5INV mm len -> (0 <= i < len)%Z -> (len - i <= Z.of_nat f)%Z -> (0 < bv_unsigned ys)%Z -> (C -> len <= len0 + 14)%Z ->
    evt bsegs Q (P5 0xecf50 xra (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 (len - i)) xt2 (Z_to_bv 64 X) xs1 (Z_to_bv 64 (X + 496)) (Z_to_bv 64 1) (Z_to_bv 64 (X + 8 * i))
                    (Z_to_bv 64 ((X + 496) / 8 + 2147450880)) (Z_to_bv 64 len) xa5 ys (Z_to_bv 64 (63 - i)) xs2 (Z_to_bv 64 2147450880) xs4 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO X8 HCL SHPX SHPL KRET.
    intros f. induction f as [|f IH]; intros until len; intros INV Hi Hf HY HB; [exfalso; lia|].
    destruct (Z.eq_dec i (len - 1)) as [IT|IT].
    - pose proof INV as INV0. p5_open INV0. p5_env. bkstep.
      bkwalk ltac:(fun pc => lazymatch pc with
        | 0xed000%Z => u_trap pc
        | 0xecf50%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0xecfd8%Z => first [ fold_limbz; num_cur_mem ltac:(fun m1 => assert (INV1 : P5INV m1 len) by (p5_close_with ltac:(cl)));
                               zstep; eapply evt_eq; [| eapply p5_exit with (r := 0%Z) (len := len)]; [num_st_eq | exact INV1 | cl] | fail 100 "cut" pc ]
        | 0xecfdc%Z => first [ sm_last len ltac:(fun l => eapply evt_eq; [| eapply p5_exit with (r := 1%Z) (len := l)]; [num_st_eq | exact INV1 | cl]) | fail 100 "cut" pc ]
        end).
    - pose proof INV as INV0. p5_open INV0. p5_env.
      assert (DA5 : IsData xa5) by exact I.
      bstep.
      bwalk ltac:(fun pc => lazymatch pc with
        | 0xed000%Z => u_trap pc
        | 0xecfd8%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0xecfdc%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0xecf50%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : P5INV m1 len) by (p5_close_with nb_other));
                               eapply evt_eq; [| eapply (IH (i + 1)%Z) with (len := len)]; [num_st_eq | exact INV1 | lia | lia | exact HY | exact HB] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma p5_aec : forall (e : Z) xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xt3 xt4 xt5 xt6 mm len,
    P5INV mm len -> (0 <= e < 27)%Z -> (C -> len <= len0 + 14)%Z ->
    evt bsegs Q (P5 0xecef0 xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) (Z_to_bv 64 (X + 496)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 2147450880) xs4 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO X8 HCL SHPX SHPL KRET.
    intros until len. intros INV He HB. pose proof INV as INV0. p5_open INV0. p5_env.
    pose proof (p5b_small_at _ MI) as TBL. unfold P5B_SMALL in TBL. pose proof p5b_small_len as TBLL.
    bkwalk ltac:(fun pc => lazymatch pc with
      | 0xed000%Z => u_trap pc
      | 0xecfdc%Z => first [ eapply evt_eq; [| eapply p5_exit with (r := 1%Z) (len := len)]; [num_st_eq | exact INV | cl] | fail 100 "cut" pc ]
      | 0xecf50%Z => first [ fold_limbz; eapply evt_eq; [| eapply (p5_M2 (Z.to_nat len) 0%Z) with (len := len)];
                             [num_st_eq | exact INV | lia | lia | replace (177608 + 8 * e - 177608)%Z with (8 * e)%Z by lia; apply p5b_small_nz; lia | exact HB] | fail 100 "cut" pc ]
      end).
  Qed.

  Notation P27 pc e l xra xt1 xt2 xa1 xs2 xs4 xt3 xt4 xt5 xt6 mm :=
    (P5 pc xra (Z_to_bv 64 1) xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) (Z_to_bv 64 (X + 496)) xa1 (Z_to_bv 64 ((X + 496) / 8 + 2147450880))
        (Z_to_bv 64 (18446744073709551615 - X)) (Z_to_bv 64 7450580596923828125) (Z_to_bv 64 l) (Z_to_bv 64 26) (Z_to_bv 64 61)
        xs2 (Z_to_bv 64 2147450880) xs4 xt3 xt4 xt5 xt6 mm).

  Section L2BODY.
    Variable e : Z.
    Hypothesis He : (27 <= e < 2147483648)%Z.

    Hypothesis KA50 : forall xra xt1 xt2 xa1 xs2 xs4 xt3 xt4 xt5 xt6 mm len,
      P5INV mm len -> (C -> e <= e0 /\ 135 * len + 6 * e <= 135 * len0 + 6 * e0 + 135)%Z -> evt bsegs Q (P27 0xece54 e len xra xt1 xt2 xa1 xs2 xs4 xt3 xt4 xt5 xt6 mm).

    Lemma p5_M1 : forall (f : nat) (i : Z) xra xt1 xs2 xs4 xt5 xt6 mm len,
      P5INV mm len -> (0 <= i < len)%Z -> (len - i <= Z.of_nat f)%Z -> POT len e ->
      evt bsegs Q (P27 0xece74 e len xra xt1 (Z_to_bv 64 (63 - i)) (Z_to_bv 64 (X + 8 * i)) xs2 xs4 (Z_to_bv 64 (X + 8 * i)) (Z_to_bv 64 (len - i)) xt5 xt6 mm).
    Proof using ROOM X0 XLO X8 HCL SHPX SHPL KRET He KA50.
      intros f. induction f as [|f IH]; intros until len; intros INV Hi Hf HP; [exfalso; lia|].
      destruct (Z.eq_dec i (len - 1)) as [IT|IT].
      - pose proof INV as INV0. p5_open INV0. p5_env. pose proof He as He'. bkstep.
        bkwalk ltac:(fun pc => lazymatch pc with
          | 0xed000%Z => u_trap pc
          | 0xece74%Z => first [ exfalso; lia | fail 100 "cut" pc ]
          | 0xecfd8%Z => first [ fold_limbz; num_cur_mem ltac:(fun m1 => assert (INV1 : P5INV m1 len) by (p5_close_with ltac:(cl)));
                                 zstep; eapply evt_eq; [| eapply p5_exit with (r := 0%Z) (len := len)]; [num_st_eq | exact INV1 | cl] | fail 100 "cut" pc ]
          | 0xece54%Z => first [ sm_last len ltac:(fun l => eapply evt_eq; [| eapply KA50 with (len := l)]; [num_st_eq | exact INV1 | cl]) | fail 100 "cut" pc ]
          end).
      - pose proof INV as INV0. p5_open INV0. p5_env.
        assert (DT1 : IsData xt1) by exact I.
        bstep.
        bwalk ltac:(fun pc => lazymatch pc with
          | 0xed000%Z => u_trap pc
          | 0xecfd8%Z => first [ exfalso; lia | fail 100 "cut" pc ]
          | 0xece54%Z => first [ exfalso; lia | fail 100 "cut" pc ]
          | 0xece74%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : P5INV m1 len) by (p5_close_with nb_other));
                                 eapply evt_eq; [| eapply (IH (i + 1)%Z) with (len := len)]; [num_st_eq | exact INV1 | lia | lia | exact HP] | fail 100 "cut" pc ]
          end).
    Qed.

    Lemma p5_a58 : forall xra xt1 xt2 xa1 xs2 xs4 xt3 xt4 xt5 xt6 mm len,
      P5INV mm len -> POT len e -> evt bsegs Q (P27 0xece5c e len xra xt1 xt2 xa1 xs2 xs4 xt3 xt4 xt5 xt6 mm).
    Proof using ROOM X0 XLO X8 HCL SHPX SHPL KRET He KA50.
      intros until len. intros INV HP. pose proof INV as INV0. p5_open INV0. p5_env.
      bwalk ltac:(fun pc => lazymatch pc with
        | 0xed000%Z => u_trap pc
        | 0xece54%Z => first [ eapply evt_eq; [| eapply KA50 with (len := len)]; [num_st_eq | exact INV | cl] | fail 100 "cut" pc ]
        | 0xece74%Z => first [ eapply evt_eq; [| eapply (p5_M1 (Z.to_nat len) 0%Z) with (len := len)]; [num_st_eq | exact INV | lia | lia | exact HP] | fail 100 "cut" pc ]
        end).
    Qed.
  End L2BODY.

  Lemma p5_a50 : forall (f : nat) (e : Z), (27 <= e < 2147483648)%Z -> (e <= 27 * Z.of_nat f)%Z ->
    forall xra xt1 xt2 xa1 xs2 xs4 xt3 xt4 xt5 xt6 mm len,
    P5INV mm len -> (C -> e <= e0 /\ 135 * len + 6 * e <= 135 * len0 + 6 * e0 + 135)%Z -> evt bsegs Q (P27 0xece54 e len xra xt1 xt2 xa1 xs2 xs4 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO X8 HCL SHPX SHPL KRET.
    intros f. induction f as [|f IH]; intros e He Hf; [exfalso; lia|].
    intros until len. intros INV HP. p5_env.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xecef0%Z => first [ eapply evt_eq; [| eapply (p5_aec (e - 27)%Z) with (len := len)]; [num_st_eq | exact INV | lia | cl] | fail 100 "cut" pc ]
      | 0xece5c%Z => first [ eapply evt_eq; [| eapply (p5_a58 (e - 27)%Z ltac:(lia)) with (len := len)]; [num_st_eq | | exact INV | cl];
                             intros; eapply (IH (e - 27)%Z); [lia | lia | eassumption | eassumption] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma p5_a08 : forall (e : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xt3 xt4 xt5 xt6 mm len,
    P5INV mm len -> (0 <= e < 135)%Z -> POT len e ->
    evt bsegs Q (P5 0xece0c xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 e) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 2147450880) xs4 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO X8 HCL SHPX SHPL KRET.
    intros until len. intros INV He HP. pose proof INV as INV0. p5_open INV0. p5_env.
    assert (X496 : ((X + 496) mod 8 = 0)%Z) by (Z.div_mod_to_equations; lia).
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xed000%Z => u_trap pc
      | 0xecef0%Z => first [ eapply evt_eq; [| eapply (p5_aec e) with (len := len)]; [num_st_eq | exact INV | lia | cl] | fail 100 "cut" pc ]
      | 0xece54%Z => first [ eapply evt_eq; [| eapply (p5_a50 (Z.to_nat e) e) with (len := len)]; [num_st_eq | lia | lia | exact INV | cl] | fail 100 "cut" pc ]
      | 0xece74%Z => first [ eapply evt_eq; [| eapply (p5_M1 e ltac:(lia) (p5_a50 (Z.to_nat e) e ltac:(lia) ltac:(lia)) (Z.to_nat len) 0%Z) with (len := len)];
                             [num_st_eq | exact INV | lia | lia | exact HP] | fail 100 "cut" pc ]
      end).
  Qed.

  Variable KOK : Z -> Prop.
  Definition p5_lm_k : Prop :=
    forall (k len : Z) xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm,
      KOK k -> P5INV mm len -> (0 <= k)%Z -> (135 <= e0 - 135 * k < 2147483648)%Z -> POT len (e0 - 135 * k) ->
      evt bsegs Q (P5 0xed058 (Z_to_bv 64 0xece00) xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 (e0 - 135 * k)) (Z_to_bv 64 X) (Z_to_bv 64 B_P5LARGE) (Z_to_bv 64 5) xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 B_P5LARGE) (Z_to_bv 64 2147450880) (Z_to_bv 64 134) xt3 xt4 xt5 xt6 mm).
  Hypothesis KLM : p5_lm_k.

  Lemma p5_9fc : forall (k r : Z) xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm len,
    KOK (k + 1) -> P5INV mm len -> (0 <= k)%Z -> (135 <= e0 - 135 * k < 2147483648)%Z -> (C -> r = 1)%Z -> POT len (e0 - 135 * (k + 1)) ->
    evt bsegs Q (P5 0xece00 xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 (e0 - 135 * k)) (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                    (Z_to_bv 64 B_P5LARGE) (Z_to_bv 64 2147450880) (Z_to_bv 64 134) xt3 xt4 xt5 xt6 mm).
  Proof using ROOM X0 XLO X8 HCL SHPX SHPL KRET KLM.
    intros until len. intros HKK INV Hk He HR HP. p5_env. unfold B_P5LARGE.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xecfd8%Z => first [ zstep; eapply evt_eq; [| eapply p5_exit with (r := 0%Z) (len := len)]; [num_st_eq | exact INV | cl] | fail 100 "cut" pc ]
      | 0xecdf0%Z => first [ bstep; bstep; bstep; bstep; eapply evt_eq; [| eapply (KLM (k + 1)%Z len)]; [unfold B_P5LARGE; num_st_eq | exact HKK | exact INV | lia | lia | exact HP] | fail 100 "cut" pc ]
      | 0xece0c%Z => first [ eapply evt_eq; [| eapply (p5_a08 (e0 - 135 * (k + 1))%Z) with (len := len)]; [num_st_eq | exact INV | lia | exact HP] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma p5_entry : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (bs0 : list byte),
    KOK 0%Z -> mem_inv bsegs m0 -> stk bsegs m0 lo SP -> b_consts m0 ->
    u8arr bsegs m0 X bs0 -> length bs0 = 496%nat -> (C -> bignorm_b bs0 len0) -> rw_cells bsegs m0 (X + 496) [C2 (Z_to_bv 64 len0)] -> (0 <= len0 <= 62)%Z ->
    (0 <= e0 < 2147483648)%Z ->
    evt bsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 e0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 B_POW5) fc None m0 (seg_rom bsegs)).
  Proof using ROOM X0 XLO X8 HCL SHPX SHPL KRET KLM.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 bs0 HK0 MI ST (G1 & G2) XA XL NB XN LEN HE0.
    unfold B_POW5. p5_env.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl bsegs m0) as WM.
    set (m := m0) in MI, ST, G1, G2, XA, XN, MU at 2, WM at 2 |- *. clearbody m.
    step.
    carve_frame 48%nat ST.
    apply (rw_cells_split_CB bsegs m _ [] 48 junk [] [8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 6 step. bstep. bstep. bstep. bstep. clear G1 G2.
    num_cur_mem ltac:(fun mm => assert (INV : P5INV mm len0) by (p5_close_with ltac:(exact NB))).
    assert (HP0 : POT len0 e0) by (intros HC; specialize (HCL' HC); lia).
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xed058%Z => first [ eapply evt_eq; [| eapply (KLM 0%Z len0)]; [unfold B_P5LARGE; num_st_eq | exact HK0 | exact INV | lia | lia | replace (e0 - 135 * 0)%Z with e0 by lia; exact HP0] | fail 100 "cut" pc ]
      | 0xece0c%Z => first [ eapply evt_eq; [| eapply (p5_a08 e0) with (len := len0)]; [num_st_eq | exact INV | lia | exact HP0] | fail 100 "cut" pc ]
      end).
  Qed.
End P5.
