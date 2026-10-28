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
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.U Require Import Sj_num_sp_pdefs Sj_num_sp_acc Sj_num_sp_exp.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_ff_defs Sj_num_ff_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_x.
Local Ltac num_abstract_data ::= num_abstract_data_u.

Ltac hkstep := kstep; anorm.
Ltac hkwalk_fuel n K :=
  lazymatch n with
  | O => lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 100 "hkwalk: out of fuel at" pc end
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [ K pc | (hkstep; hkwalk_fuel n' K) ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let H := fresh "KB" in
          if_cases H; zify_cond H; num_signed_lits_in H; knorm_in H;
          first [ solve [exfalso; lia] | hkwalk_fuel n' K ]
      end
  end.
Ltac hkwalk K := hkwalk_fuel 200%nat K.
Ltac hkwalkd_fuel n K :=
  lazymatch n with
  | O => idtac "hkwalkd: out of fuel"
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [ K pc | (hkstep; hkwalkd_fuel n' K) | idtac "STUCK at" pc ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let H := fresh "KB" in
          if_cases H; zify_cond H; num_signed_lits_in H; knorm_in H;
          first [ solve [exfalso; lia] | hkwalkd_fuel n' K ]
      end
  end.
Ltac hkwalkd K := hkwalkd_fuel 200%nat K.

Definition FFINVS (E : ffenv) (m0 mm : mem) (w0 : word) : Prop :=
  (exists v vf, rw_cells bsegs mm (f_SP E + -128) (C8 w0 :: C8 v :: C8 vf :: ff_saved E)) /\
  bytes_at bsegs mm (f_A E) (f_txt E) /\
  mem_inv bsegs mm /\ munch (FF_W E) m0 mm /\ wmono bsegs m0 mm /\ stk bsegs mm (f_lo E) (f_SP E + -128).
Lemma FFINVS_of : forall E m0 mm, FFINV E m0 mm -> exists w0, FFINVS E m0 mm w0.
Proof.
  intros E m0 mm ((j & v & vf & FR) & REST). exists (le_bytes_to_word j). split; [|exact REST]. exists v, vf.
  exact (num_cb8_c8 bsegs mm _ [] _ j FR).
Qed.
Lemma FFINV_of_S : forall E m0 mm w0, FFINVS E m0 mm w0 -> FFINV E m0 mm.
Proof.
  intros E m0 mm w0 ((v & vf & FR) & REST). split; [|exact REST].
  change (C8 w0 :: C8 v :: C8 vf :: ff_saved E) with ([C8 w0] ++ (C8 v :: C8 vf :: ff_saved E)) in FR.
  apply num_rw_cells_app in FR. destruct FR as [F0 F1].
  destruct (rw_cells_forget bsegs mm _ _ F0) as (j & FJ). cbn [cells_size csize Nat.add] in FJ.
  exists j, v, vf. change (CB 8 j :: C8 v :: C8 vf :: ff_saved E) with ([CB 8 j] ++ (C8 v :: C8 vf :: ff_saved E)).
  apply num_rw_cells_app. split; [exact FJ|]. cbn [cells_size csize Nat.add] in F1 |- *. exact F1.
Qed.
Ltac ffs_open H :=
  let v := fresh "v" in let vf := fresh "vf" in
  destruct H as ((v & vf & FR) & TXT & MI & MU & WM & ST);
  unfold ff_saved in FR;
  let TXB := fresh "TXB" in pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.
Ltac ffs_close :=
  lazymatch goal with
  | |- FFINVS _ _ _ _ =>
      split; [eexists _, _; eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Section FFPN.
  Variable E : ffenv.
  Hypothesis OK : ff_ok E.
  Variable m0 : mem.

  Hypothesis SHPT : forall m', munch (FF_W E) m0 m' -> wmono bsegs m0 m' -> shz m' (f_p E) (8 * (f_n E / 8)).
  Hypothesis SHL1 : forall m', munch (FF_W E) m0 m' -> wmono bsegs m0 m' -> shz m' 0x28c20 10416.
  Hypothesis SHL2 : forall m', munch (FF_W E) m0 m' -> wmono bsegs m0 m' -> shz m' 0x2b5a0 640.
  Notation A := (f_A E).
  Notation TL := (f_TL E).
  Notation FIRST := (f_FIRST E).
  Notation LAST := (f_LAST E).

  Ltac num_mark_words :=
    repeat match goal with
    | x : word |- _ => lazymatch goal with _ : IsData x |- _ => fail | _ => idtac end; let M := fresh "DM" in assert (M : IsData x) by exact I
    end.
  Ltac pn_start INV := (let I0 := fresh "INV0" in pose proof INV as I0);
    lazymatch goal with INVh : FFINV _ _ _ |- _ => let I1 := fresh "INV1" in pose proof INVh as I1; ff_open I1 end; ff_env OK; num_mark_words.
  Ltac pns_start INV := (let I0 := fresh "INV0" in pose proof INV as I0);
    lazymatch goal with INVh : FFINVS _ _ _ _ |- _ => let I1 := fresh "INV1" in pose proof INVh as I1; ffs_open I1 end; ff_env OK; num_mark_words.
  Ltac cut_cf4 INV HLT := first [ eapply evt_eq; [| eapply (ff_cf4 E OK m0)]; [num_st_eq | exact INV | assumption | exact HLT] | fail 100 "cut cf4" ].
  Ltac cut_exit INV := first [ eapply evt_eq; [| eapply (ff_exit E OK m0)]; [num_st_eq | exact INV | assumption] | fail 100 "cut exit" ].
  Ltac cut_884 INV q := first [ eapply evt_eq; [| eapply (ff_884 E OK m0 SHL1 SHL2 q)]; [num_st_eq | exact INV | assumption | lia] | fail 100 "cut 884" ].

  Lemma ffb_L5 : forall (f : nat) (c cnt q : Z) xra xs0 xs1 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= c < LAST)%Z -> (- (c - A) <= cnt <= 4294967296)%Z -> (-9223372036854775808 <= q < 9223372036854775808)%Z -> (LAST - c <= Z.of_nat f)%Z ->
    evt bsegs (ff_mid E m0) (FFS E 0xb2c34 xra (Z_to_bv 64 (cnt)) (Z_to_bv 64 (q)) (Z_to_bv 64 (-1)) xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (c)) (Z_to_bv 64 (c)) (Z_to_bv 64 (46)) xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (48)) xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM HLT Hc Hcnt Hq Hf; [exfalso; lia|].
    pn_start INV. bstep.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xb30c0%Z => u_trap pc
      | 0xb308c%Z => cut_cf4 INV HLT
      | 0xb2c88%Z => cut_884 INV q
      | 0xb2c34%Z => first [ eapply evt_eq; [| eapply (IH (c + 1)%Z _ q)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffb_814 : forall (IP dc q : Z) xra xt2 xs0 xs1 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= IP < LAST)%Z -> (0 <= dc <= 4294967296)%Z -> (-9223372036854775808 <= q < 9223372036854775808)%Z ->
    evt bsegs (ff_mid E m0) (FFS E 0xb2c18 xra (Z_to_bv 64 (dc)) (Z_to_bv 64 (q)) xt2 xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (IP)) xa3 xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM HLT Hip Hdc Hq. pn_start INV.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xb30c0%Z => u_trap pc
      | 0xb308c%Z => first [ exfalso; lia | cut_cf4 INV HLT ]
      | 0xb2c88%Z => cut_884 INV q
      | 0xb2c34%Z => first [ eapply evt_eq; [| eapply (ffb_L5 (Z.to_nat LAST) IP dc q)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffb_800 : forall (IP dc ex en : Z) xra xt2 xs0 xs1 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= IP < LAST)%Z -> (0 <= dc <= 4294967296)%Z -> (-2147483648 <= ex <= 0)%Z -> (- EN_MAX <= en <= EN_MAX)%Z ->
    evt bsegs (ff_mid E m0) (FFS E 0xb2c04 xra (Z_to_bv 64 (dc)) (Z_to_bv 64 (ex)) xt2 xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (IP)) xa3 xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (en)) xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM HLT Hip Hdc Hex Hen. unfold EN_MAX in Hen.
    hkwalk ltac:(fun pc => lazymatch pc with
      | 0xb30c0%Z => u_trap_b pc
      | 0xb2c18%Z => first [ eapply evt_eq; [| eapply (ffb_814 IP dc (ex + en)%Z)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffb_7f8 : forall (IP dc ex en : Z) xra xt2 xs0 xs1 xa3 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= IP < LAST)%Z -> (0 <= dc <= 4294967296)%Z -> (-2147483648 <= ex <= 0)%Z -> (0 <= en <= EN_MAX)%Z ->
    evt bsegs (ff_mid E m0) (FFS E 0xb2bfc xra (Z_to_bv 64 (dc)) (Z_to_bv 64 (ex)) xt2 xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (IP)) xa3 xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (en)) xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM HLT Hip Hdc Hex Hen.
    hkwalk ltac:(fun pc => lazymatch pc with
      | 0xb2c04%Z => first [ eapply evt_eq; [| eapply (ffb_800 IP dc ex _)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia | unfold EN_MAX in *; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffb_L4 : forall (f : nat) (IP dc ex en e : Z) xra xt2 xs1 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= IP < LAST)%Z -> (0 <= dc <= 4294967296)%Z -> (-2147483648 <= ex <= 0)%Z -> (0 <= en <= EN_MAX)%Z -> (A <= e < LAST)%Z -> (LAST - e <= Z.of_nat f)%Z ->
    evt bsegs (ff_mid E m0) (FFS E 0xb2ba0 xra (Z_to_bv 64 (dc)) (Z_to_bv 64 (ex)) xt2 (Z_to_bv 64 (2)) xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (IP)) (Z_to_bv 64 (e)) (Z_to_bv 64 (e)) xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (en)) (Z_to_bv 64 (9)) (Z_to_bv 64 (10)) (Z_to_bv 64 (268435455)) xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM HLT Hip Hdc Hex Hen He Hf; [exfalso; lia|].
    pose proof INV as INV0. ff_open INV0. ff_env OK. unfold EN_MAX in Hen.
    assert (DR : forall x, (0 <= Z.land x 255 < 256)%Z) by (intros x; rewrite land_255; apply Z.mod_pos_bound; lia).
    hkstep.
    hkwalk ltac:(fun pc => lazymatch pc with
      | 0xb30c0%Z => u_trap_b pc
      | 0xb2bfc%Z => first [ eapply evt_eq; [| eapply (ffb_7f8 IP dc ex _)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia |];
                             unfold EN_MAX;
                             repeat match goal with |- context [Z.land ?x 255] => pose proof (DR x); rewrite (land_255 x) in * end; lia
                           | fail 100 "cut" pc ]
      | 0xb2ba0%Z => first [ eapply evt_eq; [| eapply (IH IP dc ex _ (e + 1)%Z)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia | | lia | lia];
                             unfold EN_MAX;
                             repeat match goal with |- context [Z.land ?x 255] => pose proof (DR x); rewrite (land_255 x) in * end; lia
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma ffb_6d0 : forall (IP dc ex p : Z) xra xt2 xs0 xs1 xa4 xa5 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm,
    FFINV E m0 mm -> frm0 xfc -> (FIRST < LAST)%Z -> (A <= IP < LAST)%Z -> (0 <= dc <= 4294967296)%Z -> (-2147483648 <= ex <= 0)%Z -> (A <= p <= LAST)%Z ->
    evt bsegs (ff_mid E m0) (FFS E 0xb2ad4 xra (Z_to_bv 64 (dc)) (Z_to_bv 64 (ex)) xt2 xs0 xs1 (Z_to_bv 64 (FIRST)) (Z_to_bv 64 (LAST)) (Z_to_bv 64 (IP)) (Z_to_bv 64 (p)) xa4 xa5 (Z_to_bv 64 2147450880) xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT SHL1 SHL2.
    intros until mm. intros INV FRM HLT Hip Hdc Hex Hp.
    pose proof INV as INV0. ff_open INV0. ff_env OK.
    hkwalk ltac:(fun pc => lazymatch pc with
      | 0xb30c0%Z => u_trap_b pc
      | 0xb2c18%Z => first [ eapply evt_eq; [| eapply (ffb_814 IP dc ex)]; [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia] | fail 100 "cut" pc ]
      | 0xb2ba0%Z => first [ eapply evt_eq; [| eapply (ffb_L4 (Z.to_nat LAST) IP dc ex 0%Z _)];
                             [num_st_eq | exact INV | assumption | exact HLT | lia | lia | lia | unfold EN_MAX; lia | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End FFPN.
