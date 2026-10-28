(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber SjNumU SjNumN SjNumSwar.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs Sj_num_fc_pdefs Sj_num_fc_tail Sj_num_fc_k14 Sj_num_fc_pp1 Sj_num_fc_pp2 Sj_num_fc_pp2b Sj_num_fc_pp2c Sj_num_fc_pp3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_w.

Local Ltac num_abstract_data ::= num_abstract_data_u.

Lemma fcb_digit_zextb : forall b, (0 <= b < 256)%Z -> (((b + -48) mod 18446744073709551616) mod 256 <= 9)%Z -> (48 <= b <= 57)%Z.
Proof. intros b Hb H. Z.div_mod_to_equations. lia. Qed.

Lemma fcb_sxb_u : forall b : byte, bv_unsigned (sxb b) = (if (bv_unsigned b <? 128)%Z then bv_unsigned b else bv_unsigned b + 18446744073709551360)%Z.
Proof.
  intros b. unfold sxb. rewrite Z_to_bv_unsigned. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8)%Z with 256%Z in *. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  change (256 / 2)%Z with 128%Z. destruct (Z.ltb_spec (bv_unsigned b) 128); Z.div_mod_to_equations; lia.
Qed.
Lemma fcb_le4zs : forall b0 b1 b2 (b3 : byte), (0 <= b0 < 256)%Z -> (0 <= b1 < 256)%Z -> (0 <= b2 < 256)%Z ->
  exists hi, (Z.lor (Z.lor (Z.shiftl (bv_unsigned (sxb b3)) 24 mod 18446744073709551616) (Z.shiftl b2 16 mod 18446744073709551616))
                    (Z.lor (Z.shiftl b1 8 mod 18446744073709551616) b0)
              = b0 + 256 * (b1 + 256 * (b2 + 256 * (bv_unsigned b3 + 256 * hi))))%Z /\ (0 <= hi < 4294967296)%Z.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2.
  pose proof (bv_unsigned_in_range 8 b3) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8)%Z with 256%Z in R.
  rewrite fcb_sxb_u. destruct (Z.ltb_spec (bv_unsigned b3) 128) as [L|L].
  - exists 0%Z. split; [| lia]. pose proof (le4z_eq b0 b1 b2 (bv_unsigned b3) H0 H1 H2 ltac:(lia)) as EQ. unfold le4z in EQ. rewrite EQ. lia.
  - exists 4294967295%Z. split; [| lia].
    rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 24)%Z with 16777216%Z. change (2 ^ 16)%Z with 65536%Z. change (2 ^ 8)%Z with 256%Z.
    assert (X3 : ((bv_unsigned b3 + 18446744073709551360) * 16777216 mod 18446744073709551616 = bv_unsigned b3 * 16777216 + 18446744069414584320)%Z)
      by (Z.div_mod_to_equations; lia).
    rewrite X3. rewrite !Z.mod_small by lia.
    rewrite (lor_disj (b1 * 256) b0 8) by (try apply Z.mod_mul; change (2 ^ 8)%Z with 256%Z; lia).
    rewrite (lor_disj (bv_unsigned b3 * 16777216 + 18446744069414584320) (b2 * 65536) 24)
      by (change (2 ^ 24)%Z with 16777216%Z; try lia; Z.div_mod_to_equations; lia).
    rewrite (lor_disj (bv_unsigned b3 * 16777216 + 18446744069414584320 + b2 * 65536) (b1 * 256 + b0) 16)
      by (change (2 ^ 16)%Z with 65536%Z; try lia; Z.div_mod_to_equations; lia).
    lia.
Qed.

Lemma fcb_swar4 : forall E p w hi X,
  w = (sp_tb E p + 256 * (sp_tb E (p + 1) + 256 * (sp_tb E (p + 2) + 256 * (sp_tb E (p + 3) + 256 * hi))))%Z -> (0 <= hi < 4294967296)%Z ->
  Z.land (Z.lor X (bv_swrap 32 (w + 18446744072901087184) mod 18446744073709551616)) 18446744071570489472 = 0%Z ->
  forall i, (p <= i < p + 4)%Z -> (48 <= sp_tb E i)%Z.
Proof.
  intros E p w hi X HWq HHI H. eapply (sp_swar4 E p w hi X HWq).
  rewrite (Z.mod_small w); [exact H|]. subst w.
  pose proof (sp_tb_range E p). pose proof (sp_tb_range E (p + 1)). pose proof (sp_tb_range E (p + 2)). pose proof (sp_tb_range E (p + 3)). lia.
Qed.

Section FCBPP4.
  Variable E : fcbenv.
  Hypothesis OK : fcb_ok E.
  Hypothesis PV : fcb_prov E.
  Variable Q : machine_state -> Prop.
  Hypothesis K14 : fcb_kf14 E Q.
  Hypothesis KERR1 : fcb_kerr1 E Q.
  Notation A := (q_A E).
  Notation FIRST := (q_FIRST E).
  Notation LAST := (q_LAST E).
  Notation OUT := (q_OUT E).
  Notation f := (q_f E).
  Notation P2 L := (L E OK PV Q K14) (only parsing).
  Ltac cut_err INV FRM := first [ eapply evt_eq; [| eapply KERR1]; [num_st_eq | unfold FCB_ERR1; cbn [In]; repeat (first [left; reflexivity | right]) | exact INV | exact FRM | reflexivity] | fail 100 "cut err" ].

  Lemma fcb_534 : forall (IP IL p : Z) c0 c8 c16 c24 c48 xt0 xt1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs10 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 (Z_to_bv 64 OUT) (Z_to_bv 64 IL) c48 (Z_to_bv 64 (IP + IL + 1)) -> frm0 xfc -> sp_ffacts E IP IL p -> (FIRST <= IP)%Z ->
    evt bsegs Q (FCS E 0xe8938 (Z_to_bv 64 (46)) xt0 xt1 (Z_to_bv 64 (53)) (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 (p)) xs10 (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14 KERR1.
    intros until mm. intros INV FRM FF HIP.
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap_b pc
      | 0x7f338%Z => cut_err INV FRM
      | 0xe8970%Z => first [ eapply evt_eq; [| eapply (P2 fcb_56c IP IL (IP + IL + 1)%Z (p - (IP + IL + 1))%Z (IP + IL + 1 - p)%Z p c0 c8 c16 c24 (Z_to_bv 64 OUT) c48)];
                             [num_st_eq | exact INV | assumption | apply sp_ffacts_pfacts; [exact FF | lia] | exact HIP | lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_L3 : forall (f : nat) (IP IL p : Z) c0 c8 c16 c24 c48 xt0 xt1 xa1 xa2 xa4 xa7 xs7 xs10 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 (Z_to_bv 64 OUT) (Z_to_bv 64 IL) c48 (Z_to_bv 64 (IP + IL + 1)) -> frm0 xfc -> sp_ffacts E IP IL p -> (FIRST <= IP)%Z -> (p < LAST)%Z -> (LAST - p <= Z.of_nat f)%Z ->
    evt bsegs Q (FCS E 0xe88e8 (Z_to_bv 64 (46)) xt0 xt1 (Z_to_bv 64 (53)) (q_sp E) (Z_to_bv 64 (q_spq E)) (Z_to_bv 64 (p)) xa1 xa2 (Z_to_bv 64 (9)) xa4 (Z_to_bv 64 (-1)) (Z_to_bv 64 (10)) xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 (p)) xs10 (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14 KERR1.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM FF HIP Hp Hf; [exfalso; lia|].
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    pose proof (sp_tb_range E p) as Rp. unfold sp_tb in Rp.
    pose proof (fcb_digit_zextb _ Rp) as DG.
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap_b pc
      | 0xe8938%Z => first [ eapply evt_eq; [| eapply (fcb_534 IP IL _ c0 c8 c16 c24 c48)]; [num_st_eq | exact INV | assumption | | exact HIP];
                             first [ exact FF
                                   | replace (q_LAST E) with (p + 1)%Z by lia;
                                     apply sp_ffacts_app; [exact FF | lia | lia | apply sp_ge48_1; unfold sp_tb; lia] ]
                           | fail 100 "cut" pc ]
      | 0xe88e8%Z => first [ eapply evt_eq; [| eapply (IH IP IL (p + 1)%Z c0 c8 c16 c24 c48)];
                             [num_st_eq | exact INV | assumption | apply sp_ffacts_app; [exact FF | lia | lia | apply sp_ge48_1; unfold sp_tb; lia] | exact HIP | lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_4d0 : forall (IP IL p : Z) c0 c8 c16 c24 c48 xt0 xt1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs10 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 (Z_to_bv 64 OUT) (Z_to_bv 64 IL) c48 (Z_to_bv 64 (IP + IL + 1)) -> frm0 xfc -> sp_ffacts E IP IL p -> (FIRST <= IP)%Z ->
    evt bsegs Q (FCS E 0xe88d4 (Z_to_bv 64 (46)) xt0 xt1 (Z_to_bv 64 (53)) (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 (p)) xs10 (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14 KERR1.
    intros until mm. intros INV FRM FF HIP.
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap_b pc
      | 0xe8938%Z => first [ eapply evt_eq; [| eapply (fcb_534 IP IL p c0 c8 c16 c24 c48)]; [num_st_eq | exact INV | assumption | exact FF | exact HIP] | fail 100 "cut" pc ]
      | 0xe88e8%Z => first [ eapply evt_eq; [| eapply (fcb_L3 (Z.to_nat LAST) IP IL p c0 c8 c16 c24 c48)]; [num_st_eq | exact INV | assumption | exact FF | exact HIP | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_3fc : forall (IP IL p : Z) c0 c8 c16 c24 c48 xt1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs10 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 (Z_to_bv 64 OUT) (Z_to_bv 64 IL) c48 (Z_to_bv 64 (IP + IL + 1)) -> frm0 xfc -> sp_ffacts E IP IL p -> (FIRST <= IP)%Z -> (p + 4 <= LAST)%Z ->
    evt bsegs Q (FCS E 0xe8800 (Z_to_bv 64 (46)) (Z_to_bv 64 (p)) xt1 (Z_to_bv 64 (53)) (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 (p)) xs10 (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14 KERR1.
    intros until mm. intros INV FRM FF HIP Hp.
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap_b pc
      | 0xe88d4%Z => first [ eapply evt_eq; [| eapply (fcb_4d0 IP IL _ c0 c8 c16 c24 c48)]; [num_st_eq | exact INV | assumption | | exact HIP];
                             first [ exact FF
                                   | apply sp_ffacts_app; [exact FF | lia | lia |];
                                     lazymatch goal with KB : Z.land _ 18446744071570489472 = 0%Z |- _ =>
                                       destruct (fcb_le4zs (sp_tb E p) (sp_tb E (p + 1)) (sp_tb E (p + 2)) (nth (Z.to_nat (p + 3 - A)) (q_txt E) (Z_to_bv 8 0))
                                                   (sp_tb_range E p) (sp_tb_range E (p + 1)) (sp_tb_range E (p + 2))) as (hi & HW & HHI);
                                       unfold sp_tb in HW; rewrite HW in KB;
                                       eapply (fcb_swar4 E p _ hi _ eq_refl HHI); unfold sp_tb; exact KB end ]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_3f4 : forall (IP IL p : Z) c0 c8 c16 c24 c48 xt1 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs7 xs10 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 (Z_to_bv 64 OUT) (Z_to_bv 64 IL) c48 (Z_to_bv 64 (IP + IL + 1)) -> frm0 xfc -> sp_ffacts E IP IL p -> (FIRST <= IP)%Z ->
    evt bsegs Q (FCS E 0xe87f8 (Z_to_bv 64 (46)) (Z_to_bv 64 (p)) xt1 (Z_to_bv 64 (53)) (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (LAST - p)) xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 (p)) xs10 (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV K14 KERR1.
    intros until mm. intros INV FRM FF HIP.
    pose proof INV as INV0. fcp_open INV0. pose proof OK as OK'. fcb_env OK'. clear FSH TSEP. fcb_prov PV.
    pose proof FF as ((F1 & F2 & F3 & F4) & _).
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xe9f5c%Z => u_trap_b pc
      | 0xe88d4%Z => first [ eapply evt_eq; [| eapply (fcb_4d0 IP IL p c0 c8 c16 c24 c48)]; [num_st_eq | exact INV | assumption | exact FF | exact HIP] | fail 100 "cut" pc ]
      | 0xe8800%Z => first [ eapply evt_eq; [| eapply (fcb_3fc IP IL p c0 c8 c16 c24 c48)]; [num_st_eq | exact INV | assumption | exact FF | exact HIP | lia] | fail 100 "cut" pc ]
      end).
  Qed.
End FCBPP4.
