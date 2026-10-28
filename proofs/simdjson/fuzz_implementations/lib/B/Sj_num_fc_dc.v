(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU SjNumN SjNumSwar.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs Sj_num_fc_tail Sj_num_pm_defs Sj_num_pm_top.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Lemma magic_10000 : forall v, (0 <= v < 18446744073709551616 -> v * 3777893186295716171 / 18446744073709551616 / 2048 = v / 10000)%Z.
Proof. intros. Z.div_mod_to_equations. lia. Qed.
Lemma magic_100 : forall v, (0 <= v < 18446744073709551616 -> (v / 4) * 2951479051793528259 / 18446744073709551616 / 4 = v / 100)%Z.
Proof. intros. Z.div_mod_to_equations. lia. Qed.
Lemma magic_10000_m : forall v, (0 <= v < 18446744073709551616)%Z ->
  Z.shiftr (Z.shiftr (v * 3777893186295716171) 64 mod 18446744073709551616) 11 = (v / 10000)%Z.
Proof.
  intros v H. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 64)%Z with 18446744073709551616%Z. change (2 ^ 11)%Z with 2048%Z.
  rewrite Z.mod_small by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). apply magic_10000. exact H.
Qed.
Lemma magic_100_m : forall v, (0 <= v < 18446744073709551616)%Z ->
  Z.shiftr (Z.shiftr (Z.shiftr v 2 * 2951479051793528259) 64 mod 18446744073709551616) 2 = (v / 100)%Z.
Proof.
  intros v H. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 64)%Z with 18446744073709551616%Z. change (2 ^ 2)%Z with 4%Z.
  assert (Q : (0 <= v / 4 < 4611686018427387904)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite Z.mod_small by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). apply magic_100. exact H.
Qed.
Ltac shr2div :=
  repeat match goal with
  | H : context [Z.shiftr ?x 4] |- _ => rewrite (Z.shiftr_div_pow2 x 4) in H by lia; change (2 ^ 4)%Z with 16%Z in H
  end.
Lemma fcb_sx32_small : forall x, (0 <= x < 2147483648)%Z -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_id by lia. reflexivity. Qed.

Lemma fcb_c8_split_lo : forall segs (m : mem) A d, rw_cells segs m A [C8 (Z_to_bv 64 d)] -> (0 <= d < 4294967296)%Z ->
  rw_cells segs m A [C4 (Z_to_bv 64 d); C4 (Z_to_bv 64 0)].
Proof.
  intros segs m A d [[Hwf Hb] Hw] Hd. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in Hb.
    replace (le4 (Z_to_bv 64 d) ++ le4 (Z_to_bv 64 0) ++ []) with (le8 (Z_to_bv 64 d)); [exact Hb|].
    unfold le8, word_to_le_bytes, le4. rewrite !unsigned_lit by lia.
    cbn [Z_to_le_bytes app]. rewrite !Z.shiftr_shiftr by lia.
    assert (HS : forall k, (32 <= k)%Z -> Z.shiftr d k = 0%Z).
    { intros k Hk. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. split; [lia|].
      assert (2 ^ 32 <= 2 ^ k)%Z by (apply Z.pow_le_mono_r; lia). change (2 ^ 32)%Z with 4294967296%Z in *. lia. }
    rewrite (HS (8 + 8 + 8 + 8)%Z), (HS (8 + 8 + 8 + 8 + 8)%Z), (HS (8 + 8 + 8 + 8 + 8 + 8)%Z), (HS (8 + 8 + 8 + 8 + 8 + 8 + 8)%Z) by lia. rewrite !Z.shiftr_0_l.
    reflexivity.
  - exact Hw.
Qed.

Definition FCINVc (E : fcbenv) (mm : mem) (c0 c8 c16 c24 c32 c40 c48 c56 : word) (q : Z) (w lm : word) (nb tm IP IL FPT FL : Z) (bs : list byte) (len dg : Z) : Prop :=
  rw_cells bsegs mm (q_spq E) (fcb_spill E c0 c8 c16 c24 c32 c40 c48 c56) /\
  (exists vb j5 er j4, rw_cells bsegs mm (q_spq E + 72) (fcb_pns q w lm nb vb tm j5 IP IL FPT FL er j4)) /\ (0 <= nb <= 1)%Z /\ (0 <= tm <= 1)%Z /\
  rw_cells bsegs mm (q_spq E + 144) [C8 (Z_to_bv 64 dg)] /\
  (exists h0, rw_cells bsegs mm (q_f E) [CB 8 h0]) /\
  u8arr bsegs mm (q_f E + 32) bs /\ length bs = 496%nat /\ rw_cells bsegs mm (q_f E + 528) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z /\
  (exists j6, rw_cells bsegs mm (q_f E + 530) [CB 6 j6]) /\
  rw_cells bsegs mm (q_f E / 8 + 2147450884) [CB 63 (repeat (Z_to_bv 8 0) 63)] /\
  (exists v, rw_cells bsegs mm (q_OUT E) [C8 v]) /\
  bytes_at bsegs mm (q_A E) (q_txt E) /\
  mem_inv bsegs mm /\ munch (fcb_W E) (q_m0 E) mm /\ wmono bsegs (q_m0 E) mm /\ stk bsegs mm (q_lo E) (q_spq E).
Ltac fcc_open H :=
  let vb := fresh "vb" in let j5 := fresh "j5" in let er := fresh "er" in let j4 := fresh "j4" in
  let h0 := fresh "h0" in let j6 := fresh "j6" in let v := fresh "v" in
  destruct H as (SPILL & (vb & j5 & er & j4 & PNS) & ?NBR & ?TMR & DGC & (h0 & HDR) & XA & ?XL & XN & ?LEN & (j6 & XPAD) & BSH & (v & OUTC) & TXT & MI & MU & WM & ST);
  unfold fcb_spill in SPILL; unfold fcb_pns in PNS; unfold fcb_W in MU;
  let TXB := fresh "TXB" in pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.

Definition fcb_kpdc (E : fcbenv) (Q : machine_state -> Prop) : Prop :=
  forall xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc mm c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL bs len dg e,
    FCINVc E mm c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL bs len dg -> frm0 xfc ->
    bignorm_b bs len -> (len + 21 <= 62)%Z -> (0 <= e <= 328)%Z ->
    evt bsegs Q (FCB E 0xfadcc (Z_to_bv 64 0xf8a98) xt0 xt1 xt2 (Z_to_bv 64 (q_f E + 32)) (Z_to_bv 64 e) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (q_f E)) xs5 xs6 xs7 xs8 xs9
                     (Z_to_bv 64 (q_OUT E)) xt3 xt4 xt5 xt6 xF xfc mm).
Definition fcb_kndc (E : fcbenv) (Q : machine_state -> Prop) : Prop :=
  forall xt0 xt1 xt2 xa1 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc mm c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL bs len dg e p2,
    FCINVc E mm c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL bs len dg -> frm0 xfc ->
    (0 < e <= 1111)%Z -> (- NDCB_RANGE <= p2 <= NDCB_RANGE)%Z ->
    evt bsegs Q (FCB E 0xfaff8 (Z_to_bv 64 0xf8ab8) xt0 xt1 xt2 (Z_to_bv 64 (q_f E + 32)) xa1 (Z_to_bv 64 (p2 mod 4294967296)) (Z_to_bv 64 (- e)) xa4 xa5 xa6 xa7
                     (Z_to_bv 64 (q_f E)) xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (q_OUT E)) xt3 xt4 xt5 xt6 xF xfc mm).

Definition fcb_kmset (E : fcbenv) (Q : machine_state -> Prop) : Prop :=
  forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xt3 xt4 xt5 xt6 xF xfc mm c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL sci p2,
    FCINV E mm true (repeat (Z_to_bv 8 0) 63) c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc ->
    fcb_spans E IP IL FPT FL -> (-342 <= sci <= 327)%Z -> (-1000384 <= p2 <= 1000384)%Z ->
    evt bsegs Q (FCB E 0x84bc4 (Z_to_bv 64 0xf8a58) xt0 xt1 xt2 (Z_to_bv 64 (q_f E + 32)) (Z_to_bv 64 0) (Z_to_bv 64 504) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (q_f E)) xs5 xs6
                     (Z_to_bv 64 (q_f E + 32)) (Z_to_bv 64 sci) (Z_to_bv 64 p2) (Z_to_bv 64 (q_OUT E)) xt3 xt4 xt5 xt6 xF xfc mm).

Section FCBDC.
  Variable E : fcbenv.
  Hypothesis OK : fcb_ok E.
  Hypothesis PV : fcb_prov E.
  Variable Q : machine_state -> Prop.
  Hypothesis KF5 : fcb_kf5 E Q.
  Hypothesis KPDC : fcb_kpdc E Q.
  Hypothesis KNDC : fcb_kndc E Q.
  Hypothesis KMSET : fcb_kmset E Q.
  Notation OUT := (q_OUT E).
  Notation f := (q_f E).

  Lemma fcb_904 : forall (sci p2 : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xt3 xt4 xt5 xt6 xF xfc mm c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL bs len dg,
    FCINVc E mm c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL bs len dg -> frm0 xfc ->
    pmb_export bs len dg -> (-342 <= sci <= 327)%Z -> (-1000384 <= p2 <= 1000384)%Z ->
    evt bsegs Q (FCB E 0xf8a6c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 sci) (Z_to_bv 64 p2) (Z_to_bv 64 OUT)
                     xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KPDC KNDC.
    intros until dg. intros INV FRM (HDG & HCNT & HNRM) HSCI HP2. pose proof INV as INV0. fcc_open INV0. fcb_env OK. fcb_prov PV. unfold PMB_NORM_DG in HNRM.
    assert (D1 : IsData xs6) by exact I.
    apply fcb_c8_split_lo in DGC; [|lia].
    bwalk ltac:(fun pc => lazymatch pc with | 0xf8cc0%Z => u_trap pc | 0xf8a7c%Z => idtac end).
    rewrite (fcb_sx32_small dg) by lia.
    bwalk ltac:(fun pc => lazymatch pc with
      | 0xf8cc0%Z => u_trap pc
      | 0xfadcc%Z => first [ eapply evt_eq; [| eapply KPDC with (bs := bs) (len := len) (dg := dg) (e := (sci + 1 - dg)%Z)];
                             [num_st_eq | exact INV | exact FRM | apply HNRM; lia | lia | lia] | fail 100 "cut" pc ]
      | 0xfaff8%Z => first [ eapply evt_eq; [| eapply KNDC with (bs := bs) (len := len) (dg := dg) (e := (dg - sci - 1)%Z) (p2 := (p2 + 32768)%Z)];
                             [num_st_eq | exact INV | exact FRM | lia | unfold NDCB_RANGE; lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fcb_8f0 : forall (sci p2 : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xt3 xt4 xt5 xt6 xF xfc mm c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm false (repeat (Z_to_bv 8 0) 63) c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL ->
    rw_cells bsegs mm (f + 32) [CB 504 (repeat (Z_to_bv 8 0) 504)] -> b_consts mm -> frm0 xfc ->
    fcb_spans E IP IL FPT FL -> (-342 <= sci <= 327)%Z -> (-1000384 <= p2 <= 1000384)%Z ->
    evt bsegs Q (FCB E 0xf8a58 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 xs6 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 sci) (Z_to_bv 64 p2) (Z_to_bv 64 OUT)
                     xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK PV KPDC KNDC.
    intros until FL. intros INV BIGZ BC FRM SPN HSCI HP2. fc_open INV. pose proof OK as OK'. fcb_env OK'.
    destruct PV as (SHPT & SHPO & SHPF & SHPL & _). unfold fcb_W in SHPT, SHPO, SHPF, SHPL.
    assert (LO0 : (0 <= q_lo E)%Z) by (destruct ST as [? _]; assumption).

    apply (rw_cells_split_CB bsegs mm _ [] 504 _ [] [496;2;6]%nat) in BIGZ; [|reflexivity]. cbn [mk_CB_cells app] in BIGZ.
    lazymatch type of BIGZ with rw_cells _ _ _ [?c1; ?c2; ?c3] => change [c1; c2; c3] with ([c1] ++ [c2] ++ [c3]) in BIGZ end.
    apply num_rw_cells_app in BIGZ. destruct BIGZ as [LIMBS REST]. apply num_rw_cells_app in REST. destruct REST as [LENC PADC].
    cbn [cells_size csize Nat.add Nat.mul] in LENC, PADC.
    replace (f + 32 + Z.of_nat 496)%Z with (f + 528)%Z in LENC by lia.
    replace (f + 32 + Z.of_nat 496 + Z.of_nat 2)%Z with (f + 530)%Z in PADC by lia.
    replace (firstn 2 (skipn 496 (repeat (Z_to_bv 8 0) 504))) with (le2 (Z_to_bv 64 0)) in LENC by (vm_compute; reflexivity).
    apply num_cb2_c2 in LENC.
    apply u8arr_of_rw_cells in LIMBS.
    match type of LIMBS with u8arr _ _ _ ?b => set (bs0 := b) in LIMBS; assert (XL0 : length bs0 = 496%nat) by (vm_compute; reflexivity); clearbody bs0 end.
    destruct (rw_cells_forget bsegs mm _ _ DGC) as [jd' JD]. cbn [cells_size csize Nat.add] in JD.
    bwalk ltac:(fun pc => lazymatch pc with | 0xf8cc0%Z => u_trap pc | 0xf8f88%Z => idtac end).

    set (SUB := firstn (Z.to_nat (q_LAST E - q_FIRST E)) (skipn (Z.to_nat (q_FIRST E - q_A E)) (q_txt E))).
    assert (SUBL : Z.of_nat (length SUB) = (q_LAST E - q_FIRST E)%Z) by (unfold SUB; rewrite length_firstn, length_skipn; lia).
    assert (SUBT : bytes_at bsegs mm (q_FIRST E) SUB).
    { pose proof (bytes_at_sub bsegs mm (q_A E) (q_txt E) (Z.to_nat (q_FIRST E - q_A E)) (Z.to_nat (q_LAST E - q_FIRST E)) TXT ltac:(lia)) as HB.
      replace (q_A E + Z.of_nat (Z.to_nat (q_FIRST E - q_A E)))%Z with (q_FIRST E) in HB by lia. exact HB. }
    clearbody SUB. unfold fcb_spans in SPN.
    set (E' := mkPmbEnv (Z_to_bv 64 1018476) (Z_to_bv 64 (q_spq E)) (q_gp E) (q_tp E) (q_sp E) (Z_to_bv 64 (q_spq E)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880)
                 (Z_to_bv 64 (q_S E)) xs5 xs6 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 sci) (Z_to_bv 64 p2) (Z_to_bv 64 OUT) (Z_to_bv 64 f) xF xfc
                 (f + 32) (q_spq E + 72) (q_spq E + 144) (q_FIRST E) IP IL FPT FL (q_lo E) SUB mm).
    assert (USP : bv_unsigned (Z_to_bv 64 (q_spq E)) = q_spq E) by (apply unsigned_lit; lia).
    assert (XD : ((f + 32) / 8 + 2147450880 = f / 8 + 2147450884)%Z) by (Z.div_mod_to_equations; lia).
    assert (OK1 : pmb_ok E').
    { constructor; unfold E'; cbn [p_sp p_X p_N p_DG p_A p_IP p_IL p_FPT p_FL p_lo p_txt]; rewrite ?USP, ?XD;
        unfold PMB_STACK, PMB_GTOP, USTACK_TOP, NUM_TXT_MAX, pm_spans_ok; first [ lia | Z.div_mod_to_equations; lia ]. }
    assert (LIFT : forall m', munch (pmb_W E') mm m' -> wmono bsegs mm m' ->
                     munch [(q_lo E, q_spq E + 152); (f, f + 8); (f + 32, f + 536); (q_S E + 4, q_S E + 67); (OUT, OUT + 8)]%Z (q_m0 E) m' /\ wmono bsegs (q_m0 E) m').
    { intros m' MU' WM'. split; [| eapply wmono_trans; eassumption].
      eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU'].
      intros x Hx. unfold pmb_W, E'. cbn [p_sp p_X p_DG]. rewrite ?USP. unfold PMB_STACK. cbn [outside] in *. lia. }
    assert (PV1 : pmb_prov E').
    { unfold pmb_prov, PMB_POW10.
      split; [| split; [| split]]; intros m' MU' WM'; destruct (LIFT m' MU' WM') as [MU2 WM2]; unfold E'; cbn [p_A p_txt p_N p_DG].
      - eapply shz_sub; [exact (SHPT m' MU2 WM2) | lia | lia].
      - eapply shz_sub; [exact (SHPF m' MU2 WM2) | lia | lia].
      - eapply shz_sub; [exact (SHPF m' MU2 WM2) | lia | lia].
      - exact (SHPL m' MU2 WM2). }

    pose proof PNS as PNS0.
    lazymatch type of PNS0 with rw_cells _ _ _ [?a1; ?a2; ?a3; ?a4; ?a5; ?a6; ?a7; ?s1; ?s2; ?s3; ?s4; ?e1; ?e2] =>
      change [a1; a2; a3; a4; a5; a6; a7; s1; s2; s3; s4; e1; e2] with ([a1; a2; a3; a4; a5; a6; a7] ++ [s1; s2; s3; s4] ++ [e1; e2]) in PNS0 end.
    apply num_rw_cells_app in PNS0. destruct PNS0 as [_ PNS0]. apply num_rw_cells_app in PNS0. destruct PNS0 as [SPANS _].
    cbn [cells_size csize Nat.add] in SPANS. replace (q_spq E + 72 + Z.of_nat 32)%Z with (q_spq E + 72 + 32)%Z in SPANS by lia.
    assert (ZRB : bytes_at bsegs mm ((f + 32) / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63)).
    { rewrite XD. destruct BSH as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
    replace (f + 528)%Z with (f + 32 + 496)%Z in LENC by lia.
    pose proof pmb_spec as HM. unfold pmb_stmt in HM.
    eapply evt_cut.
    { eapply evt_eq; [| eapply (HM E') with (bs := bs0) (jd := jd');
                        [exact OK1 | exact PV1 | exact BC | exact MI | unfold E'; cbn [p_sp p_lo p_m0]; rewrite USP; exact ST | exact LIMBS | exact XL0
                        | exact LENC | exact ZRB | exact JD | exact SPANS | exact SUBT]];
        unfold E'; cbn [p_ra p_sp p_gp p_tp p_s0 p_s1 p_s2 p_s3 p_s4 p_s5 p_s6 p_s7 p_s8 p_s9 p_s10 p_s11 p_F p_fc p_X p_N p_DG p_m0]; unfold B_PM; num_st_eq. }
    cbv beta. intros ms' P. unfold pmb_post_g in P.
    destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & bs4 & len4 & dg4 & -> & MUc & WMc & MIc & XA4 & XL4 & XN4 & LEN4 & DG4 & STc & EXP4).
    unfold E' in MUc, STc, XA4, XN4, DG4 |- *.
    cbn [p_ra p_sp p_gp p_tp p_s0 p_s1 p_s2 p_s3 p_s4 p_s5 p_s6 p_s7 p_s8 p_s9 p_s10 p_s11 p_F p_fc p_X p_N p_DG p_lo p_m0] in MUc, STc, XA4, XN4, DG4 |- *.
    rewrite USP in MUc, STc. unfold PMB_STACK in MUc.
    assert (MU4 : munch [(q_lo E, q_spq E + 152); (f, f + 8); (f + 32, f + 536); (q_S E + 4, q_S E + 67); (OUT, OUT + 8)]%Z (q_m0 E) m4).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. intros zz Hzz. cbn [outside] in *. lia. }
    assert (WM4 : wmono bsegs (q_m0 E) m4) by (eapply wmono_trans; eassumption).
    clear LIMBS LENC JD ST SPANS ZRB DGC SUBT MU WM.
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call bsegs mo mn MUc WMc end.
    clear MUc WMc MI HM. rename MIc into MI. rename STc into ST. num_ret_pc.
    replace (f + 32 + 496)%Z with (f + 528)%Z in XN4 by lia.
    assert (INVc : FCINVc E m4 c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL bs4 len4 dg4).
    { split; [unfold fcb_spill; eassumption|]. split; [do 4 eexists; unfold fcb_pns; eassumption|]. split; [lia|]. split; [lia|].
      split; [eassumption|]. split; [eexists; eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [lia|].
      split; [eexists; eassumption|]. split; [eassumption|]. split; [eexists; eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [unfold fcb_W; exact MU4|]. split; [exact WM4 | exact ST]. }
    eapply evt_eq; [| eapply (fcb_904 sci p2) with (bs := bs4) (len := len4) (dg := dg4)]; [num_st_eq | exact INVc | exact FRM | exact EXP4 | lia | lia].
  Qed.
End FCBDC.
