From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase AF_huf_x2t_bgeo AF_huf_x2t_bdefs.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma x2e_r1_nth : forall ws A bs a i, (i < length bs)%nat ->
  nth_error (replay1 A bs a ws) i =
    if (Z.leb a (A + Z.of_nat i) && Z.ltb (A + Z.of_nat i) (a + Z.of_nat (length ws)))%bool
    then nth_error ws (Z.to_nat (A + Z.of_nat i - a)) else nth_error bs i.
Proof.
  induction ws as [|b ws IH]; intros A bs a i Hi.
  - cbn [replay1 length]. destruct (Z.leb_spec a (A + Z.of_nat i)); destruct (Z.ltb_spec (A + Z.of_nat i) (a + Z.of_nat 0));
      cbn [andb]; first [reflexivity | lia].
  - cbn [replay1 length].
    assert (LB : Nat.lt i (length (if (Z.leb A a && Z.ltb a (A + Z.of_nat (length bs)))%bool
                              then upd_bytes bs (Z.to_nat (a - A)) [b] else bs))).
    { destruct (Z.leb_spec A a); destruct (Z.ltb_spec a (A + Z.of_nat (length bs))); cbn [andb]; try exact Hi.
      rewrite upd_bytes_length; cbn [length]; lia. }
    rewrite (IH A _ (a + 1) i LB). clear LB IH.
    destruct (Z.leb_spec A a); destruct (Z.ltb_spec a (A + Z.of_nat (length bs)));
    destruct (Z.leb_spec (a + 1) (A + Z.of_nat i)); destruct (Z.ltb_spec (A + Z.of_nat i) (a + 1 + Z.of_nat (length ws)));
    destruct (Z.leb_spec a (A + Z.of_nat i)); destruct (Z.ltb_spec (A + Z.of_nat i) (a + Z.of_nat (S (length ws))));
    cbn [andb]; try lia;
    try (rewrite upd_bytes_nth by (cbn [length]; lia);
         destruct (Nat.leb_spec (Z.to_nat (a - A)) i); destruct (Nat.ltb_spec i (Z.to_nat (a - A) + length [b]));
         cbn [andb length] in *; try lia);
    first [ reflexivity
          | replace (Z.to_nat (A + Z.of_nat i - a)) with (S (Z.to_nat (A + Z.of_nat i - (a + 1)))) by lia; reflexivity
          | replace (Z.to_nat (A + Z.of_nat i - a)) with O by lia; replace (i - Z.to_nat (a - A))%nat with O by lia; reflexivity ].
Qed.

Lemma x2e_r1_in : forall ws A bs a j, 0 <= j -> A <= a -> a + Z.of_nat (length ws) <= A + Z.of_nat (length bs) ->
  a <= A + j < a + Z.of_nat (length ws) ->
  nth_error (replay1 A bs a ws) (Z.to_nat j) = nth_error ws (Z.to_nat (A + j - a)).
Proof.
  intros ws A bs a j H0 H1 H2 H3. rewrite x2e_r1_nth by lia. rewrite Z2Nat.id by lia.
  destruct (Z.leb_spec a (A + j)); destruct (Z.ltb_spec (A + j) (a + Z.of_nat (length ws))); cbn [andb]; first [reflexivity | lia].
Qed.

Lemma x2e_r1_out : forall ws A bs a j, 0 <= j < Z.of_nat (length bs) -> (A + j < a \/ a + Z.of_nat (length ws) <= A + j) ->
  nth_error (replay1 A bs a ws) (Z.to_nat j) = nth_error bs (Z.to_nat j).
Proof.
  intros ws A bs a j H0 H1. rewrite x2e_r1_nth by lia. rewrite Z2Nat.id by lia.
  destruct (Z.leb_spec a (A + j)); destruct (Z.ltb_spec (A + j) (a + Z.of_nat (length ws))); cbn [andb]; first [reflexivity | lia].
Qed.

Lemma x2e_znth_map : forall (bs : list byte) i b, nth_error bs (Z.to_nat i) = Some b ->
  Znth i (map bv_unsigned bs) = bv_unsigned b.
Proof.
  intros bs i b H. unfold Znth. apply nth_error_nth. rewrite nth_error_map, H. reflexivity.
Qed.

Lemma x2e_znth_old : forall (dt : list Z) i, 0 <= i < zlen dt -> Forall isbyte dt ->
  nth_error (map (Z_to_bv 8) dt) (Z.to_nat i) = Some (Z_to_bv 8 (Znth i dt)) /\ 0 <= Znth i dt < 256.
Proof.
  intros dt i Hi HB. unfold Znth. rewrite nth_error_map.
  rewrite (nth_error_nth' dt 0) by lia. split; [reflexivity|].
  apply (proj1 (Forall_forall _ dt) HB). apply nth_In. lia.
Qed.

Lemma x2e_bv8 : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. reflexivity. Qed.

Lemma x2e_dt_of : forall (bs : list byte), map (Z_to_bv 8) (map bv_unsigned bs) = bs /\ Forall isbyte (map bv_unsigned bs).
Proof.
  intros bs. split.
  - rewrite map_map. rewrite (map_ext _ (fun b => b)); [apply map_id|].
    intros b. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. apply bv_unsigned_in_range.
  - apply Forall_map, Forall_forall. intros b _. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Ltac x2e_ez :=
  lazymatch goal with
  | |- context [edenot ?E _] =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite ?(ez_ok zv E (kE_atoms zv xs));
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
      end
  end.

Ltac x2e_ezt X :=
  lazymatch goal with |- context [edenot ?E X] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      rewrite (ez_ok zv E (kE_atoms zv xs) X);
      let na := eval vm_compute in (length zv) in
      cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
    end
  end.

Lemma x2e_land257 : forall S, 0 <= S < 2^64 -> (S / 256) mod 2 = 0 -> Z.land S ((-257) mod 2^64) = S.
Proof.
  intros S HS HB. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  destruct (Z.ltb_spec n 64) as [L|L].
  - rewrite Z.mod_pow2_bits_low by lia. change (-257) with (Z.lnot (2^8)). rewrite Z.lnot_spec by lia.
    destruct (Z.eq_dec n 8) as [E|E].
    + subst n. rewrite Z.pow2_bits_true by lia.
      assert (TB : Z.testbit S 8 = false) by (apply (proj2 (Z.testbit_false S 8 ltac:(lia))); change (2^8) with 256; exact HB).
      rewrite TB. reflexivity.
    + rewrite Z.pow2_bits_false by lia. apply Bool.andb_true_r.
  - assert (TS : Z.testbit S n = false).
    { apply (proj2 (Z.testbit_false S n ltac:(lia))). rewrite Z.div_small; [reflexivity|].
      split; [lia|]. apply (Z.lt_le_trans _ (2^64)); [lia | apply Z.pow_le_mono_r; lia]. }
    rewrite TS. reflexivity.
Qed.

Lemma x2e_hd : forall (dt : list Z) DT (ws : list byte) k, length ws = 4%nat -> 4 <= zlen dt -> 0 <= k < 4 ->
  Znth k (map bv_unsigned (replay1 DT (map (Z_to_bv 8) dt) DT ws)) = Znth k (map bv_unsigned ws).
Proof.
  intros dt DT ws k LW LD Hk.
  destruct (nth_error ws (Z.to_nat k)) as [b|] eqn:NB.
  - rewrite (x2e_znth_map _ k b).
    + rewrite (x2e_znth_map ws k b NB). reflexivity.
    + rewrite x2e_r1_in by (rewrite ?length_map, ?LW; lia). replace (Z.to_nat (DT + k - DT)) with (Z.to_nat k) by (f_equal; lia). exact NB.
  - apply nth_error_None in NB. lia.
Qed.

Lemma x2e_rest : forall (dt : list Z) DT (ws : list byte) i, length ws = 4%nat -> 4 <= zlen dt -> Forall isbyte dt -> 4 <= i ->
  Znth i (map bv_unsigned (replay1 DT (map (Z_to_bv 8) dt) DT ws)) = Znth i dt.
Proof.
  intros dt DT ws i LW LD BY Hi.
  destruct (Z_lt_le_dec i (zlen dt)) as [Lt|Ge].
  - destruct (x2e_znth_old dt i ltac:(lia) BY) as [NO RO].
    rewrite (x2e_znth_map _ i (Z_to_bv 8 (Znth i dt))).
    + rewrite x2e_bv8. apply Z.mod_small. lia.
    + rewrite x2e_r1_out by (rewrite ?length_map, ?LW; lia). exact NO.
  - unfold Znth. rewrite !nth_overflow; try reflexivity; rewrite ?length_map, ?replay1_length, ?length_map; lia.
Qed.

Lemma x2e_wtlb4 : forall V, 0 <= V < 2^64 ->
  Znth 0 (map bv_unsigned (word_to_le_bytes 4 (Z_to_bv 64 V))) = V mod 256
  /\ Znth 1 (map bv_unsigned (word_to_le_bytes 4 (Z_to_bv 64 V))) = (V / 256) mod 256
  /\ Znth 2 (map bv_unsigned (word_to_le_bytes 4 (Z_to_bv 64 V))) = (V / 65536) mod 256
  /\ Znth 3 (map bv_unsigned (word_to_le_bytes 4 (Z_to_bv 64 V))) = (V / 16777216) mod 256.
Proof.
  intros V HV. unfold word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite (Z.mod_small V) by lia. cbn [Z_to_le_bytes map]. unfold Znth.
  change (Z.to_nat 0) with 0%nat. change (Z.to_nat 1) with 1%nat. change (Z.to_nat 2) with 2%nat. change (Z.to_nat 3) with 3%nat.
  cbn [nth]. rewrite !x2e_bv8. rewrite ?Z.shiftr_div_pow2 by lia. rewrite ?Z.div_div by lia.
  repeat split; reflexivity.
Qed.

Definition X2EHide (P : Prop) : Prop := P.

Section CANSEC1. Context {rc : runConstT}.

Lemma x2e_sh0 : forall (m : word -> option byte) lo hi P, unpoisoned m lo hi -> lo <= P < hi -> 8 * (P / 8) + 8 <= hi ->
  forall s, Z.shiftr P 3 + ASHOFF <= s < Z.shiftr P 3 + ASHOFF + 1 -> m (wa s) = Some (Z_to_bv 8 0).
Proof.
  intros m lo hi P (L0 & H64 & U) HP H8 s Hs.
  rewrite Z.shiftr_div_pow2 in Hs by lia. change (2 ^ 3) with 8 in Hs.
  assert (ES : s = ASHOFF + P / 8) by lia. subst s.
  destruct (U (P / 8)) as (b & RB & GB); [lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia |].
  rewrite RB. f_equal. apply (gran_ok_full _ _ GB). rewrite Z.min_l by lia. lia.
Qed.

Definition x2_exitB_stmt : Prop := forall (RNG : footprint) (POST : machine_state -> Prop) (F : bvmap 5 word) (fc : bv 32) (m5 m1 : amem)
    (SPV SPA lo DT WK wksz FF mtl nbs b0 b3 T r : Z) (hw rank dt rs0 rv : list Z) (syb : list byte)
    (k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k208 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392 : word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  x2B_hyps RNG SPV SPA lo DT WK wksz FF mtl ->
  unpoisoned m5 DT (DT + 4 * (1 + 2 ^ mtl)) ->
  zlen hw <= 256 -> zlen rank <= 13 ->
  k0 = Z_to_bv 64 (16777216 * b3) -> k8 = Z_to_bv 64 b0 -> k16 = Z_to_bv 64 r -> k368 = Z_to_bv 64 T ->
  0 <= b0 <= 255 -> 0 <= b3 <= 255 -> 0 <= T <= 255 -> 0 <= r < 2^64 ->
  XBB m5 SPV SPA lo DT WK wksz FF mtl nbs hw rank k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k208 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392 dt rs0 syb rv m1 ->
  (forall (m2 : amem) (dt' : list Z) (y11 y12 : word),
     XBB m5 SPV SPA lo DT WK wksz FF mtl nbs hw rank k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k208 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392 dt' rs0 syb rv m2 ->
     Znth 0 dt' = b0 -> Znth 1 dt' = 1 -> Znth 2 dt' = T -> Znth 3 dt' = b3 ->
     (forall i, 4 <= i -> Znth i dt' = Znth i dt) ->
     evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 SPA) (Z_to_bv 64 r) y11 y12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (X2B_ENTRY + 3732)) fc None m2 (seg_rom bsegs))) ->
  evtF bsegs RNG POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 SPA) (Z_to_bv 64 DT) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (X2B_ENTRY + 3684)) fc None m1 (seg_rom bsegs)).

Lemma x2_exitB : x2_exitB_stmt.
Proof.
  unfold x2_exitB_stmt. intros RNG POST F fc m5 m1 SPV SPA lo DT WK wksz FF mtl nbs b0 b3 T r hw rank dt rs0 rv syb k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k208 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392 x1 x2 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         HY UDT LHW LRK E0 E8 E16 E368 HB0 HB3 HT HR I KC.
  pose proof HY as HY'. open_hx2b HY'. open_xbb I. subst k0 k8 k16 k368.
  assert (P2 : 2 <= 2 ^ mtl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  assert (UDT1 : unpoisoned m1 DT (DT + 4 * (1 + 2 ^ mtl))).
  { eapply unpoisoned_munch; [exact UDT | exact MU |].
    clear - P2 ATR ABD ABW KLO LOS SPAB SPT DTL DTH WKL WKH WR MTL.
    unfold ablk, AIMG_HI, KLS in ABD, ABW. unfold KHIGH in KLO.
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. repeat split; Z.div_mod_to_equations; lia. }
  pose proof (x2e_sh0 m1 DT (DT + 4 * (1 + 2 ^ mtl)) DT UDT1 ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as SH0.
  assert (QR : 512 <= Z.shiftr DT 3 <= 2^44) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  assert (RSH : rng RNG (Z.shiftr DT 3 + ASHOFF) 1).
  { eapply rng_sub; [exact RSDT | |]; rewrite ?shad_div, ?nshad_div, Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia. }
  assert (RSPA : rng RNG SPA 408) by (eapply rng_sub; [exact RSTK | lia | lia]).
  assert (RDT4 : rng RNG DT 4) by (eapply rng_sub; [exact RDT | lia | lia]).
  change (X2B_ENTRY + 3684) with 535724.
  unfold ASHOFF in SH0, RSH.
  change (u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw)) with (X2EHide (u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw))) in HWC.
  change (u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank)) with (X2EHide (u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank))) in RK.
  change (u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0)) with (X2EHide (u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0))) in RS0.
  change (u8arr bsegs m1 (WK + 736) syb) with (X2EHide (u8arr bsegs m1 (WK + 736) syb)) in SYC.
  change (u32arr bsegs m1 WK (map (Z_to_bv 64) rv)) with (X2EHide (u32arr bsegs m1 WK (map (Z_to_bv 64) rv))) in RV.
  change (rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)]) with (X2EHide (rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)])) in NBC.
  let c := eval unfold ASHOFF in ASHOFF in
  kx_runFm [535772] 40%nat
    [KZRange SPA (KHIGH + 5408) (2^47 - 528); KZRange DT 4096 (2^47 - 8); KZRange (Z.shiftr DT 3) 512 (2^44);
     KZRange b0 0 255; KZRange b3 0 255; KZRange T 0 255; KZRange r 0 (2^64 - 1);
     KZWord (SPA + 128) 8 (Z.shiftr DT 3 + c); KZWord (SPA + 368) 8 T; KZWord SPA 8 (16777216 * b3);
     KZWord (SPA + 8) 8 b0; KZWord (SPA + 16) 8 r; KZZero (Z.shiftr DT 3 + c) 1; KZWr DT 4; KZDisj (SPA + 16) 8 DT 4]
    [] [(DT, 4); (SPA, 408); (Z.shiftr DT 3 + c, 1)] [].
  all: try (unfold KHIGH; lia).
  kx_post_regs.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E m1 ?lg) _) =>
    lazymatch lg with [SE ?a1 ?w1 ?v1] =>
      assert (EA1 : estart E a1 = DT) by (unfold estart; cbn [a_base a_off]; x2e_ez; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; lia);
      assert (EV1 : edenot E v1 = Z_to_bv 64 (b0 + 256 + 65536 * T + 16777216 * b3))
    end end.
  { x2e_ez.
    lazymatch goal with |- context [edenot ?E' (EAlu ALU_AND ?X ?Y)] =>
      change (edenot E' (EAlu ALU_AND X Y)) with (alu64 ALU_AND (edenot E' X) (edenot E' Y)); rewrite u_and64;
      x2e_ezt X; x2e_ezt Y end.
    f_equal. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
    lazymatch goal with |- context [Z.land (?S mod 2 ^ 64) _] => rewrite (Z.mod_small S) by lia end.
    rewrite x2e_land257 by (first [lia | Z.div_mod_to_equations; lia]).
    lia. }
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E m1 ?lg) _) =>
      unfold X2EHide in HWC, RK, RS0, SYC, RV, NBC;
      pose proof (kx_u8arr_replay bsegs E m1 lg DT _ DTC KXLF) as DTC';
      pose proof (kx_rw_cells_log bsegs E m1 lg _ _ FR KXLF) as FR';
      pose proof (kx_rw_cells_log bsegs E m1 lg _ _ NBC KXLF) as NBC';
      pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 HWC) KXLF) as HWC1;
      pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 RK) KXLF) as RK1;
      pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 RS0) KXLF) as RS01;
      pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 SYC) KXLF) as SYC1;
      pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 RV) KXLF) as RV1;
      pose proof (kx_wr_at_log bsegs E m1 lg _ _ (proj2 HWC)) as HWC2;
      pose proof (kx_wr_at_log bsegs E m1 lg _ _ (proj2 RK)) as RK2;
      pose proof (kx_wr_at_log bsegs E m1 lg _ _ (proj2 RS0)) as RS02;
      pose proof (kx_wr_at_log bsegs E m1 lg _ _ (proj2 SYC)) as SYC2;
      pose proof (kx_wr_at_log bsegs E m1 lg _ _ (proj2 RV)) as RV2;
      pose proof (kx_stk_log bsegs E m1 lg _ _ WKR) as WKR';
      pose proof (kx_stk_log bsegs E m1 lg _ _ STK) as STK';
      pose proof (kx_mem_inv_log bsegs E m1 lg MI KXLF) as MI';
      pose proof (kx_munch_log E _ m5 m1 lg MU KXLF) as MU';
      pose proof (kx_wmono_log bsegs E m5 m1 lg WM) as WM';
      cbn [log_apart log_inside log_wr] in FR', NBC', HWC1, RK1, RS01, SYC1, RV1, MI', MU';
      rewrite ?EA1 in FR', NBC', HWC1, RK1, RS01, SYC1, RV1, MI', MU';
      cbn [replay] in DTC'; rewrite EA1, EV1 in DTC'
  end.
  change (Z.of_nat 4) with 4 in FR', NBC', HWC1, RK1, RS01, SYC1, RV1, MI', MU'.
  assert (LHWm : zlen (map (Z_to_bv 8) hw) <= 256) by (rewrite length_map; lia).
  assert (LRKm : Z.of_nat (length (u32s (map (Z_to_bv 64) rank))) <= 52) by (rewrite u32s_length, length_map; lia).
  assert (LRSm : Z.of_nat (length (u32s (map (Z_to_bv 64) rs0))) = 60) by (rewrite u32s_length, length_map; lia).
  assert (LRVm : Z.of_nat (length (u32s (map (Z_to_bv 64) rv))) = 624) by (rewrite u32s_length, length_map; lia).
  specialize (FR' ltac:(cbn [cells_size csize Nat.add length]; repeat split; lia)).
  specialize (NBC' ltac:(cbn [cells_size csize Nat.add length]; repeat split; lia)).
  specialize (HWC1 ltac:(repeat split; lia)).
  specialize (RK1 ltac:(repeat split; lia)).
  specialize (RS01 ltac:(repeat split; lia)).
  specialize (SYC1 ltac:(repeat split; lia)).
  specialize (RV1 ltac:(repeat split; lia)).
  specialize (MI' ltac:(split; [|exact Logic.I]; intros j Hj; apply (proj2 (proj2 (proj2 DTC))); rewrite length_map; lia)).
  specialize (MU' ltac:(split; [cbn [inside]; left; lia | exact Logic.I])).
  lazymatch type of DTC' with u8arr _ _ _ ?b1 => set (bs1 := b1) in DTC' end.
  destruct (x2e_dt_of bs1) as [DTE DTBY']. rewrite <- DTE in DTC'.
  assert (LB1 : zlen (map bv_unsigned bs1) = 4 * (1 + 2 ^ mtl))
    by (unfold bs1; rewrite length_map, replay1_length, length_map; exact DTLEN).
  destruct (x2e_wtlb4 (b0 + 256 + 65536 * T + 16777216 * b3) ltac:(lia)) as (W0 & W1 & W2 & W3).
  assert (LW4 : length (word_to_le_bytes 4 (Z_to_bv 64 (b0 + 256 + 65536 * T + 16777216 * b3))) = 4%nat) by apply length_wtlb.
  assert (LD4 : 4 <= zlen dt) by lia.
  change (Z_to_bv 64 535772) with (Z_to_bv 64 (X2B_ENTRY + 3732)).
  eapply KC.
  - eapply XBB_close; [exact DTC' | exact LB1 | exact DTBY' | exact (conj HWC1 HWC2) | exact (conj RK1 RK2) | exact (conj RS01 RS02)
      | exact RS0LEN | exact RS0NN | exact (conj SYC1 SYC2) | exact SYLEN | exact (conj RV1 RV2) | exact RVLEN | exact RVNN
      | exact WKR' | exact NBC' | exact STK' | exact MI' | exact MU' | exact WM' | exact FR'].
  - unfold bs1. rewrite (x2e_hd dt DT _ 0 LW4 LD4) by lia. rewrite W0. Z.div_mod_to_equations. lia.
  - unfold bs1. rewrite (x2e_hd dt DT _ 1 LW4 LD4) by lia. rewrite W1. Z.div_mod_to_equations. lia.
  - unfold bs1. rewrite (x2e_hd dt DT _ 2 LW4 LD4) by lia. rewrite W2. Z.div_mod_to_equations. lia.
  - unfold bs1. rewrite (x2e_hd dt DT _ 3 LW4 LD4) by lia. rewrite W3. Z.div_mod_to_equations. lia.
  - intros i Hi. unfold bs1. exact (x2e_rest dt DT _ i LW4 LD4 DTBY Hi).
Qed.

End CANSEC1.
