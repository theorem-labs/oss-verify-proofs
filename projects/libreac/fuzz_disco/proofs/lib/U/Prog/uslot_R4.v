From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_lib.
Import ListNotations.
Open Scope Z_scope.

Ltac brn := first [ if_true | if_false | (rewrite ?eqb_lit, ?ltu_lit by lia; first [ if_true | if_false ]) ].

Ltac r4_fin := apply evt_done; eexists; eexists; split; [reflexivity|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.

Lemma uR4_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spz now x y dt i : Z) (b0 : byte) (ji jn : list byte),
  sp = Z_to_bv 64 spz -> s0 = sxb b0 -> a0 = Z_to_bv 64 x -> a1 = Z_to_bv 64 y -> s1 = Z_to_bv 64 now ->
  t0 = Z_to_bv 64 i ->
  0 <= spz -> spz + 232 <= 2 ^ 64 -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> Z.lor y x = dt -> 0 <= dt < 65536 ->
  0 <= now < 2 ^ 64 -> 0 <= i < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (spz + 144)) 8 = Some (le8 (Z_to_bv 64 MS_NS)) ->
  rw_cells rsegs m (spz + 160) [CB 8 ji] -> rw_cells rsegs m (spz + 224) [CB 8 jn] -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (a1' : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_swrap 8 (bv_unsigned b0)))
                     (Z_to_bv 64 (now_step (bv_unsigned b0) dt now)) (Z_to_bv 64 3) a1' a2 a3 a4 a5 a6 a7
                     s2 s3 s4 (Z_to_bv 64 (bv_unsigned b0 mod 4)) s6 s7 s8 (Z_to_bv 64 (bv_unsigned b0)) s10 s11
                     t3 t4 t5 t6)
                F (Z_to_bv 64 (if bv_unsigned b0 mod 4 =? 3 then 0x135ac else 0x1367c)) fc None m' (seg_rom rsegs) /\
       munch [(spz + 160, spz + 168); (spz + 224, spz + 232)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (spz + 160) [C8 (Z_to_bv 64 i)] /\
       rw_cells rsegs m' (spz + 224) [C8 (Z_to_bv 64 (now_step (bv_unsigned b0) dt now))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1356c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spz now x y dt i b0 ji jn Esp Es0 Ea0 Ea1 Es1 Et0 Hsp0 Hsp1 Hx Hy Hdt Hdt1 Hnow Hi RMS C160 C224 MI.
  subst sp s0 a0 a1 s1 t0.
  pose proof (munch_refl [(spz + 160, spz + 168); (spz + 224, spz + 232)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step.
  rewrite (unsigned_lit y), (unsigned_lit x) by lia. rewrite Hdt.
  rewrite (unsigned_lit dt) by lia. rewrite (unsigned_lit MS_NS) by (unfold MS_NS; lia).
  step.
  rewrite sxb_lts0. pose proof (byte_range b0) as Hb0.
  assert (E3 : Z.land (bv_unsigned (sxb b0)) 3 = bv_unsigned b0 mod 4) by exact (sxb_land b0 2 ltac:(lia)).
  assert (E255 : Z.land (bv_unsigned (sxb b0)) 255 = bv_unsigned b0).
  { change 255 with (Z.ones 8). rewrite (sxb_land b0 8) by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia. }
  assert (Hd : 0 <= dt * MS_NS < 2 ^ 40) by (unfold MS_NS; lia).
  destruct (Z.leb_spec 128 (bv_unsigned b0)) as [Hneg|Hpos].
  - replace (128 <=? bv_unsigned b0) with true by (symmetry; apply Z.leb_le; lia). cbv iota.
    step.
    rewrite (unsigned_lit now), (unsigned_lit (dt * MS_NS)) by lia.
    step.
    rewrite sltu_sub by lia.
    destruct (Z.ltb_spec now (dt * MS_NS)) as [Hlt|Hge].
    + replace (now <? dt * MS_NS) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      step. step. rewrite Z.land_0_l.
      step. step. step. step. step. step.
      rewrite E3, E255, eqb_lit by lia.
      assert (EN : Z_to_bv 64 (now_step (bv_unsigned b0) dt now) = Z_to_bv 64 0).
      { unfold now_step. rewrite (proj2 (Z.ltb_ge (bv_unsigned b0) 128)) by lia.
        rewrite (proj2 (Z.ltb_lt now (dt * MS_NS))) by lia. reflexivity. }
      rewrite EN, <- sxb_swrap.
      destruct (Z.eqb_spec (bv_unsigned b0 mod 4) 3) as [Em|Em]; cbn [negb]; r4_fin.
    + replace (now <? dt * MS_NS) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      step. step. rewrite Z.land_comm, Z_to_bv_land64, Z_to_bv_lit_self.
      step. step. step. step. step. step.
      rewrite E3, E255, eqb_lit by lia.
      assert (EN : Z_to_bv 64 (now_step (bv_unsigned b0) dt now) = Z_to_bv 64 (now - dt * MS_NS)).
      { unfold now_step. rewrite (proj2 (Z.ltb_ge (bv_unsigned b0) 128)) by lia.
        rewrite (proj2 (Z.ltb_ge now (dt * MS_NS))) by lia. reflexivity. }
      rewrite EN, <- sxb_swrap.
      destruct (Z.eqb_spec (bv_unsigned b0 mod 4) 3) as [Em|Em]; cbn [negb]; r4_fin.
  - replace (128 <=? bv_unsigned b0) with false by (symmetry; apply Z.leb_gt; lia). cbv iota.
    step. step.
    step. step. step. step. step. step.
    rewrite E3, E255, eqb_lit by lia.
    assert (EN : Z_to_bv 64 (now_step (bv_unsigned b0) dt now) = Z_to_bv 64 (dt * MS_NS + now)).
    { unfold now_step. rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite Z_to_bv_mod64. f_equal. lia. }
    rewrite EN, <- sxb_swrap.
    destruct (Z.eqb_spec (bv_unsigned b0 mod 4) 3) as [Em|Em]; cbn [negb]; r4_fin.
Qed.

Lemma uslot_R4 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spz n p now i : Z) (Rm ji jn : list byte),
  sp = Z_to_bv 64 spz -> s5 = Z_to_bv 64 p -> s7 = Z_to_bv 64 n -> s1 = Z_to_bv 64 now -> t0 = Z_to_bv 64 i ->
  s11 = Z_to_bv 64 1 ->
  0 <= spz -> spz + 232 <= 2 ^ 64 -> 1 <= n -> Z.of_nat (length Rm) = n -> 0 < p -> p + n < 2 ^ 64 ->
  0 <= now < 2 ^ 64 -> 0 <= i < 2 ^ 64 ->
  bytes_at rsegs m p Rm ->
  ov_read_bytes rsegs m (wa (spz + 144)) 8 = Some (le8 (Z_to_bv 64 MS_NS)) ->
  rw_cells rsegs m (spz + 160) [CB 8 ji] -> rw_cells rsegs m (spz + 224) [CB 8 jn] -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (a1' : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_swrap 8 (rdb Rm 0)))
                     (Z_to_bv 64 (now_step (rdb Rm 0) (dt_of Rm) now)) (Z_to_bv 64 3) a1' a2 a3 a4 a5 a6 a7
                     s2 s3 s4 (Z_to_bv 64 (rdb Rm 0 mod 4)) (Z_to_bv 64 (p + op_take n)) (Z_to_bv 64 (n - op_take n))
                     s8 (Z_to_bv 64 (rdb Rm 0)) s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (if rdb Rm 0 mod 4 =? 3 then 0x135ac else 0x1367c)) fc None m' (seg_rom rsegs) /\
       munch [(spz + 160, spz + 168); (spz + 224, spz + 232)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (spz + 160) [C8 (Z_to_bv 64 i)] /\
       rw_cells rsegs m' (spz + 224) [C8 (Z_to_bv 64 (now_step (rdb Rm 0) (dt_of Rm) now))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 HDR) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spz n p now i Rm ji jn Esp Es5 Es7 Es1 Et0 Es11 Hsp0 Hsp1 Hn HL Hp0 Hpn Hnow Hi HB RMS C160 C224 MI.
  subst sp s5 s7 s1 t0 s11. unfold HDR.
  assert (R0 : ov_read_bytes rsegs m (wa p) 1 = Some [nth 0 Rm (Z_to_bv 8 0)]).
  { replace (wa p) with (wa (p + Z.of_nat 0)) by (f_equal; lia). apply read1; [exact HB | lia]. }
  pose proof (bytes_at_bound rsegs m p Rm HB) as HBp.
  pose proof (byte_range (nth 1 Rm (Z_to_bv 8 0))) as Hr1.
  pose proof (byte_range (nth 2 Rm (Z_to_bv 8 0))) as Hr2.
  assert (Hdt : 0 <= dt_of Rm < 65536) by (unfold dt_of, rdb; lia).
  destruct (Z.eq_dec n 1) as [E1|N1]; [|destruct (Z.eq_dec n 2) as [E2|N2]].
  - rewrite E1 in *. step. step. brn. step. step. rewrite eqb_lit by lia. cbn [Z.eqb Pos.eqb negb].
    step. step. step. step. step.
    assert (D : dt_of Rm = 0).
    { unfold dt_of, rdb. rewrite !nth_past by lia. reflexivity. }
    eapply evt_mono.
    + apply (uR4_tail ra (Z_to_bv 64 spz) gp tp (Z_to_bv 64 i) t1 t2 (sxb (nth 0 Rm (Z_to_bv 8 0))) (Z_to_bv 64 now)
        (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
        s2 s3 s4 (Z_to_bv 64 p) (Z_to_bv 64 (p + 1)) (Z_to_bv 64 0) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6
        F fc m spz now 0 0 (dt_of Rm) i (nth 0 Rm (Z_to_bv 8 0)) ji jn);
        try reflexivity; try lia; try assumption. rewrite D. reflexivity.
    + intros ms' (a1' & m' & E & R). subst ms'. exists a1', m'. split; [reflexivity | exact R].
  - rewrite E2 in *. step. step. brn. step. step. rewrite eqb_lit by lia. cbn [Z.eqb Pos.eqb negb].
    assert (R1 : ov_read_bytes rsegs m (wa (p + 1)) 1 = Some [nth 1 Rm (Z_to_bv 8 0)]).
    { apply (read1 m p Rm 1 HB). lia. }
    step. step. brn. step. step. step. step. rewrite eqb_lit by lia. cbn [Z.eqb Pos.eqb negb].
    step. step. step.
    assert (D : dt_of Rm = rdb Rm 1).
    { unfold dt_of, rdb. rewrite (nth_past Rm 2) by lia. lia. }
    eapply evt_mono.
    + apply (uR4_tail ra (Z_to_bv 64 spz) gp tp (Z_to_bv 64 i) t1 t2 (sxb (nth 0 Rm (Z_to_bv 8 0))) (Z_to_bv 64 now)
        (zxb (nth 1 Rm (Z_to_bv 8 0))) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
        s2 s3 s4 (Z_to_bv 64 p) (Z_to_bv 64 (p + 2)) (Z_to_bv 64 0) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6
        F fc m spz now (rdb Rm 1) 0 (dt_of Rm) i (nth 0 Rm (Z_to_bv 8 0)) ji jn);
        try reflexivity; try (unfold rdb; lia); try assumption. rewrite D. reflexivity.
    + intros ms' (a1' & m' & E & R). subst ms'. exists a1', m'. split; [reflexivity | exact R].
  - step. step. brn. step. step. rewrite eqb_lit by lia.
    replace (n =? 1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    assert (R1 : ov_read_bytes rsegs m (wa (p + 1)) 1 = Some [nth 1 Rm (Z_to_bv 8 0)]).
    { apply (read1 m p Rm 1 HB). lia. }
    assert (R2 : ov_read_bytes rsegs m (wa (p + 2)) 1 = Some [nth 2 Rm (Z_to_bv 8 0)]).
    { apply (read1 m p Rm 2 HB). lia. }
    step. step. brn. step. step. step. step. rewrite eqb_lit by lia.
    replace (n =? 2) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    step. step. brn. step. step. step. step.
    assert (OT : op_take n = 3) by (unfold op_take; lia). rewrite OT.
    assert (U2 : bv_unsigned (zxb (nth 2 Rm (Z_to_bv 8 0))) = rdb Rm 2) by (unfold zxb, rdb; apply unsigned_lit; lia).
    assert (Y : Z.lor (Z.shiftl (bv_unsigned (zxb (nth 2 Rm (Z_to_bv 8 0)))) 8) (rdb Rm 1) = dt_of Rm).
    { rewrite U2. unfold dt_of. apply lor_byte_shift; unfold rdb; lia. }
    assert (YR : 0 <= Z.shiftl (bv_unsigned (zxb (nth 2 Rm (Z_to_bv 8 0)))) 8 < 2 ^ 64).
    { rewrite U2, Z.shiftl_mul_pow2 by lia. unfold rdb. lia. }
    eapply evt_mono.
    + apply (uR4_tail ra (Z_to_bv 64 spz) gp tp (Z_to_bv 64 i) t1 t2 (sxb (nth 0 Rm (Z_to_bv 8 0))) (Z_to_bv 64 now)
        (zxb (nth 1 Rm (Z_to_bv 8 0))) (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth 2 Rm (Z_to_bv 8 0)))) 8))
        a2 a3 a4 a5 a6 a7
        s2 s3 s4 (Z_to_bv 64 p) (Z_to_bv 64 (p + 3)) (Z_to_bv 64 (n + -3)) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6
        F fc m spz now (rdb Rm 1) (Z.shiftl (bv_unsigned (zxb (nth 2 Rm (Z_to_bv 8 0)))) 8) (dt_of Rm) i
        (nth 0 Rm (Z_to_bv 8 0)) ji jn);
        try reflexivity; try (unfold rdb; lia); try assumption.
    + intros ms' (a1' & m' & E & R). subst ms'. exists a1', m'. split; [reflexivity | exact R].
Qed.
