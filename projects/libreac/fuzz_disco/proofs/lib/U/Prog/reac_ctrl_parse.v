From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcKind RcKindLib RcLib RcParse RcParseLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_ctrl_parse_c memset_c memcpy_c bcmp_c kind_of_link1_c.
Import ListNotations.
Open Scope Z_scope.

Ltac mem_after_store_opt ::=
  try rewrite rc_le1_zxb;
  try fix_lit_store;
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Lemma rc_land3 : forall x, x mod 4 = 0 -> 0 <= x < 2^64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 x)) 3) = Z_to_bv 64 0.
Proof.
  intros x H R. rewrite unsigned_lit by lia. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
  change (2^2) with 4. rewrite H. reflexivity.
Qed.

Ltac ub_false :=
  rc_wrap_lits;
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false;
      [ cbv iota
      | symmetry; unfold bv_eqb, bv_ltu; rewrite ?unsigned_lit by lia; cbn [negb];
        first [ reflexivity | apply Z.eqb_neq; lia | apply Z.ltb_ge; lia | apply negb_false_iff, Z.ltb_lt; lia ] ]
  end.

Section P.
Hypothesis MSET : memset_contract.
Hypothesis MCPY : memcpy_contract.
Hypothesis BCMP : bcmp_contract.
Hypothesis KOL : kind_of_link1_contract.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Ff : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (f n o S o' : Z) (fr : list byte).
Hypothesis Hf : 0 <= f < 2^64.
Hypothesis Hn : 0 <= n < 2^64.
Hypothesis Ho : 0 <= o < 2^64.
Hypothesis HS : 80 <= S < 2^64.
Hypothesis HO : (o = 0 /\ o' = S - 76) \/ (o <> 0 /\ o' = o).
Hypothesis Ho'r : 0 < o' /\ o' + 36 <= 2^64.
Hypothesis Ho'4 : o' mod 4 = 0.
Hypothesis Ho'S : o' + 36 <= S - 40 \/ S <= o'.
Hypothesis Hfr : length fr = 50%nat.
Hypothesis HF : 50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= S - 80 \/ S <= f) /\ (o' + 36 <= f \/ f + 50 <= o').
Hypothesis Hrd : forall i, In i (cp_rd n fr) -> mrd rsegs m0 (wa (f + Z.of_nat i)) = nth_error fr i.

Ltac rdb lo len tac :=
  let HIN := fresh "HIN" in
  assert (HIN : forall j, (j < len)%nat -> In (lo + j)%nat (cp_rd n fr)) by tac;
  lazymatch goal with MU : munch ?W m0 ?m |- _ =>
    let R := fresh "RO" in
    pose proof (rc_ro_now rsegs W m0 m f fr lo len (cp_rd n fr) Hrd HIN ltac:(lia) ltac:(lia) ltac:(lia) MU
                  ltac:(cbn [disjoint_from]; repeat split; lia)) as R;
    cbn [map seq] in R;
    let z := eval vm_compute in (Z.of_nat lo) in change (Z.of_nat lo) with z in R;
    rewrite ?Z.add_0_r in R
  end;
  clear HIN.

Definition Qp : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse n fr)))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             Ff (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch (reac_ctrl_parse_fp o S) m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\
    (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]).

Lemma L_epi : forall (rr t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 : word) m k B,
  munch [(o', o' + 36); (S - 80, S)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m (S - 80) S ->
  rw_cells rsegs m (S + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m o' [CB 36 B] -> fst (ctrlparse n fr) = k -> snd (ctrlparse n fr) = B ->
  evt rsegs Qp
    (MS (mkR rr (Z_to_bv 64 (S + -80)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7 x18 x19
             s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Ff (Z_to_bv 64 0x1625c) fc None m (seg_rom rsegs)).
Proof.
  intros rr t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 m k B MU WM MI ST HR HB Ek EB.
  do 7 step.
  apply evt_done. unfold Qp. rewrite Ek.
  do 15 eexists. split; [reflexivity|].
  split; [|split; [exact WM|split; [exact MI|split]]].
  - eapply munch_weaken; [|exact MU]. unfold sub_fp, reac_ctrl_parse_fp, REAC_CTRL_PARSE_K. intros x.
    destruct HO as [[Hz Ho']|[Hz Ho']].
    + rewrite Hz. cbn [Z.eqb app outside]. lia.
    + rewrite (proj2 (Z.eqb_neq o 0) Hz). cbn [app outside]. lia.
  - unfold REAC_CTRL_PARSE_K. exact ST.
  - intros Hz. destruct HO as [[Hz' _]|[_ Ho']]; [lia|]. rewrite EB, <- Ho'. exact HB.
Qed.

Definition P1 : list byte :=
  [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11;
   cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5;
   (if cp_bcast fr then Z_to_bv 8 1 else cp_z); cp_z; cp_z; cp_z;
   cp_b fr 14; cp_b fr 15; cp_b fr 18; cp_b fr 19; cp_b fr 21; cp_b fr 20; cp_b fr 22; cp_z].

Lemma L_kind : forall (rr t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) m k tg,
  munch [(o', o' + 36); (S - 80, S)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m (S - 80) S ->
  rw_cells rsegs m (S + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m o' [CB 4 (repeat cp_z 4)] -> rw_cells rsegs m (o' + 4) [CB 24 P1] ->
  rw_cells rsegs m (o' + 28) [CB 2 tg] -> rw_cells rsegs m (o' + 30) [CB 6 (repeat cp_z 6)] ->
  fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
  snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ repeat cp_z 6 ->
  evt rsegs Qp
    (MS (mkR rr (Z_to_bv 64 (S + -80)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 o') x19
             s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Ff (Z_to_bv 64 0x162dc) fc None m (seg_rom rsegs)).
Proof.
  intros rr t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 m k tg MU WM MI ST HR HK HT HG HA Ek Hk EB.
  step. step.
  match goal with H : rw_cells rsegs ?mm o' [C4 _] |- _ => rename H into HK' end.
  pose proof (rc_rw_join rsegs _ o' (o' + 4) _ _ HK' ltac:(cbn [cells_size csize app]; lia) HT) as J1.
  pose proof (rc_rw_join rsegs _ o' (o' + 28) _ _ J1 ltac:(cbn [cells_size csize app]; lia) HG) as J2.
  pose proof (rc_rw_join rsegs _ o' (o' + 30) _ _ J2 ltac:(cbn [cells_size csize app]; lia) HA) as J3.
  apply (rc_rw_flat rsegs _ o' _ (snd (ctrlparse n fr))) in J3.
  - rewrite ctrlparse_length in J3. eapply L_epi; first [eassumption | reflexivity].
  - rewrite EB. cbn [app cells_bytes cbytes]. rewrite rc_le4_small by lia. rewrite !app_nil_r. cbn [app]. reflexivity.
Qed.

Ltac cond_norm :=
  rewrite ?rc_lor0;
  rewrite ?rc_eqb_zxb by zlitr;
  repeat match goal with
  | |- context [bv_unsigned (cp_b fr ?i)] => change (bv_unsigned (cp_b fr i)) with (cp_v fr i)
  end.

Ltac br :=
  cond_norm;
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if negb (?x =? ?y) then _ else _) _ _ _ _) => zdec x y
  | |- evt _ _ (MS _ _ (if (?x =? ?y) then _ else _) _ _ _ _) => zdec x y
  end.

Ltac drive :=
  repeat (lazymatch goal with
          | |- evt _ Qp (MS _ _ (Z_to_bv 64 0x162dc) _ _ _ _) => fail
          | |- evt _ Qp (MS _ _ (Z_to_bv 64 0x163cc) _ _ _ _) => fail
          | |- evt _ Qp (MS _ _ (Z_to_bv 64 0x162ec) _ _ _ _) => fail
          | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => br
          | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step
          end).

Ltac kfact :=
  match goal with HE : cp_hdr n fr = true |- _ => unfold ctrlparse; rewrite HE end; cbn [fst];
  unfold cp_kind, cp_type, cp_amp; zeval; reflexivity.

Ltac bfact :=
  match goal with HE : cp_hdr n fr = true |- _ => unfold ctrlparse; rewrite HE end; cbn [snd];
  unfold cp_struct, cp_rec, cp_kind, cp_type, cp_amp, P1; zeval; zeval; reflexivity.

Ltac kbound := first [zlitr | match goal with KR : 2 <= KL1 ?x <= 13 /\ _ |- _ => clear - KR; lia end].

Ltac leafk := eapply L_kind; first [eassumption | kbound | kfact | bfact].

Ltac none_exit HH :=
  step; rewrite rc_land3 by lia; step; ub_false;
  eapply L_epi; first [eassumption | unfold ctrlparse; rewrite HH; reflexivity].

Lemma L_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (jr js : list byte),
  stk rsegs m0 (S - 80) S -> mem_inv rsegs m0 ->
  rw_cells rsegs m0 (S + -40) [CB 40 jr] -> rw_cells rsegs m0 o' [CB 36 js] ->
  evt rsegs Qp
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 o) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Ff (Z_to_bv 64 REAC_CTRL_PARSE) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 jr js ST MI HR HSt.
  unfold REAC_CTRL_PARSE.
  pose proof (munch_refl [(o', o' + 36); (S - 80, S)] m0) as MU.
  pose proof (wmono_refl rsegs m0) as WM.
  assert (UO : bv_unsigned (Z_to_bv 64 o') = o') by (apply unsigned_lit; lia).
  assert (U36 : bv_unsigned (Z_to_bv 64 36) = 36) by reflexivity.
  assert (U0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
  do 11 step.
  rc_ojoin HO (S + -76).
  do 4 step.
  rc_call MSET.
  { rewrite UO, U36. change (Z.to_nat 36) with 36%nat. eassumption. }
  { assumption. }
  rename POST into HZ. rewrite UO, U36, U0 in HZ. change (Z.to_nat 36) with 36%nat in HZ.
  change (Z_to_bv 8 (0 mod 256)) with cp_z in HZ.
  do 2 step. rewrite (rc_ltu64 n 50) by lia.
  destruct (Z.ltb_spec n 50) as [Hlt|Hge]; cbv iota.
  { assert (HH : cp_hdr n fr = false) by (unfold cp_hdr; rewrite (proj2 (Z.leb_gt 50 n) Hlt); reflexivity).
    none_exit HH. }
  destruct (HF Hge) as (Hf0 & Hf50 & HfS & Hfo).
  step. ub_false. do 2 step. ub_false.
  rdb 12%nat 1%nat ltac:(intros j Hj; replace (12 + j)%nat with 12%nat by lia; apply cp_rd_12; lia).
  do 3 step.
  rewrite (rc_eqb_zxb (cp_b fr 12) 136) by lia. change (bv_unsigned (cp_b fr 12)) with (cp_v fr 12).
  destruct (Z.eqb_spec (cp_v fr 12) 136) as [E12|E12]; cbn [negb]; cbv iota.
  2:{ assert (HH : cp_hdr n fr = false)
        by (unfold cp_hdr; rewrite (proj2 (Z.eqb_neq _ _) E12), andb_false_r; reflexivity).
      none_exit HH. }
  do 2 step. ub_false.
  rdb 13%nat 1%nat ltac:(intros j Hj; replace (13 + j)%nat with 13%nat by lia; apply cp_rd_13; lia).
  do 3 step.
  rewrite (rc_eqb_zxb (cp_b fr 13) 25) by lia. change (bv_unsigned (cp_b fr 13)) with (cp_v fr 13).
  destruct (Z.eqb_spec (cp_v fr 13) 25) as [E13|E13]; cbn [negb]; cbv iota.
  2:{ assert (HH : cp_hdr n fr = false)
        by (unfold cp_hdr; rewrite (proj2 (Z.eqb_neq _ _) E13), andb_false_r; reflexivity).
      none_exit HH. }
  assert (HE : cp_hdr n fr = true) by (apply cp_hdr_spec; lia).
  clear RO RO0.
  rdb 0%nat 23%nat ltac:(intros j Hj; apply cp_rd_e; [exact HE | lia]).
  step. rewrite rc_land3 by lia. step. ub_false.
  do 2 step.
  rc_ojoin HO (S + -76).
  do 4 step.
  destruct (rc_rw_cut_at rsegs _ o' cp_z 36 4 (o' + 4) HZ ltac:(lia) ltac:(lia)) as [HK HZ1]; cbn [Nat.sub] in HZ1.
  destruct (rc_rw_cut_at rsegs _ (o' + 4) cp_z 32 6 (o' + 10) HZ1 ltac:(lia) ltac:(lia)) as [HSRC HZ2];
    cbn [Nat.sub] in HZ2.
  destruct (rc_rw_cut_at rsegs _ (o' + 10) cp_z 26 6 (o' + 16) HZ2 ltac:(lia) ltac:(lia)) as [HDST HZ3];
    cbn [Nat.sub] in HZ3.
  destruct (rc_rw_cut_at rsegs _ (o' + 16) cp_z 20 12 (o' + 28) HZ3 ltac:(lia) ltac:(lia)) as [HMID HZ4];
    cbn [Nat.sub] in HZ4.
  destruct (rc_rw_cut_at rsegs _ (o' + 28) cp_z 8 2 (o' + 30) HZ4 ltac:(lia) ltac:(lia)) as [HTG HAMP];
    cbn [Nat.sub] in HAMP.
  clear HZ HZ1 HZ2 HZ3 HZ4.
  pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 0 6 RO ltac:(cbn; lia)) as BD0.
  cbn [map seq firstn skipn] in BD0. rewrite Z.add_0_r in BD0.
  assert (Uf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (U6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  assert (U10 : bv_unsigned (Z_to_bv 64 (o' + 10)) = o' + 10) by (apply unsigned_lit; lia).
  rc_call MCPY.
  { rewrite Uf. exact BD0. }
  { reflexivity. }
  { rewrite U10, U6. exact HDST. }
  { rewrite Uf, U10, U6. lia. }
  { assumption. }
  rewrite ?U10, ?U6, ?Uf in *. change (Z.to_nat 6) with 6%nat in *.
  do 3 step. ub_false.
  do 2 step.
  rc_ojoin HO (S + -76).
  do 3 step.
  pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 6 6 RO ltac:(cbn; lia)) as BD1.
  cbn [map seq firstn skipn] in BD1. change (Z.of_nat 6) with 6 in BD1.
  assert (U4 : bv_unsigned (Z_to_bv 64 (o' + 4)) = o' + 4) by (apply unsigned_lit; lia).
  assert (Uf6 : bv_unsigned (Z_to_bv 64 (f + 6)) = f + 6) by (apply unsigned_lit; lia).
  rc_call MCPY.
  { rewrite Uf6. exact BD1. }
  { reflexivity. }
  { rewrite U4, U6. exact HSRC. }
  { rewrite Uf6, U4, U6. lia. }
  { assumption. }
  rewrite ?U4, ?U6, ?Uf6 in *. change (Z.to_nat 6) with 6%nat in *.
  do 5 step.
  destruct (rc_memcmp_ff (cp_b fr 0) (cp_b fr 1) (cp_b fr 2) (cp_b fr 3) (cp_b fr 4) (cp_b fr 5))
    as (v & Hv & Hvr & Hvb).
  rc_call BCMP.
  { rewrite Uf. exact BD0. }
  { change (bv_unsigned (Z_to_bv 64 66707)) with 66707.
    apply (rc_ro_in_image rsegs _ _ (repeat (Z_to_bv 8 255) 6)); [assumption | vm_compute; reflexivity]. }
  { rewrite U6. exact Hv. }
  { assumption. }
  do 4 step. ub_false.
  do 2 step. ub_false.
  do 3 step.
  rc_ojoin HO (S + -76).
  do 6 step. ub_false.
  do 4 step.
  rc_ojoin HO (S + -76).
  do 3 step. ub_false.
  do 3 step.
  rc_ojoin HO (S + -76).
  do 4 step. ub_false.
  do 4 step.
  rc_ojoin HO (S + -76).
  do 5 step. ub_false.
  do 3 step.
  rc_ojoin HO (S + -76).
  do 3 step. ub_false.
  do 2 step. ub_false.
  match goal with H : rw_cells rsegs _ (o' + 4) [CB 6 _] |- _ => rename H into HSRC' end.
  match goal with H : rw_cells rsegs _ (o' + 10) [CB 6 _] |- _ => rename H into HDST' end.
  pose proof (rc_rw_join rsegs _ (o' + 4) (o' + 10) _ _ HSRC' ltac:(cbn [cells_size csize app]; lia) HDST') as J1.
  pose proof (rc_rw_join rsegs _ (o' + 4) (o' + 16) _ _ J1 ltac:(cbn [cells_size csize app]; lia) HMID) as J2.
  clear HSRC' HDST' HMID J1.
  apply (rc_rw_flat rsegs _ (o' + 4) _ P1) in J2.
  2:{ cbn [app cells_bytes cbytes]. rewrite rc_le4_seqz by lia. rewrite !rc_le2_pack. rewrite Hvb.
      cbn [skipn repeat app]. reflexivity. }
  change (length P1) with 24%nat in J2. rename J2 into HP.
  step. step. step. rewrite ?rc_zextb. step. step.
  cond_norm.
  destruct ((cp_v fr 16 =? 0) && (cp_v fr 17 =? 0)) eqn:T0; cbn [negb]; cbv iota.
  { rewrite andb_true_iff, !Z.eqb_eq in T0. destruct T0 as [T0a T0b]. step. step. leafk. }
  pose proof (cp_v_range fr 16). pose proof (cp_v_range fr 17). pose proof (cp_v_range fr 18).
  pose proof (cp_v_range fr 19). pose proof (cp_v_range fr 22). pose proof (KL1_range (cp_v fr 22)) as KR.
  assert (KL6 : KL1 (cp_v fr 22) <> 6) by (clear - KR; lia).
  drive.
  all: lazymatch goal with
       | |- evt _ Qp (MS _ _ (Z_to_bv 64 0x162dc) _ _ _ _) => leafk
       | |- evt _ Qp (MS _ _ (Z_to_bv 64 0x163cc) _ _ _ _) =>
           eapply evt_cut; [eapply KOL | intros ? [? ->]];
           rewrite rc_signed_zxb; change (bv_unsigned (cp_b fr 22)) with (cp_v fr 22);
           replace (ret_pc (Z_to_bv 64 0x162d4)) with (Z_to_bv 64 0x162d4)
             by (symmetry; apply ret_pc_even; [lia | reflexivity]);
           step; leafk
       | |- evt _ Qp (MS _ _ (Z_to_bv 64 0x162ec) _ _ _ _) => idtac
       end.
  step. step. br.
  2:{ drive. leafk. }
  assert (HRC : cp_rec fr = true) by (unfold cp_rec, cp_type; zeval; reflexivity).
  pose proof (cp_v_range fr 32). pose proof (cp_v_range fr 33). pose proof (cp_v_range fr 34).
  pose proof (cp_v_range fr 35).
  do 2 step. ub_false. do 2 step. ub_false.
  rdb 34%nat 2%nat ltac:(intros j Hj; apply cp_rd_rec; [exact HE | exact HRC | lia]).
  rdb 32%nat 1%nat ltac:(intros j Hj; apply cp_rd_rec; [exact HE | exact HRC | lia]).
  do 6 step.
  rc_ojoin HO (S + -76).
  do 3 step. ub_false.
  match goal with H : rw_cells rsegs _ (o' + 28) [C2 _] |- _ => rename H into HTG' end.
  apply (rc_rw_flat rsegs _ (o' + 28) _ [cp_b fr 35; cp_b fr 34]) in HTG'.
  2:{ cbn [cells_bytes cbytes]. rewrite rc_le2_pack. reflexivity. }
  cbn [length] in HTG'.
  do 3 step. br.
  2:{ drive. leafk. }
  do 2 step. ub_false.
  rdb 33%nat 1%nat ltac:(intros j Hj; replace (33 + j)%nat with 33%nat by lia; apply cp_rd_33; [exact HE | exact HRC | lia]).
  do 3 step. br.
  2:{ drive. leafk. }
  do 2 step.
  rewrite rc_pack_eqb by zlitr.
  change (bv_unsigned (cp_b fr 34)) with (cp_v fr 34). change (bv_unsigned (cp_b fr 35)) with (cp_v fr 35).
  zdec (cp_v fr 34 * 256 + cp_v fr 35) 257.
  2:{ destruct (Z.eqb_spec (cp_v fr 34) 1); [assert (cp_v fr 35 <> 1) by lia|]; drive; leafk. }
  assert (E34 : cp_v fr 34 = 1) by lia. assert (E35 : cp_v fr 35 = 1) by lia.
  assert (K6 : cp_kind fr = 6) by (unfold cp_kind, cp_type, cp_amp; zeval; reflexivity).
  do 4 step. ub_false.
  rdb 36%nat 3%nat ltac:(intros j Hj; apply cp_rd_amp; [exact HE | exact HRC | exact K6 | lia]).
  do 2 step.
  rc_ojoin HO (S + -76).
  do 4 step. ub_false.
  do 2 step.
  rc_ojoin HO (S + -76).
  do 4 step. ub_false.
  do 2 step.
  rc_ojoin HO (S + -76).
  do 4 step.
  match goal with H : rw_cells rsegs _ o' [C4 _] |- _ => rename H into HK6 end.
  match goal with H : rw_cells rsegs _ (o' + 30) _ |- _ => rename H into HA6 end.
  pose proof (rc_rw_join rsegs _ o' (o' + 4) _ _ HK6 ltac:(cbn [cells_size csize app]; lia) HP) as J1.
  pose proof (rc_rw_join rsegs _ o' (o' + 28) _ _ J1 ltac:(cbn [cells_size csize app]; lia) HTG') as J2.
  pose proof (rc_rw_join rsegs _ o' (o' + 30) _ _ J2 ltac:(cbn [cells_size csize app]; lia) HA6) as J3.
  apply (rc_rw_flat rsegs _ o' _ (snd (ctrlparse n fr))) in J3.
  2:{ symmetry. unfold ctrlparse. rewrite HE. cbn [snd]. rewrite K6. unfold cp_struct, P1. rewrite HRC.
      cbn [Z.eqb Pos.eqb app cells_bytes cbytes]. rewrite rc_le4_small by lia.
      cbn [skipn firstn repeat app]. reflexivity. }
  rewrite ctrlparse_length in J3.
  eapply L_epi; first [eassumption | (unfold ctrlparse; rewrite HE; exact K6) | reflexivity].
Qed.

End P.

Theorem reac_ctrl_parse_holds :
  memset_contract -> memcpy_contract -> bcmp_contract -> kind_of_link1_contract -> reac_ctrl_parse_contract.
Proof.
  intros MSET MCPY BCMP KOL. unfold reac_ctrl_parse_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Ff fc m f n o S fr junk -> -> -> -> Hf Hn Ho HS1 HS16 HSK ST MI Hfr HF Hrd HOK.
  unfold REAC_CTRL_PARSE_K in HSK, ST, HF, HOK.
  pose proof ST as ST0.
  destruct (stk_carve rsegs m (S - 80) S 40 ST ltac:(lia)) as [ST1 [jr HR]].
  replace (S - Z.of_nat 40) with (S + -40) in HR by lia.
  destruct (Z.eq_dec o 0) as [Hz|Hz].
  - destruct (stk_carve rsegs m (S - 80) (S - Z.of_nat 40) 36 ST1 ltac:(lia)) as [_ [js HSt]].
    replace (S - Z.of_nat 40 - Z.of_nat 36) with (S - 76) in HSt by lia.
    eapply L_main with (o' := S - 76).
    all: first [ eassumption | lia | (left; split; [exact Hz | reflexivity])
               | (intros Hn50; pose proof (HF Hn50); lia) ].
  - destruct (HOK Hz) as (Ho4 & Ho36 & HSt & HoS & Hof).
    eapply L_main with (o' := o).
    all: first [ eassumption | lia | (right; split; [exact Hz | reflexivity])
               | (intros Hn50; pose proof (HF Hn50); pose proof (Hof Hn50); lia) ].
Qed.
