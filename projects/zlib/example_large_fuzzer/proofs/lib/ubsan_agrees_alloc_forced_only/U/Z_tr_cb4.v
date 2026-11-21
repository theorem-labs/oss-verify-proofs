(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_cb1 Z_tr_cb2 Z_tr_cb3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees TreesTab SendModel BitsModel BitsModel2 FillWinModel TrSmallModel CompressModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition byt (a : arr) : Prop := forall i, 0 <= i < arr_len a -> 0 <= arr_get a i < 256.

Lemma byt_set : forall a i v, byt a -> 0 <= v < 256 -> byt (arr_set a i v).
Proof.
  intros a i v H Hv j Hj. rewrite arr_len_set in Hj. rewrite arr_get_set. destruct ((i =? j) && arr_inb a i); [exact Hv| apply H; exact Hj].
Qed.
Lemma wrap8_range : forall z, 0 <= wrap8 z < 256.
Proof. intros. rewrite wrap8_mod. apply Z.mod_pos_bound. lia. Qed.
Lemma byt_sbF : forall PB PD BB BV V l, byt PB -> byt (sbF_PB PB PD BB BV V l).
Proof. intros. unfold sbF_PB. destruct (16 - l <? BV); [|assumption]. apply byt_set; [apply byt_set; [assumption|]|]; apply wrap8_range. Qed.

Lemma sbF_BV_range : forall BV l, 0 <= BV <= 16 -> 0 <= l <= 16 -> 0 <= sbF_BV BV l <= 16.
Proof. intros BV l H1 H2. unfold sbF_BV. destruct (Z.ltb_spec (16 - l) BV); lia. Qed.
Lemma sbF_PD_range : forall PD BV l, 0 <= PD -> PD <= sbF_PD PD BV l <= PD + 2.
Proof. intros PD BV l H. unfold sbF_PD. destruct (16 - l <? BV); lia. Qed.
Lemma sbF_PB_len : forall PB PD BB BV V l, arr_len (sbF_PB PB PD BB BV V l) = arr_len PB.
Proof. intros. unfold sbF_PB. destruct (16 - l <? BV); rewrite ?arr_len_set; reflexivity. Qed.

Lemma upd4_sym_buf_get : forall s PB PD BB BV i, sym_buf_get (upd4 s PB PD BB BV) i = arr_get PB (ds_lit_bufsize s + i).
Proof. reflexivity. Qed.
Lemma upd4_sym_next : forall s PB PD BB BV, ds_sym_next (upd4 s PB PD BB BV) = ds_sym_next s.
Proof. reflexivity. Qed.
Lemma upd4_lit_bufsize : forall s PB PD BB BV, ds_lit_bufsize (upd4 s PB PD BB BV) = ds_lit_bufsize s.
Proof. reflexivity. Qed.

Lemma land255_small : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof. intros x H. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma lor_shl8_add : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> Z.lor (Z.shiftl b 8) a = a + Z.shiftl b 8.
Proof.
  intros a b Ha Hb. rewrite Z.add_comm. symmetry. apply Z.add_nocarry_lor.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec n 8).
  - rewrite (Z.testbit_neg_r b (n - 8)) by lia. reflexivity.
  - rewrite (Z.bits_above_log2 a n); [apply andb_false_r| lia|].
    destruct (Z.eq_dec a 0) as [->|NE]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|]. eapply Z.lt_le_trans; [apply Ha|]. apply (Z.pow_le_mono_r 2 8 n); lia.
Qed.

Lemma sub_fp_refl : forall W, sub_fp W W.
Proof. intros W x H. exact H. Qed.

Lemma sbs_ok_cons_flat : forall P s PB PD BB BV v l r, sbs_ok P (upd4 s PB PD BB BV) ((v, l) :: r) ->
  0 <= l <= 16 /\ (16 - l < BV -> PD + 2 <= P) /\ sbs_ok P (upd4 s (sbF_PB PB PD BB BV v l) (sbF_PD PD BV l) (sbF_BB BB BV v l) (sbF_BV BV l)) r.
Proof.
  intros P s PB PD BB BV v l r H. cbn [sbs_ok] in H. destruct H as (H1 & H2 & H3). rewrite send_bits_sbF in H3.
  unfold sb_room, Buf_size in H2. rewrite upd4_bi_valid, upd4_pending in H2. auto.
Qed.
Lemma sbs_run_cons_flat : forall s PB PD BB BV v l r,
  sbs_run (upd4 s PB PD BB BV) ((v, l) :: r) = sbs_run (upd4 s (sbF_PB PB PD BB BV v l) (sbF_PD PD BV l) (sbF_BB BB BV v l) (sbF_BV BV l)) r.
Proof. intros. cbn [sbs_run]. rewrite send_bits_sbF. reflexivity. Qed.

Definition dist_calls (dfc ddl : arr) (dist : Z) : list (Z * Z) :=
  let dcode := d_code (dist - 1) in
  [(arr_get dfc dcode, arr_get ddl dcode)]
  ++ (if negb (arr_get extra_dbits_a dcode =? 0) then [(wrap32 (dist - 1 - arr_get base_dist_a dcode), arr_get extra_dbits_a dcode)] else []).

Lemma wrap32_small : forall z, 0 <= z < 2^32 -> wrap32 z = z.
Proof. intros z H. rewrite wrap32_mod. apply Z.mod_small. exact H. Qed.

Lemma sym_calls_lit : forall X lfc ldl dfc ddl sx, sym_dist X sx = 0 ->
  sym_calls X lfc ldl dfc ddl sx = [(arr_get lfc (sym_lc X sx), arr_get ldl (sym_lc X sx))].
Proof. intros X lfc ldl dfc ddl sx Hd. unfold sym_calls. cbv zeta. rewrite (proj2 (Z.eqb_eq _ _) Hd). reflexivity. Qed.

Lemma sym_calls_match : forall X lfc ldl dfc ddl sx, sym_dist X sx <> 0 -> 0 <= sym_lc X sx < 256 ->
  sym_calls X lfc ldl dfc ddl sx =
  (arr_get lfc (arr_get length_code_a (sym_lc X sx) + 257), arr_get ldl (arr_get length_code_a (sym_lc X sx) + 257))
  :: (if (8 <=? arr_get length_code_a (sym_lc X sx)) && (arr_get length_code_a (sym_lc X sx) <=? 27)
      then [(sym_lc X sx - arr_get base_length_a (arr_get length_code_a (sym_lc X sx)), arr_get extra_lbits_a (arr_get length_code_a (sym_lc X sx)))] else [])
     ++ dist_calls dfc ddl (sym_dist X sx).
Proof.
  intros X lfc ldl dfc ddl sx Hd Hlc. unfold sym_calls, dist_calls. cbv zeta. rewrite (proj2 (Z.eqb_neq _ _) Hd).
  destruct (extra_lbits_facts _ (length_code_range _ Hlc)) as (_ & _ & E). rewrite E.
  replace (arr_get length_code_a (sym_lc X sx) + LITERALS + 1) with (arr_get length_code_a (sym_lc X sx) + 257) by (unfold LITERALS; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
Definition c15 (fc : arr) (n : Z) : Prop := forall i, 0 <= i < n -> 0 <= arr_get fc i < 32768.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cb_part_post (EXIT : Z) (L : dlay) (s : deflate_state) (LT DT sx : Z) (PB : arr) (PD BB BV : Z) (cs : list (Z * Z))
    (ra sp gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 wbb PB' PD' BB' BV' m',
    ms' = MS (ucbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F (wz EXIT) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB' PD' wbb (wz BV') /\ bv_unsigned wbb mod 2^16 = BB' mod 2^16
    /\ sbs_run (upd4 s PB PD BB BV) cs = upd4 s PB' PD' BB' BV'
    /\ 0 <= BV' <= 16 /\ 0 <= PD' /\ byt PB'.

Lemma cb_dist_part : forall (L : dlay) (s : deflate_state) (dfc ddl : arr) (LT DT sx dist : Z) (PB : arr) (PD BB BV : Z) (w : word)
    (ra sp gp tp s2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD w (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 ->
  mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m DT dfc ddl 30 -> 1 <= dist <= 32768 -> 0 < DT -> DT + 4 * 30 < 2^63 -> DT mod 2 = 0 ->
  c15 dfc 30 ->
  0 <= BV <= 16 -> 0 <= PD -> byt PB ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (dist_calls dfc ddl dist) ->
  evt usegs (cb_part_post 0x1d9f4 L s LT DT sx PB PD BB BV (dist_calls dfc ddl dist) ra sp gp tp s11 F fc m)
      (MS (ucbR L LT DT sx ra sp gp tp (wz dist) w s2 (wz BV) s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1ddc0) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY RDD Rdist RDT1 RDT2 ADT RDf RBV RPD BYT HSB.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold dist_calls in HSB. cbv zeta in HSB.
  remember (d_code (dist - 1)) as dcode eqn:Edc.
  pose proof (dist_base_le (dist - 1) ltac:(lia)) as (Rdc & RVlo). rewrite <- Edc in Rdc, RVlo.
  pose proof (extra_dbits_facts dcode Rdc) as (Rex & Rbase & EXB).
  cbn [app] in HSB. apply sbs_ok_cons_flat in HSB. destruct HSB as (Rl & ROOM & HSB2).
  call (cb_S4 L s dfc ddl LT DT sx dist dcode (arr_get dfc dcode) (arr_get ddl dcode) PB PD BB BV w).
  1:{ exact Edc. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HW. } 1:{ exact MI. } 1:{ exact LAY. }
  1:{ exact RDD. } 1:{ exact Rdist. } 1:{ exact RDT1. } 1:{ exact RDT2. } 1:{ exact ADT. } 1:{ apply RDf. lia. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. }
  set (V1 := arr_get dfc dcode) in *. set (l1 := arr_get ddl dcode) in *.
  pose proof (sbF_BV_range BV l1 RBV Rl) as RBV1. pose proof (sbF_PD_range PD BV l1 RPD) as RPD1. pose proof (byt_sbF PB PD BB BV V1 l1 BYT) as BYT1.
  match goal with H : EM ?mm _ _ _ _ ?wr _, HWr : bv_unsigned ?wr mod _ = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (cb_S5 L s LT DT sx dist dcode (dist - 1 - arr_get base_dist_a dcode) (arr_get extra_dbits_a dcode) (4 <=? dcode) _ _ _ _ BV wr);
    [exact Edc| reflexivity| reflexivity| reflexivity| exact H| exact HWr| eassumption| exact LAY| exact Rdist| lia| exact RBV1| lia| |]
  end.
  1:{ intros X4. rewrite EXB, X4 in HSB2. cbn [negb app] in HSB2. rewrite wrap32_small in HSB2 by lia.
      apply sbs_ok_cons_flat in HSB2. destruct HSB2 as (_ & ROOM2 & _). exact ROOM2. }
  apply evt_done. unfold cb_part_post. do 17 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|].
  split. { unfold dist_calls. cbv zeta. rewrite <- Edc. rewrite EXB.
           destruct (4 <=? dcode); cbn [negb app]; rewrite ?wrap32_small by lia; rewrite !sbs_run_cons_flat; reflexivity. }
  destruct (4 <=? dcode).
  - split; [apply sbF_BV_range; lia|]. split; [|apply byt_sbF; exact BYT1].
    match goal with |- 0 <= sbF_PD ?p ?b ?l => pose proof (sbF_PD_range p b l ltac:(lia)); lia end.
  - split; [exact RBV1|]. split; [lia| exact BYT1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cb_body : forall (L : dlay) (s : deflate_state) (lfc ldl dfc ddl : arr) (LT DT sx : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m LT lfc ldl 286 -> ct_readable (Wem L) m DT dfc ddl 30 ->
  0 < LT -> LT + 4 * 286 < 2^63 -> 0 < DT -> DT + 4 * 30 < 2^63 -> LT mod 2 = 0 -> DT mod 2 = 0 ->
  c15 lfc 286 -> c15 dfc 30 ->
  0 <= BV <= 16 -> 0 <= PD -> byt PB -> 0 <= ds_lit_bufsize s -> sx < 2^31 ->
  sym_ok 65536 (upd4 s PB PD BB BV) lfc ldl dfc ddl sx ->
  evt usegs (cb_part_post 0x1d9f4 L s LT DT sx PB PD BB BV (sym_calls (upd4 s PB PD BB BV) lfc ldl dfc ddl sx) ra sp gp tp s11 F fc m)
      (MS (ucbR L LT DT sx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1da00) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HBB MI LAY RDL RDD RLT1 RLT2 RDT1 RDT2 ALT ADT RLf RDf RBV RPD BYT Rlb Rsx (Hsx & Hlb & Hdist & HSB). unfold ucbR.
  rewrite upd4_lit_bufsize in Hlb.
  pose proof EMH as (_ & _ & _ & LNPB).
  set (lb := ds_lit_bufsize s) in *.
  remember (arr_get PB (lb + sx)) as b0 eqn:Eb0. remember (arr_get PB (lb + (sx + 1))) as b1 eqn:Eb1. remember (arr_get PB (lb + (sx + 1 + 1))) as lc eqn:Elc.
  assert (Rb0 : 0 <= b0 < 256) by (rewrite Eb0; apply BYT; lia).
  assert (Rb1 : 0 <= b1 < 256) by (rewrite Eb1; apply BYT; lia).
  assert (Rlc : 0 <= lc < 256) by (rewrite Elc; apply BYT; lia).
  assert (Edist : sym_dist (upd4 s PB PD BB BV) sx = b0 + Z.shiftl b1 8).
  { unfold sym_dist, sym_d0, sym_d1. rewrite !upd4_sym_buf_get. fold lb. rewrite <- Eb0, <- Eb1, !land255_small by lia. reflexivity. }
  assert (Elc' : sym_lc (upd4 s PB PD BB BV) sx = lc) by (unfold sym_lc; rewrite upd4_sym_buf_get; fold lb; rewrite <- Elc; reflexivity).
  assert (Rsh : 0 <= Z.shiftl b1 8 <= 65280) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Edist in Hdist.
  set (dist := b0 + Z.shiftl b1 8) in *.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY.
  (* [comment removed for export] *)
  pose proof EMH as EMH'. open_EM EMH'.
  pose proof (u8arr_read usegs m (dl_Ab L) (av8 PB 65536) (lb + sx) _ (wa (dl_Ab L + (lb + sx))) Gpend (av8_nth PB 65536 (lb + sx) ltac:(lia)) ltac:(lia) eq_refl) as RD0.
  pose proof (u8arr_read usegs m (dl_Ab L) (av8 PB 65536) (lb + (sx + 1)) _ (wa (dl_Ab L + (lb + (sx + 1)))) Gpend (av8_nth PB 65536 (lb + (sx + 1)) ltac:(lia)) ltac:(lia) eq_refl) as RD1.
  pose proof (u8arr_read usegs m (dl_Ab L) (av8 PB 65536) (lb + (sx + 1 + 1)) _ (wa (dl_Ab L + (lb + (sx + 1 + 1)))) Gpend (av8_nth PB 65536 (lb + (sx + 1 + 1)) ltac:(lia)) ltac:(lia) eq_refl) as RD2.
  rewrite <- Eb0 in RD0. rewrite <- Eb1 in RD1. rewrite <- Elc in RD2.
  zs2. zs2. zs2. rewrite ?Z.mod_small by lia.
  uwalk 0x1da28 CB_TRAP. at_pc 0x1da28.
  zs2. zs2. zs2. rewrite ?Z.mod_small by lia.
  uwalk 0x1da3c CB_TRAP. at_pc 0x1da3c.
  zs2. zs2. zs2. rewrite ?Z.mod_small by lia.
  uwalk 0x1da50 CB_TRAP. at_pc 0x1da50.
  zsb. rewrite (bv8_small b1) by lia. zsb. rewrite (bv8_small b0) by lia.
  zs2. zsb. rewrite (bv8_small lc) by lia.
  zs2. zs2. rewrite (lor_shl8_add b0 b1) by lia. fold dist.
  clear GA GD Gpend RD0 RD1 RD2 LPB LNP.
  assert (Rdist : 0 <= dist < 65536) by (unfold dist; lia).
  zstep. br_cases K.
  - (* [comment removed for export] *)
    assert (SC := sym_calls_lit (upd4 s PB PD BB BV) lfc ldl dfc ddl sx ltac:(rewrite Edist; exact K)). rewrite Elc' in SC.
    rewrite SC in HSB. apply sbs_ok_cons_flat in HSB. destruct HSB as (Rl & ROOM & _).
    call (cb_S1 L s lfc ldl LT DT sx lc PB PD BB BV wbb).
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ assumption. } 1:{ exact RDL. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact ALT. }
    1:{ apply RLf. lia. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. }
    apply evt_done. unfold cb_part_post. do 17 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|].
    split. { rewrite SC. rewrite sbs_run_cons_flat. reflexivity. }
    split; [apply sbF_BV_range; assumption|]. split; [pose proof (sbF_PD_range PD BV (arr_get ldl lc) RPD); lia| apply byt_sbF; exact BYT].
  - (* [comment removed for export] *)
    assert (SC := sym_calls_match (upd4 s PB PD BB BV) lfc ldl dfc ddl sx ltac:(rewrite Edist; exact K) ltac:(rewrite Elc'; exact Rlc)).
    rewrite Edist, Elc' in SC. fold dist in SC.
    pose proof HSB as HSB'. rewrite SC in HSB'. clear HSB.
    remember (arr_get length_code_a lc) as code eqn:Ecode.
    pose proof (length_code_range lc Rlc) as Rcode. rewrite <- Ecode in Rcode.
    apply sbs_ok_cons_flat in HSB'. destruct HSB' as (Rl & ROOM & HSB2).
    call (cb_S2 L s lfc ldl LT DT sx lc dist code (arr_get lfc (code + 257)) (arr_get ldl (code + 257)) PB PD BB BV wbb).
    1:{ exact Ecode. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ assumption. } 1:{ exact RDL. }
    1:{ exact Rlc. } 1:{ lia. } 1:{ lia. } 1:{ exact ALT. } 1:{ apply RLf. lia. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. }
    set (V1 := arr_get lfc (code + 257)) in *. set (l1 := arr_get ldl (code + 257)) in *.
    pose proof (sbF_BV_range BV l1 RBV Rl) as RBV1. pose proof (sbF_PD_range PD BV l1 RPD) as RPD1. pose proof (byt_sbF PB PD BB BV V1 l1 BYT) as BYT1.
    assert (Rd2 : 1 <= dist <= 32768) by lia.
    match goal with H : EM ?mm _ _ _ _ ?wr _, HWr : bv_unsigned ?wr mod _ = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (cb_S3 L s LT DT sx lc dist code (lc - arr_get base_length_a code) (arr_get extra_lbits_a code) ((8 <=? code) && (code <=? 27)) _ _ _ _ BV wr);
      [exact Ecode| reflexivity| reflexivity| reflexivity| exact H| exact HWr| eassumption| assumption| exact Rlc| lia| exact RBV1| lia| |]
    end.
    1:{ intros X3. rewrite X3 in HSB2. cbn [app] in HSB2. apply sbs_ok_cons_flat in HSB2. destruct HSB2 as (_ & ROOM2 & _). exact ROOM2. }
    set (V2 := lc - arr_get base_length_a code) in *. set (l2 := arr_get extra_lbits_a code) in *.
    match goal with H : EM ?mm _ _ _ _ ?wr _, HWr : bv_unsigned ?wr mod _ = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (cb_dist_part L s dfc ddl LT DT sx dist _ _ _ _ wr);
      [exact H| exact HWr| eassumption| assumption| | exact Rd2| exact RDT1| exact RDT2| exact ADT| exact RDf| | | | |]
    end.
    1:{ eapply ct_readable_rebase; [exact RDD| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ destruct ((8 <=? code) && (code <=? 27)); [apply sbF_BV_range; [exact RBV1|]| exact RBV1].
        pose proof (extra_lbits_facts code Rcode) as (Rex & _); subst l2; lia. }
    1:{ destruct ((8 <=? code) && (code <=? 27)); [pose proof (sbF_PD_range (sbF_PD PD BV l1) (sbF_BV BV l1) l2 ltac:(lia)); lia| lia]. }
    1:{ destruct ((8 <=? code) && (code <=? 27)); [apply byt_sbF|]; exact BYT1. }
    1:{ destruct ((8 <=? code) && (code <=? 27)); cbn [app] in HSB2; [apply sbs_ok_cons_flat in HSB2; destruct HSB2 as (_ & _ & HSB3); exact HSB3| exact HSB2]. }
    apply evt_done. unfold cb_part_post. do 17 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|].
    split. { rewrite SC. rewrite sbs_run_cons_flat. destruct ((8 <=? code) && (code <=? 27)); cbn [app]; rewrite ?sbs_run_cons_flat; eassumption. }
    split; [assumption|]. split; assumption.
Qed.
