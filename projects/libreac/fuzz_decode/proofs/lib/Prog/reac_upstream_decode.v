From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import reac_frame_inspect_c reac_decode_c reac_upstream_decode_c ReacDecodeLib.
Import ListNotations.
Open Scope Z_scope.

Lemma braid_pos_lin' : forall s ch nch k, 0 <= k < 3 ->
  braid_pos s ch nch k = 3 * (s * nch + (ch - ch mod 2)) +
    (if k =? 0 then 3 + ch mod 2 else if k =? 1 then 5 * (ch mod 2) else 1 + ch mod 2).
Proof.
  intros s ch nch k Hk. unfold braid_pos.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  destruct (Z.eqb_spec (ch mod 2) 0) as [E|E];
  destruct (Z.eqb_spec k 0); destruct (Z.eqb_spec k 1); try rewrite E; lia.
Qed.

Lemma braid_byte_at' : forall bs nch ns ch s k, 0 <= ch -> 0 <= s < ns -> 0 <= k < 3 ->
  braid_byte bs nch ns (3 * (ch * ns + s) + k) = nth (Z.to_nat (50 + braid_pos s ch nch k)) bs (Z_to_bv 8 0).
Proof.
  intros bs nch ns ch s k Hch Hs Hk. unfold braid_byte.
  destruct (braid_div ch s k ns Hch Hs Hk) as (D1 & D2 & D3 & D4). rewrite D1, D2, D3, D4. reflexivity.
Qed.

Lemma up_ok_true : forall raw out len bs, up_ok raw out len bs = true <->
  raw <> 0 /\ out <> 0 /\ 0 <= up_nch len /\ inspect_byte bs 12 = 0x88 /\ inspect_byte bs 13 = 0x19 /\
  inspect_byte bs (Z.to_nat (len - 2)) = 0xC2 /\ inspect_byte bs (Z.to_nat (len - 1)) = 0xEA.
Proof.
  intros. unfold up_ok. rewrite !andb_true_iff, !negb_true_iff, !Z.eqb_neq, !Z.eqb_eq, Z.leb_le. tauto.
Qed.

Lemma up_nch_pos : forall len, 0 <= up_nch len ->
  124 <= len /\ (len - 52) mod 36 = 0 /\ ((len - 52) / 36) mod 2 = 0 /\ (len - 52) / 36 <= 40 /\
  up_nch len = (len - 52) / 36.
Proof.
  intros len H. unfold up_nch in *.
  destruct ((124 <=? len) && ((len - 52) mod 36 =? 0) && (((len - 52) / 36) mod 2 =? 0) && ((len - 52) / 36 <=? 40)) eqn:E.
  - rewrite !andb_true_iff, !Z.leb_le, !Z.eqb_eq in E. tauto.
  - lia.
Qed.

Lemma up_nch_val : forall len, 124 <= len -> (len - 52) mod 36 = 0 -> ((len - 52) / 36) mod 2 = 0 ->
  (len - 52) / 36 <= 40 -> up_nch len = (len - 52) / 36.
Proof.
  intros len H1 H2 H3 H4. unfold up_nch.
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.eqb_eq _ _) H2), (proj2 (Z.eqb_eq _ _) H3), (proj2 (Z.leb_le _ _) H4).
  reflexivity.
Qed.

Lemma div36 : forall x, 0 <= x < 2^64 -> Z.shiftr (Z.shiftr (x * 16397105843297379215) 64) 5 = x / 36.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
  pose proof (Z.div_mod x 36 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 36 ltac:(lia)) as B.
  symmetry. apply (Z.div_unique _ _ _ (28 * (x / 36) + (x mod 36) * 16397105843297379215)).
  - left. split; [lia|]. cbn. lia.
  - cbn. lia.
Qed.

Lemma width_test : forall q, 0 <= q < 2^31 ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 (q + -41))) (Z_to_bv 64 (-39)) = negb ((2 <=? q) && (q <=? 40)).
Proof.
  intros q Hq. rewrite swrap32_id by lia. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  destruct (Z_lt_le_dec q 41).
  - rewrite <- (Z.mod_add (q + -41) 1) by lia. rewrite Z.mod_small by lia.
    change (-39 mod 2^64) with 18446744073709551577.
    destruct (Z.leb_spec 2 q); destruct (Z.leb_spec q 40); destruct (Z.ltb_spec (q + -41 + 1 * 2^64) 18446744073709551577);
      cbn; try reflexivity; lia.
  - rewrite Z.mod_small by lia. change (-39 mod 2^64) with 18446744073709551577.
    destruct (Z.leb_spec 2 q); destruct (Z.leb_spec q 40); destruct (Z.ltb_spec (q + -41) 18446744073709551577);
      cbn; try reflexivity; lia.
Qed.

Lemma eqb_zxb : forall (b : byte) c, 0 <= c < 2^64 -> bv_eqb (zxb b) (Z_to_bv 64 c) = (bv_unsigned b =? c).
Proof.
  intros b c Hc. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  change (2 ^ Z.of_N 8) with 256 in Hb. unfold zxb, bv_eqb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma slli_srli33 : forall q, 0 <= q < 2^31 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 q)) 33))) 33) = Z_to_bv 64 q.
Proof.
  intros q Hq. rewrite (unsigned_lit q) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Section UP.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (raw out len : Z).

Definition PostU : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if up_ok raw out len bs then 12 else -1))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\
    (if up_ok raw out len bs
     then munch [(out, out + 36 * up_nch len)] m m' /\ bytes_at rsegs m' out (braid_out bs (up_nch len) 12)
     else m' = m).

Local Notation STATE pc mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 :=
  (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Lemma up_fail : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 : word),
  up_ok raw out len bs = false ->
  evt rsegs PostU (STATE 0x139fc m x5 x6 x7 (Z_to_bv 64 (-1)) x11 x12 x13 x14 x15 x16 x17 x28 x29).
Proof.
  intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 E.
  step. apply evt_done. unfold PostU.
  exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, t5, t6, m.
  rewrite E. split; [reflexivity|]. split; [apply wmono_refl | reflexivity].
Qed.

Variable nch : Z.
Hypothesis Hnchdef : up_nch len = nch.
Hypothesis Hnch : 2 <= nch <= 40.
Hypothesis Hev : nch mod 2 = 0.
Hypothesis Hlen52 : len = 52 + 36 * nch.
Hypothesis Hlen : length bs = Z.to_nat len.
Hypothesis Hraw : 0 < raw.
Hypothesis Hraw2 : raw + len <= 2^64.
Hypothesis Hout : 0 < out.
Hypothesis HoutN : out + 36 * nch < 2^64.
Hypothesis DOR : out + 36 * nch <= raw \/ raw + len <= out.
Hypothesis OK : up_ok raw out len bs = true.

Definition INVU (mk : word -> option byte) (j : Z) : Prop :=
  bytes_at rsegs mk raw bs /\ wr_at rsegs mk out (36 * nch) /\
    munch [(out, out + 36 * nch)] m mk /\ wmono rsegs m mk /\
    (forall i, 0 <= i < j -> mrd rsegs mk (Z_to_bv 64 (out + i)) = Some (braid_byte bs nch 12 i)).

Lemma INVU_idx : forall mk j j', INVU mk j -> j = j' -> INVU mk j'.
Proof. intros; subst; assumption. Qed.

Lemma INVU_rd : forall mk j ch s k, INVU mk j -> 0 <= ch < nch -> 0 <= s < 12 -> 0 <= k < 3 ->
  ov_read_bytes rsegs mk (Z_to_bv 64 (raw + (50 + (3 * (s * nch + (ch - ch mod 2)) +
    (if k =? 0 then 3 + ch mod 2 else if k =? 1 then 5 * (ch mod 2) else 1 + ch mod 2))))) 1 =
  Some [braid_byte bs nch 12 (3 * (ch * 12 + s) + k)].
Proof.
  intros mk j ch s k (HB & _) Hch Hs Hk. rewrite braid_byte_at' by lia. rewrite <- braid_pos_lin' by lia.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (s * nch <= 11 * nch) by nia.
  assert (ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  apply rd1; [exact HB|]. rewrite Hlen. rewrite braid_pos_lin' by lia.
  destruct (Z.eqb_spec k 0); destruct (Z.eqb_spec k 1); nia.
Qed.

Lemma INVU_wr : forall mk j q, INVU mk j -> 0 <= q < 36 * nch -> store_ok rsegs mk (Z_to_bv 64 (out + q)) 1 = true.
Proof.
  intros mk j q (_ & HW & _) Hq. change (Z_to_bv 64 (out + q)) with (wa (out + q)).
  apply (wr_at_store_ok rsegs mk out (36 * nch) q 1 HW); lia.
Qed.

Lemma INVU_store : forall mk j0 j j2, INVU mk j0 -> j0 = j -> 0 <= j < 36 * nch -> j2 = j + 1 ->
  INVU (write_to_mem mk (Z_to_bv 64 (out + j)) [braid_byte bs nch 12 j]) j2.
Proof.
  intros mk j0 j j2 (HB & HW & MU & WM & HP) E Hj E2. subst j0 j2.
  change (Z_to_bv 64 (out + j)) with (wa (out + j)).
  split; [|split; [|split; [|split]]].
  - apply bytes_at_write_other; [exact HB | lia | cbn; lia | rewrite Hlen; cbn; lia].
  - apply wr_at_write. exact HW.
  - apply munch_write; [exact MU | lia | cbn; lia | cbn [inside]; cbn; lia].
  - apply wmono_write. exact WM.
  - intros i Hi. change (wa (out + j)) with (Z_to_bv 64 (out + j)).
    rewrite mrd_write1 by lia.
    destruct (Z.eqb_spec (out + i) (out + j)) as [E|E].
    + replace i with j by lia. reflexivity.
    + apply HP. lia.
Qed.

Lemma INVU_out : forall mk, INVU mk (3 * nch * 12) -> bytes_at rsegs mk out (braid_out bs nch 12).
Proof.
  intros mk (_ & _ & _ & _ & HP). unfold braid_out.
  apply bytes_at_of_fun; [lia | lia |]. intros i Hi. apply HP. lia.
Qed.

Ltac do_store I0 I1 jj :=
  rewrite ?le1_zxb;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mk ?a ?b) _) =>
    assert (I1 : INVU (write_to_mem mk a b) (jj + 1)) by (eapply INVU_store; [exact I0 | lia | lia | lia]);
    let m2 := fresh "m" in set (m2 := write_to_mem mk a b) in *; clearbody m2; clear I0
  end.

Lemma up_inner : forall (ch : Z) (x5 x6 x7 x10 x11 x13 x14 x15 x16 : word),
  0 <= ch < nch -> bv_unsigned x5 = raw + 50 + ch mod 2 + 3 -> bv_unsigned x6 = raw + 50 + ch mod 2 + 1 ->
  bv_unsigned x7 = 5 * (ch mod 2) -> bv_unsigned x13 = raw + 50 -> bv_unsigned x14 = 3 * nch ->
  bv_unsigned x16 = out + 3 * (ch * 12 + 12) ->
  forall (K : nat) (s : Z) (m1 : word -> option byte) (x12 x17 x28 x29 : word),
  Z.to_nat (12 - s) = K -> 0 <= s < 12 ->
  bv_unsigned x12 = out + 3 * (ch * 12 + s) -> bv_unsigned x17 = 3 * (ch - ch mod 2) + 3 * nch * s ->
  INVU m1 (3 * (ch * 12 + s)) ->
  (forall (m2 : word -> option byte) (y12 y17 y28 y29 : word), bv_unsigned y12 = out + 3 * (ch * 12 + 12) ->
     INVU m2 (3 * (ch * 12 + 12)) ->
     evt rsegs PostU (STATE 0x13acc m2 x5 x6 x7 x10 x11 y12 x13 x14 x15 x16 y17 y28 y29)) ->
  evt rsegs PostU (STATE 0x13a98 m1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29).
Proof.
  intros ch x5 x6 x7 x10 x11 x13 x14 x15 x16 Hch H5 H6 H7 H13 H14 H16 K.
  induction K as [K IH] using lt_wf_ind.
  intros s m1 x12 x17 x28 x29 HK Hs H12 H17 I0 CONT.
  assert (s * nch <= 11 * nch) by nia.
  assert (ch * 12 <= (nch - 1) * 12) by nia.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  apply wv in H5, H6, H7, H12, H13, H14, H16, H17. subst x5 x6 x7 x12 x13 x14 x16 x17.
  pose proof (INVU_rd m1 _ ch s 0 I0 Hch Hs ltac:(lia)) as HR. cbn [Z.eqb Pos.eqb] in HR.
  pose proof (INVU_wr m1 _ (3 * (ch * 12 + s) + 0) I0 ltac:(nia)) as HS.
  step. step. step. step. step. clear HR HS. do_store I0 I1 (3 * (ch * 12 + s) + 0).
  pose proof (INVU_rd _ _ ch s 1 I1 ltac:(lia) ltac:(lia) ltac:(lia)) as HR. cbn [Z.eqb Pos.eqb] in HR.
  pose proof (INVU_wr _ _ (3 * (ch * 12 + s) + 1) I1 ltac:(nia)) as HS.
  step. step. step. clear HR HS. do_store I1 I2 (3 * (ch * 12 + s) + 1).
  pose proof (INVU_rd _ _ ch s 2 I2 ltac:(lia) ltac:(lia) ltac:(lia)) as HR. cbn [Z.eqb Pos.eqb] in HR.
  pose proof (INVU_wr _ _ (3 * (ch * 12 + s) + 2) I2 ltac:(nia)) as HS.
  step. step. clear HR HS. do_store I2 I3 (3 * (ch * 12 + s) + 2).
  step. step. step.
  brq BR.
  - eapply CONT; [rewrite unsigned_lit by lia; lia | eapply INVU_idx; [exact I3 | lia]].
  - eapply (IH (Z.to_nat (12 - (s + 1))) ltac:(lia) (s + 1));
      [ reflexivity | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by nia; nia
      | eapply INVU_idx; [exact I3 | lia] | exact CONT ].
Qed.

Lemma up_done : forall (mk : word -> option byte) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 : word),
  INVU mk (3 * nch * 12) ->
  evt rsegs PostU (STATE 0x13ad8 mk x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29).
Proof.
  intros mk x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 I0.
  step. step. apply evt_done. unfold PostU.
  exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, t5, t6, mk.
  rewrite OK. split; [reflexivity|].
  destruct I0 as (HB & HW & MU & WM & HP). split; [exact WM|]. rewrite Hnchdef. split.
  - replace (36 * nch) with (36 * nch) by lia. exact MU.
  - apply INVU_out. exact (conj HB (conj HW (conj MU (conj WM HP)))).
Qed.

Lemma up_outer : forall (K : nat) (ch : Z) (m1 : word -> option byte)
    (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 : word),
  Z.to_nat (nch - ch) = K -> 0 <= ch < nch ->
  bv_unsigned x10 = ch -> bv_unsigned x11 = ch -> bv_unsigned x12 = out + 3 * (ch * 12) ->
  bv_unsigned x13 = raw + 50 -> bv_unsigned x14 = 3 * nch -> x15 = Z_to_bv 64 nch ->
  INVU m1 (3 * (ch * 12)) ->
  evt rsegs PostU (STATE 0x13a68 m1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29).
Proof.
  induction K as [K IH] using lt_wf_ind.
  intros ch m1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 HK Hch H10 H11 H12 H13 H14 E15 I0.
  assert (ch * 12 <= (nch - 1) * 12) by nia.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  apply wv in H10, H11, H12, H13, H14. subst x10 x11 x12 x13 x14 x15.
  do 12 step.
  rewrite (unsigned_lit ch) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (ch * 2 ^ 2)) by lia.
  rewrite land_m8, land_m2 by lia. rewrite !land1.
  assert (P : ch mod 2 = 0 \/ ch mod 2 = 1) by lia.
  assert (EQ5 : bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 (ch mod 2)) 1)
    + -1))) 5)) = 5 * (ch mod 2)) by (destruct P as [P|P]; rewrite P; vm_compute; reflexivity).
  eapply (up_inner ch) with (K := Z.to_nat (12 - 0)) (s := 0);
    [ lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact EQ5
    | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
    | reflexivity | lia | rewrite unsigned_lit by lia; lia
    | rewrite (unsigned_lit (8 * (ch * 2 ^ 2 / 8))) by (Z.div_mod_to_equations; lia);
      rewrite (unsigned_lit (2 * (ch / 2))) by (Z.div_mod_to_equations; lia);
      rewrite unsigned_lit by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia
    | eapply INVU_idx; [exact I0 | lia] | ].
  intros m2 y12 y17 y28 y29 H12' I2. apply wv in H12'. subst y12.
  step. rewrite (unsigned_lit ch) by lia. rewrite swrap32_id by lia.
  step. step.
  brq BR.
  - apply up_done. apply (INVU_idx m2 (3 * (ch * 12 + 12))); [exact I2 | lia].
  - eapply (IH (Z.to_nat (nch - (ch + 1))) ltac:(lia) (ch + 1));
      [ reflexivity | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
      | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
      | reflexivity | apply (INVU_idx m2 (3 * (ch * 12 + 12))); [exact I2 | lia] ].
Qed.

End UP.

Ltac ufail :=
  eapply up_fail; apply not_true_iff_false; rewrite up_ok_true;
  intros (U1 & U2 & U3 & U4 & U5 & U6 & U7);
  try (apply up_nch_pos in U3; destruct U3 as (V1 & V2 & V3 & V4 & V5));
  unfold inspect_byte in *; first [ lia | (Z.div_mod_to_equations; lia) ].

Theorem reac_upstream_decode_holds : reac_upstream_decode_contract.
Proof.
  unfold reac_upstream_decode_contract, REAC_UPSTREAM_DECODE, DIV36_MAGIC_AT, DIV36_MAGIC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw out E0 E2 Rraw Rout Rlen HMG HB HO.
  subst a0 a2.
  pose proof (u64_range a1) as Ra1.
  set (len := bv_unsigned a1) in *.
  assert (A1 : a1 = Z_to_bv 64 len) by (symmetry; apply Z_to_bv_bv_unsigned).
  clearbody len. subst a1.
  pose proof (rd_all _ _ _ HMG) as HRM. rewrite length_le8 in HRM.
  do 4 step.
  brq B1.
  { ufail. }
  step. brq B2.
  { ufail. }
  step. brq B3.
  { ufail. }
  step. step. step. step.
  replace (len + -52) with (len - 52) in * by lia.
  rewrite (unsigned_lit (len - 52)) by lia.
  step.
  rewrite (unsigned_lit (Z.shiftr _ 64)) by (rewrite Z.shiftr_div_pow2 by lia; split;
    [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; nia]).
  rewrite div36 by lia.
  assert (QB : 2 <= (len - 52) / 36 < 2^27) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  set (q := (len - 52) / 36) in *.
  step. step. step.
  rewrite ?(unsigned_lit q) by lia. rewrite ?(unsigned_lit (q * 36)) by lia.
  rewrite ?(unsigned_lit (len - 52)) by lia.
  rewrite ?(unsigned_lit (len - 52 - q * 36)) by (subst q; Z.div_mod_to_equations; lia).
  step. brq B4.
  2:{ ufail. }
  assert (M36 : (len - 52) mod 36 = 0) by (subst q; Z.div_mod_to_equations; lia).
  step. rewrite (unsigned_lit q) by lia. step. step.
  rewrite width_test by lia.
  destruct ((2 <=? q) && (q <=? 40)) eqn:B5; cbn [negb].
  2:{ ufail. }
  apply andb_true_iff in B5. destruct B5 as [B5a B5b]. apply Z.leb_le in B5a, B5b.
  step. rewrite (unsigned_lit q) by lia. rewrite land1. step. brq B6.
  2:{ ufail. }
  assert (UQ : up_nch len = q) by (apply up_nch_val; lia).
  destruct (HB B2 B3 ltac:(lia)) as [LEN BB].
  pose proof (bytes_at_bound _ _ _ _ BB) as BBB. rewrite LEN in BBB.
  pose proof (rd1 _ _ _ 12 BB ltac:(lia)) as HR. change (Z.to_nat 12) with 12%nat in HR.
  step. step. step. rewrite eqb_zxb by lia. brq B7.
  2:{ ufail. }
  clear HR.
  pose proof (rd1 _ _ _ 13 BB ltac:(lia)) as HR. change (Z.to_nat 13) with 13%nat in HR.
  step. step. step. rewrite eqb_zxb by lia. brq B8.
  2:{ ufail. }
  clear HR.
  pose proof (rd1 _ _ _ (len - 2) BB ltac:(lia)) as HR. replace (raw + (len - 2)) with (raw + len + -2) in HR by lia.
  step. step. step. step. rewrite eqb_zxb by lia. brq B9.
  2:{ ufail. }
  clear HR.
  pose proof (rd1 _ _ _ (len - 1) BB ltac:(lia)) as HR. replace (raw + (len - 1)) with (raw + len + -1) in HR by lia.
  step. step. step. rewrite eqb_zxb by lia. brq B10.
  2:{ ufail. }
  clear HR.
  assert (OK : up_ok raw out len bs = true).
  { rewrite up_ok_true. unfold inspect_byte. rewrite UQ. repeat split; lia. }
  destruct (HO OK) as (HW & HoutN & DOR). rewrite UQ in HW, HoutN, DOR.
  do 8 step.
  rewrite slli_srli33 by lia.
  assert (I0 : INVU m bs raw out q m 0).
  { split; [exact BB|]. split; [exact HW|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros i Hi. lia. }
  eapply up_outer with (K := Z.to_nat (q - 0)) (ch := 0) (nch := q) (len := len).
  all: first [ assumption | reflexivity | lia | (Z.div_mod_to_equations; lia) | rewrite LEN; reflexivity
             | (eapply INVU_idx; [exact I0 | lia])
             | (rewrite (unsigned_lit q) by lia; rewrite Z.add_0_r, swrap32_id by lia; reflexivity)
             | (rewrite ?(unsigned_lit q) by lia; rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?unsigned_lit by nia; nia)
             | (rewrite (unsigned_lit q) by lia; rewrite !Z.shiftl_mul_pow2 by lia;
                rewrite (unsigned_lit (q * 2 ^ 33)) by lia; rewrite Z.shiftr_div_pow2, Z.div_mul by lia;
                rewrite unsigned_lit by lia; lia) ].
Qed.
