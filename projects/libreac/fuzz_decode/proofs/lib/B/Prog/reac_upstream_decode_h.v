From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA AsanKAProof reac_frame_inspect_c reac_decode_c reac_upstream_decode_c ReacDecodeLib.
Import ListNotations.
Open Scope Z_scope.

Definition boff (c k : Z) : Z := if k =? 0 then 3 + c else if k =? 1 then 5 * c else 1 + c.

Lemma braid_pos_boff : forall s ch nch k, 0 <= k < 3 ->
  braid_pos s ch nch k = 3 * (s * nch + (ch - ch mod 2)) + boff (ch mod 2) k.
Proof.
  intros s ch nch k Hk. unfold braid_pos, boff.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  destruct (Z.eqb_spec (ch mod 2) 0) as [E|E];
  destruct (Z.eqb_spec k 0); destruct (Z.eqb_spec k 1); try rewrite E; lia.
Qed.

Lemma braid_byte_at : forall bs nch ns ch s k, 0 <= ch -> 0 <= s < ns -> 0 <= k < 3 ->
  braid_byte bs nch ns (3 * (ch * ns + s) + k) = nth (Z.to_nat (50 + braid_pos s ch nch k)) bs (Z_to_bv 8 0).
Proof.
  intros bs nch ns ch s k Hch Hs Hk. unfold braid_byte.
  destruct (braid_div ch s k ns Hch Hs Hk) as (D1 & D2 & D3 & D4). rewrite D1, D2, D3, D4. reflexivity.
Qed.

Lemma land_m8 : forall c, 0 <= c < 2^64 -> Z.land c 18446744073709551608 = 8 * (c / 8).
Proof.
  intros c Hc.
  replace 18446744073709551608 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 3))) by reflexivity.
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. cbn. lia.
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

Ltac pshadow m0 addrreg EA M k SK MB :=
  let g := fresh "g" in let h := fresh "h" in let G := fresh "G" in let H := fresh "H" in
  let R := fresh "R" in let C := fresh "C" in
  step; gen_shr addrreg g G; rewrite EA in G;
  step; gen_addi g h H; rewrite G in H;
  pose proof (rdw0 m0 h _ _ M ltac:(lia)) as R; step; clear R;
  step;
  destruct SK as [C|C];
  [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]
  | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb];
    step; rewrite land7, EA; step;
    rewrite (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb] ].

