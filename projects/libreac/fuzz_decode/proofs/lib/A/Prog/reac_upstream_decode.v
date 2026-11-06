From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA AsanKAProof reac_frame_inspect_c reac_decode_c reac_upstream_decode_c ReacDecodeLib.
Import ListNotations.
Open Scope Z_scope.

Definition rs_hold (A : Prop) : Prop := A.
Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => apply rs_hide in H
  | H : _ mod _ = _ |- _ => apply rs_hide in H end.

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

(* The four marker checks of the entry: each is one shadow check whose two paths (shadow byte zero, or non-zero
   and the access in bounds) meet at one pc. One lemma per check keeps the entry proof on one goal; running
   pshadow there doubled the goals at each check (16 copies of the rest of the entry). *)
Lemma shc1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x14 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y5 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 y5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) (sxb k) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81bcc) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81bbc) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA RA M SK CONT.
  pose proof (u64_range x14) as R14. pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  pshadow mm x14 EA M k SK MB; apply CONT.
Qed.

Lemma shc2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x14 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y5 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 y5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) (sxb k) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81bec) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81bdc) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA RA M SK CONT.
  pose proof (u64_range x14) as R14. pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  pshadow mm x14 EA M k SK MB; apply CONT.
Qed.

Lemma shc3 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x11 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y5 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 y5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) (sxb k) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81c10) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81c00) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA RA M SK CONT.
  pose proof (u64_range x11) as R11. pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  pshadow mm x11 EA M k SK MB; apply CONT.
Qed.

Lemma shc4 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x11 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y17 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (sxb k) x15 (Z_to_bv 64 2147450880) y17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81c30) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81c20) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA RA M SK CONT.
  pose proof (u64_range x11) as R11. pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  pshadow mm x11 EA M k SK MB; apply CONT.
Qed.

Lemma shld1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x31 + bv_unsigned x28 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y11 y13 y19 : word, bv_unsigned y13 = A ->
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 x12 y13 x14 x15 (Z_to_bv 64 2147450880) x17 x11 y19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81ca8) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81c90) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA RA M SK CONT.
  pose proof (u64_range x31) as R31. pose proof (u64_range x28) as R28.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  step. gen_add x31 x28 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H. rewrite G in H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step. step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT; exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. rewrite land7, U. step. rewrite (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT; exact U.
Qed.

Lemma shst1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (Q0 A3 : Z),
  bv_unsigned x12 = Q0 -> Q0 < 2^64 -> bv_unsigned x13 = A3 ->
  mrd rsegs mm (wa (Q0 / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ Q0 mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A3) = Some b ->
  (forall y13 y19 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (zxb b) x12 y13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 y19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81cbc) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81ca8) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b Q0 A3 EQ0 RQ EA3 M SK Fsrc CONT.
  pose proof (u64_range x12) as R12. pose proof (Z.mod_pos_bound Q0 8 ltac:(lia)) as MB.
  step. gen_shr x12 g G. rewrite EQ0 in G.
  step. gen_addi g h H. rewrite G in H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x13 _ _ Fsrc EA3) as R. step. clear R.
  step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. rewrite land7, EQ0. step. rewrite (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma shld2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x11 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y13 y19 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 y13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 y19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81cd8) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81cc8) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA RA M SK CONT.
  pose proof (u64_range x11) as R11. pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  step. gen_shr x11 g G. rewrite EA in G.
  step. gen_addi g h H. rewrite G in H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. rewrite land7, EA. step. rewrite (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma shst2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (Q0 A2 : Z),
  bv_unsigned x12 = Q0 -> Q0 + 1 < 2^64 -> bv_unsigned x11 = A2 ->
  mrd rsegs mm (wa ((Q0 + 1) / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ (Q0 + 1) mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A2) = Some b ->
  (forall y13 y19 y20 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (zxb b) x12 y13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 y19 y20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81cf0) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81cd8) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b Q0 A2 EQ0 RQ EA2 M SK Fsrc CONT.
  pose proof (u64_range x12) as R12. pose proof (Z.mod_pos_bound (Q0 + 1) 8 ltac:(lia)) as MB.
  step. gen_addi x12 w U. rewrite EQ0 in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H. rewrite G in H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x11 _ _ Fsrc EA2) as R. step. clear R.
  step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. rewrite land7, U. step. rewrite (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma shld3 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x8 + bv_unsigned x28 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y11 y13 y19 : word, bv_unsigned y13 = A ->
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 x12 y13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 y19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81d08) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81cf4) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA RA M SK CONT.
  pose proof (u64_range x8) as R8. pose proof (u64_range x28) as R28.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  step. gen_add x8 x28 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H. rewrite G in H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT; exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. rewrite land7, U. step. rewrite (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT; exact U.
Qed.

Lemma shst3 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (Q0 A3 : Z),
  bv_unsigned x12 = Q0 -> Q0 + 2 < 2^64 -> bv_unsigned x13 = A3 ->
  mrd rsegs mm (wa ((Q0 + 2) / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ (Q0 + 2) mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A3) = Some b ->
  (forall y11 y19 y20 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 x12 (zxb b) x14 x15 (Z_to_bv 64 2147450880) x17 x18 y19 y20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81d20) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81d08) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b Q0 A3 EQ0 RQ EA3 M SK Fsrc CONT.
  pose proof (u64_range x12) as R12. pose proof (Z.mod_pos_bound (Q0 + 2) 8 ltac:(lia)) as MB.
  step. gen_addi x12 w U. rewrite EQ0 in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H. rewrite G in H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x13 _ _ Fsrc EA3) as R. step. clear R.
  step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. rewrite land7, U. step. rewrite (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Section UP.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (raw out len lo : Z).

Definition PostU : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if up_ok raw out len bs then 12 else -1))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    (if up_ok raw out len bs
     then munch [(bv_unsigned sp - 48, bv_unsigned sp); (out, out + 36 * up_nch len)] m m' /\
          bytes_at rsegs m' out (braid_out bs (up_nch len) 12)
     else munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m').

Local Notation SP := (bv_unsigned sp).
Local Notation FRU mk := (rw_cells rsegs mk (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

Hypothesis Hsp : lo + 48 <= SP.
Hypothesis Hlo : 0 <= lo.

Lemma up_exit : forall (m1 : word -> option byte) (r : Z)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
  FRU m1 -> stk rsegs m1 lo (SP + -48) -> wmono rsegs m m1 ->
  r = (if up_ok raw out len bs then 12 else -1) ->
  (if up_ok raw out len bs
   then munch [(SP - 48, SP); (out, out + 36 * up_nch len)] m m1 /\
        bytes_at rsegs m1 out (braid_out bs (up_nch len) 12)
   else munch [(SP - 48, SP)] m m1) ->
  evt rsegs PostU (MS (mkR x1 (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 r) x14 x15 x16 x17
      x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x81b74) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 r x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 HF ST WM Er HM.
  pose proof (u64_range sp) as Rsp.
  do 9 step.
  apply evt_done. unfold PostU. exists x5, x6, x7, x11, x12, (Z_to_bv 64 r), x14, x15, x16, x17, x28, x29, x30, x31, m1.
  split; [subst r; reflexivity|]. split; [exact WM|]. split.
  - pose proof (stk_release rsegs m1 lo (SP + -48) _ ST HF ltac:(lia)) as ST2.
    cbn [cells_size csize Nat.add] in ST2. replace (SP + -48 + Z.of_nat 48) with SP in ST2 by lia. exact ST2.
  - exact HM.
Qed.

Lemma up_fail : forall (m1 : word -> option byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
  FRU m1 -> stk rsegs m1 lo (SP + -48) -> wmono rsegs m m1 -> munch [(SP - 48, SP)] m m1 ->
  up_ok raw out len bs = false ->
  evt rsegs PostU (MS (mkR x1 (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 (-1)) x14 x15 x16 x17
      x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x81b74) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 HF ST WM MU E.
  eapply up_exit; [exact HF | exact ST | exact WM | rewrite E; reflexivity | rewrite E; exact MU].
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
Hypothesis DOS : out + 36 * nch <= SP - 48 \/ SP <= out.
Hypothesis AR : addressable m raw len.
Hypothesis AO : addressable m out (36 * nch).
Hypothesis APW : forall x, SP - 48 <= x < SP -> app_mem x.
Hypothesis OK : up_ok raw out len bs = true.

Local Notation N := (36 * nch).

Definition INVU (mk : word -> option byte) (j : Z) : Prop :=
  bytes_at rsegs mk raw bs /\ FRU mk /\ stk rsegs mk lo (SP + -48) /\ wr_at rsegs mk out N /\
  munch [(SP + -48, SP); (out, out + N)] m mk /\ wmono rsegs m mk /\
  (forall i, 0 <= i < j -> mrd rsegs mk (Z_to_bv 64 (out + i)) = Some (braid_byte bs nch 12 i)).

Lemma INVU_idx : forall mk j j', INVU mk j -> j = j' -> INVU mk j'.
Proof. intros; subst; assumption. Qed.

Lemma INVU_addr : forall mk j p n, INVU mk j -> addressable m p n -> addressable mk p n.
Proof.
  intros mk j p n (_ & _ & _ & _ & MU & _) A. eapply addr_munch; [exact A | exact MU |].
  intros i Hi. destruct A as (_ & _ & _ & HA). destruct (HA i Hi) as (Ha & _).
  pose proof (shadow_not_app _ Ha) as NA. cbn [outside]. split; [|split; [|exact I]].
  - intros W. apply NA, APW. lia.
  - intros W. apply NA. destruct AO as (_ & _ & _ & HO).
    destruct (HO ((p + i) / 8 + ASAN_K - out) ltac:(lia)) as (Ho & _).
    replace (out + ((p + i) / 8 + ASAN_K - out)) with ((p + i) / 8 + ASAN_K) in Ho by lia. exact Ho.
Qed.

Lemma src_bound : forall ch s k o, 0 <= ch < nch -> 0 <= s < 12 -> 0 <= k < 3 -> o = boff (ch mod 2) k ->
  0 <= 50 + (3 * (s * nch + (ch - ch mod 2)) + o) < len.
Proof.
  intros ch s k o Hch Hs Hk Ho.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (s * nch <= 11 * nch) by nia.
  assert (0 <= s * nch) by nia.
  assert (ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  assert (0 <= o <= 5) by (subst o; unfold boff; destruct (k =? 0), (k =? 1); lia).
  nia.
Qed.

Lemma INVU_rd : forall mk j ch s k o, INVU mk j -> 0 <= ch < nch -> 0 <= s < 12 -> 0 <= k < 3 ->
  o = boff (ch mod 2) k ->
  mrd rsegs mk (wa (raw + (50 + (3 * (s * nch + (ch - ch mod 2)) + o)))) = Some (braid_byte bs nch 12 (3 * (ch * 12 + s) + k)).
Proof.
  intros mk j ch s k o (HB & _) Hch Hs Hk Ho.
  pose proof (src_bound ch s k o Hch Hs Hk Ho) as SB.
  rewrite braid_byte_at by lia. rewrite (braid_pos_boff s ch nch k Hk), <- Ho.
  pose proof (bytes_nth mk raw bs (Z.to_nat (50 + (3 * (s * nch + (ch - ch mod 2)) + o))) HB ltac:(rewrite Hlen; lia)) as R.
  rewrite Z2Nat.id in R by lia. exact R.
Qed.

Lemma INVU_shr : forall mk j ch s k o, INVU mk j -> 0 <= ch < nch -> 0 <= s < 12 -> 0 <= k < 3 ->
  o = boff (ch mod 2) k ->
  exists kb, mrd rsegs mk (wa ((raw + (50 + (3 * (s * nch + (ch - ch mod 2)) + o))) / 8 + ASAN_K)) = Some kb /\
    (bv_signed kb = 0 \/ (raw + (50 + (3 * (s * nch + (ch - ch mod 2)) + o))) mod 8 < bv_signed kb).
Proof.
  intros mk j ch s k o I Hch Hs Hk Ho.
  pose proof (src_bound ch s k o Hch Hs Hk Ho) as SB.
  destruct (addr_one mk raw len (50 + (3 * (s * nch + (ch - ch mod 2)) + o)) (INVU_addr mk j raw len I AR) SB)
    as (_ & kb & M & S). exists kb. split; assumption.
Qed.

Lemma INVU_sho : forall mk j q, INVU mk j -> 0 <= q < N ->
  exists kb, mrd rsegs mk (wa ((out + q) / 8 + ASAN_K)) = Some kb /\
    (bv_signed kb = 0 \/ (out + q) mod 8 < bv_signed kb).
Proof.
  intros mk j q I Hq.
  destruct (addr_one mk out N q (INVU_addr mk j out N I AO) Hq) as (_ & kb & M & S). exists kb. split; assumption.
Qed.

Lemma INVU_wr : forall mk j q, INVU mk j -> 0 <= q < N -> store_ok rsegs mk (Z_to_bv 64 (out + q)) 1 = true.
Proof.
  intros mk j q (_ & _ & _ & HW & _) Hq. change (Z_to_bv 64 (out + q)) with (wa (out + q)).
  apply (wr_at_store_ok rsegs mk out N q 1 HW); lia.
Qed.

Lemma INVU_store : forall mk j0 j j2, INVU mk j0 -> j0 = j -> 0 <= j < N -> j2 = j + 1 ->
  INVU (write_to_mem mk (Z_to_bv 64 (out + j)) [braid_byte bs nch 12 j]) j2.
Proof.
  intros mk j0 j j2 (HB & HF & ST & HW & MU & WM & HP) E Hj E2. subst j0 j2.
  change (Z_to_bv 64 (out + j)) with (wa (out + j)).
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - apply bytes_at_write_other; [exact HB | lia | cbn; lia | rewrite Hlen; cbn; lia].
  - apply rw_cells_frame; [exact HF | lia | cbn; lia | cbn; lia].
  - apply stk_write; [exact ST | lia | cbn; lia].
  - apply wr_at_write. exact HW.
  - apply munch_write; [exact MU | lia | cbn; lia | cbn [inside]; cbn; lia].
  - apply wmono_write. exact WM.
  - intros i Hi. change (wa (out + j)) with (Z_to_bv 64 (out + j)).
    rewrite mrd_write1 by lia.
    destruct (Z.eqb_spec (out + i) (out + j)) as [E|E].
    + replace i with j by lia. reflexivity.
    + apply HP. lia.
Qed.

Lemma INVU_out : forall mk, INVU mk N -> bytes_at rsegs mk out (braid_out bs nch 12).
Proof.
  intros mk (_ & _ & _ & _ & _ & _ & HP). unfold braid_out.
  apply bytes_at_of_fun; [lia | lia |]. intros i Hi. apply HP. lia.
Qed.

Ltac do_store I0 I1 jj :=
  rewrite ?le1_zxb;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mk ?a ?b) _) =>
    assert (I1 : INVU (write_to_mem mk a b) (jj + 1)) by (eapply INVU_store; [exact I0 | lia | lia | lia]);
    let m2 := fresh "m" in set (m2 := write_to_mem mk a b) in *; clearbody m2; clear I0
  end.

Lemma up_inner : forall (ch : Z) (x5 x6 x8 x9 x14 x15 x17 x29 x30 x31 : word),
  0 <= ch < nch ->
  bv_unsigned x5 = 3 * nch -> bv_unsigned x6 = raw + 50 ->
  bv_unsigned x8 = raw + 50 + (1 + ch mod 2) -> bv_unsigned x9 = 5 * (ch mod 2) ->
  bv_unsigned x14 = ch -> bv_unsigned x15 = nch -> bv_unsigned x17 = ch ->
  bv_unsigned x29 = ch mod 2 + 1 -> bv_unsigned x30 = ch mod 2 + 3 ->
  bv_unsigned x31 = raw + 50 + (3 + ch mod 2) ->
  (forall (m2 : word -> option byte) (y7 y10 y11 y12 y13 y18 y19 y20 y28 : word),
     bv_unsigned y12 = out + 3 * (ch * 12 + 12) -> INVU m2 (3 * (ch * 12 + 12)) ->
     evt rsegs PostU (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 y7 x8 x9 y10 y11 y12 y13 x14 x15 (Z_to_bv 64 2147450880) x17 y18 y19 y20 s5 s6 s7 s8 s9 s10 s11 y28 x29 x30 x31) F (Z_to_bv 64 0x81d88) fc None m2 (seg_rom rsegs))) ->
  forall (K : nat) (s : Z) (m1 : word -> option byte) (x7 x10 x11 x12 x13 x18 x19 x20 x28 : word),
  Z.to_nat (12 - s) = K -> 0 <= s < 12 -> bv_unsigned x7 = 12 - s ->
  bv_unsigned x11 = out + 3 * (ch * 12 + s) -> bv_unsigned x12 = out + 3 * (ch * 12 + s) ->
  bv_unsigned x28 = 3 * (ch - ch mod 2) + 3 * nch * s ->
  INVU m1 (3 * (ch * 12 + s)) ->
  evt rsegs PostU (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x81c90) fc None m1 (seg_rom rsegs)).
Proof.
  intros ch x5 x6 x8 x9 x14 x15 x17 x29 x30 x31 Hch H5 H6 H8 H9 H14 H15 H17 H29 H30 H31 CONT K.
  pose proof (u64_range sp) as Rsp.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (Hc2 : ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (Hc0 : 0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  assert (ch * 12 <= (nch - 1) * 12) by nia.
  apply wv in H14, H15, H17, H29, H30. subst x14 x15 x17 x29 x30.
  induction K as [K IH] using lt_wf_ind.
  intros s m1 x7 x10 x11 x12 x13 x18 x19 x20 x28 HK Hs H7 H11 H12 H28 I0.
  apply wv in H11. subst x11.
  assert (Hsn : s * nch <= 11 * nch) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (Hsn0 : 0 <= s * nch) by nia.
  assert (Hq0 : 0 <= 3 * (ch * 12 + s) /\ 3 * (ch * 12 + s) + 2 < 36 * nch) by nia.
  (* L1: load src k0 *)
  pose proof (INVU_shr m1 _ ch s 0 (3 + ch mod 2) I0 Hch Hs ltac:(lia) ltac:(reflexivity)) as (k0 & MK0 & SK0).
  unfold ASAN_K in MK0.
  pose proof (src_bound ch s 0 (3 + ch mod 2) Hch Hs ltac:(lia) ltac:(reflexivity)) as SB0.
  eapply shld1; [ | | exact MK0 | exact SK0 | intros y11a y13a y19a Ey13a ].
  { rewrite H31, H28. ring. }
  { lia. }
  (* L2: store-shadow k0 + load src byte k0 *)
  pose proof (INVU_sho m1 _ (3 * (ch * 12 + s)) I0 ltac:(lia)) as (ks0 & MS0 & SKs0).
  unfold ASAN_K in MS0.
  pose proof (INVU_rd m1 _ ch s 0 (3 + ch mod 2) I0 Hch Hs ltac:(lia) ltac:(reflexivity)) as RD0.
  eapply shst1; [ exact H12 | lia | exact Ey13a | exact MS0 | exact SKs0 | exact RD0 | intros y13b y19b ].
  clear SK0 SKs0.
  (* store k0: add a3,t3,s1 ; sb a1,0(s2) ; add a1,t1,a3 *)
  pose proof (INVU_wr m1 _ (3 * (ch * 12 + s)) I0 ltac:(lia)) as HWok0.
  step. gen_add x28 x9 wa3 Ua3.
  step. clear HWok0.
  replace (3 * (ch * 12 + s) + 0) with (3 * (ch * 12 + s)) by lia.
  do_store I0 I1 (3 * (ch * 12 + s)).
  step. gen_add x6 wa3 wa1 Ua1.
  (* L3: load src k1, addr a1 = A2 *)
  pose proof (INVU_shr _ _ ch s 1 (5 * (ch mod 2)) I1 Hch Hs ltac:(lia) ltac:(reflexivity)) as (k1 & MK1 & SK1).
  unfold ASAN_K in MK1.
  eapply shld2; [ | | exact MK1 | exact SK1 | intros y13c y19c ].
  { rewrite Ua1, H6, Ua3, H28, H9. ring. }
  { pose proof (src_bound ch s 1 (5 * (ch mod 2)) Hch Hs ltac:(lia) ltac:(reflexivity)). lia. }
  (* L4: store-shadow k1 + load src byte k1 *)
  pose proof (INVU_sho _ _ (3 * (ch * 12 + s) + 1) I1 ltac:(lia)) as (ks1 & MS1 & SKs1).
  unfold ASAN_K in MS1.
  replace (out + (3 * (ch * 12 + s) + 1)) with (out + 3 * (ch * 12 + s) + 1) in MS1, SKs1 by lia.
  pose proof (INVU_rd _ _ ch s 1 (5 * (ch mod 2)) I1 Hch Hs ltac:(lia) ltac:(reflexivity)) as RD1.
  eapply shst2; [ exact H12 | lia | | exact MS1 | exact SKs1 | exact RD1 | intros y13d y19d y20d ].
  { rewrite Ua1, H6, Ua3, H28, H9. ring. }
  clear SK1 SKs1.
  (* store k1: sb a1,1(s2) ; add a3,s0,t3 handled by shld3 *)
  pose proof (INVU_wr _ _ (3 * (ch * 12 + s) + 1) I1 ltac:(lia)) as HWok1.
  step. clear HWok1.
  do_store I1 I2 (3 * (ch * 12 + s) + 1).
  (* L5: load src k2, addr a3 = s0 + t3 = A3 *)
  pose proof (INVU_shr _ _ ch s 2 (1 + ch mod 2) I2 Hch Hs ltac:(lia) ltac:(reflexivity)) as (k2 & MK2 & SK2).
  unfold ASAN_K in MK2.
  eapply shld3; [ | | exact MK2 | exact SK2 | intros y11e y13e y19e Ey13e ].
  { rewrite H8, H28. ring. }
  { pose proof (src_bound ch s 2 (1 + ch mod 2) Hch Hs ltac:(lia) ltac:(reflexivity)). lia. }
  (* L6: store-shadow k2 + load src byte k2 *)
  pose proof (INVU_sho _ _ (3 * (ch * 12 + s) + 2) I2 ltac:(lia)) as (ks2 & MS2 & SKs2).
  unfold ASAN_K in MS2.
  replace (out + (3 * (ch * 12 + s) + 2)) with (out + 3 * (ch * 12 + s) + 2) in MS2, SKs2 by lia.
  pose proof (INVU_rd _ _ ch s 2 (1 + ch mod 2) I2 Hch Hs ltac:(lia) ltac:(reflexivity)) as RD2.
  eapply shst3; [ exact H12 | lia | exact Ey13e | exact MS2 | exact SKs2 | exact RD2 | intros y11f y19f y20f ].
  clear SK2 SKs2.
  (* store k2: sb a3,2(s2) ; loop tail *)
  pose proof (INVU_wr _ _ (3 * (ch * 12 + s) + 2) I2 ltac:(lia)) as HWok2.
  step. clear HWok2.
  do_store I2 I3 (3 * (ch * 12 + s) + 2).
  clear MK0 MK1 MK2 RD0 RD1 RD2 MS0 MS1 MS2 SB0 Ey13a Ey13e Ua1 Ua3.
  (* loop tail: add t3,t3,t0 ; addi t2,t2,-1 ; addi a2,a2,3 ; addi a1,s2,3 ; beqz t2 *)
  step. gen_add x28 x5 wt3 Ut3.
  step.
  step. gen_addi x12 wa2 Ua2.
  step.
  step.
  brq BR.
  - (* exit: s = 11 *)
    assert (Es : s = 11) by (rewrite H7 in BR; lia).
    step.
    eapply CONT.
    { rewrite !unsigned_lit by lia. lia. }
    { eapply INVU_idx; [exact I3 | lia]. }
  - (* loop: s+1 *)
    step.
    eapply (IH (Z.to_nat (12 - (s + 1))) ltac:(lia) (s + 1)).
    all: clear CONT IH Hsn Hsn0.
    { reflexivity. }
    { lia. }
    { rewrite unsigned_lit by lia. lia. }
    { rewrite unsigned_lit by lia. lia. }
    { rewrite Ua2, H12. lia. }
    { rewrite Ut3, H28, H5. ring. }
    { eapply INVU_idx; [exact I3 | lia]. }
Qed.

Lemma up_outer : forall (K : nat) (ch : Z) (m1 : word -> option byte)
    (x5 x6 x7 x8 x9 x10 x11 x12 x13 x18 x19 x20 x28 x29 x30 x31 : word),
  Z.to_nat (nch - ch) = K -> 0 <= ch < nch ->
  bv_unsigned x5 = 3 * nch -> bv_unsigned x6 = raw + 50 -> bv_unsigned x12 = out + 3 * (ch * 12) ->
  INVU m1 (3 * (ch * 12)) ->
  evt rsegs PostU (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13
        (Z_to_bv 64 ch) (Z_to_bv 64 nch) (Z_to_bv 64 2147450880) (Z_to_bv 64 ch) x18 x19 x20
        s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x81c58) fc None m1 (seg_rom rsegs)).
Proof.
  induction K as [K IH] using lt_wf_ind.
  intros ch m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x18 x19 x20 x28 x29 x30 x31 HK Hch H5 H6 H12 I0.
  pose proof (u64_range sp) as Rsp.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (Hc0 : 0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  assert (ch * 12 <= (nch - 1) * 12) by nia.
  assert (P : ch mod 2 = 0 \/ ch mod 2 = 1) by lia.
  apply wv in H5, H6, H12. subst x5 x6 x12.
  do 14 step.
  rewrite (unsigned_lit ch) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (ch * 2 ^ 2)) by lia.
  rewrite land_m8, land_m2 by lia. rewrite !land1.
  assert (EQ5 : bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned
    (v_sltiu (Z_to_bv 64 (ch mod 2)) 1) + -1))) 5)) = 5 * (ch mod 2))
    by (destruct P as [P|P]; rewrite P; vm_compute; reflexivity).
  eapply (up_inner ch) with (K := Z.to_nat (12 - 0)) (s := 0).
  all: lazymatch goal with
       | |- (forall _ : word -> option byte, _) => idtac
       | |- INVU _ _ => eapply INVU_idx; [exact I0 | lia]
       | _ => first
         [ lia
         | reflexivity
         | (rewrite unsigned_lit by lia; lia)
         | (rewrite unsigned_lit by lia; exact EQ5)
         | (rewrite (unsigned_lit (8 * (ch * 2 ^ 2 / 8))) by (Z.div_mod_to_equations; lia);
            rewrite (unsigned_lit (2 * (ch / 2))) by (Z.div_mod_to_equations; lia);
            rewrite unsigned_lit by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia) ]
       end.
  intros m2 y7 y10 y11 y12 y13 y18 y19 y20 y28 H12' I2.
  apply wv in H12'. subst y12.
  (* ch-tail at 0x81d88: sext.w a1,a5 ; addiw a7,a7,1 ; addi a4,a4,1 ; bne a7,a1 *)
  step. rewrite (unsigned_lit nch) by lia. rewrite swrap32_id by lia.
  step. step. step.
  rewrite (unsigned_lit ch) by lia. rewrite swrap32_id by lia.
  brq BR.
  - (* exit: ch = nch - 1 *)
    assert (Ec : ch = nch - 1) by lia.
    step. step.
    destruct I2 as (BB2 & FR2 & ST2 & WA2 & MU2 & WM2 & HP2).
    eapply up_exit with (r := 12);
      [ exact FR2 | exact ST2 | exact WM2 | rewrite OK; reflexivity | ].
    rewrite OK. rewrite Hnchdef. split.
    + replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. exact MU2.
    + apply INVU_out. eapply INVU_idx;
        [ exact (conj BB2 (conj FR2 (conj ST2 (conj WA2 (conj MU2 (conj WM2 HP2)))))) | nia ].
  - (* loop: ch + 1 *)
    eapply (IH (Z.to_nat (nch - (ch + 1))) ltac:(lia) (ch + 1)).
    all: try (clear IH).
    { reflexivity. }
    { lia. }
    { rewrite unsigned_lit by lia. lia. }
    { rewrite unsigned_lit by lia. lia. }
    { rewrite unsigned_lit by lia. nia. }
    { eapply INVU_idx; [exact I2 | nia]. }
Qed.

End UP.


Ltac ufail sp :=
  eapply up_fail; first
  [ eassumption
  | (replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; eassumption)
  | (apply not_true_iff_false; rewrite up_ok_true;
     intros (HUa & HUb & HUc & HUd & HUe & HUf & HUg);
     try (apply up_nch_pos in HUc; destruct HUc as (HVa & HVb & HVc & HVd & HVe));
     unfold inspect_byte in *; first [ lia | (Z.div_mod_to_equations; lia) ]) ].

Theorem reac_upstream_decode_holds : reac_upstream_decode_contract.
Proof.
  unfold reac_upstream_decode_contract, REAC_UPSTREAM_DECODE, REAC_UPSTREAM_DECODE_D, DIV36_MAGIC_AT, DIV36_MAGIC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw out lo E0 E2 Rraw Rout Rlen HMG HB HO ST LO DR DO DM APS1 APS2 CELLS SGOT AR AO.
  assert (Ea0 : bv_unsigned a0 = raw) by (rewrite E0; apply unsigned_lit; lia).
  assert (Ea2 : bv_unsigned a2 = out) by (rewrite E2; apply unsigned_lit; lia).
  pose proof (u64_range a1) as Ra1.
  set (len := bv_unsigned a1) in *.
  assert (A1 : a1 = Z_to_bv 64 len) by (symmetry; apply Z_to_bv_bv_unsigned).
  clearbody len. subst a1.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (conj HMG CELLS) as PK. clear HMG CELLS.
  carve_frame 48%nat ST.
  do 7 step.
  destruct PK as (HMG & CELLS).
  match goal with MU' : munch _ m ?mm |- _ => rename MU' into MU1; rename mm into m0 end.
  pose proof (bytes_tp m m0 _ _ 66360 (le8 (Z_to_bv 64 16397105843297379215)) MU1
    ltac:(rewrite length_le8; unfold off_stk in DM; lia) HMG) as HMG0.
  assert (CELLS0 : asan_cells m0) by
    (eapply asan_cells_munch; [exact CELLS | exact MU1 |
     unfold MIDEND, GOT_CELL_K; unfold off_stk, GOT_CELL_K, MIDEND in SGOT; lia]).
  pose proof CELLS0 as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  pose proof (rd_all _ _ _ HMG0) as HRM. rewrite length_le8 in HRM.
  pose proof (rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 2 step.
  step. brq B1. { ufail sp. }
  step. if_cases B2. { zify_cond B2; ufail sp. }
  step. if_cases B3. { zify_cond B3; ufail sp. }
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
  step. brq B4. 2:{ ufail sp. }
  assert (M36 : (len - 52) mod 36 = 0) by (subst q; Z.div_mod_to_equations; lia).
  step. rewrite (unsigned_lit q) by lia. step. step.
  rewrite width_test by lia.
  destruct ((2 <=? q) && (q <=? 40)) eqn:B5; cbn [negb].
  2:{ ufail sp. }
  apply andb_true_iff in B5. destruct B5 as [B5a B5b]. apply Z.leb_le in B5a, B5b.
  step. rewrite (unsigned_lit q) by lia. rewrite land1. step. brq B6.
  2:{ ufail sp. }
  assert (UQ : up_nch len = q) by (apply up_nch_val; lia).
  step. step. step.
  zify_cond B2. zify_cond B3.
  assert (RN : raw <> 0) by (rewrite Ea0 in B2; lia).
  assert (ON : out <> 0) by (rewrite Ea2 in B3; lia).
  assert (UQ0 : 0 <= up_nch len) by (rewrite UQ; lia).
  destruct (HB RN ON UQ0) as [LEN BB].
  clear HB.
  specialize (DR RN ON UQ0). unfold off_stk in DR.
  specialize (AR RN ON UQ0).
  pose proof (bytes_at_bound _ _ _ _ BB) as BBB. rewrite LEN, Z2Nat.id in BBB by lia.
  pose proof (bytes_tp m m0 _ _ raw bs MU1 ltac:(rewrite LEN, Z2Nat.id by lia; lia) BB) as BB0.
  assert (AR0 : addressable m0 raw len).
  { eapply addr_munch; [exact AR | exact MU1 |].
    intros i Hi. destruct (addr_one m raw len i AR Hi) as (Hap & _).
    cbn [outside]. split; [|exact I]. intros W.
    apply (shadow_not_app (raw + i) Hap).
    apply (app_win (bv_unsigned sp) 48); [lia | exact APS1 | exact APS2 | lia]. }
  assert (RLT : raw + len <= 0x800000000000) by
    (destruct AR as (_ & _ & H & _); unfold APPMEM_END in H; exact H).
  destruct (addr_one m0 raw len 12 AR0 ltac:(lia)) as (_ & k12 & M12 & SK12). unfold ASAN_K in M12.
  destruct (addr_one m0 raw len 13 AR0 ltac:(lia)) as (_ & k13 & M13 & SK13). unfold ASAN_K in M13.
  destruct (addr_one m0 raw len (len - 2) AR0 ltac:(lia)) as (_ & k90 & M90 & SK90). unfold ASAN_K in M90.
  destruct (addr_one m0 raw len (len - 1) AR0 ltac:(lia)) as (_ & k91 & M91 & SK91). unfold ASAN_K in M91.
  pose proof (bytes_nth m0 raw bs 12 BB0 ltac:(rewrite LEN; lia)) as F12. change (Z.of_nat 12) with 12 in F12.
  pose proof (bytes_nth m0 raw bs 13 BB0 ltac:(rewrite LEN; lia)) as F13. change (Z.of_nat 13) with 13 in F13.
  pose proof (bytes_nth m0 raw bs (Z.to_nat (len - 2)) BB0 ltac:(rewrite LEN; lia)) as F90.
  rewrite Z2Nat.id in F90 by lia.
  pose proof (bytes_nth m0 raw bs (Z.to_nat (len - 1)) BB0 ltac:(rewrite LEN; lia)) as F91.
  rewrite Z2Nat.id in F91 by lia.
  assert (Elen : len = 52 + 36 * q) by (clear - M36; subst q; Z.div_mod_to_equations; lia).
  rs_hide_all. apply rs_hide in HO. apply rs_hide in DO. apply rs_hide in AO.
  (* check 1: raw+12 *)
  step. gen_addi a0 w12 U12. rewrite Ea0 in U12.
  eapply shc1; [ exact U12 | lia | exact M12 | exact SK12 | intros y5a ].
  pose proof (rdw0 m0 w12 _ _ F12 ltac:(lia)) as R; step; clear R.
  step; step; rewrite eqb_zxb by lia; brq B7; [|ufail sp].
  (* check 2: raw+13 *)
  step; gen_addi a0 w13 U13; rewrite Ea0 in U13.
  eapply shc2; [ exact U13 | lia | exact M13 | exact SK13 | intros y5b ].
  pose proof (rdw0 m0 w13 _ _ F13 ltac:(lia)) as R; step; clear R.
  step; step; rewrite eqb_zxb by lia; brq B8; [|ufail sp].
  (* check 3: raw+len-2 *)
  step; gen_addi a0 w3 U3; rewrite Ea0 in U3.
  step; gen_addi w3 w3b U3b; rewrite U3 in U3b;
    replace (raw + len + -2) with (raw + (len - 2)) in U3b by lia.
  eapply shc3; [ exact U3b | lia | exact M90 | exact SK90 | intros y5c ].
  pose proof (rdw0 m0 w3b _ _ F90 ltac:(lia)) as R; step; clear R.
  step; step; rewrite eqb_zxb by lia; brq B9; [|ufail sp].
  (* check 4: raw+len-1 *)
  step; gen_addi w3 w4 U4; rewrite U3 in U4;
    replace (raw + len + -1) with (raw + (len - 1)) in U4 by lia.
  eapply shc4; [ exact U4 | lia | exact M91 | exact SK91 | intros y17d ].
  pose proof (rdw0 m0 w4 _ _ F91 ltac:(lia)) as R; step; clear R.
  step; step; rewrite eqb_zxb by lia; brq B10; [|ufail sp].
  (* success: up_ok = true; set up INVU and run the loop *)
  all: assert (OK : up_ok raw out len bs = true) by
    (rewrite up_ok_true; unfold inspect_byte; rewrite UQ; repeat split; lia).
  all: unfold rs_hold in HO, DO, AO.
  all: destruct (HO OK) as (HW & HoutN' & DOR'); rewrite UQ in HW, HoutN', DOR'; clear HO.
  all: specialize (DO OK); unfold off_stk in DO; rewrite UQ in DO.
  all: specialize (AO OK); rewrite UQ in AO.
  all: assert (HW1 : wr_at rsegs m0 out (36 * q)) by (eapply wr_at_transport; [exact HW | exact WM]).
  all: rs_hide_all.
  all: do 4 step.
  all: rewrite slli_srli33 by lia.
  all: do 3 step.
  all: eapply up_outer with (nch := q) (K := Z.to_nat (q - 0)) (ch := 0)
    (m := m) (bs := bs) (raw := raw) (out := out) (len := len) (lo := lo).
  all: lazymatch goal with
       | |- context [INVU] =>
           replace (3 * (0 * 12)) with 0 by lia; unfold INVU;
           split; [exact BB0 | split; [exact FR | split; [exact ST |
           split; [exact HW1 | split; [apply munch_extend; exact MU1 |
           split; [exact WM | intros i Hi; lia ]]]]]]
       | _ => first
         [ exact OK | exact HW1 | exact AR | exact AO | exact DO | exact DOR' | exact HoutN'
         | exact B6 | exact UQ | exact LEN | exact LO | exact Hlo | reflexivity
         | (rewrite Ea2; lia)
         | (rewrite Ea0; rewrite unsigned_lit by lia; lia)
         | (rewrite (unsigned_lit q) by lia; rewrite Z.shiftl_mul_pow2 by lia; rewrite unsigned_lit by lia; lia)
         | (intros x Hx; apply (app_win (bv_unsigned sp) 48); [lia | exact APS1 | exact APS2 | lia])
         | lia
         | (subst q; Z.div_mod_to_equations; lia) ]
         || (lazymatch goal with |- ?g => fail 0 "UNSOLVED:" g end)
       end.
Qed.
