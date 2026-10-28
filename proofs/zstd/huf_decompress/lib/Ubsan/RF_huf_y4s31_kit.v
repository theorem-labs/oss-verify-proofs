From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation fmem := (word -> option byte).

Lemma u_idx_bound : forall tl c b, 1 <= tl <= 12 ->
  0 <= (c ≪ b mod 18446744073709551616) ≫ (64 - tl) < 2^tl.
Proof.
  intros tl c b T.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.mod_pos_bound (c ≪ b) 18446744073709551616 ltac:(lia)) as M.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    rewrite <- Z.pow_add_r by lia. replace (64 - tl + tl) with 64 by lia. change (2^64) with 18446744073709551616. lia.
Qed.

Lemma u_shr62_small : forall v, 0 <= v < 2^61 -> (v + 2305843009213693952) ≫ 62 = 0.
Proof. intros v H. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

Lemma u_lxor_m1 : forall x, 0 <= x < 18446744073709551616 ->
  Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x H. change 18446744073709551615 with (Z.ones 64).
  assert (E : Z.lxor x (Z.ones 64) = Z.land (Z.lnot x) (Z.ones 64)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases n 64) as [L|L].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
    - rewrite Z.ones_spec_high by lia.
      destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
      assert (Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia).
      rewrite (Z.bits_above_log2 x n) by lia. reflexivity. }
  rewrite E, Z.land_ones by lia. unfold Z.lnot. rewrite Z.ones_equiv.
  symmetry. apply Z.mod_unique with (q := -1); lia.
Qed.

Lemma u_neg_desc_mod64 : forall tl mtl, 1 <= tl <= 12 -> 0 <= mtl <= 255 ->
  (bv_swrap 32 (0 - (tl + 256 * mtl)) mod 18446744073709551616) mod 64 = 64 - tl.
Proof.
  intros tl mtl T M. pose proof (neg_desc_mod64 tl mtl ltac:(lia) ltac:(lia)) as E.
  remember (bv_swrap 32 (0 - (tl + 256 * mtl))) as X eqn:EX. clear EX.
  Z.div_mod_to_equations. lia.
Qed.

Lemma u_bytes_skipn : forall segs m A bs k, 0 <= k <= Z.of_nat (length bs) -> bytes_at segs m A bs ->
  bytes_at segs m (A + k) (skipn (Z.to_nat k) bs).
Proof.
  intros segs m A bs k K H. rewrite <- (firstn_skipn (Z.to_nat k) bs) in H. apply bytes_at_app in H.
  destruct H as [_ H]. rewrite firstn_length_le in H by lia. rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma u_shamt : forall tl mtl, 1 <= tl <= 12 -> 0 <= mtl <= 255 ->
  Z.land (bv_swrap 32 (0 - (tl + 256 * mtl)) mod 18446744073709551616) 63 = 64 - tl.
Proof.
  intros tl mtl T M. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2^6) with 64.
  apply u_neg_desc_mod64; lia.
Qed.

Lemma u_desc_lo : forall tl mtl, 0 <= tl < 256 -> 0 <= mtl -> Z.land (tl + 256 * mtl) 255 = tl.
Proof.
  intros tl mtl T M. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2^8) with 256.
  rewrite (Z.mul_comm 256 mtl), Z.mod_add by lia. apply Z.mod_small; lia.
Qed.

Ltac uidx tl v :=
  lazymatch goal with |- context [Z.shiftr (Z.modulo (Z.shiftl ?c ?b) ?M) ?sh] =>
    replace sh with (64 - tl) by (first [repeat (rewrite Z.mod_small by lia); reflexivity | symmetry; apply u_neg_desc_mod64; lia]);
    let EV := fresh "EV" in let VR := fresh "VR" in
    remember (Z.shiftr (Z.modulo (Z.shiftl c b) M) (64 - tl)) as v eqn:EV;
    assert (VR : 0 <= v < 2^tl) by (subst v; apply u_idx_bound; lia);
    clear EV end.

Ltac urd DT cells cbs ECB v c EC :=
  lazymatch goal with CE : bytes_at usegs ?mm (DT + 4) cbs, SQ : 0 <= x2_seq c < 65536 |- _ =>
    let RC0 := fresh "RC" in let RC2 := fresh "RC" in let RC3 := fresh "RC" in let RCB := fresh "RC" in
    destruct (x2_cell_rd usegs mm (DT + 4) cells _ v c ltac:(rewrite <- ECB; exact CE)
                ltac:(lia) ltac:(lia) ltac:(lia) EC SQ) as (RC0 & RC2 & RC3 & RCB) end.

Ltac ubuf OUT LB :=
  lazymatch type of OUT with u8arr ?sg ?m ?A (map (Z_to_bv 8) ?b) =>
    lazymatch type of LB with Z.of_nat (length ?b0) = ?N =>
      let LB2 := fresh "LB" in
      assert (LB2 : Z.of_nat (length b) = N) by (rewrite ?Zupd_length; exact LB);
      let b2 := fresh "buf" in let Eb := fresh "Eb" in
      remember b as b2 eqn:Eb; clear Eb; clear LB; rename LB2 into LB end end.

Ltac upack :=
  repeat match goal with
  | |- _ /\ _ => split
  | |- exists b, u8arr _ _ _ (map (Z_to_bv 8) b) /\ _ => eexists; split; [eassumption | eassumption]
  | |- exists _, _ => eexists
  | |- cells_size _ = _ => first [reflexivity | eassumption]
  | |- _ => eassumption
  end.

Ltac ubdnorm H :=
  repeat match type of H with
  | rw_cells _ _ _ ?l =>
      match l with
      | context [C8 ?w] => lazymatch w with Z_to_bv 64 _ => fail | _ => rewrite <- (Z_to_bv_lit_self w) in H end
      | context [C4 ?w] => lazymatch w with Z_to_bv 64 _ => fail | _ => rewrite <- (Z_to_bv_lit_self w) in H end
      end
  end.

Lemma u_shl2 : forall v, v ≪ 2 = 4 * v.
Proof. intros v. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Ltac u_reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end) end.

Ltac u_mem_addr :=
  lazymatch goal with |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with
    | Some (Load _ _ _ ?rs ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in let immz := eval vm_compute in (bv_signed imm) in
        let R := u_reg_val rz in lazymatch R with Z_to_bv 64 ?E => constr:(E + immz) end
    | Some (Store _ ?rs _ ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in let immz := eval vm_compute in (bv_signed imm) in
        let R := u_reg_val rz in lazymatch R with Z_to_bv 64 ?E => constr:(E + immz) end
    end end end.

Ltac ustore OUT LB :=
  lazymatch type of OUT with u8arr _ _ ?A _ =>
    let E := u_mem_addr in
    u8_sok OUT (E - A); zstep; u8_store_same OUT (E - A); ubuf OUT LB end.

Ltac usrc SRC :=
  lazymatch type of SRC with bytes_at usegs ?mm ?S (map (Z_to_bv 8) ?bs) =>
    repeat match goal with H : ov_read_bytes usegs _ _ 1 = Some [Z_to_bv 8 (Znth _ bs)] |- _ => clear H end;
    let E := u_mem_addr in
    let R := fresh "RS" in
    pose proof (src_rd usegs mm S bs (E - S) SRC ltac:(unfold zlen in *; lia)) as R;
    replace (S + (E - S)) with E in R by lia end.

Ltac urd_clear DT :=
  repeat match goal with H : ov_read_bytes usegs _ (Z_to_bv 64 (DT + 4 + 4 * _ + _)) _ = _ |- _ => clear H
                     | H : ov_read_bytes usegs _ (Z_to_bv 64 (DT + 4 + 4 * _)) _ = _ |- _ => clear H end.

Ltac urd_new DT cells cbs ECB :=
  urd_clear DT;
  lazymatch goal with EC : ?c = nth (Z.to_nat ?v) cells x2_default |- _ => urd DT cells cbs ECB v c EC end.

Ltac urd_all DT cells cbs ECB :=
  urd_clear DT;
  repeat match goal with EC : ?c = nth (Z.to_nat ?v) cells x2_default |- _ => urd DT cells cbs ECB v c EC; revert EC end;
  repeat match goal with |- _ = nth _ cells x2_default -> _ => let EC := fresh "EC" in intro EC end.

Ltac ucell tl cells TCK :=
  match goal with VR : 0 <= ?v < 2^tl |- _ =>
    lazymatch goal with
    | _ : _ = nth (Z.to_nat v) cells x2_default |- _ => fail
    | |- _ =>
      let c := fresh "c" in let EC := fresh "EC" in
      remember (nth (Z.to_nat v) cells x2_default) as c eqn:EC;
      let SQ := fresh "SQ" in let NB := fresh "NB" in let LN := fresh "LN" in
      destruct (TCK v VR) as (SQ & NB & LN); rewrite <- EC in SQ, NB, LN end end.

Lemma u_srl3 : forall x, 0 <= x < 2^32 -> bv_swrap 32 (bv_wrap 32 x ≫ 3) mod 18446744073709551616 = x / 8.
Proof.
  intros x H. rewrite srliw_val by lia. rewrite (Z.mod_small x) by lia. change (2^3) with 8.
  apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma u_nn_iff : forall p n, 0 < p -> 0 <= n -> n <> p ->
  Z.lxor (Z.b2z (0 <? p)) (Z.b2z (Z.lxor p n <? 1)) = 1.
Proof.
  intros p n P N E.
  replace (0 <? p) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (Z.lxor p n <? 1) with false; [reflexivity|].
  symmetry. apply Z.ltb_ge.
  assert (Z.lxor p n <> 0) by (intro X; apply Z.lxor_eq in X; lia).
  assert (0 <= Z.lxor p n) by (apply Z.lxor_nonneg; split; intros; lia).
  lia.
Qed.

Definition u_is_unimp (segs : list Segment) (a : Z) : bool :=
  match fetch_word segs (Z_to_bv 64 a) with Some w => Z.eqb (bv_unsigned w) 3221229683 | None => false end.

Definition u_is_chk (segs : list Segment) (pc : Z) : bool :=
  u_is_unimp segs pc ||
  match fetch_word segs (Z_to_bv 64 pc) with
  | Some w => match decode_any w with
              | Some (Jal rd imm, _) => Z.eqb (bv_unsigned rd) 0 && u_is_unimp segs (pc + bv_signed imm)
              | _ => false end
  | None => false end.

Lemma u_x1_lt : forall a b, Z.lxor (Z.b2z (a <? b)) 1 = 0 -> a < b.
Proof. intros a b H. revert H. destruct (a <? b) eqn:E; intro H; [apply Z.ltb_lt; exact E | cbv in H; discriminate H]. Qed.

Lemma u_x1_ge : forall a b, Z.lxor (Z.b2z (a <? b)) 1 <> 0 -> b <= a.
Proof. intros a b H. revert H. destruct (a <? b) eqn:E; intro H; [exfalso; apply H; reflexivity | apply Z.ltb_ge; exact E]. Qed.

Ltac lean_ctx :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch type of T with
      | Prop =>
          lazymatch T with
          | @eq Z _ _ => fail
          | Z.le _ _ => fail
          | Z.lt _ _ => fail
          | Z.gt _ _ => fail
          | Z.ge _ _ => fail
          | Z.le _ _ /\ Z.le _ _ => fail
          | Z.le _ _ /\ Z.lt _ _ => fail
          | Z.lt _ _ /\ Z.le _ _ => fail
          | Z.lt _ _ /\ Z.lt _ _ => fail
          | _ => clear H
          end
      end
  end.

Ltac llia := lean_ctx; lia.

Ltac zlean H := exfalso; revert H; lean_ctx; intro H; lia.

Ltac unorm H := rewrite ?u_srl3 in H by lia; try (rewrite u_nn_iff in H by lia).

Lemma u_zx32_lit : forall z, 0 <= z < 2^32 -> bv_unsigned (zx32 (Z_to_bv 64 z)) = z.
Proof. intros z H. unfold zx32. rewrite (unsigned_lit z) by lia. rewrite Z.mod_small by lia. apply unsigned_lit. lia. Qed.

Lemma u_sx32_lit : forall z, 0 <= z < 2^31 -> bv_unsigned (sx32 (Z_to_bv 64 z)) = z.
Proof. intros z H. rewrite sx32_small by lia. apply unsigned_lit. lia. Qed.

Lemma u_sub_sh3 : forall b x, 0 <= x -> x * 8 <= b < 2^31 ->
  bv_swrap 32 (b - x ≪ 3 mod 18446744073709551616) = b - x * 8.
Proof.
  intros b x X B. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
  rewrite (Z.mod_small (x * 8)) by lia. apply swrap32_small; lia.
Qed.

Ltac unum1 :=
  first [ match goal with |- context [bv_unsigned (zx32 (Z_to_bv 64 ?z))] => rewrite (u_zx32_lit z) by llia end
        | match goal with |- context [bv_unsigned (sx32 (Z_to_bv 64 ?z))] => rewrite (u_sx32_lit z) by llia end
        | match goal with |- context [bv_swrap 32 (?b - ?x ≪ 3 mod 18446744073709551616)] => rewrite (u_sub_sh3 b x) by llia end
        | match goal with |- context [bv_swrap 32 ?z] => rewrite (swrap32_small z) by llia end ].

Ltac unum1_in H :=
  first [ match type of H with context [bv_unsigned (zx32 (Z_to_bv 64 ?z))] => rewrite (u_zx32_lit z) in H by llia end
        | match type of H with context [bv_unsigned (sx32 (Z_to_bv 64 ?z))] => rewrite (u_sx32_lit z) in H by llia end
        | match type of H with context [bv_swrap 32 (?b - ?x ≪ 3 mod 18446744073709551616)] => rewrite (u_sub_sh3 b x) in H by llia end
        | match type of H with context [bv_swrap 32 ?z] => rewrite (swrap32_small z) in H by llia end ].

Ltac unum := repeat unum1; repeat (match goal with H : _ |- _ => unum1_in H end).

Ltac hnorm H :=
  try (rewrite ?u_srl3 in H by llia);
  try (apply u_x1_lt in H);
  try (apply u_x1_ge in H);
  try (rewrite u_nn_iff in H by llia);
  repeat (unum1_in H).

Lemma u_bcmod : forall b, 0 <= b <= 64 -> bv_swrap 32 (b - (b / 8) ≪ 3 mod 18446744073709551616) = b mod 8.
Proof.
  intros b B. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
  pose proof (Z.div_pos b 8 ltac:(lia) ltac:(lia)) as D1.
  pose proof (Z.div_le_upper_bound b 8 8 ltac:(lia) ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound b 8 ltac:(lia)) as D3.
  pose proof (Z.div_mod b 8 ltac:(lia)) as D4.
  rewrite (Z.mod_small (b / 8 * 8)) by lia.
  rewrite swrap32_small by lia. lia.
Qed.

Ltac ucgen BD :=
  try (match goal with H : rw_cells _ _ BD (C8 (Z_to_bv 64 ?X) :: _) |- _ =>
         lazymatch X with Z.lor _ _ => let cX := fresh "cX" in set (cX := X) in *; clearbody cX end end);
  repeat (match goal with |- context [Z_to_bv 64 (Z.lor ?a ?b)] =>
            let y := fresh "y" in set (y := Z_to_bv 64 (Z.lor a b)) in *; clearbody y end).

Ltac ptnorm BD S :=
  repeat (match goal with H : rw_cells _ _ BD ?l |- _ =>
            match l with context [S + ?a - ?b] => replace (S + a - b) with (S + (a - b)) in H by lia end end).

Ltac rassoc B X :=
  repeat (match goal with |- context [B + ?x + ?y] => lazymatch x with X => fail | _ => rewrite <- (Z.add_assoc B x y) end end).

Ltac zrefute H := exfalso; first [ lia | rewrite u_lxor_m1 in H by lia; lia | apply H; apply u_shr62_small; lia ].

Ltac uwalk1 stops tl DT cells cbs ECB TCK OUT LB SRC :=
  lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
        lazymatch eval vm_compute in (orb (existsb (Z.eqb pc) stops) (u_is_chk usegs pc)) with
        | true => fail
        | false =>
            try (let v := fresh "v" in uidx tl v);
            try rewrite u_shl2;
            try unfold sx16;
            try (rewrite ?u_srl3 by lia);
            try (rewrite u_shamt by lia);
            repeat (match goal with |- context [sx32 (Z_to_bv 64 ?z)] => rewrite (sx32_small z) by lia end);
            repeat (match goal with |- context [(?a / 8) mod 4294967296] => rewrite (Z.mod_small (a / 8) 4294967296) by llia end);
            repeat (match goal with |- context [(?a - ?b) mod 4294967296] => rewrite (Z.mod_small (a - b) 4294967296) by llia end);
            lazymatch type of SRC with bytes_at _ _ ?SB0 _ =>
              repeat (match goal with |- context [(?a - ?b) mod 18446744073709551616] =>
                        lazymatch a with context [SB0] => rewrite (Z.mod_small (a - b) 18446744073709551616) by lia end end) end;
            repeat (match goal with
                    | |- context [bv_unsigned (Z_to_bv 8 (x2_len ?c))] => rewrite (byte_lit (x2_len c)) by lia
                    | |- context [bv_unsigned (Z_to_bv 8 (x2_nbBits ?c))] => rewrite (byte_lit (x2_nbBits c)) by lia
                    | |- context [bv_unsigned (Z_to_bv 8 (x2_seq ?c))] => rewrite (byte_lit (x2_seq c)) by lia end);
            repeat (ucell tl cells TCK);
            first [ zstep | ustore OUT LB | urd_new DT cells cbs ECB; zstep | urd_all DT cells cbs ECB; zstep | usrc SRC; zstep ]
        end
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let H := fresh "B" in if_cases H; zify_cond H; hnorm H;
        first [ solve [zlean H]
              | lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                  lazymatch eval vm_compute in (u_is_chk usegs pc) with
                  | true => solve [unorm H; zrefute H]
                  end end
              | idtac ]
    end.

Ltac uwalk stops tl DT cells cbs ECB TCK OUT LB SRC := repeat (uwalk1 stops tl DT cells cbs ECB TCK OUT LB SRC).

Ltac reassoc B X :=
  repeat (match goal with
          | |- context [Z_to_bv 64 (B + ?x + ?y)] =>
              lazymatch x with X => fail | _ => replace (B + x + y) with (B + (x + y)) by lia end
          | |- context [Z_to_bv 64 (B + ?x - ?y)] =>
              lazymatch x with X => fail | _ => replace (B + x - y) with (B + (x - y)) by lia end
          end).
