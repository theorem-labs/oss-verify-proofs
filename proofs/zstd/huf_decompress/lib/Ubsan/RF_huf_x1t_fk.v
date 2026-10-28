From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Step MState Cells Mem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require STRW_merge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_h_iface RF_huf_bdt_model RF_huf_x1t_model RF_huf_x1t_cls
  RF_huf_x1t_wk.
Import ListNotations.
Open Scope Z_scope.

Lemma x1k_land_m1 : forall x, 0 <= x < 2^64 -> Z.land ((0 - 1) mod 2^64) x = x.
Proof. intros x H. change ((0 - 1) mod 2^64) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small; lia. Qed.

Lemma x1k_lx63 : forall x, 0 <= x < 9223372036854775808 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof. intros x H. apply (zb_lxor_pow2_small x 63); lia. Qed.

Lemma x1k_lx1 : forall b, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof. destruct b; reflexivity. Qed.

Lemma x1k_land255 : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof. intros x H. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small; lia. Qed.

Lemma x1k_rd1 : forall (l : list byte) i b, nth_error l i = Some b -> firstn 1 (skipn i l) = [b].
Proof. induction l as [|a l IH]; intros [|i] b H; cbn in *; try discriminate. inversion H; reflexivity. apply IH; exact H. Qed.

Lemma x1k_u8 : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof. intros x H. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small; lia. Qed.

Lemma x1k_rv : forall b n, 0 <= b < 256 ->
  Z.lor (Z.shiftl (bv_unsigned (Z_to_bv 8 b)) 8 mod 18446744073709551616) n * (X1REP mod 18446744073709551616) = rep_val b n.
Proof. intros b n H. rewrite x1k_u8 by exact H. reflexivity. Qed.

Lemma x1k_rd4_bytes : forall v : word, firstn 4 (le8 v) = le4 v.
Proof. intros v. reflexivity. Qed.

Lemma x1k_rd4 : forall segs m A cs k v a, rw_cells segs m A cs -> cell_at cs k = Some (C8 v) -> a = wa (A + Z.of_nat k) ->
  ov_read_bytes segs m a 4 = Some (le4 v).
Proof.
  intros segs m A cs k v a [[WF BA] _] CA ->.
  destruct (cell_at_split cs k (C8 v) (C8 v) CA) as (pre & post & E & SZ & _). subst cs.
  apply cells_wf_app in WF. destruct WF as [WFp WFs].
  pose proof (cells_bytes_length pre WFp) as LP.
  assert (L : (k + 4 <= length (cells_bytes (pre ++ C8 v :: post)))%nat).
  { rewrite cells_bytes_app, length_app. cbn [cells_bytes cbytes]. rewrite length_app, length_le8. lia. }
  rewrite (bytes_at_ov_read segs m A _ k 4 BA L).
  rewrite cells_bytes_app. cbn [cells_bytes cbytes].
  rewrite <- SZ, <- LP, skipn_app_exact. rewrite <- x1k_rd4_bytes.
  generalize (cells_bytes post) as l. intros l. pose proof (length_le8 v) as L8.
  destruct (le8 v) as [|b0 [|b1 [|b2 [|b3 rest]]]]; cbn in L8; try discriminate; reflexivity.
Qed.

Ltac x1k_rd4at H k a := pose proof (x1k_rd4 _ _ _ _ k _ a H ltac:(cells_cbv; reflexivity) ltac:(unfold wa; f_equal; lia)).

Ltac x1k_ltb H := repeat match type of H with context [?a <? ?b] =>
  first [ rewrite (proj2 (Z.ltb_lt a b)) in H by lia | rewrite (proj2 (Z.ltb_ge a b)) in H by lia ] end.

Ltac x1k_modsm U := match type of U with context [?a mod ?M] => rewrite (Z.mod_small a M) in U by lia end.
Ltac x1k_pow2 U := match type of U with context [2 ^ ?k] =>
  let v := eval vm_compute in (2 ^ k) in lazymatch v with Zpos _ => change (2 ^ k) with v in U end end.
Ltac x1k_sh U := first [ rewrite Z.shiftl_mul_pow2 in U by lia | rewrite Z.shiftr_div_pow2 in U by lia ].
Ltac x1k_sw U := match type of U with context [bv_swrap 32 ?x] => rewrite (swrap32_small x) in U by lia end.

Ltac x1k_close U := exfalso; x1w_hnorm U;
  repeat (first [ rewrite x1k_land_m1 in U by lia | rewrite x1k_lx63 in U by lia | progress (x1k_ltb U)
                | progress (cbn [Z.b2z negb] in U) | rewrite Z.lxor_0_l in U | rewrite Z.lxor_0_r in U
                | rewrite Z.lxor_nilpotent in U | rewrite x1k_lx1 in U | x1k_sh U | x1k_pow2 U | x1k_sw U
                | x1k_modsm U ]);
  first [ lia | Z.div_mod_to_equations; nia ].

Ltac x1k_ltbg := repeat match goal with |- context [?a <? ?b] =>
  first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ] end.
Ltac x1k_nzg :=
  repeat (first [ rewrite x1k_land_m1 by lia | rewrite x1k_land255 by lia | rewrite sx32_small by lia
                | rewrite unsigned_lit by lia | progress x1k_ltbg | progress (cbn [Z.b2z negb])
                | rewrite Z.shiftl_mul_pow2 by lia | rewrite Z.shiftr_div_pow2 by lia
                | match goal with |- context [2 ^ ?k] => let v := eval vm_compute in (2 ^ k) in
                    lazymatch v with Zpos _ => change (2 ^ k) with v end end
                | match goal with |- context [bv_swrap 32 ?x] => rewrite (swrap32_small x) by lia end
                | match goal with |- context [?a mod ?M] => rewrite (Z.mod_small a M) by lia end ]).

Ltac x1k_ck := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
  first [ let d := eval vm_compute in (a =? PHUF_RDT_X1 + 3060) in lazymatch d with true =>
            let U := fresh "CK" in if_cases U; zify_cond U; [ x1k_close U | ] end
        | let d := eval vm_compute in (b =? PHUF_RDT_X1 + 3060) in lazymatch d with true =>
            let U := fresh "CK" in if_cases U; zify_cond U; [ | x1k_close U ] end ] end.

Ltac x1k_walk := repeat (x1w_zbr; x1w_norm; first [ x1w_dec_if | x1k_ck ]).

Ltac x1k_le1 b nb HB NB :=
  pose proof (rep_le1_0 b nb HB NB);
  pose proof (rep_le1_odd b nb 8 HB NB ltac:(cbn; tauto)); pose proof (rep_le1_even b nb 16 HB NB ltac:(cbn; tauto));
  pose proof (rep_le1_odd b nb 24 HB NB ltac:(cbn; tauto)); pose proof (rep_le1_even b nb 32 HB NB ltac:(cbn; tauto));
  pose proof (rep_le1_odd b nb 40 HB NB ltac:(cbn; tauto)); pose proof (rep_le1_even b nb 48 HB NB ltac:(cbn; tauto));
  pose proof (rep_le1_odd b nb 56 HB NB ltac:(cbn; tauto)).

Lemma x1k_land_ones32_l : forall x, 0 <= x < 2^32 -> Z.land 4294967295 x = x.
Proof. intros x H. rewrite Z.land_comm. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small; lia. Qed.

Lemma x1k_lxm31 : forall u, 0 <= u < 2^31 -> Z.lxor u (X1M31 mod 18446744073709551616) = 18446744071562067967 - u.
Proof.
  intros u H.
  replace (X1M31 mod 18446744073709551616) with (Z.lxor (2^31) 18446744073709551615) by (vm_compute; reflexivity).
  rewrite <- Z.lxor_assoc. rewrite (zb_lxor_pow2_small u 31) by lia. rewrite zb_lxor_ones by lia. lia.
Qed.

Lemma x1k_le1z : forall z b, 0 <= b < 256 -> 0 <= z < 2^64 -> z mod 256 = b -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 b].
Proof.
  intros z b Hb Hz Hr. apply STRW_merge.le1_lit_of_mod8. rewrite x1k_u8 by lia.
  rewrite (Z.mod_small z) by lia. exact Hr.
Qed.

Lemma x1k_lor : forall v nb, 0 <= v -> 0 <= nb < 256 -> Z.lor (v * 256) nb = v * 256 + nb.
Proof.
  intros v nb Hv Hn.
  assert (L : Z.land (v * 256) nb = 0).
  { apply Z.bits_inj'. intros i I. rewrite Z.land_spec, Z.bits_0.
    change 256 with (2^8). rewrite Z.mul_pow2_bits by lia.
    destruct (Z.ltb_spec i 8).
    + rewrite Z.testbit_neg_r by lia. reflexivity.
    + rewrite <- (Z.mod_small nb (2^8)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- (Z.lxor_lor _ _ L). rewrite <- (Z.add_nocarry_lxor _ _ L). reflexivity.
Qed.

Ltac x1k_lit2 := repeat match goal with |- context [2 ^ ?k] => is_Zlit k;
  let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v end.

Lemma x1k_rep_lo : forall b nb, 0 <= b < 256 -> 0 <= nb < 16 ->
  le1 (Z_to_bv 64 (Z.lor ((b * 256) mod 18446744073709551616) nb * (X1REP mod 18446744073709551616))) = [Z_to_bv 8 nb].
Proof.
  intros b nb Hb Hn. rewrite (Z.mod_small (b * 256)) by lia. rewrite x1k_lor by lia.
  change (X1REP mod 18446744073709551616) with 281479271743489.
  apply x1k_le1z; x1k_lit2; Z.div_mod_to_equations; lia.
Qed.

Lemma x1k_rep_ev : forall b nb k, 0 <= b < 256 -> 0 <= nb < 16 -> In k [16; 32; 48] ->
  le1 (Z_to_bv 64 (((Z.lor ((b * 256) mod 18446744073709551616) nb * (X1REP mod 18446744073709551616))
                     mod 18446744073709551616) ≫ k)) = [Z_to_bv 8 nb].
Proof.
  intros b nb k Hb Hn Hk. rewrite (Z.mod_small (b * 256)) by lia. rewrite x1k_lor by lia.
  change (X1REP mod 18446744073709551616) with 281479271743489.
  cbn [In] in Hk.
  repeat (destruct Hk as [<-|Hk];
    [ rewrite zb_shiftr_div by lia; apply x1k_le1z; x1k_lit2; Z.div_mod_to_equations; lia | ]).
  contradiction.
Qed.

Lemma x1k_rep_od : forall b nb k, 0 <= b < 256 -> 0 <= nb < 16 -> In k [8; 24; 40; 56] ->
  le1 (Z_to_bv 64 (((Z.lor ((b * 256) mod 18446744073709551616) nb * (X1REP mod 18446744073709551616))
                     mod 18446744073709551616) ≫ k)) = [Z_to_bv 8 b].
Proof.
  intros b nb k Hb Hn Hk. rewrite (Z.mod_small (b * 256)) by lia. rewrite x1k_lor by lia.
  change (X1REP mod 18446744073709551616) with 281479271743489.
  cbn [In] in Hk.
  repeat (destruct Hk as [<-|Hk];
    [ rewrite zb_shiftr_div by lia; apply x1k_le1z; x1k_lit2; Z.div_mod_to_equations; lia | ]).
  contradiction.
Qed.

Ltac x1k_xbr DT4 ARR q E :=
  let SOK := fresh "SOK" in
  pose proof (u8arr_store_ok usegs _ DT4 _ q (wa (DT4 + q)) ARR ltac:(rewrite ?upd_length, ?ox1_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?A) _) _) => replace A with (DT4 + q) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?A) _) _) => replace A with (DT4 + q) by lia
  end;
  rewrite E;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [?bb]) _) =>
    let ARR2 := fresh "ARR" in
    pose proof (u8arr_write usegs _ DT4 _ q bb ARR ltac:(rewrite ?upd_length, ?ox1_length; lia)) as ARR2;
    clear ARR; store_done; rename ARR2 into ARR
  end.

Lemma x1k_syrd : forall m SY js syms s v, bytes_at usegs m SY (omerge js syms) -> length js = length syms ->
  0 <= s < Z.of_nat (length syms) -> nth (Z.to_nat s) syms None = Some v ->
  ov_read_bytes usegs m (Z_to_bv 64 (SY + s)) 1 = Some [Z_to_bv 8 v].
Proof.
  intros m SY js syms s v B LJ Hs N.
  pose proof (omerge_nth syms js (Z.to_nat s) v LJ N) as E.
  pose proof (bytes_at_read usegs m SY (omerge js syms) s 1 B ltac:(lia)) as R.
  rewrite omerge_length in R. specialize (R ltac:(lia)).
  unfold wa in R. rewrite R. f_equal. exact (x1k_rd1 _ _ _ E).
Qed.

Ltac x1k_shn := repeat match goal with |- context [Z.shiftl ?a ?k] => is_Zlit k; let v := eval vm_compute in (2^k) in
  replace (Z.shiftl a k) with (a * v) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity) end.

Ltac x1k_msm := repeat match goal with
  | |- context [Z.lxor 0 ?x] => rewrite (Z.lxor_0_l x)
  | |- context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
  | |- context [Z.lxor ?u ?C] => is_Zlit C; let k := eval vm_compute in (Z.log2 C) in
       let ok := eval vm_compute in (C =? 2^k) in lazymatch ok with true =>
       let E1 := fresh in let E2 := fresh in assert (E1 : C = 2^k) by reflexivity;
       pose proof (zb_lxor_pow2_small u k ltac:(lia) ltac:(lia)) as E2; rewrite <- E1 in E2; rewrite E2; clear E1 E2 end
  | |- context [?a mod ?M] => is_Zlit M; rewrite (Z.mod_small a M) by lia
  | |- context [?a mod 2 ^ ?k] => is_Zlit k; rewrite (Z.mod_small a (2 ^ k)) by lia
  | |- context [?a <? ?b] => first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
  | |- context [Z.b2z true] => change (Z.b2z true) with 1
  | |- context [Z.b2z false] => change (Z.b2z false) with 0
  | |- context [bv_swrap 32 ?a] => rewrite (FseWalkKit.swrap32_small a) by lia
  | |- context [Z.land 4294967295 ?x] => rewrite (x1k_land_ones32_l x) by lia
  | |- context [Z.land ?x 255] => rewrite (x1k_land255 x) by lia
  | |- context [(0 - 1) mod 4294967296] => change ((0 - 1) mod 4294967296) with 4294967295
  | |- context [(0 - 1) mod 18446744073709551616] => change ((0 - 1) mod 18446744073709551616) with 18446744073709551615
  | |- context [Z.land 18446744073709551615 ?x] => rewrite (Z.land_comm 18446744073709551615 x);
       change 18446744073709551615 with (Z.ones 64); rewrite (Z.land_ones x 64) by lia; change (Z.ones 64) with 18446744073709551615
  | |- context [Z.shiftr ?a ?k] => is_Zlit k; rewrite (zb_shiftr_div a k) by lia
  end.

Ltac x1k_br := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
  first [ x1w_dec_if
        | let d := eval vm_compute in (a =? PHUF_RDT_X1 + 3060) in lazymatch d with true =>
            let U := fresh "U" in if_cases U; [ zify_cond U; x1w_hnorm_t U; exfalso; lia | clear U ] end
        | let d := eval vm_compute in (b =? PHUF_RDT_X1 + 3060) in lazymatch d with true =>
            let U := fresh "U" in if_cases U; [ clear U | zify_cond U; x1w_hnorm_t U; exfalso; lia ] end
        | let U := fresh "U" in if_cases U; [ zify_cond U; x1w_hnorm_t U; exfalso; lia | clear U ]
        | let U := fresh "U" in if_cases U; [ clear U | zify_cond U; x1w_hnorm_t U; exfalso; lia ] ] end.

Ltac x1k_zb := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail
  | _ => x1w_inr; x1k_shn; zstep end).

Ltac x1k_nm := x1w_norm; x1k_shn; x1w_norm; x1k_msm.

Ltac x1k_wlk := repeat (x1k_zb; x1k_nm; x1k_br).

Ltac x1k_to o := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
      let d := eval vm_compute in (z =? PHUF_RDT_X1 + o) in lazymatch d with true => fail | false => x1w_inr; x1k_shn; zstep end
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => x1k_nm; x1k_br end).
