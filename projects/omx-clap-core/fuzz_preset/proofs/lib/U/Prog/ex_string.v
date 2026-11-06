From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar ExString.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ex_hex4_c ex_string_c.
Import ListNotations.
Open Scope Z_scope.

Lemma ex_hex4_val_hex4 : forall b0 b1 b2 b3,
  ex_hex4_val [b0; b1; b2; b3] = hex4 [bv_unsigned b0; bv_unsigned b1; bv_unsigned b2; bv_unsigned b3].
Proof. reflexivity. Qed.

Lemma sx32_small : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma signed_lit_small : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small z) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma byte_bv_eta : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. exact H. Qed.

Lemma le1_byte : forall (v : word) M, bv_unsigned v mod 256 = M -> le1 v = [Z_to_bv 8 M].
Proof.
  intros v M H. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 8) with 256. rewrite H. rewrite <- H. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma le1_zxb_eta : forall b : byte, le1 (zxb b) = [Z_to_bv 8 (bv_unsigned b)].
Proof. intros b. rewrite le1_zxb, byte_bv_eta. reflexivity. Qed.

Lemma skipn_next : forall (l r : list byte) (j : nat) (pre : list byte), skipn j l = pre ++ r ->
  skipn (j + length pre) l = r.
Proof.
  intros l r j pre H. rewrite Nat.add_comm, <- skipn_skipn, H. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma skipn_S_cons : forall (l t : list byte) (j : nat) b, skipn j l = b :: t -> skipn (S j) l = t.
Proof. intros l t j b H. rewrite <- Nat.add_1_r. exact (skipn_next l t j [b] H). Qed.

Lemma skipn_len_cons : forall (l t : list byte) (j : nat) b, skipn j l = b :: t -> length l = (j + S (length t))%nat.
Proof.
  intros l t j b H. assert (E := f_equal (@length byte) H). rewrite length_skipn in E. cbn in E.
  destruct (Nat.le_gt_cases j (length l)) as [Hle|Hgt]; [lia|].
  rewrite skipn_all2 in H by lia. discriminate H.
Qed.

Lemma rd1 : forall m a l k b, bytes_at rsegs m a l -> nth_error l k = Some b ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 1 = Some [b].
Proof.
  intros m a l k b H E. apply nth_error_split in E. destruct E as (l1 & l2 & -> & <-).
  exact (bytes_at_read_at rsegs m a l1 b l2 H).
Qed.

Lemma scan_lt : forall z c, scan z = Some c -> (c < length z)%nat.
Proof. intros z c H. apply scan_quote in H. tauto. Qed.

Lemma utf8_1 : forall cp, 0 <= cp < 128 -> utf8 cp = [cp].
Proof. intros cp H. unfold utf8. destruct (Z.ltb_spec cp 128); [reflexivity|lia]. Qed.

Lemma utf8_2 : forall cp, 128 <= cp < 2048 -> utf8 cp = [192 + cp / 64; 128 + cp mod 64].
Proof. intros cp H. unfold utf8. destruct (Z.ltb_spec cp 128); [lia|]. destruct (Z.ltb_spec cp 2048); [reflexivity|lia]. Qed.

Lemma utf8_3 : forall cp, 2048 <= cp < 65536 -> utf8 cp = [224 + cp / 4096; 128 + (cp / 64) mod 64; 128 + cp mod 64].
Proof.
  intros cp H. unfold utf8. destruct (Z.ltb_spec cp 128); [lia|]. destruct (Z.ltb_spec cp 2048); [lia|].
  destruct (Z.ltb_spec cp 65536); [reflexivity|lia].
Qed.

Lemma utf8_4 : forall cp, 65536 <= cp ->
  utf8 cp = [240 + cp / 262144; 128 + (cp / 4096) mod 64; 128 + (cp / 64) mod 64; 128 + cp mod 64].
Proof.
  intros cp H. unfold utf8. destruct (Z.ltb_spec cp 128); [lia|]. destruct (Z.ltb_spec cp 2048); [lia|].
  destruct (Z.ltb_spec cp 65536); [lia|reflexivity].
Qed.

Lemma enc_lor : forall z k c b n, 0 <= z < 2 ^ 64 -> 0 <= k -> 0 <= n -> 0 <= b -> z / 2 ^ k < 2 ^ n -> c = b * 2 ^ n ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 z)) k))) c) = Z_to_bv 64 (c + z / 2 ^ k).
Proof.
  intros z k c b n Hz Hk Hn Hb Hlt ->.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk) as Pk.
  assert (D0 : 0 <= z / 2 ^ k) by (apply Z.div_pos; lia).
  rewrite (unsigned_lit z) by exact Hz.
  rewrite (unsigned_lit (Z.shiftr z k)) by (apply zr_shiftr; [exact Hz | exact Hk]).
  rewrite Z.shiftr_div_pow2 by exact Hk.
  rewrite lor_disj by lia. f_equal. lia.
Qed.

Lemma enc_field : forall z k, 0 <= z < 2 ^ 64 -> 0 <= k <= 58 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) k))) 58 + 128) =
  Z_to_bv 64 (128 + (z / 2 ^ (58 - k)) mod 64).
Proof.
  intros z k Hz Hk. rewrite (unsigned_lit z) by exact Hz. rewrite unsigned_lit_wrap.
  rewrite shl_shr_field by lia. f_equal. lia.
Qed.

Lemma enc_low : forall z, 0 <= z < 2 ^ 64 -> Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 z)) 63 + 128) = Z_to_bv 64 (128 + z mod 64).
Proof. intros z Hz. rewrite (unsigned_lit z) by exact Hz. rewrite land63. f_equal. lia. Qed.

Lemma e2a : forall cp, 0 <= cp < 2048 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 cp)) 6))) 192) = Z_to_bv 64 (192 + cp / 64).
Proof.
  intros cp H. rewrite (enc_lor cp 6 192 3 6);
    [reflexivity | lia | lia | lia | lia | change (cp / 64 < 64); Z.div_mod_to_equations; lia | reflexivity].
Qed.

Lemma e3a : forall cp, 0 <= cp < 65536 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 cp)) 12))) 224) = Z_to_bv 64 (224 + cp / 4096).
Proof.
  intros cp H. rewrite (enc_lor cp 12 224 14 4);
    [reflexivity | lia | lia | lia | lia | change (cp / 4096 < 16); Z.div_mod_to_equations; lia | reflexivity].
Qed.

Lemma e4a : forall cp, 0 <= cp < 2097152 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 cp)) 18))) 240) = Z_to_bv 64 (240 + cp / 262144).
Proof.
  intros cp H. rewrite (enc_lor cp 18 240 30 3);
    [reflexivity | lia | lia | lia | lia | change (cp / 262144 < 8); Z.div_mod_to_equations; lia | reflexivity].
Qed.

Lemma e_f52 : forall z, 0 <= z < 2 ^ 64 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 52))) 58 + 128) =
  Z_to_bv 64 (128 + (z / 64) mod 64).
Proof. intros z Hz. rewrite enc_field by lia. reflexivity. Qed.

Lemma e_f46 : forall z, 0 <= z < 2 ^ 64 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 46))) 58 + 128) =
  Z_to_bv 64 (128 + (z / 4096) mod 64).
Proof. intros z Hz. rewrite enc_field by lia. reflexivity. Qed.

Lemma e3z : forall cp, 0 <= cp < 65536 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 cp))) 16)) = Z_to_bv 64 0.
Proof.
  intros cp H. rewrite unsigned_lit by lia. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  rewrite (Z.mod_small cp) by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma e4z : forall cp, 0 <= cp < 2 ^ 31 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 cp))) 16)) = Z_to_bv 64 (cp / 65536).
Proof.
  intros cp H. rewrite unsigned_lit by lia. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  rewrite (Z.mod_small cp) by lia. rewrite Z.shiftr_div_pow2 by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma lo_val : forall lv, 0 <= lv < 65536 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 lv) + 18446744073709494272)) = Z_to_bv 64 (lv - 57344).
Proof.
  intros lv H. rewrite unsigned_lit by lia. f_equal. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma lo_chk : forall lv, 0 <= lv < 65536 ->
  bv_ltu (Z_to_bv 64 (lv - 57344)) (Z_to_bv 64 (-1024)) = negb ((56320 <=? lv) && (lv <=? 57343)).
Proof.
  intros lv H. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  destruct (Z.ltb_spec ((lv - 57344) mod 2 ^ 64) ((-1024) mod 2 ^ 64));
    destruct (Z.leb_spec 56320 lv); destruct (Z.leb_spec lv 57343); cbn [andb negb]; try reflexivity;
    exfalso; Z.div_mod_to_equations; lia.
Qed.

Lemma sw32_eq : forall e P, 0 <= P < 2 ^ 31 -> e mod 2 ^ 32 = P -> Z_to_bv 64 (bv_swrap 32 e) = Z_to_bv 64 P.
Proof.
  intros e P HP He. f_equal. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma pair_mod : forall cp lv a b, 55296 <= cp < 56320 -> 56320 <= lv <= 57343 ->
  a = (lv + -56613888) mod 2 ^ 64 -> b = (cp * 2 ^ 10) mod 2 ^ 64 -> (a + b) mod 2 ^ 32 = pair_cp cp lv.
Proof. intros cp lv a b Hc Hl -> ->. unfold pair_cp. Z.div_mod_to_equations. lia. Qed.

Ltac weq := rewrite ?length_app; cbn [length];
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ].

Ltac ulit_in H := repeat match type of H with context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) in H by lia end.
Ltac slit_in H := repeat match type of H with context [bv_signed (Z_to_bv 64 ?z)] => rewrite (signed_lit_small z) in H by lia end.
Ltac gsimp := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.

Ltac cfs H :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; cbv delta [zxb] in H;
  fold_lit_ux_in H; ulit_in H; slit_in H;
  zify_bool H.

Ltac notrap := let T := fresh "T" in if_cases T; [cfs T; exfalso; lia | clear T].

Ltac esc_solve :=
  unfold escape; repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) end;
  first [ reflexivity | exfalso; lia ].

Ltac b1 :=
  first [ reflexivity | apply le1_zxb_eta | apply le1_byte; cbv delta [zxb]; rewrite ?unsigned_lit by lia;
          first [ reflexivity | Z.div_mod_to_equations; lia ] ].

Ltac steps_until pc0 :=
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => tryif (constr_eq p pc0) then fail else step
  end.

Ltac estore := step; step; notrap; steps_until 0x14f64.

Ltac swr cp lv := lazymatch goal with |- context [Z_to_bv 64 (bv_swrap 32 ?e)] =>
  rewrite (sw32_eq e (pair_cp cp lv));
  [ | lia
    | rewrite ?unsigned_lit_wrap; rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?(Z.mod_small cp (2 ^ 64)) by lia;
      first [ eapply pair_mod; [lia | lia | reflexivity | reflexivity]
            | unfold pair_cp; Z.div_mod_to_equations; lia ] ] end.

Section Ubsan.
Variable HEX4 : ex_hex4_contract.
Variables (sra ssp gp tp ss0 ss1 ss2 ss3 ss4 ss5 ss6 ss7 ss8 ss9 ss10 ss11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (q x0 i0 scr lo : Z) (x : list byte).

Local Notation SPZ := (bv_unsigned ssp).
Local Notation yb := (skipn (S (Z.to_nat i0)) x).
Local Notation yz := (map bv_unsigned (skipn (S (Z.to_nat i0)) x)).
Local Notation YA := (x0 + i0 + 1).
Local Notation ENDZ := (x0 + Z.of_nat (length x)).

Hypothesis HQA : q mod 8 = 0.
Hypothesis HP : bytes_at rsegs m0 q (le8 (Z_to_bv 64 (x0 + i0))).
Hypothesis HE : bytes_at rsegs m0 (q + 8) (le8 (Z_to_bv 64 (x0 + Z.of_nat (length x)))).
Hypothesis HS : bytes_at rsegs m0 (q + 24) (le8 (Z_to_bv 64 scr)).
Hypothesis HWQ : wr_at rsegs m0 q 8.
Hypothesis HX : bytes_at rsegs m0 x0 x.
Hypothesis HX0 : 0 < x0.
Hypothesis HXE : x0 + Z.of_nat (length x) < 2 ^ 64.
Hypothesis HXL : Z.of_nat (length x) < 2 ^ 63.
Hypothesis HI0 : 0 <= i0 < Z.of_nat (length x).
Hypothesis HSC : 0 < scr.
Hypothesis HWS : wr_at rsegs m0 scr (Z.of_nat (length x) + 1).
Hypothesis HD1 : scr + Z.of_nat (length x) + 1 <= q \/ q + 40 <= scr.
Hypothesis HD2 : scr + Z.of_nat (length x) + 1 <= x0 \/ x0 + Z.of_nat (length x) <= scr.
Hypothesis HST : stk rsegs m0 lo SPZ.
Hypothesis HLO : lo + 128 <= SPZ.
Hypothesis HSA : SPZ mod 16 = 0.
Hypothesis HD3 : SPZ <= q \/ q + 40 <= SPZ + -128.
Hypothesis HD4 : SPZ <= x0 \/ x0 + Z.of_nat (length x) <= SPZ + -128.
Hypothesis HD5 : SPZ <= scr \/ scr + Z.of_nat (length x) + 1 <= SPZ + -128.
Hypothesis HMI : mem_inv rsegs m0.

Lemma len_yb : Z.of_nat (length yb) = Z.of_nat (length x) - i0 - 1.
Proof. rewrite length_skipn. lia. Qed.

Lemma sp_range : 0 <= SPZ < 2 ^ 64.
Proof. exact (zr_word ssp). Qed.

Lemma lo_range : 0 <= lo.
Proof. destruct HST as [H _]. exact H. Qed.

Lemma scr_range : scr + Z.of_nat (length x) + 1 <= 2 ^ 64.
Proof. destruct HWS as (_ & H & _). lia. Qed.

Lemma q_range : 0 <= q /\ q + 32 <= 2 ^ 64.
Proof.
  pose proof (bytes_at_bound _ _ _ _ HS) as H. pose proof (bytes_at_bound _ _ _ _ HP) as H'.
  rewrite length_le8 in H, H'. cbn in H, H'. lia.
Qed.

Definition SV : list byte :=
  le8 ss11 ++ le8 ss10 ++ le8 ss9 ++ le8 ss8 ++ le8 ss7 ++ le8 ss6 ++ le8 ss5 ++ le8 ss4 ++ le8 ss3 ++ le8 ss2 ++
  le8 ss1 ++ le8 ss0 ++ le8 sra.

Definition CST : list byte := le8 (Z_to_bv 64 (-56613888)) ++ le8 (Z_to_bv 64 56320).

Definition emem (mk : word -> option byte) (n : Z) : Prop :=
  bytes_at rsegs mk (SPZ + -104) SV /\
  munch [(SPZ + -128, SPZ); (scr, scr + n)] m0 mk /\
  wmono rsegs m0 mk /\
  stk rsegs mk lo SPZ.

Definition lmem (mk : word -> option byte) (out : list Z) : Prop :=
  bytes_at rsegs mk YA yb /\
  bytes_at rsegs mk (q + 8) (le8 (Z_to_bv 64 ENDZ)) /\
  bytes_at rsegs mk (SPZ + -128) CST /\
  bytes_at rsegs mk (SPZ + -104) SV /\
  bytes_at rsegs mk scr (map (Z_to_bv 8) out) /\
  munch [(SPZ + -128, SPZ); (scr, scr + Z.of_nat (length out))] m0 mk /\
  wmono rsegs m0 mk /\
  stk rsegs mk lo SPZ.

Lemma lmem_emem : forall mk out, lmem mk out -> emem mk (Z.of_nat (length out)).
Proof. intros mk out (_ & _ & _ & H4 & _ & H6 & H7 & H8). exact (conj H4 (conj H6 (conj H7 H8))). Qed.

Lemma lmem_y : forall mk out (j : nat), lmem mk out -> (j <= length yb)%nat ->
  bytes_at rsegs mk (YA + Z.of_nat j) (skipn j yb).
Proof. intros mk out j (H & _) Hj. apply bytes_at_skipn; assumption. Qed.

Lemma lmem_rd_end : forall mk out, lmem mk out -> ov_read_bytes rsegs mk (wa (q + 8)) 8 = Some (le8 (Z_to_bv 64 ENDZ)).
Proof.
  intros mk out (_ & H & _). pose proof (bytes_at_read_whole rsegs _ _ _ H) as R. rewrite length_le8 in R. exact R.
Qed.

Lemma lmem_rd_c0 : forall mk out, lmem mk out -> ov_read_bytes rsegs mk (wa (SPZ + -128)) 8 = Some (le8 (Z_to_bv 64 (-56613888))).
Proof.
  intros mk out (_ & _ & H & _). unfold CST in H. apply bytes_at_prefix in H.
  pose proof (bytes_at_read_whole rsegs _ _ _ H) as R. rewrite length_le8 in R. exact R.
Qed.

Lemma lmem_rd_dc : forall mk out, lmem mk out -> ov_read_bytes rsegs mk (wa (SPZ + -120)) 8 = Some (le8 (Z_to_bv 64 56320)).
Proof.
  intros mk out (_ & _ & H & _). unfold CST in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_le8 in H. pose proof (bytes_at_read_whole rsegs _ _ _ H) as R. rewrite length_le8 in R.
  replace (SPZ + -120) with (SPZ + -128 + Z.of_nat 8) by lia. exact R.
Qed.

Lemma lmem_wr_scr : forall mk out, lmem mk out -> wr_at rsegs mk scr (Z.of_nat (length x) + 1).
Proof. intros mk out (_ & _ & _ & _ & _ & _ & W & _). eapply wr_at_transport; eauto. Qed.

Lemma lmem_wr_q : forall mk out, lmem mk out -> wr_at rsegs mk q 8.
Proof. intros mk out (_ & _ & _ & _ & _ & _ & W & _). eapply wr_at_transport; eauto. Qed.

Lemma lmem_store_ok : forall mk out k, lmem mk out -> 0 <= k < Z.of_nat (length x) + 1 ->
  store_ok rsegs mk (wa (scr + k)) 1 = true.
Proof.
  intros mk out k L Hk. apply (wr_at_store_ok rsegs mk scr (Z.of_nat (length x) + 1)); [eapply lmem_wr_scr; eauto | lia | lia].
Qed.

Lemma lmem_store1 : forall mk out a bs M, lmem mk out -> (length out < length yb)%nat ->
  a = wa (scr + Z.of_nat (length out)) -> bs = [Z_to_bv 8 M] -> 0 <= M < 256 ->
  lmem (write_to_mem mk a bs) (out ++ [M]).
Proof.
  intros mk out a bs M (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hlt -> -> HM.
  pose proof len_yb as LY. pose proof scr_range as SR. pose proof sp_range as SP. pose proof lo_range as LR.
  pose proof q_range as QR.
  pose proof (bytes_at_bound _ _ _ _ H5) as B5. rewrite length_map in B5.
  unfold lmem, SV, CST in *.
  split; [apply bytes_at_write_other; [exact H1| lia | cbn; lia | cbn; lia] |].
  split; [apply bytes_at_write_other; [exact H2| lia | cbn; lia | rewrite length_le8; cbn; lia] |].
  split; [apply bytes_at_write_other; [exact H3| lia | cbn; lia | rewrite !length_app, !length_le8; cbn; lia] |].
  split; [apply bytes_at_write_other; [exact H4| lia | cbn; lia | rewrite !length_app, !length_le8; cbn; lia] |].
  split.
  { rewrite map_app. cbn [map]. rewrite <- (length_map (Z_to_bv 8) out).
    apply bytes_at_snoc_write; [exact H5|]. rewrite length_map. cbn. lia. }
  split.
  { apply munch_write; [| lia | cbn; lia | cbn [inside length]; rewrite length_app; cbn; right; left; lia].
    eapply munch_weaken; [| exact H6]. intros z Hz. cbn [outside] in *. rewrite length_app in Hz. cbn [length] in Hz.
    destruct Hz as (Ha & Hb & _). split; [lia | split; [lia | exact I]]. }
  split; [apply wmono_write; exact H7|].
  apply stk_write; [exact H8 | lia | cbn; lia].
Qed.

Lemma lmem_call : forall mk m' out o bs, lmem mk out -> (length out <= length yb)%nat -> SPZ + -112 <= o -> o + Z.of_nat (length bs) <= SPZ + -104 ->
  munch [(o, o + Z.of_nat (length bs))] mk m' -> wmono rsegs mk m' -> bytes_at rsegs m' o bs -> lmem m' out.
Proof.
  intros mk m' out o bs (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hk Ho1 Ho2 MU WM HB.
  pose proof len_yb as LY. pose proof scr_range as SR. pose proof sp_range as SP. pose proof q_range as QR.
  pose proof (bytes_at_bound _ _ _ _ H5) as B5. rewrite length_map in B5.
  unfold lmem, SV, CST in *.
  split; [eapply bytes_at_transport; [exact H1 | exact MU | cbn; lia] |].
  split; [eapply bytes_at_transport; [exact H2 | exact MU | rewrite length_le8; cbn; lia] |].
  split; [eapply bytes_at_transport; [exact H3 | exact MU | rewrite !length_app, !length_le8; cbn; lia] |].
  split; [eapply bytes_at_transport; [exact H4 | exact MU | rewrite !length_app, !length_le8; cbn; lia] |].
  split; [eapply bytes_at_transport; [exact H5 | exact MU | rewrite length_map; cbn; lia] |].
  split.
  { eapply munch_trans; [exact H6|]. eapply munch_weaken; [| exact MU].
    intros z Hz. cbn [outside] in *. destruct Hz as (Ha & Hb & _). split; [lia | exact I]. }
  split; [eapply wmono_trans; eauto |].
  eapply stk_after_bytes; eauto.
Qed.

Lemma lmem_stk_store : forall mk out o bs, lmem mk out -> (length out <= length yb)%nat -> SPZ + -112 <= o -> o + Z.of_nat (length bs) <= SPZ + -104 ->
  lmem (write_to_mem mk (wa o) bs) out.
Proof.
  intros mk out o bs (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hk Ho1 Ho2.
  pose proof len_yb as LY. pose proof scr_range as SR. pose proof sp_range as SP. pose proof lo_range as LR.
  pose proof q_range as QR.
  pose proof (bytes_at_bound _ _ _ _ H5) as B5. rewrite length_map in B5.
  unfold lmem, SV, CST in *.
  split; [apply bytes_at_write_other; [exact H1| lia | lia | lia] |].
  split; [apply bytes_at_write_other; [exact H2| lia | lia | rewrite length_le8; cbn; lia] |].
  split; [apply bytes_at_write_other; [exact H3| lia | lia | rewrite !length_app, !length_le8; cbn; lia] |].
  split; [apply bytes_at_write_other; [exact H4| lia | lia | rewrite !length_app, !length_le8; cbn; lia] |].
  split; [apply bytes_at_write_other; [exact H5| lia | lia | rewrite length_map; lia] |].
  split.
  { apply munch_write; [exact H6 | lia | lia | cbn [inside]; left; lia]. }
  split; [apply wmono_write; exact H7|].
  apply stk_write; [exact H8 | lia | lia].
Qed.

Lemma lmem_slot : forall mk out (k : Z) (n : nat), lmem mk out -> 0 <= k -> k + Z.of_nat n <= 128 ->
  store_ok rsegs mk (wa (SPZ + -128 + k)) n = true.
Proof.
  intros mk out k n (_ & _ & _ & _ & _ & _ & _ & (S1 & S2 & S3)) Hk1 Hk2. pose proof sp_range.
  apply (wr_at_store_ok rsegs mk (SPZ + -128) 128); [| lia | lia].
  split; [lia|]. split; [lia|]. intros i Hi. destruct (S3 (SPZ + -128 + i)) as [W _]; [lia | exact W].
Qed.

Lemma lmem_slot_wr : forall mk out (o : Z), lmem mk out -> SPZ + -112 <= o -> o + 4 <= SPZ + -104 ->
  wr_at rsegs mk o 4.
Proof.
  intros mk out o (_ & _ & _ & _ & _ & _ & _ & (S1 & S2 & S3)) Hk1 Hk2. pose proof sp_range.
  split; [lia|]. split; [lia|]. intros i Hi. destruct (S3 (o + i)) as [W _]; [lia | exact W].
Qed.

Definition st (pc : Z) (a0 a1 a2 s1 s7 s11 : word) (mk : word -> option byte) : machine_state :=
  MS (mkR (Z_to_bv 64 117) (Z_to_bv 64 (SPZ + -128)) gp tp (Z_to_bv 64 12) (Z_to_bv 64 110) (Z_to_bv 64 10)
          (Z_to_bv 64 q) s1 a0 a1 a2 (Z_to_bv 64 91) (Z_to_bv 64 47) (Z_to_bv 64 98) (Z_to_bv 64 8) (Z_to_bv 64 102)
          (Z_to_bv 64 34) (Z_to_bv 64 32) (Z_to_bv 64 92) (Z_to_bv 64 (-1)) (Z_to_bv 64 101) s7 (Z_to_bv 64 2)
          (Z_to_bv 64 55296) (Z_to_bv 64 113) s11 (Z_to_bv 64 114) (Z_to_bv 64 13) (Z_to_bv 64 116) (Z_to_bv 64 9))
     F (Z_to_bv 64 pc) fc None mk (seg_rom rsegs).

Definition DINV (j : nat) (out : list Z) : Prop :=
  decode yz = emit out (decode (map bv_unsigned (skipn j yb))).

Definition INV (j : nat) (out : list Z) (mk : word -> option byte) : Prop :=
  lmem mk out /\ (j < length yb)%nat /\ (length out <= j)%nat /\ DINV j out.

Definition HEAD (Q : machine_state -> Prop) (j : nat) (out : list Z) (mk : word -> option byte) : Prop :=
  forall a0 a1 a2 s1 s7 s11, a0 = Z_to_bv 64 ENDZ -> s7 = Z_to_bv 64 (scr + Z.of_nat (length out)) ->
    s1 = Z_to_bv 64 (YA + Z.of_nat j) -> evt rsegs Q (st 0x14dec a0 a1 a2 s1 s7 s11 mk).

Definition KFAIL (Q : machine_state -> Prop) : Prop :=
  forall (r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word)
         mk n,
    emem mk n -> n <= Z.of_nat (length yb) -> decode yz = None ->
    evt rsegs Q (MS (mkR r1 (Z_to_bv 64 (SPZ + -128)) gp tp r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17
                         r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
                    F (Z_to_bv 64 0x150f4) fc None mk (seg_rom rsegs)).

Definition KSUCC (Q : machine_state -> Prop) : Prop :=
  forall a0 a1 a2 s1 s7 s11 mk out (j : nat),
    lmem mk out -> (j < length yb)%nat -> (length out <= j)%nat ->
    decode yz = Some (out, map bv_unsigned (skipn (S j) yb)) ->
    s7 = Z_to_bv 64 (scr + Z.of_nat (length out)) -> s1 = Z_to_bv 64 (YA + Z.of_nat j) ->
    evt rsegs Q (st 0x15134 a0 a1 a2 s1 s7 s11 mk).

Definition LOOPIH (Q : machine_state -> Prop) (j0 : nat) : Prop :=
  forall j out mk, (j0 < j)%nat -> INV j out mk -> HEAD Q j out mk.

Definition POST (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR sra ssp gp tp t0' t1' t2' ss0 ss1 r a1' a2' a3' a4' a5' a6' a7'
                  ss2 ss3 ss4 ss5 ss6 ss7 ss8 ss9 ss10 ss11 t3' t4' t5' t6')
             F (ret_pc sra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo SPZ /\
    match fst (fst (jr_string yz [])) with
    | None => r = Z_to_bv 64 (-1) /\
        munch [(SPZ - EX_STRING_K, SPZ); (scr, scr + Z.of_nat (length x) - i0 - 1)] m0 m'
    | Some (s, rest) => r = Z_to_bv 64 0 /\
        munch [(q, q + 8); (SPZ - EX_STRING_K, SPZ); (scr, scr + Z.of_nat (length s) + 1)] m0 m' /\
        (exists c, scan yz = Some c /\ rest = skipn (S c) yz /\
           bytes_at rsegs m' q (le8 (Z_to_bv 64 (x0 + i0 + Z.of_nat c + 2)))) /\
        bytes_at rsegs m' scr (map (Z_to_bv 8) s ++ [Z_to_bv 8 0])
    end.

Lemma SV_cells : forall mk, bytes_at rsegs mk (SPZ + -104) SV ->
  ro_cells rsegs mk (SPZ + -104)
    [C8 ss11; C8 ss10; C8 ss9; C8 ss8; C8 ss7; C8 ss6; C8 ss5; C8 ss4; C8 ss3; C8 ss2; C8 ss1; C8 ss0; C8 sra].
Proof.
  intros mk H. unfold ro_cells, cells_at. split; [cbn; tauto|].
  unfold SV in H. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H.
Qed.

Lemma epi : forall Q (r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word) mk,
  bytes_at rsegs mk (SPZ + -104) SV ->
  Q (MS (mkR sra ssp gp tp r5 r6 r7 ss0 ss1 r10 r11 r12 r13 r14 r15 r16 r17 ss2 ss3 ss4 ss5 ss6 ss7 ss8 ss9 ss10 ss11 r28 r29 r30 r31)
        F (ret_pc sra) fc None mk (seg_rom rsegs)) ->
  evt rsegs Q (MS (mkR r1 (Z_to_bv 64 (SPZ + -128)) gp tp r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31)
                  F (Z_to_bv 64 0x150f8) fc None mk (seg_rom rsegs)).
Proof.
  intros Q r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 mk HSV HQ.
  pose proof (SV_cells mk HSV) as RO. pose proof sp_range as SP.
  do 15 step.
  apply evt_done. exact HQ.
Qed.

Lemma wv_frame : forall z : word, SPZ + -128 <= bv_unsigned z < SPZ -> wview rsegs m0 z <> None.
Proof.
  intros z Hz. destruct HST as (_ & _ & H). destruct (H (bv_unsigned z)) as [W _]; [lia|].
  unfold wa in W. rewrite Z_to_bv_lit_self in W. exact W.
Qed.

Lemma wv_scr : forall z : word, scr <= bv_unsigned z < scr + Z.of_nat (length x) + 1 -> wview rsegs m0 z <> None.
Proof.
  intros z Hz. destruct HWS as (_ & _ & H). specialize (H (bv_unsigned z - scr) ltac:(lia)).
  replace (scr + (bv_unsigned z - scr)) with (bv_unsigned z) in H by lia.
  unfold wa in H. rewrite Z_to_bv_lit_self in H. exact H.
Qed.

Lemma wv_q : forall z : word, q <= bv_unsigned z < q + 8 -> wview rsegs m0 z <> None.
Proof.
  intros z Hz. destruct HWQ as (_ & _ & H). specialize (H (bv_unsigned z - q) ltac:(lia)).
  replace (q + (bv_unsigned z - q)) with (bv_unsigned z) in H by lia.
  unfold wa in H. rewrite Z_to_bv_lit_self in H. exact H.
Qed.

Lemma wv_any : forall z : word,
  (q <= bv_unsigned z < q + 8) \/ (SPZ + -128 <= bv_unsigned z < SPZ) \/ (scr <= bv_unsigned z < scr + Z.of_nat (length x) + 1) ->
  wview rsegs m0 z <> None.
Proof. intros z [H|[H|H]]; [apply wv_q | apply wv_frame | apply wv_scr]; exact H. Qed.

Lemma kfail : KFAIL POST.
Proof.
  intros r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 mk n
    (HSV & MU & WM & STK) Hn Hd.
  pose proof len_yb as LY.
  step.
  apply epi; [exact HSV|].
  unfold POST. do 16 eexists. split; [reflexivity|].
  split; [exact WM|].
  split.
  { apply (mem_inv_munch rsegs [(SPZ + -128, SPZ); (scr, scr + n)] m0 mk HMI MU).
    intros z Hz. cbn [outside] in Hz. apply wv_any. lia. }
  split; [exact STK|].
  rewrite jr_string_decode, Hd. cbv beta iota. split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
  eapply munch_weaken; [| exact MU]. unfold sub_fp, EX_STRING_K. cbn [outside]. intros z Hz. intuition lia.
Qed.

Lemma map_skipn' : forall (f : byte -> Z) (l : list byte) n, map f (skipn n l) = skipn n (map f l).
Proof. intros f l. induction l as [|a l IH]; intros [|n]; cbn; try reflexivity. apply IH. Qed.

Lemma scan_eq : forall out (j : nat), (j < length yb)%nat ->
  decode yz = Some (out, map bv_unsigned (skipn (S j) yb)) -> scan yz = Some j.
Proof.
  intros out j Hj Hd. destruct (decode_stop _ _ _ Hd) as (c & Hc & Hr & _).
  pose proof (scan_lt _ _ Hc) as Lc. rewrite length_map in Lc.
  rewrite map_skipn' in Hr. apply (f_equal (@length Z)) in Hr. rewrite !length_skipn, length_map in Hr.
  replace j with c by lia. exact Hc.
Qed.

Lemma ksucc_mem : forall mk out (j : nat), lmem mk out -> (length out <= j)%nat -> (j < length yb)%nat ->
  bytes_at rsegs (write_to_mem (write_to_mem mk (wa (scr + Z.of_nat (length out))) [Z_to_bv 8 0]) (wa q)
                    (le8 (Z_to_bv 64 (x0 + i0 + Z.of_nat j + 2)))) (SPZ + -104) SV /\
  munch [(q, q + 8); (SPZ - EX_STRING_K, SPZ); (scr, scr + Z.of_nat (length out) + 1)] m0
    (write_to_mem (write_to_mem mk (wa (scr + Z.of_nat (length out))) [Z_to_bv 8 0]) (wa q)
       (le8 (Z_to_bv 64 (x0 + i0 + Z.of_nat j + 2)))) /\
  wmono rsegs m0 (write_to_mem (write_to_mem mk (wa (scr + Z.of_nat (length out))) [Z_to_bv 8 0]) (wa q)
                    (le8 (Z_to_bv 64 (x0 + i0 + Z.of_nat j + 2)))) /\
  stk rsegs (write_to_mem (write_to_mem mk (wa (scr + Z.of_nat (length out))) [Z_to_bv 8 0]) (wa q)
               (le8 (Z_to_bv 64 (x0 + i0 + Z.of_nat j + 2)))) lo SPZ /\
  bytes_at rsegs (write_to_mem (write_to_mem mk (wa (scr + Z.of_nat (length out))) [Z_to_bv 8 0]) (wa q)
                    (le8 (Z_to_bv 64 (x0 + i0 + Z.of_nat j + 2)))) q (le8 (Z_to_bv 64 (x0 + i0 + Z.of_nat j + 2))) /\
  bytes_at rsegs (write_to_mem (write_to_mem mk (wa (scr + Z.of_nat (length out))) [Z_to_bv 8 0]) (wa q)
                    (le8 (Z_to_bv 64 (x0 + i0 + Z.of_nat j + 2)))) scr (map (Z_to_bv 8) out ++ [Z_to_bv 8 0]).
Proof.
  intros mk out j (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hk Hj.
  pose proof len_yb as LY. pose proof scr_range as SR. pose proof sp_range as SP. pose proof q_range as QR.
  pose proof lo_range as LR.
  pose proof (bytes_at_bound _ _ _ _ H5) as B5. rewrite length_map in B5.
  unfold SV, EX_STRING_K in *.
  split.
  { apply bytes_at_write_other; [| lia | rewrite length_le8; cbn; lia | rewrite length_le8, !length_app, !length_le8; cbn; lia].
    apply bytes_at_write_other; [exact H4 | lia | cbn; lia | rewrite !length_app, !length_le8; cbn; lia]. }
  split.
  { apply munch_write; [| lia | rewrite length_le8; cbn; lia | cbn [inside]; rewrite length_le8; cbn; lia].
    apply munch_write; [| lia | cbn; lia | cbn [inside length]; cbn; lia].
    eapply munch_weaken; [| exact H6]. unfold sub_fp. cbn [outside]. intros z Hz. intuition lia. }
  split; [apply wmono_write, wmono_write; exact H7|].
  split; [apply stk_write; [apply stk_write; [exact H8 | lia | cbn; lia] | lia | rewrite length_le8; cbn; lia]|].
  split; [apply bytes_at_write_same; [lia | rewrite length_le8; cbn; lia]|].
  apply bytes_at_write_other; [| lia | rewrite length_le8; cbn; lia | rewrite length_le8, length_app, length_map; cbn; lia].
  rewrite <- (length_map (Z_to_bv 8) out). apply bytes_at_snoc_write; [exact H5|]. rewrite length_map. cbn. lia.
Qed.

Lemma ksucc : KSUCC POST.
Proof.
  intros a0 a1 a2 s1 s7 s11 mk out j L Hj Hk Hd E7 E1. subst s7 s1. unfold st.
  pose proof len_yb as LY. pose proof scr_range as SR. pose proof sp_range as SP. pose proof q_range as QR.
  pose proof (lmem_store_ok mk out (Z.of_nat (length out)) L ltac:(lia)) as S0.
  pose proof (lmem_wr_q _ _ L) as WQ.
  step. notrap. step. step. step. notrap. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (S1 : store_ok rsegs mm (wa (q + 0)) 8 = true)
      by (apply (wr_at_store_ok rsegs mm q 8); [apply wr_at_write; exact WQ | lia | lia]) end.
  rewrite Z.add_0_r in S1.
  step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem (write_to_mem mk ?A1 ?B1) ?A2 ?B2) _) =>
    replace B1 with [Z_to_bv 8 0] by (symmetry; b1);
    replace B2 with (le8 (Z_to_bv 64 (x0 + i0 + Z.of_nat j + 2))) by (f_equal; weq);
    change A1 with (wa (scr + Z.of_nat (length out))); change A2 with (wa q) end.
  destruct (ksucc_mem mk out j L Hk Hj) as (M1 & M2 & M3 & M4 & M5 & M6).
  eapply epi; [exact M1|].
  unfold POST. do 16 eexists. split; [reflexivity|].
  split; [exact M3|].
  split.
  { eapply mem_inv_munch; [exact HMI | exact M2 |].
    intros z Hz. cbn [outside] in Hz. unfold EX_STRING_K in Hz. apply wv_any. pose proof len_yb. lia. }
  split; [exact M4|].
  rewrite jr_string_decode, Hd. cbv beta iota.
  split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
  split; [exact M2|].
  split; [| exact M6].
  exists j. split; [exact (scan_eq out j Hj Hd)|]. split; [apply map_skipn'|]. exact M5.
Qed.

Lemma back : forall Q (j0 : nat), KFAIL Q -> LOOPIH Q j0 ->
  forall (j : nat) out mk a0 a1 a2 s1 s7 s11, (j0 < j)%nat -> (j <= length yb)%nat -> lmem mk out ->
    (length out <= j)%nat -> DINV j out ->
    s11 = Z_to_bv 64 (YA + Z.of_nat j) -> a1 = Z_to_bv 64 (scr + Z.of_nat (length out)) ->
    evt rsegs Q (st 0x14f64 a0 a1 a2 s1 s7 s11 mk).
Proof.
  intros Q j0 KF IH j out mk a0 a1 a2 s1 s7 s11 Hj0 Hj L Hk Hd E11 E1. subst s11 a1. unfold st.
  pose proof len_yb as LY. pose proof scr_range as SR.
  pose proof (lmem_rd_end _ _ L) as RE.
  step. step. step. step.
  if_cases C.
  - cfs C. eapply KF; [apply lmem_emem; exact L | lia |].
    unfold DINV in Hd. rewrite Hd. replace j with (length yb) by lia. rewrite skipn_all. reflexivity.
  - cfs C. step.
    eapply IH; [exact Hj0 | split; [exact L|] | weq | weq | weq].
    split; [lia|]. split; [exact Hk | exact Hd].
Qed.

Lemma back1 : forall Q (j0 j' : nat) out mk c a0 a1 a2 s1 s7 s11 bs,
  KFAIL Q -> LOOPIH Q j0 -> (j0 < j')%nat -> (j' <= length yb)%nat -> lmem mk out -> (length out < j')%nat ->
  DINV j' (out ++ [c]) -> bs = [Z_to_bv 8 c] -> 0 <= c < 256 ->
  s11 = Z_to_bv 64 (YA + Z.of_nat j') -> a1 = Z_to_bv 64 (scr + Z.of_nat (length out) + 1) ->
  evt rsegs Q (st 0x14f64 a0 a1 a2 s1 s7 s11 (write_to_mem mk (wa (scr + Z.of_nat (length out))) bs)).
Proof.
  intros Q j0 j' out mk c a0 a1 a2 s1 s7 s11 bs KF IH Hj0 Hj L Hk Hd Eb Hc E11 E1.
  eapply (back Q j0 KF IH j' (out ++ [c])); [exact Hj0 | exact Hj | | | exact Hd | exact E11 | ].
  - apply lmem_store1; [exact L | lia | reflexivity | exact Eb | exact Hc].
  - rewrite length_app. cbn. lia.
  - rewrite E1. weq.
Qed.

Lemma join : forall Q (j0 j' : nat) out' mk (n o : Z) a0 a1 a2 s1 s7 s11, KFAIL Q -> LOOPIH Q j0 ->
  (j0 < j')%nat -> (j' <= length yb)%nat -> lmem mk out' -> (length out' <= j')%nat -> DINV j' out' ->
  0 <= n <= 4 -> scr <= o -> o + n = scr + Z.of_nat (length out') ->
  a1 = Z_to_bv 64 n -> s7 = Z_to_bv 64 o -> s11 = Z_to_bv 64 (YA + Z.of_nat j') ->
  evt rsegs Q (st 0x150e0 a0 a1 a2 s1 s7 s11 mk).
Proof.
  intros Q j0 j' out' mk n o a0 a1 a2 s1 s7 s11 KF IH Hj0 Hj L Hk Hd Hn Ho Hon E1 E7 E11. subst a1 s7 s11. unfold st.
  pose proof len_yb as LY. pose proof scr_range as SR.
  step. step. notrap. step. notrap. step. notrap. step.
  eapply (back Q j0 KF IH j' out'); [exact Hj0 | exact Hj | exact L | exact Hk | exact Hd | reflexivity | weq].
Qed.

Lemma wr_scr_ok : forall mk' a, wr_at rsegs mk' scr (Z.of_nat (length x) + 1) -> scr <= a < scr + Z.of_nat (length x) + 1 ->
  store_ok rsegs mk' (wa a) 1 = true.
Proof.
  intros mk' a W Ha. replace a with (scr + (a - scr)) by lia.
  apply (wr_at_store_ok rsegs mk' scr (Z.of_nat (length x) + 1) (a - scr) 1); [exact W | lia | lia].
Qed.

Ltac sok1 W a := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  let S := fresh "S" in pose proof (wr_scr_ok mm a ltac:(repeat apply wr_at_write; exact W) ltac:(lia)) as S end.

Ltac lchain := repeat (apply lmem_store1; [ | rewrite ?length_app; cbn [length]; lia
                                           | unfold wa; f_equal; rewrite ?length_app; cbn [length]; lia | b1 | lia ]).

Lemma enc : forall Q (j0 j' : nat) out mk cp a0 a1 a2 s1 s7 s11, KFAIL Q -> LOOPIH Q j0 -> lmem mk out ->
  (j0 < j')%nat -> (j' <= length yb)%nat -> (length out + 4 <= j')%nat -> 0 < cp <= 1114111 ->
  DINV j' (out ++ utf8 cp) ->
  a0 = Z_to_bv 64 cp -> s7 = Z_to_bv 64 (scr + Z.of_nat (length out)) -> s11 = Z_to_bv 64 (YA + Z.of_nat j') ->
  evt rsegs Q (st 0x14f40 a0 a1 a2 s1 s7 s11 mk).
Proof.
  intros Q j0 j' out mk cp a0 a1 a2 s1 s7 s11 KF IH L Hj0 Hj Hk Hc Hd E0 E7 E11. subst a0 s7 s11. unfold st.
  pose proof len_yb as LY. pose proof scr_range as SR. pose proof sp_range as SP.
  pose proof (lmem_wr_scr _ _ L) as W.
  pose proof (lmem_store_ok mk out (Z.of_nat (length out)) L ltac:(lia)) as S0.
  step. step. if_cases K1.
  - cfs K1. step. step. if_cases K2.
    + cfs K2. step.
      destruct (Z.ltb_spec cp 65536) as [HC|HC].
      * rewrite (e3z cp) by lia. step. if_false.
        step. notrap. step. step. rewrite (e3a cp) by lia.
        step. step. notrap. step. step. step. rewrite (e_f52 cp) by lia.
        sok1 W (scr + Z.of_nat (length out) + 1). step.
        step. step. notrap. step. step. rewrite (enc_low cp) by lia.
        sok1 W (scr + Z.of_nat (length out) + 2). step.
        step. step.
        eapply (join Q j0 j' (((out ++ [224 + cp / 4096]) ++ [128 + (cp / 64) mod 64]) ++ [128 + cp mod 64]) _ 3
                  (scr + Z.of_nat (length out)));
          [exact KF | exact IH | exact Hj0 | exact Hj | | | | lia | lia | | weq | weq | weq].
        -- lchain. exact L.
        -- rewrite !length_app; cbn; lia.
        -- rewrite <- !app_assoc. cbn [app]. rewrite utf8_3 in Hd by lia. exact Hd.
        -- rewrite !length_app; cbn; lia.
      * rewrite (e4z cp) by lia. step. if_cases K3; [| cfs K3; exfalso; lia].
        step. notrap. step. step. rewrite (e4a cp) by lia.
        step. step. notrap. step. step. step. rewrite (e_f46 cp) by lia.
        sok1 W (scr + Z.of_nat (length out) + 1). step.
        step. step. notrap. step. step. step. rewrite (e_f52 cp) by lia.
        sok1 W (scr + Z.of_nat (length out) + 2). step.
        step. step. notrap. step. step. rewrite (enc_low cp) by lia.
        sok1 W (scr + Z.of_nat (length out) + 3). step.
        step.
        eapply (join Q j0 j' ((((out ++ [240 + cp / 262144]) ++ [128 + (cp / 4096) mod 64]) ++ [128 + (cp / 64) mod 64])
                                ++ [128 + cp mod 64]) _ 4 (scr + Z.of_nat (length out)));
          [exact KF | exact IH | exact Hj0 | exact Hj | | | | lia | lia | | weq | weq | weq].
        -- lchain. exact L.
        -- rewrite !length_app; cbn; lia.
        -- rewrite <- !app_assoc. cbn [app]. rewrite utf8_4 in Hd by lia. exact Hd.
        -- rewrite !length_app; cbn; lia.
    + cfs K2. step. notrap. step. step. rewrite (e2a cp) by lia.
      step. step. notrap. step. step. rewrite (enc_low cp) by lia.
      sok1 W (scr + Z.of_nat (length out) + 1). step.
      step. step.
      eapply (join Q j0 j' ((out ++ [192 + cp / 64]) ++ [128 + cp mod 64]) _ 2 (scr + Z.of_nat (length out)));
        [exact KF | exact IH | exact Hj0 | exact Hj | | | | lia | lia | | weq | weq | weq].
      * lchain. exact L.
      * rewrite !length_app; cbn; lia.
      * rewrite <- app_assoc. cbn [app]. rewrite utf8_2 in Hd by lia. exact Hd.
      * rewrite !length_app; cbn; lia.
  - cfs K1. step. notrap. step. step. step.
    eapply (join Q j0 j' (out ++ [cp]) _ 1 (scr + Z.of_nat (length out)));
      [exact KF | exact IH | exact Hj0 | exact Hj | | | | lia | lia | | weq | weq | weq].
    + apply lmem_store1; [exact L | lia | reflexivity | b1 | lia].
    + rewrite length_app; cbn; lia.
    + rewrite utf8_1 in Hd by lia. exact Hd.
    + rewrite length_app; cbn; lia.
Qed.

Lemma pair : forall Q (j : nat) out mk cp t a0 a1 a2 s1 s7 s11, KFAIL Q -> LOOPIH Q j -> lmem mk out ->
  (j + 6 <= length yb)%nat -> (length out <= j)%nat -> 55296 <= cp < 56320 ->
  bytes_at rsegs mk (SPZ + -108) (le4 (Z_to_bv 64 cp)) ->
  skipn (j + 6) yb = t ->
  decode yz = emit out (match map bv_unsigned t with
                        | _ :: _ :: _ :: _ :: _ :: _ :: r4 =>
                          match low (map bv_unsigned t) with
                          | Some lo => emit (utf8 (pair_cp cp lo)) (decode r4)
                          | None => None
                          end
                        | _ => None
                        end) ->
  s1 = Z_to_bv 64 (YA + Z.of_nat j) -> s7 = Z_to_bv 64 (scr + Z.of_nat (length out)) ->
  s11 = Z_to_bv 64 (YA + Z.of_nat j + 6) ->
  evt rsegs Q (st 0x14e98 a0 a1 a2 s1 s7 s11 mk).
Proof.
  intros Q j out mk cp t a0 a1 a2 s1 s7 s11 KF IH L Hj Hk Hc RB ET Hd E1 E7 E11. subst s1 s7 s11. unfold st.
  pose proof len_yb as LY. pose proof scr_range as SR. pose proof sp_range as SP.
  pose proof (lmem_y mk out (j + 6) L Hj) as Y. rewrite ET in Y.
  assert (LT : length yb = (j + 6 + length t)%nat) by (pose proof (length_skipn (j + 6) yb) as E; rewrite ET in E; lia).
  pose proof (lmem_rd_end _ _ L) as RE.
  step. step. step. step.
  if_cases K1.
  - cfs K1. eapply KF; [apply lmem_emem; exact L | lia |]. rewrite Hd.
    destruct t as [|d0 [|d1 [|d2 [|d3 [|d4 [|d5 t]]]]]]; cbn [length] in LT; try reflexivity. lia.
  - cfs K1. destruct t as [|d0 [|d1 [|d2 [|d3 [|d4 [|d5 t]]]]]]; cbn [length] in LT; try lia.
    cbn [map] in Hd. rewrite low_cons6 in Hd.
    pose proof (byte_range d0) as RD0. pose proof (byte_range d1) as RD1.
    pose proof (rd1 _ _ _ 0 d0 Y eq_refl) as R0. pose proof (rd1 _ _ _ 1 d1 Y eq_refl) as R1.
    step. step. if_cases K2.
    + cfs K2. eapply KF; [apply lmem_emem; exact L | lia |]. rewrite Hd, low_bs by lia. reflexivity.
    + cfs K2. step. notrap. step. step. if_cases K3.
      * cfs K3. eapply KF; [apply lmem_emem; exact L | lia |]. rewrite Hd, low_u by lia. reflexivity.
      * cfs K3.
        assert (H4 : bytes_at rsegs mk (YA + Z.of_nat j + 8) [d2; d3; d4; d5]).
        { pose proof (bytes_at_skipn rsegs _ _ _ 2 Y ltac:(cbn; lia)) as Y2. cbn [skipn] in Y2.
          apply (bytes_at_prefix rsegs _ _ _ t). replace (YA + Z.of_nat j + 8) with (YA + Z.of_nat (j + 6) + Z.of_nat 2) by lia.
          exact Y2. }
        step. step. notrap. step. step. step.
        eapply evt_cut.
        { eapply HEX4 with (p := YA + Z.of_nat j + 8) (out := SPZ + -112) (b0 := d2) (b1 := d3) (b2 := d4) (b3 := d5);
            [ weq | weq | lia | exact H4 | eapply lmem_slot_wr; [exact L | lia | lia] | Z.div_mod_to_equations; lia ]. }
        intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & RES).
        replace (ret_pc (Z_to_bv 64 85712)) with (Z_to_bv 64 85712) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        rewrite ex_hex4_val_hex4 in RES.
        destruct (hex4 [bv_unsigned d2; bv_unsigned d3; bv_unsigned d4; bv_unsigned d5]) as [lv|] eqn:HL.
        -- destruct RES as [-> RB2].
           destruct (hex4_some _ _ HL) as (h0 & h1 & h2 & h3 & hr & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlv).
           assert (L' : lmem m' out)
             by (eapply (lmem_call mk m' out (SPZ + -112) (le4 (Z_to_bv 64 lv)));
                 [exact L | lia | lia | rewrite length_le4; cbn; lia | exact MU | exact WM | exact RB2]).
           assert (RB' : bytes_at rsegs m' (SPZ + -108) (le4 (Z_to_bv 64 cp)))
             by (eapply bytes_at_transport; [exact RB | exact MU | rewrite length_le4; cbn; lia]).
           pose proof (bytes_at_read_whole rsegs _ _ _ RB2) as RV. rewrite length_le4 in RV.
           pose proof (bytes_at_read_whole rsegs _ _ _ RB') as RV2. rewrite length_le4 in RV2.
           pose proof (lmem_rd_c0 _ _ L') as RC.
           do 13 step. step. if_false.
           step. rewrite (sx32_small lv) by lia.
           do 3 step.
           rewrite (lo_val lv) by lia.
           step. if_cases K4.
           ++ rewrite (lo_chk lv) in K4 by lia.
              eapply KF; [apply lmem_emem; exact L' | lia |]. rewrite Hd, K2, K3, low_hex, HL.
              destruct ((56320 <=? lv) && (lv <=? 57343)); [discriminate K4 | reflexivity].
           ++ rewrite (lo_chk lv) in K4 by lia.
              apply negb_false_iff, andb_true_iff in K4. destruct K4 as [K4a K4b]. apply Z.leb_le in K4a, K4b.
              assert (HP1 : 65536 <= pair_cp cp lv <= 1114111) by (unfold pair_cp; lia).
              step. step. notrap.
              step. rewrite (sx32_small cp) by lia.
              do 5 step.
              swr cp lv.
              pose proof (lmem_slot m' out 20 4 L' ltac:(lia) ltac:(lia)) as SS.
              step.
              assert (ET2 : skipn (j + 6 + 6) yb = t) by exact (skipn_next _ _ _ [d0; d1; d2; d3; d4; d5] ET).
              eapply (enc Q j (j + 12) out _ (pair_cp cp lv));
                [exact KF | exact IH | | lia | lia | lia | lia | | weq | reflexivity | weq].
              ** apply lmem_stk_store; [exact L' | lia | lia | rewrite length_le4; cbn; lia].
              ** unfold DINV. rewrite Hd, K2, K3, low_hex, HL.
                 rewrite (proj2 (Z.leb_le 56320 lv) K4a), (proj2 (Z.leb_le lv 57343) K4b). cbn [andb].
                 rewrite emit_emit. replace (j + 12)%nat with (j + 6 + 6)%nat by lia. rewrite ET2. reflexivity.
        -- destruct RES as [-> ->].
           do 13 step. step. if_true.
           eapply KF; [apply lmem_emem; exact L | lia |]. rewrite Hd, K2, K3, low_hex, HL. reflexivity.
Qed.

Lemma uni : forall Q (j : nat) out mk e t a0 a1 a2 s1 s7 s11, KFAIL Q -> LOOPIH Q j -> lmem mk out ->
  (j + 2 <= length yb)%nat -> (length out <= j)%nat ->
  decode yz = emit out (decode (92 :: 117 :: map bv_unsigned t)) ->
  skipn j yb = Z_to_bv 8 92 :: e :: t ->
  a0 = Z_to_bv 64 ENDZ -> s1 = Z_to_bv 64 (YA + Z.of_nat j) -> s7 = Z_to_bv 64 (scr + Z.of_nat (length out)) ->
  s11 = Z_to_bv 64 (YA + Z.of_nat j + 2) ->
  evt rsegs Q (st 0x14e24 a0 a1 a2 s1 s7 s11 mk).
Proof.
  intros Q j out mk e t a0 a1 a2 s1 s7 s11 KF IH L Hj Hk Hd EY E0 E1 E7 E11. subst a0 s1 s7 s11. unfold st.
  pose proof len_yb as LY. pose proof scr_range as SR. pose proof sp_range as SP.
  pose proof (skipn_len_cons _ _ _ _ EY) as LT. cbn [length] in LT.
  pose proof (lmem_y mk out j L ltac:(lia)) as Y. rewrite EY in Y.
  step. step. step.
  if_cases K1.
  - cfs K1. eapply KF; [apply lmem_emem; exact L | lia |]. rewrite Hd, dec_u_short; [reflexivity | rewrite length_map; lia].
  - cfs K1. destruct t as [|c0 [|c1 [|c2 [|c3 t]]]]; cbn [length] in LT; try lia.
    cbn [map] in Hd.
    assert (H4 : bytes_at rsegs mk (YA + Z.of_nat j + 2) [c0; c1; c2; c3]).
    { pose proof (bytes_at_skipn rsegs _ _ _ 2 Y ltac:(cbn; lia)) as Y2. cbn [skipn] in Y2.
      apply (bytes_at_prefix rsegs _ _ _ t). replace (YA + Z.of_nat j + 2) with (YA + Z.of_nat j + Z.of_nat 2) by lia.
      exact Y2. }
    assert (ET : skipn (j + 6) yb = t) by exact (skipn_next _ _ _ [Z_to_bv 8 92; e; c0; c1; c2; c3] EY).
    step. step. step.
    eapply evt_cut.
    { eapply HEX4 with (p := YA + Z.of_nat j + 2) (out := SPZ + -108) (b0 := c0) (b1 := c1) (b2 := c2) (b3 := c3);
        [ weq | weq | lia | exact H4 | eapply lmem_slot_wr; [exact L | lia | lia] | Z.div_mod_to_equations; lia ]. }
    intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & RES).
    replace (ret_pc (Z_to_bv 64 85564)) with (Z_to_bv 64 85564) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite ex_hex4_val_hex4 in RES.
    destruct (hex4 [bv_unsigned c0; bv_unsigned c1; bv_unsigned c2; bv_unsigned c3]) as [v|] eqn:HV.
    + destruct RES as [-> RB].
      destruct (hex4_some _ _ HV) as (h0 & h1 & h2 & h3 & hr & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv).
      assert (L' : lmem m' out)
        by (eapply (lmem_call mk m' out (SPZ + -108) (le4 (Z_to_bv 64 v)));
            [exact L | lia | lia | rewrite length_le4; cbn; lia | exact MU | exact WM | exact RB]).
      pose proof (bytes_at_read_whole rsegs _ _ _ RB) as RV. rewrite length_le4 in RV.
      pose proof (lmem_rd_dc _ _ L') as RD.
      do 13 step.
      step. if_false.
      step. rewrite (sx32_small v) by lia.
      step. if_cases K2.
      * cfs K2. eapply KF; [apply lmem_emem; exact L' | lia |]. rewrite Hd, dec_u_zero; [reflexivity|]. rewrite HV. f_equal. lia.
      * cfs K2. step. gsimp. rewrite land_m1024 by lia. gsimp.
        step. step. if_cases K3.
        -- cfs K3. eapply KF; [apply lmem_emem; exact L' | lia |]. rewrite Hd, (dec_u_dc _ _ _ _ _ v); [reflexivity | exact HV | lia].
        -- cfs K3. step. step. notrap. step. step. if_cases K4.
           ++ cfs K4. eapply (enc Q j (j + 6) out m' v); [exact KF | exact IH | exact L' | lia | lia | lia | lia | | weq | reflexivity | weq].
              unfold DINV. rewrite Hd, (dec_u_bmp _ _ _ _ _ v); [| exact HV | lia | lia]. rewrite emit_emit, ET. reflexivity.
           ++ cfs K4.
              eapply (pair Q j out m' v t); [exact KF | exact IH | exact L' | lia | exact Hk | lia | exact RB | exact ET | | reflexivity | reflexivity | weq].
              rewrite Hd, (dec_u_hi _ _ _ _ _ v); [reflexivity | exact HV | lia].
    + destruct RES as [-> ->].
      do 13 step. step. if_true.
      eapply KF; [apply lmem_emem; exact L | lia |]. rewrite Hd, dec_u_hnone; [reflexivity | exact HV].
Qed.

Lemma esc : forall Q (j : nat) out mk t a0 a1 a2 s1 s7 s11, KFAIL Q -> LOOPIH Q j -> lmem mk out ->
  (j < length yb)%nat -> (length out <= j)%nat ->
  decode yz = emit out (decode (92 :: map bv_unsigned t)) ->
  skipn j yb = Z_to_bv 8 92 :: t ->
  a0 = Z_to_bv 64 ENDZ -> s1 = Z_to_bv 64 (YA + Z.of_nat j) -> s7 = Z_to_bv 64 (scr + Z.of_nat (length out)) ->
  s11 = Z_to_bv 64 (YA + Z.of_nat j + 1) ->
  evt rsegs Q (st 0x14e00 a0 a1 a2 s1 s7 s11 mk).
Proof.
  intros Q j out mk t a0 a1 a2 s1 s7 s11 KF IH L Hj Hk Hd EY E0 E1 E7 E11. subst a0 s1 s7 s11. unfold st.
  pose proof len_yb as LY. pose proof scr_range as SR. pose proof sp_range as SP.
  pose proof (skipn_len_cons _ _ _ _ EY) as LT.
  pose proof (lmem_y mk out j L ltac:(lia)) as Y. rewrite EY in Y.
  step.
  if_cases K1.
  - cfs K1. destruct t as [|e t]; [| cbn [length] in LT; lia].
    eapply KF; [apply lmem_emem; exact L | lia |]. rewrite Hd. reflexivity.
  - cfs K1. destruct t as [|e t]; [cbn [length] in LT; lia|].
    pose proof (byte_range e) as RE.
    pose proof (rd1 _ _ _ 1 e Y eq_refl) as R1.
    pose proof (lmem_store_ok mk out (Z.of_nat (length out)) L ltac:(lia)) as S0.
    assert (ET : skipn (j + 2) yb = t) by exact (skipn_next _ _ _ [Z_to_bv 8 92; e] EY).
    cbn [map] in Hd. cbn [length] in LT.
    step. notrap. step. step. step.
    if_cases K2.
    + cfs K2. step. if_cases K3.
      * cfs K3. step. if_cases K4.
        -- cfs K4. estore.
           eapply (back1 Q j (j + 2) out mk 92); [exact KF | exact IH | lia | lia | exact L | lia | | b1 | lia | weq | weq].
           unfold DINV. rewrite Hd, (dec_esc _ 92) by esc_solve. rewrite emit_emit, ET. reflexivity.
        -- cfs K4. step. if_cases K5.
           ++ cfs K5. eapply KF; [apply lmem_emem; exact L | lia |]. rewrite Hd, dec_esc_bad; [reflexivity | esc_solve | lia].
           ++ cfs K5. estore.
              eapply (back1 Q j (j + 2) out mk 8); [exact KF | exact IH | lia | lia | exact L | lia | | b1 | lia | weq | weq].
              unfold DINV. rewrite Hd, (dec_esc _ 8) by esc_solve. rewrite emit_emit, ET. reflexivity.
      * cfs K3. step. if_cases K4.
        -- cfs K4. estore.
           eapply (back1 Q j (j + 2) out mk 34); [exact KF | exact IH | lia | lia | exact L | lia | | b1 | lia | weq | weq].
           unfold DINV. rewrite Hd, (dec_esc _ 34) by esc_solve. rewrite emit_emit, ET. reflexivity.
        -- cfs K4. step. if_cases K5.
           ++ cfs K5. eapply KF; [apply lmem_emem; exact L | lia |]. rewrite Hd, dec_esc_bad; [reflexivity | esc_solve | lia].
           ++ cfs K5. estore.
              eapply (back1 Q j (j + 2) out mk 47); [exact KF | exact IH | lia | lia | exact L | lia | | b1 | lia | weq | weq].
              unfold DINV. rewrite Hd, (dec_esc _ 47) by esc_solve. rewrite emit_emit, ET. reflexivity.
    + cfs K2. step. if_cases K3.
      * cfs K3. step. if_cases K4.
        -- cfs K4. estore.
           eapply (back1 Q j (j + 2) out mk 12); [exact KF | exact IH | lia | lia | exact L | lia | | b1 | lia | weq | weq].
           unfold DINV. rewrite Hd, (dec_esc _ 12) by esc_solve. rewrite emit_emit, ET. reflexivity.
        -- cfs K4. step. if_cases K5.
           ++ cfs K5. eapply KF; [apply lmem_emem; exact L | lia |]. rewrite Hd, dec_esc_bad; [reflexivity | esc_solve | lia].
           ++ cfs K5. estore.
              eapply (back1 Q j (j + 2) out mk 10); [exact KF | exact IH | lia | lia | exact L | lia | | b1 | lia | weq | weq].
              unfold DINV. rewrite Hd, (dec_esc _ 10) by esc_solve. rewrite emit_emit, ET. reflexivity.
      * cfs K3. step. if_cases K4.
        -- cfs K4. estore.
           eapply (back1 Q j (j + 2) out mk 13); [exact KF | exact IH | lia | lia | exact L | lia | | b1 | lia | weq | weq].
           unfold DINV. rewrite Hd, (dec_esc _ 13) by esc_solve. rewrite emit_emit, ET. reflexivity.
        -- cfs K4. step. if_cases K5.
           ++ cfs K5. estore.
              eapply (back1 Q j (j + 2) out mk 9); [exact KF | exact IH | lia | lia | exact L | lia | | b1 | lia | weq | weq].
              unfold DINV. rewrite Hd, (dec_esc _ 9) by esc_solve. rewrite emit_emit, ET. reflexivity.
           ++ cfs K5. step. if_cases K6.
              ** cfs K6. eapply KF; [apply lmem_emem; exact L | lia |]. rewrite Hd, dec_esc_bad; [reflexivity | esc_solve | lia].
              ** cfs K6.
                 eapply (uni Q j out mk e t); [exact KF | exact IH | exact L | lia | exact Hk | rewrite Hd, K6; reflexivity | exact EY
                                                | reflexivity | reflexivity | reflexivity | weq].
Qed.

Lemma head : forall Q j out mk, KFAIL Q -> KSUCC Q -> LOOPIH Q j -> INV j out mk -> HEAD Q j out mk.
Proof.
  intros Q j out mk KF KS IH (L & Hj & Hk & Hd) a0 a1 a2 s1 s7 s11 E0 E7 E1. subst a0 s7 s1. unfold st.
  pose proof len_yb as LY. pose proof scr_range as SR. pose proof sp_range as SP.
  pose proof (lmem_y mk out j L ltac:(lia)) as Y.
  destruct (skipn j yb) as [|b t] eqn:EY.
  { exfalso. apply (f_equal (@length byte)) in EY. rewrite length_skipn in EY. cbn in EY. lia. }
  pose proof (skipn_len_cons _ _ _ _ EY) as LT.
  pose proof (byte_range b) as RB.
  pose proof (bytes_at_read0 rsegs _ _ _ _ Y) as R0.
  unfold DINV in Hd. rewrite EY in Hd. cbn [map] in Hd.
  step. step.
  if_cases K1.
  - cfs K1.
    eapply KS; [exact L | exact Hj | exact Hk | | reflexivity | reflexivity].
    rewrite Hd, K1, dec_quote. cbn [emit]. rewrite app_nil_r, (skipn_S_cons _ _ _ _ EY). reflexivity.
  - cfs K1. step. if_cases K2.
    + cfs K2. eapply KF; [apply lmem_emem; exact L | lia | ].
      rewrite Hd, dec_ctl by lia. reflexivity.
    + cfs K2. step. step. if_cases K3.
      * cfs K3.
        pose proof (lmem_store_ok mk out (Z.of_nat (length out)) L ltac:(lia)) as S0.
        estore.
        eapply (back1 Q j (S j) out mk (bv_unsigned b)); [exact KF | exact IH | lia | lia | exact L | lia | | b1 | lia | weq | weq].
        unfold DINV. rewrite Hd, dec_plain by lia. rewrite emit_emit, (skipn_S_cons _ _ _ _ EY). reflexivity.
      * cfs K3.
        assert (EB : b = Z_to_bv 8 92) by (rewrite <- (byte_bv_eta b), K3; reflexivity). subst b.
        eapply (esc Q j out mk t); [exact KF | exact IH | exact L | exact Hj | exact Hk | exact Hd | exact EY
                                   | reflexivity | reflexivity | reflexivity | weq].
Qed.

Lemma emit_nil : forall d, emit [] d = d.
Proof. intros [[s r]|]; reflexivity. Qed.

Lemma loop : forall Q, KFAIL Q -> KSUCC Q -> forall n j out mk, (length yb - j <= n)%nat -> INV j out mk -> HEAD Q j out mk.
Proof.
  intros Q KF KS n. induction n as [|n IHn]; intros j out mk Hn I.
  - destruct I as (_ & Hj & _). lia.
  - apply head; [exact KF | exact KS | | exact I].
    intros j' out' mk' Hj' I'. apply IHn; [| exact I']. destruct I as (_ & Hj & _). lia.
Qed.

Lemma entry : forall mk (w0 w1 : word) jk,
  bytes_at rsegs mk x0 x -> bytes_at rsegs mk (q + 8) (le8 (Z_to_bv 64 ENDZ)) ->
  rw_cells rsegs mk (SPZ + -128) [C8 w0; C8 w1; CB 8 jk; C8 ss11; C8 ss10; C8 ss9; C8 ss8; C8 ss7; C8 ss6; C8 ss5;
                                  C8 ss4; C8 ss3; C8 ss2; C8 ss1; C8 ss0; C8 sra] ->
  w0 = Z_to_bv 64 (-56613888) -> w1 = Z_to_bv 64 56320 ->
  munch [(SPZ + -128, SPZ)] m0 mk -> wmono rsegs m0 mk -> stk rsegs mk lo (SPZ + -128) ->
  lmem mk [].
Proof.
  intros mk w0 w1 jk BX BE FR -> -> MU WM ST.
  pose proof sp_range as SP. pose proof len_yb as LY.
  pose proof (stk_release rsegs mk lo (SPZ + -128) _ ST FR ltac:(lia)) as ST'.
  cbn [cells_size csize Nat.add] in ST'. replace (SPZ + -128 + Z.of_nat 128) with SPZ in ST' by lia.
  destruct FR as [[Hwf Hb] _]. cbn [cells_bytes cbytes] in Hb. cbn [cells_wf cell_wf] in Hwf.
  destruct Hwf as (_ & _ & Hj8 & _).
  rewrite app_nil_r in Hb.
  apply bytes_at_app in Hb. destruct Hb as [B0 Hb]. rewrite length_le8 in Hb.
  apply bytes_at_app in Hb. destruct Hb as [B1 Hb]. rewrite length_le8 in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb]. rewrite Hj8 in Hb.
  pose proof (bytes_at_skipn rsegs mk x0 x (S (Z.to_nat i0)) BX ltac:(lia)) as BY.
  replace (x0 + Z.of_nat (S (Z.to_nat i0))) with (x0 + i0 + 1) in BY by lia.
  unfold lmem, CST, SV.
  split; [exact BY|]. split; [exact BE|].
  split; [apply bytes_at_app; split; [exact B0 | rewrite length_le8; exact B1]|].
  split; [replace (SPZ + -104) with (SPZ + -128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia; exact Hb|].
  split; [apply bytes_at_nil; pose proof scr_range; lia|].
  split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros z Hz; tauto|].
  split; [exact WM | exact ST'].
Qed.

Lemma early_emem : forall mk jk,
  rw_cells rsegs mk (SPZ + -128) [CB 24 jk; C8 ss11; C8 ss10; C8 ss9; C8 ss8; C8 ss7; C8 ss6; C8 ss5;
                                  C8 ss4; C8 ss3; C8 ss2; C8 ss1; C8 ss0; C8 sra] ->
  munch [(SPZ + -128, SPZ)] m0 mk -> wmono rsegs m0 mk -> stk rsegs mk lo (SPZ + -128) -> emem mk 0.
Proof.
  intros mk jk FR MU WM ST.
  pose proof sp_range as SP.
  pose proof (stk_release rsegs mk lo (SPZ + -128) _ ST FR ltac:(lia)) as ST'.
  cbn [cells_size csize Nat.add] in ST'. replace (SPZ + -128 + Z.of_nat 128) with SPZ in ST' by lia.
  destruct FR as [[Hwf Hb] _]. cbn [cells_bytes cbytes] in Hb. cbn [cells_wf cell_wf] in Hwf.
  destruct Hwf as (Hj24 & _).
  rewrite app_nil_r in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb]. rewrite Hj24 in Hb.
  unfold emem, SV.
  split; [replace (SPZ + -104) with (SPZ + -128 + Z.of_nat 24) by lia; exact Hb|].
  split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros z Hz; tauto|].
  split; [exact WM | exact ST'].
Qed.

Lemma yb_nil : x0 + i0 + 1 >= x0 + Z.of_nat (length x) -> decode yz = None.
Proof. intros H. rewrite skipn_all2 by lia. reflexivity. Qed.

Lemma run : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evt rsegs POST (MS (mkR sra ssp gp tp t0 t1 t2 ss0 ss1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
                          ss2 ss3 ss4 ss5 ss6 ss7 ss8 ss9 ss10 ss11 t3 t4 t5 t6)
                     F (Z_to_bv 64 EX_STRING) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. unfold EX_STRING.
  pose proof (loop POST kfail ksucc) as LP. unfold HEAD in LP.
  pose proof kfail as KF. pose proof entry as ENT. pose proof early_emem as EE. pose proof yb_nil as YN.
  pose proof len_yb as LY. pose proof scr_range as SR. pose proof sp_range as SP. pose proof q_range as QR.
  pose proof lo_range as LR.
  assert (LQ : Z.land q 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact HQA).
  assert (MU : munch [(SPZ + -128, SPZ)] m0 m0) by apply munch_refl.
  assert (WM : wmono rsegs m0 m0) by apply wmono_refl.
  destruct (stk_carve rsegs m0 lo SPZ 128 HST ltac:(lia)) as [ST1 [junk FR]].
  replace (SPZ - Z.of_nat 128) with (SPZ + -128) in ST1, FR by lia.
  do 14 step.
  pose proof (bytes_at_read_whole rsegs _ _ _ HP) as R0. pose proof (bytes_at_read_whole rsegs _ _ _ HE) as R1.
  pose proof (bytes_at_read_whole rsegs _ _ _ HS) as R3.
  rewrite length_le8 in R0, R1, R3.
  step. step.
  gsimp. rewrite LQ.
  step. if_false.
  step. step. step. step. notrap.
  step. step. if_cases K.
  - cfs K. eapply KF; [eapply EE; eassumption | lia | apply YN; lia].
  - cfs K.
    steps_until 0x14dec.
    eapply (LP (length yb) 0%nat []); [lia | | weq | weq | weq].
    split; [| split; [lia | split; [cbn; lia | unfold DINV; cbn [skipn]; rewrite emit_nil; reflexivity]]].
    eapply ENT; [eassumption | eassumption | eassumption | apply Z_to_bv_eqm; reflexivity | apply Z_to_bv_eqm; reflexivity
                | eassumption | eassumption | eassumption].
Qed.

End Ubsan.

Theorem ex_string_holds : ex_hex4_contract -> ex_string_contract.
Proof.
  intros HEX4. unfold ex_string_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q x0 i0 scr lo x
    E0 QA HP HE HS WQ HX X0 XE XL I0 SC WS D1 D2 ST LO SA D3 D4 D5 MI.
  subst a0. unfold EX_STRING_K in *.
  eapply run; try eassumption; lia.
Qed.
