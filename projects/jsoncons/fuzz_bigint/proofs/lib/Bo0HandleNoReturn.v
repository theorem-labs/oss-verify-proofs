(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit MemsetLib As0StepLib Bo0MemIsZero Bo0RegionPoisoned
  Bo0AsanMemset Bo0AsanMemcpy Bo0StrlenIcpt Bo0TlsGetAddr ArtMem BrtPoison BrtPoisonRun.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BrtPoison3.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_67368_674cc Bo0_code_621f4_622cc Bo0_code_69c28_69cd8 Bo0_code_69a64_69a84 Bo0_code_487ec_4917c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma testbit_mask : forall k j i, (0 <= j <= k)%Z -> (0 <= i)%Z ->
  Z.testbit (2 ^ k - 2 ^ j) i = ((j <=? i) && (i <? k))%Z%bool.
Proof.
  intros k j i Hjk Hi.
  replace (2 ^ k - 2 ^ j)%Z with (Z.ones (k - j) * 2 ^ j)%Z.
  2:{ unfold Z.ones. rewrite Z.shiftl_1_l, <- Z.sub_1_r, Z.mul_sub_distr_r, <- Z.pow_add_r by lia. replace (k - j + j)%Z with k by lia. lia. }
  destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
  - rewrite Z.mul_pow2_bits_low by lia. symmetry. apply andb_false_intro1. apply Z.leb_gt. lia.
  - rewrite Z.mul_pow2_bits by lia. replace (j <=? i)%Z with true by (symmetry; apply Z.leb_le; lia).
    destruct (Z.lt_ge_cases i k) as [Hk|Hk].
    + rewrite Z.ones_spec_low by lia. symmetry. apply Z.ltb_lt. lia.
    + rewrite Z.ones_spec_high by lia. symmetry. apply Z.ltb_ge. lia.
Qed.

Lemma land_down : forall k j x, (0 <= j <= k)%Z -> (0 <= x < 2 ^ k)%Z -> Z.land x (2 ^ k - 2 ^ j) = (x - x mod 2 ^ j)%Z.
Proof.
  intros k j x Hjk Hx.
  assert (Hp : (0 < 2 ^ j)%Z) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.div_mod x (2 ^ j) ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x (2 ^ j) Hp) as Hm.
  set (q := (x / 2 ^ j)%Z) in *. set (r := (x mod 2 ^ j)%Z) in *.
  replace (x - r)%Z with (q * 2 ^ j)%Z by lia.
  rewrite Hdm. replace (2 ^ j * q + r)%Z with (q * 2 ^ j + r)%Z by lia.
  assert (Hq : (0 <= q)%Z) by lia.
  assert (Hqk : (q * 2 ^ j < 2 ^ k)%Z) by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_mask by lia.
  destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
  - replace (j <=? i)%Z with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
    rewrite andb_false_r. symmetry. apply Z.mul_pow2_bits_low. lia.
  - rewrite testbit_drop_low' by lia. replace (j <=? i)%Z with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
    destruct (Z.lt_ge_cases i k) as [Hik|Hik].
    + replace (i <? k)%Z with true by (symmetry; apply Z.ltb_lt; lia). now rewrite andb_true_r.
    + replace (i <? k)%Z with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
      symmetry. destruct (Z.eq_dec (q * 2 ^ j) 0) as [E|NE]; [rewrite E; apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|]. apply (Z.lt_le_trans _ (2 ^ k)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
  try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].
#[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
#[local] Ltac mldq F D z R :=
  chain_step; [reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F | reflexivity | exact D | maddr z; exact R | exact (bytes_le_to_Z_8 _)]
    | step_simpl; vnorm].
(* [comment removed for export] *)
#[local] Ltac stepsdq F D aa vv oktac :=
  chain_step; [reflexivity
    | eapply step_sd_at with (a := aa) (v := vv); [exact F | reflexivity | exact D | wval | gres; rwH; first [reflexivity | f_equal; lia] | oktac]
    | step_simpl].
#[local] Ltac mlbq F D z R :=
  chain_step; [reflexivity
    | eapply step_lb; [exact F | reflexivity | exact D | maddr z; exact R]
    | step_simpl; vnorm].

Lemma wbytes_out_any : forall bs m (addr x : word),
  (bv_unsigned addr + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (bv_unsigned x < bv_unsigned addr \/ bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m addr bs x = m x.
Proof.
  intros bs m addr x Hnw [Hx|Hx]; [apply wbytes_below; assumption | apply wbytes_above; exact Hx].
Qed.

Section HNR.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables s tpv key tsd ctx th top botth fs pu pat pg B n : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hs : (0x1000000 <= s - 4160)%Z /\ (s < 2 ^ 47)%Z.              (* [comment removed for export] *)
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 160)) 160%nat = true.
  Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
  Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
  Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
  Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
  Hypothesis Hth : (0 < th /\ th + 80 <= 2 ^ 64)%Z.
  Hypothesis Htop : (botth < top)%Z /\ (0 <= botth)%Z /\ (top mod 8 = 0)%Z.
  Hypothesis HB_def : B = (s - 4160 - (s - 4160) mod 4096)%Z.              (* [comment removed for export] *)
  Hypothesis Hn_def : n = (top - B)%Z.
  Hypothesis Hn : (8 <= n < 2 ^ 26)%Z.                                       (* [comment removed for export] *)
  Hypothesis Hhigh : (kHighMemBeg <= B)%Z /\ (top <= kHighMemEnd + 1)%Z.
  Hypothesis Hfs : (2 <= fs /\ fs + 97 < 2 ^ 64)%Z /\ (fs + 97 <= s - 160 \/ s <= fs + 96)%Z /\ (fs + 97 <= SB + B / 8 \/ SB + B / 8 + n / 8 <= fs + 96)%Z.
  Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = true.
  Hypothesis Hpu : (0 < pu < 2 ^ 64)%Z.
  Hypothesis Hpat : (0 <= pat < 2 ^ 64)%Z.
  Hypothesis Hpg : (0 <= pg /\ pg + 8 < 2 ^ 64)%Z /\ (pg + 8 <= s - 160 \/ s <= pg)%Z.
  Hypothesis HL : art_layout mem0.                                         (* [comment removed for export] *)
  Hypothesis HWsh : wr ASEGS mem0 (SB + B / 8) (n / 8).                     (* [comment removed for export] *)
  Hypothesis Hshdj : apart (SB + B / 8) (n / 8) (s - 160) 160.              (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HC : forall M', (forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) ->
     rdn ASEGS M' (0xdf418 : word) 1%nat = Some [Z_to_bv 8 1] /\                                       (* [comment removed for export] *)
     rdn ASEGS M' (0xd6508 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 pu)) /\               (* [comment removed for export] *)
     rdn ASEGS M' (0x10408 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 pat)) /\              (* [comment removed for export] *)
     rdn ASEGS M' (0xddfa0 : word) 1%nat = Some [Z_to_bv 8 1] /\                                       (* [comment removed for export] *)
     rdn ASEGS M' (0xddfa4 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
     rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
     rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
     rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\
     rdn ASEGS M' (0xd64a8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 pg)) /\               (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 pg) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)) /\
     rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\                                  (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (th + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 top)) /\        (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (th + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 botth)) /\     (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (th + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 fs)).           (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HCsh : forall M', (forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z ->
                                                 ~ (SB + B / 8 <= bv_unsigned x < SB + B / 8 + n / 8)%Z -> M' x = mem0 x) ->
     rdn ASEGS M' (0xddfa0 : word) 1%nat = Some [Z_to_bv 8 1] /\
     rdn ASEGS M' (0xddfa4 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
     rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
     rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
     rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\
     rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\
     rdn ASEGS M' (Z_to_bv 64 (th + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 fs)).

  (* [comment removed for export] *)
  Definition hnr_post (M' : word -> option byte) : Prop :=
    exists MF : word -> option byte,
      M' = Wn 1 MF (fs + 96) 1
      /\ (forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> MF x = Wf mem0 (SB + B / 8) (Z.to_nat (n / 8)) 0 x)
      /\ mem_grows mem0 MF.

  Lemma sp_sh : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Lemma wbytes_agree : forall l (m1 m2 : word -> option byte) (a x : word),
    m1 x = m2 x -> wbytes m1 a l x = wbytes m2 a l x.
  Proof.
    assert (G : forall l (m1 m2 : word -> option byte) (a x : word), m1 x = m2 x -> wbytes m1 a l x = wbytes m2 a l x).
    { induction l as [|b l IH]; intros m1 m2 a x Hm; cbn [wbytes]; [exact Hm|].
      apply IH. destruct (bv_eqb x a); [reflexivity | exact Hm]. }
    exact G.
  Qed.

  #[local] Ltac hide_dj := try hide Hfs; try hide Hpg; try hide Hshdj.

  Theorem hnr_run : forall regs,
    getr regs 4 = Z_to_bv 64 tpv -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x67368 : word) mem0 rom) (mkst regs' ra M' rom)
      /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs' /\ hnr_post M'.
  Proof.
    hide_dj.
    intros regs H4 H2 H1. rewrite sp_sh in H2.
    pose proof (Z.mod_pos_bound (s - 4160) 4096 ltac:(lia)) as HBm.
    assert (HB : (s - 4160 - 4095 <= B <= s - 4160)%Z /\ (B mod 4096 = 0)%Z).
    { rewrite HB_def. split; [lia|]. rewrite Zminus_mod, Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity. }
    unfold kHighMemBeg, kHighMemEnd in Hhigh.
    assert (HB8 : (B mod 8 = 0)%Z).
    { destruct HB as [HB1 HB2]. pose proof (Z.div_mod B 4096 ltac:(lia)) as D. rewrite HB2, Z.add_0_r in D.
      rewrite D. replace (4096 * (B / 4096))%Z with ((512 * (B / 4096)) * 8)%Z by lia. apply Z_mod_mult. }
    assert (Hn8 : (n mod 8 = 0)%Z).
    { rewrite Hn_def, Zminus_mod. destruct Htop as (_ & _ & T8). rewrite T8, HB8. reflexivity. }
    assert (ESB : SB = 2147450880%Z) by reflexivity.
    assert (HshB : (0 <= SB + B / 8)%Z /\ (SB + B / 8 + n / 8 < 2 ^ 64)%Z).
    { rewrite ESB. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
      assert (B / 8 <= 2 ^ 47 / 8)%Z by (apply Z.div_le_mono; lia). assert (n / 8 <= 2 ^ 26 / 8)%Z by (apply Z.div_le_mono; lia).
      change (2 ^ 47 / 8)%Z with 17592186044416%Z in *. change (2 ^ 26 / 8)%Z with 8388608%Z in *. lia. }
    assert (Hn8' : (0 < n / 8)%Z) by (apply Z.div_str_pos; lia).
    unhide Hfs. destruct Hfs as (Fs1 & Fs2 & Fs3). hide Fs2. hide Fs3.
    unhide Hpg. destruct Hpg as (Pg1 & Pg2). hide Pg2.
    assert (Hra : ret_ok (0x6739c : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (Hrb : ret_ok (0x673b4 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (Hrc : ret_ok (0x673e0 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (Hrd : ret_ok (0x67488 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (Hre : ret_ok (0x6748c : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (Hrf : ret_ok (0x674b0 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    (* [comment removed for export] *)
    set (M5 := wbytes (wbytes (wbytes (wbytes (wbytes mem0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                 (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18))) (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19))).
    set (M7 := wbytes (wbytes M5 (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x6739c))) (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 8))).
    set (M9 := wbytes (wbytes M7 (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 pat))) (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 pat))).
    #[local] Ltac oout := intros x Hx; pose proof (u64_range x);
       destruct Hx as [Hx|Hx]; [rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | unorm; lia]
                              | rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]].
    assert (O9 : forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> M9 x = mem0 x) by (unfold M9, M7, M5; oout).
    assert (G9 : mem_grows mem0 M9) by (unfold M9, M7, M5; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    #[local] Ltac sok := apply (store_ok_mono _ _ mem0); [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); first [apply mem_grows_refl | assumption] |];
                        apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 160)) _ 160%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia].
    destruct (HC M5 ltac:(unfold M5; oout)) as (A1 & _).
    assert (O7 : forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> M7 x = mem0 x) by (unfold M7, M5; oout).
    destruct (HC M7 O7) as (_ & A2 & B3 & _).
    (* [comment removed for export] *)
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x67368 : word) mem0 rom) (mkst r1 (0x69a64 : word) M9 rom)
              /\ (getr r1 9 = Z_to_bv 64 0xdf418 /\ getr r1 4 = Z_to_bv 64 tpv /\ getr r1 2 = Z_to_bv 64 (s - 80) /\ getr r1 1 = (0x673b4 : word)
                  /\ keeps_but [1; 2; 8; 9; 18; 19]%bv regs r1)).
    { unfold M9, M7, M5. eexists. split.
      - stepiv F_67368 D_67368 (Z_to_bv 64 (s - 80)) ltac:(wval).                                        (* [comment removed for export] *)
        stepsd F_6736c D_6736c (Z_to_bv 64 (s - 8)) ra ltac:(sok).                                          (* [comment removed for export] *)
        stepsd F_67370 D_67370 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok).
        stepsd F_67374 D_67374 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok).
        stepsd F_67378 D_67378 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok).
        stepsd F_6737c D_6737c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok).                             (* [comment removed for export] *)
        stepn F_67380 D_67380.                                                                             (* [comment removed for export] *)
        stepn F_67384 D_67384.                                                                             (* [comment removed for export] *)
        mlb F_67388 D_67388 (0xdf418 : word) A1.                                                           (* [comment removed for export] *)
        stepn F_6738c D_6738c.                                                                             (* [comment removed for export] *)
        stepfence F_67390 D_67390.
        stepb_ft F_67394 D_67394 ltac:(cond).                                                              (* [comment removed for export] *)
        stepn F_67398 D_67398.                                                                             (* [comment removed for export] *)
        stepiv F_621f4 D_621f4 (Z_to_bv 64 (s - 160)) ltac:(wval).                                       (* [comment removed for export] *)
        stepsd F_621f8 D_621f8 (Z_to_bv 64 (s - 88)) (Z_to_bv 64 0x6739c) ltac:(sok).                           (* [comment removed for export] *)
        stepsd F_621fc D_621fc (Z_to_bv 64 (s - 96)) (getr regs 8) ltac:(sok).                             (* [comment removed for export] *)
        stepn F_62200 D_62200.                                                                             (* [comment removed for export] *)
        mld F_62204 D_62204 (0xd6508 : word) A2.                                                           (* [comment removed for export] *)
        stepb_tk F_62208 D_62208 ltac:(cond).                                                              (* [comment removed for export] *)
        stepn F_622b0 D_622b0.                                                                             (* [comment removed for export] *)
        stepld F_622b4 D_622b4 (Z_to_bv 64 0x6739c) ltac:(maddr (s - 88)%Z; rewrite rdn_wbytes_out; [apply rdn_wbytes_hit8; unorm; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia]).   (* [comment removed for export] *)
        stepld F_622b8 D_622b8 (getr regs 8) ltac:(maddr (s - 96)%Z; apply rdn_wbytes_hit8; unorm; lia).    (* [comment removed for export] *)
        stepiv F_622bc D_622bc (Z_to_bv 64 (s - 80)) ltac:(wval).                                        (* [comment removed for export] *)
        stepret F_622c0 D_622c0 (0x6739c : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        stepb_ft F_6739c D_6739c ltac:(cond).                                                              (* [comment removed for export] *)
        stepn F_673a0 D_673a0.                                                                             (* [comment removed for export] *)
        mld F_673a4 D_673a4 (0x10408 : word) B3.                                                           (* [comment removed for export] *)
        stepsd F_673a8 D_673a8 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 pat) ltac:(sok).                         (* [comment removed for export] *)
        stepsd F_673ac D_673ac (Z_to_bv 64 (s - 56)) (Z_to_bv 64 pat) ltac:(sok).                         (* [comment removed for export] *)
        stepn F_673b0 D_673b0.                                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q9 & Q4 & Q2 & Q1 & K1).
    (* [comment removed for export] *)
    destruct (get_current_thread_run r1 M9 rom (0x673b4 : word) (s - 80) tpv key tsd ctx th Q2 Q4 Q1 Hrb ltac:(lia) ltac:(lia) Htp Hkey Htsd Hctx ltac:(lia)
                ltac:(replace (s - 80 - 16)%Z with (s - 96)%Z by lia; unfold M9, M7, M5; sok)) as (r2 & RUN2 & T10 & T2 & T1 & K2).
    { intros M' HM'. assert (O' : forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x).
      { intros x Hx. rewrite (HM' x) by lia. apply O9. exact Hx. }
      destruct (HC M' O') as (_ & _ & _ & C4 & C5 & C6 & C7 & C8 & _). repeat split; assumption. }
    set (M10 := wbytes M9 (Z_to_bv 64 (s - 80 - 8)) (word_to_le_bytes 8 (0x673b4 : word))) in RUN2.
    assert (O10 : forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> M10 x = mem0 x).
    { intros x Hx. rewrite <- (O9 x Hx). unfold M10. revert x Hx. oout. }
    destruct (HC M10 O10) as (_ & _ & _ & _ & _ & _ & _ & _ & D9 & D10 & D11 & D12 & D13 & _).
    assert (T9 : getr r2 9 = Z_to_bv 64 0xdf418) by (rewrite (K2 9%bv) by (cbv; intuition discriminate); exact Q9).
    assert (T4 : getr r2 4 = Z_to_bv 64 tpv) by (rewrite (K2 4%bv) by (cbv; intuition discriminate); exact Q4).
    set (M12 := wbytes (wbytes M10 (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 top))) (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 B))).
    (* [comment removed for export] *)
    assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x673b4 : word) M10 rom) (mkst r3 (0x611f8 : word) M12 rom)
              /\ (getr r3 10 = Z_to_bv 64 B /\ getr r3 11 = Z_to_bv 64 n /\ getr r3 12 = Z_to_bv 64 0 /\ getr r3 4 = Z_to_bv 64 tpv
                  /\ getr r3 2 = Z_to_bv 64 (s - 80) /\ getr r3 1 = (0x67488 : word) /\ keeps_but [1; 2; 8; 9; 18; 19]%bv r2 r3)).
    { eexists. split.
      - stepb_ft F_673b4 D_673b4 ltac:(cond).                                                              (* [comment removed for export] *)
        stepn F_673b8 D_673b8.                                                                             (* [comment removed for export] *)
        mld F_673bc D_673bc (0xd64a8 : word) D9.                                                           (* [comment removed for export] *)
        mldq F_673c0 D_673c0 pg D10.                                                                        (* [comment removed for export] *)
        stepb_tk F_673c4 D_673c4 ltac:(cond).                                                              (* [comment removed for export] *)
        stepn F_673dc D_673dc.                                                                             (* [comment removed for export] *)
        mlbq F_69c28 D_69c28 (th + 40)%Z D11.                                                               (* [comment removed for export] *)
        stepfence F_69c2c D_69c2c.
        stepb_tk F_69c30 D_69c30 ltac:(rwH; cbn; cond).                                                    (* [comment removed for export] *)
        mldq F_69c68 D_69c68 (th + 8)%Z D12.                                                                (* [comment removed for export] *)
        mldq F_69c6c D_69c6c (th + 16)%Z D13.                                                               (* [comment removed for export] *)
        stepov F_69c70 D_69c70 (Z_to_bv 64 1) ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (botth <? top)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).  (* [comment removed for export] *)
        stepn F_69c74 D_69c74.                                                                             (* [comment removed for export] *)
        stepov F_69c78 D_69c78 (Z_to_bv 64 top) ltac:(gres; rwH; unfold v_and; imm_norm; unorm; rewrite Z.land_comm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia).  (* [comment removed for export] *)
        stepret F_69c7c D_69c7c (0x673e0 : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        stepiv F_673e0 D_673e0 (Z_to_bv 64 top) ltac:(wval).                                              (* [comment removed for export] *)
        stepsdq F_673e4 D_673e4 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 top) ltac:(unfold M10, M9, M7, M5; sok). (* [comment removed for export] *)
        stepiv F_673e8 D_673e8 (Z_to_bv 64 (s - 64)) ltac:(wval).                                         (* [comment removed for export] *)
        stepiv F_673ec D_673ec (Z_to_bv 64 (s - 4160)) ltac:(wval).                                       (* [comment removed for export] *)
        stepn F_673f0 D_673f0.                                                                             (* [comment removed for export] *)
        stepov F_673f4 D_673f4 (Z_to_bv 64 B)
          ltac:(gres; rwH; unfold v_and; imm_norm; unorm; change 18446744073709547520%Z with (2 ^ 64 - 2 ^ 12)%Z; rewrite land_down by lia; rewrite HB_def; f_equal; change (2 ^ 12)%Z with 4096%Z; lia).   (* [comment removed for export] *)
        stepsdq F_673f8 D_673f8 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 B) ltac:(unfold M10, M9, M7, M5; sok).   (* [comment removed for export] *)
        stepiv F_673fc D_673fc (Z_to_bv 64 n) ltac:(gres; rwH; unfold v_sub; unorm; rewrite Hn_def; reflexivity).   (* [comment removed for export] *)
        stepn F_67400 D_67400.                                                                             (* [comment removed for export] *)
        stepn F_67404 D_67404.                                                                             (* [comment removed for export] *)
        stepb_tk F_67408 D_67408 ltac:(cond).                                                              (* [comment removed for export] *)
        stepiv F_6746c D_6746c (Z_to_bv 64 (n + 7)) ltac:(wval).                                          (* [comment removed for export] *)
        stepn F_67470 D_67470.                                                                             (* [comment removed for export] *)
        stepn F_67474 D_67474.                                                                             (* [comment removed for export] *)
        stepov F_67478 D_67478 (Z_to_bv 64 n)
          ltac:(gres; rwH; unfold v_and; imm_norm; unorm; change 268435448%Z with (2 ^ 28 - 2 ^ 3)%Z; rewrite land_down by lia; f_equal;
                change (2 ^ 3)%Z with 8%Z; rewrite <- Zplus_mod_idemp_l, Hn8; replace ((0 + 7) mod 8)%Z with 7%Z by reflexivity; lia).                  (* [comment removed for export] *)
        stepiv F_6747c D_6747c (Z_to_bv 64 B) ltac:(wval).                                                (* [comment removed for export] *)
        stepn F_67480 D_67480.                                                                             (* [comment removed for export] *)
        stepn F_67484 D_67484.                                                                             (* [comment removed for export] *)
        unfold M12. apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (match goal with |- ?g => check_closed_term g; apply bv_eq; vm_compute; reflexivity end). solve_keeps_but. }
    destruct S3 as (r3 & RUN3 & U10 & U11 & U12 & U4 & U2 & U1 & K3).
    (* [comment removed for export] *)
    assert (O12 : forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> M12 x = mem0 x).
    { intros x Hx. rewrite <- (O10 x Hx). unfold M12. revert x Hx. oout. }
    assert (G12 : mem_grows mem0 M12).
    { unfold M12, M10. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). first [apply mem_grows_refl | exact G9]. }
    assert (L12 : art_layout M12).
    { pose proof HL as L0. unfold art_layout, cell in L0 |- *.
      rewrite !(rdn_ext ASEGS _ M12 mem0) by (first [cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | intros x Hx; apply O12; revert Hx; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; intros Hx; lia]).
      exact L0. }
    assert (W12 : wr ASEGS M12 (s - 80 - 64) 64).
    { intros d k Hd Hk. apply (store_ok_mono _ _ mem0 M12 _ G12).
      apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 160)) _ 160%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat] in *; lia]. }
    unhide Hshdj.
    destruct (BrtPoison3.art_poison3_run r3 M12 rom (0x67488 : word) (s - 80) B n 0 U1 Hrd U2 U10 U11 U12 ltac:(lia) ltac:(lia) W12
                ltac:(unfold apart; lia) ltac:(unfold apart; lia) L12 ltac:(right; unfold BrtPoison3.art_poison_hi_ok, kHighMemBeg, kHighMemEnd; lia) HB8 Hn8 ltac:(lia) ltac:(lia)
                ltac:(intros _; apply Z.div_lt_upper_bound; lia) ltac:(eapply wr_grows; [exact G12 | exact HWsh]))
      as (r4 & RUN4 & P10 & P1 & P2 & P8 & P9 & P18 & P19 & P20 & P21 & PK).
    match type of RUN4 with msteps _ _ (mkst _ _ ?m _) => set (M13 := m) in RUN4 end.
    assert (APF : forall x : word, (bv_unsigned x < s - 160 \/ s - 80 <= bv_unsigned x)%Z ->
              art_poison_frame M12 (s - 80) (bv_unsigned (0x67488 : word)) (bv_unsigned (getr r3 8)) (bv_unsigned (getr r3 9)) (bv_unsigned (getr r3 18))
                               (bv_unsigned (getr r3 19)) (bv_unsigned (getr r3 20)) (bv_unsigned (getr r3 21)) x = M12 x).
    { intros x Hx. unfold art_poison_frame. rewrite !Wn_outside; first [reflexivity | lia | cbn [Z.of_nat Pos.to_nat]; lia]. }
    assert (O13 : forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> ~ (SB + B / 8 <= bv_unsigned x < SB + B / 8 + n / 8)%Z -> M13 x = mem0 x).
    { intros x Hx Hnx. unfold M13, Wf. pose proof (u64_range x).
      destruct (Z.lt_ge_cases (bv_unsigned x) (SB + B / 8)) as [L|G].
      - rewrite wbytes_below; [| rewrite repeat_length; unorm; lia | unorm; lia]. rewrite APF by lia. apply O12. exact Hx.
      - rewrite wbytes_above by (rewrite repeat_length; unorm; lia). rewrite APF by lia. apply O12. exact Hx. }
    assert (G13 : mem_grows mem0 M13).
    { unfold M13. eapply mem_grows_trans; [|apply Wf_grows]. unfold art_poison_frame. do 7 (eapply mem_grows_trans; [|apply Wn_grows]). exact G12. }
    assert (P4 : getr r4 4 = Z_to_bv 64 tpv) by (rewrite (PK 4%bv) by (unfold art_poison_kept; repeat split; discriminate); exact U4).
    (* [comment removed for export] *)
    assert (S4 : exists r4b, msteps ASEGS (mkst r4 (0x67488 : word) M13 rom) (mkst r4b (0x69a64 : word) M13 rom)
              /\ (getr r4b 2 = Z_to_bv 64 (s - 80) /\ getr r4b 4 = Z_to_bv 64 tpv /\ getr r4b 1 = (0x6748c : word) /\ keeps_but [1]%bv r4 r4b)).
    { eexists. split.
      - stepn F_67488 D_67488. apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (match goal with |- ?g => check_closed_term g; apply bv_eq; vm_compute; reflexivity end). solve_keeps_but. }
    destruct S4 as (r4b & RUN4b & Pb2 & Pb4 & Pb1 & K4b).
    destruct (get_current_thread_run r4b M13 rom (0x6748c : word) (s - 80) tpv key tsd ctx th Pb2 Pb4 Pb1 Hre ltac:(lia) ltac:(lia) Htp Hkey Htsd Hctx ltac:(lia)
                ltac:(replace (s - 80 - 16)%Z with (s - 96)%Z by lia; apply (store_ok_mono _ _ mem0 M13 _ G13);
                      apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 160)) _ 160%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]))
      as (r5 & RUN5 & V10 & V2 & V1 & K5).
    { intros M' HM'. destruct (HCsh M') as (C1 & C2 & C3 & C4 & C5 & _); [|repeat split; assumption].
      intros x Hx Hnx. rewrite (HM' x) by lia. apply O13; assumption. }
    set (M14 := wbytes M13 (Z_to_bv 64 (s - 80 - 8)) (word_to_le_bytes 8 (0x6748c : word))) in RUN5.
    assert (O14 : forall x : word, (bv_unsigned x < s - 160 \/ s <= bv_unsigned x)%Z -> ~ (SB + B / 8 <= bv_unsigned x < SB + B / 8 + n / 8)%Z -> M14 x = mem0 x).
    { intros x Hx Hnx. rewrite <- (O13 x Hx Hnx). unfold M14. pose proof (u64_range x).
      destruct Hx as [Hx|Hx]; [rewrite wbytes_below; [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia]
                             | rewrite wbytes_above; [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia]]. }
    destruct (HCsh M14 O14) as (_ & _ & _ & _ & _ & E6 & E7).
    assert (G14 : mem_grows mem0 M14) by (unfold M14; eapply mem_grows_trans; [exact G13 | apply wbytes_grows]).
    set (M15 := wbytes M14 (Z_to_bv 64 (fs + 96)) [Z_to_bv 8 1]).
    unhide Fs2. unhide Fs3.
    (* [comment removed for export] *)
    assert (SL : forall k v, (k = 8 /\ v = ra \/ k = 16 /\ v = getr regs 8 \/ k = 24 /\ v = getr regs 9 \/ k = 32 /\ v = getr regs 18 \/ k = 40 /\ v = getr regs 19)%Z ->
                 rdn ASEGS M15 (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v)).
    { intros k v Hk. assert (Hk' : (8 <= k <= 40)%Z) by lia.
      rewrite (rdn_ext ASEGS 8 M15 M5); [| unorm; cbn; lia |].
      - unfold M5. destruct Hk as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]];
          repeat (rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ]);
          apply rdn_wbytes_hit8; unorm; lia.
      - intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. pose proof (u64_range x).
        unfold M15. rewrite wbytes_out_any; [| cbn [length Z.of_nat Pos.to_nat]; unorm; lia | cbn [length Z.of_nat Pos.to_nat]; unorm; lia].
        unfold M14. rewrite wbytes_above by (rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia).
        unfold M13, Wf. rewrite wbytes_out_any; [| rewrite repeat_length; unorm; lia | rewrite repeat_length; unorm; unfold apart in Hshdj; lia].
        rewrite APF by lia. unfold M12, M10, M9, M7.
        rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]. }
    eexists. exists M15. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      eapply msteps_trans; [exact RUN4b|]. eapply msteps_trans; [exact RUN5|].
      stepb_ft F_6748c D_6748c ltac:(cond).                                                                (* [comment removed for export] *)
      mlbq F_67490 D_67490 (th + 40)%Z E6.                                                                  (* [comment removed for export] *)
      stepb_ft F_67494 D_67494 ltac:(rwH; cbn; cond).                                                      (* [comment removed for export] *)
      mldq F_67498 D_67498 (th + 72)%Z E7.                                                                  (* [comment removed for export] *)
      stepiv F_6749c D_6749c (Z_to_bv 64 0) ltac:(gres; rwH; unfold v_sltiu; imm_norm; unorm; change (bv_wrap 64 2) with 2%Z; replace (fs <? 2)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).  (* [comment removed for export] *)
      stepn F_674a0 D_674a0.                                                                               (* [comment removed for export] *)
      stepov F_674a4 D_674a4 (Z_to_bv 64 fs) ltac:(gres; rwH; unfold v_and; imm_norm; unorm; rewrite Z.land_comm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; f_equal; apply Z.mod_small; lia).   (* [comment removed for export] *)
      stepb_ft F_674a8 D_674a8 ltac:(cond).                                                                (* [comment removed for export] *)
      stepn F_674ac D_674ac.                                                                               (* [comment removed for export] *)
      stepn F_48ad4 D_48ad4.                                                                               (* [comment removed for export] *)
      chain_step; [reflexivity | eapply (step_sb_at ASEGS) with (a := Z_to_bv 64 (fs + 96)) (b := Z_to_bv 8 1);
          [exact F_48ad8 | reflexivity | exact D_48ad8 | wval | gres; reflexivity | apply bv_eq; vm_compute; reflexivity
          | apply (store_ok_mono _ _ mem0 M14 _ G14); exact Hwfs ] | step_simpl; vnorm].                   (* [comment removed for export] *)
      change (wbytes M14 (Z_to_bv 64 (fs + 96)) [Z_to_bv 8 1]) with M15.
      stepret F_48adc D_48adc (0x674b0 : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      #[local] Ltac slv := first [left; split; reflexivity | right; left; split; reflexivity | right; right; left; split; reflexivity | right; right; right; left; split; reflexivity | right; right; right; right; split; reflexivity].
      stepld F_674b0 D_674b0 ra ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 8)) by (symmetry; wval) end; apply SL; slv).                                                            (* [comment removed for export] *)
      stepld F_674b4 D_674b4 (getr regs 8) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 16)) by (symmetry; wval) end; apply SL; slv).
      stepld F_674b8 D_674b8 (getr regs 9) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 24)) by (symmetry; wval) end; apply SL; slv).
      stepld F_674bc D_674bc (getr regs 18) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 32)) by (symmetry; wval) end; apply SL; slv).
      stepld F_674c0 D_674c0 (getr regs 19) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 40)) by (symmetry; wval) end; apply SL; slv).                                               (* [comment removed for export] *)
      stepiv F_674c4 D_674c4 (Z_to_bv 64 s) ltac:(wval).                                                  (* [comment removed for export] *)
      stepret F_674c8 D_674c8 ra ltac:(rwH; reflexivity).
      apply mst_refl.
    - split; [gres; symmetry; apply sp_sh|]. split; [gres; reflexivity|]. split.
      + (* [comment removed for export] *)
        assert (KP : keeps_but [1; 2; 8; 9; 18; 19]%bv r3 r4).
        { intros r Hr HnL. apply PK. clear -Hr. unfold art_poison_kept. cbv in Hr. repeat split; intros ->; intuition discriminate. }
        assert (KB : keeps_but [1; 2; 8; 9; 18; 19]%bv regs r5).
        { eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [intros r Hr HnL; apply K2; [exact Hr | clear -HnL; cbv in HnL |- *; intuition]|].
          eapply keeps_but_trans; [exact K3|]. eapply keeps_but_trans; [exact KP|].
          eapply keeps_but_trans; [intros r Hr HnL; apply K4b; [exact Hr | clear -HnL; cbv in HnL |- *; intuition]|].
          intros r Hr HnL; apply K5; [exact Hr | clear -HnL; cbv in HnL |- *; intuition]. }
        intros r Hcs. destruct (decide (r = 1%bv)) as [->|Nq1]; [gres; rewrite H1; reflexivity|].
        destruct (decide (r = 2%bv)) as [->|Nq2]; [gres; rewrite H2; reflexivity|].
        destruct (decide (r = 8%bv)) as [->|Dq8]; [gres; reflexivity|]. destruct (decide (r = 9%bv)) as [->|Dq9]; [gres; reflexivity|].
        destruct (decide (r = 18%bv)) as [->|Dq18]; [gres; reflexivity|]. destruct (decide (r = 19%bv)) as [->|Dq19]; [gres; reflexivity|].
        repeat (rewrite getr_other; [| intros ->; first [match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end | clear -Hcs; cbv in Hcs; intuition discriminate]]).
        apply KB; [exact Hcs|]. clear -Nq1 Nq2 Dq8 Dq9 Dq18 Dq19. cbv. intuition congruence.
      + (* [comment removed for export] *)
        exists M14. split; [unfold M15, Wn; reflexivity|]. split; [|exact G14].
        intros x Hx. unfold M14. pose proof (u64_range x).
        rewrite wbytes_out_any; [| rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
        unfold M13, Wf. apply wbytes_agree. rewrite APF by lia. apply O12. exact Hx.
  Qed.
End HNR.
End FPX_1.
