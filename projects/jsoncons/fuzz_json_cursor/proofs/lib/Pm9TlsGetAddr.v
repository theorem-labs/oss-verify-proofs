(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib Pm9MemIsZero Pm9RegionPoisoned Pm9AsanMemset Pm9AsanMemcpy Pm9StrlenIcpt.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  Pm9_code_6a000_6b000 Pm9_code_72000_73000 Pm9_code_83000_84000 Pm9_code_8a000_8b000 Pm9_code_98000_99000 Pm9_code_147000_148000 Pm9_code_149000_14a000
   .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Lemma v_lw_small : forall z, (0 <= z < 2 ^ 31)%Z -> v_lw (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold v_lw. f_equal. rewrite u_Z2bv by lia. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z. rewrite Z.mod_small; lia.
Qed.
Lemma zbv_mod : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z. apply Z.mod_mod. lia.
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
  gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli, v_slli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  try change (2 ^ 3)%Z with 8%Z; try change (2 ^ 4)%Z with 16%Z; first [reflexivity | f_equal; lia].
#[local] Ltac vlit := gres; rwH; apply bv_eq; vm_compute; reflexivity.
#[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.

#[local] Ltac mldq F D z R :=
  chain_step; [reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F | reflexivity | exact D | maddr z; exact R | exact (bytes_le_to_Z_8 _)]
    | step_simpl; vnorm].
#[local] Ltac mlwq F D z R :=
  chain_step; [reflexivity
    | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 _)); [exact F | reflexivity | exact D | maddr z; exact R | apply bytes_le_to_Z_4; unorm; lia]
    | step_simpl; vnorm; rewrite v_lw_small by lia].
#[local] Ltac mlbuq F D z R :=
  chain_step; [reflexivity
    | eapply step_lbu; [exact F | reflexivity | exact D | maddr z; exact R]
    | step_simpl; vnorm].
#[local] Ltac peel :=
  rewrite rdn_wbytes_out;
    [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia
      | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia ].

Lemma musl_tls_get_addr_run : forall regs (M rom : word -> option byte) (ret : word) (d tpv md off dtv ent : Z),
  getr regs 10 = Z_to_bv 64 d -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 1 = ret -> ret_ok ret ->
  (0 <= d /\ d + 16 <= 2 ^ 64)%Z -> (8 <= tpv < 2 ^ 64)%Z -> (0 <= md < 2 ^ 16)%Z -> (0 <= off < 2 ^ 64)%Z -> (0 <= dtv /\ dtv + 8 * md + 8 <= 2 ^ 64)%Z -> (0 <= ent < 2 ^ 64)%Z ->
  rdn ASEGS M (Z_to_bv 64 d) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 md)) ->
  rdn ASEGS M (Z_to_bv 64 (d + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 off)) ->
  rdn ASEGS M (Z_to_bv 64 (tpv - 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 dtv)) ->
  rdn ASEGS M (Z_to_bv 64 (dtv + 8 * md)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ent)) ->
  exists regs',
    msteps ASEGS (mkst regs (0x1474a4 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 ((ent + off) mod 2 ^ 64) /\ keeps_but [1]%bv regs regs'.
Proof.
  intros regs M rom ret d tpv md off dtv ent H10 H4 H1 Hret Hd Htp Hmd Hoff Hdtv Hent R1 R2 R3 R4.
  pose proof (Z.mod_pos_bound (ent + off) (2 ^ 64) ltac:(lia)) as Hm.
  eexists. split.
  - stepiv F_147468 D_147468 (Z_to_bv 64 tpv) ltac:(wval).
    mldq F_14746c D_14746c d R1.
    mldq F_147470 D_147470 (tpv - 8)%Z R3.
    mldq F_147474 D_147474 (d + 8)%Z R2.
    stepiv F_147478 D_147478 (Z_to_bv 64 (8 * md)) ltac:(wval).
    stepiv F_14747c D_14747c (Z_to_bv 64 (dtv + 8 * md)) ltac:(wval).
    mldq F_147480 D_147480 (dtv + 8 * md)%Z R4.
    stepiv F_147484 D_147484 (Z_to_bv 64 ((ent + off) mod 2 ^ 64)) ltac:(gres; rwH; unfold v_add; unorm; rewrite zbv_mod; f_equal; lia).
    stepret F_147488 D_147488 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; reflexivity | solve_keeps_but].
Qed.

Lemma get_current_thread_run : forall regs (M rom : word -> option byte) (ret : word) (t tpv key tsd ctx th : Z),
  getr regs 2 = Z_to_bv 64 t -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 1 = ret -> ret_ok ret ->
  (0x1000000 <= t - 16)%Z -> (t < 2 ^ 64)%Z -> (96 <= tpv < 2 ^ 64)%Z -> (0 <= key < 2 ^ 28)%Z ->
  (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z -> (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z -> (0 <= th < 2 ^ 64)%Z ->
  store_ok ASEGS M (Z_to_bv 64 (t - 16)) 16%nat = true ->

  (forall M', (forall x : word, (bv_unsigned x < t - 16 \/ t <= bv_unsigned x)%Z -> M' x = M x) ->
     rdn ASEGS M' (0x15d560 : word) 1%nat = Some [Z_to_bv 8 1] /\
     rdn ASEGS M' (0x15d564 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
     rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
     rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
     rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th))) ->
  exists regs',
    msteps ASEGS (mkst regs (0x8ae84 : word) M rom) (mkst regs' ret (wbytes M (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ret)) rom)
    /\ getr regs' 10 = Z_to_bv 64 th /\ getr regs' 2 = Z_to_bv 64 t /\ getr regs' 1 = ret /\ keeps_but [1; 2]%bv regs regs'.
Proof.
  intros regs M rom ret t tpv key tsd ctx th H2 H4 H1 Hret Ht1 Ht2 Htp Hkey Htsd Hctx Hth Hok HC.
  set (M1 := wbytes M (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ret)).
  destruct (HC M1) as (C1 & C2 & C3 & C4 & C5).
  { intros x Hx. unfold M1. pose proof (u64_range x).
    destruct Hx as [Hx|Hx]; [rewrite wbytes_below; [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia]
                           | rewrite wbytes_above; [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia]]. }
  assert (Hra : ret_ok (0x8ae90 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
  eexists. split.
  - stepiv F_8ae3c D_8ae3c (Z_to_bv 64 (t - 16)) ltac:(wval).
    stepsd F_8ae40 D_8ae40 (Z_to_bv 64 (t - 8)) ret
      ltac:(apply (store_ok_sub ASEGS M (Z_to_bv 64 (t - 16)) _ 16%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).
    change (wbytes M (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ret)) with M1.
    stepn F_8ae44 D_8ae44.
    stepn F_834bc D_834bc.
    stepn F_834c0 D_834c0.
    mlbu F_834c4 D_834c4 (0x15d560 : word) C1.
    stepb_ft F_834c8 D_834c8 ltac:(cond).
    mlw F_834cc D_834cc (0x15d564 : word) C2.
    stepn F_834d0 D_834d0.
    stepiv F_1490b0 D_1490b0 (Z_to_bv 64 tpv) ltac:(wval).
    mldq F_1490b4 D_1490b4 (tpv - 88)%Z C3.
    stepiv F_1490b8 D_1490b8 (Z_to_bv 64 (key * 2 ^ 32)) ltac:(gres; rwH; rewrite v_lw_small by lia; wval).
    stepiv F_1490bc D_1490bc (Z_to_bv 64 (8 * key))
      ltac:(gres; rwH; unfold v_srli; imm_norm; unorm; rewrite Z.shiftr_div_pow2 by lia;
            replace (key * 2 ^ 32)%Z with (8 * key * 2 ^ 29)%Z by lia; rewrite Z.div_mul by lia; reflexivity).
    stepiv F_1490c0 D_1490c0 (Z_to_bv 64 (tsd + 8 * key)) ltac:(wval).
    mldq F_1490c4 D_1490c4 (tsd + 8 * key)%Z C4.
    stepret F_1490c8 D_1490c8 (0x8ae90 : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
    stepb_ft F_8ae48 D_8ae48 ltac:(cond).
    mldq F_8ae4c D_8ae4c (ctx + 152)%Z C5.
    stepld F_8ae50 D_8ae50 ret ltac:(maddr (t - 8)%Z; unfold M1; apply rdn_wbytes_hit8; unorm; lia).
    stepiv F_8ae54 D_8ae54 (Z_to_bv 64 t) ltac:(wval).
    stepret F_8ae58 D_8ae58 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat split; gres; rwH; try reflexivity. solve_keeps_but.
Qed.

Section DTLS.
  Variable M : word -> option byte.
  Variable rom : word -> option byte.
  Variable ret : word.
  Variables t tpv d md F V verb dto blk rec : Z.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Ht : (0x1000000 <= t - 144)%Z /\ (t < 2 ^ 64)%Z.
  Hypothesis Htp : (0 <= tpv < 2 ^ 64)%Z.
  Hypothesis Hd : (0 <= d /\ d + 16 <= 2 ^ 64)%Z.
  Hypothesis Hmd : (0 <= md < 255)%Z.
  Hypothesis HF : (0 <= F /\ F + 256 <= 2 ^ 64)%Z.
  Hypothesis HV : (0 <= V /\ V + 4 <= 2 ^ 64)%Z.
  Hypothesis Hverb : (0 <= verb < 3)%Z.
  Hypothesis Hdto : (0 <= dto /\ 0 <= dto + tpv /\ dto + tpv + 8 <= 2 ^ 64)%Z.
  Hypothesis Hblk : (0 < blk /\ blk + 16 * 255 <= 2 ^ 64 - 1)%Z.
  Hypothesis Hrec : (0 < rec < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS M (Z_to_bv 64 (t - 144)) 144%nat = true.

  Hypothesis HC : forall M', (forall x : word, (bv_unsigned x < t - 144 \/ t <= bv_unsigned x)%Z -> M' x = M x) ->
     rdn ASEGS M' (0x1544f0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 F)) /\
     rdn ASEGS M' (Z_to_bv 64 (F + 137)) 1%nat = Some [Z_to_bv 8 1] /\
     rdn ASEGS M' (0x154550 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 V)) /\
     rdn ASEGS M' (Z_to_bv 64 V) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 verb)) /\
     rdn ASEGS M' (0x155320 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 dto)) /\
     rdn ASEGS M' (Z_to_bv 64 (dto + tpv)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 blk)) /\
     rdn ASEGS M' (Z_to_bv 64 d) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 md)) /\
     rdn ASEGS M' (Z_to_bv 64 (blk + 16 * md + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 rec)).

  Definition M13 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
      (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (t - 16)) (word_to_le_bytes 8 (getr rg 8)))
      (Z_to_bv 64 (t - 24)) (word_to_le_bytes 8 (getr rg 9)))
      (Z_to_bv 64 (t - 32)) (word_to_le_bytes 8 (getr rg 18)))
      (Z_to_bv 64 (t - 40)) (word_to_le_bytes 8 (getr rg 19)))
      (Z_to_bv 64 (t - 48)) (word_to_le_bytes 8 (getr rg 20)))
      (Z_to_bv 64 (t - 56)) (word_to_le_bytes 8 (getr rg 21)))
      (Z_to_bv 64 (t - 64)) (word_to_le_bytes 8 (getr rg 22)))
      (Z_to_bv 64 (t - 72)) (word_to_le_bytes 8 (getr rg 23)))
      (Z_to_bv 64 (t - 80)) (word_to_le_bytes 8 (getr rg 24)))
      (Z_to_bv 64 (t - 88)) (word_to_le_bytes 8 (getr rg 25)))
      (Z_to_bv 64 (t - 96)) (word_to_le_bytes 8 (getr rg 26)))
      (Z_to_bv 64 (t - 104)) (word_to_le_bytes 8 (getr rg 27)).
  Definition MD (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (M13 rg)
      (Z_to_bv 64 (t - 128)) (word_to_le_bytes 8 (getr rg 12)))
      (Z_to_bv 64 (t - 120)) (word_to_le_bytes 8 (getr rg 13)).

  Lemma M13_out : forall rg (x : word), (bv_unsigned x < t - 144 \/ t <= bv_unsigned x)%Z -> M13 rg x = M x.
  Proof.
    intros rg x Hx. unfold M13. pose proof (u64_range x).
    destruct Hx as [Hx|Hx].
    - rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
    - rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
  Qed.
  Lemma MD_out : forall rg (x : word), (bv_unsigned x < t - 144 \/ t <= bv_unsigned x)%Z -> MD rg x = M x.
  Proof.
    intros rg x Hx. unfold MD. pose proof (u64_range x). rewrite <- (M13_out rg x Hx).
    destruct Hx as [Hx|Hx].
    - rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
    - rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
  Qed.

  #[local] Ltac sok := first [apply (store_ok_mono _ _ M); [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl|];
                              apply (store_ok_sub ASEGS M (Z_to_bv 64 (t - 144)) _ 144%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]].
  #[local] Ltac slot := repeat peel; apply rdn_wbytes_hit8; unorm; lia.

  Lemma dtls_fast_run : forall regs (a1v : word),
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = a1v -> getr regs 2 = Z_to_bv 64 t -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 1 = ret ->
    exists regs',
      msteps ASEGS (mkst regs (0x985b4 : word) M rom) (mkst regs' ret (MD regs) rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 t /\ getr regs' 1 = ret
      /\ keeps_but [1; 2]%bv regs regs'.
  Proof.
    intros regs a1v H10 H11 H2 H4 H1.
    destruct (HC (M13 regs) (M13_out regs)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
    destruct (HC (MD regs) (MD_out regs)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    unfold MD, M13 in *.
    eexists. split.
    - stepiv F_9856c D_9856c (Z_to_bv 64 (t - 144)) ltac:(wval).
      stepsd F_98570 D_98570 (Z_to_bv 64 (t - 8)) ret ltac:(sok).
      stepsd F_98574 D_98574 (Z_to_bv 64 (t - 16)) (getr regs 8) ltac:(sok).
      stepsd F_98578 D_98578 (Z_to_bv 64 (t - 24)) (getr regs 9) ltac:(sok).
      stepsd F_9857c D_9857c (Z_to_bv 64 (t - 32)) (getr regs 18) ltac:(sok).
      stepsd F_98580 D_98580 (Z_to_bv 64 (t - 40)) (getr regs 19) ltac:(sok).
      stepsd F_98584 D_98584 (Z_to_bv 64 (t - 48)) (getr regs 20) ltac:(sok).
      stepsd F_98588 D_98588 (Z_to_bv 64 (t - 56)) (getr regs 21) ltac:(sok).
      stepsd F_9858c D_9858c (Z_to_bv 64 (t - 64)) (getr regs 22) ltac:(sok).
      stepsd F_98590 D_98590 (Z_to_bv 64 (t - 72)) (getr regs 23) ltac:(sok).
      stepsd F_98594 D_98594 (Z_to_bv 64 (t - 80)) (getr regs 24) ltac:(sok).
      stepsd F_98598 D_98598 (Z_to_bv 64 (t - 88)) (getr regs 25) ltac:(sok).
      stepsd F_9859c D_9859c (Z_to_bv 64 (t - 96)) (getr regs 26) ltac:(sok).
      stepsd F_985a0 D_985a0 (Z_to_bv 64 (t - 104)) (getr regs 27) ltac:(sok).
      stepn F_985a4 D_985a4.
      stepn F_985a8 D_985a8.
      mld F_985ac D_985ac (0x1544f0 : word) C1.
      mlbuq F_985b0 D_985b0 (F + 137)%Z C2.
      stepb_ft F_985b4 D_985b4 ltac:(cond).
      stepiv F_985b8 D_985b8 (Z_to_bv 64 d) ltac:(wval).
      stepn F_985bc D_985bc.
      mld F_985c0 D_985c0 (0x154550 : word) C3.
      mldq F_985c4 D_985c4 d C7.
      stepn F_985c8 D_985c8.
      mlwq F_985cc D_985cc V C4.
      mld F_985d0 D_985d0 (0x155320 : word) C5.
      stepn F_985d4 D_985d4.
      stepiv F_985d8 D_985d8 (Z_to_bv 64 (dto + tpv)) ltac:(wval).
      stepb_ft F_985dc D_985dc ltac:(cond).
      mldq F_985e0 D_985e0 (dto + tpv)%Z C6.
      stepn F_985e4 D_985e4.
      stepfence F_985e8 D_985e8.
      stepb_ft F_985ec D_985ec ltac:(cond).
      stepb_tk F_985f0 D_985f0 ltac:(cond).
      stepb_ft F_98674 D_98674 ltac:(cond).
      stepsd F_98678 D_98678 (Z_to_bv 64 (t - 128)) (getr regs 12) ltac:(sok).
      stepsd F_9867c D_9867c (Z_to_bv 64 (t - 120)) (getr regs 13) ltac:(sok).
      stepn F_98680 D_98680.
      stepb_tk F_98684 D_98684 ltac:(cond).
      stepiv F_98734 D_98734 (Z_to_bv 64 blk) ltac:(wval).
      stepiv F_98738 D_98738 (Z_to_bv 64 (16 * md)) ltac:(wval).
      stepiv F_9873c D_9873c (Z_to_bv 64 (blk + 16 * md)) ltac:(wval).
      mldq F_98740 D_98740 (blk + 16 * md + 8)%Z E8.
      stepb_ft F_98744 D_98744 ltac:(cond).
      stepn F_98748 D_98748.
      stepld F_9874c D_9874c ret ltac:(maddr (t - 8)%Z; slot).
      stepld F_98750 D_98750 (getr regs 8) ltac:(maddr (t - 16)%Z; slot).
      stepld F_98754 D_98754 (getr regs 9) ltac:(maddr (t - 24)%Z; slot).
      stepld F_98758 D_98758 (getr regs 18) ltac:(maddr (t - 32)%Z; slot).
      stepld F_9875c D_9875c (getr regs 19) ltac:(maddr (t - 40)%Z; slot).
      stepld F_98760 D_98760 (getr regs 20) ltac:(maddr (t - 48)%Z; slot).
      stepld F_98764 D_98764 (getr regs 21) ltac:(maddr (t - 56)%Z; slot).
      stepld F_98768 D_98768 (getr regs 22) ltac:(maddr (t - 64)%Z; slot).
      stepld F_9876c D_9876c (getr regs 23) ltac:(maddr (t - 72)%Z; slot).
      stepld F_98770 D_98770 (getr regs 24) ltac:(maddr (t - 80)%Z; slot).
      stepld F_98774 D_98774 (getr regs 25) ltac:(maddr (t - 88)%Z; slot).
      stepld F_98778 D_98778 (getr regs 26) ltac:(maddr (t - 96)%Z; slot).
      stepld F_9877c D_9877c (getr regs 27) ltac:(maddr (t - 104)%Z; slot).
      stepiv F_98780 D_98780 (Z_to_bv 64 t) ltac:(wval).
      stepret F_98784 D_98784 ret ltac:(rwH; reflexivity).
      apply mst_refl.
    - split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; rwH; reflexivity|].
      match goal with |- keeps_but _ _ ?rg =>
        assert (KD : keeps_but [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv regs rg) by solve_keeps_but end.
      intros r Hr HL.
      destruct (decide (r = 8%bv)) as [->|N8]; [gres; reflexivity|]. destruct (decide (r = 9%bv)) as [->|N9]; [gres; reflexivity|].
      destruct (decide (r = 18%bv)) as [->|N18]; [gres; reflexivity|]. destruct (decide (r = 19%bv)) as [->|N19]; [gres; reflexivity|].
      destruct (decide (r = 20%bv)) as [->|N20]; [gres; reflexivity|]. destruct (decide (r = 21%bv)) as [->|N21]; [gres; reflexivity|].
      destruct (decide (r = 22%bv)) as [->|N22]; [gres; reflexivity|]. destruct (decide (r = 23%bv)) as [->|N23]; [gres; reflexivity|].
      destruct (decide (r = 24%bv)) as [->|N24]; [gres; reflexivity|]. destruct (decide (r = 25%bv)) as [->|N25]; [gres; reflexivity|].
      destruct (decide (r = 26%bv)) as [->|N26]; [gres; reflexivity|]. destruct (decide (r = 27%bv)) as [->|N27]; [gres; reflexivity|].
      apply KD; [exact Hr|]. cbv. cbv in HL. intuition congruence.
  Qed.
End DTLS.

Section ICPT.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables s tpv d md off dtv ent key tsd ctx th tb te F V verb dto blk rec : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hs : (0x1000000 <= s - 176)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 176)) 176%nat = true.
  Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
  Hypothesis Hd : (0 <= d /\ d + 16 <= 2 ^ 64)%Z.
  Hypothesis Hmd : (0 <= md < 255)%Z.
  Hypothesis Hoff : (0 <= off < 2 ^ 64)%Z.
  Hypothesis Hdtv : (0 <= dtv /\ dtv + 8 * md + 8 <= 2 ^ 64)%Z.
  Hypothesis Hent : (0 <= ent < 2 ^ 64)%Z.
  Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
  Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
  Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
  Hypothesis Hth : (0 < th /\ th + 64 <= 2 ^ 64)%Z.
  Hypothesis Htbe : (0 <= tb < 2 ^ 64)%Z /\ (0 <= te < 2 ^ 64)%Z.
  Hypothesis HF : (0 <= F /\ F + 256 <= 2 ^ 64)%Z.
  Hypothesis HV : (0 <= V /\ V + 4 <= 2 ^ 64)%Z.
  Hypothesis Hverb : (0 <= verb < 3)%Z.
  Hypothesis Hdto : (0 <= dto /\ 0 <= dto + tpv /\ dto + tpv + 8 <= 2 ^ 64)%Z.
  Hypothesis Hblk : (0 < blk /\ blk + 16 * 255 <= 2 ^ 64 - 1)%Z.
  Hypothesis Hrec : (0 < rec < 2 ^ 64)%Z.

  Definition tls_cells (M' : word -> option byte) : Prop :=
     rdn ASEGS M' (0x15e9d8 : word) 1%nat = Some [Z_to_bv 8 1] /\
     rdn ASEGS M' (0x156418 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1474a4)) /\
     rdn ASEGS M' (Z_to_bv 64 d) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 md)) /\
     rdn ASEGS M' (Z_to_bv 64 (d + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 off)) /\
     rdn ASEGS M' (Z_to_bv 64 (tpv - 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 dtv)) /\
     rdn ASEGS M' (Z_to_bv 64 (dtv + 8 * md)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ent)) /\
     rdn ASEGS M' (0x15d560 : word) 1%nat = Some [Z_to_bv 8 1] /\
     rdn ASEGS M' (0x15d564 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
     rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
     rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
     rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\
     rdn ASEGS M' (Z_to_bv 64 (th + 48)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tb)) /\
     rdn ASEGS M' (Z_to_bv 64 (th + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 te)) /\
     rdn ASEGS M' (0x1544f0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 F)) /\
     rdn ASEGS M' (Z_to_bv 64 (F + 137)) 1%nat = Some [Z_to_bv 8 1] /\
     rdn ASEGS M' (0x154550 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 V)) /\
     rdn ASEGS M' (Z_to_bv 64 V) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 verb)) /\
     rdn ASEGS M' (0x155320 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 dto)) /\
     rdn ASEGS M' (Z_to_bv 64 (dto + tpv)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 blk)) /\
     rdn ASEGS M' (Z_to_bv 64 (blk + 16 * md + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 rec)).
  Hypothesis HC0 : forall M', (forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) -> tls_cells M'.

  Definition tls_res : Z := ((ent + off) mod 2 ^ 64)%Z.

  Lemma sp_s : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
  #[local] Ltac oout := intros x Hx; pose proof (u64_range x);
     destruct Hx as [Hx|Hx]; [rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | unorm; lia]
                            | rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]].
  Lemma MD_grows' : forall M1 r t1 rg, mem_grows M1 (MD M1 r t1 rg).
  Proof. intros. unfold MD, M13. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  #[local] Ltac sok0 := first [apply (store_ok_mono _ _ mem0); [repeat (eapply mem_grows_trans; [|first [apply wbytes_grows | apply MD_grows']]); apply mem_grows_refl|];
                              apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 176)) _ 176%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]].

  Theorem tls_icpt_run : forall regs,
    getr regs 10 = Z_to_bv 64 d -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x72634 : word) mem0 rom) (mkst regs' ra M' rom)
      /\ getr regs' 10 = Z_to_bv 64 tls_res /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ (forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) /\ mem_grows mem0 M'.
  Proof.
    intros regs H10 H4 H2 H1. rewrite sp_s in H2.

    set (M4 := wbytes (wbytes (wbytes (wbytes mem0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                 (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18))).
    set (M6 := wbytes (wbytes M4 (Z_to_bv 64 (s - 32 - 8)) (word_to_le_bytes 8 (0x72650 : word))) (Z_to_bv 64 (s - 32 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 d))).
    set (M7 := wbytes M6 (Z_to_bv 64 (s - 32 - 8)) (word_to_le_bytes 8 (0x72670 : word))).
    assert (O4 : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M4 x = mem0 x) by (unfold M4; oout).
    assert (O6 : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M6 x = mem0 x).
    { intros x Hx. rewrite <- (O4 x Hx). unfold M6. revert x Hx. oout. }
    assert (O7 : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M7 x = mem0 x).
    { intros x Hx. rewrite <- (O6 x Hx). unfold M7. revert x Hx. oout. }
    destruct (HC0 M4 O4) as (A1 & A2 & _).
    destruct (HC0 M6 O6) as (B1 & B2 & B3 & B4 & B5 & B6 & _).
    assert (Hr1 : ret_ok (0x72650 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (Hr2 : ret_ok (0x72664 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (Hr3 : ret_ok (0x72670 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (Hr4 : ret_ok (0x72694 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).

    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x72634 : word) mem0 rom) (mkst r1 (0x88684 : word) M4 rom)
              /\ (getr r1 8 = Z_to_bv 64 d /\ getr r1 4 = Z_to_bv 64 tpv /\ getr r1 2 = Z_to_bv 64 (s - 32) /\ getr r1 1 = (0x72650 : word)
                  /\ keeps_but [1; 2; 8; 9; 18]%bv regs r1)).
    { unfold M4. eexists. split.
      - stepiv F_725ec D_725ec (Z_to_bv 64 (s - 32)) ltac:(wval).
        stepsd F_725f0 D_725f0 (Z_to_bv 64 (s - 8)) ra ltac:(sok0).
        stepsd F_725f4 D_725f4 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok0).
        stepsd F_725f8 D_725f8 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok0).
        stepsd F_725fc D_725fc (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok0).
        stepiv F_72600 D_72600 (Z_to_bv 64 d) ltac:(wval).
        stepn F_72604 D_72604.
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q8 & Q4 & Q2 & Q1 & K1).
    destruct (tryinit_fast_run r1 M4 rom (0x72650 : word) (s - 32) Q2 Q1 Hr1 ltac:(lia) ltac:(lia)
                ltac:(unfold M4; replace (s - 32 - 16)%Z with (s - 48)%Z by lia; sok0) A1) as (r2 & RUN2 & U10 & U2 & U8 & U1 & K2).
    rewrite Q8 in RUN2. change (wbytes (wbytes M4 (Z_to_bv 64 (s - 32 - 8)) (word_to_le_bytes 8 (0x72650 : word))) (Z_to_bv 64 (s - 32 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 d))) with M6 in RUN2.
    rewrite Q8 in U8.
    assert (U4 : getr r2 4 = Z_to_bv 64 tpv) by (rewrite (K2 4%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact Q4).

    assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x72650 : word) M6 rom) (mkst r3 (0x1474a4 : word) M6 rom)
              /\ (getr r3 10 = Z_to_bv 64 d /\ getr r3 4 = Z_to_bv 64 tpv /\ getr r3 18 = Z_to_bv 64 1 /\ getr r3 8 = Z_to_bv 64 d
                  /\ getr r3 2 = Z_to_bv 64 (s - 32) /\ getr r3 1 = (0x72664 : word) /\ keeps_but [1; 2; 8; 9; 18]%bv r2 r3)).
    { eexists. split.
      - stepn F_72608 D_72608.
        mld F_7260c D_7260c (0x156418 : word) B2.
        stepiv F_72610 D_72610 (Z_to_bv 64 1) ltac:(wval).
        stepiv F_72614 D_72614 (Z_to_bv 64 d) ltac:(wval).
        stepjr F_72618 D_72618 (Z_to_bv 64 0x1474a4) ltac:(gres; reflexivity).
        vnorm. apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S3 as (r3 & RUN3 & V10 & V4 & V18 & V8 & V2 & V1 & K3).
    destruct (musl_tls_get_addr_run r3 M6 rom (0x72664 : word) d tpv md off dtv ent V10 V4 V1 Hr2 Hd ltac:(lia) ltac:(lia) Hoff Hdtv Hent B3 B4 B5 B6)
      as (r4 & RUN4 & W10 & K4).
    assert (W18 : getr r4 18 = Z_to_bv 64 1) by (rewrite (K4 18%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact V18).
    assert (W8 : getr r4 8 = Z_to_bv 64 d) by (rewrite (K4 8%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact V8).
    assert (W2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (rewrite (K4 2%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact V2).
    assert (W4 : getr r4 4 = Z_to_bv 64 tpv) by (rewrite (K4 4%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact V4).
    pose proof (Z.mod_pos_bound (ent + off) (2 ^ 64) ltac:(lia)) as Hres.
    unfold tls_res. remember ((ent + off) mod 2 ^ 64)%Z as tres eqn:Htres.

    assert (S5 : exists r5, msteps ASEGS (mkst r4 (0x72664 : word) M6 rom) (mkst r5 (0x8ae84 : word) M6 rom)
              /\ (getr r5 9 = Z_to_bv 64 tres /\ getr r5 4 = Z_to_bv 64 tpv /\ getr r5 8 = Z_to_bv 64 d
                  /\ getr r5 2 = Z_to_bv 64 (s - 32) /\ getr r5 1 = (0x72670 : word) /\ keeps_but [1; 2; 8; 9; 18]%bv r4 r5)).
    { eexists. split.
      - stepiv F_7261c D_7261c (Z_to_bv 64 tres) ltac:(wval).
        stepb_ft F_72620 D_72620 ltac:(cond).
        stepn F_72624 D_72624.
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S5 as (r5 & RUN5 & X9 & X4 & X8 & X2 & X1 & K5).
    destruct (get_current_thread_run r5 M6 rom (0x72670 : word) (s - 32) tpv key tsd ctx th X2 X4 X1 Hr3 ltac:(lia) ltac:(lia) Htp Hkey Htsd Hctx ltac:(lia)
                ltac:(unfold M6, M4; replace (s - 32 - 16)%Z with (s - 48)%Z by lia; sok0)) as (r6 & RUN6 & Y10 & Y2 & Y1 & K6).
    { intros M' HM'. assert (O' : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x).
      { intros x Hx. rewrite (HM' x) by lia. apply O6. exact Hx. }
      destruct (HC0 M' O') as (_ & _ & _ & _ & _ & _ & C7 & C8 & C9 & C10 & C11 & _). repeat split; assumption. }
    change (wbytes M6 (Z_to_bv 64 (s - 32 - 8)) (word_to_le_bytes 8 (0x72670 : word))) with M7 in RUN6.
    assert (Y9 : getr r6 9 = Z_to_bv 64 tres) by (rewrite (K6 9%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact X9).
    assert (Y8 : getr r6 8 = Z_to_bv 64 d) by (rewrite (K6 8%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact X8).
    assert (Y4 : getr r6 4 = Z_to_bv 64 tpv) by (rewrite (K6 4%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact X4).
    destruct (HC0 M7 O7) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D12 & D13 & _).

    assert (S7 : exists r7, msteps ASEGS (mkst r6 (0x72670 : word) M7 rom) (mkst r7 (0x985b4 : word) M7 rom)
              /\ (getr r7 10 = Z_to_bv 64 d /\ getr r7 11 = Z_to_bv 64 tres /\ getr r7 2 = Z_to_bv 64 (s - 32) /\ getr r7 4 = Z_to_bv 64 tpv
                  /\ getr r7 1 = (0x72694 : word) /\ getr r7 9 = Z_to_bv 64 tres /\ keeps_but [1; 2; 8; 9; 18]%bv r6 r7)).
    { eexists. split.
      - stepb_ft F_72628 D_72628 ltac:(cond).
        mldq F_7262c D_7262c (th + 48)%Z D12.
        mldq F_72630 D_72630 (th + 56)%Z D13.
        stepn F_72634 D_72634.
        stepiv F_72640 D_72640 (Z_to_bv 64 d) ltac:(wval).
        stepiv F_72644 D_72644 (Z_to_bv 64 tres) ltac:(wval).
        stepn F_72648 D_72648.
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S7 as (r7 & RUN7 & Z10 & Z11 & Z2 & Z4 & Z1 & Z9 & K7).
    destruct (dtls_fast_run M7 rom (0x72694 : word) (s - 32) tpv d md F V verb dto blk rec Hr4 ltac:(lia) ltac:(lia) Hd Hmd HF HV Hverb Hdto Hblk Hrec
                ltac:(unfold M7, M6, M4; replace (s - 32 - 144)%Z with (s - 176)%Z by lia; sok0)
                ltac:(intros M' HM'; assert (O' : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x)
                        by (intros x Hx; rewrite (HM' x) by lia; apply O7; exact Hx);
                      destruct (HC0 M' O') as (_ & _ & E3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E14 & E15 & E16 & E17 & E18 & E19 & E20);
                      repeat split; assumption)
                r7 (Z_to_bv 64 tres) Z10 Z11 Z2 Z4 Z1) as (r8 & RUN8 & T10 & T2 & T1 & K8).
    set (M8 := MD M7 (0x72694 : word) (s - 32) r7) in RUN8.
    assert (O8 : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M8 x = mem0 x).
    { intros x Hx. unfold M8. rewrite MD_out by lia. apply O7. exact Hx. }
    assert (T9 : getr r8 9 = Z_to_bv 64 tres) by (rewrite (K8 9%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact Z9).

    assert (SL : forall k v, (k = 8 /\ v = ra \/ k = 16 /\ v = getr regs 8 \/ k = 24 /\ v = getr regs 9 \/ k = 32 /\ v = getr regs 18)%Z ->
                 rdn ASEGS M8 (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v)).
    { intros k v Hk.
      assert (Hk' : (8 <= k <= 32)%Z) by lia.
      rewrite (rdn_ext ASEGS 8 M8 M4); [| unorm; cbn; lia |].
      - unfold M4. destruct Hk as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; repeat peel; apply rdn_wbytes_hit8; unorm; lia.
      - intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. unfold M8. rewrite MD_out by lia.
        unfold M7, M6. pose proof (u64_range x).
        rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]. }
    #[local] Ltac slv := first [left; split; reflexivity | right; left; split; reflexivity | right; right; left; split; reflexivity | right; right; right; split; reflexivity].
    eexists. exists M8. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|].
      eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|].
      stepiv F_7264c D_7264c (Z_to_bv 64 tres) ltac:(wval).
      stepld F_72650 D_72650 ra ltac:(maddr (s - 8)%Z; apply SL; slv).
      stepld F_72654 D_72654 (getr regs 8) ltac:(maddr (s - 16)%Z; apply SL; slv).
      stepld F_72658 D_72658 (getr regs 9) ltac:(maddr (s - 24)%Z; apply SL; slv).
      stepld F_7265c D_7265c (getr regs 18) ltac:(maddr (s - 32)%Z; apply SL; slv).
      stepiv F_72660 D_72660 (Z_to_bv 64 s) ltac:(wval).
      stepret F_72664 D_72664 ra ltac:(rwH; reflexivity).
      apply mst_refl.
    - split; [gres; reflexivity|]. split; [gres; symmetry; apply sp_s|]. split; [gres; reflexivity|].
      split.
      + assert (KB : keeps_but [1; 2; 8; 9; 18]%bv regs r8).
        { eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [intros r Hr HL; apply K2; [exact Hr | cbv in HL |- *; intuition]|].
          eapply keeps_but_trans; [exact K3|]. eapply keeps_but_trans; [intros r Hr HL; apply K4; [exact Hr | cbv in HL |- *; intuition]|].
          eapply keeps_but_trans; [exact K5|]. eapply keeps_but_trans; [intros r Hr HL; apply K6; [exact Hr | cbv in HL |- *; intuition]|].
          eapply keeps_but_trans; [exact K7|]. intros r Hr HL; apply K8; [exact Hr | cbv in HL |- *; intuition]. }
        intros r Hr. destruct (decide (r = 1%bv)) as [->|N1]; [gres; rewrite H1; reflexivity|].
        destruct (decide (r = 2%bv)) as [->|N2]; [gres; rewrite H2; reflexivity|].
        destruct (decide (r = 8%bv)) as [->|N8]; [gres; reflexivity|]. destruct (decide (r = 9%bv)) as [->|N9]; [gres; reflexivity|].
        destruct (decide (r = 18%bv)) as [->|N18]; [gres; reflexivity|].
        repeat (rewrite getr_other; [| intros ->; first [congruence | cbv in Hr; intuition discriminate]]).
        apply KB; [exact Hr|]. cbv. intuition congruence.
      + split; [exact O8|]. unfold M8. eapply mem_grows_trans; [|apply MD_grows'].
        unfold M7, M6, M4. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
  Qed.

  Corollary wrap_tls_get_addr_run : forall regs,
    getr regs 10 = Z_to_bv 64 d -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x6a990 : word) mem0 rom) (mkst regs' ra M' rom)
      /\ getr regs' 10 = Z_to_bv 64 tls_res /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ (forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) /\ mem_grows mem0 M'.
  Proof.
    intros regs H10 H4 H2 H1.
    destruct (tls_icpt_run regs H10 H4 H2 H1) as (r' & M' & RUN & REST).
    exists r', M'. split; [|exact REST].
    eapply msteps_trans; [|exact RUN].
    stepn F_6a948 D_6a948.
    apply mst_refl.
  Qed.
End ICPT.
End FPX_1.
