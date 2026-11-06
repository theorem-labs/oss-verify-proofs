(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib As0MemIsZero As0RegionPoisoned As0AsanMemset As0AsanMemcpy As0StrlenIcpt.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  As0_code_4dc10_4dc14 As0_code_527d0_5284c As0_code_66fe4_67084 As0_code_697e4_69804 As0_code_620e0_620f8 As0_code_cd550_cd56c
  As0_code_cc49c_cc4c0 As0_code_76ef8_77248.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

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
(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma musl_tls_get_addr_run : forall regs (M rom : word -> option byte) (ret : word) (d tpv md off dtv ent : Z),
  getr regs 10 = Z_to_bv 64 d -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 1 = ret -> ret_ok ret ->
  (0 <= d /\ d + 16 <= 2 ^ 64)%Z -> (8 <= tpv < 2 ^ 64)%Z -> (0 <= md < 2 ^ 16)%Z -> (0 <= off < 2 ^ 64)%Z -> (0 <= dtv /\ dtv + 8 * md + 8 <= 2 ^ 64)%Z -> (0 <= ent < 2 ^ 64)%Z ->
  rdn ASEGS M (Z_to_bv 64 d) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 md)) ->
  rdn ASEGS M (Z_to_bv 64 (d + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 off)) ->
  rdn ASEGS M (Z_to_bv 64 (tpv - 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 dtv)) ->
  rdn ASEGS M (Z_to_bv 64 (dtv + 8 * md)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ent)) ->
  exists regs',
    msteps ASEGS (mkst regs (0xcc49c : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 ((ent + off) mod 2 ^ 64) /\ keeps_but [1]%bv regs regs'.
Proof.
  intros regs M rom ret d tpv md off dtv ent H10 H4 H1 Hret Hd Htp Hmd Hoff Hdtv Hent R1 R2 R3 R4.
  pose proof (Z.mod_pos_bound (ent + off) (2 ^ 64) ltac:(lia)) as Hm.
  eexists. split.
  - stepiv F_cc49c D_cc49c (Z_to_bv 64 tpv) ltac:(wval).                         (* [comment removed for export] *)
    mldq F_cc4a0 D_cc4a0 d R1.                                                     (* [comment removed for export] *)
    mldq F_cc4a4 D_cc4a4 (tpv - 8)%Z R3.                                           (* [comment removed for export] *)
    mldq F_cc4a8 D_cc4a8 (d + 8)%Z R2.                                             (* [comment removed for export] *)
    stepiv F_cc4ac D_cc4ac (Z_to_bv 64 (8 * md)) ltac:(wval).                      (* [comment removed for export] *)
    stepiv F_cc4b0 D_cc4b0 (Z_to_bv 64 (dtv + 8 * md)) ltac:(wval).               (* [comment removed for export] *)
    mldq F_cc4b4 D_cc4b4 (dtv + 8 * md)%Z R4.                                      (* [comment removed for export] *)
    stepiv F_cc4b8 D_cc4b8 (Z_to_bv 64 ((ent + off) mod 2 ^ 64)) ltac:(gres; rwH; unfold v_add; unorm; rewrite zbv_mod; f_equal; lia).  (* [comment removed for export] *)
    stepret F_cc4bc D_cc4bc ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; reflexivity | solve_keeps_but].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_current_thread_run : forall regs (M rom : word -> option byte) (ret : word) (t tpv key tsd ctx th : Z),
  getr regs 2 = Z_to_bv 64 t -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 1 = ret -> ret_ok ret ->
  (0x1000000 <= t - 16)%Z -> (t < 2 ^ 64)%Z -> (96 <= tpv < 2 ^ 64)%Z -> (0 <= key < 2 ^ 28)%Z ->
  (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z -> (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z -> (0 <= th < 2 ^ 64)%Z ->
  store_ok ASEGS M (Z_to_bv 64 (t - 16)) 16%nat = true ->
  (* [comment removed for export] *)
  (forall M', (forall x : word, (bv_unsigned x < t - 16 \/ t <= bv_unsigned x)%Z -> M' x = M x) ->
     rdn ASEGS M' (0xdd3a0 : word) 1%nat = Some [Z_to_bv 8 1] /\
     rdn ASEGS M' (0xdd3a4 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
     rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
     rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
     rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th))) ->
  exists regs',
    msteps ASEGS (mkst regs (0x697e4 : word) M rom) (mkst regs' ret (wbytes M (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ret)) rom)
    /\ getr regs' 10 = Z_to_bv 64 th /\ getr regs' 2 = Z_to_bv 64 t /\ getr regs' 1 = ret /\ keeps_but [1; 2]%bv regs regs'.
Proof.
  intros regs M rom ret t tpv key tsd ctx th H2 H4 H1 Hret Ht1 Ht2 Htp Hkey Htsd Hctx Hth Hok HC.
  set (M1 := wbytes M (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ret)).
  destruct (HC M1) as (C1 & C2 & C3 & C4 & C5).
  { intros x Hx. unfold M1. pose proof (u64_range x).
    destruct Hx as [Hx|Hx]; [rewrite wbytes_below; [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia]
                           | rewrite wbytes_above; [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia]]. }
  assert (Hra : ret_ok (0x697f0 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
  eexists. split.
  - stepiv F_697e4 D_697e4 (Z_to_bv 64 (t - 16)) ltac:(wval).                                                    (* [comment removed for export] *)
    stepsd F_697e8 D_697e8 (Z_to_bv 64 (t - 8)) ret
      ltac:(apply (store_ok_sub ASEGS M (Z_to_bv 64 (t - 16)) _ 16%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).  (* [comment removed for export] *)
    change (wbytes M (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ret)) with M1.
    stepn F_697ec D_697ec.                                                                                         (* [comment removed for export] *)
    stepn F_620e0 D_620e0.                                                                                         (* [comment removed for export] *)
    stepn F_620e4 D_620e4.                                                                                         (* [comment removed for export] *)
    mlbu F_620e8 D_620e8 (0xdd3a0 : word) C1.                                                                      (* [comment removed for export] *)
    stepb_ft F_620ec D_620ec ltac:(cond).                                                                          (* [comment removed for export] *)
    mlw F_620f0 D_620f0 (0xdd3a4 : word) C2.                                                                       (* [comment removed for export] *)
    stepn F_620f4 D_620f4.                                                                                         (* [comment removed for export] *)
    stepiv F_cd550 D_cd550 (Z_to_bv 64 tpv) ltac:(wval).                                                          (* [comment removed for export] *)
    mldq F_cd554 D_cd554 (tpv - 88)%Z C3.                                                                          (* [comment removed for export] *)
    stepiv F_cd558 D_cd558 (Z_to_bv 64 (key * 2 ^ 32)) ltac:(gres; rwH; rewrite v_lw_small by lia; wval).                   (* [comment removed for export] *)
    stepiv F_cd55c D_cd55c (Z_to_bv 64 (8 * key))
      ltac:(gres; rwH; unfold v_srli; imm_norm; unorm; rewrite Z.shiftr_div_pow2 by lia;
            replace (key * 2 ^ 32)%Z with (8 * key * 2 ^ 29)%Z by lia; rewrite Z.div_mul by lia; reflexivity).              (* [comment removed for export] *)
    stepiv F_cd560 D_cd560 (Z_to_bv 64 (tsd + 8 * key)) ltac:(wval).                                               (* [comment removed for export] *)
    mldq F_cd564 D_cd564 (tsd + 8 * key)%Z C4.                                                                     (* [comment removed for export] *)
    stepret F_cd568 D_cd568 (0x697f0 : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).                                              (* [comment removed for export] *)
    stepb_ft F_697f0 D_697f0 ltac:(cond).                                                                          (* [comment removed for export] *)
    mldq F_697f4 D_697f4 (ctx + 152)%Z C5.                                                                         (* [comment removed for export] *)
    stepld F_697f8 D_697f8 ret ltac:(maddr (t - 8)%Z; unfold M1; apply rdn_wbytes_hit8; unorm; lia).              (* [comment removed for export] *)
    stepiv F_697fc D_697fc (Z_to_bv 64 t) ltac:(wval).                                                            (* [comment removed for export] *)
    stepret F_69800 D_69800 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat split; gres; rwH; try reflexivity. solve_keeps_but.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
  Hypothesis Hblk : (0 < blk /\ blk + 16 * 255 <= 2 ^ 64 - 1)%Z.      (* [comment removed for export] *)
  Hypothesis Hrec : (0 < rec < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS M (Z_to_bv 64 (t - 144)) 144%nat = true.
  (* [comment removed for export] *)
  Hypothesis HC : forall M', (forall x : word, (bv_unsigned x < t - 144 \/ t <= bv_unsigned x)%Z -> M' x = M x) ->
     rdn ASEGS M' (0xd58a8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 F)) /\
     rdn ASEGS M' (Z_to_bv 64 (F + 137)) 1%nat = Some [Z_to_bv 8 1] /\
     rdn ASEGS M' (0xd5908 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 V)) /\
     rdn ASEGS M' (Z_to_bv 64 V) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 verb)) /\
     rdn ASEGS M' (0xd6680 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 dto)) /\
     rdn ASEGS M' (Z_to_bv 64 (dto + tpv)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 blk)) /\
     rdn ASEGS M' (Z_to_bv 64 d) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 md)) /\
     rdn ASEGS M' (Z_to_bv 64 (blk + 16 * md + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 rec)).

  (* [comment removed for export] *)
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
      msteps ASEGS (mkst regs (0x76ef8 : word) M rom) (mkst regs' ret (MD regs) rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 t /\ getr regs' 1 = ret
      /\ keeps_but [1; 2]%bv regs regs'.
  Proof.
    intros regs a1v H10 H11 H2 H4 H1.
    destruct (HC (M13 regs) (M13_out regs)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
    destruct (HC (MD regs) (MD_out regs)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    unfold MD, M13 in *.
    eexists. split.
    - stepiv F_76ef8 D_76ef8 (Z_to_bv 64 (t - 144)) ltac:(wval).                                  (* [comment removed for export] *)
      stepsd F_76efc D_76efc (Z_to_bv 64 (t - 8)) ret ltac:(sok).                                   (* [comment removed for export] *)
      stepsd F_76f00 D_76f00 (Z_to_bv 64 (t - 16)) (getr regs 8) ltac:(sok).
      stepsd F_76f04 D_76f04 (Z_to_bv 64 (t - 24)) (getr regs 9) ltac:(sok).
      stepsd F_76f08 D_76f08 (Z_to_bv 64 (t - 32)) (getr regs 18) ltac:(sok).
      stepsd F_76f0c D_76f0c (Z_to_bv 64 (t - 40)) (getr regs 19) ltac:(sok).
      stepsd F_76f10 D_76f10 (Z_to_bv 64 (t - 48)) (getr regs 20) ltac:(sok).
      stepsd F_76f14 D_76f14 (Z_to_bv 64 (t - 56)) (getr regs 21) ltac:(sok).
      stepsd F_76f18 D_76f18 (Z_to_bv 64 (t - 64)) (getr regs 22) ltac:(sok).
      stepsd F_76f1c D_76f1c (Z_to_bv 64 (t - 72)) (getr regs 23) ltac:(sok).
      stepsd F_76f20 D_76f20 (Z_to_bv 64 (t - 80)) (getr regs 24) ltac:(sok).
      stepsd F_76f24 D_76f24 (Z_to_bv 64 (t - 88)) (getr regs 25) ltac:(sok).
      stepsd F_76f28 D_76f28 (Z_to_bv 64 (t - 96)) (getr regs 26) ltac:(sok).
      stepsd F_76f2c D_76f2c (Z_to_bv 64 (t - 104)) (getr regs 27) ltac:(sok).                      (* [comment removed for export] *)
      stepn F_76f30 D_76f30.                                                                         (* [comment removed for export] *)
      stepn F_76f34 D_76f34.                                                                         (* [comment removed for export] *)
      mld F_76f38 D_76f38 (0xd58a8 : word) C1.                              (* [comment removed for export] *)
      mlbuq F_76f3c D_76f3c (F + 137)%Z C2.                                 (* [comment removed for export] *)
      stepb_ft F_76f40 D_76f40 ltac:(cond).                                                          (* [comment removed for export] *)
      stepiv F_76f44 D_76f44 (Z_to_bv 64 d) ltac:(wval).                                            (* [comment removed for export] *)
      stepn F_76f48 D_76f48.                                                                         (* [comment removed for export] *)
      mld F_76f4c D_76f4c (0xd5908 : word) C3.                              (* [comment removed for export] *)
      mldq F_76f50 D_76f50 d C7.                                            (* [comment removed for export] *)
      stepn F_76f54 D_76f54.                                                                         (* [comment removed for export] *)
      mlwq F_76f58 D_76f58 V C4.                                            (* [comment removed for export] *)
      mld F_76f5c D_76f5c (0xd6680 : word) C5.                              (* [comment removed for export] *)
      stepn F_76f60 D_76f60.                                                                         (* [comment removed for export] *)
      stepiv F_76f64 D_76f64 (Z_to_bv 64 (dto + tpv)) ltac:(wval).                                  (* [comment removed for export] *)
      stepb_ft F_76f68 D_76f68 ltac:(cond).                                                          (* [comment removed for export] *)
      mldq F_76f6c D_76f6c (dto + tpv)%Z C6.                                (* [comment removed for export] *)
      stepn F_76f70 D_76f70.                                                                         (* [comment removed for export] *)
      stepfence F_76f74 D_76f74.                                                                     (* [comment removed for export] *)
      stepb_ft F_76f78 D_76f78 ltac:(cond).                                                          (* [comment removed for export] *)
      stepb_tk F_76f7c D_76f7c ltac:(cond).                                                          (* [comment removed for export] *)
      stepb_ft F_77000 D_77000 ltac:(cond).                                                          (* [comment removed for export] *)
      stepsd F_77004 D_77004 (Z_to_bv 64 (t - 128)) (getr regs 12) ltac:(sok).                      (* [comment removed for export] *)
      stepsd F_77008 D_77008 (Z_to_bv 64 (t - 120)) (getr regs 13) ltac:(sok).                      (* [comment removed for export] *)
      stepn F_7700c D_7700c.                                                                         (* [comment removed for export] *)
      stepb_tk F_77010 D_77010 ltac:(cond).                                                          (* [comment removed for export] *)
      stepiv F_770c0 D_770c0 (Z_to_bv 64 blk) ltac:(wval).                                          (* [comment removed for export] *)
      stepiv F_770c4 D_770c4 (Z_to_bv 64 (16 * md)) ltac:(wval).                                    (* [comment removed for export] *)
      stepiv F_770c8 D_770c8 (Z_to_bv 64 (blk + 16 * md)) ltac:(wval).                              (* [comment removed for export] *)
      mldq F_770cc D_770cc (blk + 16 * md + 8)%Z E8.                        (* [comment removed for export] *)
      stepb_ft F_770d0 D_770d0 ltac:(cond).                                                          (* [comment removed for export] *)
      stepn F_770d4 D_770d4.                                                                         (* [comment removed for export] *)
      stepld F_770d8 D_770d8 ret ltac:(maddr (t - 8)%Z; slot).                                      (* [comment removed for export] *)
      stepld F_770dc D_770dc (getr regs 8) ltac:(maddr (t - 16)%Z; slot).
      stepld F_770e0 D_770e0 (getr regs 9) ltac:(maddr (t - 24)%Z; slot).
      stepld F_770e4 D_770e4 (getr regs 18) ltac:(maddr (t - 32)%Z; slot).
      stepld F_770e8 D_770e8 (getr regs 19) ltac:(maddr (t - 40)%Z; slot).
      stepld F_770ec D_770ec (getr regs 20) ltac:(maddr (t - 48)%Z; slot).
      stepld F_770f0 D_770f0 (getr regs 21) ltac:(maddr (t - 56)%Z; slot).
      stepld F_770f4 D_770f4 (getr regs 22) ltac:(maddr (t - 64)%Z; slot).
      stepld F_770f8 D_770f8 (getr regs 23) ltac:(maddr (t - 72)%Z; slot).
      stepld F_770fc D_770fc (getr regs 24) ltac:(maddr (t - 80)%Z; slot).
      stepld F_77100 D_77100 (getr regs 25) ltac:(maddr (t - 88)%Z; slot).
      stepld F_77104 D_77104 (getr regs 26) ltac:(maddr (t - 96)%Z; slot).
      stepld F_77108 D_77108 (getr regs 27) ltac:(maddr (t - 104)%Z; slot).                         (* [comment removed for export] *)
      stepiv F_7710c D_7710c (Z_to_bv 64 t) ltac:(wval).                                            (* [comment removed for export] *)
      stepret F_77110 D_77110 ret ltac:(rwH; reflexivity).
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
  (* [comment removed for export] *)
  Definition tls_cells (M' : word -> option byte) : Prop :=
     rdn ASEGS M' (0xde818 : word) 1%nat = Some [Z_to_bv 8 1] /\                                        (* [comment removed for export] *)
     rdn ASEGS M' (0xd7738 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xcc49c)) /\            (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 d) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 md)) /\                  (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (d + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 off)) /\           (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (tpv - 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 dtv)) /\         (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (dtv + 8 * md)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ent)) /\    (* [comment removed for export] *)
     rdn ASEGS M' (0xdd3a0 : word) 1%nat = Some [Z_to_bv 8 1] /\                                        (* [comment removed for export] *)
     rdn ASEGS M' (0xdd3a4 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\              (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\        (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\   (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\       (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (th + 48)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tb)) /\         (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (th + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 te)) /\         (* [comment removed for export] *)
     rdn ASEGS M' (0xd58a8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 F)) /\                (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (F + 137)) 1%nat = Some [Z_to_bv 8 1] /\                                  (* [comment removed for export] *)
     rdn ASEGS M' (0xd5908 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 V)) /\                (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 V) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 verb)) /\
     rdn ASEGS M' (0xd6680 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 dto)) /\              (* [comment removed for export] *)
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
      msteps ASEGS (mkst regs (0x527d0 : word) mem0 rom) (mkst regs' ra M' rom)
      /\ getr regs' 10 = Z_to_bv 64 tls_res /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ (forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) /\ mem_grows mem0 M'.
  Proof.
    intros regs H10 H4 H2 H1. rewrite sp_s in H2.
    (* [comment removed for export] *)
    set (M4 := wbytes (wbytes (wbytes (wbytes mem0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                 (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18))).
    set (M6 := wbytes (wbytes M4 (Z_to_bv 64 (s - 32 - 8)) (word_to_le_bytes 8 (0x527ec : word))) (Z_to_bv 64 (s - 32 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 d))).
    set (M7 := wbytes M6 (Z_to_bv 64 (s - 32 - 8)) (word_to_le_bytes 8 (0x5280c : word))).
    assert (O4 : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M4 x = mem0 x) by (unfold M4; oout).
    assert (O6 : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M6 x = mem0 x).
    { intros x Hx. rewrite <- (O4 x Hx). unfold M6. revert x Hx. oout. }
    assert (O7 : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M7 x = mem0 x).
    { intros x Hx. rewrite <- (O6 x Hx). unfold M7. revert x Hx. oout. }
    destruct (HC0 M4 O4) as (A1 & A2 & _).
    destruct (HC0 M6 O6) as (B1 & B2 & B3 & B4 & B5 & B6 & _).
    assert (Hr1 : ret_ok (0x527ec : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (Hr2 : ret_ok (0x52800 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (Hr3 : ret_ok (0x5280c : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (Hr4 : ret_ok (0x52830 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    (* [comment removed for export] *)
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x527d0 : word) mem0 rom) (mkst r1 (0x66fe4 : word) M4 rom)
              /\ (getr r1 8 = Z_to_bv 64 d /\ getr r1 4 = Z_to_bv 64 tpv /\ getr r1 2 = Z_to_bv 64 (s - 32) /\ getr r1 1 = (0x527ec : word)
                  /\ keeps_but [1; 2; 8; 9; 18]%bv regs r1)).
    { unfold M4. eexists. split.
      - stepiv F_527d0 D_527d0 (Z_to_bv 64 (s - 32)) ltac:(wval).                                   (* [comment removed for export] *)
        stepsd F_527d4 D_527d4 (Z_to_bv 64 (s - 8)) ra ltac:(sok0).                                    (* [comment removed for export] *)
        stepsd F_527d8 D_527d8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok0).                         (* [comment removed for export] *)
        stepsd F_527dc D_527dc (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok0).                         (* [comment removed for export] *)
        stepsd F_527e0 D_527e0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok0).                        (* [comment removed for export] *)
        stepiv F_527e4 D_527e4 (Z_to_bv 64 d) ltac:(wval).                                             (* [comment removed for export] *)
        stepn F_527e8 D_527e8.                                                                          (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q8 & Q4 & Q2 & Q1 & K1).
    destruct (tryinit_fast_run r1 M4 rom (0x527ec : word) (s - 32) Q2 Q1 Hr1 ltac:(lia) ltac:(lia)
                ltac:(unfold M4; replace (s - 32 - 16)%Z with (s - 48)%Z by lia; sok0) A1) as (r2 & RUN2 & U10 & U2 & U8 & U1 & K2).
    rewrite Q8 in RUN2. change (wbytes (wbytes M4 (Z_to_bv 64 (s - 32 - 8)) (word_to_le_bytes 8 (0x527ec : word))) (Z_to_bv 64 (s - 32 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 d))) with M6 in RUN2.
    rewrite Q8 in U8.
    assert (U4 : getr r2 4 = Z_to_bv 64 tpv) by (rewrite (K2 4%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact Q4).
    (* [comment removed for export] *)
    assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x527ec : word) M6 rom) (mkst r3 (0xcc49c : word) M6 rom)
              /\ (getr r3 10 = Z_to_bv 64 d /\ getr r3 4 = Z_to_bv 64 tpv /\ getr r3 18 = Z_to_bv 64 1 /\ getr r3 8 = Z_to_bv 64 d
                  /\ getr r3 2 = Z_to_bv 64 (s - 32) /\ getr r3 1 = (0x52800 : word) /\ keeps_but [1; 2; 8; 9; 18]%bv r2 r3)).
    { eexists. split.
      - stepn F_527ec D_527ec.                                                                          (* [comment removed for export] *)
        mld F_527f0 D_527f0 (0xd7738 : word) B2.                                                        (* [comment removed for export] *)
        stepiv F_527f4 D_527f4 (Z_to_bv 64 1) ltac:(wval).                                             (* [comment removed for export] *)
        stepiv F_527f8 D_527f8 (Z_to_bv 64 d) ltac:(wval).                                             (* [comment removed for export] *)
        stepjr F_527fc D_527fc (Z_to_bv 64 0xcc49c) ltac:(gres; reflexivity).                           (* [comment removed for export] *)
        vnorm. apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S3 as (r3 & RUN3 & V10 & V4 & V18 & V8 & V2 & V1 & K3).
    destruct (musl_tls_get_addr_run r3 M6 rom (0x52800 : word) d tpv md off dtv ent V10 V4 V1 Hr2 Hd ltac:(lia) ltac:(lia) Hoff Hdtv Hent B3 B4 B5 B6)
      as (r4 & RUN4 & W10 & K4).
    assert (W18 : getr r4 18 = Z_to_bv 64 1) by (rewrite (K4 18%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact V18).
    assert (W8 : getr r4 8 = Z_to_bv 64 d) by (rewrite (K4 8%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact V8).
    assert (W2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (rewrite (K4 2%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact V2).
    assert (W4 : getr r4 4 = Z_to_bv 64 tpv) by (rewrite (K4 4%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact V4).
    pose proof (Z.mod_pos_bound (ent + off) (2 ^ 64) ltac:(lia)) as Hres.
    unfold tls_res. remember ((ent + off) mod 2 ^ 64)%Z as tres eqn:Htres.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (S5 : exists r5, msteps ASEGS (mkst r4 (0x52800 : word) M6 rom) (mkst r5 (0x697e4 : word) M6 rom)
              /\ (getr r5 9 = Z_to_bv 64 tres /\ getr r5 4 = Z_to_bv 64 tpv /\ getr r5 8 = Z_to_bv 64 d
                  /\ getr r5 2 = Z_to_bv 64 (s - 32) /\ getr r5 1 = (0x5280c : word) /\ keeps_but [1; 2; 8; 9; 18]%bv r4 r5)).
    { eexists. split.
      - stepiv F_52800 D_52800 (Z_to_bv 64 tres) ltac:(wval).                                       (* [comment removed for export] *)
        stepb_ft F_52804 D_52804 ltac:(cond).                                                           (* [comment removed for export] *)
        stepn F_52808 D_52808.                                                                          (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S5 as (r5 & RUN5 & X9 & X4 & X8 & X2 & X1 & K5).
    destruct (get_current_thread_run r5 M6 rom (0x5280c : word) (s - 32) tpv key tsd ctx th X2 X4 X1 Hr3 ltac:(lia) ltac:(lia) Htp Hkey Htsd Hctx ltac:(lia)
                ltac:(unfold M6, M4; replace (s - 32 - 16)%Z with (s - 48)%Z by lia; sok0)) as (r6 & RUN6 & Y10 & Y2 & Y1 & K6).
    { intros M' HM'. assert (O' : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x).
      { intros x Hx. rewrite (HM' x) by lia. apply O6. exact Hx. }
      destruct (HC0 M' O') as (_ & _ & _ & _ & _ & _ & C7 & C8 & C9 & C10 & C11 & _). repeat split; assumption. }
    change (wbytes M6 (Z_to_bv 64 (s - 32 - 8)) (word_to_le_bytes 8 (0x5280c : word))) with M7 in RUN6.
    assert (Y9 : getr r6 9 = Z_to_bv 64 tres) by (rewrite (K6 9%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact X9).
    assert (Y8 : getr r6 8 = Z_to_bv 64 d) by (rewrite (K6 8%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact X8).
    assert (Y4 : getr r6 4 = Z_to_bv 64 tpv) by (rewrite (K6 4%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact X4).
    destruct (HC0 M7 O7) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D12 & D13 & _).
    (* [comment removed for export] *)
    assert (S7 : exists r7, msteps ASEGS (mkst r6 (0x5280c : word) M7 rom) (mkst r7 (0x76ef8 : word) M7 rom)
              /\ (getr r7 10 = Z_to_bv 64 d /\ getr r7 11 = Z_to_bv 64 tres /\ getr r7 2 = Z_to_bv 64 (s - 32) /\ getr r7 4 = Z_to_bv 64 tpv
                  /\ getr r7 1 = (0x52830 : word) /\ getr r7 9 = Z_to_bv 64 tres /\ keeps_but [1; 2; 8; 9; 18]%bv r6 r7)).
    { eexists. split.
      - stepb_ft F_5280c D_5280c ltac:(cond).                                                           (* [comment removed for export] *)
        mldq F_52810 D_52810 (th + 48)%Z D12.                                                             (* [comment removed for export] *)
        mldq F_52814 D_52814 (th + 56)%Z D13.                                                             (* [comment removed for export] *)
        stepn F_52818 D_52818.                                                                          (* [comment removed for export] *)
        stepiv F_52824 D_52824 (Z_to_bv 64 d) ltac:(wval).                                             (* [comment removed for export] *)
        stepiv F_52828 D_52828 (Z_to_bv 64 tres) ltac:(wval).                                       (* [comment removed for export] *)
        stepn F_5282c D_5282c.                                                                          (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S7 as (r7 & RUN7 & Z10 & Z11 & Z2 & Z4 & Z1 & Z9 & K7).
    destruct (dtls_fast_run M7 rom (0x52830 : word) (s - 32) tpv d md F V verb dto blk rec Hr4 ltac:(lia) ltac:(lia) Hd Hmd HF HV Hverb Hdto Hblk Hrec
                ltac:(unfold M7, M6, M4; replace (s - 32 - 144)%Z with (s - 176)%Z by lia; sok0)
                ltac:(intros M' HM'; assert (O' : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x)
                        by (intros x Hx; rewrite (HM' x) by lia; apply O7; exact Hx);
                      destruct (HC0 M' O') as (_ & _ & E3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E14 & E15 & E16 & E17 & E18 & E19 & E20);
                      repeat split; assumption)
                r7 (Z_to_bv 64 tres) Z10 Z11 Z2 Z4 Z1) as (r8 & RUN8 & T10 & T2 & T1 & K8).
    set (M8 := MD M7 (0x52830 : word) (s - 32) r7) in RUN8.
    assert (O8 : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M8 x = mem0 x).
    { intros x Hx. unfold M8. rewrite MD_out by lia. apply O7. exact Hx. }
    assert (T9 : getr r8 9 = Z_to_bv 64 tres) by (rewrite (K8 9%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact Z9).
    (* [comment removed for export] *)
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
      stepiv F_52830 D_52830 (Z_to_bv 64 tres) ltac:(wval).                                         (* [comment removed for export] *)
      stepld F_52834 D_52834 ra ltac:(maddr (s - 8)%Z; apply SL; slv).                                  (* [comment removed for export] *)
      stepld F_52838 D_52838 (getr regs 8) ltac:(maddr (s - 16)%Z; apply SL; slv).                       (* [comment removed for export] *)
      stepld F_5283c D_5283c (getr regs 9) ltac:(maddr (s - 24)%Z; apply SL; slv).                       (* [comment removed for export] *)
      stepld F_52840 D_52840 (getr regs 18) ltac:(maddr (s - 32)%Z; apply SL; slv).                      (* [comment removed for export] *)
      stepiv F_52844 D_52844 (Z_to_bv 64 s) ltac:(wval).                                               (* [comment removed for export] *)
      stepret F_52848 D_52848 ra ltac:(rwH; reflexivity).
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

  (* [comment removed for export] *)
  Corollary wrap_tls_get_addr_run : forall regs,
    getr regs 10 = Z_to_bv 64 d -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x4dc10 : word) mem0 rom) (mkst regs' ra M' rom)
      /\ getr regs' 10 = Z_to_bv 64 tls_res /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ (forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) /\ mem_grows mem0 M'.
  Proof.
    intros regs H10 H4 H2 H1.
    destruct (tls_icpt_run regs H10 H4 H2 H1) as (r' & M' & RUN & REST).
    exists r', M'. split; [|exact REST].
    eapply msteps_trans; [|exact RUN].
    stepn F_4dc10 D_4dc10.                                                                              (* [comment removed for export] *)
    apply mst_refl.
  Qed.
End ICPT.
End FPX_1.
