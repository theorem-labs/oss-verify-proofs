(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib Pm8MemIsZero Pm8RegionPoisoned Pm8AsanMemset Pm8AsanMemcpy Pm8Readers Pm8StrlenIcpt.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_6a000_6b000 Pm8_code_6c000_6d000 Pm8_code_134000_135000 Pm8_code_145000_146000 Pm8_code_14b000_14ba24          .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

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
#[local] Ltac xval := gres; rwH; unfold v_xori; imm_norm; unorm; rewrite lxor_ones64 by lia; first [reflexivity | f_equal; lia].
#[local] Ltac vlit := gres; rwH; apply bv_eq; vm_compute; reflexivity.
#[local] Ltac peel0 :=
  rewrite rdn_wbytes_out;
    [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia
      | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia ].

#[local] Definition RIPL : list reg := [1; 2; 8; 9; 18; 19; 20]%bv.

Section RDPRE.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables s fd p cnt : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hs : (0x1000000 <= s - 2200)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 2200)) 2200%nat = true.
  Hypothesis Hfd : (0 <= fd < 2 ^ 64)%Z.
  Hypothesis Hp : (0 <= p < 2 ^ 64)%Z.
  Hypothesis Hcnt : (0 <= cnt < 2 ^ 64)%Z.
  Hypothesis HI : rdn ASEGS mem0 (0x15d698 : word) 1%nat = Some [Z_to_bv 8 1].
  Hypothesis HR : rdn ASEGS mem0 (0x154fa8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x14b908)).

  Lemma sp_sA : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Definition RDA (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr rg 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr rg 20)))
      (Z_to_bv 64 (s - 2136)) (word_to_le_bytes 8 (0x6c780 : word)))
      (Z_to_bv 64 (s - 2144)) (word_to_le_bytes 8 (Z_to_bv 64 s)))
      (Z_to_bv 64 (s - 2136)) (word_to_le_bytes 8 (0x6c79c : word)).

  Lemma RDA_out : forall rg (x : word), (bv_unsigned x < s - 2144 \/ s <= bv_unsigned x)%Z -> RDA rg x = mem0 x.
  Proof.
    intros rg x Hx. unfold RDA. pose proof (u64_range x).
    destruct Hx as [Hx|Hx]; [rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | unorm; lia]
                           | rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]].
  Qed.
  Lemma RDA_grows : forall rg, mem_grows mem0 (RDA rg).
  Proof. intros rg. unfold RDA. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  #[local] Ltac slot := repeat peel0; apply rdn_wbytes_hit8; unorm; lia.
  Lemma RDA_slots : forall rg,
    rdn ASEGS (RDA rg) (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra) /\
    rdn ASEGS (RDA rg) (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 (getr rg 8)) /\
    rdn ASEGS (RDA rg) (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 (getr rg 9)) /\
    rdn ASEGS (RDA rg) (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 (getr rg 18)) /\
    rdn ASEGS (RDA rg) (Z_to_bv 64 (s - 40)) 8%nat = Some (word_to_le_bytes 8 (getr rg 19)) /\
    rdn ASEGS (RDA rg) (Z_to_bv 64 (s - 48)) 8%nat = Some (word_to_le_bytes 8 (getr rg 20)) /\
    rdn ASEGS (RDA rg) (Z_to_bv 64 (s - 2136)) 8%nat = Some (word_to_le_bytes 8 (0x6c79c : word)).
  Proof. intros rg. destruct Hs as [S1' S2']. unfold RDA. repeat split; slot. Qed.

  #[local] Ltac sok := apply (store_ok_mono _ _ mem0); [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); first [apply mem_grows_refl | assumption] |];
                      apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 2200)) _ 2200%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia].

  Theorem read_icpt_pre_run : forall regs,
    getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = Z_to_bv 64 p -> getr regs 12 = Z_to_bv 64 cnt -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x6c74c : word) mem0 rom) (mkst regs' (0x145edc : word) (RDA regs) rom)
      /\ getr regs' 17 = Z_to_bv 64 63 /\ getr regs' 10 = Z_to_bv 64 fd /\ getr regs' 11 = Z_to_bv 64 p /\ getr regs' 12 = Z_to_bv 64 cnt
      /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 0
      /\ getr regs' 2 = Z_to_bv 64 (s - 2144) /\ getr regs' 1 = (0x14b930 : word)
      /\ getr regs' 8 = Z_to_bv 64 s /\ getr regs' 9 = Z_to_bv 64 p /\ getr regs' 18 = Z_to_bv 64 cnt /\ getr regs' 19 = Z_to_bv 64 fd /\ getr regs' 20 = Z_to_bv 64 1
      /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs H10 H11 H12 H2 H1. rewrite sp_sA in H2. destruct Hs as [S1' S2'].
    assert (Hra : ret_ok (0x6c780 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    set (M6 := wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18))) (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19))) (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20))).
    assert (HI6 : rdn ASEGS M6 (0x15d698 : word) 1%nat = Some [Z_to_bv 8 1]) by (unfold M6; repeat peel0; exact HI).

    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x6c74c : word) mem0 rom) (mkst r1 (0x882c4 : word) M6 rom)
              /\ (getr r1 18 = Z_to_bv 64 cnt /\ getr r1 9 = Z_to_bv 64 p /\ getr r1 19 = Z_to_bv 64 fd /\ getr r1 8 = Z_to_bv 64 s
                  /\ getr r1 2 = Z_to_bv 64 (s - 2128) /\ getr r1 1 = (0x6c780 : word) /\ keeps_but RIPL regs r1)).
    { unfold M6. eexists. split.
      - stepiv F_6c6fc D_6c6fc (Z_to_bv 64 (s - 2032)) ltac:(wval).
        stepsd F_6c700 D_6c700 (Z_to_bv 64 (s - 8)) ra ltac:(sok).
        stepsd F_6c704 D_6c704 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok).
        stepsd F_6c708 D_6c708 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok).
        stepsd F_6c70c D_6c70c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok).
        stepsd F_6c710 D_6c710 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok).
        stepsd F_6c714 D_6c714 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok).
        stepiv F_6c718 D_6c718 (Z_to_bv 64 s) ltac:(wval).
        stepiv F_6c71c D_6c71c (Z_to_bv 64 (s - 2128)) ltac:(wval).
        stepiv F_6c720 D_6c720 (Z_to_bv 64 cnt) ltac:(wval).
        stepiv F_6c724 D_6c724 (Z_to_bv 64 p) ltac:(wval).
        stepiv F_6c728 D_6c728 (Z_to_bv 64 fd) ltac:(wval).
        stepn F_6c72c D_6c72c.
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (match goal with |- ?g => check_closed_term g; apply bv_eq; vm_compute; reflexivity end). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q18 & Q9 & Q19 & Q8 & Q2 & Q1 & K1).
    destruct (tryinit_fast_run r1 M6 rom (0x6c780 : word) (s - 2128) Q2 Q1 Hra ltac:(lia) ltac:(lia)
                ltac:(replace (s - 2128 - 16)%Z with (s - 2144)%Z by lia; unfold M6; sok) HI6) as (r2 & RUN2 & T10 & T2 & T8 & T1 & K2).
    replace (s - 2128 - 8)%Z with (s - 2136)%Z in RUN2 by lia. replace (s - 2128 - 16)%Z with (s - 2144)%Z in RUN2 by lia.
    rewrite Q8 in RUN2. rewrite Q8 in T8.
    set (M8 := wbytes (wbytes M6 (Z_to_bv 64 (s - 2136)) (word_to_le_bytes 8 (0x6c780 : word))) (Z_to_bv 64 (s - 2144)) (word_to_le_bytes 8 (Z_to_bv 64 s))) in RUN2.
    assert (HR8 : rdn ASEGS M8 (0x154fa8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x14b908))) by (unfold M8, M6; repeat peel0; exact HR).
    assert (T18 : getr r2 18 = Z_to_bv 64 cnt) by (rewrite (K2 18%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact Q18).
    assert (T9 : getr r2 9 = Z_to_bv 64 p) by (rewrite (K2 9%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact Q9).
    assert (T19 : getr r2 19 = Z_to_bv 64 fd) by (rewrite (K2 19%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact Q19).
    eexists. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepn F_6c730 D_6c730.
      mld F_6c734 D_6c734 (0x154fa8 : word) HR8.
      stepiv F_6c738 D_6c738 (Z_to_bv 64 1) ltac:(wval).
      stepiv F_6c73c D_6c73c (Z_to_bv 64 fd) ltac:(wval).
      stepiv F_6c740 D_6c740 (Z_to_bv 64 p) ltac:(wval).
      stepiv F_6c744 D_6c744 (Z_to_bv 64 cnt) ltac:(wval).
      stepjr F_6c748 D_6c748 (Z_to_bv 64 0x14b908) ltac:(gres; reflexivity).
      vnorm.
      stepiv F_14b8c4 D_14b8c4 (Z_to_bv 64 (s - 2144)) ltac:(wval).
      stepsd F_14b8c8 D_14b8c8 (Z_to_bv 64 (s - 2136)) (Z_to_bv 64 0x6c79c) ltac:(unfold M8, M6; sok).
      stepiv F_14b8cc D_14b8cc (Z_to_bv 64 cnt) ltac:(wval).
      stepiv F_14b8d0 D_14b8d0 (Z_to_bv 64 p) ltac:(wval).
      stepiv F_14b8d4 D_14b8d4 (Z_to_bv 64 fd) ltac:(wval).
      stepn F_14b8d8 D_14b8d8.
      stepn F_14b8dc D_14b8dc.
      stepn F_14b8e0 D_14b8e0.
      stepn F_14b8e4 D_14b8e4.
      stepn F_14b8e8 D_14b8e8.
      stepn F_145ea0 D_145ea0.
      stepiv F_145e7c D_145e7c (Z_to_bv 64 63) ltac:(wval).
      stepiv F_145e80 D_145e80 (Z_to_bv 64 fd) ltac:(wval).
      stepiv F_145e84 D_145e84 (Z_to_bv 64 p) ltac:(wval).
      stepiv F_145e88 D_145e88 (Z_to_bv 64 cnt) ltac:(wval).
      stepiv F_145e8c D_145e8c (Z_to_bv 64 0) ltac:(wval).
      stepiv F_145e90 D_145e90 (Z_to_bv 64 0) ltac:(wval).
      stepiv F_145e94 D_145e94 (Z_to_bv 64 0) ltac:(wval).
      unfold M8, M6. fold (RDA regs). apply mst_refl.
    - repeat split; gres; rwH; try reflexivity; try (match goal with |- ?g => check_closed_term g; apply bv_eq; vm_compute; reflexivity end).
      eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [| solve_keeps_but].
      intros r Hr HL. apply K2; [exact Hr|]. cbv in HL |- *. intuition.
  Qed.

  Corollary wrap_read_pre_run : forall regs,
    getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = Z_to_bv 64 p -> getr regs 12 = Z_to_bv 64 cnt -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x6a570 : word) mem0 rom) (mkst regs' (0x145edc : word) (RDA regs) rom)
      /\ getr regs' 17 = Z_to_bv 64 63 /\ getr regs' 10 = Z_to_bv 64 fd /\ getr regs' 11 = Z_to_bv 64 p /\ getr regs' 12 = Z_to_bv 64 cnt
      /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 0
      /\ getr regs' 2 = Z_to_bv 64 (s - 2144) /\ getr regs' 1 = (0x14b930 : word)
      /\ getr regs' 8 = Z_to_bv 64 s /\ getr regs' 9 = Z_to_bv 64 p /\ getr regs' 18 = Z_to_bv 64 cnt /\ getr regs' 19 = Z_to_bv 64 fd /\ getr regs' 20 = Z_to_bv 64 1
      /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs H10 H11 H12 H2 H1.
    destruct (read_icpt_pre_run regs H10 H11 H12 H2 H1) as (r' & RUN & REST).
    exists r'. split; [|exact REST].
    eapply msteps_trans; [|exact RUN].
    stepn F_6a520 D_6a520.
    apply mst_refl.
  Qed.
End RDPRE.

Section RDPOST.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables ra : word.
  Variables p n s : Z.
  Variables kS fS lS faS laS : Z.
  Hypothesis HfS_def : fS = (SB + p / 8)%Z.           Hypothesis HlS_def : lS = (SB + (p + n - 1) / 8)%Z.
  Hypothesis HfaS_def : faS = (fS - fS mod 8)%Z.       Hypothesis HlaS_def : laS = (lS - lS mod 8)%Z.
  Hypothesis HnB : (0 < n < 2 ^ 40)%Z.
  Hypothesis HappS : in_app8 p n.
  Hypothesis Hs : (0x1000000 <= s - 2200)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis HshS : (lS + 8 <= s - 2200)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 2200)) 2200%nat = true.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HG : rt_layout_globs mem0.
  Hypothesis HZS : (0 < n)%Z -> forall x : word, (fS <= bv_unsigned x < lS)%Z -> mem0 x = Some (Z_to_bv 8 0).
  Hypothesis HLS : (0 < n)%Z -> mem0 (Z_to_bv 64 lS) = Some (Z_to_bv 8 kS).
  Hypothesis HkS : kS = 0%Z \/ ((p + n - 1) mod 8 < kS <= 7)%Z.
  Hypothesis HWS : (0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 faS) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 laS) 8%nat = Some w1.

  #[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try solve_keeps_but.
  #[local] Ltac hide_dj := try hide HkS; try hide HappS.

  Lemma Hn : (0 <= n <= 2 ^ 40)%Z.  Proof. hide_dj. lia. Qed.
  Lemma pS_facts : (0 <= p)%Z /\ (p + n + 8 <= HIGHEND)%Z /\ (0 <= p / 8 <= HIGHEND)%Z /\ (0 < n -> p / 8 <= (p + n - 1) / 8 <= HIGHEND)%Z.
  Proof.
    hide_dj.
    unhide HappS.
    unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *. destruct HappS as [[H1 H2]|[H1 H2]];
    (repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia | intros; apply Z.div_le_mono; lia | intros; apply Z.div_le_upper_bound; lia]).
  Qed.
  Lemma pD_facts : (0 <= p)%Z /\ (p + n + 8 <= HIGHEND)%Z /\ (0 <= p / 8 <= HIGHEND)%Z /\ (0 < n -> p / 8 <= (p + n - 1) / 8 <= HIGHEND)%Z.
  Proof. hide_dj. exact pS_facts. Qed.
  Lemma flS_facts : (0 < n)%Z -> (SB <= fS <= lS)%Z /\ (lS + 8 <= s - 2200)%Z /\ (fS - 7 <= faS <= fS)%Z /\ (lS - 7 <= laS <= lS)%Z.
  Proof.
    hide_dj.
    intros Hn0. pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq Hn0). unfold SB, HIGHEND in *.
    pose proof (Z.mod_pos_bound fS 8 ltac:(lia)). pose proof (Z.mod_pos_bound lS 8 ltac:(lia)). repeat split; lia.
  Qed.

  Definition out_agree (M : word -> option byte) : Prop :=
    forall x : word, (bv_unsigned x < s - 2200 \/ s <= bv_unsigned x)%Z -> M x = mem0 x.
  Lemma out_agree_refl : out_agree mem0.  Proof. hide_dj. intros x _. reflexivity. Qed.
  Lemma out_agree_rdn : forall M (a : word) k, out_agree M -> (bv_unsigned a + Z.of_nat k <= s - 2200)%Z ->
    rdn ASEGS M a k = rdn ASEGS mem0 a k.
  Proof. hide_dj. intros M a k HF Ha. apply rdn_ext; [lia|]. intros x Hx. apply HF. lia. Qed.
  Lemma out_agree_globs : forall M, out_agree M -> rt_layout_globs M /\ True.
  Proof.
    hide_dj.
    intros M HF. destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    unfold rt_layout_globs. rewrite !(out_agree_rdn M) by (first [exact HF | cbn [Z.of_nat Pos.to_nat]; imm_norm; lia]).
    repeat split; assumption.
  Qed.
  Lemma out_agree_store_ok : forall M k (j : nat), mem_grows mem0 M -> (Z.of_nat j <= k <= 2200)%Z ->
    store_ok ASEGS M (Z_to_bv 64 (s - k)) j = true.
  Proof.
    hide_dj.
    intros M k j HGr Hk. apply (store_ok_mono _ _ mem0 M _ HGr).
    apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 2200)) _ 2200%nat); [unorm; cbn [Z.of_nat Pos.to_nat]; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia].
  Qed.

  Definition slots_ok (regs0 : bvmap 5 word) (M : word -> option byte) : Prop :=
    rdn ASEGS M (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra) /\
    rdn ASEGS M (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 8)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 9)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 18)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 19)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 20)).
  Definition FR (regs0 : bvmap 5 word) (M : word -> option byte) : Prop := out_agree M /\ mem_grows mem0 M /\ slots_ok regs0 M.

  Lemma rdn_slot_ext : forall (M1 M2 : word -> option byte) k,
    (forall x : word, (s - 2128 <= bv_unsigned x < s)%Z -> M1 x = M2 x) -> (8 <= k <= 2128)%Z ->
    rdn ASEGS M1 (Z_to_bv 64 (s - k)) 8%nat = rdn ASEGS M2 (Z_to_bv 64 (s - k)) 8%nat.
  Proof.
    hide_dj.
    intros M1 M2 k HE Hk. apply rdn_ext; [unorm; cbn [Z.of_nat Pos.to_nat]; lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. apply HE. lia.
  Qed.
  Lemma slots_ok_ext : forall regs0 (M1 M2 : word -> option byte),
    (forall x : word, (s - 2128 <= bv_unsigned x < s)%Z -> M2 x = M1 x) -> slots_ok regs0 M1 -> slots_ok regs0 M2.
  Proof.
    hide_dj.
    intros regs0 M1 M2 HE (R1 & R2 & R3 & R4 & R5 & R6). unfold slots_ok.
    rewrite !(rdn_slot_ext M2 M1) by (first [exact HE | lia]). repeat split; assumption.
  Qed.
  Lemma FR_region : forall regs0 M M', FR regs0 M -> frame_only M (s - 2128) M' -> mem_grows M M' -> FR regs0 M'.
  Proof.
    hide_dj.
    intros regs0 M M' (O & G & R) HF HGr. split; [|split].
    - intros x Hx. rewrite (HF x) by lia. apply O. exact Hx.
    - eapply mem_grows_trans; [exact G | exact HGr].
    - apply (slots_ok_ext regs0 M M'); [|exact R]. intros x Hx. apply HF. lia.
  Qed.

  Lemma rdnWS : forall M, out_agree M -> (0 < n <= 64)%Z -> exists w0 w1,
    rdn ASEGS M (Z_to_bv 64 faS) 8%nat = Some w0 /\ rdn ASEGS M (Z_to_bv 64 laS) 8%nat = Some w1
    /\ (0 <= bytes_le_to_Z w0 < 2 ^ 64)%Z /\ (0 <= bytes_le_to_Z w1 < 2 ^ 64)%Z.
  Proof.
    hide_dj.
    intros M HO Hn64. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB in *.
    destruct (HWS Hn64) as (w0 & w1 & R0 & R1). exists w0, w1.
    rewrite !(out_agree_rdn M) by (first [exact HO | unorm; cbn [Z.of_nat Pos.to_nat]; lia]).
    split; [exact R0 | split; [exact R1 | split; [exact (bytes8_range _ _ _ _ R0) | exact (bytes8_range _ _ _ _ R1)]]].
  Qed.
  Lemma rdn1S : forall M z, out_agree M -> (0 < n)%Z -> (fS <= z < lS)%Z -> rdn ASEGS M (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 0].
  Proof.
    hide_dj.
    intros M z HO Hn0 Hz. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
    cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HZS Hn0) by (unorm; lia). reflexivity.
  Qed.
  Lemma rdnLS : forall M z, out_agree M -> (0 < n)%Z -> z = lS -> rdn ASEGS M (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 kS].
  Proof.
    hide_dj.
    intros M z HO Hn0 ->. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
    cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HLS Hn0). reflexivity.
  Qed.
  #[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
  #[local] Ltac mlbu0 F D z RD :=
    chain_step; [reflexivity
      | eapply step_lbu; [exact F | reflexivity | exact D | maddr z; apply RD; [assumption | lia | lia]]
      | step_simpl; vnorm].
  #[local] Ltac mlbk F D z RD k :=
    chain_step; [reflexivity
      | eapply step_lb; [exact F | reflexivity | exact D | maddr z; apply RD; [assumption | lia | lia]]
      | step_simpl; vnorm; rewrite (v_lb_k k ltac:(lia))].
  #[local] Ltac mldw F D z R w :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := w) (v := Z_to_bv 64 (bytes_le_to_Z w)); [exact F | reflexivity | exact D | maddr z; exact R | unorm; reflexivity]
      | step_simpl; vnorm].

  Definition cR_pre (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 n /\ getr rg 9 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s /\ getr rg 2 = Z_to_bv 64 (s - 2128).
  Definition cR_post (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2128).

  Lemma ret_ok_4f920 : ret_ok (0x6c8a8 : word).  Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma cRr_run : forall regs0 M regs,
    cR_pre regs -> FR regs0 M -> (64 < n)%Z ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x6c7a4 : word) M rom) (mkst regs' (0x6c7fc : word) M' rom)
      /\ cR_post regs' /\ keeps_but RIPL regs regs' /\ FR regs0 M'.
  Proof.
    hide_dj.
    intros regs0 M regs (H10 & H9 & H8 & H2) HFR Hn64. pose proof HFR as (HO & HGr & HR).
    pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x6c7a4 : word) M rom) (mkst r1 (0x826a0 : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 p /\ getr r1 11 = Z_to_bv 64 n /\ getr r1 2 = Z_to_bv 64 (s - 2128) /\ getr r1 1 = (0x6c8a8 : word)
                  /\ getr r1 18 = Z_to_bv 64 n /\ getr r1 9 = Z_to_bv 64 p /\ getr r1 8 = Z_to_bv 64 s /\ getr r1 20 = Z_to_bv 64 (s - 2120) /\ keeps_but RIPL regs r1)).
    { eexists. split.
      - stepiv F_6c754 D_6c754 (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
        stepiv F_6c758 D_6c758 (Z_to_bv 64 (s - 2048)) ltac:(wval).
        stepiv F_6c75c D_6c75c (Z_to_bv 64 (s - 2120)) ltac:(wval).
        stepb_ft F_6c760 D_6c760 ltac:(cond).
        stepiv F_6c764 D_6c764 (Z_to_bv 64 (n - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).
        stepn F_6c768 D_6c768.
        stepb_tk F_6c76c D_6c76c ltac:(cond).
        stepiv F_6c848 D_6c848 (Z_to_bv 64 n) ltac:(wval).
        stepiv F_6c84c D_6c84c (Z_to_bv 64 p) ltac:(wval).
        stepiv F_6c850 D_6c850 (Z_to_bv 64 n) ltac:(wval).
        stepn F_6c854 D_6c854.
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q18 & Q9 & Q8 & Q20 & K1).
    pose proof (out_agree_globs M HO) as (HGM & _).
    pose proof (region_is_poisoned_run M rom (Z_to_bv 64 (s - 2128)) (0x6c8a8 : word) p n (s - 2128)
                  ltac:(unorm; reflexivity) ltac:(lia) HappS ltac:(lia) ltac:(unfold SB in *; lia)
                  ltac:(replace (s - 2128 - 72)%Z with (s - 2200)%Z by lia; apply out_agree_store_ok; [exact HGr | cbn; lia])
                  (ret_ok_4f920) HGM kS) as RP.
    specialize (RP ltac:(intros x Hx; rewrite (HO x) by (unfold SB in *; lia); apply HZS; [lia | unfold SB in *; lia])).
    specialize (RP ltac:(rewrite HO by (unfold SB in *; unorm; lia); rewrite <- HlS_def; apply HLS; lia) HkS).
    destruct (RP r1 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & V2 & V1 & K2 & F2 & G2).
    assert (S18 : getr r2 18 = Z_to_bv 64 n) by (rewrite (K2 18%bv) by (cbv; tauto); exact Q18).
    assert (S9 : getr r2 9 = Z_to_bv 64 p) by (rewrite (K2 9%bv) by (cbv; tauto); exact Q9).
    assert (S8 : getr r2 8 = Z_to_bv 64 s) by (rewrite (K2 8%bv) by (cbv; tauto); exact Q8).
    eexists. exists M2. split; [|split; [|split; [|eapply FR_region; eassumption]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepiv F_6c858 D_6c858 (Z_to_bv 64 0) ltac:(wval).
      stepiv F_6c85c D_6c85c (Z_to_bv 64 n) ltac:(wval).
      stepb_tk F_6c860 D_6c860 ltac:(cond).
      apply mst_refl.
    - unfold cR_post. post.
    - eapply keeps_but_trans; [exact K1|]. solve_keeps_but.
  Qed.

  Definition cRqa_post (u0 u1 : Z) (rg : bvmap 5 word) : Prop :=
    getr rg 11 = Z_to_bv 64 fS /\ getr rg 12 = Z_to_bv 64 lS /\ getr rg 13 = Z_to_bv 64 (p + n - 1) /\ getr rg 14 = Z_to_bv 64 (Z.lor u1 u0)
    /\ getr rg 10 = Z_to_bv 64 n /\ getr rg 9 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s /\ getr rg 2 = Z_to_bv 64 (s - 2128).
  Lemma cRqa_run : forall M regs w0 w1,
    cR_pre regs -> out_agree M -> (0 < n <= 64)%Z ->
    rdn ASEGS M (Z_to_bv 64 faS) 8%nat = Some w0 -> rdn ASEGS M (Z_to_bv 64 laS) 8%nat = Some w1 ->
    (0 <= bytes_le_to_Z w0 < 2 ^ 64)%Z -> (0 <= bytes_le_to_Z w1 < 2 ^ 64)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x6c7a4 : word) M rom) (mkst regs' (0x6c7f8 : word) M rom)
      /\ cRqa_post (bytes_le_to_Z w0) (bytes_le_to_Z w1) regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs w0 w1 (H10 & H9 & H8 & H2) HO Hn64 R0 R1 B0 B1.
    pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
    pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4).
    pose proof (out_agree_globs M HO) as ((G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & _).
    unfold SB, HIGHEND in *.
    pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Mp.
    pose proof (Z.mod_pos_bound fS 8 ltac:(lia)) as Mf. pose proof (Z.mod_pos_bound lS 8 ltac:(lia)) as Ml.
    pose proof (lor_bound64 (bytes_le_to_Z w1) (bytes_le_to_Z w0) B1 B0) as BL.
    eexists. split.
    - stepiv F_6c754 D_6c754 (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
      stepiv F_6c758 D_6c758 (Z_to_bv 64 (s - 2048)) ltac:(wval).
      stepiv F_6c75c D_6c75c (Z_to_bv 64 (s - 2120)) ltac:(wval).
      stepb_ft F_6c760 D_6c760 ltac:(cond).
      stepiv F_6c764 D_6c764 (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (n + - 65)); f_equal; lia).
      stepn F_6c768 D_6c768.
      stepb_ft F_6c76c D_6c76c ltac:(cond).
      stepn F_6c770 D_6c770.
      mld F_6c774 D_6c774 (0x153138 : word) G1.
      stepiv F_6c778 D_6c778 (Z_to_bv 64 (p + n)) ltac:(wval).
      mld F_6c77c D_6c77c (0x15c9b8 : word) G2.
      stepiv F_6c780 D_6c780 (Z_to_bv 64 (p / 8)) ltac:(wval).
      stepiv F_6c784 D_6c784 (Z_to_bv 64 (p + n - 1)) ltac:(wval).
      stepiv F_6c788 D_6c788 (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
      stepiv F_6c78c D_6c78c (Z_to_bv 64 fS) ltac:(wval).
      stepiv F_6c790 D_6c790 (Z_to_bv 64 lS) ltac:(wval).
      stepiv F_6c794 D_6c794 (Z_to_bv 64 faS)
        ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
      stepiv F_6c798 D_6c798 (Z_to_bv 64 laS)
        ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
      mldw F_6c79c D_6c79c faS R0 w0.
      mldw F_6c7a0 D_6c7a0 laS R1 w1.
      stepov F_6c7a4 D_6c7a4 (Z_to_bv 64 (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0))) ltac:(gres; rwH; unfold v_or; unorm; reflexivity).
      apply mst_refl.
    - unfold cRqa_post. split; [post | solve_keeps_but].
  Qed.

  Definition qlR_inv (rg : bvmap 5 word) (i : Z) : Prop :=
    getr rg 11 = Z_to_bv 64 (fS + i) /\ getr rg 12 = Z_to_bv 64 lS /\ getr rg 13 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 n /\ getr rg 9 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s /\ getr rg 2 = Z_to_bv 64 (s - 2128).
  Definition qlR_post (rg : bvmap 5 word) : Prop :=
    getr rg 13 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 n /\ getr rg 9 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s /\ getr rg 2 = Z_to_bv 64 (s - 2128).
  Lemma qloopR_run : forall M (q : nat) regs i,
    out_agree M -> (0 < n)%Z -> qlR_inv regs i -> (0 <= i)%Z -> (fS + i + Z.of_nat q + 1 = lS)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x6c960 : word) M rom) (mkst regs' (0x6c970 : word) M rom)
      /\ qlR_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M q. induction q as [|q IH]; intros regs i HO Hn0 (H13 & H14 & H15 & H10 & H9 & H8 & H2) Hi Hq;
      pose proof (flS_facts Hn0) as (F1 & F2 & _); unfold SB in *.
    - eexists. split.
      + mlbu0 F_6c910 D_6c910 (fS + i)%Z rdn1S.
        stepiv F_6c914 D_6c914 (Z_to_bv 64 (fS + i + 1)) ltac:(wval).
        stepov F_6c918 D_6c918 (Z_to_bv 64 0) ltac:(vlit).
        stepb_ft F_6c91c D_6c91c ltac:(cond).
        apply mst_refl.
      + unfold qlR_post. post.
    - eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x6c960 : word) M rom) (fun rg => qlR_inv rg (i + 1) /\ keeps_but RIPL regs rg)).
      + eexists. split.
        * mlbu0 F_6c910 D_6c910 (fS + i)%Z rdn1S.
          stepiv F_6c914 D_6c914 (Z_to_bv 64 (fS + i + 1)) ltac:(wval).
          stepov F_6c918 D_6c918 (Z_to_bv 64 0) ltac:(vlit).
          stepb_tk F_6c91c D_6c91c ltac:(cond).
          apply mst_refl.
        * unfold qlR_inv. post.
      + cbv beta. intros r1 (I1 & K1).
        destruct (IH r1 (i + 1)%Z HO Hn0 I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
        exists r2. split; [exact RUN | split; [exact P2 | eapply keeps_but_trans; eassumption]].
  Qed.

  Lemma cRqf_run : forall M regs u0 u1,
    cRqa_post u0 u1 regs -> (0 <= Z.lor u1 u0 < 2 ^ 64)%Z -> Z.lor u1 u0 = 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x6c7f8 : word) M rom) (mkst regs' (0x6c7fc : word) M rom)
      /\ cR_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs u0 u1 (H13 & H14 & HL' & H15 & H10 & H9 & H8 & H2) BL E.
    eexists. split.
    - stepb_ft F_6c7a8 D_6c7a8 ltac:(cond).
      apply mst_refl.
    - unfold cR_post. post.
  Qed.

  Lemma cRqs_run : forall M regs u0 u1,
    cRqa_post u0 u1 regs -> out_agree M -> (0 < n <= 64)%Z -> (0 <= Z.lor u1 u0 < 2 ^ 64)%Z -> Z.lor u1 u0 <> 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x6c7f8 : word) M rom) (mkst regs' (0x6c7fc : word) M rom)
      /\ cR_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs u0 u1 (H13 & H14 & HL' & H15 & H10 & H9 & H8 & H2) HO Hn64 BL NE.
    pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
    pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB, HIGHEND in *.
    pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as Mq.
    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x6c95c : word) M rom) (fun rg => qlR_inv rg 0 /\ keeps_but RIPL regs rg)).
    { unhide HkS. destruct HkS as [K0|K7].
      - eexists. split.
        + stepb_tk F_6c7a8 D_6c7a8 ltac:(cond).
          mlbk F_6c8f4 D_6c8f4 lS rdnLS kS.
          stepiv F_6c8f8 D_6c8f8 (Z_to_bv 64 ((p + n - 1) mod 8))
            ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
          stepov F_6c8fc D_6c8fc (Z_to_bv 64 0)
            ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kS)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
          stepov F_6c900 D_6c900 (Z_to_bv 64 0)
            ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
                  replace ((p + n - 1) mod 8 <? kS)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
          stepiv F_6c904 D_6c904 (Z_to_bv 64 1) ltac:(vlit).
          stepov F_6c908 D_6c908 (Z_to_bv 64 0) ltac:(vlit).
          apply mst_refl.
        + unfold qlR_inv. post.
      - eexists. split.
        + stepb_tk F_6c7a8 D_6c7a8 ltac:(cond).
          mlbk F_6c8f4 D_6c8f4 lS rdnLS kS.
          stepiv F_6c8f8 D_6c8f8 (Z_to_bv 64 ((p + n - 1) mod 8))
            ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
          stepov F_6c8fc D_6c8fc (Z_to_bv 64 1)
            ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kS)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
          stepov F_6c900 D_6c900 (Z_to_bv 64 1)
            ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
                  replace ((p + n - 1) mod 8 <? kS)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
          stepiv F_6c904 D_6c904 (Z_to_bv 64 0) ltac:(vlit).
          stepov F_6c908 D_6c908 (Z_to_bv 64 0) ltac:(vlit).
          apply mst_refl.
        + unfold qlR_inv. post. }
    cbv beta. intros r1 ((I13 & I14 & I15 & I10 & I9 & I8 & I2) & K1).
    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x6c970 : word) M rom) (fun rg => qlR_post rg /\ keeps_but RIPL regs rg)).
    { destruct (Z.lt_ge_cases fS lS) as [Hfl|Hfl].
      - eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x6c960 : word) M rom) (fun rg => qlR_inv rg 0 /\ keeps_but RIPL regs rg)).
        + eexists. split.
          * stepb_ft F_6c90c D_6c90c ltac:(cond).
            apply mst_refl.
          * split; [unfold qlR_inv; repeat split; assumption | exact K1].
        + cbv beta. intros r2 (I2' & K2).
          destruct (qloopR_run M (Z.to_nat (lS - fS - 1)) r2 0 HO ltac:(lia) I2' ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (r3 & RUN3 & P3 & K3).
          exists r3. split; [exact RUN3 | split; [exact P3 | eapply keeps_but_trans; eassumption]].
      - eexists. split.
        + stepb_tk F_6c90c D_6c90c ltac:(cond).
          apply mst_refl.
        + split; [unfold qlR_post; repeat split; assumption | exact K1]. }
    cbv beta. intros r4 ((J15 & J10 & J9 & J8 & J2) & K4).
    eexists. split.
    - stepiv F_6c920 D_6c920 (Z_to_bv 64 0) ltac:(vlit).
      stepb_tk F_6c924 D_6c924 ltac:(cond).
      apply mst_refl.
    - unfold cR_post. split; [post|]. eapply keeps_but_trans; [exact K4|]. solve_keeps_but.
  Qed.

  Lemma cR_run : forall regs0 M regs,
    cR_pre regs -> FR regs0 M ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x6c7a4 : word) M rom) (mkst regs' (0x6c7fc : word) M' rom)
      /\ cR_post regs' /\ keeps_but RIPL regs regs' /\ FR regs0 M'.
  Proof.
    hide_dj.
    intros regs0 M regs P1 HFR. pose proof HFR as (HO & HGr & HR).
    destruct (Z.eq_dec n 0) as [Hn0|Hn0].
    { exfalso. lia. }

    destruct (Z.le_gt_cases n 64) as [Hle|Hgt].
    - destruct (rdnWS M HO ltac:(lia)) as (w0 & w1 & R0 & R1 & B0 & B1).
      destruct (cRqa_run M regs w0 w1 P1 HO ltac:(lia) R0 R1 B0 B1) as (r2 & RUN2 & P2 & K2).
      pose proof (lor_bound64 _ _ B1 B0) as BL.
      destruct (Z.eq_dec (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0)) 0) as [E|NE].
      + destruct (cRqf_run M r2 _ _ P2 BL E) as (r3 & RUN3 & P3 & K3). exists r3, M.
        split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | exact HFR]]].
      + destruct (cRqs_run M r2 _ _ P2 HO ltac:(lia) BL NE) as (r3 & RUN3 & P3 & K3). exists r3, M.
        split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | exact HFR]]].
    - exact (cRr_run regs0 M regs P1 HFR Hgt).
  Qed.

  Definition c2_pre (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2144) /\ getr rg 1 = (0x14b930 : word)
    /\ getr rg 8 = Z_to_bv 64 s /\ getr rg 9 = Z_to_bv 64 p /\ getr rg 20 = Z_to_bv 64 1.
  Lemma ret_ok_d0c80 : ret_ok (0x14b930 : word).  Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma ret_ok_4f814 : ret_ok (0x6c79c : word).  Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma c2_run : forall regs M,
    c2_pre regs -> rdn ASEGS M (Z_to_bv 64 (s - 2136)) 8%nat = Some (word_to_le_bytes 8 (0x6c79c : word)) ->
    exists regs',
      msteps ASEGS (mkst regs (0x145ee0 : word) M rom) (mkst regs' (0x6c7a4 : word) M rom)
      /\ cR_pre regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros regs M (H10 & H2 & H1 & H8 & H9 & H20) RA. destruct Hs as [S1' S2'].
    pose proof ret_ok_d0c80 as Rce. pose proof ret_ok_4f814 as R4e.
    eexists. split.
    - stepret F_145e9c D_145e9c (0x14b930 : word) ltac:(rwH; reflexivity).
      stepld F_14b8ec D_14b8ec (0x6c79c : word) ltac:(maddr (s - 2136)%Z; exact RA).
      stepiv F_14b8f0 D_14b8f0 (Z_to_bv 64 (s - 2128)) ltac:(wval).
      stepn F_14b8f4 D_14b8f4.
      stepn F_13418c D_13418c.
      stepn F_134190 D_134190.
      stepb_tk F_134194 D_134194 ltac:(cond).
      stepret F_1341c0 D_1341c0 (0x6c79c : word) ltac:(rwH; reflexivity).
      stepb_ft F_6c74c D_6c74c ltac:(cond).
      stepb_ft F_6c750 D_6c750 ltac:(rwH; unfold c_lts, bv_lts; rewrite !signed64_small by lia;
                                     first [apply Z.ltb_lt | apply Z.ltb_ge | apply Z.leb_le | apply Z.leb_gt]; lia).
      apply mst_refl.
    - unfold cR_pre. post.
  Qed.

  Lemma c3_run : forall regs0 regs M,
    cR_post regs -> FR regs0 M ->
    exists regs',
      msteps ASEGS (mkst regs (0x6c7fc : word) M rom) (mkst regs' ra M rom)
      /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20
      /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros regs0 regs M (H10 & H2) (HO & HGr & (R1 & R2 & R3 & R4 & R5 & R6)). destruct Hs as [S1' S2'].
    eexists. split.
    - stepiv F_6c7ac D_6c7ac (Z_to_bv 64 (s - 2032)) ltac:(wval).
      stepld F_6c7b0 D_6c7b0 ra ltac:(maddr (s - 8)%Z; exact R1).
      stepld F_6c7b4 D_6c7b4 (getr regs0 8) ltac:(maddr (s - 16)%Z; exact R2).
      stepld F_6c7b8 D_6c7b8 (getr regs0 9) ltac:(maddr (s - 24)%Z; exact R3).
      stepld F_6c7bc D_6c7bc (getr regs0 18) ltac:(maddr (s - 32)%Z; exact R4).
      stepld F_6c7c0 D_6c7c0 (getr regs0 19) ltac:(maddr (s - 40)%Z; exact R5).
      stepld F_6c7c4 D_6c7c4 (getr regs0 20) ltac:(maddr (s - 48)%Z; exact R6).
      stepiv F_6c7c8 D_6c7c8 (Z_to_bv 64 s) ltac:(wval).
      stepret F_6c7cc D_6c7cc ra ltac:(rwH; reflexivity).
      apply mst_refl.
    - repeat split; gres; try reflexivity; [exact H10 | solve_keeps_but].
  Qed.

  Theorem read_icpt_post_run : forall regs0 regs M,
    c2_pre regs -> FR regs0 M -> rdn ASEGS M (Z_to_bv 64 (s - 2136)) 8%nat = Some (word_to_le_bytes 8 (0x6c79c : word)) ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x145ee0 : word) M rom) (mkst regs' ra M' rom)
      /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20
      /\ keeps_but RIPL regs regs' /\ FR regs0 M'.
  Proof.
    hide_dj.
    intros regs0 regs M P2 HFR RA.
    destruct (c2_run regs M P2 RA) as (r1 & RUN1 & P1 & K1).
    destruct (cR_run regs0 M r1 P1 HFR) as (r2 & M2 & RUN2 & Q2 & K2 & F2).
    destruct (c3_run regs0 r2 M2 Q2 F2) as (r3 & RUN3 & T10 & T2 & T1 & T8 & T9 & T18 & T19 & T20 & K3).
    exists r3, M2. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - split; [exact T10|]. split; [exact T2|]. split; [exact T1|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|].
      split; [exact T19|]. split; [exact T20|]. split; [|exact F2].
      eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [exact K2|]. exact K3.
  Qed.
End RDPOST.

Section RDPOST0.
  Variable rom : word -> option byte.
  Variables ra : word.
  Variable s : Z.
  Hypothesis Hs : (0x1000000 <= s - 2200)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hret : ret_ok ra.

  Theorem read_icpt_post0_run : forall regs0 regs M,
    getr regs 10 = Z_to_bv 64 0 -> getr regs 2 = Z_to_bv 64 (s - 2144) -> getr regs 1 = (0x14b930 : word) -> getr regs 8 = Z_to_bv 64 s -> getr regs 20 = Z_to_bv 64 1 ->
    rdn ASEGS M (Z_to_bv 64 (s - 2136)) 8%nat = Some (word_to_le_bytes 8 (0x6c79c : word)) ->
    rdn ASEGS M (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra) ->
    rdn ASEGS M (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 8)) ->
    rdn ASEGS M (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 9)) ->
    rdn ASEGS M (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 18)) ->
    rdn ASEGS M (Z_to_bv 64 (s - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 19)) ->
    rdn ASEGS M (Z_to_bv 64 (s - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 20)) ->
    exists regs',
      msteps ASEGS (mkst regs (0x145ee0 : word) M rom) (mkst regs' ra M rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20
      /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs0 regs M H10 H2 H1 H8 H20 RA R1 R2 R3 R4 R5 R6. destruct Hs as [S1' S2'].
    assert (Rce : ret_ok (0x14b930 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (R4e : ret_ok (0x6c79c : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    #[local] Ltac maddr0 z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
    eexists. split.
    - stepret F_145e9c D_145e9c (0x14b930 : word) ltac:(rwH; reflexivity).
      stepld F_14b8ec D_14b8ec (0x6c79c : word) ltac:(maddr0 (s - 2136)%Z; exact RA).
      stepiv F_14b8f0 D_14b8f0 (Z_to_bv 64 (s - 2128)) ltac:(wval).
      stepn F_14b8f4 D_14b8f4.
      stepn F_13418c D_13418c.
      stepn F_134190 D_134190.
      stepb_tk F_134194 D_134194 ltac:(cond).
      stepret F_1341c0 D_1341c0 (0x6c79c : word) ltac:(rwH; reflexivity).
      stepb_ft F_6c74c D_6c74c ltac:(cond).
      stepb_tk F_6c750 D_6c750 ltac:(rwH; unfold c_lts, bv_lts; rewrite !signed64_small by lia;
                                     first [apply Z.ltb_lt | apply Z.ltb_ge | apply Z.leb_le | apply Z.leb_gt]; lia).
      stepiv F_6c7ac D_6c7ac (Z_to_bv 64 (s - 2032)) ltac:(wval).
      stepld F_6c7b0 D_6c7b0 ra ltac:(maddr0 (s - 8)%Z; exact R1).
      stepld F_6c7b4 D_6c7b4 (getr regs0 8) ltac:(maddr0 (s - 16)%Z; exact R2).
      stepld F_6c7b8 D_6c7b8 (getr regs0 9) ltac:(maddr0 (s - 24)%Z; exact R3).
      stepld F_6c7bc D_6c7bc (getr regs0 18) ltac:(maddr0 (s - 32)%Z; exact R4).
      stepld F_6c7c0 D_6c7c0 (getr regs0 19) ltac:(maddr0 (s - 40)%Z; exact R5).
      stepld F_6c7c4 D_6c7c4 (getr regs0 20) ltac:(maddr0 (s - 48)%Z; exact R6).
      stepiv F_6c7c8 D_6c7c8 (Z_to_bv 64 s) ltac:(wval).
      stepret F_6c7cc D_6c7cc ra ltac:(rwH; reflexivity).
      apply mst_refl.
    - repeat split; gres; rwH; try reflexivity. solve_keeps_but.
  Qed.
End RDPOST0.
End FPX_1.
