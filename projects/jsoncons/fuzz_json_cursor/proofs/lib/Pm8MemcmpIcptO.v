(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib PmIcptIfaceA Pm8MemIsZero Pm8RegionPoisoned Pm8AsanMemset Pm8AsanMemcpy Pm8StrlenIcpt.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8MemcmpTab Pm8MemcmpMusl Pm8MemcmpMicO Pm8MemcmpIcptI.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section FPX_1. Context {fx : PropExec.FPState}.

Definition icptO_globs (M : word -> option byte) : Prop :=
  rdn ASEGS M (0x15d698 : word) 1%nat = Some [Z_to_bv 8 1] /\
  rdn ASEGS M (0x154f90 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x144e04)).

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
#[local] Ltac mvval := gres; rwH; rewrite ?v_addi_0; reflexivity.

Section ICPT.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables p1 p2 n s : Z.
  Variables b1 b2 : list byte.
  Variables kS fS lS faS laS : Z.
  Variables kD fD lD faD laD : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis HfS_def : fS = (SB + p1 / 8)%Z.           Hypothesis HlS_def : lS = (SB + (p1 + n - 1) / 8)%Z.
  Hypothesis HfaS_def : faS = (fS - fS mod 8)%Z.       Hypothesis HlaS_def : laS = (lS - lS mod 8)%Z.
  Hypothesis HfD_def : fD = (SB + p2 / 8)%Z.           Hypothesis HlD_def : lD = (SB + (p2 + n - 1) / 8)%Z.
  Hypothesis HfaD_def : faD = (fD - fD mod 8)%Z.       Hypothesis HlaD_def : laD = (lD - lD mod 8)%Z.
  Hypothesis Hn : (0 <= n <= 2 ^ 40)%Z.
  Hypothesis HappS : in_app8 p1 n.
  Hypothesis HappD : in_app8 p2 n.
  Hypothesis Hs : (0x1000000 <= s - 4552)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis HshS : (lS + 8 <= s - 4552)%Z.
  Hypothesis HshD : (lD + 8 <= s - 4552)%Z.
  Hypothesis HdjS : (0 < n -> p1 + n <= s - 4552 \/ s <= p1)%Z.
  Hypothesis HdjD : (0 < n -> p2 + n <= s - 4552 \/ s <= p2)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 4552)) 4552%nat = true.
  Hypothesis Hsrc1 : rdn ASEGS mem0 (Z_to_bv 64 p1) (Z.to_nat n) = Some b1.
  Hypothesis Hsrc2 : rdn ASEGS mem0 (Z_to_bv 64 p2) (Z.to_nat n) = Some b2.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HG : rt_layout_globs mem0.
  Hypothesis HI : mcmp_icpt_globs mem0.
  Hypothesis HC : icptO_globs mem0.
  Hypothesis HCI : icptI_globs mem0.
  Hypothesis HZS : (0 < n)%Z -> forall x : word, (fS <= bv_unsigned x < lS)%Z -> mem0 x = Some (Z_to_bv 8 0).
  Hypothesis HLS : (0 < n)%Z -> mem0 (Z_to_bv 64 lS) = Some (Z_to_bv 8 kS).
  Hypothesis HkS : kS = 0%Z \/ ((p1 + n - 1) mod 8 < kS <= 7)%Z.
  Hypothesis HWS : (0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 faS) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 laS) 8%nat = Some w1.
  Hypothesis HZD : (0 < n)%Z -> forall x : word, (fD <= bv_unsigned x < lD)%Z -> mem0 x = Some (Z_to_bv 8 0).
  Hypothesis HLD : (0 < n)%Z -> mem0 (Z_to_bv 64 lD) = Some (Z_to_bv 8 kD).
  Hypothesis HkD : kD = 0%Z \/ ((p2 + n - 1) mod 8 < kD <= 7)%Z.
  Hypothesis HWD : (0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 faD) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 laD) 8%nat = Some w1.

  #[local] Ltac hide_dj := try hide HkS; try hide HkD; try hide HappS; try hide HappD; try hide HdjS; try hide HdjD.

  Lemma sp_s : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
  Lemma pS_facts : (0 <= p1)%Z /\ (p1 + n + 8 <= HIGHEND)%Z /\ (0 < n -> SB <= fS <= lS)%Z.
  Proof.
    hide_dj. unhide HappS. unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *.
    assert (Q : (0 < n -> p1 / 8 <= (p1 + n - 1) / 8)%Z) by (intros; apply Z.div_le_mono; lia).
    assert (Q0 : (0 <= p1 -> 0 <= p1 / 8)%Z) by (intros; apply Z.div_pos; lia).
    destruct HappS as [[H1 H2]|[H1 H2]]; (split; [lia | split; [lia | intros X; specialize (Q X); lia]]).
  Qed.
  Lemma pD_facts : (0 <= p2)%Z /\ (p2 + n + 8 <= HIGHEND)%Z /\ (0 < n -> SB <= fD <= lD)%Z.
  Proof.
    hide_dj. unhide HappD. unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *.
    assert (Q : (0 < n -> p2 / 8 <= (p2 + n - 1) / 8)%Z) by (intros; apply Z.div_le_mono; lia).
    assert (Q0 : (0 <= p2 -> 0 <= p2 / 8)%Z) by (intros; apply Z.div_pos; lia).
    destruct HappD as [[H1 H2]|[H1 H2]]; (split; [lia | split; [lia | intros X; specialize (Q X); lia]]).
  Qed.

  Definition agree (M : word -> option byte) : Prop :=
    forall x : word, (bv_unsigned x < s - 4552 \/ s <= bv_unsigned x)%Z -> M x = mem0 x.
  Lemma agree_rdn : forall M (a : word) k, agree M -> (bv_unsigned a + Z.of_nat k <= s - 4552)%Z -> rdn ASEGS M a k = rdn ASEGS mem0 a k.
  Proof. hide_dj. intros M a k HF Ha. apply rdn_ext; [lia|]. intros x Hx. apply HF. lia. Qed.
  Lemma agree_globs : forall M, agree M -> rt_layout_globs M /\ mcmp_icpt_globs M /\ icptO_globs M.
  Proof.
    hide_dj. intros M HF. destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). destruct HI as (I1 & I2 & I3). destruct HC as (C1 & C2).
    unfold rt_layout_globs, mcmp_icpt_globs, icptO_globs. rewrite !(agree_rdn M) by (first [exact HF | cbn [Z.of_nat Pos.to_nat]; imm_norm; lia]).
    repeat split; assumption.
  Qed.
  Lemma agree_store_ok : forall M k (j : nat), mem_grows mem0 M -> (Z.of_nat j <= k <= 4552)%Z -> store_ok ASEGS M (Z_to_bv 64 (s - k)) j = true.
  Proof.
    hide_dj. intros M k j HGr Hk. apply (store_ok_mono _ _ mem0 M _ HGr).
    apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 4552)) _ 4552%nat); [unorm; cbn [Z.of_nat Pos.to_nat]; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia].
  Qed.
  Lemma agree_src1 : forall M, agree M -> rdn ASEGS M (Z_to_bv 64 p1) (Z.to_nat n) = Some b1.
  Proof.
    hide_dj. intros M HF. pose proof pS_facts as (Pp & Ppn & _). unhide HdjS. unfold HIGHEND in *.
    rewrite (rdn_ext ASEGS (Z.to_nat n) M mem0); [exact Hsrc1 | unorm; rewrite Z2Nat.id by lia; lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. rewrite Z2Nat.id in Hx by lia. apply HF. lia.
  Qed.
  Lemma agree_src2 : forall M, agree M -> rdn ASEGS M (Z_to_bv 64 p2) (Z.to_nat n) = Some b2.
  Proof.
    hide_dj. intros M HF. pose proof pD_facts as (Pp & Ppn & _). unhide HdjD. unfold HIGHEND in *.
    rewrite (rdn_ext ASEGS (Z.to_nat n) M mem0); [exact Hsrc2 | unorm; rewrite Z2Nat.id by lia; lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. rewrite Z2Nat.id in Hx by lia. apply HF. lia.
  Qed.
  Lemma agree_shadow : forall M, agree M ->
    ((0 < n)%Z -> forall x : word, (fS <= bv_unsigned x < lS)%Z -> M x = Some (Z_to_bv 8 0))
    /\ ((0 < n)%Z -> M (Z_to_bv 64 lS) = Some (Z_to_bv 8 kS))
    /\ ((0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS M (Z_to_bv 64 faS) 8%nat = Some w0 /\ rdn ASEGS M (Z_to_bv 64 laS) 8%nat = Some w1)
    /\ ((0 < n)%Z -> forall x : word, (fD <= bv_unsigned x < lD)%Z -> M x = Some (Z_to_bv 8 0))
    /\ ((0 < n)%Z -> M (Z_to_bv 64 lD) = Some (Z_to_bv 8 kD))
    /\ ((0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS M (Z_to_bv 64 faD) 8%nat = Some w0 /\ rdn ASEGS M (Z_to_bv 64 laD) 8%nat = Some w1).
  Proof.
    hide_dj. intros M HF. pose proof pS_facts as (_ & _ & FS). pose proof pD_facts as (_ & _ & FD). unfold SB in *.
    assert (MS : (0 <= fS mod 8 < 8)%Z) by (apply Z.mod_pos_bound; lia). assert (MLS : (0 <= lS mod 8 < 8)%Z) by (apply Z.mod_pos_bound; lia).
    assert (MD : (0 <= fD mod 8 < 8)%Z) by (apply Z.mod_pos_bound; lia). assert (MLD : (0 <= lD mod 8 < 8)%Z) by (apply Z.mod_pos_bound; lia).
    split; [|split; [|split; [|split; [|split]]]].
    - intros Hn0 x Hx. rewrite HF by lia. exact (HZS Hn0 x Hx).
    - intros Hn0. specialize (FS Hn0). rewrite HF by (unorm; lia). exact (HLS Hn0).
    - intros Hn64. specialize (FS ltac:(lia)). destruct (HWS Hn64) as (w0 & w1 & R0 & R1). exists w0, w1.
      rewrite !(agree_rdn M) by (first [exact HF | unorm; cbn [Z.of_nat Pos.to_nat]; lia]). split; assumption.
    - intros Hn0 x Hx. rewrite HF by lia. exact (HZD Hn0 x Hx).
    - intros Hn0. specialize (FD Hn0). rewrite HF by (unorm; lia). exact (HLD Hn0).
    - intros Hn64. specialize (FD ltac:(lia)). destruct (HWD Hn64) as (w0 & w1 & R0 & R1). exists w0, w1.
      rewrite !(agree_rdn M) by (first [exact HF | unorm; cbn [Z.of_nat Pos.to_nat]; lia]). split; assumption.
  Qed.

  Lemma ret_ok_65fe0 : ret_ok (0x6b918 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma callee_run : forall regs M, agree M -> mem_grows mem0 M ->
    getr regs 10 = Z_to_bv 64 p1 -> getr regs 11 = Z_to_bv 64 p2 -> getr regs 12 = Z_to_bv 64 n -> getr regs 2 = Z_to_bv 64 (s - 2240) -> getr regs 1 = (0x6b918 : word) ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x144e04 : word) M rom) (mkst regs' (0x6b918 : word) M' rom)
      /\ getr regs' 10 = Z_to_bv 64 (memcmp_val b1 b2) /\ keeps_cs regs regs'
      /\ (forall x : word, (bv_unsigned x < s - 4552 \/ s - 2240 <= bv_unsigned x)%Z -> M' x = M x) /\ mem_grows M M'.
  Proof.
    hide_dj. intros regs M AGM GRM H10 H11 H12 H2 H1.
    pose proof (agree_globs M AGM) as (GM & IM & (CM1 & _)).
    pose proof (agree_shadow M AGM) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
    assert (CI : icptI_globs M).
    { destruct HCI as (_ & C2). split; [exact CM1|]. rewrite (agree_rdn M) by (first [exact AGM | cbn [Z.of_nat Pos.to_nat]; imm_norm; lia]). exact C2. }
    destruct (wrap_memcmp_pk M rom (Z_to_bv 64 (s - 2240)) (0x6b918 : word) p1 p2 n (s - 2240) b1 b2 kS fS lS faS laS kD fD lD faD laD
                ltac:(unorm; reflexivity) HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def HfaD_def HlaD_def Hn ltac:(unhide HappS; exact HappS) ltac:(unhide HappD; exact HappD)
                ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unhide HdjS; intros X; destruct (HdjS X); lia) ltac:(unhide HdjD; intros X; destruct (HdjD X); lia)
                ltac:(replace (s - 2240 - 2312)%Z with (s - 4552)%Z by lia; apply agree_store_ok; [exact GRM | cbn; lia])
                (agree_src1 M AGM) (agree_src2 M AGM) ret_ok_65fe0 GM IM CI Z1 Z2 ltac:(unhide HkS; exact HkS) Z3 Z4 Z5 ltac:(unhide HkD; exact HkD) Z6
                regs H10 H11 H12 H2 H1) as (r' & M' & RUN & V10 & _ & _ & KC & FRM & GRW).
    exists r', M'. split; [|split; [exact V10 | split; [exact KC | split; [|exact GRW]]]].
    - stepn Fx_144dc0 Dx_144dc0.
      exact RUN.
    - intros x Hx. apply FRM. lia.
  Qed.

  #[local] Ltac grows := first [apply mem_grows_refl | eapply mem_grows_trans; [ | apply wbytes_grows ]; grows].
  #[local] Ltac fsok := apply agree_store_ok; [grows | cbn [Z.of_nat Pos.to_nat]; lia].

  Definition M5 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes mem0
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x15f90)).
  Definition M7 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (M5 rg) (Z_to_bv 64 (s - 48 - 8)) (word_to_le_bytes 8 (0x6c180 : word))) (Z_to_bv 64 (s - 48 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 n)).
  Lemma agree_w : forall M k v, agree M -> (8 <= k <= 4552)%Z -> agree (wbytes M (Z_to_bv 64 (s - k)) (word_to_le_bytes 8 v)).
  Proof.
    hide_dj. intros M k v HF Hk x Hx. pose proof (u64_range x).
    destruct Hx as [Hx|Hx].
    - rewrite wbytes_below; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
    - rewrite wbytes_above; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
  Qed.
  Lemma M7_agree : forall rg, agree (M7 rg).
  Proof.
    hide_dj. intros rg. unfold M7, M5. replace (s - 48 - 8)%Z with (s - 56)%Z by lia. replace (s - 48 - 16)%Z with (s - 64)%Z by lia.
    repeat (apply agree_w; [|lia]). intros x _. reflexivity.
  Qed.
  Lemma M7_grows : forall rg, mem_grows mem0 (M7 rg).  Proof. hide_dj. intros rg. unfold M7, M5. grows. Qed.
  #[local] Ltac peel :=
    rewrite rdn_wbytes_out;
      [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia
        | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ].
  #[local] Ltac slot := repeat peel; apply rdn_wbytes_hit8; unorm; lia.
  Lemma M7_slots : forall rg,
    rdn ASEGS (M7 rg) (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra) /\
    rdn ASEGS (M7 rg) (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 (getr rg 8)) /\
    rdn ASEGS (M7 rg) (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 (getr rg 9)) /\
    rdn ASEGS (M7 rg) (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 (getr rg 18)).
  Proof.
    hide_dj. intros rg. unfold M7, M5. replace (s - 48 - 8)%Z with (s - 56)%Z by lia. replace (s - 48 - 16)%Z with (s - 64)%Z by lia.
    repeat split; slot.
  Qed.
  Lemma ret_ok_66914 : ret_ok (0x6c16c : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma ret_ok_66928 : ret_ok (0x6c180 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma ret_ok_6694c : ret_ok (0x6c1a4 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

  Lemma c1_run : forall regs,
    getr regs 10 = Z_to_bv 64 p1 -> getr regs 11 = Z_to_bv 64 p2 -> getr regs 12 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x6c148 : word) mem0 rom) (mkst regs' (0x882c4 : word) (M5 regs) rom)
      /\ getr regs' 8 = Z_to_bv 64 n /\ getr regs' 9 = Z_to_bv 64 p2 /\ getr regs' 18 = Z_to_bv 64 p1 /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = (0x6c180 : word)
      /\ keeps_but [1; 2; 8; 9; 18]%bv regs regs'.
  Proof.
    hide_dj. intros regs H10 H11 H12 H2 H1. rewrite sp_s in H2.
    assert (AG : agree (wbytes (wbytes (wbytes (wbytes mem0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                                 (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18))))
      by (repeat (apply agree_w; [|lia]); intros x _; reflexivity).
    pose proof (agree_globs _ AG) as (_ & _ & (C1 & _)).
    unfold M5. eexists. split.
    - stepiv Fx_6c0f8 Dx_6c0f8 (Z_to_bv 64 (s - 48)) ltac:(wval).
      stepsd Fx_6c0fc Dx_6c0fc (Z_to_bv 64 (s - 8)) ra ltac:(fsok).
      stepsd Fx_6c100 Dx_6c100 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(fsok).
      stepsd Fx_6c104 Dx_6c104 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(fsok).
      stepsd Fx_6c108 Dx_6c108 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(fsok).
      stepiv Fx_6c10c Dx_6c10c (Z_to_bv 64 n) ltac:(mvval).
      stepiv Fx_6c110 Dx_6c110 (Z_to_bv 64 p2) ltac:(mvval).
      stepiv Fx_6c114 Dx_6c114 (Z_to_bv 64 p1) ltac:(mvval).
      stepn Fx_6c118 Dx_6c118.
      stepn Fx_87364 Dx_87364.
      mlb Fx_87368 Dx_87368 (0x15d698 : word) C1.
      stepfence Fx_8736c Dx_8736c.
      stepn Fx_87370 Dx_87370.
      stepn Fx_87374 Dx_87374.
      stepret Fx_87378 Dx_87378 (0x6c16c : word) ltac:(apply bv_eq; vm_compute; reflexivity). vnorm.
      stepb Fx_6c11c Dx_6c11c.
      stepn Fx_6c120 Dx_6c120.
      stepn Fx_6c124 Dx_6c124.
      stepsd Fx_6c128 Dx_6c128 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 0x15f90) ltac:(fsok).
      stepn Fx_6c12c Dx_6c12c.
      apply mst_refl.
    - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but.
  Qed.

  Theorem icpt_run : forall regs,
    getr regs 10 = Z_to_bv 64 p1 -> getr regs 11 = Z_to_bv 64 p2 -> getr regs 12 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' Mj,
      msteps ASEGS (mkst regs (0x6c148 : word) mem0 rom) (mkst regs' ra Mj rom)
      /\ getr regs' 10 = Z_to_bv 64 (memcmp_val b1 b2) /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ agree Mj /\ mem_grows mem0 Mj.
  Proof.
    hide_dj. intros regs H10 H11 H12 H2 H1.
    destruct (c1_run regs H10 H11 H12 H2 H1) as (r1 & RUN1 & Q8 & Q9 & Q18 & Q2 & Q1 & K1).
    assert (AG5 : agree (M5 regs)) by (unfold M5; repeat (apply agree_w; [|lia]); intros x _; reflexivity).
    assert (GR5 : mem_grows mem0 (M5 regs)) by (unfold M5; grows).
    pose proof (agree_globs _ AG5) as (_ & _ & (C1 & _)).
    destruct (tryinit_fast_run r1 (M5 regs) rom (0x6c180 : word) (s - 48) Q2 Q1 ret_ok_66928 ltac:(lia) ltac:(lia)
                ltac:(replace (s - 48 - 16)%Z with (s - 64)%Z by lia; apply agree_store_ok; [exact GR5 | cbn; lia]) C1)
      as (r2 & RUN2 & T10 & T2 & T8 & T1 & K2).
    rewrite Q8 in RUN2, T8. fold (M7 regs) in RUN2.
    assert (T9 : getr r2 9 = Z_to_bv 64 p2) by (rewrite (K2 9%bv) by (first [cbv; tauto | cbv; intuition congruence]); exact Q9).
    assert (T18 : getr r2 18 = Z_to_bv 64 p1) by (rewrite (K2 18%bv) by (first [cbv; tauto | cbv; intuition congruence]); exact Q18).
    pose proof (M7_agree regs) as AG7. pose proof (M7_grows regs) as GR7.
    pose proof (agree_globs _ AG7) as (G7 & I7 & (_ & C2)).
    pose proof (agree_shadow _ AG7) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).

    assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x6c180 : word) (M7 regs) rom) (mkst r3 (0x6b7f8 : word) (M7 regs) rom)
              /\ getr r3 11 = Z_to_bv 64 0x144e04 /\ getr r3 12 = Z_to_bv 64 p1 /\ getr r3 13 = Z_to_bv 64 p2 /\ getr r3 14 = Z_to_bv 64 n
              /\ getr r3 2 = Z_to_bv 64 (s - 48) /\ getr r3 1 = (0x6c1a4 : word) /\ keeps_but [1; 2; 8; 9; 18]%bv r2 r3).
    { eexists. split.
      - stepn Fx_6c130 Dx_6c130.
        mld Fx_6c134 Dx_6c134 (0x154f90 : word) C2.
        stepb_ft Fx_6c138 Dx_6c138 ltac:(cond).
        stepiv Fx_6c13c Dx_6c13c (Z_to_bv 64 (s - 40)) ltac:(wval).
        stepn Fx_6c140 Dx_6c140.
        stepiv Fx_6c144 Dx_6c144 (Z_to_bv 64 p1) ltac:(mvval).
        stepiv Fx_6c148 Dx_6c148 (Z_to_bv 64 p2) ltac:(mvval).
        stepiv Fx_6c14c Dx_6c14c (Z_to_bv 64 n) ltac:(mvval).
        stepn Fx_6c150 Dx_6c150.
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S3 as (r3 & RUN3 & U11 & U12 & U13 & U14 & U2 & U1 & K3).
    pose proof pS_facts as (PSp & PSn & _). pose proof pD_facts as (PDp & PDn & _). unfold HIGHEND in *.
    pose proof (mic_run_pk (M7 regs) rom (Z_to_bv 64 (s - 48)) (0x6c1a4 : word) p1 p2 n (s - 48) (memcmp_val b1 b2) kS fS lS faS laS kD fD lD faD laD
                ltac:(unorm; reflexivity) HfS_def HlS_def HfaS_def HlaS_def HfD_def HlD_def HfaD_def HlaD_def Hn ltac:(unhide HappS; exact HappS) ltac:(unhide HappD; exact HappD)
                ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(replace (s - 48 - 4504)%Z with (s - 4552)%Z by lia; apply agree_store_ok; [exact GR7 | cbn; lia])
                ret_ok_6694c G7 I7 Z1 Z2 ltac:(unhide HkS; exact HkS) Z3 Z4 Z5 ltac:(unhide HkD; exact HkD) Z6) as MIC.
    match type of MIC with ?CALT -> _ => assert (CAL : CALT) end.
    {
      intros rg M AGM GRM A10 A11 A12 A2 A1.
      assert (AGM0 : agree M).
      { intros x Hx. rewrite AGM by lia. apply AG7. exact Hx. }
      replace (s - 48 - 2192)%Z with (s - 2240)%Z in A2 by lia.
      destruct (callee_run rg M AGM0 (mem_grows_trans _ _ _ GR7 GRM) A10 A11 A12 A2 A1) as (rg' & M' & RUN & V10 & KC & FRM & GRW).
      exists rg', M'. split; [exact RUN|]. split; [exact V10|]. split; [exact KC|]. split; [|exact GRW].
      intros x Hx. apply FRM. lia. }
    destruct (MIC CAL r3 U11 U12 U13 U14 U2 U1) as (r4 & M4 & RUN4 & W10 & W2 & W1 & K4 & AG4 & GR4).
    pose proof (M7_slots regs) as (R1 & R2 & R3 & R4).
    assert (SL : forall k, (8 <= k <= 32)%Z -> rdn ASEGS M4 (Z_to_bv 64 (s - k)) 8%nat = rdn ASEGS (M7 regs) (Z_to_bv 64 (s - k)) 8%nat).
    { intros k Hk. apply rdn_ext; [unorm; cbn [Z.of_nat Pos.to_nat]; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. apply AG4. lia. }
    rewrite <- (SL 8%Z) in R1 by lia. rewrite <- (SL 16%Z) in R2 by lia. rewrite <- (SL 24%Z) in R3 by lia. rewrite <- (SL 32%Z) in R4 by lia.
    #[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
    eexists. exists M4. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      stepld Fx_6c154 Dx_6c154 ra ltac:(maddr (s - 8)%Z; exact R1).
      stepld Fx_6c158 Dx_6c158 (getr regs 8) ltac:(maddr (s - 16)%Z; exact R2).
      stepld Fx_6c15c Dx_6c15c (getr regs 9) ltac:(maddr (s - 24)%Z; exact R3).
      stepld Fx_6c160 Dx_6c160 (getr regs 18) ltac:(maddr (s - 32)%Z; exact R4).
      stepiv Fx_6c164 Dx_6c164 (Z_to_bv 64 s) ltac:(wval).
      stepret Fx_6c168 Dx_6c168 ra ltac:(rwH; reflexivity).
      apply mst_refl.
    - split; [gres; exact W10|]. split; [gres; symmetry; apply sp_s|]. split; [gres; reflexivity|]. split; [|split].
      + intros r Hr. destruct (decide (r = 1%bv)) as [->|N1]; [gres; symmetry; exact H1|].
        destruct (decide (r = 2%bv)) as [->|N2]; [gres; rewrite H2; symmetry; apply sp_s|].
        destruct (decide (r = 8%bv)) as [->|N8]; [gres; reflexivity|]. destruct (decide (r = 9%bv)) as [->|N9]; [gres; reflexivity|].
        destruct (decide (r = 18%bv)) as [->|N18]; [gres; reflexivity|].
        assert (NL : ~ In r [1; 2; 8; 9; 18]%bv) by (cbv; intuition congruence).
        rewrite !getr_other by (intros X; subst r; first [exact (N1 eq_refl) | exact (N2 eq_refl) | exact (N8 eq_refl) | exact (N9 eq_refl) | exact (N18 eq_refl)]).
        rewrite (K4 r Hr). rewrite (K3 r Hr NL). rewrite (K2 r Hr ltac:(cbv; intuition congruence)). exact (K1 r Hr NL).
      + intros x Hx. rewrite AG4 by lia. apply AG7. exact Hx.
      + eapply mem_grows_trans; [exact GR7 | exact GR4].
  Qed.

  Corollary wrap_run : forall regs,
    getr regs 10 = Z_to_bv 64 p1 -> getr regs 11 = Z_to_bv 64 p2 -> getr regs 12 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' Mj,
      msteps ASEGS (mkst regs (0x6a564 : word) mem0 rom) (mkst regs' ra Mj rom)
      /\ getr regs' 10 = Z_to_bv 64 (memcmp_val b1 b2) /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ agree Mj /\ mem_grows mem0 Mj.
  Proof.
    hide_dj. intros regs H10 H11 H12 H2 H1.
    destruct (icpt_run regs H10 H11 H12 H2 H1) as (r' & M' & RUN & REST).
    exists r', M'. split; [|exact REST].
    eapply msteps_trans; [|exact RUN].
    stepn Fx_6a514 Dx_6a514.
    apply mst_refl.
  Qed.
End ICPT.

Theorem wrap_bcmp_pk : forall (mem0 rom : word -> option byte) (sp ra : word) (p1 p2 n s : Z) (b1 b2 : list byte) (kS fS lS faS laS kD fD lD faD laD : Z),
  bv_unsigned sp = s ->
  fS = (SB + p1 / 8)%Z -> lS = (SB + (p1 + n - 1) / 8)%Z -> faS = (fS - fS mod 8)%Z -> laS = (lS - lS mod 8)%Z ->
  fD = (SB + p2 / 8)%Z -> lD = (SB + (p2 + n - 1) / 8)%Z -> faD = (fD - fD mod 8)%Z -> laD = (lD - lD mod 8)%Z ->
  (0 <= n <= 2 ^ 40)%Z -> in_app8 p1 n -> in_app8 p2 n ->
  ((0x1000000 <= s - 4552)%Z /\ (s < 2 ^ 64)%Z) -> (lS + 8 <= s - 4552)%Z -> (lD + 8 <= s - 4552)%Z ->
  (0 < n -> p1 + n <= s - 4552 \/ s <= p1)%Z -> (0 < n -> p2 + n <= s - 4552 \/ s <= p2)%Z ->
  store_ok ASEGS mem0 (Z_to_bv 64 (s - 4552)) 4552%nat = true ->
  rdn ASEGS mem0 (Z_to_bv 64 p1) (Z.to_nat n) = Some b1 -> rdn ASEGS mem0 (Z_to_bv 64 p2) (Z.to_nat n) = Some b2 ->
  ret_ok ra -> rt_layout_globs mem0 -> mcmp_icpt_globs mem0 -> icptO_globs mem0 -> icptI_globs mem0 ->
  ((0 < n)%Z -> forall x : word, (fS <= bv_unsigned x < lS)%Z -> mem0 x = Some (Z_to_bv 8 0)) ->
  ((0 < n)%Z -> mem0 (Z_to_bv 64 lS) = Some (Z_to_bv 8 kS)) -> (kS = 0%Z \/ ((p1 + n - 1) mod 8 < kS <= 7)%Z) ->
  ((0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 faS) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 laS) 8%nat = Some w1) ->
  ((0 < n)%Z -> forall x : word, (fD <= bv_unsigned x < lD)%Z -> mem0 x = Some (Z_to_bv 8 0)) ->
  ((0 < n)%Z -> mem0 (Z_to_bv 64 lD) = Some (Z_to_bv 8 kD)) -> (kD = 0%Z \/ ((p2 + n - 1) mod 8 < kD <= 7)%Z) ->
  ((0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 faD) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 laD) 8%nat = Some w1) ->
  forall regs,
    getr regs 10 = Z_to_bv 64 p1 -> getr regs 11 = Z_to_bv 64 p2 -> getr regs 12 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' Mj,
      msteps ASEGS (mkst regs (0x6a564 : word) mem0 rom) (mkst regs' ra Mj rom)
      /\ getr regs' 10 = Z_to_bv 64 (memcmp_val b1 b2) /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ (forall x : word, (bv_unsigned x < s - 4552 \/ s <= bv_unsigned x)%Z -> Mj x = mem0 x) /\ mem_grows mem0 Mj.
Proof.
  intros mem0 rom sp ra p1 p2 n s b1 b2 kS fS lS faS laS kD fD lD faD laD A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A24b A25 A26 A27 A28 A29 A30 A31 A32 regs.
  exact (wrap_run mem0 rom sp ra p1 p2 n s b1 b2 kS fS lS faS laS kD fD lD faD laD A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A24b A25 A26 A27 A28 A29 A30 A31 A32 regs).
Qed.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
