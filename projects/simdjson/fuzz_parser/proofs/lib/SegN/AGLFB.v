(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec FP Image RunConst.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import AsanEmbed AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHMB AGLRB AGLC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module AGLFB.
Section F.
Context {rc : runConstT}.
Variable AI : AMallocIface.
Notation CI := (aci AI).

(* [comment removed for export] *)
Definition keep_cls (LB : list ablock) (SP x : Z) : Prop :=
  (SP <= x < 2^47) \/ SP.sh_above SP x \/ AHMB.hmA AI LB x.

Lemma sh_of_shad : forall a, SP.sh_of a = shad a.
Proof. intros a. unfold SP.sh_of, shad, ASHOFF. lia. Qed.

(* [comment removed for export] *)
Lemma shad_band : forall a, a < 2^47 -> shad a < 0x10007fff8000.
Proof.
  intros a Ha. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  assert (a / 8 < 2^44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma shad_band_lo : forall a, 0 <= a -> 0x7fff8000 <= shad a.
Proof.
  intros a Ha. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  assert (0 <= a / 8) by (apply Z.div_pos; lia). lia.
Qed.
Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof.
  intros a b H. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  assert (a / 8 <= b / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
(* [comment removed for export] *)
Lemma shad_below : forall F y, F mod 8 = 0 -> y < F -> shad y < shad F.
Proof.
  intros F y HF Hy. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  assert (y / 8 < F / 8) by (apply Z.div_lt_upper_bound; [lia|]; Z.div_mod_to_equations; lia). lia.
Qed.
Lemma shad_above : forall F n y, F mod 8 = 0 -> n mod 8 = 0 -> F + n <= y -> shad F + n / 8 <= shad y.
Proof.
  intros F n y HF Hn Hy. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  assert (F / 8 + n / 8 <= y / 8).
  { assert (E : F / 8 + n / 8 = (F + n) / 8) by (clear - HF Hn; Z.div_mod_to_equations; lia).
    rewrite E. apply Z.div_le_mono; lia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma hmA_below : forall L R st LB m x, AHEAP AI L R st LB m -> AHMB.hmA AI LB x -> x < ATOP.
Proof.
  intros L R st LB m x AH Hx. pose proof ATOP_range as AT. unfold ATOP_MIN, ATOP_MAX in AT.
  destruct Hx as [Hc|(y & (b & Hb & Hy) & ->)].
  - destruct Hc as [H|[(iv & Hiv & Hin)|[(b & Hb & Hin)|(a' & Ha' & ->)]]].
    + lia.
    + pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. lia.
    + pose proof (AI_block_bounds AI L R st LB m b AH Hb). lia.
    + assert (a' < 2^47).
      { destruct Ha' as [H|[(iv & Hiv & Hin)|(c & A & n & Hin & H)]]; [lia | |].
        - pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. lia.
        - pose proof (AI_block_bounds AI L R st LB m _ AH Hin) as (B0 & B1 & B2). cbn [ab_addr ab_size] in *. lia. }
      pose proof (shad_band a' ltac:(lia)). lia.
  - pose proof (AI_block_bounds AI L R st LB m b AH Hb). pose proof (shad_band y ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma hmA_cases : forall LB sp x, AHMB.hmA AI LB x -> aclient_addr CI LB sp x \/ (exists y, in_block LB y /\ x = shad y).
Proof.
  intros LB sp x [[H|H]|H].
  - lia.
  - left. right. exact H.
  - right. exact H.
Qed.

(* [comment removed for export] *)
Lemma keep_rt : forall LB sp SP m m' x, AGLRB.rt_pres AI LB sp m m' -> sp <= SP -> ATOP <= SP -> 0 <= x < 2^64 ->
  keep_cls LB SP x -> m' (wa x) = m (wa x).
Proof.
  intros LB sp SP m m' x (HP & HB) Hs HA Hx [H|[(a & Ha & ->)|H]].
  - apply (HP x Hx). left. lia.
  - apply (HP _ Hx). right. right. right. exists a. split; [left; lia | apply sh_of_shad].
  - destruct (hmA_cases LB sp x H) as [Hc|(y & Hy & ->)].
    + apply (HP x Hx Hc).
    + apply HB. exact Hy.
Qed.

(* [comment removed for export] *)
Lemma fresh_out : forall L R st LB m cls F n sp SP x,
  AHEAP AI L R st (mkABlock (ABFake cls) F n :: LB) m ->
  (forall a, aclient_addr CI LB sp a -> a < shad F \/ shad F + n / 8 <= a) ->
  F mod 8 = 0 -> n mod 8 = 0 -> 0 < n -> ablk F (F + n) -> F + n <= ATOP -> ATOP <= SP ->
  keep_cls LB SP x -> ~ (F <= x < F + n) /\ ~ (shad F <= x < shad F + n / 8).
Proof.
  intros L R st LB m cls F n sp SP x AH B5 HF8 Hn8 Hn HB HT HS Hx. pose proof ATOP_range as AT. unfold ATOP_MIN, ATOP_MAX in AT.
  assert (HFB : (AIMG_HI <= F /\ F + n <= KLS) \/ (0x10007fff8000 <= F /\ F + n <= ATOP)) by exact HB.
  assert (SHF : shad F + n / 8 <= shad (F + n)).
  { unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    assert (E : F / 8 + n / 8 = (F + n) / 8) by (clear - HF8 Hn8; Z.div_mod_to_equations; lia). lia. }
  assert (SHT : shad (F + n) < 0x10007fff8000) by (apply shad_band; lia).
  assert (SH0 : 0x7fff8000 <= shad F) by (apply shad_band_lo; unfold AIMG_HI, KLS in *; lia).
  destruct Hx as [H|[(a & Ha & ->)|H]].
  - split; lia.
  - rewrite sh_of_shad. pose proof (shad_band a ltac:(lia)). pose proof (shad_band_lo a ltac:(lia)).
    pose proof (shad_mono (F + n) a ltac:(lia)). unfold AIMG_HI, KLS in *. split; lia.
  - split.
    + intros Hin. destruct H as [Hc|(y & (b & Hb & Hy) & ->)].
      * destruct Hc as [H|[(iv & Hiv & Hi)|[(b & Hb & Hi)|(a' & Ha' & ->)]]].
        -- lia.
        -- pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI, KLS in *. lia.
        -- assert (ND : ~ In (mkABlock (ABFake cls) F n) LB).
           { pose proof (AI_blocks_nodup AI L R st _ m AH) as N. inversion N; assumption. }
           assert (NE : mkABlock (ABFake cls) F n <> b) by (intros <-; exact (ND Hb)).
           destruct (AI_blocks_disjoint AI L R st _ m _ _ AH (or_introl eq_refl) (or_intror Hb) NE) as [D|D];
             cbn [ab_addr ab_size] in D; lia.
        -- assert (a' < 2^47 /\ 0 <= a').
           { destruct Ha' as [H|[(iv & Hiv & Hi)|(c & A & k & Hi & H)]]; [lia | |].
             - pose proof (AI_aci_img AI iv Hiv). pose proof (AI_aci_lo AI iv Hiv). unfold AIMG_HI in *. lia.
             - pose proof (AI_block_bounds AI L R st _ m _ AH (or_intror Hi)) as (B0 & B1 & B2). cbn [ab_addr ab_size] in *.
               unfold AIMG_HI in *. lia. }
           pose proof (shad_band a' ltac:(lia)). pose proof (shad_band_lo a' ltac:(lia)). unfold AIMG_HI, KLS in *. lia.
      * pose proof (AI_block_bounds AI L R st _ m _ AH (or_intror Hb)) as (B0 & B1 & B2). unfold AIMG_HI in B0.
        pose proof (shad_band y ltac:(lia)). pose proof (shad_band_lo y ltac:(lia)). unfold AIMG_HI, KLS in *. lia.
    + intros Hin. destruct (hmA_cases LB sp x H) as [Hc|(y & (b & Hb & Hy) & ->)].
      * destruct (B5 x Hc); lia.
      * assert (ND : ~ In (mkABlock (ABFake cls) F n) LB).
        { pose proof (AI_blocks_nodup AI L R st _ m AH) as N. inversion N; assumption. }
        assert (NE : mkABlock (ABFake cls) F n <> b) by (intros <-; exact (ND Hb)).
        destruct (AI_blocks_disjoint AI L R st _ m _ _ AH (or_introl eq_refl) (or_intror Hb) NE) as [D|D];
          cbn [ab_addr ab_size] in D.
        -- pose proof (shad_above F n y HF8 Hn8 ltac:(lia)). lia.
        -- pose proof (shad_below F y HF8 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma stack_out : forall L R st LB m SP lo hi x, AHEAP AI L R st LB m -> ATOP <= lo -> hi <= SP ->
  keep_cls LB SP x -> ~ (lo <= x < hi).
Proof.
  intros L R st LB m SP lo hi x AH Hlo Hhi [H|[(a & Ha & ->)|H]].
  - lia.
  - rewrite sh_of_shad. pose proof (shad_band a ltac:(lia)). pose proof ATOP_range as AT. unfold ATOP_MIN in AT. lia.
  - pose proof (hmA_below L R st LB m x AH H). lia.
Qed.

(* [comment removed for export] *)
Lemma hmA_cons : forall b LB x, AHMB.hmA AI LB x -> AHMB.hmA AI (b :: LB) x.
Proof.
  intros b LB x [[H|[H|[(b' & Hb & Hin)|(a' & Ha' & ->)]]]|(y & (b' & Hb & Hin) & ->)].
  - left. left. exact H.
  - left. right. left. exact H.
  - left. right. right. left. exists b'. split; [right; exact Hb | exact Hin].
  - left. right. right. right. exists a'. split; [|reflexivity].
    destruct Ha' as [H|[H|(c & A & n & Hin & H)]]; [left; exact H | right; left; exact H | right; right; exists c, A, n; split; [right; exact Hin | exact H]].
  - right. exists y. split; [exists b'; split; [right; exact Hb | exact Hin] | reflexivity].
Qed.
Lemma keep_cls_cons : forall b LB SP x, keep_cls LB SP x -> keep_cls (b :: LB) SP x.
Proof. intros b LB SP x [H|[H|H]]; [left; exact H | right; left; exact H | right; right; exact (hmA_cons b LB x H)]. Qed.

(* [comment removed for export] *)
Lemma flag_out : forall L R st LB m fl SP x, AHEAP AI L R st LB m ->
  ablk fl (fl + 1) -> fl + 1 <= ATOP -> (forall b, In b LB -> fl + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fl) ->
  ~ in_ranges CI fl -> ATOP <= SP -> keep_cls LB SP x -> x <> fl.
Proof.
  intros L R st LB m fl SP x AH Hb Ht Hbl Hci HS Hx ->. pose proof ATOP_range as AT. unfold ATOP_MIN, ATOP_MAX in AT.
  assert (HFB : (AIMG_HI <= fl /\ fl + 1 <= KLS) \/ (0x10007fff8000 <= fl /\ fl + 1 <= ATOP)) by exact Hb.
  destruct Hx as [H|[(a & Ha & E)|H]].
  - lia.
  - rewrite sh_of_shad in E. pose proof (shad_band a ltac:(lia)). pose proof (shad_band_lo a ltac:(lia)). unfold AIMG_HI, KLS in *. lia.
  - destruct H as [Hc|(y & (b & Hb' & Hin) & E)].
    + destruct Hc as [H|[H|[(b & Hb' & Hin)|(a' & Ha' & E)]]].
      * lia.
      * exact (Hci H).
      * destruct (Hbl b Hb'); lia.
      * assert (a' < 2^47 /\ 0 <= a').
        { destruct Ha' as [H|[(iv & Hiv & Hi)|(c & A & k & Hi & H)]]; [lia | |].
          - pose proof (AI_aci_img AI iv Hiv). pose proof (AI_aci_lo AI iv Hiv). unfold AIMG_HI in *. lia.
          - pose proof (AI_block_bounds AI L R st LB m _ AH Hi) as (B0 & B1 & B2). cbn [ab_addr ab_size] in *. unfold AIMG_HI in *. lia. }
        pose proof (shad_band a' ltac:(lia)). pose proof (shad_band_lo a' ltac:(lia)). unfold AIMG_HI, KLS in *. lia.
    + pose proof (AI_block_bounds AI L R st LB m b AH Hb') as (B0 & B1 & B2). unfold AIMG_HI in B0.
      pose proof (shad_band y ltac:(lia)). pose proof (shad_band_lo y ltac:(lia)). unfold AIMG_HI, KLS in *. lia.
Qed.

(* [comment removed for export] *)
Lemma fp_mix : forall E0 E (W0 W : list (expr * Z * expr)) G (P : ExecF.footprint),
  SP.gagree G E0 E -> eb E0 = eb E ->
  (forall w, In w W -> (existsb (AGC.awin_eqb w) W0 && AGC.awin_cl G w)%bool = true \/
                       (forall b j, fst (SX.awin_den E w) <= b -> b + Z.of_nat j <= snd (SX.awin_den E w) -> SX.fp_of (Some W0) E0 b j \/ P b j)) ->
  forall b j, SX.fp_of (Some W) E b j -> SX.fp_of (Some W0) E0 b j \/ P b j.
Proof.
  intros E0 E W0 W G P Hg Hb H b j (w & Hw & H1 & H2). destruct (H w Hw) as [Hc|Hc].
  - left. apply andb_prop in Hc as [Hex Hcl]. apply existsb_exists in Hex as (w0 & Hw0 & Heq).
    assert (Ew : w = w0).
    { destruct w as [[b' o] n], w0 as [[b'' o'] n']. cbn [AGC.awin_eqb] in Heq.
      apply andb_prop in Heq as [Heq Hn]. apply andb_prop in Heq as [Hb' Ho].
      apply expr_eqb_eq in Hb'. apply Z.eqb_eq in Ho. apply expr_eqb_eq in Hn. subst. reflexivity. }
    subst w0. exists w. split; [exact Hw0|]. rewrite <- (AGC.awin_den_gagree G E0 E w Hg Hb Hcl). lia.
  - exact (Hc b j H1 H2).
Qed.

(* [comment removed for export] *)
Definition fresh_wins (G : nat) (W0 W : list (expr * Z * expr)) : list (expr * Z * expr) :=
  List.filter (fun w => negb (existsb (AGC.awin_eqb w) W0 && AGC.awin_cl G w)%bool) W.
Lemma fp_mix3 : forall E0 E (W0 W : list (expr * Z * expr)) G (P : ExecF.footprint),
  SP.gagree G E0 E -> eb E0 = eb E ->
  (forall w, In w (fresh_wins G W0 W) ->
     forall b j, fst (SX.awin_den E w) <= b -> b + Z.of_nat j <= snd (SX.awin_den E w) -> SX.fp_of (Some W0) E0 b j \/ P b j) ->
  forall b j, SX.fp_of (Some W) E b j -> SX.fp_of (Some W0) E0 b j \/ P b j.
Proof.
  intros E0 E W0 W G P Hg Hb H. apply (fp_mix E0 E W0 W G P Hg Hb). intros w Hw.
  destruct (existsb (AGC.awin_eqb w) W0 && AGC.awin_cl G w)%bool eqn:C; [left; reflexivity | right].
  apply H. unfold fresh_wins. apply filter_In. split; [exact Hw | rewrite C; reflexivity].
Qed.

Lemma fpu_mix : forall (hmF : ExecF.footprint) E0 E W0 W,
  (forall b j, SX.fp_of (Some W) E b j -> SX.fp_of (Some W0) E0 b j \/ hmF b j) ->
  forall b j, SP.fpu hmF (Some W) E b j -> SP.fpu hmF (Some W0) E0 b j.
Proof. intros hmF E0 E W0 W H b j [Hb|Hb]; [exact (H b j Hb) | right; exact Hb]. Qed.

End F.
End AGLFB.
