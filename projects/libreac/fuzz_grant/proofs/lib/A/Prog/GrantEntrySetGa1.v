(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySetGa1), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* The set loop of fuzz_grant's entry function LLVMFuzzerTestOneInput on the ASan build:
   the piece GA1 → G78 | the call of reac_headamp_tx_effective (the slots 0x80bb8 ..
   0x80c20, fuzz/fuzz_grant.c:201-224).

   At 0x80bb8 the turn's cell had one byte left: reac_headamp_tx_set was called with the
   channel in s2 and parameter and value 0 (gcell_cases, GrantEntrySetDefs.v:126), and a0
   holds its answer. The code keeps the answer in s9, stores 0 in slot 120 (the bytes
   left), puts the cursor past the cell in s5, and computes the answer the harness
   expects: -1 when the channel is 48 or more, else (0 < 3 && 0 < 2) - 1 = 0. The check
   `bne s9, a0` at 0x80c0c goes to the error path (0x81a0c: __asan_handle_no_return, then
   abort) when the two differ; `bnez s9` at 0x80c10 then goes to 0x80c78 (refused) or to
   the call of reac_headamp_tx_effective at 0x80c20 (accepted).

   The proof splits on the channel first. With the parameter and the value 0, the set is
   accepted exactly when the channel is below 48 (gacc, with legalb 0 0 = true,
   HeadampModel.v:58). Each side seats a symbolic state whose s9 (the answer) is the
   literal the model gives and whose channel atom carries its range, so the engine
   decides all three branches (0x80bc4, 0x80c0c, 0x80c10) itself: in neither side is the
   error branch at 0x80c0c taken. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1g YC1h YC4b YC85 YC88 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryDefs GrantEntrySetDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c SegSetModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The state at 0x80bb8: s9's source a0 pinned to the set's answer z, the channel atom
   (s2) in [lo, hi], the stack slots as R_stk has them. *)
Definition F_ga1 (lo hi : Z) : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF lo hi 0)] [] [].
Definition ss_ga1a (lo hi : Z) : sstate := mkSS 0x508 sr_atoms [R_stk] None (F_ga1 lo hi).
Definition ss_ga1 (z lo hi : Z) : sstate :=
  mkSS 0x508 (sr_set sr_atoms 10%bv (SLit z)) [R_stk] None (F_ga1 lo hi).

(* The value of register r after a run, as the atom n of the entry register rn. *)
Ltac ga1_rr HS HE regs r n rn R :=
  prreg HS r R; rewrite HE, Eimg_low in R by (unfold A_TEXT; lia);
  rewrite (ew_Ereg_nat regs _ n rn eq_refl) in R.

Ltac ga1_ms HS :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?m) => m
  | st_ok _ _ _ (restrict _ ?m) => m
  end.

(* The first region of the state a run left (R_stk, slot 120 written). *)
Ltac ga1_reg0 HS FR0 :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth_error (ss_mem ssx) 0) in
      lazymatch r0 with Some ?rr =>
        pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 0 rr HS ltac:(vm_compute; reflexivity)) as FR0 end
  | st_ok _ ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth_error (ss_mem ssx) 0) in
      lazymatch r0 with Some ?rr =>
        pose proof (st_ok_region_nth Ex ssx (restrict Hh msx) 0 rr HS ltac:(vm_compute; reflexivity)) as FR0 end
  end; cbn [ms_mem restrict] in FR0.

(* The run may write slot 120 of the machine frame (R_stk's window). *)
Ltac ga1_awr cx E9 :=
  unfold ss_ga1; cbn [ss_mem];
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
  [ reflexivity
  | rewrite E9; unfold w64; rewrite unsigned_lit_small by lia; lia
  | cbn [YP09.r_wlo R_stk]; unfold GE_STK; lia
  | cbn [YP09.r_whi R_stk]; lia
  | apply awr_ok_nil ].

Section ga1.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
(* The call of reac_headamp_tx_effective at 0x80c20 after an accepted set. *)
Hypothesis CALLE2 : call_e2_stmt B MT.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* The turn's memory after a run whose only window was slot 120, which now holds v'. *)
Lemma gmem_s120 : forall cx fp t ly3 W3 ms ms' T ws st v v',
  glayout cx fp t ly3 -> c_n cx < 2 ^ 26 -> length ws = 144%nat -> length st = 144%nat ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 120 <= a < c_sp1 cx + 128) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a) ->
  gslot cx W3 ms' 120 v' -> gmem cx fp W3 ms t T ws st v -> gmem cx fp W3 ms' t T ws st v'.
Proof.
  intros cx fp t ly3 W3 ms ms' T ws st v v' HL Hn LW LS HK H120'
    (Hsv & Hsh & Hfl & Hin & Hmid & H64 & _ & HT & Hws & Hst).
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
  pose proof (proj1 alloc_ceiling_val) as AC. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
  assert (HgF8 : 0 <= gF cx fp / 8 /\ gF cx fp / 8 + 1024 < 2 ^ 44)
    by (split; [apply Z.div_pos; lia | assert (gF cx fp / 8 < 2 ^ 44 - 1024) by (apply Z.div_lt_upper_bound; lia); lia]).
  assert (RDK : forall a v0, c_sp1 cx <= a -> a + 8 <= 2 ^ 64 ->
     (a + 8 <= c_sp1 cx + 120 \/ c_sp1 cx + 128 <= a) ->
     rdword (aview SEGS (w_H W3) (ms_mem ms)) a = Some v0 -> rdword (aview SEGS (w_H W3) (ms_mem ms')) a = Some v0).
  { intros a v0 H1 H2 H3 H. rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms)) (aview SEGS (w_H W3) (ms_mem ms')) a); [exact H|].
    intros j Hj. apply HK; lia. }
  assert (GA : forall p L, (forall a, p <= a < p + Z.of_nat (length L) -> 0 <= a < c_sp1 cx + 120) ->
     garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) p L -> garr8 SEGS (mrestrict (w_H W3) (ms_mem ms')) p L).
  { intros p L HR HG. apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms) (ms_mem ms') p L); [|exact HG].
    intros a Ha. pose proof (HR a Ha). apply HK; lia. }
  destruct Hsv as [Hra Hsv]. destruct Hmid as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  unfold gmem, gsaved, gshadow, gslots_mid, gslot, gfarr, gtabb in *.
  split; [split|].
  { apply RDK; [lia | lia | lia | exact Hra]. }
  { intros j Hj. apply RDK; [lia | lia | lia | apply Hsv, Hj]. }
  split.
  { intros j Hj. rewrite GSH_tables_len in Hj. unfold GE_NSH in Hj.
    rewrite HK; [apply Hsh; rewrite GSH_tables_len; unfold GE_NSH; exact Hj | lia | lia]. }
  split.
  { rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms)) (aview SEGS (w_H W3) (ms_mem ms')) (gF cx fp + 1016)); [exact Hfl|].
    intros j Hj. apply HK; lia. }
  split.
  { apply GA; [|exact Hin]. intros a Ha. rewrite length_map in Ha. fold (c_n cx) in Ha.
    destruct (L16 ltac:(lia)) as (P1 & P2 & P3 & P4 & P5). lia. }
  split; [splits; apply RDK; first [lia | assumption]|].
  split; [apply RDK; [lia | lia | lia | exact H64]|].
  split; [exact H120'|].
  split; [intros j H1 H2 H3 H4; rewrite HK; [apply HT; assumption | lia | lia]|].
  split; apply GA; first [assumption | intros a Ha; rewrite length_map in Ha; unfold GO_WAS, GO_SET in Ha; lia].
Qed.

(* The symbolic state at 0x80bb8 holds, for an answer z of the set and a channel in
   [lo, hi]. *)
Lemma ga1_entry : forall cx fp t ly3 W3 ms3 E v120 z lo hi c,
  E = Eimg (Ereg (ms_regs ms3) (map (Z_to_bv 64) [v120; gF cx fp + GO_SET; gF cx fp + GO_WAS])) ->
  glayout cx fp t ly3 ->
  (forall a, spZ (c_regs cx) - GE_STK <= a < spZ (c_regs cx) -> apresent (w_H W3) (ms_mem ms3) a) ->
  getr (ms_regs ms3) 9 = w64 (c_sp1 cx) -> getr (ms_regs ms3) 18 = w64 c ->
  getr (ms_regs ms3) 10 = Z_to_bv 64 z ->
  0 <= lo -> lo <= c <= hi -> hi < 2 ^ 64 -> 0 <= v120 < 2 ^ 26 ->
  gslot cx W3 ms3 120 v120 -> gslots_mid cx fp W3 ms3 ->
  st_ok_pi SEGS VAL E (ss_ga1 z lo hi)
    (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + 0x508)) (ms_mem ms3) (seg_rom SEGS))).
Proof.
  intros cx fp t ly3 W3 ms3 E v120 z lo hi c HE HL HP R9 R18 R10 Hlo Hc Hhi Hv H120 Hmid.
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & _).
  pose proof (proj1 alloc_ceiling_val) as AC.
  assert (ER : forall (n0 : nat) (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr (ms_regs ms3) r)
    by (intros n0 r Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) =
      nth j (map (Z_to_bv 64) [v120; gF cx fp + GO_SET; gF cx fp + GO_WAS]) (Z_to_bv 64 0))
    by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  assert (E9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); exact R9).
  assert (E18 : ew E 18 = w64 c) by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
  assert (E32 : ew E 32 = w64 v120) by exact (EX 0%nat ltac:(lia)).
  assert (E33 : ew E 33 = w64 (gF cx fp + GO_SET)) by exact (EX 1%nat ltac:(lia)).
  assert (E34 : ew E 34 = w64 (gF cx fp + GO_WAS)) by exact (EX 2%nat ltac:(lia)).
  apply (st_ok_pi_set_reg E (ss_ga1a lo hi) _ (10%bv : bv 5) (SLit z));
    [| discriminate | cbn [ms_regs restrict mkst sv_denot]; exact R10].
  rewrite restrict_mkst_fx. unfold ss_ga1a. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    exact (R_stk_ok cx fp t ly3 W3 ms3 E v120 HL HP E9 E32 E33 E34 Hv H120 Hmid).
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - unfold F_ga1. split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E18. unfold w64. rewrite !unsigned_lit_small by lia.
    change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
    splits; first [exact I | lia].
Qed.

Lemma ge_set_ga1 : seg_ga1_stmt B MT.
Proof.
  intros POST n i HN HE2 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO (t & HC & HLEN & HM & R10 & R18 & R26).
  pose proof HC as (HMA & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H22 & H27).
  pose proof HMA as (_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4).
  pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & _).
  pose proof (proj1 alloc_ceiling_val) as AC.
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  (* One byte was left: the cell is (that byte, 0, 0) and the cursor moves past it. *)
  pose proof (gcell_cases (c_pl cx) i) as Hcc. cbv zeta in Hcc.
  destruct Hcc as [(H3 & _) | [(H2 & _) | [(H1 & Ecell & Epos) | (H0 & _)]]]; [lia | lia | | lia].
  assert (Eq0 : gq (c_pl cx) i = 0) by (unfold gq; rewrite Ecell; reflexivity).
  assert (Ev0 : gv (c_pl cx) i = 0) by (unfold gv; rewrite Ecell; reflexivity).
  (* So the set is accepted exactly when the channel is below 48 (legalb 0 0 = true). *)
  assert (Eacc : gacc (c_pl cx) i = (gc (c_pl cx) i <? 48))
    by (unfold gacc; rewrite Eq0, Ev0; change (legalb 0 0) with true; apply andb_true_r).
  assert (Hv1 : c_n cx - Z.of_nat (gpos (c_pl cx) i) = 1) by (unfold c_n; rewrite HLEN; lia).
  assert (Hv0 : c_n cx - Z.of_nat (gpos (c_pl cx) (S i)) = 0) by (unfold c_n; rewrite HLEN, Epos; lia).
  pose proof (gcell_ok (c_pl cx) i) as (Hc0 & _ & _).
  pose proof (gtables_inv (c_pl cx) i) as (_ & LW & LS & _ & _).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSP & _).
  pose proof HM as (_ & _ & _ & _ & Hmid & _ & H120 & _).
  rewrite Hv1 in H120.
  set (E := Eimg (Ereg (ms_regs ms3) (map (Z_to_bv 64) [1; gF cx fp + GO_SET; gF cx fp + GO_WAS]))).
  assert (HE : E = Eimg (Ereg (ms_regs ms3) (map (Z_to_bv 64) [1; gF cx fp + GO_SET; gF cx fp + GO_WAS])))
    by reflexivity.
  clearbody E.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E9 : ew E 9 = w64 (c_sp1 cx)) by (subst E; rewrite (ew_Eimg_Ereg_nat _ _ 9 9%bv eq_refl); exact G9).
  assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  rewrite (gmach_mkst cx ms3 _ HMA).
  destruct (Z.ltb_spec (gc (c_pl cx) i) 48) as [Hc48 | Hc48].
  - (* The channel is below 48: the set accepted (a0 = 0); slot 120 := 0, s5 := s10, and
       a0 := (0 <u 3 && 0 <u 2) - 1 = 0 = s9, so 0x80c0c falls through; s9 = 0, so 0x80c10
       falls through to the call of reac_headamp_tx_effective at 0x80c20. *)
    (* Z.ltb_spec turned Eacc into gacc = true. *)
    pose proof Eacc as HA.
    rewrite HA in R10.
    pose proof (ga1_entry cx fp t ly3 W3 ms3 E 1 0 0 47 (gc (c_pl cx) i) HE HL HSP G9 R18 R10
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H120 Hmid) as HS.
    paj_run_tok RUN HS HJ SHOK GBspan; [ga1_awr cx E9 |].
    let m := ga1_ms HS in rename m into msA.
    assert (HWIN : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 120 <= a < c_sp1 cx + 128) ->
                   aview SEGS (w_H W3) (ms_mem msA) a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha Hw.
      apply (frame_wins E _ _ _ _ (fun a => c_sp1 cx + 120 <= a < c_sp1 cx + 128) HFr); [|exact Ha | exact Hw].
      intros x (r & Hr & Hx). cbv beta. unfold ss_ga1 in Hr. cbn [ss_mem In] in Hr.
      destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val R_stk] in Hx.
      rewrite E9 in Hx. unfold w64 in Hx. rewrite unsigned_lit_small in Hx by lia. lia. }
    ga1_reg0 HS FR0.
    assert (S120 : gslot cx W3 msA 120 (c_n cx - Z.of_nat (gpos (c_pl cx) (S i)))).
    { rewrite Hv0. unfold gslot. apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msA)); [|lia].
      eapply (field_of_regionG _ _ 9%nat (c_sp1 cx) _ _ _ _ _ 120 8%N (SLit 0) 0 FR0);
      [ rewrite E9; unfold w64; apply unsigned_lit_small; lia
      | cbn [In]; repeat (first [left; reflexivity | right])
      | reflexivity | cbn; lia | cbn; lia ]. }
    pose proof (gmem_s120 cx fp t ly3 W3 ms3 msA _ _ _ _ _ HL Hn LW LS HWIN S120 HM) as HM2.
    prreg HS (1%bv : bv 5) Q1.
    ga1_rr HS HE (ms_regs ms3) (2%bv : bv 5) 2%nat (2%bv : bv 5) Q2.
    ga1_rr HS HE (ms_regs ms3) (8%bv : bv 5) 8%nat (8%bv : bv 5) Q8.
    ga1_rr HS HE (ms_regs ms3) (9%bv : bv 5) 9%nat (9%bv : bv 5) Q9.
    ga1_rr HS HE (ms_regs ms3) (3%bv : bv 5) 3%nat (3%bv : bv 5) Q3.
    ga1_rr HS HE (ms_regs ms3) (4%bv : bv 5) 4%nat (4%bv : bv 5) Q4.
    ga1_rr HS HE (ms_regs ms3) (10%bv : bv 5) 20%nat (20%bv : bv 5) Q10.
    ga1_rr HS HE (ms_regs ms3) (11%bv : bv 5) 18%nat (18%bv : bv 5) Q11.
    prreg HS (12%bv : bv 5) Q12.
    ga1_rr HS HE (ms_regs ms3) (18%bv : bv 5) 18%nat (18%bv : bv 5) Q18.
    ga1_rr HS HE (ms_regs ms3) (19%bv : bv 5) 19%nat (19%bv : bv 5) Q19.
    ga1_rr HS HE (ms_regs ms3) (20%bv : bv 5) 20%nat (20%bv : bv 5) Q20.
    ga1_rr HS HE (ms_regs ms3) (21%bv : bv 5) 26%nat (26%bv : bv 5) Q21.
    ga1_rr HS HE (ms_regs ms3) (22%bv : bv 5) 22%nat (22%bv : bv 5) Q22.
    prreg HS (23%bv : bv 5) Q23.
    prreg HS (24%bv : bv 5) Q24.
    ga1_rr HS HE (ms_regs ms3) (27%bv : bv 5) 27%nat (27%bv : bv 5) Q27.
    pmkst HS. rewrite pa_sigma_reac_headamp_tx_effective.
    refine (CALLE2 POST n i cx fp k acc ly3 S3 W3 (ms_regs msA) (ms_mem msA) _ t HE2 HB HJ HFR HMO
      Hk Hacc Hbl Ht0 Hn Hns HA Q1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [ unfold w64 in *; congruence .. | exact HM2 ].
  - (* The channel is 48 or more: the set refused (a0 = -1); a0 := -1 = s9, so 0x80c0c
       falls through; slot 120 := 0, s5 := s10; s9 = -1, so 0x80c10 goes to 0x80c78. *)
    pose proof Eacc as HA.
    rewrite HA in R10.
    pose proof (ga1_entry cx fp t ly3 W3 ms3 E 1 (-1) 48 255 (gc (c_pl cx) i) HE HL HSP G9 R18 R10
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H120 Hmid) as HS.
    paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x5c8; [ga1_awr cx E9 |].
    let m := ga1_ms HS in rename m into msA.
    assert (HWIN : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 120 <= a < c_sp1 cx + 128) ->
                   aview SEGS (w_H W3) (ms_mem msA) a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha Hw.
      apply (frame_wins E _ _ _ _ (fun a => c_sp1 cx + 120 <= a < c_sp1 cx + 128) HFr); [|exact Ha | exact Hw].
      intros x (r & Hr & Hx). cbv beta. unfold ss_ga1 in Hr. cbn [ss_mem In] in Hr.
      destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val R_stk] in Hx.
      rewrite E9 in Hx. unfold w64 in Hx. rewrite unsigned_lit_small in Hx by lia. lia. }
    ga1_reg0 HS FR0.
    assert (S120 : gslot cx W3 msA 120 (c_n cx - Z.of_nat (gpos (c_pl cx) (S i)))).
    { rewrite Hv0. unfold gslot. apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msA)); [|lia].
      eapply (field_of_regionG _ _ 9%nat (c_sp1 cx) _ _ _ _ _ 120 8%N (SLit 0) 0 FR0);
      [ rewrite E9; unfold w64; apply unsigned_lit_small; lia
      | cbn [In]; repeat (first [left; reflexivity | right])
      | reflexivity | cbn; lia | cbn; lia ]. }
    pose proof (gmem_s120 cx fp t ly3 W3 ms3 msA _ _ _ _ _ HL Hn LW LS HWIN S120 HM) as HM2.
    apply (HN cx fp k acc ly3 S3 W3 msA _ HB HJ HFR HMO).
    destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
    ga1_rr HS HE (ms_regs ms3) (2%bv : bv 5) 2%nat (2%bv : bv 5) Q2.
    ga1_rr HS HE (ms_regs ms3) (8%bv : bv 5) 8%nat (8%bv : bv 5) Q8.
    ga1_rr HS HE (ms_regs ms3) (9%bv : bv 5) 9%nat (9%bv : bv 5) Q9.
    ga1_rr HS HE (ms_regs ms3) (3%bv : bv 5) 3%nat (3%bv : bv 5) Q3.
    ga1_rr HS HE (ms_regs ms3) (4%bv : bv 5) 4%nat (4%bv : bv 5) Q4.
    ga1_rr HS HE (ms_regs ms3) (19%bv : bv 5) 19%nat (19%bv : bv 5) Q19.
    ga1_rr HS HE (ms_regs ms3) (20%bv : bv 5) 20%nat (20%bv : bv 5) Q20.
    ga1_rr HS HE (ms_regs ms3) (21%bv : bv 5) 26%nat (26%bv : bv 5) Q21.
    ga1_rr HS HE (ms_regs ms3) (22%bv : bv 5) 22%nat (22%bv : bv 5) Q22.
    ga1_rr HS HE (ms_regs ms3) (27%bv : bv 5) 27%nat (27%bv : bv 5) Q27.
    destruct (gtables_S (c_pl cx) i) as (_ & EW & ES). rewrite HA in EW, ES.
    exists t. split; [|split].
    + unfold gcore, gmach, gregs. unfold w64 in *. splits; try assumption; congruence.
    + rewrite EW, ES. exact HM2.
    + unfold w64 in *. congruence.
Qed.

End ga1.
