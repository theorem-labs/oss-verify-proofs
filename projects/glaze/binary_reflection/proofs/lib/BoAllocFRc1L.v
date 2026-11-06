(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcM1U. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcM1U.BoAllocFRc1.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation IBq := 0x10ab58 (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section POP1MEM.
  Variables (mem : word -> option byte) (S : word) (minsz j prev a sz nx glenr B sum : Z).
  Hypothesis HS : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Ha : AIMGHI <= a /\ a + 8192 <= U S - 3584.
  Hypothesis Hprev : j <> 0 -> (AIMGHI <= prev /\ prev + 8192 <= U S - 3584) /\ (prev + 8192 <= a \/ a + 8192 <= prev).
  #[local] Abbreviation M1 := (fr_pop1 mem S minsz j prev a sz nx glenr B sum).

  Definition pop1_foot (x : Z) : Prop :=
    (IBq + 888 <= x < IBq + 904) \/ (nx = 0 /\ IBq + 904 <= x < IBq + 912) \/ (IBq + 912 <= x < IBq + 920)
    \/ (a <= x < a + 8) \/ (j <> 0 /\ prev <= x < prev + 8) \/ (j = 0 /\ U S - 2280 <= x < U S - 2272)
    \/ (U S - 2264 <= x < U S - 2256)
    \/ (B - sz <= minsz /\ (U S - 2288 <= x < U S - 2280 \/ U S - 2272 <= x < U S - 2264)).

  Ltac lsideP := wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
  Ltac digP := repeat (wd_rdstep rd8_side).
  Ltac cases3 := (lazymatch goal with |- ?G => let G' := eval unfold fr_pop1 in G in change_no_check G' end); destruct (Z.eqb_spec nx 0) as [Enx | Nnx]; destruct (Z.eqb_spec j 0) as [Ej | Nj];
                 destruct (Z.ltb_spec minsz (B - sz)) as [Hcont | Hexit]; (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end);
                 try (destruct (Hprev ltac:(assumption)) as (Hp1 & Hp2)).

  (* [comment removed for export] *)
  #[local] Ltac sd_pickD tac := first [ left; solve [tac] | right; sd_pickD tac | solve [tac] ].
  #[local] Ltac sd_lsideQ Hx :=
    wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end);
    revert Hx; unorm; intros Hx;
    first [ solve [ clear Hx; lia ]
          | lazymatch goal with
            | |- (?p < ?q \/ ?r <= ?s)%Z =>
                destruct (Z.lt_ge_cases p q) as [Hq1|Hq1]; [left; exact Hq1|];
                destruct (Z.lt_ge_cases s r) as [Hq2|Hq2]; [|right; exact Hq2];
                exfalso; apply Hx; clear Hx; sd_pickD ltac:(lia)
            end ].
  Lemma fr_pop1_outside : forall x : word, ~ pop1_foot (U x) -> M1 x = mem x.
  Proof using Hprev Ha HS.
    intros x Hx. pose proof (u64_range S) as HSr. pose proof (u64_range x) as Hxr. unfold pop1_foot in Hx.
    cases3; rewrite !wbytes_outside by first [ sd_lsideQ Hx | lsideP ]; reflexivity.
  Qed.
  Lemma fr_pop1_grows : mem_grows mem M1.
  Proof using Hprev. cases3; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl. Qed.

  (* [comment removed for export] *)
  Lemma fr_pop1_def : forall x : word, (IBq + 888 <= U x < IBq + 904 \/ IBq + 912 <= U x < IBq + 920) -> M1 x <> None.
  Proof using.
    intros x Hx. pose proof (u64_range S) as HSr.
    assert (CORE : wbytes (wbytes (if (nx =? 0)%Z then wbytes (wbytes mem (Z_to_bv 64 (IBq + 896)) (LE8 (Z_to_bv 64 nx))) (Z_to_bv 64 (IBq + 904)) (LE8 (Z_to_bv 64 0))
                               else wbytes mem (Z_to_bv 64 (IBq + 896)) (LE8 (Z_to_bv 64 nx)))
                        (Z_to_bv 64 (IBq + 888)) (LE8 (Z_to_bv 64 (glenr - 1)))) (Z_to_bv 64 (IBq + 912)) (LE8 (Z_to_bv 64 (B - sz))) x <> None).
    { destruct (Z_le_dec (IBq + 912) (U x)) as [L912|L912].
      - rewrite wbytes_inside by lsideP. discriminate.
      - apply wbytes_grows. destruct (Z_lt_dec (U x) (IBq + 896)) as [L888|L888].
        + rewrite wbytes_inside by lsideP. discriminate.
        + apply wbytes_grows. destruct (Z.eqb_spec nx 0); [apply wbytes_grows|]; rewrite wbytes_inside by lsideP; discriminate. }
    (lazymatch goal with |- ?G => let G' := eval unfold fr_pop1 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    destruct (Z.eqb_spec j 0); destruct (Z.ltb_spec minsz (B - sz)); [do 3 apply wbytes_grows | do 5 apply wbytes_grows | do 3 apply wbytes_grows | do 5 apply wbytes_grows]; exact CORE.
  Qed.

  (* [comment removed for export] *)
  Lemma fr_pop1_first : rdn BSEGS M1 (Z_to_bv 64 (IBq + 896)) 8 = Some (LE8 (Z_to_bv 64 nx)).
  Proof using Hprev Ha HS. pose proof (u64_range S) as HSr. cases3; digP. Qed.
  Lemma fr_pop1_last0 : nx = 0 -> rdn BSEGS M1 (Z_to_bv 64 (IBq + 904)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Proof using Hprev Ha HS. intros E0. pose proof (u64_range S) as HSr. cases3; try lia; digP. Qed.
  Lemma fr_pop1_len : rdn BSEGS M1 (Z_to_bv 64 (IBq + 888)) 8 = Some (LE8 (Z_to_bv 64 (glenr - 1))).
  Proof using Hprev Ha HS. pose proof (u64_range S) as HSr. cases3; digP. Qed.
  Lemma fr_pop1_bytes : rdn BSEGS M1 (Z_to_bv 64 (IBq + 912)) 8 = Some (LE8 (Z_to_bv 64 (B - sz))).
  Proof using Hprev Ha HS. pose proof (u64_range S) as HSr. cases3; digP. Qed.
  Lemma fr_pop1_sum : rdn BSEGS M1 (at_ S (-2264)) 8 = Some (LE8 (Z_to_bv 64 (sum + sz))).
  Proof using Hprev HS. pose proof (u64_range S) as HSr. cases3; digP. Qed.
  Lemma fr_pop1_anext : rdn BSEGS M1 (Z_to_bv 64 a) 8 = Some (LE8 (Z_to_bv 64 0)).
  Proof using Hprev Ha HS. pose proof (u64_range S) as HSr. cases3; digP. Qed.
  Lemma fr_pop1_prev : j <> 0 -> rdn BSEGS M1 (Z_to_bv 64 prev) 8 = Some (LE8 (Z_to_bv 64 a)).
  Proof using Hprev HS. intros N0. pose proof (u64_range S) as HSr. cases3; try lia; digP. Qed.
  Lemma fr_pop1_tfirst : j = 0 -> rdn BSEGS M1 (at_ S (-2280)) 8 = Some (LE8 (Z_to_bv 64 a)).
  Proof using Hprev HS. intros E0. pose proof (u64_range S) as HSr. cases3; try lia; digP. Qed.
  Lemma fr_pop1_tsize : B - sz <= minsz -> rdn BSEGS M1 (at_ S (-2288)) 8 = Some (LE8 (Z_to_bv 64 (j + 1))).
  Proof using Hprev HS. intros E0. pose proof (u64_range S) as HSr. cases3; try lia; digP. Qed.
  Lemma fr_pop1_tlast : B - sz <= minsz -> rdn BSEGS M1 (at_ S (-2272)) 8 = Some (LE8 (Z_to_bv 64 a)).
  Proof using Hprev HS. intros E0. pose proof (u64_range S) as HSr. cases3; try lia; digP. Qed.
End POP1MEM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ptrip := (Z * Z * Z)%type.
Definition p_addr (t : ptrip) : Z := fst (fst t).
Definition p_sz (t : ptrip) : Z := snd (fst t).
Definition p_nx (t : ptrip) : Z := snd t.
Fixpoint p_tot (l : list ptrip) : Z := match l with [] => 0 | t :: r => p_sz t + p_tot r end.
Fixpoint p_lasta (l : list ptrip) (d : Z) : Z := match l with [] => d | t :: r => p_lasta r (p_addr t) end.
Fixpoint p_lastnx (l : list ptrip) (d : Z) : Z := match l with [] => d | t :: r => p_lastnx r (p_nx t) end.

(* [comment removed for export] *)
Fixpoint pops_ok (minsz cur B : Z) (l : list ptrip) : Prop :=
  match l with
  | [] => False
  | t :: r => p_addr t = cur /\ 0 <= p_sz t <= B /\ 0 <= p_nx t < 2 ^ 64 /\
      match r with
      | [] => B - p_sz t <= minsz
      | _ => minsz < B - p_sz t /\ pops_ok minsz (p_nx t) (B - p_sz t) r
      end
  end.

(* [comment removed for export] *)
Fixpoint chain_cells (m : word -> option byte) (l : list ptrip) : Prop :=
  match l with
  | [] => True
  | t :: r => rdn BSEGS m (Z_to_bv 64 (p_addr t)) 8 = Some (LE8 (Z_to_bv 64 (match r with [] => 0 | t' :: _ => p_addr t' end)))
              /\ chain_cells m r
  end.

Definition bsep (x y : Z) : Prop := x + 8192 <= y \/ y + 8192 <= x.
Fixpoint all_sep (l : list Z) : Prop := match l with [] => True | x :: r => Forall (bsep x) r /\ all_sep r end.

Definition loop_foot (S : word) (j prev : Z) (l : list ptrip) (x : Z) : Prop :=
  (IBq + 888 <= x < IBq + 904) \/ (p_lastnx l 1 = 0 /\ IBq + 904 <= x < IBq + 912) \/ (IBq + 912 <= x < IBq + 920)
  \/ (exists t, In t l /\ p_addr t <= x < p_addr t + 8) \/ (j <> 0 /\ prev <= x < prev + 8) \/ (j = 0 /\ U S - 2280 <= x < U S - 2272)
  \/ (U S - 2288 <= x < U S - 2280) \/ (U S - 2272 <= x < U S - 2256).

Definition pop_post (S : word) (j prev glenr B sum : Z) (l : list ptrip) (mem mem' : word -> option byte) : Prop :=
  (forall x : word, ~ loop_foot S j prev l (U x) -> mem' x = mem x)
  /\ mem_grows mem mem'
  /\ rdn BSEGS mem' (Z_to_bv 64 (IBq + 896)) 8 = Some (LE8 (Z_to_bv 64 (p_lastnx l 1)))
  /\ (p_lastnx l 1 = 0 -> rdn BSEGS mem' (Z_to_bv 64 (IBq + 904)) 8 = Some (LE8 (Z_to_bv 64 0)))
  /\ rdn BSEGS mem' (Z_to_bv 64 (IBq + 888)) 8 = Some (LE8 (Z_to_bv 64 (glenr - Z.of_nat (length l))))
  /\ rdn BSEGS mem' (Z_to_bv 64 (IBq + 912)) 8 = Some (LE8 (Z_to_bv 64 (B - p_tot l)))
  /\ rdn BSEGS mem' (at_ S (-2288)) 8 = Some (LE8 (Z_to_bv 64 (j + Z.of_nat (length l))))
  /\ rdn BSEGS mem' (at_ S (-2272)) 8 = Some (LE8 (Z_to_bv 64 (p_lasta l 0)))
  /\ rdn BSEGS mem' (at_ S (-2264)) 8 = Some (LE8 (Z_to_bv 64 (sum + p_tot l)))
  /\ (j = 0 -> rdn BSEGS mem' (at_ S (-2280)) 8 = Some (LE8 (Z_to_bv 64 (match l with [] => 0 | t :: _ => p_addr t end))))
  /\ (j <> 0 -> rdn BSEGS mem' (Z_to_bv 64 prev) 8 = Some (LE8 (Z_to_bv 64 (match l with [] => 0 | t :: _ => p_addr t end))))
  /\ chain_cells mem' l
  /\ (forall x : word, (IBq + 888 <= U x < IBq + 904 \/ IBq + 912 <= U x < IBq + 920) -> mem' x <> None).

Section POPLOOP.
  Context {fx : FPState}.
  Variables (rom : word -> option byte) (S : word) (minsz : Z).
  Hypothesis HS : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Hmin : 0 <= minsz < 2 ^ 64.

  Definition geo (x : Z) : Prop := AIMGHI <= x /\ x + 8192 <= U S - 3584.

  (* [comment removed for export] *)
  Lemma rd8_frame : forall (FOOT : Z -> Prop) (m m' : word -> option byte) (c : Z) bs,
    (forall x : word, ~ FOOT (U x) -> m' x = m x) -> 0 <= c -> c + 8 <= 2 ^ 64 ->
    (forall z, c <= z < c + 8 -> ~ FOOT z) ->
    rdn BSEGS m (Z_to_bv 64 c) 8 = Some bs -> rdn BSEGS m' (Z_to_bv 64 c) 8 = Some bs.
  Proof using.
    intros FOOT m m' c bs FR H0 H1 HF Hr. apply (rd_same BSEGS m' m (Z_to_bv 64 c) 8 bs); [| wd_ulia_c | exact Hr].
    intros x Hx. apply FR. apply HF. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
  Qed.

  Lemma pops_tot : forall l cur B, pops_ok minsz cur B l -> 0 <= p_tot l <= B.
  Proof using.
    induction l as [|t r IH]; intros cur B P; [contradiction|].
    cbn [pops_ok p_tot] in *. destruct P as (_ & Hsz & _ & P). destruct r as [|t' r'].
    - (lazymatch goal with |- ?G => let G' := eval cbn [p_tot] in G in change_no_check G' end). lia.
    - destruct P as [_ P]. specialize (IH _ _ P). lia.
  Qed.

  Theorem rc_pop_loop : forall (l : list ptrip) (regs : bvmap 5 word) (mem : word -> option byte) (j prev glenr B sum cur : Z),
    pops_ok minsz cur B l ->
    getr regs 2 = at_ S (-2288) -> getr regs 10 = Z_to_bv 64 (IBq + 728) -> getr regs 11 = Z_to_bv 64 minsz ->
    getr regs 14 = Z_to_bv 64 j -> getr regs 15 = Z_to_bv 64 prev -> getr regs 16 = Z_to_bv 64 glenr -> getr regs 5 = Z_to_bv 64 cur ->
    0 <= j -> j + Z.of_nat (length l) < 2 ^ 28 -> Z.of_nat (length l) <= glenr < 2 ^ 28 -> B < 2 ^ 41 -> 0 <= sum -> sum + p_tot l < 2 ^ 42 ->
    Forall (fun t => geo (p_addr t)) l -> all_sep (map p_addr l) ->
    (j <> 0 -> geo prev /\ Forall (bsep prev) (map p_addr l)) ->
    store_ok BSEGS mem (at_ S (-2288)) 80 = true ->
    Forall (fun t => store_ok BSEGS mem (Z_to_bv 64 (p_addr t)) 8 = true) l ->
    (j <> 0 -> store_ok BSEGS mem (Z_to_bv 64 prev) 8 = true) ->
    Forall (fun t => rdn BSEGS mem (Z_to_bv 64 (p_addr t)) 8 = Some (LE8 (Z_to_bv 64 (p_nx t)))
                     /\ rdn BSEGS mem (Z_to_bv 64 (p_addr t + 8)) 8 = Some (LE8 (Z_to_bv 64 (p_sz t)))) l ->
    rdn BSEGS mem (Z_to_bv 64 (IBq + 912)) 8 = Some (LE8 (Z_to_bv 64 B)) ->
    rdn BSEGS mem (at_ S (-2264)) 8 = Some (LE8 (Z_to_bv 64 sum)) ->
    exists r mem',
      msteps BSEGS (mkst regs (0x4e500 : word) mem rom) (mkst r (0x4e55c : word) mem' rom)
      /\ rc_keep regs r /\ pop_post S j prev glenr B sum l mem mem'.
  Proof using Hmin HS.
    induction l as [|t r IH]; intros regs mem j prev glenr B sum cur POK H2 H10 H11 H14 H15 H16 H5 Hj0 Hjl Hgl HB Hs0 Hs1 GEO SEP PRV SOKS SOKL SOKP CELLS RB RSUM;
      [contradiction|].
    pose proof (u64_range S) as HSr.
    destruct t as [[a sz] nx]. cbn [pops_ok p_addr p_sz p_nx fst snd] in POK. destruct POK as (Ea & Hsz & Hnx & POK). subst cur.
    apply Forall_cons_iff in GEO as [Ga GEOr]. cbn [p_addr fst] in Ga. unfold geo in Ga.
    cbn [map all_sep p_addr fst] in SEP. destruct SEP as [SEPa SEPr].
    apply Forall_cons_iff in SOKL as [SOKa SOKr]. cbn [p_addr fst] in SOKa.
    apply Forall_cons_iff in CELLS as [[Rnx Rsz] CELLSr]. cbn [p_addr p_sz p_nx fst snd] in Rnx, Rsz.
    cbn [length] in Hjl, Hgl. cbn [p_tot p_sz fst snd] in Hs1.
    assert (Hprev1 : j <> 0 -> (AIMGHI <= prev /\ prev + 8192 <= U S - 3584) /\ (prev + 8192 <= a \/ a + 8192 <= prev)).
    { intros Nj. destruct (PRV Nj) as [Gp Fp]. split; [exact Gp|]. cbn [map p_addr fst] in Fp. apply Forall_cons_iff in Fp as [X _]. exact X. }
    destruct (rc_pop1 mem rom S minsz j prev a sz nx glenr B sum regs H2 H10 H11 H14 H15 H16 H5 HS Hmin ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(destruct r as [|t' r']; [cbn [p_tot] in Hs1; lia | destruct POK as [_ POKr]; pose proof (pops_tot _ _ _ POKr); lia])
                Hnx Ga Hprev1 SOKS SOKa SOKP Rnx Rsz RB RSUM)
      as (r1 & RUN1 & KEEP1 & A14 & A15 & A16 & A5 & A6).
    remember (fr_pop1 mem S minsz j prev a sz nx glenr B sum) as m1 eqn:Em1.
    pose proof (fr_pop1_outside mem S minsz j prev a sz nx glenr B sum HS Ga Hprev1) as OUT1. rewrite <- Em1 in OUT1.
    pose proof (fr_pop1_grows mem S minsz j prev a sz nx glenr B sum Hprev1) as GR1. rewrite <- Em1 in GR1.
    destruct r as [|t' r'].
    - (* [comment removed for export] *)
      replace (minsz <? B - sz) with false in RUN1 by (symmetry; apply Z.ltb_ge; exact POK).
      exists r1, m1. split; [exact RUN1|]. split; [exact KEEP1|].
      (lazymatch goal with |- ?G => let G' := eval unfold pop_post in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [p_lastnx p_lasta p_tot length p_addr p_sz p_nx fst snd chain_cells] in G in change_no_check G' end).
      split.
      { intros x Hx. apply OUT1. intros F. apply Hx. unfold pop1_foot in F. (lazymatch goal with |- ?G => let G' := eval unfold loop_foot in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [p_lastnx p_nx snd] in G in change_no_check G' end).
        destruct F as [F|[F|[F|[F|[F|[F|[F|F]]]]]]]; [left; exact F | right; left; exact F | do 2 right; left; exact F
          | do 3 right; left; exists (a, sz, nx); split; [left; reflexivity | exact F] | do 4 right; left; exact F | do 5 right; left; exact F
          | do 7 right; lia | destruct F as [_ [F|F]]; [do 6 right; left; exact F | do 7 right; lia] ]. }
      split; [exact GR1|].
      split; [subst m1; apply fr_pop1_first; assumption|].
      split; [intros E0; subst m1; apply fr_pop1_last0; assumption|].
      split; [replace (glenr - Z.of_nat 1) with (glenr - 1) by lia; subst m1; apply fr_pop1_len; assumption|].
      split; [replace (B - (sz + 0)) with (B - sz) by lia; subst m1; apply fr_pop1_bytes; assumption|].
      split; [replace (j + Z.of_nat 1) with (j + 1) by lia; subst m1; apply fr_pop1_tsize; assumption|].
      split; [subst m1; apply fr_pop1_tlast; assumption|].
      split; [replace (sum + (sz + 0)) with (sum + sz) by lia; subst m1; apply fr_pop1_sum; assumption|].
      split; [intros E0; subst m1; apply fr_pop1_tfirst; assumption|].
      split; [intros N0; subst m1; apply fr_pop1_prev; assumption|].
      split; [split; [subst m1; apply fr_pop1_anext; assumption | exact I]|].
      intros x Hx. subst m1. apply fr_pop1_def; assumption.
    - (* [comment removed for export] *)
      destruct POK as [Hcont POKr].
      replace (minsz <? B - sz) with true in RUN1 by (symmetry; apply Z.ltb_lt; exact Hcont).
      pose proof GEOr as GEOr'. apply Forall_cons_iff in GEOr' as [Gt' _]. unfold geo in Gt'.
      assert (Enx : nx = p_addr t') by (destruct t' as [[a' sz'] nx']; cbn [pops_ok p_addr fst] in POKr |- *; destruct POKr as (E & _); symmetry; exact E).
      destruct KEEP1 as (K2 & K10 & K11 & K12 & K13 & K8 & K9 & K18 & K19 & K20 & K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
      (* [comment removed for export] *)
      assert (CELLS1 : Forall (fun t => rdn BSEGS m1 (Z_to_bv 64 (p_addr t)) 8 = Some (LE8 (Z_to_bv 64 (p_nx t)))
                                         /\ rdn BSEGS m1 (Z_to_bv 64 (p_addr t + 8)) 8 = Some (LE8 (Z_to_bv 64 (p_sz t)))) (t' :: r')).
      { rewrite Forall_forall in CELLSr, GEOr |- *. intros t0 Hin. destruct (CELLSr t0 Hin) as [C1 C2]. pose proof (GEOr t0 Hin) as G0. unfold geo in G0.
        assert (S0 : bsep a (p_addr t0)) by (rewrite Forall_forall in SEPa; apply SEPa; apply in_map; exact Hin). unfold bsep in S0.
        assert (P0 : j <> 0 -> bsep prev (p_addr t0)).
        { intros Nj. destruct (PRV Nj) as [_ Fp]. change (map p_addr ((a, sz, nx) :: t' :: r')) with (a :: map p_addr (t' :: r')) in Fp.
          apply Forall_cons_iff in Fp as [_ Fp]. rewrite Forall_forall in Fp. exact (Fp _ (in_map p_addr (t' :: r') t0 Hin)). }
        assert (NF : forall z, p_addr t0 <= z < p_addr t0 + 16 -> ~ pop1_foot S minsz j prev a sz nx B z).
        { intros z Hz F. unfold pop1_foot in F. destruct (Z.eq_dec j 0) as [Ej|Nj].
          - destruct F as [F|[F|[F|[F|[F|[F|[F|F]]]]]]]; lia.
          - pose proof (P0 Nj) as P0'. unfold bsep in P0'. destruct F as [F|[F|[F|[F|[F|[F|[F|F]]]]]]]; lia. }
        split.
        - apply (rd8_frame (pop1_foot S minsz j prev a sz nx B) mem m1 (p_addr t0)); [exact OUT1 | lia | lia | intros z Hz; apply NF; lia | exact C1].
        - apply (rd8_frame (pop1_foot S minsz j prev a sz nx B) mem m1 (p_addr t0 + 8)); [exact OUT1 | lia | lia | intros z Hz; apply NF; lia | exact C2]. }
      destruct (IH r1 m1 (j + 1) a (glenr - 1) (B - sz) (sum + sz) nx POKr) as (r2 & m2 & RUN2 & KEEP2 & POST2).
      + rewrite K2. exact H2. + rewrite K10. exact H10. + rewrite K11. exact H11.
      + exact A14. + exact A15. + exact A16. + exact A5.
      + lia. + cbn [length] in Hjl |- *. lia. + cbn [length] in Hgl |- *. lia. + lia. + lia. + cbn [p_tot] in Hs1 |- *. lia.
      + exact GEOr. + exact SEPr.
      + intros _. split; [exact Ga | exact SEPa].
      + eapply store_ok_mono; [exact GR1 | exact SOKS].
      + rewrite Forall_forall in SOKr |- *. intros t0 Hin. eapply store_ok_mono; [exact GR1 | exact (SOKr t0 Hin)].
      + intros _. eapply store_ok_mono; [exact GR1 | exact SOKa].
      + exact CELLS1.
      + subst m1. apply fr_pop1_bytes; assumption.
      + subst m1. apply fr_pop1_sum; assumption.
      + exists r2, m2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
        split; [exact (rc_keep_trans regs r1 r2 (conj K2 (conj K10 (conj K11 (conj K12 (conj K13 (conj K8 (conj K9 (conj K18 (conj K19 (conj K20 (conj K3 (conj K4 (conj K21 (conj K22 (conj K23 (conj K24 (conj K25 (conj K26 K27)))))))))))))))))) KEEP2)|].
        destruct POST2 as (FR2 & GR2 & P896 & P904 & P888 & P912 & Psz & Plast & Psum & Ptf & Pprev & Pchain & Pdef).
        assert (FR2' : forall x : word, ~ loop_foot S j prev ((a, sz, nx) :: t' :: r') (U x) -> m2 x = m1 x).
        { intros x Hx. apply FR2. intros F. apply Hx. unfold loop_foot in F |- *. cbn [p_lastnx] in F |- *.
          destruct F as [F|[F|[F|[F|[F|[F|[F|F]]]]]]]; [left; exact F | right; left; exact F | do 2 right; left; exact F
            | do 3 right; left; destruct F as (t0 & Hin & F); exists t0; split; [right; exact Hin | exact F]
            | do 3 right; left; exists (a, sz, nx); split; [left; reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn [p_addr fst] in G in change_no_check G' end); destruct F as [_ F]; exact F]
            | lia | do 6 right; left; exact F | do 7 right; exact F ]. }
        (lazymatch goal with |- ?G => let G' := eval unfold pop_post in G in change_no_check G' end). split.
        { intros x Hx. rewrite (FR2' x Hx). apply OUT1. intros F. apply Hx. unfold pop1_foot in F. (lazymatch goal with |- ?G => let G' := eval unfold loop_foot in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [p_lastnx] in G in change_no_check G' end).
          destruct F as [F|[F|[F|[F|[F|[F|[F|F]]]]]]]; [left; exact F | exfalso; lia | do 2 right; left; exact F
            | do 3 right; left; exists (a, sz, nx); split; [left; reflexivity | exact F] | do 4 right; left; exact F | do 5 right; left; exact F
            | do 7 right; lia | exfalso; lia ]. }
        split; [eapply mem_grows_trans; [exact GR1 | exact GR2]|].
        cbn [p_lastnx p_lasta p_tot length p_addr p_sz p_nx fst snd chain_cells] in *.
        split; [exact P896|]. split; [exact P904|].
        split; [replace (glenr - Z.of_nat (Datatypes.S (Datatypes.S (length r')))) with (glenr - 1 - Z.of_nat (Datatypes.S (length r'))) by lia; exact P888|].
        split; [replace (B - (sz + (p_sz t' + p_tot r'))) with (B - sz - (p_sz t' + p_tot r')) by lia; exact P912|].
        split; [replace (j + Z.of_nat (Datatypes.S (Datatypes.S (length r')))) with (j + 1 + Z.of_nat (Datatypes.S (length r'))) by lia; exact Psz|].
        split; [exact Plast|].
        split; [replace (sum + (sz + (p_sz t' + p_tot r'))) with (sum + sz + (p_sz t' + p_tot r')) by lia; exact Psum|].
        split.
        { intros Ej. apply (rd_same BSEGS m2 m1); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | subst m1; apply fr_pop1_tfirst; assumption].
          intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply FR2. intros F. unfold loop_foot in F.
          destruct F as [F|[F|[F|[F|[F|[F|[F|F]]]]]]]; try lia.
          destruct F as (t0 & Hin & F). rewrite Forall_forall in GEOr. pose proof (GEOr t0 Hin) as G0. unfold geo in G0. lia. }
        split.
        { intros Nj. destruct (Hprev1 Nj) as (Gp & Sp). destruct (PRV Nj) as [_ Fp]. change (map p_addr ((a, sz, nx) :: t' :: r')) with (a :: map p_addr (t' :: r')) in Fp.
          apply Forall_cons_iff in Fp as [_ Fp].
          apply (rd8_frame (loop_foot S (j + 1) a (t' :: r')) m1 m2 prev); [exact FR2 | lia | lia | | subst m1; apply fr_pop1_prev; assumption].
          intros z Hz F. unfold loop_foot in F.
          destruct F as [F|[F|[F|[F|[F|[F|[F|F]]]]]]]; try lia.
          destruct F as (t0 & Hin & F). rewrite Forall_forall in Fp. pose proof (Fp (p_addr t0) (in_map p_addr (t' :: r') t0 Hin)) as S0. unfold bsep in S0. lia. }
        split; [split; [| exact Pchain] | exact Pdef].
        (* [comment removed for export] *)
        apply Pprev. lia.
  Qed.
End POPLOOP.
