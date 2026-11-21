(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (11 recorded proofs replaced by written proofs (aheap_pres_refl, aheap_pres_trans, aheap_pres_weaken and 8 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Export ABase.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AMalloc_iface () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec9AsanEmbed6aembedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC35stdpp4gmap;gmap_lookupC35stdpp4base6LookupI46Stdlib5Lists4List5NoDup00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00c59OSSVerify5KrLib5BothW=AMalloc_iface<aclient_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01c59OSSVerify5KrLib5BothW=AMalloc_iface:aheap_presC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib5BothW5ABase9in_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or01I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or02C59OSSVerify5KrLib5BothW5ABase7ab_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7ab_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2ex01C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib5BothW5ABase7in_fakeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6abkind02C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K59OSSVerify5KrLib5BothW5ABase6ablock01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00c59OSSVerify5KrLib5BothW=AMalloc_iface=aclient_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05c59OSSVerify5KrLib5BothW=AMalloc_iface;shad_unshadC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib5Lists4List9nth_errorC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc59OSSVerify5KrLib5BothW=AMalloc_ifaceBaclient_range_addrC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=AMalloc_ifaceCaheap_pres_bytes_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=AMalloc_iface@aheap_pres_wr_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=AMalloc_iface4pcovC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:avoids_allC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib4Spec8AsanCtrl8iv_clearC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z3lebC46Stdlib4Bool4Bool8orb_propC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic9False_indK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06".
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Section Client.
Variable CI : list (Z * Z).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition aclient_addr (LB : list ablock) (SP : Z) (a : Z) : Prop :=
  (SP <= a < 2^47)
  \/ in_ranges CI a
  \/ in_block LB a
  \/ (exists a', ((ATOP <= a' < 2^47) \/ in_ranges CI a' \/ in_fake LB a') /\ a = shad a').   (* [comment removed for export] *)

Definition aheap_pres (LB : list ablock) (SP : Z) (m m' : amem) : Prop :=
  forall a, 0 <= a < 2^64 -> aclient_addr LB SP a ->
    m' (wa a) = m (wa a) /\ (wview bsegs m (wa a) <> None -> wview bsegs m' (wa a) <> None).

Lemma aheap_pres_refl : forall LB SP m, aheap_pres LB SP m m.
Proof. intros LB SP m a _ _. auto. Qed.

Lemma aheap_pres_trans : forall LB SP m1 m2 m3,
  aheap_pres LB SP m1 m2 -> aheap_pres LB SP m2 m3 -> aheap_pres LB SP m1 m3.
Proof.
  intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma aheap_pres_weaken : forall LB LB' SP SP' m m',
  aheap_pres LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> aheap_pres LB' SP' m m'.
Proof.
  intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
  - left; lia.
  - right; left; exact Hc.
  - right; right; left. exists b. split; [apply HL; exact Hb| exact Hr].
  - right; right; right. exists a'. split; [|reflexivity].
    destruct Ha' as [X|[X|(c & A & n & Hin & X)]]; [left; lia| right; left; exact X| right; right].
    exists c, A, n. split; [apply HL; exact Hin| exact X].
Qed.

(* [comment removed for export] *)
Definition aclient_app_range (LB : list ablock) (SP : Z) (A n : Z) : Prop :=
  (SP <= A /\ A + n <= 2^47)
  \/ (exists iv, In iv CI /\ fst iv <= A /\ A + n <= snd iv)
  \/ (exists cls FA fn, In (mkABlock (ABFake cls) FA fn) LB /\ FA <= A /\ A + n <= FA + fn).

(* [comment removed for export] *)
Definition aclient_range (LB : list ablock) (SP : Z) (A n : Z) : Prop :=
  aclient_app_range LB SP A n
  \/ (exists b, In b LB /\ ab_addr b <= A /\ A + n <= ab_addr b + ab_size b)
  \/ aclient_app_range LB ATOP (8 * (A - ASHOFF)) (8 * n).     (* [comment removed for export] *)

Lemma shad_unshad : forall a, shad (8 * (a - ASHOFF)) = a.
Proof. intros a. unfold shad. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mul_comm, Z.div_mul by lia. lia. Qed.

Lemma aclient_range_addr : forall LB SP A n a,
  aclient_range LB SP A n -> A <= a < A + n -> aclient_addr LB SP a.
Proof.
  intros LB SP A n a HR Ha. unfold aclient_range, aclient_app_range, aclient_addr, in_ranges, in_block, in_fake in *.
  destruct HR as [[H|[(iv & Hiv & H1 & H2)|(c & FA & fn & Hb & H1 & H2)]] | [(b & Hb & H1 & H2) | HS]].
  - left; lia.
  - right; left; exists iv; split; [exact Hiv|lia].
  - right; right; left. exists (mkABlock (ABFake c) FA fn). split; [exact Hb| cbn; lia].
  - right; right; left; exists b; split; [exact Hb|lia].
  - right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
    destruct HS as [H|[(iv & Hiv & H1 & H2)|(c & FA & fn & Hb & H1 & H2)]].
    + left; lia.
    + right; left; exists iv; split; [exact Hiv|lia].
    + right; right. exists c, FA, fn. split; [exact Hb|lia].
Qed.

Lemma aheap_pres_bytes_at : forall LB SP m m' A bs,
  aheap_pres LB SP m m' -> bytes_at bsegs m A bs -> aclient_range LB SP A (Z.of_nat (length bs)) ->
  bytes_at bsegs m' A bs.
Proof.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply aclient_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma aheap_pres_wr_at : forall LB SP m m' A n,
  aheap_pres LB SP m m' -> wr_at bsegs m A n -> aclient_range LB SP A n -> wr_at bsegs m' A n.
Proof.
  intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply aclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma aheap_pres_rw_cells : forall LB SP m m' A cs,
  aheap_pres LB SP m m' -> rw_cells bsegs m A cs -> aclient_range LB SP A (Z.of_nat (cells_size cs)) ->
  rw_cells bsegs m' A cs.
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply aheap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply aheap_pres_wr_at; eauto.
Qed.

Lemma aheap_pres_stk : forall LB SP m m' lo hi,
  aheap_pres LB SP m m' -> stk bsegs m lo hi -> SP <= lo -> hi <= 2^47 -> stk bsegs m' lo hi.
Proof.
  intros LB SP m m' lo hi HP ST HS HH. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma aheap_pres_shadow : forall LB SP m m' a',
  aheap_pres LB SP m m' ->
  ((ATOP <= a' < 2^47) \/ in_ranges CI a' \/ in_fake LB a') ->
  0 <= shad a' < 2^64 ->
  m' (wa (shad a')) = m (wa (shad a')).
Proof.
  intros LB SP m m' a' HP Ha Hs. destruct (HP (shad a') Hs ltac:(right; right; right; exists a'; split; [exact Ha|reflexivity])) as [E _]. exact E.
Qed.

End Client.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pcov (RESV : list (Z * Z)) (lo hi : Z) : Prop :=
  forall x, lo <= x < hi -> exists iv, In iv RESV /\ fst iv <= x < snd iv.
Definition aresv_ok (L : alayout) (RESV : list (Z * Z)) : Prop :=
     pcov RESV 0x10000 AIMG_HI                                            (* [comment removed for export] *)
  /\ pcov RESV 0x7fff7000 0x10007fff8000                                  (* [comment removed for export] *)
  /\ pcov RESV (4096 * al_V L 221%nat) (4096 * al_V L 221%nat + 137439023104)   (* [comment removed for export] *)
  /\ pcov RESV (al_ptr_array L) (al_ptr_array L + 0x800000)              (* [comment removed for export] *)
  /\ pcov RESV (al_t L) (al_t L + 4096) /\ pcov RESV (al_ctx L) (al_ctx L + 65536)
  /\ pcov RESV (al_nodes L) (al_nodes L + 1048576) /\ pcov RESV (al_store L) (al_store L + 8388608)
  /\ pcov RESV (al_fake L) (al_fake L + 11571200) /\ pcov RESV (4096 * al_V L 323%nat) (4096 * al_V L 323%nat + 4096)   (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ pcov RESV (4096 * al_V L 91%nat) (4096 * al_V L 91%nat + 0x10000)
  /\ pcov RESV (4096 * al_V L 220%nat) (4096 * al_V L 220%nat + 0x38e000)
  /\ pcov RESV (4096 * al_V L 258%nat) (4096 * al_V L 258%nat + 4096)
  /\ pcov RESV (4096 * al_V L 503%nat) (4096 * al_V L 503%nat + 4096)
  /\ pcov RESV (4096 * al_V L 584%nat) (4096 * al_V L 584%nat + 4096).

Lemma pcov_clear : forall RESV lo hi a n,
  pcov RESV lo hi -> avoids_all a n RESV = true -> lo < hi -> 0 < n -> a + n <= lo \/ hi <= a.
Proof.
  intros RESV lo hi a n PC AV LH N.
  destruct (Z_lt_le_dec a hi) as [L1|]; [| right; lia]. destruct (Z_lt_le_dec lo (a + n)) as [L2|]; [| left; lia]. exfalso.
  destruct (PC (Z.max a lo) ltac:(lia)) as (iv & Hin & R).
  unfold avoids_all in AV. rewrite forallb_forall in AV. specialize (AV iv Hin). unfold iv_clear in AV.
  apply orb_prop in AV. destruct AV as [AV|AV]; apply Z.leb_le in AV; lia.
Qed.

Section Stmts.
Variable CI : list (Z * Z).
(* [comment removed for export] *)
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

(* [comment removed for export] *)
Definition aunw (m : amem) (L : alayout) (RNG : footprint) (lo PC : Z) (sp s0 ra : word) (tr : list Z) : Prop :=
     (bv_unsigned sp + 16 < al_top L
      /\ uchain m (al_top L) PC (bv_unsigned sp) (bv_unsigned s0) UDEPTH tr /\ (length tr <= 28)%nat
      /\ In (PC :: bv_unsigned ra :: tr) (al_U L)
      /\ rng RNG lo (al_top L - lo))            (* [comment removed for export] *)
  \/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ In [PC] (al_U L)).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition amalloc_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ match snd r with
       | None => False      (* [comment removed for export] *)
       | Some p => exists A junk,
           a0 = Z_to_bv 64 A /\ ablock_range A n
           /\ AHEAP L RNG' (fst r) (HB p A n :: LB) m'
           /\ rw_cells bsegs m' A [CB (Z.to_nat n) junk]
           /\ rng RNG' A n /\ rng RNG' (shad A) (shlen (n + 7))
           /\ (is_primary n = false -> A = aptr_addr (fst r) p)
       end.

Definition amalloc_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  AHEAP L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  (* [comment removed for export] *)
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  aresv_ok L RESV ->
  implS bsegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition afree_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (p : aptr) (lo : Z) (m : amem)
    (r : astate) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m m'
    /\ AHEAP L RNG' r (lb_remove p LB) m'.

Definition afree_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z),
  AHEAP L RNG st LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS bsegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition afree_null_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP L RNG st LB m'.

Definition afree_null_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (lo : Z) (tr : list Z),
  AHEAP L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0 ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (afree_null_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
End Stmts.

Record AMallocIface := mkAMallocIface {
  aci : list (Z * Z);          (* [comment removed for export] *)
  AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop;
  (* [comment removed for export] *)
  AI_aci_img : forall iv, In iv aci -> snd iv <= AIMG_HI;      (* [comment removed for export] *)
  AI_aci_lo : forall iv, In iv aci -> 0 <= fst iv;            (* [comment removed for export] *)
  AI_rng_mono : forall L RNG RNG' st LB m, fp_le RNG RNG' -> AHEAP L RNG st LB m -> AHEAP L RNG' st LB m;
  AI_perm : forall L RNG st LB LB' m, Permutation.Permutation LB LB' -> AHEAP L RNG st LB m -> AHEAP L RNG st LB' m;
  AI_frame : forall L RNG st LB m m' (W : list ivl),
      AHEAP L RNG st LB m -> munch W m m' -> wmono bsegs m m' ->
      Forall (fun iv => aclient_range aci LB (ATOP + 4096) (fst iv) (snd iv - fst iv)) W ->
      AHEAP L RNG st LB m';
  AI_block : forall L RNG st LB m p A n,
      AHEAP L RNG st LB m -> In (HB p A n) LB ->
      1 <= n <= AREQMAX /\                                        (* [comment removed for export] *)
      ablock_range A n /\ rng RNG A n /\ rng RNG (shad A) (shlen (n + 7)) /\ ablock_shadow m A n
      /\ wr_at bsegs m A n
      /\ (exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch))
      (* [comment removed for export] *)
      /\ exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + n + 64 <= RHI
           /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at bsegs m (shad RLO) (shlen (RHI - RLO));
  (* [comment removed for export] *)
  AI_block_bounds : forall L RNG st LB m b,
      AHEAP L RNG st LB m -> In b LB -> AIMG_HI <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP;
  AI_blocks_disjoint : forall L RNG st LB m b1 b2,
      AHEAP L RNG st LB m -> In b1 LB -> In b2 LB -> b1 <> b2 ->
      ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1;
  AI_blocks_nodup : forall L RNG st LB m, AHEAP L RNG st LB m -> List.NoDup LB;
  AI_hb_ids : forall L RNG st LB m, AHEAP L RNG st LB m -> List.NoDup (hb_ids LB);   (* [comment removed for export] *)
  AI_layout : forall L RNG st LB m, AHEAP L RNG st LB m ->
      al_bot L + 0x800000 = al_top L /\ al_top L mod 4096 = 0 /\ al_top L <= 2^47 /\ (ATOP - 160 <= al_bot L <= ATOP + 3936)
      /\ a_space_beg st = al_space_beg L /\ (length (al_U L) <= Z.to_nat AUMAX)%nat
      /\ AIMG_HI <= al_fake L /\ al_fake L + 0xb09000 <= ATOP;
  (* [comment removed for export] *)
  AI_relro : forall L RNG st LB m, AHEAP L RNG st LB m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None;
  AI_rtcells : forall L RNG st LB m, AHEAP L RNG st LB m -> artcells m;
  (* [comment removed for export] *)
  AI_malloc : amalloc_stmt aci AHEAP;
  AI_free : afree_stmt aci AHEAP;
  AI_free_null : afree_null_stmt aci AHEAP
}.

(* [comment removed for export] *)
End CANSEC1.
