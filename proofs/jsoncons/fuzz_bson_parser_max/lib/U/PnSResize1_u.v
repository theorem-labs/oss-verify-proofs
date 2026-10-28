(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmFrame. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSReset_u PnSrcSMemmove_u PnTxtKit_u PnSResizeP_u
     Bs0_code_r56838_5683c_u Bs0_code_r56c10_56c14_u Bs0_code_r56c34_56c38_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMSRZ1.
Import PMS.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (cr0 : credit).
Variables (o n S r tg : Z) (s : PM.vstr).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis K0 : K [].
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S 14336.
Hypothesis Ho1 : S <= o.
Hypothesis Ho2 : o + 24 <= hl_sptop L.
Hypothesis Ho3 : o mod 8 = 0.
Hypothesis Hn1 : 0 <= n <= PM.vs_size s + PM.CHUNK.
Hypothesis Hn2 : n < 2 ^ 26 + PM.CHUNK.
Hypothesis BRLB : PMFR.brange L LB.
Hypothesis OPN : PMS.opnew_spec L HI.
Hypothesis OPD : PMS.opdel_spec L HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.vstr) (tg' : Z) (cr' : credit),
  regs_preserved R0 R' -> PM.vstr_at RSEGS PMSP.T3 M' o s' -> PM.vs_size s' = n -> PM.tb_ok s' tg' ->
  (n <= PM.vs_cap s -> PM.vs_own s' = PM.vs_own s /\ tg' = tg) ->
  L5C.hpres L LB S (PMSP.pm_scr 1) [(o, 24)] M0 M' ->
  PMSP.credit_keep cr0 cr' (PM.pot_text L s tg) (PM.pot_text L s' tg') ->
  model_but_vm model0 model' -> hi_heap HI (PM.vs_own s' ++ LB) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22)))
  /\ L5.u64_at RSEGS M (S - 72) (bv_unsigned (getr R0 (reg 23))) /\ L5.u64_at RSEGS M (S - 80) (bv_unsigned (getr R0 (reg 24))).
(* [comment removed for export] *)
Definition kept0 (R : bvmap 5 word) : Prop := forall x, In x [3; 4; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
(* [comment removed for export] *)
Definition mem_ok (M : word -> option byte) : Prop :=
  PMK.ek L LB S 14336 [(o, 24)] M0 M /\ PMK.dk L LB S 14336 M0 M /\ L5C.stk (hl_sptop L) M S 14336 /\ L5.defined M o 24.

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof. exact (PMSRS.sub_in KS l). Qed.

(* [comment removed for export] *)
Lemma regs_back (R1 : bvmap 5 word) :
  getr R1 (reg 2) = Z_to_bv 64 S -> getr R1 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) ->
  getr R1 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) -> getr R1 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) ->
  getr R1 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) -> getr R1 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) ->
  getr R1 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) -> getr R1 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22))) ->
  getr R1 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 23))) -> getr R1 (reg 24) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 24))) ->
  kept0 R1 -> regs_preserved R0 R1.
Proof.
  intros E2 E8 E9 E18 E19 E20 E21 E22 E23 E24 KP. apply PMK.preserved_by_index. intros x Hx. unfold PMK.cs_all in Hx. cbn in Hx.
  destruct Hx as [<-|Hx]; [rewrite E2, Rsp0; reflexivity|].
  destruct Hx as [<-|Hx]; [apply KP; cbn; auto|]. destruct Hx as [<-|Hx]; [apply KP; cbn; auto|].
  destruct Hx as [<-|Hx]; [rewrite E8; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
  destruct Hx as [<-|Hx]; [rewrite E18; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E19; apply Z_to_bv_bv_unsigned|].
  destruct Hx as [<-|Hx]; [rewrite E20; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E21; apply Z_to_bv_bv_unsigned|].
  destruct Hx as [<-|Hx]; [rewrite E22; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E23; apply Z_to_bv_bv_unsigned|].
  destruct Hx as [<-|Hx]; [rewrite E24; apply Z_to_bv_bv_unsigned|].
  apply KP. destruct Hx as [<-|[<-|[<-|[]]]]; cbn; auto 10.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma finish_long (fx : FPState) R M model (q A tg' : Z) (cr' : credit) :
  PMSP.model_ok model ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 20) = Z_to_bv 64 q -> getr R (reg 22) = Z_to_bv 64 n ->
  kept0 R -> saves M -> mem_ok M ->
  L5.u64_at RSEGS M o (A + 1) -> L5.u64_at RSEGS M (o + 16) q ->
  1 <= n < A -> 26 <= A <= 2 ^ 27 -> A mod 2 = 0 -> L5.defined M q A -> 4096 <= q -> q + A <= hl_ceil L ->
  hi_heap HI ((q, A) :: LB) cr' M (m_vmmaps model) -> model_but_vm model0 model ->
  PM.tb_ok (PM.VLong A n q) tg' -> (n <= PM.vs_cap s -> [(q, A)] = PM.vs_own s /\ tg' = tg) ->
  PMSP.credit_keep cr0 cr' (PM.pot_text L s tg) (PM.pot_text L (PM.VLong A n q) tg') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x58c00 M model) K.
Proof.
  intros MOK A2 A8 A20 A22 KP SV (EK & DK & STK & DO) W0 W16 Hn HA HAe DQ Hq0 Hq1 HH MB TBOK OWN CK.
  assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
  pose proof (PMF.u8_of_u64 RSEGS M o (A + 1) ltac:(lia) W0) as B0. pose proof (PMF.odd_byte A HAe ltac:(lia)) as ODB.
  assert (H33 : 0 <= (A + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (A + 1) 256 ltac:(lia)); lia).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
  assert (WRq : L5.writable RSEGS M (q + n) 1) by (apply (L5C.writable_of_defined RSEGS M (q + n) 1); [apply (L5.defined_sub M q A (q + n) 1 DQ); lia|lia|lia]).
  assert (Dqo : q + n + 1 <= o \/ o + 24 <= q + n) by (left; lia).
  assert (Dqf : q + n + 1 <= S - 80 \/ S - 80 + 80 <= q + n) by (left; lia).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as H10. change (bv_modulus 64) with (2 ^ 64) in H10.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))) as G1. change (bv_modulus 64) with (2 ^ 64) in G1.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as G8. change (bv_modulus 64) with (2 ^ 64) in G8.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as G9. change (bv_modulus 64) with (2 ^ 64) in G9.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as G18. change (bv_modulus 64) with (2 ^ 64) in G18.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 19))) as G19. change (bv_modulus 64) with (2 ^ 64) in G19.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 20))) as G20. change (bv_modulus 64) with (2 ^ 64) in G20.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 21))) as G21. change (bv_modulus 64) with (2 ^ 64) in G21.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 22))) as G22. change (bv_modulus 64) with (2 ^ 64) in G22.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 23))) as G23. change (bv_modulus 64) with (2 ^ 64) in G23.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 24))) as G24. change (bv_modulus 64) with (2 ^ 64) in G24.
  assert (A10 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  LeanFeed.pfeed PP (PMSRZP.apML_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 33%nat => (A + 1) mod 256 | 35%nat => q | 38%nat => n
        | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
        | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
        | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 52%nat => bv_unsigned (getr R0 (reg 23))
        | 53%nat => bv_unsigned (getr R0 (reg 24)) | 54%nat => bv_unsigned (getr R (reg 10)) | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG & _ & FRZ0 & MS & KS & E1 & E2 & E8 & E9 & _ & E18 & E19 & E20 & E21 & E22 & E23 & E24 & C0 & C8)); PMK.pvz_clrT.
  set (P := fun a => (o + 8 <= a < o + 8 + 8) \/ (q + n <= a < q + n + 1)).
  assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FRZ0; [exact Ha|intro X; apply N; unfold P; lia|intro X; apply N; unfold P; lia]. }
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok ((q, A) :: LB) cr' M model fx fx1 R 0x58c00 R1 0x58c54 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS MG FRZ).
  { intros a Pa. unfold P in Pa. destruct Pa as [X|X];
      [apply (PMK.cwr_stack L ((q, A) :: LB) M S 14336 a STK); lia
      |apply (PMK.cwr_block L ((q, A) :: LB) q A a ltac:(left; reflexivity)); lia]. }
  { intros a. unfold P. apply PMK.or_dec; apply PMK.rng_dec. }
  intros HH1.
  assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra0).
  unfold PMK.cfg.
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x58c54 W_57614 r F_57614 ltac:(reflexivity) D_57614 RA1 Hr1 Hr2)|].
  assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (forall i, a <= i < a + m -> ~ P i) -> L5C.agree_on M M1 a m).
  { intros a0 m0 Ha0 Hm0 X i Hi. apply FRZ; [lia| apply X; exact Hi]. }
  apply (KONT fx1 R1 M1 model (PM.VLong A n q) tg' cr'); [| | reflexivity | exact TBOK | | | exact CK | exact MB | exact HH1].
  - apply regs_back; try assumption.
    intros x Hx. rewrite (KS x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - split; [intros i Hi; apply MG; apply DO; exact Hi|]. split; [exact I|].
    split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|X]; cdisj; lia]|lia|lia|exact W0]|].
    split; [exact C8|].
    split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|X]; cdisj; lia]|lia|lia|exact W16]|].
    split; [lia|]. split; [lia|]. split; [exact HAe|]. split; [intros i Hi; apply MG; apply DQ; exact Hi| exact I].
  - intros X. destruct (OWN X) as (O1 & O2). split; [exact O1| exact O2].
  - apply (PMK.hpres_of L LB S 14336 _ M0 M1).
    + apply (PMK.ek_trans L LB S 14336 _ M0 M M1 EK).
      apply (PMK.ek_piece L LB S 14336 _ M M1 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa. destruct Pa as [X|X].
      * apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
      * exact (PMSRS.own_not_client L HI HIok [(q, A)] LB cr' M _ q A a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA).
    + destruct (PMK.stk_grows L M M1 S 14336 MG STK) as (_ & _ & _ & _ & D1). exact D1.
    + apply (PMK.dk_trans L LB S 14336 M0 M M1 DK). apply PMK.dk_grows. exact MG.
Qed.

(* [comment removed for export] *)
Lemma finish_short (fx : FPState) R M model (b0 : Z) (cr' : credit) :
  PMSP.model_ok model ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 20) = Z_to_bv 64 (o + 1) -> getr R (reg 22) = Z_to_bv 64 n ->
  kept0 R -> saves M -> mem_ok M ->
  L5.u8_at RSEGS M o b0 -> 0 <= b0 <= 255 -> Z.testbit b0 0 = false -> 1 <= n <= 22 ->
  hi_heap HI LB cr' M (m_vmmaps model) -> model_but_vm model0 model ->
  PM.tb_ok (PM.VShort n) tg -> (n <= PM.vs_cap s -> [] = PM.vs_own s) ->
  PMSP.credit_keep cr0 cr' (PM.pot_text L s tg) (PM.pot_text L (PM.VShort n) tg) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x58c00 M model) K.
Proof.
  intros MOK A2 A8 A20 A22 KP SV (EK & DK & STK & DO) B0 HB0 EVB Hn HH MB TBOK OWN CK.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as H10. change (bv_modulus 64) with (2 ^ 64) in H10.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))) as G1. change (bv_modulus 64) with (2 ^ 64) in G1.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as G8. change (bv_modulus 64) with (2 ^ 64) in G8.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as G9. change (bv_modulus 64) with (2 ^ 64) in G9.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as G18. change (bv_modulus 64) with (2 ^ 64) in G18.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 19))) as G19. change (bv_modulus 64) with (2 ^ 64) in G19.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 20))) as G20. change (bv_modulus 64) with (2 ^ 64) in G20.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 21))) as G21. change (bv_modulus 64) with (2 ^ 64) in G21.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 22))) as G22. change (bv_modulus 64) with (2 ^ 64) in G22.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 23))) as G23. change (bv_modulus 64) with (2 ^ 64) in G23.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 24))) as G24. change (bv_modulus 64) with (2 ^ 64) in G24.
  assert (A10 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  LeanFeed.pfeed PP (PMSRZP.apMS_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 33%nat => b0 | 38%nat => n
        | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
        | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
        | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 52%nat => bv_unsigned (getr R0 (reg 23))
        | 53%nat => bv_unsigned (getr R0 (reg 24)) | 54%nat => bv_unsigned (getr R (reg 10)) | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG & _ & FRZ0 & MS & KS & E1 & E2 & E8 & E9 & _ & E18 & E19 & E20 & E21 & E22 & E23 & E24 & CN & CB)); PMK.pvz_clrT.
  set (P := fun a => o <= a < o + 24).
  assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FRZ0; [exact Ha|intro X; apply N; unfold P; lia]. }
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok LB cr' M model fx fx1 R 0x58c00 R1 0x58c54 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS MG FRZ).
  { intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L LB M S 14336 a STK); lia. }
  { intros a. unfold P. apply PMK.rng_dec. }
  intros HH1.
  assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra0).
  unfold PMK.cfg.
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x58c54 W_57614 r F_57614 ltac:(reflexivity) D_57614 RA1 Hr1 Hr2)|].
  apply (KONT fx1 R1 M1 model (PM.VShort n) tg cr'); [| | reflexivity | exact TBOK | | | exact CK | exact MB | exact HH1].
  - apply regs_back; try assumption.
    intros x Hx. rewrite (KS x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - split; [intros i Hi; apply MG; apply DO; exact Hi|]. split; [exact I|]. split; [lia| exact CB].
  - intros X. split; [exact (OWN X)| reflexivity].
  - apply (PMK.hpres_of L LB S 14336 _ M0 M1).
    + apply (PMK.ek_trans L LB S 14336 _ M0 M M1 EK).
      apply (PMK.ek_piece L LB S 14336 _ M M1 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa.
      apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
    + destruct (PMK.stk_grows L M M1 S 14336 MG STK) as (_ & _ & _ & _ & D1). exact D1.
    + apply (PMK.dk_trans L LB S 14336 M0 M M1 DK). apply PMK.dk_grows. exact MG.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma saves_keep (M M' : word -> option byte) (P : Z -> Prop) :
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> (forall a, S - 80 <= a < S -> ~ P a) ->
  140735332483152 <= S <= 2 ^ 47 -> saves M -> saves M'.
Proof.
  intros FRZ X HS (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
  assert (AG : forall a, S - 80 <= a -> a + 8 <= S -> L5C.agree_on M M' a 8).
  { intros a H1 H2 i Hi. apply FRZ; [lia| apply X; lia]. }
  unfold saves. repeat split; (eapply (L5C.u64_at_agree RSEGS M M'); [apply AG; lia|lia|lia|eassumption]).
Qed.

(* [comment removed for export] *)
Lemma fit_short (fx : FPState) R M model (n0 m : Z) :
  PMSP.model_ok model -> s = PM.VShort n0 -> n = n0 + m -> 1 <= m -> n <= 22 -> 0 <= n0 -> tg = 0 ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 m -> getr R (reg 10) = Z_to_bv 64 0 ->
  getr R (reg 18) = Z_to_bv 64 n0 -> getr R (reg 23) = Z_to_bv 64 22 ->
  kept0 R -> saves M -> mem_ok M -> L5.u8_at RSEGS M o (2 * n0) ->
  hi_heap HI LB cr0 M (m_vmmaps model) -> model_but_vm model0 model ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x58ae8 M model) K.
Proof.
  intros MOK Es En Hm Hn Hn0 Etg A2 A8 A9 A10 A18 A23 KP SV MO B0 HH MB.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
  LeanFeed.pfeed PP (PMSRZP.fitS_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 43%nat => m | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & MS1 & KS1 & F1 & F10 & _ & F12 & F20 & F22).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
  unfold PMSP.cfg.
  apply (PMK.spiece_ro RSEGS model fx fx1 R 0x58ae8 R1 0xaba00 M K Mh Ml MS1).
  (* [comment removed for export] *)
  destruct (PMTK.fill_run fx1 R1 M (o + n0 + 1) m 363520 F10 F12 F1 ltac:(split; [lia| reflexivity]) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(apply (L5.writable_sub RSEGS M o 24 (o + n0 + 1) m WRo); lia)) as (R3 & M3 & MS3 & MG3 & FR3 & D3 & KS3 & _).
  set (P := fun a => o + n0 + 1 <= a < o + n0 + 1 + m).
  apply (PMK.spiece RSEGS L HI KL HIok LB cr0 M model fx1 fx1 R1 0xaba00 R3 363520 M3 P K HH Mh Ml ltac:(destruct STOP; lia) MS3 MG3 FR3).
  { intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L LB M S 14336 a STK); lia. }
  { intros a. unfold P. apply PMK.rng_dec. }
  intros HH3.
  assert (KSR : forall x, In x L5K.CS -> getr R3 (reg x) = getr R1 (reg x)) by exact KS3.
  apply (finish_short fx1 R3 M3 model (2 * n0) cr0 MOK).
  - rewrite (KSR 2%nat) by PMK.inl. rewrite (KS1 2%nat) by PMK.inl. exact A2.
  - rewrite (KSR 8%nat) by PMK.inl. rewrite (KS1 8%nat) by PMK.inl. exact A8.
  - rewrite (KSR 20%nat) by PMK.inl. exact F20.
  - rewrite (KSR 22%nat) by PMK.inl. rewrite F22. f_equal. lia.
  - intros x Hx. rewrite (KSR x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
    rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - apply (saves_keep M M3 P FR3); [intros a Ha X; unfold P in X; lia| lia| exact SV].
  - split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M3 EK); apply (PMK.ek_piece L LB S 14336 _ M M3 P FR3);
             intros a Ha CA NE OW Pa; unfold P in Pa; apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]|].
    split; [apply (PMK.dk_trans L LB S 14336 M0 M M3 DK); apply PMK.dk_grows; exact MG3|].
    split; [exact (PMK.stk_grows L M M3 S 14336 MG3 STK)|]. intros i Hi. apply MG3. apply DO. exact Hi.
  - apply (L5C.u8_at_agree RSEGS M M3); [intros i Hi; apply FR3; [lia| unfold P; lia]|lia|lia|exact B0].
  - lia.
  - apply PMF.even_byte.
  - lia.
  - exact HH3.
  - exact MB.
  - subst tg. unfold PM.tb_ok. cbn. lia.
  - intros _. rewrite Es. reflexivity.
  - rewrite Es. unfold PMSP.credit_keep, PM.pot_text. cbn [PM.vs_cap]. lia.
Qed.

(* [comment removed for export] *)
Lemma fit_long (fx : FPState) R M model (c n0 p m : Z) :
  PMSP.model_ok model -> s = PM.VLong c n0 p -> n = n0 + m -> 1 <= m -> n <= c - 1 ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 m -> getr R (reg 10) = Z_to_bv 64 1 ->
  getr R (reg 18) = Z_to_bv 64 n0 ->
  kept0 R -> saves M -> mem_ok M ->
  L5.u64_at RSEGS M o (c + 1) -> L5.u64_at RSEGS M (o + 16) p -> 0 <= n0 -> 26 <= c <= 2 ^ 27 -> c mod 2 = 0 -> L5.defined M p c ->
  4096 <= p -> p + c <= hl_ceil L -> PM.tb_ok s tg ->
  hi_heap HI ((p, c) :: LB) cr0 M (m_vmmaps model) -> model_but_vm model0 model ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x58ae8 M model) K.
Proof.
  intros MOK Es En Hm Hn A2 A8 A9 A10 A18 KP SV MO W0 W16 Hn0 Hc Hce DP Hp0 Hp1 TBOK HH MB.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
  assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
  LeanFeed.pfeed PP (PMSRZP.fitL_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 35%nat => p | 43%nat => m | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & MS1 & KS1 & F1 & F10 & _ & F12 & F20 & F22).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
  unfold PMSP.cfg.
  apply (PMK.spiece_ro RSEGS model fx fx1 R 0x58ae8 R1 0xaba00 M K Mh Ml MS1).
  (* [comment removed for export] *)
  destruct (PMTK.fill_run fx1 R1 M (n0 + p) m 363520 F10 F12 F1 ltac:(split; [lia| reflexivity]) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(apply (L5C.writable_of_defined RSEGS M (n0 + p) m); [apply (L5.defined_sub M p c (n0 + p) m DP); lia|lia|lia])) as (R3 & M3 & MS3 & MG3 & FR3 & D3 & KS3 & _).
  set (P := fun a => n0 + p <= a < n0 + p + m).
  apply (PMK.spiece RSEGS L HI KL HIok ((p, c) :: LB) cr0 M model fx1 fx1 R1 0xaba00 R3 363520 M3 P K HH Mh Ml ltac:(destruct STOP; lia) MS3 MG3 FR3).
  { intros a Pa. unfold P in Pa. apply (PMK.cwr_block L ((p, c) :: LB) p c a ltac:(left; reflexivity)); lia. }
  { intros a. unfold P. apply PMK.rng_dec. }
  intros HH3.
  assert (KSR : forall x, In x L5K.CS -> getr R3 (reg x) = getr R1 (reg x)) by exact KS3.
  apply (finish_long fx1 R3 M3 model p c tg cr0 MOK).
  - rewrite (KSR 2%nat) by PMK.inl. rewrite (KS1 2%nat) by PMK.inl. exact A2.
  - rewrite (KSR 8%nat) by PMK.inl. rewrite (KS1 8%nat) by PMK.inl. exact A8.
  - rewrite (KSR 20%nat) by PMK.inl. exact F20.
  - rewrite (KSR 22%nat) by PMK.inl. rewrite F22. f_equal. lia.
  - intros x Hx. rewrite (KSR x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
    rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - apply (saves_keep M M3 P FR3); [intros a Ha X; unfold P in X; lia| lia| exact SV].
  - split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M3 EK); apply (PMK.ek_piece L LB S 14336 _ M M3 P FR3);
             intros a Ha CA NE OW Pa; unfold P in Pa;
             exact (PMSRS.own_not_client L HI HIok [(p, c)] LB cr0 M _ p c a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA)|].
    split; [apply (PMK.dk_trans L LB S 14336 M0 M M3 DK); apply PMK.dk_grows; exact MG3|].
    split; [exact (PMK.stk_grows L M M3 S 14336 MG3 STK)|]. intros i Hi. apply MG3. apply DO. exact Hi.
  - apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply FR3; [lia| unfold P; lia]|lia|lia|exact W0].
  - apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply FR3; [lia| unfold P; lia]|lia|lia|exact W16].
  - lia.
  - lia.
  - exact Hce.
  - intros i Hi. apply MG3. apply DP. exact Hi.
  - exact Hp0.
  - exact Hp1.
  - exact HH3.
  - exact MB.
  - rewrite Es in TBOK. unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK.
  - intros _. rewrite Es. split; reflexivity.
  - rewrite Es. unfold PMSP.credit_keep, PM.pot_text. cbn [PM.vs_cap]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma grow_store (fx : FPState) R M model (n0 m B A pc : Z) :
  PMSP.model_ok model -> n = n0 + m -> 1 <= m -> 0 <= n0 -> n < A -> 48 <= A <= 2 ^ 27 -> A mod 8 = 0 ->
  (pc = 0x58bdc \/ (pc = 0x58bc8 /\ getr R (reg 23) = Z_to_bv 64 22 /\ n0 <= 22 /\ getr R (reg 10) = Z_to_bv 64 B)) ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 m ->
  getr R (reg 18) = Z_to_bv 64 n0 -> getr R (reg 20) = Z_to_bv 64 B -> getr R (reg 21) = Z_to_bv 64 A -> getr R (reg 22) = Z_to_bv 64 n ->
  kept0 R -> saves M -> mem_ok M ->
  L5.defined M B A -> 4096 <= B -> B + A <= hl_ceil L ->
  hi_heap HI ((B, A) :: LB) (debit L cr0 A) M (m_vmmaps model) -> model_but_vm model0 model ->
  PM.tb_ok (PM.VLong A n B) (tg + 1) -> PM.vs_cap s < n ->
  PMSP.credit_keep cr0 (debit L cr0 A) (PM.pot_text L s tg) (PM.pot_text L (PM.VLong A n B) (tg + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc M model) K.
Proof.
  intros MOK En Hm Hn0 HnA HA HA8 PC A2 A8 A9 A18 A20 A21 A22 KP SV MO DB HB0 HB1 HH MB TBOK GROW CK.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
  assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as G10. change (bv_modulus 64) with (2 ^ 64) in G10.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as G24. change (bv_modulus 64) with (2 ^ 64) in G24.
  assert (A24 : getr R (reg 24) = Z_to_bv 64 (bv_unsigned (getr R (reg 24)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (A10' : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  assert (STORED : exists fx1 R1 M1, msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0xaba00) M1 (seg_rom RSEGS))
      /\ mem_grows M M1 /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 24) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
      /\ (forall x, In x [2; 3; 4; 8; 9; 18; 20; 21; 22; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
      /\ getr R1 (reg 1) = Z_to_bv 64 363520 /\ getr R1 (reg 10) = Z_to_bv 64 (n0 + B) /\ getr R1 (reg 12) = Z_to_bv 64 m
      /\ L5.u64_at RSEGS M1 (o + 16) B /\ L5.u64_at RSEGS M1 o (2 * (A / 2) + 1)).
  { destruct PC as [->|(-> & A23 & Hn022 & A10)].
    - LeanFeed.pfeed PP (PMSRZP.pF_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 38%nat => n | 40%nat => A | 41%nat => B
                    | 43%nat => m | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 24)) | _ => 0 end)) ltac:(first [PMK.sc]).
      destruct PP as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & KS1 & F1 & F10 & _ & F12 & C16 & _ & C0).
      exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros a Ha X; apply FR1; [exact Ha| lia]|].
      split; [intros x Hx; apply KS1; revert x Hx; apply sub_in; vm_compute; reflexivity|].
      split; [exact F1|]. split; [exact F10|]. split; [exact F12|]. split; [exact C16| exact C0].
    - LeanFeed.pfeed PP (PMSRZP.pDS_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 38%nat => n | 40%nat => A | 41%nat => B
                    | 43%nat => m | 56%nat => bv_unsigned (getr R (reg 24)) | _ => 0 end)) ltac:(first [PMK.sc]).
      destruct PP as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & KS1 & F1 & F10 & _ & F12 & C16 & _ & C0).
      exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros a Ha X; apply FR1; [exact Ha| lia]|].
      split; [intros x Hx; apply KS1; revert x Hx; apply sub_in; vm_compute; reflexivity|].
      split; [exact F1|]. split; [exact F10|]. split; [exact F12|]. split; [exact C16| exact C0]. }
  destruct STORED as (fx1 & R1 & M1 & MS1 & MG1 & FR1 & KS1 & F1 & F10 & F12 & C16 & C0).
  set (P1 := fun a => o <= a < o + 24).
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok ((B, A) :: LB) (debit L cr0 A) M model fx fx1 R pc R1 0xaba00 M1 P1 K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FR1).
  { intros a Pa. unfold P1 in Pa. apply (PMK.cwr_stack L ((B, A) :: LB) M S 14336 a STK); lia. }
  { intros a. unfold P1. apply PMK.rng_dec. }
  intros HH1.
  (* [comment removed for export] *)
  assert (DB1 : L5.defined M1 B A) by (intros i Hi; apply MG1; apply DB; exact Hi).
  destruct (PMTK.fill_run fx1 R1 M1 (n0 + B) m 363520 F10 F12 F1 ltac:(split; [lia| reflexivity]) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(apply (L5C.writable_of_defined RSEGS M1 (n0 + B) m); [apply (L5.defined_sub M1 B A (n0 + B) m DB1); lia|lia|lia])) as (R3 & M3 & MS3 & MG3 & FR3 & D3 & KS3 & _).
  set (P3 := fun a => n0 + B <= a < n0 + B + m).
  apply (PMK.spiece RSEGS L HI KL HIok ((B, A) :: LB) (debit L cr0 A) M1 model fx1 fx1 R1 0xaba00 R3 363520 M3 P3 K HH1 Mh Ml ltac:(destruct STOP; lia) MS3 MG3 FR3).
  { intros a Pa. unfold P3 in Pa. apply (PMK.cwr_block L ((B, A) :: LB) B A a ltac:(left; reflexivity)); lia. }
  { intros a. unfold P3. apply PMK.rng_dec. }
  intros HH3.
  assert (KSR : forall x, In x L5K.CS -> getr R3 (reg x) = getr R1 (reg x)) by exact KS3.
  assert (MG13 : mem_grows M M3) by (intros x D; apply MG3; apply MG1; exact D).
  assert (FR13 : forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 24) -> ~ (n0 + B <= a < n0 + B + m) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha X Y. rewrite FR3 by (exact Ha || exact Y). apply FR1; assumption. }
  apply (finish_long fx1 R3 M3 model B A (tg + 1) (debit L cr0 A) MOK).
  - rewrite (KSR 2%nat) by PMK.inl. rewrite (KS1 2%nat) by PMK.inl. exact A2.
  - rewrite (KSR 8%nat) by PMK.inl. rewrite (KS1 8%nat) by PMK.inl. exact A8.
  - rewrite (KSR 20%nat) by PMK.inl. rewrite (KS1 20%nat) by PMK.inl. exact A20.
  - rewrite (KSR 22%nat) by PMK.inl. rewrite (KS1 22%nat) by PMK.inl. exact A22.
  - intros x Hx. rewrite (KSR x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
    rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
    assert (AG : forall a, S - 80 <= a -> a + 8 <= S -> L5C.agree_on M M3 a 8).
    { intros a H1 H2 i Hi. apply FR13; lia. }
    unfold saves. repeat split; (eapply (L5C.u64_at_agree RSEGS M M3); [apply AG; lia|lia|lia|eassumption]).
  - split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M3 EK)|].
    { apply (PMK.ek_piece L LB S 14336 _ M M3 (fun a => (o <= a < o + 24) \/ (n0 + B <= a < n0 + B + m))).
      - intros a Ha X. apply FR13; [exact Ha| intro Y; apply X; left; exact Y| intro Y; apply X; right; exact Y].
      - intros a Ha CA NE OW [X|X].
        + apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        + exact (PMSRS.own_not_client L HI HIok [(B, A)] LB _ M _ B A a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA). }
    split; [apply (PMK.dk_trans L LB S 14336 M0 M M3 DK); apply PMK.dk_grows; exact MG13|].
    split; [exact (PMK.stk_grows L M M3 S 14336 MG13 STK)|]. intros i Hi. apply MG13. apply DO. exact Hi.
  - apply (L5C.u64_at_agree RSEGS M1 M3); [intros i Hi; apply FR3; [lia| unfold P3; lia]|lia|lia|].
    replace (A + 1) with (2 * (A / 2) + 1) by lia. exact C0.
  - apply (L5C.u64_at_agree RSEGS M1 M3); [intros i Hi; apply FR3; [lia| unfold P3; lia]|lia|lia|exact C16].
  - lia.
  - lia.
  - lia.
  - intros i Hi. apply MG3. apply DB1. exact Hi.
  - exact HB0.
  - exact HB1.
  - exact HH3.
  - exact MB.
  - exact TBOK.
  - intros X. exfalso. lia.
  - exact CK.
Qed.

(* [comment removed for export] *)
Lemma gan_short (fx : FPState) R M model (n0 m B A : Z) :
  PMSP.model_ok model -> s = PM.VShort n0 -> n = n0 + m -> 1 <= m -> 0 <= n0 <= 22 -> n < A -> 48 <= A <= 2 ^ 27 -> A mod 8 = 0 ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 m -> getr R (reg 10) = Z_to_bv 64 B ->
  getr R (reg 18) = Z_to_bv 64 n0 -> getr R (reg 19) = Z_to_bv 64 (o + 1) -> getr R (reg 21) = Z_to_bv 64 A -> getr R (reg 22) = Z_to_bv 64 n ->
  getr R (reg 23) = Z_to_bv 64 22 ->
  kept0 R -> saves M -> mem_ok M ->
  L5.defined M B A -> 4096 <= B -> B + A <= hl_ceil L ->
  hi_heap HI ((B, A) :: LB) (debit L cr0 A) M (m_vmmaps model) -> model_but_vm model0 model ->
  PM.tb_ok (PM.VLong A n B) (tg + 1) -> PM.vs_cap s < n ->
  PMSP.credit_keep cr0 (debit L cr0 A) (PM.pot_text L s tg) (PM.pot_text L (PM.VLong A n B) (tg + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x58bb0 M model) K.
Proof.
  intros MOK Es En Hm Hn0 HnA HA HA8 A2 A8 A9 A10 A18 A19 A21 A22 A23 KP SV MO DB HB0 HB1 HH MB TBOK GROW CK.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  LeanFeed.pfeed PP (PMSRZP.pN_conc fx R M (fun j => match j with 2%nat => S | 34%nat => n0 | 41%nat => B | 42%nat => o + 1 | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & EX).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
  assert (MODE : (n0 - 0) mod 2 ^ 64 = n0) by (rewrite Z.sub_0_r; apply Z.mod_small; lia).
  unfold PMSP.cfg.
  destruct EX as [(MS1 & KS1 & F1 & F11 & F12 & F20 & F)|(MS1 & KS1 & F20 & F)]; rewrite MODE in F.
  - (* [comment removed for export] *)
    apply (PMK.spiece_ro RSEGS model fx fx1 R 0x58bb0 R1 0xab884 M K Mh Ml MS1).
    assert (F10 : getr R1 (reg 10) = Z_to_bv 64 B) by (rewrite (KS1 10%nat) by PMK.inl; exact A10).
    destruct (PMCPS.memmove_run fx1 R1 M B (o + 1) n0 363464 F10 F11 F12 F1 ltac:(split; [lia| reflexivity]) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(apply (L5C.writable_of_defined RSEGS M B n0); [apply (L5.defined_sub M B A B n0 DB); lia|lia|lia])
                ltac:(apply (L5.defined_sub M o 24 (o + 1) n0 DO); lia)) as (R3 & M3 & MS3 & MG3 & FR3 & D3 & KS3 & R3_10).
    set (P3 := fun a => B <= a < B + n0).
    apply (PMK.spiece RSEGS L HI KL HIok ((B, A) :: LB) (debit L cr0 A) M model fx1 fx1 R1 0xab884 R3 363464 M3 P3 K HH Mh Ml ltac:(destruct STOP; lia) MS3 MG3 FR3).
    { intros a Pa. unfold P3 in Pa. apply (PMK.cwr_block L ((B, A) :: LB) B A a ltac:(left; reflexivity)); lia. }
    { intros a. unfold P3. apply PMK.rng_dec. }
    intros HH3.
    assert (KSR : forall x, In x L5K.CS -> getr R3 (reg x) = getr R1 (reg x)) by exact KS3.
    apply (grow_store fx1 R3 M3 model n0 m B A 0x58bc8 MOK En Hm ltac:(lia) HnA HA HA8).
    + right. split; [reflexivity|]. split; [rewrite (KSR 23%nat) by PMK.inl; rewrite (KS1 23%nat) by PMK.inl; exact A23|]. split; [lia| exact R3_10].
    + rewrite (KSR 2%nat) by PMK.inl. rewrite (KS1 2%nat) by PMK.inl. exact A2.
    + rewrite (KSR 8%nat) by PMK.inl. rewrite (KS1 8%nat) by PMK.inl. exact A8.
    + rewrite (KSR 9%nat) by PMK.inl. rewrite (KS1 9%nat) by PMK.inl. exact A9.
    + rewrite (KSR 18%nat) by PMK.inl. rewrite (KS1 18%nat) by PMK.inl. exact A18.
    + rewrite (KSR 20%nat) by PMK.inl. exact F20.
    + rewrite (KSR 21%nat) by PMK.inl. rewrite (KS1 21%nat) by PMK.inl. exact A21.
    + rewrite (KSR 22%nat) by PMK.inl. rewrite (KS1 22%nat) by PMK.inl. exact A22.
    + intros x Hx. rewrite (KSR x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
      rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
    + apply (saves_keep M M3 P3 FR3); [intros a Ha X; unfold P3 in X; lia| lia| exact SV].
    + split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M3 EK); apply (PMK.ek_piece L LB S 14336 _ M M3 P3 FR3);
               intros a Ha CA NE OW Pa; unfold P3 in Pa;
               exact (PMSRS.own_not_client L HI HIok [(B, A)] LB _ M _ B A a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA)|].
      split; [apply (PMK.dk_trans L LB S 14336 M0 M M3 DK); apply PMK.dk_grows; exact MG3|].
      split; [exact (PMK.stk_grows L M M3 S 14336 MG3 STK)|]. intros i Hi. apply MG3. apply DO. exact Hi.
    + intros i Hi. apply MG3. apply DB. exact Hi.
    + exact HB0.
    + exact HB1.
    + exact HH3.
    + exact MB.
    + exact TBOK.
    + exact GROW.
    + exact CK.
  - (* [comment removed for export] *)
    apply (PMK.spiece_ro RSEGS model fx fx1 R 0x58bb0 R1 0x58bc8 M K Mh Ml MS1).
    assert (En0 : n0 = 0) by lia.
    apply (grow_store fx1 R1 M model n0 m B A 0x58bc8 MOK En Hm ltac:(lia) HnA HA HA8).
    + right. split; [reflexivity|]. split; [rewrite (KS1 23%nat) by PMK.inl; exact A23|]. split; [lia| rewrite (KS1 10%nat) by PMK.inl; rewrite A10; f_equal; lia].
    + rewrite (KS1 2%nat) by PMK.inl. exact A2.
    + rewrite (KS1 8%nat) by PMK.inl. exact A8.
    + rewrite (KS1 9%nat) by PMK.inl. exact A9.
    + rewrite (KS1 18%nat) by PMK.inl. exact A18.
    + exact F20.
    + rewrite (KS1 21%nat) by PMK.inl. exact A21.
    + rewrite (KS1 22%nat) by PMK.inl. exact A22.
    + intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
    + exact SV.
    + exact MO.
    + exact DB.
    + exact HB0.
    + exact HB1.
    + exact HH.
    + exact MB.
    + exact TBOK.
    + exact GROW.
    + exact CK.
Qed.

(* [comment removed for export] *)
Lemma gan_long_del (fx : FPState) R M model (c n0 p m B A : Z) :
  PMSP.model_ok model -> n = n0 + m -> 1 <= m -> 0 <= n0 -> n < A -> 48 <= A <= 2 ^ 27 -> A mod 8 = 0 -> 26 <= c <= 2 ^ 27 ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 m ->
  getr R (reg 18) = Z_to_bv 64 n0 -> getr R (reg 19) = Z_to_bv 64 p -> getr R (reg 20) = Z_to_bv 64 B -> getr R (reg 21) = Z_to_bv 64 A ->
  getr R (reg 22) = Z_to_bv 64 n -> getr R (reg 23) = Z_to_bv 64 (c - 1) ->
  kept0 R -> saves M -> mem_ok M ->
  L5.defined M B A -> 4096 <= B -> B + A <= hl_ceil L -> 4096 <= p -> p + c <= hl_ceil L -> B <> p ->
  hi_heap HI ((B, A) :: (p, c) :: LB) (debit L cr0 A) M (m_vmmaps model) -> model_but_vm model0 model ->
  PM.tb_ok (PM.VLong A n B) (tg + 1) -> PM.vs_cap s < n ->
  PMSP.credit_keep cr0 (debit L cr0 A) (PM.pot_text L s tg) (PM.pot_text L (PM.VLong A n B) (tg + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x58bc8 M model) K.
Proof.
  intros MOK En Hm Hn0 HnA HA HA8 Hc A2 A8 A9 A18 A19 A20 A21 A22 A23 KP SV MO DB HB0 HB1 Hp0 Hp1 NBp HH MB TBOK GROW CK.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  LeanFeed.pfeed PP (PMSRZP.pDL_conc fx R M (fun j => match j with 2%nat => S | 37%nat => c - 1 | 42%nat => p | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & MS1 & KS1 & F1 & F10 & _).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
  unfold PMSP.cfg.
  apply (PMK.spiece_ro RSEGS model fx fx1 R 0x58bc8 R1 0x56720 M K Mh Ml MS1).
  (* [comment removed for export] *)
  set (LBc := (B, A) :: (p, c) :: LB).
  assert (Ip : In (p, c) LBc) by (right; left; reflexivity).
  assert (ELB : lb_remove p LBc = (B, A) :: LB).
  { unfold LBc. cbn [lb_remove fst]. destruct (Z.eqb_spec B p) as [X|_]; [exfalso; exact (NBp X)|]. rewrite Z.eqb_refl. reflexivity. }
  assert (STKd : L5C.stk (hl_sptop L) M (S - 80) PMSP.OPDEL_SCR).
  { apply (PMK.stk_call L M S 14336 (S - 80) PMSP.OPDEL_SCR STK); [lia| unfold PMSP.OPDEL_SCR; lia| unfold PMSP.OPDEL_SCR; lia|].
    replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  unfold PMS.opdel_spec, PMSP.opdel_spec, PMSP.opdel_spec_at in OPD. cbn [pa_opdel AD] in OPD.
  apply (OPD fx1 R1 M model K LBc (debit L cr0 A) p c (S - 80) 363484 HH MOK K0 Ip).
  { rewrite L5K.rl10. exact F10. }
  { rewrite L5K.rl1. exact F1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. rewrite (KS1 2%nat) by PMK.inl. exact A2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by PMK.inl. rewrite (KP 4%nat) by (cbn; auto). exact Rtp0. }
  { exact STKd. }
  intros fx4 R4 M4 model4 RP4 HP4 MB4 HH4. rewrite ELB in HP4, HH4.
  assert (C4 : forall x, In x [2; 8; 9; 18; 20; 21; 22]%nat -> getr R4 (reg x) = getr R (reg x)).
  { intros x Hx. rewrite (PMK.cs_of_preserved R1 R4 x RP4) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
    apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity. }
  assert (BRc : PMFR.brange L ((B, A) :: LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M4 _ HH4); apply incl_refl).
  assert (EKd : PMK.ek L ((B, A) :: LB) (S - 80) PMSP.OPDEL_SCR [] M M4) by (apply (PMK.ek_of_hpres L); exact HP4).
  assert (SC0 : 0 <= PMSP.OPDEL_SCR) by (unfold PMSP.OPDEL_SCR; lia).
  assert (WHI : forall a, PMK.inW [] a -> S - 80 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
  assert (MOK4 : PMSP.model_ok model4) by (apply (PMFR.model_ok_but_vm model model4 MOK MB4)).
  apply (grow_store fx4 R4 M4 model4 n0 m B A 0x58bdc MOK4 En Hm Hn0 HnA HA HA8 (or_introl eq_refl)).
  - rewrite (C4 2%nat) by PMK.inl. exact A2.
  - rewrite (C4 8%nat) by PMK.inl. exact A8.
  - rewrite (C4 9%nat) by PMK.inl. exact A9.
  - rewrite (C4 18%nat) by PMK.inl. exact A18.
  - rewrite (C4 20%nat) by PMK.inl. exact A20.
  - rewrite (C4 21%nat) by PMK.inl. exact A21.
  - rewrite (C4 22%nat) by PMK.inl. exact A22.
  - intros x Hx. rewrite (PMK.cs_of_preserved R1 R4 x RP4) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
    rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
    unfold saves. repeat split; (apply (PMFR.u64_keep RSEGS L KL ((B, A) :: LB) (S - 80) PMSP.OPDEL_SCR [] M M4 EKd STKd SC0);
                                 [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| eassumption]).
  - split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M4 EK)|].
    { apply (PMK.ek_callee_in' RSEGS L KL LB ((B, A) :: LB) S 14336 (S - 80) PMSP.OPDEL_SCR [(o, 24)] [] M M4 HP4); [intros x Hx; right; exact Hx
        | unfold PMSP.OPDEL_SCR; lia| lia| lia| destruct STOP; lia| intros b Hb; apply (PMFR.brange_hi L _ BRc b); right; exact Hb| intros a I; destruct (PMFR.inW_nil a I)]. }
    split; [apply (PMK.dk_trans L LB S 14336 M0 M M4 DK);
            apply (PMK.dk_callee L LB ((B, A) :: LB) S 14336 (S - 80) PMSP.OPDEL_SCR [] M M4 HP4); [intros x Hx; right; exact Hx| unfold PMSP.OPDEL_SCR; lia| lia]|].
    split; [apply (PMK.stk_after RSEGS L KL ((B, A) :: LB) M M4 S 14336 (S - 80) PMSP.OPDEL_SCR [] STK HP4); unfold PMSP.OPDEL_SCR; lia|].
    apply (PMFR.defined_keep RSEGS L KL ((B, A) :: LB) (S - 80) PMSP.OPDEL_SCR [] M M4 EKd STKd SC0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact DO].
  - apply (L5C.defined_agree M M4 B A); [apply (PMFR.ag_block RSEGS L KL ((B, A) :: LB) (S - 80) PMSP.OPDEL_SCR [] M M4 EKd STKd SC0 BRc WHI); left; reflexivity| exact DB].
  - exact HB0.
  - exact HB1.
  - exact HH4.
  - exact (L5C.model_but_vm_trans _ _ _ MB MB4).
  - exact TBOK.
  - exact GROW.
  - exact CK.
Qed.

(* [comment removed for export] *)
Lemma gan_long (fx : FPState) R M model (c n0 p m B A : Z) :
  PMSP.model_ok model -> n = n0 + m -> 1 <= m -> 0 <= n0 < c -> n < A -> 48 <= A <= 2 ^ 27 -> A mod 8 = 0 -> 26 <= c <= 2 ^ 27 ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 m -> getr R (reg 10) = Z_to_bv 64 B ->
  getr R (reg 18) = Z_to_bv 64 n0 -> getr R (reg 19) = Z_to_bv 64 p -> getr R (reg 21) = Z_to_bv 64 A ->
  getr R (reg 22) = Z_to_bv 64 n -> getr R (reg 23) = Z_to_bv 64 (c - 1) ->
  kept0 R -> saves M -> mem_ok M ->
  L5.defined M B A -> 4096 <= B -> B + A <= hl_ceil L -> L5.defined M p c -> 4096 <= p -> p + c <= hl_ceil L -> (B + A <= p \/ p + c <= B) ->
  hi_heap HI ((B, A) :: (p, c) :: LB) (debit L cr0 A) M (m_vmmaps model) -> model_but_vm model0 model ->
  PM.tb_ok (PM.VLong A n B) (tg + 1) -> PM.vs_cap s < n ->
  PMSP.credit_keep cr0 (debit L cr0 A) (PM.pot_text L s tg) (PM.pot_text L (PM.VLong A n B) (tg + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x58bb0 M model) K.
Proof.
  intros MOK En Hm Hn0 HnA HA HA8 Hc A2 A8 A9 A10 A18 A19 A21 A22 A23 KP SV MO DB HB0 HB1 DP Hp0 Hp1 ABp HH MB TBOK GROW CK.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  assert (NBp : B <> p) by lia.
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  LeanFeed.pfeed PP (PMSRZP.pN_conc fx R M (fun j => match j with 2%nat => S | 34%nat => n0 | 41%nat => B | 42%nat => p | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & EX).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
  assert (MODE : (n0 - 0) mod 2 ^ 64 = n0) by (rewrite Z.sub_0_r; apply Z.mod_small; lia).
  unfold PMSP.cfg.
  destruct EX as [(MS1 & KS1 & F1 & F11 & F12 & F20 & F)|(MS1 & KS1 & F20 & F)]; rewrite MODE in F.
  - apply (PMK.spiece_ro RSEGS model fx fx1 R 0x58bb0 R1 0xab884 M K Mh Ml MS1).
    assert (F10 : getr R1 (reg 10) = Z_to_bv 64 B) by (rewrite (KS1 10%nat) by PMK.inl; exact A10).
    destruct (PMCPS.memmove_run fx1 R1 M B p n0 363464 F10 F11 F12 F1 ltac:(split; [lia| reflexivity]) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(apply (L5C.writable_of_defined RSEGS M B n0); [apply (L5.defined_sub M B A B n0 DB); lia|lia|lia])
                ltac:(apply (L5.defined_sub M p c p n0 DP); lia)) as (R3 & M3 & MS3 & MG3 & FR3 & D3 & KS3 & R3_10).
    set (P3 := fun a => B <= a < B + n0).
    apply (PMK.spiece RSEGS L HI KL HIok ((B, A) :: (p, c) :: LB) (debit L cr0 A) M model fx1 fx1 R1 0xab884 R3 363464 M3 P3 K HH Mh Ml ltac:(destruct STOP; lia) MS3 MG3 FR3).
    { intros a Pa. unfold P3 in Pa. apply (PMK.cwr_block L ((B, A) :: (p, c) :: LB) B A a ltac:(left; reflexivity)); lia. }
    { intros a. unfold P3. apply PMK.rng_dec. }
    intros HH3.
    assert (KSR : forall x, In x L5K.CS -> getr R3 (reg x) = getr R1 (reg x)) by exact KS3.
    apply (gan_long_del fx1 R3 M3 model c n0 p m B A MOK En Hm ltac:(lia) HnA HA HA8 Hc).
    + rewrite (KSR 2%nat) by PMK.inl. rewrite (KS1 2%nat) by PMK.inl. exact A2.
    + rewrite (KSR 8%nat) by PMK.inl. rewrite (KS1 8%nat) by PMK.inl. exact A8.
    + rewrite (KSR 9%nat) by PMK.inl. rewrite (KS1 9%nat) by PMK.inl. exact A9.
    + rewrite (KSR 18%nat) by PMK.inl. rewrite (KS1 18%nat) by PMK.inl. exact A18.
    + rewrite (KSR 19%nat) by PMK.inl. rewrite (KS1 19%nat) by PMK.inl. exact A19.
    + rewrite (KSR 20%nat) by PMK.inl. exact F20.
    + rewrite (KSR 21%nat) by PMK.inl. rewrite (KS1 21%nat) by PMK.inl. exact A21.
    + rewrite (KSR 22%nat) by PMK.inl. rewrite (KS1 22%nat) by PMK.inl. exact A22.
    + rewrite (KSR 23%nat) by PMK.inl. rewrite (KS1 23%nat) by PMK.inl. exact A23.
    + intros x Hx. rewrite (KSR x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
      rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
    + apply (saves_keep M M3 P3 FR3); [intros a Ha X; unfold P3 in X; lia| lia| exact SV].
    + split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M3 EK); apply (PMK.ek_piece L LB S 14336 _ M M3 P3 FR3);
               intros a Ha CA NE OW Pa; unfold P3 in Pa;
               exact (PMSRS.own_not_client L HI HIok [(B, A); (p, c)] LB _ M _ B A a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA)|].
      split; [apply (PMK.dk_trans L LB S 14336 M0 M M3 DK); apply PMK.dk_grows; exact MG3|].
      split; [exact (PMK.stk_grows L M M3 S 14336 MG3 STK)|]. intros i Hi. apply MG3. apply DO. exact Hi.
    + intros i Hi. apply MG3. apply DB. exact Hi.
    + exact HB0.
    + exact HB1.
    + exact Hp0.
    + exact Hp1.
    + exact NBp.
    + exact HH3.
    + exact MB.
    + exact TBOK.
    + exact GROW.
    + exact CK.
  - apply (PMK.spiece_ro RSEGS model fx fx1 R 0x58bb0 R1 0x58bc8 M K Mh Ml MS1).
    apply (gan_long_del fx1 R1 M model c n0 p m B A MOK En Hm ltac:(lia) HnA HA HA8 Hc).
    + rewrite (KS1 2%nat) by PMK.inl. exact A2.
    + rewrite (KS1 8%nat) by PMK.inl. exact A8.
    + rewrite (KS1 9%nat) by PMK.inl. exact A9.
    + rewrite (KS1 18%nat) by PMK.inl. exact A18.
    + rewrite (KS1 19%nat) by PMK.inl. exact A19.
    + exact F20.
    + rewrite (KS1 21%nat) by PMK.inl. exact A21.
    + rewrite (KS1 22%nat) by PMK.inl. exact A22.
    + rewrite (KS1 23%nat) by PMK.inl. exact A23.
    + intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
    + exact SV.
    + exact MO.
    + exact DB.
    + exact HB0.
    + exact HB1.
    + exact Hp0.
    + exact Hp1.
    + exact NBp.
    + exact HH.
    + exact MB.
    + exact TBOK.
    + exact GROW.
    + exact CK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grow_credit (s' : PM.vstr) (A : Z) :
  PM.tb_ok s tg -> PM.vs_cap s <= 2 ^ 27 -> 2 * PM.vs_cap s <= PM.vs_cap s' -> PM.vs_cap s' = A - 1 -> A <= 2 ^ 27 ->
  PMSP.credit_le (PM.pot_text L s tg) cr0 ->
  credit_ok L cr0 A /\ PMSP.credit_keep cr0 (debit L cr0 A) (PM.pot_text L s tg) (PM.pot_text L s' (tg + 1)) /\ tg <= 22.
Proof.
  intros (T0 & T1 & _) Hc Hc' Ec HA (CR1 & CR2).
  pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB.
  assert (Htg : tg <= 22).
  { destruct (Z.eq_dec tg 23) as [E|N]; [|lia]. rewrite E in T1. change (2 ^ 23) with 8388608 in T1. lia. }
  pose proof (PMF.pot_text_step L s s' tg Hc') as (P1 & P2).
  unfold PM.credit_add, PM.cost1, PM.pot_text in P1, P2, CR1, CR2 |- *. cbn [fst snd] in P1, P2, CR1, CR2 |- *. rewrite ?Ec in P1, P2 |- *.
  split; [unfold credit_ok; split; nia|]. split; [|exact Htg].
  unfold PMSP.credit_keep, debit. cbn [fst snd]. split; nia.
Qed.

Lemma grow_short (fx : FPState) R M model (n0 m : Z) :
  PMSP.model_ok model -> s = PM.VShort n0 -> n = n0 + m -> 1 <= m -> 22 < n -> 0 <= n0 <= 22 -> PM.tb_ok s tg ->
  PMSP.credit_le (PM.pot_text L s tg) cr0 ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 m -> getr R (reg 10) = Z_to_bv 64 0 ->
  getr R (reg 18) = Z_to_bv 64 n0 -> getr R (reg 23) = Z_to_bv 64 22 ->
  kept0 R -> saves M -> mem_ok M ->
  hi_heap HI LB cr0 M (m_vmmaps model) -> model_but_vm model0 model ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x58b10 M model) K.
Proof.
  intros MOK Es En Hm Hn Hn0 TBOK CR A2 A8 A9 A10 A18 A23 KP SV MO HH MB.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
  assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
  assert (Hn1' : n <= 22 + 16384) by (rewrite Es in Hn1; cbn [PM.vs_size] in Hn1; unfold PM.CHUNK in Hn1; lia).
  set (A := Z.lor (Z.max 44 n) 7 + 1).
  destruct (PMF.tb_law_first n A ltac:(lia) Hn1' eq_refl) as (LAW & LA1 & LA2 & LA3 & LA4).
  assert (EA : A = 8 * (Z.max 44 n / 8) + 8) by (unfold A; apply PMF.lor7; lia).
  (* [comment removed for export] *)
  assert (REQ : exists fx2 R2, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x58b10) M (seg_rom RSEGS)) (@mkst fx2 R2 (Z_to_bv 64 0xb03b8) M (seg_rom RSEGS))
     /\ getr R2 (reg 1) = Z_to_bv 64 363440 /\ getr R2 (reg 10) = Z_to_bv 64 A /\ getr R2 (reg 19) = Z_to_bv 64 (o + 1) /\ getr R2 (reg 21) = Z_to_bv 64 A
     /\ getr R2 (reg 22) = Z_to_bv 64 n /\ (forall x, In x [2; 3; 4; 8; 9; 18; 23; 25; 26; 27]%nat -> getr R2 (reg x) = getr R (reg x))).
  { LeanFeed.pfeed PP (PMSRZP.growS_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 43%nat => m | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & EX).
    assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    assert (MODE : (n0 + m) mod 2 ^ 64 = n) by (rewrite Z.mod_small; lia).
    destruct EX as [(MS1 & KS1 & F10 & F11 & _ & F19 & F21 & F22 & F)|(MS1 & KS1 & F1 & F10 & _ & _ & F19 & F21 & F22 & _ & F)]; rewrite MODE in F.
    - idtac.
      assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by PMK.inl; exact A2).
      LeanFeed.pfeed PQ (PMSRZP.rec_conc fx1 R1 M (fun j => match j with 2%nat => S | 39%nat => n0 + m | 40%nat => 8 * ((n0 + m) / 8) + 7 | _ => 0 end)) ltac:(first [PMK.sc]).
      destruct PQ as (fx2 & R2 & M2 & MG2 & FRw2 & _ & MS2 & KS2 & G1 & G10 & G21 & _).
      assert (EM : M2 = M) by (apply functional_extensionality; exact FRw2). subst M2.
      assert (EA' : 8 * ((n0 + m) / 8) + 7 + 1 = A) by (rewrite EA, Z.max_r by lia; rewrite <- En; lia).
      exists fx2, R2. split; [eapply msteps_trans; [exact MS1| exact MS2]|].
      split; [exact G1|]. split; [rewrite G10, EA'; reflexivity|]. split; [rewrite (KS2 19%nat) by PMK.inl; exact F19|].
      split; [rewrite G21, EA'; reflexivity|]. split; [rewrite (KS2 22%nat) by PMK.inl; rewrite F22, En; reflexivity|].
      intros x Hx. rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
    - exists fx1, R1. split; [exact MS1|]. assert (EA' : A = 48) by (rewrite EA, Z.max_l by lia; reflexivity).
      split; [exact F1|]. split; [rewrite F10, EA'; reflexivity|]. split; [exact F19|]. split; [rewrite F21, EA'; reflexivity|].
      split; [rewrite F22, En; reflexivity|].
      intros x Hx. apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity. }
  destruct REQ as (fx2 & R2 & MS2 & B1 & B10 & B19 & B21 & B22 & KS2).
  unfold PMSP.cfg.
  apply (PMK.spiece_ro RSEGS model fx fx2 R 0x58b10 R2 0xb03b8 M K Mh Ml MS2).
  (* [comment removed for export] *)
  destruct (grow_credit (PM.VLong A n 0) A TBOK ltac:(rewrite Es; cbn; lia) ltac:(rewrite Es; cbn; lia) eq_refl LA3 CR) as (CROK & CK & Htg).
  assert (STKn : L5C.stk (hl_sptop L) M (S - 80) PMSP.OPNEW_SCR).
  { apply (PMK.stk_call L M S 14336 (S - 80) PMSP.OPNEW_SCR STK); [lia| unfold PMSP.OPNEW_SCR; lia| unfold PMSP.OPNEW_SCR; lia|].
    replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  unfold PMS.opnew_spec, PMSP.opnew_spec in OPN. cbn [pa_opnew AD] in OPN.
  apply (OPN fx2 R2 M model K LB cr0 A (S - 80) 363440 HH MOK K0).
  { rewrite L5K.rl10. exact B10. }
  { lia. }
  { exact CROK. }
  { rewrite L5K.rl1. exact B1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. rewrite (KS2 2%nat) by PMK.inl. exact A2. }
  { rewrite L5K.rl4. rewrite (KS2 4%nat) by PMK.inl. rewrite (KP 4%nat) by (cbn; auto). exact Rtp0. }
  { exact STKn. }
  intros fx3 R3 M3 model3 B R3_10 RP3 FB HP3 MB3 HH3. rewrite L5K.rl10 in R3_10.
  destruct FB as ((FB0 & FB1 & FB2 & FB3 & FB4) & FBa & FBd).
  assert (C3 : forall x, In x [2; 8; 9; 18; 19; 21; 22; 23]%nat -> getr R3 (reg x) = getr R2 (reg x)).
  { intros x Hx. apply (PMK.cs_of_preserved R2 R3 x RP3). revert x Hx. apply sub_in. vm_compute. reflexivity. }
  assert (EKn : PMK.ek L LB (S - 80) PMSP.OPNEW_SCR [] M M3) by (apply (PMK.ek_of_hpres L); exact HP3).
  assert (SC0 : 0 <= PMSP.OPNEW_SCR) by (unfold PMSP.OPNEW_SCR; lia).
  assert (BRX : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok _ LB cr0 M _ HH); apply incl_refl).
  assert (MOK3 : PMSP.model_ok model3) by (apply (PMFR.model_ok_but_vm model model3 MOK MB3)).
  apply (gan_short fx3 R3 M3 model3 n0 m B A MOK3 Es En Hm Hn0 ltac:(lia) ltac:(lia) LA4).
  - rewrite (C3 2%nat) by PMK.inl. rewrite (KS2 2%nat) by PMK.inl. exact A2.
  - rewrite (C3 8%nat) by PMK.inl. rewrite (KS2 8%nat) by PMK.inl. exact A8.
  - rewrite (C3 9%nat) by PMK.inl. rewrite (KS2 9%nat) by PMK.inl. exact A9.
  - exact R3_10.
  - rewrite (C3 18%nat) by PMK.inl. rewrite (KS2 18%nat) by PMK.inl. exact A18.
  - rewrite (C3 19%nat) by PMK.inl. exact B19.
  - rewrite (C3 21%nat) by PMK.inl. exact B21.
  - rewrite (C3 22%nat) by PMK.inl. exact B22.
  - rewrite (C3 23%nat) by PMK.inl. rewrite (KS2 23%nat) by PMK.inl. exact A23.
  - intros x Hx. rewrite (PMK.cs_of_preserved R2 R3 x RP3) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
    rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
    unfold saves. repeat split; (apply (PMFR.u64_keep RSEGS L KL LB (S - 80) PMSP.OPNEW_SCR [] M M3 EKn STKn SC0);
                                 [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| eassumption]).
  - split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M3 EK)|].
    { apply (PMK.ek_callee_in' RSEGS L KL LB LB S 14336 (S - 80) PMSP.OPNEW_SCR [(o, 24)] [] M M3 HP3 (incl_refl _));
        [unfold PMSP.OPNEW_SCR; lia| lia| lia| destruct STOP; lia| exact (PMFR.brange_hi L LB BRX)| intros a I; destruct (PMFR.inW_nil a I)]. }
    split; [apply (PMK.dk_trans L LB S 14336 M0 M M3 DK);
            apply (PMK.dk_callee L LB LB S 14336 (S - 80) PMSP.OPNEW_SCR [] M M3 HP3 (incl_refl _)); [unfold PMSP.OPNEW_SCR; lia| lia]|].
    split; [apply (PMK.stk_after RSEGS L KL LB M M3 S 14336 (S - 80) PMSP.OPNEW_SCR [] STK HP3); unfold PMSP.OPNEW_SCR; lia|].
    apply (PMFR.defined_keep RSEGS L KL LB (S - 80) PMSP.OPNEW_SCR [] M M3 EKn STKn SC0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact DO].
  - exact FBd.
  - exact FB0.
  - exact FB4.
  - exact HH3.
  - exact (L5C.model_but_vm_trans _ _ _ MB MB3).
  - assert (Etg : tg = 0) by (rewrite Es in TBOK; destruct TBOK as (_ & _ & X); exact X).
    rewrite Etg. split; [lia|]. split; [cbn; lia|]. split; [exact LAW| lia].
  - rewrite Es. cbn. lia.
  - rewrite Es in CK |- *. exact CK.
Qed.

Lemma grow_long (fx : FPState) R M model (c n0 p m : Z) :
  PMSP.model_ok model -> s = PM.VLong c n0 p -> n = n0 + m -> 1 <= m -> c - 1 < n -> 0 <= n0 < c -> PM.tb_ok s tg ->
  26 <= c <= 2 ^ 27 -> c mod 2 = 0 -> L5.u64_at RSEGS M (o + 16) p -> L5.defined M p c -> 4096 <= p -> p + c <= hl_ceil L ->
  PMSP.credit_le (PM.pot_text L s tg) cr0 ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 m -> getr R (reg 10) = Z_to_bv 64 1 ->
  getr R (reg 18) = Z_to_bv 64 n0 -> getr R (reg 23) = Z_to_bv 64 (c - 1) ->
  kept0 R -> saves M -> mem_ok M ->
  hi_heap HI ((p, c) :: LB) cr0 M (m_vmmaps model) -> model_but_vm model0 model ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x58b10 M model) K.
Proof.
  intros MOK Es En Hm Hn Hn0 TBOK Hc Hce W16 DP Hp0 Hp1 CR A2 A8 A9 A10 A18 A23 KP SV MO HH MB.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
  assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
  assert (Hn1' : n <= c - 1 + 16384) by (rewrite Es in Hn1; cbn [PM.vs_size] in Hn1; unfold PM.CHUNK in Hn1; lia).
  assert (TLAW : PM.tb_law c) by (rewrite Es in TBOK; destruct TBOK as (_ & _ & X & _); exact X).
  set (A := Z.lor (Z.max (2 * (c - 1)) n) 7 + 1).
  destruct (PMF.tb_law_step c n A TLAW ltac:(lia) ltac:(lia) Hn1' ltac:(lia) eq_refl) as (LAW & LA1 & LA2 & LA3 & LA4).
  assert (EA : A = 8 * (Z.max (2 * (c - 1)) n / 8) + 8) by (unfold A; apply PMF.lor7; lia).
  (* [comment removed for export] *)
  assert (REQ : exists fx2 R2, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x58b10) M (seg_rom RSEGS)) (@mkst fx2 R2 (Z_to_bv 64 0xb03b8) M (seg_rom RSEGS))
     /\ getr R2 (reg 1) = Z_to_bv 64 363440 /\ getr R2 (reg 10) = Z_to_bv 64 A /\ getr R2 (reg 19) = Z_to_bv 64 p /\ getr R2 (reg 21) = Z_to_bv 64 A
     /\ getr R2 (reg 22) = Z_to_bv 64 n /\ (forall x, In x [2; 3; 4; 8; 9; 18; 23; 25; 26; 27]%nat -> getr R2 (reg x) = getr R (reg x))).
  { LeanFeed.pfeed PP (PMSRZP.growL_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 35%nat => p | 37%nat => c - 1 | 43%nat => m | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & EX).
    assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    assert (MODE : (n0 + m) mod 2 ^ 64 = n) by (rewrite Z.mod_small; lia).
    assert (MODC : (2 * (c - 1)) mod 2 ^ 64 = 2 * (c - 1)) by (rewrite Z.mod_small; lia).
    destruct EX as [(MS1 & KS1 & F10 & F11 & _ & F19 & F21 & F22 & F)|(MS1 & KS1 & F1 & F10 & _ & _ & F19 & F21 & F22 & _ & F)]; rewrite MODE, MODC in F.
    - idtac.
      assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by PMK.inl; exact A2).
      LeanFeed.pfeed PQ (PMSRZP.rec_conc fx1 R1 M (fun j => match j with 2%nat => S | 39%nat => n0 + m | 40%nat => 8 * ((n0 + m) / 8) + 7 | _ => 0 end)) ltac:(first [PMK.sc]).
      destruct PQ as (fx2 & R2 & M2 & MG2 & FRw2 & _ & MS2 & KS2 & G1 & G10 & G21 & _).
      assert (EM : M2 = M) by (apply functional_extensionality; exact FRw2). subst M2.
      assert (EA' : 8 * ((n0 + m) / 8) + 7 + 1 = A) by (rewrite EA, Z.max_r by lia; rewrite <- En; lia).
      exists fx2, R2. split; [eapply msteps_trans; [exact MS1| exact MS2]|].
      split; [exact G1|]. split; [rewrite G10, EA'; reflexivity|]. split; [rewrite (KS2 19%nat) by PMK.inl; exact F19|].
      split; [rewrite G21, EA'; reflexivity|]. split; [rewrite (KS2 22%nat) by PMK.inl; rewrite F22, En; reflexivity|].
      intros x Hx. rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
    - exists fx1, R1. split; [exact MS1|]. assert (EA' : A = 8 * ((2 * (c - 1)) / 8) + 8) by (rewrite EA, Z.max_l by lia; reflexivity).
      split; [exact F1|]. split; [rewrite F10, EA'; reflexivity|]. split; [exact F19|]. split; [rewrite F21, EA'; reflexivity|].
      split; [rewrite F22, En; reflexivity|].
      intros x Hx. apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity. }
  destruct REQ as (fx2 & R2 & MS2 & B1 & B10 & B19 & B21 & B22 & KS2).
  unfold PMSP.cfg.
  apply (PMK.spiece_ro RSEGS model fx fx2 R 0x58b10 R2 0xb03b8 M K Mh Ml MS2).
  (* [comment removed for export] *)
  destruct (grow_credit (PM.VLong A n 0) A TBOK ltac:(rewrite Es; cbn; lia) ltac:(rewrite Es; cbn; lia) eq_refl LA3 CR) as (CROK & CK & Htg).
  assert (STKn : L5C.stk (hl_sptop L) M (S - 80) PMSP.OPNEW_SCR).
  { apply (PMK.stk_call L M S 14336 (S - 80) PMSP.OPNEW_SCR STK); [lia| unfold PMSP.OPNEW_SCR; lia| unfold PMSP.OPNEW_SCR; lia|].
    replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  unfold PMS.opnew_spec, PMSP.opnew_spec in OPN. cbn [pa_opnew AD] in OPN.
  apply (OPN fx2 R2 M model K ((p, c) :: LB) cr0 A (S - 80) 363440 HH MOK K0).
  { rewrite L5K.rl10. exact B10. }
  { lia. }
  { exact CROK. }
  { rewrite L5K.rl1. exact B1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. rewrite (KS2 2%nat) by PMK.inl. exact A2. }
  { rewrite L5K.rl4. rewrite (KS2 4%nat) by PMK.inl. rewrite (KP 4%nat) by (cbn; auto). exact Rtp0. }
  { exact STKn. }
  intros fx3 R3 M3 model3 B R3_10 RP3 FB HP3 MB3 HH3. rewrite L5K.rl10 in R3_10.
  destruct FB as ((FB0 & FB1 & FB2 & FB3 & FB4) & FBa & FBd).
  assert (C3 : forall x, In x [2; 8; 9; 18; 19; 21; 22; 23]%nat -> getr R3 (reg x) = getr R2 (reg x)).
  { intros x Hx. apply (PMK.cs_of_preserved R2 R3 x RP3). revert x Hx. apply sub_in. vm_compute. reflexivity. }
  assert (EKn : PMK.ek L ((p, c) :: LB) (S - 80) PMSP.OPNEW_SCR [] M M3) by (apply (PMK.ek_of_hpres L); exact HP3).
  assert (SC0 : 0 <= PMSP.OPNEW_SCR) by (unfold PMSP.OPNEW_SCR; lia).
  assert (BRX : PMFR.brange L ((p, c) :: LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ cr0 M _ HH); apply incl_refl).
  assert (WHI : forall a, PMK.inW [] a -> S - 80 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
  assert (ABp : B + A <= p \/ p + c <= B) by (exact (FBa (p, c) ltac:(left; reflexivity))).
  assert (MOK3 : PMSP.model_ok model3) by (apply (PMFR.model_ok_but_vm model model3 MOK MB3)).
  apply (gan_long fx3 R3 M3 model3 c n0 p m B A MOK3 En Hm Hn0 ltac:(lia) ltac:(lia) LA4 Hc).
  - rewrite (C3 2%nat) by PMK.inl. rewrite (KS2 2%nat) by PMK.inl. exact A2.
  - rewrite (C3 8%nat) by PMK.inl. rewrite (KS2 8%nat) by PMK.inl. exact A8.
  - rewrite (C3 9%nat) by PMK.inl. rewrite (KS2 9%nat) by PMK.inl. exact A9.
  - exact R3_10.
  - rewrite (C3 18%nat) by PMK.inl. rewrite (KS2 18%nat) by PMK.inl. exact A18.
  - rewrite (C3 19%nat) by PMK.inl. exact B19.
  - rewrite (C3 21%nat) by PMK.inl. exact B21.
  - rewrite (C3 22%nat) by PMK.inl. exact B22.
  - rewrite (C3 23%nat) by PMK.inl. rewrite (KS2 23%nat) by PMK.inl. exact A23.
  - intros x Hx. rewrite (PMK.cs_of_preserved R2 R3 x RP3) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
    rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
    unfold saves. repeat split; (apply (PMFR.u64_keep RSEGS L KL ((p, c) :: LB) (S - 80) PMSP.OPNEW_SCR [] M M3 EKn STKn SC0);
                                 [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| eassumption]).
  - split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M3 EK)|].
    { apply (PMK.ek_callee_in' RSEGS L KL LB ((p, c) :: LB) S 14336 (S - 80) PMSP.OPNEW_SCR [(o, 24)] [] M M3 HP3); [intros x Hx; right; exact Hx
        | unfold PMSP.OPNEW_SCR; lia| lia| lia| destruct STOP; lia| intros b Hb; apply (PMFR.brange_hi L _ BRX b); right; exact Hb| intros a I; destruct (PMFR.inW_nil a I)]. }
    split; [apply (PMK.dk_trans L LB S 14336 M0 M M3 DK);
            apply (PMK.dk_callee L LB ((p, c) :: LB) S 14336 (S - 80) PMSP.OPNEW_SCR [] M M3 HP3); [intros x Hx; right; exact Hx| unfold PMSP.OPNEW_SCR; lia| lia]|].
    split; [apply (PMK.stk_after RSEGS L KL ((p, c) :: LB) M M3 S 14336 (S - 80) PMSP.OPNEW_SCR [] STK HP3); unfold PMSP.OPNEW_SCR; lia|].
    apply (PMFR.defined_keep RSEGS L KL ((p, c) :: LB) (S - 80) PMSP.OPNEW_SCR [] M M3 EKn STKn SC0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact DO].
  - exact FBd.
  - exact FB0.
  - exact FB4.
  - apply (L5C.defined_agree M M3 p c); [apply (PMFR.ag_block RSEGS L KL ((p, c) :: LB) (S - 80) PMSP.OPNEW_SCR [] M M3 EKn STKn SC0 BRX WHI); left; reflexivity| exact DP].
  - exact Hp0.
  - exact Hp1.
  - exact ABp.
  - exact HH3.
  - exact (L5C.model_but_vm_trans _ _ _ MB MB3).
  - pose proof TBOK as (Tg0 & Tg1 & _). rewrite Es in Tg1. cbn [PM.vs_cap] in Tg1.
    split; [lia|]. split; [cbn [PM.vs_cap]; rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia|]. split; [exact LAW| lia].
  - rewrite Es. cbn. lia.
  - rewrite Es in CK |- *. exact CK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sub_wrap1 x k : 0 <= x -> x <= k -> k < 2 ^ 63 -> ((18446744073709551615 * x) mod 2 ^ 64 + k) mod 2 ^ 64 = k - x.
Proof.
  intros H0 H1 H2. replace (18446744073709551615 * x) with (- x + x * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
  rewrite Zplus_mod_idemp_l. replace (- x + k) with (k - x) by lia. apply Z.mod_small. lia.
Qed.
Lemma sub_wrap2 x y : 0 <= x -> x < y -> y < 2 ^ 63 ->
  ((((18446744073709551615 * x) mod 2 ^ 64) + (y mod 2 ^ 64)) mod 2 ^ 64 + 18446744073709551615) mod 2 ^ 64 = y - x - 1.
Proof.
  intros H0 H1 H2. rewrite (Z.mod_small y) by lia. rewrite (sub_wrap1 x y) by lia.
  replace (y - x + 18446744073709551615) with ((y - x - 1) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Definition rs_regs (R : bvmap 5 word) : Prop :=
  forall x, In x [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).

Lemma saves_of (M : word -> option byte) :
  L5.u64_at RSEGS M (S - 80) (bv_unsigned (getr R0 (reg 24))) -> L5.u64_at RSEGS M (S - 72) (bv_unsigned (getr R0 (reg 23))) ->
  L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22))) -> L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) ->
  L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20))) -> L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) ->
  L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18))) -> L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) ->
  L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8))) -> L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) -> saves M.
Proof. intros. unfold saves. repeat split; assumption. Qed.

(* [comment removed for export] *)
Lemma mem_ok_frame (M M' : word -> option byte) :
  mem_ok M -> mem_grows M M' -> (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 80 <= a < S - 80 + 80) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> mem_ok M'.
Proof.
  intros (EK & DK & STK & DO) MG FR.
  split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M' EK);
          apply (PMK.ek_piece_in RSEGS L KL LB S 14336 _ M M' (fun a => S - 80 <= a < S - 80 + 80) FR STK (PMFR.brange_hi L LB BRLB)); intros a X; left; lia|].
  split; [apply (PMK.dk_trans L LB S 14336 M0 M M' DK); apply PMK.dk_grows; exact MG|].
  split; [exact (PMK.stk_grows L M M' S 14336 MG STK)|]. intros i Hi. apply MG. apply DO. exact Hi.
Qed.

Lemma append_short (fx : FPState) R M model (n0 m : Z) :
  PMSP.model_ok model -> s = PM.VShort n0 -> n = n0 + m -> 1 <= m -> 0 <= n0 <= 22 -> PM.tb_ok s tg -> PMSP.credit_le (PM.pot_text L s tg) cr0 ->
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 m -> rs_regs R ->
  mem_ok M -> L5.u8_at RSEGS M o (2 * n0) ->
  hi_heap HI LB cr0 M (m_vmmaps model) -> model_but_vm model0 model ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x58a84 M model) K.
Proof.
  intros MOK Es En Hm Hn0 TBOK CR A10 A11 RR MO B0 HH MB.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
  assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
  assert (HO : bv_unsigned (getr R (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
  destruct (PMTK.u64_of_defined RSEGS M o ltac:(lia) ltac:(lia) ltac:(apply (L5.defined_sub M o 24 o 8 DO); lia)) as (w & Hw & W0).
  pose proof (PMTK.u64_low_byte RSEGS M o w (2 * n0) W0 B0 Hw ltac:(lia)) as WL.
  pose proof (PMTK.short_size w n0 Hw WL Hn0) as HSS.
  assert (TB0 : Z.testbit w 0 = false).
  { rewrite <- (Z.mod_pow2_bits_low w 8 0) by lia. change (2 ^ 8) with 256. rewrite WL. apply PMF.even_byte. }
  assert (R2 : getr R (reg 2) = Z_to_bv 64 S) by (rewrite (RR 2%nat) by PMK.inl; exact Rsp0).
  pose proof (PMSRZP.apS0_conc fx R M (fun j => match j with 2%nat => S | 33%nat => 2 * n0 | 36%nat => w | 43%nat => m | _ => 0 end)) as PP.
  cbn beta iota in PP. rewrite HO in PP.
  PMK.feed PP ltac:(first [PMK.sc | apply PMF.even_byte]).
  destruct PP as (fx1 & R1 & M1 & MG1 & _ & FR1 & EX).
  rewrite HSS in EX. rewrite (sub_wrap1 n0 22) in EX by lia.
  assert (MO1 : mem_ok M1) by (apply (mem_ok_frame M M1 MO MG1); intros a Ha X; apply FR1; [exact Ha| exact X]).
  assert (B01 : L5.u8_at RSEGS M1 o (2 * n0)) by (apply (L5C.u8_at_agree RSEGS M M1); [intros i Hi; apply FR1; lia|lia|lia|exact B0]).
  set (P := fun a => S - 80 <= a < S - 80 + 80).
  assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) by exact FR1.
  unfold PMSP.cfg.
  destruct EX as [(MS1 & KS1 & E2 & E8 & E9 & E10 & _ & E18 & E23 & F & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)
                 |(MS1 & KS1 & E2 & E8 & E9 & E10 & _ & E18 & E23 & F & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)].
  - apply (PMK.spiece RSEGS L HI KL HIok LB cr0 M model fx fx1 R 0x58a84 R1 0x58ae8 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
    { intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L LB M S 14336 a STK); lia. }
    { intros a. unfold P. apply PMK.rng_dec. }
    intros HH1.
    apply (fit_short fx1 R1 M1 model n0 m MOK Es En Hm ltac:(lia) ltac:(lia)).
    + rewrite Es in TBOK. destruct TBOK as (_ & _ & X). exact X.
    + exact E2.
    + rewrite E8, A10. reflexivity.
    + exact E9.
    + exact E10.
    + rewrite <- (Z_to_bv_bv_unsigned _ (getr R1 (reg 18))), E18. reflexivity.
    + exact E23.
    + intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply RR. revert x Hx. apply sub_in. vm_compute. reflexivity.
    + apply saves_of; (rewrite <- (RR _) by PMK.inl; eassumption).
    + exact MO1.
    + exact B01.
    + exact HH1.
    + exact MB.
  - apply (PMK.spiece RSEGS L HI KL HIok LB cr0 M model fx fx1 R 0x58a84 R1 0x58b10 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
    { intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L LB M S 14336 a STK); lia. }
    { intros a. unfold P. apply PMK.rng_dec. }
    intros HH1.
    apply (grow_short fx1 R1 M1 model n0 m MOK Es En Hm ltac:(lia) Hn0 TBOK CR).
    + exact E2.
    + rewrite E8, A10. reflexivity.
    + exact E9.
    + exact E10.
    + rewrite <- (Z_to_bv_bv_unsigned _ (getr R1 (reg 18))), E18. reflexivity.
    + exact E23.
    + intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply RR. revert x Hx. apply sub_in. vm_compute. reflexivity.
    + apply saves_of; (rewrite <- (RR _) by PMK.inl; eassumption).
    + exact MO1.
    + exact HH1.
    + exact MB.
Qed.

Lemma append_long (fx : FPState) R M model (c n0 p m : Z) :
  PMSP.model_ok model -> s = PM.VLong c n0 p -> n = n0 + m -> 1 <= m -> PM.tb_ok s tg -> PMSP.credit_le (PM.pot_text L s tg) cr0 ->
  getr R (reg 10) = Z_to_bv 64 o -> getr R (reg 11) = Z_to_bv 64 m -> rs_regs R ->
  mem_ok M -> PM.vstr_at RSEGS PMSP.T3 M o s -> 4096 <= p -> p + c <= hl_ceil L ->
  hi_heap HI ((p, c) :: LB) cr0 M (m_vmmaps model) -> model_but_vm model0 model ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x58a84 M model) K.
Proof.
  intros MOK Es En Hm TBOK CR A10 A11 RR MO VS Hp0 Hp1 HH MB.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  rewrite Es in VS. destruct VS as (_ & _ & W0 & W8 & W16 & Hnc & Hc & Hce & DP & _).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
  assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
  assert (HO : bv_unsigned (getr R (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
  pose proof (PMF.u8_of_u64 RSEGS M o (c + 1) ltac:(lia) W0) as B0. pose proof (PMF.odd_byte c Hce ltac:(lia)) as ODB.
  assert (H33 : 0 <= (c + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)); lia).
  assert (TB1 : Z.testbit (c + 1) 0 = true) by (rewrite <- (Z.mod_pow2_bits_low (c + 1) 8 0) by lia; exact ODB).
  assert (EC : 2 * ((c + 1) / 2) = c) by (pose proof (Z.div_mod (c + 1) 2 ltac:(lia)) as X; rewrite Z.add_mod, Hce in X by lia; cbn in X; lia).
  assert (R2 : getr R (reg 2) = Z_to_bv 64 S) by (rewrite (RR 2%nat) by PMK.inl; exact Rsp0).
  pose proof (PMSRZP.apL0_conc fx R M (fun j => match j with 2%nat => S | 33%nat => (c + 1) mod 256 | 34%nat => n0 | 36%nat => c + 1 | 43%nat => m | _ => 0 end)) as PP.
  cbn beta iota in PP. rewrite HO in PP.
  PMK.feed PP ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG1 & _ & FR1 & EX).
  rewrite EC in EX. rewrite (sub_wrap2 n0 c) in EX by lia.
  assert (MO1 : mem_ok M1) by (apply (mem_ok_frame M M1 MO MG1); intros a Ha X; apply FR1; [exact Ha| exact X]).
  assert (W01 : L5.u64_at RSEGS M1 o (c + 1)) by (apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1; lia|lia|lia|exact W0]).
  assert (W161 : L5.u64_at RSEGS M1 (o + 16) p) by (apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1; lia|lia|lia|exact W16]).
  assert (DP1 : L5.defined M1 p c) by (intros i Hi; apply MG1; apply DP; exact Hi).
  set (P := fun a => S - 80 <= a < S - 80 + 80).
  assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) by exact FR1.
  unfold PMSP.cfg.
  destruct EX as [(MS1 & KS1 & E2 & E8 & E9 & E10 & _ & E18 & E23 & F & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)
                 |(MS1 & KS1 & E2 & E8 & E9 & E10 & _ & E18 & E23 & F & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)].
  - apply (PMK.spiece RSEGS L HI KL HIok ((p, c) :: LB) cr0 M model fx fx1 R 0x58a84 R1 0x58ae8 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
    { intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L ((p, c) :: LB) M S 14336 a STK); lia. }
    { intros a. unfold P. apply PMK.rng_dec. }
    intros HH1.
    apply (fit_long fx1 R1 M1 model c n0 p m MOK Es En Hm ltac:(lia)).
    + exact E2.
    + rewrite E8, A10. reflexivity.
    + exact E9.
    + exact E10.
    + exact E18.
    + intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply RR. revert x Hx. apply sub_in. vm_compute. reflexivity.
    + apply saves_of; (rewrite <- (RR _) by PMK.inl; eassumption).
    + exact MO1.
    + exact W01.
    + exact W161.
    + lia.
    + exact Hc.
    + exact Hce.
    + exact DP1.
    + exact Hp0.
    + exact Hp1.
    + exact TBOK.
    + exact HH1.
    + exact MB.
  - apply (PMK.spiece RSEGS L HI KL HIok ((p, c) :: LB) cr0 M model fx fx1 R 0x58a84 R1 0x58b10 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
    { intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L ((p, c) :: LB) M S 14336 a STK); lia. }
    { intros a. unfold P. apply PMK.rng_dec. }
    intros HH1.
    apply (grow_long fx1 R1 M1 model c n0 p m MOK Es En Hm ltac:(lia) ltac:(lia) TBOK Hc Hce W161 DP1 Hp0 Hp1 CR).
    + exact E2.
    + rewrite E8, A10. reflexivity.
    + exact E9.
    + exact E10.
    + exact E18.
    + exact E23.
    + intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply RR. revert x Hx. apply sub_in. vm_compute. reflexivity.
    + apply saves_of; (rewrite <- (RR _) by PMK.inl; eassumption).
    + exact MO1.
    + exact HH1.
    + exact MB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma resize_entry (fx : FPState) :
  PMSP.model_ok model0 -> hi_heap HI (PM.vs_own s ++ LB) cr0 M0 (m_vmmaps model0) ->
  getr R0 (reg 10) = Z_to_bv 64 o -> getr R0 (reg 11) = Z_to_bv 64 n ->
  PM.vstr_at RSEGS PMSP.T3 M0 o s -> PM.tb_ok s tg -> PMSP.credit_le (PM.pot_text L s tg) cr0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0x59000 M0 model0) K.
Proof.
  intros MOK HH A10 A11 VS TBOK CR.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK0 as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  pose proof VS as (DO & _ & _).
  assert (WRo : L5.writable RSEGS M0 o 24) by (apply (L5C.writable_of_defined RSEGS M0 o 24 DO); lia).
  assert (HO : bv_unsigned (getr R0 (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
  assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
  assert (MO0 : mem_ok M0).
  { split; [apply PMK.ek_refl|]. split; [apply PMK.dk_refl|]. split; [exact STK0| exact DO]. }
  assert (RR0 : rs_regs R0) by (intros x _; reflexivity).
  unfold PMSP.cfg.
  assert (CASE : (exists n0, s = PM.VShort n0) \/ (exists c n0 p, s = PM.VLong c n0 p)) by (destruct s as [x|x y z]; [left; exists x | right; exists x, y, z]; reflexivity).
  destruct CASE as [(n0 & Es)|(c & n0 & p & Es)]; rewrite Es in VS, HH.
  - (* [comment removed for export] *)
    destruct VS as (_ & _ & Hn0 & B0).
    assert (Hn1' : n <= n0 + 16384) by (rewrite Es in Hn1; cbn [PM.vs_size] in Hn1; unfold PM.CHUNK in Hn1; lia).
    pose proof (PMSRZP.rzS_conc fx R0 M0 (fun j => match j with 2%nat => S | 33%nat => 2 * n0 | 37%nat => n | _ => 0 end)) as PP.
    cbn beta iota in PP. rewrite HO in PP.
    PMK.feed PP ltac:(first [PMK.sc | apply PMF.even_byte]).
    destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & EX).
    assert (EM : M1 = M0) by (apply functional_extensionality; exact FRw). subst M1.
    replace (2 * n0 / 2) with n0 in EX by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    destruct EX as [(MS1 & KS1 & F13 & _ & F)|(MS1 & KS1 & F11 & _ & _ & F)].
    + (* [comment removed for export] *)
      apply (PMK.spiece_ro RSEGS model0 fx fx1 R0 0x59000 R1 0x59014 M0 K Mh Ml MS1).
      assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 S) by (rewrite (KS1 2%nat) by PMK.inl; exact Rsp0).
      assert (R1_11 : getr R1 (reg 11) = Z_to_bv 64 n) by (rewrite (KS1 11%nat) by PMK.inl; exact A11).
      assert (HO1 : bv_unsigned (getr R1 (reg 10)) = o) by (rewrite (KS1 10%nat) by PMK.inl; exact HO).
      pose proof (PMSRZP.rzTS_conc fx1 R1 M0 (fun j => match j with 2%nat => S | 37%nat => n | _ => 0 end)) as PT.
      cbn beta iota in PT. rewrite HO1 in PT.
      PMK.feed PT ltac:(first [PMK.sc]).
      PMK.pvz_hg ltac:(idtac; destruct PT as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP;
        destruct pvzP as (MG2 & _ & FRZ0 & MS2 & KS2 & _ & _ & _ & CN & CB)); PMK.pvz_clrT.
      set (P := fun a => o <= a < o + 24).
      assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M2 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
      { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; unfold P; lia]. }
      apply (PMK.spiece RSEGS L HI KL HIok (PM.vs_own (PM.VShort n0) ++ LB) cr0 M0 model0 fx1 fx2 R1 0x59014 R2 0x5902c M2 P K HH Mh Ml ltac:(destruct STOP; lia) MS2 MG2 FRZ).
      { intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L _ M0 S 14336 a STK0); lia. }
      { intros a. unfold P. apply PMK.rng_dec. }
      intros HH2.
      assert (RA2 : getr R2 (reg 1) = Z_to_bv 64 r) by (rewrite (KS2 1%nat) by PMK.inl; rewrite (KS1 1%nat) by PMK.inl; exact Rra0).
      unfold PMK.cfg.
      eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx2 R2 M2 0x5902c W_579ec r F_579ec ltac:(reflexivity) D_579ec RA2 Hr1 Hr2)|].
      apply (KONT fx2 R2 M2 model0 (PM.VShort n) tg cr0); [| | reflexivity | | | | | apply L5C.model_but_vm_refl | exact HH2].
      * apply PMK.preserved_by_index. intros x Hx. rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
        apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
      * split; [intros i Hi; apply MG2; apply DO; exact Hi|]. split; [exact I|]. split; [lia| exact CB].
      * rewrite Es in TBOK. unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK.
      * intros _. rewrite Es. split; reflexivity.
      * apply (PMK.hpres_of L LB S 14336 _ M0 M2).
        -- apply (PMK.ek_piece L LB S 14336 _ M0 M2 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa.
           apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- destruct (PMK.stk_grows L M0 M2 S 14336 MG2 STK0) as (_ & _ & _ & _ & D2). exact D2.
        -- apply PMK.dk_grows. exact MG2.
      * rewrite Es. unfold PMSP.credit_keep, PM.pot_text. cbn [PM.vs_cap]. lia.
    + (* [comment removed for export] *)
      apply (PMK.spiece_ro RSEGS model0 fx fx1 R0 0x59000 R1 0x58a84 M0 K Mh Ml MS1).
      apply (append_short fx1 R1 M0 model0 n0 (n - n0) MOK Es ltac:(lia) ltac:(lia) Hn0 TBOK CR).
      * rewrite (KS1 10%nat) by PMK.inl. exact A10.
      * exact F11.
      * intros x Hx. apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
      * exact MO0.
      * exact B0.
      * exact HH.
      * apply L5C.model_but_vm_refl.
  - (* [comment removed for export] *)
    pose proof VS as (_ & _ & W0 & W8 & W16 & Hnc & Hc & Hce & DP & _).
    assert (Ip : In (p, c) (PM.vs_own (PM.VLong c n0 p) ++ LB)) by (left; reflexivity).
    destruct (PMFR.brange_of_heap L HI HIok _ _ cr0 M0 _ HH (incl_refl _) p c Ip) as (Pp0 & Pp1 & Pp4).
    pose proof (PMF.u8_of_u64 RSEGS M0 o (c + 1) ltac:(lia) W0) as B0. pose proof (PMF.odd_byte c Hce ltac:(lia)) as ODB.
    assert (H33 : 0 <= (c + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)); lia).
    pose proof (PMSRZP.rzL_conc fx R0 M0 (fun j => match j with 2%nat => S | 33%nat => (c + 1) mod 256 | 34%nat => n0 | 37%nat => n | _ => 0 end)) as PP.
    cbn beta iota in PP. rewrite HO in PP.
    PMK.feed PP ltac:(first [PMK.sc]).
    destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & EX).
    assert (EM : M1 = M0) by (apply functional_extensionality; exact FRw). subst M1.
    destruct EX as [(MS1 & KS1 & F11 & _ & _ & F)|(MS1 & KS1 & F13 & _ & F)].
    + (* [comment removed for export] *)
      apply (PMK.spiece_ro RSEGS model0 fx fx1 R0 0x59000 R1 0x58a84 M0 K Mh Ml MS1).
      apply (append_long fx1 R1 M0 model0 c n0 p (n - n0) MOK Es ltac:(lia) ltac:(lia) TBOK CR).
      * rewrite (KS1 10%nat) by PMK.inl. exact A10.
      * rewrite F11. f_equal. lia.
      * intros x Hx. apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
      * exact MO0.
      * rewrite Es. exact VS.
      * exact Pp0.
      * exact Pp4.
      * exact HH.
      * apply L5C.model_but_vm_refl.
    + (* [comment removed for export] *)
      apply (PMK.spiece_ro RSEGS model0 fx fx1 R0 0x59000 R1 0x59014 M0 K Mh Ml MS1).
      assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 S) by (rewrite (KS1 2%nat) by PMK.inl; exact Rsp0).
      assert (R1_11 : getr R1 (reg 11) = Z_to_bv 64 n) by (rewrite (KS1 11%nat) by PMK.inl; exact A11).
      assert (HO1 : bv_unsigned (getr R1 (reg 10)) = o) by (rewrite (KS1 10%nat) by PMK.inl; exact HO).
      assert (WRp : L5.writable RSEGS M0 (p + n) 1) by (apply (L5C.writable_of_defined RSEGS M0 (p + n) 1); [apply (L5.defined_sub M0 p c (p + n) 1 DP); lia|lia|lia]).
      assert (Dpo : p + n + 1 <= o \/ o + 24 <= p + n) by (left; lia).
      pose proof (PMSRZP.rzTL_conc fx1 R1 M0 (fun j => match j with 2%nat => S | 35%nat => p | 37%nat => n | _ => 0 end)) as PT.
      cbn beta iota in PT. rewrite HO1 in PT.
      PMK.feed PT ltac:(first [PMK.sc]).
      PMK.pvz_hg ltac:(idtac; destruct PT as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP;
        destruct pvzP as (MG2 & _ & FRZ0 & MS2 & KS2 & _ & _ & CN & C8)); PMK.pvz_clrT.
      set (P := fun a => (o + 8 <= a < o + 8 + 8) \/ (p + n <= a < p + n + 1)).
      assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M2 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
      { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; unfold P; lia| intro X; apply N; unfold P; lia]. }
      apply (PMK.spiece RSEGS L HI KL HIok (PM.vs_own (PM.VLong c n0 p) ++ LB) cr0 M0 model0 fx1 fx2 R1 0x59014 R2 0x59050 M2 P K HH Mh Ml ltac:(destruct STOP; lia) MS2 MG2 FRZ).
      { intros a Pa. unfold P in Pa. destruct Pa as [X|X];
          [apply (PMK.cwr_stack L _ M0 S 14336 a STK0); lia
          |apply (PMK.cwr_block L _ p c a Ip); lia]. }
      { intros a. unfold P. apply PMK.or_dec; apply PMK.rng_dec. }
      intros HH2.
      assert (RA2 : getr R2 (reg 1) = Z_to_bv 64 r) by (rewrite (KS2 1%nat) by PMK.inl; rewrite (KS1 1%nat) by PMK.inl; exact Rra0).
      unfold PMK.cfg.
      eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx2 R2 M2 0x59050 W_57a10 r F_57a10 ltac:(reflexivity) D_57a10 RA2 Hr1 Hr2)|].
      assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (forall i, a <= i < a + m -> ~ P i) -> L5C.agree_on M0 M2 a m).
      { intros a0 m0 Ha0 Hm0 X i Hi. apply FRZ; [lia| apply X; exact Hi]. }
      apply (KONT fx2 R2 M2 model0 (PM.VLong c n p) tg cr0); [| | reflexivity | | | | | apply L5C.model_but_vm_refl | exact HH2].
      * apply PMK.preserved_by_index. intros x Hx. rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
        apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
      * split; [intros i Hi; apply MG2; apply DO; exact Hi|]. split; [exact I|].
        split; [apply (L5C.u64_at_agree RSEGS M0 M2); [apply AG; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|X]; cdisj; lia]|lia|lia|exact W0]|].
        split; [exact C8|].
        split; [apply (L5C.u64_at_agree RSEGS M0 M2); [apply AG; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|X]; cdisj; lia]|lia|lia|exact W16]|].
        split; [lia|]. split; [lia|]. split; [exact Hce|]. split; [intros i Hi; apply MG2; apply DP; exact Hi| exact I].
      * rewrite Es in TBOK. unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK.
      * intros _. rewrite Es. split; reflexivity.
      * apply (PMK.hpres_of L LB S 14336 _ M0 M2).
        -- apply (PMK.ek_piece L LB S 14336 _ M0 M2 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa. destruct Pa as [X|X].
           ++ apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
           ++ exact (PMSRS.own_not_client L HI HIok [(p, c)] LB cr0 M0 _ p c a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA).
        -- destruct (PMK.stk_grows L M0 M2 S 14336 MG2 STK0) as (_ & _ & _ & _ & D2). exact D2.
        -- apply PMK.dk_grows. exact MG2.
      * rewrite Es. unfold PMSP.credit_keep, PM.pot_text. cbn [PM.vs_cap]. lia.
Qed.

End Call.
End WithHeap.
End PMSRZ1.
