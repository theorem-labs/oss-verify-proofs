(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmFrame PmParKit PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnSrcSMemmove_u PnSPushBackP_u
     Bs0_code_57384_57388_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSPB.
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

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma own_not_client OWN LB cr M VM B m a sp scr :
  hi_heap HI (OWN ++ LB) cr M VM -> In (B, m) OWN -> B <= a < B + m -> ~ client_addr L LB sp scr a.
Proof.
  intros HH Hin Ha. assert (BR : PMFR.brange L (OWN ++ LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  destruct (BR B m (in_or_app _ _ _ (or_introl Hin))) as (Z0 & Z1 & Z4).
  intros [((B' & m') & Hb & Hr)|[[S1 _]|[IM _]]]; [|lia|lia]. cbn in Hr.
  assert (NE : B <> B') by (apply (PMPK.fst_neq_app OWN LB B m B' m' (PMPK.heap_nodup L HI HIok _ _ _ _ HH) Hin Hb)).
  destruct (PMPK.blocks_apart_heap L HI HIok _ cr M _ B m B' m' HH (in_or_app _ _ _ (or_introl Hin)) (in_or_app _ _ _ (or_intror Hb)) NE); lia.
Qed.

(* [comment removed for export] *)
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (cr0 : credit).
Variables (o ch S r tg : Z) (x : PM.vstr).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis K0 : K [].
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S 14336.
Hypothesis Ho1 : S <= o.
Hypothesis Ho2 : o + 24 <= hl_sptop L.
Hypothesis Ho3 : o mod 8 = 0.
Hypothesis Hch : 0 <= ch < 256.
Hypothesis A11 : getr R0 (reg 11) = Z_to_bv 64 ch.
Hypothesis SZ : PM.vs_size x < 2 ^ 26.
Hypothesis BRLB : PMFR.brange L LB.
Hypothesis OPN : PMS.opnew_spec L HI.
Hypothesis OPD : PMS.opdel_spec L HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : PM.vstr) (tg' : Z) (cr' : credit),
  regs_preserved R0 R' -> PM.vstr_at RSEGS PMSP.T3 M' o x' -> PM.vs_size x' = PM.vs_size x + 1 -> PM.tb_ok x' tg' ->
  (PM.vs_size x < PM.vs_cap x -> PM.vs_own x' = PM.vs_own x /\ tg' = tg) ->
  L5C.hpres L LB S (PMSP.pm_scr 1) [(o, 24)] M0 M' ->
  PMSP.credit_keep cr0 cr' (PM.pot_text L x tg) (PM.pot_text L x' tg') ->
  model_but_vm model0 model' -> hi_heap HI (PM.vs_own x' ++ LB) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22))).
(* [comment removed for export] *)
Definition kept0 (R : bvmap 5 word) : Prop := forall x, In x [3; 4; 23; 24; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
(* [comment removed for export] *)
Definition mem_ok (M : word -> option byte) : Prop :=
  PMK.ek L LB S 14336 [(o, 24)] M0 M /\ PMK.dk L LB S 14336 M0 M /\ L5C.stk (hl_sptop L) M S 14336 /\ L5.defined M o 24.

Lemma regs_back (R1 : bvmap 5 word) :
  getr R1 (reg 2) = Z_to_bv 64 S -> getr R1 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) ->
  getr R1 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) -> getr R1 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) ->
  getr R1 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) -> getr R1 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) ->
  getr R1 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) -> getr R1 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22))) ->
  kept0 R1 -> regs_preserved R0 R1.
Proof.
  intros E2 E8 E9 E18 E19 E20 E21 E22 KP. apply PMK.preserved_by_index. intros y Hy. unfold PMK.cs_all in Hy. cbn in Hy.
  destruct Hy as [<-|Hy]; [rewrite E2, Rsp0; reflexivity|].
  destruct Hy as [<-|Hy]; [apply KP; cbn; auto|]. destruct Hy as [<-|Hy]; [apply KP; cbn; auto|].
  destruct Hy as [<-|Hy]; [rewrite E8; apply Z_to_bv_bv_unsigned|]. destruct Hy as [<-|Hy]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
  destruct Hy as [<-|Hy]; [rewrite E18; apply Z_to_bv_bv_unsigned|]. destruct Hy as [<-|Hy]; [rewrite E19; apply Z_to_bv_bv_unsigned|].
  destruct Hy as [<-|Hy]; [rewrite E20; apply Z_to_bv_bv_unsigned|]. destruct Hy as [<-|Hy]; [rewrite E21; apply Z_to_bv_bv_unsigned|].
  destruct Hy as [<-|Hy]; [rewrite E22; apply Z_to_bv_bv_unsigned|].
  apply KP. destruct Hy as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; auto 10.
Qed.

Ltac bvr1 R y := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg y))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tail (fx : FPState) R M model (n p A B pc a0 s5 tg' : Z) (cr' : credit) :
  PMSP.model_ok model -> n = PM.vs_size x -> 0 <= n -> n + 2 <= A -> 26 <= A <= 2 ^ 27 -> A mod 8 = 0 ->
  (pc = 0x58a0c /\ s5 = 23 \/ pc = 0x58a20) ->
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 ch -> getr R (reg 9) = Z_to_bv 64 o -> getr R (reg 10) = Z_to_bv 64 a0 ->
  getr R (reg 18) = Z_to_bv 64 p -> getr R (reg 19) = Z_to_bv 64 A -> getr R (reg 20) = Z_to_bv 64 n -> getr R (reg 21) = Z_to_bv 64 s5 -> getr R (reg 22) = Z_to_bv 64 B ->
  0 <= a0 < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= s5 < 2 ^ 64 ->
  kept0 R -> saves M -> mem_ok M ->
  L5.defined M B A -> 4096 <= B -> B + A <= hl_ceil L ->
  hi_heap HI ((B, A) :: LB) cr' M (m_vmmaps model) -> model_but_vm model0 model ->
  PM.tb_ok (PM.VLong A (n + 1) B) tg' -> PM.vs_cap x = n ->
  PMSP.credit_keep cr0 cr' (PM.pot_text L x tg) (PM.pot_text L (PM.VLong A (n + 1) B) tg') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc M model) K.
Proof.
  intros MOK En Hn0 HnA HA HA8 PC A2 A8 A9 A10 A18 A19 A20 A21 A22 Ha0 Hp Hs5 KP SV MO DB HB0 HB1 HH MB TBOK FULL CK.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
  assert (WRb : L5.writable RSEGS M (B + n) 2) by (apply (L5C.writable_of_defined RSEGS M (B + n) 2); [apply (L5.defined_sub M B A (B + n) 2 DB); lia|lia|lia]).
  assert (Dbo : B + n + 2 <= o \/ o + 24 <= B + n) by (left; lia).
  assert (Dbf : B + n + 2 <= S - 64 \/ S - 64 + 64 <= B + n) by (left; lia).
  destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64). bvr.
  (* [comment removed for export] *)
  assert (STORED : exists fx1 R1 M1, msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x58a68) M1 (seg_rom RSEGS))
      /\ mem_grows M M1 /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 24) -> ~ (B + n <= a < B + n + 2) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
      /\ (forall y, In y [3; 4; 23; 24; 25; 26; 27]%nat -> getr R1 (reg y) = getr R (reg y))
      /\ getr R1 (reg 1) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 1))) /\ getr R1 (reg 2) = Z_to_bv 64 S
      /\ getr R1 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) /\ getr R1 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9)))
      /\ getr R1 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) /\ getr R1 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19)))
      /\ getr R1 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) /\ getr R1 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21)))
      /\ getr R1 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22)))
      /\ L5.u8_at RSEGS M1 (B + n + 1) 0 /\ L5.u8_at RSEGS M1 (B + n) ch
      /\ L5.u64_at RSEGS M1 (o + 8) (n + 1) /\ L5.u64_at RSEGS M1 (o + 16) B /\ L5.u64_at RSEGS M1 o (2 * (A / 2) + 1)).
  { destruct PC as [(-> & ->)| ->].
    - LeanFeed.pfeed PP (PNSPBP.pbTS_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 37%nat => B | 38%nat => A | 39%nat => n | 41%nat => p
                    | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
                    | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
                    | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 54%nat => a0 | 56%nat => ch | _ => 0 end)) ltac:(first [PMK.sc]).
      destruct PP as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & KS1 & F1 & F2 & F8 & F9 & _ & _ & F18 & F19 & F20 & F21 & F22 & C1 & C2 & C3 & C4 & C5).
      exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros a Ha X Y; apply FR1; [exact Ha| lia| lia]|].
      split; [intros y Hy; apply KS1; revert y Hy; apply sub_in; vm_compute; reflexivity|].
      repeat split; first [assumption | (rewrite Z.add_comm; assumption) | (replace (B + n + 1) with ((B + n) + 1) by lia; assumption)].
    - LeanFeed.pfeed PP (PNSPBP.pbT_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 37%nat => B | 38%nat => A | 39%nat => n | 40%nat => s5 | 41%nat => p
                    | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
                    | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
                    | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 55%nat => a0 | 56%nat => ch | _ => 0 end)) ltac:(first [PMK.sc]).
      destruct PP as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & KS1 & F1 & F2 & F8 & F9 & _ & _ & F18 & F19 & F20 & F21 & F22 & C1 & C2 & C3 & C4 & C5).
      exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros a Ha X Y; apply FR1; [exact Ha| lia| lia]|].
      split; [intros y Hy; apply KS1; revert y Hy; apply sub_in; vm_compute; reflexivity|].
      repeat split; first [assumption | (rewrite Z.add_comm; assumption) | (replace (B + n + 1) with ((B + n) + 1) by lia; assumption)]. }
  destruct STORED as (fx1 & R1 & M1 & MS1 & MG1 & FR1 & KS1 & F1 & F2 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & C1 & C2 & C3 & C4 & C5).
  set (P1 := fun a => (o <= a < o + 24) \/ (B + n <= a < B + n + 2)).
  assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FR1; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]. }
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok ((B, A) :: LB) cr' M model fx fx1 R pc R1 0x58a68 M1 P1 K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
  { intros a Pa. unfold P1 in Pa. destruct Pa as [X|X];
      [apply (PMK.cwr_stack L ((B, A) :: LB) M S 14336 a STK); lia
      |apply (PMK.cwr_block L ((B, A) :: LB) B A a ltac:(left; reflexivity)); lia]. }
  { intros a. unfold P1. apply PMK.or_dec; apply PMK.rng_dec. }
  intros HH1.
  assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite F1, Z_to_bv_bv_unsigned; exact Rra0).
  unfold PMK.cfg.
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x58a68 W_57428 r F_57428 ltac:(reflexivity) D_57428 RA1 Hr1 Hr2)|].
  apply (KONT fx1 R1 M1 model (PM.VLong A (n + 1) B) tg' cr'); [| | cbn [PM.vs_size]; lia | exact TBOK | | | exact CK | exact MB | exact HH1].
  - apply regs_back; try assumption. intros y Hy. rewrite (KS1 y Hy). apply KP. exact Hy.
  - split; [intros i Hi; apply MG1; apply DO; exact Hi|]. split; [exact I|].
    split; [replace (A + 1) with (2 * (A / 2) + 1) by lia; exact C5|].
    split; [exact C3|]. split; [exact C4|].
    split; [lia|]. split; [lia|]. split; [apply Z.mod_divide; [lia|]; exists (A / 2); lia|].
    split; [intros i Hi; apply MG1; apply DB; exact Hi| exact I].
  - intros X. exfalso. rewrite FULL in X. lia.
  - apply (PMK.hpres_of L LB S 14336 _ M0 M1).
    + apply (PMK.ek_trans L LB S 14336 _ M0 M M1 EK).
      apply (PMK.ek_piece L LB S 14336 _ M M1 P1 FRZ). intros a Ha CA NE OW Pa. unfold P1 in Pa. destruct Pa as [X|X].
      * apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
      * exact (own_not_client [(B, A)] LB cr' M _ B A a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA).
    + destruct (PMK.stk_grows L M M1 S 14336 MG1 STK) as (_ & _ & _ & _ & D1). exact D1.
    + apply (PMK.dk_trans L LB S 14336 M0 M M1 DK). apply PMK.dk_grows. exact MG1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_new (fx : FPState) R M model (n q c A B s5 : Z) (OWN : list (Z * Z)) (cr' : credit) :
  PMSP.model_ok model -> n = PM.vs_size x -> 1 <= n -> n + 2 <= A -> 26 <= A <= 2 ^ 27 -> A mod 8 = 0 -> PM.vs_cap x = n ->
  ((s5 = 23 /\ OWN = [] /\ q = o + 1 /\ n = 22) \/ (s5 = c /\ OWN = [(q, c)] /\ 26 <= c <= 2 ^ 27 /\ n < c)) -> OWN = PM.vs_own x ->
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 ch -> getr R (reg 9) = Z_to_bv 64 o -> getr R (reg 10) = Z_to_bv 64 B ->
  getr R (reg 18) = Z_to_bv 64 q -> getr R (reg 19) = Z_to_bv 64 A -> getr R (reg 20) = Z_to_bv 64 n -> getr R (reg 21) = Z_to_bv 64 s5 ->
  kept0 R -> saves M -> mem_ok M -> L5.defined M q n -> 0 <= q -> q + n < 2 ^ 63 -> (q + n <= S - 14336 \/ S <= q) ->
  L5.defined M B A -> 4096 <= B -> B + A <= hl_ceil L -> (B + A <= q \/ q + n <= B) ->
  hi_heap HI ((B, A) :: OWN ++ LB) cr' M (m_vmmaps model) -> model_but_vm model0 model ->
  PM.tb_ok (PM.VLong A (n + 1) B) (tg + 1) ->
  PMSP.credit_keep cr0 cr' (PM.pot_text L x tg) (PM.pot_text L (PM.VLong A (n + 1) B) (tg + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x589fc M model) K.
Proof.
  intros MOK En Hn1 HnA HA HA8 FULL CASE EOWN A2 A8 A9 A10 A18 A19 A20 A21 KP SV MO DQ Hq0 Hq1 Hq2 DB HB0 HB1 APT HH MB TBOK CK.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
  assert (Hs5 : 0 <= s5 < 2 ^ 64) by (destruct CASE as [(-> & _)|(-> & _ & Hc & _)]; lia).
  assert (Hq64 : 0 <= q < 2 ^ 64) by lia. assert (HB64 : 0 <= B < 2 ^ 64) by lia. assert (Hn0 : 0 <= n) by lia.
  destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64). bvr.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as G22. change (bv_modulus 64) with (2 ^ 64) in G22.
  assert (A22 : getr R (reg 22) = Z_to_bv 64 (bv_unsigned (getr R (reg 22)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  LeanFeed.pfeed PP (PNSPBP.pbN_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 37%nat => B | 38%nat => A | 39%nat => n | 40%nat => s5 | 41%nat => q
                | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
                | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
                | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 56%nat => ch | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & MS1 & KS1 & F1 & F11 & F12 & F22).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
  unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x589fc R1 0xab884 M K Mh Ml MS1).
  (* [comment removed for export] *)
  assert (F10 : getr R1 (reg 10) = Z_to_bv 64 B) by (rewrite (KS1 10%nat) by PMK.inl; exact A10).
  destruct (PMCPS.memmove_run fx1 R1 M B q n 0x58a0c F10 F11 F12 F1 ltac:(split; [lia| reflexivity]) Hn1 ltac:(lia) ltac:(lia) Hq0 Hq1 ltac:(lia)
              ltac:(apply (L5C.writable_of_defined RSEGS M B n); [apply (L5.defined_sub M B A B n DB); lia|lia|lia]) DQ) as (R3 & M3 & MS3 & MG3 & FR3 & D3 & KS3 & R3_10).
  set (P3 := fun a => B <= a < B + n).
  apply (PMK.spiece RSEGS L HI KL HIok ((B, A) :: OWN ++ LB) cr' M model fx1 fx1 R1 0xab884 R3 0x58a0c M3 P3 K HH Mh Ml ltac:(destruct STOP; lia) MS3 MG3 FR3).
  { intros a Pa. unfold P3 in Pa. apply (PMK.cwr_block L ((B, A) :: OWN ++ LB) B A a ltac:(left; reflexivity)); lia. }
  { intros a. unfold P3. apply PMK.rng_dec. }
  intros HH3.
  assert (KSR : forall y, In y L5K.CS -> getr R3 (reg y) = getr R1 (reg y)) by exact KS3.
  assert (SV3 : saves M3).
  { unfold saves. repeat split; (eapply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply FR3; [lia| unfold P3; lia]|lia|lia|eassumption]). }
  assert (MO3 : mem_ok M3).
  { split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M3 EK); apply (PMK.ek_piece L LB S 14336 _ M M3 P3 FR3);
             intros a Ha CA NE OW Pa; unfold P3 in Pa;
             exact (own_not_client ((B, A) :: OWN) LB _ M _ B A a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA)|].
    split; [apply (PMK.dk_trans L LB S 14336 M0 M M3 DK); apply PMK.dk_grows; exact MG3|].
    split; [exact (PMK.stk_grows L M M3 S 14336 MG3 STK)|]. intros i Hi. apply MG3. apply DO. exact Hi. }
  assert (DB3 : L5.defined M3 B A) by (intros i Hi; apply MG3; apply DB; exact Hi).
  assert (C3 : forall y, In y [2; 8; 9; 18; 19; 20; 21; 22]%nat -> getr R3 (reg y) = getr R1 (reg y)).
  { intros y Hy. apply KSR. revert y Hy. apply sub_in. vm_compute. reflexivity. }
  pose proof (bv_unsigned_in_range 64 (getr R3 (reg 10))) as G10. change (bv_modulus 64) with (2 ^ 64) in G10.
  destruct CASE as [(Es5 & EO & Eq & En22)|(Es5 & EO & Hc & Hnc)].
  - (* [comment removed for export] *)
    subst OWN. cbn [app] in HH3.
    apply (tail fx1 R3 M3 model n q A B 0x58a0c B s5 (tg + 1) cr' MOK En Hn0 HnA HA HA8 (or_introl (conj eq_refl Es5))); try assumption.
    + rewrite (C3 2%nat) by PMK.inl. rewrite (KS1 2%nat) by PMK.inl. exact A2.
    + rewrite (C3 8%nat) by PMK.inl. rewrite (KS1 8%nat) by PMK.inl. exact A8.
    + rewrite (C3 9%nat) by PMK.inl. rewrite (KS1 9%nat) by PMK.inl. exact A9.
    + rewrite (C3 18%nat) by PMK.inl. rewrite (KS1 18%nat) by PMK.inl. exact A18.
    + rewrite (C3 19%nat) by PMK.inl. rewrite (KS1 19%nat) by PMK.inl. exact A19.
    + rewrite (C3 20%nat) by PMK.inl. rewrite (KS1 20%nat) by PMK.inl. exact A20.
    + rewrite (C3 21%nat) by PMK.inl. rewrite (KS1 21%nat) by PMK.inl. exact A21.
    + rewrite (C3 22%nat) by PMK.inl. exact F22.
    + intros y Hy. rewrite (KSR y) by (revert y Hy; apply sub_in; vm_compute; reflexivity).
      rewrite (KS1 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply KP. exact Hy.
  - (* [comment removed for export] *)
    subst OWN. cbn [app] in HH3, HH.
    pose proof SV3 as (T8 & T16 & T24 & T32 & T40 & T48 & T56 & T64). pose proof MO3 as (_ & _ & STK3 & DO3).
    pose proof (L5C.stk_writable RSEGS _ M3 S 14336 STK3) as WR3.
    assert (WRo3 : L5.writable RSEGS M3 o 24) by (apply (L5C.writable_of_defined RSEGS M3 o 24 DO3); lia).
    assert (B2 : getr R3 (reg 2) = Z_to_bv 64 (S - 64)) by (rewrite (C3 2%nat) by PMK.inl; rewrite (KS1 2%nat) by PMK.inl; exact A2).
    assert (B8 : getr R3 (reg 8) = Z_to_bv 64 ch) by (rewrite (C3 8%nat) by PMK.inl; rewrite (KS1 8%nat) by PMK.inl; exact A8).
    assert (B9 : getr R3 (reg 9) = Z_to_bv 64 o) by (rewrite (C3 9%nat) by PMK.inl; rewrite (KS1 9%nat) by PMK.inl; exact A9).
    assert (B18 : getr R3 (reg 18) = Z_to_bv 64 q) by (rewrite (C3 18%nat) by PMK.inl; rewrite (KS1 18%nat) by PMK.inl; exact A18).
    assert (B19 : getr R3 (reg 19) = Z_to_bv 64 A) by (rewrite (C3 19%nat) by PMK.inl; rewrite (KS1 19%nat) by PMK.inl; exact A19).
    assert (B20 : getr R3 (reg 20) = Z_to_bv 64 n) by (rewrite (C3 20%nat) by PMK.inl; rewrite (KS1 20%nat) by PMK.inl; exact A20).
    assert (B21 : getr R3 (reg 21) = Z_to_bv 64 s5) by (rewrite (C3 21%nat) by PMK.inl; rewrite (KS1 21%nat) by PMK.inl; exact A21).
    assert (B22 : getr R3 (reg 22) = Z_to_bv 64 B) by (rewrite (C3 22%nat) by PMK.inl; exact F22).
    LeanFeed.pfeed PP (PNSPBP.pbD_conc fx1 R3 M3 (fun j => match j with 2%nat => S | 10%nat => o | 37%nat => B | 38%nat => A | 39%nat => n | 40%nat => s5 | 41%nat => q
                | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
                | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
                | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 54%nat => B | 56%nat => ch | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx4 & R4 & M4 & MG4 & FRw4 & _ & MS4 & KS4 & Y1 & Y10 & Y11).
    assert (EM : M4 = M3) by (apply functional_extensionality; exact FRw4). subst M4.
    apply (PMK.spiece_ro RSEGS model fx1 fx4 R3 0x58a0c R4 0x56720 M3 K Mh Ml MS4).
    (* [comment removed for export] *)
    set (LBc := (B, A) :: (q, c) :: LB).
    assert (Ip : In (q, c) LBc) by (right; left; reflexivity).
    assert (NBq : B <> q) by lia.
    assert (ELB : lb_remove q LBc = (B, A) :: LB).
    { unfold LBc. cbn [lb_remove fst]. destruct (Z.eqb_spec B q) as [X|_]; [exfalso; exact (NBq X)|]. rewrite Z.eqb_refl. reflexivity. }
    assert (STKd : L5C.stk (hl_sptop L) M3 (S - 64) PMSP.OPDEL_SCR).
    { apply (PMK.stk_call L M3 S 14336 (S - 64) PMSP.OPDEL_SCR STK3); [lia| unfold PMSP.OPDEL_SCR; lia| unfold PMSP.OPDEL_SCR; lia|].
      replace (S - 64) with (S + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    pose proof OPD as OD. unfold PMS.opdel_spec, PMSP.opdel_spec, PMSP.opdel_spec_at in OD. cbn [pa_opdel AD] in OD.
    apply (OD fx4 R4 M3 model K LBc cr' q c (S - 64) 0x58a20 HH3 MOK K0 Ip).
    { rewrite L5K.rl10. exact Y10. }
    { rewrite L5K.rl1. exact Y1. }
    { split; [lia| reflexivity]. }
    { rewrite L5K.rl2. rewrite (KS4 2%nat) by PMK.inl. exact B2. }
    { rewrite L5K.rl4. rewrite (KS4 4%nat) by PMK.inl. rewrite (KSR 4%nat) by PMK.inl. rewrite (KS1 4%nat) by PMK.inl. rewrite (KP 4%nat) by (cbn; auto). exact Rtp0. }
    { exact STKd. }
    intros fx5 R5 M5 model5 RP5 HP5 MB5 HH5. rewrite ELB in HP5, HH5.
    assert (C5 : forall y, In y [2; 8; 9; 18; 19; 20; 21; 22]%nat -> getr R5 (reg y) = getr R3 (reg y)).
    { intros y Hy. rewrite (PMK.cs_of_preserved R4 R5 y RP5) by (revert y Hy; apply sub_in; vm_compute; reflexivity).
      apply KS4. revert y Hy. apply sub_in. vm_compute. reflexivity. }
    assert (BRc : PMFR.brange L ((B, A) :: LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M5 _ HH5); apply incl_refl).
    assert (EKd : PMK.ek L ((B, A) :: LB) (S - 64) PMSP.OPDEL_SCR [] M3 M5) by (apply (PMK.ek_of_hpres L); exact HP5).
    assert (SC0 : 0 <= PMSP.OPDEL_SCR) by (unfold PMSP.OPDEL_SCR; lia).
    assert (WHI : forall a, PMK.inW [] a -> S - 64 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
    assert (MOK5 : PMSP.model_ok model5) by (apply (PMFR.model_ok_but_vm model model5 MOK MB5)).
    pose proof (bv_unsigned_in_range 64 (getr R5 (reg 10))) as G5. change (bv_modulus 64) with (2 ^ 64) in G5.
    apply (tail fx5 R5 M5 model5 n q A B 0x58a20 (bv_unsigned (getr R5 (reg 10))) s5 (tg + 1) cr' MOK5 En Hn0 HnA HA HA8 (or_intror eq_refl)); try assumption.
    + rewrite (C5 2%nat) by PMK.inl. exact B2.
    + rewrite (C5 8%nat) by PMK.inl. exact B8.
    + rewrite (C5 9%nat) by PMK.inl. exact B9.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite (C5 18%nat) by PMK.inl. exact B18.
    + rewrite (C5 19%nat) by PMK.inl. exact B19.
    + rewrite (C5 20%nat) by PMK.inl. exact B20.
    + rewrite (C5 21%nat) by PMK.inl. exact B21.
    + rewrite (C5 22%nat) by PMK.inl. exact B22.
    + intros y Hy. rewrite (PMK.cs_of_preserved R4 R5 y RP5) by (revert y Hy; apply sub_in; vm_compute; reflexivity).
      rewrite (KS4 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). rewrite (KSR y) by (revert y Hy; apply sub_in; vm_compute; reflexivity).
      rewrite (KS1 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply KP. exact Hy.
    + unfold saves. repeat split; (apply (PMFR.u64_keep RSEGS L KL ((B, A) :: LB) (S - 64) PMSP.OPDEL_SCR [] M3 M5 EKd STKd SC0);
                                  [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| eassumption]).
    + pose proof MO3 as (EK3 & DK3 & _ & _).
      split; [apply (PMK.ek_trans L LB S 14336 _ M0 M3 M5 EK3)|].
      { apply (PMK.ek_callee_in' RSEGS L KL LB ((B, A) :: LB) S 14336 (S - 64) PMSP.OPDEL_SCR [(o, 24)] [] M3 M5 HP5); [intros y Hy; right; exact Hy
          | unfold PMSP.OPDEL_SCR; lia| lia| lia| destruct STOP; lia| intros b Hb; apply (PMFR.brange_hi L _ BRc b); right; exact Hb| intros a I; destruct (PMFR.inW_nil a I)]. }
      split; [apply (PMK.dk_trans L LB S 14336 M0 M3 M5 DK3);
              apply (PMK.dk_callee L LB ((B, A) :: LB) S 14336 (S - 64) PMSP.OPDEL_SCR [] M3 M5 HP5); [intros y Hy; right; exact Hy| unfold PMSP.OPDEL_SCR; lia| lia]|].
      split; [apply (PMK.stk_after RSEGS L KL ((B, A) :: LB) M3 M5 S 14336 (S - 64) PMSP.OPDEL_SCR [] STK3 HP5); unfold PMSP.OPDEL_SCR; lia|].
      apply (PMFR.defined_keep RSEGS L KL ((B, A) :: LB) (S - 64) PMSP.OPDEL_SCR [] M3 M5 EKd STKd SC0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact DO3].
    + apply (L5C.defined_agree M3 M5 B A); [apply (PMFR.ag_block RSEGS L KL ((B, A) :: LB) (S - 64) PMSP.OPDEL_SCR [] M3 M5 EKd STKd SC0 BRc WHI); left; reflexivity| exact DB3].
    + exact (L5C.model_but_vm_trans _ _ _ MB MB5).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grow_credit (x' : PM.vstr) (A : Z) :
  PM.tb_ok x tg -> PM.vs_cap x <= 2 ^ 27 -> 2 * PM.vs_cap x <= PM.vs_cap x' -> PM.vs_cap x' = A - 1 -> A <= 2 ^ 27 ->
  PMSP.credit_le (PM.pot_text L x tg) cr0 ->
  credit_ok L cr0 A /\ PMSP.credit_keep cr0 (debit L cr0 A) (PM.pot_text L x tg) (PM.pot_text L x' (tg + 1)) /\ tg <= 22.
Proof.
  intros (T0 & T1 & _) Hc Hc' Ec HA (CR1 & CR2).
  pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB.
  assert (Htg : tg <= 22).
  { destruct (Z.eq_dec tg 23) as [E|N]; [|lia]. rewrite E in T1. change (2 ^ 23) with 8388608 in T1. lia. }
  pose proof (PMF.pot_text_step L x x' tg Hc') as (P1 & P2).
  unfold PM.credit_add, PM.cost1, PM.pot_text in P1, P2, CR1, CR2 |- *. cbn [fst snd] in P1, P2, CR1, CR2 |- *. rewrite ?Ec in P1, P2 |- *.
  split; [unfold credit_ok; split; nia|]. split; [|exact Htg].
  unfold PMSP.credit_keep, debit. cbn [fst snd]. split; nia.
Qed.

(* [comment removed for export] *)
Lemma grow (fx : FPState) R M model (n q c A s5 : Z) (OWN : list (Z * Z)) :
  PMSP.model_ok model -> n = PM.vs_size x -> 1 <= n -> PM.vs_cap x = n -> PM.tb_ok x tg -> PMSP.credit_le (PM.pot_text L x tg) cr0 ->
  PM.tb_law A /\ 2 * n <= A - 1 /\ n + 2 <= A /\ A <= 2 ^ 27 /\ A mod 8 = 0 /\ 26 <= A ->
  ((s5 = 23 /\ OWN = [] /\ q = o + 1 /\ n = 22) \/ (s5 = c /\ OWN = [(q, c)] /\ 26 <= c <= 2 ^ 27 /\ n < c)) -> OWN = PM.vs_own x ->
  getr R (reg 1) = Z_to_bv 64 0x589fc ->
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 ch -> getr R (reg 9) = Z_to_bv 64 o -> getr R (reg 10) = Z_to_bv 64 A ->
  getr R (reg 18) = Z_to_bv 64 q -> getr R (reg 19) = Z_to_bv 64 A -> getr R (reg 20) = Z_to_bv 64 n -> getr R (reg 21) = Z_to_bv 64 s5 ->
  kept0 R -> saves M -> mem_ok M -> L5.defined M q n -> 0 <= q -> (q + n <= S - 14336 \/ (S <= q /\ q + n < 2 ^ 47)) ->
  hi_heap HI (OWN ++ LB) cr0 M (m_vmmaps model) -> model_but_vm model0 model ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb03b8 M model) K.
Proof.
  intros MOK En Hn1 FULL TBOK CR (LAW & LA1 & LA2 & LA3 & LA4 & LA5) CASE EOWN A1 A2 A8 A9 A10 A18 A19 A20 A21 KP SV MO DQ Hq0 Hq2 HH MB.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  assert (CAPB : PM.vs_cap x <= 2 ^ 27) by (rewrite FULL; lia).
  destruct (grow_credit (PM.VLong A (n + 1) 0) A TBOK CAPB ltac:(rewrite FULL; cbn [PM.vs_cap]; lia) ltac:(cbn [PM.vs_cap]; lia) LA3 CR) as (CROK & CK & Htg).
  assert (STKn : L5C.stk (hl_sptop L) M (S - 64) PMSP.OPNEW_SCR).
  { apply (PMK.stk_call L M S 14336 (S - 64) PMSP.OPNEW_SCR STK); [lia| unfold PMSP.OPNEW_SCR; lia| unfold PMSP.OPNEW_SCR; lia|].
    replace (S - 64) with (S + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  pose proof OPN as ON. unfold PMS.opnew_spec, PMSP.opnew_spec in ON. cbn [pa_opnew AD] in ON. unfold PMSP.cfg.
  apply (ON fx R M model K (OWN ++ LB) cr0 A (S - 64) 0x589fc HH MOK K0).
  { rewrite L5K.rl10. exact A10. }
  { lia. }
  { exact CROK. }
  { rewrite L5K.rl1. exact A1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. exact A2. }
  { rewrite L5K.rl4. rewrite (KP 4%nat) by (cbn; auto). exact Rtp0. }
  { exact STKn. }
  intros fx3 R3 M3 model3 B R3_10 RP3 FB HP3 MB3 HH3. rewrite L5K.rl10 in R3_10.
  destruct FB as ((FB0 & FB1 & FB2 & FB3 & FB4) & FBa & FBd).
  assert (C3 : forall y, In y [2; 8; 9; 18; 19; 20; 21]%nat -> getr R3 (reg y) = getr R (reg y)).
  { intros y Hy. apply (PMK.cs_of_preserved R R3 y RP3). revert y Hy. apply sub_in. vm_compute. reflexivity. }
  assert (BRX : PMFR.brange L (OWN ++ LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ cr0 M _ HH); apply incl_refl).
  assert (INL : incl LB (OWN ++ LB)) by (intros y Hy; apply in_or_app; right; exact Hy).
  assert (EKn : PMK.ek L (OWN ++ LB) (S - 64) PMSP.OPNEW_SCR [] M M3) by (apply (PMK.ek_of_hpres L); exact HP3).
  assert (SC0 : 0 <= PMSP.OPNEW_SCR) by (unfold PMSP.OPNEW_SCR; lia).
  assert (MOK3 : PMSP.model_ok model3) by (apply (PMFR.model_ok_but_vm model model3 MOK MB3)).
  assert (WHI : forall a, PMK.inW [] a -> S - 64 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
  (* [comment removed for export] *)
  assert (APT : B + A <= q \/ q + n <= B).
  { destruct CASE as [(_ & -> & -> & En22)|(_ & -> & Hc & Hnc)]; [left; unfold hl_ceil in FB4; lia|].
    destruct (FBa (q, c) ltac:(left; reflexivity)); cbn [fst snd] in *; lia. }
  apply (after_new fx3 R3 M3 model3 n q c A B s5 OWN (debit L cr0 A) MOK3 En Hn1 LA2 ltac:(lia) LA4 FULL CASE EOWN); try assumption.
  - rewrite (C3 2%nat) by PMK.inl. exact A2.
  - rewrite (C3 8%nat) by PMK.inl. exact A8.
  - rewrite (C3 9%nat) by PMK.inl. exact A9.
  - rewrite (C3 18%nat) by PMK.inl. exact A18.
  - rewrite (C3 19%nat) by PMK.inl. exact A19.
  - rewrite (C3 20%nat) by PMK.inl. exact A20.
  - rewrite (C3 21%nat) by PMK.inl. exact A21.
  - intros y Hy. rewrite (PMK.cs_of_preserved R R3 y RP3) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply KP. exact Hy.
  - destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
    unfold saves. repeat split; (apply (PMFR.u64_keep RSEGS L KL (OWN ++ LB) (S - 64) PMSP.OPNEW_SCR [] M M3 EKn STKn SC0);
                                 [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| eassumption]).
  - split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M3 EK)|].
    { apply (PMK.ek_callee_in' RSEGS L KL LB (OWN ++ LB) S 14336 (S - 64) PMSP.OPNEW_SCR [(o, 24)] [] M M3 HP3 INL);
        [unfold PMSP.OPNEW_SCR; lia| lia| lia| destruct STOP; lia| exact (PMFR.brange_hi L LB BRLB)| intros a I; destruct (PMFR.inW_nil a I)]. }
    split; [apply (PMK.dk_trans L LB S 14336 M0 M M3 DK);
            apply (PMK.dk_callee L LB (OWN ++ LB) S 14336 (S - 64) PMSP.OPNEW_SCR [] M M3 HP3 INL); [unfold PMSP.OPNEW_SCR; lia| lia]|].
    split; [apply (PMK.stk_after RSEGS L KL (OWN ++ LB) M M3 S 14336 (S - 64) PMSP.OPNEW_SCR [] STK HP3); unfold PMSP.OPNEW_SCR; lia|].
    apply (PMFR.defined_keep RSEGS L KL (OWN ++ LB) (S - 64) PMSP.OPNEW_SCR [] M M3 EKn STKn SC0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact DO].
  - (* [comment removed for export] *)
    destruct CASE as [(_ & -> & -> & En22)|(_ & -> & Hc & Hnc)].
    + apply (PMFR.defined_keep RSEGS L KL ([] ++ LB) (S - 64) PMSP.OPNEW_SCR [] M M3 EKn STKn SC0); [Lia.lia|Lia.lia| intros i Hi I; destruct (PMFR.inW_nil i I)|].
      apply (L5.defined_sub M o 24 (o + 1) n DO); Lia.lia.
    + apply (L5C.defined_agree M M3 q n); [|exact DQ].
      apply (L5C.agree_on_sub M M3 q c q n); [|lia|lia].
      apply (PMFR.ag_block RSEGS L KL ([(q, c)] ++ LB) (S - 64) PMSP.OPNEW_SCR [] M M3 EKn STKn SC0 BRX WHI). left. reflexivity.
  - lia.
  - destruct Hq2 as [X|[X _]]; [left; exact X| right; exact X].
  - exact (L5C.model_but_vm_trans _ _ _ MB MB3).
  - destruct TBOK as (T0 & T1 & _). rewrite FULL in T1. split; [lia|]. split; [cbn [PM.vs_cap]; rewrite Z.pow_add_r, Z.pow_1_r by lia; lia|]. split; [exact LAW| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma half2 c : c mod 2 = 0 -> 2 * ((c + 1) / 2) = c.
Proof.
  intros Hc. assert (E : c = 2 * (c / 2)) by (apply Z_div_exact_2; lia). set (k := c / 2) in *. rewrite E.
  replace (2 * k + 1) with (k * 2 + 1) by lia. rewrite Z.div_add_l by lia. change (1 / 2) with 0. lia.
Qed.
Lemma capm1 c : 0 <= c < 2 ^ 63 -> ((c mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64 = c - 1 + (if Z.eqb c 0 then 2 ^ 64 else 0).
Proof.
  intros Hc. rewrite (Z.mod_small c) by lia. destruct (Z.eqb_spec c 0) as [->|N]; [reflexivity|].
  replace (c + 18446744073709551615) with ((c - 1) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.
Lemma wrap_ne n0 c : 0 <= n0 -> n0 + 1 < c -> c < 2 ^ 62 -> c mod 2 = 0 ->
  1 <= ((n0 - ((((2 * ((c + 1) / 2)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64).
Proof.
  intros H0 H1 H2 Hc. rewrite half2 by exact Hc. rewrite capm1 by lia. destruct (Z.eqb_spec c 0) as [E|N]; [lia|].
  replace (n0 - (c - 1 + 0)) with ((n0 - c + 1 + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.
Lemma wrap_eq n0 c : n0 + 1 = c -> 0 < c < 2 ^ 62 -> c mod 2 = 0 ->
  ((n0 - ((((2 * ((c + 1) / 2)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64) < 1.
Proof.
  intros H1 H2 Hc. rewrite half2 by exact Hc. rewrite capm1 by lia. destruct (Z.eqb_spec c 0) as [E|N]; [lia|].
  replace (n0 - (c - 1 + 0)) with 0 by lia. rewrite Z.mod_0_l by lia. lia.
Qed.
Lemma newcnt c : 8 <= c -> c mod 8 = 0 -> 8 * ((4 * ((c + 1) / 2) - 2) / 8) + 8 = 2 * c.
Proof.
  intros Hc H8. assert (E : c = 8 * (c / 8)) by (apply Z_div_exact_2; lia). set (k := c / 8) in *. rewrite E.
  replace (8 * k + 1) with ((4 * k) * 2 + 1) by lia. rewrite Z.div_add_l by lia. change (1 / 2) with 0.
  replace (4 * (4 * k + 0) - 2) with ((2 * k - 1) * 8 + 6) by lia. rewrite Z.div_add_l by lia. change (6 / 8) with 0. lia.
Qed.

(* [comment removed for export] *)
Lemma mem_ok_frame (M M' : word -> option byte) :
  mem_ok M -> mem_grows M M' -> (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 64 <= a < S - 64 + 64) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> mem_ok M'.
Proof.
  intros (EK & DK & STK & DO) MG FR.
  split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M' EK);
          apply (PMK.ek_piece_in RSEGS L KL LB S 14336 _ M M' (fun a => S - 64 <= a < S - 64 + 64) FR STK (PMFR.brange_hi L LB BRLB)); intros a X; left; lia|].
  split; [apply (PMK.dk_trans L LB S 14336 M0 M M' DK); apply PMK.dk_grows; exact MG|].
  split; [exact (PMK.stk_grows L M M' S 14336 MG STK)|]. intros i Hi. apply MG. apply DO. exact Hi.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pb_entry (fx : FPState) :
  PMSP.model_ok model0 -> hi_heap HI (PM.vs_own x ++ LB) cr0 M0 (m_vmmaps model0) ->
  getr R0 (reg 10) = Z_to_bv 64 o -> PM.vstr_at RSEGS PMSP.T3 M0 o x -> PM.tb_ok x tg -> PMSP.credit_le (PM.pot_text L x tg) cr0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0x58938 M0 model0) K.
Proof.
  intros MOK HH A10 VS TBOK CR.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK0 as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  pose proof VS as (DO & _ & _).
  pose proof (L5C.stk_writable RSEGS _ M0 S 14336 STK0) as WR.
  assert (WRo : L5.writable RSEGS M0 o 24) by (apply (L5C.writable_of_defined RSEGS M0 o 24 DO); lia).
  assert (HO : bv_unsigned (getr R0 (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
  assert (HC : bv_unsigned (getr R0 (reg 11)) = ch) by (rewrite A11; apply L5.unsigned_lit; lia).
  assert (A8c : getr R0 (reg 11) = Z_to_bv 64 ch) by exact A11.
  assert (MO0 : mem_ok M0).
  { split; [apply PMK.ek_refl|]. split; [apply PMK.dk_refl|]. split; [exact STK0| exact DO]. }
  assert (KP0 : kept0 R0) by (intros y _; reflexivity).
  bvr. unfold PMSP.cfg.
  assert (CASE : (exists n0, x = PM.VShort n0) \/ (exists c n0 p, x = PM.VLong c n0 p)) by (destruct x as [a|a b d]; [left; exists a | right; exists a, b, d]; reflexivity).
  destruct CASE as [(n0 & Es)|(c & n0 & p & Es)]; pose proof SZ as SZx; rewrite Es in VS, HH, SZx.
  - (* [comment removed for export] *)
    destruct VS as (_ & _ & Hn0 & B0). cbn [PM.vs_size] in SZx. cbn [app] in HH.
    destruct (Z_lt_le_dec n0 22) as [LT|GE].
    + (* [comment removed for export] *)
      pose proof (PNSPBP.pbS_conc fx R0 M0 (fun j => match j with 2%nat => S | 33%nat => 2 * n0 | _ => 0 end)) as PP.
      cbn beta iota in PP. rewrite HO, HC in PP.
      PMK.feed PP ltac:(first [PMK.sc | apply PMF.even_byte]).
      PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
        destruct pvzP as (MG1 & _ & FRZ0 & MS1 & KS1 & _ & _ & C2 & C1 & C0 & _)); PMK.pvz_clrT.
      replace (2 * n0 / 2) with n0 in C2, C1 by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
      set (P := fun a => (S - 64 <= a < S - 64 + 64) \/ (o <= a < o + 24)).
      assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
      { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; unfold P; lia| intro X; apply N; unfold P; lia]. }
      apply (PMK.spiece RSEGS L HI KL HIok LB cr0 M0 model0 fx fx1 R0 0x58938 R1 0x58a68 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
      { intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L LB M0 S 14336 a STK0); lia. }
      { intros a. unfold P. apply PMK.or_dec; apply PMK.rng_dec. }
      intros HH1.
      assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by PMK.inl; exact Rra0).
      unfold PMK.cfg.
      eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x58a68 W_57428 r F_57428 ltac:(reflexivity) D_57428 RA1 Hr1 Hr2)|].
      apply (KONT fx1 R1 M1 model0 (PM.VShort (n0 + 1)) tg cr0); [| | rewrite Es; reflexivity | | | | | apply L5C.model_but_vm_refl | exact HH1].
      * apply PMK.preserved_by_index. intros y Hy. apply KS1. revert y Hy. apply sub_in. vm_compute. reflexivity.
      * split; [intros i Hi; apply MG1; apply DO; exact Hi|]. split; [exact I|]. split; [lia|]. replace (2 * (n0 + 1)) with (2 * n0 + 2) by lia. exact C0.
      * rewrite Es in TBOK. unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK.
      * intros _. rewrite Es. split; reflexivity.
      * apply (PMK.hpres_of L LB S 14336 _ M0 M1).
        -- apply (PMK.ek_piece_in RSEGS L KL LB S 14336 _ M0 M1 P FRZ STK0 (PMFR.brange_hi L LB BRLB)). intros a [X|X]; [left; lia| right].
           apply PMK.inW_here. lia.
        -- destruct (PMK.stk_grows L M0 M1 S 14336 MG1 STK0) as (_ & _ & _ & _ & D1). exact D1.
        -- apply PMK.dk_grows. exact MG1.
      * rewrite Es. unfold PMSP.credit_keep, PM.pot_text. cbn [PM.vs_cap]. lia.
    + (* [comment removed for export] *)
      assert (En0 : n0 = 22) by lia.
      pose proof (PNSPBP.pbGS_conc fx R0 M0 (fun j => match j with 2%nat => S | _ => 0 end)) as PP.
      cbn beta iota in PP. rewrite HO, HC in PP. rewrite En0 in B0.
      PMK.feed PP ltac:(first [PMK.sc]).
      destruct PP as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & F1 & F2 & F8 & F9 & F10 & _ & F18 & F19 & F20 & F21 & SVS).
      apply (PMK.spiece RSEGS L HI KL HIok LB cr0 M0 model0 fx fx1 R0 0x58938 R1 0xb03b8 M1 (fun a => S - 64 <= a < S - 64 + 64) K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ1).
      { intros a Pa. apply (PMK.cwr_stack L LB M0 S 14336 a STK0); lia. }
      { intros a. apply PMK.rng_dec. }
      intros HH1.
      destruct (PMF.tb_law_first 23 48 ltac:(lia) ltac:(lia) eq_refl) as (LAW & LA1 & LA2 & LA3 & LA4).
      apply (grow fx1 R1 M1 model0 22 (o + 1) 0 48 23 [] MOK ltac:(rewrite Es; cbn [PM.vs_size]; lia) ltac:(lia) ltac:(rewrite Es; reflexivity) TBOK CR).
      * split; [exact LAW|]. lia.
      * left. repeat split; reflexivity.
      * rewrite Es. reflexivity.
      * exact F1.
      * exact F2.
      * rewrite F8. exact A11.
      * rewrite F9. exact A10.
      * exact F10.
      * exact F18.
      * exact F19.
      * exact F20.
      * exact F21.
      * intros y Hy. apply KS1. revert y Hy. apply sub_in. vm_compute. reflexivity.
      * destruct SVS as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). unfold saves. repeat split; assumption.
      * exact (mem_ok_frame M0 M1 MO0 MG1 FRZ1).
      * intros i Hi. apply MG1. replace (o + 1 + i) with (o + (1 + i)) by lia. apply DO. lia.
      * lia.
      * right. split; lia.
      * exact HH1.
      * apply L5C.model_but_vm_refl.
  - (* [comment removed for export] *)
    pose proof VS as (_ & _ & W0 & W8 & W16 & Hnc & Hc & Hce & DP & _). cbn [PM.vs_size] in SZx. cbn [app] in HH.
    assert (Ip : In (p, c) ((p, c) :: LB)) by (left; reflexivity).
    destruct (PMFR.brange_of_heap L HI HIok _ _ cr0 M0 _ HH (incl_refl _) p c Ip) as (Pp0 & Pp1 & Pp4).
    pose proof (PMF.u8_of_u64 RSEGS M0 o (c + 1) ltac:(lia) W0) as B0. pose proof (PMF.odd_byte c Hce ltac:(lia)) as ODB.
    assert (TB1 : Z.testbit (c + 1) 0 = true) by (rewrite <- (Z.mod_pow2_bits_low (c + 1) 8 0) by lia; exact ODB).
    assert (H33 : 0 <= (c + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)); lia).
    destruct (Z_lt_le_dec (n0 + 1) c) as [LT|GE].
    + (* [comment removed for export] *)
      pose proof (wrap_ne n0 c ltac:(lia) LT ltac:(lia) Hce) as WNE.
      assert (WRp : L5.writable RSEGS M0 (p + n0) 2) by (apply (L5C.writable_of_defined RSEGS M0 (p + n0) 2); [apply (L5.defined_sub M0 p c (p + n0) 2 DP); lia|lia|lia]).
      assert (Dpo : p + n0 + 2 <= o \/ o + 24 <= p + n0) by (left; unfold hl_ceil in Pp4; lia).
      assert (Dpf : p + n0 + 2 <= S - 64 \/ S - 64 + 64 <= p + n0) by (left; unfold hl_ceil in Pp4; lia).
      pose proof (PNSPBP.pbLI_conc fx R0 M0 (fun j => match j with 2%nat => S | 33%nat => (c + 1) mod 256 | 34%nat => n0 | 35%nat => p | 36%nat => c + 1 | _ => 0 end)) as PP.
      cbn beta iota in PP. rewrite HO, HC in PP.
      PMK.feed PP ltac:(first [PMK.sc]).
      PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
        destruct pvzP as (MG1 & _ & FRZ0 & MS1 & KS1 & _ & _ & _ & C2 & C1 & C8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & CW0 & CW16)); PMK.pvz_clrT.
      set (P := fun a => (S - 64 <= a < S - 64 + 64) \/ (o <= a < o + 24) \/ (p + n0 <= a < p + n0 + 2)).
      assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
      { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; unfold P; lia| intro X; apply N; unfold P; lia| intro X; apply N; unfold P; lia]. }
      apply (PMK.spiece RSEGS L HI KL HIok ((p, c) :: LB) cr0 M0 model0 fx fx1 R0 0x58938 R1 0x58a68 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
      { intros a Pa. unfold P in Pa. destruct Pa as [X|[X|X]];
          [apply (PMK.cwr_stack L _ M0 S 14336 a STK0); lia| apply (PMK.cwr_stack L _ M0 S 14336 a STK0); lia| apply (PMK.cwr_block L _ p c a Ip); lia]. }
      { intros a. unfold P. apply PMK.or_dec; [|apply PMK.or_dec]; apply PMK.rng_dec. }
      intros HH1.
      assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by PMK.inl; exact Rra0).
      unfold PMK.cfg.
      eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x58a68 W_57428 r F_57428 ltac:(reflexivity) D_57428 RA1 Hr1 Hr2)|].
      assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (forall i, a <= i < a + m -> ~ P i) -> L5C.agree_on M0 M1 a m).
      { intros a0 m0 Ha0 Hm0 X i Hi. apply FRZ; [lia| apply X; exact Hi]. }
      apply (KONT fx1 R1 M1 model0 (PM.VLong c (n0 + 1) p) tg cr0); [| | rewrite Es; reflexivity | | | | | apply L5C.model_but_vm_refl | exact HH1].
      * apply PMK.preserved_by_index. intros y Hy. apply KS1. revert y Hy. apply sub_in. vm_compute. reflexivity.
      * split; [intros i Hi; apply MG1; apply DO; exact Hi|]. split; [exact I|].
        split; [exact CW0|]. split; [exact C8|]. split; [exact CW16|].
        split; [lia|]. split; [lia|]. split; [exact Hce|]. split; [intros i Hi; apply MG1; apply DP; exact Hi| exact I].
      * rewrite Es in TBOK. unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK.
      * intros _. rewrite Es. split; reflexivity.
      * apply (PMK.hpres_of L LB S 14336 _ M0 M1).
        -- apply (PMK.ek_piece L LB S 14336 _ M0 M1 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa. destruct Pa as [X|[X|X]].
           ++ destruct CA as [((b1 & b2) & Hb & Hr)|[[S1 S2]|[IM _]]]; [pose proof (PMFR.brange_hi L LB BRLB _ Hb) as Z4; cbn in Hr, Z4; unfold hl_ceil in Z4; lia| apply S2; lia| pose proof (PMK.kl_img RSEGS L KL); lia].
           ++ apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
           ++ exact (own_not_client [(p, c)] LB cr0 M0 _ p c a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA).
        -- destruct (PMK.stk_grows L M0 M1 S 14336 MG1 STK0) as (_ & _ & _ & _ & D1). exact D1.
        -- apply PMK.dk_grows. exact MG1.
      * rewrite Es. unfold PMSP.credit_keep, PM.pot_text. cbn [PM.vs_cap]. lia.
    + (* [comment removed for export] *)
      assert (En0 : n0 + 1 = c) by lia.
      pose proof (wrap_eq n0 c En0 ltac:(lia) Hce) as WEQ.
      pose proof (PNSPBP.pbLG_conc fx R0 M0 (fun j => match j with 2%nat => S | 33%nat => (c + 1) mod 256 | 34%nat => n0 | 35%nat => p | 36%nat => c + 1 | _ => 0 end)) as PP.
      cbn beta iota in PP. rewrite HO, HC in PP.
      PMK.feed PP ltac:(first [PMK.sc]).
      destruct PP as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & F1 & F2 & F8 & F9 & F10 & _ & _ & F18 & F19 & F20 & F21 & SVS).
      assert (TBL : PM.tb_law c /\ 1 <= tg) by (pose proof TBOK as TB; rewrite Es in TB; destruct TB as (_ & _ & TB3); exact TB3).
      destruct TBL as (TLAW & Htg1).
      assert (C8 : c mod 8 = 0).
      { destruct TLAW as (j & J0 & J1 & J2 & J3). apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 (2 ^ (3 + j)) c).
        - exists (2 ^ j). rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. lia.
        - apply Z.mod_divide; [lia| exact J3]. }
      assert (Ek : c = 8 * (c / 8)) by (apply Z_div_exact_2; lia).
      assert (EQA : Z.lor (Z.max (2 * (c - 1)) c) 7 + 1 = 2 * c).
      { rewrite Z.max_l by lia. rewrite PMF.lor7 by lia. set (k := c / 8) in *. rewrite Ek.
        replace (2 * (8 * k - 1)) with ((2 * k - 1) * 8 + 6) by lia. rewrite Z.div_add_l by lia. change (6 / 8) with 0. lia. }
      pose proof (newcnt c ltac:(lia) C8) as NC. pose proof (half2 c Hce) as H2.
      destruct (PMF.tb_law_step c c (2 * c) TLAW ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (eq_sym EQA)) as (LAW & LA1 & LA2 & LA3 & LA4).
      apply (PMK.spiece RSEGS L HI KL HIok ((p, c) :: LB) cr0 M0 model0 fx fx1 R0 0x58938 R1 0xb03b8 M1 (fun a => S - 64 <= a < S - 64 + 64) K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ1).
      { intros a Pa. apply (PMK.cwr_stack L _ M0 S 14336 a STK0); lia. }
      { intros a. apply PMK.rng_dec. }
      intros HH1.
      apply (grow fx1 R1 M1 model0 n0 p c (2 * c) c [(p, c)] MOK ltac:(rewrite Es; reflexivity) ltac:(lia) ltac:(rewrite Es; cbn [PM.vs_cap]; lia) TBOK CR).
      * split; [exact LAW|]. lia.
      * right. split; [reflexivity|]. split; [reflexivity|]. lia.
      * rewrite Es. reflexivity.
      * exact F1.
      * exact F2.
      * rewrite F8. exact A11.
      * rewrite F9. exact A10.
      * rewrite F10, NC. reflexivity.
      * exact F18.
      * rewrite F19, NC. reflexivity.
      * rewrite F20, H2. f_equal. lia.
      * rewrite F21, H2. reflexivity.
      * intros y Hy. apply KS1. revert y Hy. apply sub_in. vm_compute. reflexivity.
      * destruct SVS as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C9). unfold saves. repeat split; assumption.
      * exact (mem_ok_frame M0 M1 MO0 MG1 FRZ1).
      * intros i Hi. apply MG1. apply DP. lia.
      * lia.
      * left. unfold hl_ceil in Pp4. lia.
      * exact HH1.
      * apply L5C.model_but_vm_refl.
Qed.

End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem str_push_back_ok : PMS.opnew_spec L HI -> PMS.opdel_spec L HI -> PNRS.str_push_back_spec L HI.
Proof.
  intros OPN OPD. unfold PNRS.str_push_back_spec, PNR.str_push_back_spec.
  intros fx R M model K LB cr o c sp r tg x HH MOK K0 ENT A10 A11 Hc Ho1 Ho2 Ho3 VS TBOK SZ CR KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  change (PMSP.pm_scr 1) with 14336 in *.
  assert (BRLB : PMFR.brange L LB).
  { apply (PMFR.brange_of_heap L HI HIok _ LB cr M _ HH). intros y Hy. apply in_or_app. right. exact Hy. }
  cbn [PNL.pn_str_push_back PnLayoutS_u.NADDR_S] in *.
  exact (pb_entry R M model K LB cr o c sp r tg x Rra RAok Rsp Rtp K0 STK Ho1 Ho2 Ho3 Hc A11 SZ BRLB OPN OPD KONT fx MOK HH A10 VS TBOK CR).
Qed.

End WithHeap.
End PNSPB.
