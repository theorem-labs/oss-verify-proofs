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
     PmLayout PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmFrame PmParKit PgSrc PgV8 PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u
     L5KnA_u PnSrcSMemmove_u PnSVu8GrowP_u Bs0_code_3853c_38540_u Bs0_code_383fc_38400_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSVG.
Import PMS.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation v8_atP := (PGV8.v8_at RSEGS PMSP.T3 PMSP.T4).

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
Lemma defined_of_zeros M a n : L5KA.zeros_at M a n -> L5.defined M a n.
Proof. intros Z i Hi. rewrite (Z i Hi). discriminate. Qed.

Lemma v8_case (y : PGV8.v8) : y = PGV8.V8Null \/ exists b n c, y = PGV8.V8Blk b n c.
Proof. destruct y; [left; reflexivity| right; eexists _, _, _; reflexivity]. Qed.

(* [comment removed for export] *)
Lemma room_mod n c : 0 <= n <= c -> c <= 2 ^ 27 -> ((18446744073709551615 * n) mod 2 ^ 64 + c) mod 2 ^ 64 = c - n.
Proof.
  intros H1 H2. rewrite Zplus_mod_idemp_l. replace (18446744073709551615 * n + c) with ((c - n) + n * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma v8_at_agree M M' p y (P : Z -> Prop) :
  v8_atP M p y -> mem_grows M M' -> 0 <= p -> p + 24 <= 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, p <= a < p + 24 -> ~ P a) -> v8_atP M' p y.
Proof.
  intros VS MG Hp0 Hp1 FR NP.
  assert (AG : L5C.agree_on M M' p 24) by (intros i Hi; apply FR; [lia| apply NP; lia]).
  destruct y as [|b n c].
  - destruct VS as (D & _ & U0 & U8 & U16). split; [exact (L5C.defined_agree M M' p 24 AG D)|]. split; [exact I|].
    split; [apply (L5C.u64_at_agree RSEGS M M' p); [apply (L5C.agree_on_sub M M' p 24); [exact AG|lia|lia]|lia|lia|exact U0]|].
    split; [apply (L5C.u64_at_agree RSEGS M M' (p + 8)); [apply (L5C.agree_on_sub M M' p 24); [exact AG|lia|lia]|lia|lia|exact U8]|].
    apply (L5C.u64_at_agree RSEGS M M' (p + 16)); [apply (L5C.agree_on_sub M M' p 24); [exact AG|lia|lia]|lia|lia|exact U16].
  - destruct VS as (D & _ & U0 & U8 & U16 & H1 & H2 & H3 & H4 & Db & _ & _). split; [exact (L5C.defined_agree M M' p 24 AG D)|]. split; [exact I|].
    split; [apply (L5C.u64_at_agree RSEGS M M' p); [apply (L5C.agree_on_sub M M' p 24); [exact AG|lia|lia]|lia|lia|exact U0]|].
    split; [apply (L5C.u64_at_agree RSEGS M M' (p + 8)); [apply (L5C.agree_on_sub M M' p 24); [exact AG|lia|lia]|lia|lia|exact U8]|].
    split; [apply (L5C.u64_at_agree RSEGS M M' (p + 16)); [apply (L5C.agree_on_sub M M' p 24); [exact AG|lia|lia]|lia|lia|exact U16]|].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [intros i Hi; apply MG; apply Db; exact Hi|]. split; exact I.
Qed.

(* [comment removed for export] *)
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (cr0 : credit).
Variables (v S r g ns : Z) (x : PGV8.v8).        (* [comment removed for export] *)
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis K0 : K [].
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S 14336.
Hypothesis Hv1 : S <= v.
Hypothesis Hv2 : v + 24 <= hl_sptop L.
Hypothesis Hv3 : v mod 8 = 0.
Hypothesis OK0 : PGV8.v8_ok x g.
Hypothesis GROWOK : PGV8.v8_grow_ok x ns.
Hypothesis Hns : 0 <= ns < 2 ^ 64.
Hypothesis BRLB : PMFR.brange L LB.
Hypothesis OPN : PMS.opnew_spec L HI.
Hypothesis OPD : PMS.opdel_spec L HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : PGV8.v8) (g' : Z) (cr' : credit),
  regs_preserved R0 R' -> v8_atP M' v x' -> PGV8.v8_size x' = ns -> PGV8.v8_ok x' g' ->
  PGV8.v8_cap x <= PGV8.v8_cap x' ->
  (PGV8.v8_size x' <= PGV8.v8_cap x -> PGV8.v8_own x' = PGV8.v8_own x /\ PGV8.v8_cap x' = PGV8.v8_cap x /\ g' = g) ->
  (PGV8.v8_cap x' = PGV8.v8_cap x \/ PGV8.v8_cap x' = Z.max (2 * PGV8.v8_cap x) ns) ->
  L5C.hpres L LB S (PMSP.pm_scr 1) [(v, 24)] M0 M' ->
  PMSP.credit_keep cr0 cr' (PGV8.pot_v8 L x g) (PGV8.pot_v8 L x' g') ->
  model_but_vm model0 model' -> hi_heap HI (PGV8.v8_own x' ++ LB) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))).
(* [comment removed for export] *)
Definition kept0 (R : bvmap 5 word) : Prop := forall y, In y [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg y) = getr R0 (reg y).
Definition gframe (M : word -> option byte) (k : Z) : Prop :=
  saves M /\ L5.u64_at RSEGS M (S - 32) v /\ L5.u64_at RSEGS M (S - 40) 0 /\ L5.u64_at RSEGS M (S - 72) 0x39768
  /\ L5.u64_at RSEGS M (S - 80) v /\ L5.u64_at RSEGS M (S - 88) k /\ L5.u64_at RSEGS M (S - 96) (bv_unsigned (getr R0 (reg 18))).
(* [comment removed for export] *)
Definition mem_ok (M : word -> option byte) : Prop :=
  PMK.ek L LB S 14336 [(v, 24)] M0 M /\ PMK.dk L LB S 14336 M0 M /\ L5C.stk (hl_sptop L) M S 14336 /\ L5.defined M v 24.

Lemma regs_back (R1 : bvmap 5 word) :
  getr R1 (reg 2) = Z_to_bv 64 S -> getr R1 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) ->
  getr R1 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) -> getr R1 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) ->
  kept0 R1 -> regs_preserved R0 R1.
Proof.
  intros E2 E8 E9 E18 KP. apply PMK.preserved_by_index. intros y Hy. unfold PMK.cs_all in Hy. cbn in Hy.
  destruct Hy as [<-|Hy]; [rewrite E2, Rsp0; reflexivity|].
  destruct Hy as [<-|Hy]; [apply KP; PMK.inl|]. destruct Hy as [<-|Hy]; [apply KP; PMK.inl|].
  destruct Hy as [<-|Hy]; [rewrite E8; apply Z_to_bv_bv_unsigned|]. destruct Hy as [<-|Hy]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
  destruct Hy as [<-|Hy]; [rewrite E18; apply Z_to_bv_bv_unsigned|].
  apply KP. destruct Hy as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; PMK.inl.
Qed.

(* [comment removed for export] *)
Lemma frame_not_client a : S - 14336 <= a < S -> ~ client_addr L LB S 14336 a.
Proof.
  intros Ha [((bb & mm) & Hb & Hr)|[[S1 S2]|[IM NS]]].
  - pose proof (PMFR.brange_hi L LB BRLB (bb, mm) Hb) as X. cbn in Hr, X. pose proof STK0 as (_ & SLO & _). lia.
  - apply S2. exact Ha.
  - pose proof (PMK.kl_img _ _ KL). pose proof STK0 as (_ & SLO & _ & STOP & _). lia.
Qed.

Ltac bvr1 R y := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg y))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat; bvr1 R0 23%nat.

(* [comment removed for export] *)
Lemma mem_ok_frame (M M' : word -> option byte) :
  mem_ok M -> mem_grows M M' -> (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 96 <= a < S - 96 + 96) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> mem_ok M'.
Proof.
  intros (EK & DK & STK & DO) MG FR.
  split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M' EK);
          apply (PMK.ek_piece_in RSEGS L KL LB S 14336 _ M M' (fun a => S - 96 <= a < S - 96 + 96) FR STK (PMFR.brange_hi L LB BRLB)); intros a X; left; lia|].
  split; [apply (PMK.dk_trans L LB S 14336 M0 M M' DK); apply PMK.dk_grows; exact MG|].
  split; [exact (PMK.stk_grows L M M' S 14336 MG STK)|]. intros i Hi. apply MG. apply DO. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma grow_credit (A : Z) b' n' :
  PGV8.v8_cap x <= 2 ^ 26 -> 2 * PGV8.v8_cap x <= A -> 1 <= A <= 2 ^ 27 ->
  PMSP.credit_le (PGV8.pot_v8 L x g) cr0 ->
  credit_ok L cr0 A /\ PMSP.credit_keep cr0 (debit L cr0 A) (PGV8.pot_v8 L x g) (PGV8.pot_v8 L (PGV8.V8Blk b' n' A) (g + 1)) /\ PGV8.v8_ok (PGV8.V8Blk b' n' A) (g + 1).
Proof.
  intros Hc HA HA1 (CR1 & CR2).
  pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB.
  pose proof (PGV8.v8_ok_grow x g b' n' A OK0 HA HA1) as OK1.
  destruct (PGV8.pot_v8_grow L x g A (proj1 HK) OK0 HA b' n' OK1) as (P1 & P2).
  pose proof (PGV8.v8_ok_cap _ _ OK0) as (G0 & _). pose proof (PGV8.v8_ok_cap _ _ OK1) as (G1 & _).
  unfold PGV8.pot_v8 in P1, P2, CR1, CR2 |- *. cbn [fst snd PGV8.v8_cap] in P1, P2, CR1, CR2 |- *.
  split; [unfold credit_ok; split; nia|]. split; [|exact OK1].
  unfold PMSP.credit_keep, debit. cbn [fst snd]. split; nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tail_del (fx : FPState) R M model (b n c k A B a0 : Z) (cr' : credit) :
  PMSP.model_ok model -> x = PGV8.V8Blk b n c -> ns = n + k -> 1 <= k -> n + k <= A -> 1 <= A <= 2 ^ 27 -> 2 * c <= A -> (A = 2 * c \/ A = n + k) -> 0 <= a0 < 2 ^ 64 ->
  0 <= n <= c -> 1 <= c -> c < n + k ->
  getr R (reg 2) = Z_to_bv 64 (S - 96) -> getr R (reg 8) = Z_to_bv 64 (S - 64) -> getr R (reg 9) = Z_to_bv 64 v -> getr R (reg 10) = Z_to_bv 64 a0 ->
  getr R (reg 18) = Z_to_bv 64 B ->
  kept0 R -> saves M -> L5.u64_at RSEGS M (S - 32) v -> L5.u64_at RSEGS M (S - 40) (B + A) -> L5.u64_at RSEGS M (S - 48) (n + (B + k)) ->
  L5.u64_at RSEGS M (S - 56) (n + B) -> L5.u64_at RSEGS M (S - 64) B -> L5.u64_at RSEGS M (S - 72) 0x39780 -> L5.u64_at RSEGS M (S - 80) v ->
  L5.u64_at RSEGS M (S - 88) k -> L5.u64_at RSEGS M (S - 96) (bv_unsigned (getr R0 (reg 18))) ->
  L5.u64_at RSEGS M v b -> L5.u64_at RSEGS M (v + 8) (b + n) -> L5.u64_at RSEGS M (v + 16) (b + c) -> mem_ok M ->
  L5.defined M B A -> 4096 <= B -> B + A <= hl_ceil L -> B mod 16 = 0 -> B <> b ->
  hi_heap HI ((B, A) :: (b, c) :: LB) cr' M (m_vmmaps model) -> model_but_vm model0 model ->
  PGV8.v8_ok (PGV8.V8Blk B (n + k) A) (g + 1) ->
  PMSP.credit_keep cr0 cr' (PGV8.pot_v8 L x g) (PGV8.pot_v8 L (PGV8.V8Blk B (n + k) A) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39964 M model) K.
Proof.
  intros MOK Ex Ens Hk HnA HA H2c AMX Ha0 Hnc Hc1 Hroom A2 A8 A9 A10 A18 KP SV C32 C40 C48 C56 C64 C72 C80 C88 C96 W0 W8 W16 MO DB HB0 HB1 HB16 NBb HH MB OK1 CK.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  assert (WRo : L5.writable RSEGS M v 24) by (apply (L5C.writable_of_defined RSEGS M v 24 DO); lia).
  assert (WRB : L5.writable RSEGS M B A) by (apply (L5C.writable_of_defined RSEGS M B A DB); lia).
  destruct SV as (S8 & S16 & S24). bvr.
  assert (Ib : In (b, c) ((B, A) :: (b, c) :: LB)) by (right; left; reflexivity).
  destruct (PMFR.brange_of_heap L HI HIok _ _ cr' M _ HH (incl_refl _) b c Ib) as (Pb0 & Pb1 & Pb4).
  LeanFeed.pfeed PP (PNSVGP.vgQ_conc fx R M (fun j => match j with 2%nat => S | 10%nat => v | 33%nat => b | 34%nat => n | 35%nat => c | 37%nat => B | 38%nat => A | 43%nat => k
                | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
                | 47%nat => bv_unsigned (getr R0 (reg 18)) | 54%nat => a0 | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG1 & _ & FRZ0 & MS1 & KS1 & F1 & F2 & F8 & F9 & F10 & F11 & F12 & F13 & F18 & D40 & D64 & C16 & D48 & C8 & D56 & C0 & D8 & D16 & D24 & D32 & D72 & D80 & D88 & D96));
    PMK.pvz_clrT.
  set (P := fun a => (S - 96 <= a < S - 96 + 96) \/ (v <= a < v + 24)).
  assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; unfold P; lia| intro X; apply N; unfold P; lia]. }
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok ((B, A) :: (b, c) :: LB) cr' M model fx fx1 R 0x39964 R1 0x56720 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
  { intros a Pa. unfold P in Pa. destruct Pa as [X|X]; apply (PMK.cwr_stack L _ M S 14336 a STK); lia. }
  { intros a. unfold P. apply PMK.or_dec; apply PMK.rng_dec. }
  intros HH1.
  (* [comment removed for export] *)
  set (LBc := (B, A) :: (b, c) :: LB).
  assert (ELB : lb_remove b LBc = (B, A) :: LB).
  { unfold LBc. cbn [lb_remove fst]. destruct (Z.eqb_spec B b) as [X|_]; [exfalso; exact (NBb X)|]. rewrite Z.eqb_refl. reflexivity. }
  pose proof (PMK.stk_grows L M M1 S 14336 MG1 STK) as STK1.
  assert (STKd : L5C.stk (hl_sptop L) M1 (S - 64) PMSP.OPDEL_SCR).
  { apply (PMK.stk_call L M1 S 14336 (S - 64) PMSP.OPDEL_SCR STK1); [lia| unfold PMSP.OPDEL_SCR; lia| unfold PMSP.OPDEL_SCR; lia|].
    replace (S - 64) with (S + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  pose proof OPD as OD. unfold PMS.opdel_spec, PMSP.opdel_spec, PMSP.opdel_spec_at in OD. cbn [pa_opdel AD] in OD.
  apply (OD fx1 R1 M1 model K LBc cr' b c (S - 64) 0x39788 HH1 MOK K0 Ib).
  { rewrite L5K.rl10. exact F10. }
  { rewrite L5K.rl1. exact F1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. exact F2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by PMK.inl. rewrite (KP 4%nat) by PMK.inl. exact Rtp0. }
  { exact STKd. }
  intros fx5 R5 M5 model5 RP5 HP5 MB5 HH5. rewrite ELB in HP5, HH5.
  assert (BRc : PMFR.brange L ((B, A) :: LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M5 _ HH5); apply incl_refl).
  assert (EKd : PMK.ek L ((B, A) :: LB) (S - 64) PMSP.OPDEL_SCR [] M1 M5) by (apply (PMK.ek_of_hpres L); exact HP5).
  assert (SC0 : 0 <= PMSP.OPDEL_SCR) by (unfold PMSP.OPDEL_SCR; lia).
  assert (WHI : forall a, PMK.inW [] a -> S - 64 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
  assert (STK5 : L5C.stk (hl_sptop L) M5 S 14336) by (apply (PMK.stk_after RSEGS L KL ((B, A) :: LB) M1 M5 S 14336 (S - 64) PMSP.OPDEL_SCR [] STK1 HP5); unfold PMSP.OPDEL_SCR; lia).
  assert (MOK5 : PMSP.model_ok model5) by (apply (PMFR.model_ok_but_vm model model5 MOK MB5)).
  pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  assert (AGv : L5C.agree_on M1 M5 v 24) by (apply (PMFR.ag_hi RSEGS L KL ((B, A) :: LB) (S - 64) PMSP.OPDEL_SCR [] M1 M5 EKd STKd SC0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)]).
  assert (AGB : L5C.agree_on M1 M5 B A) by (apply (PMFR.ag_block RSEGS L KL ((B, A) :: LB) (S - 64) PMSP.OPDEL_SCR [] M1 M5 EKd STKd SC0 BRc WHI); left; reflexivity).
  assert (KF : forall a w, S - 64 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M1 a w -> L5.u64_at RSEGS M5 a w).
  { intros a w Ha1 Ha2 X. apply (PMFR.u64_keep RSEGS L KL ((B, A) :: LB) (S - 64) PMSP.OPDEL_SCR [] M1 M5 EKd STKd SC0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact X]. }
  assert (DO5 : L5.defined M5 v 24) by (apply (L5C.defined_agree M1 M5 v 24 AGv); intros i Hi; apply MG1; apply DO; exact Hi).
  assert (DB5 : L5.defined M5 B A) by (apply (L5C.defined_agree M1 M5 B A AGB); intros i Hi; apply MG1; apply DB; exact Hi).
  pose proof (L5C.stk_writable RSEGS _ M5 S 14336 STK5) as WR5.
  assert (WRo5 : L5.writable RSEGS M5 v 24) by (apply (L5C.writable_of_defined RSEGS M5 v 24 DO5); lia).
  assert (G2 : getr R5 (reg 2) = Z_to_bv 64 (S - 64)) by (rewrite (PMK.cs_of_preserved R1 R5 2%nat RP5) by PMK.inl; exact F2).
  assert (G8 : getr R5 (reg 8) = Z_to_bv 64 v) by (rewrite (PMK.cs_of_preserved R1 R5 8%nat RP5) by PMK.inl; exact F8).
  assert (G9 : getr R5 (reg 9) = Z_to_bv 64 k) by (rewrite (PMK.cs_of_preserved R1 R5 9%nat RP5) by PMK.inl; exact F9).
  assert (G18 : getr R5 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18)))) by (rewrite (PMK.cs_of_preserved R1 R5 18%nat RP5) by PMK.inl; exact F18).
  assert (G10 : getr R5 (reg 10) = Z_to_bv 64 (bv_unsigned (getr R5 (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range 64 (getr R5 (reg 10))) as B10. change (bv_modulus 64) with (2 ^ 64) in B10.
  pose proof (KF (S - 8) _ ltac:(lia) ltac:(lia) D8) as T8. pose proof (KF (S - 16) _ ltac:(lia) ltac:(lia) D16) as T16.
  pose proof (KF (S - 24) _ ltac:(lia) ltac:(lia) D24) as T24.
  LeanFeed.pfeed PQ (PNSVGP.vgQR_conc fx5 R5 M5 (fun j => match j with 2%nat => S | 10%nat => v | 33%nat => b | 34%nat => n | 35%nat => c | 37%nat => B | 38%nat => A | 43%nat => k
                | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
                | 47%nat => bv_unsigned (getr R0 (reg 18)) | 54%nat => bv_unsigned (getr R5 (reg 10)) | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct PQ as (fx6 & R6 & M6 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG6 & _ & FRZ6 & MS6 & KS6 & Q1 & Q2 & Q8 & Q9 & _ & _ & _)); PMK.pvz_clrT.
  set (P6 := fun a => S - 96 <= a < S - 96 + 96).
  assert (FR6 : forall a, 0 <= a < 2 ^ 64 -> ~ P6 a -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ6; [exact Ha| exact N]).
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok ((B, A) :: LB) cr' M5 model5 fx5 fx6 R5 0x39788 R6 0x39798 M6 P6 K HH5 Mh5 Ml5 ltac:(destruct STOP; lia) MS6 MG6 FR6).
  { intros a Pa. unfold P6 in Pa. apply (PMK.cwr_stack L _ M5 S 14336 a STK5); lia. }
  { intros a. unfold P6. apply PMK.rng_dec. }
  intros HH6.
  assert (RA6 : getr R6 (reg 1) = Z_to_bv 64 r) by (rewrite Q1, Z_to_bv_bv_unsigned; exact Rra0).
  unfold PMK.cfg.
  eapply (L5.cps_of_msteps RSEGS); [exact Mh5| exact Ml5| apply (PMK.ret_to RSEGS fx6 R6 M6 0x39798 W_39798 r F_39798 ltac:(reflexivity) D_39798 RA6 Hr1 Hr2)|].
  apply (KONT fx6 R6 M6 model5 (PGV8.V8Blk B (n + k) A) (g + 1) cr'); [| | cbn [PGV8.v8_size]; lia | exact OK1 | subst x; cbn; lia | subst x; cbn; intros X; exfalso; lia | right; subst x; cbn [PGV8.v8_cap]; lia | | exact CK | exact (L5C.model_but_vm_trans _ _ _ MB MB5) | exact HH6].
  - apply regs_back.
    + exact Q2.
    + exact Q8.
    + exact Q9.
    + rewrite (KS6 18%nat) by PMK.inl. exact G18.
    + intros y Hy. rewrite (KS6 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity).
      rewrite (PMK.cs_of_preserved R1 R5 y RP5) by (revert y Hy; apply sub_in; vm_compute; reflexivity).
      rewrite (KS1 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply KP. exact Hy.
  - (* [comment removed for export] *)
    assert (XF : forall a w, v <= a -> a + 8 <= v + 24 -> L5.u64_at RSEGS M1 a w -> L5.u64_at RSEGS M6 a w).
    { intros a w Ha1 Ha2 X. apply (L5C.u64_at_agree RSEGS M5 M6); [intros i Hi; apply FR6; unfold P6; lia|lia|lia|].
      apply (L5C.u64_at_agree RSEGS M1 M5); [eapply L5C.agree_on_sub; [exact AGv|lia|lia]|lia|lia| exact X]. }
    split; [intros i Hi; apply MG6; apply DO5; exact Hi|]. split; [exact I|].
    split; [exact (XF v B ltac:(lia) ltac:(lia) C0)|].
    split; [apply XF; [lia|lia| replace (B + (n + k)) with (n + (B + k)) by lia; exact C8]|].
    split; [exact (XF (v + 16) (B + A) ltac:(lia) ltac:(lia) C16)|].
    split; [lia|]. split; [lia|]. split; [exact HB0|]. split; [exact HB16|].
    split; [intros i Hi; apply MG6; apply DB5; exact Hi|]. split; exact I.
  - apply (PMK.hpres_of L LB S 14336 _ M0 M6).
    + apply (PMK.ek_trans L LB S 14336 _ M0 M M6 EK). apply (PMK.ek_trans L LB S 14336 _ M M1 M6).
      * apply (PMK.ek_piece L LB S 14336 _ M M1 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa. destruct Pa as [X|X].
        -- exact (frame_not_client a ltac:(lia) CA).
        -- apply (OW (v, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
      * apply (PMK.ek_trans L LB S 14336 _ M1 M5 M6).
        -- apply (PMK.ek_callee_in' RSEGS L KL LB ((B, A) :: LB) S 14336 (S - 64) PMSP.OPDEL_SCR [(v, 24)] [] M1 M5 HP5); [intros y Hy; right; exact Hy
             | unfold PMSP.OPDEL_SCR; lia| lia| lia| destruct STOP; lia| intros b0 Hb; apply (PMFR.brange_hi L _ BRc b0); right; exact Hb| intros a I; destruct (PMFR.inW_nil a I)].
        -- apply (PMK.ek_piece L LB S 14336 _ M5 M6 P6 FR6). intros a Ha CA NE OW Pa. unfold P6 in Pa. exact (frame_not_client a ltac:(lia) CA).
    + destruct (PMK.stk_grows L M5 M6 S 14336 MG6 STK5) as (_ & _ & _ & _ & D6). exact D6.
    + apply (PMK.dk_trans L LB S 14336 M0 M M6 DK). apply (PMK.dk_trans L LB S 14336 M M1 M6); [apply PMK.dk_grows; exact MG1|].
      apply (PMK.dk_trans L LB S 14336 M1 M5 M6); [|apply PMK.dk_grows; exact MG6].
      apply (PMK.dk_callee L LB ((B, A) :: LB) S 14336 (S - 64) PMSP.OPDEL_SCR [] M1 M5 HP5); [intros y Hy; right; exact Hy| unfold PMSP.OPDEL_SCR; lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_new_blk (fx : FPState) R M model (b n c k A B : Z) :
  PMSP.model_ok model -> x = PGV8.V8Blk b n c -> ns = n + k -> 1 <= k -> n + k <= A -> 1 <= A <= 2 ^ 27 -> 2 * c <= A -> (A = 2 * c \/ A = n + k) -> 0 <= n <= c -> 1 <= c -> c < n + k ->
  getr R (reg 2) = Z_to_bv 64 (S - 96) -> getr R (reg 8) = Z_to_bv 64 (S - 64) -> getr R (reg 9) = Z_to_bv 64 A -> getr R (reg 10) = Z_to_bv 64 B ->
  getr R (reg 18) = Z_to_bv 64 n ->
  kept0 R -> gframe M k -> L5.u64_at RSEGS M v b -> L5.u64_at RSEGS M (v + 8) (b + n) -> L5.u64_at RSEGS M (v + 16) (b + c) ->
  mem_ok M -> L5.defined M b n -> 4096 <= b -> b + c <= hl_ceil L -> b mod 16 = 0 ->
  L5.defined M B A -> 4096 <= B -> B + A <= hl_ceil L -> B mod 16 = 0 -> (B + A <= b \/ b + c <= B) ->
  hi_heap HI ((B, A) :: (b, c) :: LB) (debit L cr0 A) M (m_vmmaps model) -> model_but_vm model0 model ->
  PGV8.v8_ok (PGV8.V8Blk B (n + k) A) (g + 1) ->
  PMSP.credit_keep cr0 (debit L cr0 A) (PGV8.pot_v8 L x g) (PGV8.pot_v8 L (PGV8.V8Blk B (n + k) A) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39854 M model) K.
Proof.
  intros MOK Ex Ens Hk HnA HA H2c AMX Hnc Hc1 Hroom A2 A8 A9 A10 A18 KP GF W0 W8 W16 MO Db Hb0 Hb1 Hb16 DB HB0 HB1 HB16 APT HH MB OK1 CK.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  assert (WRo : L5.writable RSEGS M v 24) by (apply (L5C.writable_of_defined RSEGS M v 24 DO); lia).
  assert (WRB : L5.writable RSEGS M B A) by (apply (L5C.writable_of_defined RSEGS M B A DB); lia).
  assert (NBb : B <> b) by lia.
  assert (WRF : L5.writable RSEGS M (n + B) k) by (apply (L5.writable_sub RSEGS M B A (n + B) k WRB); lia).
  destruct GF as ((S8 & S16 & S24) & S32 & S40 & S72 & S80 & S88 & S96). bvr.
  LeanFeed.pfeed PP (PNSVGP.vgP_conc fx R M (fun j => match j with 2%nat => S | 10%nat => v | 33%nat => b | 34%nat => n | 35%nat => c | 37%nat => B | 38%nat => A | 43%nat => k
                | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
                | 47%nat => bv_unsigned (getr R0 (reg 18)) | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ0 & REST)); PMK.pvz_clrT.
  assert (MS1 : ltac:(match type of REST with (?X /\ _) \/ _ => exact X end)) by (destruct REST as [(X & _)|(X & _)]; exact X).
  assert (POST : (forall y, In y [2; 3; 4; 8; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg y) = getr R (reg y))
      /\ getr R1 (reg 1) = Z_to_bv 64 0x39964 /\ getr R1 (reg 9) = Z_to_bv 64 v /\ getr R1 (reg 10) = Z_to_bv 64 B
      /\ getr R1 (reg 11) = Z_to_bv 64 b /\ getr R1 (reg 12) = Z_to_bv 64 n /\ getr R1 (reg 18) = Z_to_bv 64 B
      /\ L5.u64_at RSEGS M1 (S - 32) v /\ L5.u64_at RSEGS M1 (S - 40) (B + A) /\ L5.u64_at RSEGS M1 (S - 48) (n + (B + k))
      /\ L5.u64_at RSEGS M1 (S - 56) (n + B) /\ L5.u64_at RSEGS M1 (S - 64) B /\ L5.u64_at RSEGS M1 (S - 72) 0x39780
      /\ L5.u64_at RSEGS M1 (S - 80) v /\ L5.u64_at RSEGS M1 (S - 88) k /\ L5.u64_at RSEGS M1 (S - 96) (bv_unsigned (getr R0 (reg 18))) /\ saves M1).
  { destruct REST as [(_ & KS1 & F1 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F18 & D96 & D88 & D80 & D72 & D48 & N0 & D40 & D56 & D64 & D8 & D16 & D24 & D32)
                     |(_ & KS1 & F1 & F9 & F11 & F12 & F13 & F14 & F15 & F18 & D96 & D88 & D80 & D72 & D48 & N1 & D40 & D56 & D64 & D8 & D16 & D24 & D32)].
    - split; [intros y Hy; apply KS1; revert y Hy; apply sub_in; vm_compute; reflexivity|].
      split; [exact F1|]. split; [exact F9|]. split; [rewrite F10; f_equal; lia|]. split; [exact F11|].
      split; [rewrite F12; f_equal; lia|]. split; [rewrite F18; f_equal; lia|].
      unfold saves. repeat split; assumption.
    - split; [intros y Hy; apply KS1; revert y Hy; apply sub_in; vm_compute; reflexivity|].
      split; [exact F1|]. split; [exact F9|]. split; [rewrite (KS1 10%nat) by PMK.inl; exact A10|]. split; [exact F11|].
      split; [exact F12|]. split; [exact F18|].
      unfold saves. repeat split; assumption. }
  destruct POST as (KS1 & F1 & F9 & F10 & F11 & F12 & F18 & D32 & D40 & D48 & D56 & D64 & D72 & D80 & D88 & D96 & SV1).
  set (P := fun a => (S - 96 <= a < S - 96 + 96) \/ (n + B <= a < n + B + k)).
  assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; unfold P; lia| intro X; apply N; unfold P; lia]. }
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok ((B, A) :: (b, c) :: LB) (debit L cr0 A) M model fx fx1 R 0x39854 R1 0xab480 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
  { intros a Pa. unfold P in Pa. destruct Pa as [X|X]; [apply (PMK.cwr_stack L _ M S 14336 a STK); lia| apply (PMK.cwr_block L ((B, A) :: (b, c) :: LB) B A a ltac:(left; reflexivity)); lia]. }
  { intros a. unfold P. apply PMK.or_dec; apply PMK.rng_dec. }
  intros HH1.
  assert (HDR : forall a w, v <= a -> a + 8 <= v + 24 -> L5.u64_at RSEGS M a w -> L5.u64_at RSEGS M1 a w).
  { intros a w Ha1 Ha2 X. apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FRZ; [lia| unfold P; lia]|lia|lia| exact X]. }
  pose proof (HDR v b ltac:(lia) ltac:(lia) W0) as W0'. pose proof (HDR (v + 8) (b + n) ltac:(lia) ltac:(lia) W8) as W8'.
  pose proof (HDR (v + 16) (b + c) ltac:(lia) ltac:(lia) W16) as W16'.
  assert (MO1 : mem_ok M1).
  { split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M1 EK); apply (PMK.ek_piece L LB S 14336 _ M M1 P FRZ);
             intros a Ha CA NE OW Pa; unfold P in Pa; destruct Pa as [X|X];
             [exact (frame_not_client a ltac:(lia) CA)| exact (own_not_client ((B, A) :: [(b, c)]) LB _ M _ B A a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA)]|].
    split; [apply (PMK.dk_trans L LB S 14336 M0 M M1 DK); apply PMK.dk_grows; exact MG1|].
    split; [exact (PMK.stk_grows L M M1 S 14336 MG1 STK)|]. intros i Hi. apply MG1. apply DO. exact Hi. }
  assert (DB1 : L5.defined M1 B A) by (intros i Hi; apply MG1; apply DB; exact Hi).
  assert (Db1 : L5.defined M1 b n) by (intros i Hi; apply MG1; apply Db; exact Hi).
  (* [comment removed for export] *)
  assert (CPY : exists fx3 R3 M3, msteps RSEGS (@mkst fx1 R1 (Z_to_bv 64 0xab480) M1 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0x39964) M3 (seg_rom RSEGS))
      /\ mem_grows M1 M3 /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (B <= a < B + n) -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))
      /\ (forall i, In i L5K.CS -> getr R3 (reg i) = getr R1 (reg i))).
  { destruct (Z.eq_dec n 0) as [En0|Nn0].
    - idtac.
      rewrite En0 in F12.
      LeanFeed.pfeed PC (PNSVGP.vgC0_conc fx1 R1 M1 (fun j => match j with 2%nat => S | 33%nat => b | 37%nat => B | _ => 0 end)) ltac:(first [PMK.sc]).
      destruct PC as (fx3 & R3 & M3 & MG3 & FRw3 & _ & MS3 & KS3 & _).
      assert (EM : M3 = M1) by (apply functional_extensionality; exact FRw3). subst M3.
      exists fx3, R3, M1. split; [exact MS3|]. split; [intros w X; exact X|]. split; [intros a _ _; reflexivity|].
      intros i Hi. apply KS3. revert i Hi. apply sub_in. vm_compute. reflexivity.
    - destruct (PMCPS.memcpy_run fx1 R1 M1 B b n 0x39964 F10 F11 F12 F1 ltac:(split; [lia| reflexivity]) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(apply (L5C.writable_of_defined RSEGS M1 B n); [apply (L5.defined_sub M1 B A B n DB1); lia|lia|lia]) Db1) as (R3 & M3 & MS3 & MG3 & FR3 & D3 & KS3 & _).
      exists fx1, R3, M3. split; [exact MS3|]. split; [exact MG3|]. split; [exact FR3| exact KS3]. }
  destruct CPY as (fx3 & R3 & M3 & MS3 & MG3 & FR3 & KS3).
  set (P3 := fun a => B <= a < B + n).
  apply (PMK.spiece RSEGS L HI KL HIok ((B, A) :: (b, c) :: LB) (debit L cr0 A) M1 model fx1 fx3 R1 0xab480 R3 0x39964 M3 P3 K HH1 Mh Ml ltac:(destruct STOP; lia) MS3 MG3 FR3).
  { intros a Pa. unfold P3 in Pa. apply (PMK.cwr_block L ((B, A) :: (b, c) :: LB) B A a ltac:(left; reflexivity)); lia. }
  { intros a. unfold P3. apply PMK.rng_dec. }
  intros HH3.
  assert (KSR : forall y, In y L5K.CS -> getr R3 (reg y) = getr R1 (reg y)) by exact KS3.
  pose proof (bv_unsigned_in_range 64 (getr R3 (reg 10))) as G10. change (bv_modulus 64) with (2 ^ 64) in G10.
  assert (X3 : forall a w, L5.u64_at RSEGS M1 a w -> (a + 8 <= B \/ B + n <= a) -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M3 a w).
  { intros a w X D Ha1 Ha2. apply (L5C.u64_at_agree RSEGS M1 M3); [intros i Hi; apply FR3; lia|lia|lia| exact X]. }
  apply (tail_del fx3 R3 M3 model b n c k A B (bv_unsigned (getr R3 (reg 10))) (debit L cr0 A) MOK Ex Ens Hk HnA HA H2c AMX G10 Hnc Hc1 Hroom); try assumption.
  - rewrite (KSR 2%nat) by PMK.inl. rewrite (KS1 2%nat) by PMK.inl. exact A2.
  - rewrite (KSR 8%nat) by PMK.inl. rewrite (KS1 8%nat) by PMK.inl. exact A8.
  - rewrite (KSR 9%nat) by PMK.inl. exact F9.
  - symmetry. apply Z_to_bv_bv_unsigned.
  - rewrite (KSR 18%nat) by PMK.inl. exact F18.
  - intros y Hy. rewrite (KSR y) by (revert y Hy; apply sub_in; vm_compute; reflexivity).
    rewrite (KS1 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply KP. exact Hy.
  - destruct SV1 as (T8 & T16 & T24). split; [|split]; (apply X3; [eassumption|lia|lia|lia]).
  - apply X3; [exact D32|lia|lia|lia].
  - apply X3; [exact D40|lia|lia|lia].
  - apply X3; [exact D48|lia|lia|lia].
  - apply X3; [exact D56|lia|lia|lia].
  - apply X3; [exact D64|lia|lia|lia].
  - apply X3; [exact D72|lia|lia|lia].
  - apply X3; [exact D80|lia|lia|lia].
  - apply X3; [exact D88|lia|lia|lia].
  - apply X3; [exact D96|lia|lia|lia].
  - apply X3; [exact W0'|lia|lia|lia].
  - apply X3; [exact W8'|lia|lia|lia].
  - apply X3; [exact W16'|lia|lia|lia].
  - destruct MO1 as (EK1 & DK1 & STK1 & DO1).
    split; [apply (PMK.ek_trans L LB S 14336 _ M0 M1 M3 EK1); apply (PMK.ek_piece L LB S 14336 _ M1 M3 P3 FR3);
             intros a Ha CA NE OW Pa; unfold P3 in Pa; exact (own_not_client ((B, A) :: [(b, c)]) LB _ M1 _ B A a S 14336 HH1 ltac:(left; reflexivity) ltac:(lia) CA)|].
    split; [apply (PMK.dk_trans L LB S 14336 M0 M1 M3 DK1); apply PMK.dk_grows; exact MG3|].
    split; [exact (PMK.stk_grows L M1 M3 S 14336 MG3 STK1)|]. intros i Hi. apply MG3. apply DO1. exact Hi.
  - intros i Hi. apply MG3. apply DB1. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma after_new_null (fx : FPState) R M model (k B : Z) :
  PMSP.model_ok model -> x = PGV8.V8Null -> ns = k -> 1 <= k <= 2 ^ 27 ->
  getr R (reg 2) = Z_to_bv 64 (S - 96) -> getr R (reg 8) = Z_to_bv 64 (S - 64) -> getr R (reg 9) = Z_to_bv 64 k -> getr R (reg 10) = Z_to_bv 64 B ->
  getr R (reg 18) = Z_to_bv 64 0 ->
  kept0 R -> gframe M k -> L5.u64_at RSEGS M v 0 -> L5.u64_at RSEGS M (v + 8) 0 -> L5.u64_at RSEGS M (v + 16) 0 -> mem_ok M ->
  L5.defined M B k -> 4096 <= B -> B + k <= hl_ceil L -> B mod 16 = 0 ->
  hi_heap HI ((B, k) :: LB) (debit L cr0 k) M (m_vmmaps model) -> model_but_vm model0 model ->
  PGV8.v8_ok (PGV8.V8Blk B k k) (g + 1) ->
  PMSP.credit_keep cr0 (debit L cr0 k) (PGV8.pot_v8 L x g) (PGV8.pot_v8 L (PGV8.V8Blk B k k) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39854 M model) K.
Proof.
  intros MOK Ex Ens Hk A2 A8 A9 A10 A18 KP GF W0 W8 W16 MO DB HB0 HB1 HB16 HH MB OK1 CK.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  assert (WRo : L5.writable RSEGS M v 24) by (apply (L5C.writable_of_defined RSEGS M v 24 DO); lia).
  assert (WRB : L5.writable RSEGS M B k) by (apply (L5C.writable_of_defined RSEGS M B k DB); lia).
  destruct GF as ((S8 & S16 & S24) & S32 & S40 & S72 & S80 & S88 & S96). bvr.
  LeanFeed.pfeed PP (PNSVGP.vgPN_conc fx R M (fun j => match j with 2%nat => S | 10%nat => v | 37%nat => B | 43%nat => k
                | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
                | 47%nat => bv_unsigned (getr R0 (reg 18)) | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG1 & _ & FRZ0 & MS1 & KS1 & F1 & F2 & F8 & F9 & _ & _ & _ & _ & _ & _ & F18 & D40 & D64 & C16 & D48 & C8 & D56 & C0 & D96 & D88 & D80 & D72 & D8 & D16 & D24 & D32));
    PMK.pvz_clrT.
  set (P := fun a => (S - 96 <= a < S - 96 + 96) \/ (v <= a < v + 24) \/ (B <= a < B + k)).
  assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; unfold P; lia| intro X; apply N; unfold P; lia| intro X; apply N; unfold P; lia]. }
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok ((B, k) :: LB) (debit L cr0 k) M model fx fx1 R 0x39854 R1 0x39798 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
  { intros a Pa. unfold P in Pa. destruct Pa as [X|[X|X]]; [apply (PMK.cwr_stack L _ M S 14336 a STK); lia| apply (PMK.cwr_stack L _ M S 14336 a STK); lia|
      apply (PMK.cwr_block L ((B, k) :: LB) B k a ltac:(left; reflexivity)); lia]. }
  { intros a. unfold P. apply PMK.or_dec; [apply PMK.rng_dec| apply PMK.or_dec; apply PMK.rng_dec]. }
  intros HH1.
  assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite F1, Z_to_bv_bv_unsigned; exact Rra0).
  unfold PMK.cfg.
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x39798 W_39798 r F_39798 ltac:(reflexivity) D_39798 RA1 Hr1 Hr2)|].
  apply (KONT fx1 R1 M1 model (PGV8.V8Blk B k k) (g + 1) (debit L cr0 k)); [| | cbn [PGV8.v8_size]; lia | exact OK1 | subst x; cbn; lia | subst x; cbn; intros X; exfalso; lia | right; subst x; cbn [PGV8.v8_cap]; lia | | exact CK | exact MB | exact HH1].
  - apply regs_back; [exact F2| exact F8| exact F9| exact F18|]. intros y Hy. rewrite (KS1 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply KP. exact Hy.
  - split; [intros i Hi; apply MG1; apply DO; exact Hi|]. split; [exact I|].
    split; [exact C0|]. split; [exact C8|]. split; [exact C16|].
    split; [lia|]. split; [lia|]. split; [exact HB0|]. split; [exact HB16|].
    split; [intros i Hi; apply MG1; apply DB; exact Hi|]. split; exact I.
  - apply (PMK.hpres_of L LB S 14336 _ M0 M1).
    + apply (PMK.ek_trans L LB S 14336 _ M0 M M1 EK).
      apply (PMK.ek_piece L LB S 14336 _ M M1 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa. destruct Pa as [X|[X|X]].
      * exact (frame_not_client a ltac:(lia) CA).
      * apply (OW (v, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
      * exact (own_not_client [(B, k)] LB _ M _ B k a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA).
    + destruct (PMK.stk_grows L M M1 S 14336 MG1 STK) as (_ & _ & _ & _ & D1). exact D1.
    + apply (PMK.dk_trans L LB S 14336 M0 M M1 DK). apply PMK.dk_grows. exact MG1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grow (fx : FPState) R M model (b n c k A : Z) :
  PMSP.model_ok model -> ns = n + k -> 1 <= k -> n + k <= A -> 1 <= A <= 2 ^ 27 -> 2 * PGV8.v8_cap x <= A ->
  n = PGV8.v8_size x -> c = PGV8.v8_cap x -> b = PGV8.v8_data x -> c < n + k -> (A = 2 * c \/ A = n + k) ->
  PMSP.credit_le (PGV8.pot_v8 L x g) cr0 ->
  getr R (reg 1) = Z_to_bv 64 0x39854 ->
  getr R (reg 2) = Z_to_bv 64 (S - 96) -> getr R (reg 8) = Z_to_bv 64 (S - 64) -> getr R (reg 9) = Z_to_bv 64 A -> getr R (reg 10) = Z_to_bv 64 A ->
  getr R (reg 18) = Z_to_bv 64 n ->
  kept0 R -> gframe M k -> mem_ok M -> v8_atP M v x ->
  hi_heap HI (PGV8.v8_own x ++ LB) cr0 M (m_vmmaps model) -> model_but_vm model0 model ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb03b8 M model) K.
Proof.
  intros MOK Ens Hk HnA HA H2c En Ec Eb Hroom AMX CR A1 A2 A8 A9 A10 A18 KP GF MO VS HH MB.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  assert (CAPB : PGV8.v8_cap x <= 2 ^ 26).
  { destruct GROWOK as [X|[X _]]; [exfalso; lia| exact X]. }
  destruct (grow_credit A 0 0 CAPB H2c HA CR) as (CROK & CK0 & OK1').
  assert (STKn : L5C.stk (hl_sptop L) M (S - 96) PMSP.OPNEW_SCR).
  { apply (PMK.stk_call L M S 14336 (S - 96) PMSP.OPNEW_SCR STK); [lia| unfold PMSP.OPNEW_SCR; lia| unfold PMSP.OPNEW_SCR; lia|].
    replace (S - 96) with (S + (-6) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  pose proof OPN as ON. unfold PMS.opnew_spec, PMSP.opnew_spec in ON. cbn [pa_opnew AD] in ON. unfold PMSP.cfg.
  apply (ON fx R M model K (PGV8.v8_own x ++ LB) cr0 A (S - 96) 0x39854 HH MOK K0).
  { rewrite L5K.rl10. exact A10. }
  { lia. }
  { exact CROK. }
  { rewrite L5K.rl1. exact A1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. exact A2. }
  { rewrite L5K.rl4. rewrite (KP 4%nat) by PMK.inl. exact Rtp0. }
  { exact STKn. }
  intros fx3 R3 M3 model3 B R3_10 RP3 FB HP3 MB3 HH3. rewrite L5K.rl10 in R3_10.
  destruct FB as ((FB0 & FB1 & FB2 & FB3 & FB4) & FBa & FBd).
  assert (C3 : forall y, In y [2; 8; 9; 18]%nat -> getr R3 (reg y) = getr R (reg y)).
  { intros y Hy. apply (PMK.cs_of_preserved R R3 y RP3). revert y Hy. apply sub_in. vm_compute. reflexivity. }
  assert (BRX : PMFR.brange L (PGV8.v8_own x ++ LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ cr0 M _ HH); apply incl_refl).
  assert (INL : incl LB (PGV8.v8_own x ++ LB)) by (intros y Hy; apply in_or_app; right; exact Hy).
  assert (EKn : PMK.ek L (PGV8.v8_own x ++ LB) (S - 96) PMSP.OPNEW_SCR [] M M3) by (apply (PMK.ek_of_hpres L); exact HP3).
  assert (SC0 : 0 <= PMSP.OPNEW_SCR) by (unfold PMSP.OPNEW_SCR; lia).
  assert (MOK3 : PMSP.model_ok model3) by (apply (PMFR.model_ok_but_vm model model3 MOK MB3)).
  assert (WHI : forall a, PMK.inW [] a -> S - 96 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
  assert (KF3 : forall a w, S - 96 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M a w -> L5.u64_at RSEGS M3 a w).
  { intros a w Ha1 Ha2 X. apply (PMFR.u64_keep RSEGS L KL (PGV8.v8_own x ++ LB) (S - 96) PMSP.OPNEW_SCR [] M M3 EKn STKn SC0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact X]. }
  assert (GF3 : gframe M3 k).
  { destruct GF as ((S8 & S16 & S24) & S32 & S40 & S72 & S80 & S88 & S96).
    unfold gframe, saves. repeat split; (apply KF3; [lia|lia| eassumption]). }
  assert (MO3 : mem_ok M3).
  { split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M3 EK)|].
    { apply (PMK.ek_callee_in' RSEGS L KL LB (PGV8.v8_own x ++ LB) S 14336 (S - 96) PMSP.OPNEW_SCR [(v, 24)] [] M M3 HP3 INL);
        [unfold PMSP.OPNEW_SCR; lia| lia| lia| destruct STOP; lia| exact (PMFR.brange_hi L LB BRLB)| intros a I; destruct (PMFR.inW_nil a I)]. }
    split; [apply (PMK.dk_trans L LB S 14336 M0 M M3 DK);
            apply (PMK.dk_callee L LB (PGV8.v8_own x ++ LB) S 14336 (S - 96) PMSP.OPNEW_SCR [] M M3 HP3 INL); [unfold PMSP.OPNEW_SCR; lia| lia]|].
    split; [apply (PMK.stk_after RSEGS L KL (PGV8.v8_own x ++ LB) M M3 S 14336 (S - 96) PMSP.OPNEW_SCR [] STK HP3); unfold PMSP.OPNEW_SCR; lia|].
    apply (PMFR.defined_keep RSEGS L KL (PGV8.v8_own x ++ LB) (S - 96) PMSP.OPNEW_SCR [] M M3 EKn STKn SC0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact DO]. }
  pose proof CAPB as CAPBx. pose proof H2c as H2cx.
  destruct (v8_case x) as [Ex | (xb & xn & xc & Ex)].
  - (* [comment removed for export] *)
    pose proof VS as VS0. rewrite Ex in VS0. destruct VS0 as (_ & _ & W0 & W8 & W16).
    rewrite Ex in En, Ec, Eb, H2c, CAPB, HH3, HH. cbn [PGV8.v8_size PGV8.v8_cap PGV8.v8_data] in En, Ec, Eb, H2c, CAPB. subst n c b. cbn [PGV8.v8_own app] in HH3, HH.
    assert (EA : A = k) by lia. subst A. rewrite Z.add_0_l in Ens.
    destruct (grow_credit k B k CAPBx H2cx HA CR) as (_ & CK & OK1).
    apply (after_new_null fx3 R3 M3 model3 k B MOK3 Ex Ens ltac:(lia)); try assumption.
    + rewrite (C3 2%nat) by PMK.inl. exact A2.
    + rewrite (C3 8%nat) by PMK.inl. exact A8.
    + rewrite (C3 9%nat) by PMK.inl. exact A9.
    + rewrite (C3 18%nat) by PMK.inl. exact A18.
    + intros y Hy. rewrite (PMK.cs_of_preserved R R3 y RP3) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply KP. exact Hy.
    + exact (KF3 v 0 ltac:(lia) ltac:(lia) W0).
    + exact (KF3 (v + 8) 0 ltac:(lia) ltac:(lia) W8).
    + exact (KF3 (v + 16) 0 ltac:(lia) ltac:(lia) W16).
    + exact (L5C.model_but_vm_trans _ _ _ MB MB3).
  - (* [comment removed for export] *)
    rewrite Ex in En, Ec, Eb, H2c, CAPB, HH3, HH, BRX, EKn, INL, VS, FBa. cbn [PGV8.v8_size PGV8.v8_cap PGV8.v8_data] in En, Ec, Eb, H2c, CAPB. subst xn xc xb.
    cbn [PGV8.v8_own app] in HH3, HH, BRX, EKn, INL.
    pose proof VS as (_ & _ & W0 & W8 & W16 & Hnc & Hc & Hb0 & Hb16 & Db & _ & _).
    destruct (BRX b c ltac:(left; reflexivity)) as (Pb0 & Pb1 & Pb4).
    assert (APT : B + A <= b \/ b + c <= B) by (destruct (FBa (b, c) ltac:(left; reflexivity)); cbn [fst snd] in *; lia).
    destruct (grow_credit A B (n + k) CAPBx H2cx HA CR) as (_ & CK & OK1).
    apply (after_new_blk fx3 R3 M3 model3 b n c k A B MOK3 Ex Ens Hk HnA HA ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hroom); try assumption.
    + rewrite (C3 2%nat) by PMK.inl. exact A2.
    + rewrite (C3 8%nat) by PMK.inl. exact A8.
    + rewrite (C3 9%nat) by PMK.inl. exact A9.
    + rewrite (C3 18%nat) by PMK.inl. exact A18.
    + intros y Hy. rewrite (PMK.cs_of_preserved R R3 y RP3) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply KP. exact Hy.
    + exact (KF3 v b ltac:(lia) ltac:(lia) W0).
    + exact (KF3 (v + 8) (b + n) ltac:(lia) ltac:(lia) W8).
    + exact (KF3 (v + 16) (b + c) ltac:(lia) ltac:(lia) W16).
    + apply (L5C.defined_agree M M3 b n); [|apply (L5.defined_sub M b c b n Db); lia].
      apply (L5C.agree_on_sub M M3 b c b n); [|lia|lia].
      apply (PMFR.ag_block RSEGS L KL ([(b, c)] ++ LB) (S - 96) PMSP.OPNEW_SCR [] M M3 EKn STKn SC0 BRX WHI). left. reflexivity.
    + exact (L5C.model_but_vm_trans _ _ _ MB MB3).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grow_fork (fx : FPState) R M model (b n c k : Z) :
  PMSP.model_ok model -> x = PGV8.V8Blk b n c -> ns = n + k -> 1 <= k -> c < n + k ->
  PMSP.credit_le (PGV8.pot_v8 L x g) cr0 ->
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 v -> getr R (reg 9) = Z_to_bv 64 k -> getr R (reg 10) = Z_to_bv 64 (b + c) ->
  getr R (reg 12) = Z_to_bv 64 (b + n) -> getr R (reg 13) = Z_to_bv 64 (c - n) -> getr R (reg 18) = getr R0 (reg 18) ->
  kept0 R -> saves M -> mem_ok M -> v8_atP M v x ->
  hi_heap HI (PGV8.v8_own x ++ LB) cr0 M (m_vmmaps model) -> model_but_vm model0 model ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x3972c M model) K.
Proof.
  intros MOK Ex Ens Hk Hroom CR A2 A8 A9 A10 A12 A13 A18 KP SV MO VS HH MB.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  assert (GR : c <= 2 ^ 26 /\ n + k <= 2 ^ 27).
  { pose proof GROWOK as GO. rewrite Ex in GO. unfold PGV8.v8_grow_ok in GO. cbn [PGV8.v8_cap] in GO. destruct GO as [X|[X Y]]; [exfalso; lia| split; lia]. }
  destruct GR as (Hc26 & Hnk).
  pose proof VS as VS0. rewrite Ex in VS0. pose proof VS0 as (_ & _ & W0 & W8 & W16 & Hnc & Hc & Hb0 & Hb16 & Db & _ & _).
  assert (BRX : PMFR.brange L (PGV8.v8_own x ++ LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ cr0 M _ HH); apply incl_refl).
  rewrite Ex in BRX. cbn [PGV8.v8_own app] in BRX. destruct (BRX b c ltac:(left; reflexivity)) as (Pb0 & Pb1 & Pb4).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  assert (WRo : L5.writable RSEGS M v 24) by (apply (L5C.writable_of_defined RSEGS M v 24 DO); lia).
  destruct SV as (S8 & S16 & S24). bvr.
  LeanFeed.pfeed PP (PNSVGP.vgG_conc fx R M (fun j => match j with 2%nat => S | 10%nat => v | 33%nat => b | 34%nat => n | 35%nat => c | 43%nat => k
                | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9)) | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ0 & REST)); PMK.pvz_clrT.
  assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ (S - 96 <= a < S - 96 + 96) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) by exact FRZ0.
  pose proof (mem_ok_frame M M1 MO MG1 FRZ) as MO1.
  assert (VS1 : v8_atP M1 v x) by (apply (v8_at_agree M M1 v x (fun a => S - 96 <= a < S - 96 + 96) VS MG1 ltac:(lia) ltac:(lia) FRZ); intros a Ha; lia).
  assert (E18 : bv_unsigned (getr R (reg 18)) = bv_unsigned (getr R0 (reg 18))) by (rewrite A18; reflexivity).
  unfold PMSP.cfg.
  destruct REST as [(MS1 & KS1 & F1 & F2 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F18 & D32 & D40 & D96 & D88 & D80 & D72 & CND & D8 & D16 & D24)
                   |(MS1 & KS1 & F1 & F2 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F18 & D32 & D40 & D96 & D88 & D80 & D72 & CND & D8 & D16 & D24)];
    rewrite E18 in D96;
    (apply (PMK.spiece RSEGS L HI KL HIok (PGV8.v8_own x ++ LB) cr0 M model fx fx1 R 0x3972c R1 0xb03b8 M1 (fun a => S - 96 <= a < S - 96 + 96) K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ);
     [intros a Pa; apply (PMK.cwr_stack L _ M S 14336 a STK); lia| intros a; apply PMK.rng_dec| intros HH1]).
  - (* [comment removed for export] *)
    apply (grow fx1 R1 M1 model b n c k (2 * c) MOK Ens Hk); try assumption.
    + rewrite Z.mod_small in CND by lia. rewrite Z.mod_small in CND by lia. lia.
    + lia.
    + rewrite Ex. cbn [PGV8.v8_cap]. lia.
    + rewrite Ex. reflexivity.
    + rewrite Ex. reflexivity.
    + rewrite Ex. reflexivity.
    + left. reflexivity.
    + intros y Hy. rewrite (KS1 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply KP. exact Hy.
    + unfold gframe, saves. repeat split; assumption.
  - (* [comment removed for export] *)
    apply (grow fx1 R1 M1 model b n c k (n + k) MOK Ens Hk); try assumption.
    + lia.
    + lia.
    + rewrite Ex. cbn [PGV8.v8_cap]. rewrite Z.mod_small in CND by lia. rewrite Z.mod_small in CND by lia. lia.
    + rewrite Ex. reflexivity.
    + rewrite Ex. reflexivity.
    + rewrite Ex. reflexivity.
    + right. reflexivity.
    + intros y Hy. rewrite (KS1 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply KP. exact Hy.
    + unfold gframe, saves. repeat split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CSR : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma append_at (fx : FPState) R M model (k : Z) :
  PMSP.model_ok model -> ns = PGV8.v8_size x + k -> 1 <= k ->
  PMSP.credit_le (PGV8.pot_v8 L x g) cr0 ->
  (forall y, In y CSR -> getr R (reg y) = getr R0 (reg y)) -> getr R (reg 10) = Z_to_bv 64 v -> getr R (reg 11) = Z_to_bv 64 k ->
  mem_ok M -> v8_atP M v x -> hi_heap HI (PGV8.v8_own x ++ LB) cr0 M (m_vmmaps model) -> model_but_vm model0 model ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39704 M model) K.
Proof.
  intros MOK Ens Hk CR RR A10 A11 MO VS HH MB.
  pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
  assert (WRo : L5.writable RSEGS M v 24) by (apply (L5C.writable_of_defined RSEGS M v 24 DO); lia).
  assert (WRf : L5.writable RSEGS M (S - 96) 96) by (intros d q Hd Hq; replace (S - 96 + d) with (S - 14336 + (14240 + d)) by lia; apply WR; lia).
  assert (A2 : getr R (reg 2) = Z_to_bv 64 S) by (rewrite (RR 2%nat) by PMK.inl; exact Rsp0).
  assert (HO : bv_unsigned (getr R (reg 10)) = v) by (rewrite A10; apply L5.unsigned_lit; lia).
  assert (NSK : ns <= 2 ^ 27).
  { pose proof GROWOK as GO. pose proof VS as VSx. unfold PGV8.v8_grow_ok in GO.
    destruct (v8_case x) as [Ex|(xb & xn & xc & Ex)]; rewrite Ex in GO, VSx; cbn [PGV8.v8_cap] in GO; [lia|].
    destruct VSx as (_ & _ & _ & _ & _ & H1 & H2 & _). lia. }
  bvr.
  assert (E1 : getr R (reg 1) = getr R0 (reg 1)) by (apply RR; PMK.inl). assert (E8 : getr R (reg 8) = getr R0 (reg 8)) by (apply RR; PMK.inl).
  assert (E9 : getr R (reg 9) = getr R0 (reg 9)) by (apply RR; PMK.inl). assert (E18 : getr R (reg 18) = getr R0 (reg 18)) by (apply RR; PMK.inl).
  assert (KP0 : kept0 R) by (intros y Hy; apply RR; revert y Hy; apply sub_in; vm_compute; reflexivity).
  destruct (v8_case x) as [Ex|(b & n & c & Ex)].
  - (* [comment removed for export] *)
    pose proof VS as VS0. rewrite Ex in VS0. destruct VS0 as (_ & _ & W0 & W8 & W16).
    rewrite Ex in Ens. cbn [PGV8.v8_size] in Ens. rewrite Z.add_0_l in Ens.
    pose proof (PNSVGP.vgFN_conc fx R M (fun j => match j with 2%nat => S | 43%nat => k | _ => 0 end)) as PP.
    cbn beta iota in PP. rewrite HO in PP. PMK.feed PP ltac:(first [PMK.sc]).
    PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
      destruct pvzP as (MG1 & _ & FRZ & MS1 & KS1 & F1 & F2 & F8 & F9 & F10 & F12 & F13 & F14 & F18 & C32 & C40 & C96 & C88 & C80 & C72 & C24 & C16 & C8)); PMK.pvz_clrT.
    pose proof (mem_ok_frame M M1 MO MG1 FRZ) as MO1.
    unfold PMSP.cfg.
    apply (PMK.spiece RSEGS L HI KL HIok (PGV8.v8_own x ++ LB) cr0 M model fx fx1 R 0x39704 R1 0xb03b8 M1 (fun a => S - 96 <= a < S - 96 + 96) K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
    { intros a Pa. apply (PMK.cwr_stack L _ M S 14336 a STK). lia. }
    { intros a. apply PMK.rng_dec. }
    intros HH1.
    apply (grow fx1 R1 M1 model 0 0 0 k k MOK ltac:(lia) Hk ltac:(lia) ltac:(lia));
      [rewrite Ex; cbn; lia | rewrite Ex; reflexivity | rewrite Ex; reflexivity | rewrite Ex; reflexivity | lia | right; reflexivity | exact CR
      | exact F1 | exact F2 | exact F8 | exact F9 | exact F10 | exact F18 | | | exact MO1 | | exact HH1 | exact MB].
    + intros y Hy. rewrite (KS1 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply KP0. exact Hy.
    + unfold gframe, saves. rewrite <- E1, <- E8, <- E9, <- E18. repeat split; assumption.
    + apply (v8_at_agree M M1 v x (fun a => S - 96 <= a < S - 96 + 96) VS MG1 ltac:(lia) ltac:(lia) FRZ). intros a Ha. lia.
  - (* [comment removed for export] *)
    pose proof VS as VS0. rewrite Ex in VS0. destruct VS0 as (_ & _ & W0 & W8 & W16 & Hnc & Hc & Hb0 & Hb16 & Db & _ & _).
    rewrite Ex in Ens. cbn [PGV8.v8_size] in Ens.
    assert (BRX : PMFR.brange L (PGV8.v8_own x ++ LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ cr0 M _ HH); apply incl_refl).
    rewrite Ex in BRX. cbn [PGV8.v8_own app] in BRX. destruct (BRX b c ltac:(left; reflexivity)) as (Pb0 & Pb1 & Pb4).
    destruct (Z_lt_le_dec c (n + k)) as [GROWS|FITS].
    + (* [comment removed for export] *)
      pose proof (PNSVGP.vgFG_conc fx R M (fun j => match j with 2%nat => S | 33%nat => b | 34%nat => n | 35%nat => c | 43%nat => k | _ => 0 end)) as PP.
      cbn beta iota in PP. rewrite HO in PP. PMK.feed PP ltac:(first [PMK.sc | rewrite room_mod by lia; lia]).
      PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
        destruct pvzP as (MG1 & _ & FRZ & MS1 & KS1 & F2 & F8 & F9 & F10 & F12 & F13 & C24 & C16 & C8)); PMK.pvz_clrT.
      pose proof (mem_ok_frame M M1 MO MG1 FRZ) as MO1.
      unfold PMSP.cfg.
      apply (PMK.spiece RSEGS L HI KL HIok (PGV8.v8_own x ++ LB) cr0 M model fx fx1 R 0x39704 R1 0x3972c M1 (fun a => S - 96 <= a < S - 96 + 96) K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
      { intros a Pa. apply (PMK.cwr_stack L _ M S 14336 a STK). lia. }
      { intros a. apply PMK.rng_dec. }
      intros HH1.
      apply (grow_fork fx1 R1 M1 model b n c k MOK Ex Ens Hk GROWS CR); try assumption.
      * rewrite F8. exact A10.
      * rewrite F13. f_equal. lia.
      * rewrite (KS1 18%nat) by PMK.inl. exact E18.
      * intros y Hy. rewrite (KS1 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply KP0. exact Hy.
      * unfold saves. rewrite <- E1, <- E8, <- E9. repeat split; assumption.
      * apply (v8_at_agree M M1 v x (fun a => S - 96 <= a < S - 96 + 96) VS MG1 ltac:(lia) ltac:(lia) FRZ). intros a Ha. lia.
    + (* [comment removed for export] *)
      assert (WRB : L5.writable RSEGS M (b + n) k) by (intros d q Hd Hq; replace (b + n + d) with (b + (n + d)) by lia; apply (L5C.writable_of_defined RSEGS M b c Db); lia).
      pose proof (PNSVGP.vgF_conc fx R M (fun j => match j with 2%nat => S | 33%nat => b | 34%nat => n | 35%nat => c | 43%nat => k | _ => 0 end)) as PP.
      cbn beta iota in PP. rewrite HO in PP. PMK.feed PP ltac:(first [PMK.sc]).
      PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ0 & REST)); PMK.pvz_clrT.
      destruct REST as [(MS1 & KS1 & F11 & F12 & F13 & F14 & F15 & C8 & CND & S24 & S16 & S8 & C0 & C16) | (_ & _ & _ & _ & _ & _ & _ & _ & CND & _)];
        [| exfalso; rewrite room_mod in CND by lia; lia].
      set (P := fun a => (S - 96 <= a < S - 96 + 96) \/ (v <= a < v + 24) \/ (b + n <= a < b + n + k)).
      assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; unfold P; lia| intro X; apply N; unfold P; lia| intro X; apply N; unfold P; lia]. }
      unfold PMSP.cfg.
      apply (PMK.spiece RSEGS L HI KL HIok (PGV8.v8_own x ++ LB) cr0 M model fx fx1 R 0x39704 R1 0x39818 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
      { intros a Pa. unfold P in Pa. destruct Pa as [X|[X|X]]; [apply (PMK.cwr_stack L _ M S 14336 a STK); lia| apply (PMK.cwr_stack L _ M S 14336 a STK); lia|].
        rewrite Ex. cbn [PGV8.v8_own app]. apply (PMK.cwr_block L ((b, c) :: LB) b c a ltac:(left; reflexivity)). lia. }
      { intros a. unfold P. apply PMK.or_dec; [apply PMK.rng_dec| apply PMK.or_dec; apply PMK.rng_dec]. }
      intros HH1.
      assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by PMK.inl; rewrite E1; exact Rra0).
      unfold PMK.cfg.
      eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x39818 W_385e0 r F_385e0 ltac:(reflexivity) D_385e0 RA1 Hr1 Hr2)|].
      apply (KONT fx1 R1 M1 model (PGV8.V8Blk b (n + k) c) g cr0);
        [| | cbn [PGV8.v8_size]; lia | rewrite Ex in OK0; exact OK0 | rewrite Ex; cbn; lia | rewrite Ex; cbn; intros _; repeat split; reflexivity | left; rewrite Ex; reflexivity | | | exact MB | rewrite Ex in HH1; exact HH1].
      * apply PMK.preserved_by_index. intros y Hy. rewrite (KS1 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply RR. revert y Hy; apply sub_in; vm_compute; reflexivity.
      * split; [intros i Hi; apply MG1; apply DO; exact Hi|]. split; [exact I|].
        split; [exact C0|]. split; [exact C8|]. split; [exact C16|].
        split; [lia|]. split; [lia|]. split; [exact Hb0|]. split; [exact Hb16|].
        split; [intros i Hi; apply MG1; apply Db; exact Hi|]. split; exact I.
      * apply (PMK.hpres_of L LB S 14336 _ M0 M1).
        -- apply (PMK.ek_trans L LB S 14336 _ M0 M M1 EK).
           apply (PMK.ek_piece L LB S 14336 _ M M1 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa. destruct Pa as [X|[X|X]].
           ++ exact (frame_not_client a ltac:(lia) CA).
           ++ apply (OW (v, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
           ++ rewrite Ex in HH. exact (own_not_client [(b, c)] LB _ M _ b c a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA).
        -- destruct (PMK.stk_grows L M M1 S 14336 MG1 STK) as (_ & _ & _ & _ & D1). exact D1.
        -- apply (PMK.dk_trans L LB S 14336 M0 M M1 DK). apply PMK.dk_grows. exact MG1.
      * rewrite Ex. unfold PMSP.credit_keep, PGV8.pot_v8. cbn [PGV8.v8_cap fst snd]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mem_ok0 : v8_atP M0 v x -> mem_ok M0.
Proof. intros VS. split; [apply PMK.ek_refl|]. split; [apply PMK.dk_refl|]. split; [exact STK0|]. destruct (v8_case x) as [Ex|(b & n & c & Ex)]; rewrite Ex in VS; destruct VS as (D & _); exact D. Qed.

Lemma resize_at (fx : FPState) :
  PMSP.model_ok model0 -> PMSP.credit_le (PGV8.pot_v8 L x g) cr0 ->
  getr R0 (reg 10) = Z_to_bv 64 v -> getr R0 (reg 11) = Z_to_bv 64 ns ->
  v8_atP M0 v x -> hi_heap HI (PGV8.v8_own x ++ LB) cr0 M0 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0x396ac M0 model0) K.
Proof.
  intros MOK CR A10 A11 VS HH.
  pose proof (mem_ok0 VS) as MO. pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof RAok as (Hr1 & Hr2).
  pose proof (L5C.stk_writable RSEGS _ M0 S 14336 STK) as WR.
  assert (WRo : L5.writable RSEGS M0 v 24) by (apply (L5C.writable_of_defined RSEGS M0 v 24 DO); lia).
  assert (HO : bv_unsigned (getr R0 (reg 10)) = v) by (rewrite A10; apply L5.unsigned_lit; lia).
  assert (NSK : ns <= 2 ^ 27).
  { pose proof GROWOK as GO. pose proof VS as VSx. unfold PGV8.v8_grow_ok in GO.
    destruct (v8_case x) as [Ex|(xb & xn & xc & Ex)]; rewrite Ex in GO, VSx; cbn [PGV8.v8_cap] in GO; [lia|].
    destruct VSx as (_ & _ & _ & _ & _ & H1 & H2 & _). lia. }
  assert (MB0 : model_but_vm model0 model0) by (apply L5C.model_but_vm_refl).
  bvr.
  destruct (v8_case x) as [Ex|(b & n & c & Ex)].
  - pose proof VS as VS0. rewrite Ex in VS0. destruct VS0 as (_ & _ & W0 & W8 & W16).
    destruct (Z.eq_dec ns 0) as [Ens0|Nns].
    + (* [comment removed for export] *)
      pose proof (PNSVGP.vgZ0_conc fx R0 M0 (fun j => match j with 2%nat => S | _ => 0 end)) as PP.
      cbn beta iota in PP. rewrite HO in PP. rewrite Ens0 in A11. PMK.feed PP ltac:(first [PMK.sc]).
      PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & FRW & _ & MS1 & KS1 & F12 & F13 & F14)); PMK.pvz_clrT.
      assert (EM : M1 = M0) by (apply functional_extensionality; exact FRW). subst M1. clear FRW MG1.
      unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model0 fx fx1 R0 0x396ac R1 0x396fc M0 K Mh Ml MS1).
      assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by PMK.inl; exact Rra0).
      unfold PMK.cfg.
      eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M0 0x396fc W_384a0 r F_384a0 ltac:(reflexivity) D_384a0 RA1 Hr1 Hr2)|].
      apply (KONT fx1 R1 M0 model0 PGV8.V8Null g cr0);
        [| rewrite Ex in VS; exact VS | cbn [PGV8.v8_size]; lia | rewrite Ex in OK0; exact OK0 | rewrite Ex; cbn; lia | rewrite Ex; cbn; intros _; repeat split; reflexivity
         | left; rewrite Ex; reflexivity | | rewrite Ex; unfold PMSP.credit_keep; cbn [fst snd]; lia | exact MB0 | rewrite Ex in HH; exact HH].
      * apply PMK.preserved_by_index. intros y Hy. rewrite (KS1 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). reflexivity.
      * apply (PMK.hpres_of L LB S 14336 _ M0 M0); [apply PMK.ek_refl| exact SDEF| apply PMK.dk_refl].
    + (* [comment removed for export] *)
      pose proof (PNSVGP.vgZN_conc fx R0 M0 (fun j => match j with 2%nat => S | 43%nat => ns | _ => 0 end)) as PP.
      cbn beta iota in PP. rewrite HO in PP. PMK.feed PP ltac:(first [PMK.sc]).
      PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & FRW & _ & MS1 & KS1 & F12 & F13 & F14)); PMK.pvz_clrT.
      assert (EM : M1 = M0) by (apply functional_extensionality; exact FRW). subst M1. clear FRW MG1.
      unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model0 fx fx1 R0 0x396ac R1 0x39704 M0 K Mh Ml MS1).
      apply (append_at fx1 R1 M0 model0 ns MOK ltac:(rewrite Ex; cbn; lia) ltac:(lia) CR); try assumption.
      * intros y Hy. apply KS1. revert y Hy; apply sub_in; vm_compute; reflexivity.
      * rewrite (KS1 10%nat) by PMK.inl. exact A10.
      * rewrite (KS1 11%nat) by PMK.inl. exact A11.
  - pose proof VS as VS0. rewrite Ex in VS0. destruct VS0 as (_ & _ & W0 & W8 & W16 & Hnc & Hc & Hb0 & Hb16 & Db & _ & _).
    assert (BRX : PMFR.brange L (PGV8.v8_own x ++ LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ cr0 M0 _ HH); apply incl_refl).
    rewrite Ex in BRX. cbn [PGV8.v8_own app] in BRX. destruct (BRX b c ltac:(left; reflexivity)) as (Pb0 & Pb1 & Pb4).
    assert (HPV : forall M1, mem_grows M0 M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 24) -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
      L5C.hpres L LB S (PMSP.pm_scr 1) [(v, 24)] M0 M1).
    { intros M1 MG1 FRZ'. apply (PMK.hpres_of L LB S 14336 _ M0 M1).
      + apply (PMK.ek_piece L LB S 14336 _ M0 M1 (fun a => v <= a < v + 24) FRZ').
        intros a Ha CA NE OW Pa. apply (OW (v, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
      + destruct (PMK.stk_grows L M0 M1 S 14336 MG1 STK) as (_ & _ & _ & _ & D1). exact D1.
      + apply PMK.dk_grows. exact MG1. }
    assert (CWR : forall a, (v <= a < v + 24) -> PMK.cwr L (PGV8.v8_own x ++ LB) a) by (intros a Pa; apply (PMK.cwr_stack L _ M0 S 14336 a STK); lia).
    assert (DEC : forall a, {v <= a < v + 24} + {~ (v <= a < v + 24)}) by (intros a; apply PMK.rng_dec).
    assert (CASES : ns = n \/ ns < n \/ n < ns) by lia.
    destruct CASES as [EQn|[LTn|GTn]].
    + (* [comment removed for export] *)
      pose proof (PNSVGP.vgZ_conc fx R0 M0 (fun j => match j with 2%nat => S | 33%nat => b | 34%nat => n | 35%nat => c | 43%nat => ns | _ => 0 end)) as PP.
      cbn beta iota in PP. rewrite HO in PP. PMK.feed PP ltac:(first [PMK.sc]).
      PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ & REST)); PMK.pvz_clrT.
      destruct REST as [(MS1 & KS1 & F12 & F13 & F14 & LE1 & C0 & C8 & C16) | (_ & _ & _ & _ & _ & _ & LT1 & _)]; [| exfalso; lia].
      assert (FRZ' : forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 24) -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ; [exact Ha| intro X; apply N; lia]).
      pose proof (HPV M1 MG1 FRZ') as HP1.
      unfold PMSP.cfg.
      apply (PMK.spiece RSEGS L HI KL HIok (PGV8.v8_own x ++ LB) cr0 M0 model0 fx fx1 R0 0x396ac R1 _ M1 (fun a => v <= a < v + 24) K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ' CWR DEC).
      intros HH1.
      assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by PMK.inl; exact Rra0).
      unfold PMK.cfg.
      eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x396fc W_384a0 r F_384a0 ltac:(reflexivity) D_384a0 RA1 Hr1 Hr2)|].
      apply (KONT fx1 R1 M1 model0 (PGV8.V8Blk b n c) g cr0);
        [| | cbn [PGV8.v8_size]; lia | rewrite Ex in OK0; exact OK0 | rewrite Ex; cbn; lia | rewrite Ex; cbn; intros _; repeat split; reflexivity
         | left; rewrite Ex; reflexivity | exact HP1 | rewrite Ex; unfold PMSP.credit_keep, PGV8.pot_v8; cbn [PGV8.v8_cap fst snd]; lia | exact MB0 | rewrite Ex in HH1; exact HH1].
      * apply PMK.preserved_by_index. intros y Hy. rewrite (KS1 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). reflexivity.
      * split; [intros i Hi; apply MG1; apply DO; exact Hi|]. split; [exact I|].
        split; [exact C0|]. split; [exact C8|]. split; [exact C16|].
        split; [lia|]. split; [lia|]. split; [exact Hb0|]. split; [exact Hb16|].
        split; [intros i Hi; apply MG1; apply Db; exact Hi|]. split; exact I.
    + (* [comment removed for export] *)
      assert (SL : forall Km : Z, Km = 2 ^ 64 - 1 -> ((Km * b) mod 2 ^ 64 + (Km * n) mod 2 ^ 64) mod 2 ^ 64 < ((Km * n) mod 2 ^ 64 + ns) mod 2 ^ 64).
      { intros Km ->. assert (Bn : 4096 <= b /\ b + n < 2 ^ 64 /\ 0 <= ns < n) by lia. clear - Bn.
        change (2 ^ 64) with 18446744073709551616 in *. Z.div_mod_to_equations. Lia.lia. }
      pose proof (PNSVGP.vgZL_conc fx R0 M0 (fun j => match j with 2%nat => S | 33%nat => b | 34%nat => n | 35%nat => c | 43%nat => ns | _ => 0 end)) as PP.
      cbn beta iota in PP. rewrite HO in PP. PMK.feed PP ltac:(first [PMK.sc | (eapply SL; reflexivity)]).
      PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
        destruct pvzP as (MG1 & _ & FRZ & MS1 & KS1 & F11 & F12 & F13 & F14 & C8 & C0 & C16)); PMK.pvz_clrT.
      assert (FRZ' : forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 24) -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ; [exact Ha| intro X; apply N; lia]).
      pose proof (HPV M1 MG1 FRZ') as HP1.
      unfold PMSP.cfg.
      apply (PMK.spiece RSEGS L HI KL HIok (PGV8.v8_own x ++ LB) cr0 M0 model0 fx fx1 R0 0x396ac R1 _ M1 (fun a => v <= a < v + 24) K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ' CWR DEC).
      intros HH1.
      assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by PMK.inl; exact Rra0).
      unfold PMK.cfg.
      eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x396fc W_384a0 r F_384a0 ltac:(reflexivity) D_384a0 RA1 Hr1 Hr2)|].
      apply (KONT fx1 R1 M1 model0 (PGV8.V8Blk b ns c) g cr0);
        [| | cbn [PGV8.v8_size]; lia | rewrite Ex in OK0; exact OK0 | rewrite Ex; cbn; lia | rewrite Ex; cbn; intros _; repeat split; reflexivity
         | left; rewrite Ex; reflexivity | exact HP1 | rewrite Ex; unfold PMSP.credit_keep, PGV8.pot_v8; cbn [PGV8.v8_cap fst snd]; lia | exact MB0 | rewrite Ex in HH1; exact HH1].
      * apply PMK.preserved_by_index. intros y Hy. rewrite (KS1 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). reflexivity.
      * split; [intros i Hi; apply MG1; apply DO; exact Hi|]. split; [exact I|].
        split; [exact C0|]. split; [exact C8|]. split; [exact C16|].
        split; [lia|]. split; [lia|]. split; [exact Hb0|]. split; [exact Hb16|].
        split; [intros i Hi; apply MG1; apply Db; exact Hi|]. split; exact I.
    + (* [comment removed for export] *)
      pose proof (PNSVGP.vgZ_conc fx R0 M0 (fun j => match j with 2%nat => S | 33%nat => b | 34%nat => n | 35%nat => c | 43%nat => ns | _ => 0 end)) as PP.
      cbn beta iota in PP. rewrite HO in PP. PMK.feed PP ltac:(first [PMK.sc]).
      PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & _ & FRZ & REST)); PMK.pvz_clrT.
      destruct REST as [(_ & _ & _ & _ & _ & LE1 & _) | (MS1 & KS1 & F11 & F12 & F13 & F14 & LT1 & C0 & C8 & C16)]; [exfalso; lia|].
      assert (FRZ' : forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 24) -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ; [exact Ha| intro X; apply N; lia]).
      pose proof (HPV M1 MG1 FRZ') as HP1.
      unfold PMSP.cfg.
      apply (PMK.spiece RSEGS L HI KL HIok (PGV8.v8_own x ++ LB) cr0 M0 model0 fx fx1 R0 0x396ac R1 _ M1 (fun a => v <= a < v + 24) K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ' CWR DEC).
      intros HH1.
      assert (MO1 : mem_ok M1).
      { split; [apply (PMK.ek_of_hpres L); exact HP1|]. split; [apply PMK.dk_grows; exact MG1|]. split; [exact (PMK.stk_grows L M0 M1 S 14336 MG1 STK)|].
        intros i Hi. apply MG1. apply DO. exact Hi. }
      apply (append_at fx1 R1 M1 model0 (ns - n) MOK ltac:(rewrite Ex; cbn; lia) ltac:(lia) CR); try assumption.
      * intros y Hy. apply KS1. revert y Hy; apply sub_in; vm_compute; reflexivity.
      * rewrite (KS1 10%nat) by PMK.inl. exact A10.
      * rewrite F11. f_equal. lia.
      * rewrite Ex. split; [intros i Hi; apply MG1; apply DO; exact Hi|]. split; [exact I|].
        split; [exact C0|]. split; [exact C8|]. split; [exact C16|].
        split; [lia|]. split; [lia|]. split; [exact Hb0|]. split; [exact Hb16|].
        split; [intros i Hi; apply MG1; apply Db; exact Hi|]. split; exact I.
Qed.

End Call.
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem vu8_append_ok : PMS.opnew_spec L HI -> PMS.opdel_spec L HI -> PNRS.vu8_append_spec L HI.
Proof.
  intros OPN OPD. unfold PNRS.vu8_append_spec, PNR.vu8_append_spec, PGV8.vu8_append_spec, PGV8.vu8_grow_spec.
  intros fx R M model K LB cr v a sp r g x HH MOK K0 ENT A10 A11 Hv1 Hv2 Hv3 VS OK Ha GO CR KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  change (PMSP.pm_scr 1) with 14336 in *.
  assert (BRLB : PMFR.brange L LB).
  { apply (PMFR.brange_of_heap L HI HIok _ LB cr M _ HH). intros y Hy. apply in_or_app. right. exact Hy. }
  cbn [PNL.pn_vu8_append PnLayoutS_u.NADDR_S] in *.
  assert (Hns : 0 <= PGV8.v8_size x + a < 2 ^ 64) by (destruct x; cbn in Ha |- *; [lia| destruct VS as (_ & _ & _ & _ & _ & H1 & _); lia]).
  apply (append_at R M model K LB cr v sp r g (PGV8.v8_size x + a) x Rra RAok Rsp Rtp K0 STK Hv1 Hv2 Hv3 OK GO Hns BRLB OPN OPD KONT fx R M model a MOK eq_refl ltac:(lia) CR);
    [intros y Hy; reflexivity | exact A10 | exact A11 | | exact VS | exact HH | apply L5C.model_but_vm_refl].
  exact (mem_ok0 M LB v sp x STK VS).
Qed.

Theorem vu8_resize_ok : PMS.opnew_spec L HI -> PMS.opdel_spec L HI -> PNRS.vu8_resize_spec L HI.
Proof.
  intros OPN OPD. unfold PNRS.vu8_resize_spec, PNR.vu8_resize_spec, PGV8.vu8_resize_spec, PGV8.vu8_grow_spec.
  intros fx R M model K LB cr v a sp r g x HH MOK K0 ENT A10 A11 Hv1 Hv2 Hv3 VS OK Ha GO CR KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  change (PMSP.pm_scr 1) with 14336 in *.
  assert (BRLB : PMFR.brange L LB).
  { apply (PMFR.brange_of_heap L HI HIok _ LB cr M _ HH). intros y Hy. apply in_or_app. right. exact Hy. }
  cbn [PNL.pn_vu8_resize PnLayoutS_u.NADDR_S] in *.
  exact (resize_at R M model K LB cr v sp r g a x Rra RAok Rsp Rtp K0 STK Hv1 Hv2 Hv3 OK GO Ha BRLB OPN OPD KONT fx MOK CR A10 A11 VS HH).
Qed.

End WithHeap.
End PNSVG.
