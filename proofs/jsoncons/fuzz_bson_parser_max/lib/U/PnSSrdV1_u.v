(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmFrame PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnParSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParKit
     PmTxtSpecs PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSSrdVP_u Bs0_code_383d4_383d8_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgSrcKit PgV8 PgV8Kit PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSSV1.
Import PMS.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation v8_atP := (PGV8.v8_at RSEGS PMSP.T3 PMSP.T4).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma room_cases a0 j c : 0 <= j -> c = a0 * 2 ^ j -> 1 <= a0 <= 2 ^ 14 -> 2 ^ 26 < c ->
  (8193 <= a0 /\ c = a0 * 8192) \/ 2 ^ 26 + 2 ^ 14 <= c.
Proof.
  intros Hj Hc Ha HC.
  destruct (Z_lt_le_dec j 13) as [Hlt|Hge].
  - exfalso. assert (P : 2 ^ j <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
    assert (c <= 2 ^ 14 * 2 ^ 12) by (rewrite Hc; apply Z.mul_le_mono_nonneg; lia). change (2 ^ 14 * 2 ^ 12) with (2 ^ 26) in H. lia.
  - destruct (Z.eq_dec j 13) as [->|Hne].
    + left. change (2 ^ 13) with 8192 in Hc. split; [|exact Hc]. rewrite Hc in HC. lia.
    + right. assert (E : 2 ^ j = 2 ^ 14 * 2 ^ (j - 14)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (T1 : 1 <= 2 ^ (j - 14)) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
      set (t := 2 ^ (j - 14)) in *. rewrite E in Hc.
      assert (M1 : 4097 <= a0 * t) by nia. nia.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nodup_perm (l l' : list (Z * Z)) : Permutation.Permutation l l' -> base.NoDup (map fst l) -> base.NoDup (map fst l').
Proof.
  intros P ND. apply NoDup_ListNoDup. apply NoDup_ListNoDup in ND.
  eapply Permutation.Permutation_NoDup; [|exact ND]. apply Permutation.Permutation_map. exact P.
Qed.
Lemma perm_tb (src : PM.srcst) (x : PGV8.v8) (OB LB : list (Z * Z)) cr M VM :
  hi_heap HI (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LB) cr M VM ->
  hi_heap HI (PGV8.v8_own x ++ (PM.src_own src ++ OB ++ LB)) cr M VM.
Proof.
  intros HH. apply (hio_perm L SCFG HI HIok _ _ cr M VM HH).
  - intros b. rewrite !in_app_iff. tauto.
  - apply (nodup_perm (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LB)); [|exact (PMPK.heap_nodup L HI HIok _ _ _ _ HH)].
    rewrite (app_assoc (PM.src_own src) (PGV8.v8_own x)). rewrite (app_assoc (PGV8.v8_own x) (PM.src_own src)).
    apply Permutation.Permutation_app_tail. apply Permutation.Permutation_app_comm.
Qed.
Lemma perm_tb_back (src : PM.srcst) (x : PGV8.v8) (OB LB : list (Z * Z)) cr M VM :
  hi_heap HI (PGV8.v8_own x ++ (PM.src_own src ++ OB ++ LB)) cr M VM ->
  hi_heap HI (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LB) cr M VM.
Proof.
  intros HH. apply (hio_perm L SCFG HI HIok _ _ cr M VM HH).
  - intros b. rewrite !in_app_iff. tauto.
  - apply (nodup_perm (PGV8.v8_own x ++ (PM.src_own src ++ OB ++ LB))); [|exact (PMPK.heap_nodup L HI HIok _ _ _ _ HH)].
    rewrite (app_assoc (PM.src_own src) (PGV8.v8_own x)). rewrite (app_assoc (PGV8.v8_own x) (PM.src_own src)).
    apply Permutation.Permutation_app_tail. apply Permutation.Permutation_app_comm.
Qed.

Lemma own_apart (OWN LB : list (Z * Z)) cr M VM : hi_heap HI (OWN ++ LB) cr M VM ->
  forall B m, In (B, m) OWN -> B + m <= hl_ceil L /\ (B + m <= hl_img_lo L \/ hl_img_hi L <= B) /\
    forall B' m', In (B', m') LB -> B + m <= B' \/ B' + m' <= B.
Proof.
  intros HH B m Hin. assert (BR : PMFR.brange L (OWN ++ LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  destruct (BR B m (in_or_app _ _ _ (or_introl Hin))) as (Z0 & Z1 & Z4). split; [exact Z4|]. split; [exact Z1|]. intros B' m' Hin'.
  assert (NE : B <> B') by (apply (PMPK.fst_neq_app OWN LB B m B' m' (PMPK.heap_nodup L HI HIok _ _ _ _ HH) Hin Hin')).
  exact (PMPK.blocks_apart_heap L HI HIok _ cr M _ B m B' m' HH (in_or_app _ _ _ (or_introl Hin)) (in_or_app _ _ _ (or_intror Hin')) NE).
Qed.
Lemma own_not_client OWN LB cr M VM B m a sp scr :
  hi_heap HI (OWN ++ LB) cr M VM -> In (B, m) OWN -> B <= a < B + m -> ~ client_addr L LB sp scr a.
Proof.
  intros HH Hin Ha. destruct (own_apart OWN LB cr M VM HH B m Hin) as (Q4 & Q1 & AP). intros [((B' & m') & Hb & Hr)|[[S1 _]|[IM _]]].
  - cbn in Hr. destruct (AP B' m' Hb); lia.
  - lia.
  - lia.
Qed.
Lemma outside_own (W OWN : list (Z * Z)) a : L5.outside W a -> L5.outside (W ++ OWN) a \/ exists B m, In (B, m) OWN /\ B <= a < B + m.
Proof.
  intros O. induction OWN as [|(B, m) OWN IH]; [left; rewrite app_nil_r; exact O|].
  destruct (PMK.rng_dec a B (B + m)) as [I|NI]; [right; exists B, m; split; [left; reflexivity| exact I]|].
  destruct IH as [O'|(B' & m' & Hin & Ha)]; [left| right; exists B', m'; split; [right; exact Hin| exact Ha]].
  intros r Hr. apply in_app_or in Hr. destruct Hr as [Hr|[<-|Hr]]; [apply O; exact Hr| unfold L5.in_rng; cbn [fst snd]; exact NI| apply O'; apply in_or_app; right; exact Hr].
Qed.
Lemma in123 {X} (l1 l2 l3 l4 : list X) y : In y (l1 ++ l2 ++ l3) -> In y (l1 ++ l2 ++ l3 ++ l4).
Proof. rewrite !in_app_iff. tauto. Qed.
Lemma in3 {X} (l1 l2 l3 l4 : list X) y : In y l3 -> In y (l1 ++ l2 ++ l3 ++ l4).
Proof. rewrite !in_app_iff. tauto. Qed.
Lemma in4 {X} (l1 l2 l3 l4 : list X) y : In y l4 -> In y (l1 ++ l2 ++ l3 ++ l4).
Proof. rewrite !in_app_iff. tauto. Qed.
Lemma own2 (src : PM.srcst) (x : PGV8.v8) (OB LB : list (Z * Z)) : PM.src_own src ++ PGV8.v8_own x ++ OB ++ LB = (PM.src_own src ++ PGV8.v8_own x) ++ (OB ++ LB).
Proof. rewrite <- !app_assoc. reflexivity. Qed.

Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (cr0 : credit).
Variables (S r len : Z) (V : PGV8.vowner) (OB : list (Z * Z)) (src0 : PM.srcst) (x0 : PGV8.v8) (g0 : Z) (str : PM.vstr) (sm0 : PM.strm).
#[local] Abbreviation os := (PGV8.vw_os V).
#[local] Abbreviation ois := (PGV8.vw_ois V).
#[local] Abbreviation ov := (PGV8.vw_ov V).
#[local] Abbreviation lo := (PGV8.vw_lo V).
#[local] Abbreviation hi := (PGV8.vw_hi V).
Hypothesis VOK : PGV8.vowner_ok RSEGS AD L HI V.
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis K0 : K [].
Hypothesis SPLO : S <= lo.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UN0 : PM.unread src0 sm0 < 2 ^ 26.
Hypothesis SZ0 : PGV8.v8_size x0 = 0.
Hypothesis ROOM0 : PGV8.v8_room x0 (PM.unread src0 sm0).
Hypothesis RSZ : PNRS.vu8_resize_spec L HI.
Hypothesis SRD : PGS.src_read_specG RSEGS AD L HI.
Hypothesis FBT : PGS.fill_buffer_tb_specG RSEGS AD L HI.
(* [comment removed for export] *)
Definition W0 : list L5.range := PGS.W_srcfG os ois ++ [(ov, 24)].
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (x' : PGV8.v8) (g' : Z)
                         (sm' : PM.strm) (cr' : credit) (d : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
  PMSP.consumed src0 src' sm0 sm' = d -> PGV8.v8_size x' = d ->
  (d = len -> PGV8.v8_room x' (PM.unread src' sm')) ->
  PGV8.vw_at V M' src' x' g' OB -> PM.iss_at RSEGS AD T3 M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5C.hpres L LBX S (PMSP.pm_scr 5) W0 M0 M' ->
  PMSP.credit_keep cr0 cr' (PGV8.pot_v8 L x0 g0) (PGV8.pot_v8 L x' g') ->
  model_but_vm model0 model' -> hi_heap HI (PM.src_own src' ++ PGV8.v8_own x' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition saves8 (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22))).
Definition kept7 (R : bvmap 5 word) : Prop := forall y, In y [3; 4; 23; 24; 25; 26; 27]%nat -> getr R (reg y) = getr R0 (reg y).
(* [comment removed for export] *)
Definition memrel (M : word -> option byte) : Prop :=
  PMK.ek L (OB ++ LBX) S 22528 W0 M0 M /\ PMK.dk L (OB ++ LBX) S 22528 M0 M /\ L5C.stk (hl_sptop L) M S 22528.
(* [comment removed for export] *)
Definition vroom (x : PGV8.v8) : Prop :=
  match x with
  | PGV8.V8Null => True
  | PGV8.V8Blk _ _ c => exists a0 j, 0 <= j /\ c = a0 * 2 ^ j /\ 1 <= a0 <= 2 ^ 14
                        /\ (a0 + PM.unread src0 sm0 <= 2 ^ 26 \/ (a0 <= len /\ (a0 = 2 ^ 14 \/ a0 = len)))
  end.
(* [comment removed for export] *)
Definition acct (src : PM.srcst) (x : PGV8.v8) (sm : PM.strm) (w : Z) : Prop :=
  PMSP.consumed src0 src sm0 sm = len - w /\ PGV8.v8_size x = len - w /\ PMSP.src_step src0 src sm0 sm
  /\ vroom x /\ (w = len \/ Z.min w PM.CHUNK <= PGV8.v8_cap x).
(* [comment removed for export] *)
Definition state_ok (M : word -> option byte) (model : Model) (src : PM.srcst) (x : PGV8.v8) (g : Z) (sm : PM.strm) (cr : credit) : Prop :=
  memrel M /\ saves8 M /\ PGV8.vw_at V M src x g OB /\ PM.iss_at RSEGS AD T3 M ois str sm
  /\ PMST.base_ok RSEGS AD M /\ PGV8.v8_ok x g
  /\ hi_heap HI (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) cr M (m_vmmaps model) /\ PMSP.model_ok model /\ model_but_vm model0 model
  /\ PMSP.credit_le (PGV8.pot_v8 L x g) cr
  /\ PMSP.credit_keep cr0 cr (PGV8.pot_v8 L x0 g0) (PGV8.pot_v8 L x g).
(* [comment removed for export] *)
Definition lregs (R : bvmap 5 word) (w : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 64) /\ getr R (reg 8) = Z_to_bv 64 len /\ getr R (reg 9) = Z_to_bv 64 ov
  /\ getr R (reg 18) = Z_to_bv 64 os /\ getr R (reg 21) = Z_to_bv 64 w /\ kept7 R.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lay : lo <= os /\ os + 296 <= hi /\ lo <= ois /\ ois + 272 <= hi /\ lo <= ov /\ ov + 24 <= hi /\ hi <= hl_sptop L /\ hi <= 2 ^ 47
            /\ os mod 8 = 0 /\ ois mod 8 = 0 /\ ov mod 8 = 0 /\ 4096 <= lo
            /\ (os + 296 <= ois \/ ois + 272 <= os) /\ (ov + 24 <= os \/ os + 296 <= ov) /\ (ov + 24 <= ois \/ ois + 272 <= ov).
Proof using VOK. exact (PGV8.vo_lay _ _ _ _ _ VOK). Qed.
Lemma tsrc M src x g : PGV8.vw_at V M src x g OB ->
  PM.src_fields_at RSEGS T3 M os ois (ois + 16) src /\ PM.nullis_at RSEGS AD T3 M (os + 8) /\ L5.defined M os 296 /\ v8_atP M ov x /\ PGV8.v8_ok x g.
Proof using VOK. exact (PGV8.vo_src _ _ _ _ _ VOK M src x g OB). Qed.
Lemma inW_W0 a : PMK.inW W0 a -> (os + 240 <= a < os + 296) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (ov <= a < ov + 24).
Proof.
  intros (r0 & Hin & Hr). unfold W0, PGS.W_srcfG in Hin. cbn [app] in Hin. unfold L5.in_rng in Hr.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma inW_W0' a : PMK.inW W0 a -> lo <= a < hi.
Proof using VOK. intros I. apply inW_W0 in I. pose proof lay. lia. Qed.
Lemma outside_W0 a : a < S -> L5.outside W0 a.
Proof using VOK SPLO. intros Ha r0 Hr0 Hin. assert (I : PMK.inW W0 a) by (exists r0; split; assumption). apply inW_W0' in I. lia. Qed.
Lemma W_src_in (src : PM.srcst) a : PMK.inW (PGS.W_srcG os ois src) a -> PMK.inW W0 a \/ (PM.sr_qc src <= a < PM.sr_qc src + PM.CHUNK).
Proof.
  intros (r0 & Hin & Hr). unfold PGS.W_srcG in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]].
  - left. exists r0. split; [unfold W0; apply in_or_app; left; exact Hin| exact Hr].
  - right. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma vw_xfer M M' src src' x x' g g' cr VM scr0 sp' scr' (Wx : list L5.range) :
  PGV8.vw_at V M src x g OB -> hi_heap HI (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) cr M VM -> L5C.stk (hl_sptop L) M S scr0 ->
  0 <= scr0 -> S - scr0 <= sp' - scr' -> sp' <= S ->
  L5C.hpres L (OB ++ LBX) sp' scr' (PGS.W_srcfG os ois ++ [(ov, 24)] ++ Wx) M M' ->
  Forall (fun r => S - scr0 <= fst r /\ fst r + snd r <= S) Wx ->
  PM.src_fields_at RSEGS T3 M' os ois (ois + 16) src' -> PM.sr_qc src' = PM.sr_qc src -> v8_atP M' ov x' -> PGV8.v8_ok x' g' ->
  PGV8.vw_at V M' src' x' g' OB.
Proof using VOK SPLO HIok.
  intros AT HH STK H0 H1 H2 HP FW SFq QC VS TB. pose proof STK as (_ & SLO & _ & STOP & _).
  pose proof (own_apart (PM.src_own src ++ PGV8.v8_own x) (OB ++ LBX) cr M VM ltac:(rewrite <- own2; exact HH)) as OWNF.
  assert (BR : PMFR.brange L (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  apply (PGV8.vo_upd _ _ _ _ _ VOK LBX sp' scr' Wx M M' src src' x x' g g' OB cr VM ltac:(lia) AT HH).
  - apply Forall_forall. intros [B m] Hin. cbn [fst snd]. left.
    destruct (BR B m (in123 _ _ _ _ _ Hin)) as (_ & _ & Z4). unfold hl_ceil in Z4. lia.
  - intros [B m] Hin. cbn [fst snd]. split.
    + destruct (OWNF (PM.sr_qc src) PM.CHUNK ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & AP).
      destruct (AP B m ltac:(apply in_or_app; left; exact Hin)); lia.
    + intros B' m' Hin'. destruct (OWNF B' m' ltac:(apply in_or_app; right; exact Hin')) as (_ & _ & AP).
      destruct (AP B m ltac:(apply in_or_app; left; exact Hin)); lia.
  - apply Forall_forall. intros [a n] Hr. pose proof (proj1 (Forall_forall _ _) FW (a, n) Hr) as [R1 R2]. cbn [fst snd] in *. split; [left; lia|].
    intros B m Hin. destruct (BR B m (in3 _ _ _ _ _ Hin)) as (_ & _ & Z4). unfold hl_ceil in Z4. lia.
  - exact HP.
  - exact SFq.
  - exact QC.
  - exact VS.
  - exact TB.
Qed.

(* [comment removed for export] *)
Lemma base_keep M M' : PMK.ek L (OB ++ LBX) S 22528 W0 M M' -> L5C.stk (hl_sptop L) M S 22528 -> PMST.base_ok RSEGS AD M -> PMST.base_ok RSEGS AD M'.
Proof using VOK SPLO KL SF LY.
  intros E (_ & SLO & _ & STOP & _) B. apply (PMKP.base_ok_keep RSEGS AD L KL SF (OB ++ LBX) S 22528 W0 M M' E); [| | | |exact B].
  all: intros a Ha; apply outside_W0; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S] in Ha; destruct STOP; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma finish (fx : FPState) R M model src x g sm cr (w : Z) :
  getr R (reg 1) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 1))) -> getr R (reg 2) = Z_to_bv 64 S ->
  getr R (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> getr R (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) ->
  getr R (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) -> getr R (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) ->
  getr R (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22))) -> kept7 R ->
  getr R (reg 10) = Z_to_bv 64 (len - w) -> 0 <= w <= len ->
  state_ok M model src x g sm cr -> acct src x sm w ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x396a4 M model) K.
Proof using All.
  intros E1 E2 E8 E9 E18 E19 E20 E21 E22 KP E10 Hw
         ((EK & DK & STK) & _ & PA & IA & BASE & TBOK & HH & MOK & MB & _ & CK) (CONS & SZ & STEP & VR & _).
  pose proof MOK as (Mh & Ml & Mm). pose proof RAok as (Hr1 & Hr2).
  assert (RA : getr R (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra0).
  unfold PMSP.cfg.
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx R M 0x396a4 W_38478 r F_38478 ltac:(reflexivity) D_38478 RA Hr1 Hr2)|].
  apply (KONT fx R M model src x g sm cr (len - w)); try assumption; try lia.
  - apply PMK.preserved_by_index. intros y Hy. unfold PMK.cs_all in Hy. cbn in Hy.
    destruct Hy as [<-|Hy]; [rewrite E2, Rsp0; reflexivity|].
    destruct Hy as [<-|Hy]; [apply KP; cbn; auto|]. destruct Hy as [<-|Hy]; [apply KP; cbn; auto|].
    destruct Hy as [<-|Hy]; [rewrite E8; apply Z_to_bv_bv_unsigned|]. destruct Hy as [<-|Hy]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
    destruct Hy as [<-|Hy]; [rewrite E18; apply Z_to_bv_bv_unsigned|]. destruct Hy as [<-|Hy]; [rewrite E19; apply Z_to_bv_bv_unsigned|].
    destruct Hy as [<-|Hy]; [rewrite E20; apply Z_to_bv_bv_unsigned|]. destruct Hy as [<-|Hy]; [rewrite E21; apply Z_to_bv_bv_unsigned|].
    destruct Hy as [<-|Hy]; [rewrite E22; apply Z_to_bv_bv_unsigned|].
    apply KP. destruct Hy as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn; auto 10.
  - (* [comment removed for export] *)
    intros Ed. assert (Hw0 : w = 0) by lia. subst w.
    pose proof STEP as (_ & _ & _ & _ & UNR). unfold PMSP.consumed in CONS.
    destruct x as [|b n c]; [exact I|]. cbn in VR |- *. destruct VR as (a0 & j & Hj & Hc & Ha0 & ALT).
    exists a0, j. split; [exact Hj|]. split; [exact Hc|]. split; [exact Ha0|]. destruct ALT as [X|[X _]]; lia.
  - apply (PMK.hpres_of L LBX S 22528 W0 M0 M).
    + apply (PMK.ek_weaken L LBX (OB ++ LBX) S 22528 S 22528 W0 W0 M0 M EK); [intros y Hy; apply in_or_app; right; exact Hy| intros y Hy; exact Hy| intros a Ha; exact Ha].
    + destruct STK as (_ & _ & _ & _ & D); exact D.
    + apply (PMPK.dk_incl L LBX (OB ++ LBX) S 22528 M0 M DK). intros y Hy; apply in_or_app; right; exact Hy.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma src_callee_mem M M' src x cr VM scr' (W' : list L5.range) :
  memrel M -> saves8 M -> hi_heap HI (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) cr M VM -> 0 <= scr' <= 22528 - 64 ->
  L5C.hpres L (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) (S - 64) scr' W' M M' ->
  (forall a, PMK.inW W' a -> PMK.inW W0 a \/ exists B m, In (B, m) (PM.src_own src ++ PGV8.v8_own x) /\ B <= a < B + m) ->
  memrel M' /\ saves8 M' /\ PMK.ek L (OB ++ LBX) S 22528 W0 M M'.
Proof using VOK SPLO HIok KL.
  intros (EK & DK & STK) SV HH Hs HP FP.
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  set (LBc := PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) in *.
  assert (BR : PMFR.brange L LBc) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  pose proof (own_apart (PM.src_own src ++ PGV8.v8_own x) (OB ++ LBX) cr M VM ltac:(unfold LBc in HH; rewrite <- own2; exact HH)) as OWNF.
  assert (OWNLO : forall a B m, In (B, m) (PM.src_own src ++ PGV8.v8_own x) -> B <= a < B + m -> a < S - 22528).
  { intros a B m Hin Ha. destruct (OWNF B m Hin) as (Q & _). lia. }
  assert (EKr : PMK.ek L LBc (S - 64) scr' W' M M') by (apply (PMK.ek_of_hpres L); exact HP).
  assert (STKr : L5C.stk (hl_sptop L) M (S - 64) scr').
  { apply (PMK.stk_call L M S 22528 (S - 64) scr' STK); [lia|lia|lia|]. replace (S - 64) with (S + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  assert (SC0 : 0 <= scr') by lia.
  assert (INC : incl (OB ++ LBX) LBc) by (intros y Hy; unfold LBc; rewrite own2; apply in_or_app; right; exact Hy).
  assert (EKn : PMK.ek L (OB ++ LBX) S 22528 W0 M M').
  { apply (PMPK.ek_drop_own L (PM.src_own src ++ PGV8.v8_own x) (OB ++ LBX) S 22528 W0 (W0 ++ (PM.src_own src ++ PGV8.v8_own x)) M M').
    - rewrite <- own2. apply (PMK.ek_callee_in' RSEGS L KL LBc LBc S 22528 (S - 64) scr' (W0 ++ (PM.src_own src ++ PGV8.v8_own x)) W' M M' HP (incl_refl _));
        [lia|lia|lia| destruct STOP; lia| exact (PMFR.brange_hi L LBc BR)|].
      intros a I. right. destruct (FP a I) as [(r0 & Hr0 & Hin)|(B & m & Hin & Ha)].
      + exists r0. split; [apply in_or_app; left; exact Hr0| exact Hin].
      + exists (B, m). split; [apply in_or_app; right; exact Hin| unfold L5.in_rng; cbn [fst snd]; lia].
    - exact OWNF.
    - intros a O. apply outside_own. exact O. }
  assert (NOTW : forall a n, S - 64 <= a -> a + n <= S -> forall i, a <= i < a + n -> ~ PMK.inW W' i).
  { intros a n H1 H2 i Hi I. destruct (FP i I) as [I'|(B & m & Hin & Ha)]; [apply inW_W0' in I'; lia| apply (OWNLO i B m Hin) in Ha; lia]. }
  split; [split; [|split]|].
  - exact (PMK.ek_trans L (OB ++ LBX) S 22528 W0 M0 M M' EK EKn).
  - apply (PMK.dk_trans L (OB ++ LBX) S 22528 M0 M M' DK).
    apply (PMK.dk_callee L (OB ++ LBX) LBc S 22528 (S - 64) scr' W' M M' HP INC); [lia| lia].
  - apply (PMK.stk_after RSEGS L KL LBc M M' S 22528 (S - 64) scr' W' STK HP); lia.
  - split; [|exact EKn].
    destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
    unfold saves8. repeat split; (apply (PMFR.u64_keep RSEGS L KL LBc (S - 64) scr' W' M M' EKr STKr SC0); [lia|lia| apply NOTW; lia| eassumption]).
Qed.

(* [comment removed for export] *)
Lemma iss_xfer M M' (LBc : list (Z * Z)) scr' (W' : list L5.range) sm :
  incl LBX LBc -> PMFR.brange L LBc -> L5C.stk (hl_sptop L) M S 22528 -> 0 <= scr' <= 22528 - 64 ->
  L5C.hpres L LBc (S - 64) scr' W' M M' ->
  (forall i, ois <= i < ois + 272 -> ~ PMK.inW W' i) -> (forall a, PMK.inW W' a -> S - 64 <= a \/ hl_img_lo L <= a < hl_img_hi L) ->
  PM.iss_at RSEGS AD T3 M ois str sm -> PM.iss_at RSEGS AD T3 M' ois str sm.
Proof using VOK SPLO HIok KL INCS.
  intros INC BR STK Hs HP NI WHI IA. pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay as LAY.
  assert (EKr : PMK.ek L LBc (S - 64) scr' W' M M') by (apply (PMK.ek_of_hpres L); exact HP).
  assert (STKr : L5C.stk (hl_sptop L) M (S - 64) scr').
  { apply (PMK.stk_call L M S 22528 (S - 64) scr' STK); [lia|lia|lia|]. replace (S - 64) with (S + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  assert (SC0 : 0 <= scr') by lia.
  apply (PMF.iss_at_agree RSEGS AD M M' ois str sm); [lia|lia| | |exact IA].
  - apply (PMFR.ag_hi RSEGS L KL LBc (S - 64) scr' W' M M' EKr STKr SC0); [lia|lia| exact NI].
  - intros c n p E. apply (PMFR.ag_block RSEGS L KL LBc (S - 64) scr' W' M M' EKr STKr SC0 BR WHI).
    apply INC. apply INCS. rewrite E. left. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grow_ok_now src x g sm w nn M :
  PGV8.vw_at V M src x g OB -> vroom x -> (w = len \/ Z.min w PM.CHUNK <= PGV8.v8_cap x) -> len - w <= PGV8.v8_size x ->
  len - w <= PM.unread src0 sm0 - PM.unread src sm -> 0 <= w <= len -> 0 <= PM.unread src sm ->
  (nn <= PGV8.v8_cap x \/ nn = (len - w) + Z.min w PM.CHUNK) ->
  PGV8.v8_grow_ok x nn /\ nn <= 2 ^ 27.
Proof using VOK UN0 Hlen.
  intros AT VR MIN SZ CONS Hw HU Hnn.
  destruct (tsrc M src x g AT) as (_ & _ & _ & VS & _). unfold PGV8.v8_grow_ok.
  destruct x as [|b n c]; cbn in SZ, VR, MIN, Hnn |- *.
  - destruct Hnn as [H| ->]; [split; [left; exact H| lia]|]. unfold PM.CHUNK. split; [right; split; lia| lia].
  - destruct VS as (_ & _ & _ & _ & _ & H1 & H2 & _).
    destruct (Z_lt_le_dec c nn) as [GT|LE]; [|split; [left; exact LE| lia]].
    destruct Hnn as [H| ->]; [exfalso; lia|].
    assert (NB : len - w + Z.min w PM.CHUNK < 2 ^ 26 + 2 ^ 14 /\ len - w + Z.min w PM.CHUNK <= len) by (unfold PM.CHUNK; lia).
    split; [|lia]. right. split; [|lia].
    destruct (Z_lt_le_dec (2 ^ 26) c) as [BIG|OK]; [|exact OK]. exfalso.
    destruct VR as (a0 & j & Hj & Hc & Ha0 & ALT).
    destruct (room_cases a0 j c Hj Hc Ha0 BIG) as [(A1 & A2)|A3]; [|lia].
    destruct ALT as [X|(X1 & [X2|X2])].
    + assert (8193 * 8193 <= 8193 * a0) by nia. unfold PM.CHUNK in *. nia.
    + rewrite X2 in A2. change (2 ^ 14 * 8192) with (2 ^ 27) in A2. lia.
    + subst a0. nia.
Qed.

Lemma vroom_after src x g w nn M M' x' :
  PGV8.vw_at V M src x g OB -> vroom x -> (w = len \/ Z.min w PM.CHUNK <= PGV8.v8_cap x) -> len - w <= PGV8.v8_size x -> 0 <= w <= len ->
  (nn <= PGV8.v8_cap x \/ nn = (len - w) + Z.min w PM.CHUNK) ->
  v8_atP M' ov x' -> PGV8.v8_size x' = nn ->
  (PGV8.v8_cap x' = PGV8.v8_cap x \/ PGV8.v8_cap x' = Z.max (2 * PGV8.v8_cap x) nn) ->
  vroom x'.
Proof using VOK Hlen.
  intros AT VR MIN SZ Hw Hnn VS' SZ' CL.
  destruct (tsrc M src x g AT) as (_ & _ & _ & VS & _).
  destruct x' as [|b' n' c']; [exact I|]. cbn in SZ', CL |- *. subst n'.
  destruct VS' as (_ & _ & _ & _ & _ & G1 & G2 & _).
  destruct x as [|b n c]; cbn in SZ, VR, MIN, Hnn, CL.
  - (* [comment removed for export] *)
    assert (E : c' = nn) by lia.
    destruct Hnn as [H|H]; [lia|]. assert (Hw' : w = len) by lia. subst w. rewrite Z.sub_diag, Z.add_0_l in H.
    exists nn, 0. change (2 ^ 0) with 1. unfold PM.CHUNK in H. split; [lia|]. split; [lia|]. split; [lia|]. right. split; lia.
  - destruct VS as (_ & _ & _ & _ & _ & H1 & H2 & _). destruct VR as (a0 & j & Hj & Hc & Ha0 & ALT).
    destruct CL as [E|E]; [exists a0, j; subst c'; split; [lia|]; split; [lia|]; split; [lia| exact ALT]|].
    destruct (Z_lt_le_dec (2 * c) nn) as [EV|DB].
    + (* [comment removed for export] *)
      destruct Hnn as [H|H]; [lia|]. destruct MIN as [-> |MN]; [|lia].
      rewrite Z.sub_diag, Z.add_0_l in H. unfold PM.CHUNK in H.
      exists nn, 0. change (2 ^ 0) with 1. split; [lia|]. split; [lia|]. split; [lia|]. right. split; lia.
    + exists a0, (j + 1). rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. split; [lia|]. split; [lia|]. split; [lia|]. exact ALT.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma call_resize (fx : FPState) R M model src x g sm cr (nn X w : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 64) -> kept7 R ->
  getr R (reg 10) = Z_to_bv 64 ov -> getr R (reg 11) = Z_to_bv 64 nn -> 0 <= nn ->
  (nn <= PGV8.v8_cap x \/ nn = (len - w) + Z.min w PM.CHUNK) ->
  vroom x -> (w = len \/ Z.min w PM.CHUNK <= PGV8.v8_cap x) -> len - w <= PGV8.v8_size x -> len - w <= PM.unread src0 sm0 - PM.unread src sm ->
  0 <= w <= len -> 0 <= PM.unread src sm ->
  state_ok M model src x g sm cr ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : PGV8.v8) (g' : Z) (cr' : credit),
     regs_preserved R R' -> PGV8.v8_size x' = nn -> PGV8.v8_cap x <= PGV8.v8_cap x' -> vroom x' ->
     state_ok M' model' src x' g' sm cr' ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x396ac M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 Hnn0 Hnn VR MIN SZW CONSW Hw HU ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK) NEXT.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay as LAY.
  set (LB' := PM.src_own src ++ OB ++ LBX).
  pose proof (perm_tb src x OB LBX cr M _ HH) as HH'. fold LB' in HH'.
  pose proof (tsrc M src x g PA) as (PSF & PNI & PD & VS & _).
  destruct (grow_ok_now src x g sm w nn M PA VR MIN SZW CONSW Hw HU Hnn) as (GOK & N27).
  assert (STKr : L5C.stk (hl_sptop L) M (S - 64) (PMSP.pm_scr 1)).
  { apply (PMK.stk_call L M S 22528 (S - 64) (PMSP.pm_scr 1) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|].
    replace (S - 64) with (S + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  pose proof RSZ as RZ. unfold PNRS.vu8_resize_spec, PNR.vu8_resize_spec, PGV8.vu8_resize_spec, PGV8.vu8_grow_spec in RZ.
  cbn [PNL.pn_vu8_resize PnLayoutS_u.NADDR_S] in RZ.
  apply (RZ fx R M model K LB' cr ov nn (S - 64) X g x HH' MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
    split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0| exact STKr]. }
  { rewrite L5K.rl10. exact A10. }
  { rewrite L5K.rl11. exact A11. }
  { lia. }
  { lia. }
  { lia. }
  { exact VS. }
  { exact TBOK. }
  { split; [exact Hnn0| destruct STOP; lia]. }
  { exact GOK. }
  { exact CRL. }
  intros fx' R' M' model' x' g' cr' RP VS' SZ OK' CAPLE OWN CL HP CK MB' HH2.
  apply (NEXT fx' R' M' model' x' g' cr' RP SZ CAPLE (vroom_after src x g w nn M M' x' PA VR MIN SZW Hw Hnn VS' SZ CL)).
  assert (BR' : PMFR.brange L LB') by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M' _ HH2); intros y Hy; apply in_or_app; right; exact Hy).
  assert (EKr : PMK.ek L LB' (S - 64) (PMSP.pm_scr 1) [(ov, 24)] M M') by (apply (PMK.ek_of_hpres L); exact HP).
  assert (SC1 : 0 <= PMSP.pm_scr 1) by (unfold PMSP.pm_scr; lia).
  assert (WHI : forall a, PMK.inW [(ov, 24)] a -> S - 64 <= a \/ hl_img_lo L <= a < hl_img_hi L).
  { intros a I. left. apply PMFR.inW_inv1 in I. lia. }
  assert (NOTW : forall a n, a + n <= ov \/ ov + 24 <= a -> forall i, a <= i < a + n -> ~ PMK.inW [(ov, 24)] i).
  { intros a n XO i Hi I. apply PMFR.inW_inv1 in I. lia. }
  assert (INL : incl (OB ++ LBX) LB') by (intros y Hy; unfold LB'; apply in_or_app; right; exact Hy).
  assert (HPw : L5C.hpres L (OB ++ LBX) (S - 64) (PMSP.pm_scr 1) (PGS.W_srcfG os ois ++ [(ov, 24)] ++ []) M M').
  { apply (PGSK.hpres_weaken L (OB ++ LBX) LB' (S - 64) (PMSP.pm_scr 1) _ [(ov, 24)] M M' HP INL).
    intros a O r0 [<-|[]]. apply O. apply in_or_app. right. left. reflexivity. }
  assert (HHn : hi_heap HI (PM.src_own src ++ PGV8.v8_own x' ++ OB ++ LBX) cr' M' (m_vmmaps model')) by (apply perm_tb_back; exact HH2).
  split; [split; [|split]|].
  - apply (PMK.ek_trans L (OB ++ LBX) S 22528 W0 M0 M M' EK).
    apply (PMK.ek_callee_in' RSEGS L KL (OB ++ LBX) LB' S 22528 (S - 64) (PMSP.pm_scr 1) W0 [(ov, 24)] M M' HP INL);
      [unfold PMSP.pm_scr; lia| lia| lia| destruct STOP; lia| exact (PMFR.brange_hi L (OB ++ LBX) (PMFR.brange_incl L (OB ++ LBX) LB' BR' INL))|].
    intros a I. right. apply PMFR.inW_inv1 in I. exists (ov, 24). split; [unfold W0; apply in_or_app; right; left; reflexivity|].
    unfold L5.in_rng. cbn [fst snd]. lia.
  - apply (PMK.dk_trans L (OB ++ LBX) S 22528 M0 M M' DK).
    apply (PMK.dk_callee L (OB ++ LBX) LB' S 22528 (S - 64) (PMSP.pm_scr 1) [(ov, 24)] M M' HP INL); [unfold PMSP.pm_scr; lia| lia].
  - apply (PMK.stk_after RSEGS L KL LB' M M' S 22528 (S - 64) (PMSP.pm_scr 1) [(ov, 24)] STK HP); unfold PMSP.pm_scr; lia.
  - split.
    { destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
      unfold saves8. repeat split; (apply (PMFR.u64_keep RSEGS L KL LB' (S - 64) (PMSP.pm_scr 1) [(ov, 24)] M M' EKr STKr SC1);
                                    [lia|lia| apply NOTW; lia| eassumption]). }
    split.
    { apply (vw_xfer M M' src src x x' g g' cr (m_vmmaps model) 22528 (S - 64) (PMSP.pm_scr 1) [] PA HH STK ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) ltac:(lia) HPw ltac:(constructor)); [|reflexivity| exact VS'| exact OK'].
      apply (PMFR.src_keep RSEGS L KL LB' (S - 64) (PMSP.pm_scr 1) [(ov, 24)] M M' EKr STKr SC1 BR' WHI os ois (ois + 16) src); [lia|lia| intros i Hi; apply (NOTW (os + 240) 56); lia| unfold LB', PM.src_own; left; reflexivity| exact PSF]. }
    split.
    { apply (iss_xfer M M' LB' (PMSP.pm_scr 1) [(ov, 24)] sm ltac:(intros y Hy; apply INL; apply in_or_app; right; exact Hy) BR' STK ltac:(unfold PMSP.pm_scr; lia) HP); [intros i Hi; apply (NOTW ois 272); lia| exact WHI| exact IA]. }
    split.
    { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB' (S - 64) (PMSP.pm_scr 1) [(ov, 24)] M M' EKr);
        first [exact BASE | intros a Ha r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; cbn in Ha; lia]. }
    split; [exact OK'|].
    split; [exact HHn|].
    split; [exact (PMFR.model_ok_but_vm model model' MOK MB')|].
    split; [exact (L5C.model_but_vm_trans _ _ _ MB MB')|].
    split; [apply (PMPK.credit_le_keep cr cr' _ _ CRL CK)|].
    unfold PMSP.credit_keep in *. destruct CRK, CK. split; lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vdst (x : PGV8.v8) (p k : Z) : Prop := exists b n c, x = PGV8.V8Blk b n c /\ b <= p /\ p + k <= b + c.

(* [comment removed for export] *)
Lemma svw_ok M x g scr0 : 0 <= scr0 -> L5C.stk (hl_sptop L) M S scr0 -> PGS.owner_ok RSEGS AD L HI (PGV8.src_of_vw V x g).
Proof using VOK SPLO HIok KL. intros Hs (_ & SLO & _ & STOP & _). apply (PGVK.src_of_vw_ok RSEGS AD L HI KL HIok V x g VOK); [unfold hl_ceil; lia| lia]. Qed.

(* [comment removed for export] *)
Lemma call_srcread (fx : FPState) R M model src x g sm cr (p k X : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 64) -> kept7 R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 p -> getr R (reg 12) = Z_to_bv 64 k ->
  1 <= k <= PM.CHUNK -> vdst x p k -> state_ok M model src x g sm cr ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (src' : PM.srcst) (sm' : PM.strm) (d : Z),
     regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 d -> 0 <= d <= k ->
     PMSP.consumed src src' sm sm' = d -> (1 <= PM.sr_rem src -> 1 <= d) ->
     (d = 0 -> PM.sr_rem src' = 0 /\ PM.sm_st sm' = 2) -> PMSP.src_step src src' sm sm' ->
     state_ok M' model src' x g sm' cr ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x370d0 M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 A12 Hk DST SO NEXT.
  pose proof SO as (MR & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay as LAY.
  assert (BR : PMFR.brange L (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  assert (DSTB : 0 <= p /\ p + k <= 2 ^ 64 /\ forall a, p <= a < p + k -> PMK.inW W0 a \/ exists B m, In (B, m) (PM.src_own src ++ PGV8.v8_own x) /\ B <= a < B + m).
  { destruct DST as (b & n & c & E & D1 & D2).
    assert (IN : In (b, c) (PM.src_own src ++ PGV8.v8_own x)) by (rewrite E; apply in_or_app; right; left; reflexivity).
    destruct (BR b c ltac:(rewrite own2; apply in_or_app; left; exact IN)) as (Q0 & _ & Q4).
    split; [lia|]. split; [destruct STOP; lia|]. intros a Ha. right. exists b, c. split; [exact IN| lia]. }
  destruct DSTB as (Dp0 & Dp1 & DIN).
  assert (STKr : L5C.stk (hl_sptop L) M (S - 64) (PMSP.pm_scr 4)).
  { apply (PMK.stk_call L M S 22528 (S - 64) (PMSP.pm_scr 4) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|].
    replace (S - 64) with (S + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  pose proof SRD as SR. unfold PGS.src_read_specG, PGS.src_specG in SR. cbn [pa_src_read AD PnLayoutS_u.ADDR_S] in SR.
  apply (SR (PGV8.src_of_vw V x g) (svw_ok M x g 22528 ltac:(lia) STK) fx R M model K (PGV8.v8_own x ++ OB) LBX cr (S - 64) X src str sm [(p, k)]);
    cbn [PGS.ow_at PGS.ow_os PGS.ow_ois PGS.ow_lo PGS.ow_hi PGS.ow_win PGV8.src_of_vw].
  { rewrite <- app_assoc. exact HH. }
  { exact MOK. }
  { exact K0. }
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
    split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0| exact STKr]. }
  { lia. }
  { rewrite L5K.rl10. exact A10. }
  { unfold PGS.read_args. exists p, k. rewrite L5K.rl11, L5K.rl12. split; [exact A11|]. split; [exact A12|]. split; [exact Hk|].
    unfold PGS.dst_okG. right. cbn [PGS.ow_win PGV8.src_of_vw]. split; [lia| exact DST]. }
  { unfold PMPS.read_W. exists p, k. rewrite L5K.rl11, L5K.rl12. split; [exact A11|]. split; [exact A12|]. split; [lia|]. split; [unfold PM.CHUNK in Hk; lia| reflexivity]. }
  { exists OB. split; [reflexivity| exact PA]. }
  { exact IA. }
  { exact BASE. }
  { exact INCS. }
  intros fx' R' M' src' sm' RP (OB1 & EOB & PA') IA' STEP RES HP HH'.
  apply app_inv_head in EOB. subst OB1.
  change (PMSP.pm_scr 4) with 20480 in HP.
  unfold PMPS.read_res in RES. destruct RES as (p' & k' & d & Y11 & Y12 & Hp' & Hk' & Y10 & Hd & CONS & _ & POS & ZERO).
  assert (pk : p' = p /\ k' = k).
  { change (getr R (reg 11) = Z_to_bv 64 p') in Y11. change (getr R (reg 12) = Z_to_bv 64 k') in Y12.
    rewrite A11 in Y11. rewrite A12 in Y12. apply (f_equal bv_unsigned) in Y11, Y12.
    unfold PM.CHUNK in Hk, Hk'. rewrite !L5.unsigned_lit in Y11, Y12 by lia. split; congruence. }
  destruct pk as (-> & ->).
  assert (QC : PM.sr_qc src' = PM.sr_qc src) by (destruct STEP as (E & _); exact E).
  apply (NEXT fx' R' M' src' sm' d RP Y10 Hd CONS POS ZERO STEP).
  rewrite <- app_assoc in HP, HH'.
  destruct (src_callee_mem M M' src x cr _ 20480 (PGS.W_srcG os ois src ++ [(p, k)]) MR SV HH ltac:(lia) HP) as (MR' & SV' & EKn).
  { intros a (r0 & Hin & Hr). apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]].
    - destruct (W_src_in src a (ex_intro _ r0 (conj Hin Hr))) as [I|I]; [left; exact I| right].
      exists (PM.sr_qc src), PM.CHUNK. split; [unfold PM.src_own; left; reflexivity| exact I].
    - apply DIN. exact Hr. }
  split; [exact MR'|]. split; [exact SV'|]. split; [exact PA'|]. split; [exact IA'|].
  split; [exact (base_keep M M' EKn STK BASE)|]. split; [exact TBOK|].
  split; [unfold PM.src_own; rewrite QC; unfold PM.src_own in HH'; exact HH'|].
  split; [exact MOK|]. split; [exact MB|]. split; [exact CRL| exact CRK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma call_fillv (fx : FPState) R M model src x g sm cr (p X b0 n0 c0 : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 64) -> kept7 R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 p -> getr R (reg 12) = Z_to_bv 64 PM.CHUNK ->
  x = PGV8.V8Blk b0 n0 c0 -> b0 <= p -> p + PM.CHUNK <= b0 + c0 -> state_ok M model src x g sm cr ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (sm' : PM.strm) (c : Z),
     regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 c -> 0 <= c <= PM.CHUNK -> PM.sm_g sm' = PM.sm_g sm + c ->
     (PM.sm_st sm = 0 -> c = Z.min PM.CHUNK (PM.sm_eg sm - PM.sm_g sm) /\ PM.sm_st sm' = (if Z.ltb c PM.CHUNK then 2 else 0)) ->
     PMSP.src_step src src sm sm' ->
     state_ok M' model src x g sm' cr ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x382d4 M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 A12 ETB D1 D2 SO NEXT.
  pose proof SO as (MR & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay as LAY.
  assert (BR : PMFR.brange L (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  assert (IN : In (b0, c0) (PM.src_own src ++ PGV8.v8_own x)) by (rewrite ETB; apply in_or_app; right; left; reflexivity).
  destruct (BR b0 c0 ltac:(rewrite own2; apply in_or_app; left; exact IN)) as (Q0 & _ & Q4).
  assert (STKr : L5C.stk (hl_sptop L) M (S - 64) (PMSP.pm_scr 3)).
  { apply (PMK.stk_call L M S 22528 (S - 64) (PMSP.pm_scr 3) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|].
    replace (S - 64) with (S + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  pose proof FBT as SR. unfold PGS.fill_buffer_tb_specG, PGS.src_specG in SR. cbn [pa_fill_buffer AD PnLayoutS_u.ADDR_S] in SR.
  apply (SR (PGV8.src_of_vw V x g) (svw_ok M x g 22528 ltac:(lia) STK) fx R M model K (PGV8.v8_own x ++ OB) LBX cr (S - 64) X src str sm [(p, PM.CHUNK)]);
    cbn [PGS.ow_at PGS.ow_os PGS.ow_ois PGS.ow_lo PGS.ow_hi PGS.ow_win PGV8.src_of_vw].
  { rewrite <- app_assoc. exact HH. }
  { exact MOK. }
  { exact K0. }
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
    split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0| exact STKr]. }
  { lia. }
  { rewrite L5K.rl10. exact A10. }
  { unfold PGS.tbfill_args. exists p. rewrite L5K.rl11, L5K.rl12. split; [exact A11|]. split; [exact A12|].
    cbn [PGS.ow_win PGV8.src_of_vw]. split; [unfold PM.CHUNK; lia|]. exists b0, n0, c0. split; [exact ETB| lia]. }
  { unfold PMTXS.tbfill_W. exists p. rewrite L5K.rl11. split; [exact A11|]. split; [destruct STOP; unfold PM.CHUNK in *; lia| reflexivity]. }
  { exists OB. split; [reflexivity| exact PA]. }
  { exact IA. }
  { exact BASE. }
  { exact INCS. }
  intros fx' R' M' src' sm' RP (OB1 & EOB & PA') IA' STEP RES HP HH'.
  apply app_inv_head in EOB. subst OB1.
  change (PMSP.pm_scr 3) with 18432 in HP.
  destruct RES as ((-> & c & Y10 & Hc & G & ST0 & ST2) & _).
  apply (NEXT fx' R' M' sm' c RP Y10 Hc G ST0 STEP).
  rewrite <- app_assoc in HP, HH'.
  destruct (src_callee_mem M M' src x cr _ 18432 (PGS.W_srcG os ois src ++ [(p, PM.CHUNK)]) MR SV HH ltac:(lia) HP) as (MR' & SV' & EKn).
  { intros a (r0 & Hin & Hr). apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]].
    - destruct (W_src_in src a (ex_intro _ r0 (conj Hin Hr))) as [I|I]; [left; exact I| right].
      exists (PM.sr_qc src), PM.CHUNK. split; [unfold PM.src_own; left; reflexivity| exact I].
    - right. exists b0, c0. split; [exact IN|]. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  split; [exact MR'|]. split; [exact SV'|]. split; [exact PA'|]. split; [exact IA'|].
  split; [exact (base_keep M M' EKn STK BASE)|]. split; [exact TBOK|].
  split; [exact HH'|].
  split; [exact MOK|]. split; [exact MB|]. split; [exact CRL| exact CRK].
Qed.

(* [comment removed for export] *)
Lemma unread_nn M model src x g sm cr : state_ok M model src x g sm cr ->
  0 <= PM.unread src sm /\ (PM.sm_st sm = 0 \/ PM.sm_st sm = 2) /\ 0 <= PM.sr_rem src <= PM.CHUNK /\ PM.sm_g sm <= PM.sm_eg sm.
Proof using All.
  intros (_ & _ & PA & IA & _).
  destruct (tsrc M src x g PA) as ((_ & _ & _ & _ & _ & _ & _ & Q8 & Q9 & Q10 & _) & _).
  destruct IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & ST) & _ & G1 & G2).
  unfold PM.unread. split; [lia|]. split; [exact ST|]. split; [unfold PM.CHUNK in *; lia| exact G2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lstate (R : bvmap 5 word) (M : word -> option byte) (model : Model) (src : PM.srcst) (x : PGV8.v8) (g : Z) (sm : PM.strm) (cr : credit) (w : Z) : Prop :=
  lregs R w /\ state_ok M model src x g sm cr /\ acct src x sm w /\ 1 <= w <= len.
Definition IHt (mu0 : Z) : Prop :=
  forall (fx : FPState) R M model src x g sm cr w, PM.mu_src src sm < mu0 -> lstate R M model src x g sm cr w ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x395a4 M model) K.
End Call.
End WithHeap.
End PNSSV1.
