(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmFrame PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnParSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParKit
     PmTxtSpecs PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSSrdP_u Bs0_code_r37944_37948_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgSrcKit.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSSR1.
Import PMS.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.

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
Lemma perm_tb (src : PM.srcst) (tb : PM.vstr) (OB LB : list (Z * Z)) cr M VM :
  hi_heap HI (PM.src_own src ++ PM.vs_own tb ++ OB ++ LB) cr M VM ->
  hi_heap HI (PM.vs_own tb ++ (PM.src_own src ++ OB ++ LB)) cr M VM.
Proof.
  intros HH. apply (hio_perm L SCFG HI HIok _ _ cr M VM HH).
  - intros b. rewrite !in_app_iff. tauto.
  - apply (nodup_perm (PM.src_own src ++ PM.vs_own tb ++ OB ++ LB)); [|exact (PMPK.heap_nodup L HI HIok _ _ _ _ HH)].
    rewrite (app_assoc (PM.src_own src) (PM.vs_own tb)). rewrite (app_assoc (PM.vs_own tb) (PM.src_own src)).
    apply Permutation.Permutation_app_tail. apply Permutation.Permutation_app_comm.
Qed.
Lemma perm_tb_back (src : PM.srcst) (tb : PM.vstr) (OB LB : list (Z * Z)) cr M VM :
  hi_heap HI (PM.vs_own tb ++ (PM.src_own src ++ OB ++ LB)) cr M VM ->
  hi_heap HI (PM.src_own src ++ PM.vs_own tb ++ OB ++ LB) cr M VM.
Proof.
  intros HH. apply (hio_perm L SCFG HI HIok _ _ cr M VM HH).
  - intros b. rewrite !in_app_iff. tauto.
  - apply (nodup_perm (PM.vs_own tb ++ (PM.src_own src ++ OB ++ LB))); [|exact (PMPK.heap_nodup L HI HIok _ _ _ _ HH)].
    rewrite (app_assoc (PM.src_own src) (PM.vs_own tb)). rewrite (app_assoc (PM.vs_own tb) (PM.src_own src)).
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
Lemma in123 {X} (l1 l2 l3 l4 : list X) x : In x (l1 ++ l2 ++ l3) -> In x (l1 ++ l2 ++ l3 ++ l4).
Proof. rewrite !in_app_iff. tauto. Qed.
Lemma in3 {X} (l1 l2 l3 l4 : list X) x : In x l3 -> In x (l1 ++ l2 ++ l3 ++ l4).
Proof. rewrite !in_app_iff. tauto. Qed.
Lemma in4 {X} (l1 l2 l3 l4 : list X) x : In x l4 -> In x (l1 ++ l2 ++ l3 ++ l4).
Proof. rewrite !in_app_iff. tauto. Qed.
Lemma own2 (src : PM.srcst) (tb : PM.vstr) (OB LB : list (Z * Z)) : PM.src_own src ++ PM.vs_own tb ++ OB ++ LB = (PM.src_own src ++ PM.vs_own tb) ++ (OB ++ LB).
Proof. rewrite <- !app_assoc. reflexivity. Qed.

Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (cr0 : credit).
Variables (S r len : Z) (T : PGS.towner) (OB : list (Z * Z)) (src0 : PM.srcst) (tb0 : PM.vstr) (tg0 : Z) (str : PM.vstr) (sm0 : PM.strm).
#[local] Abbreviation os := (PGS.tw_os T).
#[local] Abbreviation ois := (PGS.tw_ois T).
#[local] Abbreviation otb := (PGS.tw_otb T).
#[local] Abbreviation lo := (PGS.tw_lo T).
#[local] Abbreviation hi := (PGS.tw_hi T).
Hypothesis TOK : PGS.towner_ok RSEGS AD L HI T.
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis K0 : K [].
Hypothesis SPLO : S <= lo.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UNS0 : PM.vs_size tb0 + PM.unread src0 sm0 < 2 ^ 26.
Hypothesis RSZ : PMS.str_resize_spec L HI.
Hypothesis SRD : PGS.src_read_specG RSEGS AD L HI.
Hypothesis FBT : PGS.fill_buffer_tb_specG RSEGS AD L HI.
(* [comment removed for export] *)
Definition W0 : list L5.range := PGS.W_srcfG os ois ++ [(otb, 24)].
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (tb' : PM.vstr) (tg' : Z)
                         (sm' : PM.strm) (cr' : credit) (d : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
  PMSP.consumed src0 src' sm0 sm' = d -> PM.vs_size tb' = PM.vs_size tb0 + d ->
  PGS.tw_at T M' src' tb' tg' OB -> PM.iss_at RSEGS AD T3 M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5C.hpres L LBX S (PMSP.pm_scr 5) W0 M0 M' ->
  PMSP.credit_keep cr0 cr' (PM.pot_text L tb0 tg0) (PM.pot_text L tb' tg') ->
  model_but_vm model0 model' -> hi_heap HI (PM.src_own src' ++ PM.vs_own tb' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition saves9 (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22)))
  /\ L5.u64_at RSEGS M (S - 72) (bv_unsigned (getr R0 (reg 23))).
Definition kept6 (R : bvmap 5 word) : Prop := forall x, In x [3; 4; 24; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
(* [comment removed for export] *)
Definition memrel (M : word -> option byte) : Prop :=
  PMK.ek L (OB ++ LBX) S 22528 W0 M0 M /\ PMK.dk L (OB ++ LBX) S 22528 M0 M /\ L5C.stk (hl_sptop L) M S 22528.
(* [comment removed for export] *)
Definition acct (src : PM.srcst) (tb : PM.vstr) (sm : PM.strm) (w : Z) : Prop :=
  PMSP.consumed src0 src sm0 sm = len - w /\ PM.vs_size tb = PM.vs_size tb0 + (len - w) /\ PMSP.src_step src0 src sm0 sm.
(* [comment removed for export] *)
Definition state_ok (M : word -> option byte) (model : Model) (src : PM.srcst) (tb : PM.vstr) (tg : Z) (sm : PM.strm) (cr : credit) : Prop :=
  memrel M /\ saves9 M /\ PGS.tw_at T M src tb tg OB /\ PM.iss_at RSEGS AD T3 M ois str sm
  /\ PMST.base_ok RSEGS AD M /\ PM.tb_ok tb tg
  /\ hi_heap HI (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) cr M (m_vmmaps model) /\ PMSP.model_ok model /\ model_but_vm model0 model
  /\ PMSP.credit_le (PM.pot_text L tb tg) cr
  /\ PMSP.credit_keep cr0 cr (PM.pot_text L tb0 tg0) (PM.pot_text L tb tg).
(* [comment removed for export] *)
Definition lregs (R : bvmap 5 word) (w : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 80) /\ getr R (reg 8) = Z_to_bv 64 len /\ getr R (reg 9) = Z_to_bv 64 otb
  /\ getr R (reg 18) = Z_to_bv 64 os /\ getr R (reg 21) = Z_to_bv 64 w /\ getr R (reg 22) = Z_to_bv 64 (otb + 1) /\ kept6 R.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lay : lo <= os /\ os + 296 <= hi /\ lo <= ois /\ ois + 272 <= hi /\ lo <= otb /\ otb + 24 <= hi /\ hi <= hl_sptop L /\ hi <= 2 ^ 47
            /\ os mod 8 = 0 /\ ois mod 8 = 0 /\ otb mod 8 = 0 /\ 4096 <= lo
            /\ (os + 296 <= ois \/ ois + 272 <= os) /\ (otb + 24 <= os \/ os + 296 <= otb) /\ (otb + 24 <= ois \/ ois + 272 <= otb).
Proof using TOK. exact (PGS.to_lay _ _ _ _ _ TOK). Qed.
Lemma lay0 : lo <= os /\ os + 296 <= hi /\ lo <= ois /\ ois + 272 <= hi /\ lo <= otb /\ otb + 24 <= hi /\ hi <= hl_sptop L /\ hi <= 2 ^ 47
            /\ os mod 8 = 0 /\ ois mod 8 = 0 /\ otb mod 8 = 0 /\ 4096 <= lo.
Proof using TOK. destruct lay as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & _). repeat split; assumption. Qed.
Lemma tsrc M src tb tg : PGS.tw_at T M src tb tg OB ->
  PM.src_fields_at RSEGS T3 M os ois (ois + 16) src /\ PM.nullis_at RSEGS AD T3 M (os + 8) /\ L5.defined M os 296 /\ PM.vstr_at RSEGS T3 M otb tb /\ PM.tb_ok tb tg.
Proof using TOK. exact (PGS.to_src _ _ _ _ _ TOK M src tb tg OB). Qed.
Lemma inW_W0 a : PMK.inW W0 a -> (os + 240 <= a < os + 296) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (otb <= a < otb + 24).
Proof.
  intros (r0 & Hin & Hr). unfold W0, PGS.W_srcfG in Hin. cbn [app] in Hin. unfold L5.in_rng in Hr.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma inW_W0' a : PMK.inW W0 a -> lo <= a < hi.
Proof using TOK. intros I. apply inW_W0 in I. pose proof lay. lia. Qed.
Lemma outside_W0 a : a < S -> L5.outside W0 a.
Proof using TOK SPLO. intros Ha r0 Hr0 Hin. assert (I : PMK.inW W0 a) by (exists r0; split; assumption). apply inW_W0' in I. lia. Qed.
Lemma W_src_in (src : PM.srcst) a : PMK.inW (PGS.W_srcG os ois src) a -> PMK.inW W0 a \/ (PM.sr_qc src <= a < PM.sr_qc src + PM.CHUNK).
Proof.
  intros (r0 & Hin & Hr). unfold PGS.W_srcG in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]].
  - left. exists r0. split; [unfold W0; apply in_or_app; left; exact Hin| exact Hr].
  - right. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma tw_xfer M M' src src' tb tb' tg tg' cr VM scr0 sp' scr' (Wx : list L5.range) :
  PGS.tw_at T M src tb tg OB -> hi_heap HI (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) cr M VM -> L5C.stk (hl_sptop L) M S scr0 ->
  0 <= scr0 -> S - scr0 <= sp' - scr' -> sp' <= S ->
  L5C.hpres L (OB ++ LBX) sp' scr' (PGS.W_srcfG os ois ++ [(otb, 24)] ++ Wx) M M' ->
  Forall (fun r => S - scr0 <= fst r /\ fst r + snd r <= S) Wx ->
  PM.src_fields_at RSEGS T3 M' os ois (ois + 16) src' -> PM.sr_qc src' = PM.sr_qc src -> PM.vstr_at RSEGS T3 M' otb tb' -> PM.tb_ok tb' tg' ->
  PGS.tw_at T M' src' tb' tg' OB.
Proof using TOK SPLO HIok.
  intros AT HH STK H0 H1 H2 HP FW SFq QC VS TB. pose proof STK as (_ & SLO & _ & STOP & _).
  pose proof (own_apart (PM.src_own src ++ PM.vs_own tb) (OB ++ LBX) cr M VM ltac:(rewrite <- own2; exact HH)) as OWNF.
  assert (BR : PMFR.brange L (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  apply (PGS.to_upd _ _ _ _ _ TOK LBX sp' scr' Wx M M' src src' tb tb' tg tg' OB cr VM ltac:(lia) AT HH).
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
Proof using TOK SPLO KL SF LY.
  intros E (_ & SLO & _ & STOP & _) B. apply (PMKP.base_ok_keep RSEGS AD L KL SF (OB ++ LBX) S 22528 W0 M M' E); [| | | |exact B].
  all: intros a Ha; apply outside_W0; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S] in Ha; destruct STOP; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma finish (fx : FPState) R M model src tb tg sm cr (w : Z) :
  getr R (reg 1) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 1))) -> getr R (reg 2) = Z_to_bv 64 S ->
  getr R (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> getr R (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) ->
  getr R (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) -> getr R (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) ->
  getr R (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22))) -> getr R (reg 23) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 23))) -> kept6 R ->
  getr R (reg 10) = Z_to_bv 64 (len - w) -> 0 <= w <= len ->
  state_ok M model src tb tg sm cr -> acct src tb sm w ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39520 M model) K.
Proof using All.
  intros E1 E2 E8 E9 E18 E19 E20 E21 E22 E23 KP E10 Hw
         ((EK & DK & STK) & _ & PA & IA & BASE & TBOK & HH & MOK & MB & _ & CK) (CONS & SZ & STEP).
  pose proof MOK as (Mh & Ml & Mm). pose proof RAok as (Hr1 & Hr2).
  assert (RA : getr R (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra0).
  unfold PMSP.cfg.
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx R M 0x39520 W_38338 r F_38338 ltac:(reflexivity) D_38338 RA Hr1 Hr2)|].
  apply (KONT fx R M model src tb tg sm cr (len - w)); try assumption; try lia.
  - apply PMK.preserved_by_index. intros x Hx. unfold PMK.cs_all in Hx. cbn in Hx.
    destruct Hx as [<-|Hx]; [rewrite E2, Rsp0; reflexivity|].
    destruct Hx as [<-|Hx]; [apply KP; cbn; auto|]. destruct Hx as [<-|Hx]; [apply KP; cbn; auto|].
    destruct Hx as [<-|Hx]; [rewrite E8; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite E18; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E19; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite E20; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E21; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite E22; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E23; apply Z_to_bv_bv_unsigned|].
    apply KP. destruct Hx as [<-|[<-|[<-|[<-|[]]]]]; cbn; auto 10.
  - apply (PMK.hpres_of L LBX S 22528 W0 M0 M).
    + apply (PMK.ek_weaken L LBX (OB ++ LBX) S 22528 S 22528 W0 W0 M0 M EK); [intros x Hx; apply in_or_app; right; exact Hx| intros x Hx; exact Hx| intros a Ha; exact Ha].
    + destruct STK as (_ & _ & _ & _ & D); exact D.
    + apply (PMPK.dk_incl L LBX (OB ++ LBX) S 22528 M0 M DK). intros x Hx; apply in_or_app; right; exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma src_callee_mem M M' src tb cr VM scr' (W' : list L5.range) :
  memrel M -> saves9 M -> hi_heap HI (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) cr M VM -> 0 <= scr' <= 22528 - 80 ->
  L5C.hpres L (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) (S - 80) scr' W' M M' ->
  (forall a, PMK.inW W' a -> PMK.inW W0 a \/ exists B m, In (B, m) (PM.src_own src ++ PM.vs_own tb) /\ B <= a < B + m) ->
  memrel M' /\ saves9 M' /\ PMK.ek L (OB ++ LBX) S 22528 W0 M M'.
Proof using TOK SPLO HIok KL.
  intros (EK & DK & STK) SV HH Hs HP FP.
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  set (LBc := PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) in *.
  assert (BR : PMFR.brange L LBc) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  pose proof (own_apart (PM.src_own src ++ PM.vs_own tb) (OB ++ LBX) cr M VM ltac:(unfold LBc in HH; rewrite <- own2; exact HH)) as OWNF.
  assert (OWNLO : forall a B m, In (B, m) (PM.src_own src ++ PM.vs_own tb) -> B <= a < B + m -> a < S - 22528).
  { intros a B m Hin Ha. destruct (OWNF B m Hin) as (Q & _). lia. }
  assert (EKr : PMK.ek L LBc (S - 80) scr' W' M M') by (apply (PMK.ek_of_hpres L); exact HP).
  assert (STKr : L5C.stk (hl_sptop L) M (S - 80) scr').
  { apply (PMK.stk_call L M S 22528 (S - 80) scr' STK); [lia|lia|lia|]. replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  assert (SC0 : 0 <= scr') by lia.
  assert (INC : incl (OB ++ LBX) LBc) by (intros x Hx; unfold LBc; rewrite own2; apply in_or_app; right; exact Hx).
  assert (EKn : PMK.ek L (OB ++ LBX) S 22528 W0 M M').
  { apply (PMPK.ek_drop_own L (PM.src_own src ++ PM.vs_own tb) (OB ++ LBX) S 22528 W0 (W0 ++ (PM.src_own src ++ PM.vs_own tb)) M M').
    - rewrite <- own2. apply (PMK.ek_callee_in' RSEGS L KL LBc LBc S 22528 (S - 80) scr' (W0 ++ (PM.src_own src ++ PM.vs_own tb)) W' M M' HP (incl_refl _));
        [lia|lia|lia| destruct STOP; lia| exact (PMFR.brange_hi L LBc BR)|].
      intros a I. right. destruct (FP a I) as [(r0 & Hr0 & Hin)|(B & m & Hin & Ha)].
      + exists r0. split; [apply in_or_app; left; exact Hr0| exact Hin].
      + exists (B, m). split; [apply in_or_app; right; exact Hin| unfold L5.in_rng; cbn [fst snd]; lia].
    - exact OWNF.
    - intros a O. apply outside_own. exact O. }
  assert (NOTW : forall a n, S - 80 <= a -> a + n <= S -> forall i, a <= i < a + n -> ~ PMK.inW W' i).
  { intros a n H1 H2 i Hi I. destruct (FP i I) as [I'|(B & m & Hin & Ha)]; [apply inW_W0' in I'; lia| apply (OWNLO i B m Hin) in Ha; lia]. }
  split; [split; [|split]|].
  - exact (PMK.ek_trans L (OB ++ LBX) S 22528 W0 M0 M M' EK EKn).
  - apply (PMK.dk_trans L (OB ++ LBX) S 22528 M0 M M' DK).
    apply (PMK.dk_callee L (OB ++ LBX) LBc S 22528 (S - 80) scr' W' M M' HP INC); [lia| lia].
  - apply (PMK.stk_after RSEGS L KL LBc M M' S 22528 (S - 80) scr' W' STK HP); lia.
  - split; [|exact EKn].
    destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72).
    unfold saves9. repeat split; (apply (PMFR.u64_keep RSEGS L KL LBc (S - 80) scr' W' M M' EKr STKr SC0); [lia|lia| apply NOTW; lia| eassumption]).
Qed.

(* [comment removed for export] *)
Lemma iss_xfer M M' (LBc : list (Z * Z)) scr' (W' : list L5.range) sm :
  incl LBX LBc -> PMFR.brange L LBc -> L5C.stk (hl_sptop L) M S 22528 -> 0 <= scr' <= 22528 - 80 ->
  L5C.hpres L LBc (S - 80) scr' W' M M' ->
  (forall i, ois <= i < ois + 272 -> ~ PMK.inW W' i) -> (forall a, PMK.inW W' a -> S - 80 <= a \/ hl_img_lo L <= a < hl_img_hi L) ->
  PM.iss_at RSEGS AD T3 M ois str sm -> PM.iss_at RSEGS AD T3 M' ois str sm.
Proof using TOK SPLO HIok KL INCS.
  intros INC BR STK Hs HP NI WHI IA. pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay as LAY.
  assert (EKr : PMK.ek L LBc (S - 80) scr' W' M M') by (apply (PMK.ek_of_hpres L); exact HP).
  assert (STKr : L5C.stk (hl_sptop L) M (S - 80) scr').
  { apply (PMK.stk_call L M S 22528 (S - 80) scr' STK); [lia|lia|lia|]. replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  assert (SC0 : 0 <= scr') by lia.
  apply (PMF.iss_at_agree RSEGS AD M M' ois str sm); [lia|lia| | |exact IA].
  - apply (PMFR.ag_hi RSEGS L KL LBc (S - 80) scr' W' M M' EKr STKr SC0); [lia|lia| exact NI].
  - intros c n p E. apply (PMFR.ag_block RSEGS L KL LBc (S - 80) scr' W' M M' EKr STKr SC0 BR WHI).
    apply INC. apply INCS. rewrite E. left. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma call_resize (fx : FPState) R M model src tb tg sm cr (nn X : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 80) -> kept6 R ->
  getr R (reg 10) = Z_to_bv 64 otb -> getr R (reg 11) = Z_to_bv 64 nn ->
  0 <= nn <= PM.vs_size tb + PM.CHUNK -> nn < 2 ^ 26 + PM.CHUNK ->
  state_ok M model src tb tg sm cr ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (tb' : PM.vstr) (tg' : Z) (cr' : credit),
     regs_preserved R R' -> PM.vs_size tb' = nn -> (nn <= PM.vs_cap tb -> PM.vs_own tb' = PM.vs_own tb /\ tg' = tg) ->
     state_ok M' model' src tb' tg' sm cr' ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x59000 M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 Hn1 Hn2 ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK) NEXT.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay as LAY.
  set (LB' := PM.src_own src ++ OB ++ LBX).
  pose proof (perm_tb src tb OB LBX cr M _ HH) as HH'. fold LB' in HH'.
  pose proof (tsrc M src tb tg PA) as (PSF & PNI & PD & VS & _).
  assert (STKr : L5C.stk (hl_sptop L) M (S - 80) (PMSP.pm_scr 1)).
  { apply (PMK.stk_call L M S 22528 (S - 80) (PMSP.pm_scr 1) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|].
    replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  unfold PMS.str_resize_spec, PMSP.str_resize_spec in RSZ. cbn [pa_str_resize AD] in RSZ.
  apply (RSZ fx R M model K LB' cr otb nn (S - 80) X tg tb HH' MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
    split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0| exact STKr]. }
  { rewrite L5K.rl10. exact A10. }
  { rewrite L5K.rl11. exact A11. }
  { lia. }
  { lia. }
  { lia. }
  { exact VS. }
  { exact TBOK. }
  { exact Hn1. }
  { exact Hn2. }
  { exact CRL. }
  intros fx' R' M' model' tb' tg' cr' RP VS' SZ TB' OWN HP CK MB' HH2.
  apply (NEXT fx' R' M' model' tb' tg' cr' RP SZ OWN).
  assert (BR' : PMFR.brange L LB') by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M' _ HH2); intros x Hx; apply in_or_app; right; exact Hx).
  assert (EKr : PMK.ek L LB' (S - 80) (PMSP.pm_scr 1) [(otb, 24)] M M') by (apply (PMK.ek_of_hpres L); exact HP).
  assert (SC1 : 0 <= PMSP.pm_scr 1) by (unfold PMSP.pm_scr; lia).
  assert (WHI : forall a, PMK.inW [(otb, 24)] a -> S - 80 <= a \/ hl_img_lo L <= a < hl_img_hi L).
  { intros a I. left. apply PMFR.inW_inv1 in I. lia. }
  assert (NOTW : forall a n, a + n <= otb \/ otb + 24 <= a -> forall i, a <= i < a + n -> ~ PMK.inW [(otb, 24)] i).
  { intros a n XO i Hi I. apply PMFR.inW_inv1 in I. lia. }
  assert (INL : incl (OB ++ LBX) LB') by (intros x Hx; unfold LB'; apply in_or_app; right; exact Hx).
  assert (HPw : L5C.hpres L (OB ++ LBX) (S - 80) (PMSP.pm_scr 1) (PGS.W_srcfG os ois ++ [(otb, 24)] ++ []) M M').
  { apply (PGSK.hpres_weaken L (OB ++ LBX) LB' (S - 80) (PMSP.pm_scr 1) _ [(otb, 24)] M M' HP INL).
    intros a O r0 [<-|[]]. apply O. apply in_or_app. right. left. reflexivity. }
  assert (HHn : hi_heap HI (PM.src_own src ++ PM.vs_own tb' ++ OB ++ LBX) cr' M' (m_vmmaps model')) by (apply perm_tb_back; exact HH2).
  split; [split; [|split]|].
  - apply (PMK.ek_trans L (OB ++ LBX) S 22528 W0 M0 M M' EK).
    apply (PMK.ek_callee_in' RSEGS L KL (OB ++ LBX) LB' S 22528 (S - 80) (PMSP.pm_scr 1) W0 [(otb, 24)] M M' HP INL);
      [unfold PMSP.pm_scr; lia| lia| lia| destruct STOP; lia| exact (PMFR.brange_hi L (OB ++ LBX) (PMFR.brange_incl L (OB ++ LBX) LB' BR' INL))|].
    intros a I. right. apply PMFR.inW_inv1 in I. exists (otb, 24). split; [unfold W0; apply in_or_app; right; left; reflexivity|].
    unfold L5.in_rng. cbn [fst snd]. lia.
  - apply (PMK.dk_trans L (OB ++ LBX) S 22528 M0 M M' DK).
    apply (PMK.dk_callee L (OB ++ LBX) LB' S 22528 (S - 80) (PMSP.pm_scr 1) [(otb, 24)] M M' HP INL); [unfold PMSP.pm_scr; lia| lia].
  - apply (PMK.stk_after RSEGS L KL LB' M M' S 22528 (S - 80) (PMSP.pm_scr 1) [(otb, 24)] STK HP); unfold PMSP.pm_scr; lia.
  - split.
    { destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72).
      unfold saves9. repeat split; (apply (PMFR.u64_keep RSEGS L KL LB' (S - 80) (PMSP.pm_scr 1) [(otb, 24)] M M' EKr STKr SC1);
                                    [lia|lia| apply NOTW; lia| eassumption]). }
    split.
    { apply (tw_xfer M M' src src tb tb' tg tg' cr (m_vmmaps model) 22528 (S - 80) (PMSP.pm_scr 1) [] PA HH STK ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) ltac:(lia) HPw ltac:(constructor)); [|reflexivity| exact VS'| exact TB'].
      apply (PMFR.src_keep RSEGS L KL LB' (S - 80) (PMSP.pm_scr 1) [(otb, 24)] M M' EKr STKr SC1 BR' WHI os ois (ois + 16) src); [lia|lia| intros i Hi; apply (NOTW (os + 240) 56); lia| unfold LB', PM.src_own; left; reflexivity| exact PSF]. }
    split.
    { apply (iss_xfer M M' LB' (PMSP.pm_scr 1) [(otb, 24)] sm ltac:(intros x Hx; apply INL; apply in_or_app; right; exact Hx) BR' STK ltac:(unfold PMSP.pm_scr; lia) HP); [intros i Hi; apply (NOTW ois 272); lia| exact WHI| exact IA]. }
    split.
    { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB' (S - 80) (PMSP.pm_scr 1) [(otb, 24)] M M' EKr);
        first [exact BASE | intros a Ha r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; cbn in Ha; lia]. }
    split; [exact TB'|].
    split; [exact HHn|].
    split; [exact (PMFR.model_ok_but_vm model model' MOK MB')|].
    split; [exact (L5C.model_but_vm_trans _ _ _ MB MB')|].
    split; [apply (PMPK.credit_le_keep cr cr' _ _ CRL CK)|].
    unfold PMSP.credit_keep in *. destruct CRK, CK. split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tbdst (tb : PM.vstr) (p k : Z) : Prop :=
  ((exists n, tb = PM.VShort n) /\ otb + 1 <= p /\ p + k <= otb + 24)
  \/ (exists c n q, tb = PM.VLong c n q /\ q <= p /\ p + k <= q + c).

(* [comment removed for export] *)
Lemma stw_ok M tb tg scr0 : 0 <= scr0 -> L5C.stk (hl_sptop L) M S scr0 -> PGS.owner_ok RSEGS AD L HI (PGS.src_of_tw T tb tg).
Proof using TOK SPLO HIok KL. intros Hs (_ & SLO & _ & STOP & _). apply (PGSK.src_of_tw_ok RSEGS AD L HI KL HIok T tb tg TOK); [unfold hl_ceil; lia| lia]. Qed.

(* [comment removed for export] *)
Lemma call_srcread (fx : FPState) R M model src tb tg sm cr (p k X : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 80) -> kept6 R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 p -> getr R (reg 12) = Z_to_bv 64 k ->
  1 <= k <= PM.CHUNK -> tbdst tb p k -> state_ok M model src tb tg sm cr ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (src' : PM.srcst) (sm' : PM.strm) (d : Z),
     regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 d -> 0 <= d <= k ->
     PMSP.consumed src src' sm sm' = d -> (1 <= PM.sr_rem src -> 1 <= d) ->
     (d = 0 -> PM.sr_rem src' = 0 /\ PM.sm_st sm' = 2) -> PMSP.src_step src src' sm sm' ->
     state_ok M' model src' tb tg sm' cr ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x370d0 M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 A12 Hk DST SO NEXT.
  pose proof SO as (MR & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay as LAY.
  assert (BR : PMFR.brange L (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  assert (DSTB : 0 <= p /\ p + k <= 2 ^ 64 /\ forall a, p <= a < p + k -> PMK.inW W0 a \/ exists B m, In (B, m) (PM.src_own src ++ PM.vs_own tb) /\ B <= a < B + m).
  { destruct DST as [(_ & D1 & D2)|(c & n & q & E & D1 & D2)].
    - split; [lia|]. split; [destruct STOP; lia|]. intros a Ha. left. exists (otb, 24).
      split; [unfold W0; apply in_or_app; right; left; reflexivity|]. unfold L5.in_rng; cbn [fst snd]. lia.
    - assert (IN : In (q, c) (PM.src_own src ++ PM.vs_own tb)) by (rewrite E; apply in_or_app; right; left; reflexivity).
      destruct (BR q c ltac:(rewrite own2; apply in_or_app; left; exact IN)) as (Q0 & _ & Q4).
      split; [lia|]. split; [destruct STOP; lia|]. intros a Ha. right. exists q, c. split; [exact IN| lia]. }
  destruct DSTB as (Dp0 & Dp1 & DIN).
  assert (STKr : L5C.stk (hl_sptop L) M (S - 80) (PMSP.pm_scr 4)).
  { apply (PMK.stk_call L M S 22528 (S - 80) (PMSP.pm_scr 4) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|].
    replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  pose proof SRD as SR. unfold PGS.src_read_specG, PGS.src_specG in SR. cbn [pa_src_read AD PnLayoutS_u.ADDR_S] in SR.
  apply (SR (PGS.src_of_tw T tb tg) (stw_ok M tb tg 22528 ltac:(lia) STK) fx R M model K (PM.vs_own tb ++ OB) LBX cr (S - 80) X src str sm [(p, k)]);
    cbn [PGS.ow_at PGS.ow_os PGS.ow_ois PGS.ow_lo PGS.ow_hi PGS.ow_win PGS.src_of_tw].
  { rewrite <- app_assoc. exact HH. }
  { exact MOK. }
  { exact K0. }
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
    split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0| exact STKr]. }
  { lia. }
  { rewrite L5K.rl10. exact A10. }
  { unfold PGS.read_args. exists p, k. rewrite L5K.rl11, L5K.rl12. split; [exact A11|]. split; [exact A12|]. split; [exact Hk|].
    unfold PGS.dst_okG. right. cbn [PGS.ow_win PGS.src_of_tw]. split; [lia| exact DST]. }
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
  destruct (src_callee_mem M M' src tb cr _ 20480 (PGS.W_srcG os ois src ++ [(p, k)]) MR SV HH ltac:(lia) HP) as (MR' & SV' & EKn).
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
Lemma call_filltb (fx : FPState) R M model src tb tg sm cr (p X c0 n0 q0 : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 80) -> kept6 R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 p -> getr R (reg 12) = Z_to_bv 64 PM.CHUNK ->
  tb = PM.VLong c0 n0 q0 -> q0 <= p -> p + PM.CHUNK <= q0 + c0 -> state_ok M model src tb tg sm cr ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (sm' : PM.strm) (c : Z),
     regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 c -> 0 <= c <= PM.CHUNK -> PM.sm_g sm' = PM.sm_g sm + c ->
     (PM.sm_st sm = 0 -> c = Z.min PM.CHUNK (PM.sm_eg sm - PM.sm_g sm) /\ PM.sm_st sm' = (if Z.ltb c PM.CHUNK then 2 else 0)) ->
     PMSP.src_step src src sm sm' ->
     state_ok M' model src tb tg sm' cr ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x382d4 M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 A12 ETB D1 D2 SO NEXT.
  pose proof SO as (MR & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay as LAY.
  assert (BR : PMFR.brange L (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  assert (IN : In (q0, c0) (PM.src_own src ++ PM.vs_own tb)) by (rewrite ETB; apply in_or_app; right; left; reflexivity).
  destruct (BR q0 c0 ltac:(rewrite own2; apply in_or_app; left; exact IN)) as (Q0 & _ & Q4).
  assert (STKr : L5C.stk (hl_sptop L) M (S - 80) (PMSP.pm_scr 3)).
  { apply (PMK.stk_call L M S 22528 (S - 80) (PMSP.pm_scr 3) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|].
    replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  pose proof FBT as SR. unfold PGS.fill_buffer_tb_specG, PGS.src_specG in SR. cbn [pa_fill_buffer AD PnLayoutS_u.ADDR_S] in SR.
  apply (SR (PGS.src_of_tw T tb tg) (stw_ok M tb tg 22528 ltac:(lia) STK) fx R M model K (PM.vs_own tb ++ OB) LBX cr (S - 80) X src str sm [(p, PM.CHUNK)]);
    cbn [PGS.ow_at PGS.ow_os PGS.ow_ois PGS.ow_lo PGS.ow_hi PGS.ow_win PGS.src_of_tw].
  { rewrite <- app_assoc. exact HH. }
  { exact MOK. }
  { exact K0. }
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
    split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0| exact STKr]. }
  { lia. }
  { rewrite L5K.rl10. exact A10. }
  { unfold PGS.tbfill_args. exists p. rewrite L5K.rl11, L5K.rl12. split; [exact A11|]. split; [exact A12|].
    cbn [PGS.ow_win PGS.src_of_tw]. split; [unfold PM.CHUNK; lia|]. right. exists c0, n0, q0. split; [exact ETB| lia]. }
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
  destruct (src_callee_mem M M' src tb cr _ 18432 (PGS.W_srcG os ois src ++ [(p, PM.CHUNK)]) MR SV HH ltac:(lia) HP) as (MR' & SV' & EKn).
  { intros a (r0 & Hin & Hr). apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]].
    - destruct (W_src_in src a (ex_intro _ r0 (conj Hin Hr))) as [I|I]; [left; exact I| right].
      exists (PM.sr_qc src), PM.CHUNK. split; [unfold PM.src_own; left; reflexivity| exact I].
    - right. exists q0, c0. split; [exact IN|]. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  split; [exact MR'|]. split; [exact SV'|]. split; [exact PA'|]. split; [exact IA'|].
  split; [exact (base_keep M M' EKn STK BASE)|]. split; [exact TBOK|].
  split; [exact HH'|].
  split; [exact MOK|]. split; [exact MB|]. split; [exact CRL| exact CRK].
Qed.

(* [comment removed for export] *)
Lemma unread_nn M model src tb tg sm cr : state_ok M model src tb tg sm cr ->
  0 <= PM.unread src sm /\ (PM.sm_st sm = 0 \/ PM.sm_st sm = 2) /\ 0 <= PM.sr_rem src <= PM.CHUNK /\ PM.sm_g sm <= PM.sm_eg sm.
Proof using All.
  intros (_ & _ & PA & IA & _).
  destruct (tsrc M src tb tg PA) as ((_ & _ & _ & _ & _ & _ & _ & Q8 & Q9 & Q10 & _) & _).
  destruct IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & ST) & _ & G1 & G2).
  unfold PM.unread. split; [lia|]. split; [exact ST|]. split; [unfold PM.CHUNK in *; lia| exact G2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lstate (R : bvmap 5 word) (M : word -> option byte) (model : Model) (src : PM.srcst) (tb : PM.vstr) (tg : Z) (sm : PM.strm) (cr : credit) (w : Z) : Prop :=
  lregs R w /\ state_ok M model src tb tg sm cr /\ acct src tb sm w /\ 1 <= w <= len.
Definition IHt (mu0 : Z) : Prop :=
  forall (fx : FPState) R M model src tb tg sm cr w, PM.mu_src src sm < mu0 -> lstate R M model src tb tg sm cr w ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x393d8 M model) K.

End Call.
End WithHeap.
End PGSSR1.
