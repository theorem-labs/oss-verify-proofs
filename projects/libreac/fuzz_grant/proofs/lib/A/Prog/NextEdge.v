(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEdge), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8c.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACgb.v. *)
(* The edge scan of reac_headamp_tx_next on the ASan build (fuzz_grant.asan 0x8514c, the
   slot lib/A/Prog/HeadampTxNext.v names LOOPD), one of the four segments that walk is cut
   into.  The scan runs over the 144 flattened cells of the table's dirty array at offset
   288: at each index it reads the dirty byte; at the first non-zero one it clears that
   byte, writes the channel i / 3, the parameter i mod 3 and the value tb T i into the
   three bytes the caller holds, clears resweep_wait at 456 and returns 1; if no cell is
   dirty the scan falls out at AFTR (0x85228).

   The compiler divides by 3 with the 171/512 reciprocal, so the cell's address is a tree,
   not an atom.  lib/A/Prog/NextArith.v holds those trees and their values; the two aliases
   (DEXPR, SOff 47 0) and (VEXPR, SOff 48 0) make the engine's data loads resolve, and the
   two shadow entries mkSHE 47 0 1 and mkSHE 48 0 1 make every instrumented access of the
   loop covered, so the memory-checking runtime's report entries (errpath_load1 0x58914,
   errpath_load4 0x58a54, errpath_store1 0x58c34 and errpath_store4 0x58d74) are not
   reached on any slot of this segment. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaRun PaShadow GrantSyms GrantList GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaJournal GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel NextModel NextLemmas SlotNeeds_c HeadampI1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import NextArith HeadampTxEffective HeadampTxNext.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* One byte of a one-byte write, read back. *)
Lemma le1_bytes : forall u, 0 <= u < 2 ^ 64 -> le1 (Z_to_bv 64 u) = [Z_to_bv 8 u].
Proof.
  intros u Hu. unfold le1. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite (Z.mod_small u) by (change (2 ^ Z.of_N 64) with 18446744073709551616; lia).
  reflexivity.
Qed.

Lemma tb_setb_in : forall T k v, length T = 460%nat -> 0 <= k < 460 -> 0 <= v < 256 ->
  tb (setb T k v) k = v.
Proof.
  intros T k v HL Hk Hv. unfold tb, setb. rewrite nth_as_error.
  rewrite upd_bytes_nth by (rewrite ?length_le1; lia).
  rewrite length_le1.
  replace (Nat.leb (Z.to_nat k) (Z.to_nat k) && Nat.ltb (Z.to_nat k) (Z.to_nat k + 1))%bool with true
    by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
  replace (Z.to_nat k - Z.to_nat k)%nat with 0%nat by lia.
  rewrite le1_bytes by lia. cbn [nth_error].
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  apply Z.mod_small. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* The state at the head of the edge scan.  Atom 45 is the caller's stack pointer (the
   scan runs on the frame the prologue took, so the machine's sp is that atom less 80),
   46 the index, 47 and 48 the two cell addresses, 49 and 50 the two cell bytes, and
   56..65 the ten registers the prologue saved, which the epilogue reads back. *)
Definition STKR : YP09.region := YP09.mkRegion (Some 45%nat) (-80) 0 (-80) (-80)
  [ YP09.mkChunk (-8) (CVal 8 (SOff 56 0)); YP09.mkChunk (-16) (CVal 8 (SOff 57 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 58 0)); YP09.mkChunk (-32) (CVal 8 (SOff 59 0));
    YP09.mkChunk (-40) (CVal 8 (SOff 60 0)); YP09.mkChunk (-48) (CVal 8 (SOff 61 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 62 0)); YP09.mkChunk (-64) (CVal 8 (SOff 63 0));
    YP09.mkChunk (-72) (CVal 8 (SOff 64 0)); YP09.mkChunk (-80) (CVal 8 (SOff 65 0)) ].
Definition DREGR : YP09.region := YP09.mkRegion (Some 47%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 49 0))].
Definition DREGW : YP09.region := YP09.mkRegion (Some 47%nat) 0 1 0 1 [].
Definition TXSW : YP09.region := YP09.mkRegion (Some 10%nat) 456 460 456 460 [].

Definition OUTB : afact := mkAF 4096 (2 ^ 47 - 1) 0.
Definition nd_atoms : list (nat * afact) :=
  [ (45%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, PTRN 4); (11%nat, OUTB); (12%nat, OUTB); (13%nat, OUTB);
    (32%nat, mkAF SB_NX SB_NX 0);
    (46%nat, mkAF 0 143 0); (47%nat, PTRN 0); (48%nat, PTRN 0);
    (49%nat, mkAF 0 255 0); (50%nat, mkAF 0 255 0) ].
Definition nd_alias : list (sv * sv) := [ (DEXPR, SOff 47 0); (VEXPR, SOff 48 0) ].
Definition nd_SH : list shent := nx_SH ++ [ mkSHE 47 0 1; mkSHE 48 0 1 ].

Definition sr_d : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    (2%bv : bv 5) (SOff 45 (-80)))
    (5%bv : bv 5) (SOff 32 0))
    (7%bv : bv 5) (SOff 46 0))
    (28%bv : bv 5) (SOff 10 288))
    (29%bv : bv 5) (SLit 171))
    (30%bv : bv 5) (SLit 144).
Definition nd_regs : list YP09.region := [ STKR; DREGR; VREG ].
Definition nd_regs_e : list YP09.region := [ OUTV; OUTP; OUTC; TXSW; DREGW; STKR; VREG ].
Definition ss_d : sstate := mkSS LOOPD sr_d nd_regs None (mkFacts nd_atoms [] nd_alias).

Definition nd_extra (regs : bvmap 5 word) (tx i : Z) (T : list byte) : list word :=
  map (Z_to_bv 64)
    [ SB_NX; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
      spZ regs; i; tx + 288 + i; tx + i; tb T (288 + i); tb T i;
      0; 0; 0; 0; 0 ]
  ++ [ getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19;
       getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24 ].

Definition ND (regsj regs : bvmap 5 word) (tx i : Z) (T : list byte) : env :=
  Eimg (Ereg regsj (nd_extra regs tx i T)).

Definition nd_env_ok (E : env) (regs : bvmap 5 word) (sp tx chp parp valp i : Z) (T : list byte) : Prop :=
  ew E 45 = w64 sp /\ ew E 10 = w64 tx /\ ew E 11 = w64 chp /\ ew E 12 = w64 parp /\
  ew E 13 = w64 valp /\ ew E 32 = w64 SB_NX /\ ew E 46 = w64 i /\
  ew E 47 = w64 (tx + 288 + i) /\ ew E 48 = w64 (tx + i) /\
  ew E 49 = w64 (tb T (288 + i)) /\ ew E 50 = w64 (tb T i) /\
  ew E 56 = getr regs 1 /\ ew E 57 = getr regs 8 /\ ew E 58 = getr regs 9 /\
  ew E 59 = getr regs 18 /\ ew E 60 = getr regs 19 /\ ew E 61 = getr regs 20 /\
  ew E 62 = getr regs 21 /\ ew E 63 = getr regs 22 /\ ew E 64 = getr regs 23 /\
  ew E 65 = getr regs 24 /\
  ew E 3 = getr regs 3 /\ ew E 4 = getr regs 4 /\ ew E 25 = getr regs 25 /\
  ew E 26 = getr regs 26 /\ ew E 27 = getr regs 27.

Lemma nd_env_lift : forall E E' regs sp tx chp parp valp i T,
  (forall n, (n < 70)%nat -> ew E' n = ew E n) ->
  nd_env_ok E regs sp tx chp parp valp i T -> nd_env_ok E' regs sp tx chp parp valp i T.
Proof.
  intros E E' regs sp tx chp parp valp i T HA
    (A45 & A10 & A11 & A12 & A13 & A32 & A46 & A47 & A48 & A49 & A50 &
     A56 & A57 & A58 & A59 & A60 & A61 & A62 & A63 & A64 & A65 & A3 & A4 & A25 & A26 & A27).
  unfold nd_env_ok. rewrite !HA by lia.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma nd_env : forall (regsj regs : bvmap 5 word) (tx chp parp valp i : Z) (T : list byte),
  (forall r : bv 5, In r [3; 4; 25; 26; 27]%bv -> getr regsj r = getr regs r) ->
  getr regsj 10 = w64 tx -> getr regsj 11 = w64 chp ->
  getr regsj 12 = w64 parp -> getr regsj 13 = w64 valp ->
  nd_env_ok (ND regsj regs tx i T) regs (spZ regs) tx chp parp valp i T.
Proof.
  intros regsj regs tx chp parp valp i T HK H10 H11 H12 H13.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew (ND regsj regs tx i T) n = ew (Ereg regsj (nd_extra regs tx i T)) n)
    by (intros n Hn; unfold ND; apply Eimg_low; exact Hn).
  unfold nd_env_ok.
  repeat match goal with |- _ /\ _ => split end;
    rewrite EL by (unfold A_TEXT; lia).
  - exact (ew_Ereg_extra regsj _ 13).
  - rewrite (ew_Ereg_nat regsj _ 10 10%bv eq_refl). exact H10.
  - rewrite (ew_Ereg_nat regsj _ 11 11%bv eq_refl). exact H11.
  - rewrite (ew_Ereg_nat regsj _ 12 12%bv eq_refl). exact H12.
  - rewrite (ew_Ereg_nat regsj _ 13 13%bv eq_refl). exact H13.
  - exact (ew_Ereg_extra regsj _ 0).
  - exact (ew_Ereg_extra regsj _ 14).
  - exact (ew_Ereg_extra regsj _ 15).
  - exact (ew_Ereg_extra regsj _ 16).
  - exact (ew_Ereg_extra regsj _ 17).
  - exact (ew_Ereg_extra regsj _ 18).
  - exact (ew_Ereg_extra regsj _ 24).
  - exact (ew_Ereg_extra regsj _ 25).
  - exact (ew_Ereg_extra regsj _ 26).
  - exact (ew_Ereg_extra regsj _ 27).
  - exact (ew_Ereg_extra regsj _ 28).
  - exact (ew_Ereg_extra regsj _ 29).
  - exact (ew_Ereg_extra regsj _ 30).
  - exact (ew_Ereg_extra regsj _ 31).
  - exact (ew_Ereg_extra regsj _ 32).
  - exact (ew_Ereg_extra regsj _ 33).
  - rewrite (ew_Ereg_nat regsj _ 3 3%bv eq_refl). exact (HK 3%bv ltac:(cbn [In]; auto 10)).
  - rewrite (ew_Ereg_nat regsj _ 4 4%bv eq_refl). exact (HK 4%bv ltac:(cbn [In]; auto 10)).
  - rewrite (ew_Ereg_nat regsj _ 25 25%bv eq_refl). exact (HK 25%bv ltac:(cbn [In]; auto 10)).
  - rewrite (ew_Ereg_nat regsj _ 26 26%bv eq_refl). exact (HK 26%bv ltac:(cbn [In]; auto 10)).
  - rewrite (ew_Ereg_nat regsj _ 27 27%bv eq_refl). exact (HK 27%bv ltac:(cbn [In]; auto 10)).
Qed.

(* ---------------------------------------------------------------- *)
(* What two memories that this segment's runs leave alike look like.  *)

Definition nd_meq (W : world SEGS) (m1 m2 : word -> option byte) : Prop :=
  forall x : word, mrestrict (w_H W) m2 x = mrestrict (w_H W) m1 x.

Lemma nd_meq_trans : forall W m1 m2 m3, nd_meq W m1 m2 -> nd_meq W m2 m3 -> nd_meq W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 x. rewrite (H2 x). exact (H1 x). Qed.

Lemma nd_meq_mbyte : forall W m1 m2 a, nd_meq W m1 m2 ->
  mbyte SEGS (mrestrict (w_H W) m2) a = mbyte SEGS (mrestrict (w_H W) m1) a.
Proof. intros W m1 m2 a H. unfold mbyte. rewrite H. reflexivity. Qed.

Lemma nd_meq_obj : forall W m1 m2 tx T, nd_meq W m1 m2 ->
  obj_at SEGS (mrestrict (w_H W) m1) tx LAY_TX (tx_vals T) ->
  obj_at SEGS (mrestrict (w_H W) m2) tx LAY_TX (tx_vals T).
Proof.
  intros W m1 m2 tx T HQ HO. apply (proj2 (tx_obj_bytes SEGS _ _ _)). intros kk Hkk.
  rewrite (nd_meq_mbyte W m1 m2 (tx + kk) HQ).
  exact (proj1 (tx_obj_bytes SEGS _ _ _) HO kk Hkk).
Qed.

Lemma nd_meq_val : forall W m1 m2 a n v, nd_meq W m1 m2 ->
  val_mem SEGS (mrestrict (w_H W) m1) a n v -> val_mem SEGS (mrestrict (w_H W) m2) a n v.
Proof. intros W m1 m2 a n v HQ HV kk Hk. rewrite (nd_meq_mbyte W m1 m2 _ HQ). exact (HV kk Hk). Qed.

Lemma nd_meq_saved : forall W m1 m2 regs sp, nd_meq W m1 m2 ->
  nx_saved W m1 regs sp -> nx_saved W m2 regs sp.
Proof.
  intros W m1 m2 regs sp HQ (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  unfold nx_saved. repeat match goal with |- _ /\ _ => split end;
    eapply nd_meq_val; first [exact HQ | eassumption].
Qed.

Lemma nd_meq_pres : forall W m1 m2 a, nd_meq W m1 m2 ->
  apresent (w_H W) m1 a -> apresent (w_H W) m2 a.
Proof.
  intros W m1 m2 a HQ (Hh & b & Hb). split; [exact Hh|]. exists b.
  pose proof (HQ (Z_to_bv 64 a)) as Hx. unfold mrestrict in Hx. rewrite Hh in Hx.
  rewrite Hx. exact Hb.
Qed.

Lemma nd_meq_same : forall W memc m1 m2 sp tx chp parp valp d, nd_meq W m1 m2 ->
  nx_same W memc m1 sp tx chp parp valp d -> nx_same W memc m2 sp tx chp parp valp d.
Proof. intros W memc m1 m2 sp tx chp parp valp d HQ HS x H1 H2. rewrite (HQ x). exact (HS x H1 H2). Qed.

Lemma nd_grows_pres : forall (W : world SEGS) m1 m2 a,
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  apresent (w_H W) m1 a -> apresent (w_H W) m2 a.
Proof.
  intros W m1 m2 a HG (Hh & b & Hb). split; [exact Hh|].
  assert (HN : mrestrict (w_H W) m1 (Z_to_bv 64 a) <> None)
    by (unfold mrestrict; rewrite Hh, Hb; discriminate).
  pose proof (HG _ HN) as H2. unfold mrestrict in H2. rewrite Hh in H2.
  destruct (m2 (Z_to_bv 64 a)) as [b2|] eqn:Hb2; [exists b2; reflexivity | exfalso; exact (H2 eq_refl)].
Qed.

(* A run whose regions have no writable window changes nothing. *)
Definition nd_ro (rs : smem) : Prop := forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r.

Lemma nd_ro_nowr : forall E rs a, nd_ro rs -> in_wrange E rs a -> False.
Proof. intros E rs a HR (r & Hin & Ha). pose proof (HR r Hin) as H. lia. Qed.

Lemma nd_ro_awr : forall E rs STK sp0 FP bl0 blc ly own,
  nd_ro rs -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof. intros E rs STK sp0 FP bl0 blc ly own HR a Ha. exfalso. exact (nd_ro_nowr E rs a HR Ha). Qed.

Lemma nd_ro_frame : forall E rs W m1 m2, nd_ro rs ->
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) -> nd_meq W m1 m2.
Proof. intros E rs W m1 m2 HR HF x. apply HF. intros Hw. exact (nd_ro_nowr E rs _ HR Hw). Qed.

Lemma nd_ro_regs : nd_ro nd_regs.
Proof.
  intros r Hin. unfold nd_regs in Hin. cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; unfold STKR, DREGR, VREG;
    cbn [YP09.r_wlo YP09.r_whi]; lia.
Qed.

(* The bytes the edge may write. *)
Lemma nd_edge_wr : forall (E : env) (a sp tx chp parp valp d : Z),
  bv_unsigned (ew E 45) = sp -> bv_unsigned (ew E 10) = tx ->
  bv_unsigned (ew E 11) = chp -> bv_unsigned (ew E 12) = parp ->
  bv_unsigned (ew E 13) = valp -> bv_unsigned (ew E 47) = d ->
  in_wrange E nd_regs_e a ->
  (tx + 456 <= a < tx + 460) \/ a = chp \/ a = parp \/ a = valp \/ a = d.
Proof.
  intros E a sp tx chp parp valp d E45 E10 E11 E12 E13 E47 (r & Hin & Ha).
  unfold nd_regs_e in Hin. cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]];
    unfold OUTV, OUTP, OUTC, TXSW, DREGW, STKR, VREG in Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    rewrite ?E45, ?E10, ?E11, ?E12, ?E13, ?E47 in Ha; lia.
Qed.

Lemma nd_edge_keep : forall (E : env) (W : world SEGS) m1 m2 (sp tx chp parp valp d a : Z),
  bv_unsigned (ew E 45) = sp -> bv_unsigned (ew E 10) = tx ->
  bv_unsigned (ew E 11) = chp -> bv_unsigned (ew E 12) = parp ->
  bv_unsigned (ew E 13) = valp -> bv_unsigned (ew E 47) = d ->
  frame_of E nd_regs_e (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  0 <= a < 2 ^ 64 ->
  ~ (tx + 456 <= a < tx + 460) -> a <> chp -> a <> parp -> a <> valp -> a <> d ->
  mbyte SEGS (mrestrict (w_H W) m2) a = mbyte SEGS (mrestrict (w_H W) m1) a.
Proof.
  intros E W m1 m2 sp tx chp parp valp d a E45 E10 E11 E12 E13 E47 HF Ha H1 H2 H3 H4 H5.
  unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  intros Hw.
  destruct (nd_edge_wr E (bv_unsigned (Z_to_bv 64 a)) sp tx chp parp valp d
              E45 E10 E11 E12 E13 E47 Hw) as [Hx | [Hx | [Hx | [Hx | Hx]]]];
    rewrite unsigned_lit_small in Hx by lia; lia.
Qed.

Lemma nd_edge_same : forall (E : env) W memc m1 m2 (sp tx chp parp valp d : Z),
  bv_unsigned (ew E 45) = sp -> bv_unsigned (ew E 10) = tx ->
  bv_unsigned (ew E 11) = chp -> bv_unsigned (ew E 12) = parp ->
  bv_unsigned (ew E 13) = valp -> bv_unsigned (ew E 47) = d ->
  frame_of E nd_regs_e (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  nx_same W memc m1 sp tx chp parp valp d ->
  nx_same W memc m2 sp tx chp parp valp d.
Proof.
  intros E W memc m1 m2 sp tx chp parp valp d E45 E10 E11 E12 E13 E47 HF HS x H1 H2.
  rewrite (HF x); [exact (HS x H1 H2)|].
  intros Hw.
  destruct (nd_edge_wr E (bv_unsigned x) sp tx chp parp valp d
              E45 E10 E11 E12 E13 E47 Hw) as [Hx | [Hx | [Hx | [Hx | Hx]]]];
    apply H2; unfold nx_touch2; lia.
Qed.

Lemma nd_same_dd : forall W memc m sp tx chp parp valp d,
  nx_same W memc m sp tx chp parp valp (tx + 432) ->
  nx_same W memc m sp tx chp parp valp d.
Proof.
  intros W memc m sp tx chp parp valp d HS x H1 H2. apply HS; [exact H1|].
  intros Hc. apply H2. unfold nx_touch2 in *. lia.
Qed.

(* Reading a byte back off the symbolic state. *)
Lemma nd_chunk_byte : forall E m base off (n : N) (e : sv) (j : Z),
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal n e)) -> 0 <= j < Z.of_N n ->
  mbyte SEGS m (base + off + j) = Some (byte_of_word (sv_denot E e) j).
Proof.
  intros E m base off n e j HC Hj. destruct (HC j Hj) as (b & Hb1 & Hb2).
  cbn [YP09.cbyte] in Hb1. injection Hb1 as <-. exact Hb2.
Qed.

Lemma nd_region_chunk : forall E m r c, region_ok SEGS E m r -> In c (YP09.r_chunks r) ->
  YP09.chunk_ok SEGS E m (base_val E (YP09.r_base r)) c.
Proof. intros E m r c (_ & _ & _ & HF) Hin. exact (proj1 (Forall_forall _ _) HF c Hin). Qed.

Lemma nd_st_region : forall E ss ms r, st_ok_pi SEGS VAL E ss ms -> In r (ss_mem ss) ->
  region_ok SEGS E (ms_mem ms) r.
Proof.
  intros E ss ms r HS Hin.
  destruct (st_ok_mem_ok SEGS E (abs_ss VAL ss) ms HS) as (_ & HF & _).
  cbn [abs_ss setpc ss_mem] in HF. exact (proj1 (Forall_forall _ _) HF r Hin).
Qed.

Lemma nd_byte_aview : forall (W : world SEGS) m a (z : Z), 0 <= z < 256 ->
  mbyte SEGS (mrestrict (w_H W) m) a = Some (byte_of_word (Z_to_bv 64 z) 0) ->
  aview SEGS (w_H W) m a = Some z.
Proof.
  intros W m a z Hz H. unfold aview. rewrite H. cbn [option_map]. f_equal.
  unfold byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite (Z.mod_small z) by (change (2 ^ Z.of_N 64) with 18446744073709551616; lia).
  change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.

Lemma nd_region_w : forall (E : env) (m : word -> option byte) (nn : nat) (base lo hi : Z),
  bv_unsigned (ew E nn) = base -> 0 <= base + lo -> base + hi <= 2 ^ 64 ->
  (forall o, lo <= o < hi -> writable_at SEGS m (base + o)) ->
  region_ok SEGS E m (YP09.mkRegion (Some nn) lo hi lo hi []).
Proof.
  intros E m nn base lo hi Hb H1 H2 Hw. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Hb. split; [exact H1|]. split; [exact H2|]. split; [exact Hw | constructor].
Qed.

Lemma nd_getrZ : forall (regs : bvmap 5 word) (r : bv 5) (z : Z), z = bv_unsigned r ->
  getr regs (Z_to_bv 5 z) = getr regs r.
Proof.
  intros regs r z ->. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma nd_u64 : forall (x : word), 0 <= bv_unsigned x < 2 ^ (8 * Z.of_N 8).
Proof.
  intros x. pose proof (bv_unsigned_in_range 64 x) as H.
  change (bv_modulus 64) with 18446744073709551616 in H.
  change (2 ^ (8 * Z.of_N 8)) with 18446744073709551616. exact H.
Qed.

Definition nd_uenv_ok (E : env) (sp tx chp parp valp i : Z) (T : list byte) : Prop :=
  bv_unsigned (ew E 45) = sp /\ bv_unsigned (ew E 10) = tx /\ bv_unsigned (ew E 11) = chp /\
  bv_unsigned (ew E 12) = parp /\ bv_unsigned (ew E 13) = valp /\ bv_unsigned (ew E 32) = SB_NX /\
  bv_unsigned (ew E 46) = i /\ bv_unsigned (ew E 47) = tx + 288 + i /\
  bv_unsigned (ew E 48) = tx + i /\
  bv_unsigned (ew E 49) = tb T (288 + i) /\ bv_unsigned (ew E 50) = tb T i.

Lemma nd_uenv : forall E regs sp tx chp parp valp i T,
  nd_env_ok E regs sp tx chp parp valp i T ->
  0 <= sp < 2 ^ 64 -> 0 <= tx -> tx + 460 <= 2 ^ 47 ->
  0 <= chp < 2 ^ 64 -> 0 <= parp < 2 ^ 64 -> 0 <= valp < 2 ^ 64 -> 0 <= i < 144 ->
  nd_uenv_ok E sp tx chp parp valp i T.
Proof.
  intros E regs sp tx chp parp valp i T
    (A45 & A10 & A11 & A12 & A13 & A32 & A46 & A47 & A48 & A49 & A50 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _)
    Hsp Htx0 Htx1 Hchp Hparp Hvalp Hi.
  pose proof (HeadampTxEffective.tb_range T (288 + i)) as Rd.
  pose proof (HeadampTxEffective.tb_range T i) as Rv.
  unfold nd_uenv_ok.
  rewrite A45, A10, A11, A12, A13, A32, A46, A47, A48, A49, A50.
  repeat match goal with |- _ /\ _ => split end;
    apply unsigned_lit_small; unfold SB_NX; lia.
Qed.

Lemma nd_shadow_apart : forall (tx chp parp valp p : Z),
  in_app tx 460 -> 0 <= p / 8 < 17592186044416 ->
  ~ (SHADOW_OFF <= chp < SHADOW_OFF + 17592186044416) ->
  ~ (SHADOW_OFF <= parp < SHADOW_OFF + 17592186044416) ->
  ~ (SHADOW_OFF <= valp < SHADOW_OFF + 17592186044416) ->
  ~ nx_touch tx chp parp valp (SHADOW_OFF + p / 8).
Proof.
  intros tx chp parp valp p Happ Hdiv Hc Hp Hv.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold nx_touch, TX_SIZE. intros [Hq | [Hq | [Hq | Hq]]]; lia.
Qed.

Lemma nd_shadow_lo : forall (p : Z), 0 <= p / 8 < 17592186044416 ->
  0 <= SHADOW_OFF + p / 8 < 2 ^ 64.
Proof. intros p Hp. unfold SHADOW_OFF. lia. Qed.

Lemma nd_shadow_stk : forall (p sp : Z), 0 <= p / 8 < 17592186044416 ->
  2 ^ 46 <= sp <= 2 ^ 47 -> ~ (sp - NEXT_STK <= SHADOW_OFF + p / 8 < sp).
Proof. intros p sp Hp Hsp. unfold SHADOW_OFF, NEXT_STK. lia. Qed.

Lemma nd_lit0 : forall E, sv_denot E (SLit 0) = Z_to_bv 64 0.
Proof. intros E. reflexivity. Qed.

Lemma nd_byte0 : forall (j : Z), 0 <= j -> byte_of_word (Z_to_bv 64 0) j = Z_to_bv 8 0.
Proof.
  intros j Hj. unfold byte_of_word. rewrite (unsigned_lit_small 0) by lia.
  rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma nd_mem_byte : forall (W : world SEGS) E ss (ms : machine_state) (r : YP09.region)
    (nn : nat) (off : Z) (w : N) (e : sv) (a j : Z),
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> In r (ss_mem ss) ->
  YP09.r_base r = Some nn -> In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks r) ->
  bv_unsigned (ew E nn) = a -> 0 <= j < Z.of_N w ->
  mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) (a + off + j) = Some (byte_of_word (sv_denot E e) j).
Proof.
  intros W E ss ms r nn off w e a j HS Hin Hb Hch Ha Hj.
  pose proof (nd_region_chunk E (ms_mem (restrict (w_H W) ms)) r _
                (nd_st_region E ss _ r HS Hin) Hch) as CH.
  rewrite Hb in CH. cbn [base_val] in CH. rewrite Ha in CH.
  cbn [restrict ms_mem] in CH.
  exact (nd_chunk_byte E _ a off w e j CH Hj).
Qed.

Lemma st_ok_pi_submem : forall E ss ms rs,
  st_ok_pi SEGS VAL E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms rs HS Hsub Hwf.
  exact (st_ok_submem SEGS E (abs_ss VAL ss) ms rs HS Hsub Hwf).
Qed.

Local Ltac nd_dis1 :=
  cbn [all_disjoint ss_mem];
  repeat match goal with |- _ /\ _ => split end; try exact I;
  unfold extent_disjoint;
  cbn [OUTV OUTP OUTC TXSW DREGW STKR VREG YP09.r_base YP09.r_lo YP09.r_hi base_val];
  lia.

(* The edge is about to write: the dirty byte, the four bytes of resweep_wait and the
   three bytes the caller holds become writable windows of the symbolic state. *)
Lemma nd_swap : forall (E : env) ss (ms : machine_state) (sp tx chp parp valp d vv : Z),
  st_ok_pi SEGS VAL E ss ms -> ss_mem ss = nd_regs ->
  bv_unsigned (ew E 45) = sp -> bv_unsigned (ew E 10) = tx ->
  bv_unsigned (ew E 11) = chp -> bv_unsigned (ew E 12) = parp ->
  bv_unsigned (ew E 13) = valp -> bv_unsigned (ew E 47) = d -> bv_unsigned (ew E 48) = vv ->
  4096 <= tx -> tx + 460 <= sp - 80 ->
  tx <= d < tx + 432 -> tx <= vv < tx + 432 -> d <> vv ->
  ~ (tx <= chp < tx + 460) -> (chp + 1 <= sp - 80 \/ sp <= chp) ->
  ~ (tx <= parp < tx + 460) -> (parp + 1 <= sp - 80 \/ sp <= parp) ->
  ~ (tx <= valp < tx + 460) -> (valp + 1 <= sp - 80 \/ sp <= valp) ->
  chp <> parp -> chp <> valp -> parp <> valp ->
  region_ok SEGS E (ms_mem ms) DREGW -> region_ok SEGS E (ms_mem ms) TXSW ->
  region_ok SEGS E (ms_mem ms) OUTC -> region_ok SEGS E (ms_mem ms) OUTP ->
  region_ok SEGS E (ms_mem ms) OUTV ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) nd_regs_e (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms sp tx chp parp valp d vv HS Hmem E45 E10 E11 E12 E13 E47 E48
    Htx Hstk Hd Hvv Hdv Oc2 Oc3 Op2 Op3 Ov2 Ov3 Dcp Dcv Dpv RD RT RC RP RV.
  assert (HS1 : st_ok_pi SEGS VAL E
            (mkSS (ss_pc ss) (ss_regs ss) [STKR; VREG] (ss_resv ss) (ss_facts ss)) ms)
    by (apply (st_ok_pi_submem E ss ms);
        [exact HS | rewrite Hmem; unfold nd_regs; submem_tac | vm_compute; reflexivity]).
  pose proof (st_ok_pi_add_region E _ ms DREGW HS1 ltac:(vm_compute; reflexivity) RD
                ltac:(nd_dis1)) as HS2.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
  pose proof (st_ok_pi_add_region E _ ms TXSW HS2 ltac:(vm_compute; reflexivity) RT
                ltac:(nd_dis1)) as HS3.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3.
  pose proof (st_ok_pi_add_region E _ ms OUTC HS3 ltac:(vm_compute; reflexivity) RC
                ltac:(nd_dis1)) as HS4.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS4.
  pose proof (st_ok_pi_add_region E _ ms OUTP HS4 ltac:(vm_compute; reflexivity) RP
                ltac:(nd_dis1)) as HS5.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS5.
  pose proof (st_ok_pi_add_region E _ ms OUTV HS5 ltac:(vm_compute; reflexivity) RV
                ltac:(nd_dis1)) as HS6.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS6.
  exact HS6.
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

Lemma nd_edge_awr : forall (E : env) STK sp0 FP ly S lyc Sc own (sp tx chp parp valp d : Z),
  bv_unsigned (ew E 45) = sp -> bv_unsigned (ew E 10) = tx ->
  bv_unsigned (ew E 11) = chp -> bv_unsigned (ew E 12) = parp ->
  bv_unsigned (ew E 13) = valp -> bv_unsigned (ew E 47) = d ->
  tx <= d < tx + TX_SIZE ->
  (forall a, tx <= a < tx + TX_SIZE ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own chp ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own parp ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own valp ->
  awr_ok E nd_regs_e STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof.
  intros E STK sp0 FP ly S lyc Sc own sp tx chp parp valp d
    E45 E10 E11 E12 E13 E47 Hd Htab Hc Hp Hv a Ha.
  destruct (nd_edge_wr E a sp tx chp parp valp d E45 E10 E11 E12 E13 E47 Ha)
    as [Hx | [-> | [-> | [-> | ->]]]].
  - apply Htab. unfold TX_SIZE in *. lia.
  - exact Hc.
  - exact Hp.
  - exact Hv.
  - apply Htab. exact Hd.
Qed.

(* The symbolic state at the head of the edge scan. *)
Lemma nd_seat : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
    memc mdc k (regs regsj : bvmap 5 word) memj mdj
    (tx chp parp valp : Z) (T : list byte) (i : Z),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) ->
  nx_saved W memj regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals T) ->
  (forall r : bv 5, In r [3; 4; 25; 26; 27]%bv -> getr regsj r = getr regs r) ->
  0 <= i < 144 ->
  getr regsj 2 = w64 (spZ regs - 80) -> getr regsj 5 = w64 SB_NX ->
  getr regsj 7 = w64 i -> getr regsj 28 = w64 (tx + 288) ->
  getr regsj 29 = w64 171 -> getr regsj 30 = w64 144 ->
  getr regsj 10 = w64 tx -> getr regsj 11 = w64 chp ->
  getr regsj 12 = w64 parp -> getr regsj 13 = w64 valp ->
  st_ok_pi SEGS VAL (ND regsj regs tx i T) ss_d
    (restrict (w_H W) (mkst regsj (Z_to_bv 64 (BASE + LOOPD)) memj (seg_rom SEGS)))
  /\ sh_ok SEGS BxN nd_SH (ND regsj regs tx i T) (mrestrict (w_H W) memj).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
    tx chp parp valp T i HCTX HMID HSAV HOBJ HKEEP Hi R2 R5 R7 R28 R29 R30 R10 R11 R12 R13.
  pose proof HCTX as (HAR & Hg & Hoc & Hop & Hov & Dcp & Dcv & Dpv & Pc & Pp & Pv & Rac & Rap & Rav &
    Hspr & Hceil & Hsp16 & Hslo & Hshi & Hwtab & Hwc & Hwp & Hwv & Hret & Hra4 & Hgp & Htp &
    Q10 & Q11 & Q12 & Q13 & HTL & HI & Hobjc & Hpresc).
  pose proof HMID as (HJ & HSAME & HpresS & HpresK).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (proj1 HJ) as HARj.
  destruct (al_blocks _ _ LAWS lyc Sc W memj mdj tx TX_SIZE HARj Hg)
    as (Hg16 & Hg4096 & Hgceil & Hgia & Hgpres & _).
  change (req_size TX_SIZE) with 460 in Hgceil, Hgia, Hgpres.
  pose proof Hgia as Hgapp.
  destruct Hoc as (Hc0 & Hc1 & Hc2 & Hc3 & Hc4 & Hc5).
  destruct Hop as (Hp0 & Hp1 & Hp2 & Hp3 & Hp4 & Hp5).
  destruct Hov as (Hv0 & Hv1 & Hv2 & Hv3 & Hv4 & Hv5).
  pose proof (HeadampTxEffective.tb_range T (288 + i)) as Rd.
  pose proof (HeadampTxEffective.tb_range T i) as Rv.
  pose proof (nd_env regsj regs tx chp parp valp i T HKEEP R10 R11 R12 R13) as HE.
  pose proof HE as (E45 & E10 & E11 & E12 & E13 & E32 & E46 & E47 & E48 & E49 & E50 &
    E56 & E57 & E58 & E59 & E60 & E61 & E62 & E63 & E64 & E65 & E3 & E4 & E25 & E26 & E27).
  pose proof (nd_uenv (ND regsj regs tx i T) regs (spZ regs) tx chp parp valp i T HE
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HU.
  pose proof HU as (U45 & U10 & U11 & U12 & U13 & U32 & U46 & U47 & U48 & U49 & U50).
  clear HCTX HMID HE HU HI HJ HAR Hobjc Hpresc Hret Hra4 Hgp Htp
    Q10 Q11 Q12 Q13 Hwtab Hwc Hwp Hwv Pc Pp Pv Hgia Hgpres HpresS HpresK HTL.
  set (E := ND regsj regs tx i T) in *.
  assert (HUB : U E BxN = SHADOW_OFF)
    by (unfold U, BxN; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact U32).
  split.
  - rewrite restrict_mkst_fx. unfold ss_d. apply pa_entry_st_ok_full.
    + unfold sr_d.
      apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R30].
      apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R29].
      apply regs_ok_pin; [| intros X; discriminate X
        | cbn [sv_denot]; rewrite U10, R28; reflexivity].
      apply regs_ok_pin; [| intros X; discriminate X
        | cbn [sv_denot]; rewrite U46, Z.add_0_r, R7; reflexivity].
      apply regs_ok_pin; [| intros X; discriminate X
        | cbn [sv_denot]; rewrite U32, Z.add_0_r, R5; reflexivity].
      apply regs_ok_pin; [| intros X; discriminate X
        | cbn [sv_denot]; rewrite U45, R2; unfold w64; f_equal; lia].
      unfold E, ND. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold nd_regs, STKR, DREGR, VREG.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U45. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        pose proof HSAV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-8) 8 (SOff 56 0) (bv_unsigned (getr regs 1)));
             [ cbn [sv_denot]; rewrite E56, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs + -8) with (spZ regs - 8) by lia; exact S1 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-16) 8 (SOff 57 0) (bv_unsigned (getr regs 8)));
             [ cbn [sv_denot]; rewrite E57, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs + -16) with (spZ regs - 16) by lia; exact S2 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-24) 8 (SOff 58 0) (bv_unsigned (getr regs 9)));
             [ cbn [sv_denot]; rewrite E58, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs + -24) with (spZ regs - 24) by lia; exact S3 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-32) 8 (SOff 59 0) (bv_unsigned (getr regs 18)));
             [ cbn [sv_denot]; rewrite E59, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs + -32) with (spZ regs - 32) by lia; exact S4 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-40) 8 (SOff 60 0) (bv_unsigned (getr regs 19)));
             [ cbn [sv_denot]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs + -40) with (spZ regs - 40) by lia; exact S5 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-48) 8 (SOff 61 0) (bv_unsigned (getr regs 20)));
             [ cbn [sv_denot]; rewrite E61, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs + -48) with (spZ regs - 48) by lia; exact S6 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-56) 8 (SOff 62 0) (bv_unsigned (getr regs 21)));
             [ cbn [sv_denot]; rewrite E62, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs + -56) with (spZ regs - 56) by lia; exact S7 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-64) 8 (SOff 63 0) (bv_unsigned (getr regs 22)));
             [ cbn [sv_denot]; rewrite E63, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs + -64) with (spZ regs - 64) by lia; exact S8 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-72) 8 (SOff 64 0) (bv_unsigned (getr regs 23)));
             [ cbn [sv_denot]; rewrite E64, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs + -72) with (spZ regs - 72) by lia; exact S9 ].
        -- apply (chunk_ok_val SEGS E _ (spZ regs) (-80) 8 (SOff 65 0) (bv_unsigned (getr regs 24)));
             [ cbn [sv_denot]; rewrite E65, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | exact (nd_u64 _) | cbn; lia
             | replace (spZ regs + -80) with (spZ regs - 80) by lia; exact S10 ].
      * rewrite U47. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [| apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (tx + 288 + i) 0 1 (SOff 49 0) (tb T (288 + i)));
          [ cbn [sv_denot]; rewrite E49, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | cbn; lia | cbn; lia |].
        replace (tx + 288 + i + 0) with (tx + (288 + i)) by lia.
        exact (tx_cell_val SEGS _ tx T (288 + i) ltac:(lia) HOBJ).
      * rewrite U48. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [| apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (tx + i) 0 1 (SOff 50 0) (tb T i));
          [ cbn [sv_denot]; rewrite E50, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | cbn; lia | cbn; lia |].
        replace (tx + i + 0) with (tx + i) by lia.
        exact (tx_cell_val SEGS _ tx T i ltac:(lia) HOBJ).
    + apply pairwise_disjoint_of_extents.
      unfold nd_regs, STKR, DREGR, VREG, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      cbn [base_val]. rewrite U45, U47, U48.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hspr Hceil Hgceil Hg4096 Hi C1. clear. unfold NEXT_STK. intros.
      repeat split; lia.
    + split; [| split; [exact I |]].
      * cbn [nd_atoms f_atoms atoms_ok]. unfold afact_ok, PTRN, OUTB.
        cbn [af_lo af_hi af_al2].
        rewrite U45, U10, U11, U12, U13, U32, U46, U47, U48, U49, U50.
        change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
        revert Hspr Hsp16 Hg16 Hg4096 Hgceil Hi Rd Rv Hc0 Hc1 Hp0 Hp1 Hv0 Hv1 C1.
        clear. unfold SB_NX. intros.
        repeat match goal with |- _ /\ _ => split end; lia.
      * cbn [nd_alias f_alias alias_ok]. split; [| split; [| exact I]].
        -- cbn [sv_denot]. rewrite E47, Z.add_0_r, Z_to_bv_bv_unsigned.
           exact (proj1 (dexpr_denot E tx i E10 E46 ltac:(lia) ltac:(lia) ltac:(lia))).
        -- cbn [sv_denot]. rewrite E48, Z.add_0_r, Z_to_bv_bv_unsigned.
           exact (proj2 (dexpr_denot E tx i E10 E46 ltac:(lia) ltac:(lia) ltac:(lia))).
  - assert (RAj : forall p, 4096 <= p -> p + 1 <= 2 ^ 47 ->
      ~ (SHADOW_OFF <= p < SHADOW_OFF + 17592186044416) ->
      range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p 1 ->
      range_addressable (aview SEGS (w_H W) memj) SHADOW_OFF p 1).
    { intros pz Hz0 Hz1 Hz5 Hra.
      apply (range_addressable_agree (aview SEGS (w_H W) memc)); [| exact Hra].
      intros x Hx. assert (x = pz) as -> by lia.
      assert (Hdiv : 0 <= pz / 8 < 17592186044416)
        by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      unfold shadow_of_addr.
      apply (nx_same_aview W memc memj (spZ regs) tx chp parp valp (tx + 432) (SHADOW_OFF + pz / 8));
        [ exact HSAME
        | exact (nd_shadow_lo pz Hdiv)
        | revert Hgceil Hg4096; clear; unfold TX_SIZE; intros; lia
        | exact (nd_shadow_stk pz (spZ regs) Hdiv Hspr)
        | exact (nd_shadow_apart tx chp parp valp pz Hgapp Hdiv Hc5 Hp5 Hv5) ]. }
    unfold sh_ok, nd_SH, nx_SH. cbn [app].
    constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]].
    + apply (shent_of_block_at B LAWS lyc Sc W memj mdj E 10 tx tx TX_SIZE 0 460 HARj Hg HUB).
      * unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U10.
      * lia.
      * lia.
      * change (req_size TX_SIZE) with 460. lia.
    + apply (shent_ok_of_range SEGS (w_H W) memj E BxN 11 chp 1 chp 0 1
               (RAj chp ltac:(lia) ltac:(lia) ltac:(exact Hc5) Rac) HUB).
      * unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U11.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with chp by lia. exact Hc5.
    + apply (shent_ok_of_range SEGS (w_H W) memj E BxN 12 parp 1 parp 0 1
               (RAj parp ltac:(lia) ltac:(lia) ltac:(exact Hp5) Rap) HUB).
      * unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U12.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with parp by lia. exact Hp5.
    + apply (shent_ok_of_range SEGS (w_H W) memj E BxN 13 valp 1 valp 0 1
               (RAj valp ltac:(lia) ltac:(lia) ltac:(exact Hv5) Rav) HUB).
      * unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U13.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with valp by lia. exact Hv5.
    + apply (shent_of_block_at B LAWS lyc Sc W memj mdj E 47 (tx + 288 + i) tx TX_SIZE 0 1 HARj Hg HUB).
      * unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U47.
      * lia.
      * lia.
      * change (req_size TX_SIZE) with 460. lia.
    + apply (shent_of_block_at B LAWS lyc Sc W memj mdj E 48 (tx + i) tx TX_SIZE 0 1 HARj Hg HUB).
      * unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U48.
      * lia.
      * lia.
      * change (req_size TX_SIZE) with 460. lia.
Qed.

(* The regions as the edge run leaves them: the three bytes the caller holds, the four
   bytes of resweep_wait and the dirty byte all carry the value the walk wrote. *)
Definition OUTVf : YP09.region := YP09.mkRegion (Some 13%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 50 0))].
Definition OUTPf : YP09.region := YP09.mkRegion (Some 12%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 RMraw)].
Definition OUTCf : YP09.region := YP09.mkRegion (Some 11%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 Q3)].
Definition TXSWf : YP09.region := YP09.mkRegion (Some 10%nat) 456 460 456 460 [YP09.mkChunk 456 (CVal 4 (SLit 0))].
Definition DREGWf : YP09.region := YP09.mkRegion (Some 47%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))].

Local Ltac ndenv Hold Hnew :=
  lazymatch type of Hold with
  | nd_env_ok _ ?rg ?sp ?tx ?chp ?parp ?valp ?i ?T =>
    lazymatch goal with
    | HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
      assert (Hnew : nd_env_ok Ex rg sp tx chp parp valp i T)
        by (eapply nd_env_lift;
            [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact Hold])
    end
  end.

Local Ltac nd_dis0 :=
  cbn [all_disjoint ss_mem];
  repeat match goal with |- _ /\ _ => split end; try exact I;
  unfold extent_disjoint;
  cbn [OUTV OUTP OUTC TXSW DREGW STKR VREG YP09.r_base YP09.r_lo YP09.r_hi base_val].

Local Ltac nd_clr :=
  repeat match goal with
  | H : frame_of _ _ _ _ |- _ => clear H
  | H : mem_grows _ _ |- _ => clear H
  end.

Lemma nx_dloop : forall (n : nat) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
    memc mdc k (regs regsj : bvmap 5 word) memj mdj
    (tx chp parp valp : Z) (T : list byte) (i : Z),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) ->
  nx_saved W memj regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals T) ->
  ~ (u32at T 432 = 0 /\ tb T 437 = 0) ->
  0 <= i < 144 -> Z.of_nat n = 144 - i ->
  (forall l, 0 <= l < i -> tb T (288 + l) = 0) ->
  (forall (regsA : bvmap 5 word) memA mdA,
     nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memA mdA tx chp parp valp (tx + 432) ->
     nx_saved W memA regs (spZ regs) ->
     (forall r : bv 5, In r [3; 4; 25; 26; 27]%bv -> getr regsA r = getr regs r) ->
     obj_at SEGS (mrestrict (w_H W) memA) tx LAY_TX (tx_vals T) ->
     (forall l, 0 <= l < 144 -> tb T (288 + l) = 0) ->
     getr regsA 2 = w64 (spZ regs - 80) -> getr regsA 5 = w64 SB_NX ->
     getr regsA 10 = w64 tx -> getr regsA 11 = w64 chp ->
     getr regsA 12 = w64 parp -> getr regsA 13 = w64 valp ->
     SRr SEGS W (cfg_at SEGS (BASE + AFTR) regsA memA mdA)
       (tnext_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T)) ->
  (forall r : bv 5, In r [3; 4; 25; 26; 27]%bv -> getr regsj r = getr regs r) ->
  getr regsj 2 = w64 (spZ regs - 80) -> getr regsj 5 = w64 SB_NX ->
  getr regsj 7 = w64 i -> getr regsj 28 = w64 (tx + 288) ->
  getr regsj 29 = w64 171 -> getr regsj 30 = w64 144 ->
  getr regsj 10 = w64 tx -> getr regsj 11 = w64 chp ->
  getr regsj 12 = w64 parp -> getr regsj 13 = w64 valp ->
  SRr SEGS W (cfg_at SEGS (BASE + LOOPD) regsj memj mdj)
    (tnext_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).
Proof.
induction n as [|n IH]; intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
  tx chp parp valp T i HCTX HMID HSAV HOBJ HACT Hi Hn Hz KAFTR HKEEP R2 R5 R7 R28 R29 R30 R10 R11 R12 R13;
  [lia|].
pose proof HCTX as (HAR & Hg & Hoc & Hop & Hov & Dcp & Dcv & Dpv & Pc & Pp & Pv & Rac & Rap & Rav &
  Hspr & Hceil & Hsp16 & Hslo & Hshi & Hwtab & Hwc & Hwp & Hwv & Hret & Hra4 & Hgp & Htp &
  Q10 & Q11 & Q12 & Q13 & HTL & HI & Hobjc & Hpresc).
pose proof HMID as (HJ & HSAME & HpresS & HpresK).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HARj.
destruct (al_blocks _ _ LAWS lyc Sc W memj mdj tx TX_SIZE HARj Hg)
  as (Hg16 & Hg4096 & Hgceil & Hgia & Hgpres & _).
change (req_size TX_SIZE) with 460 in Hgceil, Hgia, Hgpres.
assert (Bc : 4096 <= chp < 2 ^ 47) by (destruct Hoc as (? & ? & _); lia).
assert (Bp : 4096 <= parp < 2 ^ 47) by (destruct Hop as (? & ? & _); lia).
assert (Bv : 4096 <= valp < 2 ^ 47) by (destruct Hov as (? & ? & _); lia).
unfold NEXT_STK in Hceil.
clear HI Hgia.
pose proof (HeadampTxEffective.tb_range T (288 + i)) as Rd.
pose proof (HeadampTxEffective.tb_range T i) as Rvb.
destruct (nd_seat STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
  tx chp parp valp T i HCTX HMID HSAV HOBJ HKEEP Hi R2 R5 R7 R28 R29 R30 R10 R11 R12 R13) as [HS SHOK].
pose proof (nd_env regsj regs tx chp parp valp i T HKEEP R10 R11 R12 R13) as HE0.
remember (ND regsj regs tx i T) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (rewrite HEdef; unfold ND; apply Eimg_env).
clear HEdef.
unfold cfg_at. change (w64 (BASE + LOOPD)) with (Z_to_bv 64 (BASE + LOOPD)).
paj_run_tok RUN HS HJ SHOK BspanN; [apply nd_ro_awr; exact nd_ro_regs |].
lazymatch goal with
| HFr : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    pose proof (nd_ro_frame _ _ W m1 m2 nd_ro_regs HFr) as MQ1
end.
nd_clr.
pose proof HE0 as (A45 & A10 & A11 & A12 & A13 & A32 & A46 & A47 & A48 & A49 & A50 &
  A56 & A57 & A58 & A59 & A60 & A61 & A62 & A63 & A64 & A65 & A3 & A4 & A25 & A26 & A27).
pose proof (nd_uenv _ regs (spZ regs) tx chp parp valp i T HE0
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HU0.
pose proof HU0 as (AU45 & AU10 & AU11 & AU12 & AU13 & AU32 & AU46 & AU47 & AU48 & AU49 & AU50).
ndenv HE0 HE1. clear HE0 HU0.
pose proof HE1 as (F45 & F10 & F11 & F12 & F13 & F32 & F46 & F47 & F48 & F49 & F50 &
  F56 & F57 & F58 & F59 & F60 & F61 & F62 & F63 & F64 & F65 & F3 & F4 & F25 & F26 & F27).
pose proof (nd_uenv _ regs (spZ regs) tx chp parp valp i T HE1
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HU1.
pose proof HU1 as (G45 & G10 & G11 & G12 & G13 & G32 & G46 & G47 & G48 & G49 & G50).
psrr_branch_tok RUN BR HS SHOK BspanN.
- (* the cell is dirty: the edge emits the record *)
  rewrite branch_ne_U, (U_atom _ 49 _ F49), U_lit in Hc by lia.
  rewrite negb_true_iff in Hc. apply Z.eqb_neq in Hc.
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (PRtx : forall a, tx <= a < tx + 460 -> apresent (w_H W) (ms_mem msx) a)
      by (intros a Ha; eapply nd_meq_pres; [exact MQ1|]; apply Hgpres; lia);
    assert (PRc : apresent (w_H W) (ms_mem msx) chp)
      by (eapply nd_meq_pres; [exact MQ1|]; apply HpresK; exact Pc);
    assert (PRp : apresent (w_H W) (ms_mem msx) parp)
      by (eapply nd_meq_pres; [exact MQ1|]; apply HpresK; exact Pp);
    assert (PRv : apresent (w_H W) (ms_mem msx) valp)
      by (eapply nd_meq_pres; [exact MQ1|]; apply HpresK; exact Pv)
  end.
  assert (Oc2 : ~ (tx <= chp < tx + 460))
    by (destruct Hoc as (_ & _ & X & _); unfold TX_SIZE in X; exact X).
  assert (Oc3 : chp + 1 <= spZ regs - 80 \/ spZ regs <= chp)
    by (destruct Hoc as (_ & _ & _ & X & _); unfold NEXT_STK in X; exact X).
  assert (Op2 : ~ (tx <= parp < tx + 460))
    by (destruct Hop as (_ & _ & X & _); unfold TX_SIZE in X; exact X).
  assert (Op3 : parp + 1 <= spZ regs - 80 \/ spZ regs <= parp)
    by (destruct Hop as (_ & _ & _ & X & _); unfold NEXT_STK in X; exact X).
  assert (Ov2 : ~ (tx <= valp < tx + 460))
    by (destruct Hov as (_ & _ & X & _); unfold TX_SIZE in X; exact X).
  assert (Ov3 : valp + 1 <= spZ regs - 80 \/ spZ regs <= valp)
    by (destruct Hov as (_ & _ & _ & X & _); unfold NEXT_STK in X; exact X).
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
    assert (RD : region_ok SEGS Ex (mrestrict (w_H W) (ms_mem msx)) DREGW)
      by (unfold DREGW; apply (nd_region_w _ _ 47 (tx + 288 + i) 0 1 G47 ltac:(lia) ltac:(lia));
          intros o Ho; replace (tx + 288 + i + o) with (tx + (288 + i)) by lia;
          apply (apresent_writable SEGS); apply PRtx; lia);
    assert (RT : region_ok SEGS Ex (mrestrict (w_H W) (ms_mem msx)) TXSW)
      by (unfold TXSW; apply (nd_region_w _ _ 10 tx 456 460 G10 ltac:(lia) ltac:(lia));
          intros o Ho; apply (apresent_writable SEGS); apply PRtx; lia);
    assert (RC : region_ok SEGS Ex (mrestrict (w_H W) (ms_mem msx)) OUTC)
      by (unfold OUTC; apply (nd_region_w _ _ 11 chp 0 1 G11 ltac:(lia) ltac:(lia));
          intros o Ho; replace (chp + o) with chp by lia;
          apply (apresent_writable SEGS); exact PRc);
    assert (RP : region_ok SEGS Ex (mrestrict (w_H W) (ms_mem msx)) OUTP)
      by (unfold OUTP; apply (nd_region_w _ _ 12 parp 0 1 G12 ltac:(lia) ltac:(lia));
          intros o Ho; replace (parp + o) with parp by lia;
          apply (apresent_writable SEGS); exact PRp);
    assert (RV : region_ok SEGS Ex (mrestrict (w_H W) (ms_mem msx)) OUTV)
      by (unfold OUTV; apply (nd_region_w _ _ 13 valp 0 1 G13 ltac:(lia) ltac:(lia));
          intros o Ho; replace (valp + o) with valp by lia;
          apply (apresent_writable SEGS); exact PRv)
  end.
  pose proof (nd_swap _ _ _ (spZ regs) tx chp parp valp (tx + 288 + i) (tx + i)
    HS eq_refl G45 G10 G11 G12 G13 G47 G48 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) Oc2 Oc3 Op2 Op3 Ov2 Ov3 Dcp Dcv Dpv RD RT RC RP RV) as HS1.
  clear HS. rename HS1 into HS.
  paj_run_tok RUN HS HJ SHOK BspanN;
    [ apply (nd_edge_awr _ STK sp0 FP ly S lyc Sc own (spZ regs) tx chp parp valp (tx + 288 + i));
      [ exact G45 | exact G10 | exact G11 | exact G12 | exact G13 | exact G47
      | unfold TX_SIZE; lia | exact Hwtab | exact Hwc | exact Hwp | exact Hwv ] |].
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ => pose proof HFr as FR2
  end.
  lazymatch goal with
  | HGx : mem_grows _ _ |- _ => pose proof HGx as GR2
  end.
  ndenv HE1 HE2.
  pose proof HE2 as (K45 & K10 & K11 & K12 & K13 & K32 & K46 & K47 & K48 & K49 & K50 &
    K56 & K57 & K58 & K59 & K60 & K61 & K62 & K63 & K64 & K65 & K3 & K4 & K25 & K26 & K27).
  pose proof (nd_uenv _ regs (spZ regs) tx chp parp valp i T HE2
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HU2.
  pose proof HU2 as (N45 & N10 & N11 & N12 & N13 & N32 & N46 & N47 & N48 & N49 & N50).
  (* the bytes the edge wrote, read back off the symbolic state *)
  pose proof (nd_mem_byte W _ _ _ OUTVf 13 0 1 (SOff 50 0) valp 0 HS
    ltac:(cbn [ss_mem]; left; reflexivity) eq_refl ltac:(cbn [YP09.r_chunks]; left; reflexivity)
    N13 ltac:(cbn; lia)) as BYv.
  pose proof (nd_mem_byte W _ _ _ OUTPf 12 0 1 RMraw parp 0 HS
    ltac:(cbn [ss_mem]; right; left; reflexivity) eq_refl ltac:(cbn [YP09.r_chunks]; left; reflexivity)
    N12 ltac:(cbn; lia)) as BYp.
  pose proof (nd_mem_byte W _ _ _ OUTCf 11 0 1 Q3 chp 0 HS
    ltac:(cbn [ss_mem]; right; right; left; reflexivity) eq_refl
    ltac:(cbn [YP09.r_chunks]; left; reflexivity) N11 ltac:(cbn; lia)) as BYc.
  pose proof (nd_mem_byte W _ _ _ DREGWf 47 0 1 (SLit 0) (tx + 288 + i) 0 HS
    ltac:(cbn [ss_mem]; right; right; right; right; left; reflexivity) eq_refl
    ltac:(cbn [YP09.r_chunks]; left; reflexivity) N47 ltac:(cbn; lia)) as BYd.
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (BYw : forall j, 0 <= j < 4 ->
      mbyte SEGS (mrestrict (w_H W) (ms_mem msx)) (tx + 456 + j) = Some (Z_to_bv 8 0))
      by (intros j Hj;
          rewrite (nd_mem_byte W _ _ _ TXSWf 10 456 4 (SLit 0) tx j HS
            ltac:(cbn [ss_mem]; right; right; right; left; reflexivity) eq_refl
            ltac:(cbn [YP09.r_chunks]; left; reflexivity) N10 ltac:(cbn; lia));
          rewrite nd_lit0, nd_byte0 by lia; reflexivity)
  end.
  (* the registers at the ret *)
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
  prreg HS (27%bv : bv 5) P27.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. cbn [ms_regs ms_mem].
  rewrite P1, A56. unfold YK0s.ret_ok in Hret. rewrite Hret.
  eapply (nx_finish B LAWS) with (d := tx + 288 + i)
    (T' := set4 (setb T (288 + i) 0) 456 0) (r := 1) (c := i / 3) (p := i mod 3) (v := tb T i).
  + unfold TX_SIZE. lia.
  + exact HAR.
  + exact Hg.
  + exact Hoc.
  + exact Hop.
  + exact Hov.
  + exact Hspr.
  + unfold NEXT_STK. lia.
  + rewrite (nx_model_edge T tx i HACT ltac:(lia) Hz Hc). reflexivity.
  + apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
  + (* the registers the call keeps *)
    intros r Hr.
    assert (Hcs : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/
                  r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
      by (unfold acallee_saved in Hr; lia).
    clear Hr.
    destruct Hcs as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    * rewrite !(nd_getrZ _ (2%bv : bv 5) 2 eq_refl), P2, A45. unfold spZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
    * rewrite !(nd_getrZ _ (3%bv : bv 5) 3 eq_refl), P3. exact A3.
    * rewrite !(nd_getrZ _ (4%bv : bv 5) 4 eq_refl), P4. exact A4.
    * rewrite !(nd_getrZ _ (8%bv : bv 5) 8 eq_refl), P8. exact A57.
    * rewrite !(nd_getrZ _ (9%bv : bv 5) 9 eq_refl), P9. exact A58.
    * rewrite !(nd_getrZ _ (18%bv : bv 5) 18 eq_refl), P18. exact A59.
    * rewrite !(nd_getrZ _ (19%bv : bv 5) 19 eq_refl), P19. exact A60.
    * rewrite !(nd_getrZ _ (20%bv : bv 5) 20 eq_refl), P20. exact A61.
    * rewrite !(nd_getrZ _ (21%bv : bv 5) 21 eq_refl), P21. exact A62.
    * rewrite !(nd_getrZ _ (22%bv : bv 5) 22 eq_refl), P22. exact A63.
    * rewrite !(nd_getrZ _ (23%bv : bv 5) 23 eq_refl), P23. exact A64.
    * rewrite !(nd_getrZ _ (24%bv : bv 5) 24 eq_refl), P24. exact A65.
    * rewrite !(nd_getrZ _ (25%bv : bv 5) 25 eq_refl), P25. exact A25.
    * rewrite !(nd_getrZ _ (26%bv : bv 5) 26 eq_refl), P26. exact A26.
    * rewrite !(nd_getrZ _ (27%bv : bv 5) 27 eq_refl), P27. exact A27.
  + (* what the walk left untouched *)
    eapply (nd_edge_same _ W memc _ _ (spZ regs) tx chp parp valp (tx + 288 + i)
              G45 G10 G11 G12 G13 G47 FR2).
    eapply nd_meq_same; [exact MQ1|].
    apply nd_same_dd. exact HSAME.
  + intros a Ha. eapply nd_grows_pres; [exact GR2|].
    eapply nd_meq_pres; [exact MQ1|]. exact (HpresS a Ha).
  + intros a Ha. eapply nd_grows_pres; [exact GR2|].
    eapply nd_meq_pres; [exact MQ1|]. apply HpresK. exact Ha.
  + rewrite P10. cbn [sv_denot]. reflexivity.
  + (* the table *)
    apply (proj2 (tx_obj_bytes SEGS _ _ _)). intros kk Hkk.
    pose proof (HeadampTxEffective.tx_fbyte_range kk Hkk) as Hkr.
    destruct (Z.eq_dec kk (288 + i)) as [-> | Hne].
    * rewrite <- Z_to_bv8_tb.
      rewrite (tb_set4_out (setb T (288 + i) 0) 456 0 (288 + i)
                 ltac:(apply len_setb; [exact HTL | lia]) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite (tb_setb_in T (288 + i) 0 HTL ltac:(lia) ltac:(lia)).
      replace (tx + (288 + i)) with (tx + 288 + i + 0 + 0) by lia.
      rewrite BYd, nd_lit0, nd_byte0 by lia. reflexivity.
    * destruct (Z.le_gt_cases 456 kk) as [Hk456 | Hk456].
      -- rewrite <- Z_to_bv8_tb.
         replace kk with (456 + (kk - 456)) by lia.
         rewrite (tb_set4_in (setb T (288 + i) 0) 456 0 (kk - 456)
                    ltac:(apply len_setb; [exact HTL | lia]) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
         assert (Hj4 : kk - 456 = 0 \/ kk - 456 = 1 \/ kk - 456 = 2 \/ kk - 456 = 3) by lia.
         replace (tx + (456 + (kk - 456))) with (tx + 456 + (kk - 456)) by lia.
         rewrite (BYw (kk - 456) ltac:(lia)).
         destruct Hj4 as [-> | [-> | [-> | ->]]]; cbn [nth Z.to_nat]; reflexivity.
      -- rewrite <- Z_to_bv8_tb.
         rewrite (tb_set4_out (setb T (288 + i) 0) 456 0 kk
                    ltac:(apply len_setb; [exact HTL | lia]) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
         rewrite (tb_setb_out T (288 + i) 0 kk HTL ltac:(lia) ltac:(lia) ltac:(lia)).
         rewrite Z_to_bv8_tb.
         rewrite (nd_edge_keep _ W _ _ (spZ regs) tx chp parp valp (tx + 288 + i) (tx + kk)
                    G45 G10 G11 G12 G13 G47 FR2
                    ltac:(clear - Hkr Hg4096 Hgceil C1; lia) ltac:(clear - Hk456; lia)
                    ltac:(clear - Hkr Hoc; destruct Hoc as (_ & _ & Hc2 & _); unfold TX_SIZE in Hc2; lia)
                    ltac:(clear - Hkr Hop; destruct Hop as (_ & _ & Hp2 & _); unfold TX_SIZE in Hp2; lia)
                    ltac:(clear - Hkr Hov; destruct Hov as (_ & _ & Hv2 & _); unfold TX_SIZE in Hv2; lia)
                    ltac:(clear - Hne; lia)).
         rewrite (nd_meq_mbyte W memj _ (tx + kk) MQ1).
         exact (proj1 (tx_obj_bytes SEGS _ _ _) HOBJ kk Hkk).
  + (* the three bytes the caller holds *)
    intros _. split; [| split].
    * apply (nd_byte_aview W _ chp (i / 3));
        [ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia] |].
      replace chp with (chp + 0 + 0) by lia. rewrite BYc.
      rewrite (q3_denot _ i K46 ltac:(lia)). reflexivity.
    * apply (nd_byte_aview W _ parp (i mod 3));
        [ pose proof (Z.mod_pos_bound i 3 ltac:(lia)); lia |].
      replace parp with (parp + 0 + 0) by lia. rewrite BYp.
      rewrite (proj1 (rm_denot _ i K46 ltac:(lia))). reflexivity.
    * apply (nd_byte_aview W _ valp (tb T i)); [lia |].
      replace valp with (valp + 0 + 0) by lia. rewrite BYv.
      cbn [sv_denot]. rewrite K50, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- (* the cell is clean: the scan steps to the next one *)
  rewrite branch_ne_U, (U_atom _ 49 _ F49), U_lit in Hc by lia.
  rewrite negb_false_iff in Hc. apply Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ SHOK BspanN; [apply nd_ro_awr; exact nd_ro_regs |].
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
      pose proof (nd_ro_frame _ _ W m1 m2 nd_ro_regs HFr) as MQ2
  end.
  nd_clr.
  ndenv HE1 HE2.
  pose proof HE2 as (K45 & K10 & K11 & K12 & K13 & K32 & K46 & K47 & K48 & K49 & K50 &
    K56 & K57 & K58 & K59 & K60 & K61 & K62 & K63 & K64 & K65 & K3 & K4 & K25 & K26 & K27).
  psrr_branch_tok RUN BR HS SHOK BspanN;
  [ lazymatch goal with H : branch_taken BC_EQ _ _ = true |- _ => rename H into HcB end
  | lazymatch goal with H : branch_taken BC_EQ _ _ = false |- _ => rename H into HcB end ].
  + (* the scan has run out: the walk goes on at AFTR *)
    rewrite branch_eq_U, (U_atom_off _ 46 i 1 K46 ltac:(lia) ltac:(lia)), U_lit in HcB by lia.
    apply Z.eqb_eq in HcB.
    paj_run_to_tok RUNTO HS HJ SHOK BspanN AFTR; [apply nd_ro_awr; exact nd_ro_regs |].
    lazymatch goal with
    | HFr : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
        pose proof (nd_ro_frame _ _ W m1 m2 nd_ro_regs HFr) as MQ3
    end.
    nd_clr.
    ndenv HE2 HE3.
    pose proof HE3 as (L45 & L10 & L11 & L12 & L13 & L32 & L46 & L47 & L48 & L49 & L50 &
      L56 & L57 & L58 & L59 & L60 & L61 & L62 & L63 & L64 & L65 & L3 & L4 & L25 & L26 & L27).
    pose proof (nd_uenv _ regs (spZ regs) tx chp parp valp i T HE3
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HU3.
    pose proof HU3 as (M45 & M10 & M11 & M12 & M13 & M32 & M46 & M47 & M48 & M49 & M50).
    prreg HS (2%bv : bv 5) P2. prreg HS (5%bv : bv 5) P5.
    prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
    prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13.
    prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
    pmkst HS.
    lazymatch goal with
    | |- SRr _ _ (mkCfg (mkst ?rgA _ ?mmA _) ?mdA) _ => apply (KAFTR rgA mmA mdA)
    end.
    * split; [exact HJ|]. split.
      -- eapply nd_meq_same; [exact MQ3|]. eapply nd_meq_same; [exact MQ2|].
         eapply nd_meq_same; [exact MQ1|]. exact HSAME.
      -- split.
         ++ intros a Ha. eapply nd_meq_pres; [exact MQ3|]. eapply nd_meq_pres; [exact MQ2|].
            eapply nd_meq_pres; [exact MQ1|]. apply HpresS. exact Ha.
         ++ intros a Ha. eapply nd_meq_pres; [exact MQ3|]. eapply nd_meq_pres; [exact MQ2|].
            eapply nd_meq_pres; [exact MQ1|]. apply HpresK. exact Ha.
    * eapply nd_meq_saved; [exact MQ3|]. eapply nd_meq_saved; [exact MQ2|].
      eapply nd_meq_saved; [exact MQ1|]. exact HSAV.
    * intros r Hr. cbn [In] in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]].
      -- rewrite P3. exact A3.
      -- rewrite P4. exact A4.
      -- rewrite P25. exact A25.
      -- rewrite P26. exact A26.
      -- rewrite P27. exact A27.
    * eapply nd_meq_obj; [exact MQ3|]. eapply nd_meq_obj; [exact MQ2|].
      eapply nd_meq_obj; [exact MQ1|]. exact HOBJ.
    * intros l Hl. destruct (Z.eq_dec l i) as [-> | Hne]; [exact Hc | apply Hz; lia].
    * rewrite P2, AU45. unfold w64; f_equal; try lia.
    * rewrite P5. exact A32.
    * rewrite P10. exact A10.
    * rewrite P11. exact A11.
    * rewrite P12. exact A12.
    * rewrite P13. exact A13.
  + (* the scan steps: the next cell *)
    rewrite branch_eq_U, (U_atom_off _ 46 i 1 K46 ltac:(lia) ltac:(lia)), U_lit in HcB by lia.
    apply Z.eqb_neq in HcB.
    paj_run_to_tok RUNTO HS HJ SHOK BspanN LOOPD; [apply nd_ro_awr; exact nd_ro_regs |].
    lazymatch goal with
    | HFr : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
        pose proof (nd_ro_frame _ _ W m1 m2 nd_ro_regs HFr) as MQ3
    end.
    nd_clr.
    ndenv HE2 HE3.
    pose proof HE3 as (L45 & L10 & L11 & L12 & L13 & L32 & L46 & L47 & L48 & L49 & L50 &
      L56 & L57 & L58 & L59 & L60 & L61 & L62 & L63 & L64 & L65 & L3 & L4 & L25 & L26 & L27).
    pose proof (nd_uenv _ regs (spZ regs) tx chp parp valp i T HE3
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HU3.
    pose proof HU3 as (M45 & M10 & M11 & M12 & M13 & M32 & M46 & M47 & M48 & M49 & M50).
    prreg HS (2%bv : bv 5) P2. prreg HS (5%bv : bv 5) P5.
    prreg HS (7%bv : bv 5) P7. prreg HS (28%bv : bv 5) P28.
    prreg HS (29%bv : bv 5) P29. prreg HS (30%bv : bv 5) P30.
    prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
    prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13.
    prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
    pmkst HS.
    lazymatch goal with
    | |- SRr _ _ (mkCfg (mkst ?rgA _ ?mmA _) ?mdA) _ =>
      apply (IH STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rgA mmA mdA
               tx chp parp valp T (i + 1))
    end.
    * exact HCTX.
    * split; [exact HJ|]. split.
      -- eapply nd_meq_same; [exact MQ3|]. eapply nd_meq_same; [exact MQ2|].
         eapply nd_meq_same; [exact MQ1|]. exact HSAME.
      -- split.
         ++ intros a Ha. eapply nd_meq_pres; [exact MQ3|]. eapply nd_meq_pres; [exact MQ2|].
            eapply nd_meq_pres; [exact MQ1|]. apply HpresS. exact Ha.
         ++ intros a Ha. eapply nd_meq_pres; [exact MQ3|]. eapply nd_meq_pres; [exact MQ2|].
            eapply nd_meq_pres; [exact MQ1|]. apply HpresK. exact Ha.
    * eapply nd_meq_saved; [exact MQ3|]. eapply nd_meq_saved; [exact MQ2|].
      eapply nd_meq_saved; [exact MQ1|]. exact HSAV.
    * eapply nd_meq_obj; [exact MQ3|]. eapply nd_meq_obj; [exact MQ2|].
      eapply nd_meq_obj; [exact MQ1|]. exact HOBJ.
    * exact HACT.
    * lia.
    * lia.
    * intros l Hl. destruct (Z.eq_dec l i) as [-> | Hne]; [exact Hc | apply Hz; lia].
    * exact KAFTR.
    * intros r Hr. cbn [In] in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]].
      -- rewrite P3. exact A3.
      -- rewrite P4. exact A4.
      -- rewrite P25. exact A25.
      -- rewrite P26. exact A26.
      -- rewrite P27. exact A27.
    * rewrite P2, AU45. unfold w64; f_equal; try lia.
    * rewrite P5. exact A32.
    * rewrite P7, AU46. unfold w64; f_equal; try lia.
    * rewrite P28, AU10. unfold w64; f_equal; try lia.
    * rewrite P29. cbn [sv_denot]. reflexivity.
    * rewrite P30. cbn [sv_denot]. reflexivity.
    * rewrite P10. exact A10.
    * rewrite P11. exact A11.
    * rewrite P12. exact A12.
    * rewrite P13. exact A13.
Qed.

End h.
End f.
End d.
