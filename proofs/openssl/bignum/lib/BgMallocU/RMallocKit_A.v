(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.openssl.bignum.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Export MallocKit_A.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma rmrep_wr32 : forall st m p v r,
  rmrep st m -> ticks_ok st ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup -> 0 <= snd p -> snd p + 4 <= round_up_pg (r_len r) ->
  (forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> snd p + 4 <= snd b \/ snd b + 9 <= snd p) ->
  0 <= v < 2^32 ->
  rmrep (wr32 p v st) (write_to_mem m (wa (r_base r + snd p)) (le4 (wz v)))
  /\ ticks_ok (wr32 p v st).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m p v r MR TK Hr Hk H0 H4 Hg Hv.
  rewrite le4_bytes by lia.
  change (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256); b8 ((v / 256) mod 256); b8 ((v / 65536) mod 256); b8 (v / 16777216)])
    with (write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)])
            (wa (r_base r + snd p) + 1) [b8 ((v / 256) mod 256)]) (wa (r_base r + snd p) + 1 + 1) [b8 ((v / 65536) mod 256)])
            (wa (r_base r + snd p) + 1 + 1 + 1) [b8 (v / 16777216)]).
  rewrite !wa_succ.
  unfold wr32.
  assert (E1 : forall q w stx, wr8 q w stx = wr8 q (w mod 256) stx) by (intros; apply wr8_mod).
  rewrite (E1 p v), (E1 (aadd p 1) (Z.shiftr v 8)), (E1 (aadd p 2) (Z.shiftr v 16)), (E1 (aadd p 3) (Z.shiftr v 24)).
  rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216.
  rewrite (Z.mod_small (v / 16777216) 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (B0 : 0 <= v mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (B1 : 0 <= (v / 256) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (B2 : 0 <= (v / 65536) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (B3 : 0 <= v / 16777216 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (S1 : rmrep (wr8 p (v mod 256) st) (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) /\ ticks_ok (wr8 p (v mod 256) st)).
  { split; [|apply ticks_ok_wr8; exact TK]. apply (rmrep_wr8 st m p _ r MR TK Hr Hk); [lia| |lia].
    intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
  destruct S1 as [M1 T1].
  assert (S2 : rmrep (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)) (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p + 1)) [b8 ((v / 256) mod 256)])
               /\ ticks_ok (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st))).
  { split; [|apply ticks_ok_wr8; exact T1].
    replace (r_base r + snd p + 1) with (r_base r + snd (aadd p 1)) by (cbn; lia).
    apply (rmrep_wr8 _ _ (aadd p 1) _ r M1 T1); cbn; [exact Hr| exact Hk| lia| |lia].
    intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
  destruct S2 as [M2 T2].
  assert (S3 : rmrep (wr8 (aadd p 2) ((v / 65536) mod 256) (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)))
                    (write_to_mem (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p + 1)) [b8 ((v / 256) mod 256)]) (wa (r_base r + snd p + 1 + 1)) [b8 ((v / 65536) mod 256)])
               /\ ticks_ok (wr8 (aadd p 2) ((v / 65536) mod 256) (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)))).
  { split; [|apply ticks_ok_wr8; exact T2].
    replace (r_base r + snd p + 1 + 1) with (r_base r + snd (aadd p 2)) by (cbn; lia).
    apply (rmrep_wr8 _ _ (aadd p 2) _ r M2 T2); cbn; [exact Hr| exact Hk| lia| |lia].
    intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
  destruct S3 as [M3 T3].
  split; [|apply ticks_ok_wr8; exact T3].
  replace (r_base r + snd p + 1 + 1 + 1) with (r_base r + snd (aadd p 3)) by (cbn; lia).
  apply (rmrep_wr8 _ _ (aadd p 3) _ r M3 T3); cbn; [exact Hr| exact Hk| lia| |lia].
  intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia.
Qed.

Lemma rauxv_ok_pres : forall C m m' B,
  rauxv_ok m B -> rpres_except C m m' ->
  (forall a, B <= a -> ~ C a) -> (forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> ~ C a) ->
  rauxv_ok m' B.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros C m m' B (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C1 & A1 & A2 & H) HP HB HC.
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rpres_except_rw_cells; [exact HP| exact C1|]. cbn. intros a Ha. apply HC. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A1|]. intros a Ha. apply HB. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A2|]. intros a Ha. apply HB. lia.
Qed.

Lemma rpres_write : forall (C : Z -> Prop) m0 m a bs,
  rpres_except C m0 m -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> C x) ->
  rpres_except C m0 (write_to_mem m (wa a) bs).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros C m0 m a bs HP Ha Hl HC x Hx HCx.
  destruct (HP x Hx HCx) as [E W].
  assert (NE : write_to_mem m (wa a) bs (wa x) = m (wa x)).
  { rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
    destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
    exfalso. apply HCx, HC. lia. }
  split.
  - rewrite NE. exact E.
  - intros Hw. apply wview_write_mono. apply W, Hw.
Qed.

Lemma rpres_except_munch_frame : forall C m0 m m' W,
  rpres_except C m0 m -> munch W m m' -> wmono bgusegs m m' ->
  (forall x, 0 <= x < 2^64 -> ~ C x -> outside W x) -> rpres_except C m0 m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros C m0 m m' W HP MU WM HW. eapply rpres_except_trans; [exact HP|]. eapply rpres_except_of_munch; eauto.
Qed.
End WithCeiling0.
