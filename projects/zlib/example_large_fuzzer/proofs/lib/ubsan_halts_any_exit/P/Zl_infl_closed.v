(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate HarnessSmall ZApiInst ZApiInstL.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefZApi RefInflateRel RefInflateSafeD RefInflateSafeS2 RefInflateEqS RefInflateEqB RefInflateEqU
  InflateCall ZTaintI DeflateSafe DeflateTaintTop ZApiOk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.MallocP Require Import RMallocRep RMalloc_iface RMalloc_ifaceP RF_free_spec.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Malloc Monad Stdio ZApi ZHarness ZInst ZTarget ZApiL ZHarnessL ZInstL ZTargetL Target Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd Layout Zlib_iface Z_irep Zg_zlib_iface Zg_zlib_infl_closed Zl_iend Zl_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Transparent the_zapiL the_zapi.

Notation mem := (word -> option byte).


Lemma zcall_eq : forall comprc (x : istream) cl aout,
  ZIface.zlength comprc = cl -> 0 <= zs_total_in (iz_z x) <= cl ->
  zi_zcall comprc x (cl - zs_total_in (iz_z x)) aout = mkZCall (zdrop (zs_total_in (iz_z x)) comprc) aout (iz_z x).
Proof.
  intros comprc x cl aout L T. unfold zi_zcall. f_equal. unfold zfirstn, zdrop, zskipn. apply firstn_all2.
  rewrite length_skipn. unfold ZIface.zlength in L. lia.
Qed.

Lemma il_inflate_eq : forall comprc (x : istream) cl aout ok,
  ZIface.zlength comprc = cl -> 0 <= zs_total_in (iz_z x) <= cl ->
  zi_inflate comprc x (cl - zs_total_in (iz_z x)) aout ok
  = (let '(x', consumed, bs, rc) := zil_inflate (zdrop (zs_total_in (iz_z x)) comprc) x aout ok in
     (x', cl - zs_total_in (iz_z x) - consumed, aout - ZIface.zlength bs, bs, rc)).
Proof.
  intros comprc x cl aout ok L T. unfold zi_inflate, zil_inflate. rewrite (zcall_eq comprc x cl aout L T). cbn [zc_input].
  lazymatch goal with |- context [inflate_p ?a ?s ?c ?f] => destruct (inflate_p a s c f) as [[s' zr] asked] end.
  f_equal. f_equal. f_equal. f_equal. unfold ZIface.zlength, zdrop. rewrite length_skipn. unfold ZIface.zlength in L. lia.
Qed.

Lemma il_wants_eq : forall comprc (x : istream) cl aout,
  ZIface.zlength comprc = cl -> 0 <= zs_total_in (iz_z x) <= cl ->
  zi_wantsG comprc x (cl - zs_total_in (iz_z x)) aout = zil_wants_window (zdrop (zs_total_in (iz_z x)) comprc) x aout.
Proof. intros comprc x cl aout L T. unfold zi_wantsG, zil_wants_window. rewrite (zcall_eq comprc x cl aout L T). reflexivity. Qed.

Lemma il_inflate_facts : forall inp (x : istream) aout ok,
  INV (iz_s x) -> bytes_ok inp -> ZIface.zlength inp < 2 ^ 32 -> 0 <= aout < 2 ^ 32 ->
  let '(x', consumed, bs, rc) := zil_inflate inp x aout ok in
  INV (iz_s x') /\ 0 <= ZIface.zlength bs <= aout
  /\ (rc = ZIface.Z_OK \/ rc = ZIface.Z_STREAM_END -> zs_total_out (iz_z x') = wrap64 (zs_total_out (iz_z x) + ZIface.zlength bs))
  /\ (rc = ZIface.Z_OK -> 0 <= consumed <= ZIface.zlength inp /\ zs_total_in (iz_z x') = wrap64 (zs_total_in (iz_z x) + consumed)).
Proof.
  intros inp x aout ok HI Hb Hl Ha. unfold zil_inflate.
  set (zc := mkZCall inp aout (iz_z x)).
  assert (Hz : ZC zc) by (unfold ZC, zc; cbn [zc_avail_out zc_input]; repeat split; try lia; exact Hb).
  pose proof (inflate_p_pure (wans ok) (iz_s x) zc ZIface.Z_NO_FLUSH (INV_check _ HI)) as EP.
  destruct (inflate_p (wans ok) (iz_s x) zc ZIface.Z_NO_FLUSH) as [[s' zr] asked] eqn:EIP. cbn [fst] in EP.
  pose proof (inflate_m_post ZIface.Z_NO_FLUSH (iz_s x) zc (wans ok) (s', zr) HI Hz EP) as (P1 & P2).
  pose proof (inflate_m_post2 ZIface.Z_NO_FLUSH (iz_s x) zc (wans ok) (s', zr) HI Hz EP) as (Q1 & _).
  cbn [fst snd iz_s iz_z] in *.
  split; [exact (inflate_INV' (iz_s x) zc ZIface.Z_NO_FLUSH (wans ok) s' zr HI Hz EP)|].
  split; [exact P1|]. split; [exact P2|].
  intros E. destruct (Q1 E) as (C1 & C2 & _). split; [exact C1| exact C2].
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.


Definition zr_iL (m : mem) (S : Z) (LBz : list block) (x : ISL the_zapiL) : Prop := zr_i_def m S LBz x.

Lemma zr_iL_frame : forall m m' S LBz is, zr_iL m S LBz is ->
  (forall a, 0 <= a < 2^64 -> (S + ZS_PUB <= a < S + ZS_SIZEOF \/ in_block LBz a) ->
     m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None)) ->
  zr_iL m' S LBz is.
Proof. exact zr_i_def_frame. Qed.
Lemma zr_iL_stream : forall m S LBz is, zr_iL m S LBz is -> exists j : list byte, rw_cells psegs m (S + ZS_PUB) [CB 64 j].
Proof. exact zr_i_def_stream. Qed.

Lemma zr_iL_INV : forall m S LBz (x : istream), zr_i_def m S LBz x -> INV (iz_s x).
Proof. intros m S LBz x (s_a & L & w & sp_ & _ & _ & _ & _ & HI & _ & _). destruct HI as (_ & _ & _ & H). exact H. Qed.

Definition zdF (m : mem) (S : Z) (LBz : list block) (x : DS the_zapi) : Prop := False.
Lemma zdF_frame : forall m m' S LBz ds, zdF m S LBz ds ->
  (forall a, 0 <= a < 2^64 -> (S + ZS_PUB <= a < S + ZS_SIZEOF \/ in_block LBz a) ->
     m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None)) ->
  zdF m' S LBz ds.
Proof. intros m m' S LBz ds []. Qed.
Lemma zdF_stream : forall m S LBz ds, zdF m S LBz ds -> exists j : list byte, rw_cells psegs m (S + ZS_PUB) [CB 64 j].
Proof. intros m S LBz ds []. Qed.
Definition Rs : zreps := mkZreps zdF zr_i_def zdF_frame zr_i_def_frame zdF_stream zr_i_def_stream.

Local Ltac records := cbn [ZApiL.ISL ZApiL.il_total_in ZApiL.il_total_out ZApiL.il_init ZApiL.il_end ZApiL.il_inflate ZApiL.il_wants_window
                           ZApiL.zl_isize ZApiL.zl_wsize the_zapiL zinstL
                           ZApi.IS ZApi.i_total_in ZApi.i_total_out ZApi.i_init ZApi.i_end ZApi.i_inflate ZApi.i_wants_window
                           ZApi.z_isize ZApi.z_wsize the_zapi zinst];
                      try unfold iblocksL; try unfold iblocks; cbn [app].
Local Ltac records_in H := cbn [ZApiL.ISL ZApiL.il_total_in ZApiL.il_total_out ZApiL.il_init ZApiL.il_end ZApiL.il_inflate ZApiL.il_wants_window
                                ZApiL.zl_isize ZApiL.zl_wsize the_zapiL zinstL
                                ZApi.IS ZApi.i_total_in ZApi.i_total_out ZApi.i_init ZApi.i_end ZApi.i_inflate ZApi.i_wants_window
                                ZApi.z_isize ZApi.z_wsize the_zapi zinst] in H;
                           try unfold iblocksL in H; try unfold iblocks in H; cbn [app] in H.

Section Bridge.
  Variable RL : zrepsL.
  Hypothesis ERL : zri RL = zr_iL.

  Lemma inflateInit_L : inflateInit_stmt Rs -> inflateInit_stmtL RL.
  Proof.
    intros II. unfold inflateInit_stmtL. intros until canary. intros ENV CELLS SIF LOSP SP16 FRM HA0 HA1 HA2.
    eapply implM_mono.
    { exact (II ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB S ni ai ti no ao to p1 p2 jmsg jstate jrest
                lo B errv canary ENV CELLS SIF LOSP SP16 FRM HA0 HA1 HA2). }
    intros r s' ms' PO. unfold inflateInit_post in PO. unfold inflateInit_postL.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & m' & EMS & PO).
    exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F', fc', m'. split; [exact EMS|].
    destruct r as [p|]; [| exact PO].
    destruct PO as (As & LPE & A0 & PUB & ZR). exists As. split; [exact LPE|]. split; [exact A0|].
    split; [rewrite (proj1 (zo_iinitL _ the_zapiL_ok)), (proj2 (zo_iinitL _ the_zapiL_ok)); exact PUB|].
    rewrite ERL. exact ZR.
  Qed.

  Lemma inflateEnd_L : inflateEnd_stmtX Rs -> inflateEnd_stmtL RL.
  Proof.
    intros IE. unfold inflateEnd_stmtL. intros until canary. intros ENV PUB ZR SIF LOSP SP16 FRM HA0.
    rewrite ERL in ZR. pose proof (zr_iL_INV _ _ _ _ ZR) as HINV.
    eapply implM_mono.
    { exact (IE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB S is w Aw sp_ As
                ni ai ti no ao to p1 p2 lo B errv canary ENV PUB ZR SIF LOSP SP16 FRM HA0). }
    intros [] s' ms' PO. unfold inflateEnd_postX in PO. unfold inflateEnd_postL.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & m' & EMS & LPE & A0 & HJ).
    exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F', fc', m'. split; [exact EMS|]. split; [exact LPE|].
    split; [| exact HJ]. rewrite A0. records. rewrite (iend_rc_INV _ HINV). reflexivity.
  Qed.

  Lemma inflate_L : inflate_stmtG Rs -> inflate_stmtL RL.
  Proof.
    intros IG. unfold inflate_stmtL. intros until canary.
    intros ENV PUB ZR HC CARR CCL CBY HU UARR ULEN TIN CL SZ TOUT TOUT63 CU SIF LOSP SP16 FRM HA0 HA1.
    rewrite ERL in ZR. pose proof (zr_iL_INV _ _ _ _ ZR) as HINV.
    pose proof (IG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB S C U cl size comprc uc is
                (cl - il_total_in the_zapiL is) 0 size w Aw sp_ As p1 p2 lo B errv canary) as G.
    unfold inflate_postG in G. unfold i_okG in G. unfold i_windowG in G. unfold i_wantsG in G. records_in G.
    rewrite (Z.add_0_r U) in G.
    unfold zr_iL in *. unfold i_okL. unfold i_windowL. unfold i_wantsbL. records.
    records_in TIN. records_in TOUT. records_in TOUT63. records_in PUB. records_in ZR. records_in ENV.
    assert (CCL' : ZIface.zlength comprc = cl) by exact CCL.
    assert (LD : ZIface.zlength (zdrop (zs_total_in (iz_z is)) comprc) = cl - zs_total_in (iz_z is)).
    { unfold ZIface.zlength, zdrop. rewrite length_skipn. unfold ZIface.zlength in CCL'. lia. }
    rewrite (il_wants_eq comprc is cl size CCL' TIN) in G.
    specialize (G ENV PUB ZR HC CARR CCL CBY HU UARR ULEN ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  CU SIF LOSP SP16 FRM HA0 HA1).
    eapply implM_mono; [exact G|].
    intros r s' ms' PO. unfold inflate_postL. unfold i_okL. unfold i_windowL. unfold i_wantsbL. records.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & m' & p1' & p2' & Aw' & ni' & PO).
    rewrite (il_inflate_eq comprc is cl size _ CCL' TIN) in PO.
    pose proof (il_inflate_facts (zdrop (zs_total_in (iz_z is)) comprc) is size
                  (if zil_wants_window (zdrop (zs_total_in (iz_z is)) comprc) is size && match w with Some _ => false | None => true end
                   then match r with Some _ => true | None => false end else true)
                  HINV (bytes_okP_zskipn' _ _ CBY) ltac:(lia) ltac:(lia)) as FACTS.
    destruct (zil_inflate (zdrop (zs_total_in (iz_z is)) comprc) is size
               (if zil_wants_window (zdrop (zs_total_in (iz_z is)) comprc) is size && match w with Some _ => false | None => true end
                then match r with Some _ => true | None => false end else true)) as [[[is' consumed] bs] rc].
    cbv beta iota zeta in PO. cbv beta iota zeta in FACTS.
    destruct PO as (EMS & LPE & AWE & A0 & PUB' & NIE & ZR' & UARR').
    destruct FACTS as (HINV' & BSR & TOE & OKE).
    exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F', fc', m', p1', p2', Aw', ni', (cl - zs_total_in (iz_z is) - consumed).
    split; [exact EMS|]. split; [exact LPE|]. split; [exact AWE|]. split; [exact A0|].
    split; [unfold zlength; unfold ZIface.zlength in BSR; lia|].
    split; [exact PUB'|].
    split. { intros E. destruct (OKE E) as (C1 & C2). rewrite C2, wrap64_id by lia. split; [| lia]. rewrite (NIE E), C2, wrap64_id by lia. reflexivity. }
    split. { intros E. rewrite (TOE E). unfold zlength. unfold ZIface.zlength in BSR |- *. apply wrap64_id. lia. }
    split; [rewrite ERL; exact ZR'| exact UARR'].
  Qed.
End Bridge.

Theorem zlib_infl_closedL : forall RL : zrepsL, zri RL = zr_iL ->
  inflateInit_stmtL RL /\ inflate_stmtL RL /\ inflateEnd_stmtL RL.
Proof.
  intros RL ERL. destruct (zlib_infl_closedG Rs eq_refl) as (II & IG & _).
  split; [exact (inflateInit_L RL ERL II)|]. split; [exact (inflate_L RL ERL IG)|].
  exact (inflateEnd_L RL ERL (inflateEnd_okX rfree_spec_proof RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof Rs eq_refl)).
Qed.
End WithCeiling0.
