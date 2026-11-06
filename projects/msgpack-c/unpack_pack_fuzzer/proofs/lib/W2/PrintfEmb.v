(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AKit AKit2 ARep ARepKit ABytes AFrameD RT_stubs. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammapz. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_aunmap AMalloc_iface AEmbRep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val Instr State StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require Import SegL PrintfFmt2 PrintfSeg2 PrintfRegs F_mmapordie F_embrealloc F_embappend F_printf_tail.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC2. Context {rc : runConstT}.

Definition emb_fresh (RESV : list (Z * Z)) (st : astate) (ncap mb : Z) : bool :=
  mmap_answer_ok ATOP ncap mb && negb (is_err mb) && avoids_all mb ncap (RESV ++ asec_ranges st).

Definition KR {R} (RESV : list (Z * Z)) (st : astate) (want : Z) (k : astate -> AM R) (mb : Z) : itree node (exc R) :=
  let '(d, cap, sz) := a_emb st in
  let ncap := rup want PG in
  aembed ATOP (if negb (mmap_answer_ok ATOP ncap mb) then aundef_ UBadAnswer (k st)
               else if is_err mb then aundef_ USpin (k st)
               else if negb (avoids_all mb ncap (RESV ++ asec_ranges st)) then aundef_ UBadAnswer (k st)
               else let st1 := set_emb (mb, ncap, sz) st in
                    if cap =? 0 then k st1 else
                    ev (AMunmap d cap) (fun r => if r =? 0 then k st1 else if is_err r then aundef_ USpin (k st1) else aundef_ UBadAnswer (k st1))).

Lemma aembed_emb_realloc : forall {R} RESV st want (k : astate -> AM R),
  aembed ATOP (emb_realloc ATOP RESV st want k)
  = ebind (enode (NMmap 0 (rup want PG) 3 34) (adec_mmap ATOP (rup want PG) 3)) (KR RESV st want k).
Proof.
  intros R RESV st want k. unfold emb_realloc, KR. destruct (a_emb st) as [[d cap] sz]. unfold ev. rewrite aembed_vis. reflexivity.
Qed.

Lemma KR_unr : forall {R} RESV st want (k : astate -> AM R) mb, emb_fresh RESV st (rup want PG) mb = false -> KR RESV st want k mb = Ret Unr.
Proof.
  intros R RESV st want k mb H. unfold KR, emb_fresh in *. destruct (a_emb st) as [[d cap] sz].
  destruct (mmap_answer_ok ATOP (rup want PG) mb); [| reflexivity]. destruct (is_err mb); [reflexivity|].
  cbn [negb andb] in H. rewrite H. reflexivity.
Qed.

Lemma KR_fresh0 : forall {R} RESV st want (k : astate -> AM R) mb d sz, a_emb st = (d, 0, sz) ->
  emb_fresh RESV st (rup want PG) mb = true -> KR RESV st want k mb = aembed ATOP (k (set_emb (mb, rup want PG, sz) st)).
Proof.
  intros R RESV st want k mb d sz E H. unfold KR, emb_fresh in *. rewrite E.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. rewrite H1. destruct (is_err mb); [discriminate H2|]. rewrite H3. reflexivity.
Qed.

Lemma KR_fresh1 : forall {R} RESV st want (k : astate -> AM R) mb d cap sz, a_emb st = (d, cap, sz) -> cap <> 0 ->
  emb_fresh RESV st (rup want PG) mb = true ->
  KR RESV st want k mb = ebind (enode (NMunmap d cap) (adec_munmap d cap))
                               (fun r => aembed ATOP (if r =? 0 then k (set_emb (mb, rup want PG, sz) st)
                                                      else if is_err r then aundef_ USpin (k (set_emb (mb, rup want PG, sz) st))
                                                      else aundef_ UBadAnswer (k (set_emb (mb, rup want PG, sz) st)))).
Proof.
  intros R RESV st want k mb d cap sz E NZ H. unfold KR, emb_fresh in *. rewrite E.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. rewrite H1. destruct (is_err mb); [discriminate H2|]. rewrite H3.
  cbn [negb]. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). unfold ev. rewrite aembed_vis. reflexivity.
Qed.

Lemma emb_fresh_facts : forall L RESV st ncap mb d cap sz,
  emb_fresh RESV st ncap mb = true -> aresv_ok L RESV -> a_emb st = (d, cap, sz) -> ncap mod 4096 = 0 -> 65536 <= ncap ->
  0 < mb /\ mb mod 4096 = 0 /\ mb + ncap <= ATOP /\ AIMG_HI <= mb /\ (cap <> 0 -> mb + ncap <= d \/ d + cap <= mb) /\ avoids_all mb ncap (RESV ++ asec_ranges st) = true.
Proof.
  intros L RESV st ncap mb d cap sz H ROK E NCM NCB. unfold emb_fresh in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  assert (E2 : is_err mb = false) by (destruct (is_err mb); [discriminate| reflexivity]).
  unfold mmap_answer_ok in H1. rewrite E2 in H1. cbn [orb] in H1.
  apply andb_prop in H1 as [H1 H9]. apply andb_prop in H1 as [H1 H8]. apply andb_prop in H1 as [H6 H7].
  apply Z.ltb_lt in H6. apply Z.eqb_eq in H7. apply Z.leb_le in H8. apply Z.ltb_lt in H9.
  assert (RU : rup ncap PG = ncap) by (unfold rup, PG; clear -NCM NCB; Z.div_mod_to_equations; lia). rewrite RU in H8. change PG with 4096 in H7.
  pose proof H3 as H30. unfold avoids_all in H3. rewrite forallb_app in H3. apply andb_prop in H3 as [H4 H5].
  destruct ROK as (R1 & _).
  pose proof (pcov_clear _ _ _ _ _ R1 H4 ltac:(unfold AIMG_HI; clear; lia) ltac:(clear -NCB; lia)) as C1.
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [clear -C1 H6 NCB; lia|]. split; [| exact H30].
  intros NZ. unfold asec_ranges in H5. rewrite forallb_app in H5. apply andb_prop in H5 as [_ H5].
  unfold emb_iv in H5. rewrite E in H5. replace (cap =? 0) with false in H5 by (symmetry; apply Z.eqb_neq; exact NZ).
  cbn [forallb] in H5. apply andb_prop in H5 as [H5 _]. unfold iv_clear in H5. cbn [fst snd] in H5.
  apply orb_prop in H5. destruct H5 as [H5|H5]; apply Z.leb_le in H5; lia.
Qed.

Definition pr_ret (RESV : list (Z * Z)) (sp : word) (lo : Z) (RNG : footprint) (st : astate) (m : amem) (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let '(d0, cap0, _) := a_emb st in let '(d2, cap2, _) := a_emb st2 in
  fp_le RNG RNG'
  /\ (exists e2, st2 = set_emb e2 st)
  /\ emb_cells st2 m' /\ emb_rng st2 RNG' /\ exh_cells m' /\ arelro m'
  /\ munch [(bv_unsigned sp - 1280, bv_unsigned sp); (AEMB, AEMB + 56); (d0, d0 + cap0); (d2, d2 + cap2)]%Z m m'
  /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
  /\ cap2 <= Z.max 65536 (cap0 + 8192)
  /\ ((d2 = d0 /\ cap2 = cap0 /\ cap0 <> 0) \/ avoids_all d2 cap2 (RESV ++ asec_ranges st) = true).

Lemma a_emb_set_emb : forall v st, a_emb (set_emb v st) = v. Proof. reflexivity. Qed.

Lemma printf_emb_spec : forall RNG {R} (RESV : list (Z * Z)) (k : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (RA FMT : int) (LEN : nat) (xf : FI.rf Val.sv) (L : alayout)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (st : astate) (lo : Z),
  PrintfFmt2.checkP RA FMT LEN xf = true -> FI.rf_get xf FI.X0 = Val.VL W64.wzero -> (1 <= LEN <= 400)%nat ->
  (forall r, rget (StepB.core_of
                (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x733e0) fc None m (seg_rom asegs)))
             (St.reg_of_r5 r)
             = Val.den (SegL.envW (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F fc) (FI.rf_get xf r)) ->
  bv_unsigned fc < 32 -> bv_unsigned sp < 2 ^ 63 ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 1280 ->
  mem_inv asegs m -> arelro m -> exh_cells m -> emb_cells st m -> aresv_ok L RESV ->
  (let '(_, cap0, _) := a_emb st in cap0 < 2 ^ 37) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> emb_rng st RNG ->
  (forall st2 RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      pr_ret RESV sp lo RNG st m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (k st2)) (epostF Q)
            (MS (mkR (Z_to_bv 64 (to_Z RA)) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc (Z_to_bv 64 (to_Z RA))) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (emb_append ATOP RESV st (Z.of_nat LEN) k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x733e0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros CHK HX0 LENB HR FC SPHI ST CEIL LO MI RELRO XC EC ROK CAPB RIMG RSTK RBUF KONT.
  word_range sp SPR. pose proof atop_range as ATR.
  iprefix.
  eapply evtF_cut.
  { eapply (PrintfSeg2.printf_fmt_seg RNG RA FMT LEN xf CHK HX0 ltac:(clear -LENB; lia) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo).
    - exact HR.
    - exact FC.
    - exact SPHI.
    - exact ST.
    - exact LO.
    - clear -CEIL ATR. lia.
    - exact MI.
    - exact RELRO.
    - eapply rng_sub'; [exact RSTK|]. clear -LO SPR. lia.
    - exact RIMG. }
  intros ms1 PO.
  destruct PO as (ra' & t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & s4' & s5' & s6' & s7' & s8' & s9' & t3' & t4' & t5' & t6' & va & m1 & str
                  & -> & MU1 & WM1 & MI1 & ST1 & SL0 & SL1 & SL2 & SL3 & SLEN & SNZ & SB).
  apply evtF_done.

  destruct XC as (RC & TN & CF64 & CBC). destruct RC as (GPG & PGSZ & GOT & DPM & MLIM).
  assert (WCL : forall A n, 0 <= A -> A + n <= bv_unsigned sp - 1280 -> disjoint_from [(bv_unsigned sp - 1280, bv_unsigned sp)]%Z A n) by (intros A n H1 H2; cbn [disjoint_from fst snd]; split; [left; lia| exact I]).
  xport GPG MU1 WM1 ltac:(clear -LO CEIL ATR; lia). xport PGSZ MU1 WM1 ltac:(clear -LO CEIL ATR; lia). xport GOT MU1 WM1 ltac:(clear -LO CEIL ATR; lia).
  xport DPM MU1 WM1 ltac:(clear -LO CEIL ATR; lia). xport MLIM MU1 WM1 ltac:(clear -LO CEIL ATR; lia). xport TN MU1 WM1 ltac:(clear -LO CEIL ATR; lia).
  xport CF64 MU1 WM1 ltac:(clear -LO CEIL ATR; lia). xport CBC MU1 WM1 ltac:(clear -LO CEIL ATR; lia).
  assert (RC1 : rmap_cells m1) by (unfold rmap_cells; repeat (split; [assumption|]); assumption).
  assert (RELRO1 : arelro m1).
  { intros i Hi. rewrite (MU1 (wa i)); [apply RELRO; exact Hi|]. cbn [outside]. unfold ARELRO_LO, ARELRO_HI in Hi.
    split; [| exact I]. unfold wa. rewrite unsigned_lit by (clear -Hi; lia). clear -Hi LO CEIL ATR. lia. }
  unfold emb_cells in EC. unfold emb_rng in RBUF. unfold pr_ret in KONT.
  destruct (a_emb st) as [[d cap] sz] eqn:EA.
  destruct EC as [MTX EC]. change (AEMB + 16) with 0xd9338 in MTX. xport MTX MU1 WM1 ltac:(clear -LO CEIL ATR; lia).
  unfold emb_append. rewrite EA.
  set (len := Z.of_nat LEN) in *.
  assert (LENR : 1 <= len <= 400) by (subst len; clear -LENB; lia).
  destruct (cap =? 0) eqn:C0.
  -
    apply Z.eqb_eq in C0. subst cap. destruct EC as (PTR & SZ0 & VEC). subst sz.
    change AEMB with 0xd9328 in PTR. change (AEMB + 32) with 0xd9348 in VEC.
    xport PTR MU1 WM1 ltac:(clear -LO CEIL ATR; lia). xport VEC MU1 WM1 ltac:(clear -LO CEIL ATR; lia).
    rewrite aembed_emb_realloc. change (rup EMB_INIT PG) with 65536.
    eapply (printf_first_tail RNG (KR RESV st EMB_INIT _) Q (emb_fresh RESV st 65536) (to_Z RA) (to_Z FMT)) with (lo := lo) (str := str) (va := va).
    all: try eassumption.
    all: try (subst len; rewrite ?SLEN; first [exact LENB | eassumption]).
    + intros a HFR A0 ACE. destruct (emb_fresh_facts L RESV st 65536 a d 0 0 HFR ROK EA eq_refl ltac:(clear; lia)) as (_ & _ & _ & AH & _ & _). exact AH.
    + intros a RNG' ms' HFR A0 AAL ACE LE. rewrite (KR_unr RESV st EMB_INIT _ a HFR). apply implF_ret_unr.
    + intros a RNG' m' t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x HFR PO CBC' CF64'.
      rewrite (KR_fresh0 RESV st EMB_INIT _ a d 0 EA HFR). change (rup EMB_INIT PG) with 65536.
      cbv beta zeta. rewrite a_emb_set_emb. fold len.
      replace (65536 <? 0 + len) with false by (symmetry; apply Z.ltb_ge; clear -LENR; lia).
      destruct PO as (FPLE & BW & AAL & A0 & ACE & MU2 & WM2 & MI2 & ST2 & PTR2 & MTX2 & VEC2 & JNK & RCH & RSCH & RC2).
      destruct (emb_fresh_facts L RESV st 65536 a d 0 0 HFR ROK EA eq_refl ltac:(clear; lia)) as (_ & _ & _ & AH & _ & AVR).
      xport TN MU2 WM2 ltac:(unfold AIMG_HI in AH; clear -LO CEIL ATR AH; lia).
      apply KONT. unfold emb_set_size. rewrite !a_emb_set_emb.
      split; [exact FPLE|].
      split. { exists (a, 65536, 0 + len). reflexivity. }
      split. { unfold emb_cells. rewrite a_emb_set_emb. change (AEMB + 16) with 0xd9338. split; [exact MTX2|].
               change (65536 =? 0) with false. cbv iota. change AEMB with 0xd9328. change (0xd9328 + 32) with 0xd9348.
               split; [exact PTR2|]. split; [subst len; rewrite SLEN in VEC2; exact VEC2|]. split; [clear -LENR; lia|]. split; [unfold EMB_INIT; clear; lia|].
               split; [reflexivity|]. split; [exact AAL|]. split; [exact AH|]. split; [exact ACE|].
               destruct JNK as [jk JNK]. exists jk. exact JNK. }
      split. { unfold emb_rng. rewrite a_emb_set_emb. right. exact RCH. }
      split. { unfold exh_cells. split; [exact RC2|]. split; [exact TN|]. split; [exact CF64'| exact CBC']. }
      split. { intros i Hi. rewrite (MU2 (wa i)); [apply RELRO1; exact Hi|]. cbn [outside]. unfold ARELRO_LO, ARELRO_HI in Hi. unfold AIMG_HI in AH.
               unfold wa. rewrite unsigned_lit by (clear -Hi; lia). clear -Hi LO CEIL ATR AH. lia. }
      split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; unfold AEMB; clear; intros q Hq; lia. }
      split; [exact MI2|]. split; [exact ST2|]. split; [clear; lia|]. right. exact AVR.
  -
    apply Z.eqb_neq in C0.
    destruct EC as (PTR & VEC & SZR & CINI & CAL & DAL & DLO & DHI & (junk & OLD)). unfold EMB_INIT in CINI.
    change AEMB with 0xd9328 in PTR. change (AEMB + 32) with 0xd9348 in VEC.
    destruct RBUF as [RBUF|RBUF]; [contradiction|].
    xport PTR MU1 WM1 ltac:(clear -LO CEIL ATR; lia). xport VEC MU1 WM1 ltac:(clear -LO CEIL ATR; lia).
    xport OLD MU1 WM1 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO DHI CINI; lia).
    destruct (cap <? sz + len) eqn:CL.
    +
      apply Z.ltb_lt in CL.
      rewrite aembed_emb_realloc.
      set (ncap := rup (sz + len) PG).
      assert (NCE : ncap = (sz + Z.of_nat (length str) + 4095) / 4096 * 4096) by (unfold ncap, rup, PG; rewrite SLEN; fold len; f_equal; f_equal; clear; lia).
      assert (NCF : ncap mod 4096 = 0 /\ 65536 <= ncap /\ ncap < sz + len + 4096 /\ sz + len <= ncap) by (unfold ncap, rup, PG; clear -CL CINI SZR LENR; Z.div_mod_to_equations; lia).
      destruct NCF as (NCM & NCB & NCH & NCL).
      eapply (printf_grow_tail RNG (KR RESV st (sz + len) _)
                (fun a r => aembed ATOP (if r =? 0 then _ else if is_err r then aundef_ USpin _ else aundef_ UBadAnswer _))
                Q (emb_fresh RESV st ncap) (to_Z RA) (to_Z FMT)) with (lo := lo) (str := str) (va := va) (d0 := d) (cap0 := cap) (sz := sz) (ncap := ncap).
      all: try eassumption.
      all: try (rewrite ?SLEN; fold len; first [exact LENB | eassumption | clear -CL CINI SZR LENR CAPB DHI ATR; lia]).
      * exists junk. exact OLD.
      * intros a HFR A0 ACE. destruct (emb_fresh_facts L RESV st ncap a d cap sz HFR ROK EA NCM NCB) as (_ & _ & _ & AH & ADJ & _). split; [exact AH| exact (ADJ C0)].
      * intros a RNG' ms' HFR A0 AAL ACE LE. fold ncap. rewrite (KR_unr RESV st (sz + len) _ a HFR). apply implF_ret_unr.
      * intros a HFR. fold ncap. rewrite (KR_fresh1 RESV st (sz + len) _ a d cap sz EA C0 HFR). reflexivity.
      * intros a RNG' m' t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x HFR PO CBC' CF64'.
        cbv beta. change (0 =? 0) with true. cbv iota. fold ncap.
        destruct PO as (FPLE & AAL & A0 & ACE & MU2 & MI2 & ST2 & PTR2 & MTX2 & VEC2 & JNK & RCH & RC2).
        destruct (emb_fresh_facts L RESV st ncap a d cap sz HFR ROK EA NCM NCB) as (_ & _ & _ & AH & ADJ & AVR). specialize (ADJ C0).
        eapply cells_frameD in TN; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; unfold AIMG_HI in *; clear -LO CEIL ATR AH DLO; lia].
        apply KONT. unfold emb_set_size. rewrite !a_emb_set_emb.
        split; [exact FPLE|].
        split. { exists (a, ncap, sz + len). reflexivity. }
        split. { unfold emb_cells. rewrite a_emb_set_emb. change (AEMB + 16) with 0xd9338. split; [exact MTX2|].
                 replace (ncap =? 0) with false by (symmetry; apply Z.eqb_neq; clear -NCB; lia). change AEMB with 0xd9328. change (0xd9328 + 32) with 0xd9348.
                 split; [exact PTR2|]. split; [rewrite SLEN in VEC2; exact VEC2|]. split; [clear -LENR SZR NCL; lia|]. split; [unfold EMB_INIT; exact NCB|].
                 split; [exact NCM|]. split; [exact AAL|]. split; [exact AH|]. split; [exact ACE|].
                 destruct JNK as [jk JNK]. exists jk. exact JNK. }
        split. { unfold emb_rng. rewrite a_emb_set_emb. right. exact RCH. }
        split. { unfold exh_cells. split; [exact RC2|]. split; [exact TN|]. split; [exact CF64'| exact CBC']. }
        split. { intros i Hi. rewrite (MU2 (wa i)); [apply RELRO1; exact Hi|]. cbn [outside]. unfold ARELRO_LO, ARELRO_HI in Hi. unfold AIMG_HI in *.
                 unfold wa. rewrite unsigned_lit by (clear -Hi; lia). clear -Hi LO CEIL ATR AH DLO. lia. }
        split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; unfold AEMB; clear; intros q Hq; lia. }
        split; [exact MI2|]. split; [exact ST2|]. split; [clear -NCH CL LENR SZR; lia|]. right. exact AVR.
    +
      apply Z.ltb_ge in CL.
      iprefix. eapply evtF_cut.
      { eapply (printf_fit_tail RNG (to_Z RA) (to_Z FMT)) with (lo := lo) (str := str) (va := va) (d := d) (cap := cap) (sz := sz).
        all: try eassumption.
        all: try (rewrite ?SLEN; fold len; first [exact LENB | eassumption | clear -CL CINI SZR LENR CAPB DHI ATR; lia]).
        exists junk. exact OLD. }
      intros ms2 PO. unfold printf_fit_post in PO.
      destruct PO as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m' & -> & MU2 & WM2 & MI2 & ST2 & PTR2 & MTX2 & VEC2 & JNK).
      apply evtF_done.
      xport GPG MU2 WM2 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO; lia). xport PGSZ MU2 WM2 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO; lia).
      xport GOT MU2 WM2 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO; lia). xport DPM MU2 WM2 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO; lia).
      xport MLIM MU2 WM2 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO; lia). xport TN MU2 WM2 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO; lia).
      xport CF64 MU2 WM2 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO; lia). xport CBC MU2 WM2 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO; lia).
      apply KONT. unfold emb_set_size. rewrite EA. rewrite !a_emb_set_emb.
      split; [apply fp_le_refl|].
      split. { exists (d, cap, sz + len). reflexivity. }
      split. { unfold emb_cells. rewrite a_emb_set_emb. change (AEMB + 16) with 0xd9338. split; [exact MTX2|].
               replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; exact C0). change AEMB with 0xd9328. change (0xd9328 + 32) with 0xd9348.
               split; [exact PTR2|]. split; [rewrite SLEN in VEC2; exact VEC2|]. split; [clear -LENR SZR CL; lia|]. split; [unfold EMB_INIT; exact CINI|].
               split; [exact CAL|]. split; [exact DAL|]. split; [exact DLO|]. split; [exact DHI|].
               destruct JNK as [jk JNK]. exists jk. exact JNK. }
      split. { unfold emb_rng. rewrite a_emb_set_emb. right. exact RBUF. }
      split. { unfold exh_cells. split; [unfold rmap_cells; repeat (split; [assumption|]); assumption|]. repeat (split; [assumption|]). assumption. }
      split. { intros i Hi. rewrite (MU2 (wa i)); [apply RELRO1; exact Hi|]. cbn [outside]. unfold ARELRO_LO, ARELRO_HI in Hi. unfold AIMG_HI in *.
               unfold wa. rewrite unsigned_lit by (clear -Hi; lia). clear -Hi LO CEIL ATR DLO. lia. }
      split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; unfold AEMB; clear; intros q Hq; lia. }
      split; [exact MI2|]. split; [exact ST2|]. split; [clear; lia|]. left. split; [reflexivity|]. split; [reflexivity| exact C0].
Qed.
End CANSEC2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AKit.TwinB AKit2.TwinB ARep.TwinB ARepKit.TwinB ABytes.TwinB AFrameD.TwinB RT_stubs.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammapz. Import F_aunmap.TwinB AMalloc_iface.TwinB AEmbRep.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import SegL.TwinB PrintfFmt2.TwinB PrintfSeg2.TwinB PrintfRegs.TwinB F_mmapordie.TwinB F_embrealloc.TwinB F_embappend.TwinB F_printf_tail.TwinB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC2. Context {rc : runConstT}.

Definition emb_fresh (RESV : list (Z * Z)) (st : astate) (ncap mb : Z) : bool :=
  mmap_answer_ok ATOP ncap mb && negb (is_err mb) && avoids_all mb ncap (RESV ++ asec_ranges st).

Definition KR {R} (RESV : list (Z * Z)) (st : astate) (want : Z) (k : astate -> AM R) (mb : Z) : itree node (exc R) :=
  let '(d, cap, sz) := a_emb st in
  let ncap := rup want PG in
  aembed ATOP (if negb (mmap_answer_ok ATOP ncap mb) then aundef_ UBadAnswer (k st)
               else if is_err mb then aundef_ USpin (k st)
               else if negb (avoids_all mb ncap (RESV ++ asec_ranges st)) then aundef_ UBadAnswer (k st)
               else let st1 := set_emb (mb, ncap, sz) st in
                    if cap =? 0 then k st1 else
                    ev (AMunmap d cap) (fun r => if r =? 0 then k st1 else if is_err r then aundef_ USpin (k st1) else aundef_ UBadAnswer (k st1))).

Lemma aembed_emb_realloc : forall {R} RESV st want (k : astate -> AM R),
  aembed ATOP (emb_realloc ATOP RESV st want k)
  = ebind (enode (NMmap 0 (rup want PG) 3 34) (adec_mmap ATOP (rup want PG) 3)) (KR RESV st want k).
Proof.
  intros R RESV st want k. unfold emb_realloc, KR. destruct (a_emb st) as [[d cap] sz]. unfold ev. rewrite aembed_vis. reflexivity.
Qed.

Lemma KR_unr : forall {R} RESV st want (k : astate -> AM R) mb, emb_fresh RESV st (rup want PG) mb = false -> KR RESV st want k mb = Ret Unr.
Proof.
  intros R RESV st want k mb H. unfold KR, emb_fresh in *. destruct (a_emb st) as [[d cap] sz].
  destruct (mmap_answer_ok ATOP (rup want PG) mb); [| reflexivity]. destruct (is_err mb); [reflexivity|].
  cbn [negb andb] in H. rewrite H. reflexivity.
Qed.

Lemma KR_fresh0 : forall {R} RESV st want (k : astate -> AM R) mb d sz, a_emb st = (d, 0, sz) ->
  emb_fresh RESV st (rup want PG) mb = true -> KR RESV st want k mb = aembed ATOP (k (set_emb (mb, rup want PG, sz) st)).
Proof.
  intros R RESV st want k mb d sz E H. unfold KR, emb_fresh in *. rewrite E.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. rewrite H1. destruct (is_err mb); [discriminate H2|]. rewrite H3. reflexivity.
Qed.

Lemma KR_fresh1 : forall {R} RESV st want (k : astate -> AM R) mb d cap sz, a_emb st = (d, cap, sz) -> cap <> 0 ->
  emb_fresh RESV st (rup want PG) mb = true ->
  KR RESV st want k mb = ebind (enode (NMunmap d cap) (adec_munmap d cap))
                               (fun r => aembed ATOP (if r =? 0 then k (set_emb (mb, rup want PG, sz) st)
                                                      else if is_err r then aundef_ USpin (k (set_emb (mb, rup want PG, sz) st))
                                                      else aundef_ UBadAnswer (k (set_emb (mb, rup want PG, sz) st)))).
Proof.
  intros R RESV st want k mb d cap sz E NZ H. unfold KR, emb_fresh in *. rewrite E.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. rewrite H1. destruct (is_err mb); [discriminate H2|]. rewrite H3.
  cbn [negb]. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). unfold ev. rewrite aembed_vis. reflexivity.
Qed.

Lemma emb_fresh_facts : forall L RESV st ncap mb d cap sz,
  emb_fresh RESV st ncap mb = true -> aresv_ok L RESV -> a_emb st = (d, cap, sz) -> ncap mod 4096 = 0 -> 65536 <= ncap ->
  0 < mb /\ mb mod 4096 = 0 /\ mb + ncap <= ATOP /\ AIMG_HI <= mb /\ (cap <> 0 -> mb + ncap <= d \/ d + cap <= mb) /\ avoids_all mb ncap (RESV ++ asec_ranges st) = true.
Proof.
  intros L RESV st ncap mb d cap sz H ROK E NCM NCB. unfold emb_fresh in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  assert (E2 : is_err mb = false) by (destruct (is_err mb); [discriminate| reflexivity]).
  unfold mmap_answer_ok in H1. rewrite E2 in H1. cbn [orb] in H1.
  apply andb_prop in H1 as [H1 H9]. apply andb_prop in H1 as [H1 H8]. apply andb_prop in H1 as [H6 H7].
  apply Z.ltb_lt in H6. apply Z.eqb_eq in H7. apply Z.leb_le in H8. apply Z.ltb_lt in H9.
  assert (RU : rup ncap PG = ncap) by (unfold rup, PG; clear -NCM NCB; Z.div_mod_to_equations; lia). rewrite RU in H8. change PG with 4096 in H7.
  pose proof H3 as H30. unfold avoids_all in H3. rewrite forallb_app in H3. apply andb_prop in H3 as [H4 H5].
  destruct ROK as (R1 & _).
  pose proof (pcov_clear _ _ _ _ _ R1 H4 ltac:(unfold AIMG_HI; clear; lia) ltac:(clear -NCB; lia)) as C1.
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [clear -C1 H6 NCB; lia|]. split; [| exact H30].
  intros NZ. unfold asec_ranges in H5. rewrite forallb_app in H5. apply andb_prop in H5 as [_ H5].
  unfold emb_iv in H5. rewrite E in H5. replace (cap =? 0) with false in H5 by (symmetry; apply Z.eqb_neq; exact NZ).
  cbn [forallb] in H5. apply andb_prop in H5 as [H5 _]. unfold iv_clear in H5. cbn [fst snd] in H5.
  apply orb_prop in H5. destruct H5 as [H5|H5]; apply Z.leb_le in H5; lia.
Qed.

Definition pr_ret (RESV : list (Z * Z)) (sp : word) (lo : Z) (RNG : footprint) (st : astate) (m : amem) (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let '(d0, cap0, _) := a_emb st in let '(d2, cap2, _) := a_emb st2 in
  fp_le RNG RNG'
  /\ (exists e2, st2 = set_emb e2 st)
  /\ emb_cells st2 m' /\ emb_rng st2 RNG' /\ exh_cells m' /\ arelro m'
  /\ munch [(bv_unsigned sp - 1280, bv_unsigned sp); (AEMB, AEMB + 56); (d0, d0 + cap0); (d2, d2 + cap2)]%Z m m'
  /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
  /\ cap2 <= Z.max 65536 (cap0 + 8192)
  /\ ((d2 = d0 /\ cap2 = cap0 /\ cap0 <> 0) \/ avoids_all d2 cap2 (RESV ++ asec_ranges st) = true).

Lemma a_emb_set_emb : forall v st, a_emb (set_emb v st) = v. Proof. reflexivity. Qed.

Lemma printf_emb_spec : forall RNG {R} (RESV : list (Z * Z)) (k : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (RA FMT : int) (LEN : nat) (xf : FI.rf Val.sv) (L : alayout)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (st : astate) (lo : Z),
  PrintfFmt2.TwinB.PrintfFmt2.checkP RA FMT LEN xf = true -> FI.rf_get xf FI.X0 = Val.VL W64.wzero -> (1 <= LEN <= 400)%nat ->
  (forall r, rget (StepB.core_of
                (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x73d70) fc None m (seg_rom bsegs)))
             (St.reg_of_r5 r)
             = Val.den (SegL.TwinB.SegL.envW (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F fc) (FI.rf_get xf r)) ->
  bv_unsigned fc < 32 -> bv_unsigned sp < 2 ^ 63 ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 1280 ->
  mem_inv bsegs m -> arelro m -> exh_cells m -> emb_cells st m -> aresv_ok L RESV ->
  (let '(_, cap0, _) := a_emb st in cap0 < 2 ^ 37) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> emb_rng st RNG ->
  (forall st2 RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      pr_ret RESV sp lo RNG st m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (k st2)) (epostF Q)
            (MS (mkR (Z_to_bv 64 (to_Z RA)) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc (Z_to_bv 64 (to_Z RA))) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (emb_append ATOP RESV st (Z.of_nat LEN) k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x73d70) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros CHK HX0 LENB HR FC SPHI ST CEIL LO MI RELRO XC EC ROK CAPB RIMG RSTK RBUF KONT.
  word_range sp SPR. pose proof atop_range as ATR.
  iprefix.
  eapply evtF_cut.
  { eapply (PrintfSeg2.TwinB.PrintfSeg2.printf_fmt_seg RNG RA FMT LEN xf CHK HX0 ltac:(clear -LENB; lia) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo).
    - exact HR.
    - exact FC.
    - exact SPHI.
    - exact ST.
    - exact LO.
    - clear -CEIL ATR. lia.
    - exact MI.
    - exact RELRO.
    - eapply rng_sub'; [exact RSTK|]. clear -LO SPR. lia.
    - exact RIMG. }
  intros ms1 PO.
  destruct PO as (ra' & t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & s4' & s5' & s6' & s7' & s8' & s9' & t3' & t4' & t5' & t6' & va & m1 & str
                  & -> & MU1 & WM1 & MI1 & ST1 & SL0 & SL1 & SL2 & SL3 & SLEN & SNZ & SB).
  apply evtF_done.

  destruct XC as (RC & TN & CF64 & CBC). destruct RC as (GPG & PGSZ & GOT & DPM & MLIM).
  assert (WCL : forall A n, 0 <= A -> A + n <= bv_unsigned sp - 1280 -> disjoint_from [(bv_unsigned sp - 1280, bv_unsigned sp)]%Z A n) by (intros A n H1 H2; cbn [disjoint_from fst snd]; split; [left; lia| exact I]).
  xport GPG MU1 WM1 ltac:(clear -LO CEIL ATR; lia). xport PGSZ MU1 WM1 ltac:(clear -LO CEIL ATR; lia). xport GOT MU1 WM1 ltac:(clear -LO CEIL ATR; lia).
  xport DPM MU1 WM1 ltac:(clear -LO CEIL ATR; lia). xport MLIM MU1 WM1 ltac:(clear -LO CEIL ATR; lia). xport TN MU1 WM1 ltac:(clear -LO CEIL ATR; lia).
  xport CF64 MU1 WM1 ltac:(clear -LO CEIL ATR; lia). xport CBC MU1 WM1 ltac:(clear -LO CEIL ATR; lia).
  assert (RC1 : rmap_cells m1) by (unfold rmap_cells; repeat (split; [assumption|]); assumption).
  assert (RELRO1 : arelro m1).
  { intros i Hi. rewrite (MU1 (wa i)); [apply RELRO; exact Hi|]. cbn [outside]. unfold ARELRO_LO, ARELRO_HI in Hi.
    split; [| exact I]. unfold wa. rewrite unsigned_lit by (clear -Hi; lia). clear -Hi LO CEIL ATR. lia. }
  unfold emb_cells in EC. unfold emb_rng in RBUF. unfold pr_ret in KONT.
  destruct (a_emb st) as [[d cap] sz] eqn:EA.
  destruct EC as [MTX EC]. change (AEMB + 16) with 0xdb4f8 in MTX. xport MTX MU1 WM1 ltac:(clear -LO CEIL ATR; lia).
  unfold emb_append. rewrite EA.
  set (len := Z.of_nat LEN) in *.
  assert (LENR : 1 <= len <= 400) by (subst len; clear -LENB; lia).
  destruct (cap =? 0) eqn:C0.
  -
    apply Z.eqb_eq in C0. subst cap. destruct EC as (PTR & SZ0 & VEC). subst sz.
    change AEMB with 0xdb4e8 in PTR. change (AEMB + 32) with 0xdb508 in VEC.
    xport PTR MU1 WM1 ltac:(clear -LO CEIL ATR; lia). xport VEC MU1 WM1 ltac:(clear -LO CEIL ATR; lia).
    rewrite aembed_emb_realloc. change (rup EMB_INIT PG) with 65536.
    eapply (printf_first_tail RNG (KR RESV st EMB_INIT _) Q (emb_fresh RESV st 65536) (to_Z RA) (to_Z FMT)) with (lo := lo) (str := str) (va := va).
    all: try eassumption.
    all: try (subst len; rewrite ?SLEN; first [exact LENB | eassumption]).
    + intros a HFR A0 ACE. destruct (emb_fresh_facts L RESV st 65536 a d 0 0 HFR ROK EA eq_refl ltac:(clear; lia)) as (_ & _ & _ & AH & _ & _). exact AH.
    + intros a RNG' ms' HFR A0 AAL ACE LE. rewrite (KR_unr RESV st EMB_INIT _ a HFR). apply implF_ret_unr.
    + intros a RNG' m' t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x HFR PO CBC' CF64'.
      rewrite (KR_fresh0 RESV st EMB_INIT _ a d 0 EA HFR). change (rup EMB_INIT PG) with 65536.
      cbv beta zeta. rewrite a_emb_set_emb. fold len.
      replace (65536 <? 0 + len) with false by (symmetry; apply Z.ltb_ge; clear -LENR; lia).
      destruct PO as (FPLE & BW & AAL & A0 & ACE & MU2 & WM2 & MI2 & ST2 & PTR2 & MTX2 & VEC2 & JNK & RCH & RSCH & RC2).
      destruct (emb_fresh_facts L RESV st 65536 a d 0 0 HFR ROK EA eq_refl ltac:(clear; lia)) as (_ & _ & _ & AH & _ & AVR).
      xport TN MU2 WM2 ltac:(unfold AIMG_HI in AH; clear -LO CEIL ATR AH; lia).
      apply KONT. unfold emb_set_size. rewrite !a_emb_set_emb.
      split; [exact FPLE|].
      split. { exists (a, 65536, 0 + len). reflexivity. }
      split. { unfold emb_cells. rewrite a_emb_set_emb. change (AEMB + 16) with 0xdb4f8. split; [exact MTX2|].
               change (65536 =? 0) with false. cbv iota. change AEMB with 0xdb4e8. change (0xdb4e8 + 32) with 0xdb508.
               split; [exact PTR2|]. split; [subst len; rewrite SLEN in VEC2; exact VEC2|]. split; [clear -LENR; lia|]. split; [unfold EMB_INIT; clear; lia|].
               split; [reflexivity|]. split; [exact AAL|]. split; [exact AH|]. split; [exact ACE|].
               destruct JNK as [jk JNK]. exists jk. exact JNK. }
      split. { unfold emb_rng. rewrite a_emb_set_emb. right. exact RCH. }
      split. { unfold exh_cells. split; [exact RC2|]. split; [exact TN|]. split; [exact CF64'| exact CBC']. }
      split. { intros i Hi. rewrite (MU2 (wa i)); [apply RELRO1; exact Hi|]. cbn [outside]. unfold ARELRO_LO, ARELRO_HI in Hi. unfold AIMG_HI in AH.
               unfold wa. rewrite unsigned_lit by (clear -Hi; lia). clear -Hi LO CEIL ATR AH. lia. }
      split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; unfold AEMB; clear; intros q Hq; lia. }
      split; [exact MI2|]. split; [exact ST2|]. split; [clear; lia|]. right. exact AVR.
  -
    apply Z.eqb_neq in C0.
    destruct EC as (PTR & VEC & SZR & CINI & CAL & DAL & DLO & DHI & (junk & OLD)). unfold EMB_INIT in CINI.
    change AEMB with 0xdb4e8 in PTR. change (AEMB + 32) with 0xdb508 in VEC.
    destruct RBUF as [RBUF|RBUF]; [contradiction|].
    xport PTR MU1 WM1 ltac:(clear -LO CEIL ATR; lia). xport VEC MU1 WM1 ltac:(clear -LO CEIL ATR; lia).
    xport OLD MU1 WM1 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO DHI CINI; lia).
    destruct (cap <? sz + len) eqn:CL.
    +
      apply Z.ltb_lt in CL.
      rewrite aembed_emb_realloc.
      set (ncap := rup (sz + len) PG).
      assert (NCE : ncap = (sz + Z.of_nat (length str) + 4095) / 4096 * 4096) by (unfold ncap, rup, PG; rewrite SLEN; fold len; f_equal; f_equal; clear; lia).
      assert (NCF : ncap mod 4096 = 0 /\ 65536 <= ncap /\ ncap < sz + len + 4096 /\ sz + len <= ncap) by (unfold ncap, rup, PG; clear -CL CINI SZR LENR; Z.div_mod_to_equations; lia).
      destruct NCF as (NCM & NCB & NCH & NCL).
      eapply (printf_grow_tail RNG (KR RESV st (sz + len) _)
                (fun a r => aembed ATOP (if r =? 0 then _ else if is_err r then aundef_ USpin _ else aundef_ UBadAnswer _))
                Q (emb_fresh RESV st ncap) (to_Z RA) (to_Z FMT)) with (lo := lo) (str := str) (va := va) (d0 := d) (cap0 := cap) (sz := sz) (ncap := ncap).
      all: try eassumption.
      all: try (rewrite ?SLEN; fold len; first [exact LENB | eassumption | clear -CL CINI SZR LENR CAPB DHI ATR; lia]).
      * exists junk. exact OLD.
      * intros a HFR A0 ACE. destruct (emb_fresh_facts L RESV st ncap a d cap sz HFR ROK EA NCM NCB) as (_ & _ & _ & AH & ADJ & _). split; [exact AH| exact (ADJ C0)].
      * intros a RNG' ms' HFR A0 AAL ACE LE. fold ncap. rewrite (KR_unr RESV st (sz + len) _ a HFR). apply implF_ret_unr.
      * intros a HFR. fold ncap. rewrite (KR_fresh1 RESV st (sz + len) _ a d cap sz EA C0 HFR). reflexivity.
      * intros a RNG' m' t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x HFR PO CBC' CF64'.
        cbv beta. change (0 =? 0) with true. cbv iota. fold ncap.
        destruct PO as (FPLE & AAL & A0 & ACE & MU2 & MI2 & ST2 & PTR2 & MTX2 & VEC2 & JNK & RCH & RC2).
        destruct (emb_fresh_facts L RESV st ncap a d cap sz HFR ROK EA NCM NCB) as (_ & _ & _ & AH & ADJ & AVR). specialize (ADJ C0).
        eapply cells_frameD in TN; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; unfold AIMG_HI in *; clear -LO CEIL ATR AH DLO; lia].
        apply KONT. unfold emb_set_size. rewrite !a_emb_set_emb.
        split; [exact FPLE|].
        split. { exists (a, ncap, sz + len). reflexivity. }
        split. { unfold emb_cells. rewrite a_emb_set_emb. change (AEMB + 16) with 0xdb4f8. split; [exact MTX2|].
                 replace (ncap =? 0) with false by (symmetry; apply Z.eqb_neq; clear -NCB; lia). change AEMB with 0xdb4e8. change (0xdb4e8 + 32) with 0xdb508.
                 split; [exact PTR2|]. split; [rewrite SLEN in VEC2; exact VEC2|]. split; [clear -LENR SZR NCL; lia|]. split; [unfold EMB_INIT; exact NCB|].
                 split; [exact NCM|]. split; [exact AAL|]. split; [exact AH|]. split; [exact ACE|].
                 destruct JNK as [jk JNK]. exists jk. exact JNK. }
        split. { unfold emb_rng. rewrite a_emb_set_emb. right. exact RCH. }
        split. { unfold exh_cells. split; [exact RC2|]. split; [exact TN|]. split; [exact CF64'| exact CBC']. }
        split. { intros i Hi. rewrite (MU2 (wa i)); [apply RELRO1; exact Hi|]. cbn [outside]. unfold ARELRO_LO, ARELRO_HI in Hi. unfold AIMG_HI in *.
                 unfold wa. rewrite unsigned_lit by (clear -Hi; lia). clear -Hi LO CEIL ATR AH DLO. lia. }
        split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; unfold AEMB; clear; intros q Hq; lia. }
        split; [exact MI2|]. split; [exact ST2|]. split; [clear -NCH CL LENR SZR; lia|]. right. exact AVR.
    +
      apply Z.ltb_ge in CL.
      iprefix. eapply evtF_cut.
      { eapply (printf_fit_tail RNG (to_Z RA) (to_Z FMT)) with (lo := lo) (str := str) (va := va) (d := d) (cap := cap) (sz := sz).
        all: try eassumption.
        all: try (rewrite ?SLEN; fold len; first [exact LENB | eassumption | clear -CL CINI SZR LENR CAPB DHI ATR; lia]).
        exists junk. exact OLD. }
      intros ms2 PO. unfold printf_fit_post in PO.
      destruct PO as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m' & -> & MU2 & WM2 & MI2 & ST2 & PTR2 & MTX2 & VEC2 & JNK).
      apply evtF_done.
      xport GPG MU2 WM2 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO; lia). xport PGSZ MU2 WM2 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO; lia).
      xport GOT MU2 WM2 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO; lia). xport DPM MU2 WM2 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO; lia).
      xport MLIM MU2 WM2 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO; lia). xport TN MU2 WM2 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO; lia).
      xport CF64 MU2 WM2 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO; lia). xport CBC MU2 WM2 ltac:(unfold AIMG_HI in DLO; clear -LO CEIL ATR DLO; lia).
      apply KONT. unfold emb_set_size. rewrite EA. rewrite !a_emb_set_emb.
      split; [apply fp_le_refl|].
      split. { exists (d, cap, sz + len). reflexivity. }
      split. { unfold emb_cells. rewrite a_emb_set_emb. change (AEMB + 16) with 0xdb4f8. split; [exact MTX2|].
               replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; exact C0). change AEMB with 0xdb4e8. change (0xdb4e8 + 32) with 0xdb508.
               split; [exact PTR2|]. split; [rewrite SLEN in VEC2; exact VEC2|]. split; [clear -LENR SZR CL; lia|]. split; [unfold EMB_INIT; exact CINI|].
               split; [exact CAL|]. split; [exact DAL|]. split; [exact DLO|]. split; [exact DHI|].
               destruct JNK as [jk JNK]. exists jk. exact JNK. }
      split. { unfold emb_rng. rewrite a_emb_set_emb. right. exact RBUF. }
      split. { unfold exh_cells. split; [unfold rmap_cells; repeat (split; [assumption|]); assumption|]. repeat (split; [assumption|]). assumption. }
      split. { intros i Hi. rewrite (MU2 (wa i)); [apply RELRO1; exact Hi|]. cbn [outside]. unfold ARELRO_LO, ARELRO_HI in Hi. unfold AIMG_HI in *.
               unfold wa. rewrite unsigned_lit by (clear -Hi; lia). clear -Hi LO CEIL ATR DLO. lia. }
      split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; unfold AEMB; clear; intros q Hq; lia. }
      split; [exact MI2|]. split; [exact ST2|]. split; [clear; lia|]. left. split; [reflexivity|]. split; [reflexivity| exact C0].
Qed.
End CANSEC2.
End TwinB.
