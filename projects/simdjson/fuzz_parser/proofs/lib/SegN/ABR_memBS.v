(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require PropExec StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec FP Image RunConst.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import AsanEmbed AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase RtCells AMalloc_iface AU_iface I_asan_memset AU_rt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKitA PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegCall SegProg SegLib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import SegLibBr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHMB AMEMHB AMEMHBS ABR_memB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3.AX2. Import AxSymExec3Sound.AX2S. Import AxSymRun3. Import ST.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Module ABRBS.
Import ABRB.
Ltac kget HK K := pose proof (kin _ _ _ _ K HK ltac:(cbn [app AMHBS.opnd2s AMHB.opnd2 AMHB.stk2]; repeat (first [left; reflexivity | right]))).

Section Br.
Context {rc : runConstT}.
Lemma opnd2s_ok : forall E M p n p8 g h he,
  know_ok bsegs E M (AMHBS.opnd2s p n p8 g h he) -> u (edenot E n) <= 2^40 ->
  app_blk (u (edenot E p)) (u (edenot E p) + u (edenot E n))
  /\ unpoisoned M (u (edenot E p)) (u (edenot E p) + u (edenot E n))
  /\ 64 * u (edenot E h) <= u (edenot E p) /\ u (edenot E p) + u (edenot E n) <= 64 * u (edenot E he)
  /\ 0 <= 64 * u (edenot E h) /\ 64 * u (edenot E he) <= KEND
  /\ (64 * u (edenot E h)) mod 64 = 0 /\ (64 * u (edenot E he)) mod 64 = 0
  /\ wr_at bsegs M (shad (64 * u (edenot E h))) (shad (64 * u (edenot E he)) - shad (64 * u (edenot E h)))
  /\ u (edenot E (AMHB.mul 8 h)) + AMHB.SH = shad (64 * u (edenot E h))
  /\ u (edenot E (AMHB.mul 8 (AMHB.sub he h))) = shad (64 * u (edenot E he)) - shad (64 * u (edenot E h))
  /\ u (edenot E p) + u (edenot E n) <= 0x7ffffffffff8 /\ 0x7ffe00000000 <= u (edenot E p).
Proof.
  intros E M p n p8 g h he HK HN.
  set (P := u (edenot E p)). set (N := u (edenot E n)). set (P8 := u (edenot E p8)). set (G := u (edenot E g)).
  set (H := u (edenot E h)). set (HE := u (edenot E he)).
  assert (RP := ur (edenot E p)). assert (RN := ur (edenot E n)). assert (RP8 := ur (edenot E p8)).
  assert (RG := ur (edenot E g)). assert (RH := ur (edenot E h)). assert (RHE := ur (edenot E he)).
  fold P N P8 G H HE in RP, RN, RP8, RG, RH, RHE.
  kget HK (KRange p8 0 0x200000000000). kget HK (KRange h 0 0x200000000000). kget HK (KRange he 0 0x200000000000).
  kget HK (KRange p 0x7ffe00000000 0x800000000000). kget HK (KRange (AMHB.add p n) 0x7ffe00000000 0x7ffffffffff8).
  kget HK (KRange (AMHB.sub p (AMHB.mul 8 p8)) 0 7). kget HK (KRange g 0 0x2000000000).
  kget HK (KRange (AMHB.sub (AMHB.mul 8 g) (AMHB.sub (AMHB.add p n) (AMHB.mul 8 p8))) 0 7).
  kget HK (KZero (SA p8 AMHB.SH) g).
  kget HK (KRange (AMHB.sub p (AMHB.mul 64 h)) 0 1048576). kget HK (KRange (AMHB.sub (AMHB.mul 64 he) (AMHB.add p n)) 0 63).
  kget HK (KWr (SA (AMHB.mul 8 h) AMHB.SH) (AMHB.mul 8 (AMHB.sub he h))).
  kget HK (KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA p 0) n).
  match goal with
  | H1 : kentry_ok _ _ _ (KRange p8 _ _), H2 : kentry_ok _ _ _ (KRange h _ _), H3 : kentry_ok _ _ _ (KRange he _ _),
    H4 : kentry_ok _ _ _ (KRange p _ _), H5 : kentry_ok _ _ _ (KRange (AMHB.add p n) _ _),
    H6 : kentry_ok _ _ _ (KRange (AMHB.sub p (AMHB.mul 8 p8)) _ _), H7 : kentry_ok _ _ _ (KRange g _ _),
    H8 : kentry_ok _ _ _ (KRange (AMHB.sub (AMHB.mul 8 g) _) _ _), H9 : kentry_ok _ _ _ (KZero _ _),
    H10 : kentry_ok _ _ _ (KRange (AMHB.sub p (AMHB.mul 64 h)) _ _), H11 : kentry_ok _ _ _ (KRange (AMHB.sub (AMHB.mul 64 he) _) _ _),
    H12 : kentry_ok _ _ _ (KWr _ _), H13 : kentry_ok _ _ _ (KDisj _ _ _ _) |- _ =>
    rename H1 into F11; rename H2 into F12; rename H3 into F13; rename H4 into F8; rename H5 into F9; rename H6 into F1;
    rename H7 into F2; rename H8 into F3; rename H9 into F4; rename H10 into F5; rename H11 into F6; rename H12 into F7;
    rename H13 into F10
  end.
  cbn [kentry_ok] in F11, F12, F13, F8, F2. fold P8 H HE P G in F11, F12, F13, F8, F2.
  cbn [kentry_ok AMHB.add AMHB.sub AMHB.mul edenot] in F9, F1, F3, F5, F6.
  zden F9. zden F1. zden F3. zden F5. zden F6.
  fold P N P8 G H HE in F9, F1, F3, F5, F6.
  change (8 mod 2^64) with 8 in F1, F3. change (64 mod 2^64) with 64 in F5, F6.
  rewrite (Z.mod_small (8 * P8)) in F1 by lia. rewrite (Z.mod_small (8 * P8)) in F3 by lia. rewrite (Z.mod_small (8 * G)) in F3 by lia.
  rewrite (Z.mod_small (64 * H)) in F5 by lia. rewrite (Z.mod_small (64 * HE)) in F6 by lia.
  rewrite (Z.mod_small (P + N)) in F9 by lia. rewrite (Z.mod_small (P + N)) in F3 by lia. rewrite (Z.mod_small (P + N)) in F6 by lia.
  assert (A1 : 0 <= P - 8 * P8 <= 7) by (apply modr; lia).
  assert (A3 : 0 <= 8 * G - (P + N - 8 * P8) <= 7).
  { rewrite (Z.mod_small (P + N - 8 * P8)) in F3 by lia. apply modr; lia. }
  assert (A5 : 0 <= P - 64 * H <= 1048576) by (apply modr; lia).
  assert (A6 : 0 <= 64 * HE - (P + N) <= 63) by (apply modr; lia).
  assert (HSH : forall x, 0 <= x -> shad (64 * x) = 8 * x + ASHOFF).
  { intros x Hx. rewrite shad_div. replace (64 * x) with ((8 * x) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  split.
  { (* [comment removed for export] *)
    cbn [kentry_ok] in F10. unfold estart, elenZ in F10. cbn [a_base a_off edenot] in F10. fold P N in F10. zden F10.
    rewrite ?(Z.mod_small 0 (2^64)), ?(Z.mod_small 0x100000001000 (2^64)) in F10 by lia.
    unfold app_blk, KLOW, KHIGH, KEND. lia. }
  split.
  { (* [comment removed for export] *)
    destruct (Z.eq_dec N 0) as [N0|N0].
    - rewrite N0, Z.add_0_r. apply unpoisoned_nil. lia.
    - apply (unpoisoned_of_zero M P (P + N) (ASHOFF + P8)); [lia | lia | lia | |].
      + f_equal. Z.div_mod_to_equations. lia.
      + intros i Hi. destruct F4 as [_ Z4]. unfold elenZ, estart in Z4. cbn [a_base a_off] in Z4. fold P8 G in Z4.
        unfold wa. replace (ASHOFF + P8 + i) with (P8 + AMHB.SH + i) by (unfold ASHOFF, AMHB.SH; lia). apply Z4.
        split; [lia|]. Z.div_mod_to_equations. lia. }
  split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold KEND; lia|].
  split; [rewrite Z.mul_comm; apply Z_mod_mult|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
  assert (E1 : u (edenot E (AMHB.mul 8 h)) = 8 * H).
  { cbn [AMHB.mul edenot]. rewrite u_mul64, u_lit64a. fold H. rewrite (Z.mod_small 8) by lia. apply Z.mod_small. lia. }
  assert (E2 : u (edenot E (AMHB.mul 8 (AMHB.sub he h))) = 8 * (HE - H)).
  { cbn [AMHB.mul AMHB.sub edenot]. rewrite u_mul64, u_sub64, u_lit64a. fold H HE. rewrite (Z.mod_small 8) by lia.
    rewrite (Z.mod_small (HE - H)) by lia. apply Z.mod_small. lia. }
  split.
  { pose proof (SLB.kn_wr_at bsegs E M _ _ _ F7) as W. rewrite E1, E2 in W. rewrite !HSH by lia.
    replace (8 * HE + ASHOFF - (8 * H + ASHOFF)) with (8 * (HE - H)) by lia. unfold ASHOFF, AMHB.SH in *.
    replace (8 * H + 2147450880) with (8 * H + 2147450880) by lia. exact W. }
  split; [rewrite E1, HSH by lia; unfold ASHOFF, AMHB.SH; lia|].
  split; [rewrite E2, !HSH by lia; lia|].
  lia.
Qed.
End Br.

Section Bridge.
Context {rc : runConstT}.
Variable AI : AMallocIface.
Variables (L : alayout) (RNGh : ExecF.footprint) (st : astate) (LB : list ablock).
Variable GP : nat -> list word -> (word -> option byte) -> Prop.
Local Notation hmH := (AHMB.hmH AI L RNGh st LB).
Local Notation hmA := (AHMB.hmA AI LB).
Local Notation hmC := (AHMB.hmC AI LB).
Local Notation hmR := AHMB.hmR.
Lemma ra_lit : forall (x : word) rpc, 0 <= rpc < 2^64 -> rpc <= u x <= rpc -> x = Z_to_bv 64 rpc.
Proof. intros x rpc H1 H2. apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). lia. Qed.

Lemma msags_lib : forall c rpc, 0 <= c < 256 -> 0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  SLib.summ_libH bsegs GP hmH hmA hmC hmR (AMHBS.MSAGS c rpc).
Proof.
  intros c rpc Hc Hr0 Hr2 E M rom R F fc HRom HAG HWC HHM HRF HR HK _ HZ.
  unfold AHMB.hmR in HRom. subst rom. destruct HHM as [HH MI].
  cbn [AMHBS.MSAGS SP.SUMR SP.sm_pre SP.sm_post SP.sm_A SP.sm_W SP.sm_G SP.sm_PS t_pc t_regs t_know AMHBS.MSGS_pre AMHB.MSG_post TM] in *.
  rewrite (regs_ok_canon E (AMHB.MSG_pre_regs c) R HRF HR).
  unfold AMHBS.MSGS_pre_kn in HK.
  pose proof HK as HK0. apply Forall_app in HK0 as [_ HKa]. apply Forall_app in HKa as [_ HKb]. apply Forall_app in HKb as [_ HKO].
  kget HK (KRange (AMHB.V 0) rpc rpc). kget HK (KRange (AMHB.V 1) (0x7ffe00000000 + 2208) 0x800000000000).
  kget HK (KWr (SA AMHB.vSP (-2208)) (ELit 2208)). kget HK (KUnk (SA AMHB.vSP (-2208)) (ELit 2208)).
  kget HK (KRange (AMHB.V 17) 0 0x10000000000). kget HK (KWr (SA (AMHB.V 16) 0) (AMHB.V 17)). kget HK (KUnk (SA (AMHB.V 16) 0) (AMHB.V 17)).
  kget HK (KDisj (SA AMHB.vSP (-2208)) (ELit 2208) (SA (AMHB.V 16) 0) (AMHB.V 17)).
  match goal with
  | K0 : kentry_ok _ _ _ (KRange (AMHB.V 0) _ _), K1 : kentry_ok _ _ _ (KRange (AMHB.V 1) _ _),
    K2 : kentry_ok _ _ _ (KWr (SA AMHB.vSP _) _), K3 : kentry_ok _ _ _ (KUnk (SA AMHB.vSP _) _),
    K4 : kentry_ok _ _ _ (KRange (AMHB.V 17) _ _), K5 : kentry_ok _ _ _ (KWr (SA (AMHB.V 16) 0) _),
    K6 : kentry_ok _ _ _ (KUnk (SA (AMHB.V 16) 0) _), K7 : kentry_ok _ _ _ (KDisj _ _ _ _) |- _ =>
    rename K0 into KRA; rename K1 into KSP; rename K2 into KSW; rename K3 into KSU; rename K4 into KN; rename K5 into KDW;
    rename K6 into KDU; rename K7 into KDJ
  end.
  cbn [kentry_ok AMHB.V edenot] in KRA, KSP, KN.
  set (sp := u (ev E 1)) in *. set (D := u (ev E 16)) in *. set (N := u (ev E 17)) in *.
  pose proof (ur (ev E 1)) as Rsp. pose proof (ur (ev E 16)) as RD. pose proof (ur (ev E 17)) as RN. fold sp D N in Rsp, RD, RN.
  destruct (opnd2s_ok E M _ _ _ _ _ _ HKO ltac:(cbn [AMHB.V edenot]; fold N; lia))
    as (APP & UNP & HL1 & HL2 & HL3 & HL4 & HL5 & HL6 & WRS & EH1 & EH2 & PB1 & PB2).
  cbn [AMHB.V edenot] in APP, UNP, HL1, HL2, HL3, HL4, HL5, HL6, WRS, EH1, EH2, PB1, PB2. fold D N in APP, UNP, HL1, HL2, PB1, PB2.
  set (H := u (ev E 20)) in *. set (HE := u (ev E 21)) in *.
  (* [comment removed for export] *)
  pose proof (SLB.kn_stk bsegs E M _ _ _ KSW KSU) as STK. cbn [AMHB.vSP AMHB.V edenot] in STK. fold sp in STK.
  rewrite SLB.u64 in STK by lia. replace (sp + -2208 + 2208) with sp in STK by lia. replace (sp + -2208) with (sp - 2208) in STK by lia.
  (* [comment removed for export] *)
  destruct (SLB.kn_rw_CB bsegs E M _ _ _ KDW KDU) as (junk & DST). cbn [AMHB.V edenot] in DST. fold D N in DST. rewrite Z.add_0_r in DST.
  cbn [kentry_ok] in KDJ. unfold estart, elenZ in KDJ. cbn [a_base a_off AMHB.vSP AMHB.V edenot] in KDJ. fold sp D N in KDJ.
  rewrite SLB.u64 in KDJ by lia.
  (* [comment removed for export] *)
  destruct (AI_rtcells AI L RNGh st LB M HH) as (_ & GOT & RIC & REAL & SHB & _ & INI & LAY & _).
  (* [comment removed for export] *)
  assert (RW : forall w lo len, In w AMHB.MSG_A -> fst (SX.awin_den E w) <= lo -> lo + len <= snd (SX.awin_den E w) -> 0 <= len ->
                 ExecF.rng (SX.fp_of (Some AMHB.MSG_A) E) lo len).
  { intros w lo len Hw H1 H2 H3. pose proof (SLib.rng_fp_of AMHB.MSG_A E w HAG Hw) as R0. eapply ExecF.rng_sub; [exact R0 | lia | lia]. }
  assert (RIMG : ExecF.rng (SX.fp_of (Some AMHB.MSG_A) E) 0x10000 0x661000).
  { apply (RW AMHB.IMGW); [cbn; tauto | cbn [SX.awin_den AMHB.IMGW edenot fst snd]; rewrite !SLB.u64 by lia; lia .. | lia]. }
  assert (RSTK : ExecF.rng (SX.fp_of (Some AMHB.MSG_A) E) (sp - 2208) (sp - (sp - 2208))).
  { apply (RW (AMHB.vSP, -2208, ELit 2208)); [cbn; tauto | cbn [SX.awin_den edenot AMHB.vSP AMHB.V fst snd]; fold sp; rewrite ?SLB.u64 by lia; lia .. | lia]. }
  assert (RDST : ExecF.rng (SX.fp_of (Some AMHB.MSG_A) E) D N).
  { apply (RW (AMHB.V 16, 0, AMHB.V 17)); [cbn; tauto | cbn [SX.awin_den edenot AMHB.V fst snd]; fold D N; lia .. | lia]. }
  assert (RSH : ExecF.rng (SX.fp_of (Some AMHB.MSG_A) E) (shad (64 * H)) (shad (64 * HE) - shad (64 * H))).
  { apply (RW (AMHB.hullw (AMHB.V 20) (AMHB.V 21))); [cbn; tauto | cbn [SX.awin_den AMHB.hullw fst snd]; unfold AMHB.SH in *; lia .. | ].
    rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  pose proof (asan_memset_spec (SX.fp_of (Some AMHB.MSG_A) E) (ev E 0) (ev E 1) (ev E 2) (ev E 3) (ev E 22) (ev E 23) (ev E 24) (ev E 4) (ev E 5)
                (ev E 16) (Z_to_bv 64 c) (ev E 17) (ev E 25) (ev E 26) (ev E 27) (ev E 28) (ev E 29)
                (ev E 6) (ev E 7) (ev E 8) (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15)
                (ev E 30) (ev E 31) (ev E 32) (ev E 33) F fc M (sp - 2208) junk (64 * H) (64 * HE)) as RUN.
  fold sp D N in RUN.
  specialize (RUN MI STK ltac:(lia) ltac:(unfold KHIGH; lia) GOT RIC SHB INI LAY REAL DST ltac:(lia) APP UNP ltac:(lia)).
  specialize (RUN ltac:(unfold KEND in *; lia) WRS RIMG RSTK RDST RSH).
  destruct RUN as (ms' & Hrun & Hpost).
  pose proof (PIosRegs.msteps_wrel bsegs _ _ (ExecF.mstepsF_msteps bsegs _ _ _ Hrun)) as HW.
  destruct Hpost as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Hms' & MU & WM & MI' & STK' & DST').
  rewrite Hms' in HW. cbn [ms_mem MS] in HW.
  exists ms'. split; [exact Hrun|].
  set (E' := SLB.env_ext E 34 [t0; t1; t2; a1'; a2'; a3; a4; a5; a6; a7; t3; t4; t5; t6]).
  assert (EQ : forall v, (v < 34)%nat -> ev E' v = ev E v) by (intros v Hv; apply SLB.env_ext_lt; exact Hv).
  exists (AMHB.MSG_post c rpc), E', m',
    (mkR (ev E 0) (ev E 1) (ev E 2) (ev E 3) t0 t1 t2 (ev E 4) (ev E 5) (ev E 16) a1' a2' a3 a4 a5 a6 a7 (ev E 6) (ev E 7) (ev E 8)
         (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15) t3 t4 t5 t6), F, fc.
  split; [left; reflexivity|].
  split.
  { rewrite Hms'. cbn [AMHB.MSG_post TM t_pc]. f_equal. rewrite (ra_lit (ev E 0) rpc Hr0 KRA). apply ret_pc_even; assumption. }
  split; [exact HZ|]. split; [apply rfull_mkR|].
  split; [apply regs_ok_mkR; reflexivity|].
  split.
  { constructor; [|constructor].
    assert (E16 : ev E' 16 = ev E 16) by (apply EQ; lia). assert (E17 : ev E' 17 = ev E 17) by (apply EQ; lia).
    destruct DST' as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    rewrite SLB.u64 in B by lia. rewrite (Z.mod_small c 256) in B by lia.
    assert (DEF : forall i, 0 <= i < N -> m' (Z_to_bv 64 (D + i)) = Some (Z_to_bv 8 c)).
    { intros i Hi. destruct B as (B1 & B2 & HB). specialize (HB (Z.to_nat i)). rewrite repeat_length in HB.
      specialize (HB ltac:(fold N; lia)). rewrite Z2Nat.id in HB by lia. unfold mrd, wa in HB. fold D in HB.
      pose proof (SLB.kn_defined bsegs E M (AMHB.V 16) 0 (AMHB.V 17) KDU i) as D0. cbn [AMHB.V edenot] in D0. fold D N in D0.
      rewrite Z.add_0_r in D0.
      pose proof (SC.wrel_grows bsegs _ _ HW _ (D0 Hi)) as D1. unfold wa in D1.
      destruct (m' (Z_to_bv 64 (D + i))) as [x|]; [|contradiction].
      rewrite HB. rewrite nth_error_repeat by lia. reflexivity. }
    destruct (Z.eqb c 0) eqn:Hc0.
    - apply Z.eqb_eq in Hc0. subst c. cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off AMHB.V edenot]. rewrite ?E16, ?E17.
      fold D N. split; [unfold flat, estart, elenZ; cbn [a_base a_off AMHB.V edenot]; rewrite ?E16, ?E17; fold D N; lia|].
      intros i Hi. rewrite Z.add_0_r. exact (DEF i Hi).
    - cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off AMHB.V edenot]. rewrite ?E16, ?E17.
      fold D N. split; [unfold flat, estart, elenZ; cbn [a_base a_off AMHB.V edenot]; rewrite ?E16, ?E17; fold D N; lia|].
      intros i Hi. rewrite Z.add_0_r. exact (DEF i Hi). }
  split; [constructor|].
  split; [apply SLB.gagree_ext; cbn [AMHBS.MSAGS SP.SUMR SP.sm_G]; lia|].
  split; [reflexivity|].
  assert (EQW : map (SP.win_den E) AMHB.MSG_W = [(sp - 2208, sp); (D, D + N)]).
  { cbn [map AMHB.MSG_W SP.win_den edenot AMHB.vSP AMHB.V]. fold sp D N. rewrite !SLB.u64 by lia.
    replace (sp + -2208) with (sp - 2208) by lia. replace (sp - 2208 + 2208) with sp by lia. rewrite Z.add_0_r. reflexivity. }
  split.
  { split; [|exact MI'].
    apply (AI_frame AI L RNGh st LB M m' [(sp - 2208, sp); (D, D + N)] HH MU WM).
    rewrite <- EQW. unfold SP.wins_client in HWC. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (w & <- & Hw).
    exact (proj1 (Forall_forall _ _) HWC w Hw). }
  cbn [SP.frame_ok AMHBS.MSAGS SP.SUMR SP.sm_PS SP.sm_W]. apply SLB.frame_of_munch. rewrite EQW. exact MU.
Qed.

Theorem msags_ok : forall c rpc, 0 <= c < 256 -> 0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  SP.summ_okH bsegs GP hmH hmA hmC hmR (AMHBS.MSAGS c rpc).
Proof. intros c rpc H0 H1 H2. apply SLib.summ_of_libH. exact (msags_lib c rpc H0 H1 H2). Qed.
End Bridge.
End ABRBS.
Print Assumptions ABRBS.msags_ok.
