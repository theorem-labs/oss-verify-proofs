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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase RtCells AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKitA PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegCall SegProg SegLib SegVC.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import SegLibBr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHMB AMEMHB AMEMHBN ABR_memB I_asan_memmoveC NRMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3.AX2. Import AxSymExec3Sound.AX2S. Import AxSymRun3. Import ST.
Open Scope Z_scope.
Local Notation u := bv_unsigned.

Module ABRVBN.
Import ABRB.

(* [comment removed for export] *)
Lemma rdn_lib_as : forall segs m n a, PropExec.rdn segs m a n = AS.PropExec.rdn segs m a n.
Proof.
  intros segs m n; induction n as [|n IH]; intros a; [reflexivity|].
  cbn [PropExec.rdn AS.PropExec.rdn]. rewrite IH. unfold PropExec.seg_rom, AS.PropExec.seg_rom. reflexivity.
Qed.

Section Bridge.
Context {rc : runConstT}.
Variable AI : AMallocIface.
Variables (L : alayout) (RNGh : ExecF.footprint) (st : astate) (LB : list ablock).
Local Notation GP := (SNU.snu_gp bsegs).
Local Notation hmH := (AHMB.hmH AI L RNGh st LB).
Local Notation hmA := (AHMB.hmA AI LB).
Local Notation hmC := (AHMB.hmC AI LB).
Local Notation hmR := AHMB.hmR.

(* [comment removed for export] *)
Lemma mvahn_lib : forall rpc, 0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  SLib.summ_libH bsegs GP hmH hmA hmC hmR (AMHBN.MVAHN rpc).
Proof.
  intros rpc Hr0 Hr2 E M rom R F fc HRom HAG HWC HHM HRF HR HK HG HZ.
  unfold AHMB.hmR in HRom. subst rom. destruct HHM as [HH MI].
  cbn [AMHBN.MVAHN SP.SUMR SP.sm_pre SP.sm_post SP.sm_A SP.sm_W SP.sm_G SP.sm_PS t_pc t_regs t_know t_ghost AMHBN.MVN_pre AMHBN.MVN_post] in *.
  unfold AMHBN.MVN_pre_kn in HK. pose proof (Forall_inv HK) as KN1. apply Forall_inv_tail in HK.
  rewrite (regs_ok_canon E AMHB.MV_pre_regs R HRF HR).
  unfold AMHB.MV_pre_kn in HK.
  pose proof HK as HK0. apply Forall_app in HK0 as [_ HKa]. apply Forall_app in HKa as [HKOS HKOD].
  kget HK (KRange (AMHB.V 0) rpc rpc). kget HK (KRange (AMHB.sub (AMHB.V 16) (AMHB.mul 8 (AMHB.V 19))) 0 0).
  kget HK (KRange (AMHB.sub (AMHB.V 17) (AMHB.mul 8 (AMHB.V 20))) 0 0). kget HK (KRange (AMHB.sub (AMHB.V 18) (AMHB.mul 8 (AMHB.V 21))) 0 0).
  kget HK (KRange (AMHB.V 21) 0 62). kget HK (KRange (AMHB.V 1) (0x7ffe00000000 + 4096) 0x800000000000).
  kget HK (KWr (SA AMHB.vSP (-4096)) (ELit 4096)). kget HK (KUnk (SA AMHB.vSP (-4096)) (ELit 4096)).
  kget HK (KUnk (SA (AMHB.V 17) 0) (AMHB.V 18)). kget HK (KWr (SA (AMHB.V 16) 0) (AMHB.V 18)). kget HK (KUnk (SA (AMHB.V 16) 0) (AMHB.V 18)).
  kget HK (KDisj (SA AMHB.vSP (- 4096)) (ELit 4096) (SA (AMHB.mul 8 (AMHB.V 19)) 0) (AMHB.mul 8 (AMHB.V 21))).
  kget HK (KDisj (SA AMHB.vSP (- 4096)) (ELit 4096) (SA (AMHB.mul 8 (AMHB.V 20)) 0) (AMHB.mul 8 (AMHB.V 21))).
  match goal with
  | K0 : kentry_ok _ _ _ (KRange (AMHB.V 0) _ _), K1 : kentry_ok _ _ _ (KRange (AMHB.sub (AMHB.V 16) _) _ _),
    K2 : kentry_ok _ _ _ (KRange (AMHB.sub (AMHB.V 17) _) _ _), K2' : kentry_ok _ _ _ (KRange (AMHB.sub (AMHB.V 18) _) _ _),
    K3 : kentry_ok _ _ _ (KRange (AMHB.V 21) _ _), K4 : kentry_ok _ _ _ (KRange (AMHB.V 1) _ _),
    K5 : kentry_ok _ _ _ (KWr (SA AMHB.vSP _) _), K6 : kentry_ok _ _ _ (KUnk (SA AMHB.vSP _) _),
    K7 : kentry_ok _ _ _ (KUnk (SA (AMHB.V 17) 0) _), K8 : kentry_ok _ _ _ (KWr (SA (AMHB.V 16) 0) _),
    K10 : kentry_ok _ _ _ (KUnk (SA (AMHB.V 16) 0) _),
    K11 : kentry_ok _ _ _ (KDisj (SA AMHB.vSP _) _ (SA (AMHB.mul 8 (AMHB.V 19)) 0) _),
    K12 : kentry_ok _ _ _ (KDisj (SA AMHB.vSP _) _ (SA (AMHB.mul 8 (AMHB.V 20)) 0) _) |- _ =>
    rename K0 into KRA; rename K1 into KD8; rename K2 into KS8; rename K2' into KN8; rename K3 into KN; rename K4 into KSP;
    rename K5 into KSW; rename K6 into KSU; rename K7 into KSRC; rename K8 into KDW; rename K10 into KDU;
    rename K11 into KDJD; rename K12 into KDJS
  end.
  cbn [kentry_ok AMHB.V edenot] in KRA, KSP, KN.
  destruct (opnd_ok E M _ _ _ _ HKOD ltac:(cbn [AMHB.V edenot]; lia))
    as (E8D & E8N & APPD & UNPD & HD1 & HD2 & HD3 & HD5 & HD6 & WRSD & EHD1 & EHD2 & PBD).
  destruct (opnd_ok E M _ _ _ _ HKOS ltac:(cbn [AMHB.V edenot]; lia))
    as (E8S & _ & APPS & UNPS & HS1 & HS2 & HS3 & HS5 & HS6 & WRSS & EHS1 & EHS2 & PBS).
  cbn [AMHB.V edenot] in E8D, E8N, APPD, UNPD, HD1, HD2, HD3, HD5, HD6, WRSD, EHD1, EHD2, PBD.
  cbn [AMHB.V edenot] in E8S, APPS, UNPS, HS1, HS2, HS3, HS5, HS6, WRSS, EHS1, EHS2, PBS.
  set (sp := u (ev E 1)) in *. set (D := u (ev E 16)) in *. set (S := u (ev E 17)) in *. set (N := u (ev E 18)) in *.
  set (D8 := u (ev E 19)) in *. set (S8 := u (ev E 20)) in *. set (N8 := u (ev E 21)) in *.
  set (r := u (edenot E (AMHB.mul 8 (AMHB.V 22)))) in *.
  pose proof (ur (ev E 1)) as Rsp. pose proof (ur (ev E 16)) as RD. pose proof (ur (ev E 17)) as RS. pose proof (ur (ev E 18)) as RN.
  fold sp D S N in Rsp, RD, RS, RN.
  cbn [kentry_ok AMHB.sub AMHB.mul AMHB.V edenot] in KD8, KS8, KN8. zden KD8. zden KS8. zden KN8. fold D S N D8 S8 N8 in KD8, KS8, KN8.
  change (8 mod 2^64) with 8 in KD8, KS8, KN8.
  rewrite (Z.mod_small (8 * D8)) in KD8 by lia. rewrite (Z.mod_small (8 * S8)) in KS8 by lia. rewrite (Z.mod_small (8 * N8)) in KN8 by lia.
  assert (HD : D = 8 * D8) by (pose proof (modr (D - 8 * D8) 0 0 ltac:(lia) ltac:(lia) KD8); lia).
  assert (HS : S = 8 * S8) by (pose proof (modr (S - 8 * S8) 0 0 ltac:(lia) ltac:(lia) KS8); lia).
  assert (HN : N = 8 * N8) by (pose proof (modr (N - 8 * N8) 0 0 ltac:(lia) ltac:(lia) KN8); lia).
  rewrite <- HD in APPD, UNPD, HD1, HD2. rewrite <- HN in APPD, UNPD, HD2.
  rewrite <- HS in APPS, UNPS, HS1, HS2. rewrite <- HN in APPS, UNPS, HS2.
  (* [comment removed for export] *)
  pose proof (SLB.kn_stk bsegs E M _ _ _ KSW KSU) as STK. cbn [AMHB.vSP AMHB.V edenot] in STK. fold sp in STK.
  rewrite SLB.u64 in STK by lia. replace (sp + -4096 + 4096) with sp in STK by lia. replace (sp + -4096) with (sp - 4096) in STK by lia.
  (* [comment removed for export] *)
  destruct (SLB.kn_bytes_of_unk bsegs E M _ _ _ KSRC) as (src & SRCB & SRCL). cbn [AMHB.V edenot] in SRCB, SRCL. fold S N in SRCB, SRCL.
  rewrite Z.add_0_r in SRCB.
  pose proof (SLB.kn_wr_at bsegs E M _ _ _ KDW) as DWR. cbn [AMHB.V edenot] in DWR. fold D N in DWR. rewrite Z.add_0_r in DWR.
  cbn [kentry_ok] in KDJD, KDJS. unfold estart, elenZ in KDJD, KDJS. cbn [a_base a_off] in KDJD, KDJS.
  rewrite E8D, E8N in KDJD. rewrite E8S, E8N in KDJS.
  unfold AMHB.vSP, AMHB.V in KDJD, KDJS. cbn [edenot] in KDJD, KDJS. fold sp D S N D8 S8 N8 in KDJD, KDJS.
  rewrite ?SLB.u64 in KDJD by lia. rewrite ?SLB.u64 in KDJS by lia.
  (* [comment removed for export] *)
  destruct (AI_rtcells AI L RNGh st LB M HH) as (_ & GOT & RIC & REAL & SHB & _ & INI & LAY & _).
  (* [comment removed for export] *)
  assert (RW : forall w lo len, In w AMHB.MV_A -> fst (SX.awin_den E w) <= lo -> lo + len <= snd (SX.awin_den E w) -> 0 <= len ->
                 ExecF.rng (SX.fp_of (Some AMHB.MV_A) E) lo len).
  { intros w lo len Hw H1 H2 H3. pose proof (SLib.rng_fp_of AMHB.MV_A E w HAG Hw) as R0. eapply ExecF.rng_sub; [exact R0 | lia | lia]. }
  assert (RIMG : ExecF.rng (SX.fp_of (Some AMHB.MV_A) E) 0x10000 0x661000).
  { apply (RW AMHB.IMGW); [cbn; tauto | cbn [SX.awin_den AMHB.IMGW edenot fst snd]; rewrite !SLB.u64 by lia; lia .. | lia]. }
  assert (RSTK : ExecF.rng (SX.fp_of (Some AMHB.MV_A) E) (sp - 4096) (sp - (sp - 4096))).
  { apply (RW (AMHB.vSP, -4096, ELit 4096)); [cbn; tauto | cbn [SX.awin_den edenot AMHB.vSP AMHB.V fst snd]; fold sp; rewrite ?SLB.u64 by lia; lia .. | lia]. }
  assert (RSRC : ExecF.rng (SX.fp_of (Some AMHB.MV_A) E) S N).
  { apply (RW (AMHB.V 17, 0, AMHB.V 18)); [cbn; tauto | cbn [SX.awin_den edenot AMHB.V fst snd]; fold S N; lia .. | lia]. }
  assert (RDST : ExecF.rng (SX.fp_of (Some AMHB.MV_A) E) D N).
  { apply (RW (AMHB.V 16, 0, AMHB.V 18)); [cbn; tauto | cbn [SX.awin_den edenot AMHB.V fst snd]; fold D N; lia .. | lia]. }
  assert (RSH : ExecF.rng (SX.fp_of (Some AMHB.MV_A) E) (shad (8 * r)) (shad (8 * r + 576) - shad (8 * r))).
  { apply (RW (AMHB.mul 8 (AMHB.V 22), AMHB.SH, ELit 72)); [cbn; tauto | cbn [SX.awin_den fst snd]; fold r; rewrite ?EHD2, ?EHD1;
      cbn [edenot]; rewrite ?SLB.u64 by lia; unfold AMHB.SH in *; lia .. | lia]. }
  (* [comment removed for export] *)
  pose proof (ur (edenot E (AMHB.mul 8 (AMHB.V 22)))) as Rr. fold r in Rr.
  assert (Z0r : 0 <= 8 * r) by (clear - Rr; lia).
  pose proof (AMVC.asan_memmove_spec (SX.fp_of (Some AMHB.MV_A) E) (ev E 0) (ev E 1) (ev E 2) (ev E 3) (ev E 23) (ev E 24) (ev E 25) (ev E 4) (ev E 5)
                (ev E 16) (ev E 17) (ev E 18) (ev E 26) (ev E 27) (ev E 28) (ev E 29) (ev E 30)
                (ev E 6) (ev E 7) (ev E 8) (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15)
                (ev E 31) (ev E 32) (ev E 33) (ev E 34) F fc M (sp - 4096) src (8 * r) (8 * r + 576) (8 * r) (8 * r + 576)) as RUN.
  fold sp D S N in RUN.
  specialize (RUN MI STK ltac:(clear - KSP; lia) ltac:(unfold KHIGH; clear - KSP; lia) GOT RIC SHB INI LAY SRCB SRCL DWR).
  specialize (RUN ltac:(clear - KDJS HS HN; lia) ltac:(clear - KDJD HD HN; lia) APPS APPD UNPS UNPD ltac:(clear - KN HN; lia)).
  specialize (RUN (conj HS1 (conj HS2 (conj HS5 (conj HS6 (conj Z0r HS3))))) (conj HD1 (conj HD2 (conj HD5 (conj HD6 (conj Z0r HD3)))))
                   WRSS WRSD RIMG RSTK RSRC RDST RSH RSH).
  destruct RUN as (ms' & Hrun & Hpost).
  pose proof (PIosRegs.msteps_wrel bsegs _ _ (ExecF.mstepsF_msteps bsegs _ _ _ Hrun)) as HW.
  destruct Hpost as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Hms' & MU & WM & MI' & STK' & DSTB).
  rewrite Hms' in HW. cbn [ms_mem MS] in HW.
  exists ms'. split; [exact Hrun|].
  set (E' := SLB.env_ext E 35 [t0; t1; t2; a1'; a2'; a3; a4; a5; a6; a7; t3; t4; t5; t6]).
  assert (EQ : forall v, (v < 35)%nat -> ev E' v = ev E v) by (intros v Hv; apply SLB.env_ext_lt; exact Hv).
  (* [comment removed for export] *)
  assert (POSTG : SG.gholds GP E' m' [GA 10 [AMHB.add (AMHB.V 16) (AMHB.V 18)]]).
  { cbn [kentry_ok edenot AMHB.V] in KN1. fold N8 in KN1.
    unfold SG.gholds in HG |- *. apply Forall_inv in HG. constructor; [|constructor].
    cbn [g_id g_args map AMHB.add AMHB.V edenot] in HG |- *. rewrite (EQ 16%nat ltac:(lia)), (EQ 18%nat ltac:(lia)).
    cbn [SNU.snu_gp] in HG |- *. destruct HG as (H8 & bs & Hrd & Hnz).
    assert (USN : u (alu64 ALU_ADD (ev E 17) (ev E 18)) = S + N) by (rewrite SV.u_alu_add; fold S N; apply Z.mod_small; lia).
    assert (UDN : u (alu64 ALU_ADD (ev E 16) (ev E 18)) = D + N) by (rewrite SV.u_alu_add; fold D N; apply Z.mod_small; lia).
    rewrite USN in Hrd. unfold SNU.g_topw. rewrite UDN. split; [lia|]. exists bs. split; [|exact Hnz].
    assert (RS8 := bytes_at_rdn bsegs M S src (Z.to_nat (N - 8)) 8 SRCB ltac:(lia)).
    assert (RD8 := bytes_at_rdn bsegs m' D src (Z.to_nat (N - 8)) 8 DSTB ltac:(lia)).
    rewrite Z2Nat.id in RS8, RD8 by lia.
    replace (Z_to_bv 64 (S + N - 8)) with (wa (S + (N - 8))) in Hrd by (f_equal; lia).
    replace (Z_to_bv 64 (D + N - 8)) with (wa (D + (N - 8))) by (f_equal; lia).
    rewrite rdn_lib_as in RS8, RD8. rewrite RD8. rewrite RS8 in Hrd. exact Hrd. }
  exists (AMHBN.MVN_post rpc), E', m',
    (mkR (ev E 0) (ev E 1) (ev E 2) (ev E 3) t0 t1 t2 (ev E 4) (ev E 5) (ev E 16) a1' a2' a3 a4 a5 a6 a7 (ev E 6) (ev E 7) (ev E 8)
         (ev E 9) (ev E 10) (ev E 11) (ev E 12) (ev E 13) (ev E 14) (ev E 15) t3 t4 t5 t6), F, fc.
  split; [left; reflexivity|].
  split.
  { rewrite Hms'. cbn [AMHBN.MVN_post t_pc]. f_equal. rewrite (ra_lit (ev E 0) rpc Hr0 KRA). apply ret_pc_even; assumption. }
  split; [exact HZ|]. split; [apply rfull_mkR|].
  split; [apply regs_ok_mkR; reflexivity|].
  split.
  { constructor; [|constructor].
    assert (E16 : ev E' 16 = ev E 16) by (apply EQ; lia). assert (E18 : ev E' 18 = ev E 18) by (apply EQ; lia).
    cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off AMHB.V edenot]. rewrite ?E16, ?E18. fold D N.
    split; [unfold flat, estart, elenZ; cbn [a_base a_off AMHB.V edenot]; rewrite ?E16, ?E18; fold D N; lia|].
    intros i Hi. rewrite Z.add_0_r.
    pose proof (SLB.kn_defined bsegs E M (AMHB.V 16) 0 (AMHB.V 18) KDU i) as D0. cbn [AMHB.V edenot] in D0. fold D N in D0.
    rewrite Z.add_0_r in D0. exact (SC.wrel_grows bsegs _ _ HW _ (D0 Hi)). }
  split; [exact POSTG|].
  split; [apply SLB.gagree_ext; cbn [AMHBN.MVAHN SP.SUMR SP.sm_G]; lia|].
  split; [reflexivity|].
  assert (EQW : map (SP.win_den E) AMHB.MV_W = [(sp - 4096, sp); (D, D + N)]).
  { cbn [map AMHB.MV_W SP.win_den edenot AMHB.vSP AMHB.V]. fold sp D N. rewrite !SLB.u64 by lia.
    replace (sp + -4096) with (sp - 4096) by lia. replace (sp - 4096 + 4096) with sp by lia. rewrite Z.add_0_r. reflexivity. }
  apply (munch_weaken _ [(sp - 4096, sp); (D, D + N)]) in MU.
  2:{ unfold sub_fp; cbn [outside]; intros; lia. }
  split.
  { split; [|exact MI'].
    apply (AI_frame AI L RNGh st LB M m' [(sp - 4096, sp); (D, D + N)] HH MU WM).
    rewrite <- EQW. unfold SP.wins_client in HWC. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (w & <- & Hw).
    exact (proj1 (Forall_forall _ _) HWC w Hw). }
  cbn [SP.frame_ok AMHBN.MVAHN SP.SUMR SP.sm_PS SP.sm_W]. apply SLB.frame_of_munch. rewrite EQW. exact MU.
Qed.

Theorem mvahn_ok : forall rpc, 0 <= rpc < 2^64 -> rpc mod 2 = 0 -> SP.summ_okH bsegs GP hmH hmA hmC hmR (AMHBN.MVAHN rpc).
Proof. intros rpc H1 H2. apply SLib.summ_of_libH. exact (mvahn_lib rpc H1 H2). Qed.
End Bridge.
End ABRVBN.
