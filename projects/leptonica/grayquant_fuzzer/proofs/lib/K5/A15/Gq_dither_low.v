(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_lits Lept_litmem Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit Lept_objkit Lept_chain Gq_iface
  Gq_dither_l1 Gq_dither_l0 Gq_dither_line Gq_dither_lastrow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Gm_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section DLOW.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RC : rt_contracts RT.

Local Ltac park_ne := repeat match goal with H : (?a <> ?b) |- _ => lazymatch type of a with Z => change (a <> b) with (parked (a <> b)) in H end end.

(* [comment removed for export] *)
Definition dlow_keep (L : list (Z * Z)) (frames : list (Z * nat)) (usp datad rd bufs1 bufs2 n1 : Z) (a : Z) : Prop :=
  aclient L frames (usp - 128) a /\ outside [(datad, datad + rd); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1)] a.

(* [comment removed for export] *)
Definition dlow_frame (h datad wpld : Z) (s11e s10e s9e s8e s7e s6e s5e s4e s3e s2e s1e s0e rae : word) : list cell :=
  [C8 (Z_to_bv 64 (h + -1)); C8 (Z_to_bv 64 datad); C8 (Z_to_bv 64 wpld); C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e;
   C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae].

(* [comment removed for export] *)
Definition dlow_geom (sp0 lo usp datad rd datas rs bufs1 bufs2 n1 wpls wpld w h : Z) : Prop :=
  0 < wpls <= 5001 /\ 0 < wpld <= 626 /\ wpld <= wpls /\ w <= n1 /\ w <= 32 * wpld /\ 0 < rs <= 67108864 /\ 0 < rd <= rs
  /\ n1 = 4 * wpls /\ rs = 4 * (wpls * h) /\ rd = 4 * (wpld * h) /\ n1 <= rs /\ 0 < w <= 20000 /\ 0 < h <= 20000
  /\ 0 < datad /\ datad mod 16 = 0 /\ datad + rd <= sp0 - STACK_WIN /\ (datad + rd <= 0x10000 \/ SEGTOP_A <= datad) /\ (datad + rd <= 0x7fff7000 \/ 0x10007fff8000 <= datad)
  /\ 0 < datas /\ datas mod 16 = 0 /\ datas + rs <= sp0 - STACK_WIN /\ (datas + rs <= 0x10000 \/ SEGTOP_A <= datas) /\ (datas + rs <= 0x7fff7000 \/ 0x10007fff8000 <= datas)
  /\ 0 < bufs1 /\ bufs1 mod 16 = 0 /\ bufs1 + n1 <= sp0 - STACK_WIN /\ (bufs1 + n1 <= 0x10000 \/ SEGTOP_A <= bufs1) /\ (bufs1 + n1 <= 0x7fff7000 \/ 0x10007fff8000 <= bufs1)
  /\ 0 < bufs2 /\ bufs2 mod 16 = 0 /\ bufs2 + n1 <= sp0 - STACK_WIN /\ (bufs2 + n1 <= 0x10000 \/ SEGTOP_A <= bufs2) /\ (bufs2 + n1 <= 0x7fff7000 \/ 0x10007fff8000 <= bufs2)
  /\ (datad + rd <= datas \/ datas + rs <= datad) /\ (datad + rd <= bufs1 \/ bufs1 + n1 <= datad) /\ (datad + rd <= bufs2 \/ bufs2 + n1 <= datad)
  /\ (datas + rs <= bufs1 \/ bufs1 + n1 <= datas) /\ (datas + rs <= bufs2 \/ bufs2 + n1 <= datas) /\ (bufs1 + n1 <= bufs2 \/ bufs2 + n1 <= bufs1)
  /\ sp0 - STACK_WIN <= lo /\ lo + LSTK 4 <= usp /\ usp + 16 <= USTACK_TOP /\ usp mod 16 = 0 /\ usp <= sp0
  /\ SEGTOP_A + STACK_WIN <= sp0 <= USTACK_TOP /\ 0x7fff80000000 <= sp0 /\ 0 <= lo.

Definition dlow_rows_post (Σ : rts RT) PMc (gp : word) (usp lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h : Z)
    (s11e s10e s9e s8e s7e s6e s5e s4e s3e s2e s1e s0e rae : word) (mh : mem) : config -> Prop :=
  fun c => ASTA RT Σ PMc (fun ms => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
      ms = MS (mkR ra' (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 bufs1) (Z_to_bv 64 10) a0' a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 10) (Z_to_bv 64 w) (Z_to_bv 64 0) (Z_to_bv 64 bufs2) (Z_to_bv 64 (wpls * 4)) (Z_to_bv 64 (wpls * 4))
                   (Z_to_bv 64 (datas + wpls * 4 * h)) (Z_to_bv 64 (datad + wpld * 4 * (h - 1))) (Z_to_bv 64 (wpld * 4)) (Z_to_bv 64 SHB) t3' t4' t5' t6')
              F' (Z_to_bv 64 0x9cc70) (frm_clear fc') None m' (seg_rom asegs)
      /\ ART RT Σ m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -128) /\ LIBH m' /\ io_ssp m'
      /\ rw_cells asegs m' (usp + -128) (dlow_frame h datad wpld s11e s10e s9e s8e s7e s6e s5e s4e s3e s2e s1e s0e rae)
      /\ wmono asegs mh m' /\ agree_on (dlow_keep (rt_live RT Σ) (rt_frames RT Σ) usp datad rd bufs1 bufs2 n1) mh m') c.

(* [comment removed for export] *)
Lemma dlow_rows : forall (k : nat) (i : Z) (Σ : rts RT) PMc (mh : mem)
    (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (usp lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h : Z) (s11e s10e s9e s8e s7e s6e s5e s4e s3e s2e s1e s0e rae : word),
  Z.of_nat k = h - 1 - i -> 0 <= i -> (1 <= k)%nat ->
  fdfs_only PMc -> mat_stable PMc ->
  dlow_geom (rt_sp0 RT Σ) lo usp datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ->
  In (datad, rd) (rt_live RT Σ) -> In (datas, rs) (rt_live RT Σ) -> In (bufs1, n1) (rt_live RT Σ) -> In (bufs2, n1) (rt_live RT Σ) ->
  ART RT Σ mh -> mem_inv asegs mh -> stk asegs mh lo (usp + -128) -> LIBH mh -> io_ssp mh ->
  rw_cells asegs mh (usp + -128) (dlow_frame h datad wpld s11e s10e s9e s8e s7e s6e s5e s4e s3e s2e s1e s0e rae) ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 bufs1) (Z_to_bv 64 10) a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 10) (Z_to_bv 64 w) (Z_to_bv 64 (h - 1 - i)) (Z_to_bv 64 bufs2) (Z_to_bv 64 (wpls * 4)) (Z_to_bv 64 (wpls * 4))
                                        (Z_to_bv 64 (datas + wpls * 4 * (i + 1))) (Z_to_bv 64 (datad + wpld * 4 * i)) (Z_to_bv 64 (wpld * 4)) (Z_to_bv 64 SHB) t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x9cc20) (frm_clear fc) None mh (seg_rom asegs))))
    (dlow_rows_post Σ PMc gp usp lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h s11e s10e s9e s8e s7e s6e s5e s4e s3e s2e s1e s0e rae mh).
Proof using AF GP RC.
  induction k as [|k IH]; intros i Σ PMc mh ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc usp lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h
    s11e s10e s9e s8e s7e s6e s5e s4e s3e s2e s1e s0e rae HK HI HK1 FDO MST GEOM DDIN DSIN B1IN B2IN ART0 MI ST LH SSP FR.
  { exfalso. lia. }
  pose proof GEOM as (WPLS & WPLD & WDS & WN1 & W32 & RS & RD & EN1 & ERS & ERD & NRS & HW & HH
                      & DD0 & DD16 & CKR & CKS & CKH & DS0 & DS16 & CKR0 & CKS0 & CKH0 & B10 & B116 & CKR1 & CKS1 & CKH1 & B20 & B216 & CKR2 & CKS2 & CKH2
                      & AP1 & AP2 & AP3 & AP4 & AP5 & AP6 & LOW & LOR & SPT & SPA & SPB & SP0R & SP0W & STa).
  assert (SZ : hid (0 < wpls <= 5001 /\ 0 < wpld <= 626 /\ wpld <= wpls /\ w <= n1 /\ w <= 32 * wpld /\ 0 < rs <= 67108864 /\ 0 < rd <= rs
                    /\ n1 = 4 * wpls /\ rs = 4 * (wpls * h) /\ rd = 4 * (wpld * h) /\ n1 <= rs /\ 0 < w <= 20000 /\ 0 < h <= 20000)) by (unfold hid; clear - WPLS WPLD WDS WN1 W32 RS RD EN1 ERS ERD NRS HW HH; tauto).
  clear WPLS WPLD WDS WN1 W32 RS RD NRS.
  assert (SP0H : hid (rt_sp0 RT Σ <= 2^47)) by (unfold hid; clear - SP0R; unfold USTACK_TOP in SP0R; lia).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := dlow_keep (rt_live RT Σ) (rt_frames RT Σ) usp datad rd bufs1 bufs2 n1).
  pose proof (agree_refl PF mh) as AGF.
  assert (PFS : forall a, PF a -> usp - 128 <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ mh (usp - 128) a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; clear - H LOW; lia]. }
  unfold dlow_frame in FR.
  lib_refresh RT GP. refresh RT AF. unfold shad, SHB in *. clear_acc.
  park_disj.
  idtac "MARK rows: setup".
  (* [comment removed for export] *)
  assert (HIH : 0 <= i /\ i + 1 <= h - 1) by (clear - HK HI HK1; lia).
  assert (ROWB : hid (0 <= wpls * 4 * (i + 1) /\ wpls * 4 * (i + 1) + n1 <= rs /\ 0 <= wpld * 4 * i /\ wpld * 4 * i + 4 * wpld <= rd /\ wpld * 4 * i + 4 * wpld + 4 * wpld <= rd)).
  { unfold hid. unfold hid in SZ. rewrite EN1, ERS, ERD. clear - SZ HIH. nia. }
  walk_to AF MST (@nil (Z * Z)) [e_asan_memcpy].
  idtac "MARK rows: at memcpy A".
  at_call RT AF ltac:(cbn [ivls_client]; exact I)
                ltac:(fun Hx => cbn [outside]; exact I).
  idtac "MARK rows: at_call A".
  lazymatch goal with A : ART RT Σ ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    pose proof (af_acc_live RT AF Σ mm bufs2 n1 A B2IN) as (WRS & ACCS);
    pose proof (af_acc_live RT AF Σ mm bufs1 n1 A B1IN) as (WR1 & ACC1) end.
  apply wr_at_rw_CB in WRS; [| unfold hid in SZ; clear - SZ; lia]. destruct WRS as (cbs & SBC).
  pose proof SBC as [[[SBL2 _] _] _]. cbn in SBL2.
  apply u8arr_of_rw_cells in SBC. destruct SBC as [SB2 _].
  assert (SBL1 : Z.of_nat (length cbs) = n1) by (rewrite SBL2; unfold hid in SZ; clear - SZ; lia).
  assert (Q8a : 0 <= bufs1 <= 2^47) by (unfold hid in SP0H, SZ; clear - CKR1 SP0H B10 SZ; lia).
  assert (Q7a : 0 <= bufs2 <= 2^47) by (unfold hid in SP0H, SZ; clear - CKR2 SP0H B20 SZ; lia).
  assert (Q6 : bufs1 + n1 <= bufs2 \/ bufs2 + n1 <= bufs1) by (unfold parked in AP6; clear - AP6; lia).
  assert (Q5 : bufs2 + n1 <= lo) by (clear - CKR2 LOW; lia).
  eapply cps_seq.
  { pose proof (rc_asan_memcpy RT RC) as MC0; unfold memcpy_icontract in MC0;
    eapply MC0 with (lo := lo) (d := bufs1) (s := bufs2) (bs := cbs); rewrite ?SBL1.
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; unfold hid in SZ; clear - SZ; lia
         | |- bytes_at _ _ _ _ => exact SB2
         | |- ART _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- checked_src _ _ _ _ _ _ _ =>
             unfold checked_src; rewrite ?unsigned_lit by (clear - STa LOR; lia);
             split; [intros _; split; [exact ACCS | left; exists bufs2, n1; split; [exact B2IN| clear; lia]] | left; exact Q5]
         | |- checked_dst _ _ _ _ _ _ =>
             unfold checked_dst; rewrite ?unsigned_lit by (clear - STa LOR; lia);
             split; [intros _; split; [exact ACC1| left; exists bufs1, n1; split; [exact B1IN| clear; lia]]|];
             split; [intros i0 Hi; right; right; left; exists bufs1, n1; split; [exact B1IN| clear - Hi; lia]| exact WR1]
         | |- call_ok _ _ _ _ _ => call_ok_tac
         | |- _ \/ _ => exact Q6
         | |- (_ <= _ <= _) => first [exact Q8a | exact Q7a]
         | |- (_ < _) => unfold hid in SZ; clear - SZ; lia
         | |- ?g => idtac "LEFT:" g
         end. }
  rewrite SBL1. clear SB2 SBL1 SBL2 ACCS ACC1 WR1.
  idtac "MARK rows: memcpy A applied".
  after_call RT AF.
  idtac "MARK rows: after_call A".
  fold_ag ltac:(fun Hx => unfold PF, dlow_keep in Hx; destruct Hx as [Hx1 Hx2]; split; [exact Hx1 | cbn [outside] in Hx2; clear - Hx2; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST (@nil (Z * Z)) [e_asan_memcpy].
  idtac "MARK rows: at memcpy B".
  at_call RT AF ltac:(cbn [ivls_client]; exact I)
                ltac:(fun Hx => cbn [outside]; exact I).
  idtac "MARK rows: at_call B".
  lazymatch goal with A : ART RT Σ ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    pose proof (af_acc_live RT AF Σ mm datas rs A DSIN) as (WRS & ACCS);
    pose proof (af_acc_live RT AF Σ mm bufs2 n1 A B2IN) as (WR2 & ACC2) end.
  apply wr_at_rw_CB in WRS; [| unfold hid in SZ; clear - SZ; lia]. destruct WRS as (sbs & SBC).
  pose proof SBC as [[[SBL _] _] _]. cbn in SBL.
  apply u8arr_of_rw_cells in SBC. destruct SBC as [SB _].
  pose proof ROWB as RB. unfold hid in RB.
  rewrite <- (firstn_skipn (Z.to_nat (wpls * 4 * (i + 1))) sbs) in SB. apply bytes_at_app in SB. destruct SB as [_ SB].
  rewrite firstn_length_le in SB by (rewrite SBL; clear - RB SZ; unfold hid in SZ; lia). rewrite Z2Nat.id in SB by (clear - RB; lia).
  rewrite <- (firstn_skipn (Z.to_nat n1) (skipn (Z.to_nat (wpls * 4 * (i + 1))) sbs)) in SB. apply bytes_at_app in SB. destruct SB as [SB1 _].
  set (rowbs := firstn (Z.to_nat n1) (skipn (Z.to_nat (wpls * 4 * (i + 1))) sbs)) in SB1.
  assert (SBL1 : Z.of_nat (length rowbs) = n1) by (subst rowbs; rewrite firstn_length_le; [| rewrite skipn_length, SBL]; unfold hid in SZ; clear - SZ RB; lia).
  clearbody rowbs. clear SBL sbs.
  assert (Q7a : 0 <= bufs2 <= 2^47) by (unfold hid in SP0H, SZ; clear - CKR2 SP0H B20 SZ; lia).
  assert (Q7b : 0 <= datas + wpls * 4 * (i + 1) <= 2^47) by (unfold hid in SP0H, SZ; clear - CKR0 SP0H DS0 SZ RB; lia).
  assert (Q3 : bufs2 + n1 <= datas + wpls * 4 * (i + 1) \/ datas + wpls * 4 * (i + 1) + n1 <= bufs2) by (unfold parked in AP5; unfold hid in SZ; clear - AP5 SZ RB; lia).
  assert (Q4 : datas + wpls * 4 * (i + 1) + n1 <= lo) by (unfold hid in SZ; clear - CKR0 LOW SZ RB; lia).
  eapply cps_seq.
  { pose proof (rc_asan_memcpy RT RC) as MC0; unfold memcpy_icontract in MC0;
    eapply MC0 with (lo := lo) (d := bufs2) (s := datas + wpls * 4 * (i + 1)) (bs := rowbs); rewrite ?SBL1.
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; unfold hid in SZ; clear - SZ; lia
         | |- bytes_at _ _ _ _ => exact SB1
         | |- ART _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- checked_src _ _ _ _ _ _ _ =>
             unfold checked_src; rewrite ?unsigned_lit by (clear - STa LOR; lia);
             split; [intros _; split; [eapply acc_sub; [exact ACCS| clear - RB; lia | unfold hid in SZ; clear - SZ RB; lia]
                                    | left; exists datas, rs; split; [exact DSIN| unfold hid in SZ; clear - SZ RB; lia]]
                   | left; exact Q4]
         | |- checked_dst _ _ _ _ _ _ =>
             unfold checked_dst; rewrite ?unsigned_lit by (clear - STa LOR; lia);
             split; [intros _; split; [exact ACC2| left; exists bufs2, n1; split; [exact B2IN| clear; lia]]|];
             split; [intros i0 Hi; right; right; left; exists bufs2, n1; split; [exact B2IN| clear - Hi; lia]| exact WR2]
         | |- call_ok _ _ _ _ _ => call_ok_tac
         | |- _ \/ _ => exact Q3
         | |- (_ <= _ <= _) => first [exact Q7a | exact Q7b]
         | |- (_ < _) => unfold hid in SZ; clear - SZ; lia
         | |- ?g => idtac "LEFT:" g
         end. }
  rewrite SBL1. clear SB1 SBL1 ACCS ACC2 WR2 RB.
  idtac "MARK rows: memcpy B applied".
  after_call RT AF.
  idtac "MARK rows: after_call B".
  fold_ag ltac:(fun Hx => unfold PF, dlow_keep in Hx; destruct Hx as [Hx1 Hx2]; split; [exact Hx1 | cbn [outside] in Hx2; clear - Hx2; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp + -128 - 48, usp + -128); (datad + wpld * 4 * i, datad + wpld * 4 * i + 4 * wpld); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1)] [e_ditherToBinaryLineLow].
  idtac "MARK rows: at leaf".
  pose proof ROWB as RB. unfold hid in RB.
  set (lined := datad + wpld * 4 * i) in *. set (nl := 4 * wpld) in *.
  assert (ELI : lined = datad + wpld * 4 * i) by reflexivity. assert (ENL : nl = 4 * wpld) by reflexivity. clearbody lined nl.
  assert (GEO2 : dl_geom2 lined nl bufs1 bufs2 n1 w).
  { unfold dl_geom2, dl_geom, SEGTOP_A. unfold hid in SZ, SP0H. unfold parked in CKH, CKS, CKH1, CKS1, CKH2, CKS2, AP2, AP3, AP6.
    clear - SZ RB ELI ENL CKR CKH CKS CKR1 CKH1 CKS1 CKR2 CKH2 CKS2 AP2 AP3 AP6 B10 B116 B20 B216 DD0 DD16 SP0H.
    repeat lazymatch goal with |- _ /\ _ => split end; first [lia | Z.div_mod_to_equations; lia]. }
  idtac "MARK rows: GEO2".
  lazymatch goal with A : ART RT Σ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (af_acc_live RT AF Σ mm bufs1 n1 A B1IN) as (WR1 & ACC1);
    pose proof (af_acc_live RT AF Σ mm bufs2 n1 A B2IN) as (WR2 & ACC2);
    pose proof (af_acc_live RT AF Σ mm datad rd A DDIN) as (WRD & ACCD) end.
  apply wr_at_rw_CB in WR1; [| unfold hid in SZ; clear - SZ; lia]. destruct WR1 as (cbs1 & UB1).
  pose proof UB1 as [[[UBL1 _] _] _]. cbn in UBL1. apply u8arr_of_rw_cells in UB1.
  apply Nat2Z.inj_iff in UBL1. rewrite Z2Nat.id in UBL1 by (unfold hid in SZ; clear - SZ; lia).
  apply wr_at_rw_CB in WR2; [| unfold hid in SZ; clear - SZ; lia]. destruct WR2 as (cbs2 & UB2).
  pose proof UB2 as [[[UBL2 _] _] _]. cbn in UBL2. apply u8arr_of_rw_cells in UB2.
  apply Nat2Z.inj_iff in UBL2. rewrite Z2Nat.id in UBL2 by (unfold hid in SZ; clear - SZ; lia).
  pose proof (wr_at_sub _ _ _ lined nl WRD ltac:(clear - RB ELI; lia) ltac:(clear - RB ELI ENL; lia) ltac:(unfold hid in SZ; clear - SZ ENL; lia)) as WRL.
  pose proof (acc_sub asegs _ _ _ lined nl ACCD ltac:(clear - RB ELI; lia) ltac:(clear - RB ELI ENL; lia)) as ACCL.
  apply wr_at_rw_CB in WRL; [| unfold hid in SZ; clear - SZ ENL; lia]. destruct WRL as (lbs & LBC).
  pose proof LBC as [[[LBL _] _] _]. cbn in LBL. apply u8arr_of_rw_cells in LBC.
  destruct (u8arr_u32arr _ lined lbs wpld LBC ltac:(rewrite LBL; unfold hid in SZ; clear - SZ ENL; lia)) as (wl & UL & ULL0).
  assert (ULL : 4 * Z.of_nat (length wl) = nl) by (rewrite ULL0, ENL; clear; lia). clear ULL0 LBC LBL lbs WRD ACCD.
  idtac "MARK rows: arrays".
  eapply evt_cut.
  { lazymatch goal with MIx : mem_inv asegs ?mm, STx : stk asegs ?mm lo _, G1x : ro_cells asegs ?mm 931248 _, G2x : ro_cells asegs ?mm 979384 _ |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      epose proof (ditherToBinaryLineLow_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -128) lo lined nl bufs1 bufs2 n1 w cbs1 cbs2 wl
                     GEO2 MIx UB1 UBL1 ACC1 UB2 UBL2 ACC2 UL ULL ACCL G1x G2x STx) as ZR end.
    eapply ZR; unfold hid in SZ, SP0H; clear - SZ SP0H RB ELI ENL LOW LOR SPT SP0W CKR CKR1 CKR2; lia. }
  idtac "MARK rows: leaf applied".
  intros ms' PO. unfold ditherToBinaryLineLow_post in PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & bs1' & bs2' & wl' & -> & MUl & WMl & MIl & STl
                  & UB1' & UBL1' & ACC1' & UB2' & UBL2' & ACC2' & UL' & ULL' & ACCL').
  clear UB1 UBL1 ACC1 UB2 UBL2 ACC2 UL ULL ACCL cbs1 cbs2 wl.
  lazymatch type of MUl with munch _ ?ma ?mb =>
    lazymatch goal with A : ART RT ?S ma |- _ =>
      loop_art RT AF S mb lo MUl ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul
        | split; [intros zz Hzz; right; right; left; exists datad, rd; split; [exact DDIN| clear - Hzz ELI ENL RB; lia]
        | split; [intros zz Hzz; right; right; left; exists bufs1, n1; split; [exact B1IN| clear - Hzz; lia]
        | split; [intros zz Hzz; right; right; left; exists bufs2, n1; split; [exact B2IN| clear - Hzz; lia] | exact I]]]]) end end.
  idtac "MARK rows: loop_art".
  lazymatch type of MUl with munch _ ?ma ?mb =>
    loop_transport ma mb MUl ltac:(fun Hx => clear - Hx ELI ENL RB SZ CKR CKS CKH CKR1 CKS1 CKH1 CKR2 CKS2 CKH2 LOW LOR SP0H SP0R0 SP0R1 SP0W STa; unfold hid in *; unfold parked in *; first [lia | Z.div_mod_to_equations; lia]) end.
  idtac "MARK rows: loop_transport".
  fix_ret_pc.
  unfold SHB. awalk [0x9cc20; 0x9cc70].
  idtac "MARK rows: at bnez".
  destruct k as [|k].
  - (* [comment removed for export] *)
    assert (EI : i + 1 = h - 1) by (clear - HK; lia).
    brF.
    cps_stop.
    idtac "MARK rows: exit".
    lazymatch type of AGF with agree_on _ _ ?ma => lazymatch goal with MUx : munch _ ma ?mf |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => unfold PF, dlow_keep in Hx; destruct Hx as [Hx1 Hx2]; pose proof (PFS _ (conj Hx1 Hx2)) as Hx3; cbn [outside] in Hx2 |- *;
                               unfold hid in SZ; clear - Hx2 Hx3 LOR ELI ENL RB SZ; lia) end end.
    apply cps_finish. intros c Hc. subst QF. unfold dlow_rows_post.
    eapply (ASTA_conseq RT); [exact Hc|]. cbv beta. intros ms <-.
    lazymatch goal with A : ART RT Σ ?mf |- _ => exists mf end.
    do 16 eexists. eexists. eexists.
    split.
    { replace (h - 1 - i + -1) with 0 by (clear - EI; lia).
      replace (datas + wpls * 4 * (i + 1) + wpls * 4) with (datas + wpls * 4 * h) by (clear - EI; lia).
      replace (lined + wpld * 4) with (datad + wpld * 4 * (h - 1)) by (clear - EI ELI; lia).
      reflexivity. }
    repeat match goal with |- _ /\ _ => split end; assumption.
  - (* [comment removed for export] *)
    brT.
    cps_stop.
    idtac "MARK rows: next".
    lazymatch type of AGF with agree_on _ _ ?ma => lazymatch goal with MUx : munch _ ma ?mf |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => unfold PF, dlow_keep in Hx; destruct Hx as [Hx1 Hx2]; pose proof (PFS _ (conj Hx1 Hx2)) as Hx3; cbn [outside] in Hx2 |- *;
                               unfold hid in SZ; clear - Hx2 Hx3 LOR ELI ENL RB SZ; lia) end end.
    replace (h - 1 - i + -1) with (h - 1 - (i + 1)) by (clear; lia).
    replace (datas + wpls * 4 * (i + 1) + wpls * 4) with (datas + wpls * 4 * (i + 1 + 1)) by (clear; lia).
    replace (lined + wpld * 4) with (datad + wpld * 4 * (i + 1)) by (clear - ELI; lia).
    replace (Z_to_bv 64 2147450880) with (Z_to_bv 64 SHB) by reflexivity.
    eapply cps_conseq; [ | intros c Hc; exact Hc | ].
    + lazymatch goal with A : ART RT Σ ?mf, MIx : mem_inv asegs ?mf, STx : stk asegs ?mf lo _, LHx : LIBH ?mf, SSPx : io_ssp ?mf, FRx : rw_cells asegs ?mf (usp + -128) _ |- _ =>
        eapply (IH (i + 1) Σ PMc mf) end.
      all: first [eassumption | clear - HK HI; lia].
    + intros c PO. subst QF. unfold dlow_rows_post in PO |- *.
      eapply (ASTA_conseq RT); [exact PO|]. cbv beta.
      intros ms (m2 & ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & t32 & t42 & t52 & t62 & F2 & fc2 & E & A2 & MI2 & ST2 & LH2 & SSP2 & FR2 & WM2 & AG2).
      exists m2, ra2, t02, t12, t22, a02, a12, a22, a32, a42, a52, a62, a72, t32, t42, t52, t62, F2, fc2.
      split; [exact E|]. split; [exact A2|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact LH2|]. split; [exact SSP2|]. split; [exact FR2|].
      split.
      * lazymatch goal with WMx : wmono asegs mh ?mf |- _ => exact (wmono_trans asegs _ _ _ WMx WM2) end.
      * lazymatch goal with AGFx : agree_on PF mh ?mf |- _ => exact (agree_trans _ _ _ _ AGFx AG2) end.
Qed.

Theorem ditherToBinaryLow_ok : ditherToBinaryLow_cps RT.
Proof using AF GP RC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    datad w h wpld datas wpls bufs1 bufs2 FDO MST -> -> (HWR & ->) (HHR & ->) (HPDR & ->) -> (HPSR & ->) -> -> -> ->
    HW HH EWD EWS RSB DDC DSC B1C B2C ND ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct DDC as (DDIN & DD0 & DD16 & DDN). destruct DSC as (DSIN & DS0 & DS16 & DSN).
  destruct B1C as (B1IN & B10 & B116 & B1N). destruct B2C as (B2IN & B20 & B216 & B2N).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_ditherToBinaryLow, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  lib_refresh RT GP.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a
                     /\ outside [(datad, datad + 4 * (wpld * h)); (bufs1, bufs1 + 4 * wpls); (bufs2, bufs2 + 4 * wpls)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  (* [comment removed for export] *)
  assert (WPLS : 0 < wpls <= 5001) by (rewrite EWS; clear - HW; Z.div_mod_to_equations; lia).
  assert (WPLD : 0 < wpld <= 626) by (rewrite EWD; clear - HW; Z.div_mod_to_equations; lia).
  assert (WDS : wpld <= wpls) by (rewrite EWD, EWS; clear - HW; Z.div_mod_to_equations; lia).
  assert (WN1 : w <= 4 * wpls) by (rewrite EWS; clear - HW; Z.div_mod_to_equations; lia).
  assert (W32 : w <= 32 * wpld) by (rewrite EWD; clear - HW; Z.div_mod_to_equations; lia).
  assert (RS0 : 0 < wpls * h) by (clear - WPLS HH; apply Z.mul_pos_pos; lia).
  assert (RD0 : 0 < wpld * h) by (clear - WPLD HH; apply Z.mul_pos_pos; lia).
  assert (RDS : wpld * h <= wpls * h) by (clear - WDS HH; apply Z.mul_le_mono_nonneg_r; lia).
  assert (SZ : hid (0 < wpls <= 5001 /\ 0 < wpld <= 626 /\ wpld <= wpls /\ w <= 4 * wpls /\ w <= 32 * wpld /\ 0 < 4 * (wpls * h) <= 67108864 /\ 0 < 4 * (wpld * h) <= 4 * (wpls * h)
                    /\ 4 * wpls = 4 * wpls /\ 4 * (wpls * h) = 4 * (wpls * h) /\ 4 * (wpld * h) = 4 * (wpld * h) /\ 4 * wpls <= 4 * (wpls * h) /\ 0 < w <= 20000 /\ 0 < h <= 20000)).
  { unfold hid. clear - HW HH RSB WPLS WPLD WDS WN1 W32 RS0 RD0 RDS. repeat lazymatch goal with |- _ /\ _ => split end; nia. }
  clear WPLS WPLD WDS WN1 W32 RS0 RD0 RDS.
  assert (SP0H : hid (rt_sp0 RT Σ <= 2^47)) by (unfold hid; clear - SP0R; lia).
  chunk_facts RT AF GP datad (4 * (wpld * h)). chunk_facts RT AF GP datas (4 * (wpls * h)). chunk_facts RT AF GP bufs1 (4 * wpls). chunk_facts RT AF GP bufs2 (4 * wpls).
  (* [comment removed for export] *)
  pose proof (proj1 (stdpp.list_relations.list.NoDup_cons _ _) ND) as [N1 ND2].
  pose proof (proj1 (stdpp.list_relations.list.NoDup_cons _ _) ND2) as [N2 ND3].
  pose proof (proj1 (stdpp.list_relations.list.NoDup_cons _ _) ND3) as [N3 _].
  pose proof (proj1 (stdpp.list_basics.list.not_elem_of_cons _ _ _) N1) as [NE1 N1b].
  pose proof (proj1 (stdpp.list_basics.list.not_elem_of_cons _ _ _) N1b) as [NE2 N1c].
  pose proof (proj1 (stdpp.list_basics.list.not_elem_of_cons _ _ _) N1c) as [NE3 _].
  pose proof (proj1 (stdpp.list_basics.list.not_elem_of_cons _ _ _) N2) as [NE4 N2b].
  pose proof (proj1 (stdpp.list_basics.list.not_elem_of_cons _ _ _) N2b) as [NE5 _].
  pose proof (proj1 (stdpp.list_basics.list.not_elem_of_cons _ _ _) N3) as [NE6 _].
  clear N1 N2 N3 ND2 ND3 N1b N1c N2b ND.
  pose proof (live_apart2 RT AF Σ m datad (4 * (wpld * h)) datas (4 * (wpls * h)) ART0 DDIN DSIN ltac:(intros E; injection E; intros; apply NE1; assumption)) as AP1.
  pose proof (live_apart2 RT AF Σ m datad (4 * (wpld * h)) bufs1 (4 * wpls) ART0 DDIN B1IN ltac:(intros E; injection E; intros; apply NE2; assumption)) as AP2.
  pose proof (live_apart2 RT AF Σ m datad (4 * (wpld * h)) bufs2 (4 * wpls) ART0 DDIN B2IN ltac:(intros E; injection E; intros; apply NE3; assumption)) as AP3.
  pose proof (live_apart2 RT AF Σ m datas (4 * (wpls * h)) bufs1 (4 * wpls) ART0 DSIN B1IN ltac:(intros E; injection E; intros; apply NE4; assumption)) as AP4.
  pose proof (live_apart2 RT AF Σ m datas (4 * (wpls * h)) bufs2 (4 * wpls) ART0 DSIN B2IN ltac:(intros E; injection E; intros; apply NE5; assumption)) as AP5.
  pose proof (live_apart2 RT AF Σ m bufs1 (4 * wpls) bufs2 (4 * wpls) ART0 B1IN B2IN ltac:(intros E; injection E; intros; apply NE6; assumption)) as AP6.
  assert (GEOM : dlow_geom (rt_sp0 RT Σ) lo usp datad (4 * (wpld * h)) datas (4 * (wpls * h)) bufs1 bufs2 (4 * wpls) wpls wpld w h).
  { unfold dlow_geom, LSTK, STDERR_STACK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A. unfold hid in SZ, SP0H.
    clear - SZ SP0H DD0 DD16 DS0 DS16 B10 B116 B20 B216 CKR CKS CKH CKR0 CKS0 CKH0 CKR1 CKS1 CKH1 CKR2 CKS2 CKH2 AP1 AP2 AP3 AP4 AP5 AP6 LOW LOR SPT SPA SPB SP0R SP0W STa.
    repeat lazymatch goal with |- _ /\ _ => split end; first [assumption | lia]. }
  set (n1 := 4 * wpls) in *. set (rs := 4 * (wpls * h)) in *. set (rd := 4 * (wpld * h)) in *.
  idtac "MARK facts".
  carve_frame 128%nat ST.
  walk_to AF MST [(usp - 128, usp)] [e_asan_memcpy].
  idtac "MARK at memcpy 1".
  park_disj. park_ne.
  rewrite (bv_swrap_small 32 (wpls * 4)) by (unfold hid in SZ; clear - SZ; change (bv_half_modulus 32) with (2^31); lia).
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  idtac "MARK at_call 1".
  lazymatch goal with A : ART RT Σ ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    pose proof (af_acc_live RT AF Σ mm datas rs A DSIN) as (WRS & ACCS);
    pose proof (af_acc_live RT AF Σ mm bufs2 n1 A B2IN) as (WR2 & ACC2) end.
  apply wr_at_rw_CB in WRS; [| unfold hid in SZ; clear - SZ; lia]. destruct WRS as (sbs & SBC).
  pose proof SBC as [[[SBL _] _] _]. cbn in SBL.
  apply u8arr_of_rw_cells in SBC. destruct SBC as [SB _].
  rewrite <- (firstn_skipn (Z.to_nat n1) sbs) in SB. apply bytes_at_app in SB. destruct SB as [SB1 _].
  assert (SBL1 : Z.of_nat (length (firstn (Z.to_nat n1) sbs)) = n1) by (rewrite firstn_length_le; [| rewrite SBL]; unfold hid in SZ; clear - SZ; lia).
  assert (Q7a : 0 <= bufs2 <= 2^47) by (unfold hid in SP0H; clear - CKR2 SP0H B20 B2N; lia).
  assert (Q7b : 0 <= datas <= 2^47) by (unfold hid in SP0H, SZ; clear - CKR0 SP0H DS0 SZ; lia).
  assert (Q3 : bufs2 + n1 <= datas \/ datas + n1 <= bufs2) by (unfold parked in AP5; unfold hid in SZ; clear - AP5 SZ; lia).
  assert (Q4 : datas + n1 <= lo) by (unfold hid in SZ; clear - CKR0 LOW SZ; lia).
  eapply cps_seq.
  { pose proof (rc_asan_memcpy RT RC) as MC0; unfold memcpy_icontract in MC0;
    eapply MC0 with (lo := lo) (d := bufs2) (s := datas) (bs := firstn (Z.to_nat n1) sbs); rewrite ?SBL1.
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; unfold hid in SZ; clear - SZ; lia
         | |- bytes_at _ _ _ _ => exact SB1
         | |- ART _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- checked_src _ _ _ _ _ _ _ =>
             unfold checked_src; rewrite ?unsigned_lit by (clear - USP LO STb LOR; lia);
             split; [intros _; split; [eapply acc_sub; [exact ACCS| clear; lia | unfold hid in SZ; clear - SZ; lia]
                                    | left; exists datas, rs; split; [exact DSIN| unfold hid in SZ; clear - SZ; lia]]
                   | left; exact Q4]
         | |- checked_dst _ _ _ _ _ _ =>
             unfold checked_dst; rewrite ?unsigned_lit by (clear - USP LO STb LOR; lia);
             split; [intros _; split; [exact ACC2| left; exists bufs2, n1; split; [exact B2IN| clear; lia]]|];
             split; [intros i Hi; right; right; left; exists bufs2, n1; split; [exact B2IN| clear - Hi; lia]| exact WR2]
         | |- call_ok _ _ _ _ _ => call_ok_tac
         | |- _ \/ _ => exact Q3
         | |- (_ <= _ <= _) => first [exact Q7a | exact Q7b]
         | |- (_ < _) => unfold hid in SZ; clear - SZ; lia
         | |- ?g => idtac "LEFT:" g
         end. }
  rewrite SBL1. clear SB1 SBL1 ACCS ACC2 WR2.
  after_call RT AF.
  idtac "MARK after_call 1".
  fold_ag ltac:(fun Hx => unfold PF in Hx; destruct Hx as [Hx1 Hx2]; split; [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [intros e He; exact He| solve [frames_sub_tac]| clear - Hx1; lia] | cbn [outside] in Hx2; clear - Hx2; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(usp - 128, usp)] [e_asan_memcpy; 0x9cc70; 0x9cc20].
  idtac "MARK at the h dispatch".
  destruct (Z.eq_dec h 1) as [HONE|HTWO].
  - (* [comment removed for export] *)
    brT.
    awalk [e_asan_memcpy; 0x9cc20].
    idtac "MARK h = 1 at memcpy L".
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    idtac "MARK at_call L".
    lazymatch goal with A : ART RT Σ ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (af_acc_live RT AF Σ mm bufs2 n1 A B2IN) as (WRS & ACCS);
      pose proof (af_acc_live RT AF Σ mm bufs1 n1 A B1IN) as (WR1 & ACC1) end.
    apply wr_at_rw_CB in WRS; [| unfold hid in SZ; clear - SZ; lia]. destruct WRS as (cbs & SBC).
    pose proof SBC as [[[SBL2 _] _] _]. cbn in SBL2.
    apply u8arr_of_rw_cells in SBC. destruct SBC as [SB2 _].
    assert (SBL1 : Z.of_nat (length cbs) = n1) by (rewrite SBL2; unfold hid in SZ; clear - SZ; lia).
    assert (Q8a : 0 <= bufs1 <= 2^47) by (unfold hid in SP0H, SZ; clear - CKR1 SP0H B10 SZ; lia).
    assert (Q8b : 0 <= bufs2 <= 2^47) by (unfold hid in SP0H, SZ; clear - CKR2 SP0H B20 SZ; lia).
    assert (Q6 : bufs1 + n1 <= bufs2 \/ bufs2 + n1 <= bufs1) by (unfold parked in AP6; clear - AP6; lia).
    assert (Q5 : bufs2 + n1 <= lo) by (clear - CKR2 LOW; lia).
    eapply cps_seq.
    { pose proof (rc_asan_memcpy RT RC) as MC0; unfold memcpy_icontract in MC0;
      eapply MC0 with (lo := lo) (d := bufs1) (s := bufs2) (bs := cbs); rewrite ?SBL1.
      all: lazymatch goal with
           | |- fdfs_only _ => exact FDO
           | |- mat_stable _ => exact MST
           | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; unfold hid in SZ; clear - SZ; lia
           | |- bytes_at _ _ _ _ => exact SB2
           | |- ART _ _ _ => assumption
           | |- mem_inv _ _ => assumption
           | |- checked_src _ _ _ _ _ _ _ =>
               unfold checked_src; rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia);
               split; [intros _; split; [exact ACCS | left; exists bufs2, n1; split; [exact B2IN| clear; lia]] | left; exact Q5]
           | |- checked_dst _ _ _ _ _ _ =>
               unfold checked_dst; rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia);
               split; [intros _; split; [exact ACC1| left; exists bufs1, n1; split; [exact B1IN| clear; lia]]|];
               split; [intros i0 Hi; right; right; left; exists bufs1, n1; split; [exact B1IN| clear - Hi; lia]| exact WR1]
           | |- call_ok _ _ _ _ _ => call_ok_tac
           | |- _ \/ _ => exact Q6
           | |- (_ <= _ <= _) => first [exact Q8a | exact Q8b]
           | |- (_ < _) => unfold hid in SZ; clear - SZ; lia
           | |- ?g => idtac "LEFT:" g
           end. }
    rewrite SBL1. clear SB2 SBL1 SBL2 ACCS ACC1 WR1.
    idtac "MARK memcpy L applied".
    after_call RT AF.
    idtac "MARK after_call L".
    fold_ag ltac:(fun Hx => unfold PF in Hx; destruct Hx as [Hx1 Hx2]; split; [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [intros e He; exact He| solve [frames_sub_tac]| clear - Hx1; lia] | cbn [outside] in Hx2; clear - Hx2; lia]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    walk_to AF MST [(usp - 128, usp); (datad, datad + rd); (bufs1, bufs1 + n1)] [0x9cc98].
    idtac "MARK at lastrow".
    assert (HM1 : 0 <= (h + -1) * wpld /\ (h + -1) * wpld + wpld = wpld * h) by (unfold hid in SZ; clear - SZ; nia).
    rewrite (bv_swrap_small 32 ((h + -1) * wpld)) by (change (bv_half_modulus 32) with (2^31); unfold hid in SZ; clear - SZ HM1; lia).
    rewrite (Z.mod_small ((h + -1) * wpld) 18446744073709551616) by (unfold hid in SZ; clear - SZ HM1; lia).
    set (lined := datad + (h + -1) * wpld * 4) in *.
    set (nl := 4 * wpld) in *.
    assert (GEO : dl_geom lined nl bufs1 n1 w).
    { unfold dl_geom, SEGTOP_A. subst lined nl. unfold hid in SZ. unfold parked in CKH, CKS, CKH1, CKS1, AP2. unfold hid in SP0H.
      clear - SZ HM1 CKR CKH CKS CKR1 CKH1 CKS1 AP2 B10 B116 DD0 DD16 SP0H.
      repeat lazymatch goal with |- _ /\ _ => split end; first [lia | Z.div_mod_to_equations; lia]. }
    idtac "MARK GEO".
    lazymatch goal with A : ART RT Σ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (af_acc_live RT AF Σ mm bufs1 n1 A B1IN) as (WR1 & ACC1);
      pose proof (af_acc_live RT AF Σ mm datad rd A DDIN) as (WRD & ACCD) end.
    apply wr_at_rw_CB in WR1; [| unfold hid in SZ; clear - SZ; lia]. destruct WR1 as (cbs1 & SBC).
    pose proof SBC as [[[SBL9 _] _] _]. cbn in SBL9. apply u8arr_of_rw_cells in SBC.
    assert (UBL : Z.of_nat (length cbs1) = n1) by (rewrite SBL9; unfold hid in SZ; clear - SZ; lia). clear SBL9.
    pose proof (wr_at_sub _ _ _ lined nl WRD ltac:(subst lined; clear - HM1; lia) ltac:(subst lined nl rd; clear - HM1; lia) ltac:(subst nl; unfold hid in SZ; clear - SZ; lia)) as WRL.
    pose proof (acc_sub asegs _ _ _ lined nl ACCD ltac:(subst lined; clear - HM1; lia) ltac:(subst lined nl rd; clear - HM1; lia)) as ACCL.
    apply wr_at_rw_CB in WRL; [| subst nl; unfold hid in SZ; clear - SZ; lia]. destruct WRL as (lbs & LBC).
    pose proof LBC as [[[LBL _] _] _]. cbn in LBL. apply u8arr_of_rw_cells in LBC.
    destruct (u8arr_u32arr _ lined lbs wpld LBC ltac:(rewrite LBL; subst nl; unfold hid in SZ; clear - SZ; lia)) as (wl & UL & ULL0).
    assert (ULL : 4 * Z.of_nat (length wl) = nl) by (rewrite ULL0; subst nl; clear; lia). clear ULL0 LBC LBL lbs.
    idtac "MARK arrays".
    assert (ELI : lined = datad + (h + -1) * wpld * 4) by reflexivity. assert (ENL : nl = 4 * wpld) by reflexivity. clearbody lined nl.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, rd; split; [exact DDIN| clear - Hzz; lia] | split; [intros zz Hzz; right; right; left; exists bufs1, n1; split; [exact B1IN| clear - Hzz; lia] | exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => unfold PF in Hx; destruct Hx as [Hx1 Hx2]; pose proof (PFS _ (conj Hx1 Hx2)) as Hx3; cbn [outside] in Hx2 |- *; clear - Hx2 Hx3 LOR; lia) end.
    idtac "MARK segment closed".
    walk_to AF MST [(usp - 128, usp); (lined, lined + nl); (bufs1, bufs1 + n1)] [0x9cc98].
    replace (Z_to_bv 64 2147450880) with (Z_to_bv 64 SHB) by reflexivity.
    eapply evt_cut.
    { eapply dlr_row; [exact GEO | assumption | exact SBC | exact UBL | exact ACC1 | exact UL | exact ULL | exact ACCL]. }
    intros ms' PO. destruct PO as (t0' & a3' & a4' & a5' & a6' & a7' & s3' & PO). unfold dlr_end in PO.
    destruct PO as (s0' & a0' & a1' & a2' & m' & bs' & wl' & -> & MUl & WMl & MIl & UB' & UBL' & ACCB' & UL' & ULL' & ACCL').
    idtac "MARK lastrow applied".
    lazymatch type of MUl with munch _ ?ma ?mb =>
      lazymatch goal with A : ART RT ?S ma |- _ =>
        loop_art RT AF S mb lo MUl ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, rd; split; [exact DDIN| clear - Hzz ELI ENL HM1; lia] | split; [intros zz Hzz; right; right; left; exists bufs1, n1; split; [exact B1IN| clear - Hzz; lia] | exact I]]]) end end.
    idtac "MARK loop_art".
    lazymatch type of MUl with munch _ ?ma ?mb =>
      loop_transport ma mb MUl ltac:(fun Hx => clear - Hx ELI ENL HM1 SZ CKR CKS CKH CKR1 CKS1 CKH1 LOW LOR SP0H SP0R0 SP0R1 STa; unfold hid in *; unfold parked in *; first [lia | Z.div_mod_to_equations; lia]) end.
    idtac "MARK loop_transport".
    unfold SHB. awalk (@nil Z).
    idtac "MARK epilogue walked".
    cps_stop.
    lazymatch type of AGF with agree_on _ _ ?ma => lazymatch goal with MUx : munch _ ma ?mf |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => unfold PF in Hx; destruct Hx as [Hx1 Hx2]; pose proof (PFS _ (conj Hx1 Hx2)) as Hx3; cbn [outside] in Hx2 |- *;
                               unfold hid in SZ; clear - Hx2 Hx3 LOR ELI ENL HM1 SZ; lia) end end.
    idtac "MARK final agf".
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    exists Σ. eexists.
    split.
    2:{ repeat split; first [reflexivity | lia]. }
    eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-.
    lazymatch goal with A : ART RT Σ ?mf |- _ => exists mf end.
    split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
    unfold lpost, keeps, keepsL, rt_after, rt_pres_fp. rewrite ?unsigned_lit by (clear - USP0 USP1; lia).
    split.
    { split; [| split; assumption]. split; [assumption|]. split; [assumption|]. split; assumption. }
    intros a Ha Ho. apply AGF. split; [exact Ha| exact Ho].
  - (* [comment removed for export] *)
    brF.
    awalk [0x9cc20; e_asan_memcpy].
    idtac "MARK at loop head".
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with MUx : munch _ ?mm _ |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      lazymatch type of MUx with munch _ _ mc =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end end.
    idtac "MARK loop segment closed".
    replace ((h + -1) * 4294967296 / 4294967296) with (h - 1 - 0) by (rewrite Z.div_mul by (clear; lia); clear; lia).
    replace (Z_to_bv 64 (datas + wpls * 4)) with (Z_to_bv 64 (datas + wpls * 4 * (0 + 1))) by (f_equal; clear; lia).
    replace (Z_to_bv 64 datad) with (Z_to_bv 64 (datad + wpld * 4 * 0)) by (f_equal; clear; lia).
    replace (Z_to_bv 64 2147450880) with (Z_to_bv 64 SHB) by reflexivity.
    assert (RK1 : Z.of_nat (Z.to_nat (h - 1)) = h - 1 - 0) by (unfold hid in SZ; clear - SZ HTWO; lia).
    assert (RK3 : (1 <= Z.to_nat (h - 1))%nat) by (unfold hid in SZ; clear - SZ HTWO; lia).
    eapply cps_seq.
    { lazymatch goal with A : ART RT Σ ?mf, MIx : mem_inv asegs ?mf, STx : stk asegs ?mf lo _, LHx : LIBH ?mf, SSPx : io_ssp ?mf, FRx : rw_cells asegs ?mf (usp + -128) _ |- _ =>
        eapply (dlow_rows (Z.to_nat (h - 1)) 0 Σ PMc mf); first [exact RK1 | exact RK3 | exact GEOM | exact FRx | eassumption | clear; lia] end. }
    idtac "MARK rows applied".
    clear RK1 RK3.
    cps_open RT.
    idtac "MARK rows opened".
    lazymatch goal with Hx : ART RT Σ ?mr /\ _ |- _ =>
      destruct Hx as (ARTr & MIr & STr & LHr & SSPr & FRr & WMr & AGr);
      lazymatch type of WMr with wmono _ ?mq mr =>
        (* [comment removed for export] *)
        lazymatch goal with WMx : wmono asegs m mq |- _ => apply (fun h0 => wmono_trans asegs m mq mr h0 WMr) in WMx end;
        agf_call AGF AGr ltac:(fun Hx => unfold PF in Hx; destruct Hx as [Hx1 Hx2]; split;
                                 [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [intros e He; exact He| solve [frames_sub_tac]| clear - Hx1; lia] | exact Hx2]);
        clear WMr AGr;
        repeat match goal with Hx : context [mq] |- _ => clear Hx end
      end end.
    unfold dlow_frame in FRr.
    idtac "MARK after the rows".
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    walk_to AF MST [(usp - 128, usp)] [e_asan_memcpy].
    idtac "MARK h >= 2 at memcpy L".
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    idtac "MARK at_call L".
    lazymatch goal with A : ART RT Σ ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (af_acc_live RT AF Σ mm bufs2 n1 A B2IN) as (WRS & ACCS);
      pose proof (af_acc_live RT AF Σ mm bufs1 n1 A B1IN) as (WR1 & ACC1) end.
    apply wr_at_rw_CB in WRS; [| unfold hid in SZ; clear - SZ; lia]. destruct WRS as (cbs & SBC).
    pose proof SBC as [[[SBL2 _] _] _]. cbn in SBL2.
    apply u8arr_of_rw_cells in SBC. destruct SBC as [SB2 _].
    assert (SBL1 : Z.of_nat (length cbs) = n1) by (rewrite SBL2; unfold hid in SZ; clear - SZ; lia).
    assert (Q8a : 0 <= bufs1 <= 2^47) by (unfold hid in SP0H, SZ; clear - CKR1 SP0H B10 SZ; lia).
    assert (Q8b : 0 <= bufs2 <= 2^47) by (unfold hid in SP0H, SZ; clear - CKR2 SP0H B20 SZ; lia).
    assert (Q6 : bufs1 + n1 <= bufs2 \/ bufs2 + n1 <= bufs1) by (unfold parked in AP6; clear - AP6; lia).
    assert (Q5 : bufs2 + n1 <= lo) by (clear - CKR2 LOW; lia).
    eapply cps_seq.
    { pose proof (rc_asan_memcpy RT RC) as MC0; unfold memcpy_icontract in MC0;
      eapply MC0 with (lo := lo) (d := bufs1) (s := bufs2) (bs := cbs); rewrite ?SBL1.
      all: lazymatch goal with
           | |- fdfs_only _ => exact FDO
           | |- mat_stable _ => exact MST
           | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; unfold hid in SZ; clear - SZ; lia
           | |- bytes_at _ _ _ _ => exact SB2
           | |- ART _ _ _ => assumption
           | |- mem_inv _ _ => assumption
           | |- checked_src _ _ _ _ _ _ _ =>
               unfold checked_src; rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia);
               split; [intros _; split; [exact ACCS | left; exists bufs2, n1; split; [exact B2IN| clear; lia]] | left; exact Q5]
           | |- checked_dst _ _ _ _ _ _ =>
               unfold checked_dst; rewrite ?unsigned_lit by (clear - USP0 USP1 LOR STa; lia);
               split; [intros _; split; [exact ACC1| left; exists bufs1, n1; split; [exact B1IN| clear; lia]]|];
               split; [intros i0 Hi; right; right; left; exists bufs1, n1; split; [exact B1IN| clear - Hi; lia]| exact WR1]
           | |- call_ok _ _ _ _ _ => call_ok_tac
           | |- _ \/ _ => exact Q6
           | |- (_ <= _ <= _) => first [exact Q8a | exact Q8b]
           | |- (_ < _) => unfold hid in SZ; clear - SZ; lia
           | |- ?g => idtac "LEFT:" g
           end. }
    rewrite SBL1. clear SB2 SBL1 SBL2 ACCS ACC1 WR1.
    idtac "MARK memcpy L applied".
    after_call RT AF.
    idtac "MARK after_call L".
    fold_ag ltac:(fun Hx => unfold PF in Hx; destruct Hx as [Hx1 Hx2]; split; [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [intros e He; exact He| solve [frames_sub_tac]| clear - Hx1; lia] | cbn [outside] in Hx2; clear - Hx2; lia]).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    walk_to AF MST [(usp - 128, usp); (datad, datad + rd); (bufs1, bufs1 + n1)] [0x9cc98].
    idtac "MARK at lastrow".
    assert (HM1 : 0 <= (h + -1) * wpld /\ (h + -1) * wpld + wpld = wpld * h) by (unfold hid in SZ; clear - SZ; nia).
    rewrite (bv_swrap_small 32 ((h + -1) * wpld)) by (change (bv_half_modulus 32) with (2^31); unfold hid in SZ; clear - SZ HM1; lia).
    rewrite (Z.mod_small ((h + -1) * wpld) 18446744073709551616) by (unfold hid in SZ; clear - SZ HM1; lia).
    set (lined := datad + (h + -1) * wpld * 4) in *.
    set (nl := 4 * wpld) in *.
    assert (GEO : dl_geom lined nl bufs1 n1 w).
    { unfold dl_geom, SEGTOP_A. subst lined nl. unfold hid in SZ. unfold parked in CKH, CKS, CKH1, CKS1, AP2. unfold hid in SP0H.
      clear - SZ HM1 CKR CKH CKS CKR1 CKH1 CKS1 AP2 B10 B116 DD0 DD16 SP0H.
      repeat lazymatch goal with |- _ /\ _ => split end; first [lia | Z.div_mod_to_equations; lia]. }
    idtac "MARK GEO".
    lazymatch goal with A : ART RT Σ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (af_acc_live RT AF Σ mm bufs1 n1 A B1IN) as (WR1 & ACC1);
      pose proof (af_acc_live RT AF Σ mm datad rd A DDIN) as (WRD & ACCD) end.
    apply wr_at_rw_CB in WR1; [| unfold hid in SZ; clear - SZ; lia]. destruct WR1 as (cbs1 & SBC).
    pose proof SBC as [[[SBL9 _] _] _]. cbn in SBL9. apply u8arr_of_rw_cells in SBC.
    assert (UBL : Z.of_nat (length cbs1) = n1) by (rewrite SBL9; unfold hid in SZ; clear - SZ; lia). clear SBL9.
    pose proof (wr_at_sub _ _ _ lined nl WRD ltac:(subst lined; clear - HM1; lia) ltac:(subst lined nl rd; clear - HM1; lia) ltac:(subst nl; unfold hid in SZ; clear - SZ; lia)) as WRL.
    pose proof (acc_sub asegs _ _ _ lined nl ACCD ltac:(subst lined; clear - HM1; lia) ltac:(subst lined nl rd; clear - HM1; lia)) as ACCL.
    apply wr_at_rw_CB in WRL; [| subst nl; unfold hid in SZ; clear - SZ; lia]. destruct WRL as (lbs & LBC).
    pose proof LBC as [[[LBL _] _] _]. cbn in LBL. apply u8arr_of_rw_cells in LBC.
    destruct (u8arr_u32arr _ lined lbs wpld LBC ltac:(rewrite LBL; subst nl; unfold hid in SZ; clear - SZ; lia)) as (wl & UL & ULL0).
    assert (ULL : 4 * Z.of_nat (length wl) = nl) by (rewrite ULL0; subst nl; clear; lia). clear ULL0 LBC LBL lbs.
    idtac "MARK arrays".
    assert (ELI : lined = datad + (h + -1) * wpld * 4) by reflexivity. assert (ENL : nl = 4 * wpld) by reflexivity. clearbody lined nl.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, rd; split; [exact DDIN| clear - Hzz; lia] | split; [intros zz Hzz; right; right; left; exists bufs1, n1; split; [exact B1IN| clear - Hzz; lia] | exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => unfold PF in Hx; destruct Hx as [Hx1 Hx2]; pose proof (PFS _ (conj Hx1 Hx2)) as Hx3; cbn [outside] in Hx2 |- *; clear - Hx2 Hx3 LOR; lia) end.
    idtac "MARK segment closed".
    walk_to AF MST [(usp - 128, usp); (lined, lined + nl); (bufs1, bufs1 + n1)] [0x9cc98].
    replace (Z_to_bv 64 2147450880) with (Z_to_bv 64 SHB) by reflexivity.
    eapply evt_cut.
    { eapply dlr_row; [exact GEO | assumption | exact SBC | exact UBL | exact ACC1 | exact UL | exact ULL | exact ACCL]. }
    intros ms' PO. destruct PO as (t0' & a3' & a4' & a5' & a6' & a7' & s3' & PO). unfold dlr_end in PO.
    destruct PO as (s0' & a0' & a1' & a2' & m' & bs' & wl' & -> & MUl & WMl & MIl & UB' & UBL' & ACCB' & UL' & ULL' & ACCL').
    idtac "MARK lastrow applied".
    lazymatch type of MUl with munch _ ?ma ?mb =>
      lazymatch goal with A : ART RT ?S ma |- _ =>
        loop_art RT AF S mb lo MUl ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, rd; split; [exact DDIN| clear - Hzz ELI ENL HM1; lia] | split; [intros zz Hzz; right; right; left; exists bufs1, n1; split; [exact B1IN| clear - Hzz; lia] | exact I]]]) end end.
    idtac "MARK loop_art".
    lazymatch type of MUl with munch _ ?ma ?mb =>
      loop_transport ma mb MUl ltac:(fun Hx => clear - Hx ELI ENL HM1 SZ CKR CKS CKH CKR1 CKS1 CKH1 LOW LOR SP0H SP0R0 SP0R1 STa; unfold hid in *; unfold parked in *; first [lia | Z.div_mod_to_equations; lia]) end.
    idtac "MARK loop_transport".
    unfold SHB. awalk (@nil Z).
    idtac "MARK epilogue walked".
    cps_stop.
    lazymatch type of AGF with agree_on _ _ ?ma => lazymatch goal with MUx : munch _ ma ?mf |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => unfold PF in Hx; destruct Hx as [Hx1 Hx2]; pose proof (PFS _ (conj Hx1 Hx2)) as Hx3; cbn [outside] in Hx2 |- *;
                               unfold hid in SZ; clear - Hx2 Hx3 LOR ELI ENL HM1 SZ; lia) end end.
    idtac "MARK final agf".
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    exists Σ. eexists.
    split.
    2:{ repeat split; first [reflexivity | lia]. }
    eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-.
    lazymatch goal with A : ART RT Σ ?mf |- _ => exists mf end.
    split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
    unfold lpost, keeps, keepsL, rt_after, rt_pres_fp. rewrite ?unsigned_lit by (clear - USP0 USP1; lia).
    split.
    { split; [| split; assumption]. split; [assumption|]. split; [assumption|]. split; assumption. }
    intros a Ha Ho. apply AGF. split; [exact Ha| exact Ho].
Qed.

End DLOW.
