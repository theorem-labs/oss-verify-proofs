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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_lits Lept_litmem Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit Lept_objkit Lept_chain RT_frame Gq_iface
  Gq_dither2_l1 Gq_dither2_line.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Gm_kit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma u32arr_agree_yn : forall (m m' : mem) a ws n, u32arr asegs m a ws -> Z.of_nat (length ws) = n ->
  agree_on (fun x => a <= x < a + 4 * n) m m' -> wmono asegs m m' -> u32arr asegs m' a ws.
Proof.
  intros m m' a ws n U L HA W. apply (u32arr_agree m m' a ws U); [| exact W]. rewrite L. exact HA.
Qed.
Ltac u32arr_side AG A :=
  eapply agree_sub; [exact AG|]; cbv beta; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
  first [ acl_dispatch A | split; [acl_dispatch A | first [notin_side | outside_side]] ].
Ltac rt_transport_extra m m' AG ::=
  lept_rt_transport_extra m m' AG;
  repeat match goal with
  | H : u32arr asegs m ?A ?ws |- _ =>
      first [ match goal with WMx : wmono asegs m m', L : Z.of_nat (length ws) = ?n |- _ =>
                apply (u32arr_agree_yn m m' A ws n) in H; [ | exact L | solve [u32arr_side AG A] | exact WMx ] end
            | idtac "note: dropping u32arr fact at a runtime call:" H; clear H ]
  end.

Section D2ROWS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RC : rt_contracts RT.

Local Ltac park_ne := repeat match goal with H : (?a <> ?b) |- _ => lazymatch type of a with Z => change (a <> b) with (parked (a <> b)) in H end end.
Notation ONE := (Z_to_bv 64 1) (only parsing).

(* [comment removed for export] *)
Definition d2r_keep (L : list (Z * Z)) (frames : list (Z * nat)) (sa datad rd bufs1 bufs2 n1 : Z) (a : Z) : Prop :=
  aclient L frames sa a /\ outside [(datad, datad + rd); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1)] a.

(* [comment removed for export] *)
Definition d2r_frame (w wpls datas wpld datad ta t38 t14 : Z) (c88 : word) : list cell :=
  [C8 (Z_to_bv 64 t14); C8 (Z_to_bv 64 wpld); C8 (Z_to_bv 64 datad); C8 (Z_to_bv 64 wpls); C8 c88;
   C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 ta); C8 (Z_to_bv 64 t38)].

(* [comment removed for export] *)
Definition d2r_geom (sp0 lo sa datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ta t38 t14 : Z) : Prop :=
  0 < wpls <= 5001 /\ 0 < wpld <= 1251 /\ wpld <= wpls /\ w <= n1 /\ w <= 16 * wpld /\ 0 < rs <= 67108864 /\ 0 < rd <= rs
  /\ n1 = 4 * wpls /\ rs = 4 * (wpls * h) /\ rd = 4 * (wpld * h) /\ n1 <= rs /\ 0 < w <= 20000 /\ 0 < h <= 20000
  /\ 0 < datad /\ datad mod 16 = 0 /\ datad + rd <= sp0 - STACK_WIN /\ (datad + rd <= 0x10000 \/ SEGTOP_A <= datad) /\ (datad + rd <= 0x7fff7000 \/ 0x10007fff8000 <= datad)
  /\ 0 < datas /\ datas mod 16 = 0 /\ datas + rs <= sp0 - STACK_WIN /\ (datas + rs <= 0x10000 \/ SEGTOP_A <= datas) /\ (datas + rs <= 0x7fff7000 \/ 0x10007fff8000 <= datas)
  /\ 0 < bufs1 /\ bufs1 mod 16 = 0 /\ bufs1 + n1 <= sp0 - STACK_WIN /\ (bufs1 + n1 <= 0x10000 \/ SEGTOP_A <= bufs1) /\ (bufs1 + n1 <= 0x7fff7000 \/ 0x10007fff8000 <= bufs1)
  /\ 0 < bufs2 /\ bufs2 mod 16 = 0 /\ bufs2 + n1 <= sp0 - STACK_WIN /\ (bufs2 + n1 <= 0x10000 \/ SEGTOP_A <= bufs2) /\ (bufs2 + n1 <= 0x7fff7000 \/ 0x10007fff8000 <= bufs2)
  /\ 0 < ta /\ ta mod 16 = 0 /\ ta + 1024 <= sp0 - STACK_WIN /\ (ta + 1024 <= 0x10000 \/ SEGTOP_A <= ta) /\ (ta + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= ta)
  /\ 0 < t38 /\ t38 mod 16 = 0 /\ t38 + 1024 <= sp0 - STACK_WIN /\ (t38 + 1024 <= 0x10000 \/ SEGTOP_A <= t38) /\ (t38 + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= t38)
  /\ 0 < t14 /\ t14 mod 16 = 0 /\ t14 + 1024 <= sp0 - STACK_WIN /\ (t14 + 1024 <= 0x10000 \/ SEGTOP_A <= t14) /\ (t14 + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= t14)
  /\ (datad + rd <= datas \/ datas + rs <= datad) /\ (datad + rd <= bufs1 \/ bufs1 + n1 <= datad) /\ (datad + rd <= bufs2 \/ bufs2 + n1 <= datad)
  /\ (datas + rs <= bufs1 \/ bufs1 + n1 <= datas) /\ (datas + rs <= bufs2 \/ bufs2 + n1 <= datas) /\ (bufs1 + n1 <= bufs2 \/ bufs2 + n1 <= bufs1)
  /\ (ta + 1024 <= datad \/ datad + rd <= ta) /\ (ta + 1024 <= bufs1 \/ bufs1 + n1 <= ta) /\ (ta + 1024 <= bufs2 \/ bufs2 + n1 <= ta)
  /\ (t38 + 1024 <= datad \/ datad + rd <= t38) /\ (t38 + 1024 <= bufs1 \/ bufs1 + n1 <= t38) /\ (t38 + 1024 <= bufs2 \/ bufs2 + n1 <= t38)
  /\ (t14 + 1024 <= datad \/ datad + rd <= t14) /\ (t14 + 1024 <= bufs1 \/ bufs1 + n1 <= t14) /\ (t14 + 1024 <= bufs2 \/ bufs2 + n1 <= t14)
  /\ sp0 - STACK_WIN <= lo /\ lo + LSTK 4 <= sa /\ sa + 272 <= USTACK_TOP /\ sa mod 32 = 0 /\ sa <= sp0
  /\ SEGTOP_A + STACK_WIN <= sp0 <= USTACK_TOP /\ 0x7fff80000000 <= sp0 /\ 0 <= lo.

(* [comment removed for export] *)
Definition d2r_tabs (m : mem) (ta t38 t14 : Z) (tw t38w t14w : list word) : Prop :=
  u32arr asegs m ta tw /\ Z.of_nat (length tw) = 256
  /\ u32arr asegs m t38 t38w /\ Z.of_nat (length t38w) = 256 /\ u32arr asegs m t14 t14w /\ Z.of_nat (length t14w) = 256.

Definition d2r_post (Σ : rts RT) PMc (gp s0 s2 s9 : word) (sa lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ta t38 t14 : Z) (c88 : word)
    (tw t38w t14w : list word) (mh : mem) : config -> Prop :=
  fun c => ASTA RT Σ PMc (fun ms => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
      ms = MS (mkR ra' (Z_to_bv 64 sa) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0 (Z_to_bv 64 sa) a0' a1' a2' a3' a4' a5' a6' a7'
                   s2 (Z_to_bv 64 (wpls * 4)) (Z_to_bv 64 h) (Z_to_bv 64 bufs1) (Z_to_bv 64 datad) (Z_to_bv 64 h) (Z_to_bv 64 bufs2) s9 ONE ONE t3' t4' t5' t6')
              F' (Z_to_bv 64 0xa02c4) (frm_clear fc') None m' (seg_rom asegs)
      /\ ART RT Σ m' /\ mem_inv asegs m' /\ stk asegs m' lo sa /\ LIBH m' /\ io_ssp m'
      /\ rw_cells asegs m' (sa + 56) (d2r_frame w wpls datas wpld datad ta t38 t14 c88)
      /\ d2r_tabs m' ta t38 t14 tw t38w t14w
      /\ wmono asegs mh m' /\ agree_on (d2r_keep (rt_live RT Σ) (rt_frames RT Σ) sa datad rd bufs1 bufs2 n1) mh m') c.

Lemma d2_rows : forall (k : nat) (i : Z) (Σ : rts RT) PMc (mh : mem)
    (ra gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s9 t3 t4 t5 t6 : word) (c88 : word) (F : bvmap 5 word) (fc : bv 32)
    (sa lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ta t38 t14 : Z) (tw t38w t14w : list word),
  Z.of_nat k = h - 1 - i -> 0 <= i -> (1 <= k)%nat ->
  fdfs_only PMc -> mat_stable PMc ->
  d2r_geom (rt_sp0 RT Σ) lo sa datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ta t38 t14 ->
  In (datad, rd) (rt_live RT Σ) -> In (datas, rs) (rt_live RT Σ) -> In (bufs1, n1) (rt_live RT Σ) -> In (bufs2, n1) (rt_live RT Σ) ->
  In (ta, 1024) (rt_live RT Σ) -> In (t38, 1024) (rt_live RT Σ) -> In (t14, 1024) (rt_live RT Σ) ->
  ART RT Σ mh -> mem_inv asegs mh -> stk asegs mh lo sa -> LIBH mh -> io_ssp mh ->
  rw_cells asegs mh (sa + 56) (d2r_frame w wpls datas wpld datad ta t38 t14 c88) ->
  d2r_tabs mh ta t38 t14 tw t38w t14w -> Forall tsmall t38w -> Forall tsmall t14w ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 sa) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 (Z_to_bv 64 sa) a0 a1 a2 a3 a4 a5 a6 a7
                                        s2 (Z_to_bv 64 (wpls * 4)) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 bufs1) (Z_to_bv 64 datad) (Z_to_bv 64 h) (Z_to_bv 64 bufs2) s9 ONE ONE t3 t4 t5 t6)
                                   F (Z_to_bv 64 0xa01f0) (frm_clear fc) None mh (seg_rom asegs))))
    (d2r_post Σ PMc gp s0 s2 s9 sa lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ta t38 t14 c88 tw t38w t14w mh).
Proof using AF GP RC.
  induction k as [|k IH]; intros i Σ PMc mh ra gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s9 t3 t4 t5 t6 c88 F fc sa lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ta t38 t14
    tw t38w t14w HK HI HK1 FDO MST GEOM DDIN DSIN B1IN B2IN TAIN T38IN T14IN ART0 MI ST LH SSP FR TABS TS8 TS4.
  { exfalso. lia. }
  pose proof GEOM as (WPLS & WPLD & WDS & WN1 & W16 & RS & RD & EN1 & ERS & ERD & NRS & HW & HH
                      & DD0 & DD16 & CKR & CKS & CKH & DS0 & DS16 & CKR0 & CKS0 & CKH0 & B10 & B116 & CKR1 & CKS1 & CKH1 & B20 & B216 & CKR2 & CKS2 & CKH2
                      & TA0 & TA16 & CKRT & CKST & CKHT & T380 & T3816 & CKR8 & CKS8 & CKH8 & T140 & T1416 & CKR4 & CKS4 & CKH4
                      & AP1 & AP2 & AP3 & AP4 & AP5 & AP6 & AT1 & AT2 & AT3 & A81 & A82 & A83 & A41 & A42 & A43
                      & LOW & LOR & SPT & SPA & SPB & SP0R & SP0W & STa).
  destruct TABS as (TA & TAL & T38 & T38L & T14 & T14L).
  assert (SZ : hid (0 < wpls <= 5001 /\ 0 < wpld <= 1251 /\ wpld <= wpls /\ w <= n1 /\ w <= 16 * wpld /\ 0 < rs <= 67108864 /\ 0 < rd <= rs
                    /\ n1 = 4 * wpls /\ rs = 4 * (wpls * h) /\ rd = 4 * (wpld * h) /\ n1 <= rs /\ 0 < w <= 20000 /\ 0 < h <= 20000)) by (unfold hid; clear - WPLS WPLD WDS WN1 W16 RS RD EN1 ERS ERD NRS HW HH; tauto).
  clear WDS WN1 W16 RS RD NRS.
  assert (SP0H : hid (rt_sp0 RT Σ <= 2^47)) by (unfold hid; clear - SP0R; unfold USTACK_TOP in SP0R; lia).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := d2r_keep (rt_live RT Σ) (rt_frames RT Σ) sa datad rd bufs1 bufs2 n1).
  pose proof (agree_refl PF mh) as AGF.
  assert (PFS : forall a, PF a -> sa <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ mh sa a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; clear - H LOW; lia]. }
  assert (USP0 : 0 <= sa) by (clear - LOR STa; lia). assert (USP1 : sa < 2^64) by (unfold hid in SP0H; clear - SPB SP0H; lia).
  unfold d2r_frame in FR.
  (* [comment removed for export] *)
  assert (HIH : 0 <= i /\ i + 1 <= h - 1) by (clear - HK HI HK1; lia).
  assert (P1 : 0 <= (i + 1) * wpls /\ (i + 1) * wpls + wpls <= wpls * h /\ wpls * h <= 16777216) by (unfold hid in SZ; clear - SZ HIH; nia).
  assert (P2 : 0 <= i * wpld /\ i * wpld + wpld + wpld <= wpld * h /\ wpld * h <= 16777216) by (unfold hid in SZ; clear - SZ HIH; nia).
  assert (P1h : hid (0 <= (i + 1) * wpls /\ (i + 1) * wpls + wpls <= wpls * h /\ wpls * h <= 16777216)) by (unfold hid; exact P1).
  assert (P2h : hid (0 <= i * wpld /\ i * wpld + wpld + wpld <= wpld * h /\ wpld * h <= 16777216)) by (unfold hid; exact P2).   (* [comment removed for export] *)
  assert (ROWB : hid (0 <= wpls * 4 * (i + 1) /\ wpls * 4 * (i + 1) + n1 <= rs /\ 0 <= wpld * 4 * i /\ wpld * 4 * i + 4 * wpld <= rd /\ wpld * 4 * i + 4 * wpld + 4 * wpld <= rd)).
  { unfold hid. unfold hid in SZ. rewrite EN1, ERS, ERD. clear - SZ HIH. nia. }
  lib_refresh RT GP. refresh RT AF. unfold shad, SHB in *. clear_acc.
  park_disj. park_ne.
  idtac "MARK rows: setup".
  walk_to AF MST (@nil (Z * Z)) [e_asan_memcpy; 0xa03a8].
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
             unfold checked_src; rewrite ?unsigned_lit by (clear - USP0 USP1 STa LOR; lia);
             split; [intros _; split; [exact ACCS | left; exists bufs2, n1; split; [exact B2IN| clear; lia]] | left; exact Q5]
         | |- checked_dst _ _ _ _ _ _ =>
             unfold checked_dst; rewrite ?unsigned_lit by (clear - USP0 USP1 STa LOR; lia);
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
  unpark AT2. unpark AT3. unpark A82. unpark A83. unpark A42. unpark A43.
  after_call RT AF.
  park AT2. park AT3. park A82. park A83. park A42. park A43.
  idtac "MARK rows: after_call A".
  fold_ag ltac:(fun Hx => unfold PF, d2r_keep in Hx; destruct Hx as [Hx1 Hx2]; split; [exact Hx1 | cbn [outside] in Hx2; clear - Hx2; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj. park_ne.
  walk_to AF MST (@nil (Z * Z)) [e_asan_memcpy; 0xa03a8].
  (* [comment removed for export] *)
  change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by (clear; lia). change (2 ^ 64) with 18446744073709551616.
  rewrite ?(Z.mod_small ((i + 1) * wpls) 18446744073709551616) by (pose proof P1h as X; unfold hid in X, SZ; clear - X SZ; lia).
  rewrite ?(Z.mod_small (datas + (i + 1) * wpls * 4) 18446744073709551616) by (pose proof P1h as X; unfold hid in X, SP0H, SZ; clear - X CKR0 DS0 SP0H SZ; lia).
  swrap_fix.
  awalk [e_asan_memcpy; 0xa03a8].
  idtac "MARK rows: at memcpy B".
  rewrite ?Z.add_0_r. rewrite ?(Z.mod_small ((i + 1) * wpls) 18446744073709551616) by (pose proof P1h as X; unfold hid in X, SZ; clear - X SZ; lia).
  try replace (datas + (i + 1) * wpls * 4) with (datas + wpls * 4 * (i + 1)) by (clear; lia).
  swrap_fix. try replace (i + 1 - 1) with i by (clear; lia). try replace (i + 1 + -1) with i by (clear; lia).
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
             unfold checked_src; rewrite ?unsigned_lit by (clear - USP0 USP1 STa LOR; lia);
             split; [intros _; split; [eapply acc_sub; [exact ACCS| clear - RB; lia | unfold hid in SZ; clear - SZ RB; lia]
                                    | left; exists datas, rs; split; [exact DSIN| unfold hid in SZ; clear - SZ RB; lia]]
                   | left; exact Q4]
         | |- checked_dst _ _ _ _ _ _ =>
             unfold checked_dst; rewrite ?unsigned_lit by (clear - USP0 USP1 STa LOR; lia);
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
  unpark AT2. unpark AT3. unpark A82. unpark A83. unpark A42. unpark A43.
  after_call RT AF.
  park AT2. park AT3. park A82. park A83. park A42. park A43.
  idtac "MARK rows: after_call B".
  fold_ag ltac:(fun Hx => unfold PF, d2r_keep in Hx; destruct Hx as [Hx1 Hx2]; split; [exact Hx1 | cbn [outside] in Hx2; clear - Hx2; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj. park_ne.
  (* [comment removed for export] *)
  walk_to AF MST [(sa - 112, sa); (datad + wpld * 4 * i, datad + wpld * 4 * i + 4 * wpld); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1)] [e_ditherTo2bppLineLow; 0xa03a8].
  swrap_fix. rewrite ?Z.add_0_r. try replace (i + 1 - 1) with i by (clear; lia). try replace (i + 1 + -1) with i by (clear; lia).
  (* [comment removed for export] *)
  change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by (clear; lia). change (2 ^ 64) with 18446744073709551616.
  rewrite ?(Z.mod_small (i * wpld) 18446744073709551616) by (pose proof P2h as X; unfold hid in X, SZ; clear - X SZ; lia).
  rewrite ?(Z.mod_small (i * wpld * 4 + datad) 18446744073709551616) by (pose proof P2h as X; unfold hid in X, SP0H, SZ; clear - X CKR DD0 SP0H SZ; lia).
  awalk [e_ditherTo2bppLineLow; 0xa03a8].
  idtac "MARK rows: at leaf".
  pose proof ROWB as RB. unfold hid in RB.
  set (lined := datad + wpld * 4 * i) in *. set (nl := 4 * wpld) in *.
  try replace (i * wpld * 4 + datad) with lined by (subst lined; clear; lia).
  try replace (datad + i * wpld * 4) with lined by (subst lined; clear; lia).
  assert (ELI : lined = datad + wpld * 4 * i) by reflexivity. assert (ENL : nl = 4 * wpld) by reflexivity. clearbody lined nl.
  assert (GEO2 : d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w).
  { unfold d2_geom, SEGTOP_A. unfold hid in SZ, SP0H.
    (* [comment removed for export] *)
    repeat lazymatch goal with |- _ /\ _ => split end.
    all: first [ assumption
               | match goal with H : parked _ |- _ => unpark H; exact H end
               | clear - SZ RB ELI ENL B10 B116 B20 B216 DD0 DD16 TA0 TA16 T380 T3816 T140 T1416 CKR CKR1 CKR2 CKRT CKR8 CKR4 SP0H LOW; first [lia | Z.div_mod_to_equations; lia]
               | match goal with H : parked _ |- _ => unpark H; clear - H SZ RB ELI ENL CKR CKR1 CKR2 CKRT CKR8 CKR4 DD0 B10 B20 TA0 T380 T140 SP0H LOW; lia end ]. }
  idtac "MARK rows: GEO2".
  lazymatch goal with A : ART RT Σ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (af_acc_live RT AF Σ mm bufs1 n1 A B1IN) as (WR1 & ACC1);
    pose proof (af_acc_live RT AF Σ mm bufs2 n1 A B2IN) as (WR2 & ACC2);
    pose proof (af_acc_live RT AF Σ mm datad rd A DDIN) as (WRD & ACCD);
    pose proof (proj2 (af_acc_live RT AF Σ mm ta 1024 A TAIN)) as ACCT;
    pose proof (proj2 (af_acc_live RT AF Σ mm t38 1024 A T38IN)) as ACC8;
    pose proof (proj2 (af_acc_live RT AF Σ mm t14 1024 A T14IN)) as ACC4 end.
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
  { lazymatch goal with MIx : mem_inv asegs ?mm, STx : stk asegs ?mm lo _, G1x : ro_cells asegs ?mm 965088 _, G2x : ro_cells asegs ?mm 1013304 _,
                        TAx : u32arr asegs ?mm ta tw, T38x : u32arr asegs ?mm t38 t38w, T14x : u32arr asegs ?mm t14 t14w |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      epose proof (ditherTo2bppLineLow0_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm sa lo lined nl bufs1 bufs2 n1 ta t38 t14 w cbs1 cbs2 wl tw t38w t14w
                     GEO2 MIx UB1 UBL1 ACC1 UB2 UBL2 ACC2 UL ULL ACCL TAx TAL ACCT T38x T38L ACC8 TS8 T14x T14L ACC4 TS4 G1x G2x STx) as ZR end.
    eapply ZR; unfold hid in SZ, SP0H; clear - SZ SP0H RB ELI ENL LOW LOR SPT SP0W CKR CKR1 CKR2 CKRT CKR8 CKR4; lia. }
  idtac "MARK rows: leaf applied".
  intros ms' PO. unfold ditherTo2bppLineLow_post in PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & bs1' & bs2' & wl' & -> & MUl & WMl & MIl & STl
                  & UB1' & UBL1' & ACC1' & UB2' & UBL2' & ACC2' & UL' & ULL' & ACCL').
  clear UB1 UBL1 ACC1 UB2 UBL2 ACC2 UL ULL ACCL cbs1 cbs2 wl ACCT ACC8 ACC4.
  (* [comment removed for export] *)
  lazymatch type of MUl with munch ?W ?ma ?mb =>
    lazymatch goal with TAx : u32arr asegs ma ta tw, T38x : u32arr asegs ma t38 t38w, T14x : u32arr asegs ma t14 t14w |- _ =>
      pose proof (u32arr_transport asegs W ma mb ta tw TAx MUl WMl ltac:(rewrite TAL; cbn [disjoint_from]; unpark AT1; unpark AT2; unpark AT3; clear - AT1 AT2 AT3 RB ELI ENL CKRT LOW LOR; repeat split; try exact I; lia)) as TAn;
      pose proof (u32arr_transport asegs W ma mb t38 t38w T38x MUl WMl ltac:(rewrite T38L; cbn [disjoint_from]; unpark A81; unpark A82; unpark A83; clear - A81 A82 A83 RB ELI ENL CKR8 LOW LOR; repeat split; try exact I; lia)) as T38n;
      pose proof (u32arr_transport asegs W ma mb t14 t14w T14x MUl WMl ltac:(rewrite T14L; cbn [disjoint_from]; unpark A41; unpark A42; unpark A43; clear - A41 A42 A43 RB ELI ENL CKR4 LOW LOR; repeat split; try exact I; lia)) as T14n;
      clear TAx T38x T14x end end.
  idtac "MARK rows: tables moved".
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
  unfold SHB. awalk [0xa01f0; 0xa02c4; 0xa03a8].
  swrap_fix.
  try replace (i + 1 + 1) with (i + 2) by (clear; lia).
  idtac "MARK rows: at bne".
  destruct k as [|k].
  - (* [comment removed for export] *)
    assert (EI : i + 1 = h - 1) by (clear - HK; lia).
    brF.
    cps_stop.
    idtac "MARK rows: exit".
    lazymatch type of AGF with agree_on _ _ ?ma => lazymatch goal with MUx : munch _ ma ?mf |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => unfold PF, d2r_keep in Hx; destruct Hx as [Hx1 Hx2]; pose proof (PFS _ (conj Hx1 Hx2)) as Hx3; cbn [outside] in Hx2 |- *;
                               unfold hid in SZ; clear - Hx2 Hx3 LOR ELI ENL RB SZ; lia) end end.
    apply cps_finish. intros c Hc. subst QF. unfold d2r_post.
    eapply (ASTA_conseq RT); [exact Hc|]. cbv beta. intros ms <-.
    lazymatch goal with A : ART RT Σ ?mf |- _ => exists mf end.
    do 16 eexists. eexists. eexists.
    split.
    { replace (i + 2) with h by (clear - EI; lia). reflexivity. }
    unfold d2r_tabs, d2r_frame. repeat match goal with |- _ /\ _ => split end; assumption.
  - (* [comment removed for export] *)
    brT.
    cps_stop.
    idtac "MARK rows: next".
    lazymatch type of AGF with agree_on _ _ ?ma => lazymatch goal with MUx : munch _ ma ?mf |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => unfold PF, d2r_keep in Hx; destruct Hx as [Hx1 Hx2]; pose proof (PFS _ (conj Hx1 Hx2)) as Hx3; cbn [outside] in Hx2 |- *;
                               unfold hid in SZ; clear - Hx2 Hx3 LOR ELI ENL RB SZ; lia) end end.
    replace (Z_to_bv 64 2147450880) with (Z_to_bv 64 SHB) by reflexivity.
    replace (i + 2) with (i + 1 + 1) by (clear; lia).
    eapply cps_conseq; [ | intros c Hc; exact Hc | ].
    + lazymatch goal with A : ART RT Σ ?mf, MIx : mem_inv asegs ?mf, STx : stk asegs ?mf lo _, LHx : LIBH ?mf, SSPx : io_ssp ?mf, FRx : rw_cells asegs ?mf (sa + 56) _ |- _ =>
        eapply (IH (i + 1) Σ PMc mf) with (tw := tw) (t38w := t38w) (t14w := t14w) end.
      all: first [eassumption | clear - HK HI; lia | unfold d2r_tabs; repeat match goal with |- _ /\ _ => split end; assumption | idtac].
    + intros c PO. subst QF. unfold d2r_post in PO |- *.
      eapply (ASTA_conseq RT); [exact PO|]. cbv beta.
      intros ms (m2 & ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & t32 & t42 & t52 & t62 & F2 & fc2 & E & A2 & MI2 & ST2 & LH2 & SSP2 & FR2 & TB2 & WM2 & AG2).
      exists m2, ra2, t02, t12, t22, a02, a12, a22, a32, a42, a52, a62, a72, t32, t42, t52, t62, F2, fc2.
      split; [exact E|]. split; [exact A2|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact LH2|]. split; [exact SSP2|]. split; [exact FR2|]. split; [exact TB2|].
      split.
      * lazymatch goal with WMx : wmono asegs mh ?mf |- _ => exact (wmono_trans asegs _ _ _ WMx WM2) end.
      * lazymatch goal with AGFx : agree_on PF mh ?mf |- _ => exact (agree_trans _ _ _ _ AGFx AG2) end.
Qed.

(* [comment removed for export] *)
Definition d2f_post (Σ : rts RT) PMc (gp s0 s2 s9 s10 s11 : word) (sa lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ta t38 t14 : Z)
    (m0 : mem) : config -> Prop :=
  fun c => ASTA RT Σ PMc (fun ms => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
      ms = MS (mkR ra' (Z_to_bv 64 sa) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0 (Z_to_bv 64 sa) a0' a1' a2' a3' a4' a5' a6' a7'
                   s2 (Z_to_bv 64 (wpls * 4)) (Z_to_bv 64 t14) (Z_to_bv 64 bufs1) (Z_to_bv 64 datad) (Z_to_bv 64 h) (Z_to_bv 64 bufs2) s9 s10 s11 t3' t4' t5' t6')
              F' (Z_to_bv 64 0xa0340) (frm_clear fc') None m' (seg_rom asegs)
      /\ ART RT Σ m' /\ mem_inv asegs m' /\ stk asegs m' lo sa /\ LIBH m' /\ io_ssp m'
      /\ rw_cells asegs m' (sa + 56) (d2r_frame w wpls datas wpld datad ta t38 t14 (Z_to_bv 64 0))
      /\ wmono asegs m0 m' /\ agree_on (d2r_keep (rt_live RT Σ) (rt_frames RT Σ) sa datad rd bufs1 bufs2 n1) m0 m') c.

Lemma d2_finish : forall (Σ : rts RT) PMc (m0 mh : mem)
    (ra gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (sa lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ta t38 t14 : Z) (tw t38w t14w : list word),
  fdfs_only PMc -> mat_stable PMc ->
  d2r_geom (rt_sp0 RT Σ) lo sa datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ta t38 t14 ->
  In (datad, rd) (rt_live RT Σ) -> In (datas, rs) (rt_live RT Σ) -> In (bufs1, n1) (rt_live RT Σ) -> In (bufs2, n1) (rt_live RT Σ) ->
  In (ta, 1024) (rt_live RT Σ) -> In (t38, 1024) (rt_live RT Σ) -> In (t14, 1024) (rt_live RT Σ) ->
  ART RT Σ mh -> mem_inv asegs mh -> stk asegs mh lo sa -> LIBH mh -> io_ssp mh ->
  rw_cells asegs mh (sa + 16) [C8 (Z_to_bv 64 (h - 1))] ->
  rw_cells asegs mh (sa + 56) (d2r_frame w wpls datas wpld datad ta t38 t14 (Z_to_bv 64 0)) ->
  d2r_tabs mh ta t38 t14 tw t38w t14w -> Forall tsmall t38w ->
  wmono asegs m0 mh ->
  agree_on (d2r_keep (rt_live RT Σ) (rt_frames RT Σ) sa datad rd bufs1 bufs2 n1) m0 mh ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 sa) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 (Z_to_bv 64 sa) a0 a1 a2 a3 a4 a5 a6 a7
                                        s2 (Z_to_bv 64 (wpls * 4)) s4 (Z_to_bv 64 bufs1) (Z_to_bv 64 datad) (Z_to_bv 64 h) (Z_to_bv 64 bufs2) s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0xa02c4) (frm_clear fc) None mh (seg_rom asegs))))
    (d2f_post Σ PMc gp s0 s2 s9 s10 s11 sa lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ta t38 t14 m0).
Proof using AF GP RC.
  intros Σ PMc m0 mh ra gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s9 s10 s11 t3 t4 t5 t6 F fc sa lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ta t38 t14
    tw t38w t14w FDO MST GEOM DDIN DSIN B1IN B2IN TAIN T38IN T14IN ART0 MI ST LH SSP C16 FR TABS TS8 WM0 AGF.
  pose proof GEOM as (WPLS & WPLD & WDS & WN1 & W16 & RS & RD & EN1 & ERS & ERD & NRS & HW & HH
                      & DD0 & DD16 & CKR & CKS & CKH & DS0 & DS16 & CKR0 & CKS0 & CKH0 & B10 & B116 & CKR1 & CKS1 & CKH1 & B20 & B216 & CKR2 & CKS2 & CKH2
                      & TA0 & TA16 & CKRT & CKST & CKHT & T380 & T3816 & CKR8 & CKS8 & CKH8 & T140 & T1416 & CKR4 & CKS4 & CKH4
                      & AP1 & AP2 & AP3 & AP4 & AP5 & AP6 & AT1 & AT2 & AT3 & A81 & A82 & A83 & A41 & A42 & A43
                      & LOW & LOR & SPT & SPA & SPB & SP0R & SP0W & STa).
  destruct TABS as (TA & TAL & T38 & T38L & T14 & T14L).
  clear T14 T14L.   (* [comment removed for export] *)
  assert (SZ : hid (0 < wpls <= 5001 /\ 0 < wpld <= 1251 /\ wpld <= wpls /\ w <= n1 /\ w <= 16 * wpld /\ 0 < rs <= 67108864 /\ 0 < rd <= rs
                    /\ n1 = 4 * wpls /\ rs = 4 * (wpls * h) /\ rd = 4 * (wpld * h) /\ n1 <= rs /\ 0 < w <= 20000 /\ 0 < h <= 20000)) by (unfold hid; clear - WPLS WPLD WDS WN1 W16 RS RD EN1 ERS ERD NRS HW HH; tauto).
  clear WDS WN1 W16 RS RD NRS.
  assert (SP0H : hid (rt_sp0 RT Σ <= 2^47)) by (unfold hid; clear - SP0R; unfold USTACK_TOP in SP0R; lia).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  lazymatch type of AGF with agree_on ?P _ _ => set (PF := P) in AGF end.
  assert (PFS : forall a, PF a -> sa <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ mh sa a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; clear - H LOW; lia]. }
  assert (USP0 : 0 <= sa) by (clear - LOR STa; lia). assert (USP1 : sa < 2^64) by (unfold hid in SP0H; clear - SPB SP0H; lia).
  unfold d2r_frame in FR.
  (* [comment removed for export] *)
  assert (HM1 : 0 <= (h - 1) * wpld /\ (h - 1) * wpld + wpld = wpld * h /\ wpld * h <= 16777216) by (unfold hid in SZ; clear - SZ; nia).
  assert (HM1h : hid (0 <= (h - 1) * wpld /\ (h - 1) * wpld + wpld = wpld * h /\ wpld * h <= 16777216)) by (unfold hid; exact HM1).
  assert (ROWB : hid (0 <= wpld * 4 * (h - 1) /\ wpld * 4 * (h - 1) + 4 * wpld <= rd)).
  { unfold hid. unfold hid in SZ. rewrite ERD. clear - SZ. nia. }
  lib_refresh RT GP. refresh RT AF. unfold shad, SHB in *. clear_acc.
  park_disj. park_ne.
  idtac "MARK finish: setup".
  walk_to AF MST (@nil (Z * Z)) [e_asan_memcpy; 0xa03a8].
  idtac "MARK finish: at memcpy L".
  at_call RT AF ltac:(cbn [ivls_client]; exact I)
                ltac:(fun Hx => cbn [outside]; exact I).
  idtac "MARK finish: at_call L".
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
             unfold checked_src; rewrite ?unsigned_lit by (clear - USP0 USP1 STa LOR; lia);
             split; [intros _; split; [exact ACCS | left; exists bufs2, n1; split; [exact B2IN| clear; lia]] | left; exact Q5]
         | |- checked_dst _ _ _ _ _ _ =>
             unfold checked_dst; rewrite ?unsigned_lit by (clear - USP0 USP1 STa LOR; lia);
             split; [intros _; split; [exact ACC1| left; exists bufs1, n1; split; [exact B1IN| clear; lia]]|];
             split; [intros i0 Hi; right; right; left; exists bufs1, n1; split; [exact B1IN| clear - Hi; lia]| exact WR1]
         | |- call_ok _ _ _ _ _ => call_ok_tac
         | |- _ \/ _ => exact Q6
         | |- (_ <= _ <= _) => first [exact Q8a | exact Q7a]
         | |- (_ < _) => unfold hid in SZ; clear - SZ; lia
         | |- ?g => idtac "LEFT:" g
         end. }
  rewrite SBL1. clear SB2 SBL1 SBL2 ACCS ACC1 WR1.
  idtac "MARK finish: memcpy L applied".
  unpark AT2. unpark AT3. unpark A82. unpark A83.
  after_call RT AF.
  park AT2. park AT3. park A82. park A83.
  idtac "MARK finish: after_call L".
  fold_ag ltac:(fun Hx => unfold PF, d2r_keep in Hx; destruct Hx as [Hx1 Hx2]; split; [exact Hx1 | cbn [outside] in Hx2; clear - Hx2; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj. park_ne.
  (* [comment removed for export] *)
  walk_to AF MST [(sa - 112, sa); (datad + wpld * 4 * (h - 1), datad + wpld * 4 * (h - 1) + 4 * wpld); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1)] [e_ditherTo2bppLineLow; 0xa03a8].
  swrap_fix. rewrite ?Z.add_0_r.
  (* [comment removed for export] *)
  change 18446744073709551615 with (Z.ones 64). rewrite ?Z.land_ones by (clear; lia). change (2 ^ 64) with 18446744073709551616.
  rewrite ?(Z.mod_small ((h - 1) * wpld) 18446744073709551616) by (pose proof HM1h as X; unfold hid in X, SZ; clear - X SZ; lia).
  rewrite ?(Z.mod_small ((h - 1) * wpld * 4 + datad) 18446744073709551616) by (pose proof HM1h as X; unfold hid in X, SP0H, SZ; clear - X CKR DD0 SP0H SZ; lia).
  rewrite ?(Z.mod_small ((h + -1) * wpld) 18446744073709551616) by (pose proof HM1h as X; unfold hid in X, SZ; clear - X SZ; lia).
  rewrite ?(Z.mod_small ((h + -1) * wpld * 4 + datad) 18446744073709551616) by (pose proof HM1h as X; unfold hid in X, SP0H, SZ; clear - X CKR DD0 SP0H SZ; lia).
  awalk [e_ditherTo2bppLineLow; 0xa03a8].
  idtac "MARK finish: at leaf".
  pose proof ROWB as RB. unfold hid in RB.
  set (lined := datad + wpld * 4 * (h - 1)) in *. set (nl := 4 * wpld) in *.
  try replace ((h - 1) * wpld * 4 + datad) with lined by (subst lined; clear; lia).
  try replace (datad + (h - 1) * wpld * 4) with lined by (subst lined; clear; lia).
  try replace ((h + -1) * wpld * 4 + datad) with lined by (subst lined; clear; lia).
  try replace (datad + (h + -1) * wpld * 4) with lined by (subst lined; clear; lia).
  assert (ELI : lined = datad + wpld * 4 * (h - 1)) by reflexivity. assert (ENL : nl = 4 * wpld) by reflexivity. clearbody lined nl.
  assert (GEO2 : d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w).
  { unfold d2_geom, SEGTOP_A. unfold hid in SZ, SP0H.
    (* [comment removed for export] *)
    repeat lazymatch goal with |- _ /\ _ => split end.
    all: first [ assumption
               | match goal with H : parked _ |- _ => unpark H; exact H end
               | clear - SZ RB ELI ENL B10 B116 B20 B216 DD0 DD16 TA0 TA16 T380 T3816 T140 T1416 CKR CKR1 CKR2 CKRT CKR8 CKR4 SP0H LOW; first [lia | Z.div_mod_to_equations; lia]
               | match goal with H : parked _ |- _ => unpark H; clear - H SZ RB ELI ENL CKR CKR1 CKR2 CKRT CKR8 CKR4 DD0 B10 B20 TA0 T380 T140 SP0H LOW; lia end ]. }
  idtac "MARK finish: GEO2".
  lazymatch goal with A : ART RT Σ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (af_acc_live RT AF Σ mm bufs1 n1 A B1IN) as (WR1 & ACC1);
    pose proof (af_acc_live RT AF Σ mm bufs2 n1 A B2IN) as (WR2 & ACC2);
    pose proof (af_acc_live RT AF Σ mm datad rd A DDIN) as (WRD & ACCD);
    pose proof (proj2 (af_acc_live RT AF Σ mm ta 1024 A TAIN)) as ACCT;
    pose proof (proj2 (af_acc_live RT AF Σ mm t38 1024 A T38IN)) as ACC8 end.
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
  idtac "MARK finish: arrays".
  eapply evt_cut.
  { lazymatch goal with MIx : mem_inv asegs ?mm, STx : stk asegs ?mm lo _, G1x : ro_cells asegs ?mm 965088 _, G2x : ro_cells asegs ?mm 1013304 _,
                        TAx : u32arr asegs ?mm ta tw, T38x : u32arr asegs ?mm t38 t38w |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      epose proof (ditherTo2bppLineLow1_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm sa lo lined nl bufs1 bufs2 n1 ta t38 t14 w cbs1 cbs2 wl tw t38w
                     GEO2 MIx UB1 UBL1 ACC1 UB2 UBL2 ACC2 UL ULL ACCL TAx TAL ACCT T38x T38L ACC8 TS8 G1x G2x STx) as ZR end.
    eapply ZR; unfold hid in SZ, SP0H; clear - SZ SP0H RB ELI ENL LOW LOR SPT SP0W CKR CKR1 CKR2 CKRT CKR8 CKR4; lia. }
  idtac "MARK finish: leaf applied".
  intros ms' PO. unfold ditherTo2bppLineLow_post in PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & bs1' & bs2' & wl' & -> & MUl & WMl & MIl & STl
                  & UB1' & UBL1' & ACC1' & UB2' & UBL2' & ACC2' & UL' & ULL' & ACCL').
  clear UB1 UBL1 ACC1 UB2 UBL2 ACC2 UL ULL ACCL cbs1 cbs2 wl ACCT ACC8.
  (* [comment removed for export] *)
  lazymatch type of MUl with munch ?W ?ma ?mb =>
    lazymatch goal with TAx : u32arr asegs ma ta tw, T38x : u32arr asegs ma t38 t38w |- _ => clear TAx T38x end end.
  lazymatch type of MUl with munch _ ?ma ?mb =>
    lazymatch goal with A : ART RT ?S ma |- _ =>
      loop_art RT AF S mb lo MUl ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul
        | split; [intros zz Hzz; right; right; left; exists datad, rd; split; [exact DDIN| clear - Hzz ELI ENL RB; lia]
        | split; [intros zz Hzz; right; right; left; exists bufs1, n1; split; [exact B1IN| clear - Hzz; lia]
        | split; [intros zz Hzz; right; right; left; exists bufs2, n1; split; [exact B2IN| clear - Hzz; lia] | exact I]]]]) end end.
  idtac "MARK finish: loop_art".
  lazymatch type of MUl with munch _ ?ma ?mb =>
    loop_transport ma mb MUl ltac:(fun Hx => clear - Hx ELI ENL RB SZ CKR CKS CKH CKR1 CKS1 CKH1 CKR2 CKS2 CKH2 LOW LOR SP0H SP0R0 SP0R1 SP0W STa; unfold hid in *; unfold parked in *; first [lia | Z.div_mod_to_equations; lia]) end.
  idtac "MARK finish: loop_transport".
  fix_ret_pc.
  cps_stop.
  lazymatch type of AGF with agree_on _ _ ?ma => lazymatch goal with MUx : munch _ ma ?mf |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => unfold PF, d2r_keep in Hx; destruct Hx as [Hx1 Hx2]; pose proof (PFS _ (conj Hx1 Hx2)) as Hx3; cbn [outside] in Hx2 |- *;
                             unfold hid in SZ; clear - Hx2 Hx3 LOR ELI ENL RB SZ; lia) end end.
  idtac "MARK finish: final agf".
  apply cps_finish. intros c Hc. subst QF. unfold d2f_post.
  eapply (ASTA_conseq RT); [exact Hc|]. cbv beta. intros ms <-.
  lazymatch goal with A : ART RT Σ ?mf |- _ => exists mf end.
  do 16 eexists. eexists. eexists.
  split; [reflexivity|].
  (* [comment removed for export] *)
  unfold d2r_frame. repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

End D2ROWS.
