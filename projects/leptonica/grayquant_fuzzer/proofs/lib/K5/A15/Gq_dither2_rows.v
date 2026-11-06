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
  Gq_dither2_l1 Gq_dither2_l0.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Gm_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section D2ROWS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RC : rt_contracts RT.

Local Ltac park_ne := repeat match goal with H : (?a <> ?b) |- _ => lazymatch type of a with Z => change (a <> b) with (parked (a <> b)) in H end end.

Notation CMASK := (Z_to_bv 64 (-1073741824)) (only parsing).
Notation MASK28 := (Z_to_bv 64 268435455) (only parsing).

(* [comment removed for export] *)
Definition d2r_keep (L : list (Z * Z)) (frames : list (Z * nat)) (sa datad rd bufs1 bufs2 n1 : Z) (a : Z) : Prop :=
  aclient L frames sa a /\ outside [(datad, datad + rd); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1); (sa + 144, sa + 152)] a.

(* [comment removed for export] *)
Definition d2r_frame (w h wpls datas wpld datad bufs1 t38 t14 : Z) (ic : word) : list cell :=
  [C8 (Z_to_bv 64 (w - 1)); C8 (Z_to_bv 64 (w - 1)); C8 (Z_to_bv 64 t38); C8 (Z_to_bv 64 w); C8 (Z_to_bv 64 (h - 1));
   C8 (Z_to_bv 64 (4 * wpls)); C8 (Z_to_bv 64 wpls); C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 wpld); C8 (Z_to_bv 64 datad);
   C8 (Z_to_bv 64 bufs1); C8 ic; C8 (Z_to_bv 64 t14)].

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
  /\ sp0 - STACK_WIN <= lo /\ lo + LSTK 4 <= sa /\ sa + 304 <= USTACK_TOP /\ sa mod 32 = 0 /\ sa <= sp0
  /\ SEGTOP_A + STACK_WIN <= sp0 <= USTACK_TOP /\ 0x7fff80000000 <= sp0 /\ 0 <= lo.

Definition d2r_post (Σ : rts RT) PMc (gp s0 s11 : word) (sa lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ta t38 t14 : Z)
    (mh : mem) : config -> Prop :=
  fun c => ASTA RT Σ PMc (fun ms => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' s2' s9' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
      ms = MS (mkR ra' (Z_to_bv 64 sa) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0 (Z_to_bv 64 sa) a0' a1' a2' a3' a4' a5' a6' (Z_to_bv 64 bufs1)
                   s2' (Z_to_bv 64 30) (Z_to_bv 64 SHB) (Z_to_bv 64 (h - 1)) CMASK MASK28 (Z_to_bv 64 ta) s9' (Z_to_bv 64 bufs2) s11 t3' t4' t5' t6')
              F' (Z_to_bv 64 0x9ead4) (frm_clear fc') None m' (seg_rom asegs)
      /\ ART RT Σ m' /\ mem_inv asegs m' /\ stk asegs m' lo sa /\ LIBH m' /\ io_ssp m'
      /\ rw_cells asegs m' (sa + 56) (d2r_frame w h wpls datas wpld datad bufs1 t38 t14 (Z_to_bv 64 (h - 1)))
      /\ wmono asegs mh m' /\ agree_on (d2r_keep (rt_live RT Σ) (rt_frames RT Σ) sa datad rd bufs1 bufs2 n1) mh m') c.

Local Ltac peel H A k Hc :=
    lazymatch type of H with rw_cells _ _ ?B (?c :: ?rest) =>
      change (c :: rest) with ([c] ++ rest) in H; apply (proj1 (rw_cells_app _ _ _ _)) in H; destruct H as [Hc H];
      cbn [cells_size csize Z.of_nat Pos.of_succ_nat Pos.succ Nat.add] in H;
      replace (B + 8) with (A + k) in H by lia
    end.

(* [comment removed for export] *)
Lemma d2r_frame_cells : forall (m : mem) (sa w h wpls datas wpld datad bufs1 t38 t14 : Z) (ic : word),
  rw_cells asegs m (sa + 56) (d2r_frame w h wpls datas wpld datad bufs1 t38 t14 ic) ->
  rw_cells asegs m (sa + 56) [C8 (Z_to_bv 64 (w - 1))] /\ rw_cells asegs m (sa + 64) [C8 (Z_to_bv 64 (w - 1))]
  /\ rw_cells asegs m (sa + 72) [C8 (Z_to_bv 64 t38)] /\ rw_cells asegs m (sa + 80) [C8 (Z_to_bv 64 w)]
  /\ rw_cells asegs m (sa + 88) [C8 (Z_to_bv 64 (h - 1))] /\ rw_cells asegs m (sa + 136) [C8 (Z_to_bv 64 bufs1)]
  /\ rw_cells asegs m (sa + 144) [C8 ic] /\ rw_cells asegs m (sa + 152) [C8 (Z_to_bv 64 t14)].
Proof.
  intros m sa w h wpls datas wpld datad bufs1 t38 t14 ic FR. unfold d2r_frame in FR.
  peel FR sa 64 C56. peel FR sa 72 C64. peel FR sa 80 C72. peel FR sa 88 C80. peel FR sa 96 C88. peel FR sa 104 C96.
  peel FR sa 112 C104. peel FR sa 120 C112. peel FR sa 128 C120. peel FR sa 136 C128. peel FR sa 144 C136. peel FR sa 152 C144.
  repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
Lemma d2_rows : forall (k : nat) (i : Z) (Σ : rts RT) PMc (mh : mem)
    (ra gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 s2 s9 s11 t3 t4 t5 t6 : word) (ic : word) (F : bvmap 5 word) (fc : bv 32)
    (sa lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ta t38 t14 : Z),
  Z.of_nat k = h - 1 - i -> 0 <= i -> (1 <= k)%nat ->
  fdfs_only PMc -> mat_stable PMc ->
  d2r_geom (rt_sp0 RT Σ) lo sa datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ta t38 t14 ->
  In (datad, rd) (rt_live RT Σ) -> In (datas, rs) (rt_live RT Σ) -> In (bufs1, n1) (rt_live RT Σ) -> In (bufs2, n1) (rt_live RT Σ) ->
  In (ta, 1024) (rt_live RT Σ) -> In (t38, 1024) (rt_live RT Σ) -> In (t14, 1024) (rt_live RT Σ) ->
  ART RT Σ mh -> mem_inv asegs mh -> stk asegs mh lo sa -> LIBH mh -> io_ssp mh ->
  rw_cells asegs mh (sa + 56) (d2r_frame w h wpls datas wpld datad bufs1 t38 t14 ic) ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 sa) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 (Z_to_bv 64 sa) a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 bufs1)
                                        s2 (Z_to_bv 64 30) (Z_to_bv 64 SHB) (Z_to_bv 64 i) CMASK MASK28 (Z_to_bv 64 ta) s9 (Z_to_bv 64 bufs2) s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x9e6a8) (frm_clear fc) None mh (seg_rom asegs))))
    (d2r_post Σ PMc gp s0 s11 sa lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ta t38 t14 mh).
Proof using AF GP RC.
  induction k as [|k IH]; intros i Σ PMc mh ra gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 s2 s9 s11 t3 t4 t5 t6 ic F fc sa lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ta t38 t14
    HK HI HK1 FDO MST GEOM DDIN DSIN B1IN B2IN TAIN T38IN T14IN ART0 MI ST LH SSP FR.
  { exfalso. lia. }
  pose proof GEOM as (WPLS & WPLD & WDS & WN1 & W16 & RS & RD & EN1 & ERS & ERD & NRS & HW & HH
                      & DD0 & DD16 & CKR & CKS & CKH & DS0 & DS16 & CKR0 & CKS0 & CKH0 & B10 & B116 & CKR1 & CKS1 & CKH1 & B20 & B216 & CKR2 & CKS2 & CKH2
                      & TA0 & TA16 & CKRT & CKST & CKHT & T380 & T3816 & CKR8 & CKS8 & CKH8 & T140 & T1416 & CKR4 & CKS4 & CKH4
                      & AP1 & AP2 & AP3 & AP4 & AP5 & AP6 & AT1 & AT2 & AT3 & A81 & A82 & A83 & A41 & A42 & A43
                      & LOW & LOR & SPT & SPA & SPB & SP0R & SP0W & STa).
  assert (SZ : hid (0 < wpls <= 5001 /\ 0 < wpld <= 1251 /\ wpld <= wpls /\ w <= n1 /\ w <= 16 * wpld /\ 0 < rs <= 67108864 /\ 0 < rd <= rs
                    /\ n1 = 4 * wpls /\ rs = 4 * (wpls * h) /\ rd = 4 * (wpld * h) /\ n1 <= rs /\ 0 < w <= 20000 /\ 0 < h <= 20000)) by (unfold hid; clear - WPLS WPLD WDS WN1 W16 RS RD EN1 ERS ERD NRS HW HH; tauto).
  clear WPLS WPLD WDS WN1 W16 RS RD NRS.
  assert (SP0H : hid (rt_sp0 RT Σ <= 2^47)) by (unfold hid; clear - SP0R; unfold USTACK_TOP in SP0R; lia).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := d2r_keep (rt_live RT Σ) (rt_frames RT Σ) sa datad rd bufs1 bufs2 n1).
  pose proof (agree_refl PF mh) as AGF.
  assert (PFS : forall a, PF a -> sa <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ mh sa a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; clear - H LOW; lia]. }
  unfold d2r_frame in FR.
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
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; unfold hid in SZ; clear - SZ EN1; lia
         | |- bytes_at _ _ _ _ => exact SB2
         | |- ART _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- checked_src _ _ _ _ _ _ _ =>
             unfold checked_src; rewrite ?unsigned_lit by (clear - STa LOR SPT; lia);
             split; [intros _; split; [exact ACCS | left; exists bufs2, n1; split; [exact B2IN| clear; lia]] | left; exact Q5]
         | |- checked_dst _ _ _ _ _ _ =>
             unfold checked_dst; rewrite ?unsigned_lit by (clear - STa LOR SPT; lia);
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
  fold_ag ltac:(fun Hx => unfold PF, d2r_keep in Hx; destruct Hx as [Hx1 Hx2]; split; [exact Hx1 | cbn [outside] in Hx2; clear - Hx2; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(sa + 144, sa + 152)] [e_asan_memcpy].
  idtac "MARK rows: at memcpy B".
  (* [comment removed for export] *)
  change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by (clear; lia). change (2 ^ 64) with 18446744073709551616.
  rewrite (Z.mod_small wpls 18446744073709551616) by (unfold hid in SZ; clear - SZ; lia).
  pose proof ROWB as RB. unfold hid in RB.
  rewrite (Z.mod_small ((i + 1) * wpls) 18446744073709551616) by (unfold hid in SZ; clear - SZ HK HI RB; nia).
  replace (datas + (i + 1) * wpls * 4) with (datas + wpls * 4 * (i + 1)) by (clear; lia).
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul | exact I])
                ltac:(fun Hx => cbn [outside]; unfold PF, d2r_keep in Hx; destruct Hx as [_ Hx2]; cbn [outside] in Hx2; split; [clear - Hx2; lia | exact I]).
  idtac "MARK rows: at_call B".
  lazymatch goal with A : ART RT Σ ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    pose proof (af_acc_live RT AF Σ mm datas rs A DSIN) as (WRS & ACCS);
    pose proof (af_acc_live RT AF Σ mm bufs2 n1 A B2IN) as (WR2 & ACC2) end.
  apply wr_at_rw_CB in WRS; [| unfold hid in SZ; clear - SZ; lia]. destruct WRS as (sbs & SBC).
  pose proof SBC as [[[SBL _] _] _]. cbn in SBL.
  apply u8arr_of_rw_cells in SBC. destruct SBC as [SB _].
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
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; unfold hid in SZ; clear - SZ EN1; lia
         | |- bytes_at _ _ _ _ => exact SB1
         | |- ART _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- checked_src _ _ _ _ _ _ _ =>
             unfold checked_src; rewrite ?unsigned_lit by (clear - STa LOR SPT; lia);
             split; [intros _; split; [eapply acc_sub; [exact ACCS| clear - RB; lia | unfold hid in SZ; clear - SZ RB; lia]
                                    | left; exists datas, rs; split; [exact DSIN| unfold hid in SZ; clear - SZ RB; lia]]
                   | left; exact Q4]
         | |- checked_dst _ _ _ _ _ _ =>
             unfold checked_dst; rewrite ?unsigned_lit by (clear - STa LOR SPT; lia);
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
  fold_ag ltac:(fun Hx => unfold PF, d2r_keep in Hx; destruct Hx as [Hx1 Hx2]; split; [exact Hx1 | cbn [outside] in Hx2; clear - Hx2; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  walk_to AF MST [(datad + wpld * 4 * i, datad + wpld * 4 * i + 4 * wpld); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1)] [0x9e6fc].
  idtac "MARK rows: at line".
  (* [comment removed for export] *)
  pose proof ROWB as RB. unfold hid in RB.
  change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by (clear; lia). change (2 ^ 64) with 18446744073709551616.
  rewrite (Z.mod_small wpld 18446744073709551616) by (unfold hid in SZ; clear - SZ; lia).
  rewrite (Z.mod_small (i * wpld) 18446744073709551616) by (unfold hid in SZ; clear - SZ HK HI RB; nia).
  replace (datad + i * wpld * 4) with (datad + wpld * 4 * i) by (clear; lia).
  set (lined := datad + wpld * 4 * i) in *. set (nl := 4 * wpld) in *.
  assert (ELI : lined = datad + wpld * 4 * i) by reflexivity. assert (ENL : nl = 4 * wpld) by reflexivity. clearbody lined nl.
  assert (GEO2 : d2_geom lined nl bufs1 bufs2 n1 ta t38 t14 w).
  { unfold d2_geom, SEGTOP_A. unfold hid in SZ, SP0H.
    unpark CKH; unpark CKS; unpark CKH1; unpark CKS1; unpark CKH2; unpark CKS2; unpark CKHT; unpark CKST; unpark CKH8; unpark CKS8; unpark CKH4; unpark CKS4.
    unpark AP2; unpark AP3; unpark AP6; unpark AT1; unpark AT2; unpark AT3; unpark A81; unpark A82; unpark A83; unpark A41; unpark A42; unpark A43.
    clear - SZ RB ELI ENL EN1 CKR CKH CKS CKR1 CKH1 CKS1 CKR2 CKH2 CKS2 CKRT CKHT CKST CKR8 CKH8 CKS8 CKR4 CKH4 CKS4
            AP2 AP3 AP6 AT1 AT2 AT3 A81 A82 A83 A41 A42 A43 B10 B116 B20 B216 DD0 DD16 TA0 TA16 T380 T3816 T140 T1416 SP0H.
    repeat lazymatch goal with |- _ /\ _ => split end.
    all: try assumption.
    all: let t1 := fun H => (clear - H SZ RB ELI ENL EN1 CKR CKR1 CKR2 CKRT CKR8 CKR4 B10 B116 B20 B216 DD0 DD16 TA0 TA16 T380 T3816 T140 T1416 SP0H; first [lia | Z.div_mod_to_equations; lia]) in
         first [ t1 SZ | t1 CKH | t1 CKS | t1 AP2 | t1 AP3 | t1 AP6 | t1 AT1 | t1 A81 | t1 A41 | t1 CKH1 | t1 CKS1 | t1 CKH2 | t1 CKS2
               | t1 CKHT | t1 CKST | t1 CKH8 | t1 CKS8 | t1 CKH4 | t1 CKS4 | t1 AT2 | t1 AT3 | t1 A82 | t1 A83 | t1 A42 | t1 A43 ]. }
  idtac "MARK rows: GEO2".
  lazymatch goal with A : ART RT Σ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (af_acc_live RT AF Σ mm bufs1 n1 A B1IN) as (WR1 & ACC1);
    pose proof (af_acc_live RT AF Σ mm bufs2 n1 A B2IN) as (WR2 & ACC2);
    pose proof (af_acc_live RT AF Σ mm datad rd A DDIN) as (WRD & ACCD);
    pose proof (af_acc_live RT AF Σ mm ta 1024 A TAIN) as (WRT & ACCT);
    pose proof (af_acc_live RT AF Σ mm t38 1024 A T38IN) as (WR8 & ACC8);
    pose proof (af_acc_live RT AF Σ mm t14 1024 A T14IN) as (WR4 & ACC4) end.
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
  (* [comment removed for export] *)
  apply wr_at_rw_CB in WRT; [| clear; lia]. destruct WRT as (tbs & TBC). pose proof TBC as [[[TBL _] _] _]. cbn in TBL. apply u8arr_of_rw_cells in TBC.
  destruct (u8arr_u32arr _ ta tbs 256 TBC ltac:(rewrite TBL; clear; lia)) as (tw & UT & UTL). clear TBC TBL tbs.
  apply wr_at_rw_CB in WR8; [| clear; lia]. destruct WR8 as (tbs & TBC). pose proof TBC as [[[TBL _] _] _]. cbn in TBL. apply u8arr_of_rw_cells in TBC.
  destruct (u8arr_u32arr _ t38 tbs 256 TBC ltac:(rewrite TBL; clear; lia)) as (t38w & U38 & U38L). clear TBC TBL tbs.
  apply wr_at_rw_CB in WR4; [| clear; lia]. destruct WR4 as (tbs & TBC). pose proof TBC as [[[TBL _] _] _]. cbn in TBL. apply u8arr_of_rw_cells in TBC.
  destruct (u8arr_u32arr _ t14 tbs 256 TBC ltac:(rewrite TBL; clear; lia)) as (t14w & U14 & U14L). clear TBC TBL tbs.
  idtac "MARK rows: arrays".
  (* [comment removed for export] *)
  lazymatch goal with FRx : rw_cells asegs ?mm (sa + 56) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (d2r_frame_cells mm sa w h wpls datas wpld datad bufs1 t38 t14 (Z_to_bv 64 (i + 1)) FRx) as (C56 & C64 & C72 & C80 & C88 & C136 & C144 & C152) end.
  idtac "MARK rows: cells".
  eapply evt_cut.
  { lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      epose proof (d2l0_line _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm sa lined nl bufs1 bufs2 n1 ta t38 t14 w cbs1 cbs2 wl tw t38w t14w
                     GEO2 MIx UB1 UBL1 ACC1 UB2 UBL2 ACC2 UL ULL ACCL UT UTL ACCT U38 U38L ACC8 U14 U14L ACC4 C56 C64 C72 C80 C136 C152) as ZR end.
    eapply ZR; unfold hid in SZ, SP0H; clear - SZ SP0H RB ELI ENL LOW LOR SPT SPA SP0W CKR CKR1 CKR2; lia. }
  idtac "MARK rows: leaf applied".
  intros ms' PO. unfold d2l0_lend in PO.
  destruct PO as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & s2' & s5' & t3' & t4' & t5' & t6' & m' & bs1' & bs2' & wl' & -> & MUl & WMl & MIl
                  & UB1' & UBL1' & ACC1' & UB2' & UBL2' & ACC2' & UL' & ULL' & ACCL' & UT' & ACCT' & U38' & ACC38' & U14' & ACC14').
  clear UB1 UBL1 ACC1 UB2 UBL2 ACC2 UL ULL ACCL cbs1 cbs2 wl C56 C64 C72 C80 C88 C136 C144 C152.
  clear UB1' UBL1' UB2' UBL2' UL' ULL' UT' U38' U14' UT UTL U38 U38L U14 U14L.
  lazymatch type of MUl with munch _ ?ma ?mb =>
    lazymatch goal with A : ART RT ?S ma |- _ =>
      loop_art RT AF S mb lo MUl ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists datad, rd; split; [exact DDIN| clear - Hzz ELI ENL RB; lia]
        | split; [intros zz Hzz; right; right; left; exists bufs1, n1; split; [exact B1IN| clear - Hzz; lia]
        | split; [intros zz Hzz; right; right; left; exists bufs2, n1; split; [exact B2IN| clear - Hzz; lia] | exact I]]]) end end.
  idtac "MARK rows: loop_art".
  lazymatch type of MUl with munch _ ?ma ?mb =>
    loop_transport ma mb MUl ltac:(fun Hx => clear - Hx ELI ENL RB SZ CKR CKS CKH CKR1 CKS1 CKH1 CKR2 CKS2 CKH2 LOW LOR SPT SP0H SP0R0 SP0R1 SP0W STa; unfold hid in *; unfold parked in *; first [lia | Z.div_mod_to_equations; lia]) end.
  idtac "MARK rows: loop_transport".
  fix_ret_pc.
  unfold SHB. awalk [0x9e6a8; 0x9ead4].
  idtac "MARK rows: at bne".
  destruct k as [|k].
  - (* [comment removed for export] *)
    assert (EI : i + 1 = h - 1) by (clear - HK; lia).
    brF.
    awalk [0x9ead4].
    cps_stop.
    idtac "MARK rows: exit".
    lazymatch type of AGF with agree_on _ _ ?ma => lazymatch goal with MUx : munch _ ma ?mf |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => unfold PF, d2r_keep in Hx; destruct Hx as [Hx1 Hx2]; pose proof (PFS _ (conj Hx1 Hx2)) as Hx3; cbn [outside] in Hx2 |- *;
                               unfold hid in SZ; clear - Hx2 Hx3 LOR ELI ENL RB SZ; lia) end end.
    apply cps_finish. intros c Hc. subst QF. unfold d2r_post.
    eapply (ASTA_conseq RT); [exact Hc|]. cbv beta. intros ms <-.
    lazymatch goal with A : ART RT Σ ?mf |- _ => exists mf end.
    do 17 eexists. eexists. eexists.
    split.
    { rewrite EI. reflexivity. }
    rewrite EI in *. unfold d2r_frame.
    repeat match goal with |- _ /\ _ => split end; assumption.
  - (* [comment removed for export] *)
    brT.
    cps_stop.
    idtac "MARK rows: next".
    lazymatch type of AGF with agree_on _ _ ?ma => lazymatch goal with MUx : munch _ ma ?mf |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => unfold PF, d2r_keep in Hx; destruct Hx as [Hx1 Hx2]; pose proof (PFS _ (conj Hx1 Hx2)) as Hx3; cbn [outside] in Hx2 |- *;
                               unfold hid in SZ; clear - Hx2 Hx3 LOR ELI ENL RB SZ; lia) end end.
    replace (Z_to_bv 64 2147450880) with (Z_to_bv 64 SHB) by reflexivity.
    eapply cps_conseq; [ | intros c Hc; exact Hc | ].
    + lazymatch goal with A : ART RT Σ ?mf, MIx : mem_inv asegs ?mf, STx : stk asegs ?mf lo _, LHx : LIBH ?mf, SSPx : io_ssp ?mf, FRx : rw_cells asegs ?mf (sa + 56) _ |- _ =>
        eapply (IH (i + 1) Σ PMc mf) with (ic := Z_to_bv 64 (i + 1)) (h := h) end.
      all: first [eassumption | clear - HK HI; lia].
    + intros c PO. subst QF. unfold d2r_post in PO |- *.
      eapply (ASTA_conseq RT); [exact PO|]. cbv beta.
      intros ms (m2 & ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & s22 & s92 & t32 & t42 & t52 & t62 & F2 & fc2 & E & A2 & MI2 & ST2 & LH2 & SSP2 & FR2 & WM2 & AG2).
      exists m2, ra2, t02, t12, t22, a02, a12, a22, a32, a42, a52, a62, s22, s92, t32, t42, t52, t62, F2, fc2.
      split; [exact E|]. split; [exact A2|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact LH2|]. split; [exact SSP2|]. split; [exact FR2|].
      split.
      * lazymatch goal with WMx : wmono asegs mh ?mf |- _ => exact (wmono_trans asegs _ _ _ WMx WM2) end.
      * lazymatch goal with AGFx : agree_on PF mh ?mf |- _ => exact (agree_trans _ _ _ _ AGFx AG2) end.
Qed.

End D2ROWS.
