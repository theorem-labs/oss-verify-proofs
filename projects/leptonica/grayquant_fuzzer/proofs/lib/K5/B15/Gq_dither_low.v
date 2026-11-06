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
  Lept_iface Lept_lits Lept_litmem Lept_env LeptC_kit Lept_leaf LeptC_leaf LeptL_kit Lept_objkit Lept_chain Gq_iface
  Gq_dither_l1 Gq_dither_l0 Gq_dither_line.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Gm_kit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import LeptB_guard LeptB_guard2.
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
  aclient L frames (usp - 144) a /\ outside [(datad, datad + rd); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1)] a.

(* [comment removed for export] *)
Definition dlow_frame (h w : Z) (t3e t4e s11e s10e s9e s8e s7e s6e s5e s4e s3e s2e s1e s0e rae : word) : list cell :=
  [C8 (Z_to_bv 64 (h + -1)); C8 (Z_to_bv 64 w); C8 t3e; C8 t4e; C8 (Z_to_bv 64 0);
   C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae].

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

(* [comment removed for export] *)
Definition dlow_Q (Σ : rts RT) PMc (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (lo datad w h wpld wpls bufs1 bufs2 : Z)
    : config -> Prop :=
  fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo
          /\ keeps RT Σ Σ' sp [(datad, datad + 4 * (wpld * h)); (bufs1, bufs1 + 4 * wpls); (bufs2, bufs2 + 4 * wpls)] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ <= rt_credit RT Σ'.

(* [comment removed for export] *)
Ltac fold_mkR :=
  lazymatch goal with |- context [MS (TNode
    (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
       (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
    None
    (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2)
       (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty))))) _ _ _ _ _ _] =>
    let t := constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) in
    lazymatch goal with |- context [MS ?R _ _ _ _ _ _] => change R with t end
  end.

(* [comment removed for export] *)
Lemma srliw30_guard : forall x, 0 <= x < 536870912 -> bv_swrap 32 (bv_wrap 32 (x + 536870912) / 1073741824) = 0.
Proof.
  intros x Hx. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  rewrite Z.mod_small by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma negw_sgtz_mask : forall x, 0 < x < 2^31 ->
  Z.land (bv_swrap 32 (0 - Z.b2z (9223372036854775808 <? Z.lxor x 9223372036854775808)) mod 18446744073709551616) x = x.
Proof.
  intros x Hx.
  assert (E : Z.lxor x 9223372036854775808 = x + 9223372036854775808).
  { symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    change 9223372036854775808 with (2^63). rewrite Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec 63 n) as [<-|NE]; [| apply andb_false_r].
    rewrite andb_true_r. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite E. replace (9223372036854775808 <? x + 9223372036854775808) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [Z.b2z]. change (bv_swrap 32 (0 - 1) mod 18446744073709551616) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Definition dlow_rows_post (Σ : rts RT) PMc (gp : word) (usp lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h : Z)
    (t3e t4e s11e s10e s9e s8e s7e s6e s5e s4e s3e s2e s1e s0e rae : word) (mh : mem) : config -> Prop :=
  fun c => ASTA RT Σ PMc (fun ms => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
      ms = MS (mkR ra' (Z_to_bv 64 (usp + -144)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 (h + -1)) (Z_to_bv 64 1) a0' a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 bufs2) (Z_to_bv 64 bufs1) (Z_to_bv 64 (h + -1)) (Z_to_bv 64 datad) (Z_to_bv 64 wpld) (Z_to_bv 64 wpls)
                   (Z_to_bv 64 datas) (Z_to_bv 64 (wpls * 4)) (Z_to_bv 64 (h + -1)) (Z_to_bv 64 1) t3' t4' t5' t6')
              F' (Z_to_bv 64 0x9e22c) (frm_clear fc') None m' (seg_rom asegs)
      /\ ART RT Σ m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -144) /\ LIBH m' /\ io_ssp m'
      /\ rw_cells asegs m' (usp + -144) (dlow_frame h w t3e t4e s11e s10e s9e s8e s7e s6e s5e s4e s3e s2e s1e s0e rae)
      /\ wmono asegs mh m' /\ agree_on (dlow_keep (rt_live RT Σ) (rt_frames RT Σ) usp datad rd bufs1 bufs2 n1) mh m') c.

(* [comment removed for export] *)
Lemma dlow_rows : forall (k : nat) (i : Z) (Σ : rts RT) PMc (mh : mem)
    (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (usp lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h : Z) (t3e t4e s11e s10e s9e s8e s7e s6e s5e s4e s3e s2e s1e s0e rae : word),
  Z.of_nat k = h - 1 - i -> 0 <= i -> (1 <= k)%nat ->
  fdfs_only PMc -> mat_stable PMc ->
  dlow_geom (rt_sp0 RT Σ) lo usp datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ->
  In (datad, rd) (rt_live RT Σ) -> In (datas, rs) (rt_live RT Σ) -> In (bufs1, n1) (rt_live RT Σ) -> In (bufs2, n1) (rt_live RT Σ) ->
  ART RT Σ mh -> mem_inv asegs mh -> stk asegs mh lo (usp + -144) -> LIBH mh -> io_ssp mh ->
  rw_cells asegs mh (usp + -144) (dlow_frame h w t3e t4e s11e s10e s9e s8e s7e s6e s5e s4e s3e s2e s1e s0e rae) ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 (usp + -144)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 (h + -1)) (Z_to_bv 64 1) a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 bufs2) (Z_to_bv 64 bufs1) s4 (Z_to_bv 64 datad) (Z_to_bv 64 wpld) (Z_to_bv 64 wpls)
                                        (Z_to_bv 64 datas) (Z_to_bv 64 (wpls * 4)) (Z_to_bv 64 i) (Z_to_bv 64 1) t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x9e170) (frm_clear fc) None mh (seg_rom asegs))))
    (dlow_rows_post Σ PMc gp usp lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h t3e t4e s11e s10e s9e s8e s7e s6e s5e s4e s3e s2e s1e s0e rae mh).
Proof using AF GP RC.
  induction k as [|k IH]; intros i Σ PMc mh ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 F fc usp lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h
    t3e t4e s11e s10e s9e s8e s7e s6e s5e s4e s3e s2e s1e s0e rae HK HI HK1 FDO MST GEOM DDIN DSIN B1IN B2IN ART0 MI ST LH SSP FR.
  { exfalso. lia. }
  pose proof GEOM as (WPLS & WPLD & WDS & WN1 & W32 & RS & RD & EN1 & ERS & ERD & NRS & HW & HH
                      & DD0 & DD16 & CKR & CKS & CKH & DS0 & DS16 & CKR0 & CKS0 & CKH0 & B10 & B116 & CKR1 & CKS1 & CKH1 & B20 & B216 & CKR2 & CKS2 & CKH2
                      & AP1 & AP2 & AP3 & AP4 & AP5 & AP6 & LOW & LOR & SPT & SPA & SPB & SP0R & SP0W & STa).
  assert (SZ : hid (0 < wpls <= 5001 /\ 0 < wpld <= 626 /\ wpld <= wpls /\ w <= n1 /\ w <= 32 * wpld /\ 0 < rs <= 67108864 /\ 0 < rd <= rs
                    /\ n1 = 4 * wpls /\ rs = 4 * (wpls * h) /\ rd = 4 * (wpld * h) /\ n1 <= rs /\ 0 < w <= 20000 /\ 0 < h <= 20000)) by (unfold hid; clear - WPLS WPLD WDS WN1 W32 RS RD EN1 ERS ERD NRS HW HH; tauto).
  clear WDS WN1 W32 RS RD NRS.
  assert (SP0H : hid (rt_sp0 RT Σ <= 2^47)) by (unfold hid; clear - SP0R; unfold USTACK_TOP in SP0R; lia).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := dlow_keep (rt_live RT Σ) (rt_frames RT Σ) usp datad rd bufs1 bufs2 n1).
  pose proof (agree_refl PF mh) as AGF.
  assert (PFS : forall a, PF a -> usp - 144 <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ mh (usp - 144) a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; clear - H LOW; lia]. }
  assert (USP0 : 0 <= usp) by (clear - LOR STa; lia). assert (USP1 : usp < 2^64) by (unfold hid in SP0H; clear - SPB SP0H; lia).
  unfold dlow_frame in FR.
  (* [comment removed for export] *)
  assert (HIH : 0 <= i /\ i + 1 <= h - 1) by (clear - HK HI HK1; lia).
  assert (P1 : 0 <= (i + 1) * wpls /\ (i + 1) * wpls + wpls <= wpls * h /\ wpls * h <= 16777216) by (unfold hid in SZ; clear - SZ HIH; nia).
  assert (P2 : 0 <= i * wpld /\ i * wpld + wpld + wpld <= wpld * h /\ wpld * h <= 16777216) by (unfold hid in SZ; clear - SZ HIH; nia).
  assert (ROWB : hid (0 <= wpls * 4 * (i + 1) /\ wpls * 4 * (i + 1) + n1 <= rs /\ 0 <= wpld * 4 * i /\ wpld * 4 * i + 4 * wpld <= rd /\ wpld * 4 * i + 4 * wpld + 4 * wpld <= rd)).
  { unfold hid. unfold hid in SZ. rewrite EN1, ERS, ERD. clear - SZ HIH. nia. }
  lib_refresh RT GP. refresh RT AF. unfold shad, SHB in *. clear_acc.
  park_disj. park_ne.
  idtac "MARK rows: setup".
  walk_to AF MST (@nil (Z * Z)) [e_asan_memcpy; 0x9e2d4].
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
  after_call RT AF.
  idtac "MARK rows: after_call A".
  fold_ag ltac:(fun Hx => unfold PF, dlow_keep in Hx; destruct Hx as [Hx1 Hx2]; split; [exact Hx1 | cbn [outside] in Hx2; clear - Hx2; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj. park_ne.
  walk_to AF MST (@nil (Z * Z)) [e_asan_memcpy; 0x9e2d4].
  (* [comment removed for export] *)
  rewrite (Z.mod_small (i + 1) 18446744073709551616) by lia.
  swrap_fix.
  awalk [e_asan_memcpy; 0x9e2d4].
  idtac "MARK rows: at memcpy B".
  rewrite Z.add_0_r. rewrite (Z.mod_small ((i + 1) * wpls) 18446744073709551616) by lia.
  replace (datas + (i + 1) * wpls * 4) with (datas + wpls * 4 * (i + 1)) by (clear; lia).
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
  after_call RT AF.
  idtac "MARK rows: after_call B".
  fold_ag ltac:(fun Hx => unfold PF, dlow_keep in Hx; destruct Hx as [Hx1 Hx2]; split; [exact Hx1 | cbn [outside] in Hx2; clear - Hx2; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj. park_ne.
  (* [comment removed for export] *)
  walk_to AF MST [(usp + -144 - 64, usp + -144); (datad + wpld * 4 * i, datad + wpld * 4 * i + 4 * wpld); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1)] [0x9e1e4; 0x9e2d4].
  swrap_fix. rewrite Z.add_0_r.
  awalk [e_ditherToBinaryLineLow; 0x9e2d4].
  idtac "MARK rows: at leaf".
  pose proof ROWB as RB. unfold hid in RB.
  set (lined := datad + wpld * 4 * i) in *. set (nl := 4 * wpld) in *.
  replace (i * wpld * 4 + datad) with lined by (subst lined; clear; lia).
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
  { lazymatch goal with MIx : mem_inv asegs ?mm, STx : stk asegs ?mm lo _, G1x : ro_cells asegs ?mm 965088 _, G2x : ro_cells asegs ?mm 1013304 _ |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      epose proof (ditherToBinaryLineLow_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -144) lo lined nl bufs1 bufs2 n1 w cbs1 cbs2 wl
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
  unfold SHB. awalk [0x9e170; 0x9e22c; 0x9e2d4].
  idtac "MARK rows: at bne".
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
    { replace (i + 1) with (h + -1) by (clear - EI; lia). reflexivity. }
    repeat match goal with |- _ /\ _ => split end; assumption.
  - (* [comment removed for export] *)
    brT.
    cps_stop.
    idtac "MARK rows: next".
    lazymatch type of AGF with agree_on _ _ ?ma => lazymatch goal with MUx : munch _ ma ?mf |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => unfold PF, dlow_keep in Hx; destruct Hx as [Hx1 Hx2]; pose proof (PFS _ (conj Hx1 Hx2)) as Hx3; cbn [outside] in Hx2 |- *;
                               unfold hid in SZ; clear - Hx2 Hx3 LOR ELI ENL RB SZ; lia) end end.
    replace (Z_to_bv 64 2147450880) with (Z_to_bv 64 SHB) by reflexivity.
    eapply cps_conseq; [ | intros c Hc; exact Hc | ].
    + lazymatch goal with A : ART RT Σ ?mf, MIx : mem_inv asegs ?mf, STx : stk asegs ?mf lo _, LHx : LIBH ?mf, SSPx : io_ssp ?mf, FRx : rw_cells asegs ?mf (usp + -144) _ |- _ =>
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

(* [comment removed for export] *)
Lemma dlow_finish : forall (Σ : rts RT) PMc (m0 mh : mem)
    (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (usp lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h : Z)
    (rae s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3e t4e : word),
  fdfs_only PMc -> mat_stable PMc ->
  dlow_geom (rt_sp0 RT Σ) lo usp datad rd datas rs bufs1 bufs2 n1 wpls wpld w h ->
  In (datad, rd) (rt_live RT Σ) -> In (datas, rs) (rt_live RT Σ) -> In (bufs1, n1) (rt_live RT Σ) -> In (bufs2, n1) (rt_live RT Σ) ->
  ART RT Σ mh -> mem_inv asegs mh -> stk asegs mh lo (usp + -144) -> LIBH mh -> io_ssp mh ->
  rw_cells asegs mh (usp + -144) (dlow_frame h w t3e t4e s11e s10e s9e s8e s7e s6e s5e s4e s3e s2e s1e s0e rae) ->
  wmono asegs m0 mh ->
  agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(datad, datad + rd); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1)] a) m0 mh ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 (usp + -144)) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                        (Z_to_bv 64 bufs2) (Z_to_bv 64 bufs1) s4 (Z_to_bv 64 datad) (Z_to_bv 64 wpld) (Z_to_bv 64 wpls)
                                        (Z_to_bv 64 datas) (Z_to_bv 64 (wpls * 4)) s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x9e22c) (frm_clear fc) None mh (seg_rom asegs))))
    (dlow_Q Σ PMc rae (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo datad w h wpld wpls bufs1 bufs2).
Proof using AF GP RC.
  intros Σ PMc m0 mh ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 s11 t3 t4 t5 t6 F fc usp lo datad rd datas rs bufs1 bufs2 n1 wpls wpld w h
    rae s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3e t4e FDO MST GEOM DDIN DSIN B1IN B2IN ART0 MI ST LH SSP FR WM0 AGF.
  pose proof GEOM as (WPLS & WPLD & WDS & WN1 & W32 & RS & RD & EN1 & ERS & ERD & NRS & HW & HH
                      & DD0 & DD16 & CKR & CKS & CKH & DS0 & DS16 & CKR0 & CKS0 & CKH0 & B10 & B116 & CKR1 & CKS1 & CKH1 & B20 & B216 & CKR2 & CKS2 & CKH2
                      & AP1 & AP2 & AP3 & AP4 & AP5 & AP6 & LOW & LOR & SPT & SPA & SPB & SP0R & SP0W & STa).
  assert (SZ : hid (0 < wpls <= 5001 /\ 0 < wpld <= 626 /\ wpld <= wpls /\ w <= n1 /\ w <= 32 * wpld /\ 0 < rs <= 67108864 /\ 0 < rd <= rs
                    /\ n1 = 4 * wpls /\ rs = 4 * (wpls * h) /\ rd = 4 * (wpld * h) /\ n1 <= rs /\ 0 < w <= 20000 /\ 0 < h <= 20000)) by (unfold hid; clear - WPLS WPLD WDS WN1 W32 RS RD EN1 ERS ERD NRS HW HH; tauto).
  clear WDS WN1 W32 RS RD NRS.
  assert (SP0H : hid (rt_sp0 RT Σ <= 2^47)) by (unfold hid; clear - SP0R; unfold USTACK_TOP in SP0R; lia).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  lazymatch type of AGF with agree_on ?P _ _ => set (PF := P) in AGF end.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ mh usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; clear - H LOW; lia]. }
  assert (USP0 : 0 <= usp) by (clear - LOR STa; lia). assert (USP1 : usp < 2^64) by (unfold hid in SP0H; clear - SPB SP0H; lia).
  (* [comment removed for export] *)
  assert (HM1 : 0 <= (h + -1) * wpld /\ (h + -1) * wpld + wpld = wpld * h /\ wpld * h <= 16777216) by (unfold hid in SZ; clear - SZ; nia).
  unfold dlow_frame in FR.
  lib_refresh RT GP. refresh RT AF. unfold shad, SHB in *. clear_acc.
  park_disj. park_ne.
  idtac "MARK finish: setup".
  walk_to AF MST [(usp - 144, usp)] [e_asan_memcpy; 0x9e2d4].
  idtac "MARK finish: at memcpy L".
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  idtac "MARK finish: at_call L".
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
  idtac "MARK finish: memcpy L applied".
  after_call RT AF.
  idtac "MARK finish: after_call L".
  fold_ag ltac:(fun Hx => unfold PF in Hx; destruct Hx as [Hx1 Hx2]; split; [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [intros e He; exact He| solve [frames_sub_tac]| clear - Hx1; lia] | cbn [outside] in Hx2; clear - Hx2; lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj. park_ne.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 144, usp); (usp - 64, usp); (datad + (h + -1) * wpld * 4, datad + (h + -1) * wpld * 4 + 4 * wpld); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1)]
          [e_ditherToBinaryLineLow; 0x9e2d4].
  idtac "MARK finish: at the tail jump".
  rewrite Z.add_0_r. pose proof SZ as SZv; unfold hid in SZv. rewrite (Z.mod_small ((h + -1) * wpld) 18446744073709551616) by (clear - HM0 HM1 HM3 SZv; lia).
  set (lined := datad + (h + -1) * wpld * 4) in *.
  replace ((h + -1) * wpld * 4 + datad) with lined by (subst lined; clear; lia).
  set (nl := 4 * wpld) in *.
  assert (ELI : lined = datad + (h + -1) * wpld * 4) by reflexivity. assert (ENL : nl = 4 * wpld) by reflexivity. clearbody lined nl.
  assert (GEO2 : dl_geom2 lined nl bufs1 bufs2 n1 w).
  { unfold dl_geom2, dl_geom, SEGTOP_A. unfold hid in SZ, SP0H. unfold parked in CKH, CKS, CKH1, CKS1, CKH2, CKS2, AP2, AP3, AP6.
    clear - SZ HM0 HM1 HM3 ELI ENL CKR CKH CKS CKR1 CKH1 CKS1 CKR2 CKH2 CKS2 AP2 AP3 AP6 B10 B116 B20 B216 DD0 DD16 SP0H.
    repeat lazymatch goal with |- _ /\ _ => split end; first [lia | Z.div_mod_to_equations; lia]. }
  idtac "MARK finish: GEO2".
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
  pose proof (wr_at_sub _ _ _ lined nl WRD ltac:(clear - HM0 HM1 ELI; lia) ltac:(unfold hid in SZ; clear - HM0 HM1 SZ ELI ENL; lia) ltac:(unfold hid in SZ; clear - SZ ENL; lia)) as WRL.
  pose proof (acc_sub asegs _ _ _ lined nl ACCD ltac:(clear - HM0 HM1 ELI; lia) ltac:(unfold hid in SZ; clear - HM0 HM1 SZ ELI ENL; lia)) as ACCL.
  apply wr_at_rw_CB in WRL; [| unfold hid in SZ; clear - SZ ENL; lia]. destruct WRL as (lbs & LBC).
  pose proof LBC as [[[LBL _] _] _]. cbn in LBL. apply u8arr_of_rw_cells in LBC.
  destruct (u8arr_u32arr _ lined lbs wpld LBC ltac:(rewrite LBL; unfold hid in SZ; clear - SZ ENL; lia)) as (wl & UL & ULL0).
  assert (ULL : 4 * Z.of_nat (length wl) = nl) by (rewrite ULL0, ENL; clear; lia). clear ULL0 LBC LBL lbs WRD ACCD.
  idtac "MARK finish: arrays".
  eapply evt_cut.
  { lazymatch goal with MIx : mem_inv asegs ?mm, STx : stk asegs ?mm lo _, G1x : ro_cells asegs ?mm 965088 _, G2x : ro_cells asegs ?mm 1013304 _ |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      epose proof (ditherToBinaryLineLow1_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm usp lo lined nl bufs1 bufs2 n1 w cbs1 cbs2 wl
                     GEO2 MIx UB1 UBL1 ACC1 UB2 UBL2 ACC2 UL ULL ACCL G1x G2x STx) as ZR end.
    eapply ZR; unfold hid in SZ, SP0H; clear - SZ SP0H HM0 HM1 HM3 ELI ENL LOW LOR SPT SP0W CKR CKR1 CKR2; lia. }
  idtac "MARK finish: leaf applied".
  intros ms' PO. unfold ditherToBinaryLineLow_post in PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & bs1' & bs2' & wl' & -> & MUl & WMl & MIl & STl
                  & UB1' & UBL1' & ACC1' & UB2' & UBL2' & ACC2' & UL' & ULL' & ACCL').
  clear UB1 UBL1 ACC1 UB2 UBL2 ACC2 UL ULL ACCL cbs1 cbs2 wl.
  lazymatch type of MUl with munch _ ?ma ?mb =>
    lazymatch goal with A : ART RT ?S ma |- _ =>
      loop_art RT AF S mb lo MUl ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul | split; [intros zz Hzz; left; ul
        | split; [intros zz Hzz; right; right; left; exists datad, rd; split; [exact DDIN| clear - Hzz ELI ENL HM0 HM1 SZ; unfold hid in SZ; lia]
        | split; [intros zz Hzz; right; right; left; exists bufs1, n1; split; [exact B1IN| clear - Hzz; lia]
        | split; [intros zz Hzz; right; right; left; exists bufs2, n1; split; [exact B2IN| clear - Hzz; lia] | exact I]]]]]) end end.
  idtac "MARK finish: loop_art".
  lazymatch type of MUl with munch _ ?ma ?mb =>
    loop_transport ma mb MUl ltac:(fun Hx => clear - Hx ELI ENL HM0 HM1 HM3 SZ CKR CKS CKH CKR1 CKS1 CKH1 CKR2 CKS2 CKH2 LOW LOR SP0H SP0R0 SP0R1 SP0W STa; unfold hid in *; unfold parked in *; first [lia | Z.div_mod_to_equations; lia]) end.
  idtac "MARK finish: loop_transport".
  cps_stop.
  lazymatch type of AGF with agree_on _ _ ?ma => lazymatch goal with MUx : munch _ ma ?mf |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => unfold PF in Hx; destruct Hx as [Hx1 Hx2]; pose proof (PFS _ (conj Hx1 Hx2)) as Hx3; cbn [outside] in Hx2 |- *;
                             unfold hid in SZ; clear - Hx2 Hx3 LOR ELI ENL HM0 HM1 SZ; lia) end end.
  idtac "MARK finish: final agf".
  apply cps_finish. intros c Hc. subst QF. unfold dlow_Q.
  exists Σ. eexists.
  split.
  2:{ repeat split; first [reflexivity | lia]. }
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-.
  lazymatch goal with A : ART RT Σ ?mf |- _ => exists mf end.
  split; [unfold ret_st; do 16 eexists; reflexivity|].
  unfold lpost, keeps, keepsL, rt_after, rt_pres_fp. rewrite ?unsigned_lit by (clear - USP0 USP1; lia).
  split.
  { split; [| split; assumption]. split; [assumption|]. split; [assumption|]. split; assumption. }
  unfold hid in SZ. replace (4 * (wpld * h)) with rd by (clear - SZ; lia). replace (4 * wpls) with n1 by (clear - SZ; lia).
  intros a Ha Ho. apply AGF. split; [exact Ha| exact Ho].
Qed.

Theorem ditherToBinaryLow_ok : ditherToBinaryLow_cps RT.
Proof using AF GP RC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    datad w h wpld datas wpls bufs1 bufs2 FDO MST -> -> (HWR & ->) (HHR & ->) (HPDR & ->) -> (HPSR & ->) -> -> T3E T4E
    HW HH EWD EWS RSB DDC DSC B1C B2C ND ENV RES.
  lazymatch goal with |- cps ?sg ?P _ => change (cps sg P (dlow_Q Σ PMc ra sp gp (Z_to_bv 64 TP_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo datad w h wpld wpls bufs1 bufs2)) end.
  unfold lenv, lres in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
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
  (* [comment removed for export] *)
  park_disj. park_ne.
  carve_frame 144%nat ST.
  walk_to AF MST [(usp - 144, usp)] [e_asan_memcpy; 0x9e2d4].
  (* [comment removed for export] *)
  rewrite (srliw30_guard wpls) by (unfold hid in SZ; clear - SZ; lia). brF.
  awalk [e_asan_memcpy; 0x9e2d4].
  idtac "MARK at memcpy 1".
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
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj. park_ne.
  walk_to AF MST [(usp - 144, usp)] [e_asan_memcpy; 0x9e22c; 0x9e170; 0x9e2d4].
  idtac "MARK at the h dispatch".
  destruct (Z.eq_dec h 1) as [HONE|HTWO].
  - (* [comment removed for export] *)
    brT.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with MUx : munch _ ?mm _ |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      lazymatch type of MUx with munch _ _ mc =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end end.
    idtac "MARK h = 1 segment closed".
    lazymatch goal with FRx : rw_cells asegs ?mf (usp + -144) _ |- _ =>
      replace (Z.land bufs1 3) with 0 in FRx by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by (clear; lia); change (2 ^ 2) with 4; clear - B116; Z.div_mod_to_equations; lia) end.
    lazymatch goal with A : ART RT Σ ?mf, MIx : mem_inv asegs ?mf, STx : stk asegs ?mf lo _, LHx : LIBH ?mf, SSPx : io_ssp ?mf, FRx : rw_cells asegs ?mf (usp + -144) _, WMx : wmono asegs m ?mf |- _ =>
      eapply (dlow_finish Σ PMc m mf); first [exact FDO | exact MST | exact GEOM | exact FRx | exact WMx | exact AGF | eassumption] end.
  - (* [comment removed for export] *)
    brF.
    awalk [0x9e170; 0x9e2d4].
    idtac "MARK at loop head".
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with MUx : munch _ ?mm _ |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      lazymatch type of MUx with munch _ _ mc =>
        agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end end.
    idtac "MARK loop segment closed".
    rewrite (negw_sgtz_mask (h + -1)) by (unfold hid in SZ; clear - SZ HTWO; lia).
    replace (0 <? datad) with true by (symmetry; apply Z.ltb_lt; clear - DD0; lia).
    replace (0 <? datas) with true by (symmetry; apply Z.ltb_lt; clear - DS0; lia).
    cbn [Z.b2z].
    lazymatch goal with FRx : rw_cells asegs ?mf (usp + -144) _ |- _ =>
      replace (Z.land bufs1 3) with 0 in FRx by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by (clear; lia); change (2 ^ 2) with 4; clear - B116; Z.div_mod_to_equations; lia) end.
    assert (RK1 : Z.of_nat (Z.to_nat (h - 1)) = h - 1 - 0) by (unfold hid in SZ; clear - SZ HTWO; lia).
    assert (RK3 : (1 <= Z.to_nat (h - 1))%nat) by (unfold hid in SZ; clear - SZ HTWO; lia).
    eapply cps_seq.
    { lazymatch goal with A : ART RT Σ ?mf, MIx : mem_inv asegs ?mf, STx : stk asegs ?mf lo _, LHx : LIBH ?mf, SSPx : io_ssp ?mf, FRx : rw_cells asegs ?mf (usp + -144) _ |- _ =>
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
    idtac "MARK after the rows".
    lazymatch goal with A : ART RT Σ ?mf, MIx : mem_inv asegs ?mf, STx : stk asegs ?mf lo _, LHx : LIBH ?mf, SSPx : io_ssp ?mf, FRx : rw_cells asegs ?mf (usp + -144) _, WMx : wmono asegs m ?mf |- _ =>
      eapply (dlow_finish Σ PMc m mf); first [exact FDO | exact MST | exact GEOM | exact FRx | exact WMx | exact AGF | eassumption] end.
Qed.

End DLOW.
