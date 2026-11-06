(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Km_setelem Km_iface Km_kit D_iface D_defs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import LeptB_guard LeptB_guard2 LeptB_guard3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac rt_transport_extra m m' AG ::=
  lept_rt_transport_extra m m' AG;
  repeat match goal with
  | H : u64arr asegs m ?A ?ws |- _ =>
      first [ apply (u64arr_agree_nw asegs m m' A ws) in H; [ | solve [agree_range AG A ltac:(fun A => acl_dispatch A)] ]
            | idtac "note: dropping u64arr:" H; clear H ]
  end.

Definition e_create2d : Z := 0x91b18.

Section KCREATE.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
(* [comment removed for export] *)
Hypothesis CK : calloc_contractK RT.
(* [comment removed for export] *)
Hypothesis TRC1 : In [0x9198c] CLIENT_TRACES.
Hypothesis TRC2 : In [0x91c14] CLIENT_TRACES.
Hypothesis TRC3 : In [0x91c3c] CLIENT_TRACES.

(* [comment removed for export] *)
Definition c2d_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (h w : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 h -> a1 = Z_to_bv 64 w -> 3 <= h <= 20000 -> 3 <= w <= 20000 -> h * w <= 2^26 ->
  lenv RT Σ m sp lo (LSTK 2) -> lres RT Σ 0 (h + 1) (km_cost h w) ->
  sec_bytes (rt_live RT Σ) + 8 * h + 4 * (w * h) <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_create2d m)))
    (fun c => exists (Σ' : rts RT) (data : Z) (rows : list Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 data) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ u64arr asegs m' data (map (Z_to_bv 64) rows)) c
       /\ rt_live RT Σ' = rev (map (fun r => (r, 4 * w)) rows) ++ (data, 8 * h) :: rt_live RT Σ
       /\ Z.of_nat (length rows) = h /\ Forall (fun r => 0 < r /\ r mod 16 = 0) rows /\ 0 < data /\ data mod 16 = 0
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - km_cost h w <= rt_credit RT Σ').

Lemma create2d_ok : c2d_cps.
Proof using AF GP CK TRC2 TRC3.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo h w
    FDO MST -> -> -> HB WB HWB ENV RES SECB.
  unfold lpost, lenv, lres, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_create2d, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (KCB : km_cost h w <= rt_credit RT Σ) by exact CRB.
  assert (MC8 : 0 <= mcost (8 * h) <= km_cost h w) by (unfold km_cost, mcost; destruct (Z.leb_spec (8 * h) 64512), (Z.leb_spec (4 * w) 64512); nia).
  assert (MC4 : 0 <= mcost (4 * w)) by (unfold mcost; destruct (Z.leb_spec (4 * w) 64512); lia).
  refresh RT AF.
  park_disj.
  walk_to AF MST [(usp + -80, usp)] [e_calloc].
  rewrite (swrap32_high (w + 18446744073709451615)) by lia.
  brT.
  awalk [e_calloc].
  rewrite (swrap32_high (h + 18446744073709451615)) by lia.
  brT.
  awalk [e_calloc].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { eapply CK with (lo := lo) (nmemb := h) (size := 8); rt_side idtac.
    all: lazymatch goal with
         | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact TRC2| left; ul]
         | |- _ <= CALLOCK_MAX => unfold CALLOCK_MAX; lia
         | |- 64512 < _ -> _ => intros; nia
         | |- mcost _ <= _ => replace (h * 8) with (8 * h) by lia; lia
         | |- Z.of_nat (length (rt_live RT _)) < LIVE_MAX => lia
         | |- ?g => idtac "LEFT:" g
         end. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac] | solve [frames_sub_tac] | lia]).
  lazymatch goal with H : rt_live RT ?S = (?p, h * 8) :: rt_live RT Σ |- _ => rename p into data; rename S into S2; rename H into LV2 end.
  lazymatch goal with H : rt_frames RT S2 = _ |- _ => rename H into FRS2 end.
  lazymatch goal with H : rt_sp0 RT S2 = _ |- _ => rename H into SP2 end.
  lazymatch goal with H : rt_credit RT S2 = _ |- _ => rename H into CR2 end.
  lazymatch goal with H : wr_at asegs _ data _ |- _ => rename H into DW end.
  lazymatch goal with H : 0 < data |- _ => rename H into D0 end.
  lazymatch goal with H : data mod 16 = 0 |- _ => rename H into D16 end.
  replace (h * 8) with (8 * h) in * by lia.
  chunk_facts RT AF GP data (8 * h).
  refresh RT AF. park_disj.
  walk_to AF MST [(usp + -80, usp)] [e_calloc; 0x91c30].
  assert (C2SEC : forall rows0 L, sec_bytes (rev (map (fun r => (r, 4 * w)) rows0) ++ (data, 8 * h) :: L)
                                  <= Z.of_nat (length rows0) * (4 * w) + 8 * h + sec_bytes L).
  { intros rows0 L. rewrite sec_bytes_app, sec_bytes_rev.
    pose proof (sec_bytes_rows_le rows0 (4 * w) ltac:(lia)). pose proof (sec_bytes_cons_le data (8 * h) L ltac:(lia)). lia. }
  assert (C2LEN : forall rows0 L, Z.of_nat (length (rev (map (fun r => (r, 4 * w)) rows0) ++ (data, 8 * h) :: L))
                                  = Z.of_nat (length rows0) + 1 + Z.of_nat (length L)).
  { intros rows0 L. rewrite length_app, length_rev, length_map. cbn [length]. lia. }
  assert (C2IN : forall rows0 L, In (data, 8 * h) (rev (map (fun r => (r, 4 * w)) rows0) ++ (data, 8 * h) :: L))
    by (intros rows0 L; apply in_or_app; right; left; reflexivity).
  assert (EXITD : forall (Sx : rts RT) (mx : mem) (rows : list Z)
                         (rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x x0v x1v x3v x4v x5v x6v x7v t3x t4x t5x t6x : word)
                         (Fx : bvmap 5 word) (fcx : bv 32) (jk : list byte),
    Z.of_nat (length rows) = h -> Forall (fun r => 0 < r /\ r mod 16 = 0) rows ->
    ART RT Sx mx -> mem_inv asegs mx -> wmono asegs m mx -> stk asegs mx lo (usp + -80) ->
    rw_cells asegs mx (usp + -80) [CB 8 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    u64arr asegs mx data (map (Z_to_bv 64) rows) ->
    LIBH mx -> io_ssp mx -> agree_on PF m mx ->
    rt_live RT Sx = rev (map (fun r => (r, 4 * w)) rows) ++ (data, 8 * h) :: rt_live RT Σ -> rt_frames RT Sx = rt_frames RT Σ ->
    rt_sp0 RT Sx = rt_sp0 RT Σ -> rt_credit RT Sx = rt_credit RT Σ - mcost (8 * h) - h * mcost (4 * w) ->
    cps asegs (ASTA RT Sx PMc (eq (entry_st rax (Z_to_bv 64 (usp + -80)) gp (Z_to_bv 64 TP_A) t0x t1x t2x x0v x1v
               a0x a1x a2x a3x a4x a5x a6x a7x (Z_to_bv 64 data) x3v x4v x5v x6v x7v s8 s9 s10 s11
               t3x t4x t5x t6x Fx fcx 0x91c74 mx))) QF).
  { intros Sx mx rows rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x x0v x1v x3v x4v x5v x6v x7v t3x t4x t5x t6x Fx fcx jk
      LENX RAL ARTx MIx WMx STx FRx DAx LHx SSPx AGFx LVx FRSx SPx CRx.
    unfold entry_st.
    refresh RT AF. park_disj.
    walk_to AF MST [(usp + -80, usp)] (@nil Z).
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
    apply cps_finish. intros c0 Hc. subst QF. cbv beta.
    lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S', data, rows end.
    split.
    { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; assumption]]| split; assumption]|].
      split; [intros xa HXa HXo; apply AGFx; exact HXa|].
      assumption. }
    split; [exact LVx|]. split; [exact LENX|]. split; [exact RAL|]. split; [exact D0|]. split; [exact D16|].
    split; [exact FRSx|]. split; [exact SPx|]. rewrite CRx. unfold km_cost. lia.
  }
  assert (LOOPD : forall k i, Z.to_nat (h - i) = k -> 0 <= i < h ->
    forall (Si : rts RT) (mi : mem) (rows : list Z)
           (rai t0i t1i t2i a0i a1i a2i a3i a4i a5i a6i a7i t3i t4i t5i t6i : word) (Fi : bvmap 5 word) (fci : bv 32) (jk : list byte),
    Z.of_nat (length rows) = i -> Forall (fun r => 0 < r /\ r mod 16 = 0) rows ->
    ART RT Si mi -> mem_inv asegs mi -> wmono asegs m mi -> stk asegs mi lo (usp + -80) ->
    rw_cells asegs mi (usp + -80) [CB 8 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    u64arr asegs mi data (map (Z_to_bv 64) rows) ->
    LIBH mi -> io_ssp mi -> agree_on PF m mi ->
    rt_live RT Si = rev (map (fun r => (r, 4 * w)) rows) ++ (data, 8 * h) :: rt_live RT Σ -> rt_frames RT Si = rt_frames RT Σ ->
    rt_sp0 RT Si = rt_sp0 RT Σ -> rt_credit RT Si = rt_credit RT Σ - mcost (8 * h) - i * mcost (4 * w) ->
    cps asegs (ASTA RT Si PMc (eq (entry_st rai (Z_to_bv 64 (usp + -80)) gp (Z_to_bv 64 TP_A) t0i t1i t2i
               (Z_to_bv 64 w) (Z_to_bv 64 (h - i)) a0i a1i a2i a3i a4i a5i a6i a7i
               (Z_to_bv 64 data) (Z_to_bv 64 (data + 8 * i)) (Z_to_bv 64 SHB) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (data + 8 * i))
               s8 s9 s10 s11 t3i t4i t5i t6i Fi fci 0x91c30 mi))) QF).
  { intros k. induction k as [k IH] using lt_wf_ind.
    intros i Hk Hi Si mi rows rai t0i t1i t2i a0i a1i a2i a3i a4i a5i a6i a7i t3i t4i t5i t6i Fi fci jk
      LENI RAL ARTi MIi WMi STi FRi DAi LHi SSPi AGFi LVi FRSi SPi CRi.
    unfold entry_st.
    assert (DINi : In (data, 8 * h) (rt_live RT Si)) by (rewrite LVi; apply C2IN).
    pose proof (acc_live RT AF Si mi data (8 * h) ARTi DINi) as ACCD.
    assert (LENW : Z.of_nat (length (map (Z_to_bv 64) rows)) = i) by (rewrite length_map; exact LENI).
    refresh RT AF. park_disj.
    walk_to AF MST [(usp + -80, usp)] [e_calloc].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { eapply CK with (lo := lo) (nmemb := w) (size := 4); rt_side idtac.
      all: lazymatch goal with
           | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact TRC3| left; ul]
           | |- _ <= CALLOCK_MAX => unfold CALLOCK_MAX; lia
           | |- 64512 < _ -> _ => intros; rewrite LVi; pose proof (C2SEC rows (rt_live RT Σ)); nia
           | |- mcost _ <= _ => rewrite CRi; replace (w * 4) with (4 * w) by lia; unfold km_cost in KCB; nia
           | |- Z.of_nat (length (rt_live RT _)) < LIVE_MAX => rewrite LVi, C2LEN; lia
           | |- ?g => idtac "LEFT:" g
           end. }
    assert (DINr : In (data, 8 * h) (rev (map (fun r => (r, 4 * w)) rows) ++ (data, 8 * h) :: rt_live RT Σ)) by apply C2IN.
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx);
                   [ solve [let e := fresh "e" in let He := fresh "He" in intros e He;
                            repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end;
                            apply in_or_app; right; right; exact He]
                   | solve [frames_sub_tac] | lia]).
    lazymatch goal with H : rt_live RT ?S = (?p, w * 4) :: rt_live RT Si |- _ => rename p into r; rename S into Sr; rename H into LVr end.
    lazymatch goal with H : rt_frames RT Sr = _ |- _ => rename H into FRSr end.
    lazymatch goal with H : rt_sp0 RT Sr = _ |- _ => rename H into SPr end.
    lazymatch goal with H : rt_credit RT Sr = _ |- _ => rename H into CRr end.
    lazymatch goal with H : 0 < r |- _ => rename H into R0 end.
    lazymatch goal with H : r mod 16 = 0 |- _ => rename H into R16 end.
    replace (w * 4) with (4 * w) in * by lia.
    assert (DINs : In (data, 8 * h) (rt_live RT Sr)) by (rewrite LVr, LVi; right; apply C2IN).
    lazymatch goal with A : ART RT Sr ?mm |- _ => pose proof (acc_live RT AF Sr mm data (8 * h) A DINs) as ACCD2;
                                                  pose proof (proj1 (af_acc_live RT AF Sr mm data (8 * h) A DINs)) as DWs end.
    refresh RT AF. park_disj.
    walk_to AF MST [(usp + -80, usp); (data + 8 * i, data + 8 * i + 8)] [e_calloc; 0x91c30; 0x91c74].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (wr_at_store_ok asegs mm data (8 * h) (8 * i) 8 DWs ltac:(lia) ltac:(lia)) as SOK end.
    unfold wa in SOK.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 (data + 8 * i)) (le8 (Z_to_bv 64 r))) _) =>
      lazymatch goal with DAx : u64arr asegs mm data (map (Z_to_bv 64) rows) |- _ =>
        assert (DA2 : u64arr asegs (write_to_mem mm (wa (data + 8 * i)) (le8 (Z_to_bv 64 r))) data (map (Z_to_bv 64) (rows ++ [r])));
        [ rewrite map_app; cbn [map];
          pose proof (u64arr_snoc_write mm data (map (Z_to_bv 64) rows) (Z_to_bv 64 r) DAx) as X;
          rewrite LENW in X; apply X;
          apply (wr_at_sub mm data (8 * h) (data + 8 * i) 8 DWs); lia
        | clear DAx ] end end.
    unfold parked in CKS, CKH.
    assert (DSEG : data + 8 * i + 8 <= 65536 \/ 6463488 <= data) by lia.
    assert (DSH : data + 8 * i + 8 <= 2147446784 \/ 17594333495296 <= data) by lia.
    store_done.
    awalk [e_calloc; 0x91c30; 0x91c74].
    destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
    + brT.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists data, (8 * h); split; [exact DINs| lia]| exact I]]).
      lazymatch goal with MUx : munch _ ?mm ?mc |- _ =>
        agf_munch AGFi MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx);
                                  lazymatch goal with A : ART RT S2 ?mm2 |- _ =>
                                    pose proof (fresh_chunk_apart RT AF S2 mm2 [] data (8 * h) (rt_live RT Σ) (rt_frames RT Σ) usp _ A LV2
                                                  ltac:(rewrite FRS2; reflexivity) ltac:(rewrite SP2; unfold STACK_WIN; lia) Hx) end;
                                  split; [lia| split; [lia| exact I]]) end.
      to_entry.
      replace (h - i + -1) with (h - (i + 1)) by lia.
      replace (data + 8 * i + 8) with (data + 8 * (i + 1)) by lia.
      eapply (IH (Z.to_nat (h - (i + 1))) ltac:(lia) (i + 1) eq_refl ltac:(lia) Sr _ (rows ++ [r])).
      all: lazymatch goal with
           | |- Z.of_nat (length (_ ++ _)) = _ => rewrite length_app; cbn [length]; lia
           | |- Forall _ (_ ++ _) => apply Forall_app; split; [exact RAL| apply Forall_cons; [split; lia| apply Forall_nil]]
           | |- rt_live RT _ = _ => rewrite map_app, rev_app_distr; cbn [map rev app];
                                    repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_frames RT _ = _ => repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_sp0 RT _ = _ => repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_credit RT _ = _ => repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H end; lia
           | |- rw_cells _ _ _ (CB _ _ :: _) => eassumption
           | |- _ => assumption
           end.
    + brF.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists data, (8 * h); split; [exact DINs| lia]| exact I]]).
      lazymatch goal with MUx : munch _ ?mm ?mc |- _ =>
        agf_munch AGFi MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx);
                                  lazymatch goal with A : ART RT S2 ?mm2 |- _ =>
                                    pose proof (fresh_chunk_apart RT AF S2 mm2 [] data (8 * h) (rt_live RT Σ) (rt_frames RT Σ) usp _ A LV2
                                                  ltac:(rewrite FRS2; reflexivity) ltac:(rewrite SP2; unfold STACK_WIN; lia) Hx) end;
                                  split; [lia| split; [lia| exact I]]) end.
      to_entry.
      assert (HI1 : i + 1 = h) by lia.
      eapply (EXITD Sr _ (rows ++ [r])).
      all: lazymatch goal with
           | |- Z.of_nat (length (_ ++ _)) = _ => rewrite length_app; cbn [length]; lia
           | |- Forall _ (_ ++ _) => apply Forall_app; split; [exact RAL| apply Forall_cons; [split; lia| apply Forall_nil]]
           | |- rt_live RT _ = _ => rewrite map_app, rev_app_distr; cbn [map rev app];
                                    repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_frames RT _ = _ => repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_sp0 RT _ = _ => repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_credit RT _ = _ => repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H end; rewrite <- HI1; lia
           | |- rw_cells _ _ _ (CB _ _ :: _) => eassumption
           | |- _ => assumption
           end.
  }
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  lazymatch goal with MUx : munch _ ?mm ?mc |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
  to_entry.
  assert (DL7 : Z.land data 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
  replace (Z.b2z (0 <? data)) with 1 by (rewrite (proj2 (Z.ltb_lt 0 data) D0); reflexivity).
  rewrite DL7. change (Z.b2z (0 <? 1)) with 1. change (Z.land 1 1) with 1.
  replace (Z_to_bv 64 h) with (Z_to_bv 64 (h - 0)) by (f_equal; lia).
  replace (Z_to_bv 64 data) with (Z_to_bv 64 (data + 8 * 0)) at 2 3 by (f_equal; lia).
  eapply (LOOPD (Z.to_nat (h - 0)) 0 eq_refl ltac:(lia) S2 _ []).
  all: lazymatch goal with
       | |- Z.of_nat (length []) = _ => reflexivity
       | |- Forall _ [] => apply Forall_nil
       | |- u64arr asegs _ _ (map _ []) => apply u64arr_nil; lia
       | |- rt_live RT _ = _ => cbn [map rev app]; repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; reflexivity
       | |- rt_frames RT _ = _ => repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; reflexivity
       | |- rt_sp0 RT _ = _ => repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity
       | |- rt_credit RT _ = _ => repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H end; lia
       | |- rw_cells _ _ _ (CB _ _ :: _) => eassumption
       | |- _ => assumption
       end.
Qed.
(* [comment removed for export] *)
Theorem kernelCreate_ok : kernelCreate_cps RT.
Proof using AF GP CK TRC1 TRC2 TRC3.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo h w
    FDO MST -> -> -> HB WB HWB ENV RES SECB.
  unfold lpost, lenv, lres, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_kernelCreate, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (KCB : km_cost h w <= rt_credit RT Σ) by exact CRB.
  refresh RT AF.
  park_disj.
  walk_to AF MST [(usp + -32, usp)] [e_calloc].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 1) (size := 24); rt_side idtac.
    all: lazymatch goal with
         | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite !unsigned_lit by (unfold SHB; ul); [exact TRC1| left; unfold SHB; ul]
         | |- _ <= CALLOC_MAX => unfold CALLOC_MAX; lia
         | |- ?g => idtac "LEFT:" g
         end. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac] | solve [frames_sub_tac] | lia]).
  change (1 * 24) with 24 in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 24) :: rt_live RT Σ |- _ => rename p into kel; rename S into S1; rename H into LV1 end.
  lazymatch goal with H : rt_frames RT S1 = _ |- _ => rename H into FRS1 end.
  lazymatch goal with H : rt_sp0 RT S1 = _ |- _ => rename H into SP1 end.
  lazymatch goal with H : rt_credit RT S1 = _ |- _ => rename H into CR1 end.
  lazymatch goal with H : rw_cells asegs _ kel _ |- _ => rename H into KC end.
  chunk_facts RT AF GP kel 24.
  lazymatch goal with H : 0 < kel |- _ => rename H into K0 end.
  lazymatch goal with H : kel mod 16 = 0 |- _ => rename H into K16 end.
  refresh RT AF. park_disj.
  split_last_CB KC [4; 4; 16]%nat.
  walk_to AF MST [(usp + -32, usp); (kel, kel + 24)] [e_create2d].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; aclient_tac| exact I]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx);
                                lazymatch goal with A : ART RT S1 ?mm |- _ =>
                                  pose proof (fresh_chunk_apart RT AF S1 mm [] kel 24 (rt_live RT Σ) (rt_frames RT Σ) usp _ A LV1 FRS1
                                                ltac:(rewrite SP1; unfold STACK_WIN; lia) Hx) end;
                                split; [lia| split; [lia| exact I]]).
  pose proof create2d_ok as C2D. unfold c2d_cps in C2D.
  eapply cps_seq.
  { eapply C2D with (lo := lo) (h := h) (w := w); rt_side idtac.
    all: lazymatch goal with
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ =>
             unfold lres, FRAMES_MAX, LIVE_MAX in *; rewrite FRS1, LV1; cbn [length];
             split; [lia| split; [lia| split; [rewrite CR1; unfold mcost; cbn; lia| intros p n [E|Hin]; [injection E as <- <-; lia| exact (LVP p n Hin)]]]]
         | |- sec_bytes _ + _ + _ <= _ => rewrite LV1, sec_bytes_cons_small by lia; lia
         | |- _ <= _ <= _ => lia
         | |- ?g => idtac "LEFT-C2D:" g
         end. }
  after_call RT AF.
  lazymatch goal with H : rt_live RT ?S = rev (map _ ?rs) ++ (?d, 8 * h) :: rt_live RT S1 |- _ =>
    rename S into S2; rename H into LV2; rename d into data; rename rs into rows end.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx);
                 [ solve [let e := fresh "e" in let He := fresh "He" in intros e He; rewrite LV1; right; exact He]
                 | solve [frames_sub_tac] | lia] | exact I]).
  lazymatch goal with H : Z.of_nat (length rows) = h |- _ => rename H into LEN2 end.
  lazymatch goal with H : Forall _ rows |- _ => rename H into RAL end.
  lazymatch goal with H : 0 < data |- _ => rename H into D0 end.
  lazymatch goal with H : data mod 16 = 0 |- _ => rename H into D16 end.
  lazymatch goal with H : rt_frames RT S2 = _ |- _ => rename H into FRS2 end.
  lazymatch goal with H : rt_sp0 RT S2 = _ |- _ => rename H into SP2 end.
  lazymatch goal with H : rt_credit RT S1 - km_cost h w <= rt_credit RT S2 |- _ => rename H into CR2 end.
  lazymatch goal with H : u64arr asegs _ data _ |- _ => rename H into DA2 end.
  assert (LV2k : rt_live RT S2 = km_live kel data h w rows (rt_live RT Σ)) by (rewrite LV2, LV1; reflexivity).
  assert (KINr : In (kel, 24) (km_live kel data h w rows (rt_live RT Σ))) by apply km_live_in_kel.
  assert (DINr : In (data, 8 * h) (km_live kel data h w rows (rt_live RT Σ))) by apply km_live_in_data.
  assert (KIN2 : In (kel, 24) (rt_live RT S2)) by (rewrite LV2k; exact KINr).
  assert (DIN2 : In (data, 8 * h) (rt_live RT S2)) by (rewrite LV2k; exact DINr).
  assert (LVPK : forall p n, In (p, n) (rt_live RT S2) -> 0 < n).
  { intros p n Hin. rewrite LV2k in Hin. apply km_live_inv in Hin as [Hin|Hin]; [| exact (LVP p n Hin)].
    unfold km_chunks in Hin. destruct Hin as [E|[E|Hin]]; [injection E as <- <-; lia| injection E as <- <-; lia|].
    apply in_map_iff in Hin as (r & E & Hr). injection E as <- <-. lia. }
  lazymatch goal with A : ART RT S2 ?mm |- _ =>
    pose proof (live_nodup RT AF S2 mm A LVPK) as NDX;
    pose proof (live_apart2 RT AF S2 mm kel 24 data (8 * h) A KIN2 DIN2) as AKDf;
    pose proof (acc_live RT AF S2 mm kel 24 A KIN2) as ACCK end.
  rewrite LV2k in NDX. destruct (km_live_nodup_split _ _ _ _ _ _ NDX) as (NDK & NIN). clear NDX.
  assert (NEKD : kel <> data) by (apply List.NoDup_cons_iff in NDK as (NK & _); intros E; apply NK; left; symmetry; exact E).
  specialize (AKDf NEKD).
  assert (LENW : Z.of_nat (length (map (Z_to_bv 64) rows)) = h) by (rewrite length_map; exact LEN2).
  assert (AKD2 : data + 8 * Z.of_nat (length (map (Z_to_bv 64) rows)) <= kel \/ kel + 24 <= data) by (rewrite LENW; lia).
  assert (LVk : rt_live RT S2 = (rev (map (fun r => (r, 4 * w)) rows) ++ [(data, 8 * h)]) ++ (kel, 24) :: rt_live RT Σ)
    by (rewrite LV2k; unfold km_live; rewrite <- app_assoc; reflexivity).
  split_last_CB KC [8; 8]%nat.
  refresh RT AF. park_disj.
  walk_to AF MST [(usp + -32, usp); (kel, kel + 24)] (@nil Z).
  lazymatch goal with A : ART RT S2 ?mm |- _ => pose proof (af_live_range RT AF S2 mm data (8 * h) A DIN2) as DLR end.
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in DLR.
  brF.
  awalk (@nil Z).
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists kel, 24; split; [exact KIN2| lia]| exact I]]).
  lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    lazymatch goal with A : ART RT S2 ?mx |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx);
                              pose proof (fresh_chunk_apart RT AF S2 mx _ kel 24 (rt_live RT Σ) (rt_frames RT Σ) usp _ A LVk
                                            ltac:(rewrite FRS2, FRS1; reflexivity) ltac:(rewrite SP2, SP1; unfold STACK_WIN; lia) Hx);
                              split; [lia| split; [lia| exact I]]) end end.
  apply cps_finish. intros c0 Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S', kel, data, rows end.
  split.
  { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; assumption]]| split; assumption]|].
    split; [intros xa HXa HXo; apply AGF; exact HXa|].
    unfold kel_obj.
    lazymatch goal with KCx : rw_cells asegs _ kel _ |- _ => split; [exact (kel_cells_of_zero _ kel h w data _ eq_refl KCx)|] end.
    split; [split; [exact KIN2| repeat split; lia]|].
    split; [assumption|].
    split; [split; [exact DIN2| repeat split; lia]|].
    split; [exact LEN2|].
    split; [| split; [exact NDK| lia]].
    apply Forall_forall. intros r Hr. rewrite Forall_forall in RAL. destruct (RAL r Hr) as (R0 & R16).
    assert (RIN : In (r, 4 * w) (rt_live RT S2)) by (rewrite LV2k; apply km_live_in_row; exact Hr).
    split; [split; [exact RIN| repeat split; lia]|].
    lazymatch goal with A : ART RT S2 ?mf |- wr_at asegs ?mf _ _ => exact (proj1 (af_acc_live RT AF S2 mf r (4 * w) A RIN)) end. }
  split; [exact LV2k|]. split; [rewrite FRS2; exact FRS1|]. split; [rewrite SP2; exact SP1|]. rewrite CR1 in CR2. lia.
Qed.
End KCREATE.
