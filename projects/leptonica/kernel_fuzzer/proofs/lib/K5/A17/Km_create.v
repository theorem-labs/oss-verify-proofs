(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Km_setelem Km_iface Km_kit D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac rt_transport_extra m m' AG ::=
  lept_rt_transport_extra m m' AG;   (* [comment removed for export] *)
  repeat match goal with
  | H : u64arr asegs m ?A ?ws |- _ =>
      first [ apply (u64arr_agree_nw asegs m m' A ws) in H; [ | solve [agree_range AG A ltac:(fun A => acl_dispatch A)] ]
            | idtac "note: dropping u64arr:" H; clear H ]
  end.

Section KCREATE.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
(* [comment removed for export] *)
Hypothesis CK : calloc_contractK RT.
(* [comment removed for export] *)
Hypothesis TRC1 : In [0x90f74] CLIENT_TRACES.
Hypothesis TRC2 : In [0x9110c] CLIENT_TRACES.
Hypothesis TRC3 : In [0x91124] CLIENT_TRACES.

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
  assert (MC8 : 0 <= mcost (8 * h) <= km_cost h w) by (unfold km_cost, mcost; destruct (Z.leb_spec (8 * h) 64512), (Z.leb_spec (4 * w) 64512); nia).
  assert (MC4 : 0 <= mcost (4 * w)) by (unfold mcost; destruct (Z.leb_spec (4 * w) 64512); lia).
  refresh RT AF.
  park_disj.
  walk_to AF MST [(usp + -64, usp)] [e_calloc].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 1) (size := 24); rt_side idtac.
    all: lazymatch goal with
         | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact TRC1| left; ul]
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
  refresh RT AF. park_disj.
  split_last_CB KC [4; 4; 16]%nat.
  walk_to AF MST [(usp + -64, usp); (kel, kel + 24)] [e_calloc].
  rewrite (swrap32_high (w + 18446744073709451615)) by lia.
  brT.
  awalk [e_calloc].
  rewrite (swrap32_high (h + 18446744073709451615)) by lia.
  brT.
  awalk [e_calloc].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; aclient_tac| exact I]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx);
                                lazymatch goal with A : ART RT S1 ?mm |- _ =>
                                  pose proof (fresh_chunk_apart RT AF S1 mm [] kel 24 (rt_live RT Σ) (rt_frames RT Σ) usp _ A LV1 FRS1
                                                ltac:(rewrite SP1; unfold STACK_WIN; lia) Hx) end;
                                split; [lia| split; [lia| exact I]]).
  eapply cps_seq.
  { eapply CK with (lo := lo) (nmemb := h) (size := 8); rt_side idtac.
    all: lazymatch goal with
         | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact TRC2| left; ul]
         | |- _ <= CALLOCK_MAX => unfold CALLOCK_MAX; lia
         | |- 64512 < _ -> _ => intros; rewrite LV1, sec_bytes_cons_small by lia; nia
         | |- mcost _ <= _ => rewrite CR1; replace (h * 8) with (8 * h) by lia; lia
         | |- Z.of_nat (length (rt_live RT _)) < LIVE_MAX => rewrite LV1; cbn [length]; lia
         | |- ?g => idtac "LEFT:" g
         end. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_add_tac] | solve [frames_sub_tac] | lia]).
  lazymatch goal with H : rt_live RT ?S = (?p, h * 8) :: rt_live RT S1 |- _ => rename p into data; rename S into S2; rename H into LV2 end.
  lazymatch goal with H : rt_frames RT S2 = _ |- _ => rename H into FRS2 end.
  lazymatch goal with H : rt_sp0 RT S2 = _ |- _ => rename H into SP2 end.
  lazymatch goal with H : rt_credit RT S2 = _ |- _ => rename H into CR2 end.
  lazymatch goal with H : wr_at asegs _ data _ |- _ => rename H into DW end.
  lazymatch goal with H : 0 < kel |- _ => rename H into K0 end.
  lazymatch goal with H : kel mod 16 = 0 |- _ => rename H into K16 end.
  lazymatch goal with H : 0 < data |- _ => rename H into D0 end.
  lazymatch goal with H : data mod 16 = 0 |- _ => rename H into D16 end.
  replace (h * 8) with (8 * h) in * by lia.
  chunk_facts RT AF GP data (8 * h).
  assert (LVPK : forall kel0 data0 rows0, Forall (fun r => 0 < r /\ r mod 16 = 0) rows0 ->
            forall p n, In (p, n) (km_live kel0 data0 h w rows0 (rt_live RT Σ)) -> 0 < n).
  { intros kel0 data0 rows0 _ p n Hin. apply km_live_inv in Hin as [Hin|Hin]; [| exact (LVP p n Hin)].
    unfold km_chunks in Hin. destruct Hin as [E|[E|Hin]]; [injection E as <- <-; lia| injection E as <- <-; lia|].
    apply in_map_iff in Hin as (r & E & _). injection E as <- <-. lia. }
  refresh RT AF. park_disj.
  assert (EXITC : forall (Sx : rts RT) (mx : mem) (rows : list Z)
                         (rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x x1v x3v x6v t3x t4x t5x t6x : word)
                         (Fx : bvmap 5 word) (fcx : bv 32),
    Z.of_nat (length rows) = h -> Forall (fun r => 0 < r /\ r mod 16 = 0) rows ->
    ART RT Sx mx -> mem_inv asegs mx -> wmono asegs m mx -> stk asegs mx lo (usp + -64) ->
    rw_cells asegs mx (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mx kel [C4 (Z_to_bv 64 h); C4 (Z_to_bv 64 w); CB 16 (repeat (Z_to_bv 8 0) 16)] ->
    u64arr asegs mx data (map (Z_to_bv 64) rows) ->
    LIBH mx -> io_ssp mx -> agree_on PF m mx ->
    rt_live RT Sx = km_live kel data h w rows (rt_live RT Σ) -> rt_frames RT Sx = rt_frames RT Σ -> rt_sp0 RT Sx = rt_sp0 RT Σ ->
    rt_credit RT Sx = rt_credit RT Σ - mcost (8 * h) - h * mcost (4 * w) ->
    cps asegs (ASTA RT Sx PMc (eq (entry_st rax (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 TP_A) t0x t1x t2x (Z_to_bv 64 w) x1v
               a0x a1x a2x a3x a4x a5x a6x a7x (Z_to_bv 64 data) x3v (Z_to_bv 64 SHB) (Z_to_bv 64 kel) x6v s7 s8 s9 s10 s11
               t3x t4x t5x t6x Fx fcx 0x91148 mx))) QF).
  { intros Sx mx rows rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x x1v x3v x6v t3x t4x t5x t6x Fx fcx
      LENX RAL ARTx MIx WMx STx FRx KCx DAx LHx SSPx AGFx LVx FRSx SPx CRx.
    unfold entry_st.
    assert (KINr : In (kel, 24) (km_live kel data h w rows (rt_live RT Σ))) by apply km_live_in_kel.
    assert (DINr : In (data, 8 * h) (km_live kel data h w rows (rt_live RT Σ))) by apply km_live_in_data.
    assert (KINx : In (kel, 24) (rt_live RT Sx)) by (rewrite LVx; exact KINr).
    assert (DINx : In (data, 8 * h) (rt_live RT Sx)) by (rewrite LVx; exact DINr).
    pose proof (live_nodup RT AF Sx mx ARTx ltac:(rewrite LVx; exact (LVPK kel data rows RAL))) as NDX.
    rewrite LVx in NDX. destruct (km_live_nodup_split _ _ _ _ _ _ NDX) as (NDK & NIN). clear NDX.
    assert (NEKD : kel <> data) by (apply List.NoDup_cons_iff in NDK as (NK & _); intros E; apply NK; left; symmetry; exact E).
    pose proof (live_apart2 RT AF Sx mx kel 24 data (8 * h) ARTx KINx DINx NEKD) as AKD.
    pose proof (acc_live RT AF Sx mx kel 24 ARTx KINx) as ACCK.
    assert (LENW : Z.of_nat (length (map (Z_to_bv 64) rows)) = h) by (rewrite length_map; exact LENX).
    assert (AKD2 : data + 8 * Z.of_nat (length (map (Z_to_bv 64) rows)) <= kel \/ kel + 24 <= data) by (rewrite LENW; lia).
    assert (LVk : rt_live RT Sx = (rev (map (fun r => (r, 4 * w)) rows) ++ [(data, 8 * h)]) ++ (kel, 24) :: rt_live RT Σ)
      by (rewrite LVx; unfold km_live; rewrite <- app_assoc; reflexivity).
    split_last_CB KCx [8; 8]%nat.
    refresh RT AF. park_disj.
    walk_to AF MST [(usp + -64, usp); (kel, kel + 24)] (@nil Z).
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists kel, 24; split; [exact KINx| lia]| exact I]]).
    lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx);
                                pose proof (fresh_chunk_apart RT AF Sx mx _ kel 24 (rt_live RT Σ) (rt_frames RT Σ) usp _ ARTx LVk FRSx
                                              ltac:(rewrite SPx; unfold STACK_WIN; lia) Hx);
                                split; [lia| split; [lia| exact I]]) end.
    apply cps_finish. intros c0 Hc. subst QF. cbv beta.
    lazymatch type of Hc with ASTA RT ?S' _ _ _ => exists S', kel, data, rows end.
    split.
    { eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
      split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
      split; [split; [split; [assumption| split; [assumption| split; assumption]]| split; assumption]|].
      split; [intros xa HXa HXo; apply AGFx; exact HXa|].
      unfold kel_obj.
      split; [exact (kel_cells_of_zero _ kel h w data _ eq_refl KCx)|].
      split; [split; [exact KINx| repeat split; lia]|].
      split; [exact DAx|].
      split; [split; [exact DINx| repeat split; lia]|].
      split; [exact LENX|].
      split; [| split; [exact NDK| lia]].
      apply Forall_forall. intros r Hr. rewrite Forall_forall in RAL. destruct (RAL r Hr) as (R0 & R16).
      assert (RIN : In (r, 4 * w) (rt_live RT Sx)) by (rewrite LVx; apply km_live_in_row; exact Hr).
      split; [split; [exact RIN| repeat split; lia]|].
      lazymatch goal with A : ART RT Sx ?mf |- wr_at asegs ?mf _ _ => exact (proj1 (af_acc_live RT AF Sx mf r (4 * w) A RIN)) end. }
    split; [exact LVx|]. split; [exact FRSx|]. split; [exact SPx|]. rewrite CRx. unfold km_cost. lia.
  }
  assert (LOOPC : forall k i, Z.to_nat (h - i) = k -> 0 <= i < h ->
    forall (Si : rts RT) (mi : mem) (rows : list Z)
           (rai t0i t1i t2i a0i a1i a2i a3i a4i a5i a6i a7i t3i t4i t5i t6i : word) (Fi : bvmap 5 word) (fci : bv 32),
    Z.of_nat (length rows) = i -> Forall (fun r => 0 < r /\ r mod 16 = 0) rows ->
    ART RT Si mi -> mem_inv asegs mi -> wmono asegs m mi -> stk asegs mi lo (usp + -64) ->
    rw_cells asegs mi (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mi kel [C4 (Z_to_bv 64 h); C4 (Z_to_bv 64 w); CB 16 (repeat (Z_to_bv 8 0) 16)] ->
    u64arr asegs mi data (map (Z_to_bv 64) rows) ->
    LIBH mi -> io_ssp mi -> agree_on PF m mi ->
    rt_live RT Si = km_live kel data h w rows (rt_live RT Σ) -> rt_frames RT Si = rt_frames RT Σ -> rt_sp0 RT Si = rt_sp0 RT Σ ->
    rt_credit RT Si = rt_credit RT Σ - mcost (8 * h) - i * mcost (4 * w) ->
    cps asegs (ASTA RT Si PMc (eq (entry_st rai (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 TP_A) t0i t1i t2i (Z_to_bv 64 w) (Z_to_bv 64 (h - i))
               a0i a1i a2i a3i a4i a5i a6i a7i (Z_to_bv 64 data) (Z_to_bv 64 (data + 8 * i)) (Z_to_bv 64 SHB) (Z_to_bv 64 kel)
               (Z_to_bv 64 (data + 8 * i)) s7 s8 s9 s10 s11 t3i t4i t5i t6i Fi fci 0x91118 mi))) QF).
  { intros k. induction k as [k IH] using lt_wf_ind.
    intros i Hk Hi Si mi rows rai t0i t1i t2i a0i a1i a2i a3i a4i a5i a6i a7i t3i t4i t5i t6i Fi fci
      LENI RAL ARTi MIi WMi STi FRi KCi DAi LHi SSPi AGFi LVi FRSi SPi CRi.
    unfold entry_st.
    assert (KINr : In (kel, 24) (km_live kel data h w rows (rt_live RT Σ))) by apply km_live_in_kel.
    assert (DINr : In (data, 8 * h) (km_live kel data h w rows (rt_live RT Σ))) by apply km_live_in_data.
    assert (KINi : In (kel, 24) (rt_live RT Si)) by (rewrite LVi; exact KINr).
    assert (DINi : In (data, 8 * h) (rt_live RT Si)) by (rewrite LVi; exact DINr).
    pose proof (acc_live RT AF Si mi kel 24 ARTi KINi) as ACCK. pose proof (acc_live RT AF Si mi data (8 * h) ARTi DINi) as ACCD.
    assert (LENW : Z.of_nat (length (map (Z_to_bv 64) rows)) = i) by (rewrite length_map; exact LENI).
    refresh RT AF. park_disj.
    walk_to AF MST [(usp + -64, usp)] [e_calloc].
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { eapply CK with (lo := lo) (nmemb := w) (size := 4); rt_side idtac.
      all: lazymatch goal with
           | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact TRC3| left; ul]
           | |- _ <= CALLOCK_MAX => unfold CALLOCK_MAX; lia
           | |- 64512 < _ -> _ => intros; rewrite LVi; pose proof (km_live_sec kel data h w rows (rt_live RT Σ) ltac:(lia) ltac:(lia)); nia
           | |- mcost _ <= _ => rewrite CRi; replace (w * 4) with (4 * w) by lia; unfold km_cost in KCB; nia
           | |- Z.of_nat (length (rt_live RT _)) < LIVE_MAX => rewrite LVi, km_live_length; lia
           | |- ?g => idtac "LEFT:" g
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx);
                   [ solve [let e := fresh "e" in let He := fresh "He" in intros e He;
                            repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end;
                            apply km_live_in_old; exact He]
                   | solve [frames_sub_tac] | lia]).
    lazymatch goal with H : rt_live RT ?S = (?p, w * 4) :: rt_live RT Si |- _ => rename p into r; rename S into Sr; rename H into LVr end.
    lazymatch goal with H : rt_frames RT Sr = _ |- _ => rename H into FRSr end.
    lazymatch goal with H : rt_sp0 RT Sr = _ |- _ => rename H into SPr end.
    lazymatch goal with H : rt_credit RT Sr = _ |- _ => rename H into CRr end.
    lazymatch goal with H : 0 < r |- _ => rename H into R0 end.
    lazymatch goal with H : r mod 16 = 0 |- _ => rename H into R16 end.
    replace (w * 4) with (4 * w) in * by lia.
    assert (DINr2 : In (data, 8 * h) ((r, 4 * w) :: km_live kel data h w rows (rt_live RT Σ))) by (right; exact DINr).
    assert (DINs : In (data, 8 * h) (rt_live RT Sr)) by (rewrite LVr, LVi; exact DINr2).
    lazymatch goal with A : ART RT Sr ?mm |- _ => pose proof (acc_live RT AF Sr mm data (8 * h) A DINs) as ACCD2;
                                                  pose proof (proj1 (af_acc_live RT AF Sr mm data (8 * h) A DINs)) as DWs end.
    refresh RT AF. park_disj.
    walk_to AF MST [(usp + -64, usp); (data + 8 * i, data + 8 * i + 8)] [e_calloc; 0x91118; 0x91148].
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
    assert (AKD : data + 8 * h <= kel \/ kel + 24 <= data).
    { lazymatch goal with A : ART RT S2 ?mm |- _ =>
        apply (af_live_disj RT AF S2 mm data (8 * h) kel 24 [] ((kel, 24) :: rt_live RT Σ) A);
        [rewrite LV2, LV1; reflexivity| left; reflexivity] end. }
    unfold parked in CKS0, CKH0.
    assert (DSEG : data + 8 * i + 8 <= 65536 \/ 6459392 <= data) by lia.
    assert (DSH : data + 8 * i + 8 <= 2147446784 \/ 17594333495296 <= data) by lia.
    assert (DKA : kel + 24 <= data + 8 * i \/ data + 8 * i + 8 <= kel) by lia.
    store_done.
    awalk [e_calloc; 0x91118; 0x91148].
    destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
    + brT.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists data, (8 * h); split; [exact DINs| lia]| exact I]]).
      lazymatch goal with MUx : munch _ ?mm ?mc |- _ =>
        agf_munch AGFi MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx);
                                  lazymatch goal with A : ART RT S2 ?mm2 |- _ =>
                                    pose proof (fresh_chunk_apart RT AF S2 mm2 [] data (8 * h) (rt_live RT S1) (rt_frames RT Σ) usp _ A LV2
                                                  ltac:(rewrite FRS2, FRS1; reflexivity) ltac:(rewrite SP2, SP1; unfold STACK_WIN; lia)
                                                  (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp (rt_live RT S1) (rt_frames RT Σ) usp _ Hx
                                                     ltac:(intros e He; rewrite LV1; right; exact He) ltac:(intros e He; exact He) ltac:(lia))) end;
                                  split; [lia| split; [lia| exact I]]) end.
      to_entry.
      replace (h - i + -1) with (h - (i + 1)) by lia.
      replace (data + 8 * i + 8) with (data + 8 * (i + 1)) by lia.
      eapply (IH (Z.to_nat (h - (i + 1))) ltac:(lia) (i + 1) eq_refl ltac:(lia) Sr _ (rows ++ [r])).
      all: lazymatch goal with
           | |- Z.of_nat (length (_ ++ _)) = _ => rewrite length_app; cbn [length]; lia
           | |- Forall _ (_ ++ _) => apply Forall_app; split; [exact RAL| apply Forall_cons; [split; lia| apply Forall_nil]]
           | |- rt_live RT _ = _ => rewrite km_live_snoc; repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_frames RT _ = _ => repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_sp0 RT _ = _ => repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_credit RT _ = _ => repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H end; lia
           | |- _ => assumption
           end.
    + brF.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists data, (8 * h); split; [exact DINs| lia]| exact I]]).
      lazymatch goal with MUx : munch _ ?mm ?mc |- _ =>
        agf_munch AGFi MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx);
                                  lazymatch goal with A : ART RT S2 ?mm2 |- _ =>
                                    pose proof (fresh_chunk_apart RT AF S2 mm2 [] data (8 * h) (rt_live RT S1) (rt_frames RT Σ) usp _ A LV2
                                                  ltac:(rewrite FRS2, FRS1; reflexivity) ltac:(rewrite SP2, SP1; unfold STACK_WIN; lia)
                                                  (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp (rt_live RT S1) (rt_frames RT Σ) usp _ Hx
                                                     ltac:(intros e He; rewrite LV1; right; exact He) ltac:(intros e He; exact He) ltac:(lia))) end;
                                  split; [lia| split; [lia| exact I]]) end.
      to_entry.
      assert (HI1 : i + 1 = h) by lia.
      eapply (EXITC Sr _ (rows ++ [r])).
      all: lazymatch goal with
           | |- Z.of_nat (length (_ ++ _)) = _ => rewrite length_app; cbn [length]; lia
           | |- Forall _ (_ ++ _) => apply Forall_app; split; [exact RAL| apply Forall_cons; [split; lia| apply Forall_nil]]
           | |- rt_live RT _ = _ => rewrite km_live_snoc; repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_frames RT _ = _ => repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_sp0 RT _ = _ => repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity
           | |- rt_credit RT _ = _ => repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H end; rewrite <- HI1; lia
           | |- _ => assumption
           end.
  }
  walk_to AF MST [(usp + -64, usp)] [e_calloc; 0x91118].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  lazymatch goal with MUx : munch _ ?mm ?mc |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]) end.
  to_entry.
  replace (Z_to_bv 64 h) with (Z_to_bv 64 (h - 0)) by (f_equal; lia).

  replace (Z_to_bv 64 data) with (Z_to_bv 64 (data + 8 * 0)) at 3 4 by (f_equal; lia).

  eapply (LOOPC (Z.to_nat (h - 0)) 0 eq_refl ltac:(lia) S2 _ []).
  all: lazymatch goal with
       | |- Z.of_nat (length []) = _ => reflexivity
       | |- Forall _ [] => apply Forall_nil
       | |- u64arr asegs _ _ (map _ []) => apply u64arr_nil; lia
       | |- rw_cells asegs _ _ [C4 _; C4 _; CB 16 _] => exact KC
       | |- rt_live RT _ = _ => repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; reflexivity
       | |- rt_frames RT _ = _ => repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; reflexivity
       | |- rt_sp0 RT _ = _ => repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity
       | |- rt_credit RT _ = _ => repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H end; lia
       | |- _ => assumption
       end.
Qed.
End KCREATE.
