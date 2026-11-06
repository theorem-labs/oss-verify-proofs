(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf Lept_chain LeptC_leaf Lept_objkit LeptL_kit Lept_gmax_defs Lept_deserkit Lept_fuzzkit
  Gm_iface Gq_iface Gq_cmap_iface Gm_kit Gm_leaf Gm_livekit Gm_livekit2 Gq_toarr_loop.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac ta_at_call RT AF PFS PFO ACR ACG ACB ACA :=
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul|
                        split; [intros zz Hzz; refine (aclient_mono _ _ _ _ _ _ zz (accok_aclient _ _ _ _ _ 8 zz ACR ltac:(lia)) _ _ _); [solve [live_sub_tac] | solve [frames_sub_tac] | lia]|
                        split; [intros zz Hzz; refine (aclient_mono _ _ _ _ _ _ zz (accok_aclient _ _ _ _ _ 8 zz ACG ltac:(lia)) _ _ _); [solve [live_sub_tac] | solve [frames_sub_tac] | lia]|
                        split; [intros zz Hzz; refine (aclient_mono _ _ _ _ _ _ zz (accok_aclient _ _ _ _ _ 8 zz ACB ltac:(lia)) _ _ _); [solve [live_sub_tac] | solve [frames_sub_tac] | lia]|
                        split; [intros zz Hzz; refine (aclient_mono _ _ _ _ _ _ zz (accok_aclient _ _ _ _ _ 8 zz ACA ltac:(lia)) _ _ _); [solve [live_sub_tac] | solve [frames_sub_tac] | lia]| exact I]]]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (PFO _ Hx); repeat split; try exact I; lia).
Ltac ta_calloc RT GP lo n TR :=
  eapply cps_seq;
  [ let CC := fresh "CC" in pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := n) (size := 4); rt_side idtac;
    lazymatch goal with
    | |- unwind_okC _ _ _ _ => apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact TR| left; ul]
    | |- _ => first [ unfold CALLOC_MAX; lia
                    | repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; cbn [length]; unfold LIVE_MAX in *; lia
                    | repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; unfold mcost; lia
                    | lazymatch goal with |- ?g => idtac "LEFT:" g end ]
    end
  | ].
(* [comment removed for export] *)
Ltac accok_now RT :=
  repeat match goal with
  | H : accok ?lv ?frs ?mm ?a ?n |- cps _ (ASTA RT ?S _ _) _ =>
      lazymatch lv with
      | rt_live RT S => fail
      | _ => apply (accok_mono lv frs (rt_live RT S) (rt_frames RT S) mm a n) in H; [| solve [live_add_tac] | solve [frames_sub_tac]]
      end
  end.

Ltac acl_of ACR :=
  lazymatch type of ACR with accok ?lv ?frs ?m ?b ?n =>
    lazymatch goal with |- aclient ?lv' ?frs' ?sp' ?x =>
      apply (aclient_mono lv frs sp' lv' frs' sp' x);
      [ exact (accok_aclient lv frs m sp' b n x ACR ltac:(lia)) | solve [live_sub_tac] | solve [frames_sub_tac] | lia ] end end.
Ltac ta_at_call2 RT AF PFS PFO ACR ACG ACB ACA :=
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul|
                        split; [intros zz Hzz; acl_of ACR| split; [intros zz Hzz; acl_of ACG| split; [intros zz Hzz; acl_of ACB| split; [intros zz Hzz; acl_of ACA| exact I]]]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (PFO _ Hx); repeat split; try exact I; lia).

Section TOARR.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem pixcmapToArrays_ok : pixcmapToArrays_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo cmap cv pr pg pb pa x1 x2 x3 x4
    FDO MST -> -> -> -> -> -> COBJ NZ OPR OPG OPB OPA CR CG CB_ CA ND ENV RES.
  pose proof (gp_calloc RT GP) as CALLOC.
  unfold lpost, lenv, lres, keeps, keepsL, optrF in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct OPR as (OWNR & PR0 & PR8 & PRH & PRS). destruct OPG as (OWNG & PG0 & PG8 & PGH & PGS).
  destruct OPB as (OWNB & PB0 & PB8 & PBH & PBS). destruct OPA as (OWNA & PA0 & PA8 & PAH & PAS).
  pose proof COBJ as ((cpad & CMC) & (CIN & C0 & C16 & _) & (AIN & A0 & A16 & ASZ) & (CDEP & CNAL & CN0 & CNN) & CANE).
  unfold cmap_cells in CMC.
  assert (CN256 : c_nalloc cv <= 256).
  { clear - CDEP CNAL. rewrite CNAL. cbn [In] in CDEP. destruct CDEP as [E|[E|[E|[E|E]]]]; try (rewrite <- E; cbv; discriminate). destruct E. }
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixcmapToArrays, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  clearbody usp.
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (LVF := rt_live RT Σ) in *.
  set (PF0 := fun a => aclient LVF (rt_frames RT Σ) usp a).
  set (PF := fun a => aclient LVF (rt_frames RT Σ) usp a /\ outside [(pr, pr + 8); (pg, pg + 8); (pb, pb + 8); (pa, pa + 8)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (LVFS : forall e, In e LVF -> In e (rt_live RT Σ)) by (intros e He; exact He).
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (PFO : forall a, PF a -> (a < pr \/ pr + 8 <= a) /\ (a < pg \/ pg + 8 <= a) /\ (a < pb \/ pb + 8 <= a) /\ (a < pa \/ pa + 8 <= a)).
  { intros a [_ Ho]. cbn [outside] in Ho. lia. }
  assert (ACR : accok LVF (rt_frames RT Σ) m pr 8) by (right; exact OWNR).
  assert (ACG : accok LVF (rt_frames RT Σ) m pg 8) by (right; exact OWNG).
  assert (ACB : accok LVF (rt_frames RT Σ) m pb 8) by (right; exact OWNB).
  assert (ACA : accok LVF (rt_frames RT Σ) m pa 8) by (right; exact OWNA).
  assert (PLO : pr + 8 <= lo /\ pg + 8 <= lo /\ pb + 8 <= lo /\ pa + 8 <= lo).
  { repeat split.
    - destruct OWNR as (f & k & Hin & H1 & H2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). unfold STACK_WIN in R. lia.
    - destruct OWNG as (f & k & Hin & H1 & H2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). unfold STACK_WIN in R. lia.
    - destruct OWNB as (f & k & Hin & H1 & H2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). unfold STACK_WIN in R. lia.
    - destruct OWNA as (f & k & Hin & H1 & H2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). unfold STACK_WIN in R. lia. }
  destruct PLO as (PRLO & PGLO & PBLO & PALO).
  destruct ND as (NRG & NRB & NRA & NGB & NGA & NBA).
  chunk_facts RT AF GP cmap 24. chunk_facts RT AF GP (c_arr cv) (4 * c_nalloc cv).
  assert (ACCR : acc asegs m pr 8) by (apply (accok_acc RT AF Σ m pr 8 ART0 ltac:(lia)); right; exact OWNR).
  assert (ACCG : acc asegs m pg 8) by (apply (accok_acc RT AF Σ m pg 8 ART0 ltac:(lia)); right; exact OWNG).
  assert (ACCB : acc asegs m pb 8) by (apply (accok_acc RT AF Σ m pb 8 ART0 ltac:(lia)); right; exact OWNB).
  assert (ACCA : acc asegs m pa 8) by (apply (accok_acc RT AF Σ m pa 8 ART0 ltac:(lia)); right; exact OWNA).
  assert (APC : forall p, own_frame (rt_frames RT Σ) m p 8 -> (p + 8 <= cmap \/ cmap + 24 <= p) /\ (p + 8 <= c_arr cv \/ c_arr cv + 4 * c_nalloc cv <= p)).
  { intros p (f & k & Hin & H1 & H2 & _). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & _ & R).
    pose proof (R cmap 24 CIN) as R1. pose proof (R (c_arr cv) (4 * c_nalloc cv) AIN) as R2. clear - H1 H2 R1 R2. lia. }
  destruct (APC pr OWNR) as (PRC_ & PRA_). destruct (APC pg OWNG) as (PGC_ & PGA_). destruct (APC pb OWNB) as (PBC_ & PBA_). destruct (APC pa OWNA) as (PAC_ & PAA_).
  clear APC.
  park_disj. carve_frame 112%nat ST.
  idtac "MARK carved".
  pose proof (af_acc_live RT AF Σ m cmap 24 ART0 CIN) as (WRC & ACCC).
  pose proof (af_acc_live RT AF Σ m (c_arr cv) (4 * c_nalloc cv) ART0 AIN) as (WRA & ACCAR).
  Time walk_to AF MST [(usp - 112, usp); (pr, pr + 8); (pg, pg + 8); (pb, pb + 8); (pa, pa + 8)] [e_calloc; 0x991f8; 0x99228].
  assert (TR1 : In [0x99184] CLIENT_TRACES) by (apply ct_mem_In; vm_compute; reflexivity).
  assert (TR2 : In [0x99194] CLIENT_TRACES) by (apply ct_mem_In; vm_compute; reflexivity).
  assert (TR3 : In [0x991a4] CLIENT_TRACES) by (apply ct_mem_In; vm_compute; reflexivity).
  assert (TR4 : In [0x991e4] CLIENT_TRACES) by (apply ct_mem_In; vm_compute; reflexivity).
  unfold LVF in LVB, LVP.
  rewrite ?(sx32_small (c_n cv)) by lia.
  ta_at_call2 RT AF PFS PFO ACR ACG ACB ACA.
  idtac "MARK at calloc 1".
  ta_calloc RT GP lo (c_n cv) TR1.
  idtac "MARK calloc 1 applied".
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono LVF _ usp _ _ _ _ (proj1 Hx)); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
  lazymatch goal with H : rt_live RT ?S = (?p, _) :: _ |- cps _ (ASTA RT ?S _ _) _ => rename H into LV1; rename S into Σ1; rename p into rmap end.
  lazymatch goal with H : rw_cells asegs _ rmap _ |- _ => rename H into RCB end.
  lazymatch goal with H : 0 < rmap |- _ => rename H into RM0 end.
  lazymatch goal with H : rmap mod 16 = 0 |- _ => rename H into RM16 end.
  chunk_facts RT AF GP rmap (c_n cv * 4). accok_now RT.
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  idtac "MARK after calloc 1".
  Time walk_to AF MST [(usp - 112, usp); (pr, pr + 8); (pg, pg + 8); (pb, pb + 8); (pa, pa + 8)] [e_calloc; 0x991f8; 0x99228].
  ta_at_call2 RT AF PFS PFO ACR ACG ACB ACA.
  idtac "MARK at calloc 2".
  ta_calloc RT GP lo (c_n cv) TR2.
  idtac "MARK calloc 2 applied".
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono LVF _ usp _ _ _ _ (proj1 Hx)); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
  lazymatch goal with H : rt_live RT ?S = (?p, _) :: _ |- cps _ (ASTA RT ?S _ _) _ => rename H into LV2; rename S into Σ2; rename p into gmap end.
  lazymatch goal with H : rw_cells asegs _ gmap _ |- _ => rename H into GCB end.
  lazymatch goal with H : 0 < gmap |- _ => rename H into GM0 end.
  lazymatch goal with H : gmap mod 16 = 0 |- _ => rename H into GM16 end.
  chunk_facts RT AF GP gmap (c_n cv * 4). accok_now RT.
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  idtac "MARK after calloc 2".
  Time walk_to AF MST [(usp - 112, usp); (pr, pr + 8); (pg, pg + 8); (pb, pb + 8); (pa, pa + 8)] [e_calloc; 0x991f8; 0x99228].
  ta_at_call2 RT AF PFS PFO ACR ACG ACB ACA.
  idtac "MARK at calloc 3".
  ta_calloc RT GP lo (c_n cv) TR3.
  idtac "MARK calloc 3 applied".
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono LVF _ usp _ _ _ _ (proj1 Hx)); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
  lazymatch goal with H : rt_live RT ?S = (?p, _) :: _ |- cps _ (ASTA RT ?S _ _) _ => rename H into LV3; rename S into Σ3; rename p into bmap end.
  lazymatch goal with H : rw_cells asegs _ bmap _ |- _ => rename H into BCB end.
  lazymatch goal with H : 0 < bmap |- _ => rename H into BM0 end.
  lazymatch goal with H : bmap mod 16 = 0 |- _ => rename H into BM16 end.
  chunk_facts RT AF GP bmap (c_n cv * 4). accok_now RT.
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  idtac "MARK after calloc 3".
  Time walk_to AF MST [(usp - 112, usp); (pr, pr + 8); (pg, pg + 8); (pb, pb + 8); (pa, pa + 8)] [e_calloc; 0x991f8; 0x99228].
  ta_at_call2 RT AF PFS PFO ACR ACG ACB ACA.
  idtac "MARK at calloc 4".
  ta_calloc RT GP lo (c_n cv) TR4.
  idtac "MARK calloc 4 applied".
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono LVF _ usp _ _ _ _ (proj1 Hx)); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
  lazymatch goal with H : rt_live RT ?S = (?p, _) :: _ |- cps _ (ASTA RT ?S _ _) _ => rename H into LV4; rename S into Σ4; rename p into amap end.
  lazymatch goal with H : rw_cells asegs _ amap _ |- _ => clear H end.
  lazymatch goal with H : 0 < amap |- _ => rename H into AM0 end.
  lazymatch goal with H : amap mod 16 = 0 |- _ => rename H into AM16 end.
  chunk_facts RT AF GP amap (c_n cv * 4). accok_now RT.
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  idtac "MARK after calloc 4".
  Time walk_to AF MST [(usp - 112, usp); (pr, pr + 8); (pg, pg + 8); (pb, pb + 8); (pa, pa + 8)] [0x992d8; 0x9940c; 0x991f8; 0x99228].
  (* [comment removed for export] *)
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; acl_of ACR| split; [intros zz Hzz; acl_of ACG| split; [intros zz Hzz; acl_of ACB| split; [intros zz Hzz; acl_of ACA| exact I]]]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); pose proof (PFO _ Hx); repeat split; try exact I; lia) end.
  idtac "MARK loop: segment closed".
  set (n := c_n cv) in *.
  assert (LVA : rt_live RT Σ4 = (amap, n * 4) :: (bmap, n * 4) :: (gmap, n * 4) :: (rmap, n * 4) :: rt_live RT Σ)
    by (rewrite LV4, LV3, LV2, LV1; reflexivity).
  assert (FRS4 : rt_frames RT Σ4 = rt_frames RT Σ) by (repeat match goal with E : rt_frames _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (SP04 : rt_sp0 RT Σ4 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CR4 : rt_credit RT Σ <= rt_credit RT Σ4) by (repeat match goal with E : rt_credit _ _ = _ |- _ => rewrite E end; unfold mcost; repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia).
  assert (INR : In (rmap, n * 4) (rt_live RT Σ4)) by (rewrite LVA; do 3 right; left; reflexivity).
  assert (ING : In (gmap, n * 4) (rt_live RT Σ4)) by (rewrite LVA; do 2 right; left; reflexivity).
  assert (INB : In (bmap, n * 4) (rt_live RT Σ4)) by (rewrite LVA; right; left; reflexivity).
  assert (INZ : In (amap, n * 4) (rt_live RT Σ4)) by (rewrite LVA; left; reflexivity).
  assert (INC : In (c_arr cv, 4 * c_nalloc cv) (rt_live RT Σ4)) by (rewrite LVA; do 4 right; exact AIN).
  lazymatch goal with A : ART RT Σ4 ?mm |- cps _ (ASTA RT Σ4 _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    pose proof (af_acc_live RT AF Σ4 mm rmap (n * 4) A INR) as (WRR & ACR_);
    pose proof (af_acc_live RT AF Σ4 mm gmap (n * 4) A ING) as (WRG & ACG_);
    pose proof (af_acc_live RT AF Σ4 mm bmap (n * 4) A INB) as (WRB & ACB_);
    pose proof (af_acc_live RT AF Σ4 mm amap (n * 4) A INZ) as (WRZ & ACZ_);
    pose proof (af_acc_live RT AF Σ4 mm (c_arr cv) (4 * c_nalloc cv) A INC) as (WRC_ & ACC_);
    pose proof (af_live_range RT AF Σ4 mm rmap (n * 4) A INR) as (_ & RHI_ & RSEG_); pose proof (gp_live_hi RT GP Σ4 mm rmap (n * 4) A INR) as RSH_;
    pose proof (af_live_range RT AF Σ4 mm gmap (n * 4) A ING) as (_ & GHI_ & GSEG_); pose proof (gp_live_hi RT GP Σ4 mm gmap (n * 4) A ING) as GSH_;
    pose proof (af_live_range RT AF Σ4 mm bmap (n * 4) A INB) as (_ & BHI_ & BSEG_); pose proof (gp_live_hi RT GP Σ4 mm bmap (n * 4) A INB) as BSH_;
    pose proof (af_live_range RT AF Σ4 mm amap (n * 4) A INZ) as (_ & ZHI_ & ZSEG_); pose proof (gp_live_hi RT GP Σ4 mm amap (n * 4) A INZ) as ZSH_;
    pose proof (af_live_range RT AF Σ4 mm (c_arr cv) (4 * c_nalloc cv) A INC) as (_ & CHI_ & CSEG_); pose proof (gp_live_hi RT GP Σ4 mm (c_arr cv) (4 * c_nalloc cv) A INC) as CSH_;
    (* [comment removed for export] *)
    pose proof (af_live_disj RT AF Σ4 mm amap (n * 4) bmap (n * 4) [] _ A LVA ltac:(cbn [app In]; left; reflexivity)) as SZB_;
    pose proof (af_live_disj RT AF Σ4 mm amap (n * 4) gmap (n * 4) [] _ A LVA ltac:(cbn [app In]; right; left; reflexivity)) as SZG_;
    pose proof (af_live_disj RT AF Σ4 mm amap (n * 4) rmap (n * 4) [] _ A LVA ltac:(cbn [app In]; do 2 right; left; reflexivity)) as SZR_;
    pose proof (af_live_disj RT AF Σ4 mm amap (n * 4) (c_arr cv) (4 * c_nalloc cv) [] _ A LVA ltac:(cbn [app In]; do 3 right; exact AIN)) as SZC_;
    pose proof (af_live_disj RT AF Σ4 mm bmap (n * 4) gmap (n * 4) [(amap, n * 4)] _ A LVA ltac:(cbn [app In]; right; left; reflexivity)) as SBG_;
    pose proof (af_live_disj RT AF Σ4 mm bmap (n * 4) rmap (n * 4) [(amap, n * 4)] _ A LVA ltac:(cbn [app In]; do 2 right; left; reflexivity)) as SBR_;
    pose proof (af_live_disj RT AF Σ4 mm bmap (n * 4) (c_arr cv) (4 * c_nalloc cv) [(amap, n * 4)] _ A LVA ltac:(cbn [app In]; do 3 right; exact AIN)) as SBC_;
    pose proof (af_live_disj RT AF Σ4 mm gmap (n * 4) rmap (n * 4) [(amap, n * 4); (bmap, n * 4)] _ A LVA ltac:(cbn [app In]; do 2 right; left; reflexivity)) as SGR_;
    pose proof (af_live_disj RT AF Σ4 mm gmap (n * 4) (c_arr cv) (4 * c_nalloc cv) [(amap, n * 4); (bmap, n * 4)] _ A LVA ltac:(cbn [app In]; do 3 right; exact AIN)) as SGC_;
    pose proof (af_live_disj RT AF Σ4 mm rmap (n * 4) (c_arr cv) (4 * c_nalloc cv) [(amap, n * 4); (bmap, n * 4); (gmap, n * 4)] _ A LVA ltac:(cbn [app In]; do 3 right; exact AIN)) as SRC_
  end.
  unfold STACK_WIN, SEGTOP_A in *.
  rewrite SP04 in RHI_, GHI_, BHI_, ZHI_, CHI_.
  park_disj.
  idtac "MARK loop: chunk facts".
  (* [comment removed for export] *)
  assert (N1 : 1 <= n <= 256) by (unfold n; clear - NZ CNN CN256; lia).
  apply wr_at_rw_CB in WRR; [| clear - N1; lia]. destruct WRR as (rbs & RBC).
  pose proof RBC as [[[RBL _] _] _]. cbn in RBL. apply u8arr_of_rw_cells in RBC.
  lazymatch type of RBC with u8arr _ ?mm _ _ => destruct (u8arr_u32arr mm rmap rbs n RBC ltac:(rewrite RBL; clear - N1; lia)) as (rs & UAR & UARL) end.
  apply wr_at_rw_CB in WRG; [| clear - N1; lia]. destruct WRG as (gbs & GBC).
  pose proof GBC as [[[GBL _] _] _]. cbn in GBL. apply u8arr_of_rw_cells in GBC.
  lazymatch type of GBC with u8arr _ ?mm _ _ => destruct (u8arr_u32arr mm gmap gbs n GBC ltac:(rewrite GBL; clear - N1; lia)) as (gs & UAG & UAGL) end.
  apply wr_at_rw_CB in WRB; [| clear - N1; lia]. destruct WRB as (bbs & BBC).
  pose proof BBC as [[[BBL _] _] _]. cbn in BBL. apply u8arr_of_rw_cells in BBC.
  lazymatch type of BBC with u8arr _ ?mm _ _ => destruct (u8arr_u32arr mm bmap bbs n BBC ltac:(rewrite BBL; clear - N1; lia)) as (bs & UAB & UABL) end.
  apply wr_at_rw_CB in WRZ; [| clear - N1; lia]. destruct WRZ as (zbs & ZBC).
  pose proof ZBC as [[[ZBL _] _] _]. cbn in ZBL. apply u8arr_of_rw_cells in ZBC.
  lazymatch type of ZBC with u8arr _ ?mm _ _ => destruct (u8arr_u32arr mm amap zbs n ZBC ltac:(rewrite ZBL; clear - N1; lia)) as (zs & UAZ & UAZL) end.
  apply wr_at_rw_CB in WRC_; [| clear - ASZ; lia]. destruct WRC_ as (cbs & CBC).
  pose proof CBC as [[[CBL _] _] _]. cbn in CBL. apply u8arr_of_rw_cells in CBC.
  assert (CBL' : Z.of_nat (length cbs) = 4 * c_nalloc cv) by (rewrite CBL; clear - ASZ; lia).
  clear RBC GBC BBC ZBC.
  idtac "MARK loop: arrays".
  (* [comment removed for export] *)
  assert (Q1 : Z.of_nat (Z.to_nat n) = n - 0) by (clear - N1; lia).
  assert (Q3 : (1 <= Z.to_nat n)%nat) by (clear - N1; lia).
  assert (QN : n <= c_nalloc cv) by (unfold n; exact CNN).
  assert (QPA : 0 < pa < 2^64) by (clear - PA0 PALO STb LOR; lia).
  assert (C8_ : c_arr cv mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
  assert (CHI' : c_arr cv + 4 * c_nalloc cv <= 2^47) by (clear - CHI_ SP0R1; lia).
  assert (CSH' : c_arr cv + 4 * c_nalloc cv <= 0x7fff7000 \/ 0x10007fff8000 <= c_arr cv) by (clear - CSH_; unfold parked in CSH_; lia).
  assert (CSEG' : c_arr cv + 4 * c_nalloc cv <= 0x10000 \/ 6569984 <= c_arr cv) by (clear - CSEG_; unfold parked in CSEG_; lia).
  assert (R8 : rmap mod 8 = 0) by (clear - RM16; Z.div_mod_to_equations; lia).
  assert (RHI' : rmap + 4 * n <= 2^47) by (clear - RHI_ SP0R1; lia).
  assert (RSH' : rmap + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= rmap) by (clear - RSH_; unfold parked in RSH_; lia).
  assert (RSEG' : rmap + 4 * n <= 0x10000 \/ 6569984 <= rmap) by (clear - RSEG_; unfold parked in RSEG_; lia).
  assert (G8 : gmap mod 8 = 0) by (clear - GM16; Z.div_mod_to_equations; lia).
  assert (GHI' : gmap + 4 * n <= 2^47) by (clear - GHI_ SP0R1; lia).
  assert (GSH' : gmap + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= gmap) by (clear - GSH_; unfold parked in GSH_; lia).
  assert (GSEG' : gmap + 4 * n <= 0x10000 \/ 6569984 <= gmap) by (clear - GSEG_; unfold parked in GSEG_; lia).
  assert (B8 : bmap mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  assert (BHI' : bmap + 4 * n <= 2^47) by (clear - BHI_ SP0R1; lia).
  assert (BSH' : bmap + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= bmap) by (clear - BSH_; unfold parked in BSH_; lia).
  assert (BSEG' : bmap + 4 * n <= 0x10000 \/ 6569984 <= bmap) by (clear - BSEG_; unfold parked in BSEG_; lia).
  assert (Z8 : amap mod 8 = 0) by (clear - AM16; Z.div_mod_to_equations; lia).
  assert (ZHI' : amap + 4 * n <= 2^47) by (clear - ZHI_ SP0R1; lia).
  assert (ZSH' : amap + 4 * n <= 0x7fff7000 \/ 0x10007fff8000 <= amap) by (clear - ZSH_; unfold parked in ZSH_; lia).
  assert (ZSEG' : amap + 4 * n <= 0x10000 \/ 6569984 <= amap) by (clear - ZSEG_; unfold parked in ZSEG_; lia).
  assert (SCR' : c_arr cv + 4 * c_nalloc cv <= rmap \/ rmap + 4 * n <= c_arr cv) by (clear - SRC_; unfold parked in SRC_; lia).
  assert (SCG' : c_arr cv + 4 * c_nalloc cv <= gmap \/ gmap + 4 * n <= c_arr cv) by (clear - SGC_; unfold parked in SGC_; lia).
  assert (SCB' : c_arr cv + 4 * c_nalloc cv <= bmap \/ bmap + 4 * n <= c_arr cv) by (clear - SBC_; unfold parked in SBC_; lia).
  assert (SCZ' : c_arr cv + 4 * c_nalloc cv <= amap \/ amap + 4 * n <= c_arr cv) by (clear - SZC_; unfold parked in SZC_; lia).
  assert (SRG' : rmap + 4 * n <= gmap \/ gmap + 4 * n <= rmap) by (clear - SGR_; unfold parked in SGR_; lia).
  assert (SRB' : rmap + 4 * n <= bmap \/ bmap + 4 * n <= rmap) by (clear - SBR_; unfold parked in SBR_; lia).
  assert (SRZ' : rmap + 4 * n <= amap \/ amap + 4 * n <= rmap) by (clear - SZR_; unfold parked in SZR_; lia).
  assert (SGB' : gmap + 4 * n <= bmap \/ bmap + 4 * n <= gmap) by (clear - SBG_; unfold parked in SBG_; lia).
  assert (SGZ' : gmap + 4 * n <= amap \/ amap + 4 * n <= gmap) by (clear - SZG_; unfold parked in SZG_; lia).
  assert (SBZ' : bmap + 4 * n <= amap \/ amap + 4 * n <= bmap) by (clear - SZB_; unfold parked in SZB_; lia).
  assert (ACR' : forall mm p, acc asegs mm p (n * 4) -> acc asegs mm p (4 * n)) by (intros mm p Hq; replace (4 * n) with (n * 4) by (clear; lia); exact Hq).
  apply ACR' in ACR_. apply ACR' in ACG_. apply ACR' in ACB_. apply ACR' in ACZ_. clear ACR'.
  park_disj.
  idtac "MARK loop: premises".
  (* [comment removed for export] *)
  assert (N4 : 0 < n * 4) by (clear - N1; lia).
  assert (SUBR : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ4) /\ fst e <> rmap)
    by (intros e He; split; [rewrite LVA; do 4 right; exact He|];
        apply (fresh_chunk_ne RT AF Σ4 _ [(amap, n * 4); (bmap, n * 4); (gmap, n * 4)] rmap (n * 4) _ e ltac:(eassumption) LVA);
        [ cbn [app In]; do 3 right; exact He | exact N4 | destruct e as [eq ek]; exact (LVP eq ek He) ]).
  assert (SUBG : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ4) /\ fst e <> gmap)
    by (intros e He; split; [rewrite LVA; do 4 right; exact He|];
        apply (fresh_chunk_ne RT AF Σ4 _ [(amap, n * 4); (bmap, n * 4)] gmap (n * 4) _ e ltac:(eassumption) LVA);
        [ cbn [app In]; do 3 right; exact He | exact N4 | destruct e as [eq ek]; exact (LVP eq ek He) ]).
  assert (SUBB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ4) /\ fst e <> bmap)
    by (intros e He; split; [rewrite LVA; do 4 right; exact He|];
        apply (fresh_chunk_ne RT AF Σ4 _ [(amap, n * 4)] bmap (n * 4) _ e ltac:(eassumption) LVA);
        [ cbn [app In]; do 3 right; exact He | exact N4 | destruct e as [eq ek]; exact (LVP eq ek He) ]).
  assert (SUBA : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ4) /\ fst e <> amap)
    by (intros e He; split; [rewrite LVA; do 4 right; exact He|];
        apply (fresh_chunk_ne RT AF Σ4 _ [] amap (n * 4) _ e ltac:(eassumption) LVA);
        [ cbn [app In]; do 3 right; exact He | exact N4 | destruct e as [eq ek]; exact (LVP eq ek He) ]).
  lazymatch goal with A : ART RT Σ4 ?mm |- cps _ (ASTA RT Σ4 _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    assert (NCR : forall a, PF a -> a < rmap \/ rmap + n * 4 <= a)
      by (intros a [Ha _]; apply (inner_chunk_apart RT AF Σ4 mm rmap (n * 4) (rt_live RT Σ) (rt_frames RT Σ) usp a A INR SUBR);
          [ rewrite FRS4; intros e He; exact He | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; clear - LOW LOR; lia | exact Ha ]);
    assert (NCG : forall a, PF a -> a < gmap \/ gmap + n * 4 <= a)
      by (intros a [Ha _]; apply (inner_chunk_apart RT AF Σ4 mm gmap (n * 4) (rt_live RT Σ) (rt_frames RT Σ) usp a A ING SUBG);
          [ rewrite FRS4; intros e He; exact He | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; clear - LOW LOR; lia | exact Ha ]);
    assert (NCB : forall a, PF a -> a < bmap \/ bmap + n * 4 <= a)
      by (intros a [Ha _]; apply (inner_chunk_apart RT AF Σ4 mm bmap (n * 4) (rt_live RT Σ) (rt_frames RT Σ) usp a A INB SUBB);
          [ rewrite FRS4; intros e He; exact He | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; clear - LOW LOR; lia | exact Ha ]);
    assert (NCA : forall a, PF a -> a < amap \/ amap + n * 4 <= a)
      by (intros a [Ha _]; apply (inner_chunk_apart RT AF Σ4 mm amap (n * 4) (rt_live RT Σ) (rt_frames RT Σ) usp a A INZ SUBA);
          [ rewrite FRS4; intros e He; exact He | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; clear - LOW LOR; lia | exact Ha ])
  end.
  clear SUBR SUBG SUBB SUBA.
  (* [comment removed for export] *)
  assert (OAP : forall p X, own_frame (rt_frames RT Σ) m p 8 -> In (X, n * 4) (rt_live RT Σ4) -> p + 8 <= X \/ X + n * 4 <= p).
  { intros p X (f & k & Hin & Hq1 & Hq2 & _) HX.
    lazymatch goal with A : ART RT Σ4 ?mm |- _ =>
      pose proof (af_frames_range RT AF Σ4 mm f k A ltac:(rewrite FRS4; exact Hin)) as (_ & _ & _ & R) end.
    pose proof (R X (n * 4) HX) as Rq1. clear - Hq1 Hq2 Rq1. lia. }
  pose proof (OAP pr rmap OWNR INR) as PRr. pose proof (OAP pr gmap OWNR ING) as PRg. pose proof (OAP pr bmap OWNR INB) as PRb. pose proof (OAP pr amap OWNR INZ) as PRz.
  pose proof (OAP pg rmap OWNG INR) as PGr. pose proof (OAP pg gmap OWNG ING) as PGg. pose proof (OAP pg bmap OWNG INB) as PGb. pose proof (OAP pg amap OWNG INZ) as PGz.
  pose proof (OAP pb rmap OWNB INR) as PBr. pose proof (OAP pb gmap OWNB ING) as PBg. pose proof (OAP pb bmap OWNB INB) as PBb. pose proof (OAP pb amap OWNB INZ) as PBz.
  pose proof (OAP pa rmap OWNA INR) as PAr. pose proof (OAP pa gmap OWNA ING) as PAg. pose proof (OAP pa bmap OWNA INB) as PAb. pose proof (OAP pa amap OWNA INZ) as PAz.
  clear OAP. park_disj.
  idtac "MARK loop: apartness".
  walk_to AF MST [(rmap, rmap + 4 * n); (gmap, gmap + 4 * n); (bmap, bmap + 4 * n); (amap, amap + 4 * n)] [0x992d8].
  replace (n * 4) with (4 * n) by (clear; lia).
  eapply evt_cut.
  { lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      epose proof (toarr_loop (Z.to_nat n) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (c_arr cv) (c_nalloc cv) rmap gmap bmap amap pa n cbs rs gs bs zs
                     Q1 ltac:(lia) Q3 QN CN256 QPA CBC CBL' ACC_ A0 C8_ CHI' CSH' CSEG'
                     UAR UARL ACR_ RM0 R8 RHI' RSH' RSEG' UAG UAGL ACG_ GM0 G8 GHI' GSH' GSEG' UAB UABL ACB_ BM0 B8 BHI' BSH' BSEG' UAZ UAZL ACZ_ AM0 Z8 ZHI' ZSH' ZSEG'
                     SCR' SCG' SCB' SCZ' SRG' SRB' SRZ' SGB' SGZ' SBZ' MIx) as ZR end.
    unfold SHB, SEGTOP_A in ZR. change (4 * 0) with 0 in ZR.
    exact ZR. }
  idtac "MARK loop applied".
  intros ms' PO. unfold toarr_exit in PO.
  destruct PO as (a1r & a2r & a3r & a5r & a6r & a7r & mr & -> & MUr & WMr & MIr).
  unfold SHB.
  loop_art RT AF Σ4 mr lo MUr ltac:(cbn [ivls_client];
     split; [intros zz Hzz; right; right; left; exists rmap, (n * 4); split; [exact INR| clear - Hzz; lia]|
     split; [intros zz Hzz; right; right; left; exists gmap, (n * 4); split; [exact ING| clear - Hzz; lia]|
     split; [intros zz Hzz; right; right; left; exists bmap, (n * 4); split; [exact INB| clear - Hzz; lia]|
     split; [intros zz Hzz; right; right; left; exists amap, (n * 4); split; [exact INZ| clear - Hzz; lia]| exact I]]]]).
  clear UAR UARL UAG UAGL UAB UABL UAZ UAZL CBC ACR_ ACG_ ACB_ ACZ_ ACC_.
  idtac "MARK loop_art".
  lazymatch type of MUr with munch _ ?ma ?mb =>
    loop_transport ma mb MUr ltac:(fun Hx => first
      [ clear - Hx RHI_ GHI_ BHI_ ZHI_ LOW LOR; lia
      | clear - Hx RSEG_ GSEG_ BSEG_ ZSEG_; unfold parked in *; lia
      | clear - Hx PRr PRg PRb PRz; unfold parked in *; lia
      | clear - Hx PGr PGg PGb PGz; unfold parked in *; lia
      | clear - Hx PBr PBg PBb PBz; unfold parked in *; lia
      | clear - Hx PAr PAg PAb PAz; unfold parked in *; lia
      | clear - Hx SCR' SCG' SCB' SCZ'; unfold parked in *; lia ]) end.
  idtac "MARK loop_transport".
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client];
     split; [intros zz Hzz; right; right; left; exists rmap, (n * 4); split; [solve [in_live_tac]| clear - Hzz; lia]|
     split; [intros zz Hzz; right; right; left; exists gmap, (n * 4); split; [solve [in_live_tac]| clear - Hzz; lia]|
     split; [intros zz Hzz; right; right; left; exists bmap, (n * 4); split; [solve [in_live_tac]| clear - Hzz; lia]|
     split; [intros zz Hzz; right; right; left; exists amap, (n * 4); split; [solve [in_live_tac]| clear - Hzz; lia]| exact I]]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (NCR _ Hx) as Nr; pose proof (NCG _ Hx) as Ng; pose proof (NCB _ Hx) as Nb; pose proof (NCA _ Hx) as Na;
                                      clear - Nr Ng Nb Na; repeat split; try exact I; lia) end.
  idtac "MARK after loop".
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  Time walk_to AF MST [(usp - 112, usp)] (@nil Z).
  cps_stop.
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, rmap, gmap, bmap, amap end.
  split.
  - eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
    split; [unfold ret_st; do 16 eexists; reflexivity|].
    split; [split; [split; [eassumption| split; [assumption| split; [exact WM| assumption]]]| split; assumption]|].
    split; [intros a Ha Ho; apply AGF; split; [exact Ha| exact Ho]|].
    split; [exact CR|]. split; [exact CG|]. split; [exact CB_| exact CA].
  - rewrite LVA. unfold n. replace (c_n cv * 4) with (4 * c_n cv) by (clear; lia).
    split; [reflexivity|]. split; [exact FRS4|]. split; [exact SP04| exact CR4].
Qed.
End TOARR.
