(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ALogic16 ARtStmts AMTac AMallocI.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ACallocE.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ACallocE AMalmys AMaly5g ASecB1 ACor4x6 AWrapKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACallocE.ACallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACallocE OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMaly5g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AWrapKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module AWrapM.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic
     ALogic16 ARtStmts AMTac AMallocI AMalmys AMaly5g ASecB1 ACor4x6 AWrapKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section Wrap.
Context {Clg : Ceiling}.
  Hypothesis UNW : unwind_stmt.
  (* [comment removed for export] *)
  Hypothesis ACORE : alloc_core_cps1.

  #[using="ACORE UNW"] Theorem pa_malloc16_of_core : @pa_malloc_obligation16 _ DepotRepL.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A n T.
    cbv zeta. intros AI MI Ha0 NRQ NCAP LIM NLV TINY SCRED PCRED TPE SPA RA4 SITE S0C CEIL SM KK.   (* [comment removed for export] *)
    cbn [cl_segs cl_malloc_pc LPA] in MI |- *.
    pose proof (hit_stk A m sp CEIL SM) as ST. pose proof (hit_sp47 A m md sp AI CEIL SM) as SPH. unfold ASTK in *.
    pose proof alloc_ceiling_val as CE. pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
    (first [ pose proof ((hit_place A m md AI)) as dR_1; dand7 dR_1 as TH1 TH2 THRA CT1 CT2 TOPR BOTR | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & CT1 & CT2 & TOPR & BOTR) ]).
    (first [ pose proof ((hit_sep A m md AI)) as dR_2; dand4 dR_2 as _ _ SEP_tc _ | pose proof (hit_sep A m md AI) as (_ & _ & SEP_tc & _) ]).
    pose proof (hit_TC A m md AI) as TC. pose proof (hit_tsd A m md AI) as [TSD1 TSD2].
    pose proof (hit_INI A m md AI) as CINI. pose proof (hit_CMCS A m md AI) as CMCS. pose proof (hit_CFU A m md AI) as CFU.
    pose proof (hit_TTB A m md AI) as TTB. pose proof (hit_TDT A m md AI) as TDT. pose proof (hit_TUNW A m md AI) as TUNW.
    pose proof (hit_PCo A m md AI) as PCo. unfold poison_consts in PCo.
    (first [ dand13 PCo as _ Cflags _ _ _ _ _ _ _ _ _ Cgps Cps | destruct PCo as (_ & Cflags & _ & _ & _ & _ & _ & _ & _ & _ & _ & Cgps & Cps) ]).
    subst a0 tp. unfold REQ_MAX in NRQ.
    assert (LO : alloc_ceiling <= bv_unsigned sp - 8192 /\ bv_unsigned sp - 8192 <= bv_unsigned sp - 2128 - 224) by lia.
    pose proof (proj1 (Forall_forall _ _) pa_sites_range _ SITE) as RAr. cbv beta in RAr. assert (RA0 : 4096 <= bv_unsigned ra) by lia.
    assert (RANE : bv_unsigned ra <> 0x58c14) by (intros E; apply (pa_pcs_not_sites 0x58c14 ltac:(cbn; tauto)); rewrite <- E; exact SITE).
    assert (VLE : bv_unsigned s0 <= bv_unsigned sp) by lia.
    assert (TPL : bv_unsigned (cl_tp LPA) = 0x5e83d8) by (cbn [cl_tp LPA]; rewrite unsigned_lit by lia; reflexivity).
    destruct (asI_minv A m md AI) as [HMI HH].
    set (fp := bv_unsigned sp) in *. set (thr := p_thr (a_pl A)) in *. set (v := aview_of (pa_hull A) m) in *.
    set (top := p_stk_top (a_pl A)) in *. set (bot := p_stk_bot (a_pl A)) in *.
    (* [comment removed for export] *)
    pose (Q1 := fun ms' : machine_state => exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (pad jb1 jrest : list byte) (m1 : mem),
        ms' = MS (mkR (wz 0x3716c) (wz (fp + -2144)) gp (cl_tp LPA) t0' t1' t2' sp (wz n)
                     (wz 0xb1d58) (wz n) (wz 8) (wz (fp + -2128)) (wz 1) (wz 1) a6' a7'
                     (wz 0x58c14) (wz 1) (wz (fp + -2128)) (wz (fp + -81)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (wz alloc_entry) fc None m1 (seg_rom rsegs)
        /\ munch [(fp - 2128 - 224, fp); (thr + off_th_unwinding, thr + off_th_unwinding + 1)] v m1
        /\ wmono rsegs v m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 (fp - 8192) (fp - 2144)
        /\ rw_cells rsegs m1 (fp + -2128) [C8 (wz (fp + -2128 + 16))]
        /\ (if unwind_depth2 top bot fp
            then rw_cells rsegs m1 (fp + -2128 + 8) [C4 (wz 2)] /\ rw_cells rsegs m1 (fp + -2128 + 16) [C8 (wz 0x58c14); C8 ra]
            else rw_cells rsegs m1 (fp + -2128 + 8) [C4 (wz 1)] /\ rw_cells rsegs m1 (fp + -2128 + 16) [C8 (wz 0x58c14); CB 8 jb1])
        /\ rw_cells rsegs m1 (fp + -2128 + 12) [C4 (wz 0)]
        /\ rw_cells rsegs m1 (fp + -2128 + 32) [CB 2024 jrest]
        /\ rw_cells rsegs m1 (fp + -2128 + 2056) [C8 (wz fp)]
        /\ rw_cells rsegs m1 (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)]
        /\ rw_cells rsegs m1 (fp + -64) [CB 8 pad; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ rw_cells rsegs m1 (fp + -2144) [C8 sp; C8 (wz 0x58c80)]).
    eapply (srz_evt_restrict rsegs (pa_hull A) (asI_hull_segs A m md AI) pa_wx _ (pa_eager A) Q1 _ md T HMI HH).
    { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A)) m) with v.
      amz. (* [comment removed for export] *)
      pose proof (malloc_pro_ok UNW) as PRO. unfold malloc_pro_stmt in PRO.
      eapply (PRO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ n pa_tsd (p_ctx (a_pl A)) thr top bot (fp - 8192)); clear PRO.
      all: try eassumption. all: try reflexivity. all: try (clear KK; lia).
      intros t0' t1' t2' a6' a7' t3' t4' t5' t6' pad jb1 jrest m1 O0 DEP O12 O32 PC1 TUNW1 FR1 AMF1 MU1 WM1 MI1 ST1.
      apply evt_done. unfold Q1. first [ hotw_ex13 t0' t1' t2' a6' a7' t3' t4' t5' t6' pad jb1 jrest m1 | exists t0', t1', t2', a6', a7', t3', t4', t5', t6', pad, jb1, jrest, m1 ].
      split; [reflexivity|].
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption. }
    intros msr1 md1 HQ1 HI1 SB1 CL1.
    (first [ dex13 HQ1 as t0' t1' t2' a6' a7' t3' t4' t5' t6' pad jb1 jrest m1; dand13 HQ1 as -> MU1 WM1 MI1 ST1 O0 DEP O12 O32 PC1 TUNW1 FR1 AMF1 | dand26 HQ1 as t0' t1' t2' a6' a7' t3' t4' t5' t6' pad jb1 jrest m1 -> MU1 WM1 MI1 ST1 O0 DEP O12 O32 PC1 TUNW1 FR1 AMF1 | destruct HQ1 as (t0' & t1' & t2' & a6' & a7' & t3' & t4' & t5' & t6' & pad & jb1 & jrest & m1 & -> & MU1 & WM1 & MI1 & ST1 & O0 & DEP & O12 & O32 & PC1 & TUNW1 & FR1 & AMF1) ]).
    rewrite unrestrict_MS. cbn [ms_mem] in CL1.
    lazymatch goal with |- context [munrestrict ?Hh (ms_mem (MS ?R ?FF ?pc ?fcx ?rv ?mm ?ro)) ?v2] => change (ms_mem (MS R FF pc fcx rv mm ro)) with mm end.
    assert (AG1 : forall a, 0 <= a < 2^64 -> ~ (fp - ASTK <= a < fp) -> a <> thr + 3168 -> ~ (cl_errno LPA <= a < cl_errno LPA + 4) -> ~ nowhere a -> m1 (wz a) = v (wz a)).
    { intros a Ha NW NT NE _. unfold ASTK in NW. apply MU1. rewrite unsigned_lit by lia. unfold off_th_unwinding. cbn [outside app].
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; first [apply NW; clear -X; lia| apply NT; clear -X; lia]. }
    pose proof (shell_ainv A m md md1 fp m1 nowhere AI CEIL SM AG1 ltac:(intros a []) TUNW1 WM1 CL1 HI1 SB1) as AI1.
    pose proof (shell_view A m m1 CL1) as VIEW1.
    set (m1r := munrestrict (hidc (pa_hull A)) m m1) in *.
    set (KEY := wkey 0x58c14 top bot fp ra).
    (* [comment removed for export] *)
    pose proof ACORE as AC. unfold alloc_core_cps1 in AC.
    eapply (AC (wz 0x3716c) (wz (fp + -2144)) gp (cl_tp LPA) t0' t1' t2' sp (wz n) a6' a7' (wz 0x58c14) (wz 1) (wz (fp + -2128)) (wz (fp + -81))
               s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m1r md1 A n 1 (fp + -2128) (fp - 8192) fp KEY T); clear AC.
    - (* [comment removed for export] *)
      unfold alloc_core_pre. rewrite VIEW1. cbn [cl_segs LPA].
      rewrite !unsigned_lit by lia.
      assert (KL : Z.of_nat (length KEY) = (if unwind_depth2 top bot fp then 2 else 1)) by (unfold KEY, wkey; destruct (unwind_depth2 top bot fp); reflexivity).
      split; [exact AI1|]. split; [exact MI1|]. split; [unfold REQ_MAX; lia|]. split; [exact NCAP|]. split; [exact LIM|]. split; [exact NLV|].
      split; [exact TINY|]. split; [exact SCRED|]. split; [exact PCRED|]. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [clear -SPH; lia|].
      split; [clear -SPA; Z.div_mod_to_equations; lia|]. split; [reflexivity|].
      split; [exact ST1|].
      split. { eapply (mapped_mono _ m1); [eapply (ALogic2.mapped_sub _ _ _ _ _ SM); lia|].
               intros i Hi Hv. apply (wmono_NN _ _ _ WM1); [clear -Hi CE CEIL; lia| clear -Hi SPR CE CEIL; lia| exact Hv]. }
      split; [lia|]. split; [lia|].
      split. { rewrite KL. destruct (unwind_depth2 top bot fp); destruct DEP as [D8 D16].
               all: split; [exact (conj I (conj I I))|]; cbn [cells_bytes cbytes app]; rewrite app_nil_r.
               all: apply bytes_at_app; split; [destruct O0 as [[_ B] _]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B; exact B|].
               all: rewrite length_le8; replace (fp + -2128 + Z.of_nat 8) with (fp + -2128 + 8) by lia.
               1: exact (proj2 (ro_C44_C8 m1 (fp + -2128 + 8) 2 eq_refl D8 ltac:(replace (fp + -2128 + 8 + 4) with (fp + -2128 + 12) by lia; exact O12))).
               exact (proj2 (ro_C44_C8 m1 (fp + -2128 + 8) 1 eq_refl D8 ltac:(replace (fp + -2128 + 8 + 4) with (fp + -2128 + 12) by lia; exact O12))). }
      split. { unfold KEY, wkey. destruct (unwind_depth2 top bot fp); destruct DEP as [D8 D16]; destruct D16 as [[_ B] _]; cbn [cells_bytes cbytes app map u64s] in B |- *.
               - rewrite app_nil_r in B. rewrite Z_to_bv_bv_unsigned. exact B.
               - apply bytes_at_app in B. destruct B as [B _]. rewrite app_nil_r. exact B. }
      split. { unfold KEY, wkey. (first [ pose proof ((place_extra A m md AI)) as dR_5; dand6 dR_5 as _ _ _ _ SK _ | destruct (place_extra A m md AI) as (_ & _ & _ & _ & SK & _) ]).
               destruct (SK 0x58c14 (bv_unsigned ra) ltac:(cbn; tauto) SITE) as [K2 K1]. destruct (unwind_depth2 top bot fp); [exact K2| exact K1]. }
      apply wkey_range. lia.
    - (* [comment removed for export] *)
      unfold alloc_core_K1v. cbv zeta. rewrite VIEW1.
      intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c r A' m' md' AI' MI' AMD HLE FFR PLE IAE VG RNZ LN0 LS1 LQ LB TCR LN LS LP CZ PRIM FRK ERRK CFI STK'.
      cbn [cl_segs cl_errno LPA] in MI', FRK, ERRK, CFI, STK' |- *.
      set (v' := aview_of (pa_hull A') m') in *.
      replace (ret_pc (wz 0x3716c)) with (wz 0x3716c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite !unsigned_lit in CFI, STK' by lia. replace (fp - (fp - 8192)) with 8192 in FRK by lia.
      destruct (asI_minv A' m' md' AI') as [HMI' HH'].
      (first [ pose proof ((hit_place A' m' md' AI')) as dR_6; dand3 dR_6 as TH1' TH2' _ | pose proof (hit_place A' m' md' AI') as (TH1' & TH2' & _) ]). pose proof (aobj_facts _ _ TH1') as THF'.
      pose proof (hit_TUNW A' m' md' AI') as TUNW'. fold v' in TUNW'. unfold off_th_unwinding in TUNW'.
      (* [comment removed for export] *)
      assert (CF : forall a cs, rw_cells rsegs m1 a cs -> fp - 2144 <= a -> a + Z.of_nat (cells_size cs) <= fp -> rw_cells rsegs v' a cs).
      { intros a cs H Ha Hb. apply (rw_cells_agree m1 v' a cs H). intros i Hi. apply CFI. lia. }
      pose proof (CF _ _ AMF1 ltac:(lia) ltac:(cbn; lia)) as AMF'. pose proof (CF _ _ O0 ltac:(lia) ltac:(cbn; lia)) as O0'.
      pose proof (CF _ _ O12 ltac:(lia) ltac:(cbn; lia)) as O12'. pose proof (CF _ _ O32 ltac:(lia) ltac:(cbn; lia)) as O32'.
      pose proof (CF _ _ PC1 ltac:(lia) ltac:(cbn; lia)) as PC1'. pose proof (CF _ _ FR1 ltac:(lia) ltac:(cbn; lia)) as FR'.
      assert (DEP' : exists w8 cs16, cells_size cs16 = 16%nat /\ rw_cells rsegs v' (fp + -2120) [C4 w8] /\ rw_cells rsegs v' (fp + -2112) cs16).
      { destruct (unwind_depth2 top bot fp); destruct DEP as [D8 D16].
        - exists (wz 2), [C8 (wz 0x58c14); C8 ra]. split; [reflexivity|]. split.
          + replace (fp + -2120) with (fp + -2128 + 8) by lia. exact (CF _ _ D8 ltac:(lia) ltac:(cbn; lia)).
          + replace (fp + -2112) with (fp + -2128 + 16) by lia. exact (CF _ _ D16 ltac:(lia) ltac:(cbn; lia)).
        - exists (wz 1), [C8 (wz 0x58c14); CB 8 jb1]. split; [reflexivity|]. split.
          + replace (fp + -2120) with (fp + -2128 + 8) by lia. exact (CF _ _ D8 ltac:(lia) ltac:(cbn; lia)).
          + replace (fp + -2112) with (fp + -2128 + 16) by lia. apply (CF _ _ D16 ltac:(lia)). destruct D16 as [[[_ WFj] _] _]. cbn in WFj |- *. lia. }
      (first [ dex2 DEP' as w8 cs16; dand3 DEP' as S16 D8' D16' | dand5 DEP' as w8 cs16 S16 D8' D16' | destruct DEP' as (w8 & cs16 & S16 & D8' & D16') ]).
      replace (fp + -2128 + 12) with (fp + -2116) in O12' by lia. replace (fp + -2128 + 32) with (fp + -2096) in O32' by lia.
      replace (fp + -2128 + 2056) with (fp + -72) in PC1' by lia.
      (* [comment removed for export] *)
      assert (OWW : forall a, pa_owned A a -> ~ (fp - 8192 <= a < fp) /\ ~ (6193972 <= a < 6193972 + 4)).
      { intros a OW. destruct (asI_owned_where A m md a AI OW) as [ST0|HZ].
        - cbn [cl_static LPA] in ST0. unfold pa_static in ST0. clear -ST0 CE CEIL. lia.
        - unfold heap_zone, in_image in HZ. cbn [cl_image_lo cl_image_hi LPA] in HZ. clear -HZ CEIL. lia. }
      assert (P1 : forall a, 0 <= a < 2^64 -> ~ (fp - 8192 <= a < fp) -> m1 (wz a) = v (wz a)).
      { intros a Ha NW. destruct (Z.eq_dec a (thr + 3168)) as [->|NT]; [exact (shell_unw A m md m1 AI TUNW1 WM1)|].
        apply MU1. rewrite unsigned_lit by lia. unfold off_th_unwinding. cbn [outside app].
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; first [apply NW; clear -X; lia| apply NT; clear -X; lia]. }
      assert (P2 : forall a, (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> 0 <= a < 2^64 -> v (wz a) <> None -> m1 (wz a) <> None).
      { intros a H1 H2. exact (wmono_NN _ _ a WM1 H1 H2). }
      + (* [comment removed for export] *)
        (first [ pose proof ((asI_live_ok A' m' md' r n AI' LS1)) as dR_11; dand5 dR_11 as _ _ APR RCE _ | pose proof (asI_live_ok A' m' md' r n AI' LS1) as (_ & _ & APR & RCE & _) ]).
        assert (RR : 0 < r < 2^64).
        { unfold app_range, app_lo, app_hi, kLowAppEnd, kHighMemBeg in APR. cbn [cl_image_lo cl_image_hi LPA] in APR. clear -APR RCE RNZ CE. lia. }
        pose (Q2 := fun ms2 : machine_state =>
            ms2 = MS (mkR ra (wz fp) gp (cl_tp LPA) t0c t1c t2c s0 s1 (wz r) a1c a2c a3c a4c a5c a6c a7c s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                     F (ret_pc ra) fc None v' (seg_rom rsegs)
            /\ stk rsegs v' (fp - 8192) fp).
        eapply (srz_evt_restrict rsegs (pa_hull A') (asI_hull_segs A' m' md' AI') pa_wx _ (pa_eager A') Q2 _ md' T HMI' HH').
        { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A')) m') with v'.
          pose proof (malloc_epi_ok) as EPI. unfold malloc_epi_stmt in EPI.
          eapply (EPI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc v' fp (fp - 8192) r); clear EPI.
          all: try eassumption. all: try reflexivity. all: try (clear KK; lia).
          intros ST2. apply evt_done. unfold Q2. split; [reflexivity| exact ST2]. }
        intros msr2 md2 HQ2 HI2 SB2 CL2. destruct HQ2 as [-> ST2].
        rewrite unrestrict_MS.
        lazymatch goal with |- context [munrestrict ?Hh (ms_mem (MS ?R ?FF ?pc ?fcx ?rv ?mm ?ro)) ?v2] => change (ms_mem (MS R FF pc fcx rv mm ro)) with mm end.
        cbn [ms_mem] in CL2.
        assert (AG2 : forall a, 0 <= a < 2^64 -> ~ (fp - ASTK <= a < fp) -> a <> p_thr (a_pl A') + 3168 -> ~ (6193972 <= a < 6193972 + 4) -> ~ nowhere a -> v' (wz a) = v' (wz a))
          by (intros; reflexivity).
        assert (SM' : mapped v' (fp - ASTK) ASTK).
        { (first [ dand4 FRK as _ _ F3 _ | destruct FRK as (_ & _ & F3 & _) ]). unfold ASTK. exact F3. }
        pose proof (shell_ainv A' m' md' md2 fp v' nowhere AI' CEIL SM' AG2 ltac:(intros a []) TUNW' (wmono_refl rsegs v') CL2 HI2 SB2) as AI2.
        pose proof (shell_view A' m' v' CL2) as VIEW2.
        replace (ret_pc ra) with ra by (rewrite <- (Z_to_bv_bv_unsigned ra); symmetry; apply ret_pc_even; [lia| clear -RA4; lia]).
        replace (Z_to_bv 64 fp) with sp by (subst fp; symmetry; apply Z_to_bv_bv_unsigned).
        eapply (KK t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c r A' (munrestrict (hidc (pa_hull A')) m' v') md2).
        * exact AI2.
        * cbn [cl_segs LPA]. rewrite VIEW2. exact MI'.
        * eapply (wamd_sbm_l md md1); [exact SB1| exact HH|]. eapply wamd_sbm_r; [exact AMD| exact SB2].
        * exact HLE.
        * exact FFR.
        * exact TCR.
        * OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
        * rewrite VIEW2. cbn [cl_errno LPA] in OWW.
          apply (frame_ok_shell (pa_owned A) (pa_owned A') nowhere (newblk r n) fp 8192 v m1 v' v' FRK (fun a Ha NW _ => P1 a Ha NW) P2).
          -- intros; reflexivity.
          -- intros a _ _ H. exact H.
          -- eapply stk_mapped_pa; [exact ST2| exact CEIL| lia| lia].
          -- exact OWW.
          -- intros a [].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Wrap.
End AWrapM.

   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

(* [comment removed for export] *)
Lemma live_block_CB `{Clg : Ceiling} : forall A m md r n, @pa_ainv _ DepotRepL A m md -> as_live A r = Some n ->
  exists uj, rw_cells rsegs (aview_of (pa_hull A) m) r [CB (Z.to_nat n) uj].
Proof.
  intros A m md r n AI HL. pose proof alloc_ceiling_val as CE.
  (first [ pose proof ((asI_live_ok A m md r n AI HL)) as dR_1; dand7 dR_1 as NR _ APR RCE NI MP _ | pose proof (asI_live_ok A m md r n AI HL) as (NR & _ & APR & RCE & NI & MP & _) ]).
  assert (R0 : 4096 <= r).
  { unfold app_range, app_lo, app_hi, kLowAppEnd, kHighMemBeg in APR. cbn [cl_image_lo cl_image_hi LPA] in APR. lia. }
  (first [ pose proof ((junk_at_of_mapped rsegs _ r n ltac:(lia) ltac:(lia) ltac:(lia) MP)) as dR_2; dex1 dR_2 as bs; destruct dR_2 as [L B] | pose proof ((junk_at_of_mapped rsegs _ r n ltac:(lia) ltac:(lia) ltac:(lia) MP)) as dR_2; dand3 dR_2 as bs L B | destruct (junk_at_of_mapped rsegs _ r n ltac:(lia) ltac:(lia) ltac:(lia) MP) as (bs & L & B) ]).
  exists bs. apply ro_rw.
  - split; [cbn; split; [lia| exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact MP.
Qed.

(* [comment removed for export] *)
Lemma live_not_thr `{Clg : Ceiling} : forall A m md r n a, @pa_ainv _ DepotRepL A m md -> as_live A r = Some n ->
  r <= a < r + n -> ~ (p_thr (a_pl A) <= a < p_thr (a_pl A) + 4096).
Proof.
  intros A m md r n a AI HL Ha Ht. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W.
  (first [ pose proof ((bm_nth_fixed A)) as dR_3; dand6 dR_3 as _ _ _ _ E4 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & E4 & _) ]).
  apply (fixed_bm_no_live_user A 4 (a_thr A) 4096 a W ltac:(lia) E4 ltac:(unfold a_thr; exact Ht)).
  unfold as_live, as_live_ in HL. destruct (a_livemap A !! r) as [li|] eqn:Hl; [|discriminate]. cbn in HL. injection HL as HL.
  first [ hotw_ex2 r li | exists r, li ]. split; [exact Hl| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Wrap.
Context {Clg : Ceiling}.
  Hypothesis UNW : unwind_stmt.
  (* [comment removed for export] *)
  Hypothesis ACORE : alloc_core_cps1.

  #[using="ACORE UNW"] Theorem pa_calloc16_of_core : @pa_calloc_obligation16 _ DepotRepL.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A cnt sz T.
    cbv zeta. intros AI MI Ha0 Ha1 CR SR NRQ NCAP LIM NLV TINY SCRED PCRED TPE SPA RA4 SITE S0C CEIL SM KK.   (* [comment removed for export] *)
    cbn [cl_segs cl_calloc_pc LPA] in MI |- *.
    set (n := cnt * sz) in *.
    pose proof (hit_stk A m sp CEIL SM) as ST. pose proof (hit_sp47 A m md sp AI CEIL SM) as SPH. unfold ASTK in *.
    pose proof alloc_ceiling_val as CE. pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
    (first [ pose proof ((hit_place A m md AI)) as dR_4; dand7 dR_4 as TH1 TH2 THRA CT1 CT2 TOPR BOTR | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & CT1 & CT2 & TOPR & BOTR) ]).
    (first [ pose proof ((hit_sep A m md AI)) as dR_5; dand4 dR_5 as _ _ SEP_tc _ | pose proof (hit_sep A m md AI) as (_ & _ & SEP_tc & _) ]).
    pose proof (hit_TC A m md AI) as TC. pose proof (hit_tsd A m md AI) as [TSD1 TSD2].
    pose proof (hit_INI A m md AI) as CINI. pose proof (hit_CMCS A m md AI) as CMCS. pose proof (hit_CFU A m md AI) as CFU.
    pose proof (hit_TTB A m md AI) as TTB. pose proof (hit_TDT A m md AI) as TDT. pose proof (hit_TUNW A m md AI) as TUNW.
    pose proof (hit_PCo A m md AI) as PCo. unfold poison_consts in PCo.
    (first [ dand13 PCo as _ Cflags _ _ _ _ _ _ _ _ _ Cgps Cps | destruct PCo as (_ & Cflags & _ & _ & _ & _ & _ & _ & _ & _ & _ & Cgps & Cps) ]).
    subst a0 a1 tp. unfold REQ_MAX in NRQ, CR, SR.
    assert (LO : alloc_ceiling <= bv_unsigned sp - 8192 /\ bv_unsigned sp - 8192 <= bv_unsigned sp - 2144 - 224) by lia.
    pose proof (proj1 (Forall_forall _ _) pa_sites_range _ SITE) as RAr. cbv beta in RAr. assert (RA0 : 4096 <= bv_unsigned ra) by lia.
    assert (RANE : bv_unsigned ra <> 0x58e48) by (intros E; apply (pa_pcs_not_sites 0x58e48 ltac:(cbn; tauto)); rewrite <- E; exact SITE).
    assert (VLE : bv_unsigned s0 <= bv_unsigned sp) by lia.
    assert (TPL : bv_unsigned (cl_tp LPA) = 0x5e83d8) by (cbn [cl_tp LPA]; rewrite unsigned_lit by lia; reflexivity).
    destruct (asI_minv A m md AI) as [HMI HH].
    set (fp := bv_unsigned sp) in *. set (thr := p_thr (a_pl A)) in *. set (v := aview_of (pa_hull A) m) in *.
    set (top := p_stk_top (a_pl A)) in *. set (bot := p_stk_bot (a_pl A)) in *.
    (* [comment removed for export] *)
    pose (Q1 := fun ms' : machine_state => exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (pad1 pad2 jb1 jrest js0 : list byte) (m1 : mem),
        ms' = MS (mkR (wz 0x37b78) (wz (fp + -2192)) gp (cl_tp LPA) t0' t1' t2' (wz (cnt * sz)) (wz (fp + -2136))
                     (wz 0xb1d58) (wz (cnt * sz)) (wz 8) (wz (fp + -2136)) (wz 1) (wz 0) a6' a7'
                     (wz 0xb1d58) (wz 1) (wz 1) (wz (fp + -2136)) (wz (fp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (wz alloc_entry) fc None m1 (seg_rom rsegs)
        /\ munch [(fp - 2144 - 224, fp); (thr + off_th_unwinding, thr + off_th_unwinding + 1)] v m1
        /\ wmono rsegs v m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 (fp - 8192) (fp - 2192)
        /\ rw_cells rsegs m1 (fp + -2136) [C8 (wz (fp + -2136 + 16))]
        /\ (if unwind_depth2 top bot fp
            then rw_cells rsegs m1 (fp + -2136 + 8) [C4 (wz 2)] /\ rw_cells rsegs m1 (fp + -2136 + 16) [C8 (wz 0x58e48); C8 ra]
            else rw_cells rsegs m1 (fp + -2136 + 8) [C4 (wz 1)] /\ rw_cells rsegs m1 (fp + -2136 + 16) [C8 (wz 0x58e48); CB 8 jb1])
        /\ rw_cells rsegs m1 (fp + -2136 + 12) [C4 (wz 0)]
        /\ rw_cells rsegs m1 (fp + -2136 + 32) [CB 2024 jrest]
        /\ rw_cells rsegs m1 (fp + -2136 + 2056) [C8 (wz fp)]
        /\ rw_cells rsegs m1 (fp + -72) [CB 8 pad1]
        /\ rw_cells rsegs m1 (fp + -2144) [CB 8 pad2]
        /\ rw_cells rsegs m1 (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)]
        /\ rw_cells rsegs m1 (fp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ rw_cells rsegs m1 (fp + -2192) [CB 8 js0; C8 (wz 0x58e48); C8 (wz cnt); C8 (wz sz); C8 sp; C8 (wz 0x58eb8)]).
    eapply (srz_evt_restrict rsegs (pa_hull A) (asI_hull_segs A m md AI) pa_wx _ (pa_eager A) Q1 _ md T HMI HH).
    { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A)) m) with v.
      amz. (* [comment removed for export] *)
      pose proof (calloc_pro_ok UNW) as PRO. unfold calloc_pro_stmt in PRO.
      eapply (PRO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ cnt sz pa_tsd (p_ctx (a_pl A)) thr top bot (fp - 8192)); clear PRO.
      all: try eassumption. all: try reflexivity. all: try (clear KK; lia).
      intros t0' t1' t2' a6' a7' t3' t4' t5' t6' pad1 pad2 jb1 jrest js0 m1 O0 DEP O12 O32 PC1 P1c P2c TUNW1 FR1 C48 MU1 WM1 MI1 ST1.
      apply evt_done. unfold Q1. first [ hotw_ex15 t0' t1' t2' a6' a7' t3' t4' t5' t6' pad1 pad2 jb1 jrest js0 m1 | exists t0', t1', t2', a6', a7', t3', t4', t5', t6', pad1, pad2, jb1, jrest, js0, m1 ].
      split; [reflexivity|].
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption. }
    intros msr1 md1 HQ1 HI1 SB1 CL1.
    (first [ dex15 HQ1 as t0' t1' t2' a6' a7' t3' t4' t5' t6' pad1 pad2 jb1 jrest js0 m1; dand15 HQ1 as -> MU1 WM1 MI1 ST1 O0 DEP O12 O32 PC1 P1c P2c TUNW1 FR1 C48 | dand30 HQ1 as t0' t1' t2' a6' a7' t3' t4' t5' t6' pad1 pad2 jb1 jrest js0 m1 -> MU1 WM1 MI1 ST1 O0 DEP O12 O32 PC1 P1c P2c TUNW1 FR1 C48 | destruct HQ1 as (t0' & t1' & t2' & a6' & a7' & t3' & t4' & t5' & t6' & pad1 & pad2 & jb1 & jrest & js0 & m1 & -> & MU1 & WM1 & MI1 & ST1
                     & O0 & DEP & O12 & O32 & PC1 & P1c & P2c & TUNW1 & FR1 & C48) ]).
    rewrite unrestrict_MS. cbn [ms_mem] in CL1.
    lazymatch goal with |- context [munrestrict ?Hh (ms_mem (MS ?R ?FF ?pc ?fcx ?rv ?mm ?ro)) ?v2] => change (ms_mem (MS R FF pc fcx rv mm ro)) with mm end.
    assert (AG1 : forall a, 0 <= a < 2^64 -> ~ (fp - ASTK <= a < fp) -> a <> thr + 3168 -> ~ (cl_errno LPA <= a < cl_errno LPA + 4) -> ~ nowhere a -> m1 (wz a) = v (wz a)).
    { intros a Ha NW NT NE _. unfold ASTK in NW. apply MU1. rewrite unsigned_lit by lia. unfold off_th_unwinding. cbn [outside app].
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; first [apply NW; clear -X; lia| apply NT; clear -X; lia]. }
    pose proof (shell_ainv A m md md1 fp m1 nowhere AI CEIL SM AG1 ltac:(intros a []) TUNW1 WM1 CL1 HI1 SB1) as AI1.
    pose proof (shell_view A m m1 CL1) as VIEW1.
    set (m1r := munrestrict (hidc (pa_hull A)) m m1) in *.
    set (KEY := wkey 0x58e48 top bot fp ra).
    (* [comment removed for export] *)
    pose proof ACORE as AC. unfold alloc_core_cps1 in AC.
    eapply (AC (wz 0x37b78) (wz (fp + -2192)) gp (cl_tp LPA) t0' t1' t2' (wz (cnt * sz)) (wz (fp + -2136)) a6' a7' (wz 0xb1d58) (wz 1) (wz 1) (wz (fp + -2136)) (wz (fp + -89))
               s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m1r md1 A n 0 (fp + -2136) (fp - 8192) fp KEY T); clear AC.
    - (* [comment removed for export] *)
      unfold alloc_core_pre. rewrite VIEW1. cbn [cl_segs LPA].
      rewrite !unsigned_lit by lia.
      assert (KL : Z.of_nat (length KEY) = (if unwind_depth2 top bot fp then 2 else 1)) by (unfold KEY, wkey; destruct (unwind_depth2 top bot fp); reflexivity).
      split; [exact AI1|]. split; [exact MI1|]. split; [unfold REQ_MAX; lia|]. split; [exact NCAP|]. split; [exact LIM|]. split; [exact NLV|].
      split; [exact TINY|]. split; [exact SCRED|]. split; [exact PCRED|]. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [clear -SPH; lia|].
      split; [clear -SPA; Z.div_mod_to_equations; lia|]. split; [reflexivity|].
      split; [exact ST1|].
      split. { eapply (mapped_mono _ m1); [eapply (ALogic2.mapped_sub _ _ _ _ _ SM); lia|].
               intros i Hi Hv. apply (wmono_NN _ _ _ WM1); [clear -Hi CE CEIL; lia| clear -Hi SPR CE CEIL; lia| exact Hv]. }
      split; [lia|]. split; [lia|].
      split. { rewrite KL. destruct (unwind_depth2 top bot fp); destruct DEP as [D8 D16].
               all: split; [exact (conj I (conj I I))|]; cbn [cells_bytes cbytes app]; rewrite app_nil_r.
               all: apply bytes_at_app; split; [destruct O0 as [[_ B] _]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B; exact B|].
               all: rewrite length_le8; replace (fp + -2136 + Z.of_nat 8) with (fp + -2136 + 8) by lia.
               1: exact (proj2 (ro_C44_C8 m1 (fp + -2136 + 8) 2 eq_refl D8 ltac:(replace (fp + -2136 + 8 + 4) with (fp + -2136 + 12) by lia; exact O12))).
               exact (proj2 (ro_C44_C8 m1 (fp + -2136 + 8) 1 eq_refl D8 ltac:(replace (fp + -2136 + 8 + 4) with (fp + -2136 + 12) by lia; exact O12))). }
      split. { unfold KEY, wkey. destruct (unwind_depth2 top bot fp); destruct DEP as [D8 D16]; destruct D16 as [[_ B] _]; cbn [cells_bytes cbytes app map u64s] in B |- *.
               - rewrite app_nil_r in B. rewrite Z_to_bv_bv_unsigned. exact B.
               - apply bytes_at_app in B. destruct B as [B _]. rewrite app_nil_r. exact B. }
      split. { unfold KEY, wkey. (first [ pose proof ((place_extra A m md AI)) as dR_8; dand6 dR_8 as _ _ _ _ SK _ | destruct (place_extra A m md AI) as (_ & _ & _ & _ & SK & _) ]).
               destruct (SK 0x58e48 (bv_unsigned ra) ltac:(cbn; tauto) SITE) as [K2 K1]. destruct (unwind_depth2 top bot fp); [exact K2| exact K1]. }
      apply wkey_range. lia.
    - (* [comment removed for export] *)
      unfold alloc_core_K1v. cbv zeta. rewrite VIEW1.
      intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c r A' m' md' AI' MI' AMD HLE FFR PLE IAE VG RNZ LN0 LS1 LQ LB TCR LN LS LP CZ PRIM FRK ERRK CFI STK'.
      cbn [cl_segs cl_errno LPA] in MI', FRK, ERRK, CFI, STK' |- *.
      set (v' := aview_of (pa_hull A') m') in *.
      replace (ret_pc (wz 0x37b78)) with (wz 0x37b78 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite !unsigned_lit in CFI, STK' by lia. replace (fp - (fp - 8192)) with 8192 in FRK by lia.
      destruct (asI_minv A' m' md' AI') as [HMI' HH'].
      (first [ pose proof ((hit_place A' m' md' AI')) as dR_9; dand3 dR_9 as TH1' TH2' _ | pose proof (hit_place A' m' md' AI') as (TH1' & TH2' & _) ]). pose proof (aobj_facts _ _ TH1') as THF'.
      pose proof (hit_TUNW A' m' md' AI') as TUNW'. fold v' in TUNW'. unfold off_th_unwinding in TUNW'.
      (* [comment removed for export] *)
      assert (CF : forall a cs, rw_cells rsegs m1 a cs -> fp - 2192 <= a -> a + Z.of_nat (cells_size cs) <= fp -> rw_cells rsegs v' a cs).
      { intros a cs H Ha Hb. apply (rw_cells_agree m1 v' a cs H). intros i Hi. apply CFI. lia. }
      pose proof (CF _ _ C48 ltac:(lia) ltac:(cbn; lia)) as C48'. pose proof (CF _ _ O0 ltac:(lia) ltac:(cbn; lia)) as O0'.
      pose proof (CF _ _ O12 ltac:(lia) ltac:(cbn; lia)) as O12'. pose proof (CF _ _ O32 ltac:(lia) ltac:(cbn; lia)) as O32'.
      pose proof (CF _ _ PC1 ltac:(lia) ltac:(cbn; lia)) as PC1'. pose proof (CF _ _ FR1 ltac:(lia) ltac:(cbn; lia)) as FR'.
      pose proof (CF _ _ P1c ltac:(lia) ltac:(cbn; destruct P1c as [[[? _] _] _]; cbn in *; lia)) as P1'.
      pose proof (CF _ _ P2c ltac:(lia) ltac:(cbn; destruct P2c as [[[? _] _] _]; cbn in *; lia)) as P2'.
      assert (DEP' : exists w8 cs16, cells_size cs16 = 16%nat /\ rw_cells rsegs v' (fp + -2128) [C4 w8] /\ rw_cells rsegs v' (fp + -2120) cs16).
      { destruct (unwind_depth2 top bot fp); destruct DEP as [D8 D16].
        - exists (wz 2), [C8 (wz 0x58e48); C8 ra]. split; [reflexivity|]. split.
          + replace (fp + -2128) with (fp + -2136 + 8) by lia. exact (CF _ _ D8 ltac:(lia) ltac:(cbn; lia)).
          + replace (fp + -2120) with (fp + -2136 + 16) by lia. exact (CF _ _ D16 ltac:(lia) ltac:(cbn; lia)).
        - exists (wz 1), [C8 (wz 0x58e48); CB 8 jb1]. split; [reflexivity|]. split.
          + replace (fp + -2128) with (fp + -2136 + 8) by lia. exact (CF _ _ D8 ltac:(lia) ltac:(cbn; lia)).
          + replace (fp + -2120) with (fp + -2136 + 16) by lia. apply (CF _ _ D16 ltac:(lia)). destruct D16 as [[[_ WFj] _] _]. cbn in WFj |- *. lia. }
      (first [ dex2 DEP' as w8 cs16; dand3 DEP' as S16 D8' D16' | dand5 DEP' as w8 cs16 S16 D8' D16' | destruct DEP' as (w8 & cs16 & S16 & D8' & D16') ]).
      replace (fp + -2136 + 12) with (fp + -2124) in O12' by lia. replace (fp + -2136 + 32) with (fp + -2104) in O32' by lia.
      replace (fp + -2136 + 2056) with (fp + -80) in PC1' by lia.
      (* [comment removed for export] *)
      assert (OWW : forall a, pa_owned A a -> ~ (fp - 8192 <= a < fp) /\ ~ (6193972 <= a < 6193972 + 4)).
      { intros a OW. destruct (asI_owned_where A m md a AI OW) as [ST0|HZ].
        - cbn [cl_static LPA] in ST0. unfold pa_static in ST0. clear -ST0 CE CEIL. lia.
        - unfold heap_zone, in_image in HZ. cbn [cl_image_lo cl_image_hi LPA] in HZ. clear -HZ CEIL. lia. }
      assert (P1 : forall a, 0 <= a < 2^64 -> ~ (fp - 8192 <= a < fp) -> m1 (wz a) = v (wz a)).
      { intros a Ha NW. destruct (Z.eq_dec a (thr + 3168)) as [->|NT]; [exact (shell_unw A m md m1 AI TUNW1 WM1)|].
        apply MU1. rewrite unsigned_lit by lia. unfold off_th_unwinding. cbn [outside app].
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; first [apply NW; clear -X; lia| apply NT; clear -X; lia]. }
      assert (P2 : forall a, (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> 0 <= a < 2^64 -> v (wz a) <> None -> m1 (wz a) <> None).
      { intros a H1 H2. exact (wmono_NN _ _ a WM1 H1 H2). }
      + (* [comment removed for export] *)
        (first [ pose proof ((asI_live_ok A' m' md' r n AI' LS1)) as dR_14; dand5 dR_14 as _ _ APR RCE _ | pose proof (asI_live_ok A' m' md' r n AI' LS1) as (_ & _ & APR & RCE & _) ]).
        assert (RR : 0 < r < 2^64).
        { unfold app_range, app_lo, app_hi, kLowAppEnd, kHighMemBeg in APR. cbn [cl_image_lo cl_image_hi LPA] in APR. clear -APR RCE RNZ CE. lia. }
        pose proof (hit_SBc A' m' md' AI') as SBc'. fold v' in SBc'.
        (first [ pose proof ((sb_facts A' (ai_wf _ _ _ _ _ _ _ AI'))) as dR_15; dand5 dR_15 as _ SBA' HB6' RSB' SCE' | pose proof (sb_facts A' (ai_wf _ _ _ _ _ _ _ AI')) as (_ & SBA' & HB6' & RSB' & SCE') ]).
        assert (SBE : p_sb (a_pl A) = a_sb A') by (unfold a_sb; rewrite PLE; reflexivity).
        rewrite SBE in PRIM. unfold kSpaceSize in PRIM.
        destruct (Z.le_gt_cases n kMaxPrimaryUser) as [NP|NS].
        * (* [comment removed for export] *)
          destruct PRIM as [PR _]. specialize (PR NP).
          destruct (live_block_CB A' m' md' r n AI' LS1) as (uj & UB). fold v' in UB.
          (first [ pose proof ((asI_live_ok A' m' md' r n AI' LS1)) as dR_16; dand8 dR_16 as _ _ _ _ NIr MPr NOWr _ | pose proof (asI_live_ok A' m' md' r n AI' LS1) as (_ & _ & _ & _ & NIr & MPr & NOWr & _) ]). fold v' in MPr.
          pose proof (hit_PCo A' m' md' AI') as PCo'. unfold poison_consts in PCo'.
          (first [ dand12 PCo' as _ _ _ _ _ _ _ _ _ Cgm Crm _ | destruct PCo' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Cgm & Crm & _) ]). fold v' in Cgm, Crm.
          pose (Q2 := fun ms2 : machine_state => exists (t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e : word) (m2 : mem),
              ms2 = MS (mkR ra (wz fp) gp (cl_tp LPA) t0e t1e t2e s0 s1 (wz r) a1e a2e a3e a4e a5e a6e a7e s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3e t4e t5e t6e)
                       F (ret_pc ra) fc None m2 (seg_rom rsegs)
              /\ stk rsegs m2 (fp - 8192) fp /\ mem_inv rsegs m2 /\ munch [(r, r + n)] v' m2 /\ wmono rsegs v' m2
              /\ rw_cells rsegs m2 r [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]).
          eapply (srz_evt_restrict rsegs (pa_hull A') (asI_hull_segs A' m' md' AI') pa_wx _ (pa_eager A') Q2 _ md' T HMI' HH').
          { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A')) m') with v'.
            pose proof (calloc_epiP_ok) as EPI. unfold calloc_epiP_stmt in EPI.
            eapply (EPI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc v' fp (fp - 8192) r (a_sb A') n); clear EPI.
            all: try eassumption. all: try reflexivity. all: try (clear KK; unfold kMaxPrimaryUser, kHighMemBeg, kSpaceSize in *; lia).
            intros t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e m2 ST2 MI2 MU2 WM2 ZB. apply evt_done. unfold Q2.
            first [ hotw_ex15 t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e m2 | exists t0e, t1e, t2e, a1e, a2e, a3e, a4e, a5e, a6e, a7e, t3e, t4e, t5e, t6e, m2 ].
            OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [reflexivity| assumption]. }
          intros msr2 md2 HQ2 HI2 SB2 CL2.
          (first [ dex15 HQ2 as t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e m2; dand6 HQ2 as -> ST2 MI2 MU2 WM2 ZB | dand21 HQ2 as t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e m2 -> ST2 MI2 MU2 WM2 ZB | destruct HQ2 as (t0e & t1e & t2e & a1e & a2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & m2 & -> & ST2 & MI2 & MU2 & WM2 & ZB) ]).
          rewrite unrestrict_MS.
          lazymatch goal with |- context [munrestrict ?Hh (ms_mem (MS ?R ?FF ?pc ?fcx ?rv ?mm ?ro)) ?v2] => change (ms_mem (MS R FF pc fcx rv mm ro)) with mm end.
          assert (AG2 : forall a, 0 <= a < 2^64 -> ~ (fp - ASTK <= a < fp) -> a <> p_thr (a_pl A') + 3168 -> ~ (6193972 <= a < 6193972 + 4) -> ~ (r <= a < r + n) -> m2 (wz a) = v' (wz a)).
          { intros a Ha NW NT NE NB. apply MU2. rewrite unsigned_lit by lia. cbn [outside app]. split; [exact NB| exact I]. }
          assert (XOK : forall a, r <= a < r + n -> ~ pa_owned A' a /\ ~ cl_shared LPA a /\ v' (wz a) <> None).
          { intros a Ha. split; [| split].
            - replace a with (r + (a - r)) by lia. apply NOWr. lia.
            - intros SH. pose proof (asI_shared_where a SH) as W. cbn [cl_rw_lo cl_image_hi LPA] in W.
              unfold in_image in NIr. cbn [cl_image_lo cl_image_hi LPA] in NIr.
              unfold app_range, app_lo, app_hi, kLowAppEnd, kHighMemBeg in APR. cbn [cl_image_lo cl_image_hi LPA] in APR. clear -W NIr APR Ha RCE CE. lia.
            - replace a with (r + (a - r)) by lia. apply MPr. lia. }
          assert (TUNW2 : rw_cells rsegs m2 (p_thr (a_pl A') + 3168) [C1 (Z_to_bv 8 0)]).
          { apply (rw_cells_agree v' m2 _ _ TUNW'). intros i Hi. cbn in Hi. apply MU2. rewrite unsigned_lit by (clear -THF' Hi CE; lia). cbn [outside app].
            split; [| exact I]. intros X. exact (live_not_thr A' m' md' r n _ AI' LS1 X ltac:(clear -Hi; lia)). }
          assert (SM' : mapped v' (fp - ASTK) ASTK).
          { (first [ dand4 FRK as _ _ F3 _ | destruct FRK as (_ & _ & F3 & _) ]). unfold ASTK. exact F3. }
          pose proof (shell_ainv A' m' md' md2 fp m2 (fun a => r <= a < r + n) AI' CEIL SM' AG2 XOK TUNW2 WM2 CL2 HI2 SB2) as AI2.
          pose proof (shell_view A' m' m2 CL2) as VIEW2.
          replace (ret_pc ra) with ra by (rewrite <- (Z_to_bv_bv_unsigned ra); symmetry; apply ret_pc_even; [lia| clear -RA4; lia]).
          replace (Z_to_bv 64 fp) with sp by (subst fp; symmetry; apply Z_to_bv_bv_unsigned).
          eapply (KK t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e r A' (munrestrict (hidc (pa_hull A')) m' m2) md2).
          -- exact AI2.
          -- cbn [cl_segs LPA]. rewrite VIEW2. exact MI2.
          -- eapply (wamd_sbm_l md md1); [exact SB1| exact HH|]. eapply wamd_sbm_r; [exact AMD| exact SB2].
          -- exact HLE.
          -- exact FFR.
          -- exact TCR.
          -- rewrite VIEW2. split; [exact RNZ|]. split; [exact LN0|]. split; [exact LS1|]. split; [exact LQ|]. split.
             { (* [comment removed for export] *) intros i Hi. destruct ZB as [[_ B] (_ & _ & W3)]. cbn [cells_bytes cbytes cells_size csize] in B, W3.
               rewrite app_nil_r in B. rewrite Nat.add_0_r in W3.
               (first [ dand3 B as _ _ B | destruct B as (_ & _ & B) ]). specialize (B (Z.to_nat i) ltac:(rewrite repeat_length; lia)). rewrite Z2Nat.id in B by lia.
               rewrite nth_error_repeat in B by lia. unfold wa in B.
               assert (P : m2 (wz (r + i)) <> None).
               { specialize (W3 i ltac:(lia)). unfold wview, wa in W3. rewrite unsigned_lit in W3 by lia.
                 unfold in_image in NIr. cbn [cl_image_lo cl_image_hi LPA] in NIr.
                 unfold app_range, app_lo, app_hi, kLowAppEnd, kHighMemBeg in APR. cbn [cl_image_lo cl_image_hi LPA] in APR.
                 rewrite (pa_find_segment_none (r + i) 1 ltac:(lia) ltac:(clear -NIr APR Hi RCE CE; lia)) in W3.
                 destruct (m2 (wz (r + i))); [discriminate| exact W3]. }
               exact (mrd_some_eq_ m2 _ _ P B). }
             split; [exact LB|]. split; [exact LN|]. split; [exact LS|]. exact LP.   (* [comment removed for export] *)
          -- rewrite VIEW2. cbn [cl_errno LPA] in OWW.
             apply (frame_ok_shell (pa_owned A) (pa_owned A') nowhere (newblk r n) fp 8192 v m1 v' m2 FRK (fun a Ha NW _ => P1 a Ha NW) P2).
             ++ intros a Ha NW NE NB. apply MU2. rewrite unsigned_lit by lia. cbn [outside app]. split; [| exact I].
                intros X. apply NB. unfold newblk, blk. left. split; [exact RNZ| exact X].
             ++ intros a H1 H2. exact (wmono_NN _ _ a WM2 H1 H2).
             ++ eapply stk_mapped_pa; [exact ST2| exact CEIL| lia| lia].
             ++ exact OWW.
             ++ intros a [].
        * (* [comment removed for export] *)
          destruct PRIM as [_ PR2].
          assert (NPR : r < a_sb A' \/ a_sb A' + 2^37 <= r) by (destruct (Z.lt_ge_cases r (a_sb A')); [left; lia| right]; destruct (Z.le_gt_cases (a_sb A' + 2^37) r); [lia|]; exfalso; unfold kMaxPrimaryUser in *; lia).
          pose (Q2 := fun ms2 : machine_state => exists a1e : word,
              ms2 = MS (mkR ra (wz fp) gp (cl_tp LPA) t0c t1c t2c s0 s1 (wz r) a1e a2c a3c a4c a5c a6c a7c s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                       F (ret_pc ra) fc None v' (seg_rom rsegs)
              /\ stk rsegs v' (fp - 8192) fp).
          eapply (srz_evt_restrict rsegs (pa_hull A') (asI_hull_segs A' m' md' AI') pa_wx _ (pa_eager A') Q2 _ md' T HMI' HH').
          { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A')) m') with v'.
            pose proof (calloc_epiS_ok) as EPI. unfold calloc_epiS_stmt in EPI.
            eapply (EPI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc v' fp (fp - 8192) r (a_sb A')); clear EPI.
            all: try eassumption. all: try reflexivity. all: try (clear KK; unfold kMaxPrimaryUser, kHighMemBeg, kSpaceSize in *; lia).
            intros a1e ST2. apply evt_done. unfold Q2. exists a1e. split; [reflexivity| exact ST2]. }
          intros msr2 md2 HQ2 HI2 SB2 CL2. (first [ dex1 HQ2 as a1e; destruct HQ2 as [-> ST2] | dand3 HQ2 as a1e -> ST2 | destruct HQ2 as (a1e & -> & ST2) ]).
          rewrite unrestrict_MS.
          lazymatch goal with |- context [munrestrict ?Hh (ms_mem (MS ?R ?FF ?pc ?fcx ?rv ?mm ?ro)) ?v2] => change (ms_mem (MS R FF pc fcx rv mm ro)) with mm end.
          cbn [ms_mem] in CL2.
          assert (AG2 : forall a, 0 <= a < 2^64 -> ~ (fp - ASTK <= a < fp) -> a <> p_thr (a_pl A') + 3168 -> ~ (6193972 <= a < 6193972 + 4) -> ~ nowhere a -> v' (wz a) = v' (wz a))
            by (intros; reflexivity).
          assert (SM' : mapped v' (fp - ASTK) ASTK).
          { (first [ dand4 FRK as _ _ F3 _ | destruct FRK as (_ & _ & F3 & _) ]). unfold ASTK. exact F3. }
          pose proof (shell_ainv A' m' md' md2 fp v' nowhere AI' CEIL SM' AG2 ltac:(intros a []) TUNW' (wmono_refl rsegs v') CL2 HI2 SB2) as AI2.
          pose proof (shell_view A' m' v' CL2) as VIEW2.
          replace (ret_pc ra) with ra by (rewrite <- (Z_to_bv_bv_unsigned ra); symmetry; apply ret_pc_even; [lia| clear -RA4; lia]).
          replace (Z_to_bv 64 fp) with sp by (subst fp; symmetry; apply Z_to_bv_bv_unsigned).
          eapply (KK t0c t1c t2c a1e a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c r A' (munrestrict (hidc (pa_hull A')) m' v') md2).
          -- exact AI2.
          -- cbn [cl_segs LPA]. rewrite VIEW2. exact MI'.
          -- eapply (wamd_sbm_l md md1); [exact SB1| exact HH|]. eapply wamd_sbm_r; [exact AMD| exact SB2].
          -- exact HLE.
          -- exact FFR.
          -- exact TCR.
          -- rewrite VIEW2. split; [exact RNZ|]. split; [exact LN0|]. split; [exact LS1|]. split; [exact LQ|]. split.
             { exact (CZ eq_refl NS). }
             split; [exact LB|]. split; [exact LN|]. split; [exact LS|]. exact LP.   (* [comment removed for export] *)
          -- rewrite VIEW2. cbn [cl_errno LPA] in OWW.
             apply (frame_ok_shell (pa_owned A) (pa_owned A') nowhere (newblk r n) fp 8192 v m1 v' v' FRK (fun a Ha NW _ => P1 a Ha NW) P2).
             ++ intros; reflexivity.
             ++ intros a _ _ H. exact H.
             ++ eapply stk_mapped_pa; [exact ST2| exact CEIL| lia| lia].
             ++ exact OWW.
             ++ intros a [].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Wrap.
