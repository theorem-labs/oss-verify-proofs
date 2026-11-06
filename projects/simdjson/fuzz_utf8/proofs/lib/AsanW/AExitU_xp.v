(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac MState Mem Cells Step Frame Arr InitMem ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import ExecF ITreeA Shadow ModelX.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Stdio AsanCtrl AsanEmbed AsanProgDeps AsanHandoff.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import TopLevel AsanMainU.     (* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AImg ABase ABytes RtCells ALayout AMalloc_iface StdioFiles Stdio_kit I_fwrite AIos_iface AExitU_wr
     MonadF ADriver_iface AD_kit AIcptU_hmap AIcptU_fflush AIcptU_defs AIcptU_wdefs ARepInit_kit AD_handoff0 AD_hokit AD_handoff ATsafeMain AMain_asm AMain_closed AMain_closedI.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Keyed Unification.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma icpt_tab_of_at : forall m T, icpt_tab_at m T -> icpt_tab T m.
Proof.
  intros m T (C & B1 & B2 & TLO & THI & TAL). unfold icpt_tab, HMAP, BOFF_ERR, BOFF_OUT.
  apply (proj1 (rw_cells_app asegs m 0x16e540 [C8 (Z_to_bv 64 0x16e548)] [C8 (Z_to_bv 64 T)])) in C. destruct C as [C1 C2].
  cbn [cells_size csize Nat.add] in C2. change (0x16e540 + Z.of_nat 8) with 0x16e548 in C2.
  split; [exact C1|]. split; [exact C2|].
  split. { eapply rw_cells_recast; [exact B1 | unfold hm_bucket0; repeat constructor | reflexivity | reflexivity]. }
  split. { eapply rw_cells_recast; [exact B2 | unfold hm_bucket0; repeat constructor | reflexivity | reflexivity]. }
  unfold AIMG_HI in TLO. split; [exact TLO|]. split; [lia|]. clear - TAL. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma icpt_tab_base_eq : forall m T T', icpt_tab T m -> icpt_tab T' m -> T = T'.
Proof.
  intros m T T' (_ & C & _ & _ & L1 & H1 & _) (_ & C' & _ & _ & L2 & H2 & _). unfold HMAP in *.
  pose proof (rw_cells_read asegs m _ _ 0%nat _ C ltac:(reflexivity)) as R1.
  pose proof (rw_cells_read asegs m _ _ 0%nat _ C' ltac:(reflexivity)) as R2.
  cbn [csize] in R1, R2. rewrite R1 in R2.
  assert (E : le8 (Z_to_bv 64 T) = le8 (Z_to_bv 64 T')) by (clear - R2; cbn [cbytes] in R2; congruence). clear R1 R2.
  apply (f_equal le_bytes_to_word) in E. rewrite !le_bytes_to_word_le8 in E.
  pose proof atop_range as AR. unfold ATOP_MIN, ATOP_MAX in AR.
  apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by (clear - L1 H1 L2 H2 AR; lia). exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition icpt_addr (a : Z) : Prop :=
  (0x167fc8 <= a < 0x167fd0) \/ (0x168000 <= a < 0x168008) \/ (0x16a17c <= a < 0x16a180)       (* [comment removed for export] *)
  \/ (MBST_SH <= a < MBST_SH + 8)                                                              (* [comment removed for export] *)
  \/ (shad ATOP <= a < XSH_HI).                                                                (* [comment removed for export] *)

Lemma icpt_addr_cli : forall (CI : list (Z * Z)) LB SP a, (forall iv, In iv drv_img_ranges -> In iv CI) -> icpt_addr a -> aclient_addr CI LB SP a.
Proof.
  intros CI LB SP a HCI Ha. pose proof atop_range as AR. unfold ATOP_MIN, ATOP_MAX in AR. pose proof ATOP_al16 as A16.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - right; left. exists (0x167fc8, 0x167fd0). split; [apply HCI; unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto] | cbn [fst snd]; lia].
  - right; left. exists (0x168000, 0x168008). split; [apply HCI; unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto] | cbn [fst snd]; lia].
  - right; left. exists (0x16a17c, 0x16a180). split; [apply HCI; unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto] | cbn [fst snd]; lia].
  - right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad]. right; left.
    exists (0x6a1828, 0x6a1e80). split; [apply HCI; unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto] |].
    unfold MBST_SH in Ha. unfold AsanEmbed.ASHOFF. unfold ASHOFF. cbn [fst snd]. lia.
  - right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad]. left.
    rewrite shad_div in Ha. unfold XSH_HI in Ha. unfold AsanEmbed.ASHOFF in *. unfold ASHOFF in *. Z.div_mod_to_equations. lia.
Qed.

Lemma icpt_addr_far : forall a, icpt_addr a -> (a < 0x6c6000 /\ ~ xin_ivs drv_touch a) \/ (0x7fff7000 <= a < 0x10007fff8000).
Proof.
  intros a Ha. pose proof atop_range as AR. unfold ATOP_MIN, ATOP_MAX in AR.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  1-3: (left; split; [lia|]; unfold drv_touch, xin_ivs, ASTAGE, AINIT_FLAG, AU_consts.ANEWH; cbn [fst snd]; lia).
  - right. unfold MBST_SH in Ha. lia.
  - right. rewrite shad_div in Ha. unfold XSH_HI in Ha. unfold AsanEmbed.ASHOFF in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma drv_wr_disjoint : forall W A n, Forall drv_wr_ok W -> 0 <= n -> A + n <= 0x691350 -> (A + n <= 0x16a8e8 \/ 0x16a9d0 <= A) ->
  disjoint_from W A n.
Proof.
  intros W A n HW Hn HA HE. induction HW as [|[l h] W H1 HW IH]; cbn; [exact I|]. split; [| exact IH].
  pose proof atop_range as AR. unfold ATOP_MIN, ATOP_MAX in AR.
  unfold drv_wr_ok, ablk, Shadow.KHIGH, KLS, AIMG_HI, ASTAGE in H1. cbn [fst snd] in H1. lia.
Qed.

(* [comment removed for export] *)
Lemma drv_wr_disjoint_sh : forall W A n, Forall drv_wr_ok W -> KLS <= A -> A + n <= 0x10007fff8000 -> disjoint_from W A n.
Proof.
  intros W A n HW HA HE. induction HW as [|[l h] W H1 HW IH]; cbn; [exact I|]. split; [| exact IH].
  pose proof atop_range as AR. unfold ATOP_MIN, ATOP_MAX in AR.
  unfold drv_wr_ok, ablk, Shadow.KHIGH, KLS, AIMG_HI, ASTAGE in *. cbn [fst snd] in H1. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Laws.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma icpt_tab_reheap : forall (AI : AMallocIface) L RNG st LB RNG0 st0 LB0 m m' T,
    icpt_tab T m -> AHEAP AI L RNG0 st0 LB0 m -> AHEAP AI L RNG st LB m' -> icpt_tab T m'.
  Proof.
    intros AI L RNG st LB RNG0 st0 LB0 m m' T TAB AH0 AH'.
    pose proof (icpt_tab_of_at _ _ (AI_xr AI _ _ _ _ _ AH0)) as TAB0.
    rewrite (icpt_tab_base_eq m _ _ TAB TAB0). exact (icpt_tab_of_at _ _ (AI_xr AI _ _ _ _ _ AH')).
  Qed.

  (* [comment removed for export] *)
  Lemma icpt_rt_of_aheap : forall (AI : AMallocIface) L RNG st LB m',
    AHEAP AI L RNG st LB m' -> rt_inited m' /\ rt_real_fwrite m' /\ rt_real_mem m' /\ rt_got_ric m' /\ rt_shbase m'.
  Proof.
    intros AI L RNG st LB m' AH. pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT. unfold artcells in RT. decompose [and] RT.
    repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.
  Lemma icpt_got_of_aheap : forall (AI : AMallocIface) L RNG st LB m', AHEAP AI L RNG st LB m' ->
    rw_cells asegs m' 0x166150 [C8 (Z_to_bv 64 0x16a17c)] /\ rw_cells asegs m' 0x1660b8 [C8 (Z_to_bv 64 0x16ecf8)] /\ rw_cells asegs m' 0x1660e0 [C8 (Z_to_bv 64 0x168100)].
  Proof.
    intros AI L RNG st LB m' AH.
    repeat match goal with |- _ /\ _ => split end;
      (eapply (relro_C8 AI); [exact AH | unfold ARELRO_LO; lia | unfold ARELRO_HI; lia | vm_compute; reflexivity]).
  Qed.

  Lemma icptW_agree : forall T (AI : AMallocIface) (P : Z -> Prop) L RNG st LB RNG0 st0 LB0 m m',
    magree asegs P m m' -> (forall a, icpt_addr a -> P a) -> AHEAP AI L RNG st LB m' -> mem_inv asegs m' -> icptW T m ->
    AHEAP AI L RNG0 st0 LB0 m -> icptW T m'.
  Proof.
    intros T AI P L RNG st LB RNG0 st0 LB0 m m' AG HP AH' MI' [[RT TAB] WC] AH0.
    destruct (icpt_rt_of_aheap AI _ _ _ _ _ AH') as (R1 & R2 & R3 & R4 & R5).
    destruct (icpt_got_of_aheap AI _ _ _ _ _ AH') as (G1' & G2' & G3').
    split; [split; [| exact (icpt_tab_reheap AI _ _ _ _ _ _ _ _ _ _ TAB AH0 AH')] |].
    - unfold icpt_rt in *. decompose [and] RT.
      repeat match goal with |- _ /\ _ => split end;
        first [ assumption
              | (eapply rw_cells_magree; [exact AG | eassumption | cbn [cells_size csize Nat.add]; intros a Ha; apply HP; unfold icpt_addr; lia]) ].
    - destruct WC as (G1 & SZ & G2 & SB & G3 & MB & XS). unfold icpt_wcr.
      split; [exact G1'|]. split.
      { eapply rw_cells_magree; [exact AG | exact SZ | cbn [cells_size csize Nat.add]; intros a Ha; apply HP; unfold icpt_addr; lia]. }
      split; [exact G2'|]. split; [exact R5|]. split; [exact G3'|]. split.
      { eapply rw_cells_magree; [exact AG | exact MB | cbn [cells_size csize Nat.add]; intros a Ha; apply HP; unfold icpt_addr; lia]. }
      pose proof XS as (X0 & X1 & _). eapply shadow_bytes_agree; [exact XS|]. intros a Ha.
      apply (AG a ltac:(lia)). apply HP. unfold icpt_addr. lia.
  Qed.

  Lemma icptW_frame : forall T (AI : AMallocIface) L RNG st LB RNG0 st0 LB0 W m m',
    icptW T m -> munch W m m' -> wmono asegs m m' -> Forall drv_wr_ok W ->
    AHEAP AI L RNG st LB m' -> AHEAP AI L RNG0 st0 LB0 m -> icptW T m'.
  Proof.
    intros T AI L RNG st LB RNG0 st0 LB0 W m m' [[RT TAB] WC] MU WM HW AH' AH0.
    pose proof atop_range as AR. unfold ATOP_MIN, ATOP_MAX in AR.
    split; [split; [| exact (icpt_tab_reheap AI _ _ _ _ _ _ _ _ _ _ TAB AH0 AH')] |].
    - unfold icpt_rt in *. decompose [and] RT.
      repeat match goal with |- _ /\ _ => split end;
        (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply drv_wr_disjoint; [exact HW | cbn; lia | cbn; lia | cbn; lia]]).
    - destruct WC as (G1 & SZ & G2 & SB & G3 & MB & XS). unfold icpt_wcr, MBST_SH in *.
      repeat match goal with |- _ /\ _ => split end.
      1-5: (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply drv_wr_disjoint; [exact HW | cbn; lia | cbn; lia | cbn; lia]]).
      + eapply rw_cells_transport; [exact MB | exact MU | exact WM | apply drv_wr_disjoint_sh; [exact HW | unfold KLS; cbn; lia | cbn; lia]].
      + eapply shadow_bytes_munch; [exact XS | exact MU |]. apply drv_wr_disjoint_sh; [exact HW | |].
        * rewrite shad_div. unfold AsanEmbed.ASHOFF, KLS. Z.div_mod_to_equations. lia.
        * unfold XSH_HI. lia.
  Qed.

  (* [comment removed for export] *)
  Definition XPi (T : Z) : ExitParams :=
    {| xp_ICPT := icptW T;  xp_ICPTR := icptW_rng T;  xp_SLO := XSLO;  xp_SHI := XSHI;  xp_addr := icpt_addr;
       xp_ICPTR_mono := icptW_rng_mono T;
       xp_agree := icptW_agree T;
       xp_cli := icpt_addr_cli;
       xp_far := icpt_addr_far;
       xp_frame := icptW_frame T;
       xp_frame_exit := icptW_frame_exit T |}.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Init.
    Variable AI : AMallocIface.
    Hypothesis AHEAP_INIT : aheap_init_stmt AI ATsafeMain.A0.       (* [comment removed for export] *)

    Lemma xp_init : xp_init_fam_stmt XPi ATsafeMain.A0.
    Proof.
      intros en inp w V m ms mo VE VI AM HA.
      pose proof (AHEAP_INIT en inp w V m ms mo VE VI AM HA) as AH.
      pose proof (AI_xr AI _ _ _ _ _ AH) as TAT.
      change (4096 * al_V (LDRV V w) 220%nat) with (XT V) in TAT.
      pose proof AM as (_ & _ & PIN & HMF & HPF & _). apply Forall_app in HMF as [HM _]. apply Forall_app in HPF as [HP _].
      assert (HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP).
      { destruct PIN as (_ & _ & _ & USP & _). rewrite USP. exact HA. }
      pose proof atop_range as AR. unfold ATOP_MIN, ATOP_MAX in AR.
      pose proof (fun p => ATsafeMain.A0_init V p) as AL.
      destruct (icpt_rt_of_aheap AI _ _ _ _ _ AH) as (R1 & R2 & R3 & R4 & R5).
      destruct (icpt_got_of_aheap AI _ _ _ _ _ AH) as (G1 & G2 & G3).
      cbn [xp_ICPT xp_ICPTR XPi]. split; [split; [split; [| exact (icpt_tab_of_at _ _ TAT)] |] |].
      - unfold icpt_rt. repeat match goal with |- _ /\ _ => split end; first [assumption | ho_cells V m HM].
      - unfold icpt_wcr, MBST_SH. split; [exact G1|]. split; [ho_cells V m HM|]. split; [exact G2|]. split; [exact R5|]. split; [exact G3|].
        split.
        { (* [comment removed for export] *)
          pose proof (zrun_chunk V m HM _ _ MBST_SH 8 (sh_zero5 V m HM)
                        ltac:(unfold MBST_SH; lia) ltac:(lia) ltac:(unfold MBST_SH; lia) ltac:(unfold MBST_SH; lia) ltac:(unfold MBST_SH; lia)) as Z8.
          unfold MBST_SH in Z8.
          eapply rw_cells_recast; [exact Z8 | repeat constructor | first [reflexivity | apply bytes_eq_of_unsigned; vm_compute; reflexivity] | reflexivity]. }
        (* [comment removed for export] *)
        pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
        mf V m HM (MZeroS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304))
                          (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))) ZW.
        replace XSH_HI with (shad ATOP + (XSH_HI - shad ATOP)) by lia.
        apply shadow_bytes_of_pointwise.
        + intros i Hi. rewrite shad_div in Hi |- *. unfold AsanEmbed.ASHOFF, XSH_HI in Hi |- *.
          match goal with |- m (wa ?a) = _ =>
            replace a with (4096 * V 0%nat + 512 * V 10%nat + 2146402304 + (a - (4096 * V 0%nat + 512 * V 10%nat + 2146402304))) by (clear; lia) end.
          apply ZW. clear - HAT P0 P6 P10 Hi. Z.div_mod_to_equations. lia.
        + rewrite shad_div. unfold AsanEmbed.ASHOFF. Z.div_mod_to_equations. lia.
        + unfold XSH_HI. lia.
      - destruct TAT as (_ & _ & _ & TLO & THI & _). unfold AIMG_HI in TLO.
        unfold icptW_rng, icptU_rng, BOFF_ERR, BOFF_OUT, MBST_SH, RNG0. unfold XT in *.
        split; [split|split].
        1-2: (eapply (vis_rng (m_vm_lazy (MX mo [])) (ATsafeMain.A0 V) V AL 10); [reflexivity | cbn [fst snd zv]; lia | cbn [fst snd zv]; lia | lia | lia]).
        + apply (rng_image_sh (m_vm_lazy (MX mo [])) (ATsafeMain.A0 V) V AL); lia.
        + apply (rng_stackside_sh (m_vm_lazy (MX mo [])) (ATsafeMain.A0 V) V AL HP HAT); [lia | unfold XSH_HI; lia].
    Qed.
  End Init.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma icpt_post_lift : forall T (FILE : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : mem) (Q : mem -> Prop) ms',
    icpt_wcr m -> ATOP <= bv_unsigned sp - 4096 -> (FILE = RSTDOUT \/ FILE = RSTDERR) ->
    icpt_post (icptU T) [(bv_unsigned sp - 4096, bv_unsigned sp); (FILE, FILE + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m Q ms' ->
    icpt_post (icptW T) [(bv_unsigned sp - 4096, bv_unsigned sp); (FILE, FILE + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m Q ms'.
  Proof.
    intros until ms'. intros WC HSP HF PO. unfold icpt_post in *.
    destruct PO as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & MU & WM & MI & ST & SSP & IC & HQ).
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
    repeat match goal with |- _ /\ _ => split end; try assumption.
    split; [exact IC|].
    eapply icpt_wcr_frame_exit; [exact WC | exact MU | exact WM |].
    unfold exit_wr_ok. constructor; [left; cbn [fst snd]; lia|]. constructor; [| constructor]. right; left. cbn [fst snd]. destruct HF as [-> | ->]; lia.
  Qed.

  Section Closed.
    Hypothesis WCR : forall T, wcrtomb0_stmt (icptW T) (icptW_rng T) XSLO XSHI.                 (* [comment removed for export] *)
    Hypothesis FW0 : forall T, fwrite0_out_stmt (icptU T) (icptU_rng T).                        (* [comment removed for export] *)
    Hypothesis FW0E : forall T, fwrite0_err_stmt (icptU T) (icptU_rng T).                       (* [comment removed for export] *)
    Hypothesis FFL : forall T (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St),
      (forall s so, get_so (set_so so s) = so) -> (forall s so so', set_so so' (set_so so s) = set_so so' s) -> (forall s, set_so (get_so s) s = s) ->
      fflush_out_stmt (icptU T) (icptU_rng T) get_so set_so.                                    (* [comment removed for export] *)
    Hypothesis FFLE : forall T, fflush_err_stmt (icptU T) (icptU_rng T).                        (* [comment removed for export] *)

    Lemma FW0_W : forall T, fwrite0_out_stmt (icptW T) (icptW_rng T).
    Proof.
      intros T. unfold fwrite0_out_stmt. intros until so_x. intros ST SOF SSP [IC WC] MI E1 E2 E3 ETP LO GLO ATL AL RSTK RIMG [RX _].
      eapply evtF_mono; [eapply (FW0 T); eassumption|]. cbv beta. intros ms' PO.
      apply (icpt_post_lift T RSTDOUT); [exact WC | lia | left; reflexivity | exact PO].
    Qed.
    Lemma FW0E_W : forall T, fwrite0_err_stmt (icptW T) (icptW_rng T).
    Proof.
      intros T. unfold fwrite0_err_stmt. intros until guard. intros ST SEF SSP [IC WC] MI E1 E2 E3 ETP LO GLO ATL AL RSTK RIMG [RX _].
      eapply evtF_mono; [eapply (FW0E T); eassumption|]. cbv beta. intros ms' PO.
      apply (icpt_post_lift T RSTDERR); [exact WC | lia | right; reflexivity | exact PO].
    Qed.
    Lemma FFLE_W : forall T, fflush_err_stmt (icptW T) (icptW_rng T).
    Proof.
      intros T. unfold fflush_err_stmt. intros until guard. intros ST SEF SSP [IC WC] MI E1 ETP LO GLO ATL AL RSTK RIMG [RX _].
      eapply evtF_mono; [eapply (FFLE T); eassumption|]. cbv beta. intros ms' PO.
      apply (icpt_post_lift T RSTDERR); [exact WC | lia | right; reflexivity | exact PO].
    Qed.
    Lemma FFL_W : forall T (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St),
      (forall s so, get_so (set_so so s) = so) -> (forall s so so', set_so so' (set_so so s) = set_so so' s) -> (forall s, set_so (get_so s) s = s) ->
      fflush_out_stmt (icptW T) (icptW_rng T) get_so set_so.
    Proof.
      intros T St get_so set_so GS SS SG. unfold fflush_out_stmt. intros until so_x.
      intros ST SOF EB EQ SF SL SSP [IC WC] MI E1 ETP LO GLO ATL AL RSTK RIMG [RX _] RG0 SP47.
      eapply implAM_mono; [eapply (FFL T St get_so set_so GS SS SG); eassumption|]. cbv beta.
      intros [] st' ms' (so' & E' & EB' & PO). exists so'. split; [exact E'|]. split; [exact EB'|].
      apply (icpt_post_lift T RSTDOUT); [exact WC | lia | left; reflexivity | exact PO].
    Qed.

    Lemma xp_chains : forall T, @xp_chains_stmt rc (XPi T).
    Proof.
      intros T. unfold xp_chains_stmt. cbn [xp_ICPT xp_ICPTR xp_SLO xp_SHI XPi].
      split; [exact (WCR T)|]. split; [exact (FW0_W T)|]. split; [exact (FW0E_W T)|].
      split. { apply (FFL_W T APS aps_so aset_so); [intros s so; reflexivity | intros s so so'; reflexivity | intros s; destruct s; reflexivity]. }
      split. { apply (FFL_W T stdout_st (fun so => so) (fun so _ => so)); [intros s so; reflexivity | intros s so so'; reflexivity | intros s; reflexivity]. }
      split; [exact (FFLE_W T)|]. unfold XSLO, XSHI. split; lia.
    Qed.

    Theorem xp_closed : forall (AI : AMallocIface), aheap_init_stmt AI ATsafeMain.A0 -> xp_closed_stmt XPi.
    Proof. intros AI AHI. split; [exact xp_chains | exact (xp_init AI AHI)]. Qed.
  End Closed.
End Laws.
End CANSEC1.
