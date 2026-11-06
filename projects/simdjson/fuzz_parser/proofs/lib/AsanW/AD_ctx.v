(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AU_kit AU_iface AHarnessU_iface F_syscalls StdioFiles Stdio_kit Stdio_iface F_printf_iface MonadF AExit F_module_dtor_pre ADriver_iface AD_kit AU_fuzz_kit AAtexit_iface AIos_iface AExitU2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Set Keyed Unification.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {XP : ExitParams}.
Lemma implMA_of_implAM : forall {A} RNG (c : @Monad.M APS A) (s : APS) (Q : A -> APS -> machine_state -> Prop) ms,
  implAM RNG c s Q ms -> implMA RNG c s (fun a s' RNG' ms' => RNG' = RNG /\ Q a s' ms') ms.
Proof. intros A RNG c s Q ms H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CTX.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  (* [comment removed for export] *)
  Variables (usp : Z) (TID : Z).
  (* [comment removed for export] *)
  Variables (S0 S1 S2 S3 S4 S5 S6 S7 : word) (J8 : list byte).

  Definition ALO : Z := usp - 8388608 + 4096.

  Definition AMFRAME (mm : amem) : Prop :=
    rw_cells asegs mm (usp + -128) [CB 8 J8; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 (Z_to_bv 64 ASTAGE2_RET)].

  (* [comment removed for export] *)
  Definition ASTATc (mm : amem) : Prop :=
       rw_cells asegs mm 0x642dc8 [C4 (Z_to_bv 64 TID)]
    /\ rw_cells asegs mm 0x6630e0 [C4 (Z_to_bv 64 0)]
    /\ (exists cdt thr sec tm1, rw_cells asegs mm 0x663100 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
    /\ rw_cells asegs mm 0x10d314 [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs mm 0x1a19a0 [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs mm 0x103a88 [C8 (Z_to_bv 64 0x96608); C8 (Z_to_bv 64 0x43cfc)]
    /\ rw_cells asegs mm 0x10c490 [C1 (Z_to_bv 8 0)]
    /\ (exists dso, rw_cells asegs mm 0x1090c0 [C8 dso])
    /\ rw_cells asegs mm 0x663568 [C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs mm 0x10bc88 [C8 (Z_to_bv 64 RSTDIN)]
    /\ rw_cells asegs mm RSTDIN stdin_cells
    /\ rw_cells asegs mm 0x10bb98 [C8 (Z_to_bv 64 RSTDOUT)]
    /\ rw_cells asegs mm 0x10baa8 [C8 (Z_to_bv 64 RSTDERR)]
    /\ rw_cells asegs mm 0x10d310 [C4 (Z_to_bv 64 1)]
    /\ mdtor_stat mm.
  Definition ASTAT (tbl : list (Z * Z)) (mm : amem) : Prop := ASTATc mm /\ ios_cells mm /\ xp_ICPT mm /\ ATXS tbl mm.   (* [comment removed for export] *)

  Definition astatc_app (a : Z) : Prop :=
    (0x642dc8 <= a < 0x642dc8 + 4) \/ (0x6630e0 <= a < 0x6630e0 + 4) \/ (0x663100 <= a < 0x663100 + 8) \/ (0x10d314 <= a < 0x10d314 + 1) \/ (0x1a19a0 <= a < 0x1a19a0 + 1) \/ (0x103a88 <= a < 0x103a88 + 16) \/ (0x10c490 <= a < 0x10c490 + 1) \/ (0x1090c0 <= a < 0x1090c0 + 8) \/ (0x663568 <= a < 0x663568 + 8) \/ (0x10bc88 <= a < 0x10bc88 + 8) \/ (RSTDIN <= a < RSTDIN + 144) \/ (0x10bb98 <= a < 0x10bb98 + 8) \/ (0x10baa8 <= a < 0x10baa8 + 8) \/ (0x10d310 <= a < 0x10d310 + 4).
  Definition astat_app (a : Z) : Prop := astatc_app a \/ (0x662ec0 <= a < 0x6630e0) \/ (0x642154 <= a < 0x642155).
  Definition astat_addr (a : Z) : Prop := astat_app a \/ mdtor_stat_app a \/ mdtor_stat_sh a.
  (* [comment removed for export] *)
  Definition ios_addr (a : Z) : Prop := False.   (* [comment removed for export] *)

  Lemma ASTATc_agree : forall (P : Z -> Prop) m m', magree asegs P m m' -> (forall a, astatc_app a \/ mdtor_stat_app a \/ mdtor_stat_sh a -> P a) -> ASTATc m -> ASTATc m'.
  Proof.
    intros P m m' AG HP ST. unfold ASTATc in *.
    Ltac tr1 AG HP := eapply rw_cells_magree; [exact AG | eassumption | intros a Ha; apply HP; left; unfold astatc_app; cbn in Ha; unfold RSTDIN in Ha |- *; lia].
    decompose [and ex] ST.
    repeat match goal with
           | |- _ /\ _ => split
           | |- exists _, _ => eexists
           end.
    all: first [ tr1 AG HP
               | eapply mdtor_stat_magree; [exact AG | intros a Ha; apply HP; right; exact Ha | eassumption] ].
  Qed.

  (* [comment removed for export] *)
  Lemma ios_cells_agreeH : forall (P : Z -> Prop) L RNG st LB m m', magree asegs P m m' -> (forall a, ios_addr a -> P a) ->
    AHEAP AI L RNG st LB m' -> ios_cells m -> ios_cells m'.
  Proof. intros; exact I. Qed.

  (* [comment removed for export] *)
  Lemma ASTAT_agreeH : forall (P : Z -> Prop) tbl L RNG st LB RNG0 st0 LB0 m m', magree asegs P m m' ->
    (forall a, astat_addr a \/ ios_addr a \/ xp_addr a -> P a) -> AHEAP AI L RNG st LB m' -> mem_inv asegs m' -> ASTAT tbl m ->
    AHEAP AI L RNG0 st0 LB0 m -> ASTAT tbl m'.
  Proof.
    intros P tbl L RNG st LB RNG0 st0 LB0 m m' AG HP AH MI (A & B & C & D) AH0. split; [| split; [| split]].
    - eapply ASTATc_agree; [exact AG | intros a Ha; apply HP; left; unfold astat_addr, astat_app; destruct Ha as [Ha|Ha]; [left; left; exact Ha| right; exact Ha] | exact A].
    - eapply ios_cells_agreeH; [exact AG | intros a Ha; apply HP; right; left; exact Ha | exact AH | exact B].
    - eapply (xp_agree AI); [exact AG | intros a Ha; apply HP; right; right; exact Ha | exact AH | exact MI | exact C | exact AH0].
    - eapply ATXS_magree; [exact D | exact AG | intros a Ha; apply HP; left; unfold astat_addr, astat_app; left; right; unfold atxs_addr, aincb_addr in Ha; lia].
  Qed.

  (* [comment removed for export] *)
  Definition astring (mm : amem) (P : Z) (s : list Z) (slack : list byte) (r : region) : Prop :=
    bytes_at asegs mm P (zb s ++ Z_to_bv 8 0 :: slack)
    /\ Forall (fun c => 0 < c < 256) s
    /\ ((- (P + zlength s + 1)) mod 8 <= zlength slack)
    /\ (zlength s <= 131071)
    /\ usp + 24 <= P
    /\ rclean mm r /\ inreg r P (zlength s + 1 + zlength slack) /\ usp + -128 <= r_rlo r.

  Lemma astring_facts : forall m P s slack r, astring m P s slack r ->
    usp + 24 <= P /\ P + zlength s + 1 + zlength slack <= r_hi r /\ r_lo r <= P /\ usp + -128 <= r_rlo r /\ r_rlo r <= r_lo r
    /\ r_hi r <= r_rhi r /\ r_rhi r <= 2^47 /\ 0 <= zlength slack /\ 0 <= zlength s <= 131071.
  Proof.
    intros m P s slack r (BY & HF & SL & LEN & LO & RC & IR & RLO).
    pose proof (rclean_shclean _ _ RC) as (_ & HUL & _ & _). unfold hull64, KEND in HUL. unfold inreg in IR.
    unfold zlength in *. repeat split; lia.
  Qed.

  Lemma astring_magree : forall (P0 : Z -> Prop) m m' P s slack r,
    magree asegs P0 m m' ->
    (forall a, usp + -128 <= a < 2^47 -> P0 a) -> (forall a, shad (usp + -128) <= a < shad (2^47) -> P0 a) ->
    astring m P s slack r -> astring m' P s slack r.
  Proof.
    intros P0 m m' P s slack r AG H1 H2 AS. pose proof (astring_facts _ _ _ _ _ AS) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
    destruct AS as (BY & HF & SL & LEN & LO & RC & IR & RLO).
    unfold astring. repeat match goal with |- _ /\ _ => split end; try assumption.
    - eapply bytes_at_magree; [exact AG | exact BY |]. intros a Ha. rewrite length_app, zb_length in Ha. cbn [length] in Ha. apply H1. unfold zlength in *. lia.
    - eapply rclean_magree; [exact AG | | exact RC]. intros a Ha. apply H2.
      pose proof (shad_mono (usp + -128) (r_rlo r) ltac:(lia)). pose proof (shad_mono (r_rhi r) (2^47) ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Variable RSTK : region.
  Hypothesis RSTK_lo : r_lo RSTK <= ALO.
  Hypothesis RSTK_hi : usp + -112 <= r_hi RSTK.   (* [comment removed for export] *)
  Hypothesis RSTK_rlo : ATOP <= r_rlo RSTK.
  (* [comment removed for export] *)
  Hypothesis USP16 : usp mod 16 = 0.
  Hypothesis USPLO : ATOP + 8388608 <= usp.
  Hypothesis USPHI : usp + 24 <= 2^47.
  (* [comment removed for export] *)
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.
  Hypothesis URI_CI : forall iv, In iv uri_img_ranges -> In iv CI.
  Variable canary : word.
  (* [comment removed for export] *)
  Hypothesis XSLO : xp_SLO <= ALO.
  Hypothesis XSHI : usp <= xp_SHI.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ABASE (so : stdout_st) (mm : amem) : Prop :=
    stk asegs mm ALO (usp + -128) /\ mem_inv asegs mm /\ AMFRAME mm /\ ASTAT TBL_MAIN mm
    /\ stderr_wfile0 mm /\ rw_cells asegs mm ssp_guard [C8 canary]
    /\ atrun_cells0 mm /\ harness_inv0 mm /\ rodata_sh0 mm /\ rclean mm RSTK /\ rclean mm RBstdout
    /\ rclean mm RSTG                                                      (* [comment removed for export] *)
    /\ (exists errv, rw_cells asegs mm (errno_addr (Z_to_bv 64 ATP)) [C4 errv])
    /\ stdout_file mm so.

  Lemma geo : ATOP <= ALO /\ ALO + 8388608 - 4096 = usp /\ KHIGH <= ALO /\ usp + 24 <= 2^47 /\ usp mod 16 = 0.
  Proof. unfold ALO, KHIGH in *. repeat split; lia. Qed.

  Lemma errno_addr_ATP : errno_addr (Z_to_bv 64 ATP) = 0x642dcc.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Section AfterCallee.
    Variables (LB : list ablock) (m m' : amem).
    Hypothesis HP : aheap_pres CI LB (usp + -128) m m'.
    Hypothesis HS : astk_shadow_pres (usp + -128) m m'.
    Hypothesis HLB : forall b, In b LB -> 0x665000 <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP.

    Let AG : magree asegs (dcli CI LB (usp + -128)) m m' := magree_of_dpost _ _ _ _ _ HP HS.

    Lemma ci_drv : forall lo' hi' a, In (lo', hi') drv_img_ranges -> lo' <= a < hi' -> dcli CI LB (usp + -128) a.
    Proof. intros lo' hi' a Hin Ha. left. right; left. exists (lo', hi'). split; [apply DRV_CI; exact Hin| cbn; lia]. Qed.
    Lemma ci_drv_sh : forall lo' hi' a, In (lo', hi') drv_img_ranges -> shad lo' <= a < shad hi' -> lo' mod 8 = 0 -> hi' mod 8 = 0 -> dcli CI LB (usp + -128) a.
    Proof.
      intros lo' hi' a Hin Ha M1 M2. left. right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
      right; left. exists (lo', hi'). split; [apply DRV_CI; exact Hin|]. cbn. rewrite !shad_div in Ha. unfold ASHOFF in *. Z.div_mod_to_equations. lia.
    Qed.
    Lemma ci_drv_sh' : forall lo' hi' a, In (lo', hi') drv_img_ranges -> shad lo' <= a <= shad (hi' - 1) -> lo' mod 8 = 0 -> dcli CI LB (usp + -128) a.
    Proof.
      intros lo' hi' a Hin Ha M1. left. right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
      right; left. exists (lo', hi'). split; [apply DRV_CI; exact Hin|]. cbn. rewrite !shad_div in Ha. unfold ASHOFF in *. Z.div_mod_to_equations. lia.
    Qed.
    Lemma ci_uri_sh : forall lo' hi' a, In (lo', hi') uri_img_ranges -> shad lo' <= a <= shad (hi' - 1) -> lo' mod 8 = 0 -> dcli CI LB (usp + -128) a.
    Proof.
      intros lo' hi' a Hin Ha M1. left. right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
      right; left. exists (lo', hi'). split; [apply URI_CI; exact Hin|]. cbn. rewrite !shad_div in Ha. unfold ASHOFF in *. Z.div_mod_to_equations. lia.
    Qed.
    Lemma stack_dcli : forall a, usp + -128 <= a < 2^47 -> dcli CI LB (usp + -128) a.
    Proof. intros a Ha. left. left. lia. Qed.
    Lemma stack_sh_dcli : forall RLO RHI a, ATOP <= RLO -> RHI <= KEND -> shad RLO <= a < shad RHI -> dcli CI LB (usp + -128) a.
    Proof.
      intros RLO RHI a H1 H2 Ha. destruct (Z.lt_ge_cases a (shad (usp + -128))) as [LT|GE].
      - right. pose proof (shad_mono ATOP RLO H1). lia.
      - left. right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad]. left.
        rewrite !shad_div in *. unfold ASHOFF, KEND in *. Z.div_mod_to_equations. lia.
    Qed.

    (* [comment removed for export] *)
    Ltac tryr lo hi := exists (lo, hi); split; [ | cbn; lia ]; apply DRV_CI; unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto].
    Lemma astat_dcli : forall a, astat_addr a \/ ios_addr a \/ xp_addr a -> dcli CI LB (usp + -128) a.
    Proof.
      Ltac trysh ci lo hi := apply (ci lo hi); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto] | rewrite !shad_div; unfold ASHOFF; lia | reflexivity].
      Ltac tryall :=
           first [ tryr 0x662ec0 0x6630e0
                 | tryr 0x10000 0x22ec0
                 | tryr 0x642150 0x642338
                 | tryr constr:(RSTDERR) constr:(RSTDERR + 232)
                 | tryr constr:(RSTDOUT) constr:(RSTDOUT + 232)
                 | tryr 0x10baa8 0x10bab0
                 | tryr 0x10bb98 0x10bba0
                 | tryr 0x10bc88 0x10bc90
                 | tryr 0x663560 0x663980
                 | tryr 0x642dc8 0x642dd0
                 | tryr 0x662eb0 0x662eb8
                 | tryr 0x662ec0 0x662ee8
                 | tryr 0x662fe0 0x662fe8
                 | tryr 0x6630e0 0x6630e8
                 | tryr 0x663100 0x663110
                 | tryr 0x10bcc0 0x10c448
                 | tryr 0x10c490 0x10c491
                 | tryr 0x1090c0 0x1090c8
                 | tryr 0x1a19a0 0x1a19a1
                 | tryr 0x10d310 0x10d314
                 | tryr 0x10d3b0 0x10d3b8
                 | tryr 0x103000 0x103e80
                 | tryr 0x22ec0 0x283c0
                 | tryr 0x2ac80 0x2afe0
                 | tryr 0x103e80 0x104000
                 | tryr 0x642180 0x642320
                 | tryr 0x10bba0 0x10bc30
                 | tryr 0x6a14a8 0x6a1b00
                 | tryr 0x6a1f60 0x6a1f68
                 | tryr 0x6a20f0 0x6a2108
                 | tryr 0x642e40 0x642e48
                 | tryr 0x10d314 0x10d315
                 | tryr 0x103a88 0x103a98
                 | tryr 0x109140 0x109148
                 | tryr 0x109170 0x109178
                 | tryr 0x10b2bc 0x10b2c0
                 | tryr 0x632140 0x642180 ].
      intros a [Ha|[Ha|Ha]].
      - destruct Ha as [Ha|[Ha|Ha]].
        + unfold astat_app, astatc_app, RSTDIN in Ha. left. right; left.
          repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end; tryall.
        + unfold mdtor_stat_app in Ha. left. right; left.
          repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end; tryall.
        + unfold mdtor_stat_sh in Ha.
          repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end;
           first [ trysh ci_drv_sh' 0x103e80 0x104000
                 | trysh ci_drv_sh' 0x10bcc0 0x10c448
                 | trysh ci_drv_sh' 0x22ec0 0x283c0
                 | trysh ci_drv_sh' 0x2ac80 0x2afe0
                 | trysh ci_drv_sh' 0x642180 0x642320 ].
      - unfold ios_addr in Ha. destruct Ha.
      - left. eapply xp_cli; [exact DRV_CI| exact Ha].
    Qed.

    Lemma ASTAT_dpost : forall tbl L RNG st LB' RNG0 st0 LB0, AHEAP AI L RNG st LB' m' -> mem_inv asegs m' -> ASTAT tbl m -> AHEAP AI L RNG0 st0 LB0 m -> ASTAT tbl m'.
    Proof. intros tbl L RNG st LB' RNG0 st0 LB0 AH' MI' AS AH0. eapply ASTAT_agreeH; [exact AG | exact astat_dcli | exact AH' | exact MI' | exact AS | exact AH0]. Qed.

    (* [comment removed for export] *)
    Lemma harness_inv0_dpost : forall L RNG st LB', AHEAP AI L RNG st LB' m' -> mem_inv asegs m' -> harness_inv0 m -> harness_inv0 m'.
    Proof.
      intros L RNG st LB' AH' MI' [[IG SH] CS0]. split; [split|].
      - eapply (client_img_pres AI URI_CI); [exact IG | exact HP | exact AH' | exact MI'].
      - eapply (client_sh_pres AI URI_CI); [exact HP | exact SH].
      - intros s LB0 HN. pose proof (client_static_pres AI URI_CI s LB _ m m' HP (CS0 s LB HN)) as X. exact X.
    Qed.

    Lemma ABASE_after_dpost : forall L RNG st LB' RNG0 st0 LB0 so, AHEAP AI L RNG st LB' m' -> mem_inv asegs m' -> stk asegs m' ALO (usp + -128) ->
      ABASE so m -> AHEAP AI L RNG0 st0 LB0 m -> ABASE so m'.
    Proof.
      intros L RNG st LB' RNG0 st0 LB0 so AH' MI' ST' (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & [errv ERR] & SOF) AH0.
      pose proof geo as (G1 & G2 & G3 & G4 & G5). pose proof RSTK_rlo as RSC. atop_facts. unfold KHIGH in G3.
      split; [exact ST'|]. split; [exact MI'|].
      split. { unfold AMFRAME in *. eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply stack_dcli; cbn in Ha; lia]. }
      split. { eapply ASTAT_dpost; [exact AH'| exact MI'| exact AS| exact AH0]. }
      split. { destruct SE as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
               eapply rw_cells_magree; [exact AG| exact Hc|]. intros a Ha. apply (ci_drv RSTDERR (RSTDERR + 232)); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| cbn in Ha; lia]. }
      split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. apply (ci_drv 0x662eb0 0x662eb8); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| unfold ssp_guard in Ha; cbn in Ha; lia]. }
      split. { destruct TR as [PI [nh NH]]. split; [| exists nh];
                 (eapply rw_cells_magree; [exact AG| eassumption| intros a Ha; apply (ci_drv 0x642150 0x642338); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| unfold AINIT_FLAG, ANEWH in Ha; cbn in Ha; lia]]). }
      split. { eapply harness_inv0_dpost; [exact AH'| exact MI'| exact HI]. }
      split. { eapply rodata_sh0_magree; [exact AG| | exact ROD]. intros a Ha. apply (ci_drv_sh 0x10000 0x22ec0); [left; reflexivity| exact Ha| reflexivity| reflexivity]. }
      split. { eapply rclean_magree; [exact AG| | exact RCS]. intros a Ha. destruct RCS as [(_ & HL64 & _) _]. unfold hull64 in HL64.
               apply (stack_sh_dcli (r_rlo RSTK) (r_rhi RSTK)); [atop_facts; lia| lia| exact Ha]. }
      split. { eapply rclean_magree; [exact AG| | exact RCB]. intros a Ha. unfold RBstdout in Ha. cbn [r_rlo r_rhi] in Ha.
               apply (ci_drv_sh 0x663560 0x663980); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| | reflexivity| reflexivity].
               rewrite !shad_div in *. unfold ASHOFF in *. lia. }
      split. { eapply rclean_magree; [exact AG| | exact RSG]. intros a Ha. unfold RSTG in Ha. cbn [r_rlo r_rhi] in Ha.
               apply (ci_drv_sh 0x632140 0x642180); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| | reflexivity| reflexivity].
               rewrite !shad_div in *. unfold ASHOFF in *. lia. }
      split. { exists errv. eapply rw_cells_magree; [exact AG| exact ERR|]. intros a' Ha'. rewrite errno_addr_ATP in Ha'. cbn in Ha'.
               apply (ci_drv 0x642dc8 0x642dd0); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| lia]. }
      eapply stdout_file_magree; [exact AG| | exact SOF]. intros a [Ha|Ha].
      - apply (ci_drv RSTDOUT (RSTDOUT + 232)); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| exact Ha].
      - apply (ci_drv 0x663560 0x663980); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| cbn in Ha |- *; lia].
    Qed.

    (* [comment removed for export] *)
    Lemma astring_after_dpost : forall P str slack r, astring m P str slack r -> astring m' P str slack r.
    Proof.
      intros P str slack r AS. eapply astring_magree; [exact AG| | | exact AS].
      - intros a Ha. apply stack_dcli. lia.
      - intros a Ha. pose proof geo as (G1 & _). apply (stack_sh_dcli (usp + -128) (2^47)); [atop_facts; lia| unfold KEND; lia| exact Ha].
    Qed.
  End AfterCallee.

  (* [comment removed for export] *)
  Definition WOKb (hi : Z) (iv : Z * Z) : Prop :=
    (ALO <= fst iv /\ snd iv <= hi)
    \/ (fst iv = 0x642dcc /\ snd iv = 0x642dd0)                                   (* [comment removed for export] *)
    \/ (fst iv = RSTDERR /\ snd iv = RSTDERR + 232)                               (* [comment removed for export] *)
    \/ ablk (fst iv) (snd iv)                                                     (* [comment removed for export] *)
    \/ (ASTAGE <= fst iv /\ snd iv <= ASTAGE + 65536).                           (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition WOK : Z * Z -> Prop := WOKb (usp + -128).

  (* [comment removed for export] *)
  Lemma WOKb_outside : forall hi W a, ALO <= hi -> Forall (WOKb hi) W ->
    (hi <= a
     \/ (a < 0x665000 /\ ~ (0x642dcc <= a < 0x642dd0) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x632150 <= a < 0x642150))
     \/ (0x7fff7000 <= a < 0x10007fff8000)) -> outside W a.
  Proof.
    pose proof geo as (G1 & G2 & G3 & _). unfold KHIGH in *. atop_facts.
    intros hi. induction W as [|[lo1 hi1] W IH]; intros a Hhi HW Ha; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    unfold WOKb, ablk, ASTAGE, AIMG_HI, KLS in H1. cbn [fst snd] in H1. lia.
  Qed.
  Lemma WOK_outside : forall W a, Forall WOK W ->
    (usp + -128 <= a
     \/ (a < 0x665000 /\ ~ (0x642dcc <= a < 0x642dd0) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x632150 <= a < 0x642150))
     \/ (0x7fff7000 <= a < 0x10007fff8000)) -> outside W a.
  Proof. intros W a HW Ha. pose proof geo as (_ & G2 & _). eapply WOKb_outside; [| exact HW| exact Ha]. lia. Qed.

  Lemma WOKb_appW : forall hi W, hi <= usp + 24 -> Forall (WOKb hi) W -> appW W.
  Proof.
    pose proof geo as (G1 & G2 & G3 & _). unfold KHIGH in G3. atop_facts. intros hi W Hhi.
    induction W as [|[lo1 hi1] W IH]; intros HW; [apply Forall_nil|]. inversion HW as [|x l H1 H2]; subst.
    constructor; [| apply IH; exact H2]. unfold WOKb, ablk, ASTAGE, AIMG_HI, KLS, KHIGH in H1. cbn [fst snd] in H1 |- *. unfold KLOW, KHIGH. lia.
  Qed.
  Lemma WOK_appW : forall W, Forall WOK W -> appW W.
  Proof. intros W HW. eapply WOKb_appW; [| exact HW]. lia. Qed.

  (* [comment removed for export] *)
  Lemma WOKb_drv_wr_ok : forall hi W, Forall (WOKb hi) W -> Forall drv_wr_ok W.
  Proof.
    pose proof geo as (G1 & G2 & G3 & _). intros hi W HW. eapply Forall_impl; [| exact HW]. intros iv H. unfold WOKb, drv_wr_ok in *.
    destruct H as [H|[H|[H|[H|H]]]]; [left; lia| right; left; exact H| right; right; left; exact H| right; right; right; left; exact H| right; right; right; right; exact H].
  Qed.
  Lemma ASTAT_munch : forall tbl L RNG st LB RNG0 st0 LB0 hi W m m', ALO <= hi <= usp + 24 -> Forall (WOKb hi) W -> munch W m m' -> wmono asegs m m' -> ASTAT tbl m ->
    AHEAP AI L RNG st LB m' -> AHEAP AI L RNG0 st0 LB0 m -> ASTAT tbl m'.
  Proof.
    intros tbl L RNG st LB RNG0 st0 LB0 hi W m m' Hhi HW MU WM (A & B & C & D) AHN AHO. pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof (magree_of_munch asegs _ _ _ MU WM) as AG. split; [| split; [| split]].
    - eapply ASTATc_agree; [exact AG | | exact A]. intros a Ha. eapply WOKb_outside; [| exact HW |]; [lia|]. right.
      unfold astatc_app, mdtor_stat_app, mdtor_stat_sh, RSTDIN in Ha. unfold ASTAGE in *. lia.
    - exact I.
    - eapply (xp_frame AI); [exact C | exact MU | exact WM | eapply WOKb_drv_wr_ok; exact HW | exact AHN | exact AHO].
    - eapply ATXS_magree; [exact D | exact AG | intros a Ha; eapply WOKb_outside; [| exact HW |]; [lia|]; right; unfold atxs_addr, aincb_addr in Ha; unfold ASTAGE in *; lia].
  Qed.
  Lemma harness_inv0_munch : forall hi W m m', ALO <= hi <= usp + 24 -> Forall (WOKb hi) W -> munch W m m' -> wmono asegs m m' -> harness_inv0 m -> harness_inv0 m'.
  Proof.
    intros hi W m m' Hhi HW MU WM [HI CS0]. pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof (magree_of_munch asegs _ _ _ MU WM) as AG.
    Ltac outw HW := eapply WOKb_outside; [| exact HW |]; [lia|]; right; unfold ASTAGE in *; lia.
    split.
    - eapply harness_invA_magree; [exact AG | | exact HI]. intros a Ha. outw HW.
    - intros s LB0 HN. specialize (CS0 s LB0 HN). destruct CS0 as [CL CS]. split; [exact CL|].
      unfold client_static0, client_static1, AACTIVE, AACTIVE_GUARD, AFALLBACK, AFALLBACK_GUARD, fallback_cells, guard0, guard1 in *.
      destruct CS as [CS|CS]; [left| right]; decompose [and] CS; repeat match goal with |- _ /\ _ => split end;
        (eapply rw_cells_magree; [exact AG | eassumption | intros a Ha; cbn in Ha; outw HW]).
  Qed.
  (* [comment removed for export] *)
  Lemma ASTAT_after_adrv : forall tbl tbl' L RNG st LB LB' RNG0 st0 LB0 m m', adrv_pres AI LB (usp + -128) m m' -> AHEAP AI L RNG st LB' m' -> mem_inv asegs m' -> ASTAT tbl m ->
    ATXS tbl' m' -> AHEAP AI L RNG0 st0 LB0 m -> ASTAT tbl' m'.
  Proof.
    intros tbl tbl' L RNG st LB LB' RNG0 st0 LB0 m m' HPR AH MI (A & B & C & _) TX AH0.
    assert (AG : magree asegs (fun a => dcli CI LB (usp + -128) a /\ ~ rin_ivs atrun_ivs a) m m') by (intros a Ha [Hc Hn]; exact (HPR a Ha Hc Hn)).
    split; [| split; [| split; [| exact TX]]].
    - eapply ASTATc_agree; [exact AG | | exact A]. intros a Ha. split.
      + apply astat_dcli. left. unfold astat_addr, astat_app. destruct Ha as [Ha|Ha]; [left; left; exact Ha| right; exact Ha].
      + unfold astatc_app, mdtor_stat_app, mdtor_stat_sh, RSTDIN in Ha. unfold atrun_ivs, rin_ivs, AINIT_FLAG, ANEWH. cbn [fst snd]. lia.
    - eapply ios_cells_agreeH; [exact AG | intros a Ha; unfold ios_addr in Ha; destruct Ha | exact AH | exact B].
    - eapply (xp_agree AI); [exact AG | | exact AH | exact MI | exact C | exact AH0]. intros a Ha. split; [apply astat_dcli; right; right; exact Ha|].
      pose proof (xp_far a Ha) as XF. unfold drv_touch, xin_ivs, ASTAGE, AINIT_FLAG, ANEWH in XF. cbn [fst snd] in XF.
      unfold atrun_ivs, rin_ivs, AINIT_FLAG, ANEWH. cbn [fst snd]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ABASE_of_parts : forall L RNG st LB RNG0 st0 LB0 hi W m m' so, ALO <= hi <= usp + 24 -> Forall (WOKb hi) W -> munch W m m' -> wmono asegs m m' ->
    ASTAT TBL_MAIN m -> rw_cells asegs m ssp_guard [C8 canary] -> atrun_cells0 m -> harness_inv0 m -> rodata_sh0 m ->
    rclean m RSTK -> rclean m RBstdout -> rclean m RSTG -> stdout_file m so ->
    stk asegs m' ALO (usp + -128) -> mem_inv asegs m' -> AMFRAME m' -> stderr_wfile0 m' ->
    (exists errv, rw_cells asegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
    AHEAP AI L RNG st LB m' -> AHEAP AI L RNG0 st0 LB0 m ->
    ABASE so m'.
  Proof.
    intros L RNG st LB RNG0 st0 LB0 hi W m m' so Hhi HW MU WM AS GU TR HI ROD RCS RCB RSG SOF ST' MI' FR' SE' ERR' AHN AHO.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof (magree_of_munch asegs _ _ _ MU WM) as AG. pose proof (WOKb_appW hi W ltac:(lia) HW) as AW.
    assert (OUT : forall a, (hi <= a \/ (a < 0x665000 /\ ~ (0x642dcc <= a < 0x642dd0) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x632150 <= a < 0x642150))
                             \/ (0x7fff7000 <= a < 0x10007fff8000)) ->
                            (fun x => outside W x) a) by (intros a Ha; eapply WOKb_outside; [| eassumption| exact Ha]; lia).
    split; [exact ST'|]. split; [exact MI'|]. split; [exact FR'|].
    split. { eapply (ASTAT_munch _ L RNG st LB RNG0 st0 LB0 hi); [lia| exact HW| exact MU| exact WM| exact AS| exact AHN| exact AHO]. }
    split; [exact SE'|].
    split. { eapply rw_cells_magree; [exact AG| exact GU| intros a Ha; apply OUT; unfold ssp_guard in Ha; cbn in Ha; lia]. }
    split. { destruct TR as [PI [nh NH]]. split; [| exists nh]; (eapply rw_cells_magree; [exact AG| eassumption| intros a Ha; apply OUT; unfold AINIT_FLAG, ANEWH in Ha; cbn in Ha; lia]). }
    split. { eapply (harness_inv0_munch hi); [lia| exact HW| exact MU| exact WM| exact HI]. }
    split; [eapply rodata_sh0_frame; [exact ROD| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCS| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCB| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RSG| exact MU| exact WM| exact AW]|]. split; [exact ERR'|].
    eapply stdout_file_magree; [exact AG| | exact SOF]. intros a Ha. apply OUT. cbn in Ha. lia.
  Qed.

  Lemma ABASE_munch : forall L RNG st LB RNG0 st0 LB0 W m m' so, ABASE so m -> Forall WOK W -> munch W m m' -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' ALO (usp + -128) -> stderr_wfile0 m' ->
    (exists errv, rw_cells asegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
    AHEAP AI L RNG st LB m' -> AHEAP AI L RNG0 st0 LB0 m ->
    ABASE so m'.
  Proof.
    intros L RNG st LB RNG0 st0 LB0 W m m' so (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & ERR & SOF) HW MU WM MI' ST' SE' ERR' AHN AHO.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    eapply (ABASE_of_parts L RNG st LB RNG0 st0 LB0 (usp + -128)); try eassumption; [lia|].
    unfold AMFRAME in *. eapply rw_cells_magree; [eapply magree_of_munch; [exact MU| exact WM]| exact FR|].
    intros a Ha. apply WOK_outside; [exact HW|]. cbn in Ha. lia.
  Qed.

  Lemma astring_munch : forall hi W m m' P str slack r, ALO <= hi <= usp + 24 -> Forall (WOKb hi) W -> munch W m m' -> wmono asegs m m' ->
    astring m P str slack r -> astring m' P str slack r.
  Proof.
    intros hi W m m' P str slack r Hhi HW MU WM AS. pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof (astring_facts _ _ _ _ _ AS) as (F1 & _).
    destruct AS as (BY & HF & SL & LEN & LO & RC & IR & RLO). pose proof (magree_of_munch asegs _ _ _ MU WM) as AG.
    pose proof (bytes_at_bound _ _ _ _ BY) as B. rewrite length_app, zb_length in B. cbn [length] in B.
    pose proof (rclean_shclean _ _ RC) as (_ & HUL & _). unfold hull64, KEND in HUL. unfold inreg in IR.
    unfold astring. repeat match goal with |- _ /\ _ => split end; try assumption.
    - eapply bytes_at_magree; [exact AG | exact BY |]. intros a Ha. rewrite length_app, zb_length in Ha. cbn [length] in Ha.
      eapply WOKb_outside; [| exact HW|]; unfold zlength, KHIGH in *; lia.
    - eapply rclean_magree; [exact AG | | exact RC]. intros a Ha. eapply WOKb_outside; [| exact HW|]; [lia|]. right; right.
      rewrite !shad_div in Ha. unfold ASHOFF in Ha. unfold KHIGH, KEND in *. atop_facts. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma exit_relro_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m ->
       rw_cells asegs m 0x108080 [C8 (Z_to_bv 64 0x103a98); C8 (Z_to_bv 64 0x103a88)]
    /\ rw_cells asegs m 0x1072d0 [C8 (Z_to_bv 64 0xeed38); C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m 0x107fa8 [C8 (Z_to_bv 64 0x10bcc0); C8 (Z_to_bv 64 0x10c440)]
    /\ rw_cells asegs m 0x107320 [C8 (Z_to_bv 64 0x109248)]
    /\ rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)].
  Proof.
    intros L RNG st LB m AH. unfold got_ssp, ssp_guard.
    Ltac relro_tac AH bs :=
      eapply rw_cells_recast;
      [ apply (rw_cells_image0 asegs _ _ bs);
        [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply (AI_relro AI _ _ _ _ _ AH); rewrite ?length_app, ?length_le8 in Ha; unfold ARELRO_LO, ARELRO_HI; lia
        | vm_compute; reflexivity | lia | rewrite ?length_app, ?length_le8; lia ]
      | cbn; repeat split; exact I | reflexivity | reflexivity ].
    split; [relro_tac AH (le8 (Z_to_bv 64 0x103a98) ++ le8 (Z_to_bv 64 0x103a88))|].
    split; [relro_tac AH (le8 (Z_to_bv 64 0xeed38) ++ le8 (Z_to_bv 64 0))|].
    split; [relro_tac AH (le8 (Z_to_bv 64 0x10bcc0) ++ le8 (Z_to_bv 64 0x10c440))|].
    split; [relro_tac AH (le8 (Z_to_bv 64 0x109248))|].
    relro_tac AH (le8 (Z_to_bv 64 ssp_guard)).
  Qed.

  Lemma mdtor_rt_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rw_cells asegs m 0x10d310 [C4 (Z_to_bv 64 1)] -> mdtor_rt m.
  Proof.
    intros L RNG st LB m AH RG. pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT. unfold artcells in RT. decompose [and] RT.
    destruct (exit_relro_of_aheap _ _ _ _ _ AH) as (_ & _ & _ & X5 & _).
    unfold mdtor_rt. repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma aat_exit_intro : forall (code : Z) (s : APS) L (LB : list ablock) (SP : Z) RNG tbl
      (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : amem),
    stk asegs m ALO SP -> ALO <= SP - 48 - MDTOR_DEPTH -> usp + -128 <= SP <= usp + -48 ->
    ASTAT tbl m -> AHEAP AI L RNG (aps_m s) LB m -> stdout_file m (aps_so s) -> stderr_file m -> rw_cells asegs m ssp_guard [C8 canary] ->
    mem_inv asegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    SP mod 16 = 0 ->
    harness_invA m -> client_static s LB m -> (forall b, In b LB -> exists q A n, b = HB q A n) -> aps_ok L s -> frm0 fc ->
    rclean m RSTK -> rrng RNG RSTK -> HUX L -> rng RNG ALO (al_top L - ALO) -> xp_ICPTR RNG -> In [AFREE_PC] (al_U L) ->
    aat_exit AI code s RNG (MS (mkR ra (Z_to_bv 64 SP) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (Z_to_bv 64 AEXIT_PC) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros ST LOS SPR AS AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0 SP16 HI CS HBO RK FRM RCL RRS HUXL RTOP XR TOPL.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof RSTK_lo as RL. pose proof RSTK_hi as RH. pose proof RSTK_rlo as RRL. pose proof XSLO as XL. pose proof XSHI as XH. unfold ALO in *.
    destruct AS as (ASc & IOS & ICP & ATX). pose proof ASc as (E0 & E1 & (cdt & thr & sec & tm1 & E2) & E3 & E4 & E5 & E6 & (dso & E7) & E8 & E9 & E10 & E11 & E12 & ERG & MS).
    destruct (exit_relro_of_aheap _ _ _ _ _ AH) as (_ & _ & XG & _ & _).
    pose proof (mdtor_rt_of_aheap _ _ _ _ _ AH ERG) as RT.
    pose proof (mdtor_pre_of_stat _ RT XG MS) as MDP.
    destruct CS as [CLN _].
    assert (ARM : aps_cl s = None) by (exact CLN).   (* [comment removed for export] *)
    unfold aat_exit, aat_exitU2. do 33 eexists. exists m, (usp - 8388608 + 4096), TID, cdt, thr, sec, tm1, dso, canary, tbl, L, LB, RSTK.
    split; [reflexivity|]. rewrite !unsigned_lit by lia.
    repeat match goal with |- _ /\ _ => split end;
      first [ assumption | reflexivity | lia | exact ARM | unfold AEXITU2_STACK; lia
            | (eapply rng_sub'; [exact RSTK'| lia])
            | (unfold MDTOR_W; repeat (apply Forall_cons; [cbn [fst snd]|]); [..| apply Forall_nil];
               first [ eapply rng_sub'; [exact RIMG| lia] | eapply rng_sub'; [exact RIMSH| lia] ])
            | idtac ].
  Qed.

  (* [comment removed for export] *)
  Lemma amain_return : forall (code : Z) (s : APS) L (LB : list ablock) RNG tbl
      (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
    AMFRAME m -> stk asegs m ALO (usp + -128) -> ASTAT tbl m -> AHEAP AI L RNG (aps_m s) LB m ->
    stdout_file m (aps_so s) -> stderr_file m -> rw_cells asegs m ssp_guard [C8 canary] -> mem_inv asegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    harness_invA m -> client_static s LB m -> (forall b, In b LB -> exists q A n, b = HB q A n) -> aps_ok L s -> frm0 fc ->
    rclean m RSTK -> rrng RNG RSTK -> HUX L -> rng RNG ALO (al_top L - ALO) -> xp_ICPTR RNG -> In [AFREE_PC] (al_U L) ->
    evtF asegs RNG (aat_exit AI code s RNG)
      (MS (mkR x1 (Z_to_bv 64 (usp + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x955b8) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros FR ST AS AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0 HI CS HBO RK FRM RCL RRS HUXL RTOP XR TOPL.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    unfold AMFRAME, ASTAGE2_RET in FR.
    do 11 zstep. release_frame FR ST (usp + -48). zstep.
    replace (ret_pc (Z_to_bv 64 0xee754)) with (Z_to_bv 64 0xee754) by (symmetry; rpc).
    zstep.
    apply evtF_done. unfold AEXIT_PC.
    eapply aat_exit_intro; first [eassumption | lia | unfold MDTOR_DEPTH; lia
                                 | (pose proof USP16 as U16; clear -U16; Z.div_mod_to_equations; lia)].
  Qed.

  (* [comment removed for export] *)
  Lemma aexit2_tail : forall (s : APS) L (LB : list ablock) RNG tbl
      (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
    stk asegs m ALO (usp + -128) -> ASTAT tbl m -> AHEAP AI L RNG (aps_m s) LB m ->
    stdout_file m (aps_so s) -> stderr_file m -> rw_cells asegs m ssp_guard [C8 canary] -> mem_inv asegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    harness_invA m -> client_static s LB m -> (forall b, In b LB -> exists q A n, b = HB q A n) -> aps_ok L s -> frm0 fc ->
    rclean m RSTK -> rrng RNG RSTK -> HUX L -> rng RNG ALO (al_top L - ALO) -> xp_ICPTR RNG -> In [AFREE_PC] (al_U L) ->
    evtF asegs RNG (aat_exit AI 2 s RNG)
      (MS (mkR x1 (Z_to_bv 64 (usp + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x95644) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros ST AS AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0 HI CS HBO RK FRM RCL RRS HUXL RTOP XR TOPL.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    zstep. zstep.
    apply evtF_done. unfold AEXIT_PC.
    eapply aat_exit_intro; first [eassumption | lia | unfold MDTOR_DEPTH; lia
                                 | (pose proof USP16 as U16; clear -U16; Z.div_mod_to_equations; lia)].
  Qed.
End CTX.
End CANSEC1.
