(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter AsanCtrl AsanEmbed HarnessU ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AU_kit AU_iface AHarnessU_iface F_syscalls StdioFiles Stdio_kit Stdio_iface F_printf_iface MonadF AExit F_module_dtor_pre ADriver_iface AD_kit AU_fuzz_kit AAtexit_iface AIos_iface AExitU2.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
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
Section CTX.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  (* [comment removed for export] *)
  Variables (usp : Z) (TID : Z).
  (* [comment removed for export] *)
  Variables (S0 S1 S2 S3 S4 S5 S6 S7 : word) (J8 : list byte).

  Definition ALO : Z := usp - 8388608 + 4096.

  Definition AMFRAME (mm : amem) : Prop :=
    rw_cells bsegs mm (usp + -128) [CB 8 J8; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 (Z_to_bv 64 ASTAGE2_RET)].

  (* [comment removed for export] *)
  Definition ASTATc (mm : amem) : Prop :=
       rw_cells bsegs mm 0x6afa60 [C4 (Z_to_bv 64 TID)]
    /\ rw_cells bsegs mm 0x6cfd78 [C4 (Z_to_bv 64 0)]
    /\ (exists cdt thr sec tm1, rw_cells bsegs mm 0x6cfd98 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
    /\ rw_cells bsegs mm 0x178894 [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs mm 0x20cf20 [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs mm 0x16bf18 [C8 (Z_to_bv 64 0xb38c8); C8 (Z_to_bv 64 0x59000)]
    /\ rw_cells bsegs mm 0x177a10 [C1 (Z_to_bv 8 0)]
    /\ (exists dso, rw_cells bsegs mm 0x173e60 [C8 dso])
    /\ rw_cells bsegs mm 0x6d0310 [C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs mm 0x176de8 [C8 (Z_to_bv 64 RSTDIN)]
    /\ rw_cells bsegs mm RSTDIN stdin_cells
    /\ rw_cells bsegs mm 0x176ed8 [C8 (Z_to_bv 64 RSTDOUT)]
    /\ rw_cells bsegs mm 0x176cf8 [C8 (Z_to_bv 64 RSTDERR)]
    /\ rw_cells bsegs mm 0x178890 [C4 (Z_to_bv 64 1)]
    /\ mdtor_stat mm.
  Definition ASTAT (mm : amem) : Prop := ASTATc mm /\ ios_cells mm /\ xp_ICPT mm.

  Definition astat_app (a : Z) : Prop :=
    (0x6afa60 <= a < 0x6afa60 + 4) \/ (0x6cfd78 <= a < 0x6cfd78 + 4) \/ (0x6cfd98 <= a < 0x6cfd98 + 8) \/ (0x178894 <= a < 0x178894 + 1) \/ (0x20cf20 <= a < 0x20cf20 + 1) \/ (0x16bf18 <= a < 0x16bf18 + 16) \/ (0x177a10 <= a < 0x177a10 + 1) \/ (0x173e60 <= a < 0x173e60 + 8) \/ (0x6d0310 <= a < 0x6d0310 + 8) \/ (0x176de8 <= a < 0x176de8 + 8) \/ (RSTDIN <= a < RSTDIN + 144) \/ (0x176ed8 <= a < 0x176ed8 + 8) \/ (0x176cf8 <= a < 0x176cf8 + 8) \/ (0x178890 <= a < 0x178890 + 4).
  Definition astat_addr (a : Z) : Prop := astat_app a \/ mdtor_stat_app a \/ mdtor_stat_sh a.
  (* [comment removed for export] *)
  Definition ios_addr (a : Z) : Prop :=
    (0x6adba8 <= a < 0x6ae200) \/ (0x6ae660 <= a < 0x6ae668) \/ (0x6ae7f0 <= a < 0x6ae808) \/ (0x6afad8 <= a < 0x6afae0) \/ (0x178894 <= a < 0x178895) \/ (0x16bf18 <= a < 0x16bf28).

  Lemma ASTATc_agree : forall (P : Z -> Prop) m m', magree bsegs P m m' -> (forall a, astat_addr a -> P a) -> ASTATc m -> ASTATc m'.
  Proof.
    intros P m m' AG HP ST. unfold ASTATc in *.
    Ltac tr1 AG HP := eapply rw_cells_magree; [exact AG | eassumption | intros a Ha; apply HP; left; unfold astat_app; cbn in Ha; unfold RSTDIN in Ha |- *; lia].
    decompose [and ex] ST.
    repeat match goal with
           | |- _ /\ _ => split
           | |- exists _, _ => eexists
           end.
    all: first [ tr1 AG HP
               | eapply mdtor_stat_magree; [exact AG | intros a Ha; apply HP; right; exact Ha | eassumption] ].
  Qed.

  (* [comment removed for export] *)
  Lemma ios_cells_agreeH : forall (P : Z -> Prop) L RNG st LB m m', magree bsegs P m m' -> (forall a, ios_addr a -> P a) ->
    AHEAP AI L RNG st LB m' -> ios_cells m -> ios_cells m'.
  Proof.
    intros P L RNG st LB m m' AG HP AH IOS.
    unfold ios_cells, ios_char_shared, ios_cout, ios_clog, ios_wide_shared, ios_wcout, ios_wclog in *.
    decompose [and] IOS.
    repeat match goal with |- _ /\ _ => split end.
    all: first [ solve [eapply rw_cells_magree; [exact AG | eassumption | intros a Ha; apply HP; unfold ios_addr; cbn in Ha; lia]]
               | solve [eapply (relro_C8 AI); [exact AH | unfold ARELRO_LO; lia | unfold ARELRO_HI; lia | vm_compute; reflexivity]] ].
  Qed.

  (* [comment removed for export] *)
  Lemma ASTAT_agreeH : forall (P : Z -> Prop) L RNG st LB RNG0 st0 LB0 m m', magree bsegs P m m' ->
    (forall a, astat_addr a \/ ios_addr a \/ xp_addr a -> P a) -> AHEAP AI L RNG st LB m' -> mem_inv bsegs m' -> ASTAT m ->
    AHEAP AI L RNG0 st0 LB0 m -> ASTAT m'.
  Proof.
    intros P L RNG st LB RNG0 st0 LB0 m m' AG HP AH MI (A & B & C) AH0. split; [| split].
    - eapply ASTATc_agree; [exact AG | intros a Ha; apply HP; left; exact Ha | exact A].
    - eapply ios_cells_agreeH; [exact AG | intros a Ha; apply HP; right; left; exact Ha | exact AH | exact B].
    - eapply (xp_agree AI); [exact AG | intros a Ha; apply HP; right; right; exact Ha | exact AH | exact MI | exact C | exact AH0].
  Qed.

  (* [comment removed for export] *)
  Definition astring (mm : amem) (P : Z) (s : list Z) (slack : list byte) (r : region) : Prop :=
    bytes_at bsegs mm P (zb s ++ Z_to_bv 8 0 :: slack)
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
    magree bsegs P0 m m' ->
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
    stk bsegs mm ALO (usp + -128) /\ mem_inv bsegs mm /\ AMFRAME mm /\ ASTAT mm
    /\ stderr_wfile0 mm /\ rw_cells bsegs mm ssp_guard [C8 canary]
    /\ atrun_cells0 mm /\ harness_inv0 mm /\ rodata_sh0 mm /\ rclean mm RSTK /\ rclean mm RBstdout
    /\ rclean mm RSTG                                                      (* [comment removed for export] *)
    /\ (exists errv, rw_cells bsegs mm (errno_addr (Z_to_bv 64 ATP)) [C4 errv])
    /\ stdout_file mm so.

  Lemma geo : ATOP <= ALO /\ ALO + 8388608 - 4096 = usp /\ KHIGH <= ALO /\ usp + 24 <= 2^47 /\ usp mod 16 = 0.
  Proof. unfold ALO, KHIGH in *. repeat split; lia. Qed.

  Lemma errno_addr_ATP : errno_addr (Z_to_bv 64 ATP) = 0x6afa64.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Section AfterCallee.
    Variables (LB : list ablock) (m m' : amem).
    Hypothesis HP : aheap_pres CI LB (usp + -128) m m'.
    Hypothesis HS : astk_shadow_pres (usp + -128) m m'.
    Hypothesis HLB : forall b, In b LB -> 0x6d2000 <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP.

    Let AG : magree bsegs (dcli CI LB (usp + -128)) m m' := magree_of_dpost _ _ _ _ _ HP HS.

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
           first [ tryr 0x10000 0x23640
                 | tryr 0x6ad6d0 0x6ad978
                 | tryr constr:(RSTDERR) constr:(RSTDERR + 232)
                 | tryr constr:(RSTDOUT) constr:(RSTDOUT + 232)
                 | tryr 0x176cf8 0x176d00
                 | tryr 0x176ed8 0x176ee0
                 | tryr 0x176de8 0x176df0
                 | tryr 0x6d01f8 0x6d0b40
                 | tryr 0x6afa60 0x6afa68
                 | tryr 0x6cfb48 0x6cfb50
                 | tryr 0x6cfb58 0x6cfb80
                 | tryr 0x6cfc78 0x6cfc80
                 | tryr 0x6cfd78 0x6cfd80
                 | tryr 0x6cfd98 0x6cfda8
                 | tryr 0x176f10 0x1779c8
                 | tryr 0x177a10 0x177a11
                 | tryr 0x173e60 0x173e68
                 | tryr 0x20cf20 0x20cf21
                 | tryr 0x178890 0x178894
                 | tryr 0x178930 0x178938
                 | tryr 0x16b000 0x16c320
                 | tryr 0x23660 0x288e0
                 | tryr 0x2b1a0 0x2b520
                 | tryr 0x16c320 0x16c4a0
                 | tryr 0x1767a0 0x176b60
                 | tryr 0x6ad700 0x6ad960
                 | tryr 0x176d00 0x176d90
                 | tryr 0x6adba8 0x6ae200
                 | tryr 0x6ae660 0x6ae668
                 | tryr 0x6ae7f0 0x6ae808
                 | tryr 0x6afad8 0x6afae0
                 | tryr 0x178894 0x178895
                 | tryr 0x16bf18 0x16bf28
                 | tryr 0x173f20 0x173f28
                 | tryr 0x173f58 0x173f60
                 | tryr 0x1760d4 0x1760d8
                 | tryr 0x69d6c0 0x6ad700 ].
      intros a [Ha|[Ha|Ha]].
      - destruct Ha as [Ha|[Ha|Ha]].
        + unfold astat_app, RSTDIN in Ha. left. right; left.
          repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end; tryall.
        + unfold mdtor_stat_app in Ha. left. right; left.
          repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end; tryall.
        + unfold mdtor_stat_sh in Ha.
          repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end;
           first [ trysh ci_drv_sh' 0x16c320 0x16c4a0
                 | trysh ci_drv_sh' 0x1767a0 0x176b60
                 | trysh ci_drv_sh' 0x176f10 0x1779c8
                 | trysh ci_drv_sh' 0x23660 0x288e0
                 | trysh ci_drv_sh' 0x2b1a0 0x2b520
                 | trysh ci_drv_sh' 0x6ad700 0x6ad960 ].
      - unfold ios_addr in Ha. left. right; left.
        repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end; tryall.
      - left. eapply xp_cli; [exact DRV_CI| exact Ha].
    Qed.

    Lemma ASTAT_dpost : forall L RNG st LB' RNG0 st0 LB0, AHEAP AI L RNG st LB' m' -> mem_inv bsegs m' -> ASTAT m -> AHEAP AI L RNG0 st0 LB0 m -> ASTAT m'.
    Proof. intros L RNG st LB' RNG0 st0 LB0 AH' MI' AS AH0. eapply ASTAT_agreeH; [exact AG | exact astat_dcli | exact AH' | exact MI' | exact AS | exact AH0]. Qed.

    (* [comment removed for export] *)
    Lemma harness_inv0_dpost : forall L RNG st LB', AHEAP AI L RNG st LB' m' -> mem_inv bsegs m' -> harness_inv0 m -> harness_inv0 m'.
    Proof.
      intros L RNG st LB' AH' MI' [[IG SH] CS0]. split; [split|].
      - eapply (client_img_pres AI URI_CI); [exact IG | exact HP | exact AH' | exact MI'].
      - eapply (client_sh_pres AI URI_CI); [exact HP | exact SH].
      - exact (client_static0_pres AI URI_CI LB _ m m' HP CS0).
    Qed.

    Lemma ABASE_after_dpost : forall L RNG st LB' RNG0 st0 LB0 so, AHEAP AI L RNG st LB' m' -> mem_inv bsegs m' -> stk bsegs m' ALO (usp + -128) ->
      ABASE so m -> AHEAP AI L RNG0 st0 LB0 m -> ABASE so m'.
    Proof.
      intros L RNG st LB' RNG0 st0 LB0 so AH' MI' ST' (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & [errv ERR] & SOF) AH0.
      pose proof geo as (G1 & G2 & G3 & G4 & G5). pose proof RSTK_rlo as RSC. atop_facts. unfold KHIGH in G3.
      split; [exact ST'|]. split; [exact MI'|].
      split. { unfold AMFRAME in *. eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply stack_dcli; cbn in Ha; lia]. }
      split. { eapply ASTAT_dpost; [exact AH'| exact MI'| exact AS| exact AH0]. }
      split. { destruct SE as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
               eapply rw_cells_magree; [exact AG| exact Hc|]. intros a Ha. apply (ci_drv RSTDERR (RSTDERR + 232)); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| cbn in Ha; lia]. }
      split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. apply (ci_drv 0x6cfb48 0x6cfb50); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| unfold ssp_guard in Ha; cbn in Ha; lia]. }
      split. { destruct TR as (PI & [nh NH] & ICB). unfold aincb in ICB |- *. split; [| split; [exists nh|]];
                 (eapply rw_cells_magree; [exact AG| eassumption| intros a Ha; apply (ci_drv 0x6ad6d0 0x6ad978); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| unfold AINIT_FLAG, ANEWH in Ha; cbn in Ha; lia]]). }
      split. { eapply harness_inv0_dpost; [exact AH'| exact MI'| exact HI]. }
      split. { eapply rodata_sh0_magree; [exact AG| | exact ROD]. intros a Ha. apply (ci_drv_sh 0x10000 0x23640); [left; reflexivity| exact Ha| reflexivity| reflexivity]. }
      split. { eapply rclean_magree; [exact AG| | exact RCS]. intros a Ha. destruct RCS as [(_ & HL64 & _) _]. unfold hull64 in HL64.
               apply (stack_sh_dcli (r_rlo RSTK) (r_rhi RSTK)); [atop_facts; lia| lia| exact Ha]. }
      split. { eapply rclean_magree; [exact AG| | exact RCB]. intros a Ha. unfold RBstdout in Ha. cbn [r_rlo r_rhi] in Ha.
               apply (ci_drv_sh 0x6d01f8 0x6d0b40); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| | reflexivity| reflexivity].
               rewrite !shad_div in *. unfold ASHOFF in *. lia. }
      split. { eapply rclean_magree; [exact AG| | exact RSG]. intros a Ha. unfold RSTG in Ha. cbn [r_rlo r_rhi] in Ha.
               apply (ci_drv_sh 0x69d6c0 0x6ad700); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| | reflexivity| reflexivity].
               rewrite !shad_div in *. unfold ASHOFF in *. lia. }
      split. { exists errv. eapply rw_cells_magree; [exact AG| exact ERR|]. intros a' Ha'. rewrite errno_addr_ATP in Ha'. cbn in Ha'.
               apply (ci_drv 0x6afa60 0x6afa68); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| lia]. }
      eapply stdout_file_magree; [exact AG| | exact SOF]. intros a [Ha|Ha].
      - apply (ci_drv RSTDOUT (RSTDOUT + 232)); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| exact Ha].
      - apply (ci_drv 0x6d01f8 0x6d0b40); [unfold drv_img_ranges; cbn; first [solve [clear; tauto] | tauto]| cbn in Ha |- *; lia].
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
    \/ (fst iv = 0x6afa64 /\ snd iv = 0x6afa68)                                   (* [comment removed for export] *)
    \/ (fst iv = RSTDERR /\ snd iv = RSTDERR + 232)                               (* [comment removed for export] *)
    \/ ablk (fst iv) (snd iv)                                                     (* [comment removed for export] *)
    \/ (ASTAGE <= fst iv /\ snd iv <= ASTAGE + 65536).                           (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition WOK : Z * Z -> Prop := WOKb (usp + -128).

  (* [comment removed for export] *)
  Lemma WOKb_outside : forall hi W a, ALO <= hi -> Forall (WOKb hi) W ->
    (hi <= a
     \/ (a < 0x6d2000 /\ ~ (0x6afa64 <= a < 0x6afa68) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x69d6d0 <= a < 0x6ad6d0))
     \/ (0x7fff7000 <= a < 0x10007fff8000)) -> outside W a.
  Proof.
    pose proof geo as (G1 & G2 & G3 & _). unfold KHIGH in *. atop_facts.
    intros hi. induction W as [|[lo1 hi1] W IH]; intros a Hhi HW Ha; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    unfold WOKb, ablk, ASTAGE, AIMG_HI, KLS in H1. cbn [fst snd] in H1. lia.
  Qed.
  Lemma WOK_outside : forall W a, Forall WOK W ->
    (usp + -128 <= a
     \/ (a < 0x6d2000 /\ ~ (0x6afa64 <= a < 0x6afa68) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x69d6d0 <= a < 0x6ad6d0))
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
  Lemma ASTAT_munch : forall L RNG st LB RNG0 st0 LB0 hi W m m', ALO <= hi <= usp + 24 -> Forall (WOKb hi) W -> munch W m m' -> wmono bsegs m m' -> ASTAT m ->
    AHEAP AI L RNG st LB m' -> AHEAP AI L RNG0 st0 LB0 m -> ASTAT m'.
  Proof.
    intros L RNG st LB RNG0 st0 LB0 hi W m m' Hhi HW MU WM (A & B & C) AHN AHO. pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG. split; [| split].
    - eapply ASTATc_agree; [exact AG | | exact A]. intros a Ha. eapply WOKb_outside; [| exact HW |]; [lia|]. right.
      unfold astat_addr, astat_app, mdtor_stat_app, mdtor_stat_sh, RSTDIN in Ha. unfold ASTAGE in *. lia.
    - unfold ios_cells, ios_char_shared, ios_cout, ios_clog, ios_wide_shared, ios_wcout, ios_wclog in *.
      decompose [and] B.
      repeat match goal with |- _ /\ _ => split end.
      all: (eapply rw_cells_magree; [exact AG | eassumption | intros a Ha; eapply WOKb_outside; [| exact HW |]; [lia|]; right; cbn in Ha; unfold ASTAGE in *; lia]).
    - eapply (xp_frame AI); [exact C | exact MU | exact WM | eapply WOKb_drv_wr_ok; exact HW | exact AHN | exact AHO].
  Qed.
  Definition exit_tableA (s : APS) (LB : list ablock) (m : amem) : Prop := client_static s LB m \/ (aps_cl s = None /\ client_static0 m).
  Lemma exit_tableA_of_static : forall s LB m, client_static s LB m -> exit_tableA s LB m.
  Proof. intros s LB m H. left. exact H. Qed.
  Lemma exit_tableA_of_static0 : forall s LB m, aps_cl s = None -> client_static0 m -> exit_tableA s LB m.
  Proof. intros s LB m E H. right. split; [exact E| exact H]. Qed.

  Lemma aincb_munchW : forall cb hi W m m', ALO <= hi <= usp + 24 -> Forall (WOKb hi) W -> munch W m m' -> wmono bsegs m m' ->
    aincb cb m -> aincb cb m'.
  Proof.
    intros cb hi W m m' Hhi HW MU WM TX. pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    eapply aincb_munch; [exact MU| exact WM| | exact TX]. intros a Ha. pose proof (aincb_addr_range a Ha). eapply WOKb_outside; [| exact HW|]; [lia|]. right.
    unfold ASTAGE in *. lia.
  Qed.
  Lemma exit_tableA_of_inv0 : forall s LB m, harness_inv0 m -> aps_cl s = None -> exit_tableA s LB m.
  Proof. intros s LB m [_ CS0] E. right. split; [exact E| exact CS0]. Qed.
  Lemma harness_inv0_munch : forall hi W m m', ALO <= hi <= usp + 24 -> Forall (WOKb hi) W -> munch W m m' -> wmono bsegs m m' -> harness_inv0 m -> harness_inv0 m'.
  Proof.
    intros hi W m m' Hhi HW MU WM [HI CS0]. pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG.
    Ltac outw HW := eapply WOKb_outside; [| exact HW |]; [lia|]; right; unfold ASTAGE in *; lia.
    split.
    - eapply harness_invA_magree; [exact AG | | exact HI]. intros a Ha. outw HW.
    - destruct CS0 as (AR & AT & CS). split; [| split].
      + eapply atexit_rt_magree; [exact AR | exact AG |]. intros a Ha. outw HW.
      + eapply ATEXIT_magree; [exact AT | exact AG |]. intros a Ha. outw HW.
      + unfold AVEC, AVEC_GUARD, AFALLBACK, guard0 in *. decompose [and] CS.
        repeat match goal with |- _ /\ _ => split end.
        all: first [ solve [eapply rw_cells_magree; [exact AG | eassumption | intros a Ha; cbn in Ha; outw HW]]
                   | solve [eapply wr_at_magree; [exact AG | eassumption | intros a Ha; rewrite shad_div in Ha; unfold ASHOFF in Ha; outw HW]] ].
  Qed.
  (* [comment removed for export] *)
  Lemma ASTAT_after_adrv : forall L RNG st LB LB' RNG0 st0 LB0 m m', adrv_pres AI LB (usp + -128) m m' -> AHEAP AI L RNG st LB' m' -> mem_inv bsegs m' -> ASTAT m ->
    AHEAP AI L RNG0 st0 LB0 m -> ASTAT m'.
  Proof.
    intros L RNG st LB LB' RNG0 st0 LB0 m m' HPR AH MI AS AH0.
    assert (AG : magree bsegs (fun a => dcli CI LB (usp + -128) a /\ ~ rin_ivs atrun_ivs a) m m') by (intros a Ha [Hc Hn]; exact (HPR a Ha Hc Hn)).
    eapply ASTAT_agreeH; [exact AG | | exact AH | exact MI | exact AS | exact AH0].
    intros a Ha. split; [apply astat_dcli; exact Ha|].
    destruct Ha as [Ha|[Ha|Ha]].
    - unfold astat_addr, astat_app, mdtor_stat_app, mdtor_stat_sh, RSTDIN in Ha. unfold atrun_ivs, rin_ivs, AINIT_FLAG, ANEWH. cbn [fst snd]. lia.
    - unfold ios_addr in Ha. unfold atrun_ivs, rin_ivs, AINIT_FLAG, ANEWH. cbn [fst snd]. lia.
    - pose proof (xp_far a Ha) as XF. unfold drv_touch, xin_ivs, ASTAGE, AINIT_FLAG, ANEWH in XF. cbn [fst snd] in XF.
      unfold atrun_ivs, rin_ivs, AINIT_FLAG, ANEWH. cbn [fst snd]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ABASE_of_parts : forall L RNG st LB RNG0 st0 LB0 hi W m m' so, ALO <= hi <= usp + 24 -> Forall (WOKb hi) W -> munch W m m' -> wmono bsegs m m' ->
    ASTAT m -> rw_cells bsegs m ssp_guard [C8 canary] -> atrun_cells0 m -> harness_inv0 m -> rodata_sh0 m ->
    rclean m RSTK -> rclean m RBstdout -> rclean m RSTG -> stdout_file m so ->
    stk bsegs m' ALO (usp + -128) -> mem_inv bsegs m' -> AMFRAME m' -> stderr_wfile0 m' ->
    (exists errv, rw_cells bsegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
    AHEAP AI L RNG st LB m' -> AHEAP AI L RNG0 st0 LB0 m ->
    ABASE so m'.
  Proof.
    intros L RNG st LB RNG0 st0 LB0 hi W m m' so Hhi HW MU WM AS GU TR HI ROD RCS RCB RSG SOF ST' MI' FR' SE' ERR' AHN AHO.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG. pose proof (WOKb_appW hi W ltac:(lia) HW) as AW.
    assert (OUT : forall a, (hi <= a \/ (a < 0x6d2000 /\ ~ (0x6afa64 <= a < 0x6afa68) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x69d6d0 <= a < 0x6ad6d0))
                             \/ (0x7fff7000 <= a < 0x10007fff8000)) ->
                            (fun x => outside W x) a) by (intros a Ha; eapply WOKb_outside; [| eassumption| exact Ha]; lia).
    split; [exact ST'|]. split; [exact MI'|]. split; [exact FR'|].
    split. { eapply (ASTAT_munch L RNG st LB RNG0 st0 LB0 hi); [lia| exact HW| exact MU| exact WM| exact AS| exact AHN| exact AHO]. }
    split; [exact SE'|].
    split. { eapply rw_cells_magree; [exact AG| exact GU| intros a Ha; apply OUT; unfold ssp_guard in Ha; cbn in Ha; lia]. }
    split. { destruct TR as (PI & [nh NH] & ICB). unfold aincb in ICB |- *. split; [| split; [exists nh|]]; (eapply rw_cells_magree; [exact AG| eassumption| intros a Ha; apply OUT; unfold AINIT_FLAG, ANEWH in Ha; cbn in Ha; lia]). }
    split. { eapply (harness_inv0_munch hi); [lia| exact HW| exact MU| exact WM| exact HI]. }
    split; [eapply rodata_sh0_frame; [exact ROD| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCS| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCB| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RSG| exact MU| exact WM| exact AW]|]. split; [exact ERR'|].
    eapply stdout_file_magree; [exact AG| | exact SOF]. intros a Ha. apply OUT. cbn in Ha. lia.
  Qed.

  Lemma ABASE_munch : forall L RNG st LB RNG0 st0 LB0 W m m' so, ABASE so m -> Forall WOK W -> munch W m m' -> wmono bsegs m m' ->
    mem_inv bsegs m' -> stk bsegs m' ALO (usp + -128) -> stderr_wfile0 m' ->
    (exists errv, rw_cells bsegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
    AHEAP AI L RNG st LB m' -> AHEAP AI L RNG0 st0 LB0 m ->
    ABASE so m'.
  Proof.
    intros L RNG st LB RNG0 st0 LB0 W m m' so (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & ERR & SOF) HW MU WM MI' ST' SE' ERR' AHN AHO.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    eapply (ABASE_of_parts L RNG st LB RNG0 st0 LB0 (usp + -128)); try eassumption; [lia|].
    unfold AMFRAME in *. eapply rw_cells_magree; [eapply magree_of_munch; [exact MU| exact WM]| exact FR|].
    intros a Ha. apply WOK_outside; [exact HW|]. cbn in Ha. lia.
  Qed.

  Lemma astring_munch : forall hi W m m' P str slack r, ALO <= hi <= usp + 24 -> Forall (WOKb hi) W -> munch W m m' -> wmono bsegs m m' ->
    astring m P str slack r -> astring m' P str slack r.
  Proof.
    intros hi W m m' P str slack r Hhi HW MU WM AS. pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof (astring_facts _ _ _ _ _ AS) as (F1 & _).
    destruct AS as (BY & HF & SL & LEN & LO & RC & IR & RLO). pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG.
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
       rw_cells bsegs m 0x172e08 [C8 (Z_to_bv 64 0x16bf28); C8 (Z_to_bv 64 0x16bf18)]
    /\ rw_cells bsegs m 0x171fc8 [C8 (Z_to_bv 64 0x152b80); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m 0x172cb8 [C8 (Z_to_bv 64 0x176f10); C8 (Z_to_bv 64 0x177990)]
    /\ rw_cells bsegs m 0x172018 [C8 (Z_to_bv 64 0x174060)]
    /\ rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)].
  Proof.
    intros L RNG st LB m AH. unfold got_ssp, ssp_guard.
    Ltac relro_tac AH bs :=
      eapply rw_cells_recast;
      [ apply (rw_cells_image0 bsegs _ _ bs);
        [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply (AI_relro AI _ _ _ _ _ AH); rewrite ?length_app, ?length_le8 in Ha; unfold ARELRO_LO, ARELRO_HI; lia
        | vm_compute; reflexivity | lia | rewrite ?length_app, ?length_le8; lia ]
      | cbn; repeat split; exact I | reflexivity | reflexivity ].
    split; [relro_tac AH (le8 (Z_to_bv 64 0x16bf28) ++ le8 (Z_to_bv 64 0x16bf18))|].
    split; [relro_tac AH (le8 (Z_to_bv 64 0x152b80) ++ le8 (Z_to_bv 64 0))|].
    split; [relro_tac AH (le8 (Z_to_bv 64 0x176f10) ++ le8 (Z_to_bv 64 0x177990))|].
    split; [relro_tac AH (le8 (Z_to_bv 64 0x174060))|].
    relro_tac AH (le8 (Z_to_bv 64 ssp_guard)).
  Qed.

  Lemma mdtor_rt_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rw_cells bsegs m 0x178890 [C4 (Z_to_bv 64 1)] -> mdtor_rt m.
  Proof.
    intros L RNG st LB m AH RG. pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT. unfold artcells in RT. decompose [and] RT.
    destruct (exit_relro_of_aheap _ _ _ _ _ AH) as (_ & _ & _ & X5 & _).
    unfold mdtor_rt. repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma aat_exit_intro : forall (code : Z) (s : APS) L (LB : list ablock) (SP : Z) RNG
      (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : amem),
    stk bsegs m ALO SP -> ALO <= SP - 48 - MDTOR_DEPTH -> usp + -128 <= SP <= usp + -48 ->
    ASTAT m -> AHEAP AI L RNG (aps_m s) LB m -> stdout_file m (aps_so s) -> stderr_file m -> rw_cells bsegs m ssp_guard [C8 canary] ->
    mem_inv bsegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    SP mod 16 = 0 ->
    harness_invA m -> exit_tableA s LB m -> (forall b, In b LB -> exists q A n, b = HB q A n) -> aps_ok L s -> frm0 fc ->
    rclean m RSTK -> rrng RNG RSTK -> HUX L -> rng RNG ALO (al_top L - ALO) -> xp_ICPTR RNG -> In [AFREE_PC] (al_U L) ->
    aincb 0 m ->
    aat_exit AI code s RNG (MS (mkR ra (Z_to_bv 64 SP) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (Z_to_bv 64 AEXIT_PC) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST LOS SPR AS AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0 SP16 HI CS HBO RK FRM RCL RRS HUXL RTOP XR TOPL INCB.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof RSTK_lo as RL. pose proof RSTK_hi as RH. pose proof RSTK_rlo as RRL. pose proof XSLO as XL. pose proof XSHI as XH. unfold ALO in *.
    destruct AS as (ASc & IOS & ICP). pose proof ASc as (E0 & E1 & (cdt & thr & sec & tm1 & E2) & E3 & E4 & E5 & E6 & (dso & E7) & E8 & E9 & E10 & E11 & E12 & ERG & MS).
    destruct (exit_relro_of_aheap _ _ _ _ _ AH) as (_ & _ & XG & _ & _).
    pose proof (mdtor_rt_of_aheap _ _ _ _ _ AH ERG) as RT.
    pose proof (mdtor_pre_of_stat _ RT XG MS) as MDP.
    assert (TB : exists tbl, ATEXIT tbl m /\
                 ((aps_cl s = None /\ (tbl = TBL_MAIN \/ tbl = TBL_REG))
                  \/ (exists p V, aps_cl s = Some p /\ tbl = TBL_RUN ADTOR_THUNK AVEC /\ In (HB p V 8) LB
                                  /\ rw_cells bsegs m AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))]
                                  /\ rw_cells bsegs m V [C8 (Z_to_bv 64 AFALLBACK)]))).
    { destruct CS as [CS|[HN CS0]].
      - destruct CS as (ATR & ATX & CSM). exists (client_tbl s). split; [exact ATX|].
        unfold client_tbl in *. destruct (aps_cl s) as [p|]; [| left; split; [reflexivity| right; reflexivity]].
        destruct CSM as (V & HIN & CV & CVEC & _). right. exists p, V. split; [reflexivity|]. split; [reflexivity|]. split; [exact HIN|]. split; [exact CVEC| exact CV].
      - destruct CS0 as (ATR & ATX & _). exists TBL_MAIN. split; [exact ATX|]. left. split; [exact HN| left; reflexivity]. }
    destruct TB as (tbl & ATX & ARM).
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
  Lemma amain_return : forall (code : Z) (s : APS) L (LB : list ablock) RNG
      (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
    AMFRAME m -> stk bsegs m ALO (usp + -128) -> ASTAT m -> AHEAP AI L RNG (aps_m s) LB m ->
    stdout_file m (aps_so s) -> stderr_file m -> rw_cells bsegs m ssp_guard [C8 canary] -> mem_inv bsegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    harness_invA m -> exit_tableA s LB m -> (forall b, In b LB -> exists q A n, b = HB q A n) -> aps_ok L s -> frm0 fc ->
    rclean m RSTK -> rrng RNG RSTK -> HUX L -> rng RNG ALO (al_top L - ALO) -> xp_ICPTR RNG -> In [AFREE_PC] (al_U L) ->
    aincb 0 m ->
    evtF bsegs RNG (aat_exit AI code s RNG)
      (MS (mkR x1 (Z_to_bv 64 (usp + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xafa60) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros FR ST AS AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0 HI CS HBO RK FRM RCL RRS HUXL RTOP XR TOPL INCB.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    unfold AMFRAME, ASTAGE2_RET in FR.
    do 11 zstep. release_frame FR ST (usp + -48). zstep.
    replace (ret_pc (Z_to_bv 64 0x15259c)) with (Z_to_bv 64 0x15259c) by (symmetry; rpc).
    zstep.
    apply evtF_done. unfold AEXIT_PC.
    eapply aat_exit_intro; first [eassumption | lia | unfold MDTOR_DEPTH; lia
                                 | (pose proof USP16 as U16; clear -U16; Z.div_mod_to_equations; lia)].
  Qed.

  (* [comment removed for export] *)
  Lemma aexit2_tail : forall (s : APS) L (LB : list ablock) RNG
      (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
    stk bsegs m ALO (usp + -128) -> ASTAT m -> AHEAP AI L RNG (aps_m s) LB m ->
    stdout_file m (aps_so s) -> stderr_file m -> rw_cells bsegs m ssp_guard [C8 canary] -> mem_inv bsegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    harness_invA m -> exit_tableA s LB m -> (forall b, In b LB -> exists q A n, b = HB q A n) -> aps_ok L s -> frm0 fc ->
    rclean m RSTK -> rrng RNG RSTK -> HUX L -> rng RNG ALO (al_top L - ALO) -> xp_ICPTR RNG -> In [AFREE_PC] (al_U L) ->
    aincb 0 m ->
    evtF bsegs RNG (aat_exit AI 2 s RNG)
      (MS (mkR x1 (Z_to_bv 64 (usp + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xafaec) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST AS AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0 HI CS HBO RK FRM RCL RRS HUXL RTOP XR TOPL INCB.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    zstep. zstep.
    apply evtF_done. unfold AEXIT_PC.
    eapply aat_exit_intro; first [eassumption | lia | unfold MDTOR_DEPTH; lia
                                 | (pose proof USP16 as U16; clear -U16; Z.div_mod_to_equations; lia)].
  Qed.
End CTX.
End CANSEC1.
