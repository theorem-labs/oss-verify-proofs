(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Spec Require Import Prelim STree Monad Stdio Driver Adapter AsanCtrl AsanEmbed ProgA AsanProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AUri_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit Stdio_iface F_printf_iface MonadF AExit F_module_dtor ADriver_iface AD_kit.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CANSEC1. Context {rc : runConstT}.
Lemma implMA_of_implAM : forall {A} RNG (c : @Monad.M APS A) (s : APS) (Q : A -> APS -> machine_state -> Prop) ms,
  implAM RNG c s Q ms -> implMA RNG c s (fun a s' RNG' ms' => RNG' = RNG /\ Q a s' ms') ms.
Proof. intros A RNG c s Q ms H. exact H. Qed.

Section CTX.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (usp : Z) (TID : Z).
  Variables (S0 S1 S2 S3 S4 S5 S6 S7 : word) (J8 : list byte).

  (* the stack floor moves up to usp - 6144512, one byte inside
     ASTK = 6144513 (the stack known writable below sp, AS/MainEntry amain_at row c); 6144512 = 64 x 96008
     keeps ALO = usp mod 64. ATOP = usp - 8 MiB is unchanged. *)
  Definition ALO : Z := usp - 6144512.

  Definition AMFRAME (mm : amem) : Prop :=
    rw_cells bsegs mm (usp + -128) [CB 8 J8; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 (Z_to_bv 64 ASTAGE2_RET)].

  Definition ASTAT (mm : amem) : Prop :=
       rw_cells bsegs mm 0x5d49e8 [C4 (Z_to_bv 64 TID)]
    /\ rw_cells bsegs mm 0x5f4d00 [C4 (Z_to_bv 64 0)]
    /\ (exists cdt thr sec tm1, rw_cells bsegs mm 0x5f4d20 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
    /\ rw_cells bsegs mm 0x1339a0 [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs mm 0x9e490 [C1 (Z_to_bv 8 0)]
    /\ (exists dso, rw_cells bsegs mm 0x9b5d0 [C8 dso])
    /\ rw_cells bsegs mm 0x5f5188 [C8 (Z_to_bv 64 0)] /\ rw_cells bsegs mm 0x9e150 [C8 (Z_to_bv 64 RSTDIN)]
    /\ rw_cells bsegs mm RSTDIN stdin_cells
    /\ rw_cells bsegs mm 0x9e060 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells bsegs mm 0x9df70 [C8 (Z_to_bv 64 RSTDERR)]
    /\ rw_cells bsegs mm 0x9f310 [C4 (Z_to_bv 64 1)]
    /\ rw_cells bsegs mm 0x9e440 [C8 (Z_to_bv 64 1)]
    /\ rw_cells bsegs mm 0x9f3b0 [C8 (Z_to_bv 64 0)]
    /\ gdesc mm 0x9e180 0x20d20 0xd 0x20 0x1bfaf 0x20cdb (2^64 - 1)
    /\ gdesc mm 0x9e1c0 0x20d40 0x17 0x40 0x1f793 0x20cdb (2^64 - 1)
    /\ gdesc mm 0x9e200 0x20d80 0xd 0x20 0x1e6fa 0x20cdb (2^64 - 1)
    /\ gdesc mm 0x9e240 0x20da0 0x49 0x80 0x2046f 0x20cdb (2^64 - 1)
    /\ gdesc mm 0x9e280 0x20e20 0x45 0x80 0x1476e 0x20cdb (2^64 - 1)
    /\ gdesc mm 0x9e2c0 0x20ea0 0x47 0x80 0x136f4 0x20cdb (2^64 - 1)
    /\ gdesc mm 0x9e300 0x20f20 0x11 0x40 0x1cf53 0x20cdb (2^64 - 1)
    /\ gdesc mm 0x9e340 0x20f60 0x55 0x80 0x1872c 0x20cdb (2^64 - 1)
    /\ gdesc mm 0x9e380 0x20fe0 0x400 0x500 0x1580c 0x22980 (2^64 - 1)
    /\ gdesc mm 0x9e3c0 0x214e0 0x1000 0x1400 0x18733 0x22980 (2^64 - 1)
    /\ gdesc mm 0x9e400 0x228e0 0x80 0xa0 0x15eb3 0x22980 (2^64 - 1)
    /\ (exists j, rw_cells bsegs mm 0x7fffc1a4 [CB 4 j])
    /\ (exists j, rw_cells bsegs mm 0x7fffc1a8 [CB 8 j])
    /\ (exists j, rw_cells bsegs mm 0x7fffc1b0 [CB 4 j])
    /\ (exists j, rw_cells bsegs mm 0x7fffc1b4 [CB 16 j])
    /\ (exists j, rw_cells bsegs mm 0x7fffc1c4 [CB 16 j])
    /\ (exists j, rw_cells bsegs mm 0x7fffc1d4 [CB 16 j])
    /\ (exists j, rw_cells bsegs mm 0x7fffc1e4 [CB 8 j])
    /\ (exists j, rw_cells bsegs mm 0x7fffc1ec [CB 16 j])
    /\ (exists j, rw_cells bsegs mm 0x7fffc1fc [CB 160 j])
    /\ (exists j, rw_cells bsegs mm 0x7fffc29c [CB 640 j])
    /\ (exists j, rw_cells bsegs mm 0x7fffc51c [CB 20 j])
    /\ (exists j, rw_cells bsegs mm 0x8000bc30 [CB 88 j]).

  Definition astat_app (a : Z) : Prop :=
       (0x5d49e8 <= a < 0x5d49ec) \/ (0x5f4d00 <= a < 0x5f4d08) \/ (0x5f4d20 <= a < 0x5f4d30)
    \/ (0x1339a0 <= a < 0x1339a1) \/ (0x9e490 <= a < 0x9e491) \/ (0x9b5d0 <= a < 0x9b5d8)
    \/ (0x5f5180 <= a < 0x5f51a0) \/ (0x9e150 <= a < 0x9e158) \/ (0x9e068 <= a < 0x9e0f8) \/ (0x9e060 <= a < 0x9e068) \/ (0x9df70 <= a < 0x9df78)
    \/ (0x9f310 <= a < 0x9f314) \/ (0x9e180 <= a < 0x9e448) \/ (0x9f3b0 <= a < 0x9f3b8).
  Definition astat_sh (a : Z) : Prop :=
       (0x7fffc1a4 <= a < 0x7fffc1fc) \/ (0x7fffc1fc <= a < 0x7fffc51c) \/ (0x7fffc51c <= a < 0x7fffc530) \/ (0x8000bc30 <= a < 0x8000bc88).
  Definition astat_addr (a : Z) : Prop := astat_app a \/ astat_sh a.

  Lemma gdesc_magree : forall (P : Z -> Prop) m m' d b sz szr nm mn odr,
    magree bsegs P m m' -> (forall a, d <= a < d + 64 -> P a) -> gdesc m d b sz szr nm mn odr -> gdesc m' d b sz szr nm mn odr.
  Proof.
    intros P m m' d b sz szr nm mn odr AG HP [G1 G2]. split.
    - eapply rw_cells_magree; [exact AG | exact G1 | intros a Ha; apply HP; cbn in Ha; lia].
    - eapply rw_cells_magree; [exact AG | exact G2 | intros a Ha; apply HP; cbn in Ha; lia].
  Qed.

  Lemma ASTAT_agree : forall (P : Z -> Prop) m m', magree bsegs P m m' -> (forall a, astat_addr a -> P a) -> ASTAT m -> ASTAT m'.
  Proof.
    intros P m m' AG HP ST. unfold ASTAT in *.
    Ltac tr1 AG HP := eapply rw_cells_magree; [exact AG | eassumption | intros a Ha; apply HP; unfold astat_addr, astat_app, astat_sh; cbn in Ha; unfold RSTDIN in Ha; lia].
    Ltac tr_lock AG HP H :=
      lazymatch type of H with
      | _ /\ _ => let HcL := fresh "HcL" in let HcR := fresh "HcR" in destruct H as [HcL HcR]; split; [clear HcR; tr_lock AG HP HcL | clear HcL; tr_lock AG HP HcR]
      | exists _, _ => let j := fresh "j" in let HcE := fresh "HcE" in destruct H as [j HcE]; exists j; tr_lock AG HP HcE
      | gdesc _ _ _ _ _ _ _ _ => eapply gdesc_magree; [exact AG | intros a Ha; apply HP; unfold astat_addr, astat_app; lia | exact H]
      | _ => eapply rw_cells_magree; [exact AG | exact H | intros a Ha; apply HP; unfold astat_addr, astat_app, astat_sh; cbn in Ha; unfold RSTDIN in Ha; lia]
      end.
    tr_lock AG HP ST.
  Qed.

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

  Variable RSTK : region.
  Hypothesis RSTK_lo : r_lo RSTK <= ALO.
  Hypothesis RSTK_hi : usp + -128 <= r_hi RSTK.
  Hypothesis RSTK_rlo : ATOP <= r_rlo RSTK.
  Hypothesis USP16 : usp mod 16 = 0.
  Hypothesis USPLO : ATOP + 8388608 <= usp.
  Hypothesis USPHI : usp + 24 <= 2^47.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.
  Variable canary : word.

  Definition ABASE (so : stdout_st) (mm : amem) : Prop :=
    stk bsegs mm ALO (usp + -128) /\ mem_inv bsegs mm /\ AMFRAME mm /\ ASTAT mm
    /\ stderr_wfile0 mm /\ rw_cells bsegs mm ssp_guard [C8 canary]
    /\ atrun_cells0 mm /\ harness_invA mm /\ rodata_sh0 mm /\ rclean mm RSTK /\ rclean mm RBstdout
    /\ rclean mm RSTG
    /\ (exists errv, rw_cells bsegs mm (errno_addr (Z_to_bv 64 ATP)) [C4 errv])
    /\ stdout_file mm so.

  Lemma geo : ATOP <= ALO /\ ALO + 6144512 = usp /\ KHIGH <= ALO /\ usp + 24 <= 2^47 /\ usp mod 16 = 0.
  Proof. unfold ALO, KHIGH in *. repeat split; lia. Qed.

  Lemma errno_addr_ATP : errno_addr (Z_to_bv 64 ATP) = 0x5d49ec.
  Proof. reflexivity. Qed.

  Section AfterCallee.
    Variables (LB : list ablock) (m m' : amem).
    Hypothesis HP : aheap_pres CI LB (usp + -128) m m'.
    Hypothesis HS : astk_shadow_pres (usp + -128) m m'.
    Hypothesis HLB : forall b, In b LB -> 0x5f7000 <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP.

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
    Lemma stack_dcli : forall a, usp + -128 <= a < 2^47 -> dcli CI LB (usp + -128) a.
    Proof. intros a Ha. left. left. lia. Qed.
    Lemma stack_sh_dcli : forall RLO RHI a, ATOP <= RLO -> RHI <= KEND -> shad RLO <= a < shad RHI -> dcli CI LB (usp + -128) a.
    Proof.
      intros RLO RHI a H1 H2 Ha. destruct (Z.lt_ge_cases a (shad (usp + -128))) as [LT|GE].
      - right. pose proof (shad_mono ATOP RLO H1). lia.
      - left. right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad]. left.
        rewrite !shad_div in *. unfold ASHOFF, KEND in *. Z.div_mod_to_equations. lia.
    Qed.

    Lemma ABASE_after_dpost : forall L RNG st LB' so, AHEAP AI L RNG st LB' m' -> mem_inv bsegs m' -> stk bsegs m' ALO (usp + -128) ->
      ABASE so m -> ABASE so m'.
    Proof.
      intros L RNG st LB' so AH' MI' ST' (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & [errv ERR] & SOF).
      pose proof geo as (G1 & G2 & G3 & G4 & G5). pose proof RSTK_rlo as RSC. atop_facts. unfold KHIGH in G3.
      split; [exact ST'|]. split; [exact MI'|].
      split. { unfold AMFRAME in *. eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply stack_dcli; cbn in Ha; lia]. }
      split. { eapply ASTAT_agree; [exact AG| | exact AS]. intros a [Ha|Ha].
               - unfold astat_app in Ha. left. right; left.
                 Ltac tryr lo hi := lazymatch goal with Hx : (lo <= _ < _) |- _ => idtac end;
                   exists (lo, hi); split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto | cbn; lia].
                 repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end;
                   first [ tryr 0x5d49e8 0x5d49f0 | tryr 0x5f4d00 0x5f4d08 | tryr 0x5f4d20 0x5f4d30 
                         | tryr 0x1339a0 0x1339a1 | tryr 0x9e490 0x9e491 | tryr 0x9b5d0 0x9b5d8
                         | tryr 0x5f5180 0x5f55d0 | tryr 0x9e150 0x9e158 | tryr 0x9e068 0x9e0f8 | tryr 0x9e060 0x9e068 | tryr 0x9df70 0x9df78
                         | tryr 0x9f310 0x9f314 | tryr 0x9e180 0x9e448 | tryr 0x9f3b0 0x9f3b8 ].
               - unfold astat_sh in Ha. destruct Ha as [Ha|[Ha|[Ha|Ha]]].
                 + apply (ci_drv_sh' 0x20d20 0x20fe0); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity].
                 + apply (ci_drv_sh' 0x20fe0 0x228e0); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity].
                 + apply (ci_drv_sh' 0x228e0 0x22980); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity].
                 + apply (ci_drv_sh' 0x9e180 0x9e448); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity]. }
      split. { destruct SE as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
               eapply rw_cells_magree; [exact AG| exact Hc|]. intros a Ha. apply (ci_drv RSTDERR (RSTDERR + 232)); [unfold drv_img_ranges; cbn; tauto| cbn in Ha; lia]. }
      split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. apply (ci_drv 0x5f4ad0 0x5f4ad8); [unfold drv_img_ranges; cbn; tauto| unfold ssp_guard in Ha; cbn in Ha; lia]. }
      split. { unfold atrun_cells0 in *. destruct TR as (TR & TI & TX & (cdt & thr & sec & tm1 & TL)). split.
                 - eapply rw_cells_magree; [exact AG| exact TR| intros a Ha; apply (ci_drv 0x5d4150 0x5d4170); [unfold drv_img_ranges; cbn; tauto| unfold AINIT_FLAG in Ha; cbn in Ha; lia]].
                 - split. { eapply rw_cells_magree; [exact AG| exact TI| intros a Ha; apply (ci_drv 0x5d4150 0x5d4170); [unfold drv_img_ranges; cbn; tauto| unfold AAEF_INCB in Ha; cbn in Ha; lia]]. }
                   split. { eapply atx_cells1w_agree; [exact AG| | exact TX]. intros a Ha. apply (ci_drv 0x5f4ae0 0x5f4d00); [unfold drv_img_ranges; cbn; tauto| unfold atx_addrA, AATX, AATX_N in Ha; lia]. }
                   exists cdt, thr, sec, tm1. eapply rw_cells_magree; [exact AG| exact TL| intros a Ha; apply (ci_drv 0x5f4d20 0x5f4d30); [unfold drv_img_ranges; cbn; tauto| unfold ALIBC in Ha; cbn in Ha; lia]]. }
      split.
      { eapply harness_invA_magree; [exact AG| | exact HI]. intros a Ha.
        destruct (Z.lt_ge_cases a 0x7fffc51c);
          [ apply (ci_drv_sh 0x20fe0 0x228e0); [unfold drv_img_ranges; cbn; tauto| rewrite !shad_div; unfold ASHOFF; lia| reflexivity| reflexivity]
          | apply (ci_drv_sh 0x228e0 0x22980); [unfold drv_img_ranges; cbn; tauto| rewrite !shad_div; unfold ASHOFF; lia| reflexivity| reflexivity] ]. }
      split. { eapply rodata_sh0_magree; [exact AG| | exact ROD]. intros a Ha. apply (ci_drv_sh 0x10000 0x20cc0); [left; reflexivity| exact Ha| reflexivity| reflexivity]. }
      split. { eapply rclean_magree; [exact AG| | exact RCS]. intros a Ha. destruct RCS as [(_ & HL64 & _) _]. unfold hull64 in HL64.
               apply (stack_sh_dcli (r_rlo RSTK) (r_rhi RSTK)); [atop_facts; lia| lia| exact Ha]. }
      split. { eapply rclean_magree; [exact AG| | exact RCB]. intros a Ha. unfold RBstdout in Ha. cbn [r_rlo r_rhi] in Ha.
               apply (ci_drv_sh 0x5f5180 0x5f55d0); [unfold drv_img_ranges; cbn; tauto| | reflexivity| reflexivity].
               rewrite !shad_div in *. unfold ASHOFF in *. lia. }
      split. { eapply rclean_magree; [exact AG| | exact RSG]. intros a Ha. unfold RSTG in Ha. cbn [r_rlo r_rhi] in Ha.
               apply (ci_drv_sh 0x5c4140 0x5d4180); [unfold drv_img_ranges; cbn; tauto| | reflexivity| reflexivity].
               rewrite !shad_div in *. unfold ASHOFF in *. lia. }
      split. { exists errv. eapply rw_cells_magree; [exact AG| exact ERR|]. intros a' Ha'. rewrite errno_addr_ATP in Ha'. cbn in Ha'.
               apply (ci_drv 0x5d49e8 0x5d49f0); [unfold drv_img_ranges; cbn; tauto| lia]. }
      eapply stdout_file_magree; [exact AG| | exact SOF]. intros a [Ha|Ha].
      - apply (ci_drv RSTDOUT (RSTDOUT + 232)); [unfold drv_img_ranges; cbn; tauto| exact Ha].
      - apply (ci_drv 0x5f5180 0x5f55d0); [unfold drv_img_ranges; cbn; tauto| cbn in Ha |- *; lia].
    Qed.

    Lemma astring_after_dpost : forall P str slack r, astring m P str slack r -> astring m' P str slack r.
    Proof.
      intros P str slack r AS. eapply astring_magree; [exact AG| | | exact AS].
      - intros a Ha. apply stack_dcli. lia.
      - intros a Ha. pose proof geo as (G1 & _). apply (stack_sh_dcli (usp + -128) (2^47)); [atop_facts; lia| unfold KEND; lia| exact Ha].
    Qed.
  End AfterCallee.

  Definition WOKb (hi : Z) (iv : Z * Z) : Prop :=
    (ALO <= fst iv /\ snd iv <= hi)
    \/ (fst iv = 0x5d49ec /\ snd iv = 0x5d49f0)
    \/ (fst iv = RSTDERR /\ snd iv = RSTDERR + 232)
    \/ ablk (fst iv) (snd iv)
    \/ (ASTAGE <= fst iv /\ snd iv <= ASTAGE + 65536).
  Definition WOK : Z * Z -> Prop := WOKb (usp + -128).

  Lemma WOKb_outside : forall hi W a, ALO <= hi -> Forall (WOKb hi) W ->
    (hi <= a
     \/ (a < 0x5f7000 /\ ~ (0x5d49ec <= a < 0x5d49f0) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x5c4150 <= a < 0x5d4150))
     \/ (0x7fff7000 <= a < 0x10007fff8000)) -> outside W a.
  Proof.
    pose proof geo as (G1 & G2 & G3 & _). unfold KHIGH in *. atop_facts.
    intros hi. induction W as [|[lo1 hi1] W IH]; intros a Hhi HW Ha; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    unfold WOKb, ablk, ASTAGE, AIMG_HI, KLS in H1. cbn [fst snd] in H1. lia.
  Qed.
  Lemma WOK_outside : forall W a, Forall WOK W ->
    (usp + -128 <= a
     \/ (a < 0x5f7000 /\ ~ (0x5d49ec <= a < 0x5d49f0) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x5c4150 <= a < 0x5d4150))
     \/ (0x7fff7000 <= a < 0x10007fff8000)) -> outside W a.
  Proof. intros W a HW Ha. pose proof geo as (_ & G2 & _). eapply WOKb_outside; [| exact HW| exact Ha]. lia. Qed.

  Lemma WOKb_appW : forall hi W, hi <= usp + 24 -> Forall (WOKb hi) W -> appW W.
  Proof.
    pose proof geo as (G1 & G2 & G3 & _). unfold KHIGH in G3. atop_facts. intros hi W Hhi.
    induction W as [|[lo1 hi1] W IH]; intros HW; [apply Forall_nil|]. inversion HW as [|x l H1 H2]; subst.
    constructor; [| apply IH; exact H2]. unfold WOKb, ablk, ASTAGE, AIMG_HI, KLS, KHIGH in H1. cbn [fst snd] in H1 |- *. unfold KLOW, KHIGH. lia.
  Qed.

  Lemma ABASE_of_parts : forall hi W m m' so, ALO <= hi <= usp + 24 -> Forall (WOKb hi) W -> munch W m m' -> wmono bsegs m m' ->
    ASTAT m -> rw_cells bsegs m ssp_guard [C8 canary] -> atrun_cells0 m -> harness_invA m -> rodata_sh0 m ->
    rclean m RSTK -> rclean m RBstdout -> rclean m RSTG -> stdout_file m so ->
    stk bsegs m' ALO (usp + -128) -> mem_inv bsegs m' -> AMFRAME m' -> stderr_wfile0 m' ->
    (exists errv, rw_cells bsegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
    ABASE so m'.
  Proof.
    intros hi W m m' so Hhi HW MU WM AS GU TR HI ROD RCS RCB RSG SOF ST' MI' FR' SE' ERR'.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG. pose proof (WOKb_appW hi W ltac:(lia) HW) as AW.
    assert (OUT : forall a, (hi <= a \/ (a < 0x5f7000 /\ ~ (0x5d49ec <= a < 0x5d49f0) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x5c4150 <= a < 0x5d4150))
                             \/ (0x7fff7000 <= a < 0x10007fff8000)) ->
                            (fun x => outside W x) a) by (intros a Ha; eapply WOKb_outside; [| eassumption| exact Ha]; lia).
    split; [exact ST'|]. split; [exact MI'|]. split; [exact FR'|].
    split. { eapply ASTAT_agree; [exact AG| | exact AS]. intros a Ha. apply OUT. right.
             unfold astat_addr, astat_app, astat_sh in Ha. rewrite ?shad_div in Ha. unfold ASHOFF in Ha. lia. }
    split; [exact SE'|].
    split. { eapply rw_cells_magree; [exact AG| exact GU| intros a Ha; apply OUT; unfold ssp_guard in Ha; cbn in Ha; lia]. }
    split. { unfold atrun_cells0 in *. destruct TR as (TR & TI & TX & (cdt & thr & sec & tm1 & TL)). split; [eapply rw_cells_magree; [exact AG| exact TR| intros a Ha; apply OUT; unfold AINIT_FLAG in Ha; cbn in Ha; lia]|].
             split; [eapply rw_cells_magree; [exact AG| exact TI| intros a Ha; apply OUT; unfold AAEF_INCB in Ha; cbn in Ha; lia]|].
             split; [eapply atx_cells1w_agree; [exact AG| | exact TX]; intros a Ha; apply OUT; unfold atx_addrA, AATX, AATX_N in Ha; lia|].
             exists cdt, thr, sec, tm1. eapply rw_cells_magree; [exact AG| exact TL| intros a Ha; apply OUT; unfold ALIBC in Ha; cbn in Ha; lia]. }
    split. { eapply harness_invA_magree; [exact AG| | exact HI]. intros a Ha. apply OUT. lia. }
    split; [eapply rodata_sh0_frame; [exact ROD| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCS| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RCB| exact MU| exact WM| exact AW]|].
    split; [eapply rclean_transport; [exact RSG| exact MU| exact WM| exact AW]|]. split; [exact ERR'|].
    eapply stdout_file_magree; [exact AG| | exact SOF]. intros a Ha. apply OUT. cbn in Ha. lia.
  Qed.

  Lemma ABASE_munch : forall W m m' so, ABASE so m -> Forall WOK W -> munch W m m' -> wmono bsegs m m' ->
    mem_inv bsegs m' -> stk bsegs m' ALO (usp + -128) -> stderr_wfile0 m' ->
    (exists errv, rw_cells bsegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
    ABASE so m'.
  Proof.
    intros W m m' so (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & ERR & SOF) HW MU WM MI' ST' SE' ERR'.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    eapply (ABASE_of_parts (usp + -128)); try eassumption; [lia|].
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


  Lemma exit_relro_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m ->
       rw_cells bsegs m 0x9a590 [C8 (Z_to_bv 64 0x99370); C8 (Z_to_bv 64 0x99360)]
    /\ rw_cells bsegs m 0x99360 [C8 (Z_to_bv 64 0x80860); C8 (Z_to_bv 64 0x318b0)]
    /\ rw_cells bsegs m 0x998a8 [C8 (Z_to_bv 64 0x892d8); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m 0x9a550 [C8 (Z_to_bv 64 0x9e180); C8 (Z_to_bv 64 0x9e440)]
    /\ rw_cells bsegs m 0x998f8 [C8 (Z_to_bv 64 0x9b738)]
    /\ rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)].
  Proof.
    intros L RNG st LB m AH. unfold got_ssp, ssp_guard.
    Ltac relro_tac AH bs :=
      eapply rw_cells_recast;
      [ apply (rw_cells_image0 bsegs _ _ bs);
        [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply (AI_relro AI _ _ _ _ _ AH); rewrite ?length_app, ?length_le8 in Ha; unfold ARELRO_LO, ARELRO_HI; lia
        | vm_compute; reflexivity | lia | rewrite ?length_app, ?length_le8; lia ]
      | cbn; repeat split; exact I | reflexivity | reflexivity ].
    split; [relro_tac AH (le8 (Z_to_bv 64 0x99370) ++ le8 (Z_to_bv 64 0x99360))|].
    split; [relro_tac AH (le8 (Z_to_bv 64 0x80860) ++ le8 (Z_to_bv 64 0x318b0))|].
    split; [relro_tac AH (le8 (Z_to_bv 64 0x892d8) ++ le8 (Z_to_bv 64 0))|].
    split; [relro_tac AH (le8 (Z_to_bv 64 0x9e180) ++ le8 (Z_to_bv 64 0x9e440))|].
    split; [relro_tac AH (le8 (Z_to_bv 64 0x9b738))| relro_tac AH (le8 (Z_to_bv 64 0x5f4ad0))].
  Qed.

  Lemma mdtor_rt_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rw_cells bsegs m 0x9f310 [C4 (Z_to_bv 64 1)] -> mdtor_rt m.
  Proof.
    intros L RNG st LB m AH RG. pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT. unfold artcells in RT. decompose [and] RT.
    destruct (exit_relro_of_aheap _ _ _ _ _ AH) as (_ & _ & _ & _ & X5 & _).
    unfold mdtor_rt. repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.

  Lemma aat_exit_intro : forall (code : Z) (s : APS) L (LB : list ablock) (SP : Z) RNG
      (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : amem),
    stk bsegs m ALO SP -> ALO <= SP - 48 - MDTOR_DEPTH -> usp + -128 <= SP <= usp ->
    ASTAT m -> atx_exit m -> AHEAP AI L RNG (aps_m s) LB m -> stdout_file m (aps_so s) -> stderr_file m -> rw_cells bsegs m ssp_guard [C8 canary] ->
    mem_inv bsegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    aat_exit code s RNG (MS (mkR ra (Z_to_bv 64 SP) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (Z_to_bv 64 AEXIT_PC) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST LOS SPR AS ATX AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof AS as (A1 & A2 & (cdt & thr & sec & tm1 & A3) & A11 & A12 & [dso A13] & A14 & A15 & A15' & A16 & A17
                      & D1 & D2 & D3 & GD0 & GD1 & GD2 & GD3 & GD4 & GD5 & GD6 & GD7 & GD8 & GD9 & GD10 & SH0 & SH1 & SH2 & SH3 & SH4 & SH5 & SH6 & SH7 & SH8 & SH9 & SH10 & SH11).
    destruct (exit_relro_of_aheap _ _ _ _ _ AH) as (X1 & X2 & X3 & X4 & X5 & X6).
    pose proof (mdtor_rt_of_aheap _ _ _ _ _ AH D1) as RT.
    unfold aat_exit. do 33 eexists. exists m, ALO, TID, cdt, thr, sec, tm1, dso, canary.
    split; [reflexivity|]. rewrite !unsigned_lit by lia.
    split. { unfold mdtor_pre. repeat match goal with |- _ /\ _ => split end; try assumption; eexists; eassumption. }
    repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try lia.
    - eapply rng_sub'; [exact RSTK'| lia].
    - unfold MDTOR_W. repeat (apply Forall_cons; [cbn [fst snd]|]); [..| apply Forall_nil].
      all: first [ eapply rng_sub'; [exact RIMG| lia] | eapply rng_sub'; [exact RIMSH| lia] ].
  Qed.

  Lemma amain_return : forall (code : Z) (s : APS) L (LB : list ablock) RNG
      (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
    AMFRAME m -> stk bsegs m ALO (usp + -128) -> ASTAT m -> atx_exit m -> AHEAP AI L RNG (aps_m s) LB m ->
    stdout_file m (aps_so s) -> stderr_file m -> rw_cells bsegs m ssp_guard [C8 canary] -> mem_inv bsegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    evtF bsegs RNG (aat_exit code s RNG)
      (MS (mkR x1 (Z_to_bv 64 (usp + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x801f8) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros FR ST AS ATX AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    unfold AMFRAME, ASTAGE2_RET in FR.
    do 11 zstep. release_frame FR ST (usp + -48). zstep.
    replace (ret_pc (Z_to_bv 64 0x88cf4)) with (Z_to_bv 64 0x88cf4) by (symmetry; rpc).
    zstep.
    apply evtF_done. unfold AEXIT_PC.
    eapply aat_exit_intro; first [eassumption | lia | unfold MDTOR_DEPTH; lia].
  Qed.

  Lemma aexit2_tail : forall (s : APS) L (LB : list ablock) RNG
      (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
    stk bsegs m ALO (usp + -128) -> ASTAT m -> atx_exit m -> AHEAP AI L RNG (aps_m s) LB m ->
    stdout_file m (aps_so s) -> stderr_file m -> rw_cells bsegs m ssp_guard [C8 canary] -> mem_inv bsegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    evtF bsegs RNG (aat_exit 2 s RNG)
      (MS (mkR x1 (Z_to_bv 64 (usp + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x80284) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST AS ATX AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    zstep. zstep.
    apply evtF_done. unfold AEXIT_PC.
    eapply aat_exit_intro; first [eassumption | lia | unfold MDTOR_DEPTH; lia].
  Qed.
End CTX.
End CANSEC1.
