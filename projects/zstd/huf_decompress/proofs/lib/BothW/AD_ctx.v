(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (ALO, the program's stack bottom, inside the 6,144,513-byte stack window every launch zero-maps below sp, rounded to sp's 64-byte grid; geo restated to match; 14 recorded proofs replaced by written proofs (implMA_of_implAM, gdesc_magree, gdescs_magree and 11 more); ported by content from zstd_frame_info's file of the same role, with this binary's addresses and names). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit Stdio_iface F_printf_iface MonadF AF_atexit AExit F_module_dtor ADriver_iface AD_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import AHarness_bm.
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

  (* LPS 727298f3: the stack every launch zero-maps below sp is the model's [stack_window_depth],
     6144513 bytes (InitMem.im_stack_depth); its bottom rounded up to sp's 64-byte grid is sp - 6144512 *)
  Definition ALO : Z := usp - 6144512.

  Definition AMFRAME (mm : amem) : Prop :=
    rw_cells bsegs mm (usp + -128) [CB 8 J8; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 (Z_to_bv 64 ASTAGE2_RET)].

  
  Definition ASTAT (mm : amem) : Prop :=
       rw_cells bsegs mm 0x5ed1e8 [C4 (Z_to_bv 64 TID)]                                 
    /\ rw_cells bsegs mm 0x60d500 [C4 (Z_to_bv 64 0)]                                   
    /\ (exists cdt thr sec tm1, rw_cells bsegs mm 0x60d520 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])  
    /\ (exists reg : bool, atx_stateA reg mm)                                          
    /\ rw_cells bsegs mm 0xb6c90 [C1 (Z_to_bv 8 0)]                                   
    /\ (exists dso, rw_cells bsegs mm 0xb3e40 [C8 dso])                                
    /\ rw_cells bsegs mm 0x60d988 [C8 (Z_to_bv 64 0)] /\ rw_cells bsegs mm 0xb69c0 [C8 (Z_to_bv 64 RSTDIN)]  
    /\ rw_cells bsegs mm RSTDIN stdin_cells                                          
    /\ rw_cells bsegs mm 0xb68d0 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells bsegs mm 0xb67e0 [C8 (Z_to_bv 64 RSTDERR)]  
    
    /\ rw_cells bsegs mm 0xb7b10 [C4 (Z_to_bv 64 1)]
    /\ rw_cells bsegs mm 0xb6c40 [C8 (Z_to_bv 64 1)]
    /\ rw_cells bsegs mm 0xb7bb0 [C8 (Z_to_bv 64 0)]
    /\ gdescs mm 0xb69f0 AGLOBALS
    /\ (exists j, rw_cells bsegs mm 0x7fffc1c0 [CB 144 j]) /\ (exists j, rw_cells bsegs mm 0x8000ed3e [CB 72 j]).

  
  Definition astat_app (a : Z) : Prop :=
       (0x5ed1e8 <= a < 0x5ed1ec) \/ (0x60d500 <= a < 0x60d508) \/ (0x60d520 <= a < 0x60d530) \/ (0x60d2e0 <= a < 0x60d310)
    \/ (0x60d400 <= a < 0x60d410) \/ (0x14c1a0 <= a < 0x14c1a1) \/ (0x5ec954 <= a < 0x5ec955) \/ (0xb6c90 <= a < 0xb6c91) \/ (0xb3e40 <= a < 0xb3e48)
    \/ (0x60d980 <= a < 0x60d9a0) \/ (0xb69c0 <= a < 0xb69c8) \/ (0xb68d8 <= a < 0xb6968) \/ (0xb68d0 <= a < 0xb68d8) \/ (0xb67e0 <= a < 0xb67e8)
    \/ (0xb7b10 <= a < 0xb7b14) \/ (0xb69f0 <= a < 0xb6c30) \/ (0xb6c40 <= a < 0xb6c48) \/ (0xb7bb0 <= a < 0xb7bb8).
  Definition astat_sh (a : Z) : Prop :=
       (0x7fffc1c0 <= a < 0x7fffc250) \/ (0x8000ed3e <= a < 0x8000ed86).
  Definition astat_addr (a : Z) : Prop := astat_app a \/ astat_sh a.

  Lemma gdesc_magree : forall (P : Z -> Prop) m m' d b sz szr nm mn odr,
    magree bsegs P m m' -> (forall a, d <= a < d + 64 -> P a) -> gdesc m d b sz szr nm mn odr -> gdesc m' d b sz szr nm mn odr.
  Proof.
    intros P m m' d b sz szr nm mn odr AG HP [G1 G2]. split.
    - eapply rw_cells_magree; [exact AG | exact G1 | intros a Ha; apply HP; cbn in Ha; lia].
    - eapply rw_cells_magree; [exact AG | exact G2 | intros a Ha; apply HP; cbn in Ha; lia].
  Qed.

  Lemma gdescs_magree : forall G (P : Z -> Prop) m m' d, magree bsegs P m m' ->
    (forall a, d <= a < d + 64 * Z.of_nat (length G) -> P a) -> gdescs m d G -> gdescs m' d G.
  Proof.
    induction G as [|[[[[b sz] swr] nm] md] G IH]; intros P m m' d AG HP HG; cbn [gdescs length] in *; [exact I|].
    split; [eapply gdesc_magree; [exact AG| | exact (proj1 HG)]; intros a Ha; apply HP; lia|].
    eapply IH; [exact AG| | exact (proj2 HG)]. intros a Ha. apply HP. lia.
  Qed.

  Lemma ASTAT_agree : forall (P : Z -> Prop) m m', magree bsegs P m m' -> (forall a, astat_addr a -> P a) -> ASTAT m -> ASTAT m'.
Proof.
intros P m m' AG HP ST. unfold ASTAT in *.
Ltac tr1 AG HP := eapply rw_cells_magree; [exact AG | eassumption | intros a Ha; apply HP; unfold astat_addr, astat_app, astat_sh; cbn in Ha; unfold RSTDIN in Ha; lia].
decompose [and ex] ST.
repeat match goal with
| |- _ /\ _ => split
| |- exists _, _ => eexists
end.
all: first [ tr1 AG HP
| eapply atx_stateA_agree; [exact AG | intros a Ha; apply HP; unfold atx_state_addrA, atx_addrA in Ha; unfold astat_addr, astat_app; lia | eassumption]
| eapply gdescs_magree; [exact AG | intros a Ha; apply HP; rewrite AGLOBALS_length in Ha; unfold astat_addr, astat_app; lia | eassumption] ].
Qed.

  
  Definition ASTATX (mm : amem) : Prop := exists reg : bool, atx_stateA reg mm.

  
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
  Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv CI.
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

  Lemma errno_addr_ATP : errno_addr (Z_to_bv 64 ATP) = 0x5ed1ec.
Proof.
vm_compute. reflexivity. Qed.

  
  Section AfterCallee.
    Variables (LB : list ablock) (m m' : amem).
    Hypothesis HP : aheap_pres CI LB (usp + -128) m m'.
    Hypothesis HS : astk_shadow_pres (usp + -128) m m'.
    Hypothesis HLB : forall b, In b LB -> 0x60f000 <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP.

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
    Lemma ci_cli_sh : forall lo' hi' a, In (lo', hi') cli_img_ranges -> shad lo' <= a <= shad (hi' - 1) -> lo' mod 8 = 0 -> dcli CI LB (usp + -128) a.
    Proof.
      intros lo' hi' a Hin Ha M1. left. right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
      right; left. exists (lo', hi'). split; [apply CLI_CI; exact Hin|]. cbn. rewrite !shad_div in Ha. unfold ASHOFF in *. Z.div_mod_to_equations. lia.
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
Ltac tryr lo hi := exists (lo, hi); split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto | cbn; lia].
Ltac drv_pick k := let L := eval vm_compute in drv_img_ranges in
  let rec go L := lazymatch L with
    | cons (?lo, ?hi) ?t => first [ k lo hi | go t ]
    | nil => fail
  end in go L.
repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end;
drv_pick ltac:(fun lo hi => tryr lo hi).
- unfold astat_sh in Ha. destruct Ha as [Ha|Ha];
drv_pick ltac:(fun lo hi => apply (ci_drv_sh' lo hi); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity]). }
split. { destruct SE as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
eapply rw_cells_magree; [exact AG| exact Hc|]. intros a Ha. apply (ci_drv RSTDERR (RSTDERR + 232)); [unfold drv_img_ranges; cbn; tauto| cbn in Ha; lia]. }
split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. drv_pick ltac:(fun lo hi => apply (ci_drv lo hi); [unfold drv_img_ranges; cbn; tauto| unfold ssp_guard in Ha; cbn in Ha; lia]). }
split. { eapply atrun_cells0_magree; [exact AG| | exact TR]. intros a [Ha|[Ha|[Ha|Ha]]].
- drv_pick ltac:(fun lo hi => apply (ci_drv lo hi); [unfold drv_img_ranges; cbn; tauto| unfold AINIT_FLAG in Ha; lia]).
- unfold atx_addrA in Ha. destruct Ha as [Ha|[Ha|[Ha|Ha]]];
drv_pick ltac:(fun lo hi => apply (ci_drv lo hi); [unfold drv_img_ranges; cbn; tauto| lia]).
- drv_pick ltac:(fun lo hi => apply (ci_drv lo hi); [unfold drv_img_ranges; cbn; tauto| lia]).
- drv_pick ltac:(fun lo hi => apply (ci_drv lo hi); [unfold drv_img_ranges; cbn; tauto| lia]). }
split. { exact ((fun _ => I) CLI_CI). }
split. { eapply rodata_sh0_magree; [exact AG| | exact ROD]. intros a Ha. destruct Ha as [Ha|Ha]; try unfold AHBM_LO, AHBM_HI in Ha;
drv_pick ltac:(fun lo hi => apply (ci_drv_sh lo hi); [unfold drv_img_ranges; cbn; tauto| rewrite !shad_div in *; unfold ASHOFF in *; lia| reflexivity| reflexivity]). }
split. { eapply rclean_magree; [exact AG| | exact RCS]. intros a Ha. destruct RCS as [(_ & HL64 & _) _]. unfold hull64 in HL64.
apply (stack_sh_dcli (r_rlo RSTK) (r_rhi RSTK)); [atop_facts; lia| lia| exact Ha]. }
split. { eapply rclean_magree; [exact AG| | exact RCB]. intros a Ha. unfold RBstdout in Ha. cbn [r_rlo r_rhi] in Ha.
drv_pick ltac:(fun lo hi => apply (ci_drv_sh lo hi); [unfold drv_img_ranges; cbn; tauto| rewrite !shad_div in *; unfold ASHOFF in *; lia | reflexivity| reflexivity]). }
split. { eapply rclean_magree; [exact AG| | exact RSG]. intros a Ha. unfold RSTG in Ha. cbn [r_rlo r_rhi] in Ha.
drv_pick ltac:(fun lo hi => apply (ci_drv_sh lo hi); [unfold drv_img_ranges; cbn; tauto| rewrite !shad_div in *; unfold ASHOFF in *; lia | reflexivity| reflexivity]). }
split. { exists errv. eapply rw_cells_magree; [exact AG| exact ERR|]. intros a' Ha'. rewrite errno_addr_ATP in Ha'. cbn in Ha'.
drv_pick ltac:(fun lo hi => apply (ci_drv lo hi); [unfold drv_img_ranges; cbn; tauto| lia]). }
eapply stdout_file_magree; [exact AG| | exact SOF]. intros a [Ha|Ha].
- apply (ci_drv RSTDOUT (RSTDOUT + 232)); [unfold drv_img_ranges; cbn; tauto| exact Ha].
- drv_pick ltac:(fun lo hi => apply (ci_drv lo hi); [unfold drv_img_ranges; cbn; tauto| cbn in Ha |- *; lia]).
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
    \/ (fst iv = 0x5ed1ec /\ snd iv = 0x5ed1f0)                                   
    \/ (fst iv = RSTDERR /\ snd iv = RSTDERR + 232)                               
    \/ ablk (fst iv) (snd iv)                                                     
    \/ (ASTAGE <= fst iv /\ snd iv <= ASTAGE + 65536).                           
  
  Definition WOK : Z * Z -> Prop := WOKb (usp + -128).

  
  Lemma WOKb_outside : forall hi W a, ALO <= hi -> Forall (WOKb hi) W ->
    (hi <= a
     \/ (a < 0x60f000 /\ ~ (0x5ed1ec <= a < 0x5ed1f0) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x5dc950 <= a < 0x5ec950))
     \/ (0x7fff7000 <= a < 0x10007fff8000)) -> outside W a.
Proof.
pose proof geo as (G1 & G2 & G3 & _). unfold KHIGH in *. atop_facts.
intros hi. induction W as [|[lo1 hi1] W IH]; intros a Hhi HW Ha; cbn; [exact I|].
inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
unfold WOKb, ablk, ASTAGE, AIMG_HI, KLS in H1. cbn [fst snd] in H1.
lia.
Qed.
  Lemma WOK_outside : forall W a, Forall WOK W ->
    (usp + -128 <= a
     \/ (a < 0x60f000 /\ ~ (0x5ed1ec <= a < 0x5ed1f0) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x5dc950 <= a < 0x5ec950))
     \/ (0x7fff7000 <= a < 0x10007fff8000)) -> outside W a.
Proof.
intros W a HW Ha. pose proof geo as (_ & G2 & _). eapply WOKb_outside; [| exact HW| exact Ha].
lia. Qed.

  Lemma WOKb_appW : forall hi W, hi <= usp + 24 -> Forall (WOKb hi) W -> appW W.
Proof.
pose proof geo as (G1 & G2 & G3 & _). unfold KHIGH in G3. atop_facts. intros hi W Hhi.
induction W as [|[lo1 hi1] W IH]; intros HW; [apply Forall_nil|]. inversion HW as [|x l H1 H2]; subst.
constructor; [| apply IH; exact H2]. unfold WOKb, ablk, ASTAGE, AIMG_HI, KLS, KHIGH in H1. cbn [fst snd] in H1 |- *. unfold KLOW, KHIGH. lia.
Qed.
  Lemma WOK_appW : forall W, Forall WOK W -> appW W.
  Proof. intros W HW. eapply WOKb_appW; [| exact HW]. lia. Qed.

  
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
pose proof (fun a => WOKb_outside hi W a ltac:(lia) HW) as OUT.
split; [exact ST'|]. split; [exact MI'|]. split; [exact FR'|].
split. { eapply ASTAT_agree; [exact AG| | exact AS]. intros a Ha. apply OUT. right.
unfold astat_addr, astat_app, astat_sh in Ha. rewrite ?shad_div in Ha. unfold ASHOFF in Ha. lia. }
split; [exact SE'|].
split. { eapply rw_cells_magree; [exact AG| exact GU| intros a Ha; apply OUT; unfold ssp_guard in Ha; cbn in Ha; lia]. }
split. { eapply atrun_cells0_magree; [exact AG| | exact TR]. intros a Ha. apply OUT. right; left.
unfold atrun0_addrA, atx_state_addrA, atx_addrA, AINIT_FLAG in Ha. lia. }
split. { exact I. }
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
       rw_cells bsegs m 0xb2e00 [C8 (Z_to_bv 64 0xb1bc0); C8 (Z_to_bv 64 0xb1bb0)]
    /\ rw_cells bsegs m 0xb1bb0 [C8 (Z_to_bv 64 0x969cc); C8 (Z_to_bv 64 0x3072c)]
    /\ rw_cells bsegs m 0xb20f8 [C8 (Z_to_bv 64 0xa1b28); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m 0xb2dc0 [C8 (Z_to_bv 64 0xb69f0); C8 (Z_to_bv 64 0xb6c30)]
    /\ rw_cells bsegs m 0xb2148 [C8 (Z_to_bv 64 0xb3fa8)]
    /\ rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)].
Proof.
Ltac relro_tac AH bs :=
      eapply rw_cells_recast;
      [ apply (rw_cells_image0 bsegs _ _ bs);
        [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply (AI_relro AI _ _ _ _ _ AH); rewrite ?length_app, ?length_le8 in Ha; unfold ARELRO_LO, ARELRO_HI; lia
        | vm_compute; reflexivity | lia | rewrite ?length_app, ?length_le8; lia ]
      | cbn; repeat split; exact I | reflexivity | reflexivity ].
intros L RNG st LB m AH. unfold got_ssp, ssp_guard.
Ltac cells_bs cells := lazymatch cells with
  | cons (C8 ?v) nil => constr:(le8 v)
  | cons (C8 ?v) ?t => let r := cells_bs t in constr:(le8 v ++ r)
  end.
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- rw_cells _ _ _ ?cells => let bs := cells_bs cells in relro_tac AH bs end.
Qed.

  Lemma mdtor_rt_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rw_cells bsegs m 0xb7b10 [C4 (Z_to_bv 64 1)] -> mdtor_rt m.
Proof.
intros L RNG st LB m AH RG. pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT. unfold artcells in RT. decompose [and] RT.
destruct (exit_relro_of_aheap _ _ _ _ _ AH) as (_ & _ & _ & _ & X5 & _).
unfold mdtor_rt. repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.

  
  Lemma aat_exit_intro : forall (code : Z) (s : APS) L (LB : list ablock) (SP : Z) RNG
      (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : amem),
    stk bsegs m ALO SP -> ALO <= SP - 48 - MDTOR_DEPTH -> usp + -128 <= SP <= usp ->
    ASTAT m -> AHEAP AI L RNG (aps_m s) LB m -> stdout_file m (aps_so s) -> stderr_file m -> rw_cells bsegs m ssp_guard [C8 canary] ->
    mem_inv bsegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    aat_exit code s RNG (MS (mkR ra (Z_to_bv 64 SP) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (Z_to_bv 64 AEXIT_PC) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LOS SPR AS AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0.
pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
pose proof AS as (A1 & A2 & (cdt & thr & sec & tm1 & A3) & [reg AX] & A12 & [dso A13] & A14 & A15 & A15' & A16 & A17
& D1 & D2 & D3 & GD & SH1 & SH2).
destruct (exit_relro_of_aheap _ _ _ _ _ AH) as (X1 & X2 & X3 & X4 & X5 & X6).
pose proof (mdtor_rt_of_aheap _ _ _ _ _ AH D1) as RT.
unfold aat_exit. do 33 eexists. exists m, ALO, TID, cdt, thr, sec, tm1, dso, canary.
split; [reflexivity|].
rewrite !unsigned_lit by lia.
split. { unfold mdtor_pre. repeat match goal with |- _ /\ _ => split end; try assumption; eexists; eassumption. }
repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try lia.
all: try (exists reg; exact AX).
- eapply rng_sub'; [exact RSTK'| lia].
- unfold MDTOR_W. repeat (apply Forall_cons; [cbn [fst snd]|]); [..| apply Forall_nil].
all: first [ eapply rng_sub'; [exact RIMG| lia] | eapply rng_sub'; [exact RIMSH| lia] ].
Qed.

  
  Lemma amain_return : forall (code : Z) (s : APS) L (LB : list ablock) RNG
      (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
    AMFRAME m -> stk bsegs m ALO (usp + -128) -> ASTAT m -> AHEAP AI L RNG (aps_m s) LB m ->
    stdout_file m (aps_so s) -> stderr_file m -> rw_cells bsegs m ssp_guard [C8 canary] -> mem_inv bsegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    evtF bsegs RNG (aat_exit code s RNG)
      (MS (mkR x1 (Z_to_bv 64 (usp + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x7fce8) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR ST AS AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0.
pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
unfold AMFRAME, ASTAGE2_RET in FR.
do 11 zstep. release_frame FR ST (usp + -48). zstep.
let v := eval cbv in ASTAGE2_RET in replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; rpc).
zstep.
apply evtF_done. unfold AEXIT_PC.
eapply aat_exit_intro; first [eassumption | lia | unfold MDTOR_DEPTH; lia].
Qed.

  
  Lemma aexit2_tail : forall (s : APS) L (LB : list ablock) RNG
      (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
    stk bsegs m ALO (usp + -128) -> ASTAT m -> AHEAP AI L RNG (aps_m s) LB m ->
    stdout_file m (aps_so s) -> stderr_file m -> rw_cells bsegs m ssp_guard [C8 canary] -> mem_inv bsegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    evtF bsegs RNG (aat_exit 2 s RNG)
      (MS (mkR x1 (Z_to_bv 64 (usp + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x7fd74) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST AS AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0.
pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
zstep. zstep.
apply evtF_done. unfold AEXIT_PC.
eapply aat_exit_intro; first [eassumption | lia | unfold MDTOR_DEPTH; lia].
Qed.
End CTX.
End CANSEC1.
