(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AHarness_iface
F_syscalls StdioFiles Stdio_kit Stdio_iface F_printf_iface MonadF AF_atexit AExit F_module_dtor ADriver_iface AD_kit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma implMA_of_implAM : forall {A} RNG (c : @Monad.M APS A) (s : APS) (Q : A -> APS -> machine_state -> Prop) ms,
implAM RNG c s Q ms -> implMA RNG c s (fun a s' RNG' ms' => RNG' = RNG /\ Q a s' ms') ms.
Proof. intros A RNG c s Q ms H. exact H. Qed.
Section CTX.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variables (usp : Z) (TID : Z).
Variables (S0 S1 S2 S3 S4 S5 S6 S7 : word) (J8 : list byte).
Definition ALO : Z := usp - 8388608 + 4096.
Definition AMFRAME (mm : amem) : Prop :=
rw_cells bsegs mm (usp + -128) [CB 8 J8; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 (Z_to_bv 64 ASTAGE2_RET)].
Definition ASTAT (mm : amem) : Prop :=
rw_cells bsegs mm 0x5d5428 [C4 (Z_to_bv 64 TID)]
/\ rw_cells bsegs mm 0x5f5740 [C4 (Z_to_bv 64 0)]
/\ (exists cdt thr sec tm1, rw_cells bsegs mm 0x5f5760 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
/\ (exists reg : bool, atx_stateA reg mm)
/\ rw_cells bsegs mm 0x9eed0 [C1 (Z_to_bv 8 0)]
/\ (exists dso, rw_cells bsegs mm 0x9b610 [C8 dso])
/\ rw_cells bsegs mm 0x5f5bc8 [C8 (Z_to_bv 64 0)] /\ rw_cells bsegs mm 0x9e190 [C8 (Z_to_bv 64 RSTDIN)]
/\ rw_cells bsegs mm RSTDIN stdin_cells
/\ rw_cells bsegs mm 0x9e0a0 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells bsegs mm 0x9dfb0 [C8 (Z_to_bv 64 RSTDERR)]
/\ rw_cells bsegs mm 0x9fd50 [C4 (Z_to_bv 64 1)]
/\ rw_cells bsegs mm 0x9ee80 [C8 (Z_to_bv 64 1)]
/\ rw_cells bsegs mm 0x9fdf0 [C8 (Z_to_bv 64 0)]
/\ gdescs mm 0x9e1c0 AGLOBALS
/\ (exists j, rw_cells bsegs mm 0x7fffc1cc [CB 576 j]) /\ (exists j, rw_cells bsegs mm 0x8000bc38 [CB 408 j]).
Definition astat_app (a : Z) : Prop :=
(0x5d5428 <= a < 0x5d542c) \/ (0x5f5740 <= a < 0x5f5748) \/ (0x5f5760 <= a < 0x5f5770) \/ (0x5f5520 <= a < 0x5f5550)
\/ (0x5f5640 <= a < 0x5f5650) \/ (0x1343e0 <= a < 0x1343e1) \/ (0x5d4b94 <= a < 0x5d4b95) \/ (0x9eed0 <= a < 0x9eed1) \/ (0x9b610 <= a < 0x9b618)
\/ (0x5f5bc0 <= a < 0x5f5be0) \/ (0x9e190 <= a < 0x9e198) \/ (0x9e0a8 <= a < 0x9e138) \/ (0x9e0a0 <= a < 0x9e0a8) \/ (0x9dfb0 <= a < 0x9dfb8)
\/ (0x9fd50 <= a < 0x9fd54) \/ (0x9e1c0 <= a < 0x9ee80) \/ (0x9ee80 <= a < 0x9ee88) \/ (0x9fdf0 <= a < 0x9fdf8).
Definition astat_sh (a : Z) : Prop :=
(0x7fffc1cc <= a < 0x7fffc40c) \/ (0x8000bc38 <= a < 0x8000bdd0).
Definition astat_addr (a : Z) : Prop := astat_app a \/ astat_sh a.
#[using="Type"] Lemma gdesc_magree : forall (P : Z -> Prop) m m' d b sz szr nm mn odr,
magree bsegs P m m' -> (forall a, d <= a < d + 64 -> P a) -> gdesc m d b sz szr nm mn odr -> gdesc m' d b sz szr nm mn odr.
Proof.
intros P m m' d b sz szr nm mn odr AG HP [G1 G2]. split.
- Local Ltac2 Set LiaHints.tbl := fun () => "0010>44286343777.29000004S2Ha".
eapply rw_cells_magree; [exact AG | exact G1 | intros a Ha; apply HP; cbn in Ha; lia].
- eapply rw_cells_magree; [exact AG | exact G2 | intros a Ha; apply HP; cbn in Ha; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma gdescs_magree : forall G (P : Z -> Prop) m m' d, magree bsegs P m m' ->
(forall a, d <= a < d + 64 * Z.of_nat (length G) -> P a) -> gdescs m d G -> gdescs m' d G.
Proof.
induction G as [|[[[[b sz] swr] nm] md] G IH]; intros P m m' d AG HP HG; cbn [gdescs length] in *; [exact I|].
Local Ltac2 Set LiaHints.tbl := fun () => "0010>45699206569.29000004S2Ha".
split; [eapply gdesc_magree; [exact AG| | exact (proj1 HG)]; intros a Ha; apply HP; lia|].
eapply IH; [exact AG| | exact (proj2 HG)]. intros a Ha. apply HP. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ASTAT_agree : forall (P : Z -> Prop) m m', magree bsegs P m m' -> (forall a, astat_addr a -> P a) -> ASTAT m -> ASTAT m'.
Proof.
intros P m m' AG HP ST. unfold ASTAT in *.
Ltac tr1 AG HP := eapply rw_cells_magree; [exact AG | eassumption | intros a Ha; apply HP; unfold astat_addr, astat_app, astat_sh; cbn in Ha; unfold RSTDIN in Ha; lia].
decompose [and ex] ST.
repeat match goal with
| |- _ /\ _ => split
| |- exists _, _ => eexists
end.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>57599054207.4666549718394.46000004008S2HaS2Ha".
all: first [ tr1 AG HP
| eapply atx_stateA_agree; [exact AG | intros a Ha; apply HP; unfold atx_state_addrA, atx_addrA in Ha; unfold astat_addr, astat_app; lia | eassumption]
| eapply gdescs_magree; [exact AG | intros a Ha; apply HP; rewrite AGLOBALS_length in Ha; unfold astat_addr, astat_app; lia | eassumption] ].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition ASTATX (mm : amem) : Prop := exists reg : bool, atx_stateA reg mm.
Definition astring (mm : amem) (P : Z) (s : list Z) (slack : list byte) (r : region) : Prop :=
bytes_at bsegs mm P (zb s ++ Z_to_bv 8 0 :: slack)
/\ Forall (fun c => 0 < c < 256) s
/\ ((- (P + zlength s + 1)) mod 8 <= zlength slack)
/\ (zlength s <= 131071)
/\ usp + 24 <= P
/\ rclean mm r /\ inreg r P (zlength s + 1 + zlength slack) /\ usp + -128 <= r_rlo r.
#[using="Type"] Lemma astring_facts : forall m P s slack r, astring m P s slack r ->
usp + 24 <= P /\ P + zlength s + 1 + zlength slack <= r_hi r /\ r_lo r <= P /\ usp + -128 <= r_rlo r /\ r_rlo r <= r_lo r
/\ r_hi r <= r_rhi r /\ r_rhi r <= 2^47 /\ 0 <= zlength slack /\ 0 <= zlength s <= 131071.
Proof.
intros m P s slack r (BY & HF & SL & LEN & LO & RC & IR & RLO).
pose proof (rclean_shclean _ _ RC) as (_ & HUL & _ & _). unfold hull64, KEND in HUL. unfold inreg in IR.
unfold zlength in *. repeat split; lia.
Qed.
#[using="Type"] Lemma astring_magree : forall (P0 : Z -> Prop) m m' P s slack r,
magree bsegs P0 m m' ->
(forall a, usp + -128 <= a < 2^47 -> P0 a) -> (forall a, shad (usp + -128) <= a < shad (2^47) -> P0 a) ->
astring m P s slack r -> astring m' P s slack r.
Proof.
intros P0 m m' P s slack r AG H1 H2 AS. pose proof (astring_facts _ _ _ _ _ AS) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
destruct AS as (BY & HF & SL & LEN & LO & RC & IR & RLO).
unfold astring. repeat match goal with |- _ /\ _ => split end; try assumption.
- eapply bytes_at_magree; [exact AG | exact BY |]. intros a Ha. rewrite length_app, zb_length in Ha. cbn [length] in Ha. apply H1. unfold zlength in *. Local Ltac2 Set LiaHints.tbl := fun () => "0040>15675868737.4352792921091.4455181160242.4265141986942.4200000400=00M00RS2F7S2Ha1H2H0S2F12F22F62F72HaS3RLO".
lia.
- eapply rclean_magree; [exact AG | | exact RC]. intros a Ha. apply H2.
pose proof (shad_mono (usp + -128) (r_rlo r) ltac:(lia)). pose proof (shad_mono (r_rhi r) (2^47) ltac:(lia)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
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
#[using="USP16 USPLO USPHI"] Lemma geo : ATOP <= ALO /\ ALO + 8388608 - 4096 = usp /\ KHIGH <= ALO /\ usp + 24 <= 2^47 /\ usp mod 16 = 0.
Proof. unfold ALO, KHIGH in *. repeat split; lia. Qed.
#[using="Type"] Lemma errno_addr_ATP : errno_addr (Z_to_bv 64 ATP) = 0x5d542c.
Proof. reflexivity. Qed.
Section AfterCallee.
Variables (LB : list ablock) (m m' : amem).
Hypothesis HP : aheap_pres CI LB (usp + -128) m m'.
Hypothesis HS : astk_shadow_pres (usp + -128) m m'.
Hypothesis HLB : forall b, In b LB -> 0x5f7000 <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP.
Let AG : magree bsegs (dcli CI LB (usp + -128)) m m' := magree_of_dpost _ _ _ _ _ HP HS.
#[using="DRV_CI"] Lemma ci_drv : forall lo' hi' a, In (lo', hi') drv_img_ranges -> lo' <= a < hi' -> dcli CI LB (usp + -128) a.
Proof. intros lo' hi' a Hin Ha. left. right; left. exists (lo', hi'). Local Ltac2 Set LiaHints.tbl := fun () => "0010=2594151127.36000004S2Ha".
split; [apply DRV_CI; exact Hin| cbn; lia]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="DRV_CI"] Lemma ci_drv_sh : forall lo' hi' a, In (lo', hi') drv_img_ranges -> shad lo' <= a < shad hi' -> lo' mod 8 = 0 -> hi' mod 8 = 0 -> dcli CI LB (usp + -128) a.
Proof.
intros lo' hi' a Hin Ha M1 M2. left. right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
right; left. exists (lo', hi'). split; [apply DRV_CI; exact Hin|]. cbn. rewrite !shad_div in Ha. unfold ASHOFF in *. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>33244156431.5900000?S2Ha2M12M21H2H4".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="DRV_CI"] Lemma ci_drv_sh' : forall lo' hi' a, In (lo', hi') drv_img_ranges -> shad lo' <= a <= shad (hi' - 1) -> lo' mod 8 = 0 -> dcli CI LB (usp + -128) a.
Proof.
intros lo' hi' a Hin Ha M1. left. right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
right; left. exists (lo', hi'). split; [apply DRV_CI; exact Hin|]. cbn. rewrite !shad_div in Ha. unfold ASHOFF in *. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>33244156431.5800000?S2Ha2M11H2H42H5".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma stack_dcli : forall a, usp + -128 <= a < 2^47 -> dcli CI LB (usp + -128) a.
Proof. intros a Ha. left. left. Local Ltac2 Set LiaHints.tbl := fun () => "0010>55187454681.33000004S2Ha".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="USP16 USPLO"] Lemma stack_sh_dcli : forall RLO RHI a, ATOP <= RLO -> RHI <= KEND -> shad RLO <= a < shad RHI -> dcli CI LB (usp + -128) a.
Proof.
intros RLO RHI a H1 H2 Ha. destruct (Z.lt_ge_cases a (shad (usp + -128))) as [LT|GE].
- right. pose proof (shad_mono ATOP RLO H1). Local Ltac2 Set LiaHints.tbl := fun () => "0020>52792921091.398117701366.66 00000B00iS5USPLO2Ha2LT1H2H0S5USP165USPLO2H22Ha2GE1H2H03H113H123H16".
lia.
- left. right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad]. left.
rewrite !shad_div in *. unfold ASHOFF, KEND in *. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="RSTK_rlo USP16 USPLO USPHI DRV_CI CLI_CI LB HP HS AG"] Lemma ABASE_after_dpost : forall L RNG st LB' so, AHEAP AI L RNG st LB' m' -> mem_inv bsegs m' -> stk bsegs m' ALO (usp + -128) ->
ABASE so m -> ABASE so m'.
Proof.
intros L RNG st LB' so AH' MI' ST' (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & [errv ERR] & SOF).
pose proof geo as (G1 & G2 & G3 & G4 & G5). pose proof RSTK_rlo as RSC. atop_facts. unfold KHIGH in G3.
split; [exact ST'|]. split; [exact MI'|].
split. { unfold AMFRAME in *. Local Ltac2 Set LiaHints.tbl := fun () => "00I0>15196446384.6216412950896.6216720094064.6220557961866.622060431987.62 23394620064.6225519476080.6239714382960.6240520776432.6247612406512.6252590594720.6252794183724.6253713954928.6255181160242.625721498072.62 58187469552.6259024209881.6860681890544.6262868026096.6263832633712.6264162808560.6265324800752.6266050162032.627247018736.62 7459635952.62 00000400800<00A00K00O00S00W00[00_00c00i00m01401C01G01K01O01S01W01[01_01c01g01kS2HaS2HaS2HaS3Ha'S8RSTK_rloS2HaS2HaS2HaS2HaS2HaS2HaS4HL64S2HaS2G42HaS5USPLO2G51H2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2Ha".
eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply stack_dcli; cbn in Ha; lia]. }
split. { eapply ASTAT_agree; [exact AG| | exact AS]. intros a [Ha|Ha].
- unfold astat_app in Ha. left. right; left.
Ltac tryr lo hi := exists (lo, hi); split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto | cbn; lia].
repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end;
first [ tryr 0x5d5428 0x5d5430 | tryr 0x5f5740 0x5f5748 | tryr 0x5f5760 0x5f5770 | tryr 0x5f5520 0x5f5550
| tryr 0x5f5640 0x5f5650 | tryr 0x1343e0 0x1343e1 | tryr 0x5d4b90 0x5d4bc0 | tryr 0x9eed0 0x9eed1 | tryr 0x9b610 0x9b618
| tryr 0x5f5bc0 0x5f6000 | tryr 0x9e190 0x9e198 | tryr 0x9e0a8 0x9e138 | tryr 0x9e0a0 0x9e0a8 | tryr 0x9dfb0 0x9dfb8
| tryr 0x9fd50 0x9fd54 | tryr 0x9e1c0 0x9ee80 | tryr 0x9ee80 0x9ee88 | tryr 0x9fdf0 0x9fdf8 ].
- unfold astat_sh in Ha. destruct Ha as [Ha|Ha].
+ apply (ci_drv_sh' 0x20e60 0x22060); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity].
+ apply (ci_drv_sh' 0x9e1c0 0x9ee80); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity]. }
split. { destruct SE as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
eapply rw_cells_magree; [exact AG| exact Hc|]. intros a Ha. apply (ci_drv RSTDERR (RSTDERR + 232)); [unfold drv_img_ranges; cbn; tauto| cbn in Ha; lia]. }
split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. apply (ci_drv 0x5f5510 0x5f5518); [unfold drv_img_ranges; cbn; tauto| unfold ssp_guard in Ha; cbn in Ha; lia]. }
split. { eapply atrun_cells0_magree; [exact AG| | exact TR]. intros a [Ha|[Ha|[Ha|Ha]]].
- apply (ci_drv 0x5d4b90 0x5d4bc0); [unfold drv_img_ranges; cbn; tauto| unfold AINIT_FLAG in Ha; lia].
- unfold atx_addrA in Ha. destruct Ha as [Ha|[Ha|[Ha|Ha]]];
first [ apply (ci_drv 0x5f5520 0x5f5550); [unfold drv_img_ranges; cbn; tauto| lia]
| apply (ci_drv 0x5f5640 0x5f5650); [unfold drv_img_ranges; cbn; tauto| lia] ].
- apply (ci_drv 0x5d4b90 0x5d4bc0); [unfold drv_img_ranges; cbn; tauto| lia].
- apply (ci_drv 0x1343e0 0x1343e1); [unfold drv_img_ranges; cbn; tauto| lia]. }
split. { exact ((fun _ => I) CLI_CI). }
split. { eapply rodata_sh0_magree; [exact AG| | exact ROD]. intros a Ha. apply (ci_drv_sh 0x10000 0x20de0); [left; reflexivity| exact Ha| reflexivity| reflexivity]. }
split. { eapply rclean_magree; [exact AG| | exact RCS]. intros a Ha. destruct RCS as [(_ & HL64 & _) _]. unfold hull64 in HL64.
apply (stack_sh_dcli (r_rlo RSTK) (r_rhi RSTK)); [atop_facts; lia| lia| exact Ha]. }
split. { eapply rclean_magree; [exact AG| | exact RCB]. intros a Ha. unfold RBstdout in Ha. cbn [r_rlo r_rhi] in Ha.
apply (ci_drv_sh 0x5f5bc0 0x5f6000); [unfold drv_img_ranges; cbn; tauto| | reflexivity| reflexivity].
rewrite !shad_div in *. unfold ASHOFF in *. lia. }
split. { eapply rclean_magree; [exact AG| | exact RSG]. intros a Ha. unfold RSTG in Ha. cbn [r_rlo r_rhi] in Ha.
apply (ci_drv_sh 0x5c4b80 0x5d4bc0); [unfold drv_img_ranges; cbn; tauto| | reflexivity| reflexivity].
rewrite !shad_div in *. unfold ASHOFF in *. lia. }
split. { exists errv. eapply rw_cells_magree; [exact AG| exact ERR|]. intros a' Ha'. rewrite errno_addr_ATP in Ha'. cbn in Ha'.
apply (ci_drv 0x5d5428 0x5d5430); [unfold drv_img_ranges; cbn; tauto| lia]. }
eapply stdout_file_magree; [exact AG| | exact SOF]. intros a [Ha|Ha].
- apply (ci_drv RSTDOUT (RSTDOUT + 232)); [unfold drv_img_ranges; cbn; tauto| exact Ha].
- apply (ci_drv 0x5f5bc0 0x5f6000); [unfold drv_img_ranges; cbn; tauto| cbn in Ha |- *; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc AI USP16 USPLO USPHI LB HP HS AG"] Lemma astring_after_dpost : forall P str slack r, astring m P str slack r -> astring m' P str slack r.
Proof.
intros P str slack r AS. eapply astring_magree; [exact AG| | | exact AS].
- intros a Ha. apply stack_dcli. Local Ltac2 Set LiaHints.tbl := fun () => "0030>55187454681.386681591031.39 67739932984.3900000400500<S2HaSS5USPLO".
lia.
- intros a Ha. pose proof geo as (G1 & _). apply (stack_sh_dcli (usp + -128) (2^47)); [atop_facts; lia| unfold KEND; lia| exact Ha].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End AfterCallee.
Definition WOKb (hi : Z) (iv : Z * Z) : Prop :=
(ALO <= fst iv /\ snd iv <= hi)
\/ (fst iv = 0x5d542c /\ snd iv = 0x5d5430)
\/ (fst iv = RSTDERR /\ snd iv = RSTDERR + 232)
\/ ablk (fst iv) (snd iv)
\/ (ASTAGE <= fst iv /\ snd iv <= ASTAGE + 65536).
Definition WOK : Z * Z -> Prop := WOKb (usp + -128).
#[using="USP16 USPLO USPHI"] Lemma WOKb_outside : forall hi W a, ALO <= hi -> Forall (WOKb hi) W ->
(hi <= a
\/ (a < 0x5f7000 /\ ~ (0x5d542c <= a < 0x5d5430) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x5c4b90 <= a < 0x5d4b90))
\/ (0x7fff7000 <= a < 0x10007fff8000)) -> outside W a.
Proof.
pose proof geo as (G1 & G2 & G3 & _). unfold KHIGH in *. atop_facts.
intros hi. induction W as [|[lo1 hi1] W IH]; intros a Hhi HW Ha; cbn; [exact I|].
inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
unfold WOKb, ablk, ASTAGE, AIMG_HI, KLS in H1. cbn [fst snd] in H1. Local Ltac2 Set LiaHints.tbl := fun () => "0010>20525475421.3800000LS5USP165USPLO2G21H3Hhi2Ha2H1".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="USP16 USPLO USPHI"] Lemma WOK_outside : forall W a, Forall WOK W ->
(usp + -128 <= a
\/ (a < 0x5f7000 /\ ~ (0x5d542c <= a < 0x5d5430) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x5c4b90 <= a < 0x5d4b90))
\/ (0x7fff7000 <= a < 0x10007fff8000)) -> outside W a.
Proof. intros W a HW Ha. pose proof geo as (_ & G2 & _). eapply WOKb_outside; [| exact HW| exact Ha]. Local Ltac2 Set LiaHints.tbl := fun () => "0010>59719357545.29000004S2G2".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="USP16 USPLO USPHI"] Lemma WOKb_appW : forall hi W, hi <= usp + 24 -> Forall (WOKb hi) W -> appW W.
Proof.
pose proof geo as (G1 & G2 & G3 & _). unfold KHIGH in G3. atop_facts. intros hi W Hhi.
induction W as [|[lo1 hi1] W IH]; intros HW; [apply Forall_nil|]. inversion HW as [|x l H1 H2]; subst.
constructor; [| apply IH; exact H2]. unfold WOKb, ablk, ASTAGE, AIMG_HI, KLS, KHIGH in H1. cbn [fst snd] in H1 |- *. unfold KLOW, KHIGH. Local Ltac2 Set LiaHints.tbl := fun () => "0010>58393837457.3600000?S5USPLO2G21H2H1".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="USP16 USPLO USPHI"] Lemma ABASE_of_parts : forall hi W m m' so, ALO <= hi <= usp + 24 -> Forall (WOKb hi) W -> munch W m m' -> wmono bsegs m m' ->
ASTAT m -> rw_cells bsegs m ssp_guard [C8 canary] -> atrun_cells0 m -> harness_invA m -> rodata_sh0 m ->
rclean m RSTK -> rclean m RBstdout -> rclean m RSTG -> stdout_file m so ->
stk bsegs m' ALO (usp + -128) -> mem_inv bsegs m' -> AMFRAME m' -> stderr_wfile0 m' ->
(exists errv, rw_cells bsegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
ABASE so m'.
Proof.
intros hi W m m' so Hhi HW MU WM AS GU TR HI ROD RCS RCB RSG SOF ST' MI' FR' SE' ERR'.
pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG. Local Ltac2 Set LiaHints.tbl := fun () => "0050>13076082658.5714030124957.5735527003848.5343103070567.569302149080.57 00000400800=00B00FS2HaS2HaS3HhiS3HhiS2Ha".
pose proof (WOKb_appW hi W ltac:(lia) HW) as AW.
assert (OUT : forall a, (hi <= a \/ (a < 0x5f7000 /\ ~ (0x5d542c <= a < 0x5d5430) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x5c4b90 <= a < 0x5d4b90))
\/ (0x7fff7000 <= a < 0x10007fff8000)) ->
(fun x => outside W x) a) by (intros a Ha; eapply WOKb_outside; [| eassumption| exact Ha]; lia).
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
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="USP16 USPLO USPHI"] Lemma ABASE_munch : forall W m m' so, ABASE so m -> Forall WOK W -> munch W m m' -> wmono bsegs m m' ->
mem_inv bsegs m' -> stk bsegs m' ALO (usp + -128) -> stderr_wfile0 m' ->
(exists errv, rw_cells bsegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
ABASE so m'.
Proof.
intros W m m' so (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & ERR & SOF) HW MU WM MI' ST' SE' ERR'.
pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>19422392943.5660805687064.54000004008S2HaS2G2".
eapply (ABASE_of_parts (usp + -128)); try eassumption; [lia|].
unfold AMFRAME in *. eapply rw_cells_magree; [eapply magree_of_munch; [exact MU| exact WM]| exact FR|].
intros a Ha. apply WOK_outside; [exact HW|]. cbn in Ha. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="USP16 USPLO USPHI"] Lemma astring_munch : forall hi W m m' P str slack r, ALO <= hi <= usp + 24 -> Forall (WOKb hi) W -> munch W m m' -> wmono bsegs m m' ->
astring m P str slack r -> astring m' P str slack r.
Proof.
intros hi W m m' P str slack r Hhi HW MU WM AS. pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
pose proof (astring_facts _ _ _ _ _ AS) as (F1 & _).
destruct AS as (BY & HF & SL & LEN & LO & RC & IR & RLO). pose proof (magree_of_munch bsegs _ _ _ MU WM) as AG.
pose proof (bytes_at_bound _ _ _ _ BY) as B. rewrite length_app, zb_length in B. cbn [length] in B.
pose proof (rclean_shclean _ _ RC) as (_ & HUL & _). unfold hull64, KEND in HUL. unfold inreg in IR.
unfold astring. repeat match goal with |- _ /\ _ => split end; try assumption.
- eapply bytes_at_magree; [exact AG | exact BY |]. intros a Ha. rewrite length_app, zb_length in Ha. cbn [length] in Ha.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>14030124957.5516087836840.9743103070567.5500000L01201<S5USPLO3Hhi2IR2F11B3HUL2Ha1HS5USPLO3RLO1B3HUL2Ha1H2H02H12H52H63H10S3Hhi1B2Ha".
eapply WOKb_outside; [| exact HW|]; unfold zlength, KHIGH in *; lia.
- eapply rclean_magree; [exact AG | | exact RC]. intros a Ha. eapply WOKb_outside; [| exact HW|]; [lia|]. right; right.
rewrite !shad_div in Ha. unfold ASHOFF in Ha. unfold KHIGH, KEND in *. atop_facts. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="usp"] Lemma exit_relro_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m ->
rw_cells bsegs m 0x9a5d0 [C8 (Z_to_bv 64 0x993a8); C8 (Z_to_bv 64 0x99398)]
/\ rw_cells bsegs m 0x99398 [C8 (Z_to_bv 64 0x81544); C8 (Z_to_bv 64 0x31200)]
/\ rw_cells bsegs m 0x998e0 [C8 (Z_to_bv 64 0x89310); C8 (Z_to_bv 64 0)]
/\ rw_cells bsegs m 0x9a590 [C8 (Z_to_bv 64 0x9e1c0); C8 (Z_to_bv 64 0x9ee80)]
/\ rw_cells bsegs m 0x99930 [C8 (Z_to_bv 64 0x9b778)]
/\ rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)].
Proof.
intros L RNG st LB m AH. unfold got_ssp, ssp_guard.
Ltac relro_tac AH bs :=
eapply rw_cells_recast;
[ apply (rw_cells_image0 bsegs _ _ bs);
[ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply (AI_relro AI _ _ _ _ _ AH); rewrite ?length_app, ?length_le8 in Ha; unfold ARELRO_LO, ARELRO_HI; lia
| vm_compute; reflexivity | lia | rewrite ?length_app, ?length_le8; lia ]
| cbn; repeat split; exact I | reflexivity | reflexivity ].
Local Ltac2 Set LiaHints.tbl := fun () => "00=0>12772688141.3014501757590.302253783886.30 36335627982.3040058634958.3042710925846.3044517006742.3045254569351.3250659936718.3057139362966.3061066661389.3061568543126.3065997727382.3000000100200300400500600700;00<00=00>00?00@SSSSSSSS2HaSSSSS".
split; [relro_tac AH (le8 (Z_to_bv 64 0x993a8) ++ le8 (Z_to_bv 64 0x99398))|].
split; [relro_tac AH (le8 (Z_to_bv 64 0x81544) ++ le8 (Z_to_bv 64 0x31200))|].
split; [relro_tac AH (le8 (Z_to_bv 64 0x89310) ++ le8 (Z_to_bv 64 0))|].
split; [relro_tac AH (le8 (Z_to_bv 64 0x9e1c0) ++ le8 (Z_to_bv 64 0x9ee80))|].
split; [relro_tac AH (le8 (Z_to_bv 64 0x9b778))| relro_tac AH (le8 (Z_to_bv 64 0x5f5510))].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="usp"] Lemma mdtor_rt_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rw_cells bsegs m 0x9fd50 [C4 (Z_to_bv 64 1)] -> mdtor_rt m.
Proof.
intros L RNG st LB m AH RG. pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT. unfold artcells in RT. decompose [and] RT.
destruct (exit_relro_of_aheap _ _ _ _ _ AH) as (_ & _ & _ & _ & X5 & _).
unfold mdtor_rt. repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.
#[using="USP16 USPLO USPHI"] Lemma aat_exit_intro : forall (code : Z) (s : APS) L (LB : list ablock) (SP : Z) RNG
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
split; [reflexivity|]. Local Ltac2 Set LiaHints.tbl := fun () => "00<0?21530739642.10930031366090.1093643202838.109 45125558529.10948266967333.1095102311775.109 63161793631.10964653155551.10966474373727.10967359229898.1097110091119.109 8206433427.109 00000400D00H00M00U00V00W00X00Y00Z00[00\S2HTS5USPLO3SPR2G41HS2HTS3SPRS3SPR2G4SSSSFFF".
rewrite !unsigned_lit by lia.
split. { unfold mdtor_pre. repeat match goal with |- _ /\ _ => split end; try assumption; eexists; eassumption. }
repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try lia.
all: try (exists reg; exact AX).
- eapply rng_sub'; [exact RSTK'| lia].
- unfold MDTOR_W. repeat (apply Forall_cons; [cbn [fst snd]|]); [..| apply Forall_nil].
all: first [ eapply rng_sub'; [exact RIMG| lia] | eapply rng_sub'; [exact RIMSH| lia] ].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="USP16 USPLO USPHI"] Lemma amain_return : forall (code : Z) (s : APS) L (LB : list ablock) RNG
(x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
AMFRAME m -> stk bsegs m ALO (usp + -128) -> ASTAT m -> AHEAP AI L RNG (aps_m s) LB m ->
stdout_file m (aps_so s) -> stderr_file m -> rw_cells bsegs m ssp_guard [C8 canary] -> mem_inv bsegs m -> 0 < TID < 4194304 ->
rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
evtF bsegs RNG (aat_exit code s RNG)
(MS (mkR x1 (Z_to_bv 64 (usp + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x80a7c) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR ST AS AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0.
pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
unfold AMFRAME, ASTAGE2_RET in FR.
Local Ltac2 Set LiaHints.tbl := fun () => "00I0>11164420964.8412453600615.8122468534238.762546095281.84 37045569201.8238005200817.8239417202602.7543168340711.8143597027941.8344466171110.8244894727268.8444925642556.7647179659185.8552405051364.7654065164209.8554599870385.8559725769686.7662013604854.8062030059274.7662418886577.8467692047537.838179171302.82 8482228913.83 9472770533.83 9866592612.84 00000400800900:00;00<00=00A00E00I00M00N00O00S00T00U00Y00Z00[00\00]00a00b00f00jS2G2S2G2FSSSSS2G2S2G2S2G2S2G2SSS2G2SSS2G2SSSSS2G2SS2G2S2G2".
do 11 zstep. release_frame FR ST (usp + -48). zstep.
replace (ret_pc (Z_to_bv 64 0x88d2c)) with (Z_to_bv 64 0x88d2c) by (symmetry; rpc).
zstep.
apply evtF_done. unfold AEXIT_PC.
eapply aat_exit_intro; first [eassumption | lia | unfold MDTOR_DEPTH; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="USP16 USPLO USPHI"] Lemma aexit2_tail : forall (s : APS) L (LB : list ablock) RNG
(x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
stk bsegs m ALO (usp + -128) -> ASTAT m -> AHEAP AI L RNG (aps_m s) LB m ->
stdout_file m (aps_so s) -> stderr_file m -> rw_cells bsegs m ssp_guard [C8 canary] -> mem_inv bsegs m -> 0 < TID < 4194304 ->
rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
evtF bsegs RNG (aat_exit 2 s RNG)
(MS (mkR x1 (Z_to_bv 64 (usp + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x80b08) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST AS AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0.
pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
zstep. zstep.
apply evtF_done. unfold AEXIT_PC.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>2031093052.76 22468534238.7652405051364.76000001002006SFS2G2".
eapply aat_exit_intro; first [eassumption | lia | unfold MDTOR_DEPTH; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CTX.
End CANSEC1.
