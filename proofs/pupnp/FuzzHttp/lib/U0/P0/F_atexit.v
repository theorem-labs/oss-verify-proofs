From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Startup_lib.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Agree.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
Definition RATEXIT : Z := 0x17c7c.
Definition RATX : Z := 0x5b860.
Definition RATX_CALLFN : Z := 0x17d40.
Definition RATX_NEED_LOCKS : Z := 0x5baab.
Definition REXIT_GUARD : Z := 0x13f44.
Definition RAEF_INCB : Z := 0x3b6d4.
Definition atx_cells (head slot f0 a0 : Z) (m : word -> option byte) : Prop :=
rw_cells rsegs m 0x5b860 [C1 (Z_to_bv 8 0)]
/\ rw_cells rsegs m (0x5b864) [C4 (Z_to_bv 64 0)]
/\ rw_cells rsegs m (0x5b868) [C4 (Z_to_bv 64 slot)]
/\ rw_cells rsegs m (0x5b870) [C8 (Z_to_bv 64 head)]
/\ rw_cells rsegs m (0x5b878) [C8 (Z_to_bv 64 0)]
/\ rw_cells rsegs m (0x5b880) [C8 (Z_to_bv 64 f0)]
/\ rw_cells rsegs m (0x5b980) [C8 (Z_to_bv 64 a0)].
Definition atx_state (reg : bool) (m : word -> option byte) : Prop :=
atx_cells (if reg then 0x5b878 else 0) (if reg then 1 else 0) (if reg then RATX_CALLFN else 0) (if reg then REXIT_GUARD else 0) m
/\ rw_cells rsegs m RAEF_INCB [C1 (Z_to_bv 8 0)].
Definition atx_addr (a : Z) : Prop :=
(0x5b860 <= a < 0x5b861)%Z \/ (0x5b864 <= a < 0x5b86c)%Z \/ (0x5b870 <= a < 0x5b888)%Z \/ (0x5b980 <= a < 0x5b988)%Z.
Definition atx_state_addr (a : Z) : Prop := atx_addr a \/ (RAEF_INCB <= a < RAEF_INCB + 1)%Z.
Lemma atx_cells_agree : forall (P : Z -> Prop) m m' head slot f0 a0,
agree_on rsegs P m m' -> (forall a, atx_addr a -> P a) -> atx_cells head slot f0 a0 m -> atx_cells head slot f0 a0 m'.
Proof.
intros P m m' head slot f0 a0 AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold atx_cells.
Ltac agx AG HP A := eapply rw_cells_agree; [exact AG| exact A| intros a Ha; apply HP; unfold atx_addr, RATX in *; cbn in Ha; lia].
split; [agx AG HP A1|]. split; [agx AG HP A2|]. split; [agx AG HP A3|]. split; [agx AG HP A4|].
split; [agx AG HP A5|]. split; [agx AG HP A6| agx AG HP A7].
Qed.
Lemma atx_state_agree : forall (P : Z -> Prop) m m' reg,
agree_on rsegs P m m' -> (forall a, atx_state_addr a -> P a) -> atx_state reg m -> atx_state reg m'.
Proof.
intros P m m' reg AG HP [AX CB]. split.
- eapply atx_cells_agree; [exact AG| intros a Ha; apply HP; left; exact Ha| exact AX].
-
eapply rw_cells_agree; [exact AG| exact CB| intros a Ha; apply HP; right; unfold RAEF_INCB in *; cbn in Ha; lia].
Qed.
Definition ratexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo g : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x5b868, 0x5b86c); (0x5b870, 0x5b878); (0x5b880, 0x5b888); (0x5b980, 0x5b988)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ atx_cells (0x5b878) 1 RATX_CALLFN g m'.
Lemma ratexit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo g : Z),
stk rsegs m lo (bv_unsigned sp) ->
atx_cells 0 0 0 0 m ->
rw_cells rsegs m RATX_NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
mem_inv rsegs m ->
a0 = Z_to_bv 64 g -> (0 <= g < 2^64)%Z ->
(lo <= bv_unsigned sp - 48)%Z -> (0x5d000 <= lo)%Z ->
evt rsegs (ratexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo g m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RATEXIT) fc None m (seg_rom rsegs)).
Proof.
intros until g. intros ST (X1 & X2 & X3 & X4 & X5 & X6 & X7) NL MI -> Hg LO LOLO.
unfold RATX, RATX_NEED_LOCKS, RATEXIT in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x5b868, 0x5b86c); (0x5b870, 0x5b878); (0x5b880, 0x5b888); (0x5b980, 0x5b988)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
carve_frame 48%nat ST.
steps_to 0x251dc%Z.
lstep. lstep. lstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. lstep.
steps_to 0x17cac%Z.
lstep. lstep. lstep. if_false.
lstep. lstep. if_false. lstep. lstep.
lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
lstep. lstep. if_true.
steps_to 0x25464%Z.
lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
lstep. if_false. lstep.
steps_to 0x17d38%Z.
release_frame FR ST (bv_unsigned sp). astep. astep.
unfold ratexit_post, atx_cells, RATX, RATX_CALLFN. sys_finish.
Qed.
