(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib DrvAgree.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg F_syscalls MonadF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Ltac sort_lits :=
  repeat (match goal with H : rw_cells bsegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells bsegs _ (Zpos ?p') _ |- _ =>
                     lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
            then fail
            else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
          end); sf_unhide.
Ltac hstep := sort_lits; zstep; fix_lit_store.
(* [comment removed for export] *)
Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.
Ltac astep := hstep; try (first [if_true | if_false]).
Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition APATEXIT : Z := 0x88a14.       (* [comment removed for export] *)
Definition APATX : Z := 0x5f4020.         (* [comment removed for export] *)
Definition APATX_CALLFN : Z := 0x88ad8.   (* [comment removed for export] *)
Definition APNEED_LOCKS : Z := 0x5f4263.  (* [comment removed for export] *)
Definition ACOV_HOOK : Z := 0x6f1f4.      (* [comment removed for export] *)
Definition ACOV_FLAG : Z := 0x132ee0.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition APEXIT_GUARD : Z := 0x7fbbc.   (* [comment removed for export] *)
Definition APAEF_INCB : Z := 0x5d3694.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atx_cellsA (slot f1 a1 : Z) (m : mem) : Prop :=
  rw_cells bsegs m 0x5f4020 [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m 0x5f4024 [C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0x5f4028 [C4 (Z_to_bv 64 slot)]
  /\ rw_cells bsegs m 0x5f4030 [C8 (Z_to_bv 64 0x5f4038)]
  /\ rw_cells bsegs m 0x5f4038 [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0x5f4040 [C8 (Z_to_bv 64 APATX_CALLFN)]
  /\ rw_cells bsegs m 0x5f4140 [C8 (Z_to_bv 64 ACOV_HOOK)]
  /\ rw_cells bsegs m 0x5f4048 [C8 (Z_to_bv 64 f1)]
  /\ rw_cells bsegs m 0x5f4148 [C8 (Z_to_bv 64 a1)].

(* [comment removed for export] *)
Definition atx_stateA (reg : bool) (m : mem) : Prop :=
  atx_cellsA (if reg then 2 else 1) (if reg then APATX_CALLFN else 0) (if reg then APEXIT_GUARD else 0) m
  /\ rw_cells bsegs m APAEF_INCB [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m ACOV_FLAG [C1 (Z_to_bv 8 0)].

Definition atx_addrA (a : Z) : Prop :=
  (0x5f4020 <= a < 0x5f4021)%Z \/ (0x5f4024 <= a < 0x5f402c)%Z \/ (0x5f4030 <= a < 0x5f4050)%Z \/ (0x5f4140 <= a < 0x5f4150)%Z.
Definition atx_state_addrA (a : Z) : Prop := atx_addrA a \/ (0x5d3694 <= a < 0x5d3695)%Z \/ (0x132ee0 <= a < 0x132ee1)%Z.

Lemma atx_cellsA_agree : forall (P : Z -> Prop) m m' slot f1 a1,
  magree bsegs P m m' -> (forall a, atx_addrA a -> P a) -> atx_cellsA slot f1 a1 m -> atx_cellsA slot f1 a1 m'.
Proof.
  intros P m m' slot f1 a1 AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). unfold atx_cellsA.
  Ltac agx AG HP A := eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold atx_addrA in *; cbn in Ha; lia].
  Local Ltac2 Set LiaHints.tbl := fun () => "0010>64235928772.19000004S2Ha".
split; [agx AG HP A1|]. split; [agx AG HP A2|]. split; [agx AG HP A3|]. split; [agx AG HP A4|].
  split; [agx AG HP A5|]. split; [agx AG HP A6|]. split; [agx AG HP A7|]. split; [agx AG HP A8| agx AG HP A9].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma atx_stateA_agree : forall (P : Z -> Prop) m m' reg,
  magree bsegs P m m' -> (forall a, atx_state_addrA a -> P a) -> atx_stateA reg m -> atx_stateA reg m'.
Proof.
  intros P m m' reg AG HP (AX & CB & CF). split; [| split].
  - eapply atx_cellsA_agree; [exact AG| intros a Ha; apply HP; left; exact Ha| exact AX].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0020>5400879776.11 60677049120.11000004008S2HaS2Ha".
eapply rw_cells_magree; [exact AG| exact CB| intros a Ha; apply HP; right; left; unfold APAEF_INCB in *; cbn in Ha; lia].
  - eapply rw_cells_magree; [exact AG| exact CF| intros a Ha; apply HP; right; right; unfold ACOV_FLAG in *; cbn in Ha; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma atx_stateA_munch : forall W m m' reg,
  munch W m m' -> wmono bsegs m m' -> (forall a, atx_state_addrA a -> outside W a) -> atx_stateA reg m -> atx_stateA reg m'.
Proof. intros W m m' reg MU WM HW. apply (atx_stateA_agree _ _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition patexit_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo g : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x5f4028, 0x5f402c); (0x5f4048, 0x5f4050); (0x5f4148, 0x5f4150)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ atx_cellsA 2 APATX_CALLFN g m'.

#[using="Type"] Lemma patexit_specA : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo g : Z),
  stk bsegs m lo (bv_unsigned sp) ->
  atx_cellsA 1 0 0 m ->
  rw_cells bsegs m APNEED_LOCKS [C1 (Z_to_bv 8 0)] ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 g -> (0 <= g < 2^64)%Z ->
  (lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
  evtF bsegs RNG (patexit_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo g m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APATEXIT) fc None m (seg_rom bsegs)).
Proof.
  intros until g. intros ST (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9) NL MI -> Hg LO KH RSTK RIMG.
  unfold APNEED_LOCKS, APATEXIT, APATX_CALLFN, ACOV_HOOK in *. pose proof KH as KH'. unfold KHIGH in KH'.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x5f4028, 0x5f402c); (0x5f4048, 0x5f4050); (0x5f4148, 0x5f4150)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  Local Ltac2 Set LiaHints.tbl := fun () => "01n0>100583406.67  10279686709.7410600373102.6911382190574.6711716686062.701212764730.74 13651802606.6713652894266.7214290588398.7014993016302.6915552782733.6916577348149.7216577716558.6917399173998.6917440010734.6717737863790.6917776320431.6817962199098.691800609155.69 18276986478.7019715914222.671994914414.69 20148087866.6920313996398.6921659337070.6922133345850.6922389541692.6723783395190.6723806169710.6924638473347.6924638473347.7024812739566.6925271559662.6926961506542.7027361570160.6927907070492.6128417259964.6929013669434.7429655979962.6929889014842.7430876851182.6931357318714.7431378308326.6032638227566.693309735918.67 33427435470.6933583088186.7233680001082.7033924000758.6733964601038.6934430152252.7034466450490.6936083910202.7236115622446.6936115622447.6837218512752.7238230178030.7040059657198.694038645178.72 40457739452.6940597249904.7440647629038.7042930927674.6943059266230.5843091392750.7043299019630.694360033082.69 43959694190.6943987951406.6943988483203.6743988483203.6844195543534.6744253452910.694509240205.72 45221239098.6945848756903.6746468661564.6948654615790.6949103592506.7249649769127.7050693720814.7051324249070.6951711223320.6052105090727.6952398535994.7252567164907.6752567164907.6952567164907.7052567164907.7252567164907.7453326475118.6753767577775.6854030706746.6954243526019.6956185332718.69563227834.69  56341343290.74563780493.74  57745675194.6959415204078.7059650966842.7460471841134.6960805654074.6960858483367.6961674577390.6962019383790.6762245250030.6962879821877.6963235321900.6663235321900.6763305555623.6963393662522.726402560570.74 64307395438.6964650279534.6964788652110.7064997134979.7065097823086.6965522451898.7466242362426.7268454250042.748583720762.67 8901816942.69 9109202490.72 9163131726.67 9333008750.69 00000800@00H00P00X00Y00a00b00j01201301;01C01K01S01[01_01`01a01i02102902:02B02J02K02O02P02X02Y02Z02b02j03203303703;03<03=03>03F03G03H03P03X03`03a03f03g03o04304404504904=04>04F04N04O04S04T04\04]04a04i05105205:05>05?05@05H05P05Q05V05W05[05c05d05e05m06506606706806906:06;06<06=06E06I06J06K06S06X06Y06Z06_06g06h07007107207:07B07J07R07V07Z07[07\07]07e07m08508608>08?08@08A08F08N08O08W08_S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'SS2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LOSSS2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'S2LO3KH'SS2HBSS2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'SS2LOS2HBSSSS2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'SS3RSPSS2LO3KH'S2HBSSS2LOS2LOSS2LO3KH'S2LO3KH'SS2HBSS2LO3KH'SS2LOS2LO3KH'S2LO3KH'SS2LO3KH'S2LOSSS2LO3KH'S2LO3KH'SS3RSPSS2HBS2LO3KH'SSS2LO3KH'S2LO3KH'SSSSSSSSS2LO3KH'S2LOSSS2LO3KH'S3RSPSSS3RSPS2LO3KH'SS2LO3KH'SSS2LO3KH'S2LO3KH'S2LO3KH'S2LO3KH'S2LOS2LOSSSS2LO3KH'S2LO3KH'S2LO3KH'SS2LO3KH'SSSS3RSPS2LO3KH'SS2LO3KH'S2LO3KH'".
carve_frame 48%nat ST.
  (* [comment removed for export] *)
  steps_to 0x92c10%Z.
  (* [comment removed for export] *)
  hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
  steps_to 0x88a44%Z.
  (* [comment removed for export] *)
  hstep. hstep. hstep. if_false.
  (* [comment removed for export] *)
  hstep. hstep. if_true.
  (* [comment removed for export] *)
  hstep. try replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  hstep. hstep. if_true.
  (* [comment removed for export] *)
  steps_to 0x92e98%Z.
  (* [comment removed for export] *)
  hstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
  hstep. if_false. hstep.
  (* [comment removed for export] *)
  steps_to 0x88ad0%Z.
  release_frame FR ST (bv_unsigned sp). astep. astep.
  unfold patexit_postA, atx_cellsA, APATX_CALLFN, ACOV_HOOK. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
