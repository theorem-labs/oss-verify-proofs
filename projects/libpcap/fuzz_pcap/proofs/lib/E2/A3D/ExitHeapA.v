(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface AFake_arep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AInstanceF__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.AInstanceF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require DrvKitA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require F_module_dtorA ExitAllA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_module_dtorA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitAllA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition EXIT_CI_KEEP : list (Z * Z) :=
  [(0xa71d0, 0xa71d8); (0xa9db0, 0xaaf30); (0xaaf40, 0xaaf48); (0xaaf90, 0xaaf91); (0xabe10, 0xabe14); (0xabeb0, 0xabeb8); (0x1404a0, 0x1404a1);
   (0x5e0ca0, 0x5e0ca1); (0x601828, 0x60182c)].     (* [comment removed for export] *)
Lemma exit_ci_keep_ok : ci_okb EXIT_CI_KEEP = true.
Proof. vm_compute. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

Definition exit_ci (t : Z) (m : amem) : Prop :=
     rw_cells asegs m (ATPv + -168) [C4 (Z_to_bv 64 t)]
  /\ rw_cells asegs m 0x601828 [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0x1404a0 [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0xaaf90 [C1 (Z_to_bv 8 0)]
  /\ (exists dso : word, rw_cells asegs m 0xa71d0 [C8 dso])
  /\ (0 < t < 4194304)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xabe10 [C4 (Z_to_bv 64 1)]
  /\ rw_cells asegs m 0xaaf40 [C8 (Z_to_bv 64 1)]
  /\ rw_cells asegs m 0xabeb0 [C8 (Z_to_bv 64 0)]
  /\ descs_at m 0xa9db0 GD69
  /\ rw_cells asegs m 700144 [C8 (Z_to_bv 64 0x5e0c80); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 0x16fb6);
                                C8 (Z_to_bv 64 0x21200); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x5e0ca0)]
  /\ (exists b, rw_cells asegs m 0x5e0ca0 [C1 b])
  /\ Forall (gd_shw m) GD69 /\ wr_at asegs m (shd 0x5e0c80) (shn 32) /\ wr_at asegs m (shd 0xa9db0) (shn 4480).

(* [comment removed for export] *)
#[using="Type"] Lemma relro_pair : forall (m : amem) A v1 v2,
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  ARELRO_LO <= A -> A + 16 <= ARELRO_HI ->
  rw_bytes_b asegs A (le8 (Z_to_bv 64 v1)) = true -> rw_bytes_b asegs (A + 8) (le8 (Z_to_bv 64 v2)) = true ->
  rw_cells asegs m A [C8 (Z_to_bv 64 v1); C8 (Z_to_bv 64 v2)].
Proof.
  intros m A v1 v2 R LO HI B1 B2. apply rw_cells_cons.
  - apply relro_word; [exact R| exact LO| lia| exact B1].
  - cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ]. apply relro_word; [exact R| lia| lia| exact B2].
Qed.

#[using="Type"] Theorem exit_statics_of_heap : forall (H : aholes) L RNG st LB (m : amem) t reg,
  AHEAP_P H L RNG st LB m -> exit_ci t m -> atx_cells reg 0 m -> exit_statics m.
Proof.
  intros H L RNG st LB m t reg AH EC ATXC.
  pose proof (AHEAP_P_relro H L RNG st LB m AH) as RO.
  (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). (nd_pre AR 3%nat; intros _ RT _; nd_post).
  (nd_pre RT 24%nat; intros R1 R2 R3 _ _ R6 _ _ _ _ R11 R12 _ _ R15 _ _ _ _ _ _ _ R23 _; nd_post).
  (nd_pre EC 15%nat; intros TID EXL COV FINZ DSO Ht RGL FLG MTX DA D69 OD SH SH69 SHT; nd_post).
  assert (GF : rw_cells asegs m 0xa6190 [C8 (Z_to_bv 64 0xa4f40); C8 (Z_to_bv 64 0xa4f30)])
    by (apply relro_pair; [exact RO| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity| vm_compute; reflexivity]).
  assert (FA : rw_cells asegs m 0xa4f30 [C8 (Z_to_bv 64 0x84c10); C8 (Z_to_bv 64 0x32a80)])
    by (apply relro_pair; [exact RO| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity| vm_compute; reflexivity]).
  assert (GCX : rw_cells asegs m 0xa5480 [C8 (Z_to_bv 64 0x946a8); C8 (Z_to_bv 64 0)])
    by (apply relro_pair; [exact RO| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity| vm_compute; reflexivity]).
  assert (GSS : rw_cells asegs m 0xa6148 [C8 (Z_to_bv 64 0xa9db0); C8 (Z_to_bv 64 0xaaf30)])
    by (apply relro_pair; [exact RO| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity| vm_compute; reflexivity]).
  split.
  - exists t, reg. unfold exit_cells. repeat (split; [assumption|]). exact Ht.
  - unfold mdtor_pre. split.
    { unfold mdtor_rt. repeat (split; [assumption|]). exact RGL. }
    repeat (split; [assumption|]). exact SHT.
Qed.

#[using="Type"] Lemma exit_ci_frame : forall t (m m' : amem) W,
  exit_ci t m -> munch W m m' -> wmono asegs m m' -> Forall (iv_clear ((ATPv + -168, ATPv + -164) :: EXIT_CI_KEEP)) W -> exit_ci t m'.
Proof.
  intros t m m' W EC MU WM HW.
  assert (K : forall k A n, In k ((ATPv + -168, ATPv + -164) :: EXIT_CI_KEEP) -> fst k <= A -> A + n <= snd k -> disjoint_from W A n)
    by (intros k A n Hk H1 H2; eapply keep_disjoint; eassumption).
  (nd_pre EC 15%nat; intros TID EXL COV FINZ (dso & DSO) Ht RGL FLG MTX DA D69 (ob & OD) SH SH69 SHT; nd_post).
  unfold exit_ci.
  Ltac trk K k := eapply rw_cells_transport; [eassumption | eassumption | eassumption | apply (K k); [unfold EXIT_CI_KEEP; keep_in| cbn; lia| cbn; lia]].
  split; [trk K (ATPv + -168, ATPv + -164)|]. split; [trk K (0x601828, 0x60182c)|].
  split; [trk K (0x1404a0, 0x1404a1)|]. split; [trk K (0xaaf90, 0xaaf91)|].
  split; [exists dso; trk K (0xa71d0, 0xa71d8)|]. split; [exact Ht|].
  split; [trk K (0xabe10, 0xabe14)|]. split; [trk K (0xaaf40, 0xaaf48)|]. split; [trk K (0xabeb0, 0xabeb8)|].
  split. { eapply descs_at_transport; [exact DA| exact MU| exact WM| apply (K (0xa9db0, 0xaaf30)); [unfold EXIT_CI_KEEP; keep_in| cbn; lia| cbn; lia]]. }
  split; [trk K (0xa9db0, 0xaaf30)|]. split; [exists ob; trk K (0x5e0ca0, 0x5e0ca1)|].
  split; [eapply gd_shw_transport; [exact SH| exact WM]|]. split; (eapply wr_at_transport; [eassumption| exact WM]).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma descs_at_pres : forall CI LB SP gs (m m' : amem) d iv, aheap_pres CI LB SP m m' -> In iv CI -> fst iv <= d -> d + 64 * Z.of_nat (length gs) <= snd iv ->
  descs_at m d gs -> descs_at m' d gs.
Proof.
  intros CI LB SP gs. induction gs as [|g gs IH]; intros m m' d iv HP Hin H1 H2 DA; cbn [descs_at] in *; [exact I|].
  destruct DA as [D DA]. cbn [length] in H2. split.
  - eapply aheap_pres_rw_cells; [exact HP| exact D|]. rewrite gd_cells_size. left. right. left. exists iv. split; [exact Hin| lia].
  - eapply (IH m m' (d + 64) iv HP Hin); [lia| lia| exact DA].
Qed.

#[using="Type"] Lemma gd_shw_pres : forall CI LB SP gs (m m' : amem), aheap_pres CI LB SP m m' -> Forall gd_ok gs -> Forall (gd_shw m) gs -> Forall (gd_shw m') gs.
Proof.
  intros CI LB SP gs m m' HP OK SH. apply Forall_forall. intros g Hg.
  pose proof (proj1 (Forall_forall _ _) OK g Hg) as OKg. pose proof (proj1 (Forall_forall _ _) SH g Hg) as SHg.
  destruct g as ((((beg, sz), swr), nm), md). unfold gd_shw in *. (nd_pre OKg 4%nat; intros AL SWR BLO BHI; nd_post).
  assert (SWRf : swr mod 8 = 0 /\ 0 < swr) by (clear -SWR; destruct SWR as [->|[->|[->| ->]]]; (split; [reflexivity| lia])).
  destruct SWRf as [SL SZ]. (pose proof (shadow_window beg swr AL SL SZ BLO BHI) as ndP__; nd_pre ndP__ 3%nat; intros S1 S2 S3; nd_post).
  eapply aheap_pres_imsh_wr_at; [exact HP| exact SHg| unfold AIMSH_LO, SHW_LO in *; lia| unfold AIMSH_LO, AIMSH_LEN, SHW_LO, SHW_LEN in *; lia].
Qed.

#[using="Type"] Lemma exit_ci_pres : forall CI LB SP t (m m' : amem),
  aheap_pres CI LB SP m m' ->
  Forall (fun k => exists iv, In iv CI /\ fst iv <= fst k /\ snd k <= snd iv) EXIT_CI_KEEP ->
  exit_ci t m -> exit_ci t m'.
Proof.
  intros CI LB SP t m m' HP COV EC.
  assert (KC : forall k A cs, In k EXIT_CI_KEEP -> fst k <= A -> A + Z.of_nat (cells_size cs) <= snd k -> rw_cells asegs m A cs -> rw_cells asegs m' A cs).
  { intros k A cs Hk H1 H2 HC. (nd_pre (proj1 (Forall_forall _ _) COV k Hk) 4%nat; intros iv Hin I1 I2; nd_post).
    eapply aheap_pres_rw_cells; [exact HP| exact HC|]. left. right. left. exists iv. split; [exact Hin| lia]. }
  (nd_pre EC 15%nat; intros TID EXL COV0 FINZ (dso & DSO) Ht RGL FLG MTX DA D69 (ob & OD) SH SH69 SHT; nd_post).
  unfold exit_ci.
  Ltac kc KC k := eapply (KC k); [unfold EXIT_CI_KEEP; keep_in| cbn; lia| cbn; lia| eassumption].
  split. { eapply aheap_pres_tls_rw_cells; [exact HP| exact TID| lia| cbn; lia]. }
  split; [kc KC (0x601828, 0x60182c)|].
 
  split; [kc KC (0x1404a0, 0x1404a1)|]. split; [kc KC (0xaaf90, 0xaaf91)|].
  split; [exists dso; kc KC (0xa71d0, 0xa71d8)|]. split; [exact Ht|].
  split; [kc KC (0xabe10, 0xabe14)|]. split; [kc KC (0xaaf40, 0xaaf48)|]. split; [kc KC (0xabeb0, 0xabeb8)|].
  split. { (nd_pre (proj1 (Forall_forall _ _) COV (0xa9db0, 0xaaf30) ltac:(unfold EXIT_CI_KEEP; keep_in)) 4%nat; intros iv Hin I1 I2; nd_post). cbn [fst snd] in I1, I2.
           eapply (descs_at_pres CI LB SP GD69 m m' 0xa9db0 iv HP Hin); [exact I1| change (Z.of_nat (length GD69)) with 69; lia| exact DA]. }
  split; [kc KC (0xa9db0, 0xaaf30)|]. split; [exists ob; kc KC (0x5e0ca0, 0x5e0ca1)|].
  split; [eapply gd_shw_pres; [exact HP| exact GD69_ok| exact SH]|].
  split; (eapply aheap_pres_imsh_wr_at; [exact HP| eassumption| vm_compute; discriminate| vm_compute; discriminate]).
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.AInstanceF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_module_dtorA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitAllA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition EXIT_CI_KEEP : list (Z * Z) :=
  [(0xa75b0, 0xa75b8); (0xaa190, 0xab310); (0xab340, 0xab348); (0xab390, 0xab391); (0xac210, 0xac214); (0xac2b0, 0xac2b8); (0x1408a0, 0x1408a1);
   (0x5e10a0, 0x5e10a1); (0x601c28, 0x601c2c)].     (* [comment removed for export] *)
Lemma exit_ci_keep_ok : ci_okb EXIT_CI_KEEP = true.
Proof. vm_compute. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

Definition exit_ci (t : Z) (m : amem) : Prop :=
     rw_cells asegs m (ATPv + -168) [C4 (Z_to_bv 64 t)]
  /\ rw_cells asegs m 0x601c28 [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0x1408a0 [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0xab390 [C1 (Z_to_bv 8 0)]
  /\ (exists dso : word, rw_cells asegs m 0xa75b0 [C8 dso])
  /\ (0 < t < 4194304)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xac210 [C4 (Z_to_bv 64 1)]
  /\ rw_cells asegs m 0xab340 [C8 (Z_to_bv 64 1)]
  /\ rw_cells asegs m 0xac2b0 [C8 (Z_to_bv 64 0)]
  /\ descs_at m 0xaa190 GD69
  /\ rw_cells asegs m 0xab2d0 [C8 (Z_to_bv 64 0x5e1080); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 0x16fb6);
                                C8 (Z_to_bv 64 0x21200); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x5e10a0)]
  /\ (exists b, rw_cells asegs m 0x5e10a0 [C1 b])
  /\ Forall (gd_shw m) GD69 /\ wr_at asegs m (shd 0x5e1080) (shn 32) /\ wr_at asegs m (shd 0xaa190) (shn 4480).

(* [comment removed for export] *)
#[using="Type"] Lemma relro_pair : forall (m : amem) A v1 v2,
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  ARELRO_LO <= A -> A + 16 <= ARELRO_HI ->
  rw_bytes_b asegs A (le8 (Z_to_bv 64 v1)) = true -> rw_bytes_b asegs (A + 8) (le8 (Z_to_bv 64 v2)) = true ->
  rw_cells asegs m A [C8 (Z_to_bv 64 v1); C8 (Z_to_bv 64 v2)].
Proof.
  intros m A v1 v2 R LO HI B1 B2. apply rw_cells_cons.
  - apply relro_word; [exact R| exact LO| lia| exact B1].
  - cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ]. apply relro_word; [exact R| lia| lia| exact B2].
Qed.

#[using="Type"] Theorem exit_statics_of_heap : forall (H : aholes) L RNG st LB (m : amem) t reg,
  AHEAP_P H L RNG st LB m -> exit_ci t m -> atx_cells reg 0 m -> exit_statics m.
Proof.
  intros H L RNG st LB m t reg AH EC ATXC.
  pose proof (AHEAP_P_relro H L RNG st LB m AH) as RO.
  (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). (nd_pre AR 3%nat; intros _ RT _; nd_post).
  (nd_pre RT 24%nat; intros R1 R2 R3 _ _ R6 _ _ _ _ R11 R12 _ _ R15 _ _ _ _ _ _ _ R23 _; nd_post).
  (nd_pre EC 15%nat; intros TID EXL COV FINZ DSO Ht RGL FLG MTX DA D69 OD SH SH69 SHT; nd_post).
  assert (GF : rw_cells asegs m 0xa6570 [C8 (Z_to_bv 64 0xa5320); C8 (Z_to_bv 64 0xa5310)])
    by (apply relro_pair; [exact RO| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity| vm_compute; reflexivity]).
  assert (FA : rw_cells asegs m 0xa5310 [C8 (Z_to_bv 64 0x84c9c); C8 (Z_to_bv 64 0x32ae8)])
    by (apply relro_pair; [exact RO| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity| vm_compute; reflexivity]).
  assert (GCX : rw_cells asegs m 0xa5860 [C8 (Z_to_bv 64 0x94a8c); C8 (Z_to_bv 64 0)])
    by (apply relro_pair; [exact RO| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity| vm_compute; reflexivity]).
  assert (GSS : rw_cells asegs m 0xa6528 [C8 (Z_to_bv 64 0xaa190); C8 (Z_to_bv 64 0xab310)])
    by (apply relro_pair; [exact RO| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity| vm_compute; reflexivity]).
  split.
  - exists t, reg. unfold exit_cells. repeat (split; [assumption|]). exact Ht.
  - unfold mdtor_pre. split.
    { unfold mdtor_rt. repeat (split; [assumption|]). exact RGL. }
    repeat (split; [assumption|]). exact SHT.
Qed.

#[using="Type"] Lemma exit_ci_frame : forall t (m m' : amem) W,
  exit_ci t m -> munch W m m' -> wmono asegs m m' -> Forall (iv_clear ((ATPv + -168, ATPv + -164) :: EXIT_CI_KEEP)) W -> exit_ci t m'.
Proof.
  intros t m m' W EC MU WM HW.
  assert (K : forall k A n, In k ((ATPv + -168, ATPv + -164) :: EXIT_CI_KEEP) -> fst k <= A -> A + n <= snd k -> disjoint_from W A n)
    by (intros k A n Hk H1 H2; eapply keep_disjoint; eassumption).
  (nd_pre EC 15%nat; intros TID EXL COV FINZ (dso & DSO) Ht RGL FLG MTX DA D69 (ob & OD) SH SH69 SHT; nd_post).
  unfold exit_ci.
  Ltac trk K k := eapply rw_cells_transport; [eassumption | eassumption | eassumption | apply (K k); [unfold EXIT_CI_KEEP; keep_in| cbn; lia| cbn; lia]].
  split; [trk K (ATPv + -168, ATPv + -164)|]. split; [trk K (0x601c28, 0x601c2c)|].
  split; [trk K (0x1408a0, 0x1408a1)|]. split; [trk K (0xab390, 0xab391)|].
  split; [exists dso; trk K (0xa75b0, 0xa75b8)|]. split; [exact Ht|].
  split; [trk K (0xac210, 0xac214)|]. split; [trk K (0xab340, 0xab348)|]. split; [trk K (0xac2b0, 0xac2b8)|].
  split. { eapply descs_at_transport; [exact DA| exact MU| exact WM| apply (K (0xaa190, 0xab310)); [unfold EXIT_CI_KEEP; keep_in| cbn; lia| cbn; lia]]. }
  split; [trk K (0xaa190, 0xab310)|]. split; [exists ob; trk K (0x5e10a0, 0x5e10a1)|].
  split; [eapply gd_shw_transport; [exact SH| exact WM]|]. split; (eapply wr_at_transport; [eassumption| exact WM]).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma descs_at_pres : forall CI LB SP gs (m m' : amem) d iv, aheap_pres CI LB SP m m' -> In iv CI -> fst iv <= d -> d + 64 * Z.of_nat (length gs) <= snd iv ->
  descs_at m d gs -> descs_at m' d gs.
Proof.
  intros CI LB SP gs. induction gs as [|g gs IH]; intros m m' d iv HP Hin H1 H2 DA; cbn [descs_at] in *; [exact I|].
  destruct DA as [D DA]. cbn [length] in H2. split.
  - eapply aheap_pres_rw_cells; [exact HP| exact D|]. rewrite gd_cells_size. left. right. left. exists iv. split; [exact Hin| lia].
  - eapply (IH m m' (d + 64) iv HP Hin); [lia| lia| exact DA].
Qed.

#[using="Type"] Lemma gd_shw_pres : forall CI LB SP gs (m m' : amem), aheap_pres CI LB SP m m' -> Forall gd_ok gs -> Forall (gd_shw m) gs -> Forall (gd_shw m') gs.
Proof.
  intros CI LB SP gs m m' HP OK SH. apply Forall_forall. intros g Hg.
  pose proof (proj1 (Forall_forall _ _) OK g Hg) as OKg. pose proof (proj1 (Forall_forall _ _) SH g Hg) as SHg.
  destruct g as ((((beg, sz), swr), nm), md). unfold gd_shw in *. (nd_pre OKg 4%nat; intros AL SWR BLO BHI; nd_post).
  assert (SWRf : swr mod 8 = 0 /\ 0 < swr) by (clear -SWR; destruct SWR as [->|[->|[->| ->]]]; (split; [reflexivity| lia])).
  destruct SWRf as [SL SZ]. (pose proof (shadow_window beg swr AL SL SZ BLO BHI) as ndP__; nd_pre ndP__ 3%nat; intros S1 S2 S3; nd_post).
  eapply aheap_pres_imsh_wr_at; [exact HP| exact SHg| unfold AIMSH_LO, SHW_LO in *; lia| unfold AIMSH_LO, AIMSH_LEN, SHW_LO, SHW_LEN in *; lia].
Qed.

#[using="Type"] Lemma exit_ci_pres : forall CI LB SP t (m m' : amem),
  aheap_pres CI LB SP m m' ->
  Forall (fun k => exists iv, In iv CI /\ fst iv <= fst k /\ snd k <= snd iv) EXIT_CI_KEEP ->
  exit_ci t m -> exit_ci t m'.
Proof.
  intros CI LB SP t m m' HP COV EC.
  assert (KC : forall k A cs, In k EXIT_CI_KEEP -> fst k <= A -> A + Z.of_nat (cells_size cs) <= snd k -> rw_cells asegs m A cs -> rw_cells asegs m' A cs).
  { intros k A cs Hk H1 H2 HC. (nd_pre (proj1 (Forall_forall _ _) COV k Hk) 4%nat; intros iv Hin I1 I2; nd_post).
    eapply aheap_pres_rw_cells; [exact HP| exact HC|]. left. right. left. exists iv. split; [exact Hin| lia]. }
  (nd_pre EC 15%nat; intros TID EXL COV0 FINZ (dso & DSO) Ht RGL FLG MTX DA D69 (ob & OD) SH SH69 SHT; nd_post).
  unfold exit_ci.
  Ltac kc KC k := eapply (KC k); [unfold EXIT_CI_KEEP; keep_in| cbn; lia| cbn; lia| eassumption].
  split. { eapply aheap_pres_tls_rw_cells; [exact HP| exact TID| lia| cbn; lia]. }
  split; [kc KC (0x601c28, 0x601c2c)|].
 
  split; [kc KC (0x1408a0, 0x1408a1)|]. split; [kc KC (0xab390, 0xab391)|].
  split; [exists dso; kc KC (0xa75b0, 0xa75b8)|]. split; [exact Ht|].
  split; [kc KC (0xac210, 0xac214)|]. split; [kc KC (0xab340, 0xab348)|]. split; [kc KC (0xac2b0, 0xac2b8)|].
  split. { (nd_pre (proj1 (Forall_forall _ _) COV (0xaa190, 0xab310) ltac:(unfold EXIT_CI_KEEP; keep_in)) 4%nat; intros iv Hin I1 I2; nd_post). cbn [fst snd] in I1, I2.
           eapply (descs_at_pres CI LB SP GD69 m m' 0xaa190 iv HP Hin); [exact I1| change (Z.of_nat (length GD69)) with 69; lia| exact DA]. }
  split; [kc KC (0xaa190, 0xab310)|]. split; [exists ob; kc KC (0x5e10a0, 0x5e10a1)|].
  split; [eapply gd_shw_pres; [exact HP| exact GD69_ok| exact SH]|].
  split; (eapply aheap_pres_imsh_wr_at; [exact HP| eassumption| vm_compute; discriminate| vm_compute; discriminate]).
Qed.
End CANSEC1.
End TwB.
