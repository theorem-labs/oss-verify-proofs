(* reloc-zl14c b522f5b2fa8f355f340ff9eaf1bf281c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim STree Monad Stdio Driver Adapter AsanCtrl AsanEmbed ProgA AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AUri_kit AHarness_iface F_syscalls StdioFiles Stdio_kit Stdio_iface F_printf_iface MonadF AExit F_module_dtor ADriver_iface AD_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
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

  (* an earlier development run 727298f3 (the development lead's ruling): the stack floor moves up to usp - 6144512, one byte inside
     ASTK = 6144513 (the stack known writable below sp, AS/MainEntry amain_at row c); 6144512 = 64 x 96008
     keeps ALO = usp mod 64. ATOP = usp - 8 MiB is unchanged. *)
  Definition ALO : Z := usp - 6144512.

  Definition AMFRAME (mm : amem) : Prop :=
    rw_cells asegs mm (usp + -128) [CB 8 J8; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 (Z_to_bv 64 ASTAGE2_RET)].

  (* [comment removed for export] *)
  Definition ASTAT (mm : amem) : Prop :=
       rw_cells asegs mm 0x65ba90 [C4 (Z_to_bv 64 TID)]                                 (* [comment removed for export] *)
    /\ rw_cells asegs mm 0x67bda8 [C4 (Z_to_bv 64 0)]                                   (* [comment removed for export] *)
    /\ (exists cdt thr sec tm1, rw_cells asegs mm 0x67bdc8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])  (* [comment removed for export] *)
    /\ rw_cells asegs mm 0x16a820 [C1 (Z_to_bv 8 0)]                                   (* [comment removed for export] *)
    /\ rw_cells asegs mm 0xd5310 [C1 (Z_to_bv 8 0)]                                   (* [comment removed for export] *)
    /\ (exists dso, rw_cells asegs mm 0xd1eb8 [C8 dso])                                (* [comment removed for export] *)
    /\ rw_cells asegs mm 0x67c230 [C8 (Z_to_bv 64 0)] /\ rw_cells asegs mm 0xd4a68 [C8 (Z_to_bv 64 RSTDIN)]  (* [comment removed for export] *)
    /\ rw_cells asegs mm RSTDIN stdin_cells                                          (* [comment removed for export] *)
    /\ rw_cells asegs mm 0xd4978 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells asegs mm 0xd4888 [C8 (Z_to_bv 64 RSTDERR)]  (* [comment removed for export] *)
    (* [comment removed for export] *)
    /\ rw_cells asegs mm 0xd6190 [C4 (Z_to_bv 64 1)]
    /\ rw_cells asegs mm 0xd52c0 [C8 (Z_to_bv 64 1)]
    /\ rw_cells asegs mm 0xd6230 [C8 (Z_to_bv 64 0)]
    /\ gdesc mm 0xd4aa0 0x22760 0x4 0x20 0x1d1e7 0x22780 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4ae0 0x22840 0x26 0x60 0x19a8f 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4b20 0x228a0 0x17 0x40 0x1fce7 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4b60 0x228e0 0x1b 0x40 0x21dea 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4ba0 0x22920 0x14 0x40 0x14bfa 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4be0 0x22960 0x19 0x40 0x13a96 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4c20 0x229a0 0x14 0x40 0x1e2fc 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4c60 0x229e0 0x13 0x40 0x19364 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4ca0 0x22a20 0x1d 0x40 0x1b40b 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4ce0 0x22a60 0x24 0x60 0x114ed 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4d20 0x22ac0 0x19 0x40 0x16dde 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4d60 0x22b00 0x1a 0x40 0x20fec 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4da0 0x22b40 0x25 0x60 0x114f4 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4de0 0x22ba0 0x1c 0x40 0x1ad1b 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4e20 0x22be0 0x16 0x40 0x20ff4 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4e60 0x22c20 0x1c 0x40 0x1f20c 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4ea0 0x22c60 0x16 0x40 0x1d1ec 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4ee0 0x22ca0 0x1e 0x40 0x1a517 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4f20 0x22ce0 0x15 0x40 0x1c92b 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4f60 0x22d20 0x17 0x40 0x11d18 0x22d60 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4fa0 0x22da0 0x400 0x500 0x15ef5 0x246a0 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd4fe0 0x232a0 0x1000 0x1400 0x1936b 0x246a0 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd5020 0x246e0 0x3e 0x60 0x11d20 0x25300 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd5060 0x24740 0x3e 0x60 0x1dbfb 0x25300 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd50a0 0x247a0 0x40 0x60 0x176a8 0x25300 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd50e0 0x24800 0x40 0x60 0x15eff 0x25300 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd5120 0x24860 0x800 0xa00 0x15482 0x25300 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd5160 0x25260 0x80 0xa0 0x11d34 0x25300 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd51a0 0x25340 0x1e 0x40 0x1d1e7 0x25400 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd51e0 0x25380 0x16 0x40 0x1fce7 0x25400 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd5220 0x253c0 0x1c 0x40 0x21dea 0x25400 (2^64 - 1)        (* [comment removed for export] *)
    /\ gdesc mm 0xd5260 0x60b000 0x40000 0x50000 0x1c924 0x22713 (2^64 - 1)        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc4ec [CB 4 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc508 [CB 12 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc514 [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc51c [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc524 [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc52c [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc534 [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc53c [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc544 [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc54c [CB 12 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc558 [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc560 [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc568 [CB 12 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc574 [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc57c [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc584 [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc58c [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc594 [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc59c [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc5a4 [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc90c [CB 320 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffca4c [CB 20 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc5b4 [CB 160 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc654 [CB 640 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc8dc [CB 12 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc8e8 [CB 12 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc8f4 [CB 12 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffc900 [CB 12 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffca68 [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffca70 [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x7fffca78 [CB 8 j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x800b9600 [CB (Z.to_nat 40960) j])        (* [comment removed for export] *)
    /\ (exists j, rw_cells asegs mm 0x80012954 [CB 256 j]).        (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition astat_app (a : Z) : Prop :=
       (0x65ba90 <= a < 0x65ba94) \/ (0x67bda8 <= a < 0x67bdb0) \/ (0x67bdc8 <= a < 0x67bdd8)
    \/ (0x16a820 <= a < 0x16a821) \/ (0xd5310 <= a < 0xd5311) \/ (0xd1eb8 <= a < 0xd1ec0)
    \/ (0x67c228 <= a < 0x67c248) \/ (0xd4a68 <= a < 0xd4a70) \/ (0xd4980 <= a < 0xd4a10) \/ (0xd4978 <= a < 0xd4980) \/ (0xd4888 <= a < 0xd4890)
    \/ (0xd6190 <= a < 0xd6194) \/ (0xd4aa0 <= a < 0xd52e8) \/ (0xd6230 <= a < 0xd6238).
  Definition astat_sh (a : Z) : Prop :=
       (0x7fffc4ec <= a < 0x7fffc4f0) \/ (0x7fffc508 <= a < 0x7fffca60) \/ (0x7fffc5b4 <= a < 0x7fffc8d4) \/ (0x7fffc8dc <= a < 0x7fffc90c) \/ (0x7fffca68 <= a < 0x7fffca80) \/ (0x800b9600 <= a < 0x800c3600) \/ (0x80012954 <= a < 0x80012a54).
  Definition astat_addr (a : Z) : Prop := astat_app a \/ astat_sh a.

  (* [comment removed for export] *)
  Lemma csz_cons : forall c cs, Z.of_nat (cells_size (c :: cs)) = Z.of_nat (csize c) + Z.of_nat (cells_size cs).
  Proof. intros. cbn [cells_size]. lia. Qed.
  Lemma csz_nil : Z.of_nat (cells_size []) = 0. Proof. reflexivity. Qed.
  Lemma csz_CB : forall n bs, Z.of_nat (csize (CB n bs)) = Z.of_nat n. Proof. reflexivity. Qed.
  Lemma csz_C8 : forall v, Z.of_nat (csize (C8 v)) = 8. Proof. reflexivity. Qed.
  Lemma csz_C4 : forall v, Z.of_nat (csize (C4 v)) = 4. Proof. reflexivity. Qed.
  Lemma csz_C2 : forall v, Z.of_nat (csize (C2 v)) = 2. Proof. reflexivity. Qed.
  Lemma csz_C1 : forall v, Z.of_nat (csize (C1 v)) = 1. Proof. reflexivity. Qed.
  Ltac csz_norm H := rewrite ?csz_cons, ?csz_nil, ?csz_CB, ?csz_C8, ?csz_C4, ?csz_C2, ?csz_C1 in H; rewrite ?Z2Nat.id in H by lia.

  Lemma gdesc_magree : forall (P : Z -> Prop) m m' d b sz szr nm mn odr,
    magree asegs P m m' -> (forall a, d <= a < d + 64 -> P a) -> gdesc m d b sz szr nm mn odr -> gdesc m' d b sz szr nm mn odr.
  Proof.
    intros P m m' d b sz szr nm mn odr AG HP [G1 G2]. split.
    - eapply rw_cells_magree; [exact AG | exact G1 | intros a Ha; apply HP; cbn in Ha; lia].
    - eapply rw_cells_magree; [exact AG | exact G2 | intros a Ha; apply HP; cbn in Ha; lia].
  Qed.

  Lemma ASTAT_agree : forall (P : Z -> Prop) m m', magree asegs P m m' -> (forall a, astat_addr a -> P a) -> ASTAT m -> ASTAT m'.
  Proof.
    intros P m m' AG HP ST. unfold ASTAT in *.
    Ltac tr1 AG HP := eapply rw_cells_magree; [exact AG | eassumption | intros a Ha; apply HP; unfold astat_addr, astat_app, astat_sh; try unfold stdin_cells in Ha; csz_norm Ha; unfold RSTDIN in Ha; lia].
    (* [comment removed for export] *)
    Ltac tr_lock AG HP H :=
      lazymatch type of H with
      | _ /\ _ => let HcL := fresh "HcL" in let HcR := fresh "HcR" in destruct H as [HcL HcR]; split; [clear HcR; tr_lock AG HP HcL | clear HcL; tr_lock AG HP HcR]
      | exists _, _ => let j := fresh "j" in let HcE := fresh "HcE" in destruct H as [j HcE]; exists j; tr_lock AG HP HcE
      | gdesc _ _ _ _ _ _ _ _ => eapply gdesc_magree; [exact AG | intros a Ha; apply HP; unfold astat_addr, astat_app; lia | exact H]
      | _ => eapply rw_cells_magree; [exact AG | exact H | intros a Ha; apply HP; unfold astat_addr, astat_app, astat_sh; try unfold stdin_cells in Ha; csz_norm Ha; unfold RSTDIN in Ha; lia]
      end.
    tr_lock AG HP ST.
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
  Hypothesis RSTK_hi : usp + -128 <= r_hi RSTK.
  Hypothesis RSTK_rlo : ATOP <= r_rlo RSTK.
  (* [comment removed for export] *)
  Hypothesis USP16 : usp mod 16 = 0.
  Hypothesis USPLO : ATOP + 8388608 <= usp.
  Hypothesis USPHI : usp + 24 <= 2^47.
  (* [comment removed for export] *)
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.
  Variable canary : word.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ABASE (so : stdout_st) (mm : amem) : Prop :=
    stk asegs mm ALO (usp + -128) /\ mem_inv asegs mm /\ AMFRAME mm /\ ASTAT mm
    /\ stderr_wfile0 mm /\ rw_cells asegs mm ssp_guard [C8 canary]
    /\ atrun_cells0 mm /\ harness_invA mm /\ rodata_sh0 mm /\ rclean mm RSTK /\ rclean mm RBstdout
    /\ rclean mm RSTG                                                      (* [comment removed for export] *)
    /\ (exists errv, rw_cells asegs mm (errno_addr (Z_to_bv 64 ATP)) [C4 errv])
    /\ stdout_file mm so.

  Lemma geo : ATOP <= ALO /\ ALO + 6144512 = usp /\ KHIGH <= ALO /\ usp + 24 <= 2^47 /\ usp mod 16 = 0.
  Proof. unfold ALO, KHIGH in *. repeat split; lia. Qed.

  Lemma errno_addr_ATP : errno_addr (Z_to_bv 64 ATP) = 0x65ba94.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Section AfterCallee.
    Variables (LB : list ablock) (m m' : amem).
    Hypothesis HP : aheap_pres CI LB (usp + -128) m m'.
    Hypothesis HS : astk_shadow_pres (usp + -128) m m'.
    Hypothesis HLB : forall b, In b LB -> 0x67e000 <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP.

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
    Lemma stack_dcli : forall a, usp + -128 <= a < 2^47 -> dcli CI LB (usp + -128) a.
    Proof. intros a Ha. left. left. lia. Qed.
    Lemma stack_sh_dcli : forall RLO RHI a, ATOP <= RLO -> RHI <= KEND -> shad RLO <= a < shad RHI -> dcli CI LB (usp + -128) a.
    Proof.
      intros RLO RHI a H1 H2 Ha. destruct (Z.lt_ge_cases a (shad (usp + -128))) as [LT|GE].
      - right. pose proof (shad_mono ATOP RLO H1). lia.
      - left. right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad]. left.
        rewrite !shad_div in *. unfold ASHOFF, KEND in *. Z.div_mod_to_equations. lia.
    Qed.

    Lemma ABASE_after_dpost : forall L RNG st LB' so, AHEAP AI L RNG st LB' m' -> mem_inv asegs m' -> stk asegs m' ALO (usp + -128) ->
      ABASE so m -> ABASE so m'.
    Proof.
      intros L RNG st LB' so AH' MI' ST' (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & [errv ERR] & SOF).
      pose proof geo as (G1 & G2 & G3 & G4 & G5). pose proof RSTK_rlo as RSC. atop_facts. unfold KHIGH in G3.
      split; [exact ST'|]. split; [exact MI'|].
      split. { unfold AMFRAME in *. eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; apply stack_dcli; cbn in Ha; lia]. }
      split. { eapply ASTAT_agree; [exact AG| | exact AS]. intros a [Ha|Ha].
               - unfold astat_app in Ha. left. right; left.
                 Ltac tryr lo hi := lazymatch goal with Hx : (lo <= _ < _) |- _ => idtac end;   (* [comment removed for export] *)
                   exists (lo, hi); split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto | cbn; lia].
                 repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end;
                   first [ tryr 0x65ba90 0x65ba98 | tryr 0x67bda8 0x67bdb0 | tryr 0x67bdc8 0x67bdd8 
                         | tryr 0x16a820 0x16a821 | tryr 0xd5310 0xd5311 | tryr 0xd1eb8 0xd1ec0
                         | tryr 0x67c228 0x67c680 | tryr 0xd4a68 0xd4a70 | tryr 0xd4980 0xd4a10 | tryr 0xd4978 0xd4980 | tryr 0xd4888 0xd4890
                         | tryr 0xd6190 0xd6194 | tryr 0xd4aa0 0xd52e8 | tryr 0xd6230 0xd6238 ].
               - unfold astat_sh in Ha. destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]].
                 + apply (ci_drv_sh' 0x22760 0x22780); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity].
                 + apply (ci_drv_sh' 0x22840 0x25300); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity].
                 + apply (ci_drv_sh' 0x22da0 0x246a0); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity].
                 + apply (ci_drv_sh' 0x246e0 0x24860); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity].
                 + apply (ci_drv_sh' 0x25340 0x25400); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity].
                 + apply (ci_drv_sh' 0x60b000 0x65b000); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity].
                 + apply (ci_drv_sh' 0xd4aa0 0xd52e8); [unfold drv_img_ranges; cbn; tauto | rewrite !shad_div; unfold ASHOFF; lia | reflexivity]. }
      split. { destruct SE as (flags & mode & e & wend & tail & Hc & HR). exists flags, mode, e, wend, tail. split; [| exact HR].
               eapply rw_cells_magree; [exact AG| exact Hc|]. intros a Ha. apply (ci_drv RSTDERR (RSTDERR + 232)); [unfold drv_img_ranges; cbn; tauto| cbn in Ha; lia]. }
      split. { eapply rw_cells_magree; [exact AG| exact GU|]. intros a Ha. apply (ci_drv 0x67bb78 0x67bb80); [unfold drv_img_ranges; cbn; tauto| unfold ssp_guard in Ha; cbn in Ha; lia]. }
      split. { unfold atrun_cells0 in *. destruct TR as (TR & TI & TX & (cdt & thr & sec & tm1 & TL)). split.
                 - eapply rw_cells_magree; [exact AG| exact TR| intros a Ha; apply (ci_drv 0x60afd0 0x60aff0); [unfold drv_img_ranges; cbn; tauto| unfold AINIT_FLAG in Ha; cbn in Ha; lia]].
                 - split. { eapply rw_cells_magree; [exact AG| exact TI| intros a Ha; apply (ci_drv 0x60afd0 0x60aff0); [unfold drv_img_ranges; cbn; tauto| unfold AAEF_INCB in Ha; cbn in Ha; lia]]. }
                   split. { eapply atx_cells1w_agree; [exact AG| | exact TX]. intros a Ha. apply (ci_drv 0x67bb88 0x67bda8); [unfold drv_img_ranges; cbn; tauto| unfold atx_addrA, AATX, AATX_N in Ha; lia]. }
                   exists cdt, thr, sec, tm1. eapply rw_cells_magree; [exact AG| exact TL| intros a Ha; apply (ci_drv 0x67bdc8 0x67bdd8); [unfold drv_img_ranges; cbn; tauto| unfold ALIBC in Ha; cbn in Ha; lia]]. }
      split.
      { eapply harness_invA_magree; [exact AG| | exact HI]. intros a Ha.
        repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end;
          first [ apply (ci_drv_sh 0x22760 0x22780); [unfold drv_img_ranges; cbn; tauto| rewrite !shad_div; unfold ASHOFF; lia| reflexivity| reflexivity]
                | apply (ci_drv_sh 0x22840 0x25300); [unfold drv_img_ranges; cbn; tauto| rewrite !shad_div; unfold ASHOFF; lia| reflexivity| reflexivity]
                | apply (ci_drv_sh 0x22da0 0x246a0); [unfold drv_img_ranges; cbn; tauto| rewrite !shad_div; unfold ASHOFF; lia| reflexivity| reflexivity]
                | apply (ci_drv_sh 0x246e0 0x24860); [unfold drv_img_ranges; cbn; tauto| rewrite !shad_div; unfold ASHOFF; lia| reflexivity| reflexivity]
                | apply (ci_drv_sh 0x25340 0x25400); [unfold drv_img_ranges; cbn; tauto| rewrite !shad_div; unfold ASHOFF; lia| reflexivity| reflexivity]
                | apply (ci_drv_sh 0x60b000 0x65b000); [unfold drv_img_ranges; cbn; tauto| rewrite !shad_div; unfold ASHOFF; lia| reflexivity| reflexivity]
                | apply (ci_drv 0x22760 0x22780); [unfold drv_img_ranges; cbn; tauto| lia]
                | apply (ci_drv 0x22840 0x25300); [unfold drv_img_ranges; cbn; tauto| lia]
                | apply (ci_drv 0x22da0 0x246a0); [unfold drv_img_ranges; cbn; tauto| lia]
                | apply (ci_drv 0x246e0 0x24860); [unfold drv_img_ranges; cbn; tauto| lia]
                | apply (ci_drv 0x25340 0x25400); [unfold drv_img_ranges; cbn; tauto| lia]
                | apply (ci_drv 0x60b000 0x65b000); [unfold drv_img_ranges; cbn; tauto| lia] ]. }
      split. { eapply rodata_sh0_magree; [exact AG| | exact ROD]. intros a Ha. apply (ci_drv_sh 0x10000 0x22740); [left; reflexivity| exact Ha| reflexivity| reflexivity]. }
      split. { eapply rclean_magree; [exact AG| | exact RCS]. intros a Ha. destruct RCS as [(_ & HL64 & _) _]. unfold hull64 in HL64.
               apply (stack_sh_dcli (r_rlo RSTK) (r_rhi RSTK)); [atop_facts; lia| lia| exact Ha]. }
      split. { eapply rclean_magree; [exact AG| | exact RCB]. intros a Ha. unfold RBstdout in Ha. cbn [r_rlo r_rhi] in Ha.
               apply (ci_drv_sh 0x67c228 0x67c680); [unfold drv_img_ranges; cbn; tauto| | reflexivity| reflexivity].
               rewrite !shad_div in *. unfold ASHOFF in *. lia. }
      split. { eapply rclean_magree; [exact AG| | exact RSG]. intros a Ha. unfold RSTG in Ha. cbn [r_rlo r_rhi] in Ha.
               apply (ci_drv_sh 0x5fafc0 0x60b000); [unfold drv_img_ranges; cbn; tauto| | reflexivity| reflexivity].
               rewrite !shad_div in *. unfold ASHOFF in *. lia. }
      split. { exists errv. eapply rw_cells_magree; [exact AG| exact ERR|]. intros a' Ha'. rewrite errno_addr_ATP in Ha'. cbn in Ha'.
               apply (ci_drv 0x65ba90 0x65ba98); [unfold drv_img_ranges; cbn; tauto| lia]. }
      eapply stdout_file_magree; [exact AG| | exact SOF]. intros a [Ha|Ha].
      - apply (ci_drv RSTDOUT (RSTDOUT + 232)); [unfold drv_img_ranges; cbn; tauto| exact Ha].
      - apply (ci_drv 0x67c228 0x67c680); [unfold drv_img_ranges; cbn; tauto| cbn in Ha |- *; lia].
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
    \/ (fst iv = 0x65ba94 /\ snd iv = 0x65ba98)                                   (* [comment removed for export] *)
    \/ (fst iv = RSTDERR /\ snd iv = RSTDERR + 232)                               (* [comment removed for export] *)
    \/ ablk (fst iv) (snd iv)                                                     (* [comment removed for export] *)
    \/ (ASTAGE <= fst iv /\ snd iv <= ASTAGE + 65536).                           (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition WOK : Z * Z -> Prop := WOKb (usp + -128).

  (* [comment removed for export] *)
  Lemma WOKb_outside : forall hi W a, ALO <= hi -> Forall (WOKb hi) W ->
    (hi <= a
     \/ (a < 0x67e000 /\ ~ (0x65ba94 <= a < 0x65ba98) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x5fafd0 <= a < 0x60afd0))
     \/ (0x7fff7000 <= a < 0x10007fff8000)) -> outside W a.
  Proof.
    pose proof geo as (G1 & G2 & G3 & _). unfold KHIGH in *. atop_facts.
    intros hi. induction W as [|[lo1 hi1] W IH]; intros a Hhi HW Ha; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    unfold WOKb, ablk, ASTAGE, AIMG_HI, KLS in H1. cbn [fst snd] in H1. lia.
  Qed.
  Lemma WOK_outside : forall W a, Forall WOK W ->
    (usp + -128 <= a
     \/ (a < 0x67e000 /\ ~ (0x65ba94 <= a < 0x65ba98) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x5fafd0 <= a < 0x60afd0))
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
  Lemma ABASE_of_parts : forall hi W m m' so, ALO <= hi <= usp + 24 -> Forall (WOKb hi) W -> munch W m m' -> wmono asegs m m' ->
    ASTAT m -> rw_cells asegs m ssp_guard [C8 canary] -> atrun_cells0 m -> harness_invA m -> rodata_sh0 m ->
    rclean m RSTK -> rclean m RBstdout -> rclean m RSTG -> stdout_file m so ->
    stk asegs m' ALO (usp + -128) -> mem_inv asegs m' -> AMFRAME m' -> stderr_wfile0 m' ->
    (exists errv, rw_cells asegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
    ABASE so m'.
  Proof.
    intros hi W m m' so Hhi HW MU WM AS GU TR HI ROD RCS RCB RSG SOF ST' MI' FR' SE' ERR'.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof (magree_of_munch asegs _ _ _ MU WM) as AG. pose proof (WOKb_appW hi W ltac:(lia) HW) as AW.
    assert (OUT : forall a, (hi <= a \/ (a < 0x67e000 /\ ~ (0x65ba94 <= a < 0x65ba98) /\ ~ (RSTDERR <= a < RSTDERR + 232) /\ ~ (0x5fafd0 <= a < 0x60afd0))
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

  Lemma ABASE_munch : forall W m m' so, ABASE so m -> Forall WOK W -> munch W m m' -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' ALO (usp + -128) -> stderr_wfile0 m' ->
    (exists errv, rw_cells asegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
    ABASE so m'.
  Proof.
    intros W m m' so (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & ERR & SOF) HW MU WM MI' ST' SE' ERR'.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    eapply (ABASE_of_parts (usp + -128)); try eassumption; [lia|].
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
       rw_cells asegs m 0xd0e78 [C8 (Z_to_bv 64 0xccd48); C8 (Z_to_bv 64 0xccd38)]
    /\ rw_cells asegs m 0xccd38 [C8 (Z_to_bv 64 0x8ce10); C8 (Z_to_bv 64 0x3c00c)]
    /\ rw_cells asegs m 0xd0148 [C8 (Z_to_bv 64 0xbc95c); C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m 0xd0df0 [C8 (Z_to_bv 64 0xd4aa0); C8 (Z_to_bv 64 0xd52a0)]
    /\ rw_cells asegs m 0xd0198 [C8 (Z_to_bv 64 0xd2030)]
    /\ rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)].
  Proof.
    intros L RNG st LB m AH. unfold got_ssp, ssp_guard.
    Ltac relro_tac AH bs :=
      eapply rw_cells_recast;
      [ apply (rw_cells_image0 asegs _ _ bs);
        [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply (AI_relro AI _ _ _ _ _ AH); rewrite ?length_app, ?length_le8 in Ha; unfold ARELRO_LO, ARELRO_HI; lia
        | vm_compute; reflexivity | lia | rewrite ?length_app, ?length_le8; lia ]
      | cbn; repeat split; exact I | reflexivity | reflexivity ].
    split; [relro_tac AH (le8 (Z_to_bv 64 0xccd48) ++ le8 (Z_to_bv 64 0xccd38))|].
    split; [relro_tac AH (le8 (Z_to_bv 64 0x8ce10) ++ le8 (Z_to_bv 64 0x3c00c))|].
    split; [relro_tac AH (le8 (Z_to_bv 64 0xbc95c) ++ le8 (Z_to_bv 64 0))|].
    split; [relro_tac AH (le8 (Z_to_bv 64 0xd4aa0) ++ le8 (Z_to_bv 64 0xd52a0))|].
    split; [relro_tac AH (le8 (Z_to_bv 64 0xd2030))| relro_tac AH (le8 (Z_to_bv 64 0x67bb78))].
  Qed.

  Lemma mdtor_rt_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rw_cells asegs m 0xd6190 [C4 (Z_to_bv 64 1)] -> mdtor_rt m.
  Proof.
    intros L RNG st LB m AH RG. pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT. unfold artcells in RT. decompose [and] RT.
    destruct (exit_relro_of_aheap _ _ _ _ _ AH) as (_ & _ & _ & _ & X5 & _).
    unfold mdtor_rt. repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma aat_exit_intro : forall (code : Z) (s : APS) L (LB : list ablock) (SP : Z) RNG
      (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : amem),
    stk asegs m ALO SP -> ALO <= SP - 48 - MDTOR_DEPTH -> usp + -128 <= SP <= usp ->
    ASTAT m -> atx_exit m -> AHEAP AI L RNG (aps_m s) LB m -> stdout_file m (aps_so s) -> stderr_file m -> rw_cells asegs m ssp_guard [C8 canary] ->
    mem_inv asegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    aat_exit code s RNG (MS (mkR ra (Z_to_bv 64 SP) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (Z_to_bv 64 AEXIT_PC) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros ST LOS SPR AS ATX AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof AS as (A1 & A2 & (cdt & thr & sec & tm1 & A3) & A11 & A12 & [dso A13] & A14 & A15 & A15' & A16 & A17
                      & D1 & D2 & D3 & GD0 & GD1 & GD2 & GD3 & GD4 & GD5 & GD6 & GD7 & GD8 & GD9 & GD10 & GD11 & GD12 & GD13 & GD14 & GD15 & GD16 & GD17 & GD18 & GD19 & GD20 & GD21 & GD22 & GD23 & GD24 & GD25 & GD26 & GD27 & GD28 & GD29 & GD30 & GD31 & SH0 & SH1 & SH2 & SH3 & SH4 & SH5 & SH6 & SH7 & SH8 & SH9 & SH10 & SH11 & SH12 & SH13 & SH14 & SH15 & SH16 & SH17 & SH18 & SH19 & SH20 & SH21 & SH22 & SH23 & SH24 & SH25 & SH26 & SH27 & SH28 & SH29 & SH30 & SH31 & SH32).
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

  (* [comment removed for export] *)
  Lemma amain_return : forall (code : Z) (s : APS) L (LB : list ablock) RNG
      (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
    AMFRAME m -> stk asegs m ALO (usp + -128) -> ASTAT m -> atx_exit m -> AHEAP AI L RNG (aps_m s) LB m ->
    stdout_file m (aps_so s) -> stderr_file m -> rw_cells asegs m ssp_guard [C8 canary] -> mem_inv asegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    evtF asegs RNG (aat_exit code s RNG)
      (MS (mkR x1 (Z_to_bv 64 (usp + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8c870) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros FR ST AS ATX AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    unfold AMFRAME, ASTAGE2_RET in FR.
    do 11 zstep. release_frame FR ST (usp + -48). zstep.
    replace (ret_pc (Z_to_bv 64 0xbc378)) with (Z_to_bv 64 0xbc378) by (symmetry; rpc).
    zstep.
    apply evtF_done. unfold AEXIT_PC.
    eapply aat_exit_intro; first [eassumption | lia | unfold MDTOR_DEPTH; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma aexit2_tail : forall (s : APS) L (LB : list ablock) RNG
      (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem),
    stk asegs m ALO (usp + -128) -> ASTAT m -> atx_exit m -> AHEAP AI L RNG (aps_m s) LB m ->
    stdout_file m (aps_so s) -> stderr_file m -> rw_cells asegs m ssp_guard [C8 canary] -> mem_inv asegs m -> 0 < TID < 4194304 ->
    rng RNG ALO (usp - ALO) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng0 RNG ->
    evtF asegs RNG (aat_exit 2 s RNG)
      (MS (mkR x1 (Z_to_bv 64 (usp + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8c8fc) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros ST AS ATX AH SOF SEF GU MI HT RSTK' RIMG RIMSH RG0.
    pose proof geo as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    zstep. zstep.
    apply evtF_done. unfold AEXIT_PC.
    eapply aat_exit_intro; first [eassumption | lia | unfold MDTOR_DEPTH; lia].
  Qed.
End CTX.
End CANSEC1.
