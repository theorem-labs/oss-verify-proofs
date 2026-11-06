(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
 BnModel BnMath BnMem BnDefs LibIface BnCbdLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import MemsetLib BothMemset_code BothMemset1 BothMemset.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsRtLibB AsZX AsZXTac AsZXDefs BnA_lib BnA_frame.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Definition shcellsB (m : word -> option byte) : Prop :=
  cellN SEGS_B m 0x12a380 8 0x132738 /\ cellN SEGS_B m 0x132738 8 SHA.

(* [comment removed for export] *)
Definition objshB (m : word -> option byte) (o : Z) : Prop :=
  forall g, 0 <= g < 64 -> cellN SEGS_B m (SHA + o / 8 + g) 1 0.

Lemma shcellsB_unch : forall m m' rs,
  unch m m' rs -> (forall r, In r rs -> KHI <= fst r \/ (IMG <= fst r /\ snd r <= LOSH)) -> shcellsB m -> shcellsB m'.
Proof.
  intros m m' rs Hu Hrs [A B]. split.
  all: eapply cellN_unch; [exact Hu | lia | cbn; lia | intros r Hr; specialize (Hrs r Hr); cbn; lia | assumption].
Qed.

Lemma objshB_unch : forall m m' rs o,
  unch m m' rs -> (forall r, In r rs -> KHI <= fst r \/ (IMG <= fst r /\ snd r <= LOSH)) -> 0 <= o -> o + 516 <= HIE -> objshB m o -> objshB m' o.
Proof.
  intros m m' rs o Hu Hrs Ho1 Ho2 H g Hg.
  eapply cellN_unch; [exact Hu | lia | cbn; lia | intros r Hr; specialize (Hrs r Hr); cbn; lia | apply H; exact Hg].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition tblshB (m : word -> option byte) : Prop := forall g, 0 <= g < 6 -> cellN SEGS_B m (SHA + 18172 + g) 1 0.

Lemma objshB_unch2 : forall m m' rs q,
  unch m m' rs -> (forall r, In r rs -> KHI <= fst r \/ snd r <= LOSH \/ snd r <= SHA + q / 8 \/ SHA + q / 8 + 64 <= fst r) ->   (* [comment removed for export] *)
  0 <= q -> q + 516 <= HIE -> objshB m q -> objshB m' q.
Proof.
  intros m m' rs q U HR Hq1 Hq2 H k Hk.
  eapply cellN_unch; [exact U | lia | cbn; lia | | apply H; exact Hk].
  intros r Hr. specialize (HR r Hr). cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mscellsB (m : word -> option byte) : Prop :=
  cellN SEGS_B m 0x12a3a0 8 0x12c360 /\ cellN SEGS_B m 0x12c360 8 0x11d480.
(* [comment removed for export] *)
Definition suarB (m : word -> option byte) : Prop :=
  cellN SEGS_B m 0x12a3d8 8 0x132740 /\ cellN SEGS_B m 0x132740 4 1.

Lemma mscellsB_intro : forall m, ro_ok SEGS_B RO_B m -> mscellsB m.
Proof.
  intros m RO. split; (eapply cellN_ro_B; [exact RO | vm_compute; reflexivity | vm_compute; reflexivity | lia | cbn; lia]).
Qed.
Lemma suarB_intro : forall m, rt_ok_B m -> ro_ok SEGS_B RO_B m -> suarB m.
Proof.
  intros m RT RO. split.
  - eapply cellN_ro_B; [exact RO | vm_compute; reflexivity | vm_compute; reflexivity | lia | cbn; lia].
  - eapply cellN_rt_B; [exact RT | vm_compute; reflexivity | lia | cbn; lia].
Qed.
Lemma shcellsB_intro : forall m, rt_ok_B m -> ro_ok SEGS_B RO_B m -> shcellsB m.
Proof.
  intros m RT RO. split.
  - eapply cellN_ro_B; [exact RO | vm_compute; reflexivity | vm_compute; reflexivity | lia | cbn; lia].
  - eapply cellN_rt_B; [exact RT | vm_compute; reflexivity | lia | cbn; lia].
Qed.
Lemma tblshB_intro : forall m, gsh_ok_B m -> tblshB m.
Proof.
  intros m G g Hg. eapply cellN_byte; [| lia | lia | lia].
  eapply mem_byte_of_tbl; [exact G|].
  assert (C : g = 0 \/ g = 1 \/ g = 2 \/ g = 3 \/ g = 4 \/ g = 5) by lia.
  destruct C as [-> |[-> |[-> |[-> |[-> | ->]]]]]; vm_compute; reflexivity.
Qed.
Lemma five_tbl_B0 : arr32 SEGS_B (fun _ => None) 145376 five_tbl.
Proof.
  intros i Hi. cbn [length five_tbl] in Hi.
  assert (H : forallb (fun k => match rdn SEGS_B (fun _ => None) (Z_to_bv 64 (145376 + 4 * Z.of_nat k)) 4 with
                               | Some bs => bytes_le_to_Z bs =? nth k five_tbl 0 | None => false end) (seq 0 12) = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) H i ltac:(apply in_seq; lia)) as Hk. cbn beta in Hk. unfold cellN.
  destruct (rdn SEGS_B _ _ 4) as [bs|]; [|discriminate]. exists bs. split; [reflexivity|]. apply Z.eqb_eq. exact Hk.
Qed.
Lemma five_tblB_intro : forall m, ro_ok SEGS_B RO_B m -> arr32 SEGS_B m 145376 five_tbl.
Proof.
  intros m RO. eapply BnCbdLib.arr32_rom; [lia | cbn; lia | | apply five_tbl_B0].
  intros x b Hx Hb. apply RO; [|exact Hb]. cbn [length five_tbl] in Hx. exists (0x10000, 0x4e000). split; [left; reflexivity | cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cellN_low_unchB : forall m m' rs a n v,
  unch m m' rs -> (forall r, In r rs -> highr r) -> 0 <= a -> (a + Z.of_nat n <= IMG \/ (SHA <= a /\ a + Z.of_nat n <= LSLO)) ->   (* [comment removed for export] *)
  cellN SEGS_B m a n v -> cellN SEGS_B m' a n v.
Proof.
  intros m m' rs a n v U H Ha Hb C. eapply cellN_unch; [exact U | lia | lia | | exact C].
  intros r Hr. specialize (H r Hr). unfold highr in H. lia.
Qed.
Lemma mscellsB_unch : forall m m' rs, unch m m' rs -> (forall r, In r rs -> highr r) -> mscellsB m -> mscellsB m'.
Proof. intros m m' rs U H [A B]. split; (eapply cellN_low_unchB; [exact U | exact H | lia | cbn; lia | assumption]). Qed.
Lemma suarB_unch : forall m m' rs, unch m m' rs -> (forall r, In r rs -> highr r) -> suarB m -> suarB m'.
Proof. intros m m' rs U H [A B]. split; (eapply cellN_low_unchB; [exact U | exact H | lia | cbn; lia | assumption]). Qed.
Lemma shcellsB_unch' : forall m m' rs, unch m m' rs -> (forall r, In r rs -> highr r) -> shcellsB m -> shcellsB m'.
Proof. intros m m' rs U H [A B]. split; (eapply cellN_low_unchB; [exact U | exact H | lia | cbn; lia | assumption]). Qed.
Lemma tblshB_unch : forall m m' rs, unch m m' rs -> (forall r, In r rs -> highr r) -> tblshB m -> tblshB m'.
Proof. intros m m' rs U H T g Hg. eapply cellN_low_unchB; [exact U | exact H | lia | cbn; lia | apply T; exact Hg]. Qed.
Lemma five_tblB_unch : forall m m' rs, unch m m' rs -> (forall r, In r rs -> highr r) ->
  arr32 SEGS_B m 145376 five_tbl -> arr32 SEGS_B m' 145376 five_tbl.
Proof.
  intros m m' rs U H T. eapply arr32_unch; [exact U | lia | cbn; lia | | exact T].
  intros r Hr. specialize (H r Hr). unfold highr in H. cbn [length five_tbl]. lia.
Qed.
Lemma rt_ok_B_unch : forall m m' rs, unch m m' rs -> (forall r, In r rs -> highr r) -> rt_ok_B m -> rt_ok_B m'.
Proof.
  intros m m' rs U H RT a b Hin. specialize (RT a b Hin). destruct RT as (bs & Hr & Hv). exists bs. split; [|exact Hv].
  assert (Ha : 0 <= a < IMG).   (* [comment removed for export] *)
  { pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun c => (0 <=? fst c) && (fst c <? IMG)) RT_B = true) (a, b) Hin) as X.
    cbn [fst] in X. lia. }
  rewrite <- Hr. cbn [rdn]. rewrite (U (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hr1 & Hr2). specialize (H r Hr1). unfold highr in H. rewrite u_Z2bv64, Z.mod_small in Hr2 by lia. lia.
Qed.
Lemma ro_ok_unchB : forall m m' rs, unch m m' rs -> (forall r, In r rs -> highr r) -> ro_ok SEGS_B RO_B m -> ro_ok SEGS_B RO_B m'.
Proof.
  intros m m' rs U H RO. eapply ro_ok_unch; [exact U | | exact RO].
  intros a (r0 & Hin & Hr0). assert (X : 0 <= a < IMG).   (* [comment removed for export] *)
  { pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun c => (0 <=? fst c) && (snd c <? IMG)) RO_B = true) r0 Hin) as Y.
    cbn beta in Y. apply andb_true_iff in Y. destruct Y as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.ltb_lt in Y2. lia. }
  split; [lia|]. intros r Hr. specialize (H r Hr). unfold highr in H. lia.
Qed.
Lemma gsh_ok_B_unch : forall m m' rs, unch m m' rs -> (forall r, In r rs -> highr r) -> gsh_ok_B m -> gsh_ok_B m'.
Proof.
  intros m m' rs U H G. eapply cells_ok_unch; [exact U | | exact G].
  intros a b Hin.
  assert (Ha : SHA <= a < LSLO).   (* [comment removed for export] *)
  { pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun c => (SHA <=? fst c) && (fst c <? LSLO)) GSH_B = true) (a, b) Hin) as X.
    cbn [fst] in X. lia. }
  split; [lia|]. intros r Hr. specialize (H r Hr). unfold highr in H. lia.
Qed.

Lemma malloc_ctx_ok_B_unch : forall wlo whi wlo' whi' FS m m' rs,
  malloc_ctx_ok_B wlo whi FS m -> unch m m' rs -> mem_grows m m' ->
  (forall r, In r rs -> IMG <= fst r /\ ((wlo <= fst r /\ snd r <= whi) \/ (FS <= fst r /\ snd r <= FS + FS_LEN) \/ (LOSH <= fst r /\ snd r <= KHI_A))) ->
     (* [comment removed for export] *)
  wlo <= wlo' -> whi' <= whi -> malloc_ctx_ok_B wlo' whi' FS m'.
Proof.
  intros wlo whi wlo' whi' FS m m' rs (CTX & THR & DT & H1 & H2 & H3 & H4 & H5 & B1 & B2 & B3 & B4 & C1 & C2 & C3) U Gr HR Hlo Hhi.
  unfold ctx_cell_ok, app_mem, KHI_A, HIEND_A, IMGHI_A, LOSH_A, FS_LEN in *.
  exists CTX, THR, DT. unfold ctx_cell_ok, app_mem, KHI_A, HIEND_A, IMGHI_A, LOSH_A, FS_LEN.
  split; [eapply cellN_unch; [exact U | lia | cbn; lia | intros r Hr; destruct (HR r Hr) as [X _]; cbn; lia | exact H1]|].   (* [comment removed for export] *)
  split.
  { eapply mem_u64_unch; [exact U | lia | lia | | exact H2]. intros r Hr. destruct (HR r Hr) as [_ X]. cbn. lia. }
  split; [eapply mem_def_grows; [exact Gr | exact H3]|].
  split; [eapply cellN_unch; [exact U | lia | cbn; lia | intros r Hr; destruct (HR r Hr) as [X _]; cbn; lia | exact H4]|].
  split.
  { eapply mem_u64_unch; [exact U | lia | unfold TP_B in *; lia | | exact H5]. intros r Hr. destruct (HR r Hr) as [_ X]. cbn. lia. }
  repeat split; lia.
Qed.

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

#[using="Type"] Lemma setsh_B : forall (f8 : bool) regs m (a n : Z) (ret : word),
  getr regs 10%bv = Z_to_bv 64 a -> getr regs 11%bv = Z_to_bv 64 n -> getr regs 1%bv = ret -> ret_ok ret ->
  0 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 a) (Z.to_nat n) = true -> mscellsB m ->
  exists regs',
    msteps SEGS_B (mkst regs (Z_to_bv 64 (if f8 then 0x78590 else 0x78470)) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 a) (repeat (Z_to_bv 8 (if f8 then 248 else 0)) (Z.to_nat n))) rom)
    /\ keeps SETSH_KEEP regs regs'.
Proof.
  intros f8 regs m a n ret R10 R11 R1 Hret Ha Hn Han Hst [MC1 MC2].
  pose proof (u64_range ret) as Hr.
  replace (1%bv : reg) with (Z_to_bv 5 1 : reg) in R1 by (apply bv_eq; reflexivity).
  assert (STUB : forall pc cvz, (pc = 0x78590 /\ cvz = 248) \/ (pc = 0x78470 /\ cvz = 0) ->
    exists regs1, msteps SEGS_B (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs1 (Z_to_bv 64 0x11d480) m rom)
      /\ getr regs1 10%bv = Z_to_bv 64 a /\ getr regs1 11%bv = Z_to_bv 64 cvz /\ getr regs1 12%bv = Z_to_bv 64 n
      /\ getr regs1 1%bv = ret /\ keeps SETSH_KEEP regs regs1).
  { intros pc cvz [[-> ->]|[-> ->]].
    - zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)])
                            [KC (ZL 0) 0x12a3a0 8 (ZL 0x12c360); KC (ZL 0) 0x12c360 8 (ZL 0x11d480)] (@nil kwin))
        10%nat [0x11d480] (SCR [] []) constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33)]) [a; n]
        constr:([Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)]) regs m rom 0x78590.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 MC1; kc1 MC2; exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
      exists regs1. split; [exact ZM|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
      split; [etransitivity; [exact (reg_kept _ _ _ _ (1%bv : reg) ZR ltac:(vm_compute; reflexivity)) | rewrite <- R1; reflexivity]|].
      eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
    - zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)])
                            [KC (ZL 0) 0x12a3a0 8 (ZL 0x12c360); KC (ZL 0) 0x12c360 8 (ZL 0x11d480)] (@nil kwin))
        10%nat [0x11d480] (SCR [] []) constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33)]) [a; n]
        constr:([Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)]) regs m rom 0x78470.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 MC1; kc1 MC2; exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
      exists regs1. split; [exact ZM|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
      split; [etransitivity; [exact (reg_kept _ _ _ _ (1%bv : reg) ZR ltac:(vm_compute; reflexivity)) | rewrite <- R1; reflexivity]|].
      eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
  destruct (STUB (if f8 then 0x78590 else 0x78470) (if f8 then 248 else 0)) as (regs1 & M1 & A10 & A11 & A12 & A1 & K1);
    [destruct f8; [left|right]; split; reflexivity|].
  destruct (memset_summary m (Z_to_bv 64 a) (Z_to_bv 64 (if f8 then 248 else 0)) ret n rom Hn
              ltac:(rewrite u_Z2bv64, Z.mod_small by lia; lia) Hst Hret regs1 A10 A11 A12 A1) as (regs2 & M2 & B10 & AG).
  exists regs2. split.
  - eapply msteps_trans; [exact M1|]. unfold cbyte in M2. rewrite u_Z2bv64, Z.mod_small in M2 by (destruct f8; lia). exact M2.
  - intros r Hrr. etransitivity; [| exact (K1 r Hrr)]. apply (ms_agree_getr _ _ _ AG).
    cbn in Hrr. unfold ms_clob. cbn [In].
    decompose [or] Hrr; subst; intros HH; decompose [or] HH; try discriminate; auto.
Qed.
End S.
