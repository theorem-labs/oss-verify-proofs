(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec StepTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMem VStepMemSound VCert VContract VState2 VStepMem2 VGamma2 VContractA VCert2 VContract2 VContract2Iface VContractASound1.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require AsanMemset.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require MemsetLib CatSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.

Definition A_GOT_memset : Z := 0xaaea0.
Definition A_CELL_memset : Z := 0xaccf0.
Definition A_memset : Z := 0xa45b0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac vm_refl := vm_refl_bv.

(* [comment removed for export] *)
Definition W_56cf0 : bv 32 := 0x00058613.
Lemma F_56cf0 : fetch_word Asan.M.loaded_segments (0x56cf0 : word) = Some W_56cf0.
Proof. vm_refl. Qed.
Lemma D_56cf0 : decode_any W_56cf0 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56cf4 : bv 32 := 0x00054597.
Lemma F_56cf4 : fetch_word Asan.M.loaded_segments (0x56cf4 : word) = Some W_56cf4.
Proof. vm_refl. Qed.
Lemma D_56cf4 : decode_any W_56cf4 = Some (Auipc 11 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56cf8 : bv 32 := 0x1ac5b583.
Lemma F_56cf8 : fetch_word Asan.M.loaded_segments (0x56cf8 : word) = Some W_56cf8.
Proof. vm_refl. Qed.
Lemma D_56cf8 : decode_any W_56cf8 = Some (Load SZ8 true 11 11 428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56cfc : bv 32 := 0x0005b303.
Lemma F_56cfc : fetch_word Asan.M.loaded_segments (0x56cfc : word) = Some W_56cfc.
Proof. vm_refl. Qed.
Lemma D_56cfc : decode_any W_56cfc = Some (Load SZ8 true 6 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56d00 : bv 32 := 0x00000593.
Lemma F_56d00 : fetch_word Asan.M.loaded_segments (0x56d00 : word) = Some W_56d00.
Proof. vm_refl. Qed.
Lemma D_56d00 : decode_any W_56d00 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56d04 : bv 32 := 0x00030067.
Lemma F_56d04 : fetch_word Asan.M.loaded_segments (0x56d04 : word) = Some W_56d04.
Proof. vm_refl. Qed.
Lemma D_56d04 : decode_any W_56d04 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56df8 : bv 32 := 0x00054617.
Lemma F_56df8 : fetch_word Asan.M.loaded_segments (0x56df8 : word) = Some W_56df8.
Proof. vm_refl. Qed.
Lemma D_56df8 : decode_any W_56df8 = Some (Auipc 12 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56dfc : bv 32 := 0x0a863603.
Lemma F_56dfc : fetch_word Asan.M.loaded_segments (0x56dfc : word) = Some W_56dfc.
Proof. vm_refl. Qed.
Lemma D_56dfc : decode_any W_56dfc = Some (Load SZ8 true 12 12 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56e00 : bv 32 := 0x00063303.
Lemma F_56e00 : fetch_word Asan.M.loaded_segments (0x56e00 : word) = Some W_56e00.
Proof. vm_refl. Qed.
Lemma D_56e00 : decode_any W_56e00 = Some (Load SZ8 true 6 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56e04 : bv 32 := 0x00058613.
Lemma F_56e04 : fetch_word Asan.M.loaded_segments (0x56e04 : word) = Some W_56e04.
Proof. vm_refl. Qed.
Lemma D_56e04 : decode_any W_56e04 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56e08 : bv 32 := 0x0f500593.
Lemma F_56e08 : fetch_word Asan.M.loaded_segments (0x56e08 : word) = Some W_56e08.
Proof. vm_refl. Qed.
Lemma D_56e08 : decode_any W_56e08 = Some (OpImm ALU_ADD 11 0 245, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56e0c : bv 32 := 0x00030067.
Lemma F_56e0c : fetch_word Asan.M.loaded_segments (0x56e0c : word) = Some W_56e0c.
Proof. vm_refl. Qed.
Lemma D_56e0c : decode_any W_56e0c = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56e10 : bv 32 := 0x00054617.
Lemma F_56e10 : fetch_word Asan.M.loaded_segments (0x56e10 : word) = Some W_56e10.
Proof. vm_refl. Qed.
Lemma D_56e10 : decode_any W_56e10 = Some (Auipc 12 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56e14 : bv 32 := 0x09063603.
Lemma F_56e14 : fetch_word Asan.M.loaded_segments (0x56e14 : word) = Some W_56e14.
Proof. vm_refl. Qed.
Lemma D_56e14 : decode_any W_56e14 = Some (Load SZ8 true 12 12 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56e18 : bv 32 := 0x00063303.
Lemma F_56e18 : fetch_word Asan.M.loaded_segments (0x56e18 : word) = Some W_56e18.
Proof. vm_refl. Qed.
Lemma D_56e18 : decode_any W_56e18 = Some (Load SZ8 true 6 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56e1c : bv 32 := 0x00058613.
Lemma F_56e1c : fetch_word Asan.M.loaded_segments (0x56e1c : word) = Some W_56e1c.
Proof. vm_refl. Qed.
Lemma D_56e1c : decode_any W_56e1c = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56e20 : bv 32 := 0x0f800593.
Lemma F_56e20 : fetch_word Asan.M.loaded_segments (0x56e20 : word) = Some W_56e20.
Proof. vm_refl. Qed.
Lemma D_56e20 : decode_any W_56e20 = Some (OpImm ALU_ADD 11 0 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56e24 : bv 32 := 0x00030067.
Lemma F_56e24 : fetch_word Asan.M.loaded_segments (0x56e24 : word) = Some W_56e24.
Proof. vm_refl. Qed.
Lemma D_56e24 : decode_any W_56e24 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma asan_msteps_bridge segs s1 s2 :
  OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.CatSim.msteps segs s1 s2 -> msteps segs s1 s2.
Proof. induction 1; [apply mst_refl|eapply mst_step; eauto]. Qed.

Lemma memset_asan : forall mem (d cv ret : word) (n : Z) rom regs,
    (0 <= n)%Z -> (bv_unsigned d + n < 2 ^ 64)%Z -> store_ok ASEGS mem d (Z.to_nat n) = true -> ret_ok ret ->
    getr regs 10 = d -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    exists regs',
      msteps ASEGS (mkst regs (wordZ A_memset) mem rom) (mkst regs' ret (wbytes mem d (repeat (Z_to_bv 8 (bv_unsigned cv)) (Z.to_nat n))) rom)
      /\ getr regs' 10 = d
      /\ (forall r : reg, ~ In r [11; 12; 13; 14; 15; 16]%bv -> getr regs' r = getr regs r).
Proof.
  intros mem d cv ret n rom regs Hn Hnw Hok Hret H10 H11 H12 H1.
  destruct (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.AsanMemset.memset_summary mem d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1)
    as (regs' & RUN & P10 & AG).
  exists regs'. split; [|split; [exact P10|exact AG]].
  apply asan_msteps_bridge. exact RUN.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Thunks.
  Variable rom : word -> option byte.

  Lemma agree_pack (fill : Z) regs regs1 :
    (forall r : reg, r <> 12 -> r <> 6 -> r <> 11 -> getr regs1 r = getr regs r) ->
    getr regs1 11 = Z_to_bv 64 fill -> getr regs1 12 = getr regs 11 ->
    getr regs1 10 = getr regs 10 /\ getr regs1 11 = Z_to_bv 64 fill /\ getr regs1 12 = getr regs 11
    /\ getr regs1 1 = getr regs 1
    /\ (forall r : reg, bv_unsigned r <> 0%Z -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs1 r = getr regs r).
  Proof.
    intros HR H11 H12. split; [apply HR; intros X; discriminate|]. split; [exact H11|]. split; [exact H12|].
    split; [apply HR; intros X; discriminate|].
    intros r Hr Hcs. apply HR; intros ->; apply Hcs; unfold CALLER_SAVED; cbn; auto 20.
  Qed.

  (* [comment removed for export] *)
  Lemma thunk_d120c regs mem :
    rdn ASEGS mem (wordZ A_GOT_memset) 8 = Some (word_to_le_bytes 8 (wordZ A_CELL_memset)) ->
    rdn ASEGS mem (wordZ A_CELL_memset) 8 = Some (word_to_le_bytes 8 (wordZ A_memset)) ->
    exists regs1,
      msteps ASEGS (mkst regs (wordZ 0x56df8) mem rom) (mkst regs1 (wordZ A_memset) mem rom)
      /\ getr regs1 10 = getr regs 10 /\ getr regs1 11 = Z_to_bv 64 245 /\ getr regs1 12 = getr regs 11
      /\ getr regs1 1 = getr regs 1
      /\ (forall r : reg, bv_unsigned r <> 0%Z -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs1 r = getr regs r).
  Proof.
    intros GOT CELL. eexists. split.
    - replace (wordZ 0x56df8) with (0x56df8 : word) by bveq. replace (wordZ A_memset) with (0xa45b0 : word) by bveq.
      stepi F_56df8 D_56df8.
      stepld F_56dfc D_56dfc (wordZ A_GOT_memset) (wordZ A_CELL_memset) ltac:(exact GOT).
      stepld F_56e00 D_56e00 (wordZ A_CELL_memset) (wordZ A_memset) ltac:(exact CELL).
      stepi F_56e04 D_56e04.
      stepi F_56e08 D_56e08.
      stepjr F_56e0c D_56e0c (wordZ A_memset) ltac:(getr_resolve; reflexivity).
      apply mst_refl.
    - apply agree_pack.
      + intros r N12 N6 N11. rewrite !getr_other by assumption. reflexivity.
      + getr_resolve. bveq.
      + getr_resolve. change (bv_signed (0 : bv 12)) with 0%Z. rewrite v_addi_0. reflexivity.
  Qed.

  Lemma thunk_d1224 regs mem :
    rdn ASEGS mem (wordZ A_GOT_memset) 8 = Some (word_to_le_bytes 8 (wordZ A_CELL_memset)) ->
    rdn ASEGS mem (wordZ A_CELL_memset) 8 = Some (word_to_le_bytes 8 (wordZ A_memset)) ->
    exists regs1,
      msteps ASEGS (mkst regs (wordZ 0x56e10) mem rom) (mkst regs1 (wordZ A_memset) mem rom)
      /\ getr regs1 10 = getr regs 10 /\ getr regs1 11 = Z_to_bv 64 248 /\ getr regs1 12 = getr regs 11
      /\ getr regs1 1 = getr regs 1
      /\ (forall r : reg, bv_unsigned r <> 0%Z -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs1 r = getr regs r).
  Proof.
    intros GOT CELL. eexists. split.
    - replace (wordZ 0x56e10) with (0x56e10 : word) by bveq. replace (wordZ A_memset) with (0xa45b0 : word) by bveq.
      stepi F_56e10 D_56e10.
      stepld F_56e14 D_56e14 (wordZ A_GOT_memset) (wordZ A_CELL_memset) ltac:(exact GOT).
      stepld F_56e18 D_56e18 (wordZ A_CELL_memset) (wordZ A_memset) ltac:(exact CELL).
      stepi F_56e1c D_56e1c.
      stepi F_56e20 D_56e20.
      stepjr F_56e24 D_56e24 (wordZ A_memset) ltac:(getr_resolve; reflexivity).
      apply mst_refl.
    - apply agree_pack.
      + intros r N12 N6 N11. rewrite !getr_other by assumption. reflexivity.
      + getr_resolve. bveq.
      + getr_resolve. change (bv_signed (0 : bv 12)) with 0%Z. rewrite v_addi_0. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma thunk_d1104 regs mem :
    rdn ASEGS mem (wordZ A_GOT_memset) 8 = Some (word_to_le_bytes 8 (wordZ A_CELL_memset)) ->
    rdn ASEGS mem (wordZ A_CELL_memset) 8 = Some (word_to_le_bytes 8 (wordZ A_memset)) ->
    exists regs1,
      msteps ASEGS (mkst regs (wordZ 0x56cf0) mem rom) (mkst regs1 (wordZ A_memset) mem rom)
      /\ getr regs1 10 = getr regs 10 /\ getr regs1 11 = Z_to_bv 64 0 /\ getr regs1 12 = getr regs 11
      /\ getr regs1 1 = getr regs 1
      /\ (forall r : reg, bv_unsigned r <> 0%Z -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs1 r = getr regs r).
  Proof.
    intros GOT CELL. eexists. split.
    - replace (wordZ 0x56cf0) with (0x56cf0 : word) by bveq. replace (wordZ A_memset) with (0xa45b0 : word) by bveq.
      stepi F_56cf0 D_56cf0.
      stepi F_56cf4 D_56cf4.
      stepld F_56cf8 D_56cf8 (wordZ A_GOT_memset) (wordZ A_CELL_memset) ltac:(exact GOT).
      stepld F_56cfc D_56cfc (wordZ A_CELL_memset) (wordZ A_memset) ltac:(exact CELL).
      stepi F_56d00 D_56d00.
      stepjr F_56d04 D_56d04 (wordZ A_memset) ltac:(getr_resolve; reflexivity).
      apply mst_refl.
    - assert (AGR : forall regs1,
                (forall r : reg, r <> 12 -> r <> 11 -> r <> 6 -> getr regs1 r = getr regs r) ->
                getr regs1 11 = Z_to_bv 64 0 -> getr regs1 12 = getr regs 11 ->
                getr regs1 10 = getr regs 10 /\ getr regs1 11 = Z_to_bv 64 0 /\ getr regs1 12 = getr regs 11
                /\ getr regs1 1 = getr regs 1
                /\ (forall r : reg, bv_unsigned r <> 0%Z -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs1 r = getr regs r)).
      { intros regs1 HR H11 H12. split; [apply HR; intros X; discriminate|]. split; [exact H11|]. split; [exact H12|].
        split; [apply HR; intros X; discriminate|].
        intros r Hr Hcs. apply HR; intros ->; apply Hcs; unfold CALLER_SAVED; cbn; auto 20. }
      apply AGR.
      + intros r N12 N11 N6. rewrite !getr_other by assumption. reflexivity.
      + getr_resolve. bveq.
      + getr_resolve. change (bv_signed (0 : bv 12)) with 0%Z. rewrite v_addi_0. reflexivity.
  Qed.
End Thunks.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma GOT_BYTES_asan : rdn ASEGS (fun _ => None) (wordZ A_GOT_memset) 8 = Some (word_to_le_bytes 8 (wordZ A_CELL_memset)).
Proof. vm_refl. Qed.
Lemma CELL_BYTES_asan : rdn ASEGS (fun _ => None) (wordZ A_CELL_memset) 8 = Some (word_to_le_bytes 8 (wordZ A_memset)).
Proof. vm_refl. Qed.

Section Contracts.
  Variable P : vparams2.
  Variable E : venv2.
  Variables mem0 rom : word -> option byte.
  Variable CI : cimg.
  Hypothesis PO2 : params_ok2 ASEGS P.
  (* [comment removed for export] *)
  Hypothesis GOT_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ (plo <= A_GOT_memset)%Z /\ (A_GOT_memset + 8 <= phi)%Z.
  Hypothesis CELL_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ (plo <= A_CELL_memset)%Z /\ (A_CELL_memset + 8 <= phi)%Z.

  Theorem set_shadow_00_post : contract_post2 ASEGS P E mem0 rom CI (C_set_shadow 0) 0x56cf0.
  Proof.
    eapply (set_shadow_post ASEGS P E mem0 rom CI PO2 0x56cf0 0 A_GOT_memset A_CELL_memset A_memset); try lia.
    - exact GOT_PRISTINE. - exact GOT_BYTES_asan. - exact CELL_PRISTINE. - exact CELL_BYTES_asan.
    - intros regs mem G C. exact (thunk_d1104 rom regs mem G C).
    - intros. eapply memset_asan; eauto.
  Qed.
  Theorem set_shadow_f5_post : contract_post2 ASEGS P E mem0 rom CI (C_set_shadow 245) 0x56df8.
  Proof.
    eapply (set_shadow_post ASEGS P E mem0 rom CI PO2 0x56df8 245 A_GOT_memset A_CELL_memset A_memset); try lia.
    - exact GOT_PRISTINE. - exact GOT_BYTES_asan. - exact CELL_PRISTINE. - exact CELL_BYTES_asan.
    - intros regs mem G C. exact (thunk_d120c rom regs mem G C).
    - intros. eapply memset_asan; eauto.
  Qed.
  Theorem set_shadow_f8_post : contract_post2 ASEGS P E mem0 rom CI (C_set_shadow 248) 0x56e10.
  Proof.
    eapply (set_shadow_post ASEGS P E mem0 rom CI PO2 0x56e10 248 A_GOT_memset A_CELL_memset A_memset); try lia.
    - exact GOT_PRISTINE. - exact GOT_BYTES_asan. - exact CELL_PRISTINE. - exact CELL_BYTES_asan.
    - intros regs mem G C. exact (thunk_d1224 rom regs mem G C).
    - intros. eapply memset_asan; eauto.
  Qed.
  Theorem set_shadow_dead_any b : contract_dead2 ASEGS P E mem0 CI (C_set_shadow b).
  Proof. exact (set_shadow_dead ASEGS P E mem0 CI b). Qed.
End Contracts.
