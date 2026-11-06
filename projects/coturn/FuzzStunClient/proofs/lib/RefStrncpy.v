(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import StartupTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefMemcpyBase RefStrLib RefMemchr RefStrlen RefMemset Ref_code_235f0_2427c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Abbreviation SEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition core_clob : list reg := [1; 8; 10; 11; 12; 13; 14; 15; 16; 17]%list.

(* [comment removed for export] *)
Lemma sd_bytes_LDv : forall l, length l = 8%nat -> word_to_le_bytes 8 (LDv l) = l.
Proof.
  intros l Hl. unfold word_to_le_bytes. rewrite u_LDv by exact Hl.
  rewrite <- Hl. apply Z_to_le_bytes_lez.
Qed.

(* [comment removed for export] *)
Lemma wbytes_shadow1 : forall m (a : word) (b z : byte) zs,
  wbytes (wbytes m a [b]) a (z :: zs) = wbytes m a (z :: zs).
Proof.
  intros m a b z zs. cbn [wbytes].
  f_equal. apply functional_extensionality. intros x.
  destruct (bv_eqb x a); reflexivity.
Qed.

Lemma step_sltu_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SLTU rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_sltu (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_sltu segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.
Ltac stepsltu F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_sltu_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section CORE.
  Variable MB : word -> option byte.     (* [comment removed for export] *)
  Variables d s : word.
  Variable n : Z.
  Variable src : list byte.               (* [comment removed for export] *)
  Variable rom : word -> option byte.
  #[local] Notation W := (Z.of_nat (length src)).
  #[local] Notation us := (bv_unsigned s).
  #[local] Notation ud := (bv_unsigned d).
  Hypothesis Hsrc : rdn SEGS MB s (length src) = Some src.
  Hypothesis Hroom : (n <= W)%Z \/ exists K, (0 <= K < W)%Z /\ bv_unsigned (nth (Z.to_nat K) src B0) = 0%Z
                                             /\ (strlen_span us K <= W)%Z.
  Hypothesis Hdst : store_ok SEGS MB d (Z.to_nat n) = true.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnws : (us + W < 2 ^ 64)%Z.
  Hypothesis Hnwd : (ud + n < 2 ^ 64)%Z.
  Hypothesis Hdisj : (ud + n <= us \/ us + W <= ud)%Z.
  Hypothesis Hro : rodata_clear MB.
  Hypothesis Hdro : (0x105a8 <= ud \/ ud + n <= 0x10588)%Z.   (* [comment removed for export] *)

  Definition B_ (j : Z) : byte := nth (Z.to_nat j) src B0.
  Definition SB (j : Z) (m : nat) : list byte := sub src (Z.to_nat j) m.
  (* [comment removed for export] *)
  Definition memk (k : Z) : word -> option byte := wbytes MB d (firstn (Z.to_nat k) src).
  (* [comment removed for export] *)
  Definition FIN (m : Z) : word -> option byte :=
    wbytes MB d (firstn (Z.to_nat m) src ++ zeros (Z.to_nat (n - m))).
  (* [comment removed for export] *)
  Definition SPEC (m : Z) : Prop :=
    (0 <= m <= n)%Z /\ (m <= W)%Z /\ (forall j, (0 <= j < m)%Z -> bv_unsigned (B_ j) <> 0%Z)
    /\ ((m < n)%Z -> bv_unsigned (B_ m) = 0%Z).

  Lemma len_firstn_k : forall k, (0 <= k <= W)%Z -> length (firstn (Z.to_nat k) src) = Z.to_nat k.
  Proof. intros k Hk. rewrite length_firstn. lia. Qed.

  Lemma memk_0 : memk 0 = MB.
  Proof. reflexivity. Qed.

  Lemma rd_src : forall k j m, (0 <= k <= W)%Z -> (k <= n)%Z -> (0 <= j)%Z -> (j + Z.of_nat m <= W)%Z ->
    rdn SEGS (memk k) (at_ s j) m = Some (SB j m).
  Proof.
    intros k j m Hk Hkn Hj Hm. unfold memk, SB. pose proof (u64_range s). pose proof (u64_range d).
    destruct m as [|m']. { cbn. unfold sub. cbn. reflexivity. }
    rewrite rdn_wbytes_out.
    - replace (at_ s j) with (at_ s (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
      apply (rdn_sub SEGS MB (length src)); [exact Hsrc | lia].
    - rewrite len_firstn_k, at_u by lia. lia.
    - rewrite at_u; lia.
    - rewrite len_firstn_k; lia.
  Qed.

  Lemma rd_src1 : forall k j, (0 <= k <= W)%Z -> (k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= W)%Z ->
    rdn SEGS (memk k) (at_ s j) 1 = Some [B_ j].
  Proof.
    intros k j Hk Hkn Hj H1. rewrite (rd_src k j 1) by lia. unfold SB, B_.
    rewrite sub_nth; [reflexivity | lia].
  Qed.

  Lemma wr_dst : forall k j m, (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
    store_ok SEGS (memk k) (at_ d j) m = true.
  Proof.
    intros k j m Hj Hm. unfold memk.
    apply (store_ok_at SEGS MB d (Z.to_nat n)); try assumption; try lia.
  Qed.

  Lemma memk_extend1 : forall k, (0 <= k)%Z -> (k + 1 <= W)%Z ->
    wbytes (memk k) (at_ d k) [B_ k] = memk (k + 1).
  Proof.
    intros k Hk H1. unfold memk, B_.
    rewrite <- (sub_nth src (Z.to_nat k)) by lia.
    replace (at_ d k) with (at_ d (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
    rewrite wbytes_extend' by lia. f_equal. f_equal. lia.
  Qed.

  Lemma memk_extend8 : forall k, (0 <= k)%Z -> (k + 8 <= W)%Z ->
    wbytes (memk k) (at_ d k) (SB k 8) = memk (k + 8).
  Proof.
    intros k Hk H8. unfold memk, SB.
    replace (at_ d k) with (at_ d (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
    rewrite wbytes_extend' by lia. f_equal. f_equal. lia.
  Qed.

  Lemma memk_out : forall k (x : word), (0 <= k <= n)%Z ->
    (bv_unsigned x < ud \/ ud + n <= bv_unsigned x)%Z -> memk k x = MB x.
  Proof.
    intros k x Hk Hx. unfold memk. pose proof (u64_range d).
    assert (HL : (Z.of_nat (length (firstn (Z.to_nat k) src)) <= k)%Z) by (rewrite length_firstn; lia).
    apply MemSplit.wbytes_outside; lia.
  Qed.

  Lemma ro_k : forall k, (0 <= k <= n)%Z -> rodata_clear (memk k).
  Proof.
    intros k Hk i Hi. rewrite memk_out; [apply Hro; exact Hi | lia |].
    rewrite u_Z2bv by lia. lia.
  Qed.

  Lemma SB_len : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= W)%Z -> length (SB j m) = m.
  Proof. intros j m Hj Hm. unfold SB. apply sub_length. lia. Qed.

  Lemma SB_nth : forall j (i : nat), (0 <= j)%Z -> (i < 8)%nat -> (j + 8 <= W)%Z ->
    nth i (SB j 8) B0 = B_ (j + Z.of_nat i).
  Proof. intros j i Hj Hi H8. unfold SB, B_. rewrite nth_sub by lia. f_equal. lia. Qed.

  (* [comment removed for export] *)
  Lemma fin_eq : forall m c, (0 <= m <= n)%Z -> (m <= W)%Z ->
    (c = m \/ (c = m + 1 /\ m < n /\ m + 1 <= W))%Z ->
    wbytes (memk c) (at_ d m) (zeros (Z.to_nat (n - m))) = FIN m.
  Proof.
    intros m c Hm HmW Hc. unfold FIN.
    rewrite wbytes_app. rewrite len_firstn_k by lia.
    replace (Z.of_nat (Z.to_nat m)) with m by lia.
    destruct Hc as [-> | (-> & Hmn & HmW1)]; [reflexivity|].
    rewrite <- memk_extend1 by lia.
    destruct (Z.to_nat (n - m)) as [|z] eqn:E; [lia|]. cbn [zeros repeat].
    apply wbytes_shadow1.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma c_lbu : forall regs pc w rd rs (imm : bv 12) k j0 j,
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= k <= W)%Z -> (k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= W)%Z ->
    RiscvSemantics.step SEGS (mkst regs pc (memk k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (B_ j))) (v_addi pc 4) (memk k) rom).
  Proof.
    intros regs pc w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hkn Hj0 Hj1.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs, at_addi, Hj. apply rd_src1; lia.
  Qed.

  Lemma c_ld : forall regs pc w rd rs (imm : bv 12) k j0 j,
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
    getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= k <= W)%Z -> (k <= n)%Z -> (0 <= j)%Z -> (j + 8 <= W)%Z ->
    RiscvSemantics.step SEGS (mkst regs pc (memk k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LDv (SB j 8))) (v_addi pc 4) (memk k) rom).
  Proof.
    intros regs pc w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hkn Hj0 Hj8.
    eapply step_ld; [exact Hf | exact He | exact Hd | |].
    - rewrite Hrs, at_addi, Hj. apply (rd_src k j 8); lia.
    - symmetry. apply u_LDv. apply SB_len; lia.
  Qed.

  Lemma c_sb : forall regs pc w rs1 rs2 (imm : bv 12) k k0,
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ d k0 -> (k0 + bv_signed imm = k)%Z ->
    getr regs rs2 = LBv (B_ k) ->
    (0 <= k)%Z -> (k + 1 <= n)%Z -> (k + 1 <= W)%Z ->
    RiscvSemantics.step SEGS (mkst regs pc (memk k) rom) =
    MachineOk (mkst regs (v_addi pc 4) (memk (k + 1)) rom).
  Proof.
    intros regs pc w rs1 rs2 imm k k0 Hf He Hd Hrs1 Hk Hrs2 Hk0 Hk1 HkW.
    rewrite <- memk_extend1 by lia.
    eapply MmapSim.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | apply sb_byte_LBv |].
    - rewrite Hrs1, at_addi, Hk. reflexivity.
    - apply wr_dst; lia.
  Qed.

  Lemma c_sd : forall regs pc w rs1 rs2 (imm : bv 12) k k0,
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ d k0 -> (k0 + bv_signed imm = k)%Z ->
    getr regs rs2 = LDv (SB k 8) ->
    (0 <= k)%Z -> (k + 8 <= n)%Z -> (k + 8 <= W)%Z ->
    RiscvSemantics.step SEGS (mkst regs pc (memk k) rom) =
    MachineOk (mkst regs (v_addi pc 4) (memk (k + 8)) rom).
  Proof.
    intros regs pc w rs1 rs2 imm k k0 Hf He Hd Hrs1 Hk Hrs2 Hk0 Hk8 HkW.
    rewrite <- memk_extend8 by lia. rewrite <- (sd_bytes_LDv (SB k 8)) by (apply SB_len; lia).
    eapply step_sd_at; [exact Hf | exact He | exact Hd | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Hk. reflexivity.
    - apply wr_dst; lia.
  Qed.

  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply c_lbu with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mld F D jj :=
    chain_step; [reflexivity
      | eapply c_ld with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac msb F D :=
    chain_step; [reflexivity
      | eapply c_sb;
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia
        | gres; rwH; reflexivity | lia | lia | lia]
      | step_simpl].
  Ltac msd F D :=
    chain_step; [reflexivity
      | eapply c_sd;
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia
        | gres; rwH; reflexivity | lia | lia | lia]
      | step_simpl].
  Ltac cond := try unfold v_addi; cond_lia.
  Ltac litbv := lazymatch goal with |- Z_to_bv 64 ?z = @BV _ _ _ => is_Z_lit z; apply bv_eq; vm_compute; reflexivity end.
  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try litbv; try (symmetry; apply at_0);
               try (f_equal; lia); try (unfold v_addi; unorm; f_equal; lia).

  (* [comment removed for export] *)
  Definition POST (regs0 r : bvmap 5 word) (m : Z) : Prop :=
    SPEC m /\ getr r 8 = at_ d m /\ regs_agree (fun x => In x core_clob) regs0 r.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ret_ok_23730 : ret_ok (0x23d20 : word).
  Proof. apply bv_eq. vm_compute. reflexivity. Qed.

  Lemma tail_run : forall regs0 regs m c,
    SPEC m -> (c = m \/ (c = m + 1 /\ m < n /\ m + 1 <= W))%Z ->
    getr regs 8 = at_ d m -> getr regs 13 = Z_to_bv 64 (n - m) ->
    regs_agree (fun x => In x core_clob) regs0 regs ->
    exists r (m' : Z),
      msteps SEGS (mkst regs (0x23d10 : word) (memk c) rom) (mkst r (0x23d20 : word) (FIN m') rom)
      /\ POST regs0 r m'.
  Proof.
    intros regs0 regs m c HS Hc H8 H13 AG. pose proof HS as (Hm & HmW & _ & _).
    pose proof (u64_range d) as Hd.
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23a44 : word) (memk c) rom)
             (fun r => getr r 1 = (0x23d20 : word) /\ getr r 10 = at_ d m /\ getr r 11 = Z_to_bv 64 0
                       /\ getr r 12 = Z_to_bv 64 (n - m) /\ getr r 8 = at_ d m
                       /\ regs_agree (fun x => In x core_clob) regs0 r)
             (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
    - eexists. split.
      + stepn F_23d10 D_23d10.              (* [comment removed for export] *)
        stepn F_23d14 D_23d14.              (* [comment removed for export] *)
        stepn F_23d18 D_23d18.              (* [comment removed for export] *)
        stepn F_23d1c D_23d1c.              (* [comment removed for export] *)
        apply mst_refl.
      + post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
    - cbv beta. intros r1 (R1 & R10 & R11 & R12 & R8 & AG1).
      destruct (ref_memset0 (memk c) (at_ d m) (n - m) rom ltac:(lia)
                  ltac:(rewrite at_u by lia; lia)
                  ltac:(apply wr_dst; lia)
                  r1 (0x23d20 : word) ret_ok_23730 R1 R10 R11 R12) as (r2 & RUN & AG2).
      exists r2, m. split.
      + rewrite (fin_eq m c) in RUN by assumption. exact RUN.
      + split; [exact HS|]. split.
        * rewrite (AG2 8%bv) by (unfold memset_clob; cbn [In]; intros HH; decompose [or] HH; try discriminate; auto). exact R8.
        * eapply regs_agree_trans; [exact AG1|]. eapply regs_agree_mono; [|exact AG2].
          unfold memset_clob, core_clob. cbn [In]. intros x HH. decompose [or] HH; subst; auto 20.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma room_byte : forall k, (0 <= k < n)%Z ->
    (forall j, (0 <= j < k)%Z -> bv_unsigned (B_ j) <> 0%Z) -> (k + 1 <= W)%Z.
  Proof.
    intros k Hk Hnz. destruct Hroom as [HW | (K & HK & HzK & HsK)]; [lia|].
    destruct (Z_lt_le_dec K k) as [Hl|Hl]; [|lia]. exfalso. apply (Hnz K); [lia | exact HzK].
  Qed.

  Lemma room_word : forall k t, (0 <= k)%Z -> (k + 8 <= n)%Z -> (us + k = 8 * t)%Z ->
    (forall j, (0 <= j < k)%Z -> bv_unsigned (B_ j) <> 0%Z) -> (k + 8 <= W)%Z.
  Proof.
    intros k t Hk Hkn Ht Hnz. pose proof (u64_range s) as Hs.
    destruct Hroom as [HW | (K & HK & HzK & HsK)]; [lia|].
    assert (HkK : (k <= K)%Z).
    { destruct (Z_lt_le_dec K k) as [Hl|Hl]; [|lia]. exfalso. apply (Hnz K); [lia | exact HzK]. }
    pose proof (hd_facts us ltac:(lia)) as (q & A & Bq & C).
    destruct (Z_lt_le_dec K (hd us)) as [HKh|HKh].
    - exfalso. clear -Hk HkK HKh A Bq Ht. lia.
    - destruct (span_word us K ltac:(lia) HKh) as (tK & EK & RK).
      pose proof (al_le tK t (us + K) RK ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma b_loop : forall (cnt : nat) regs0 regs k,
    (Z.of_nat cnt = n - k)%Z -> (0 <= k < n)%Z -> (k <= W)%Z ->
    (forall j, (0 <= j < k)%Z -> bv_unsigned (B_ j) <> 0%Z) ->
    getr regs 11 = at_ s k -> getr regs 8 = at_ d k -> getr regs 13 = Z_to_bv 64 (n - k) ->
    regs_agree (fun x => In x core_clob) regs0 regs ->
    exists r (m' : Z),
      msteps SEGS (mkst regs (0x23c50 : word) (memk k) rom) (mkst r (0x23d20 : word) (FIN m') rom)
      /\ POST regs0 r m'.
  Proof.
    induction cnt as [|cnt IH]; intros regs0 regs k Hcnt Hk HkW Hnz H11 H8 H13 AG; [lia|].
    pose proof (u64_range s) as Hs. pose proof (u64_range d) as Hd.
    pose proof (room_byte k Hk Hnz) as HR. pose proof (u8_range (B_ k)) as U.
    destruct (Z.eq_dec (bv_unsigned (B_ k)) 0) as [Hz|Hnzk].
    - (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23d10 : word) (memk (k + 1)) rom)
               (fun r => getr r 8 = at_ d k /\ getr r 13 = Z_to_bv 64 (n - k)
                         /\ regs_agree (fun x => In x core_clob) regs0 r)
               (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
      + eexists. split.
        * mlbu F_23c50 D_23c50 k.            (* [comment removed for export] *)
          msb F_23c54 D_23c54.               (* [comment removed for export] *)
          stepb_tk F_23c58 D_23c58 ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_eq; exact Hz).  (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
      + cbv beta. intros r1 (R8 & R13 & AG1).
        apply (tail_run regs0 r1 k (k + 1)); try assumption; try lia.
        split; [lia|]. split; [lia|]. split; [exact Hnz | intros _; exact Hz].
    - destruct (Z.eq_dec (k + 1) n) as [Hlast|Hmore].
      + (* [comment removed for export] *)
        eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23d10 : word) (memk (k + 1)) rom)
                 (fun r => getr r 8 = at_ d (k + 1) /\ getr r 13 = Z_to_bv 64 (n - (k + 1))
                           /\ regs_agree (fun x => In x core_clob) regs0 r)
                 (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
        * eexists. split.
          -- mlbu F_23c50 D_23c50 k.
             msb F_23c54 D_23c54.
             stepb_ft F_23c58 D_23c58 ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_neq; exact Hnzk).  (* [comment removed for export] *)
             sv F_23c5c D_23c5c (Z_to_bv 64 (n - (k + 1))).   (* [comment removed for export] *)
             stepn F_23c60 D_23c60.             (* [comment removed for export] *)
             stepn F_23c64 D_23c64.             (* [comment removed for export] *)
             stepb_ft F_23c68 D_23c68 ltac:(cond).   (* [comment removed for export] *)
             stepn F_23c6c D_23c6c.             (* [comment removed for export] *)
             apply mst_refl.
          -- post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
        * cbv beta. intros r1 (R8 & R13 & AG1).
          apply (tail_run regs0 r1 (k + 1) (k + 1)); try assumption; try lia.
          split; [lia|]. split; [lia|]. split; [|intros; lia].
          intros j Hj. destruct (Z.eq_dec j k) as [->|]; [exact Hnzk | apply Hnz; lia].
      + (* [comment removed for export] *)
        eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23c50 : word) (memk (k + 1)) rom)
                 (fun r => getr r 11 = at_ s (k + 1) /\ getr r 8 = at_ d (k + 1) /\ getr r 13 = Z_to_bv 64 (n - (k + 1))
                           /\ regs_agree (fun x => In x core_clob) regs0 r)
                 (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
        * eexists. split.
          -- mlbu F_23c50 D_23c50 k.
             msb F_23c54 D_23c54.
             stepb_ft F_23c58 D_23c58 ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_neq; exact Hnzk).
             sv F_23c5c D_23c5c (Z_to_bv 64 (n - (k + 1))).
             stepn F_23c60 D_23c60.
             stepn F_23c64 D_23c64.
             stepb_tk F_23c68 D_23c68 ltac:(cond).   (* [comment removed for export] *)
             apply mst_refl.
          -- post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
        * cbv beta. intros r1 (R11 & R8 & R13 & AG1).
          apply (IH regs0 r1 (k + 1)%Z ltac:(lia) ltac:(lia) ltac:(lia)); try assumption.
          intros j Hj. destruct (Z.eq_dec j k) as [->|]; [exact Hnzk | apply Hnz; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma b_entry_c : forall regs0 regs k,
    (0 <= k < n)%Z -> (k <= W)%Z ->
    (forall j, (0 <= j < k)%Z -> bv_unsigned (B_ j) <> 0%Z) ->
    getr regs 11 = at_ s k -> getr regs 8 = at_ d k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    regs_agree (fun x => In x core_clob) regs0 regs ->
    exists r (m' : Z),
      msteps SEGS (mkst regs (0x23c4c : word) (memk k) rom) (mkst r (0x23d20 : word) (FIN m') rom)
      /\ POST regs0 r m'.
  Proof.
    intros regs0 regs k Hk HkW Hnz H11 H8 H12 AG.
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23c50 : word) (memk k) rom)
             (fun r => getr r 11 = at_ s k /\ getr r 8 = at_ d k /\ getr r 13 = Z_to_bv 64 (n - k)
                       /\ regs_agree (fun x => In x core_clob) regs0 r)
             (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
    - eexists. split.
      + stepn F_23c4c D_23c4c.               (* [comment removed for export] *)
        apply mst_refl.
      + post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
    - cbv beta. intros r1 (R11 & R8 & R13 & AG1).
      apply (b_loop (Z.to_nat (n - k)) regs0 r1 k ltac:(lia) Hk HkW Hnz); assumption.
  Qed.

  Lemma b_entry : forall regs0 regs k,
    (0 <= k <= n)%Z -> (k <= W)%Z ->
    (forall j, (0 <= j < k)%Z -> bv_unsigned (B_ j) <> 0%Z) ->
    getr regs 11 = at_ s k -> getr regs 8 = at_ d k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    regs_agree (fun x => In x core_clob) regs0 regs ->
    exists r (m' : Z),
      msteps SEGS (mkst regs (0x23c48 : word) (memk k) rom) (mkst r (0x23d20 : word) (FIN m') rom)
      /\ POST regs0 r m'.
  Proof.
    intros regs0 regs k Hk HkW Hnz H11 H8 H12 AG. pose proof (u64_range d) as Hd.
    destruct (Z.eq_dec k n) as [->|Hkn].
    - (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23d10 : word) (memk n) rom)
               (fun r => getr r 8 = at_ d n /\ getr r 13 = Z_to_bv 64 (n - n)
                         /\ regs_agree (fun x => In x core_clob) regs0 r)
               (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
      + eexists. split.
        * stepb_tk F_23c48 D_23c48 ltac:(cond).    (* [comment removed for export] *)
          stepn F_23d0c D_23d0c.                   (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
      + cbv beta. intros r1 (R8 & R13 & AG1).
        apply (tail_run regs0 r1 n n); try assumption; try lia.
        split; [lia|]. split; [lia|]. split; [exact Hnz | intros; lia].
    - eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23c4c : word) (memk k) rom)
               (fun r => getr r 11 = at_ s k /\ getr r 8 = at_ d k /\ getr r 12 = Z_to_bv 64 (n - k)
                         /\ regs_agree (fun x => In x core_clob) regs0 r)
               (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
      + eexists. split.
        * stepb_ft F_23c48 D_23c48 ltac:(cond).    (* [comment removed for export] *)
          apply mst_refl.
        * post. exact AG.
      + cbv beta. intros r1 (R11 & R8 & R12 & AG1).
        apply (b_entry_c regs0 r1 k); try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma zero_in_word : forall k, (0 <= k)%Z ->
    (exists i : nat, (i < 8)%nat /\ bv_unsigned (B_ (k + Z.of_nat i)) = 0%Z
                     /\ forall j : nat, (j < i)%nat -> bv_unsigned (B_ (k + Z.of_nat j)) <> 0%Z)
    \/ (forall i : nat, (i < 8)%nat -> bv_unsigned (B_ (k + Z.of_nat i)) <> 0%Z).
  Proof.
    intros k Hk.
    destruct (existsb (fun i => (bv_unsigned (B_ (k + Z.of_nat i)) =? 0)%Z) (seq 0 8)) eqn:E.
    - left. apply existsb_exists in E as (i0 & Hi0 & E0). apply in_seq in Hi0. apply Z.eqb_eq in E0.
      (* [comment removed for export] *)
      assert (HF : forall m : nat, (m <= 8)%nat ->
        (exists i : nat, (i < m)%nat /\ bv_unsigned (B_ (k + Z.of_nat i)) = 0%Z
                         /\ forall j : nat, (j < i)%nat -> bv_unsigned (B_ (k + Z.of_nat j)) <> 0%Z)
        \/ (forall i : nat, (i < m)%nat -> bv_unsigned (B_ (k + Z.of_nat i)) <> 0%Z)).
      { induction m as [|m IH]; intros Hm; [right; intros; lia|].
        destruct (IH ltac:(lia)) as [(i & Hi & Zi & NZ)|ALL].
        - left. exists i. repeat split; try assumption. lia.
        - destruct (Z.eq_dec (bv_unsigned (B_ (k + Z.of_nat m))) 0) as [Zm|NZm].
          + left. exists m. repeat split; try assumption; try lia.
          + right. intros i Hi. destruct (Nat.eq_dec i m) as [->|]; [exact NZm | apply ALL; lia]. }
      destruct (HF 8%nat ltac:(lia)) as [H|ALL]; [exact H|]. exfalso. apply (ALL i0); [lia | exact E0].
    - right. intros i Hi Zi.
      assert (existsb (fun i => (bv_unsigned (B_ (k + Z.of_nat i)) =? 0)%Z) (seq 0 8) = true); [|congruence].
      apply existsb_exists. exists i. split; [apply in_seq; lia | apply Z.eqb_eq; exact Zi].
  Qed.

  Ltac condw_hit i :=
    rwH;
    lazymatch goal with |- c_eq (v_and (v_or (v_sub _ ?x) _) _) _ = ?b =>
      change (c_eq (TW0 x) (Z_to_bv 64 Hc) = b); rewrite TW0_TW end;
    apply (TW_haszero _ i); [apply SB_len; lia | lia | rewrite SB_nth by lia; assumption
                            | intros jj Hjj; rewrite SB_nth by lia; auto].
  Ltac condw_miss :=
    rwH;
    lazymatch goal with |- c_eq (v_and (v_or (v_sub _ ?x) _) _) _ = ?b =>
      change (c_eq (TW0 x) (Z_to_bv 64 Hc) = b); rewrite TW0_TW end;
    apply TW_nozero; [apply SB_len; lia | intros jj Hjj; rewrite SB_nth by lia; auto].

  Lemma w_loop : forall (cnt : nat) regs0 regs k t,
    (Z.of_nat cnt = n - k)%Z -> (0 <= k)%Z -> (k + 8 <= n)%Z -> (us + k = 8 * t)%Z ->
    (forall j, (0 <= j < k)%Z -> bv_unsigned (B_ j) <> 0%Z) ->
    getr regs 11 = at_ s k -> getr regs 8 = at_ d k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 13 = Z_to_bv 64 Mc -> getr regs 14 = Z_to_bv 64 Hc -> getr regs 15 = Z_to_bv 64 7 ->
    regs_agree (fun x => In x core_clob) regs0 regs ->
    exists r (m' : Z),
      msteps SEGS (mkst regs (0x23ce0 : word) (memk k) rom) (mkst r (0x23d20 : word) (FIN m') rom)
      /\ POST regs0 r m'.
  Proof.
    induction cnt as [cnt IH] using (well_founded_induction Wf_nat.lt_wf).
    intros regs0 regs k t Hcnt Hk Hkn Ht Hnz H11 H8 H12 H13 H14 H15 AG.
    pose proof (u64_range s) as Hs. pose proof (u64_range d) as Hd.
    pose proof (room_word k t Hk Hkn Ht Hnz) as HR.
    destruct (zero_in_word k Hk) as [(i & Hi & Zi & NZi) | ALL].
    - (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23c4c : word) (memk k) rom)
               (fun r => getr r 11 = at_ s k /\ getr r 8 = at_ d k /\ getr r 12 = Z_to_bv 64 (n - k)
                         /\ regs_agree (fun x => In x core_clob) regs0 r)
               (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
      + eexists. split.
        * mld F_23ce0 D_23ce0 k.                     (* [comment removed for export] *)
          stepn F_23ce4 D_23ce4.                      (* [comment removed for export] *)
          stepn F_23ce8 D_23ce8.                      (* [comment removed for export] *)
          stepn F_23cec D_23cec.                      (* [comment removed for export] *)
          stepb_tk F_23cf0 D_23cf0 ltac:(condw_hit i).  (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
      + cbv beta. intros r1 (R11 & R8 & R12 & AG1).
        apply (b_entry_c regs0 r1 k); try assumption; lia.
    - (* [comment removed for export] *)
      destruct (Z_lt_le_dec 7 (n - k - 8)) as [Hmore|Hlast].
      + eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23ce0 : word) (memk (k + 8)) rom)
                 (fun r => getr r 11 = at_ s (k + 8) /\ getr r 8 = at_ d (k + 8) /\ getr r 12 = Z_to_bv 64 (n - (k + 8))
                           /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc /\ getr r 15 = Z_to_bv 64 7
                           /\ regs_agree (fun x => In x core_clob) regs0 r)
                 (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
        * eexists. split.
          -- mld F_23ce0 D_23ce0 k.
             stepn F_23ce4 D_23ce4.
             stepn F_23ce8 D_23ce8.
             stepn F_23cec D_23cec.
             stepb_ft F_23cf0 D_23cf0 ltac:(condw_miss).   (* [comment removed for export] *)
             msd F_23cf4 D_23cf4.                          (* [comment removed for export] *)
             sv F_23cf8 D_23cf8 (Z_to_bv 64 (n - (k + 8))).   (* [comment removed for export] *)
             stepn F_23cfc D_23cfc.                        (* [comment removed for export] *)
             stepn F_23d00 D_23d00.                        (* [comment removed for export] *)
             stepb_tk F_23d04 D_23d04 ltac:(cond).         (* [comment removed for export] *)
             apply mst_refl.
          -- post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
        * cbv beta. intros r1 (R11 & R8 & R12 & R13 & R14 & R15 & AG1).
          apply (IH (Z.to_nat (n - (k + 8))) ltac:(lia) regs0 r1 (k + 8)%Z (t + 1)%Z); try assumption; try lia.
          intros j Hj. destruct (Z_lt_le_dec j k) as [Hl|Hl]; [apply Hnz; lia|].
          replace j with (k + Z.of_nat (Z.to_nat (j - k)))%Z by lia. apply ALL. lia.
      + eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23c48 : word) (memk (k + 8)) rom)
                 (fun r => getr r 11 = at_ s (k + 8) /\ getr r 8 = at_ d (k + 8) /\ getr r 12 = Z_to_bv 64 (n - (k + 8))
                           /\ regs_agree (fun x => In x core_clob) regs0 r)
                 (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
        * eexists. split.
          -- mld F_23ce0 D_23ce0 k.
             stepn F_23ce4 D_23ce4.
             stepn F_23ce8 D_23ce8.
             stepn F_23cec D_23cec.
             stepb_ft F_23cf0 D_23cf0 ltac:(condw_miss).
             msd F_23cf4 D_23cf4.
             sv F_23cf8 D_23cf8 (Z_to_bv 64 (n - (k + 8))).
             stepn F_23cfc D_23cfc.
             stepn F_23d00 D_23d00.
             stepb_ft F_23d04 D_23d04 ltac:(cond).         (* [comment removed for export] *)
             stepn F_23d08 D_23d08.                        (* [comment removed for export] *)
             apply mst_refl.
          -- post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
        * cbv beta. intros r1 (R11 & R8 & R12 & AG1).
          apply (b_entry regs0 r1 (k + 8)%Z); try assumption; try lia.
          intros j Hj. destruct (Z_lt_le_dec j k) as [Hl|Hl]; [apply Hnz; lia|].
          replace j with (k + Z.of_nat (Z.to_nat (j - k)))%Z by lia. apply ALL. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac ldc F D vv RD :=
    chain_step; [reflexivity
      | eapply step_ld with (v := vv);
        [exact F | reflexivity | exact D
        | gres; imm_norm;
          lazymatch goal with |- rdn _ _ ?a _ = _ =>
            lazymatch type of RD with rdn _ _ ?c _ = _ =>
              replace a with c by (apply bv_eq; vm_compute; reflexivity) end end;
          exact RD
        | assumption ]
      | step_simpl]; vnorm.

  Lemma j_run : forall regs0 regs k (e : Z),
    (0 <= k <= n)%Z -> (k <= W)%Z ->
    ((e = 0 /\ k = n) \/ (e = 1 /\ k < n /\ exists t, us + k = 8 * t))%Z ->
    (forall j, (0 <= j < k)%Z -> bv_unsigned (B_ j) <> 0%Z) ->
    getr regs 11 = at_ s k -> getr regs 8 = at_ d k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = Z_to_bv 64 e ->
    regs_agree (fun x => In x core_clob) regs0 regs ->
    exists r (m' : Z),
      msteps SEGS (mkst regs (0x23cb8 : word) (memk k) rom) (mkst r (0x23d20 : word) (FIN m') rom)
      /\ POST regs0 r m'.
  Proof.
    intros regs0 regs k e Hk HkW He Hnz H11 H8 H12 H14 AG.
    pose proof (u64_range s) as Hs. pose proof (u64_range d) as Hd.
    destruct He as [(-> & ->) | (-> & Hkn & (t & Ht))].
    - (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23d10 : word) (memk n) rom)
               (fun r => getr r 8 = at_ d n /\ getr r 13 = Z_to_bv 64 (n - n)
                         /\ regs_agree (fun x => In x core_clob) regs0 r)
               (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
      + eexists. split.
        * stepb_tk F_23cb8 D_23cb8 ltac:(cond).    (* [comment removed for export] *)
          stepn F_23d0c D_23d0c.                   (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
      + cbv beta. intros r1 (R8 & R13 & AG1).
        apply (tail_run regs0 r1 n n); try assumption; try lia.
        split; [lia|]. split; [lia|]. split; [exact Hnz | intros; lia].
    - pose proof (room_byte k ltac:(lia) Hnz) as HR. pose proof (u8_range (B_ k)) as U.
      destruct (Z.eq_dec (bv_unsigned (B_ k)) 0) as [Hz|Hnzk].
      + (* [comment removed for export] *)
        eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23d10 : word) (memk k) rom)
                 (fun r => getr r 8 = at_ d k /\ getr r 13 = Z_to_bv 64 (n - k)
                           /\ regs_agree (fun x => In x core_clob) regs0 r)
                 (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
        * eexists. split.
          -- stepb_ft F_23cb8 D_23cb8 ltac:(cond).    (* [comment removed for export] *)
             mlbu F_23cbc D_23cbc k.                    (* [comment removed for export] *)
             stepb_tk F_23cc0 D_23cc0 ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_eq; exact Hz).  (* [comment removed for export] *)
             stepn F_23d34 D_23d34.                     (* [comment removed for export] *)
             stepn F_23d38 D_23d38.                     (* [comment removed for export] *)
             apply mst_refl.
          -- post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
        * cbv beta. intros r1 (R8 & R13 & AG1).
          apply (tail_run regs0 r1 k k); try assumption; try lia.
          split; [lia|]. split; [lia|]. split; [exact Hnz | intros _; exact Hz].
      + destruct (Z_lt_le_dec (n - k) 8) as [Hsmall|Hbig].
        * (* [comment removed for export] *)
          eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23c48 : word) (memk k) rom)
                   (fun r => getr r 11 = at_ s k /\ getr r 8 = at_ d k /\ getr r 12 = Z_to_bv 64 (n - k)
                             /\ regs_agree (fun x => In x core_clob) regs0 r)
                   (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
          -- eexists. split.
             ++ stepb_ft F_23cb8 D_23cb8 ltac:(cond).
                mlbu F_23cbc D_23cbc k.
                stepb_ft F_23cc0 D_23cc0 ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_neq; exact Hnzk).
                stepn F_23cc4 D_23cc4.                  (* [comment removed for export] *)
                stepb_tk F_23cc8 D_23cc8 ltac:(cond).   (* [comment removed for export] *)
                apply mst_refl.
             ++ post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
          -- cbv beta. intros r1 (R11 & R8 & R12 & AG1).
             apply (b_entry regs0 r1 k); try assumption; lia.
        * (* [comment removed for export] *)
          destruct (rd_const_M (memk k) (ro_k k ltac:(lia))) as (bsM & RM & EM).
          destruct (rd_const_H (memk k) (ro_k k ltac:(lia))) as (bsH & RH & EH).
          eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23ce0 : word) (memk k) rom)
                   (fun r => getr r 11 = at_ s k /\ getr r 8 = at_ d k /\ getr r 12 = Z_to_bv 64 (n - k)
                             /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc /\ getr r 15 = Z_to_bv 64 7
                             /\ regs_agree (fun x => In x core_clob) regs0 r)
                   (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
          -- eexists. split.
             ++ stepb_ft F_23cb8 D_23cb8 ltac:(cond).
                mlbu F_23cbc D_23cbc k.
                stepb_ft F_23cc0 D_23cc0 ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_neq; exact Hnzk).
                stepn F_23cc4 D_23cc4.                  (* [comment removed for export] *)
                stepb_ft F_23cc8 D_23cc8 ltac:(cond).   (* [comment removed for export] *)
                stepn F_23ccc D_23ccc.                  (* [comment removed for export] *)
                stepn F_23cd0 D_23cd0.                  (* [comment removed for export] *)
                ldc F_23cd4 D_23cd4 (Z_to_bv 64 Mc) RM. (* [comment removed for export] *)
                ldc F_23cd8 D_23cd8 (Z_to_bv 64 Hc) RH. (* [comment removed for export] *)
                stepn F_23cdc D_23cdc.                  (* [comment removed for export] *)
                apply mst_refl.
             ++ post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
          -- cbv beta. intros r1 (R11 & R8 & R12 & R13 & R14 & R15 & AG1).
             apply (w_loop (Z.to_nat (n - k)) regs0 r1 k t); try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma v_sltu0 : forall z, (0 <= z < 2 ^ 64)%Z ->
    v_sltu (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 (if (z =? 0)%Z then 0 else 1).
  Proof.
    intros z Hz. unfold v_sltu, c_ltu, bv_ltu. rewrite (u_Z2bv 0), (u_Z2bv z) by lia.
    destruct (Z.eqb_spec z 0) as [->|Hne]; [reflexivity|].
    replace (0 <? z)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  Qed.

  Lemma h_loop : forall (cnt : nat) regs0 regs k q,
    (Z.of_nat cnt = hd us - k)%Z -> (0 <= k < n)%Z -> (k < hd us)%Z -> (us + hd us = 8 * q)%Z -> (k <= W)%Z ->
    (forall j, (0 <= j < k)%Z -> bv_unsigned (B_ j) <> 0%Z) ->
    getr regs 11 = at_ s k -> getr regs 8 = at_ d k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 15 = at_ s (k + 1) -> getr regs 16 = Z_to_bv 64 1 ->
    regs_agree (fun x => In x core_clob) regs0 regs ->
    exists r (m' : Z),
      msteps SEGS (mkst regs (0x23c88 : word) (memk k) rom) (mkst r (0x23d20 : word) (FIN m') rom)
      /\ POST regs0 r m'.
  Proof.
    induction cnt as [cnt IH] using (well_founded_induction Wf_nat.lt_wf).
    intros regs0 regs k q Hcnt Hk Hkh Hq HkW Hnz H11 H8 H12 H15 H16 AG.
    pose proof (u64_range s) as Hs. pose proof (u64_range d) as Hd.
    pose proof (hd_facts us ltac:(lia)) as (q' & A & Bq & C).
    pose proof (room_byte k Hk Hnz) as HR. pose proof (u8_range (B_ k)) as U.
    destruct (Z.eq_dec (bv_unsigned (B_ k)) 0) as [Hz|Hnzk].
    { (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23d10 : word) (memk (k + 1)) rom)
               (fun r => getr r 8 = at_ d k /\ getr r 13 = Z_to_bv 64 (n - k)
                         /\ regs_agree (fun x => In x core_clob) regs0 r)
               (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
      - eexists. split.
        + mlbu F_23c88 D_23c88 k.                 (* [comment removed for export] *)
          stepn F_23c8c D_23c8c.                   (* [comment removed for export] *)
          msb F_23c90 D_23c90.                     (* [comment removed for export] *)
          stepb_tk F_23c94 D_23c94 ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_eq; exact Hz).  (* [comment removed for export] *)
          apply mst_refl.
        + post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
      - cbv beta. intros r1 (R8 & R13 & AG1).
        apply (tail_run regs0 r1 k (k + 1)); try assumption; try lia.
        split; [lia|]. split; [lia|]. split; [exact Hnz | intros _; exact Hz]. }
    (* [comment removed for export] *)
    assert (Hnz' : forall j, (0 <= j < k + 1)%Z -> bv_unsigned (B_ j) <> 0%Z).
    { intros j Hj. destruct (Z.eq_dec j k) as [->|]; [exact Hnzk | apply Hnz; lia]. }
    destruct (Z.eq_dec (k + 1) (hd us)) as [Hal|Hnal].
    { (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23cb8 : word) (memk (k + 1)) rom)
               (fun r => getr r 11 = at_ s (k + 1) /\ getr r 8 = at_ d (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1))
                         /\ getr r 14 = Z_to_bv 64 (if (n - (k + 1) =? 0)%Z then 0 else 1)
                         /\ regs_agree (fun x => In x core_clob) regs0 r)
               (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
      - eexists. split.
        + mlbu F_23c88 D_23c88 k.
          stepn F_23c8c D_23c8c.
          msb F_23c90 D_23c90.
          stepb_ft F_23c94 D_23c94 ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_neq; exact Hnzk).
          sv F_23c98 D_23c98 (Z_to_bv 64 (n - (k + 1))).   (* [comment removed for export] *)
          stepn F_23c9c D_23c9c.                   (* [comment removed for export] *)
          stepn F_23ca0 D_23ca0.                   (* [comment removed for export] *)
          stepiv F_23ca4 D_23ca4 (Z_to_bv 64 0)
            ltac:(gres; rwH; imm_norm; unfold v_andi, at_; unorm;
                  change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; f_equal;
                  apply (mod8_mul _ q); lia).    (* [comment removed for export] *)
          stepsltu F_23ca8 D_23ca8 (Z_to_bv 64 (if (n - (k + 1) =? 0)%Z then 0 else 1))
            ltac:(gres; rwH; apply v_sltu0; lia).   (* [comment removed for export] *)
          stepb_tk F_23cac D_23cac ltac:(cond_lia).   (* [comment removed for export] *)
          apply mst_refl.
        + post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
      - cbv beta. intros r1 (R11 & R8 & R12 & R14 & AG1).
        apply (j_run regs0 r1 (k + 1) (if (n - (k + 1) =? 0)%Z then 0 else 1)); try assumption; try lia.
        destruct (Z.eqb_spec (n - (k + 1)) 0); [left; lia | right]. split; [reflexivity|]. split; [lia|]. exists q. lia. }
    destruct (Z.eq_dec (k + 1) n) as [Hlast|Hmore].
    { (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23cb8 : word) (memk (k + 1)) rom)
               (fun r => getr r 11 = at_ s (k + 1) /\ getr r 8 = at_ d (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1))
                         /\ getr r 14 = Z_to_bv 64 0
                         /\ regs_agree (fun x => In x core_clob) regs0 r)
               (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
      - eexists. split.
        + mlbu F_23c88 D_23c88 k.
          stepn F_23c8c D_23c8c.
          msb F_23c90 D_23c90.
          stepb_ft F_23c94 D_23c94 ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_neq; exact Hnzk).
          sv F_23c98 D_23c98 (Z_to_bv 64 (n - (k + 1))).
          stepn F_23c9c D_23c9c.
          stepn F_23ca0 D_23ca0.
          stepn F_23ca4 D_23ca4.                   (* [comment removed for export] *)
          stepsltu F_23ca8 D_23ca8 (Z_to_bv 64 0)
            ltac:(gres; rwH; rewrite v_sltu0 by lia; replace (n - (k + 1) =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
          stepb_ft F_23cac D_23cac
            ltac:(rwH; unfold c_eq, bv_eqb, v_andi, at_; unorm;
                  change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia;
                  pose proof (mod8_range (bv_unsigned s + (k + 1))); unorm;
                  apply mod8_C; apply (C (k + 1)%Z); lia).   (* [comment removed for export] *)
          stepn F_23cb0 D_23cb0.                   (* [comment removed for export] *)
          stepb_ft F_23cb4 D_23cb4 ltac:(cond).    (* [comment removed for export] *)
          apply mst_refl.
        + post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
      - cbv beta. intros r1 (R11 & R8 & R12 & R14 & AG1).
        apply (j_run regs0 r1 (k + 1) 0); try assumption; try lia. }
    (* [comment removed for export] *)
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23c88 : word) (memk (k + 1)) rom)
             (fun r => getr r 11 = at_ s (k + 1) /\ getr r 8 = at_ d (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1))
                       /\ getr r 15 = at_ s (k + 1 + 1) /\ getr r 16 = Z_to_bv 64 1
                       /\ regs_agree (fun x => In x core_clob) regs0 r)
             (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
    - eexists. split.
      + mlbu F_23c88 D_23c88 k.
        stepn F_23c8c D_23c8c.
        msb F_23c90 D_23c90.
        stepb_ft F_23c94 D_23c94 ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_neq; exact Hnzk).
        sv F_23c98 D_23c98 (Z_to_bv 64 (n - (k + 1))).
        stepn F_23c9c D_23c9c.
        stepn F_23ca0 D_23ca0.
        stepn F_23ca4 D_23ca4.
        stepn F_23ca8 D_23ca8.                     (* [comment removed for export] *)
        stepb_ft F_23cac D_23cac
          ltac:(rwH; unfold c_eq, bv_eqb, v_andi, at_; unorm;
                change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia;
                pose proof (mod8_range (bv_unsigned s + (k + 1))); unorm;
                apply mod8_C; apply (C (k + 1)%Z); lia).
        stepn F_23cb0 D_23cb0.                     (* [comment removed for export] *)
        stepb_tk F_23cb4 D_23cb4 ltac:(cond).      (* [comment removed for export] *)
        apply mst_refl.
      + post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
    - cbv beta. intros r1 (R11 & R8 & R12 & R15 & R16 & AG1).
      apply (IH (Z.to_nat (hd us - (k + 1))) ltac:(lia) regs0 r1 (k + 1)%Z q); try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma core_run : forall regs,
    getr regs 8 = d -> getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = Z_to_bv 64 n ->
    exists r (m' : Z),
      msteps SEGS (mkst regs (0x23c3c : word) MB rom) (mkst r (0x23d20 : word) (FIN m') rom)
      /\ POST regs r m'.
  Proof.
    intros regs H8 H10 H11 H12.
    pose proof (u64_range s) as Hs. pose proof (u64_range d) as Hd.
    pose proof (hd_facts us ltac:(lia)) as (q & A & Bq & C).
    change MB with (memk 0).
    destruct (c_eq (v_andi (v_xor s d) 7) (Z_to_bv 64 0)) eqn:EQ.
    2:{ (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23c48 : word) (memk 0) rom)
               (fun r => getr r 11 = at_ s 0 /\ getr r 8 = at_ d 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                         /\ regs_agree (fun x => In x core_clob) regs r)
               (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
      - eexists. split.
        + stepn F_23c3c D_23c3c.                   (* [comment removed for export] *)
          stepn F_23c40 D_23c40.                   (* [comment removed for export] *)
          stepb_ft F_23c44 D_23c44 ltac:(rwH; exact EQ).   (* [comment removed for export] *)
          apply mst_refl.
        + post; try (rewrite Z.sub_0_r; reflexivity). unfold core_clob. solve_regs_agree.
      - cbv beta. intros r1 (R11 & R8x & R12 & AG1).
        apply (b_entry regs r1 0); try assumption; try lia; try (intros; lia). }
    destruct (Z.eq_dec (hd us) 0) as [Hh0|Hh0].
    { (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23cb8 : word) (memk 0) rom)
               (fun r => getr r 11 = at_ s 0 /\ getr r 8 = at_ d 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                         /\ getr r 14 = Z_to_bv 64 (if (n =? 0)%Z then 0 else 1)
                         /\ regs_agree (fun x => In x core_clob) regs r)
               (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
      - eexists. split.
        + stepn F_23c3c D_23c3c.
          stepn F_23c40 D_23c40.
          stepb_tk F_23c44 D_23c44 ltac:(rwH; exact EQ).   (* [comment removed for export] *)
          stepiv F_23c70 D_23c70 (Z_to_bv 64 0)
            ltac:(gres; rwH; imm_norm; unfold v_andi; change (bv_wrap 64 7) with (Z.ones 3);
                  rewrite Z.land_ones by lia; f_equal; apply hd0_mod; lia).   (* [comment removed for export] *)
          stepsltu F_23c74 D_23c74 (Z_to_bv 64 (if (n =? 0)%Z then 0 else 1))
            ltac:(gres; rwH; apply v_sltu0; lia).   (* [comment removed for export] *)
          stepb_tk F_23c78 D_23c78 ltac:(cond_lia).  (* [comment removed for export] *)
          apply mst_refl.
        + post; try (rewrite Z.sub_0_r; reflexivity). unfold core_clob. solve_regs_agree.
      - cbv beta. intros r1 (R11 & R8x & R12 & R14 & AG1).
        apply (j_run regs r1 0 (if (n =? 0)%Z then 0 else 1)); try assumption; try lia; try (intros; lia).
        destruct (Z.eqb_spec n 0); [left; lia | right]. split; [reflexivity|]. split; [lia|]. exists q. lia. }
    destruct (Z.eq_dec n 0) as [Hn0|Hn0].
    { (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23cb8 : word) (memk 0) rom)
               (fun r => getr r 11 = at_ s 0 /\ getr r 8 = at_ d 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                         /\ getr r 14 = Z_to_bv 64 0
                         /\ regs_agree (fun x => In x core_clob) regs r)
               (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
      - eexists. split.
        + stepn F_23c3c D_23c3c.
          stepn F_23c40 D_23c40.
          stepb_tk F_23c44 D_23c44 ltac:(rwH; exact EQ).
          stepn F_23c70 D_23c70.                   (* [comment removed for export] *)
          stepsltu F_23c74 D_23c74 (Z_to_bv 64 0)
            ltac:(gres; rwH; rewrite v_sltu0 by lia; replace (n =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
          stepb_ft F_23c78 D_23c78
            ltac:(rwH; unfold c_eq, bv_eqb, v_andi; imm_norm; change (bv_wrap 64 7) with (Z.ones 3);
                  rewrite Z.land_ones by lia; pose proof (mod8_range (bv_unsigned s)); unorm;
                  apply hdnz_mod; lia).            (* [comment removed for export] *)
          stepb_tk F_23c7c D_23c7c ltac:(cond).    (* [comment removed for export] *)
          apply mst_refl.
        + post; try (rewrite Z.sub_0_r; reflexivity). unfold core_clob. solve_regs_agree.
      - cbv beta. intros r1 (R11 & R8x & R12 & R14 & AG1).
        apply (j_run regs r1 0 0); try assumption; try lia; try (intros; lia). }
    (* [comment removed for export] *)
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23c88 : word) (memk 0) rom)
             (fun r => getr r 11 = at_ s 0 /\ getr r 8 = at_ d 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                       /\ getr r 15 = at_ s (0 + 1) /\ getr r 16 = Z_to_bv 64 1
                       /\ regs_agree (fun x => In x core_clob) regs r)
             (fun r m' => mkst r (0x23d20 : word) (FIN m') rom)).
    - eexists. split.
      + stepn F_23c3c D_23c3c.
        stepn F_23c40 D_23c40.
        stepb_tk F_23c44 D_23c44 ltac:(rwH; exact EQ).
        stepn F_23c70 D_23c70.
        stepn F_23c74 D_23c74.
        stepb_ft F_23c78 D_23c78
          ltac:(rwH; unfold c_eq, bv_eqb, v_andi; imm_norm; change (bv_wrap 64 7) with (Z.ones 3);
                rewrite Z.land_ones by lia; pose proof (mod8_range (bv_unsigned s)); unorm;
                apply hdnz_mod; lia).
        stepb_ft F_23c7c D_23c7c ltac:(cond).      (* [comment removed for export] *)
        stepn F_23c80 D_23c80.                     (* [comment removed for export] *)
        stepn F_23c84 D_23c84.                     (* [comment removed for export] *)
        apply mst_refl.
      + post; try (rewrite Z.sub_0_r; reflexivity). unfold core_clob. solve_regs_agree.
    - cbv beta. intros r1 (R11 & R8x & R12 & R15 & R16 & AG1).
      apply (h_loop (Z.to_nat (hd us)) regs r1 0 q); try assumption; try lia; try (intros; lia).
  Qed.
End CORE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strncpy_clob : list reg := [11; 12; 13; 14; 15; 16; 17]%list.
Definition stpncpy_clob : list reg := [10; 11; 12; 13; 14; 15; 16; 17]%list.

(* [comment removed for export] *)
Record sncH (mem : word -> option byte) (d s sp : word) (n : Z) (src : list byte) : Prop := SNCH {
  Hsrc  : rdn SEGS mem s (length src) = Some src;
  Hroom : (n <= Z.of_nat (length src))%Z
          \/ exists K, (0 <= K < Z.of_nat (length src))%Z /\ bv_unsigned (nth (Z.to_nat K) src B0) = 0%Z
                       /\ (strlen_span (bv_unsigned s) K <= Z.of_nat (length src))%Z;
  Hdst  : store_ok SEGS mem d (Z.to_nat n) = true;
  Hn    : (0 <= n)%Z;
  Hnws  : (bv_unsigned s + Z.of_nat (length src) < 2 ^ 64)%Z;
  Hnwd  : (bv_unsigned d + n < 2 ^ 64)%Z;
  Hdisj : (bv_unsigned d + n <= bv_unsigned s \/ bv_unsigned s + Z.of_nat (length src) <= bv_unsigned d)%Z;
  Hro   : rodata_clear mem;
  Hdro  : (0x105a8 <= bv_unsigned d \/ bv_unsigned d + n <= 0x10588)%Z;
  Hstk  : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true;
  Hspro : (0x105a8 <= bv_unsigned sp - 32)%Z;
  Hsps  : (bv_unsigned sp <= bv_unsigned s \/ bv_unsigned s + Z.of_nat (length src) <= bv_unsigned sp - 32)%Z;
  Hspd  : (bv_unsigned sp <= bv_unsigned d \/ bv_unsigned d + n <= bv_unsigned sp - 32)%Z }.

Section WRAP.
  Variable mem : word -> option byte.
  Variables d s sp : word.
  Variable n : Z.
  Variable src : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : sncH mem d s sp n src.

  #[local] Notation usp := (bv_unsigned sp).
  #[local] Notation W8 v := (word_to_le_bytes 8 v).
  #[local] Notation W := (Z.of_nat (length src)).

  (* [comment removed for export] *)
  Definition MB (ra s0 : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes mem (Z_to_bv 64 (usp - 8)) (W8 ra)) (Z_to_bv 64 (usp - 16)) (W8 s0))
                   (Z_to_bv 64 (usp - 24)) (W8 (0x23c18 : word))) (Z_to_bv 64 (usp - 32)) (W8 d).
  (* [comment removed for export] *)
  Definition MF (ra s0 : word) (m : Z) : word -> option byte := FIN (MB ra s0) d n src m.

  Lemma lenW8 : forall v : word, length (W8 v) = 8%nat.
  Proof. intros v. apply length_N_to_le_bytes. Qed.

  Lemma MB_out : forall ra s0 (a : word),
    (bv_unsigned a < usp - 32 \/ usp <= bv_unsigned a)%Z -> MB ra s0 a = mem a.
  Proof.
    intros ra s0 a Ha. pose proof (u64_range sp). pose proof (Hspro _ _ _ _ _ _ HOK). unfold MB.
    rewrite !MemSplit.wbytes_outside; rewrite ?lenW8; u_norm; try lia. reflexivity.
  Qed.

  Lemma MB_core : forall ra s0,
    rdn SEGS (MB ra s0) s (length src) = Some src
    /\ store_ok SEGS (MB ra s0) d (Z.to_nat n) = true
    /\ rodata_clear (MB ra s0).
  Proof.
    intros ra s0. pose proof (u64_range sp). pose proof (u64_range s). destruct HOK. repeat split.
    - rewrite <- Hsrc0. apply rdn_ext; [lia|]. intros x Hx. apply MB_out. lia.
    - unfold MB. (try store_ok_peel_fast1; repeat (eapply store_ok_mono; [apply wbytes_grows|])). exact Hdst0.
    - intros i Hi. rewrite MB_out; [apply Hro0; exact Hi | u_norm; lia].
  Qed.

  Lemma MF_out : forall ra s0 m (a : word), (0 <= m <= n)%Z -> (m <= W)%Z ->
    (bv_unsigned a < bv_unsigned d \/ bv_unsigned d + n <= bv_unsigned a)%Z -> MF ra s0 m a = MB ra s0 a.
  Proof.
    intros ra s0 m a Hm HmW Ha. pose proof (u64_range d). pose proof (Hnwd _ _ _ _ _ _ HOK). unfold MF, FIN.
    apply MemSplit.wbytes_outside; rewrite length_app, length_firstn, length_zeros; lia.
  Qed.

  Lemma rd_slot : forall ra s0 m (k : Z) (v : word), (0 <= m <= n)%Z -> (m <= W)%Z ->
    ((k = 8%Z /\ v = ra) \/ (k = 16%Z /\ v = s0) \/ (k = 24%Z /\ v = (0x23c18 : word)) \/ (k = 32%Z /\ v = d)) ->
    rdn SEGS (MF ra s0 m) (Z_to_bv 64 (usp - k)) 8 = Some (W8 v).
  Proof.
    intros ra s0 m k v Hm HmW Hk. pose proof (u64_range sp). pose proof (Hspro _ _ _ _ _ _ HOK).
    pose proof (Hspd _ _ _ _ _ _ HOK).
    rewrite (rdn_ext SEGS 8 (MF ra s0 m) (MB ra s0)).
    2:{ u_norm. lia. }
    2:{ intros x Hx. apply MF_out; try lia. revert Hx. u_norm. lia. }
    unfold MB. destruct Hk as [(-> & ->)|[(-> & ->)|[(-> & ->)|(-> & ->)]]];
      repeat (rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia)); apply rdn_wbytes_hit8; u_norm; lia.
  Qed.

  Ltac okstk :=
    (try store_ok_peel_fast1; repeat (eapply store_ok_mono; [apply wbytes_grows|]));
    eapply (store_ok_sub SEGS mem (Z_to_bv 64 (usp - 32)) _ 32 8);
      [u_norm; lia | exact (Hstk _ _ _ _ _ _ HOK) | u_norm; lia | u_norm; cbn; lia].
  Ltac msd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; imm_norm; rwH; unfold v_addi; unorm; f_equal; lia
        | gres; rwH; reflexivity
        | okstk ]
      | step_simpl]; vnorm.
  Ltac mld8 F D vv RD :=
    chain_step; [reflexivity
      | eapply step_ld with (v := vv);
        [exact F | reflexivity | exact D
        | gres; imm_norm; rwH;
          lazymatch goal with |- rdn _ _ ?a _ = _ =>
            lazymatch type of RD with rdn _ _ ?c _ = _ =>
              replace a with c by (unfold v_addi; unorm; f_equal; lia) end end;
          exact RD
        | apply bytes_le_to_Z_8 ]
      | step_simpl]; vnorm.

  Theorem strncpy_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
    getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = Z_to_bv 64 n ->
    exists regs' (m : Z),
      msteps SEGS (mkst regs (0x23c04 : word) mem rom) (mkst regs' ret (MF ret (getr regs 8) m) rom)
      /\ regs_agree (fun x => In x strncpy_clob) regs regs'
      /\ SPEC n src m.
  Proof.
    intros regs ret Hret H1 H2 H10 H11 H12.
    pose proof (u64_range sp) as Hsp. pose proof (u64_range d) as Hd. pose proof (Hspro _ _ _ _ _ _ HOK) as Hspro'.
    set (s0 := getr regs 8).
    destruct (MB_core ret s0) as (C1 & C2 & C3).
    (* [comment removed for export] *)
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23c3c : word) (MB ret s0) rom)
             (fun r => getr r 1 = (0x23c18 : word) /\ getr r 2 = Z_to_bv 64 (usp - 32)
                       /\ getr r 8 = d /\ getr r 10 = d /\ getr r 11 = s /\ getr r 12 = Z_to_bv 64 n
                       /\ regs_agree (fun x => In x [1; 2; 8]%list) regs r)
             (fun r m => mkst r ret (MF ret s0 m) rom)).
    { eexists. split.
      - stepiv F_23c04 D_23c04 (Z_to_bv 64 (usp - 16))
          ltac:(gres; imm_norm; rwH; unfold v_addi; f_equal; lia).   (* [comment removed for export] *)
        msd F_23c08 D_23c08 (Z_to_bv 64 (usp - 8)).                  (* [comment removed for export] *)
        msd F_23c0c D_23c0c (Z_to_bv 64 (usp - 16)).                 (* [comment removed for export] *)
        stepn F_23c10 D_23c10.                                        (* [comment removed for export] *)
        stepn F_23c14 D_23c14.                                        (* [comment removed for export] *)
        stepiv F_23c2c D_23c2c (Z_to_bv 64 (usp - 32))
          ltac:(gres; imm_norm; rwH; unfold v_addi; unorm; f_equal; lia).   (* [comment removed for export] *)
        msd F_23c30 D_23c30 (Z_to_bv 64 (usp - 24)).                 (* [comment removed for export] *)
        msd F_23c34 D_23c34 (Z_to_bv 64 (usp - 32)).                 (* [comment removed for export] *)
        stepn F_23c38 D_23c38.                                        (* [comment removed for export] *)
        rwH. fold s0. unfold MB.
        replace (Z_to_bv 64 0x23c18) with (0x23c18 : word) by (apply bv_eq; vm_compute; reflexivity).
        apply mst_refl.
      - cbv beta. repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity).
        solve_regs_agree. }
    cbv beta. intros r1 (R1 & R2 & R8 & R10 & R11 & R12 & AG1).
    (* [comment removed for export] *)
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0x23c3c : word) (MB ret s0) rom) (fun r => r = r1)
             (fun r m => mkst r ret (MF ret s0 m) rom)).
    { exists r1. split; [apply mst_refl | reflexivity]. }
    cbv beta. intros r1' ->.
    destruct (core_run (MB ret s0) d s n src rom C1 (Hroom _ _ _ _ _ _ HOK) C2 (Hn _ _ _ _ _ _ HOK)
                (Hnws _ _ _ _ _ _ HOK) (Hnwd _ _ _ _ _ _ HOK) (Hdisj _ _ _ _ _ _ HOK) C3 (Hdro _ _ _ _ _ _ HOK)
                r1 R8 R10 R11 R12) as (r2 & m & RUN & HS & S8 & AG2).
    pose proof HS as (Hm & HmW & _ & _).
    assert (S2 : getr r2 2 = Z_to_bv 64 (usp - 32)).
    { rewrite (AG2 2%bv) by (unfold core_clob; notin_list). exact R2. }
    eexists. exists m. split; [|split; [|exact HS]].
    - eapply msteps_trans; [exact RUN|]. change (FIN (MB ret s0) d n src m) with (MF ret s0 m).
      (* [comment removed for export] *)
      stepn F_23d20 D_23d20.                                          (* [comment removed for export] *)
      mld8 F_23d24 D_23d24 (0x23c18 : word) (rd_slot ret s0 m 24 (0x23c18 : word) Hm HmW ltac:(tauto)).  (* [comment removed for export] *)
      mld8 F_23d28 D_23d28 d (rd_slot ret s0 m 32 d Hm HmW ltac:(tauto)).                            (* [comment removed for export] *)
      stepiv F_23d2c D_23d2c (Z_to_bv 64 (usp - 16))
        ltac:(gres; imm_norm; rwH; unfold v_addi; unorm; f_equal; lia).                             (* [comment removed for export] *)
      stepret F_23d30 D_23d30 (0x23c18 : word) ltac:(reflexivity).                                  (* [comment removed for export] *)
      (* [comment removed for export] *)
      stepn F_23c18 D_23c18.                                          (* [comment removed for export] *)
      mld8 F_23c1c D_23c1c ret (rd_slot ret s0 m 8 ret Hm HmW ltac:(tauto)).                          (* [comment removed for export] *)
      mld8 F_23c20 D_23c20 s0 (rd_slot ret s0 m 16 s0 Hm HmW ltac:(tauto)).                           (* [comment removed for export] *)
      stepiv F_23c24 D_23c24 sp
        ltac:(gres; imm_norm; rwH; unfold v_addi; unorm; rewrite <- (Z_to_bv_bv_unsigned 64 sp) at 2; f_equal; lia).
                                                                      (* [comment removed for export] *)
      stepret F_23c28 D_23c28 ret ltac:(reflexivity).
      apply mst_refl.
    - (* [comment removed for export] *)
      assert (AGall : regs_agree (fun x => In x ([10; 8; 2; 1] ++ strncpy_clob)%list) regs r2).
      { eapply regs_agree_trans; [eapply regs_agree_mono; [|exact AG1] | eapply regs_agree_mono; [|exact AG2]];
          unfold core_clob, strncpy_clob; cbn [In app]; intros x HH; decompose [or] HH; subst; auto 20. }
      apply (regs_agree_drop _ 1); [apply (regs_agree_drop _ 2); [apply (regs_agree_drop _ 8); [apply (regs_agree_drop _ 10)|]|]|];
        [ | gres; subst s0; rewrite ?H10; reflexivity | gres; subst s0; reflexivity | gres; rewrite H2; reflexivity | gres; rewrite H1; reflexivity ].
      repeat (apply regs_agree_upd; [in_list|]). cbn [app] in AGall. exact AGall.
  Qed.
End WRAP.

Theorem ref_strncpy : forall mem (d s sp : word) (n : Z) (src : list byte) rom regs (ret : word),
  sncH mem d s sp n src ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = Z_to_bv 64 n ->
  exists regs' mem' (m : Z),
    msteps SEGS (mkst regs (0x23c04 : word) mem rom) (mkst regs' ret mem' rom)
    /\ regs_agree (fun x => In x strncpy_clob) regs regs'
    /\ SPEC n src m
    /\ mem' = MF mem d sp n src ret (getr regs 8) m
    /\ rdn SEGS mem' d (Z.to_nat n) = Some (firstn (Z.to_nat m) src ++ zeros (Z.to_nat (n - m)))
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z); (d, n)].
Proof.
  intros mem d s sp n src rom regs ret HOK Hret H1 H2 H10 H11 H12.
  destruct (strncpy_run mem d s sp n src rom HOK regs ret Hret H1 H2 H10 H11 H12) as (r & m & RUN & AG & HS).
  pose proof HS as (Hm & HmW & _ & _).
  pose proof (u64_range d) as Hd. pose proof (u64_range sp) as Hsp.
  pose proof (Hnwd _ _ _ _ _ _ HOK) as Hnwd'. pose proof (Hspro _ _ _ _ _ _ HOK) as Hspro'.
  assert (HL : length (firstn (Z.to_nat m) src ++ zeros (Z.to_nat (n - m))) = Z.to_nat n).
  { rewrite length_app, length_firstn, length_zeros. lia. }
  exists r, (MF mem d sp n src ret (getr regs 8) m), m.
  split; [exact RUN|]. split; [exact AG|]. split; [exact HS|]. split; [reflexivity|]. split.
  - unfold MF, FIN. rewrite <- HL at 1. apply rdn_wbytes_hit. rewrite HL. lia.
  - split.
    + intros a (Ho1 & Ho2 & _). unfold in_rng in Ho1, Ho2. rewrite u_Z2bv in Ho1 by lia.
      rewrite (MF_out mem d s sp n src HOK) by lia. apply (MB_out mem d s sp n src HOK). lia.
    + unfold MF, FIN, MB. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.
