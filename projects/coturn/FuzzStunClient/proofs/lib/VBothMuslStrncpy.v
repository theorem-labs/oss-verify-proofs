(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import StartupTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import BothMemcpyBase BothMemchr BothRegionPoisoned.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VBothMuslStrLib VBothMuslStrlen VBothMusl_code VBothIcMemset_code VBothMemsetWalk VBothIcMemsetWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastV.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ flia2 | Zify.zify; xlia zchecker ].  (* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition core_clob : list reg := [1; 8; 10; 11; 12; 13; 14; 15; 16; 17; 5; 6; 7; 28; 29; 30; 31]%list.

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
  Hypothesis Hdro : (0x10388 <= ud \/ ud + n <= 0x10360)%Z.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable sp2 : Z.
  #[local] Notation SHB := BothRegionPoisoned.SB.
  Hypothesis Hn40 : (n <= 2 ^ 40)%Z.
  Hypothesis Hrng : (0 < n)%Z -> (ud + n <= kLowEnd)%Z \/ (kHighBeg <= ud /\ ud + n <= kHighEnd)%Z.
  Hypothesis Hsp2 : (SHB + IM_FRAME + 8 <= sp2 < 2 ^ 64)%Z.
  Hypothesis Hdst2 : (sp2 <= ud \/ ud + n <= sp2 - IM_FRAME)%Z.
  Hypothesis Hshd : (0 < n)%Z -> (SHB + (ud + n - 1) / 8 + 8 < sp2 - IM_FRAME)%Z.
  Hypothesis Hzg : forall g, (0 < n)%Z -> (ud / 8 <= g < (ud + n - 1) / 8)%Z -> MB (Z_to_bv 64 (SHB + g)) = Some (Z_to_bv 8 0).
  Hypothesis HlastS : (0 < n)%Z -> exists b1 : byte, MB (Z_to_bv 64 (SHB + (ud + n - 1) / 8)) = Some b1
                                        /\ (bv_unsigned b1 = 0%Z \/ ((ud + n - 1) mod 8 < bv_unsigned b1 < 8)%Z).
  Hypothesis Hwords : (0 < n)%Z -> forall a, ((SHB + ud / 8) / 8 * 8 <= a)%Z -> (a <= (SHB + (ud + n - 1) / 8) / 8 * 8)%Z -> (a mod 8 = 0)%Z ->
                        exists w : word, rdn SEGS MB (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 w).
  Hypothesis Hstk2 : forall a, (sp2 - IM_FRAME <= a < sp2)%Z -> store_ok SEGS MB (Z_to_bv 64 a) 1 = true.
  Hypothesis Hcel : im_cells MB.
  Hypothesis Hdcel : (ud + n <= 0xa8000 \/ 0xb3340 <= ud)%Z.   (* [comment removed for export] *)

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

  #[using="d n Hn Hdro"] Lemma len_firstn_k : forall k, (0 <= k <= W)%Z -> length (firstn (Z.to_nat k) src) = Z.to_nat k.
  Proof. intros k Hk. rewrite length_firstn. lia. Qed.

  #[using="Type"] Lemma memk_0 : memk 0 = MB.
  Proof. reflexivity. Qed.

  #[using="Hsrc Hn Hnws Hnwd Hdisj Hdro Hdcel"] Lemma rd_src : forall k j m, (0 <= k <= W)%Z -> (k <= n)%Z -> (0 <= j)%Z -> (j + Z.of_nat m <= W)%Z ->
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

  #[using="Hsrc Hn Hnws Hnwd Hdisj Hdro Hdcel"] Lemma rd_src1 : forall k j, (0 <= k <= W)%Z -> (k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= W)%Z ->
    rdn SEGS (memk k) (at_ s j) 1 = Some [B_ j].
  Proof.
    intros k j Hk Hkn Hj H1. rewrite (rd_src k j 1) by lia. unfold SB, B_.
    rewrite sub_nth; [reflexivity | lia].
  Qed.

  #[using="Hdst Hn Hnwd Hdro"] Lemma wr_dst : forall k j m, (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
    store_ok SEGS (memk k) (at_ d j) m = true.
  Proof.
    intros k j m Hj Hm. unfold memk.
    apply (store_ok_at SEGS MB d (Z.to_nat n)); try assumption; try lia.
  Qed.

  #[using="n Hn Hdro"] Lemma memk_extend1 : forall k, (0 <= k)%Z -> (k + 1 <= W)%Z ->
    wbytes (memk k) (at_ d k) [B_ k] = memk (k + 1).
  Proof.
    intros k Hk H1. unfold memk, B_.
    rewrite <- (sub_nth src (Z.to_nat k)) by lia.
    replace (at_ d k) with (at_ d (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
    rewrite wbytes_extend' by lia. f_equal. f_equal. lia.
  Qed.

  #[using="n Hn Hdro"] Lemma memk_extend8 : forall k, (0 <= k)%Z -> (k + 8 <= W)%Z ->
    wbytes (memk k) (at_ d k) (SB k 8) = memk (k + 8).
  Proof.
    intros k Hk H8. unfold memk, SB.
    replace (at_ d k) with (at_ d (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
    rewrite wbytes_extend' by lia. f_equal. f_equal. lia.
  Qed.

  #[using="s Hn Hnws Hnwd Hdro"] Lemma memk_out : forall k (x : word), (0 <= k <= n)%Z ->
    (bv_unsigned x < ud \/ ud + n <= bv_unsigned x)%Z -> memk k x = MB x.
  Proof.
    intros k x Hk Hx. unfold memk. pose proof (u64_range d).
    assert (HL : (Z.of_nat (length (firstn (Z.to_nat k) src)) <= k)%Z) by (rewrite length_firstn; lia).
    apply MemSplit.wbytes_outside; lia.
  Qed.

  #[using="s Hn Hnws Hnwd Hro Hdro"] Lemma ro_k : forall k, (0 <= k <= n)%Z -> rodata_clear (memk k).
  Proof.
    intros k Hk i Hi. rewrite memk_out; [apply Hro; exact Hi | lia |].
    rewrite u_Z2bv by lia. lia.
  Qed.

  #[using="d n Hn Hdro"] Lemma SB_len : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= W)%Z -> length (SB j m) = m.
  Proof. intros j m Hj Hm. unfold SB. apply sub_length. lia. Qed.

  #[using="d n Hn Hdro"] Lemma SB_nth : forall j (i : nat), (0 <= j)%Z -> (i < 8)%nat -> (j + 8 <= W)%Z ->
    nth i (SB j 8) B0 = B_ (j + Z.of_nat i).
  Proof. intros j i Hj Hi H8. unfold SB, B_. rewrite nth_sub by lia. f_equal. lia. Qed.

  (* [comment removed for export] *)
  #[using="Hn Hdro"] Lemma fin_eq : forall m c, (0 <= m <= n)%Z -> (m <= W)%Z ->
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
  #[using="Hsrc Hn Hnws Hnwd Hdisj Hdro Hdcel"] Lemma c_lbu : forall regs pc w rd rs (imm : bv 12) k j0 j,
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

  #[using="Hsrc Hn Hnws Hnwd Hdisj Hdro Hdcel"] Lemma c_ld : forall regs pc w rd rs (imm : bv 12) k j0 j,
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

  #[using="Hdst Hn Hnwd Hdro"] Lemma c_sb : forall regs pc w rs1 rs2 (imm : bv 12) k k0,
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

  #[using="Hdst Hn Hnwd Hdro"] Lemma c_sd : forall regs pc w rs1 rs2 (imm : bv 12) k k0,
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
  Definition JOUT (x : word) : Prop := (bv_unsigned x < sp2 - IM_FRAME \/ sp2 <= bv_unsigned x)%Z.
  Definition PF (regs0 r : bvmap 5 word) (km : Z * (word -> option byte)) : Prop :=
    POST regs0 r (fst km) /\ (forall x, JOUT x -> snd km x = FIN (fst km) x) /\ (forall x, MB x <> None -> snd km x <> None).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma ret_ok_137668 : ret_ok (0xa3058 : word).
  Proof. apply bv_eq. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Ltac liac := clear Hdisj Hro Hdro Hroom Hstk2 Hcel Hdcel Hdst2; lia.
  Ltac liad := clear Hdisj Hro Hdro Hroom Hstk2 Hcel Hdcel; lia.

  (* [comment removed for export] *)
  #[using="src Hdro Hn40 Hrng Hdcel"] Lemma shadow_off : (0 < n)%Z -> forall x, ((SHB + ud / 8) / 8 * 8 <= x)%Z -> (x < SHB + (ud + n - 1) / 8 + 8)%Z ->
    (x < ud \/ ud + n <= x)%Z.
  Proof.
    intros Hn0 x H1 H2. pose proof SB_val. pose proof (u64_range d).
    pose proof (Z.div_mod ud 8 ltac:(lia)). pose proof (Z.mod_pos_bound ud 8 ltac:(lia)).
    pose proof (Z.div_mod (ud + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (ud + n - 1) 8 ltac:(lia)).
    pose proof (Z.div_mod (SHB + ud / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SHB + ud / 8) 8 ltac:(lia)).
    destruct (Hrng Hn0) as [L|[Hh1 Hh2]]; unfold kLowEnd, kHighBeg, kHighEnd in *; (ltac2:(LK.k [@Hdro; @Hdcel; @H1; @H; @H0; @H3; @H4; @H7; @H8; @L; @Hn40; @H2; @H5; @Hh1]); lia).
  Qed.

  #[using="s Hn Hnws Hnwd Hdro Hn40 Hrng Hdcel"] Lemma memk_MB : forall k (x : word), (0 <= k <= n)%Z -> (0 < n)%Z ->
    ((SHB + ud / 8) / 8 * 8 <= bv_unsigned x)%Z -> (bv_unsigned x < SHB + (ud + n - 1) / 8 + 8)%Z -> memk k x = MB x.
  Proof. intros k x Hk Hn0 H1 H2. apply memk_out; [exact Hk|]. apply shadow_off; assumption. Qed.

  #[using="s Hn Hnws Hnwd Hdro Hdcel"] Lemma rdn_memk_cells : forall k (a : Z) m, (0 <= k <= n)%Z -> (0xa8000 <= a)%Z -> (a + Z.of_nat m <= 0xb3340)%Z ->
    rdn SEGS (memk k) (Z_to_bv 64 a) m = rdn SEGS MB (Z_to_bv 64 a) m.
  Proof.
    intros k a m Hk Ha Hm. apply rdn_ext; [rewrite zbv_u by lia; lia|]. intros x Hx. rewrite zbv_u in Hx by lia.
    apply memk_out; [exact Hk|]. lia.
  Qed.

  #[using="s Hn Hnws Hnwd Hdro sp2 Hn40 Hrng Hsp2 Hshd Hwords Hdcel"] Lemma words_memk : forall k a, (0 <= k <= n)%Z -> (0 < n)%Z ->
    ((SHB + ud / 8) / 8 * 8 <= a)%Z -> (a <= (SHB + (ud + n - 1) / 8) / 8 * 8)%Z -> (a mod 8 = 0)%Z ->
    exists w : word, rdn SEGS (memk k) (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 w).
  Proof.
    intros k a Hk Hn0 H1 H2 H3.
    pose proof SB_val. pose proof (u64_range d). pose proof Hsp2 as HSP. unfold IM_FRAME in HSP. pose proof (Hshd Hn0) as SH. unfold IM_FRAME in SH.
    pose proof (Z.div_mod ud 8 ltac:(liac)). pose proof (Z.mod_pos_bound ud 8 ltac:(liac)).
    pose proof (Z.div_mod (ud + n - 1) 8 ltac:(liac)). pose proof (Z.mod_pos_bound (ud + n - 1) 8 ltac:(liac)).
    pose proof (Z.div_mod (SHB + ud / 8) 8 ltac:(liac)). pose proof (Z.mod_pos_bound (SHB + ud / 8) 8 ltac:(liac)).
    pose proof (Z.div_mod (SHB + (ud + n - 1) / 8) 8 ltac:(liac)). pose proof (Z.mod_pos_bound (SHB + (ud + n - 1) / 8) 8 ltac:(liac)).
    destruct (Hwords Hn0 a H1 H2 H3) as [w Hw]. exists w. rewrite <- Hw.
    assert (A8 : (0 <= a)%Z /\ (a + 8 < 2 ^ 64)%Z) by liac.
    apply rdn_ext; [rewrite zbv_u by liac; cbn; liac|]. intros x Hx. rewrite zbv_u in Hx by liac. cbn in Hx.
    apply (memk_MB k); [exact Hk|exact Hn0|liac|liac].
  Qed.

  #[using="s Hdst Hn Hnws Hnwd Hdro Hn40 Hrng Hsp2 Hdst2 Hshd Hzg HlastS Hwords Hstk2 Hcel Hdcel"] Lemma imH_memk : forall k m, (0 <= k <= n)%Z -> (0 <= m <= n)%Z -> imH (memk k) (ud + m) 0 (n - m) sp2.
  Proof.
    intros k m Hk Hm. pose proof SB_val. pose proof (u64_range d). pose proof Hsp2 as HSP. unfold IM_FRAME in HSP.
    pose proof (Z.div_mod ud 8 ltac:(liac)). pose proof (Z.mod_pos_bound ud 8 ltac:(liac)).
    pose proof (Z.div_mod (ud + m) 8 ltac:(liac)). pose proof (Z.mod_pos_bound (ud + m) 8 ltac:(liac)).
    pose proof (Z.div_mod (ud + n - 1) 8 ltac:(liac)). pose proof (Z.mod_pos_bound (ud + n - 1) 8 ltac:(liac)).
    pose proof (Z.div_le_mono ud (ud + m) 8 ltac:(liac) ltac:(liac)) as DM1.
    constructor; rewrite ?Z.add_assoc; try replace (ud + m + (n - m))%Z with (ud + n)%Z by liac.
    - liac.
    - liac.
    - liac.
    - liac.
    - intros Hn0. destruct (Hrng ltac:(liac)) as [L|[R1 R2]]; [left; liac|right; liac].
    - unfold IM_FRAME in *. liac.
    - unfold IM_FRAME in *. liad.
    - intros Hn0. specialize (Hshd ltac:(liac)). unfold IM_FRAME in *. liac.
    - intros g Hn0' Hg. assert (Hn0 : (0 < n)%Z) by liac.
      pose proof (Hshd Hn0) as SH. unfold IM_FRAME in SH.
      pose proof (Z.div_le_mono (ud + m) (ud + n - 1) 8 ltac:(liac) ltac:(liac)).
      pose proof (Z.div_mod (SHB + ud / 8) 8 ltac:(liac)). pose proof (Z.mod_pos_bound (SHB + ud / 8) 8 ltac:(liac)).
      rewrite (memk_MB k); [apply Hzg; liac|exact Hk|exact Hn0|rewrite zbv_u by liac; liac|rewrite zbv_u by liac; liac].
    - intros Hn0.
      pose proof (Hshd ltac:(liac)) as SH. unfold IM_FRAME in SH.
      destruct (HlastS ltac:(liac)) as (b1 & L1 & B1). exists b1. split; [|exact B1].
      pose proof (Z.div_mod (SHB + ud / 8) 8 ltac:(liac)). pose proof (Z.mod_pos_bound (SHB + ud / 8) 8 ltac:(liac)).
      pose proof (Z.div_le_mono ud (ud + n - 1) 8 ltac:(liac) ltac:(liac)).
      rewrite (memk_MB k); [exact L1|exact Hk|liac|rewrite zbv_u by liac; liac|rewrite zbv_u by liac; liac].
    - intros Hn0.
      pose proof (Z.div_le_mono (ud + m) (ud + n - 1) 8 ltac:(liac) ltac:(liac)).
      pose proof (Z.div_mod (SHB + ud / 8) 8 ltac:(liac)). pose proof (Z.mod_pos_bound (SHB + ud / 8) 8 ltac:(liac)).
      pose proof (Z.div_mod (SHB + (ud + m) / 8) 8 ltac:(liac)). pose proof (Z.mod_pos_bound (SHB + (ud + m) / 8) 8 ltac:(liac)).
      pose proof (Z.div_le_mono (SHB + ud / 8) (SHB + (ud + m) / 8) 8 ltac:(liac) ltac:(liac)).
      pose proof (Z.div_le_mono (SHB + (ud + m) / 8) (SHB + (ud + n - 1) / 8) 8 ltac:(liac) ltac:(liac)).
      apply (words_memk k); [exact Hk|liac|liac|liac|rewrite Z_mod_mult; reflexivity].
    - intros Hn0.
      pose proof (Z.div_mod (SHB + ud / 8) 8 ltac:(liac)). pose proof (Z.mod_pos_bound (SHB + ud / 8) 8 ltac:(liac)).
      pose proof (Z.div_mod (SHB + (ud + n - 1) / 8) 8 ltac:(liac)). pose proof (Z.mod_pos_bound (SHB + (ud + n - 1) / 8) 8 ltac:(liac)).
      pose proof (Z.div_le_mono ud (ud + n - 1) 8 ltac:(liac) ltac:(liac)).
      pose proof (Z.div_le_mono (SHB + ud / 8) (SHB + (ud + n - 1) / 8) 8 ltac:(liac) ltac:(liac)).
      apply (words_memk k); [exact Hk|liac|liac|liac|rewrite Z_mod_mult; reflexivity].
    - intros j Hj. replace (Z_to_bv 64 (ud + m + j)) with (at_ d (m + j)) by (unfold at_; apply (f_equal (Z_to_bv 64)); liac).
      apply (wr_dst k (m + j) 1); cbn; liac.
    - intros a Ha. unfold memk. apply store_ok1_wbytes. apply Hstk2. exact Ha.
    - pose proof Hcel as (C & C1 & B1 & C2). unfold im_cells, cells, cell in *.
      rewrite !(rdn_memk_cells k) by (first [exact Hk | cbn; liac]). split; [exact C|]. split; [exact C1|]. split; [exact B1|exact C2].
  Qed.

  #[using="Type"] Lemma core_clob_of_im : forall x : reg, ~ In x core_clob -> im_clob x = false.
  Proof.
    intros x Hx. unfold core_clob in Hx. cbn [In] in Hx. unfold im_clob.
    repeat match goal with |- context [bv_eqb x ?k] =>
      destruct (bv_eq_dec _ x k) as [->|NEQ];
        [exfalso; apply Hx; let rec go := first [left; reflexivity | right; go] in go
        | rewrite (bv_eqb_neq _ _ NEQ); clear NEQ] end.
    reflexivity.
  Qed.

  #[using="s Hdst Hn Hnws Hnwd Hdro Hn40 Hrng Hsp2 Hdst2 Hshd Hzg HlastS Hwords Hstk2 Hcel Hdcel"] Lemma tail_run : forall regs0 regs m c,
    SPEC m -> (c = m \/ (c = m + 1 /\ m < n /\ m + 1 <= W))%Z ->
    getr regs 8 = at_ d m -> getr regs 13 = Z_to_bv 64 (n - m) ->
    regs_agree (fun x => In x core_clob) regs0 regs ->
    getr regs0 2 = Z_to_bv 64 sp2 ->
    exists r (km : Z * (word -> option byte)),
      msteps SEGS (mkst regs (0xa3048 : word) (memk c) rom) (mkst r (0xa3058 : word) (snd km) rom)
      /\ PF regs0 r km.
  Proof.
    intros regs0 regs m c HS Hc H8 H13 AG HS2. pose proof HS as (Hm & HmW & _ & _).
    pose proof (u64_range d) as Hd.
    assert (Hcn : (0 <= c <= n)%Z) by lia.
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0x53e18 : word) (memk c) rom)
             (fun r => getr r 1 = (0xa3058 : word) /\ getr r 10 = at_ d m /\ getr r 11 = Z_to_bv 64 0
                       /\ getr r 12 = Z_to_bv 64 (n - m) /\ getr r 8 = at_ d m /\ getr r 2 = Z_to_bv 64 sp2
                       /\ regs_agree (fun x => In x core_clob) regs0 r)
             (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
    - eexists. split.
      + stepn F_a3048 D_a3048.              (* [comment removed for export] *)
        stepn F_a304c D_a304c.              (* [comment removed for export] *)
        stepn F_a3050 D_a3050.              (* [comment removed for export] *)
        stepn F_a3054 D_a3054.              (* [comment removed for export] *)
        apply mst_refl.
      + post.
        * rewrite <- HS2. apply AG. unfold core_clob. notin_list.
        * eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
    - cbv beta. intros r1 (R1 & R10 & R11 & R12 & R8 & R2 & AG1).
      assert (R10' : getr r1 10 = Z_to_bv 64 (ud + m)) by (rewrite R10; reflexivity).
      destruct (ic_memset_run (memk c) rom (ud + m) 0 (n - m) sp2 (imH_memk c m Hcn ltac:(lia)) r1 (0xa3058 : word)
                  ret_ok_137668 R1 R2 R10' R11 R12) as (r2 & m2 & RUN & Q10 & Q2 & Q1 & QK & QM & QG).
      exists r2, (m, m2). split; [exact RUN|].
      split; [|split].
      + split; [exact HS|]. split.
        * rewrite (QK 8) by reflexivity. exact R8.
        * intros x Hx. rewrite (QK x (core_clob_of_im x Hx)). apply AG1. exact Hx.
      + intros x Hx. cbn [fst snd]. rewrite (QM x Hx). rewrite <- (fin_eq m c) by assumption.
        unfold zeros, at_. reflexivity.
      + intros x Hx. cbn [snd]. apply QG. unfold memk. apply wbytes_keep. exact Hx.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="d s Hroom Hdro"] Lemma room_byte : forall k, (0 <= k < n)%Z ->
    (forall j, (0 <= j < k)%Z -> bv_unsigned (B_ j) <> 0%Z) -> (k + 1 <= W)%Z.
  Proof.
    intros k Hk Hnz. destruct Hroom as [HW | (K & HK & HzK & HsK)]; [lia|].
    destruct (Z_lt_le_dec K k) as [Hl|Hl]; [|lia]. exfalso. apply (Hnz K); [lia | exact HzK].
  Qed.

  #[using="d Hroom Hdro"] Lemma room_word : forall k t, (0 <= k)%Z -> (k + 8 <= n)%Z -> (us + k = 8 * t)%Z ->
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
  #[using="Hsrc Hroom Hdst Hn Hnws Hnwd Hdisj Hdro Hn40 Hrng Hsp2 Hdst2 Hshd Hzg HlastS Hwords Hstk2 Hcel Hdcel"] Lemma b_loop : forall (cnt : nat) regs0 regs k,
    (Z.of_nat cnt = n - k)%Z -> (0 <= k < n)%Z -> (k <= W)%Z ->
    (forall j, (0 <= j < k)%Z -> bv_unsigned (B_ j) <> 0%Z) ->
    getr regs 11 = at_ s k -> getr regs 8 = at_ d k -> getr regs 13 = Z_to_bv 64 (n - k) ->
    regs_agree (fun x => In x core_clob) regs0 regs ->
    getr regs0 2 = Z_to_bv 64 sp2 ->
    exists r (km : Z * (word -> option byte)),
      msteps SEGS (mkst regs (0xa2f88 : word) (memk k) rom) (mkst r (0xa3058 : word) (snd km) rom)
      /\ PF regs0 r km.
  Proof.
    induction cnt as [|cnt IH]; intros regs0 regs k Hcnt Hk HkW Hnz H11 H8 H13 AG HS2; [lia|].
    pose proof (u64_range s) as Hs. pose proof (u64_range d) as Hd.
    pose proof (room_byte k Hk Hnz) as HR. pose proof (u8_range (B_ k)) as U.
    destruct (Z.eq_dec (bv_unsigned (B_ k)) 0) as [Hz|Hnzk].
    - (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3048 : word) (memk (k + 1)) rom)
               (fun r => getr r 8 = at_ d k /\ getr r 13 = Z_to_bv 64 (n - k)
                         /\ regs_agree (fun x => In x core_clob) regs0 r)
               (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
      + eexists. split.
        * mlbu F_a2f88 D_a2f88 k.            (* [comment removed for export] *)
          msb F_a2f8c D_a2f8c.               (* [comment removed for export] *)
          stepb_tk F_a2f90 D_a2f90 ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_eq; exact Hz).  (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
      + cbv beta. intros r1 (R8 & R13 & AG1).
        apply (tail_run regs0 r1 k (k + 1)); try assumption; try lia.
        split; [lia|]. split; [lia|]. split; [exact Hnz | intros _; exact Hz].
    - destruct (Z.eq_dec (k + 1) n) as [Hlast|Hmore].
      + (* [comment removed for export] *)
        eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3048 : word) (memk (k + 1)) rom)
                 (fun r => getr r 8 = at_ d (k + 1) /\ getr r 13 = Z_to_bv 64 (n - (k + 1))
                           /\ regs_agree (fun x => In x core_clob) regs0 r)
                 (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
        * eexists. split.
          -- mlbu F_a2f88 D_a2f88 k.
             msb F_a2f8c D_a2f8c.
             stepb_ft F_a2f90 D_a2f90 ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_neq; exact Hnzk).  (* [comment removed for export] *)
             sv F_a2f94 D_a2f94 (Z_to_bv 64 (n - (k + 1))).   (* [comment removed for export] *)
             stepn F_a2f98 D_a2f98.             (* [comment removed for export] *)
             stepn F_a2f9c D_a2f9c.             (* [comment removed for export] *)
             stepb_ft F_a2fa0 D_a2fa0 ltac:(cond).   (* [comment removed for export] *)
             stepn F_a2fa4 D_a2fa4.             (* [comment removed for export] *)
             apply mst_refl.
          -- post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
        * cbv beta. intros r1 (R8 & R13 & AG1).
          apply (tail_run regs0 r1 (k + 1) (k + 1)); try assumption; try lia.
          split; [lia|]. split; [lia|]. split; [|intros; lia].
          intros j Hj. destruct (Z.eq_dec j k) as [->|]; [exact Hnzk | apply Hnz; lia].
      + (* [comment removed for export] *)
        eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa2f88 : word) (memk (k + 1)) rom)
                 (fun r => getr r 11 = at_ s (k + 1) /\ getr r 8 = at_ d (k + 1) /\ getr r 13 = Z_to_bv 64 (n - (k + 1))
                           /\ regs_agree (fun x => In x core_clob) regs0 r)
                 (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
        * eexists. split.
          -- mlbu F_a2f88 D_a2f88 k.
             msb F_a2f8c D_a2f8c.
             stepb_ft F_a2f90 D_a2f90 ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_neq; exact Hnzk).
             sv F_a2f94 D_a2f94 (Z_to_bv 64 (n - (k + 1))).
             stepn F_a2f98 D_a2f98.
             stepn F_a2f9c D_a2f9c.
             stepb_tk F_a2fa0 D_a2fa0 ltac:(cond).   (* [comment removed for export] *)
             apply mst_refl.
          -- post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
        * cbv beta. intros r1 (R11 & R8 & R13 & AG1).
          apply (IH regs0 r1 (k + 1)%Z ltac:(lia) ltac:(lia) ltac:(lia)); try assumption.
          intros j Hj. destruct (Z.eq_dec j k) as [->|]; [exact Hnzk | apply Hnz; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Hsrc Hroom Hdst Hn Hnws Hnwd Hdisj Hdro Hn40 Hrng Hsp2 Hdst2 Hshd Hzg HlastS Hwords Hstk2 Hcel Hdcel"] Lemma b_entry_c : forall regs0 regs k,
    (0 <= k < n)%Z -> (k <= W)%Z ->
    (forall j, (0 <= j < k)%Z -> bv_unsigned (B_ j) <> 0%Z) ->
    getr regs 11 = at_ s k -> getr regs 8 = at_ d k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    regs_agree (fun x => In x core_clob) regs0 regs ->
    getr regs0 2 = Z_to_bv 64 sp2 ->
    exists r (km : Z * (word -> option byte)),
      msteps SEGS (mkst regs (0xa2f84 : word) (memk k) rom) (mkst r (0xa3058 : word) (snd km) rom)
      /\ PF regs0 r km.
  Proof.
    intros regs0 regs k Hk HkW Hnz H11 H8 H12 AG HS2.
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa2f88 : word) (memk k) rom)
             (fun r => getr r 11 = at_ s k /\ getr r 8 = at_ d k /\ getr r 13 = Z_to_bv 64 (n - k)
                       /\ regs_agree (fun x => In x core_clob) regs0 r)
             (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
    - eexists. split.
      + stepn F_a2f84 D_a2f84.               (* [comment removed for export] *)
        apply mst_refl.
      + post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
    - cbv beta. intros r1 (R11 & R8 & R13 & AG1).
      apply (b_loop (Z.to_nat (n - k)) regs0 r1 k ltac:(lia) Hk HkW Hnz); try assumption.
  Qed.

  #[using="Hsrc Hroom Hdst Hn Hnws Hnwd Hdisj Hdro Hn40 Hrng Hsp2 Hdst2 Hshd Hzg HlastS Hwords Hstk2 Hcel Hdcel"] Lemma b_entry : forall regs0 regs k,
    (0 <= k <= n)%Z -> (k <= W)%Z ->
    (forall j, (0 <= j < k)%Z -> bv_unsigned (B_ j) <> 0%Z) ->
    getr regs 11 = at_ s k -> getr regs 8 = at_ d k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    regs_agree (fun x => In x core_clob) regs0 regs ->
    getr regs0 2 = Z_to_bv 64 sp2 ->
    exists r (km : Z * (word -> option byte)),
      msteps SEGS (mkst regs (0xa2f80 : word) (memk k) rom) (mkst r (0xa3058 : word) (snd km) rom)
      /\ PF regs0 r km.
  Proof.
    intros regs0 regs k Hk HkW Hnz H11 H8 H12 AG HS2. pose proof (u64_range d) as Hd.
    destruct (Z.eq_dec k n) as [->|Hkn].
    - (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3048 : word) (memk n) rom)
               (fun r => getr r 8 = at_ d n /\ getr r 13 = Z_to_bv 64 (n - n)
                         /\ regs_agree (fun x => In x core_clob) regs0 r)
               (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
      + eexists. split.
        * stepb_tk F_a2f80 D_a2f80 ltac:(cond).    (* [comment removed for export] *)
          stepn F_a3044 D_a3044.                   (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
      + cbv beta. intros r1 (R8 & R13 & AG1).
        apply (tail_run regs0 r1 n n); try assumption; try lia.
        split; [lia|]. split; [lia|]. split; [exact Hnz | intros; lia].
    - eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa2f84 : word) (memk k) rom)
               (fun r => getr r 11 = at_ s k /\ getr r 8 = at_ d k /\ getr r 12 = Z_to_bv 64 (n - k)
                         /\ regs_agree (fun x => In x core_clob) regs0 r)
               (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
      + eexists. split.
        * stepb_ft F_a2f80 D_a2f80 ltac:(cond).    (* [comment removed for export] *)
          apply mst_refl.
        * post. exact AG.
      + cbv beta. intros r1 (R11 & R8 & R12 & AG1).
        apply (b_entry_c regs0 r1 k); try assumption; try lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="d n"] Lemma zero_in_word : forall k, (0 <= k)%Z ->
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

  #[using="Hsrc Hroom Hdst Hn Hnws Hnwd Hdisj Hdro Hn40 Hrng Hsp2 Hdst2 Hshd Hzg HlastS Hwords Hstk2 Hcel Hdcel"] Lemma w_loop : forall (cnt : nat) regs0 regs k t,
    (Z.of_nat cnt = n - k)%Z -> (0 <= k)%Z -> (k + 8 <= n)%Z -> (us + k = 8 * t)%Z ->
    (forall j, (0 <= j < k)%Z -> bv_unsigned (B_ j) <> 0%Z) ->
    getr regs 11 = at_ s k -> getr regs 8 = at_ d k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 13 = Z_to_bv 64 Mc -> getr regs 14 = Z_to_bv 64 Hc -> getr regs 15 = Z_to_bv 64 7 ->
    regs_agree (fun x => In x core_clob) regs0 regs ->
    getr regs0 2 = Z_to_bv 64 sp2 ->
    exists r (km : Z * (word -> option byte)),
      msteps SEGS (mkst regs (0xa3018 : word) (memk k) rom) (mkst r (0xa3058 : word) (snd km) rom)
      /\ PF regs0 r km.
  Proof.
    induction cnt as [cnt IH] using (well_founded_induction Wf_nat.lt_wf).
    intros regs0 regs k t Hcnt Hk Hkn Ht Hnz H11 H8 H12 H13 H14 H15 AG HS2.
    pose proof (u64_range s) as Hs. pose proof (u64_range d) as Hd.
    pose proof (room_word k t Hk Hkn Ht Hnz) as HR.
    destruct (zero_in_word k Hk) as [(i & Hi & Zi & NZi) | ALL].
    - (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa2f84 : word) (memk k) rom)
               (fun r => getr r 11 = at_ s k /\ getr r 8 = at_ d k /\ getr r 12 = Z_to_bv 64 (n - k)
                         /\ regs_agree (fun x => In x core_clob) regs0 r)
               (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
      + eexists. split.
        * mld F_a3018 D_a3018 k.                     (* [comment removed for export] *)
          stepn F_a301c D_a301c.                      (* [comment removed for export] *)
          stepn F_a3020 D_a3020.                      (* [comment removed for export] *)
          stepn F_a3024 D_a3024.                      (* [comment removed for export] *)
          stepb_tk F_a3028 D_a3028 ltac:(condw_hit i).  (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
      + cbv beta. intros r1 (R11 & R8 & R12 & AG1).
        apply (b_entry_c regs0 r1 k); try assumption; try lia.
    - (* [comment removed for export] *)
      destruct (Z_lt_le_dec 7 (n - k - 8)) as [Hmore|Hlast].
      + eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3018 : word) (memk (k + 8)) rom)
                 (fun r => getr r 11 = at_ s (k + 8) /\ getr r 8 = at_ d (k + 8) /\ getr r 12 = Z_to_bv 64 (n - (k + 8))
                           /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc /\ getr r 15 = Z_to_bv 64 7
                           /\ regs_agree (fun x => In x core_clob) regs0 r)
                 (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
        * eexists. split.
          -- mld F_a3018 D_a3018 k.
             stepn F_a301c D_a301c.
             stepn F_a3020 D_a3020.
             stepn F_a3024 D_a3024.
             stepb_ft F_a3028 D_a3028 ltac:(condw_miss).   (* [comment removed for export] *)
             msd F_a302c D_a302c.                          (* [comment removed for export] *)
             sv F_a3030 D_a3030 (Z_to_bv 64 (n - (k + 8))).   (* [comment removed for export] *)
             stepn F_a3034 D_a3034.                        (* [comment removed for export] *)
             stepn F_a3038 D_a3038.                        (* [comment removed for export] *)
             stepb_tk F_a303c D_a303c ltac:(cond).         (* [comment removed for export] *)
             apply mst_refl.
          -- post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
        * cbv beta. intros r1 (R11 & R8 & R12 & R13 & R14 & R15 & AG1).
          apply (IH (Z.to_nat (n - (k + 8))) ltac:(lia) regs0 r1 (k + 8)%Z (t + 1)%Z); try assumption; try lia.
          intros j Hj. destruct (Z_lt_le_dec j k) as [Hl|Hl]; [apply Hnz; lia|].
          replace j with (k + Z.of_nat (Z.to_nat (j - k)))%Z by lia. apply ALL. lia.
      + eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa2f80 : word) (memk (k + 8)) rom)
                 (fun r => getr r 11 = at_ s (k + 8) /\ getr r 8 = at_ d (k + 8) /\ getr r 12 = Z_to_bv 64 (n - (k + 8))
                           /\ regs_agree (fun x => In x core_clob) regs0 r)
                 (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
        * eexists. split.
          -- mld F_a3018 D_a3018 k.
             stepn F_a301c D_a301c.
             stepn F_a3020 D_a3020.
             stepn F_a3024 D_a3024.
             stepb_ft F_a3028 D_a3028 ltac:(condw_miss).
             msd F_a302c D_a302c.
             sv F_a3030 D_a3030 (Z_to_bv 64 (n - (k + 8))).
             stepn F_a3034 D_a3034.
             stepn F_a3038 D_a3038.
             stepb_ft F_a303c D_a303c ltac:(cond).         (* [comment removed for export] *)
             stepn F_a3040 D_a3040.                        (* [comment removed for export] *)
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

  #[using="Hsrc Hroom Hdst Hn Hnws Hnwd Hdisj Hro Hdro Hn40 Hrng Hsp2 Hdst2 Hshd Hzg HlastS Hwords Hstk2 Hcel Hdcel"] Lemma j_run : forall regs0 regs k (e : Z),
    (0 <= k <= n)%Z -> (k <= W)%Z ->
    ((e = 0 /\ k = n) \/ (e = 1 /\ k < n /\ exists t, us + k = 8 * t))%Z ->
    (forall j, (0 <= j < k)%Z -> bv_unsigned (B_ j) <> 0%Z) ->
    getr regs 11 = at_ s k -> getr regs 8 = at_ d k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = Z_to_bv 64 e ->
    regs_agree (fun x => In x core_clob) regs0 regs ->
    getr regs0 2 = Z_to_bv 64 sp2 ->
    exists r (km : Z * (word -> option byte)),
      msteps SEGS (mkst regs (0xa2ff0 : word) (memk k) rom) (mkst r (0xa3058 : word) (snd km) rom)
      /\ PF regs0 r km.
  Proof.
    intros regs0 regs k e Hk HkW He Hnz H11 H8 H12 H14 AG HS2.
    pose proof (u64_range s) as Hs. pose proof (u64_range d) as Hd.
    destruct He as [(-> & ->) | (-> & Hkn & (t & Ht))].
    - (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3048 : word) (memk n) rom)
               (fun r => getr r 8 = at_ d n /\ getr r 13 = Z_to_bv 64 (n - n)
                         /\ regs_agree (fun x => In x core_clob) regs0 r)
               (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
      + eexists. split.
        * stepb_tk F_a2ff0 D_a2ff0 ltac:(cond).    (* [comment removed for export] *)
          stepn F_a3044 D_a3044.                   (* [comment removed for export] *)
          apply mst_refl.
        * post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
      + cbv beta. intros r1 (R8 & R13 & AG1).
        apply (tail_run regs0 r1 n n); try assumption; try lia.
        split; [lia|]. split; [lia|]. split; [exact Hnz | intros; lia].
    - pose proof (room_byte k ltac:(lia) Hnz) as HR. pose proof (u8_range (B_ k)) as U.
      destruct (Z.eq_dec (bv_unsigned (B_ k)) 0) as [Hz|Hnzk].
      + (* [comment removed for export] *)
        eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3048 : word) (memk k) rom)
                 (fun r => getr r 8 = at_ d k /\ getr r 13 = Z_to_bv 64 (n - k)
                           /\ regs_agree (fun x => In x core_clob) regs0 r)
                 (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
        * eexists. split.
          -- stepb_ft F_a2ff0 D_a2ff0 ltac:(cond).    (* [comment removed for export] *)
             mlbu F_a2ff4 D_a2ff4 k.                    (* [comment removed for export] *)
             stepb_tk F_a2ff8 D_a2ff8 ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_eq; exact Hz).  (* [comment removed for export] *)
             stepn F_a306c D_a306c.                     (* [comment removed for export] *)
             stepn F_a3070 D_a3070.                     (* [comment removed for export] *)
             apply mst_refl.
          -- post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
        * cbv beta. intros r1 (R8 & R13 & AG1).
          apply (tail_run regs0 r1 k k); try assumption; try lia.
          split; [lia|]. split; [lia|]. split; [exact Hnz | intros _; exact Hz].
      + destruct (Z_lt_le_dec (n - k) 8) as [Hsmall|Hbig].
        * (* [comment removed for export] *)
          eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa2f80 : word) (memk k) rom)
                   (fun r => getr r 11 = at_ s k /\ getr r 8 = at_ d k /\ getr r 12 = Z_to_bv 64 (n - k)
                             /\ regs_agree (fun x => In x core_clob) regs0 r)
                   (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
          -- eexists. split.
             ++ stepb_ft F_a2ff0 D_a2ff0 ltac:(cond).
                mlbu F_a2ff4 D_a2ff4 k.
                stepb_ft F_a2ff8 D_a2ff8 ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_neq; exact Hnzk).
                stepn F_a2ffc D_a2ffc.                  (* [comment removed for export] *)
                stepb_tk F_a3000 D_a3000 ltac:(cond).   (* [comment removed for export] *)
                apply mst_refl.
             ++ post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
          -- cbv beta. intros r1 (R11 & R8 & R12 & AG1).
             apply (b_entry regs0 r1 k); try assumption; try lia.
        * (* [comment removed for export] *)
          destruct (rd_const_M (memk k) (ro_k k ltac:(lia))) as (bsM & RM & EM).
          destruct (rd_const_H (memk k) (ro_k k ltac:(lia))) as (bsH & RH & EH).
          eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3018 : word) (memk k) rom)
                   (fun r => getr r 11 = at_ s k /\ getr r 8 = at_ d k /\ getr r 12 = Z_to_bv 64 (n - k)
                             /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc /\ getr r 15 = Z_to_bv 64 7
                             /\ regs_agree (fun x => In x core_clob) regs0 r)
                   (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
          -- eexists. split.
             ++ stepb_ft F_a2ff0 D_a2ff0 ltac:(cond).
                mlbu F_a2ff4 D_a2ff4 k.
                stepb_ft F_a2ff8 D_a2ff8 ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_neq; exact Hnzk).
                stepn F_a2ffc D_a2ffc.                  (* [comment removed for export] *)
                stepb_ft F_a3000 D_a3000 ltac:(cond).   (* [comment removed for export] *)
                stepn F_a3004 D_a3004.                  (* [comment removed for export] *)
                stepn F_a3008 D_a3008.                  (* [comment removed for export] *)
                ldc F_a300c D_a300c (Z_to_bv 64 Mc) RM. (* [comment removed for export] *)
                ldc F_a3010 D_a3010 (Z_to_bv 64 Hc) RH. (* [comment removed for export] *)
                stepn F_a3014 D_a3014.                  (* [comment removed for export] *)
                apply mst_refl.
             ++ post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
          -- cbv beta. intros r1 (R11 & R8 & R12 & R13 & R14 & R15 & AG1).
             apply (w_loop (Z.to_nat (n - k)) regs0 r1 k t); try assumption; try lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="d n src"] Lemma v_sltu0 : forall z, (0 <= z < 2 ^ 64)%Z ->
    v_sltu (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 (if (z =? 0)%Z then 0 else 1).
  Proof.
    intros z Hz. unfold v_sltu, c_ltu, bv_ltu. rewrite (u_Z2bv 0), (u_Z2bv z) by lia.
    destruct (Z.eqb_spec z 0) as [->|Hne]; [reflexivity|].
    replace (0 <? z)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  Qed.

  #[using="Hsrc Hroom Hdst Hn Hnws Hnwd Hdisj Hro Hdro Hn40 Hrng Hsp2 Hdst2 Hshd Hzg HlastS Hwords Hstk2 Hcel Hdcel"] Lemma h_loop : forall (cnt : nat) regs0 regs k q,
    (Z.of_nat cnt = hd us - k)%Z -> (0 <= k < n)%Z -> (k < hd us)%Z -> (us + hd us = 8 * q)%Z -> (k <= W)%Z ->
    (forall j, (0 <= j < k)%Z -> bv_unsigned (B_ j) <> 0%Z) ->
    getr regs 11 = at_ s k -> getr regs 8 = at_ d k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 15 = at_ s (k + 1) -> getr regs 16 = Z_to_bv 64 1 ->
    regs_agree (fun x => In x core_clob) regs0 regs ->
    getr regs0 2 = Z_to_bv 64 sp2 ->
    exists r (km : Z * (word -> option byte)),
      msteps SEGS (mkst regs (0xa2fc0 : word) (memk k) rom) (mkst r (0xa3058 : word) (snd km) rom)
      /\ PF regs0 r km.
  Proof.
    induction cnt as [cnt IH] using (well_founded_induction Wf_nat.lt_wf).
    intros regs0 regs k q Hcnt Hk Hkh Hq HkW Hnz H11 H8 H12 H15 H16 AG HS2.
    pose proof (u64_range s) as Hs. pose proof (u64_range d) as Hd.
    pose proof (hd_facts us ltac:(lia)) as (q' & A & Bq & C).
    pose proof (room_byte k Hk Hnz) as HR. pose proof (u8_range (B_ k)) as U.
    destruct (Z.eq_dec (bv_unsigned (B_ k)) 0) as [Hz|Hnzk].
    { (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa3048 : word) (memk (k + 1)) rom)
               (fun r => getr r 8 = at_ d k /\ getr r 13 = Z_to_bv 64 (n - k)
                         /\ regs_agree (fun x => In x core_clob) regs0 r)
               (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
      - eexists. split.
        + mlbu F_a2fc0 D_a2fc0 k.                 (* [comment removed for export] *)
          stepn F_a2fc4 D_a2fc4.                   (* [comment removed for export] *)
          msb F_a2fc8 D_a2fc8.                     (* [comment removed for export] *)
          stepb_tk F_a2fcc D_a2fcc ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_eq; exact Hz).  (* [comment removed for export] *)
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
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa2ff0 : word) (memk (k + 1)) rom)
               (fun r => getr r 11 = at_ s (k + 1) /\ getr r 8 = at_ d (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1))
                         /\ getr r 14 = Z_to_bv 64 (if (n - (k + 1) =? 0)%Z then 0 else 1)
                         /\ regs_agree (fun x => In x core_clob) regs0 r)
               (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
      - eexists. split.
        + mlbu F_a2fc0 D_a2fc0 k.
          stepn F_a2fc4 D_a2fc4.
          msb F_a2fc8 D_a2fc8.
          stepb_ft F_a2fcc D_a2fcc ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_neq; exact Hnzk).
          sv F_a2fd0 D_a2fd0 (Z_to_bv 64 (n - (k + 1))).   (* [comment removed for export] *)
          stepn F_a2fd4 D_a2fd4.                   (* [comment removed for export] *)
          stepn F_a2fd8 D_a2fd8.                   (* [comment removed for export] *)
          stepiv F_a2fdc D_a2fdc (Z_to_bv 64 0)
            ltac:(gres; rwH; imm_norm; unfold v_andi, at_; unorm;
                  change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; f_equal;
                  apply (mod8_mul _ q); lia).    (* [comment removed for export] *)
          stepsltu F_a2fe0 D_a2fe0 (Z_to_bv 64 (if (n - (k + 1) =? 0)%Z then 0 else 1))
            ltac:(gres; rwH; apply v_sltu0; lia).   (* [comment removed for export] *)
          stepb_tk F_a2fe4 D_a2fe4 ltac:(cond_lia).   (* [comment removed for export] *)
          apply mst_refl.
        + post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
      - cbv beta. intros r1 (R11 & R8 & R12 & R14 & AG1).
        apply (j_run regs0 r1 (k + 1) (if (n - (k + 1) =? 0)%Z then 0 else 1)); try assumption; try lia.
        destruct (Z.eqb_spec (n - (k + 1)) 0); [left; lia | right]. split; [reflexivity|]. split; [lia|]. exists q. lia. }
    destruct (Z.eq_dec (k + 1) n) as [Hlast|Hmore].
    { (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa2ff0 : word) (memk (k + 1)) rom)
               (fun r => getr r 11 = at_ s (k + 1) /\ getr r 8 = at_ d (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1))
                         /\ getr r 14 = Z_to_bv 64 0
                         /\ regs_agree (fun x => In x core_clob) regs0 r)
               (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
      - eexists. split.
        + mlbu F_a2fc0 D_a2fc0 k.
          stepn F_a2fc4 D_a2fc4.
          msb F_a2fc8 D_a2fc8.
          stepb_ft F_a2fcc D_a2fcc ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_neq; exact Hnzk).
          sv F_a2fd0 D_a2fd0 (Z_to_bv 64 (n - (k + 1))).
          stepn F_a2fd4 D_a2fd4.
          stepn F_a2fd8 D_a2fd8.
          stepn F_a2fdc D_a2fdc.                   (* [comment removed for export] *)
          stepsltu F_a2fe0 D_a2fe0 (Z_to_bv 64 0)
            ltac:(gres; rwH; rewrite v_sltu0 by lia; replace (n - (k + 1) =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
          stepb_ft F_a2fe4 D_a2fe4
            ltac:(rwH; unfold c_eq, bv_eqb, v_andi, at_; unorm;
                  change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by (ltac2:(LK.k [@Hdro; @Hk; @Hkh; @Hs; @Hd; @U; @Hnzk; @Hnal; @Hlast; @Hnws; @Hnwd; @Hdcel; @HR; @H]); lia);
                  pose proof (mod8_range (bv_unsigned s + (k + 1))); unorm;
                  apply mod8_C; apply (C (k + 1)%Z); (ltac2:(LK.k [@Hdro; @Hk; @Hkh; @Hs; @Hd; @U; @Hnzk; @Hnal; @Hlast; @Hnws; @Hnwd; @Hdcel; @HR; @H]); lia)).   (* [comment removed for export] *)
          stepn F_a2fe8 D_a2fe8.                   (* [comment removed for export] *)
          stepb_ft F_a2fec D_a2fec ltac:(cond).    (* [comment removed for export] *)
          apply mst_refl.
        + post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
      - cbv beta. intros r1 (R11 & R8 & R12 & R14 & AG1).
        apply (j_run regs0 r1 (k + 1) 0); try assumption; try lia. }
    (* [comment removed for export] *)
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa2fc0 : word) (memk (k + 1)) rom)
             (fun r => getr r 11 = at_ s (k + 1) /\ getr r 8 = at_ d (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1))
                       /\ getr r 15 = at_ s (k + 1 + 1) /\ getr r 16 = Z_to_bv 64 1
                       /\ regs_agree (fun x => In x core_clob) regs0 r)
             (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
    - eexists. split.
      + mlbu F_a2fc0 D_a2fc0 k.
        stepn F_a2fc4 D_a2fc4.
        msb F_a2fc8 D_a2fc8.
        stepb_ft F_a2fcc D_a2fcc ltac:(rwH; rewrite c_eq_LBv_0; apply Z.eqb_neq; exact Hnzk).
        sv F_a2fd0 D_a2fd0 (Z_to_bv 64 (n - (k + 1))).
        stepn F_a2fd4 D_a2fd4.
        stepn F_a2fd8 D_a2fd8.
        stepn F_a2fdc D_a2fdc.
        stepn F_a2fe0 D_a2fe0.                     (* [comment removed for export] *)
        stepb_ft F_a2fe4 D_a2fe4
          ltac:(rwH; unfold c_eq, bv_eqb, v_andi, at_; unorm;
                change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by (ltac2:(LK.k [@Hdro; @Hk; @Hkh; @Hs; @Hd; @U; @Hnzk; @Hnal; @Hmore; @Hnws; @Hnwd; @Hdcel; @HR; @H]); lia);
                pose proof (mod8_range (bv_unsigned s + (k + 1))); unorm;
                apply mod8_C; apply (C (k + 1)%Z); (ltac2:(LK.k [@Hdro; @Hk; @Hkh; @Hs; @Hd; @U; @Hnzk; @Hnal; @Hmore; @Hnws; @Hnwd; @Hdcel; @HR; @H]); lia)).
        stepn F_a2fe8 D_a2fe8.                     (* [comment removed for export] *)
        stepb_tk F_a2fec D_a2fec ltac:(cond).      (* [comment removed for export] *)
        apply mst_refl.
      + post. eapply regs_agree_trans; [exact AG|]. unfold core_clob. solve_regs_agree.
    - cbv beta. intros r1 (R11 & R8 & R12 & R15 & R16 & AG1).
      apply (IH (Z.to_nat (hd us - (k + 1))) ltac:(lia) regs0 r1 (k + 1)%Z q); try assumption; try lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hsrc Hroom Hdst Hn Hnws Hnwd Hdisj Hro Hdro Hn40 Hrng Hsp2 Hdst2 Hshd Hzg HlastS Hwords Hstk2 Hcel Hdcel"] Lemma core_run : forall regs,
    getr regs 8 = d -> getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = Z_to_bv 64 n ->
    getr regs 2 = Z_to_bv 64 sp2 ->
    exists r (km : Z * (word -> option byte)),
      msteps SEGS (mkst regs (0xa2f74 : word) MB rom) (mkst r (0xa3058 : word) (snd km) rom)
      /\ PF regs r km.
  Proof.
    intros regs H8 H10 H11 H12 HS2.
    pose proof (u64_range s) as Hs. pose proof (u64_range d) as Hd.
    pose proof (hd_facts us ltac:(lia)) as (q & A & Bq & C).
    change MB with (memk 0).
    destruct (c_eq (v_andi (v_xor s d) 7) (Z_to_bv 64 0)) eqn:EQ.
    2:{ (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa2f80 : word) (memk 0) rom)
               (fun r => getr r 11 = at_ s 0 /\ getr r 8 = at_ d 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                         /\ regs_agree (fun x => In x core_clob) regs r)
               (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
      - eexists. split.
        + stepn F_a2f74 D_a2f74.                   (* [comment removed for export] *)
          stepn F_a2f78 D_a2f78.                   (* [comment removed for export] *)
          stepb_ft F_a2f7c D_a2f7c ltac:(rwH; exact EQ).   (* [comment removed for export] *)
          apply mst_refl.
        + post; try (rewrite Z.sub_0_r; reflexivity). unfold core_clob. solve_regs_agree.
      - cbv beta. intros r1 (R11 & R8x & R12 & AG1).
        apply (b_entry regs r1 0); try assumption; try lia; try (intros; lia). }
    destruct (Z.eq_dec (hd us) 0) as [Hh0|Hh0].
    { (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa2ff0 : word) (memk 0) rom)
               (fun r => getr r 11 = at_ s 0 /\ getr r 8 = at_ d 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                         /\ getr r 14 = Z_to_bv 64 (if (n =? 0)%Z then 0 else 1)
                         /\ regs_agree (fun x => In x core_clob) regs r)
               (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
      - eexists. split.
        + stepn F_a2f74 D_a2f74.
          stepn F_a2f78 D_a2f78.
          stepb_tk F_a2f7c D_a2f7c ltac:(rwH; exact EQ).   (* [comment removed for export] *)
          stepiv F_a2fa8 D_a2fa8 (Z_to_bv 64 0)
            ltac:(gres; rwH; imm_norm; unfold v_andi; change (bv_wrap 64 7) with (Z.ones 3);
                  rewrite Z.land_ones by lia; f_equal; apply hd0_mod; lia).   (* [comment removed for export] *)
          stepsltu F_a2fac D_a2fac (Z_to_bv 64 (if (n =? 0)%Z then 0 else 1))
            ltac:(gres; rwH; apply v_sltu0; lia).   (* [comment removed for export] *)
          stepb_tk F_a2fb0 D_a2fb0 ltac:(cond_lia).  (* [comment removed for export] *)
          apply mst_refl.
        + post; try (rewrite Z.sub_0_r; reflexivity). unfold core_clob. solve_regs_agree.
      - cbv beta. intros r1 (R11 & R8x & R12 & R14 & AG1).
        apply (j_run regs r1 0 (if (n =? 0)%Z then 0 else 1)); try assumption; try lia; try (intros; lia).
        destruct (Z.eqb_spec n 0); [left; lia | right]. split; [reflexivity|]. split; [lia|]. exists q. lia. }
    destruct (Z.eq_dec n 0) as [Hn0|Hn0].
    { (* [comment removed for export] *)
      eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa2ff0 : word) (memk 0) rom)
               (fun r => getr r 11 = at_ s 0 /\ getr r 8 = at_ d 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                         /\ getr r 14 = Z_to_bv 64 0
                         /\ regs_agree (fun x => In x core_clob) regs r)
               (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
      - eexists. split.
        + stepn F_a2f74 D_a2f74.
          stepn F_a2f78 D_a2f78.
          stepb_tk F_a2f7c D_a2f7c ltac:(rwH; exact EQ).
          stepn F_a2fa8 D_a2fa8.                   (* [comment removed for export] *)
          stepsltu F_a2fac D_a2fac (Z_to_bv 64 0)
            ltac:(gres; rwH; rewrite v_sltu0 by lia; replace (n =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
          stepb_ft F_a2fb0 D_a2fb0
            ltac:(rwH; unfold c_eq, bv_eqb, v_andi; imm_norm; change (bv_wrap 64 7) with (Z.ones 3);
                  rewrite Z.land_ones by lia; pose proof (mod8_range (bv_unsigned s)); unorm;
                  apply hdnz_mod; lia).            (* [comment removed for export] *)
          stepb_tk F_a2fb4 D_a2fb4 ltac:(cond).    (* [comment removed for export] *)
          apply mst_refl.
        + post; try (rewrite Z.sub_0_r; reflexivity). unfold core_clob. solve_regs_agree.
      - cbv beta. intros r1 (R11 & R8x & R12 & R14 & AG1).
        apply (j_run regs r1 0 0); try assumption; try lia; try (intros; lia). }
    (* [comment removed for export] *)
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa2fc0 : word) (memk 0) rom)
             (fun r => getr r 11 = at_ s 0 /\ getr r 8 = at_ d 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                       /\ getr r 15 = at_ s (0 + 1) /\ getr r 16 = Z_to_bv 64 1
                       /\ regs_agree (fun x => In x core_clob) regs r)
             (fun r km => mkst r (0xa3058 : word) (snd km) rom)).
    - eexists. split.
      + stepn F_a2f74 D_a2f74.
        stepn F_a2f78 D_a2f78.
        stepb_tk F_a2f7c D_a2f7c ltac:(rwH; exact EQ).
        stepn F_a2fa8 D_a2fa8.
        stepn F_a2fac D_a2fac.
        stepb_ft F_a2fb0 D_a2fb0
          ltac:(rwH; unfold c_eq, bv_eqb, v_andi; imm_norm; change (bv_wrap 64 7) with (Z.ones 3);
                rewrite Z.land_ones by lia; pose proof (mod8_range (bv_unsigned s)); unorm;
                apply hdnz_mod; lia).
        stepb_ft F_a2fb4 D_a2fb4 ltac:(cond).      (* [comment removed for export] *)
        stepn F_a2fb8 D_a2fb8.                     (* [comment removed for export] *)
        stepn F_a2fbc D_a2fbc.                     (* [comment removed for export] *)
        apply mst_refl.
      + post; try (rewrite Z.sub_0_r; reflexivity). unfold core_clob. solve_regs_agree.
    - cbv beta. intros r1 (R11 & R8x & R12 & R15 & R16 & AG1).
      apply (h_loop (Z.to_nat (hd us)) regs r1 0 q); try assumption; try lia; try (intros; lia).
  Qed.
End CORE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strncpy_clob : list reg := [11; 12; 13; 14; 15; 16; 17; 5; 6; 7; 28; 29; 30; 31]%list.
Definition stpncpy_clob : list reg := [10; 11; 12; 13; 14; 15; 16; 17; 5; 6; 7; 28; 29; 30; 31]%list.

Definition SNC_FRAME : Z := 2248.   (* [comment removed for export] *)

(* [comment removed for export] *)
Record sncH (mem : word -> option byte) (d s sp : word) (n : Z) (src : list byte) : Prop := SNCH {
  Hsrc  : rdn SEGS mem s (length src) = Some src;
  Hroom : (n <= Z.of_nat (length src))%Z
          \/ exists K, (0 <= K < Z.of_nat (length src))%Z /\ bv_unsigned (nth (Z.to_nat K) src B0) = 0%Z
                       /\ (strlen_span (bv_unsigned s) K <= Z.of_nat (length src))%Z;
  Hdst  : store_ok SEGS mem d (Z.to_nat n) = true;
  Hn    : (0 <= n <= 2 ^ 40)%Z;
  Hnws  : (bv_unsigned s + Z.of_nat (length src) < 2 ^ 64)%Z;
  Hnwd  : (bv_unsigned d + n < 2 ^ 64)%Z;
  Hdisj : (bv_unsigned d + n <= bv_unsigned s \/ bv_unsigned s + Z.of_nat (length src) <= bv_unsigned d)%Z;
  Hro   : rodata_clear mem;
  Hdro  : (0x10388 <= bv_unsigned d \/ bv_unsigned d + n <= 0x10360)%Z;
  Hstk  : forall a, (bv_unsigned sp - SNC_FRAME <= a < bv_unsigned sp)%Z -> store_ok SEGS mem (Z_to_bv 64 a) 1 = true;
  Hsp   : (BothRegionPoisoned.SB + SNC_FRAME + 8 <= bv_unsigned sp < 2 ^ 64)%Z;
  Hsps  : (bv_unsigned sp <= bv_unsigned s \/ bv_unsigned s + Z.of_nat (length src) <= bv_unsigned sp - SNC_FRAME)%Z;
  Hspd  : (bv_unsigned sp <= bv_unsigned d \/ bv_unsigned d + n <= bv_unsigned sp - SNC_FRAME)%Z;
  Hrng  : (0 < n)%Z -> (bv_unsigned d + n <= kLowEnd)%Z \/ (kHighBeg <= bv_unsigned d /\ bv_unsigned d + n <= kHighEnd)%Z;
  Hshd  : (0 < n)%Z -> (BothRegionPoisoned.SB + (bv_unsigned d + n - 1) / 8 + 8 < bv_unsigned sp - SNC_FRAME)%Z;
  Hzg   : forall g, (0 < n)%Z -> (bv_unsigned d / 8 <= g < (bv_unsigned d + n - 1) / 8)%Z ->
            mem (Z_to_bv 64 (BothRegionPoisoned.SB + g)) = Some (Z_to_bv 8 0);
  Hlast : (0 < n)%Z -> exists b1 : byte, mem (Z_to_bv 64 (BothRegionPoisoned.SB + (bv_unsigned d + n - 1) / 8)) = Some b1
                       /\ (bv_unsigned b1 = 0%Z \/ ((bv_unsigned d + n - 1) mod 8 < bv_unsigned b1 < 8)%Z);
  Hwords : (0 < n)%Z -> forall a, ((BothRegionPoisoned.SB + bv_unsigned d / 8) / 8 * 8 <= a)%Z ->
             (a <= (BothRegionPoisoned.SB + (bv_unsigned d + n - 1) / 8) / 8 * 8)%Z -> (a mod 8 = 0)%Z ->
             exists w : word, rdn SEGS mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 w);
  Hcel  : im_cells mem;
  Hdcel : (bv_unsigned d + n <= 0xa8000 \/ 0xb3340 <= bv_unsigned d)%Z }.

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
  #[local] Notation SHB := BothRegionPoisoned.SB.

  (* [comment removed for export] *)
  Definition MB (ra s0 : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes mem (Z_to_bv 64 (usp - 8)) (W8 ra)) (Z_to_bv 64 (usp - 16)) (W8 s0))
                   (Z_to_bv 64 (usp - 24)) (W8 (0xa2f50 : word))) (Z_to_bv 64 (usp - 32)) (W8 d).
  (* [comment removed for export] *)
  Definition MF (ra s0 : word) (m : Z) : word -> option byte := FIN (MB ra s0) d n src m.

  #[using="Type"] Lemma lenW8 : forall v : word, length (W8 v) = 8%nat.
  Proof. intros v. apply length_N_to_le_bytes. Qed.

  #[using="mem d s n src HOK"] Lemma Hsp' : (0x7fff8000 + 2256 <= usp < 2 ^ 64)%Z.
  Proof. pose proof (Hsp _ _ _ _ _ _ HOK). unfold SNC_FRAME, BothRegionPoisoned.SB in *. lia. Qed.

  #[using="s n src HOK"] Lemma MB_out : forall ra s0 (a : word),
    (bv_unsigned a < usp - 32 \/ usp <= bv_unsigned a)%Z -> MB ra s0 a = mem a.
  Proof.
    intros ra s0 a Ha. pose proof Hsp'. unfold MB.
    rewrite !MemSplit.wbytes_outside; rewrite ?lenW8; u_norm; try lia. reflexivity.
  Qed.

  #[using="s n src HOK"] Lemma rdn_MB_out : forall ra s0 (a : Z) k, (0 <= a)%Z -> (a + Z.of_nat k <= usp - 32)%Z ->
    rdn SEGS (MB ra s0) (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof.
    intros ra s0 a k Ha Hk. pose proof Hsp'. apply rdn_ext; [u_norm; lia|]. intros x Hx. revert Hx. u_norm. intros Hx. apply MB_out. lia.
  Qed.

  #[using="HOK"] Lemma MB_core : forall ra s0,
    rdn SEGS (MB ra s0) s (length src) = Some src
    /\ store_ok SEGS (MB ra s0) d (Z.to_nat n) = true
    /\ rodata_clear (MB ra s0).
  Proof.
    intros ra s0. pose proof Hsp'. pose proof (u64_range s). destruct HOK. unfold SNC_FRAME in *. repeat split.
    - rewrite <- Hsrc0. apply rdn_ext; [lia|]. intros x Hx. apply MB_out. lia.
    - unfold MB. repeat (eapply store_ok_mono; [apply wbytes_grows|]). exact Hdst0.
    - intros i Hi. rewrite MB_out; [apply Hro0; exact Hi | u_norm; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="s src HOK"] Lemma MB_icpt : forall ra s0,
    (forall g, (0 < n)%Z -> (bv_unsigned d / 8 <= g < (bv_unsigned d + n - 1) / 8)%Z -> MB ra s0 (Z_to_bv 64 (SHB + g)) = Some (Z_to_bv 8 0))
    /\ ((0 < n)%Z -> exists b1 : byte, MB ra s0 (Z_to_bv 64 (SHB + (bv_unsigned d + n - 1) / 8)) = Some b1
                      /\ (bv_unsigned b1 = 0%Z \/ ((bv_unsigned d + n - 1) mod 8 < bv_unsigned b1 < 8)%Z))
    /\ ((0 < n)%Z -> forall a, ((SHB + bv_unsigned d / 8) / 8 * 8 <= a)%Z -> (a <= (SHB + (bv_unsigned d + n - 1) / 8) / 8 * 8)%Z -> (a mod 8 = 0)%Z ->
          exists w : word, rdn SEGS (MB ra s0) (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 w))
    /\ (forall a, (usp - 32 - IM_FRAME <= a < usp - 32)%Z -> store_ok SEGS (MB ra s0) (Z_to_bv 64 a) 1 = true)
    /\ im_cells (MB ra s0).
  Proof.
    intros ra s0. pose proof Hsp'. pose proof SB_val. pose proof (u64_range d). pose proof (Hn _ _ _ _ _ _ HOK).
    assert (SHD : (0 < n)%Z -> (SHB + (bv_unsigned d + n - 1) / 8 + 8 < usp - 2248)%Z).
    { intros Hn0. pose proof (Hshd _ _ _ _ _ _ HOK Hn0). unfold SNC_FRAME in *. lia. }
    pose proof (Z.div_mod (bv_unsigned d) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned d) 8 ltac:(lia)).
    split; [|split; [|split; [|split]]].
    - intros g Hn0 Hg. rewrite MB_out; [exact (Hzg _ _ _ _ _ _ HOK g Hn0 Hg)|]. u_norm. specialize (SHD Hn0). lia.
    - intros Hn0. destruct (Hlast _ _ _ _ _ _ HOK Hn0) as (b1 & L1 & B1). exists b1. split; [|exact B1].
      rewrite MB_out; [exact L1|]. u_norm. specialize (SHD Hn0). lia.
    - intros Hn0 a Ha Hb Hm. specialize (SHD Hn0).
      pose proof (Z.div_mod (SHB + bv_unsigned d / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SHB + bv_unsigned d / 8) 8 ltac:(lia)).
      pose proof (Z.div_mod (SHB + (bv_unsigned d + n - 1) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SHB + (bv_unsigned d + n - 1) / 8) 8 ltac:(lia)).
      rewrite rdn_MB_out; [exact (Hwords _ _ _ _ _ _ HOK Hn0 a Ha Hb Hm)|lia|cbn; lia].
    - intros a Ha. unfold MB. repeat apply store_ok1_wbytes. apply (Hstk _ _ _ _ _ _ HOK). unfold SNC_FRAME, IM_FRAME in *. lia.
    - pose proof (Hcel _ _ _ _ _ _ HOK) as (C & C1 & B1 & C2). unfold im_cells, cells, cell in *.
      rewrite !rdn_MB_out by (cbn; lia). split; [exact C|]. split; [exact C1|]. split; [exact B1|exact C2].
  Qed.

  (* [comment removed for export] *)
  #[using="s HOK"] Lemma rd_slot : forall ra s0 m (mf : word -> option byte) (k : Z) (v : word), (0 <= m <= n)%Z -> (m <= W)%Z ->
    (forall x : word, (bv_unsigned x < usp - 32 - IM_FRAME \/ usp - 32 <= bv_unsigned x)%Z -> mf x = MF ra s0 m x) ->
    ((k = 8%Z /\ v = ra) \/ (k = 16%Z /\ v = s0) \/ (k = 24%Z /\ v = (0xa2f50 : word)) \/ (k = 32%Z /\ v = d)) ->
    rdn SEGS mf (Z_to_bv 64 (usp - k)) 8 = Some (W8 v).
  Proof.
    intros ra s0 m mf k v Hm HmW MFJ Hk. pose proof Hsp'. pose proof (u64_range d). pose proof (Hnwd _ _ _ _ _ _ HOK).
    pose proof (Hspd _ _ _ _ _ _ HOK) as SPD. unfold SNC_FRAME in SPD.
    rewrite (rdn_ext SEGS 8 mf (MB ra s0)).
    2:{ u_norm. lia. }
    2:{ intros x Hx. rewrite MFJ by (revert Hx; u_norm; lia). unfold MF, FIN.
        apply MemSplit.wbytes_outside; rewrite length_app, length_firstn, length_zeros; revert Hx; u_norm; lia. }
    unfold MB. destruct Hk as [(-> & ->)|[(-> & ->)|[(-> & ->)|(-> & ->)]]];
      repeat (rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; (ltac2:(LK.k [@H]); lia))); apply rdn_wbytes_hit8; u_norm; (ltac2:(LK.k [@H]); lia).
  Qed.

  Ltac okstk :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    apply store_ok8_bytes; [lia | lia | intros j Hj; apply (Hstk _ _ _ _ _ _ HOK); unfold SNC_FRAME; lia].
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

  #[using="HOK"] Theorem strncpy_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
    getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = Z_to_bv 64 n ->
    exists regs' (km : Z * (word -> option byte)),
      msteps SEGS (mkst regs (0xa2f3c : word) mem rom) (mkst regs' ret (snd km) rom)
      /\ (regs_agree (fun x => In x strncpy_clob) regs regs'
          /\ SPEC n src (fst km)
          /\ (forall x : word, (bv_unsigned x < usp - 32 - IM_FRAME \/ usp - 32 <= bv_unsigned x)%Z -> snd km x = MF ret (getr regs 8) (fst km) x)
          /\ (forall x, mem x <> None -> snd km x <> None)).
  Proof.
    intros regs ret Hret H1 H2 H10 H11 H12.
    pose proof Hsp' as HSP. pose proof (u64_range d) as Hd. pose proof (Hn _ _ _ _ _ _ HOK) as HN.
    set (s0 := getr regs 8).
    destruct (MB_core ret s0) as (C1 & C2 & C3).
    destruct (MB_icpt ret s0) as (I1 & I2 & I3 & I4 & I5).
    assert (SPS : (usp - 32 <= bv_unsigned s \/ bv_unsigned s + W <= usp - 32 - IM_FRAME)%Z).
    { pose proof (Hsps _ _ _ _ _ _ HOK). unfold SNC_FRAME, IM_FRAME in *. lia. }
    assert (SPD : (usp - 32 <= bv_unsigned d \/ bv_unsigned d + n <= usp - 32 - IM_FRAME)%Z).
    { pose proof (Hspd _ _ _ _ _ _ HOK). unfold SNC_FRAME, IM_FRAME in *. lia. }
    assert (SHD : (0 < n)%Z -> (SHB + (bv_unsigned d + n - 1) / 8 + 8 < usp - 32 - IM_FRAME)%Z).
    { intros Hn0. pose proof (Hshd _ _ _ _ _ _ HOK Hn0). unfold SNC_FRAME, IM_FRAME in *. lia. }
    assert (HSP2 : (SHB + IM_FRAME + 8 <= usp - 32 < 2 ^ 64)%Z) by (unfold IM_FRAME, BothRegionPoisoned.SB; lia).
    (* [comment removed for export] *)
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa2f74 : word) (MB ret s0) rom)
             (fun r => getr r 1 = (0xa2f50 : word) /\ getr r 2 = Z_to_bv 64 (usp - 32)
                       /\ getr r 8 = d /\ getr r 10 = d /\ getr r 11 = s /\ getr r 12 = Z_to_bv 64 n
                       /\ regs_agree (fun x => In x [1; 2; 8]%list) regs r)
             (fun r km => mkst r ret (snd km) rom)).
    { eexists. split.
      - stepiv F_a2f3c D_a2f3c (Z_to_bv 64 (usp - 16))
          ltac:(gres; imm_norm; rwH; unfold v_addi; f_equal; lia).   (* [comment removed for export] *)
        msd F_a2f40 D_a2f40 (Z_to_bv 64 (usp - 8)).                  (* [comment removed for export] *)
        msd F_a2f44 D_a2f44 (Z_to_bv 64 (usp - 16)).                 (* [comment removed for export] *)
        stepn F_a2f48 D_a2f48.                                        (* [comment removed for export] *)
        stepn F_a2f4c D_a2f4c.                                        (* [comment removed for export] *)
        stepiv F_a2f64 D_a2f64 (Z_to_bv 64 (usp - 32))
          ltac:(gres; imm_norm; rwH; unfold v_addi; unorm; f_equal; lia).   (* [comment removed for export] *)
        msd F_a2f68 D_a2f68 (Z_to_bv 64 (usp - 24)).                 (* [comment removed for export] *)
        msd F_a2f6c D_a2f6c (Z_to_bv 64 (usp - 32)).                 (* [comment removed for export] *)
        stepn F_a2f70 D_a2f70.                                        (* [comment removed for export] *)
        rwH. fold s0. unfold MB.
        replace (Z_to_bv 64 0xa2f50) with (0xa2f50 : word) by (apply bv_eq; vm_compute; reflexivity).
        apply mst_refl.
      - cbv beta. repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity).
        solve_regs_agree. }
    cbv beta. intros r1 (R1 & R2 & R8 & R10 & R11 & R12 & AG1).
    (* [comment removed for export] *)
    eapply (runs_trans_km SEGS _ (fun r => mkst r (0xa2f74 : word) (MB ret s0) rom) (fun r => r = r1)
             (fun r km => mkst r ret (snd km) rom)).
    { exists r1. split; [apply mst_refl | reflexivity]. }
    cbv beta. intros r1' ->.
    destruct (core_run (MB ret s0) d s n src rom C1 (Hroom _ _ _ _ _ _ HOK) C2 (proj1 HN)
                (Hnws _ _ _ _ _ _ HOK) (Hnwd _ _ _ _ _ _ HOK) (Hdisj _ _ _ _ _ _ HOK) C3 (Hdro _ _ _ _ _ _ HOK)
                (usp - 32) (proj2 HN) (Hrng _ _ _ _ _ _ HOK) HSP2 SPD SHD I1 I2 I3 I4 I5 (Hdcel _ _ _ _ _ _ HOK)
                r1 R8 R10 R11 R12 R2) as (r2 & [m mf] & RUN & (HS & S8 & AG2) & MFJ & MG).
    cbn [fst snd] in HS, S8, MFJ, MG, RUN.
    pose proof HS as (Hm & HmW & _ & _).
    assert (S2 : getr r2 2 = Z_to_bv 64 (usp - 32)).
    { rewrite (AG2 2%bv) by (unfold core_clob; notin_list). exact R2. }
    assert (MFJ' : forall x : word, (bv_unsigned x < usp - 32 - IM_FRAME \/ usp - 32 <= bv_unsigned x)%Z -> mf x = MF ret s0 m x).
    { intros x Hx. apply MFJ. unfold JOUT. exact Hx. }
    eexists. exists (m, mf). cbn [fst snd]. split; [|split; [|split; [exact HS|split; [exact MFJ'|]]]].
    - eapply msteps_trans; [exact RUN|].
      (* [comment removed for export] *)
      stepn F_a3058 D_a3058.                                          (* [comment removed for export] *)
      mld8 F_a305c D_a305c (0xa2f50 : word) (rd_slot ret s0 m mf 24 (0xa2f50 : word) Hm HmW MFJ' ltac:(tauto)).  (* [comment removed for export] *)
      mld8 F_a3060 D_a3060 d (rd_slot ret s0 m mf 32 d Hm HmW MFJ' ltac:(tauto)).                            (* [comment removed for export] *)
      stepiv F_a3064 D_a3064 (Z_to_bv 64 (usp - 16))
        ltac:(gres; imm_norm; rwH; unfold v_addi; unorm; f_equal; lia).                             (* [comment removed for export] *)
      stepret F_a3068 D_a3068 (0xa2f50 : word) ltac:(reflexivity).                                  (* [comment removed for export] *)
      (* [comment removed for export] *)
      stepn F_a2f50 D_a2f50.                                          (* [comment removed for export] *)
      mld8 F_a2f54 D_a2f54 ret (rd_slot ret s0 m mf 8 ret Hm HmW MFJ' ltac:(tauto)).                          (* [comment removed for export] *)
      mld8 F_a2f58 D_a2f58 s0 (rd_slot ret s0 m mf 16 s0 Hm HmW MFJ' ltac:(tauto)).                           (* [comment removed for export] *)
      stepiv F_a2f5c D_a2f5c sp
        ltac:(gres; imm_norm; rwH; unfold v_addi; unorm; rewrite <- (Z_to_bv_bv_unsigned 64 sp) at 2; f_equal; lia).
                                                                      (* [comment removed for export] *)
      stepret F_a2f60 D_a2f60 ret ltac:(reflexivity).
      apply mst_refl.
    - (* [comment removed for export] *)
      assert (AGall : regs_agree (fun x => In x ([10; 8; 2; 1] ++ strncpy_clob)%list) regs r2).
      { eapply regs_agree_trans; [eapply regs_agree_mono; [|exact AG1] | eapply regs_agree_mono; [|exact AG2]];
          unfold core_clob, strncpy_clob; cbn [In app]; intros x HH; decompose [or] HH; subst; auto 20. }
      apply (regs_agree_drop _ 1); [apply (regs_agree_drop _ 2); [apply (regs_agree_drop _ 8); [apply (regs_agree_drop _ 10)|]|]|];
        [ | gres; subst s0; rewrite ?H10; reflexivity | gres; subst s0; reflexivity | gres; rewrite H2; reflexivity | gres; rewrite H1; reflexivity ].
      repeat (apply regs_agree_upd; [in_list|]). cbn [app] in AGall. exact AGall.
    - intros x Hx. apply MG. unfold MB. repeat apply wbytes_keep. exact Hx.
  Qed.
End WRAP.

Theorem ref_strncpy : forall mem (d s sp : word) (n : Z) (src : list byte) rom regs (ret : word),
  sncH mem d s sp n src ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = Z_to_bv 64 n ->
  exists regs' mem' (m : Z),
    msteps SEGS (mkst regs (0xa2f3c : word) mem rom) (mkst regs' ret mem' rom)
    /\ regs_agree (fun x => In x strncpy_clob) regs regs'
    /\ SPEC n src m
    /\ (forall x : word, (bv_unsigned x < bv_unsigned sp - SNC_FRAME \/ bv_unsigned sp <= bv_unsigned x)%Z ->
          mem' x = wbytes mem d (firstn (Z.to_nat m) src ++ zeros (Z.to_nat (n - m))) x)
    /\ (forall x, mem x <> None -> mem' x <> None).
Proof.
  intros mem d s sp n src rom regs ret HOK Hret H1 H2 H10 H11 H12.
  destruct (strncpy_run mem d s sp n src rom HOK regs ret Hret H1 H2 H10 H11 H12) as (r & [m mf] & RUN & AG & HS & MFJ & MG).
  cbn [fst snd] in RUN, HS, MFJ, MG. pose proof HS as (Hm & HmW & _ & _).
  pose proof (u64_range d) as Hd. pose proof (Hsp' mem d s sp n src HOK) as HSP.
  pose proof (Hnwd _ _ _ _ _ _ HOK) as Hnwd'.
  exists r, mf, m.
  split; [exact RUN|]. split; [exact AG|]. split; [exact HS|]. split; [|exact MG].
  intros x Hx. unfold SNC_FRAME, IM_FRAME in *. rewrite MFJ by lia. unfold MF, FIN.
  apply VBothMemsetWalk.wbytes_agree. apply (MB_out mem d s sp n src HOK). lia.
Qed.
