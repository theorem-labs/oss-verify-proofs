(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim MuslStrlen
  RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.musl Require Import Pm10MemcpyBase_u Pm10Memchr_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10_code_b6000_b7000_u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition sl_clob : list reg := [10; 11; 12; 13; 14; 15; 16]%bv.
Section FPX_0. Context {fx : PropExec.FPState}.
Definition sl_agree (regs regs' : bvmap 5 word) : Prop := regs_agree (fun r => In r sl_clob) regs regs'.
Lemma sl_agree_refl : forall regs, sl_agree regs regs.
Proof. intros regs. apply regs_agree_refl. Qed.
Lemma sl_agree_trans : forall r1 r2 r3, sl_agree r1 r2 -> sl_agree r2 r3 -> sl_agree r1 r3.
Proof. intros r1 r2 r3. apply regs_agree_trans. Qed.
Lemma sl_agree_upd : forall regs regs' (rd : reg) v,
  sl_agree regs regs' -> In rd sl_clob -> sl_agree regs (regupd regs' rd v).
Proof. intros regs regs' rd v H Hin. apply regs_agree_upd; assumption. Qed.
Lemma sl_agree_getr : forall regs regs' (r : reg), sl_agree regs regs' -> ~ In r sl_clob -> getr regs' r = getr regs r.
Proof. intros regs regs' r H Hn. apply H. exact Hn. Qed.
End FPX_0.
Ltac in_sl_clob := cbn [sl_clob In]; repeat first [ left; reflexivity | right ].
Ltac solve_sl_agree :=
  repeat (apply sl_agree_upd; [| in_sl_clob]); first [apply sl_agree_refl | assumption].

Section FPX_1. Context {fx : PropExec.FPState}.

Definition TWs (x : word) : word := v_and (v_or (v_sub (Z_to_bv 64 Mc) x) x) (Z_to_bv 64 Hc).

Lemma TWs_TW : forall x, TWs x = TW x.
Proof. intros x. unfold TWs, TW. rewrite !v_xor_0. reflexivity. Qed.

Lemma v_sub_at : forall (s : word) K, (0 <= K < 2 ^ 64)%Z -> v_sub (at_ s K) s = Z_to_bv 64 K.
Proof.
  intros s K HK. unfold v_sub, at_. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma v_sub_self : forall (s : word), v_sub s s = Z_to_bv 64 0.
Proof. intros s. unfold v_sub. rewrite Z.sub_diag. reflexivity. Qed.

Lemma andi7_u : forall (s : word) j, (0 <= bv_unsigned s + j < 2 ^ 64)%Z ->
  bv_unsigned (v_andi (at_ s j) 7) = ((bv_unsigned s + j) mod 8)%Z.
Proof.
  intros s j Hj. rewrite u_andi by lia. rewrite at_u by lia.
  change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

Record slenH (mem : word -> option byte) (s : word) (buf : list byte) (K : Z) : Prop := SLENH {

  Hbuf : rdn RSEGS mem s (length buf) = Some buf;

  Hwin : ((bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf))%Z;
  Hnw  : (bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64)%Z;

  HK0  : (0 <= K)%Z;
  Hzero : bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0%Z;
  Hnz  : forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0%Z;

  Hro  : rodata_clear mem }.

Section SLEN.
  Variable mem : word -> option byte.
  Variable s : word.
  Variable buf : list byte.
  Variable K : Z.
  Variable rom : word -> option byte.
  Hypothesis HOK : slenH mem s buf K.

  #[local] Abbreviation L := (Z.of_nat (length buf)).
  Definition b_ (j : Z) : byte := nth (Z.to_nat j) buf (Z_to_bv 8 0).
  Definition sb_ (j : Z) (m : nat) : list byte := sub buf (Z.to_nat j) m.

  Let Hbuf := Hbuf _ _ _ _ HOK.
  Let Hwin : ((bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + L)%Z := Hwin _ _ _ _ HOK.
  Let Hnw : (bv_unsigned s + L < 2 ^ 64)%Z := Hnw _ _ _ _ HOK.
  Let HK0 : (0 <= K)%Z := HK0 _ _ _ _ HOK.
  Let Hro := Hro _ _ _ _ HOK.

  Lemma KL : (K + 1 <= L)%Z.
  Proof.
    clear -Hwin HK0. pose proof (u64_range s).
    pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)). lia.
  Qed.

  Definition KE : Z := ((bv_unsigned s + K) / 8 * 8 + 8 - bv_unsigned s)%Z.
  Lemma KE_facts : (K + 1 <= KE <= K + 8)%Z /\ (KE <= L)%Z /\ ((bv_unsigned s + KE) mod 8 = 0)%Z.
  Proof.
    unfold KE. clear -Hwin HK0. pose proof (u64_range s).
    pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)).
    repeat split; try lia.
    replace (bv_unsigned s + ((bv_unsigned s + K) / 8 * 8 + 8 - bv_unsigned s))%Z
      with (8 + ((bv_unsigned s + K) / 8) * 8)%Z by lia.
    rewrite Z.mod_add by lia. reflexivity.
  Qed.

  Lemma bz : bv_unsigned (b_ K) = 0%Z.
  Proof. exact (Hzero _ _ _ _ HOK). Qed.
  Lemma bnz : forall j, (0 <= j < K)%Z -> bv_unsigned (b_ j) <> 0%Z.
  Proof. intros j Hj. unfold b_. apply (Hnz _ _ _ _ HOK). lia. Qed.

  Lemma rd_w : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= L)%Z ->
    rdn RSEGS mem (at_ s j) m = Some (sb_ j m).
  Proof.
    intros j m Hj Hm. unfold sb_.
    replace (at_ s j) with (at_ s (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
    apply (rdn_sub RSEGS mem (length buf)); [exact Hbuf | lia].
  Qed.

  Lemma rd_b : forall j, (0 <= j)%Z -> (j + 1 <= L)%Z ->
    rdn RSEGS mem (at_ s j) 1 = Some [b_ j].
  Proof.
    intros j Hj H1. rewrite (rd_w j 1) by lia. unfold sb_, b_.
    rewrite sub_nth; [reflexivity | lia].
  Qed.

  Lemma sb_len : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= L)%Z -> length (sb_ j m) = m.
  Proof. intros j m Hj Hm. unfold sb_. apply sub_length. lia. Qed.

  Lemma sb_nth : forall j (i : nat), (0 <= j)%Z -> (i < 8)%nat -> (j + 8 <= L)%Z ->
    nth i (sb_ j 8) (Z_to_bv 8 0) = b_ (j + Z.of_nat i).
  Proof.
    intros j i Hj Hi H8. unfold sb_, b_. rewrite nth_sub by lia. f_equal. lia.
  Qed.

  Lemma m_lbu : forall regs pc w rd rs (imm : bv 12) j0 j,
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= j)%Z -> (j + 1 <= L)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (b_ j))) (v_addi pc 4) mem rom).
  Proof.
    intros regs pc w rd rs imm j0 j Hf He Hd Hrs Hj Hj0 Hj1.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs, at_addi, Hj. apply rd_b; lia.
  Qed.

  Lemma m_ld : forall regs pc w rd rs (imm : bv 12) j0 j,
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
    getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= j)%Z -> (j + 8 <= L)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LDv (sb_ j 8))) (v_addi pc 4) mem rom).
  Proof.
    intros regs pc w rd rs imm j0 j Hf He Hd Hrs Hj Hj0 Hj8.
    eapply step_ld; [exact Hf | exact He | exact Hd | |].
    - rewrite Hrs, at_addi, Hj. apply (rd_w j 8); lia.
    - symmetry. apply u_LDv. apply sb_len; lia.
  Qed.

  Lemma al_room : forall j, ((bv_unsigned s + j) mod 8 = 0)%Z -> (0 <= j <= K)%Z -> (j + 8 <= KE)%Z.
  Proof.
    intros j Hal Hj. unfold KE. clear -Hal Hj HK0. pose proof (u64_range s).
    pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.div_mod (bv_unsigned s + j) 8 ltac:(lia)).
    assert ((bv_unsigned s + j) / 8 <= (bv_unsigned s + K) / 8)%Z by (apply Z.div_le_mono; lia).
    lia.
  Qed.

  Lemma tw_hit : forall j, (0 <= j <= K)%Z -> (K < j + 8)%Z -> (j + 8 <= L)%Z ->
    c_eq (TWs (LDv (sb_ j 8))) (Z_to_bv 64 Hc) = false.
  Proof.
    intros j Hj HKj HL. rewrite TWs_TW.
    apply (TW_haszero _ (Z.to_nat (K - j))).
    - apply sb_len; lia.
    - lia.
    - rewrite sb_nth by lia. rewrite <- bz. f_equal. unfold b_. f_equal. lia.
    - intros jj Hjj. rewrite sb_nth by lia. apply bnz. lia.
  Qed.

  Lemma tw_miss : forall j, (0 <= j)%Z -> (j + 8 <= K)%Z -> (j + 8 <= L)%Z ->
    c_eq (TWs (LDv (sb_ j 8))) (Z_to_bv 64 Hc) = true.
  Proof.
    intros j Hj HKj HL. rewrite TWs_TW. apply TW_nozero.
    - apply sb_len; lia.
    - intros i Hi. rewrite sb_nth by lia. apply bnz. lia.
  Qed.

  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply m_lbu with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mld F D jj :=
    chain_step; [reflexivity
      | eapply m_ld with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia]
      | step_simpl]; vnorm.

  Ltac condb :=
    rwH; rewrite ?getr_zero; rewrite c_eq_LBv_0;
    first [ apply Z.eqb_eq; rewrite <- bz; f_equal; f_equal; lia
          | apply Z.eqb_neq; apply bnz; lia ].

  Ltac cond := try unfold v_addi; cond_lia.

  Ltac condw lem :=
    rwH;
    lazymatch goal with |- c_eq (v_and (v_or (v_sub _ ?x) _) _) _ = ?b =>
      change (c_eq (TWs x) (Z_to_bv 64 Hc) = b) end;
    apply lem; lia.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (rewrite ?at_0; reflexivity);
               try (f_equal; lia); try (unfold v_addi; unorm; f_equal; lia); try solve_sl_agree.

  Lemma t_loop : forall (i : nat) regs (ret : word) j,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s -> getr regs 12 = at_ s j -> getr regs 11 = at_ s (j - 1) ->
    (0 <= j <= K)%Z -> (Z.of_nat i = K - j)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0xb8368 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ sl_agree regs regs'.
  Proof.
    pose proof KL as HKL. pose proof (u64_range s) as Hs.
    induction i as [|i IH]; intros regs ret j Hret H1 H10 H12 H11 Hj Hi.
    -
      eexists. split.
      + mlbu F_b64d8 D_b64d8 j.
        stepn F_b64dc D_b64dc.
        stepn F_b64e0 D_b64e0.
        stepb_ft F_b64e4 D_b64e4 ltac:(condb).
        stepiv F_b64e8 D_b64e8 (Z_to_bv 64 K)
          ltac:(gres; rwH; rewrite ?at_addi; replace (j - 1 + 1)%Z with K by lia; apply v_sub_at; lia).
        stepret F_b64ec D_b64ec ret ltac:(rwH; reflexivity).
        apply mst_refl.
      + post.
    -
      eapply (runs_trans RSEGS _ (fun r => mkst r (0xb8368 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (j + 1) /\ getr r 11 = at_ s (j + 1 - 1)
                         /\ sl_agree regs r)).
      + eexists. split.
        * mlbu F_b64d8 D_b64d8 j.
          stepn F_b64dc D_b64dc.
          stepn F_b64e0 D_b64e0.
          stepb_tk F_b64e4 D_b64e4 ltac:(condb).
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R12 & R11 & KC).
        destruct (IH r1 ret (j + 1)%Z Hret R1 R10 R12 R11 ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
  Qed.

  Lemma w_loop : forall (i : nat) regs (ret : word) j,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s -> getr regs 12 = at_ s (j - 8) -> getr regs 11 = at_ s (j - 9) ->
    getr regs 13 = Z_to_bv 64 Mc -> getr regs 14 = Z_to_bv 64 Hc ->
    (0 <= j <= K)%Z -> ((bv_unsigned s + j) mod 8 = 0)%Z -> (Z.of_nat i = (K - j) / 8)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0xb834c : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ sl_agree regs regs'.
  Proof.
    pose proof KL as HKL. pose proof KE_facts as (HKE1 & HKE2 & HKE3). pose proof (u64_range s) as Hs.
    induction i as [|i IH]; intros regs ret j Hret H1 H10 H12 H11 H13 H14 Hj Hal Hi;
      pose proof (al_room j Hal Hj) as HR.
    -
      assert (HKj : (K < j + 8)%Z).
      { clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
      eapply (runs_trans RSEGS _ (fun r => mkst r (0xb8368 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s j /\ getr r 11 = at_ s (j - 1)
                         /\ sl_agree regs r)).
      + eexists. split.
        * mld F_b64bc D_b64bc j.
          stepn F_b64c0 D_b64c0.
          stepn F_b64c4 D_b64c4.
          stepn F_b64c8 D_b64c8.
          stepn F_b64cc D_b64cc.
          stepn F_b64d0 D_b64d0.
          stepb_ft F_b64d4 D_b64d4 ltac:(condw tw_hit).
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R12 & R11 & KC).
        destruct (t_loop (Z.to_nat (K - j)) r1 ret j Hret R1 R10 R12 R11 ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
    -
      assert (HKj : (j + 8 <= K)%Z).
      { clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
      eapply (runs_trans RSEGS _ (fun r => mkst r (0xb834c : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (j + 8 - 8) /\ getr r 11 = at_ s (j + 8 - 9)
                         /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc /\ sl_agree regs r)).
      + eexists. split.
        * mld F_b64bc D_b64bc j.
          stepn F_b64c0 D_b64c0.
          stepn F_b64c4 D_b64c4.
          stepn F_b64c8 D_b64c8.
          stepn F_b64cc D_b64cc.
          stepn F_b64d0 D_b64d0.
          stepb_tk F_b64d4 D_b64d4 ltac:(condw tw_miss).
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R12 & R11 & R13 & R14 & KC).
        destruct (IH r1 ret (j + 8)%Z Hret R1 R10 R12 R11 R13 R14 ltac:(lia)
                    ltac:(rewrite Z.add_assoc, <- Zplus_mod_idemp_l, Hal; reflexivity)
                    ltac:(clear -Hi HKj; pose proof (Z.div_mod (K - j) 8 ltac:(lia));
                          pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia));
                          pose proof (Z.div_mod (K - (j + 8)) 8 ltac:(lia));
                          pose proof (Z.mod_pos_bound (K - (j + 8)) 8 ltac:(lia)); nia))
          as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
  Qed.

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

  Lemma a_entry : forall regs (ret : word) j,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s -> getr regs 12 = at_ s j ->
    (0 <= j <= K)%Z -> ((bv_unsigned s + j) mod 8 = 0)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0xb8334 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ sl_agree regs regs'.
  Proof.
    intros regs ret j Hret H1 H10 H12 Hj Hal.
    pose proof KL as HKL. pose proof (u64_range s) as Hs.
    destruct (rd_const_M mem Hro) as (bsM & RM & EM).
    destruct (rd_const_H mem Hro) as (bsH & RH & EH).
    eapply (runs_trans RSEGS _ (fun r => mkst r (0xb834c : word) mem rom)
             (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (j - 8) /\ getr r 11 = at_ s (j - 9)
                       /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc /\ sl_agree regs r)).
    - eexists. split.
      + stepn F_b64a4 D_b64a4.
        stepn F_b64a8 D_b64a8.
        ldc F_b64ac D_b64ac (Z_to_bv 64 Mc) RM.
        ldc F_b64b0 D_b64b0 (Z_to_bv 64 Hc) RH.
        stepn F_b64b4 D_b64b4.
        stepn F_b64b8 D_b64b8.
        apply mst_refl.
      + post.
    - cbv beta. intros r1 (R1 & R10 & R12 & R11 & R13 & R14 & KC).
      destruct (w_loop (Z.to_nat ((K - j) / 8)) r1 ret j Hret R1 R10 R12 R11 R13 R14 Hj Hal
                  ltac:(clear -Hj; pose proof (Z.div_pos (K - j) 8); lia)) as (r2 & RUN & A10 & K2).
      exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
  Qed.

  Lemma h_loop : forall (i : nat) regs (ret : word) j,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s -> getr regs 11 = at_ s j -> getr regs 12 = at_ s (j + 1) ->
    (0 <= j < K)%Z ->
    (((bv_unsigned s + j + 1) mod 8 <> 0 /\ Z.of_nat i + (bv_unsigned s + j + 1) mod 8 = 8)
     \/ (i = 0%nat /\ (bv_unsigned s + j + 1) mod 8 = 0))%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0xb8314 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ sl_agree regs regs'.
  Proof.
    pose proof KL as HKL. pose proof (u64_range s) as Hs.
    induction i as [|i IH]; intros regs ret j Hret H1 H10 H11 H12 Hj Hi;
      pose proof (Z.mod_pos_bound (bv_unsigned s + j + 1) 8 ltac:(lia)) as HM1.
    -
      assert (Hal : ((bv_unsigned s + j + 1) mod 8 = 0)%Z) by (clear -Hi HM1; lia).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0xb8334 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (j + 1) /\ sl_agree regs r)).
      + eexists. split.
        * stepn F_b6484 D_b6484.
          stepn F_b6488 D_b6488.
          stepb_tk F_b648c D_b648c
            ltac:(rwH; rewrite ?at_addi; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_eq;
                  rewrite Z.add_assoc; exact Hal).
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R12 & KC).
        destruct (a_entry r1 ret (j + 1)%Z Hret R1 R10 R12 ltac:(lia) ltac:(rewrite Z.add_assoc; exact Hal))
          as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
    -
      assert (Hna : ((bv_unsigned s + j + 1) mod 8 = 7 - Z.of_nat i)%Z /\ ((bv_unsigned s + j + 1) mod 8 <> 0)%Z) by (clear -Hi; lia).
      destruct Hna as [Hna Hnz0].
      destruct (Z.eq_dec (j + 1) K) as [HjK|HjK].
      +
        eexists. split.
        * stepn F_b6484 D_b6484.
          stepn F_b6488 D_b6488.
          stepb_ft F_b648c D_b648c
            ltac:(rwH; rewrite ?at_addi; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
                  rewrite Z.add_assoc; lia).
          mlbu F_b6490 D_b6490 (j + 1)%Z.
          stepn F_b6494 D_b6494.
          stepn F_b6498 D_b6498.
          stepb_ft F_b649c D_b649c ltac:(condb).
          stepn F_b64a0 D_b64a0.
          stepiv F_b64e8 D_b64e8 (Z_to_bv 64 K)
            ltac:(gres; rwH; rewrite ?at_addi; rewrite HjK; apply v_sub_at; lia).
          stepret F_b64ec D_b64ec ret ltac:(rwH; reflexivity).
          apply mst_refl.
        * post.
      +
        eapply (runs_trans RSEGS _ (fun r => mkst r (0xb8314 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = at_ s (j + 1) /\ getr r 12 = at_ s (j + 1 + 1)
                           /\ sl_agree regs r)).
        * eexists. split.
          -- stepn F_b6484 D_b6484.
             stepn F_b6488 D_b6488.
             stepb_ft F_b648c D_b648c
               ltac:(rwH; rewrite ?at_addi; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
                     rewrite Z.add_assoc; lia).
             mlbu F_b6490 D_b6490 (j + 1)%Z.
             stepn F_b6494 D_b6494.
             stepn F_b6498 D_b6498.
             stepb_tk F_b649c D_b649c ltac:(condb).
             apply mst_refl.
          -- post.
        * cbv beta. intros r1 (R1 & R10 & R11 & R12 & KC).
          assert (HM : ((bv_unsigned s + (j + 1) + 1) mod 8 = ((bv_unsigned s + j + 1) mod 8 + 1) mod 8)%Z).
          { clear -Hs Hj. replace (bv_unsigned s + (j + 1) + 1)%Z with (bv_unsigned s + j + 1 + 1)%Z by lia.
            rewrite <- (Zplus_mod_idemp_l (bv_unsigned s + j + 1)). reflexivity. }
          destruct (IH r1 ret (j + 1)%Z Hret R1 R10 R11 R12 ltac:(lia)) as (r2 & RUN & A10 & K2).
          { rewrite HM, Hna. clear -Hna Hnz0 HM1. destruct i as [|i].
            - right. split; [reflexivity|]. reflexivity.
            - left. rewrite Z.mod_small by lia. lia. }
          exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
  Qed.

  Lemma strlen_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s ->
    exists regs',
      msteps RSEGS (mkst regs (0xb82f8 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ sl_agree regs regs'.
  Proof.
    intros regs ret Hret H1 H10.
    pose proof KL as HKL. pose proof (u64_range s) as Hs.
    pose proof (Z.mod_pos_bound (bv_unsigned s) 8 ltac:(lia)) as HM.

    assert (E0 : exists j0 : Z, j0 = 0%Z) by (exists 0%Z; reflexivity). destruct E0 as [j0 Hj0].
    rewrite <- (at_0 s), <- Hj0 in H10.
    destruct (Z.eq_dec (bv_unsigned s mod 8) 0) as [Hal|Hal].
    -
      eapply (runs_trans RSEGS _ (fun r => mkst r (0xb8334 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s 0 /\ sl_agree regs r)).
      + eexists. split.
        * stepn F_b6468 D_b6468.
          stepn F_b646c D_b646c.
          stepb_tk F_b6470 D_b6470
            ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_eq;
                  rewrite Hj0, Z.add_0_r; exact Hal).
          apply mst_refl.
        * post; rewrite ?Hj0, ?at_0; reflexivity.
      + cbv beta. intros r1 (R1 & R10 & R12 & KC).
        destruct (a_entry r1 ret 0 Hret R1 R10 R12 ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hal))
          as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
    - destruct (Z.eq_dec K 0) as [HK|HK].
      +
        eexists. split.
        * stepn F_b6468 D_b6468.
          stepn F_b646c D_b646c.
          stepb_ft F_b6470 D_b6470
            ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
                  rewrite Hj0, Z.add_0_r; exact Hal).
          mlbu F_b6474 D_b6474 j0.
          stepb_tk F_b6478 D_b6478 ltac:(condb).
          stepiv F_b64f0 D_b64f0 (Z_to_bv 64 K)
            ltac:(gres; rwH; rewrite HK; apply v_sub_self).
          stepret F_b64f4 D_b64f4 ret ltac:(rwH; reflexivity).
          apply mst_refl.
        * post; rewrite ?Hj0, ?at_0; reflexivity.
      +
        eapply (runs_trans RSEGS _ (fun r => mkst r (0xb8314 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = at_ s 0 /\ getr r 12 = at_ s (0 + 1)
                           /\ sl_agree regs r)).
        * eexists. split.
          -- stepn F_b6468 D_b6468.
             stepn F_b646c D_b646c.
             stepb_ft F_b6470 D_b6470
               ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
                     rewrite Hj0, Z.add_0_r; exact Hal).
             mlbu F_b6474 D_b6474 j0.
             stepb_ft F_b6478 D_b6478 ltac:(condb).
             stepn F_b647c D_b647c.
             stepn F_b6480 D_b6480.
             apply mst_refl.
          -- post; rewrite ?Hj0, ?at_0; reflexivity.
        * cbv beta. intros r1 (R1 & R10 & R11 & R12 & KC).
          pose proof (Z.mod_pos_bound (bv_unsigned s + 1) 8 ltac:(lia)) as HM1.
          destruct (h_loop (Z.to_nat ((8 - (bv_unsigned s + 1) mod 8) mod 8)) r1 ret 0 Hret R1 R10 R11 R12 ltac:(lia))
            as (r2 & RUN & A10 & K2).
          { rewrite Z.add_0_r.
            destruct (Z.eq_dec ((bv_unsigned s + 1) mod 8) 0) as [Hz|Hz].
            - right. rewrite Hz. split; [reflexivity | reflexivity].
            - left. split; [exact Hz|]. rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). rewrite Z.mod_small by lia. lia. }
          exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
  Qed.

End SLEN.

Theorem ref_strlen : forall mem (s : word) buf K rom regs (ret : word),
  slenH mem s buf K ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s ->
  exists regs',
    msteps RSEGS (mkst regs (0xb82f8 : word) mem rom) (mkst regs' ret mem rom)
    /\ sl_agree regs regs'
    /\ getr regs' 10 = Z_to_bv 64 K.
Proof.
  intros mem s buf K rom regs ret HOK Hret H1 H10.
  destruct (strlen_run mem s buf K rom HOK regs ret Hret H1 H10) as (r & RUN & A10 & KC).
  exists r. split; [exact RUN | split; [exact KC | exact A10]].
Qed.

End FPX_1.
