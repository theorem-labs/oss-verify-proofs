(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim MuslStrlen
  RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.muslA Require Import Ba0MemcpyBase_b Ba0Memchr_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_rcb2e4_cbd08_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition TWs (x : word) : word := v_and (v_or (v_sub (Z_to_bv 64 Mc) x) x) (Z_to_bv 64 Hc).

Lemma TWs_TW : forall x, TWs x = TW x.
Proof. intros x. unfold TWs, TW. rewrite !v_xor_0. reflexivity. Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record slenH (mem : word -> option byte) (s : word) (buf : list byte) (K : Z) : Prop := SLENH {
  (* [comment removed for export] *)
  Hbuf : rdn RSEGS mem s (length buf) = Some buf;
  (* [comment removed for export] *)
  Hwin : ((bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf))%Z;
  Hnw  : (bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64)%Z;
  (* [comment removed for export] *)
  HK0  : (0 <= K)%Z;
  Hzero : bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0%Z;
  Hnz  : forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0%Z;
  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Lemma al_room : forall j, ((bv_unsigned s + j) mod 8 = 0)%Z -> (0 <= j <= K)%Z -> (j + 8 <= KE)%Z.
  Proof.
    intros j Hal Hj. unfold KE. clear -Hal Hj HK0. pose proof (u64_range s).
    pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.div_mod (bv_unsigned s + j) 8 ltac:(lia)).
    assert ((bv_unsigned s + j) / 8 <= (bv_unsigned s + K) / 8)%Z by (apply Z.div_le_mono; lia).
    lia.
  Qed.

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

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

  (* [comment removed for export] *)
  Ltac condb :=
    rwH; rewrite ?getr_zero; rewrite c_eq_LBv_0;
    first [ apply Z.eqb_eq; rewrite <- bz; f_equal; f_equal; lia
          | apply Z.eqb_neq; apply bnz; lia ].
  (* [comment removed for export] *)
  Ltac cond := try unfold v_addi; cond_lia.
  (* [comment removed for export] *)
  Ltac condw lem :=
    rwH;
    lazymatch goal with |- c_eq (v_and (v_or (v_sub _ ?x) _) _) _ = ?b =>
      change (c_eq (TWs x) (Z_to_bv 64 Hc) = b) end;
    apply lem; lia.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (rewrite ?at_0; reflexivity);
               try (f_equal; lia); try (unfold v_addi; unorm; f_equal; lia); try solve_sl_agree.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_loop : forall (i : nat) regs (ret : word) j,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s -> getr regs 12 = at_ s j -> getr regs 11 = at_ s (j - 1) ->
    (0 <= j <= K)%Z -> (Z.of_nat i = K - j)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x12a258 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ sl_agree regs regs'.
  Proof.
    pose proof KL as HKL. pose proof (u64_range s) as Hs.
    induction i as [|i IH]; intros regs ret j Hret H1 H10 H12 H11 Hj Hi.
    - (* [comment removed for export] *)
      eexists. split.
      + mlbu F_127c68 D_127c68 j.                     (* [comment removed for export] *)
        stepn F_127c6c D_127c6c.                      (* [comment removed for export] *)
        stepn F_127c70 D_127c70.                      (* [comment removed for export] *)
        stepb_ft F_127c74 D_127c74 ltac:(condb).      (* [comment removed for export] *)
        stepiv F_127c78 D_127c78 (Z_to_bv 64 K)
          ltac:(gres; rwH; rewrite ?at_addi; replace (j - 1 + 1)%Z with K by lia; apply v_sub_at; lia).  (* [comment removed for export] *)
        stepret F_127c7c D_127c7c ret ltac:(rwH; reflexivity).
        apply mst_refl.
      + post.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x12a258 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (j + 1) /\ getr r 11 = at_ s (j + 1 - 1)
                         /\ sl_agree regs r)).
      + eexists. split.
        * mlbu F_127c68 D_127c68 j.                   (* [comment removed for export] *)
          stepn F_127c6c D_127c6c.                    (* [comment removed for export] *)
          stepn F_127c70 D_127c70.                    (* [comment removed for export] *)
          stepb_tk F_127c74 D_127c74 ltac:(condb).    (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R12 & R11 & KC).
        destruct (IH r1 ret (j + 1)%Z Hret R1 R10 R12 R11 ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma w_loop : forall (i : nat) regs (ret : word) j,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s -> getr regs 12 = at_ s (j - 8) -> getr regs 11 = at_ s (j - 9) ->
    getr regs 13 = Z_to_bv 64 Mc -> getr regs 14 = Z_to_bv 64 Hc ->
    (0 <= j <= K)%Z -> ((bv_unsigned s + j) mod 8 = 0)%Z -> (Z.of_nat i = (K - j) / 8)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x12a23c : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ sl_agree regs regs'.
  Proof.
    pose proof KL as HKL. pose proof KE_facts as (HKE1 & HKE2 & HKE3). pose proof (u64_range s) as Hs.
    induction i as [|i IH]; intros regs ret j Hret H1 H10 H12 H11 H13 H14 Hj Hal Hi;
      pose proof (al_room j Hal Hj) as HR.
    - (* [comment removed for export] *)
      assert (HKj : (K < j + 8)%Z).
      { clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x12a258 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s j /\ getr r 11 = at_ s (j - 1)
                         /\ sl_agree regs r)).
      + eexists. split.
        * mld F_127c4c D_127c4c j.                    (* [comment removed for export] *)
          stepn F_127c50 D_127c50.                    (* [comment removed for export] *)
          stepn F_127c54 D_127c54.                    (* [comment removed for export] *)
          stepn F_127c58 D_127c58.                    (* [comment removed for export] *)
          stepn F_127c5c D_127c5c.                    (* [comment removed for export] *)
          stepn F_127c60 D_127c60.                    (* [comment removed for export] *)
          stepb_ft F_127c64 D_127c64 ltac:(condw tw_hit).   (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R12 & R11 & KC).
        destruct (t_loop (Z.to_nat (K - j)) r1 ret j Hret R1 R10 R12 R11 ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
    - (* [comment removed for export] *)
      assert (HKj : (j + 8 <= K)%Z).
      { clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x12a23c : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (j + 8 - 8) /\ getr r 11 = at_ s (j + 8 - 9)
                         /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc /\ sl_agree regs r)).
      + eexists. split.
        * mld F_127c4c D_127c4c j.
          stepn F_127c50 D_127c50.
          stepn F_127c54 D_127c54.
          stepn F_127c58 D_127c58.
          stepn F_127c5c D_127c5c.
          stepn F_127c60 D_127c60.
          stepb_tk F_127c64 D_127c64 ltac:(condw tw_miss).  (* [comment removed for export] *)
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

  Lemma a_entry : forall regs (ret : word) j,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s -> getr regs 12 = at_ s j ->
    (0 <= j <= K)%Z -> ((bv_unsigned s + j) mod 8 = 0)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x12a224 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ sl_agree regs regs'.
  Proof.
    intros regs ret j Hret H1 H10 H12 Hj Hal.
    pose proof KL as HKL. pose proof (u64_range s) as Hs.
    destruct (rd_const_M mem Hro) as (bsM & RM & EM).
    destruct (rd_const_H mem Hro) as (bsH & RH & EH).
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x12a23c : word) mem rom)
             (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (j - 8) /\ getr r 11 = at_ s (j - 9)
                       /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc /\ sl_agree regs r)).
    - eexists. split.
      + stepn F_127c34 D_127c34.                      (* [comment removed for export] *)
        stepn F_127c38 D_127c38.                      (* [comment removed for export] *)
        ldc F_127c3c D_127c3c (Z_to_bv 64 Mc) RM.     (* [comment removed for export] *)
        ldc F_127c40 D_127c40 (Z_to_bv 64 Hc) RH.     (* [comment removed for export] *)
        stepn F_127c44 D_127c44.                      (* [comment removed for export] *)
        stepn F_127c48 D_127c48.                      (* [comment removed for export] *)
        apply mst_refl.
      + post.
    - cbv beta. intros r1 (R1 & R10 & R12 & R11 & R13 & R14 & KC).
      destruct (w_loop (Z.to_nat ((K - j) / 8)) r1 ret j Hret R1 R10 R12 R11 R13 R14 Hj Hal
                  ltac:(clear -Hj; pose proof (Z.div_pos (K - j) 8); lia)) as (r2 & RUN & A10 & K2).
      exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma h_loop : forall (i : nat) regs (ret : word) j,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s -> getr regs 11 = at_ s j -> getr regs 12 = at_ s (j + 1) ->
    (0 <= j < K)%Z ->
    (((bv_unsigned s + j + 1) mod 8 <> 0 /\ Z.of_nat i + (bv_unsigned s + j + 1) mod 8 = 8)
     \/ (i = 0%nat /\ (bv_unsigned s + j + 1) mod 8 = 0))%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x12a204 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ sl_agree regs regs'.
  Proof.
    pose proof KL as HKL. pose proof (u64_range s) as Hs.
    induction i as [|i IH]; intros regs ret j Hret H1 H10 H11 H12 Hj Hi;
      pose proof (Z.mod_pos_bound (bv_unsigned s + j + 1) 8 ltac:(lia)) as HM1.
    - (* [comment removed for export] *)
      assert (Hal : ((bv_unsigned s + j + 1) mod 8 = 0)%Z) by (clear -Hi HM1; lia).
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x12a224 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (j + 1) /\ sl_agree regs r)).
      + eexists. split.
        * stepn F_127c14 D_127c14.                    (* [comment removed for export] *)
          stepn F_127c18 D_127c18.                    (* [comment removed for export] *)
          stepb_tk F_127c1c D_127c1c
            ltac:(rwH; rewrite ?at_addi; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_eq;
                  rewrite Z.add_assoc; exact Hal).  (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R12 & KC).
        destruct (a_entry r1 ret (j + 1)%Z Hret R1 R10 R12 ltac:(lia) ltac:(rewrite Z.add_assoc; exact Hal))
          as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
    - (* [comment removed for export] *)
      assert (Hna : ((bv_unsigned s + j + 1) mod 8 = 7 - Z.of_nat i)%Z /\ ((bv_unsigned s + j + 1) mod 8 <> 0)%Z) by (clear -Hi; lia).
      destruct Hna as [Hna Hnz0].
      destruct (Z.eq_dec (j + 1) K) as [HjK|HjK].
      + (* [comment removed for export] *)
        eexists. split.
        * stepn F_127c14 D_127c14.                    (* [comment removed for export] *)
          stepn F_127c18 D_127c18.                    (* [comment removed for export] *)
          stepb_ft F_127c1c D_127c1c
            ltac:(rwH; rewrite ?at_addi; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
                  rewrite Z.add_assoc; lia).        (* [comment removed for export] *)
          mlbu F_127c20 D_127c20 (j + 1)%Z.           (* [comment removed for export] *)
          stepn F_127c24 D_127c24.                    (* [comment removed for export] *)
          stepn F_127c28 D_127c28.                    (* [comment removed for export] *)
          stepb_ft F_127c2c D_127c2c ltac:(condb).    (* [comment removed for export] *)
          stepn F_127c30 D_127c30.                    (* [comment removed for export] *)
          stepiv F_127c78 D_127c78 (Z_to_bv 64 K)
            ltac:(gres; rwH; rewrite ?at_addi; rewrite HjK; apply v_sub_at; lia).  (* [comment removed for export] *)
          stepret F_127c7c D_127c7c ret ltac:(rwH; reflexivity).
          apply mst_refl.
        * post.
      + (* [comment removed for export] *)
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x12a204 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = at_ s (j + 1) /\ getr r 12 = at_ s (j + 1 + 1)
                           /\ sl_agree regs r)).
        * eexists. split.
          -- stepn F_127c14 D_127c14.                 (* [comment removed for export] *)
             stepn F_127c18 D_127c18.                 (* [comment removed for export] *)
             stepb_ft F_127c1c D_127c1c
               ltac:(rwH; rewrite ?at_addi; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
                     rewrite Z.add_assoc; lia).     (* [comment removed for export] *)
             mlbu F_127c20 D_127c20 (j + 1)%Z.        (* [comment removed for export] *)
             stepn F_127c24 D_127c24.                 (* [comment removed for export] *)
             stepn F_127c28 D_127c28.                 (* [comment removed for export] *)
             stepb_tk F_127c2c D_127c2c ltac:(condb). (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma strlen_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s ->
    exists regs',
      msteps RSEGS (mkst regs (0x12a1e8 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ sl_agree regs regs'.
  Proof.
    intros regs ret Hret H1 H10.
    pose proof KL as HKL. pose proof (u64_range s) as Hs.
    pose proof (Z.mod_pos_bound (bv_unsigned s) 8 ltac:(lia)) as HM.
    (* [comment removed for export] *)
    assert (E0 : exists j0 : Z, j0 = 0%Z) by (exists 0%Z; reflexivity). destruct E0 as [j0 Hj0].
    rewrite <- (at_0 s), <- Hj0 in H10.
    destruct (Z.eq_dec (bv_unsigned s mod 8) 0) as [Hal|Hal].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x12a224 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s 0 /\ sl_agree regs r)).
      + eexists. split.
        * stepn F_127bf8 D_127bf8.                    (* [comment removed for export] *)
          stepn F_127bfc D_127bfc.                    (* [comment removed for export] *)
          stepb_tk F_127c00 D_127c00
            ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_eq;
                  rewrite Hj0, Z.add_0_r; exact Hal).    (* [comment removed for export] *)
          apply mst_refl.
        * post; rewrite ?Hj0, ?at_0; reflexivity.
      + cbv beta. intros r1 (R1 & R10 & R12 & KC).
        destruct (a_entry r1 ret 0 Hret R1 R10 R12 ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hal))
          as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply sl_agree_trans; eassumption]].
    - destruct (Z.eq_dec K 0) as [HK|HK].
      + (* [comment removed for export] *)
        eexists. split.
        * stepn F_127bf8 D_127bf8.                    (* [comment removed for export] *)
          stepn F_127bfc D_127bfc.                    (* [comment removed for export] *)
          stepb_ft F_127c00 D_127c00
            ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
                  rewrite Hj0, Z.add_0_r; exact Hal).    (* [comment removed for export] *)
          mlbu F_127c04 D_127c04 j0.                  (* [comment removed for export] *)
          stepb_tk F_127c08 D_127c08 ltac:(condb).    (* [comment removed for export] *)
          stepiv F_127c80 D_127c80 (Z_to_bv 64 K)
            ltac:(gres; rwH; rewrite HK; apply v_sub_self).  (* [comment removed for export] *)
          stepret F_127c84 D_127c84 ret ltac:(rwH; reflexivity).
          apply mst_refl.
        * post; rewrite ?Hj0, ?at_0; reflexivity.
      + (* [comment removed for export] *)
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x12a204 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = at_ s 0 /\ getr r 12 = at_ s (0 + 1)
                           /\ sl_agree regs r)).
        * eexists. split.
          -- stepn F_127bf8 D_127bf8.                 (* [comment removed for export] *)
             stepn F_127bfc D_127bfc.                 (* [comment removed for export] *)
             stepb_ft F_127c00 D_127c00
               ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
                     rewrite Hj0, Z.add_0_r; exact Hal). (* [comment removed for export] *)
             mlbu F_127c04 D_127c04 j0.               (* [comment removed for export] *)
             stepb_ft F_127c08 D_127c08 ltac:(condb). (* [comment removed for export] *)
             stepn F_127c0c D_127c0c.                 (* [comment removed for export] *)
             stepn F_127c10 D_127c10.                 (* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem ref_strlen : forall mem (s : word) buf K rom regs (ret : word),
  slenH mem s buf K ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s ->
  exists regs',
    msteps RSEGS (mkst regs (0x12a1e8 : word) mem rom) (mkst regs' ret mem rom)
    /\ sl_agree regs regs'
    /\ getr regs' 10 = Z_to_bv 64 K.
Proof.
  intros mem s buf K rom regs ret HOK Hret H1 H10.
  destruct (strlen_run mem s buf K rom HOK regs ret Hret H1 H10) as (r & RUN & A10 & KC).
  exists r. split; [exact RUN | split; [exact KC | exact A10]].
Qed.

End FPX_1.
