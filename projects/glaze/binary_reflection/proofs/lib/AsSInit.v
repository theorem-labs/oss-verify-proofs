(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanPlacement OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzSymStepR AzSymExec3 AzSymExec3B AzSymExec3Sound AzSymRun3 AzPlanCore AzPlan AzAPS AzGPS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsSDefs.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require PuLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
#[local] Ltac lia ::= PuLia.lia_nd.
#[local] Ltac nia ::= PuLia.znia_nd.
Import ListNotations.
Import AX2. Import AX2B. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).


(* [comment removed for export] *)
Record img_facts (segs : list Segment) (A : atable) (ph : PhdrInfo) : Prop := IMG_FACTS {
  if_ph    : ph_addr_z A = Z.of_N (ph_addr ph) /\ ph_ent_z A = Z.of_N (ph_ent ph) /\ ph_num_z A = Z.of_N (ph_num ph);
  if_hull  : 0 <= img_lo A <= img_hi A /\ img_hi A <= 2 ^ 32 /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0;
  if_top   : reserved_top (segments_reserved segs) = img_hi A;
  if_res   : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                    (segments_reserved segs);
  if_sizes : sum_sizes (segments_reserved segs) = img_hi A - img_lo A;
  if_rw    : (0 <= rw_lo A /\ 0 <= rw_len A /\ rw_lo A + rw_len A < 2 ^ 64)
             /\ forall m (x : word), rw_lo A <= bv_unsigned x < rw_lo A + rw_len A -> wview segs m x <> None;
  if_shadow : 0 <= shadow_off A <= 2 ^ 47
}.

(* [comment removed for export] *)
Definition stack_image_size (argv envp : list (list byte)) : Z :=
  let struct_size := (8 + (Z.of_nat (length argv) + 1) * 8
                      + (Z.of_nat (length envp) + 1) * 8 + 160)%Z in
  let len := (struct_size + total_arg_bytes argv + total_arg_bytes envp)%Z in
  (len + ((8 - len mod 8) mod 8) + 16)%Z.

Section Init.
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  (* [comment removed for export] *)
  Variable uid gid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  (* [comment removed for export] *)
  Variable nofile sigmask : word.
  Variable abort : bool.
  Variable va : VaSize.
  (* [comment removed for export] *)
  Variable urnd : InputStream.

  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* [comment removed for export] *)
  Hypothesis Huid : valid_id uid.
  (* [comment removed for export] *)
  Hypothesis Hhw : valid_hwcap hw.

  Definition inp : ProcInput := mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw abort va urnd [].  (* [comment removed for export] *)  (* [comment removed for export] *)
  Let bsb := build_stack_bytes ph sp argv envp uid hw rdraw.
  Let SIMG := entry_stack_image ph sp argv envp uid hw rdraw.   (* [comment removed for export] *)
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let L0 := Z.of_nat (length (nth 0 argv [])).
  Let L1 := Z.of_nat (length (nth 1 argv [])).
  (* [comment removed for export] *)
  Let W := (Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184)) / 8.

  (* [comment removed for export] *)
  Let TV := (usp - 160 + 4095) / 4096 - 8 * (usp / 32768).
  Let PV := usp / 4096 - 8 * (usp / 32768).
  (* [comment removed for export] *)
  Let BV := (usp + Z.of_nat (length bsb) + 63) / 64.
  Let R8V := (64 * BV - (usp + Z.of_nat (length bsb))) / 8.

  Definition vals0 : list word :=
    [Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
     Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 32768) / 16); Z_to_bv 64 L1; uid;
     hw; Z_to_bv 64 TV; Z_to_bv 64 PV; Z_to_bv 64 R8V].
  (* [comment removed for export] *)
  Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0)) (fun _ => []).

  (* [comment removed for export] *)
  Definition argH0 (E : env) (a : word) : bool :=
    let z := bv_unsigned a in
    ((uE E e_sp0 =? usp) &&
     (((usp + 8 * argc + 16 <=? z) && (z <? usp + 8 * argc + 8 * envc + 24))
      || ((usp + 8 * argc + 8 * envc + 184 <=? z) && (z <? usp + 8 * argc + 8 * envc + 184 + 8 * W))))%bool.

  Definition SINV0 (E : env) (M : word -> option byte) : Prop :=
    (forall n, (n < NXS)%nat -> ev E n = ev E0 n)
    /\ (forall a, argH0 E a = true -> M a = wrap_mem ph sp argv envp uid hw rdraw a).

  (* [comment removed for export] *)
  Lemma argH0_high : forall E a, argH0 E a = true -> sp_window_lo <= bv_unsigned a /\ bv_unsigned (edenot E ISP_S) <= bv_unsigned a.
  Proof.
    intros E a H. unfold argH0 in H. destruct Hsp as [Hlo _].
    pose proof (valid_argv_len argv Hva).
    apply andb_prop in H as [He H]. apply Z.eqb_eq in He. unfold ISP_S. unfold uE in He. rewrite He.
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H; unfold usp, argc, envc in H |- *; lia.
  Qed.

  Lemma e_sp0_vars : expr_vars_lt NXS e_sp0 = true.
  Proof. reflexivity. Qed.

  Lemma argH0_agree : forall E E' a, env_agree NXS E E' -> argH0 E a = argH0 E' a.
  Proof.
    intros E E' a Hag. unfold argH0, uE. rewrite (edenot_agree NXS E E' e_sp0 Hag e_sp0_vars). reflexivity.
  Qed.

  Lemma SINV0_frame : forall E M M', (forall a, argH0 E a = true -> M' a = M a) -> SINV0 E M -> SINV0 E M'.
  Proof. intros E M M' Hf [H1 H2]. split; [exact H1|]. intros a Ha. rewrite (Hf a Ha). apply H2. exact Ha. Qed.

  Lemma SINV0_agree : forall E E' M, env_agree NXS E E' -> SINV0 E M -> SINV0 E' M.
  Proof.
    intros E E' M Hag0 [H1 H2]. pose proof Hag0 as [Hag _]. split.
    - intros n Hn. rewrite <- (Hag n) by (unfold NXS in *; lia). apply H1. exact Hn.
    - intros a Ha. apply H2. rewrite (argH0_agree E E' a Hag0). exact Ha.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma Hlo' : (sp_window_lo <= bv_unsigned sp)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hhi' : (bv_unsigned sp <= sp_window_hi)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.

  Lemma Hav0 : (0 < length argv)%nat. Proof. destruct Hva as [[? ?] _]; lia. Qed.

  Lemma len_av : 1 <= argc <= 1024.
  Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  Lemma len_ev : 0 <= envc <= 256.
  Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
  Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. unfold usp. destruct Hsp as [H _]. exact H. Qed.
  Lemma usp_al : usp mod 16 = 0.
  Proof. unfold usp. destruct Hsp as (_ & _ & H). exact H. Qed.

  (* [comment removed for export] *)
  Lemma length_bsb_eq : Z.of_nat (length bsb) = stack_image_size argv envp.
  Proof.
    unfold bsb, build_stack_bytes, stack_image_size. cbv zeta.
    rewrite (string_addrs_pair argv). cbv beta iota.
    rewrite (string_addrs_pair envp). cbv beta iota.
    rewrite !length_app, length_at_random_bytes, repeat_length, !length_flat_map_le8,
      !length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
      !length_flatten_strings.
    rewrite !total_arg_bytes_Z. unfold auxv_size.
    rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
    match goal with
    | |- context [Z.to_nat ?pd] =>
        assert (Hpd : (0 <= pd < 8)%Z) by (apply Z.mod_pos_bound; lia); rewrite (Z2Nat.id pd) by lia
    end.
    lia.
  Qed.

  Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
  Proof.
    pose proof (build_stack_bytes_within_span ph sp argv envp uid hw rdraw) as B. fold bsb in B.
    unfold entry_stack_fits, sp_window_hi in Hfit. unfold usp. lia.
  Qed.

  Lemma bsb_ge : 8 * argc + 8 * envc + 200 <= Z.of_nat (length bsb) /\ (Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184)) mod 8 = 0.
  Proof.
    rewrite length_bsb_eq. unfold stack_image_size, argc, envc. cbv zeta.
    pose proof (total_arg_bytes_Z argv). pose proof (total_arg_bytes_Z envp).
    match goal with |- context [((8 - ?l mod 8) mod 8)%Z] => set (len := l) end.
    assert (0 <= Z.of_nat (total_arg_bytes_nat argv)) by lia.
    split; [lia|].
    assert (Hpd : 0 <= (8 - len mod 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (Hm : (len + (8 - len mod 8) mod 8) mod 8 = 0).
    { rewrite <- Zplus_mod_idemp_l. rewrite Zplus_mod_idemp_r.
      replace (len mod 8 + (8 - len mod 8)) with 8 by lia. reflexivity. }
    replace (len + (8 - len mod 8) mod 8 + 16 - 16 - (8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184))
      with (len + (8 - len mod 8) mod 8 - 8 * (Z.of_nat (length argv) + Z.of_nat (length envp) + 23)) by (unfold len; lia).
    rewrite Zminus_mod, Hm, Z.mul_comm, Z_mod_mult. reflexivity.
  Qed.

  Lemma W_range : 0 <= W /\ 8 * W = Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184) /\ W <= 280000.
  Proof.
    pose proof bsb_ge as [G M]. pose proof (bsb_bound ph sp argv envp uid hw rdraw Hva Hve) as B. fold bsb in B.
    unfold W. pose proof len_av. pose proof len_ev.
    lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma brk_range : img_hi A <= bv_unsigned brk0 <= img_hi A + BRK_ASLR /\ bv_unsigned brk0 mod 4096 = 0.
  Proof.
    destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
    rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
  Qed.

  Lemma usp_hi : usp + 208 <= 2 ^ 47.
  Proof. pose proof usp_fit. pose proof bsb_ge as [G _]. pose proof len_av. pose proof len_ev. lia. Qed.


  (* [comment removed for export] *)
  Lemma uE0 :
    uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 32768) / 16
    /\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
    /\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    pose proof (u64_range brk0) as [B1 B2].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva ltac:(destruct Hva as [Hl _]; lia)). lia. }
    unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK].
    rewrite !u64_lit by lia. repeat split; reflexivity.
  Qed.

  Lemma L1_range : 0 <= L1 <= 131071.
  Proof.
    unfold L1. destruct (Nat.lt_ge_cases 1 (length argv)) as [Hl|Hl].
    - pose proof (valid_argv_str_len argv 1 Hva Hl). lia.
    - rewrite nth_overflow by lia. cbn. lia.
  Qed.

  Lemma uE0_L1 : uE E0 (EVar V_L1) = L1.
  Proof. pose proof L1_range. unfold uE. cbn [edenot E0 ev nth vals0 V_L1]. rewrite u64_lit by lia. reflexivity. Qed.


  Lemma uE0_uid : uE E0 (EVar V_UID) = bv_unsigned uid.
  Proof. reflexivity. Qed.

  Lemma u_e_sp0 : uE E0 e_sp0 = usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _).
    unfold e_sp0, eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma edenot_e_sp0 : edenot E0 e_sp0 = sp.
  Proof. apply bv_eq. exact u_e_sp0. Qed.

  Lemma u_sp8 : uE E0 (eadd (escale 4096 (EVar V_S1)) (escale 2 (EVar V_S2))) = usp / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _).
    unfold eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_envp : uE E0 e_envp = usp + 8 * argc + 16.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. destruct uE0 as (_ & _ & U3 & _).
    pose proof u_e_sp0 as US. unfold e_envp, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite US, U3.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_auxv : uE E0 e_auxv = usp + 8 * argc + 8 * envc + 24.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. destruct uE0 as (_ & _ & _ & U4 & _).
    pose proof u_e_envp as UE. unfold e_auxv, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UE, U4.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str0 : uE E0 e_str0 = usp + 8 * argc + 8 * envc + 184.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
    pose proof u_e_auxv as UA. unfold e_str0, AUXV_SIZE, eaddz, uE in *. rewrite mkAlu_denot, edenot_lit.
    rewrite u_add64, u64_lit by lia. rewrite UA. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_str1 : uE E0 e_str1 = usp + 8 * argc + 8 * envc + 184 + L0 + 1.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    destruct uE0 as (_ & _ & _ & _ & U5 & _).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE in *. rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite US, U5. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_atrandom : uE E0 e_atrandom = usp + Z.of_nat (length bsb) - 16.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
    pose proof u_e_str0 as US. unfold e_atrandom, eadd, escale, uE in *. rewrite mkAlu_denot, mkMd_denot, edenot_lit.
    rewrite u_add64, u_mul64, u64_lit by lia. rewrite US, U6. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + W.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7). pose proof u_sp8 as U8.
    unfold e_atr8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit, !u_add64, !u_mul64, !u64_lit in U8 by lia.
    rewrite U1, U2, U3, U4, U6 in *.
    (* [comment removed for export] *)
    rewrite U8. clear U1 U2 U3 U4 U5 U6 U7 U8 W2. clearbody W.
    assert (B8 : 0 <= usp / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    set (q := usp / 8) in *. clearbody q.
    rewrite (Z.mod_small (envc + W)) by lia. rewrite (Z.mod_small (argc + (envc + W))) by lia.
    rewrite Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma TV_range : 0 <= TV <= 8 /\ 0 <= (usp mod 32768) + 3935 - 4096 * TV <= 4095.
  Proof. pose proof usp_lo. pose proof usp_hi. pose proof usp_al. unfold TV. split; [split|split]; nia || lia. Qed.

  Lemma PV_range : 0 <= PV <= 7 /\ 0 <= (usp mod 32768) - 4096 * PV <= 4095 /\ 0 <= TV - PV <= 1.
  Proof. pose proof usp_lo. pose proof usp_hi. pose proof usp_al. unfold TV, PV. lia. Qed.

  Lemma BV_range : 0x1FFFE000004 <= BV <= 0x20000000000 /\ 0 <= R8V <= 7 /\ 64 * BV = usp + Z.of_nat (length bsb) + 8 * R8V.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof bsb_ge as [G GM]. pose proof len_av. pose proof len_ev. pose proof usp_al.
    unfold R8V, BV. lia.
  Qed.

  Lemma uE0_R8 : uE E0 (EVar V_R8) = R8V.
  Proof. pose proof BV_range as (_ & [? ?] & _). unfold uE. cbn [edenot E0 ev nth vals0 V_R8]. rewrite u64_lit by lia. reflexivity. Qed.


  Lemma uE0_hw : edenot E0 (EVar V_HW) = hw.
  Proof. reflexivity. Qed.

  Lemma uE0_T : uE E0 (EVar V_T) = TV.
  Proof. pose proof TV_range as [[? ?] _]. unfold uE. cbn [edenot E0 ev nth vals0 V_T]. rewrite u64_lit by lia. reflexivity. Qed.

  Lemma uE0_P : uE E0 (EVar V_P) = PV.
  Proof. pose proof PV_range as [[? ?] _]. unfold uE. cbn [edenot E0 ev nth vals0 V_P]. rewrite u64_lit by lia. reflexivity. Qed.

  Lemma u_e_top : uE E0 e_top = 32768 * (usp / 32768) + 4096 * TV.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof TV_range as [[? ?] _]. destruct uE0 as (U1 & _).
    pose proof uE0_T as UT. unfold e_top, eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UT. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_ISPD : uE E0 ISPD = 32768 * (usp / 32768) + 4096 * PV.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof PV_range as [[? ?] _]. destruct uE0 as (U1 & _).
    pose proof uE0_P as UP. unfold ISPD, eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UP. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_bend : uE E0 e_bend = usp + Z.of_nat (length bsb).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
    pose proof u_e_str0 as US. unfold e_bend, eadd, eaddz, escale, uE in *. rewrite !mkAlu_denot, mkMd_denot, !edenot_lit.
    rewrite !u_add64, u_mul64, !u64_lit by lia. rewrite US, U6. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_bend64 : uE E0 e_bend64 = 64 * BV.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof BV_range as (? & [? ?] & HB). pose proof uE0_R8 as UR. pose proof u_e_bend as UB.
    unfold e_bend64, eadd, escale, uE in *. rewrite mkAlu_denot, mkMd_denot, edenot_lit.
    rewrite u_add64, u_mul64, u64_lit by lia. rewrite UB, UR. rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
  Definition FULL0 : word -> option byte := wrap_mem ph sp argv envp uid hw rdraw.
  Definition model0 : Model := init_model (segments_reserved segs) brk0 mbase sp LIMIT_S inp.  (* [comment removed for export] *)

  Let cs0 := init_acs3 A.
  Let hid0 := hid A argH0 E0 cs0 model0.
  Let Mr0 := Mr A argH0 E0 cs0 model0 FULL0.

  Lemma model0_facts :
    m_halted model0 = None /\ m_fds model0 = fds_std /\ m_tid model0 = None
    /\ vm_reserved (m_vmmaps model0) = segments_reserved segs /\ vm_maps (m_vmmaps model0) = []
    /\ vm_noaccess (m_vmmaps model0) = [] /\ m_vm_lazy model0 = [] /\ m_vm_materialized model0 = []
    /\ vm_limit (m_vmmaps model0) = LIMIT_S /\ vm_brk (m_vmmaps model0) = brk0 /\ vm_start_brk (m_vmmaps model0) = brk0
    /\ vm_mmap_base (m_vmmaps model0) = mbase /\ eager_used model0 = 0.
  Proof. repeat split; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma alloc_top0 : alloc_top (m_vmmaps model0) = usp - 8388608.
  Proof. unfold alloc_top. replace (vm_init_sp (m_vmmaps model0)) with sp by reflexivity. unfold stack_max_size, usp. lia. Qed.

  (* [comment removed for export] *)
  Lemma hid0_eq : forall a : word, hid0 a = (argH0 E0 a || negb (APS.in_hull A (bv_unsigned a) || (usp - 8388608 <=? bv_unsigned a)))%bool.
  Proof.
    intros a. unfold hid0, hid, vis. rewrite alloc_top0. destruct model0_facts as (_&_&_&_&Hm&Hn&Hl&_). rewrite Hm. cbn [in_ivs existsb andb].
    rewrite orb_false_r. reflexivity.
  Qed.

  Lemma Mr0_visible : forall a : word, usp - 8388608 <= bv_unsigned a -> argH0 E0 a = false -> Mr0 a = FULL0 a.
  Proof.
    intros a Hc Ha. unfold Mr0, Mr, mrestrict. fold hid0. rewrite hid0_eq, Ha.
    replace (usp - 8388608 <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Hc). rewrite orb_true_r. reflexivity.
  Qed.

  Lemma FULL0_below : forall a : word, usp - 8388608 <= bv_unsigned a < usp -> FULL0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    assert (Hs : stack_to_mem sp SIMG a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold SIMG. rewrite Hs. unfold stack_max_size, usp in *.
    replace (Z.leb (bv_unsigned sp - 8 * 1024 * 1024) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  Qed.

  Lemma FULL0_low : forall a : word, bv_unsigned a < usp - 8388608 -> FULL0 a = None.
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    assert (Hs : stack_to_mem sp SIMG a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold SIMG. rewrite Hs. unfold stack_max_size, usp in *.
    replace (Z.leb (bv_unsigned sp - 8 * 1024 * 1024) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_Mr0_stack : forall (a : word) n,
    usp <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> argH0 E0 x = false) ->
    rdn segs Mr0 a n = rdn segs (stack_to_mem sp SIMG) a n.
  Proof.
    intros a n Ha Hn Hvis. pose proof usp_lo. unfold SIMG.
    rewrite <- (rdn_wrap_stack_above segs ph sp argv envp a n uid hw rdraw) by (unfold usp in *; lia).
    apply rdn_ext; [exact Hn|]. intros x Hx. apply Mr0_visible; [unfold usp in *; lia | apply Hvis; exact Hx].
  Qed.

  Lemma split_u : forall E e b k, split_lit e = (b, k) -> 0 <= k -> k <= uE E e ->
    bv_unsigned (edenot E b) + k = uE E e.
  Proof.
    intros E e b k Hs Hk Hle. unfold uE in *. rewrite (split_lit_denot E e b k Hs) in Hle |- *.
    pose proof (u64_range (edenot E b)) as Rb.
    rewrite Z_to_bv_unsigned in Hle |- *. unfold bv_wrap, bv_modulus in *. change (2 ^ Z.of_N 64) with (2 ^ 64) in *.
    destruct (Z_lt_le_dec (bv_unsigned (edenot E b) + k) (2 ^ 64)).
    - rewrite Z.mod_small by lia. reflexivity.
    - exfalso.
      assert ((bv_unsigned (edenot E b) + k) mod 2 ^ 64 = bv_unsigned (edenot E b) + k - 2 ^ 64).
      { replace (bv_unsigned (edenot E b) + k) with ((bv_unsigned (edenot E b) + k - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      lia.
  Qed.

  Lemma adenot_SA : forall E b k, adenot E (SA b k) = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
  Proof. intros. unfold adenot, v_addi. cbn [a_base a_off]. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma argH0_range : forall a : word, argH0 E0 a = true ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 24
    \/ usp + 8 * argc + 8 * envc + 184 <= bv_unsigned a < usp + Z.of_nat (length bsb) - 16.
  Proof.
    intros a H. unfold argH0 in H. pose proof W_range as (W1 & W2 & W3).
    apply andb_prop in H as [_ H].
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; [left|right]; lia.
  Qed.


  Lemma not_argH0 : forall a : word,
    (bv_unsigned a < usp + 8 * argc + 16 \/ (usp + 8 * argc + 8 * envc + 24 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 184)
     \/ usp + Z.of_nat (length bsb) - 16 <= bv_unsigned a) -> argH0 E0 a = false.
  Proof.
    intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
    pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kword_stack : forall b k v (w : word),
    bv_unsigned (edenot E0 b) + k = bv_unsigned w ->
    usp <= bv_unsigned w -> bv_unsigned w + 8 <= usp + Z.of_nat (length bsb) ->
    (forall x : word, bv_unsigned w <= bv_unsigned x < bv_unsigned w + 8 -> argH0 E0 x = false) ->
    rdn segs (stack_to_mem sp SIMG) w 8%nat = Some (word_le8 (edenot E0 v)) ->
    kentry_ok segs E0 Mr0 (KWord (SA b k) 8 v).
  Proof.
    intros b k v w Hw Hlo Hhi Hvis Hrd. pose proof usp_fit. pose proof usp_lo. pose proof (u64_range w).
    cbn [kentry_ok]. split; [lia|].
    assert (Hfl : flat E0 (SA b k) (Z.of_nat 8)) by (unfold flat, estart; cbn [a_base a_off]; change (Z.of_nat 8) with 8; lia).
    split; [exact Hfl|].
    rewrite adenot_SA. cbn [a_base a_off]. rewrite Hw, Z_to_bv_bv_unsigned.
    rewrite rdn_Mr0_stack; [| lia | change (Z.of_nat 8) with 8; lia | exact Hvis].
    rewrite Hrd. rewrite n_to_le_8_spec. reflexivity.
  Qed.


  (* [comment removed for export] *)
  Lemma auxv_word_ok : forall (j : nat) v,
    (j < 20)%nat ->
    nth j (auxv_words ph (at_random_ptr sp argv envp) uid hw) (Z_to_bv 64 0) = edenot E0 v ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
  Proof.
    intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    apply (kword_stack ab (ak + 8 * Z.of_nat j) v (sp + nat_to_word (auxv_off argv envp + 8 * j))%bv).
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold auxv_off, usp in *; [|lia].
      rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia.
    - rewrite <- Hv.
      pose proof (read_auxv_word segs ph sp rdraw argv envp uid hw Hva Hve Hhi' j Hj) as RW.
      exact RW.
  Qed.

  Lemma auxw_ok : forall i ty v,
    (0 <= i <= 9) ->
    nth (Z.to_nat (2 * i)) (auxv_words ph (at_random_ptr sp argv envp) uid hw) (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    nth (Z.to_nat (2 * i + 1)) (auxv_words ph (at_random_ptr sp argv envp) uid hw) (Z_to_bv 64 0) = edenot E0 v ->
    know_ok segs E0 Mr0 (auxw i ty v).
  Proof.
    intros i ty v Hi H1 H2. unfold auxw.
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
    - replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [lia|]. exact H2.
  Qed.

  Lemma kr_ok : forall e lo hi, lo <= uE E0 e <= hi -> kentry_ok segs E0 Mr0 (KRange e lo hi).
  Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma Mr0_below : forall a : word, usp - 8388608 <= bv_unsigned a < usp -> Mr0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. pose proof usp_lo. pose proof len_av.
    rewrite Mr0_visible; [apply FULL0_below; exact Ha | lia | apply not_argH0; lia].
  Qed.

  Lemma stack_window_ok :
    kentry_ok segs E0 Mr0 (KWr (SA e_sp0 (-8388608)) (ELit 8388608))
    /\ kentry_ok segs E0 Mr0 (KZero (SA e_sp0 (-8388608)) (ELit 8388608)).
  Proof.
    pose proof usp_lo. pose proof usp_hi.
    assert (Hst : estart E0 (SA e_sp0 (-8388608)) = usp - 8388608).
    { unfold estart. cbn [a_base a_off]. pose proof u_e_sp0 as U. unfold uE in U. rewrite U. lia. }
    assert (Hl : elenZ E0 (ELit 8388608) = 8388608) by (apply elenZ_lit; lia).
    assert (Hfl : flat E0 (SA e_sp0 (-8388608)) (elenZ E0 (ELit 8388608))).
    { unfold flat. rewrite Hst, Hl. lia. }
    split; cbn [kentry_ok]; (split; [exact Hfl|]); rewrite Hst, ?Hl.
    - intros d m Hd Hdm. apply store_ok_of_all; rewrite u_small by lia; [lia|].
      intros x Hx. unfold wview. rewrite (Mr0_below x) by lia. discriminate.
    - intros i Hi. apply Mr0_below. rewrite u_small by lia. lia.
  Qed.

  Lemma argc_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 0) 8 (EVar V_ARGC)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    apply (kword_stack e_sp0 0 (EVar V_ARGC) sp).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. unfold usp. lia.
    - unfold usp. lia.
    - unfold usp in *. lia.
    - intros x Hx. apply not_argH0. unfold usp in *. lia.
    - pose proof (read_argc ph segs sp argv envp uid hw rdraw) as RW.
      assert (Hv : len_word argv = edenot E0 (EVar V_ARGC)).
      { apply bv_eq. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. rewrite U3. unfold argc. exact (u_argcN argv Hva). }
      rewrite <- Hv. apply RW. fold bsb. pose proof usp_fit. unfold usp in *. lia.
  Qed.

  Lemma argv0_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 8) 8 e_str0).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    apply (kword_stack e_sp0 8 e_str0 (sp + nat_to_word (8 + 8 * 0))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - pose proof (read_argv_ptr_k ph segs sp argv envp 0 uid hw rdraw Hav0) as RW.
      assert (Hv : cat_argv_ptr sp argv envp 0 = edenot E0 e_str0).
      { apply bv_eq. rewrite (@u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve Hlo' Hhi' 0 Hav0).
        pose proof u_e_str0 as U. unfold uE in U. rewrite U. unfold cat_struct_size, auxv_size. replace (total_arg_bytes_nat (firstn 0 argv)) with 0%nat by reflexivity.
        unfold usp, argc, envc. lia. }
      rewrite <- Hv. apply RW. fold bsb. unfold usp in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma argv1_word_ok : kentry_ok segs E0 Mr0 (kw_argv1 e_argv1w).
  Proof.
    unfold kw_argv1.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    assert (Hw1 : edenot E0 e_argv1w = if (1 <? argc) then edenot E0 e_str1 else Z_to_bv 64 0).
    { unfold e_argv1w. cbn [edenot]. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
      apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U3 by lia.
      pose proof (u64_range (edenot E0 e_str1)).
      destruct (1 <? argc); [rewrite Z.mul_1_l, Z.mod_small by lia; reflexivity | rewrite u64_lit by lia; reflexivity]. }
    apply (kword_stack e_sp0 16 e_argv1w (sp + nat_to_word (8 + 8 * 1))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - rewrite Hw1. destruct (1 <? argc) eqn:Hc.
      + apply Z.ltb_lt in Hc. assert (Hav1 : (1 < length argv)%nat) by (unfold argc in Hc; lia).
        pose proof (read_argv_ptr_k ph segs sp argv envp 1 uid hw rdraw Hav1) as RW.
        assert (Hv : cat_argv_ptr sp argv envp 1 = edenot E0 e_str1).
        { apply bv_eq. rewrite (@u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve Hlo' Hhi' 1 Hav1).
          pose proof u_e_str1 as U. unfold uE in U. rewrite U. unfold cat_struct_size, auxv_size.
          assert (TF : forall l : list (list byte), (0 < length l)%nat ->
                        Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
            by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
          rewrite Nat2Z.inj_add, (TF argv Hav0). unfold L0, usp, argc, envc. lia. }
        rewrite <- Hv. apply RW. fold bsb. unfold usp in *. lia.
      + apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
        pose proof (read_argv_null segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as RW. rewrite Hav1 in RW.
        exact RW.
  Qed.

  (* [comment removed for export] *)
  Lemma atrandom_byte : forall i, 0 <= i < 16 ->
    exists b, Mr0 (Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i)) = Some b.
  Proof.
    intros i Hi. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    destruct (at_random_off segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as [off (Hp & Hlen & Hmod & Hrd)].
    fold bsb in Hlen.
    assert (Hu : bv_unsigned (at_random_ptr sp argv envp) = usp + Z.of_nat off).
    { rewrite Hp, word_add_nat. apply u64_lit. unfold usp in *. lia. }
    specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold bsb in Hrd. fold SIMG in Hrd.
    rewrite (BackingAlgebra.AsanCeil.firstn1_skipn_nth _ _ (Z_to_bv 8 0)) in Hrd by (rewrite length_at_random_bytes; lia).
    assert (Ha : (at_random_ptr sp argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i)).
    { apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
    rewrite Ha in Hrd.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp ph sp argv envp _ uid hw rdraw) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    cbn [rdn] in Hrd.
    destruct (stack_to_mem sp SIMG (Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i))) as [b|] eqn:Hstk.
    - exists b. reflexivity.
    - exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
      replace (usp <=? usp + Z.of_nat (length bsb) - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
      cbv zeta in Hstk.
      assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, entry_stack_image; cbv zeta; rewrite length_app; fold bsb; lia).
      replace (usp + Z.of_nat (length bsb) - 16 + i - usp <? Z.of_nat (length SIMG)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
      apply nth_error_None in Hstk. lia.
  Qed.

  Lemma atrb_start : estart E0 (SA (fst e_atrb) (snd e_atrb)) = usp + Z.of_nat (length bsb) - 16.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb)) by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
    set (ab := fst e_atrb) in *. set (ak := snd e_atrb) in *.
    pose proof (split_u E0 e_atrandom ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : ak = 184) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)). unfold estart; cbn [a_base a_off]. lia.
  Qed.

  Lemma atrandom_unk_ok : kentry_ok segs E0 Mr0 (KUnk (SA (fst e_atrb) (snd e_atrb)) (ELit 16)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite atrb_start, Hl.
    split; [unfold flat; rewrite atrb_start; unfold usp in *; lia|].
    intros i Hi. destruct (atrandom_byte i Hi) as [b Hb]. rewrite Hb. discriminate.
  Qed.

  Lemma atrandom_wr_ok : kentry_ok segs E0 Mr0 (KWr (SA (fst e_atrb) (snd e_atrb)) (ELit 16)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite atrb_start, Hl.
    split; [unfold flat; rewrite atrb_start; unfold usp in *; lia|].
    intros d m Hd Hdm. apply store_ok_of_all; rewrite u_small by (unfold usp in *; lia); [unfold usp in *; lia|].
    intros x Hx. unfold wview.
    destruct (atrandom_byte (bv_unsigned x - (usp + Z.of_nat (length bsb) - 16)) ltac:(lia)) as [b Hb].
    replace (Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + (bv_unsigned x - (usp + Z.of_nat (length bsb) - 16)))) with x in Hb
      by (apply bv_eq; rewrite u64_lit; [lia | pose proof (u64_range x); lia]).
    rewrite Hb. discriminate.
  Qed.

  Lemma kimg_ok : kentry_ok segs E0 Mr0 (KImg (img_lo A) (img_hi A)).
  Proof.
    pose proof usp_lo. pose proof (if_hull _ _ _ IMG) as (H1 & H2 & H3 & H4). cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    unfold Mr0, Mr, mrestrict. destruct (hid A argH0 E0 cs0 model0 (Z_to_bv 64 i)); [reflexivity|].
    apply FULL0_low. rewrite u64_lit; lia.
  Qed.

  Lemma rw_window_ok : kentry_ok segs E0 Mr0 (KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))).
  Proof.
    pose proof (if_rw _ _ _ IMG) as ((R1 & R0 & R2) & R3).
    assert (Hst : estart E0 (SA (ELit 0) (rw_lo A)) = rw_lo A) by (unfold estart; cbn [a_base a_off]; rewrite edenot_lit, u64_lit; lia).
    assert (Hl : elenZ E0 (ELit (rw_len A)) = rw_len A) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; lia|].
    intros d m Hd Hdm. destruct m as [|m']; [reflexivity|].
    assert (Hu : bv_unsigned (Z_to_bv 64 (rw_lo A + d)) = rw_lo A + d) by (apply u_small; rewrite Nat2Z.inj_succ in Hdm; lia).
    apply store_ok_of_all; rewrite Hu; [lia|].
    intros x Hx. apply R3. lia.
  Qed.

  Lemma atr_ptr_eq : at_random_ptr sp argv envp = edenot E0 e_atrandom.
  Proof.
    pose proof usp_lo. pose proof usp_fit.
    destruct (at_random_off segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as [off (Hp & Hlen & Hmod & _)]. fold bsb in Hlen.
    apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold usp in *; lia).
    pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold usp. lia.
  Qed.

  Lemma init_kn3_ok : know_ok segs E0 Mr0 (init_kn3 A).
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    pose proof brk_range as [B1 B2]. pose proof bsb_ge as [G _]. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3). pose proof usp_al.
    pose proof TV_range as [[T1 T2] [T3 T4]]. pose proof PV_range as ([Q1 Q2] & [Q3 Q4] & [Q5 Q6]).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    assert (Hmod : usp mod 32768 = usp - 32768 * (usp / 32768)) by lia.
    clearbody W TV PV BV R8V.   (* [comment removed for export] *)
    unfold init_kn3.
    destruct stack_window_ok as [SW1 SW2].
    apply Forall_app; split.
    { apply Forall_cons; [apply kr_ok; rewrite U1; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U2; lia|].
      apply Forall_cons; [apply kr_ok; unfold eaddz, uE; rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia;
                          pose proof u_e_atrandom as U; unfold uE in U; rewrite U; rewrite Z.mod_small by lia; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_atr8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_sp0; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_sp8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U3; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U4; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U5; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_L1; pose proof L1_range; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_uid; unfold valid_id in Huid; pose proof (u64_range uid); lia|].
      apply Forall_cons; [apply kr_ok; unfold uE; rewrite uE0_hw; pose proof Hhw as HW'; unfold valid_hwcap, hwcap_rv64gc, hwcap_rv64gcv in HW';
                          destruct HW' as [HW' | HW']; rewrite HW'; rewrite u64_lit by lia; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_T; lia|].
      apply Forall_cons.
      { apply kr_ok. unfold eaddz, esub, escale, uE. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
        rewrite u_add64, u_sub64, !u_mul64, !u64_lit by lia.
        pose proof uE0_T as UT; unfold uE in UT; unfold uE in U2; rewrite U2, UT.
        rewrite (Z.mod_small (16 * _)) by lia. rewrite (Z.mod_small (4096 * _)) by lia.
        rewrite Z.add_mod_idemp_l by lia. rewrite Z.mod_small by lia. lia. }
      apply Forall_cons; [apply kr_ok; rewrite uE0_P; lia|].
      apply Forall_cons.
      { apply kr_ok. unfold esub, escale, uE. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
        rewrite u_sub64, !u_mul64, !u64_lit by lia.
        pose proof uE0_P as UP; unfold uE in UP; unfold uE in U2; rewrite U2, UP.
        rewrite (Z.mod_small (16 * _)) by lia. rewrite (Z.mod_small (4096 * _)) by lia. rewrite Z.mod_small by lia. lia. }
      apply Forall_cons.
      { apply kr_ok. unfold esub, uE. rewrite mkAlu_denot, u_sub64.
        pose proof uE0_T as UT; pose proof uE0_P as UP; unfold uE in UT, UP; rewrite UT, UP. rewrite Z.mod_small by lia. lia. }
      apply Forall_cons.
      { apply kr_ok. unfold uE. cbn [edenot]. rewrite u_sub64.
        pose proof u_e_sp0 as US; pose proof u_ISPD as UI; unfold uE in US, UI; rewrite US, UI. rewrite Z.mod_small by lia. lia. }
      pose proof BV_range as ([BV1 BV2] & [BV3 BV4] & BV5).
      apply Forall_cons; [apply kr_ok; rewrite uE0_R8; lia|].
      apply Forall_cons.
      { apply kr_ok. unfold eadd, uE. rewrite mkAlu_denot, u_add64.
        pose proof u_e_atr8 as UA; pose proof uE0_R8 as UR; unfold uE in UA, UR; rewrite UA, UR. rewrite Z.mod_small by lia. lia. }
      apply Forall_cons; [apply kr_ok; rewrite u_e_bend64; lia|].
      apply Forall_cons.
      { (* [comment removed for export] *)
        apply kr_ok. unfold eadd, uE. rewrite mkAlu_denot. cbn [edenot].
        pose proof uE0_R8 as UR. unfold uE in UR, U3, U4, U6, U2. cbn [edenot] in UR, U3, U4, U6, U2.
        rewrite u_add64, u_and64, !u_add64, u_mul64, !u64_lit by lia. rewrite UR, U3, U4, U6, U2.
        rewrite (Z.mod_small (2 * _)) by lia. rewrite (Z.mod_small (W + _)) by lia. rewrite (Z.mod_small (envc + _)) by lia. rewrite (Z.mod_small (argc + _)) by lia.
        replace (Z.land (argc + (envc + (W + 2 * (usp mod 32768 / 16)))) 7) with (Z.land (argc + (envc + (W + 2 * (usp mod 32768 / 16)))) (Z.ones 3)) by reflexivity.
        rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        set (b := usp mod 32768 / 16) in *.
        assert (Hu : usp = 32768 * (usp / 32768) + 16 * b) by (subst b; lia).
        assert (H8 : 8 * BV = 4096 * (usp / 32768) + 2 * b + W + argc + envc + 25 + R8V) by lia.
        assert (HM : (argc + (envc + (W + 2 * b))) mod 8 = 7 - R8V).
        { replace (argc + (envc + (W + 2 * b))) with ((7 - R8V) + (BV - 512 * (usp / 32768) - 4) * 8) by lia.
          rewrite Z.mod_add, Z.mod_small by lia. reflexivity. }
        rewrite HM. rewrite Z.mod_small by lia. lia. }
      apply Forall_cons; [apply kr_ok; rewrite U6; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U7; unfold BRK_ASLR in *; lia|].
      apply Forall_cons; [exact SW1|].
      apply Forall_cons; [exact SW2|].
      apply Forall_cons; [exact argc_word_ok|].
      apply Forall_cons; [exact argv0_word_ok|].
      apply Forall_cons; [exact argv1_word_ok|].
      apply Forall_nil. }
    repeat (apply Forall_app; split).
    1-10: apply auxw_ok; [lia | rewrite auxv_words_eq; cbn [nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul]; try reflexivity ..].
    all: try (rewrite edenot_lit; reflexivity).
    1: rewrite edenot_lit, P1; reflexivity.
    1: rewrite edenot_lit, P2; reflexivity.
    1: rewrite edenot_lit, P3; reflexivity.
    1: exact atr_ptr_eq.
    apply Forall_cons; [exact atrandom_unk_ok|].
    apply Forall_cons; [exact atrandom_wr_ok|].
    apply Forall_cons; [exact kimg_ok|].
    apply Forall_cons; [exact rw_window_ok|].
    apply Forall_nil.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma init_regs_nth : forall n, nth n init_regs (ELit 0) = if Nat.eqb n 2 then e_sp0 else ELit 0.
  Proof.
    intros n. unfold init_regs.
    do 32 (destruct n as [|n]; [reflexivity|]). cbn. destruct n; reflexivity.
  Qed.

  Lemma init_regs_ok : regs_ok E0 init_regs R0.
  Proof.
    intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
    - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
    - rewrite init_regs_nth. pose proof (ridx_range r) as Hlt.
      destruct (Nat.eqb (ridx r) 2) eqn:H2.
      + apply Nat.eqb_eq in H2. rewrite edenot_e_sp0.
        assert (r = 2%bv) by (rewrite <- (ridx_roundtrip r); rewrite H2; apply bv_eq; reflexivity). subst r. reflexivity.
      + rewrite edenot_lit. apply Nat.eqb_neq in H2.
        rewrite <- (ridx_roundtrip r). rewrite <- (ridx_roundtrip r) in Hr0.
        set (n := ridx r) in *. clearbody n.
        do 32 (destruct n as [|n]; [first [exfalso; clear - H2; lia | vm_compute in Hr0 |- *; first [discriminate | reflexivity]] |]).
        exfalso. lia.
  Qed.

  Lemma allowA_init : allowA A E0 cs0 =
    flat_map (allow1 A E0) (init_vis3 A).
  Proof. unfold allowA, cs0, init_acs3. cbn [a_vis a_ghost]. rewrite app_nil_r. reflexivity. Qed.

  Lemma A_bytes_app : forall l1 l2, A_bytes (l1 ++ l2) = A_bytes l1 + A_bytes l2.
  Proof. induction l1 as [|[a b] l1 IH]; intros l2; cbn; [reflexivity|]. rewrite IH. lia. Qed.

  (* [comment removed for export] *)
  Lemma allow1_cost : forall p n, 0 <= uE E0 (snd p) <= n -> 0 <= uE E0 (fst p) -> uE E0 (fst p) mod 8 = 0 -> 0 <= shadow_off A ->
    A_bytes (allow1 A E0 p) <= vis_cost n.
  Proof.
    intros [b l] n Hn Hb Hal HS. clearbody W TV PV BV R8V.   (* [comment removed for export] *)
    unfold allow1, sh_lo, sh_hi. cbn [fst snd A_bytes] in *. unfold vis_cost.
    pose proof (pageup_minus_pagedown (uE E0 b) (uE E0 b + uE E0 l) ltac:(lia)).
    pose proof (pageup_minus_pagedown (shadow_off A + uE E0 b / 8) (shadow_off A + (uE E0 b + uE E0 l) / 8) ltac:(lia)).
    assert ((uE E0 b + uE E0 l) / 8 - uE E0 b / 8 <= n / 8) by (apply Z.le_trans with ((uE E0 b + n) / 8 - uE E0 b / 8); [apply Z.sub_le_mono_r; apply Z.div_le_mono; lia | lia]).
    lia.
  Qed.

  Lemma abytes_init : A_bytes (allowA A E0 cs0) <= init_abytes A /\ init_abytes A <= LIMIT_S.
  Proof.
    clearbody W TV PV BV R8V.   (* [comment removed for export] *)
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    pose proof TV_range as [[T1 T2] [T3 T4]]. pose proof usp_al.
    rewrite allowA_init. unfold init_vis3. cbn [flat_map]. rewrite !A_bytes_app. cbn [A_bytes app]. rewrite Z.add_0_r.
    unfold init_abytes. split; [| unfold vis_cost, LIMIT_S, STACK_MAX, WBLK2_LEN; rewrite StoreOk.RunLim.LMIN_val; lia].   (* [comment removed for export] *)
    assert (NEG8 : bv_unsigned (Z_to_bv 64 (- STACK_MAX)) = 2 ^ 64 - 8388608) by (rewrite Z_to_bv_unsigned; reflexivity).
    assert (NEG4 : bv_unsigned (Z_to_bv 64 (- WBLK2_LEN)) = 2 ^ 64 - 4194304) by (rewrite Z_to_bv_unsigned; reflexivity).
    assert (USP8 : uE E0 (EAlu Instr.ALU_ADD e_sp0 (ELit (- STACK_MAX))) = usp - 8388608).
    { pose proof u_e_sp0 as US. unfold uE in *. cbn [edenot]. rewrite u_add64, NEG8, US.
      replace (usp + (2 ^ 64 - 8388608)) with ((usp - 8388608) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia. }
    assert (TOP8 : uE E0 (EAlu Instr.ALU_ADD e_top (ELit (- STACK_MAX))) = 32768 * (usp / 32768) + 4096 * TV - 8388608).
    { pose proof u_e_top as UT. unfold uE in *. cbn [edenot]. rewrite u_add64, NEG8, UT.
      replace (32768 * (usp / 32768) + 4096 * TV + (2 ^ 64 - 8388608)) with ((32768 * (usp / 32768) + 4096 * TV - 8388608) + 1 * 2 ^ 64) by lia.
      rewrite Z.mod_add, Z.mod_small by lia. lia. }
    pose proof BV_range as ([BV1 BV2] & [BV3 BV4] & BV5).
    assert (BEND4 : uE E0 (eaddz e_bend64 (- WBLK2_LEN)) = 64 * BV - 4194304).
    { pose proof u_e_bend64 as UB. unfold eaddz, uE in *. rewrite mkAlu_denot. cbn [edenot]. rewrite u_add64, NEG4, UB.
      replace (64 * BV + (2 ^ 64 - 4194304)) with ((64 * BV - 4194304) + 1 * 2 ^ 64) by lia.
      rewrite Z.mod_add, Z.mod_small by lia. lia. }
    assert (LIT : forall z, 0 <= z < 2 ^ 64 -> uE E0 (ELit z) = z) by (intros z Hz; unfold uE; rewrite edenot_lit, u64_lit by lia; reflexivity).
    pose proof bsb_ge as [_ GM].
    assert (C1 : A_bytes (allow1 A E0 (ELit (img_lo A), ELit (img_hi A - img_lo A))) <= vis_cost (img_hi A - img_lo A)).
    { apply allow1_cost; cbn [fst snd]; rewrite ?LIT by lia; lia. }
    assert (C2 : A_bytes (allow1 A E0 (EAlu Instr.ALU_ADD e_sp0 (ELit (- STACK_MAX)), ELit STACK_MAX)) <= vis_cost STACK_MAX).
    { apply allow1_cost; cbn [fst snd]; rewrite ?USP8, ?LIT by (unfold STACK_MAX; lia); unfold STACK_MAX; lia. }
    assert (C3 : A_bytes (allow1 A E0 (EAlu Instr.ALU_ADD e_top (ELit (- STACK_MAX)), ELit STACK_MAX)) <= vis_cost STACK_MAX).
    { apply allow1_cost; cbn [fst snd]; rewrite ?TOP8, ?LIT by (unfold STACK_MAX; lia); unfold STACK_MAX; lia. }
    assert (C4 : A_bytes (allow1 A E0 (eaddz e_bend64 (- WBLK2_LEN), ELit WBLK2_LEN)) <= vis_cost WBLK2_LEN).
    { apply allow1_cost; cbn [fst snd]; rewrite ?BEND4, ?LIT by (unfold WBLK2_LEN; lia); unfold WBLK2_LEN; lia. }
    lia.
  Qed.

  Theorem init_cs_ok : cs_ok segs A LIMIT_S SINV0 argH0 ISP_S fs E0 cs0 R0 FULL0 model0.
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2]. pose proof usp_lo. pose proof usp_hi.
    constructor; cbn [cs0 init_acs3 a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_meter a_fake a_fbud];
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_kn3_ok.
    - reflexivity.
    - reflexivity.     (* [comment removed for export] *)
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - constructor.     (* [comment removed for export] *)
    - constructor.     (* [comment removed for export] *)
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      unfold model0. apply init_sp_ok_init_model. exact Hsp.
    - constructor.     (* [comment removed for export] *)
    - constructor.     (* [comment removed for export] *)
    - intros z Hz. exact Hz.   (* [comment removed for export] *)
    - constructor.     (* [comment removed for export] *)
    - constructor.     (* [comment removed for export] *)
    - rewrite app_nil_r, (if_sizes _ _ _ IMG). lia.   (* [comment removed for export] *)
    - unfold ISP_S. rewrite edenot_e_sp0. reflexivity.   (* [comment removed for export] *)
    - split; [unfold model0; apply init_sp_ok_init_model; exact Hsp | cbn; exact Hhi'].   (* [comment removed for export] *)
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.   (* [comment removed for export] *)
    - cbn. lia.        (* [comment removed for export] *)
    - lia.             (* [comment removed for export] *)
    - exact AB1.       (* [comment removed for export] *)
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].   (* [comment removed for export] *)
    - intros a _ Hm. cbn in Hm. discriminate Hm.   (* [comment removed for export] *)
    - intros a Hm _. cbn in Hm. discriminate Hm.   (* [comment removed for export] *)
    - intros a Hp. cbn in Hp. discriminate Hp.     (* [comment removed for export] *)
    - split; [intros; reflexivity | intros a Ha; reflexivity].   (* [comment removed for export] *)
    - constructor.     (* [comment removed for export] *)
    - constructor.     (* [comment removed for export] *)
    - constructor.     (* [comment removed for export] *)
  Qed.




  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition model0_at (LIM : Z) : Model := init_model (segments_reserved segs) brk0 mbase sp LIM inp.


  Lemma model0_at_facts : forall LIM,
    m_halted (model0_at LIM) = None /\ m_fds (model0_at LIM) = fds_std /\ m_tid (model0_at LIM) = None
    /\ vm_reserved (m_vmmaps (model0_at LIM)) = segments_reserved segs /\ vm_maps (m_vmmaps (model0_at LIM)) = []
    /\ vm_noaccess (m_vmmaps (model0_at LIM)) = [] /\ m_vm_lazy (model0_at LIM) = [] /\ m_vm_materialized (model0_at LIM) = []
    /\ vm_limit (m_vmmaps (model0_at LIM)) = LIM /\ vm_brk (m_vmmaps (model0_at LIM)) = brk0 /\ vm_start_brk (m_vmmaps (model0_at LIM)) = brk0
    /\ vm_mmap_base (m_vmmaps (model0_at LIM)) = mbase /\ eager_used (model0_at LIM) = 0
    /\ alloc_top (m_vmmaps (model0_at LIM)) = alloc_top (m_vmmaps model0) /\ vm_init_sp (m_vmmaps (model0_at LIM)) = sp.
  Proof. intros LIM. repeat split; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma hid_at : forall LIM, hid A argH0 E0 cs0 (model0_at LIM) = hid A argH0 E0 cs0 model0.
  Proof. intros LIM. reflexivity. Qed.
  Lemma Mr_at : forall LIM, Mr A argH0 E0 cs0 (model0_at LIM) FULL0 = Mr A argH0 E0 cs0 model0 FULL0.
  Proof. intros LIM. reflexivity. Qed.

  Theorem init_cs_ok_at : forall LIM : Z, LIMIT_S <= LIM -> cs_ok segs A LIMIT_S SINV0 argH0 ISP_S fs E0 cs0 R0 FULL0 (model0_at LIM).
  Proof.
    intros LIM HLIM. pose proof init_cs_ok as H.
    destruct (model0_at_facts LIM) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    destruct H; constructor; rewrite ?hid_at, ?Mr_at, ?N1, ?N2, ?N3, ?N4, ?N5, ?N6, ?N7, ?N8, ?N9, ?N10, ?N11, ?N12, ?N14, ?N15;
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M10, ?M11, ?M12 in *; try assumption; try exact HLIM.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- MInv _ _ =>
             lazymatch goal with MI : MInv _ model0 |- _ =>
               destruct MI as [_ _ _ _ B5]; constructor; rewrite ?N7, ?N8, ?N9, ?N13;
                 [constructor | intros p [] | intros p [] | intros p [] | rewrite M9, M13 in B5; lia] end
         | |- model_ivs_wf _ =>
             unfold model_ivs_wf; rewrite N5, N6, N7; repeat split; try (intros q []); unfold model0_at; apply init_sp_ok_init_model; exact Hsp
         | |- init_sp_ok _ /\ _ =>
             split; [unfold model0_at; apply init_sp_ok_init_model; exact Hsp |];
             lazymatch goal with I : init_sp_ok _ /\ _ |- _ => exact (proj2 I) end
         | |- fds_ok _ _ _ => lazymatch goal with F : fds_ok _ _ model0 |- _ => exact F end
         | |- _ = edenot _ ISP_S => lazymatch goal with I : _ = edenot _ ISP_S |- _ => exact I end
         | |- _ <= a_eager _ => lazymatch goal with EG : _ <= a_eager _ |- _ => rewrite M13 in EG; exact EG end
         end.
  Qed.

  Theorem init_cfg_eq_at : forall (LIM : Z) (apc : N), Z.of_N apc = a_entry A ->
    init_config segs apc ph sp brk0 mbase rdraw LIM inp = cfg_of segs R0 (a_entry A) FULL0 (model0_at LIM).
  Proof.
    intros LIM apc Hpc. unfold init_config, cfg_of. cbn [in_argv in_envp in_uid in_hwcap inp]. rewrite init_mkst. rewrite Hpc. reflexivity.
  Qed.
  Theorem init_cfg_eqF_at : forall (LIM : Z) (apc : N), Z.of_N apc = a_entry A ->
    init_config segs apc ph sp brk0 mbase rdraw LIM inp = GPS.cfgF segs fx0 R0 (a_entry A) FULL0 (model0_at LIM).
  Proof. intros LIM apc Hpc. rewrite (init_cfg_eq_at LIM apc Hpc). reflexivity. Qed.
End Init.
