(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition setsh_words : list (option (bv 32)) :=
  [None; None; Some W_703e4; Some W_703e8; None; Some W_703f0].

(* [comment removed for export] *)
Definition setsh_clob : list reg := [6; 11; 12; 13; 14; 15; 16].



Section SETSH.
  Variable segs : list Segment.
  Variables base mset : word.
  Variables g_rms p_rms val : Z.
  Hypothesis HCODE : code_ato segs base 0 setsh_words.
  Hypothesis HMSET : code_at segs mset 0 mmemset_words.
  Hypothesis HMSET_OK : ret_ok mset.
  Hypothesis G0 : gload segs base 0 12 g_rms.
  (* [comment removed for export] *)
  Hypothesis LI16 : forall regs mem rom,
    msteps segs (mkst regs (at_ base 16) mem rom) (mkst (regupd regs 11 (Z_to_bv 64 val)) (at_ base 20) mem rom).

  Lemma Fo8 : fetch_word segs (at_ base 8) = Some W_703e4.
  Proof using HCODE. exact (code_ato_get segs base 0 setsh_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo12 : fetch_word segs (at_ base 12) = Some W_703e8.
  Proof using HCODE. exact (code_ato_get segs base 0 setsh_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_703f0.
  Proof using HCODE. exact (code_ato_get segs base 0 setsh_words 5 _ HCODE eq_refl). Qed.

  Ltac gl G Hr := eapply msteps_trans; [ eapply G; exact Hr | ]; zlit_at.
  Ltac cld F D vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Hr | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma setsh_stub : forall mem rom (addr nv ra : word) regs,
    rdn segs mem (Z_to_bv 64 g_rms) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 p_rms)) ->
    rdn segs mem (Z_to_bv 64 p_rms) 8 = Some (word_to_le_bytes 8 mset) ->
    (0 <= p_rms /\ p_rms + 8 <= 2 ^ 64)%Z ->
    getr regs 10 = addr -> getr regs 11 = nv -> getr regs 1 = ra ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r (at_ mset 0) mem rom)
      /\ getr r 10 = addr /\ getr r 11 = Z_to_bv 64 val /\ getr r 12 = nv /\ getr r 1 = ra
      /\ regs_agree (fun r => In r setsh_clob) regs r.
  Proof using LI16 G0 HMSET_OK HCODE.
    intros mem rom addr nv ra regs R1 R2 B H10 H11 H1.
    pose proof (u64_range mset) as Hm. pose proof HMSET_OK as Hk.
    wd_eexists. split; [|split; [|split; [|split; [|split]]]].
    - gl G0 R1.                                          (* [comment removed for export] *)
      cld Fo8 D_703e4 mset R2.                           (* [comment removed for export] *)
      an Fo12 D_703e8.                                   (* [comment removed for export] *)
      eapply msteps_trans; [apply LI16|]. zlit_at.       (* [comment removed for export] *)
      aret Fo20 D_703f0 mset.                           (* [comment removed for export] *)
      wd_refl.
    - gres; rwH; reflexivity.
    - gres; rwH; reflexivity.
    - gres; rwH; reflexivity.
    - gres; rwH; reflexivity.
    - (lazymatch goal with |- ?G => let G' := eval unfold setsh_clob in G in change_no_check G' end). solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Theorem setsh_run : forall mem rom (addr ra : word) (n : Z) regs,
    rdn segs mem (Z_to_bv 64 g_rms) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 p_rms)) ->
    rdn segs mem (Z_to_bv 64 p_rms) 8 = Some (word_to_le_bytes 8 mset) ->
    (0 <= p_rms /\ p_rms + 8 <= 2 ^ 64)%Z ->
    (0 <= n)%Z -> (bv_unsigned addr + n < 2 ^ 64)%Z ->
    store_ok segs mem addr (Z.to_nat n) = true -> ret_ok ra ->
    getr regs 10 = addr -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 = ra ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom)
                  (mkst r ra (wbytes mem addr (repeat (cbyte (Z_to_bv 64 val)) (Z.to_nat n))) rom)
      /\ getr r 10 = addr /\ regs_agree (fun r => In r setsh_clob) regs r.
  Proof using LI16 G0 HMSET_OK HMSET HCODE.
    intros mem rom addr ra n regs R1 R2 B Hn Hnw Hok Hret H10 H11 H1.
    destruct (setsh_stub mem rom addr (Z_to_bv 64 n) ra regs R1 R2 B H10 H11 H1) as (r1 & RUN1 & P10 & P11 & P12 & P1 & AG1).
    destruct (memset_summary segs mset HMSET mem addr (Z_to_bv 64 val) ra n rom Hn Hnw Hok Hret r1 P10 P11 P12 P1)
      as (r2 & RUN2 & Q10 & AG2).
    exists r2. split; [|split; [exact Q10|]].
    - eapply msteps_trans; [exact RUN1 | exact RUN2].
    - intros r Hr. rewrite (AG2 r); [apply AG1; exact Hr|].
      intros Hm. apply Hr. unfold ms_clob in Hm. (lazymatch goal with |- ?G => let G' := eval unfold setsh_clob in G in change_no_check G' end). cbn [In] in *. tauto.
  Qed.

  (* [comment removed for export] *)
  Theorem setsh_run_fp : forall mem rom (addr ra : word) (n : Z) (H : word -> bool) regs,
    rdn segs mem (Z_to_bv 64 g_rms) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 p_rms)) ->
    rdn segs mem (Z_to_bv 64 p_rms) 8 = Some (word_to_le_bytes 8 mset) ->
    (0 <= p_rms /\ p_rms + 8 <= 2 ^ 64)%Z -> (0 <= g_rms /\ g_rms + 8 <= 2 ^ 64)%Z ->
    (0 <= n)%Z -> (bv_unsigned addr + n < 2 ^ 64)%Z ->
    store_ok segs mem addr (Z.to_nat n) = true -> ret_ok ra ->
    hid_off H g_rms 8 -> hid_off H p_rms 8 -> hid_off H (bv_unsigned addr) n ->
    getr regs 10 = addr -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 = ra ->
    exists r,
      msteps segs (mkst regs (at_ base 0) (mrestrict H mem) rom)
                  (mkst r ra (mrestrict H (wbytes mem addr (repeat (cbyte (Z_to_bv 64 val)) (Z.to_nat n)))) rom)
      /\ getr r 10 = addr /\ regs_agree (fun r => In r setsh_clob) regs r.
  Proof using LI16 G0 HMSET_OK HMSET HCODE.
    intros mem rom addr ra n H regs R1 R2 B Bg Hn Hnw Hok Hret Hh1 Hh2 Hh3 H10 H11 H1.
    rewrite <- (wbytes_mrestrict_at H _ mem addr n (repeat_length _ _) Hn ltac:(lia) Hh3).
    apply (setsh_run (mrestrict H mem) rom addr ra n regs); try assumption.
    - rewrite rdn_mrestrict; [exact R1 | wd_ulia_c | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); exact Hh1].
    - rewrite rdn_mrestrict; [exact R2 | wd_ulia_c | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); exact Hh2].
    - rewrite store_ok_mrestrict; [exact Hok | lia | intros x Hx; apply Hh3; lia].
  Qed.
End SETSH.
End FPGen1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.glaze.binary_reflection.images Require Import Asan.

Section FPGen2.
Context {fx : FPState}.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition asan_g_rms : Z := 0xff290.
Definition asan_p_rms : Z := 0x1011b0.

Record setshH (mem : word -> option byte) (addr ra : word) (n : Z) : Prop := SETSHH {
  ss_g_rms : rdn ASEGS mem (Z_to_bv 64 asan_g_rms) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 asan_p_rms));
  ss_rms : rdn ASEGS mem (Z_to_bv 64 asan_p_rms) 8 = Some (word_to_le_bytes 8 asan_memset_entry);
  ss_n : (0 <= n)%Z;
  ss_nw : (bv_unsigned addr + n < 2 ^ 64)%Z;
  ss_ok : store_ok ASEGS mem addr (Z.to_nat n) = true;
  ss_ret : ret_ok ra }.

Ltac setsh_inst base Fa Da Fl Dl Fli Dli :=
  intros mem rom addr ra n regs [R1 R2 Hn Hnw Hok Hret] H10 H11 H1;
  rewrite <- (at_0 base);
  eapply (setsh_run ASEGS base asan_memset_entry asan_g_rms asan_p_rms); try eassumption;
  [ (lazymatch goal with |- ?G => let G' := eval unfold setsh_words in G in change_no_check G' end); code_ato_vm
  | exact asan_memset_code
  | apply ret_ok_even; reflexivity
  | gload_tac Fa Da Fl Dl
  | intros rg mm rm; lit_pc;
    (chain_step; [reflexivity | eapply step_addi_at; [exact Fli | reflexivity | exact Dli | reflexivity | gres; reflexivity] | step_simpl]);
    close_refl
  | (lazymatch goal with |- ?G => let G' := eval unfold asan_p_rms in G in change_no_check G' end); lia ].



(* [comment removed for export] *)
Ltac setsh_inst_fp base Fa Da Fl Dl Fli Dli :=
  intros mem rom addr ra n H regs [R1 R2 Hn Hnw Hok Hret] Hh1 Hh2 Hh3 H10 H11 H1;
  rewrite <- (at_0 base);
  eapply (setsh_run_fp ASEGS base asan_memset_entry asan_g_rms asan_p_rms); try eassumption;
  [ (lazymatch goal with |- ?G => let G' := eval unfold setsh_words in G in change_no_check G' end); code_ato_vm
  | exact asan_memset_code
  | apply ret_ok_even; reflexivity
  | gload_tac Fa Da Fl Dl
  | intros rg mm rm; lit_pc;
    (chain_step; [reflexivity | eapply step_addi_at; [exact Fli | reflexivity | exact Dli | reflexivity | gres; reflexivity] | step_simpl]);
    close_refl
  | (lazymatch goal with |- ?G => let G' := eval unfold asan_p_rms in G in change_no_check G' end); lia
  | (lazymatch goal with |- ?G => let G' := eval unfold asan_g_rms in G in change_no_check G' end); lia ].

Theorem asan_set_shadow_f5_fp : forall mem rom (addr ra : word) (n : Z) (H : word -> bool) regs,
  setshH mem addr ra n ->
  hid_off H asan_g_rms 8 -> hid_off H asan_p_rms 8 -> hid_off H (bv_unsigned addr) n ->
  getr regs 10 = addr -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 = ra ->
  exists r,
    msteps ASEGS (mkst regs (0x703e4 : word) (mrestrict H mem) rom)
                 (mkst r ra (mrestrict H (wbytes mem addr (repeat (cbyte (Z_to_bv 64 245)) (Z.to_nat n)))) rom)
    /\ getr r 10 = addr /\ regs_agree (fun r => In r setsh_clob) regs r.
Proof using. setsh_inst_fp (0x703e4 : word) F_703dc D_703dc F_703e0 D_703e0 F_703ec D_703ec. Qed.


(* [comment removed for export] *)
End FPGen2.
