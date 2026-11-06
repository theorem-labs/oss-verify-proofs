From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells codec_main_inv
  check_personality_c LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Lemma codec_main_entry : S_entry.
Proof.
  unfold S_entry, entry_goal, st.
  intros CP e HE EX HEAD t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HN.
  pose proof HE as (HD & HMI & ST & HLO & SPA & DJ & HPB & HR & HDJ).
  unfold LLVM_CODEC_STACK, LLVM_CODEC in *.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 (e_p e)) as Rp. unfold bv_modulus in Rp.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
  pose proof ST as [Hlo0 _].
  assert (MU : munch [(bv_unsigned (e_sp e) - 592, bv_unsigned (e_sp e))] (e_m e) (e_m e)) by apply munch_refl.
  assert (WM : wmono rsegs (e_m e) (e_m e)) by apply wmono_refl.
  clear HD HR.
  zstep.
  carve_frame 400%nat ST.
  do 13 zstep.
  destruct (rw_cells_app_split _ (bv_unsigned (e_sp e) + -400) [CB 296 _] (saved e) ltac:(exact FR)) as [F296 SV].
  cbn [cells_size csize Nat.add] in SV.
  replace (bv_unsigned (e_sp e) + -400 + Z.of_nat 296) with (bv_unsigned (e_sp e) + -104) in SV by lia.
  clear FR.
  zstep. zstep. zstep.
  if_cases EBIG.
  2: { zify_cond EBIG. zstep.
       eapply EX; [ | exact F296 | ]; [ reflexivity | ].
       split; [exact SV|]. split; [exact ST|]. split; [|split; [exact WM | exact HMI]].
       unfold LLVM_CODEC_STACK. exact MU. }
  zify_cond EBIG.
  assert (HN0 : bv_unsigned a1 < 2 ^ 26)
    by (rewrite Z.shiftr_div_pow2 in EBIG by lia; Z.div_mod_to_equations; lia).
  zstep. zstep.
  unfold check_personality_contract, CHECK_PERSONALITY, CHECK_PERSONALITY_DEPTH in CP.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -400)) = bv_unsigned (e_sp e) + -400)
    by (apply unsigned_lit; lia).
  call CP.
  { unfold check_personality_pre, CHECK_PERSONALITY_DEPTH. rewrite unsigned_lit by lia.
    split; [ exact (relro_of_munch e _ HE MU) | ].
    split; [ apply (callee_relro_disj e); [exact HE | lia] | ].
    split; [ assumption | ]. split; [ assumption | lia ]. }
  rewrite ?USP in *.
  zstep. zstep.
  if_cases EN0.
  2: { zify_cond EN0. zstep.
       eapply EX; [ | eassumption | ]; [ reflexivity | ].
       exact (conj SV (conj POST (conj MU (conj WM MI)))). }
  zify_cond EN0.
  do 17 zstep.
  rewrite <- (Z_to_bv_bv_unsigned a1).
  assert (Ep : e_p e = Z_to_bv 64 (bv_unsigned (e_p e) + 0))
    by (rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned).
  match goal with H : rw_cells _ _ (bv_unsigned (e_sp e) + -400) _ |- _ => rewrite Ep in H end.
  unfold head_ok, st, body_regs in HEAD.
  eapply HEAD with (c := 0); [ | | | eassumption | exact (conj SV (conj POST (conj MU (conj WM MI)))) ].
  - split; rewrite unsigned_lit by lia; lia.
  - lia.
  - unfold cur_ok. lia.
Qed.
