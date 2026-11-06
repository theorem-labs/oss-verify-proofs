From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP Arr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import CJBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require RStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G Require G_pad.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require Printf_text G_printf_core_common.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require G_sn_write G_snprintf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.I Require InstFmtP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import printf_facts_c snprintf_c snprintf_img_c snprintf.
Import ListNotations.
Open Scope Z_scope.

(* snprintf_img_contract from the released snprintf walk (snprintf.v, CJ G_snprintf): the same steps as
   snprintf_stk_holds with no stack arguments; the destination premise of G_snprintf is met by its globals window
   (GOT_GUARD_SLOT + 8 <= D, D + dn <= STACK_GUARD), which the instance maps to GOT_GUARD and GUARD. *)
Theorem snprintf_img_holds : snprintf_img_contract.
Proof.
  unfold snprintf_img_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary
         fmt ps args T junk.
  cbv zeta.
  intros BYF RLO REND PARSE PAOK TEXT DST Hn HT D0 DLO GLD GHI ST LO IMGLO SHI FRM MI TM GG GQ.
  destruct (text_ok _ _ _ _ _ _ fmt ps args T PAOK PARSE TEXT HT) as (MODEL & P1 & HF).
  assert (Edn : exists dn : nat, Z.of_nat dn = Z.min (Z.of_nat (length T)) (bv_unsigned a1 - 1) + 1)
    by (exists (Z.to_nat (Z.min (Z.of_nat (length T)) (bv_unsigned a1 - 1) + 1)); lia).
  destruct Edn as [dn Hdn].
  pose proof (task_bound m (bv_unsigned a0) _ junk MI TM DST ltac:(lia)) as DT.
  pose proof (proj2 (rw_cells_iff rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a1)) junk]) DST) as DST1.
  cbn [map cell_to] in DST1.
  replace (Z.to_nat (bv_unsigned a1)) with (dn + (Z.to_nat (bv_unsigned a1) - dn))%nat in DST1 by lia.
  destruct (G_sn_write.rw_CB_split _ _ _ _ _ _ DST1) as [DSTd _].
  unfold SNPRINTF_K, RO_LO, RO_END in *.
  pose proof (pargs_ok m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) dn ps args _ PAOK ltac:(lia) ltac:(lia))
    as AOK.
  pose proof (ssp_of_bytes m canary GG GQ) as SSP.
  pose proof (mem_inv_to_cj rsegs m MI TM) as MIc.
  pose proof c_got as CG. pose proof c_guard as CQ. unfold G_pad.got_ssp, G_pad.ssp_guard in CG, CQ.
  pose proof InstFmtP.N_snprintf as RS. unfold G_snprintf.snprintf_x_stmt in RS.
  specialize (RS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                 (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) dn (firstn dn junk) (fmt ++ [0]) []
                 (Printf_text.pf_pargs (map tpc ps) (map ta args)) lo canary (Prelim.zlength T) T).
  cbv zeta in RS. rewrite c_snprintf, c_gtop in RS. unfold G_printf_core_common.G_printf_iface.STATIC_SPLIT, G_snprintf.SNPRINTF_DEPTH in RS.
  unfold IMG_END, TASK_SIZE, GOT_GUARD, GUARD in *.
  specialize (RS (eq_sym (Z_to_bv_bv_unsigned a0)) (eq_sym (Z_to_bv_bv_unsigned a1)) (eq_sym (Z_to_bv_bv_unsigned a2))
                 DSTd Hdn BYF HF P1 (bytes_at_nil rsegs m (bv_unsigned sp) ltac:(lia))
                 ltac:(unfold Prelim.zlength; cbn [length]; lia) AOK MODEL Hn ST ltac:(lia) ltac:(lia) SHI SSP MIc FRM
                 ltac:(unfold Prelim.zlength; rewrite length_app; cbn [length]; lia) RLO D0
                 ltac:(lia) ltac:(unfold Prelim.zlength; cbn [length]; lia) ltac:(lia)).
  eapply evt_bridge; [| exact RS].
  intros ms' P. exact (post_of_cj ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo (bv_unsigned a0) (bv_unsigned a1) dn
                         T m canary ms' (proj1 Hn) Hdn P).
Qed.

(* Satisfiability at the real instance (a Theorem Labs lane 21:4xZ rule): the call snprintf(g_names[k], 8, "nl%d", k) of
   interfaces() (LLVMFuzzerTestOneInput, jal snprintf at 0x138e0; a0 = g_names + 8 k, a1 = 8, a2 = 0x10483, a3 = k)
   meets the new premises at link's own symbols. g_names is OBJECT 0x741f8, 512 bytes, in link's plain symbol table;
   "nl%d" is at .rodata 0x10483. *)
Definition G_NAMES : Z := 0x741f8.
Definition NL_FMT : Z := 0x10483.
Definition nl_fmt : list Z := [110; 108; 37; 100].

Lemma g_names_rw : forallb (fun i => match find_segment rsegs (G_NAMES + Z.of_nat i) 1 with
                                     | Some s => seg_writable s | None => false end) (seq 0 512) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nl_fmt_ro : forallb (fun i => ro_addr rsegs (wa (NL_FMT + Z.of_nat i))) (seq 0 5) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nl_fmt_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m NL_FMT (pf_bytes (nl_fmt ++ [0])).
Proof.
  intros m MI. split; [unfold NL_FMT; lia|]. split; [cbn [pf_bytes nl_fmt app map length Z.of_nat]; unfold NL_FMT; lia|].
  intros i Hi. cbn [pf_bytes nl_fmt app map length] in Hi.
  assert (RO : ro_addr rsegs (wa (NL_FMT + Z.of_nat i)) = true).
  { pose proof nl_fmt_ro as R. rewrite forallb_forall in R. apply R. apply in_seq. lia. }
  unfold mrd. destruct (m (wa (NL_FMT + Z.of_nat i))) as [b|] eqn:E.
  { apply MI in E. rewrite RO in E. discriminate. }
  do 5 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma nl_fmt_parse : pf_parse nl_fmt = Some [PLit 110; PLit 108; Pd].
Proof. reflexivity. Qed.

Lemma nl_text : forall k, pf_text [PLit 110; PLit 108; Pd] [AInt k] = Some (110 :: 108 :: pf_dec k ++ []).
Proof. intros k. reflexivity. Qed.

Lemma nl_dec_len : forall k, 0 <= k < 64 -> (length (pf_dec k) <= 2)%nat.
Proof.
  intros k Hk. unfold pf_dec. replace (k <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [pf_digits]. destruct (k <? 10) eqn:E1; [cbn; lia|].
  apply Z.ltb_ge in E1. cbn [pf_digits].
  replace (k / 10 <? 10) with true by (symmetry; apply Z.ltb_lt; apply Z.div_lt_upper_bound; lia).
  cbn. lia.
Qed.

Lemma snprintf_img_g_names_sat : forall k, 0 <= k < 64 ->
  let D := G_NAMES + 8 * k in
  0 < D /\ GOT_GUARD + 8 <= D /\ D + 8 <= GUARD /\ D + 8 <= IMG_END /\
  @G_pad.got_ssp InstFmtP.N_img_fmt + 8 <= D /\ D + 8 <= @G_pad.ssp_guard InstFmtP.N_img_fmt /\
  RO_LO <= NL_FMT /\ NL_FMT + Z.of_nat (length nl_fmt) + 1 <= RO_END /\
  (forall m, mem_inv rsegs m -> bytes_at rsegs m NL_FMT (pf_bytes (nl_fmt ++ [0]))) /\
  pf_parse nl_fmt = Some [PLit 110; PLit 108; Pd] /\
  (exists T, pf_text [PLit 110; PLit 108; Pd] [AInt k] = Some T /\ Z.of_nat (length T) < 8).
Proof.
  intros k Hk. cbv zeta. rewrite c_got, c_guard.
  pose proof (nl_dec_len k Hk) as L.
  unfold G_NAMES, GOT_GUARD, GUARD, IMG_END, RO_LO, RO_END, NL_FMT.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [cbn; lia|]. split; [exact nl_fmt_bytes|]. split; [exact nl_fmt_parse|].
  exists (110 :: 108 :: pf_dec k ++ []). split; [apply nl_text|].
  cbn [length]. rewrite length_app. cbn [length]. lia.
Qed.
