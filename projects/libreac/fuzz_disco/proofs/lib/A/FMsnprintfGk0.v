(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfGk0.v (a working branch 3e35620c52e); relocated to libreac/fuzz_disco.asan by reloc.py (target disco-A): module paths changed; 5 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table: this file's rows in provenance/evidence/g9-gxa/g9tool/g9-table-disco-A.tsv). *)
(* Hand fix (a Theorem Labs lane, 2026-10-29): g_ranges' first word count 39 -> 36: disco's __wrap_* trampoline block runs
   0x429c4 .. 0x42a54 (next function ___interceptor_strlen), 3 trampolines fewer than fm's (no strncmp / strncasecmp /
   strstr interceptors); the tool keeps counts as non-address numerals. The other four counts measure equal on disco A. *)
(* fm's snprintf glue, kit without any stack window (split out of FMsnprintfGk.v, which re-exports it): the code table
   of the walks above printf_core, their run and return steps, registers and stack slots read off a symbolic state,
   dropping and adding a region. New file. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YI00 YI16 YK06.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import FMH_Base FMsnprintfK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import FMsnprintfImg.
Import ListNotations.
Open Scope Z_scope.

(* ---- the code: all of musl, the __wrap_* trampolines, the vfprintf / vsnprintf / snprintf interceptors and
   TryAsanInitFromRtl (MEASURED word counts: the next function starts right after each range) ---- *)
Definition g_ranges : list (Z * nat) :=
  [(0x429c4, 36%nat); (0x45e14, 45%nat); (0x45ec8, 198%nat); (0x462b8, 28%nat); (0x5a0a0, 40%nat)].
Definition tbl_g : ctable := Eval vm_compute in build_ranges g_ranges tfibmusl_tbl.
Lemma tbl_g_eq : tbl_g = build_ranges g_ranges tfibmusl_tbl.
Proof. vm_cast_no_check (eq_refl tbl_g). Qed.
Lemma tbl_g_ok : table_ok tfibsegs tbl_g.
Proof.
rewrite tbl_g_eq. apply build_ranges_ok; [unfold g_ranges; repeat constructor; cbn; discriminate | exact tfibmusl_tbl_ok].
Qed.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma g_phase : forall (W : world tfibsegs) E ss ss' st ms md,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl_g FUEL ss = (ss', st) ->
  SRr tfibsegs W (mkCfg ms md)
    (fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
       match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
       | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
       frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1)).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_g tbl_g_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF _. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1 | exact HF].
Qed.
Lemma g_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_run_toN tfibsegs tbl_g FUEL stop ss = (ss', st) ->
  SRr tfibsegs W (mkCfg ms md)
    (fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
       match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
       | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
       frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1)).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_g tbl_g_ok AF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF _. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1 | exact HF].
Qed.
(* the return `ret` at the end of a walk *)
Lemma g_ret : forall (W : world tfibsegs) E ss ms md Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  clookup tbl_g (ss_pc ss) = Some RET_WORD_r ->
  (forall mat', Q W (mkCfg (mkst (ms_regs ms) (v_jalr (getr (ms_regs ms) 1) 0) (ms_mem ms) (seg_rom tfibsegs))
     (with_vm_backing (m_vm_lazy md) mat' md))) ->
  SRr tfibsegs W (mkCfg ms md) Q.
Proof. intros. eapply (SRr_ret_at tfibsegs tbl_g tbl_g_ok AF0x.Hwx_tfa); eassumption. Qed.

(* ---- registers and stack slots read off a symbolic state ---- *)
Lemma g_reg : forall (W : world tfibsegs) E ss ms (r : bv 5) v,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = v -> getr (ms_regs ms) r = sv_denot E v.
Proof. intros W E ss ms r v HS <-. exact (st_ok_reg_denot (w_H W) E ss ms r HS). Qed.
Lemma g_slot : forall (W : world tfibsegs) E ss ms i r off (n : N) e v,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros W E ss ms i r off n e v HS Hi Hc He Hv Hn.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
apply nth_error_In in Hi. pose proof (proj1 (Forall_forall _ _) Hrs r Hi) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck.
exact (val_of_chunk_ok tfibsegs E _ _ off n e v Hck He Hv Hn).
Qed.

(* ---- dropping and adding a region ---- *)
Definition set_mem (ss : sstate) (rs : smem) : sstate :=
  mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) rs (ss_resv ss) (ss_facts ss).
Lemma regions_wf_app : forall rs1 rs2, regions_wf (rs1 ++ rs2) = regions_wf rs1 && regions_wf rs2.
Proof. induction rs1 as [|r rs1 IH]; intros rs2; cbn; [reflexivity|]. rewrite IH. apply andb_assoc. Qed.
Lemma all_disjoint_app : forall E r rs1 rs2, all_disjoint E r (rs1 ++ rs2) <-> all_disjoint E r rs1 /\ all_disjoint E r rs2.
Proof. induction rs1 as [|r1 rs1 IH]; intros rs2; cbn; [tauto|]. rewrite IH. tauto. Qed.
Lemma all_disjoint_forall : forall E r rs, all_disjoint E r rs <-> Forall (extent_disjoint E r) rs.
Proof.
induction rs as [|r1 rs IH]; cbn; [split; [constructor | tauto]|]. rewrite IH. split.
- intros [H1 H2]. constructor; assumption.
- intros H. inversion H; subst. split; assumption.
Qed.
Lemma pairwise_disjoint_del : forall E rs1 r rs2, pairwise_disjoint E (rs1 ++ r :: rs2) -> pairwise_disjoint E (rs1 ++ rs2).
Proof.
intros E rs1 r rs2. induction rs1 as [|r1 rs1 IH]; cbn; [tauto|].
intros [H1 H2]. split; [|exact (IH H2)]. apply all_disjoint_app in H1 as [H1a H1b]. apply all_disjoint_app.
split; [exact H1a|]. cbn in H1b. tauto.
Qed.
Lemma st_ok_del : forall E ss ms rs1 r rs2,
  st_ok tfibsegs E ss ms -> ss_mem ss = rs1 ++ r :: rs2 -> st_ok tfibsegs E (set_mem ss (rs1 ++ rs2)) ms.
Proof.
intros E ss ms rs1 r rs2 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hm.
rewrite Hm in Hwf, Hok, Hpd. unfold st_ok, set_mem. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [|exact H9]. split; [|split].
- rewrite regions_wf_app in *. cbn [regions_wf] in Hwf. apply andb_prop in Hwf as [Ha Hb].
  apply andb_prop in Hb as [_ Hb]. rewrite Ha, Hb. reflexivity.
- apply Forall_app in Hok as [Ha Hb]. apply Forall_app. split; [exact Ha | exact (Forall_inv_tail Hb)].
- exact (pairwise_disjoint_del E rs1 r rs2 Hpd).
Qed.
Lemma extent_disjoint_sym : forall E r1 r2, extent_disjoint E r1 r2 -> extent_disjoint E r2 r1.
Proof. intros E r1 r2 H. unfold extent_disjoint in *. lia. Qed.
Lemma pairwise_disjoint_ins : forall E rs1 r rs2,
  pairwise_disjoint E (rs1 ++ rs2) -> Forall (extent_disjoint E r) (rs1 ++ rs2) ->
  pairwise_disjoint E (rs1 ++ r :: rs2).
Proof.
intros E rs1 r rs2. induction rs1 as [|r1 rs1 IH]; cbn; intros Hp Hd.
- split; [apply all_disjoint_forall; exact Hd | exact Hp].
- destruct Hp as [H1 H2]. inversion Hd as [|x l Hx Hl]; subst. split; [|exact (IH H2 Hl)].
  apply all_disjoint_app in H1 as [H1a H1b]. apply all_disjoint_app. split; [exact H1a|].
  cbn. split; [exact (extent_disjoint_sym E r r1 Hx) | exact H1b].
Qed.
Lemma st_ok_ins : forall E ss ms rs1 r rs2,
  st_ok tfibsegs E ss ms -> ss_mem ss = rs1 ++ rs2 -> region_wf r = true -> region_ok tfibsegs E (ms_mem ms) r ->
  Forall (extent_disjoint E r) (rs1 ++ rs2) ->
  st_ok tfibsegs E (set_mem ss (rs1 ++ r :: rs2)) ms.
Proof.
intros E ss ms rs1 r rs2 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hm Hrw Hro Hd.
rewrite Hm in Hwf, Hok, Hpd. unfold st_ok, set_mem. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [|exact H9]. split; [|split].
- rewrite regions_wf_app in *. cbn [regions_wf]. apply andb_prop in Hwf as [Ha Hb]. rewrite Ha, Hrw, Hb. reflexivity.
- apply Forall_app in Hok as [Ha Hb]. apply Forall_app. split; [exact Ha | constructor; assumption].
- exact (pairwise_disjoint_ins E rs1 r rs2 Hpd Hd).
Qed.
Lemma in_wrangeb_dec : forall E rs a, in_wrange E rs a \/ ~ in_wrange E rs a.
Proof.
intros E rs a.
destruct (existsb (fun r => (base_val E (YP09.r_base r) + YP09.r_wlo r <=? a) && (a <? base_val E (YP09.r_base r) + YP09.r_whi r))%bool rs) eqn:Eb.
- left. apply existsb_exists in Eb as (r & Hin & Hb). apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists r. split; [exact Hin | lia].
- right. intros (r & Hin & Ha).
  assert (X : existsb (fun r => (base_val E (YP09.r_base r) + YP09.r_wlo r <=? a) && (a <? base_val E (YP09.r_base r) + YP09.r_whi r))%bool rs = true).
  { apply existsb_exists. exists r. split; [exact Hin|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite X in Eb. discriminate Eb.
Qed.

End g.
