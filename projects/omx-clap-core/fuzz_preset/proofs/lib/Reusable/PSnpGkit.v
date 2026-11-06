(* fm's snprintf glue, kit: the code table of the walks above printf_core, their run and return steps, dropping and
   adding a region of a symbolic state, and the frame bookkeeping of FMsnprintfI's snk_frame across runs and calls.
   New file. *)
(* Modified by Theorem Labs, 2026-10: the image-free half of origin/cold/port-fm-rtprintf-param 7e395de08f5
   proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfGk.v for the chain restated over ARx (route (a), c-omx-hpreset
   10:51Z): the register / slot reads (:74-88) and the region kit (:91-119), with `tfibsegs` a Section variable segs
   (no image numeral). The code table and its run / return steps (:27-71) are image-bearing and live in
   lib/A/PSnpGk.v at preset image A. Items not reached by the four roots (snp_ok / svsni_ok / svsn_ok / svfi_ok):
   all_disjoint_forall, extent_disjoint_sym, pairwise_disjoint_ins, st_ok_ins, in_wrangeb_dec and the ARU-form
   g_frame_init / g_frame_step / g_frame_run (:157-228) are not ported. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI00 YI16 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {segs : list Segment}.

(* ---- registers and stack slots read off a symbolic state ---- *)
Lemma g_reg : forall (W : world segs) E ss ms (r : bv 5) v,
  st_ok segs E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = v -> getr (ms_regs ms) r = sv_denot E v.
Proof. intros W E ss ms r v HS <-. exact (st_ok_restrict_reg segs (w_H W) E ss ms r HS). Qed.
Lemma g_slot : forall (W : world segs) E ss ms i r off (n : N) e v,
  st_ok segs E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem segs (mrestrict (w_H W) (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros W E ss ms i r off n e v HS Hi Hc He Hv Hn.
pose proof (st_ok_mem_ok segs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
apply nth_error_In in Hi. pose proof (proj1 (Forall_forall _ _) Hrs r Hi) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck.
exact (val_of_chunk_ok segs E _ _ off n e v Hck He Hv Hn).
Qed.

(* ---- dropping a region ---- *)
Definition set_mem (ss : sstate) (rs : smem) : sstate :=
  mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) rs (ss_resv ss) (ss_facts ss).
Lemma regions_wf_app : forall rs1 rs2, regions_wf (rs1 ++ rs2) = regions_wf rs1 && regions_wf rs2.
Proof. induction rs1 as [|r rs1 IH]; intros rs2; cbn; [reflexivity|]. rewrite IH. apply andb_assoc. Qed.
Lemma all_disjoint_app : forall E r rs1 rs2, all_disjoint E r (rs1 ++ rs2) <-> all_disjoint E r rs1 /\ all_disjoint E r rs2.
Proof. induction rs1 as [|r1 rs1 IH]; intros rs2; cbn; [tauto|]. rewrite IH. tauto. Qed.
Lemma pairwise_disjoint_del : forall E rs1 r rs2, pairwise_disjoint E (rs1 ++ r :: rs2) -> pairwise_disjoint E (rs1 ++ rs2).
Proof.
intros E rs1 r rs2. induction rs1 as [|r1 rs1 IH]; cbn; [tauto|].
intros [H1 H2]. split; [|exact (IH H2)]. apply all_disjoint_app in H1 as [H1a H1b]. apply all_disjoint_app.
split; [exact H1a|]. cbn in H1b. tauto.
Qed.
Lemma st_ok_del : forall E ss ms rs1 r rs2,
  st_ok segs E ss ms -> ss_mem ss = rs1 ++ r :: rs2 -> st_ok segs E (set_mem ss (rs1 ++ rs2)) ms.
Proof.
intros E ss ms rs1 r rs2 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hm.
rewrite Hm in Hwf, Hok, Hpd. unfold st_ok, set_mem. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [|exact H9]. split; [|split].
- rewrite regions_wf_app in *. cbn [regions_wf] in Hwf. apply andb_prop in Hwf as [Ha Hb].
  apply andb_prop in Hb as [_ Hb]. rewrite Ha, Hb. reflexivity.
- apply Forall_app in Hok as [Ha Hb]. apply Forall_app. split; [exact Ha | exact (Forall_inv_tail Hb)].
- exact (pairwise_disjoint_del E rs1 r rs2 Hpd).
Qed.
End g.
