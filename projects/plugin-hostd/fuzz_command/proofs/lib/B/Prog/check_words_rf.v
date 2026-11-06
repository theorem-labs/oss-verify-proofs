(* check_words' ASan+UBSan walk: the record facts its segment files carry as Section hypotheses (check_words_d.v's
   *_P), proved from the CmdRecFacts lemmas (lib/B/Prog/CmdRecBase.v, CmdRecCells.v, CmdRecRo.v, CmdRecImg.v), so
   the final theorem discharges them by `exact` and names only the walk hypotheses and CmdRecFacts.v's facts. Each
   list fact is one boolean check closed by vm_compute (no destruct over a per-binary list). The B twin of
   lib/A/Prog/check_words_rf.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the two closed checks over check_words' image ranges CW_ZSH (check_words_d.v) *)
Definition cw_zsh_b : bool :=
  forallb (fun an => cmd_addr_b (fst an) (snd an) && cmd_hull_b (fst an) (snd an)) CW_ZSH.
Lemma cw_zsh_b_ok : cw_zsh_b = true.
Proof. vm_compute. reflexivity. Qed.
(* every range of CW_ZSH but g_rec lies inside one of CmdRo's objects *)
Definition cw_in_ro_b : bool :=
  forallb (fun an => (fst an =? A_G_REC) ||
    existsb (fun r => (fst r <=? fst an) && (fst an + snd an <=? fst r + snd r)) cmd_ro_objs) CW_ZSH.
Lemma cw_in_ro_b_ok : cw_in_ro_b = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cw_in_ro : forall a n i, In (a, n) CW_ZSH -> a <> A_G_REC -> 0 <= i < n -> Exists (in_zr (a + i)) cmd_ro_objs.
Proof.
intros a n i Hin Hne Hi.
pose proof (proj1 (forallb_forall _ _) cw_in_ro_b_ok (a, n) Hin) as Hb. cbn [fst snd] in Hb.
apply orb_prop in Hb as [Hb|Hb]; [apply Z.eqb_eq in Hb; contradiction|].
apply existsb_exists in Hb as (r & Hr & Hc). apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
apply Exists_exists. exists r. split; [exact Hr|]. unfold in_zr. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.

Lemma cw_rf_rec_cells : cmd_rec_cells_P B.
Proof. exact (cmd_rec_cells SEGS B LAWS HB IMG). Qed.
Lemma cw_rf_tail_vis : cmd_tail_vis_P B.
Proof. exact (cmd_tail_vis_at SEGS B LAWS HB IMG). Qed.
Lemma cw_rf_zsh : CW_ZSH_P B.
Proof.
intros ly S W mem md a n HAR Hin.
pose proof (proj1 (forallb_forall _ _) cw_zsh_b_ok (a, n) Hin) as Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [H1 H2].
exact (cmd_aread_ok_chk SEGS B LAWS HB ly S W mem md a n HAR H1 H2).
Qed.
Lemma cw_rf_ro_unowned : cw_ro_unowned_P B.
Proof.
intros a n i Hin Hne Hi. pose proof (cw_in_ro a n i Hin Hne Hi) as Hx.
split; [exact (cmd_ro_in_to _ (cif_ro_img SEGS B IMG) (a + i) Hx)|].
exact (cmd_ro_in_to _ (cif_ro_unowned SEGS B IMG) (a + i) Hx).
Qed.
Lemma cw_rf_heap_tail_vis : cmd_heap_tail_vis_P B.
Proof. exact (cmd_heap_tail_vis SEGS B LAWS HB). Qed.
Lemma cw_rf_prog_unowned : cmd_prog_unowned_P B.
Proof. exact (cmd_prog_unowned SEGS B LAWS HB IMG). Qed.
Lemma cw_rf_rom_view_on : cmd_rom_view_on_P B.
Proof. exact (cmd_rom_view_on SEGS B LAWS HB IMG CMD_RLO CMD_RHI). Qed.
Lemma cw_rf_got_rec : cmd_got_rec_P B.
Proof. exact (cmd_got_rec SEGS B LAWS HB IMG). Qed.
Lemma cw_rf_rro : RRO_P.
Proof. exact (RRO SEGS B LAWS HB IMG). Qed.
End e.
End f.
End d.
