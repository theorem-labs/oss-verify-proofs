(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* The code the sprintf walk steps through, and the step lemmas of its symbolic runs.
   Measured on the pinned fuzz_command.asan (objdump; the disassembler on ___interceptor_sprintf,
   ___interceptor_vsprintf, vsprintf):
   - the trampoline 0x451cc (`j 0x49f74`),
   - ___interceptor_sprintf 0x49f74 (36 words, to 0x4a004),
   - ___interceptor_vsprintf 0x49bbc (184 words, to 0x49e9c),
   - musl vsprintf 0x9e194 (5 words: mv a3,a2; mv a2,a1; lui a1,0x80000; addiw a1,a1,-1; j 0x451c4),
   - the vsnprintf trampoline 0x451c4 (`j 0x498a4`), so run B ends at ___interceptor_vsnprintf 0x498a4, where the
     route's vsnprintf-interceptor contract is proved (omx-clap-core/fuzz_manifest's FMsnprintfSvsni.svsni_ok at A_VSNI),
   - __asan::TryAsanInitFromRtl 0x5f68c (40 words).
   printf_common 0x48d28, ___interceptor_vsnprintf 0x498a4 and the range check 0x5a1f8 are NOT in the table: a run
   stops at their entry and the walk uses their contracts.
   The read-only cells the runs read (each a const cell of the per-binary record, rodata_chk): AE2y's icpt_rodata
   (TryAsanInitFromRtl's init cells), the GOT word 0xa5f40 -> common_flags 0x142768, the check_printf flag byte
   0x142768 + 84 = 0x1427bc (1), and REAL(vsprintf)'s slot 0xa7d00 -> 0x9e194. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition spf_ranges : list (Z * nat) :=
[(0x451cc, 1%nat); (0x49f74, 36%nat); (0x49bbc, 184%nat); (0x9e194, 5%nat); (0x451c4, 1%nat); (0x5f68c, 40%nat)].
Definition tbl_spf : ctable := Eval vm_compute in build_ranges spf_ranges TEmpty.
Lemma tbl_spf_eq : tbl_spf = build_ranges spf_ranges TEmpty. Proof. vm_cast_no_check (eq_refl tbl_spf). Qed.
Lemma tbl_spf_ok : table_ok tfibsegs tbl_spf.
Proof.
rewrite tbl_spf_eq. apply build_ranges_ok; [unfold spf_ranges; repeat constructor; cbn; discriminate | exact (table_ok_empty tfibsegs)].
Qed.
Lemma tbl_spf_probe : clookup tbl_spf 0x48d28 = None /\ clookup tbl_spf 0x498a4 = None /\ clookup tbl_spf 0x5a1f8 = None
/\ clookup tbl_spf 0x451cc = Some 0x5a90406f /\ clookup tbl_spf 0x451c4 = Some 0x6e00406f.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition spf_rodata : list (Z * Z * list (Z * N * Z)) :=
icpt_rodata ++ [(0xa5f40, 8, [(0, 8%N, 0x142768)]); (0x1427bc, 1, [(0, 1%N, 1)]); (0xa7d00, 8, [(0, 8%N, 0x9e194)])].
Lemma spf_rodata_chk : forall ly, rodata_chk ly spf_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
(* every read-only region lies below the image's end, has no writable window and no chunk outside it *)
Definition ro_low_b (r : YP09.region) : bool :=
region_wf r && obase_eqb (YP09.r_base r) None && (0x10000 <=? YP09.r_lo r) && (YP09.r_hi r <=? 0x200000) &&
(YP09.r_whi r <=? YP09.r_wlo r).
Lemma spf_ro_low_chk : forallb ro_low_b (map ro_region spf_rodata) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma spf_ro_low : forall r, In r (map ro_region spf_rodata) ->
  region_wf r = true /\ YP09.r_base r = None /\ 0x10000 <= YP09.r_lo r /\ YP09.r_hi r <= 0x200000 /\
  YP09.r_whi r <= YP09.r_wlo r.
Proof.
intros r Hr. pose proof (proj1 (forallb_forall _ _) spf_ro_low_chk r Hr) as H. unfold ro_low_b in H.
apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
apply andb_prop in H as [H1 H2]. apply obase_eqb_eq in H2.
apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5. tauto.
Qed.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma spf_phase : forall (W : world tfibsegs) E ss ss' st ms md,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl_spf FUEL ss = (ss', st) ->
  SRr tfibsegs W (mkCfg ms md)
    (fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
       match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
       | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
       frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1)).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_spf tbl_spf_ok YF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF _. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1 | exact HF].
Qed.
Lemma spf_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_run_toN tfibsegs tbl_spf FUEL stop ss = (ss', st) ->
  SRr tfibsegs W (mkCfg ms md)
    (fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
       match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
       | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
       frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1)).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_spf tbl_spf_ok YF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF _. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1 | exact HF].
Qed.
(* the return `ret` at the end of the walk *)
Lemma spf_ret : forall (W : world tfibsegs) E ss ms md Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  clookup tbl_spf (ss_pc ss) = Some RET_WORD_r ->
  (forall mat', Q W (mkCfg (mkst (ms_regs ms) (v_jalr (getr (ms_regs ms) 1) 0) (ms_mem ms) (seg_rom tfibsegs))
     (with_vm_backing (m_vm_lazy md) mat' md))) ->
  SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros W E ss ms md Q HS Hrv Hlk HQ.
exact (SRr_ret_at tfibsegs tbl_spf tbl_spf_ok YF0x.Hwx_tfa W E ss ms md Q HS Hrv Hlk HQ).
Qed.
(* registers and stack slots read off a symbolic state *)
Lemma spf_reg : forall (W : world tfibsegs) E ss ms (r : bv 5) v,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = v -> getr (ms_regs ms) r = sv_denot E v.
Proof. intros W E ss ms r v HS <-. exact (st_ok_reg_denot (w_H W) E ss ms r HS). Qed.
Lemma spf_slot : forall (W : world tfibsegs) E ss ms i r off (n : N) e v,
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
End g.

(* st_ok reads the FP state only through mkst's own fields (fuzz_manifest's FMsnprintfSk.v st_ok_fx) *)
Lemma st_ok_fx : forall (fx1 fx2 : YK11.FPState) E ss regs pc mem,
  st_ok (fx:=fx1) tfibsegs E ss (mkst (fx:=fx1) regs pc mem (seg_rom tfibsegs)) ->
  st_ok (fx:=fx2) tfibsegs E ss (mkst (fx:=fx2) regs pc mem (seg_rom tfibsegs)).
Proof.
intros fx1 fx2 E ss regs pc mem (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
split; [reflexivity|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [reflexivity|].
split; [exact H6|]. split; [exact H7|]. split; [exact H8 | exact H9].
Qed.
