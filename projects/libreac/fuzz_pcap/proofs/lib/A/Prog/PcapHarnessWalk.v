(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapSourceClose.v: pcap_source_close (fuzz_pcap.asan-ubsan
   0x81d4c, listing offset AF_pcap_source_close = 0x15c4, 31 instructions) on libreac v1.9.0's ASan+UBSan build, walked
   against lib/A's contract.

   The code is lib/A's ASan code (fuzz_pcap.asan 0x81e90, 27 instructions) with two UBSan guards and a register swap
   (measured: pcap-ubsan-inventory.md (sha256 5b607b62e337; internal record), row G6 and the pcap_source_close row of (c)). After
   the 32-byte frame and the saves of ra, s0 and s1, 0x81d5c `beqz a0` branches to the `unimp` at 0x81db4 when ps is
   null, 0x81d60 `mv s0,a0` (above the GOT load here), and 0x81d64 `andi a0,a0,7` / 0x81d68 `bnez a0` branch to the same
   `unimp` when ps is not 8-aligned. The shadow base is then loaded through the GOT word 0x996f8 (object 1; through a0,
   where the ASan code uses a1) from the cell 0xa17b8 (object 15). The rest is the ASan code at other pcs: the shadow
   check of ps's 8 bytes (0x81d80 `lbu`, 0x81d84 `bnez` to the error path at 0x81db8), f = ps->f (0x81d88), the test of
   f (0x81d8c `beqz` to 0x81da0), the call of the fclose wrapper's 4-byte jump (0x81d90 `jal
   __interceptor_trampoline_fclose`, 0x4161c), the second shadow check (0x81d94, 0x81d98 `bnez` to the error path at
   0x81dc0), ps->f = NULL (0x81d9c `sd zero,0(s0)`), the restores and the return (0x81db0).

   THE GUARDS. The walk's first symbolic run decides both, from the facts on a0 = ps that cl_entry proves (atom 10: ps
   >= 4096 and ps mod 2^3 = 0; ps >= 4096 because ps lies in a frame of the caller (frames_bounds), which gives the
   statement's ps <> 0; the alignment is the statement's ps mod 8 = 0):
     0x81d5c: decide_cond2 (Reusable/YP0e.v:932) through decide_eq (Reusable/YP0m.v:658-672), whose SOff / SLit arm
              (:665-666) tests ranges_disjoint (:653): ps's range [4096, ...] is disjoint from 0, so the branch is not
              taken;
     0x81d68: s_and_ptr (Reusable/YP0m.v:969-980) rewrites ps & 7 to 0 from the alignment fact, so `bnez` sees 0 and is
              not taken.
   These are the decisions of the released UBSan proof for the v1.8 image (proofs/libreac/fuzz_pcap/lib/U/Prog/
   pcap_source_close.v on origin/ossv/recipes c8557374ad2e): close_closed :43 (if_false, premise bv_unsigned a0 <> 0 at
   :23) and :45-46 (ub_align A8, premise bv_unsigned a0 mod 8 = 0 at :23), close_pro :82 and :84-85 (premises :58).

   The contract is lib/A's, not a copy (the shared-text rule): pb_pcap_source_closeX proves lib/A's image-generic
   AC.tpcap_source_close_specX (with AC.tpcap_source_close_post and AC.tclose_kept) at this image's segments SEGS and
   relro window pa_relro_lo / pa_relro_hi of the lib/B PAImg instance (on the pin PcapRelro.PCAP_RLO /
   PcapRelro.PCAP_RHI, lib/B/Prog/PcapRelro.v), at a = BASE + AF_pcap_source_close of the lib/B listing. The image-free constants
   (TPCAP_SOURCE_CLOSE_STK, EV_CLOSE, tclose_fblk) and lemmas are lib/A's too, through AC. The fclose wrapper's contract
   is the Section hypothesis AFCLOSE, of lib/A/Stdio/PFclose.v's image-generic afclose_source_spec type at this image.
   There is no lib/B/Stdio/PFclose.v (that statement takes the image as parameters). AFCLOSE is discharged by the
   asan-ubsan instance of a Theorem Labs lane's fclose walk lib/A/Stdio/WFclose.v, whose lib/B walk twin is
   lib/B/Stdio/WFclose.v (lib/B/Stdio/PFcloseInstB.v's inst_AFCLOSE_U composes it with lib/B/Stdio/WFcloseI.v).
   getr / mkst / seg_rom come from YK11; nothing from lib/Lib is imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceClose.v, with its module names changed; 3497 of its 3557 lines of code are new or changed and 570 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessTail.v; 743 of its 863 lines of code are new or changed and 3437 lines of the source are left out. *)
(* The record walk of fuzz_pcap's entry function LLVMFuzzerTestOneInput on the ASan build of libreac v1.9.0,
   from the cut PP_KD (0x80af4, the first pcap_source_next returned) to the cut PP_K5 (0x8107c, the record loop
   is done).

   The cuts, the machine data every cut carries and the shape a phase lemma has are NOT this file's: they are
   lib/A/Prog/PcapEntryDefs.v (pe_base / pe_body / pe_from / pe_post) and lib/A/Prog/PcapEntryPhases.v
   (GI_KD, GI_K4, GI_KL2, GI_K5), which the harness lanes share. This file proves

     pe_Walk   : pe_from POST GI_K5 -> pe_from POST GI_KD                       (the walk, for every POST)
     pe_KD_at  : pe_from POST GI_K4 -> pe_from POST GI_K5 -> pe_from POST GI_KD  (PP_KD: blez, the prologue)
     pe_KL2_at : at_cut GI_K4 POST n -> pe_from POST GI_K5 -> at_cut GI_KL2 POST n  (the loop's exit, PP_KL2)

   The record loop itself, PP_K4 -> PP_K5 (the skip loop PP_KR, the bcmp calls 0x80d8c / 0x80da8 / 0x80e08, the
   loop's pcap_source_next 0x80fa0, the back edge 0x80fac and the induction on the plain model's record walk), is
   pe_WalkR in lib/A/Prog/PcapHarnessWalkR.v, which Requires this file (its at_cut, pe_KL2_at and the transport
   helpers below); pe_Walk takes it as the Section hypothesis WALKR, and lib/A/Prog/PcapEntryFinal.v composes the
   two. The plain model (PcapEntryPhases' psn_q / kind / res_of / pos_of) and lib/Prog/Slot/PWalk.v's model lemmas
   are Required, never Imported; no slot contract is used (rule 24).

   No ASan check lies in this file's own segments (0x80af4 .. 0x80b34 and 0x81074 .. 0x8107c: the prologue's three
   stores are spill stores to s1), and no frame-kind branch either: the frame is the cut's pF on both arms (the
   machine-frame arm is refuted in the prologue lane, from AR_const_law and the stack_malloc rule).

   Every number is read from the pinned fuzz_pcap.asan image
   (sha256 b7a91d9b1fb0017d...; symbols from its unstripped twin, capstone 5 disassembly). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase YC4b YC81 YC1g YC1h YC85 PcapFrame PcapEntry PcapEntryA PcapEntryDefs PcapEntryPhases PcapSourceClose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
(* The harness's journal: the donor's, plus the program-global ranges its own stores change (pe_G). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journal.
(* The plain model of the walk, required and never imported. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require PWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module PW := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.
(* AE2f (cgif's text, required transitively) turns zify's euclidean-division equations off globally; this walk's
   division goals (the realigned stack pointer, an address's shadow) are discharged with explicit div lemmas, so
   plain `lia` on linear goals is kept (setting the flag true breaks linear lia with "No applicable tactic"). *)

(* ---- the shape of a machine state at a cut ---- *)

Lemma ms_of_body : forall {fx : YK11.FPState} (ms : machine_state) (pc : Z) (rom : word -> option byte),
  ms_pc_val ms = w64 pc -> ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = rom ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) rom.
Proof.
  intros fx ms pc rom Hpc Hrv Hsv Hrom Hfr Hcsr.
  destruct ms as [regs fregs pcv svc resv fcsr mem rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in *.
  subst. unfold w64, mkst. reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* SK is explicit: the closure of sink_head is the plain build's, so it must never be inferred. *)
Context (SK : OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sink_head).
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Notation VAL := (@pa_val _ pcap_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Notation BASE := (@pa_val _ pcap_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

Hypothesis LAWS : AR_laws SEGS B.
(* The stream's environment bytes are image bytes outside the owned statics and errno (PSourceMeta); the
   composition (PcapEntryTop.v) holds it as its own Section hypothesis ASIL. *)
Hypothesis ASIL : asource_img_laws SK SEGS B KS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_pcap) (PI := PI).

(* gx_ok for the harness's two globals is a fact about B alone; every phase gets it from its own pe_base
   (hw_gx_of_base below), and the run chain of W_journal.v needs it at the point where RUN is built.  The phase
   lemmas therefore live in Section g, which takes it; pe_Walk, after Section g, takes it from pe_base for each
   call. *)
Section g.
Hypothesis HGX : gx_ok SEGS B pe_G.
Let RUN := paj_run_x B LAWS pe_G HGX 0 [].
Let RUNTO := paj_run_to_x B LAWS pe_G HGX 0 [].

(* The shadow base, as the walk's token engine needs it: one atom (32) that holds SHADOW_OFF, and the band of
   shadow addresses the engine may touch. *)
Definition HW_SB : Z := 0x7fff8000.
Definition HWBx : sv := SOff 32 0.
Definition HWspan : Z * Z := (HW_SB, HW_SB + 2 ^ 44 - 1).
Lemma HW_SB_eq : HW_SB = SHADOW_OFF.
Proof. reflexivity. Qed.

(* ---- the phase goals, with the loop measure the two loops decrease ---- *)

(* The position the harness is at: s2 (register 18) holds it at PP_K4, PP_KR and PP_KL2. *)
Definition hw_pos (ms3 : machine_state) : Z := bv_unsigned (getr (ms_regs ms3) 18).
Definition hw_meas (cx : ecx) (ms3 : machine_state) : nat := Z.to_nat (p_nF cx - hw_pos ms3).

Definition at_cut (GI : ecx -> Z -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop)
  (POST : ecx -> world SEGS -> config -> Prop) (n : nat) : Prop :=
  forall (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  GI cx fp k acc ly3 S3 W3 ms3 md3 ->
  (hw_meas cx ms3 <= n)%nat ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).

Lemma at_cut_mono : forall GI POST n m, (n <= m)%nat -> at_cut GI POST m -> at_cut GI POST n.
Proof.
  intros GI POST n m Hnm H cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HG Hn.
  exact (H cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HG ltac:(lia)).
Qed.

(* ---- the symbolic state of a cut whose run touches no memory ---- *)

(* No region: such a run stores nothing, so `frame_of` over the empty region list gives back the memory
   function itself. *)
Definition hw_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

Lemma hw_entry0 : forall (W3 : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) pc,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 HW_SB])) (hw_ss0 pc)
    (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros W3 regs mem pc. rewrite restrict_mkst_fx. unfold hw_ss0.
  apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - unfold facts_ok; cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I].
Qed.

Lemma hw_entry_body : forall (W3 : world SEGS) (ms3 : machine_state) pc,
  ms_pc_val ms3 = w64 (BASE + pc) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) [w64 HW_SB])) (hw_ss0 pc) (restrict (w_H W3) ms3).
Proof.
  intros W3 ms3 pc Hpc Hrv Hsv Hrom Hfr Hcsr.
  destruct ms3 as [rg fg pcv svc resv fcsr mm rom].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in *.
  subst. exact (hw_entry0 W3 rg mm pc).
Qed.

Lemma hw_sh_nil : forall (E : env) (m : word -> option byte), sh_ok SEGS HWBx [] E m.
Proof. intros E m. unfold sh_ok. apply Forall_nil. Qed.

(* The model a run leaves: the descriptors and the file system are the ones it started from. *)
Lemma hw_md_fds : forall (md : Model) (mat : list word),
  m_fds (with_vm_backing (m_vm_lazy md) mat md) = m_fds md /\
  m_fs (with_vm_backing (m_vm_lazy md) mat md) = m_fs md.
Proof.
  intros md mat.
  destruct (same_but_materialized_frame md (with_vm_backing (m_vm_lazy md) mat md)
    (with_vm_backing_same md mat)) as (_ & _ & _ & _ & _ & _ & _ & _ & Hfds & _ & _ & Hfs & _).
  split; [exact Hfds | exact Hfs].
Qed.

(* A run with no region keeps the memory function itself. *)
Lemma hw_mem_kept : forall (E : env) (rs : smem) (m m' : word -> option byte),
  rs = [] -> frame_of E rs m m' -> m' = m.
Proof.
  intros E rs m m' -> HF. apply functional_extensionality. intros x. apply HF.
  intros (r & Hin & _). destruct Hin.
Qed.

(* The fields of a machine state the engine leaves, read off its shape. *)
Lemma hw_fields_of_shape : forall (ms : machine_state) (regs : bvmap 5 word) pc mem,
  ms = mkst regs (Z_to_bv 64 pc) mem (seg_rom SEGS) ->
  ms_pc_val ms = w64 pc /\ ms_resv ms = None /\ ms_svc_pending ms = None /\
  ms_rom ms = seg_rom SEGS /\ ms_fregs ms = fp_regs /\ ms_fcsr ms = fp_csr.
Proof. intros ms regs pc mem ->. repeat split; reflexivity. Qed.

(* A signed branch, as the walk reads it. *)
Lemma hw_branch_lt : forall (E : env) a b,
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros E a b. cbn [branch_taken]. unfold bv_lts, Sg. reflexivity. Qed.

Lemma hw_sg_reg : forall (E : env) (i : nat) (v : Z),
  ew E i = w64 v -> - 2 ^ 63 <= v < 2 ^ 63 -> Sg E (SOff i 0) = v.
Proof.
  intros E i v Hv Hr. unfold Sg. cbn [sv_denot]. rewrite Hv. unfold w64.
  rewrite unsigned_lit, Z.add_0_r, Z_to_bv64_canon, signed_lit, bv_swrap_wrap'.
  apply swrap64_id. unfold half64. lia.
Qed.

Lemma hw_sg_lit0 : forall (E : env), Sg E (SLit 0) = 0.
Proof. intros E. reflexivity. Qed.

Lemma hw_branch_ge : forall (E : env) a b,
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. intros E a b. cbn [branch_taken]. unfold bv_lts, Sg. reflexivity. Qed.

(* gx_ok for pe_G, read off any phase's pe_base. *)
Lemma hw_gx_of_base : forall cx, pe_base SK B MT KS cx -> gx_ok SEGS B pe_G.
Proof.
  intros cx HB. unfold pe_base in HB. tauto.
Qed.

(* ---- what a cut's memory facts need: the memory function, not the machine state ---- *)

Lemma hw_pslot_mem : forall cx W3 (ms ms' : machine_state) off v,
  ms_mem ms' = ms_mem ms -> pslot cx W3 ms off v -> pslot cx W3 ms' off v.
Proof. intros cx W3 ms ms' off v Hm H. unfold pslot in *. rewrite Hm. exact H. Qed.

Lemma hw_pslots_mem : forall cx fp W3 (ms ms' : machine_state),
  ms_mem ms' = ms_mem ms -> pslots cx fp W3 ms -> pslots cx fp W3 ms'.
Proof. intros cx fp W3 ms ms' Hm H. unfold pslots, pslot in *. rewrite Hm. exact H. Qed.

Lemma hw_plslots_mem : forall cx fp W3 (ms ms' : machine_state) buf,
  ms_mem ms' = ms_mem ms -> p_lslots cx fp W3 ms buf -> p_lslots cx fp W3 ms' buf.
Proof. intros cx fp W3 ms ms' buf Hm H. unfold p_lslots, pslots, pslot in *. rewrite Hm. exact H. Qed.

Lemma hw_pglob_mem : forall cx W3 (ms ms' : machine_state) src,
  ms_mem ms' = ms_mem ms -> p_glob cx W3 ms src -> p_glob cx W3 ms' src.
Proof. intros cx W3 ms ms' src Hm H. unfold p_glob, pval in *. rewrite Hm. exact H. Qed.

Lemma hw_preader_mem : forall cx fp W3 (ms ms' : machine_state) b h buf p,
  ms_mem ms' = ms_mem ms ->
  p_reader KS cx fp W3 ms b h buf p -> p_reader KS cx fp W3 ms' b h buf p.
Proof.
  intros cx fp W3 ms ms' b h buf p Hm H. unfold p_reader, p_psopen, pval in *. rewrite Hm. exact H.
Qed.

Lemma hw_pspad_mem : forall cx fp W3 (ms ms' : machine_state),
  ms_mem ms' = ms_mem ms -> p_pspad cx fp W3 ms -> p_pspad cx fp W3 ms'.
Proof. intros cx fp W3 ms ms' Hm H. unfold p_pspad in *. rewrite Hm. exact H. Qed.

(* pe_body at a new pc: the machine data of the cut, with the memory function kept. *)
Lemma hw_body_mem : forall cx fp pc pc' W3 (ms ms' : machine_state) sh,
  ms_mem ms' = ms_mem ms -> ms_pc_val ms' = w64 (BASE + pc') ->
  ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS ->
  ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr -> pregs cx ms' ->
  pe_body cx fp pc W3 ms sh -> pe_body cx fp pc' W3 ms' sh.
Proof.
  intros cx fp pc pc' W3 ms ms' sh Hm Hpc Hrv Hsv Hrom Hfr Hcsr Hregs HBD.
  unfold pe_body, psaved, pheader, pshadow in HBD |- *.
  destruct HBD as (_ & _ & _ & _ & _ & _ & _ & Hsaved & Hhdr & Hshd & Hlen & Hinp).
  rewrite Hm.
  split; [exact Hpc|]. split; [exact Hrv|]. split; [exact Hsv|]. split; [exact Hrom|].
  split; [exact Hfr|]. split; [exact Hcsr|]. split; [exact Hregs|].
  split; [exact Hsaved|]. split; [exact Hhdr|]. split; [exact Hshd|].
  split; [exact Hlen|exact Hinp].
Qed.

(* ---- the stack of the call, as every phase with a write window needs it ---- *)

Lemma hw_sp1_eq : forall cx, pe_base SK B MT KS cx -> c_sp1 cx = pe_sp1 (spZ (c_regs cx)).
Proof. intros cx HB. unfold pe_base in HB. tauto. Qed.

(* The realigned stack pointer s1 (0x80808, 0x8080c) and the window the journal keeps present. *)
Lemma hw_sp : forall cx fp k ly3 S3 W3 (ms3 : machine_state) md3,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  spZ (c_regs cx) mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= spZ (c_regs cx) /\
  spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 256 < c_sp1 cx <= spZ (c_regs cx) - 224 /\ c_sp1 cx mod 32 = 0 /\
  (forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W3) (ms_mem ms3) a).
Proof.
  intros cx fp k ly3 S3 W3 ms3 md3 HB HJ.
  destruct HJ as (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  rewrite (hw_sp1_eq cx HB). unfold pe_sp1, PE_MFRAME.
  pose proof (Z_div_mod_eq_full (spZ (c_regs cx) - 224) 32) as Hdm.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 224) 32 ltac:(lia)) as Hmb.
  rewrite Z.add_0_r in Hal16, Hslo, Hshi, Hbot, Htop2, Hpres.
  split; [exact Hal16|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [rewrite Z.mul_comm; apply Z_mod_mult|].
  intros a Ha. apply Hpres. lia.
Qed.

(* Everything a cut names, except the machine stack, lies under the allocator's ceiling: the frame on the side
   stack and its shadow (the app region), the blocks the call holds, the image.  So a run that writes only
   inside the machine frame keeps all of them, and the disjointness of each fact is one `lia`. *)
Lemma hw_geom : forall cx fp k ly3 S3 W3 (ms3 : machine_state) md3,
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  4096 <= pF cx fp /\ pF cx fp + PE_FRAME <= alloc_ceiling /\
  4096 <= pSH cx fp /\ pSH cx fp + 16 <= alloc_ceiling.
Proof.
  intros cx fp k ly3 S3 W3 ms3 md3 HJ Hfrs.
  pose proof (ASAN_CEIL_range (rc := rc)) as ((HC1 & HC1') & HC2).
  unfold ASAN_CEIL in HC1, HC1', HC2.
  pose proof HJ as (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (HAR & Hly & _).
  assert (Hin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hin) as (H4096 & Hceil & _).
  assert (Efa : frame_addr ly3 PE_CID fp = frame_addr (c_ly cx) PE_CID fp).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  rewrite Efa in H4096, Hceil.
  change (fs_frame_bytes PE_CID) with 128 in Hceil.
  unfold pSH, pF, shadow_of_addr, SHADOW_OFF, PE_FRAME in *.
  assert (HpF47 : frame_addr (c_ly cx) PE_CID fp <= 8 * 2 ^ 44) by lia.
  assert (HpF0 : 0 <= frame_addr (c_ly cx) PE_CID fp) by lia.
  pose proof (Z.div_le_upper_bound (frame_addr (c_ly cx) PE_CID fp) 8 (2 ^ 44) ltac:(lia) HpF47) as Hdu.
  pose proof (Z.div_pos (frame_addr (c_ly cx) PE_CID fp) 8 HpF0 ltac:(lia)) as Hdp.
  remember (frame_addr (c_ly cx) PE_CID fp / 8) as q eqn:Hq. clear Hq.
  split; [exact H4096|]. split; [exact Hceil|]. split; lia.
Qed.

(* ---- the memory a run keeps: the bytes outside its write window ---- *)

(* The walk states what a run keeps as one predicate over addresses, so that each cut fact is transported by
   one lemma and the disjointness is proved once, from the stack and heap bounds. *)
Definition hw_eqon (W : world SEGS) (m m' : word -> option byte) (P : Z -> Prop) : Prop :=
  forall a, P a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.

(* hw_eqon over the one stack window [c_sp1+wlo, c_sp1+whi), from kept_of_frame's output shape. *)
Lemma hw_eqon_of_kept : forall W (m m' : word -> option byte) (sp1 wlo whi : Z),
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + wlo <= a < sp1 + whi) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  hw_eqon W m m' (fun a => 0 <= a < 2 ^ 64 /\ ~ (sp1 + wlo <= a < sp1 + whi)).
Proof. intros W m m' sp1 wlo whi UN a (Ha1 & Ha2). exact (UN a Ha1 Ha2). Qed.

Lemma hw_mbyte_on : forall W m m' (P : Z -> Prop) a,
  hw_eqon W m m' P -> P a ->
  mbyte SEGS (mrestrict (w_H W) m') a = mbyte SEGS (mrestrict (w_H W) m) a.
Proof. intros W m m' P a HE HP. apply (mbyte_of_aview SEGS). exact (HE a HP). Qed.

Lemma hw_rdword_on : forall W m m' (P : Z -> Prop) x v,
  hw_eqon W m m' P -> (forall i, 0 <= i < 8 -> P (x + i)) ->
  rdword (aview SEGS (w_H W) m) x = Some v -> rdword (aview SEGS (w_H W) m') x = Some v.
Proof.
  intros W m m' P x v HE HP H.
  assert (K : forall i, 0 <= i < 8 -> aview SEGS (w_H W) m' (x + i) = aview SEGS (w_H W) m (x + i))
    by (intros i Hi; apply HE, HP, Hi).
  pose proof (K 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  unfold rdword in *.
  rewrite K0, (K 1 ltac:(lia)), (K 2 ltac:(lia)), (K 3 ltac:(lia)), (K 4 ltac:(lia)),
          (K 5 ltac:(lia)), (K 6 ltac:(lia)), (K 7 ltac:(lia)).
  exact H.
Qed.

Lemma hw_val_on : forall W m m' (P : Z -> Prop) x n v,
  hw_eqon W m m' P -> (forall i, 0 <= i < Z.of_nat n -> P (x + i)) ->
  val_mem SEGS (mrestrict (w_H W) m) x n v -> val_mem SEGS (mrestrict (w_H W) m') x n v.
Proof.
  intros W m m' P x n v HE HP H j Hj. rewrite <- (H j Hj).
  apply (hw_mbyte_on W m m' P); [exact HE | apply HP; lia].
Qed.

Lemma hw_garr_on : forall W m m' (P : Z -> Prop) x l,
  hw_eqon W m m' P -> (forall i, 0 <= i < Z.of_nat (length l) -> P (x + i)) ->
  garr8 SEGS (mrestrict (w_H W) m) x l -> garr8 SEGS (mrestrict (w_H W) m') x l.
Proof.
  intros W m m' P x l HE HP H. apply (garr8_frame SEGS _ _ _ _ H). intros a Ha.
  apply (hw_mbyte_on W m m' P); [exact HE|]. replace a with (x + (a - x)) by lia. apply HP. lia.
Qed.

(* ---- the cut predicates, transported across a run by hw_eqon (each over its own footprint) ---- *)

Lemma hw_pslot_on : forall cx W (ms ms' : machine_state) (P : Z -> Prop) off v,
  hw_eqon W (ms_mem ms) (ms_mem ms') P -> (forall i, 0 <= i < 8 -> P (c_sp1 cx + off + i)) ->
  pslot cx W ms off v -> pslot cx W ms' off v.
Proof. intros cx W ms ms' P off v HE HP H. unfold pslot in *.
  exact (hw_rdword_on W (ms_mem ms) (ms_mem ms') P (c_sp1 cx + off) v HE HP H). Qed.

Lemma hw_pval_on : forall W (ms ms' : machine_state) (P : Z -> Prop) a n v,
  hw_eqon W (ms_mem ms) (ms_mem ms') P -> (forall i, 0 <= i < Z.of_nat n -> P (a + i)) ->
  pval W ms a n v -> pval W ms' a n v.
Proof. intros W ms ms' P a n v HE HP H. unfold pval, val_mem in *.
  exact (hw_val_on W (ms_mem ms) (ms_mem ms') P a n v HE HP H). Qed.

(* pe_body across a run that keeps every byte the body reads: the frame header (pF..pF+128), its shadow
   (pSH..pSH+16), the saved registers (sp0-104..sp0-1) and the input block.  Each is given as a P-obligation
   (P = the bytes the run keeps); the caller discharges them from hw_geom / hw_sp by lia. *)
Lemma hw_body_on : forall cx fp pc pc' W (ms ms' : machine_state) sh (P : Z -> Prop),
  hw_eqon W (ms_mem ms) (ms_mem ms') P ->
  ms_pc_val ms' = w64 (BASE + pc') -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr -> pregs cx ms' ->
  (forall i, 0 <= i < 128 -> P (pF cx fp + i)) ->
  (forall i, 0 <= i < 16 -> P (pSH cx fp + i)) ->
  (forall i, 0 <= i < 104 -> P (spZ (c_regs cx) - 104 + i)) ->
  (forall i, 0 <= i < Z.of_nat (length (c_pl cx)) -> P (c_p cx + i)) ->
  pe_body cx fp pc W ms sh -> pe_body cx fp pc' W ms' sh.
Proof.
  intros cx fp pc pc' W ms ms' sh P HE Hpc Hrv Hsv Hrom Hfr Hcsr Hpregs Hhf Hshf Hsvf Hinf HBODY.
  pose proof HBODY as (_ & _ & _ & _ & _ & _ & _ & Hsaved & Hhdr & Hshd & Hlen & Hin).
  split; [exact Hpc|]. split; [exact Hrv|]. split; [exact Hsv|]. split; [exact Hrom|].
  split; [exact Hfr|]. split; [exact Hcsr|]. split; [exact Hpregs|].
  split.
  { unfold psaved in *. destruct Hsaved as (Hra & Hs12). split.
    - apply (hw_rdword_on W (ms_mem ms) (ms_mem ms') P (spZ (c_regs cx) - 8) _ HE);
        [ intros i Hi; replace (spZ (c_regs cx) - 8 + i) with (spZ (c_regs cx) - 104 + (96 + i)) by lia;
          apply Hsvf; lia | exact Hra ].
    - intros j Hj. apply (hw_rdword_on W (ms_mem ms) (ms_mem ms') P (spZ (c_regs cx) - 16 - 8 * j) _ HE);
        [ intros i Hi; replace (spZ (c_regs cx) - 16 - 8 * j + i) with (spZ (c_regs cx) - 104 + (88 - 8 * j + i)) by lia;
          apply Hsvf; lia | apply Hs12; exact Hj ]. }
  split.
  { unfold pheader in *. destruct Hhdr as (H0 & H8 & H16 & HFL).
    split; [ apply (hw_rdword_on W (ms_mem ms) (ms_mem ms') P (pF cx fp) _ HE);
             [ intros i Hi; replace (pF cx fp + i) with (pF cx fp + i) by lia; apply Hhf; lia | exact H0 ] |].
    split; [ apply (hw_rdword_on W (ms_mem ms) (ms_mem ms') P (pF cx fp + 8) _ HE);
             [ intros i Hi; replace (pF cx fp + 8 + i) with (pF cx fp + (8 + i)) by lia; apply Hhf; lia | exact H8 ] |].
    split; [ apply (hw_rdword_on W (ms_mem ms) (ms_mem ms') P (pF cx fp + 16) _ HE);
             [ intros i Hi; replace (pF cx fp + 16 + i) with (pF cx fp + (16 + i)) by lia; apply Hhf; lia | exact H16 ] |].
    apply (hw_rdword_on W (ms_mem ms) (ms_mem ms') P (pF cx fp + PE_FLAGPTR) _ HE);
      [ intros i Hi; unfold PE_FLAGPTR; replace (pF cx fp + 120 + i) with (pF cx fp + (120 + i)) by lia; apply Hhf; lia | exact HFL ]. }
  split.
  { unfold pshadow in *. intros i Hi. rewrite Hlen in Hi. unfold PE_NSH in Hi.
    rewrite (HE (pSH cx fp + Z.of_nat i) (Hshf (Z.of_nat i) ltac:(lia))). apply Hshd. rewrite Hlen. exact Hi. }
  split; [exact Hlen|].
  apply (hw_garr_on W (ms_mem ms) (ms_mem ms') P (c_p cx) _ HE); [|exact Hin].
  intros i Hi. rewrite length_map in Hi. apply Hinf. exact Hi.
Qed.

Lemma hw_pslots_on : forall cx fp W (ms ms' : machine_state) (P : Z -> Prop),
  hw_eqon W (ms_mem ms) (ms_mem ms') P ->
  (forall off, (off = PS_PSP \/ off = PS_GLEN \/ off = PS_D \/ off = PS_SH \/ off = PS_F \/ off = PS_FK \/ off = PS_TSP) ->
     forall i, 0 <= i < 8 -> P (c_sp1 cx + off + i)) ->
  pslots cx fp W ms -> pslots cx fp W ms'.
Proof.
  intros cx fp W ms ms' P HE HP H. unfold pslots in *.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  split; [eapply hw_pslot_on; [exact HE | intros i Hi; apply HP; [tauto | exact Hi] | exact A1]|].
  split; [eapply hw_pslot_on; [exact HE | intros i Hi; apply HP; [tauto | exact Hi] | exact A2]|].
  split; [eapply hw_pslot_on; [exact HE | intros i Hi; apply HP; [tauto | exact Hi] | exact A3]|].
  split; [eapply hw_pslot_on; [exact HE | intros i Hi; apply HP; [tauto | exact Hi] | exact A4]|].
  split; [eapply hw_pslot_on; [exact HE | intros i Hi; apply HP; [tauto | exact Hi] | exact A5]|].
  split; [eapply hw_pslot_on; [exact HE | intros i Hi; apply HP; [tauto | exact Hi] | exact A6]|].
  eapply hw_pslot_on; [exact HE | intros i Hi; apply HP; [tauto | exact Hi] | exact A7].
Qed.

Lemma hw_pglob_on : forall cx W (ms ms' : machine_state) src (P : Z -> Prop),
  hw_eqon W (ms_mem ms) (ms_mem ms') P ->
  (forall i, 0 <= i < 8 -> P (pa_val (A_OBJ 2) + i)) -> (forall i, 0 <= i < 8 -> P (pa_val (A_OBJ 4) + i)) ->
  p_glob cx W ms src -> p_glob cx W ms' src.
Proof.
  intros cx W ms ms' src P HE HP2 HP4 (H2 & H4). unfold p_glob. split.
  - exact (hw_pval_on W ms ms' P (pa_val (A_OBJ 2)) 8 src HE HP2 H2).
  - exact (hw_pval_on W ms ms' P (pa_val (A_OBJ 4)) 8 (p_nF cx) HE HP4 H4).
Qed.

Lemma hw_pspad_on : forall cx fp W (ms ms' : machine_state) (P : Z -> Prop),
  hw_eqon W (ms_mem ms) (ms_mem ms') P -> (forall i, 0 <= i < 2 -> P (pPS cx fp + 22 + i)) ->
  p_pspad cx fp W ms -> p_pspad cx fp W ms'.
Proof.
  intros cx fp W ms ms' P HE HP H. unfold p_pspad in *.
  apply (hw_garr_on W (ms_mem ms) (ms_mem ms') P (pPS cx fp + 22) [165;165] HE); [|exact H].
  intros i Hi. apply HP. cbn [length] in Hi. lia.
Qed.

Lemma hw_preader_on : forall cx fp W (ms ms' : machine_state) b h buf p (P : Z -> Prop),
  hw_eqon W (ms_mem ms) (ms_mem ms') P ->
  (forall a, (h <= a < h + SRC_FILE_BLOCK) \/ (b <= a < b + Z.of_nat (length (p_C cx))) \/ asrc_env_addr KS a -> P a) ->
  (forall i, 0 <= i < 24 -> P (pPS cx fp + i)) -> (forall i, 0 <= i < 8 -> P (pTS cx fp + i)) ->
  (p_kind cx (p_q cx p) = PSN.KFit ->
     forall i, 0 <= i < Z.of_nat (length (PSN.rec_bytes (p_sw cx) (p_F cx) (p_q cx p))) -> P (buf + i)) ->
  p_reader KS cx fp W ms b h buf p -> p_reader KS cx fp W ms' b h buf p.
Proof.
  intros cx fp W ms ms' b h buf p P HE Hsrc Hps Hts Hbuf (Hasrc & Hpso & HKFit).
  unfold p_reader. split; [|split].
  - eapply (asource_at_frame_segs SEGS KS (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')));
      [ intros a Ha; apply (hw_mbyte_on W (ms_mem ms) (ms_mem ms') P a HE); apply Hsrc; exact Ha | exact Hasrc ].
  - unfold p_psopen in *. destruct Hpso as (Hpa & Hpb). split.
    + exact (hw_pval_on W ms ms' P (pPS cx fp) 8 h HE (fun i Hi => Hps i ltac:(lia)) Hpa).
    + exact (hw_pval_on W ms ms' P (pPS cx fp + 8) 4 (p_swz cx) HE
        (fun i Hi => ltac:(replace (pPS cx fp + 8 + i) with (pPS cx fp + (8 + i)) by lia; apply Hps; lia)) Hpb).
  - intros HK. destruct (HKFit HK) as (Ho & Ht & Hv & Hts' & Hg). split; [|split; [|split; [|split]]].
    + exact (hw_pval_on W ms ms' P (pPS cx fp + 12) 4 _ HE
        (fun i Hi => ltac:(replace (pPS cx fp + 12 + i) with (pPS cx fp + (12 + i)) by lia; apply Hps; lia)) Ho).
    + exact (hw_pval_on W ms ms' P (pPS cx fp + 16) 4 _ HE
        (fun i Hi => ltac:(replace (pPS cx fp + 16 + i) with (pPS cx fp + (16 + i)) by lia; apply Hps; lia)) Ht).
    + exact (hw_pval_on W ms ms' P (pPS cx fp + 20) 2 _ HE
        (fun i Hi => ltac:(replace (pPS cx fp + 20 + i) with (pPS cx fp + (20 + i)) by lia; apply Hps; lia)) Hv).
    + exact (hw_pval_on W ms ms' P (pTS cx fp) 8 _ HE Hts Hts').
    + apply (hw_garr_on W (ms_mem ms) (ms_mem ms') P buf _ HE); [|exact Hg].
      intros i Hi. rewrite length_map in Hi. apply (Hbuf HK). exact Hi.
Qed.

(* The length of the bytes a fit record leaves in the harness's buffer: its incl_len field.  The proof keeps
   every length in nat and carries its Z image, so that no goal mixes Nat.min with Z.to_nat. *)
Lemma hw_recbytes_len : forall cx Q, 0 <= Q -> p_kind cx Q = PSN.KFit ->
  Z.of_nat (length (PSN.rec_bytes (p_sw cx) (p_F cx) Q)) = PSN.incl (p_sw cx) (p_F cx) Q.
Proof.
  intros cx Q HQ HK. unfold p_kind in HK.
  destruct (PW.kind_fit (p_sw cx) (p_F cx) (p_cap cx) Q HK) as (_ & _ & _ & Hfit & Hincl).
  pose proof (PW.incl_nonneg (p_sw cx) (p_F cx) Q) as Hnn.
  change (PSN.flen (p_F cx)) with (Z.of_nat (length (p_F cx))) in Hfit.
  assert (HnZ : Z.of_nat (Z.to_nat (PSN.incl (p_sw cx) (p_F cx) Q)) = PSN.incl (p_sw cx) (p_F cx) Q) by (apply Z2Nat.id; lia).
  assert (HmZ : Z.of_nat (Z.to_nat (Q + 16)) = Q + 16) by (apply Z2Nat.id; lia).
  assert (Hq : (Z.to_nat (Q + 16) + Z.to_nat (PSN.incl (p_sw cx) (p_F cx) Q) <= length (p_F cx))%nat).
  { apply (proj2 (Nat2Z.inj_le _ _)). rewrite Nat2Z.inj_add, HnZ, HmZ. lia. }
  assert (HrawL : length (PSN.rec_raw (p_sw cx) (p_F cx) Q) = Z.to_nat (PSN.incl (p_sw cx) (p_F cx) Q)).
  { unfold PSN.rec_raw. rewrite length_firstn, length_skipn, Nat.min_l by lia. reflexivity. }
  unfold PSN.rec_bytes. cbv zeta.
  destruct (PSN.tagged (p_sw cx) (p_F cx) Q) eqn:HT.
  - assert (H18 : 18 <= PSN.incl (p_sw cx) (p_F cx) Q).
    { unfold PSN.tagged in HT. apply andb_prop in HT as [HT1 _]. apply andb_prop in HT1 as [HT1 _].
      apply Z.leb_le in HT1. exact HT1. }
    assert (H16Z : Z.of_nat (Z.to_nat (PSN.incl (p_sw cx) (p_F cx) Q - 16)) = PSN.incl (p_sw cx) (p_F cx) Q - 16) by (apply Z2Nat.id; lia).
    assert (H4Z : Z.of_nat (Z.to_nat (PSN.incl (p_sw cx) (p_F cx) Q - 4)) = PSN.incl (p_sw cx) (p_F cx) Q - 4) by (apply Z2Nat.id; lia).
    assert (L1 : (12 <= length (PSN.rec_raw (p_sw cx) (p_F cx) Q))%nat) by (rewrite HrawL; lia).
    assert (L2 : (Z.to_nat (PSN.incl (p_sw cx) (p_F cx) Q - 16) <= length (skipn 16 (PSN.rec_raw (p_sw cx) (p_F cx) Q)))%nat)
      by (rewrite length_skipn, HrawL; lia).
    rewrite !length_app, (firstn_length_le _ L1), (firstn_length_le _ L2), length_skipn, HrawL.
    lia.
  - rewrite HrawL. exact HnZ.
Qed.

(* ---- what the reader's answer says about the record it answered for (PWalk's W4) ---- *)

(* The answer is the record's length, 0 at the end of the file, or -1; the length is a 32-bit field. *)
Lemma hw_res_range : forall cx Q, -4 <= p_res cx Q < 2 ^ 32.
Proof.
  intros cx Q. pose proof (PW.pw_hw_range (p_sw cx) (p_F cx) Q 8) as HI.
  unfold p_res, PSN.res_of, PSN.rec_len, PSN.incl.
  destruct (PSN.kind (p_sw cx) (p_F cx) (p_cap cx) Q); try lia.
  destruct (PSN.tagged (p_sw cx) (p_F cx) Q); lia.
Qed.

Lemma hw_res_small : forall cx Q, - 2 ^ 63 <= p_res cx Q < 2 ^ 63.
Proof. intros cx Q. pose proof (hw_res_range cx Q). lia. Qed.

(* A positive answer is exactly a record that fits in the harness's buffer. *)
Lemma hw_kind_fit : forall cx p, 0 < p_res cx (p_q cx p) -> p_kind cx (p_q cx p) = PSN.KFit.
Proof.
  intros cx p H. unfold p_res, PSN.res_of in H. unfold p_kind.
  destruct (PSN.kind (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p)); cbn in H; try lia; reflexivity.
Qed.

Lemma hw_kind_nfit : forall cx p, p_res cx (p_q cx p) <= 0 -> p_kind cx (p_q cx p) <> PSN.KFit.
Proof.
  intros cx p H HK. unfold p_kind in HK. unfold p_res, PSN.res_of in H. rewrite HK in H.
  destruct (PW.kind_fit (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p) HK) as (_ & (HR1 & _) & _). lia.
Qed.

(* ---- the symbolic state for the three stores of the record-loop prologue ---- *)
(* From PP_KD the loop prologue stores buf+12 (0x30(s1)=PS_BUF12), 0xf00 (0x28(s1)=PS_VMASK) and
   10^6*2^32 (0x38(s1)=PS_USEC) into the machine frame; the write window is [c_sp1 + 40, c_sp1 + 64). *)
Definition hwR_KD : YP09.region := YP09.mkRegion (Some 9%nat) 40 64 40 64 [].
Definition hfacts_KD : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition hss_KD : sstate := mkSS PP_KD sr_atoms [hwR_KD] None hfacts_KD.

Lemma hw_entry0_KD : forall (W3 : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (sp1 : Z),
  getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall o, 40 <= o < 64 -> apresent (w_H W3) mem (sp1 + o)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 HW_SB])) hss_KD
    (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + PP_KD)) mem (seg_rom SEGS))).
Proof.
  intros W3 regs mem sp1 H9 Hsp1 Hsp1m Hpres.
  assert (E9 : ew (Eimg (Ereg regs [w64 HW_SB])) 9%nat = w64 sp1).
  { rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl). exact H9. }
  assert (Eu : bv_unsigned (ew (Eimg (Ereg regs [w64 HW_SB])) 9%nat) = sp1).
  { rewrite E9. unfold w64. apply unsigned_lit_small. lia. }
  rewrite restrict_mkst_fx. unfold hss_KD.
  apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold hwR_KD, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Eu. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  - cbn [hwR_KD pairwise_disjoint all_disjoint]. split; exact I.
  - unfold hfacts_KD, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|exact I]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite Eu. split; [lia|]. split; [exact Hsp1m | lia].
Qed.

Lemma hw_entryKD : forall (W3 : world SEGS) (ms3 : machine_state) (sp1 : Z),
  ms_pc_val ms3 = w64 (BASE + PP_KD) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  getr (ms_regs ms3) 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall o, 40 <= o < 64 -> apresent (w_H W3) (ms_mem ms3) (sp1 + o)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) [w64 HW_SB])) hss_KD (restrict (w_H W3) ms3).
Proof.
  intros W3 ms3 sp1 Hpc Hrv Hsv Hrom Hfr Hcsr H9 Hsp1 Hsp1m Hpres.
  destruct ms3 as [rg fg pcv svc resv fcsr mm rom].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in *. subst.
  exact (hw_entry0_KD W3 rg mm sp1 H9 Hsp1 Hsp1m Hpres).
Qed.

(* ---- the bytes the PP_KD run keeps: everything outside the prologue's window [s1 + 40, s1 + 64) ---- *)
Definition hw_PKD (s1 a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ (s1 + 40 <= a < s1 + 64).

(* Below the allocator's ceiling: the frame, its shadow, the blocks, the image (the window is in the stack). *)
Lemma hw_PKD_low : forall s1 a, alloc_ceiling + 32000 <= s1 -> 0 <= a < alloc_ceiling -> hw_PKD s1 a.
Proof.
  intros s1 a H1 H2. pose proof (ASAN_CEIL_range (rc := rc)) as ((_ & HC) & _). unfold ASAN_CEIL in HC.
  unfold hw_PKD. lia.
Qed.

(* Above the window: the saved registers at sp0 - 104 .. sp0 - 1. *)
Lemma hw_PKD_high : forall s1 sp0 a, 0 <= s1 -> s1 <= sp0 - 224 -> sp0 <= 2 ^ 47 -> sp0 - 104 <= a < sp0 ->
  hw_PKD s1 a.
Proof. intros s1 sp0 a H0 H1 H2 H3. unfold hw_PKD. lia. Qed.

(* A spill slot outside the window. *)
Lemma hw_PKD_slot : forall s1 off i, 0 <= s1 <= 2 ^ 47 -> 0 <= off -> (off + 8 <= 40 \/ 64 <= off <= 96) ->
  0 <= i < 8 -> hw_PKD s1 (s1 + off + i).
Proof. intros s1 off i H0 H1 H2 H3. unfold hw_PKD. lia. Qed.

Lemma hw_img_PKD : forall s1 a, alloc_ceiling + 32000 <= s1 -> in_img SEGS a -> hw_PKD s1 a.
Proof.
  intros s1 a Hs Ha. pose proof (pa_segs_low a Ha) as Hl. unfold kLowMemEnd in Hl.
  pose proof (ASAN_CEIL_range (rc := rc)) as ((HC & _) & _). unfold ASAN_CEIL in HC.
  apply hw_PKD_low; [exact Hs | lia].
Qed.

(* Every fact of the PP_KD cut but its registers, across a run whose kept bytes are hw_PKD (c_sp1 cx). *)
Lemma hw_KD_keep : forall cx fp k acc ly3 S3 W3 (ms3 ms' : machine_state) md3 pc' b h buf,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  p_cut B cx fp PP_KD PSH_ts k 3 acc (PA_K3 MT cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 ->
  p_good cx = true ->
  p_pspad cx fp W3 ms3 -> pslots cx fp W3 ms3 -> p_glob cx W3 ms3 b -> p_reader KS cx fp W3 ms3 b h buf 24 ->
  hw_eqon W3 (ms_mem ms3) (ms_mem ms') (hw_PKD (c_sp1 cx)) ->
  ms_pc_val ms' = w64 (BASE + pc') -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr -> pregs cx ms' ->
  pe_body cx fp pc' W3 ms' PSH_ts /\ p_pspad cx fp W3 ms' /\ pslots cx fp W3 ms' /\
  p_glob cx W3 ms' b /\ p_reader KS cx fp W3 ms' b h buf 24.
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 ms' md3 pc' b h buf HB HJ Hfrs HCUT Hgood Hpad Hsl Hglob Hrd HE
    Hpc Hrv Hsv Hrom Hfr Hcsr Hpregs.
  pose proof HCUT as (HBODY & _ & _ & HPerm & _ & _).
  pose proof (hw_sp cx fp k ly3 S3 W3 ms3 md3 HB HJ) as (_ & HspLo & HspHi & Hsp1rng & _ & _).
  unfold LLVMF_STK in HspLo.
  pose proof (hw_geom cx fp k ly3 S3 W3 ms3 md3 HJ Hfrs) as (HF4096 & HFceil & HSH4096 & HSHceil).
  pose proof (ASAN_CEIL_range (rc := rc)) as ((HCa & HCb) & _). unfold ASAN_CEIL in HCa, HCb.
  assert (Hs1 : alloc_ceiling + 32000 <= c_sp1 cx) by lia.
  assert (Hs1b : 0 <= c_sp1 cx <= 2 ^ 47) by lia.
  pose proof (hw_gx_of_base cx HB) as HG.
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite ?Z.add_0_r in HJi.
  pose proof HJi as (HAR3 & _).
  assert (Hb_in : In (b, p_nF cx) (ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym HPerm)); apply in_or_app; right; left; reflexivity).
  assert (Hh_in : In (h, SRC_FILE_BLOCK) (ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym HPerm)); apply in_or_app; right; right; left; reflexivity).
  assert (Hbuf_in : In (buf, p_bn cx) (ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym HPerm)); apply in_or_app; right; right; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb_in) as (_ & Hb4096 & Hbceil & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hh_in) as (_ & Hh4096 & Hhceil & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hbuf_in) as (_ & Hbuf4096 & Hbufceil & _).
  pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
  pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hreqb].
  pose proof (req_size_pos SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)) as [_ Hreqh].
  pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [_ Hreqbn].
  assert (LOW : forall a, 0 <= a < alloc_ceiling -> hw_PKD (c_sp1 cx) a)
    by (intros a Ha; apply hw_PKD_low; [exact Hs1 | exact Ha]).
  split; [|split; [|split; [|split]]].
  - apply (hw_body_on cx fp PP_KD pc' W3 ms3 ms' PSH_ts (hw_PKD (c_sp1 cx)) HE Hpc Hrv Hsv Hrom Hfr Hcsr Hpregs);
      [ intros i Hi; apply LOW; unfold PE_FRAME in HFceil; lia
      | intros i Hi; apply LOW; lia
      | intros i Hi; apply (hw_PKD_high (c_sp1 cx) (spZ (c_regs cx))); lia
      | | exact HBODY ].
    intros i Hi. pose proof HB as (_ & _ & _ & _ & HINP & _).
    destruct HINP as [(Hn0 & _) | (Hn & Hin0)].
    + unfold c_n in Hn0. lia.
    + assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
        by (apply (Permutation_in _ (Permutation_sym HPerm)); apply in_or_app; left; exact Hin0).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpceil & _).
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreqp].
      apply LOW. unfold c_n in *. lia.
  - apply (hw_pspad_on cx fp W3 ms3 ms' _ HE); [|exact Hpad].
    intros i Hi. apply LOW. unfold pPS, PO_PS. unfold PE_FRAME in HFceil. lia.
  - apply (hw_pslots_on cx fp W3 ms3 ms' _ HE); [|exact Hsl].
    intros off Hoff i Hi. apply hw_PKD_slot; [exact Hs1b | | | exact Hi];
      unfold PS_PSP, PS_GLEN, PS_D, PS_SH, PS_F, PS_FK, PS_TSP in Hoff; lia.
  - apply (hw_pglob_on cx W3 ms3 ms' b _ HE); [ | | exact Hglob]; intros i Hi; apply (hw_img_PKD _ _ Hs1).
    + apply (proj1 (HG (pa_val (A_OBJ 2) + i)
        ltac:(unfold inG, pe_G; apply Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia))).
    + apply (proj1 (HG (pa_val (A_OBJ 4) + i)
        ltac:(unfold inG, pe_G; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia))).
  - apply (hw_preader_on cx fp W3 ms3 ms' b h buf 24 _ HE); [ | | | | exact Hrd ].
    + intros a [Ha | [Ha | Ha]].
      * apply LOW. change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil, Hreqh. unfold SRC_FILE_BLOCK in *. lia.
      * apply LOW. unfold p_C in Ha. rewrite length_map in Ha. change (Z.of_nat (length (p_F cx))) with (p_nF cx) in Ha. lia.
      * destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & _). exact (hw_img_PKD _ _ Hs1 Hi).
    + intros i Hi. apply LOW. unfold pPS, PO_PS. unfold PE_FRAME in HFceil. lia.
    + intros i Hi. apply LOW. unfold pTS, PO_TS. unfold PE_FRAME in HFceil. lia.
    + intros HK i Hi. apply LOW.
      pose proof (PW.psn_q_ge (p_sw cx) (p_F cx) (p_cap cx) 24) as Hq24. fold (p_q cx 24) in Hq24.
      rewrite (hw_recbytes_len cx (p_q cx 24) ltac:(lia) HK) in Hi.
      unfold p_kind in HK. destruct (PW.kind_fit (p_sw cx) (p_F cx) (p_cap cx) (p_q cx 24) HK) as (_ & _ & _ & _ & Hincl).
      assert (Hcb : p_cap cx <= p_bn cx) by (unfold p_bn; lia).
      lia.
Qed.

(* A value's bytes as a field of a region of the symbolic state (PcapHarnessA's h_field, for st_ok_pi). *)
Lemma hw_field_pi : forall E ss ms i n lo hi wlo whi cs b od (w : N) e v,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS (ms_mem ms) (b + od) (N.to_nat w) v.
Proof.
  intros E ss ms i n lo hi wlo whi cs b od w e v HS Hi Hb Hin He Hv Hw.
  exact (field_of_region E (ms_mem ms) n b cs lo hi wlo whi od w e v (st_ok_pi_region_nth E ss ms i _ HS Hi)
    Hb Hin He Hv Hw).
Qed.

(* ---- PP_KD (0x80af4): the first pcap_source_next returned; the record loop's prologue ---- *)
(* 0x80af4 mv s10,a0 | 0x80af8 blez a0 -> PP_K5-setup (0x81074) | else the three stores of the loop prologue
   (PS_BUF12, PS_VMASK, PS_USEC) and i:=0, p:=24, s7:=0xff00, a2:=first -> PP_K4 (0x80b34).
   The answer a0 = first decides the first turn: first > 0 is a fit record (loop enters at K4, i=0, p=24);
   first <= 0 ends the loop at once (K5, p=24). *)
Lemma pe_KD_at : forall POST,
  pe_from SK B MT KS POST (GI_K4 B MT KS) ->
  pe_from SK B MT KS POST (GI_K5 B MT KS) ->
  pe_from SK B MT KS POST (GI_KD B MT KS).
Proof.
intros POST HK4 HK5 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG.
destruct HG as (b & h & buf & HCUT & Hpad & H26 & Hgood & R10 & R19 & R21 & R22 & Hsl & Hglob & Hrd).
pose proof HCUT as (HBODY & Hk3 & Hacc & HPerm & Hfds & Hfs).
pose proof HBODY as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsaved & Hhdr & Hshd & Hshlen & Hinp).
destruct Hregs as (G2 & G8 & G9 & G27 & G3 & G4).
pose proof (hw_sp cx fp k ly3 S3 W3 ms3 md3 HB HJ) as (Hsp16 & HspLo & HspHi & Hsp1rng & Hsp1m & Hpresent).
pose proof (hw_geom cx fp k ly3 S3 W3 ms3 md3 HJ Hfrs) as (HF4096 & HFceil & HSH4096 & HSHceil).
pose proof (ASAN_CEIL_range (rc := rc)) as ((HCa & HCb) & _). unfold ASAN_CEIL in HCa, HCb.
unfold LLVMF_STK in HspLo.
assert (Hc1lo : 2 ^ 46 <= c_sp1 cx) by lia.
assert (Hc1hi : c_sp1 cx <= 2 ^ 47) by lia.
assert (Hpres' : forall o, 40 <= o < 64 -> apresent (w_H W3) (ms_mem ms3) (c_sp1 cx + o))
  by (intros o Ho; apply Hpresent; unfold LLVMF_STK; lia).
assert (HL24 : 24 <= p_nF cx).
{ unfold p_good in Hgood. apply andb_prop in Hgood as [H24 _]. apply Z.leb_le in H24. exact H24. }
pose proof (hw_entryKD W3 ms3 (c_sp1 cx) Hpc Hrv Hsv Hrom Hfreg Hfcsr G9 (conj Hc1lo Hc1hi) Hsp1m Hpres') as HS.
set (E := Eimg (Ereg (ms_regs ms3) [w64 HW_SB])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r).
{ intros i r Hi. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hi. }
assert (U9 : bv_unsigned (ew E 9%nat) = c_sp1 cx)
  by (rewrite (EEo 9%nat 9%bv eq_refl), G9; unfold w64; apply unsigned_lit_small; lia).
pose proof (hw_sh_nil E (mrestrict (w_H W3) (ms_mem ms3))) as SHOK.
pose proof HJ as HJ0.
paj_run_tok RUN HS HJ SHOK HWspan;
  [ apply awr_ok_x_of0; eapply awr_ok_cons_stack_off with (n := 9%nat) (d := c_sp1 cx - spZ (c_regs cx));
    [ reflexivity | rewrite U9; lia | cbn [YP09.r_wlo hwR_KD]; unfold LLVMF_STK; lia | cbn [YP09.r_whi hwR_KD]; lia | apply awr_ok_nil ] |].
(* the first run's frame: the bytes kept from PP_KD to the branch *)
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => c_sp1 cx + 40 <= a < c_sp1 cx + 64) HFr
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW; rewrite ?U9 in HrrW; lia|]);
        destruct HinW)) as UN1.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK HWspan.
- (* blez taken: first <= 0, the record loop ends at PP_K5, no store executed *)
  rewrite hw_branch_ge, hw_sg_lit0, (hw_sg_reg E 10%nat (p_res cx (p_q cx 24)))
    in Hc by (first [rewrite (EEo 10%nat 10%bv eq_refl); exact R10 | apply hw_res_small]).
  apply negb_true_iff, Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK HWspan PP_K5;
    [ apply awr_ok_x_of0; eapply awr_ok_cons_stack_off with (n := 9%nat) (d := c_sp1 cx - spZ (c_regs cx));
      [ reflexivity | rewrite U9; lia | cbn [YP09.r_wlo hwR_KD]; unfold LLVMF_STK; lia | cbn [YP09.r_whi hwR_KD]; lia | apply awr_ok_nil ] |].
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => c_sp1 cx + 40 <= a < c_sp1 cx + 64) HFr
    ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
          repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW; rewrite ?U9 in HrrW; lia|]);
          destruct HinW)) as UN2.
  clear HF HFr HG.
  lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
    assert (HE : hw_eqon W3 (ms_mem ms3) m2 (hw_PKD (c_sp1 cx)))
      by (intros a (Ha1 & Ha2); rewrite (UN2 a Ha1 Ha2); exact (UN1 a Ha1 Ha2)) end.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
    pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ msx HS eq_refl) as Hshape;
    cbn [ss_pc] in Hshape;
    prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
    prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9;
    prreg HS (12%bv : bv 5) Q12; prreg HS (18%bv : bv 5) Q18; prreg HS (19%bv : bv 5) Q19;
    prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22;
    prreg HS (26%bv : bv 5) Q26; prreg HS (27%bv : bv 5) Q27;
    rewrite (EEo 2%nat 2%bv eq_refl) in Q2; rewrite (EEo 3%nat 3%bv eq_refl) in Q3;
    rewrite (EEo 4%nat 4%bv eq_refl) in Q4; rewrite (EEo 8%nat 8%bv eq_refl) in Q8;
    rewrite (EEo 9%nat 9%bv eq_refl) in Q9; rewrite (EEo 10%nat 10%bv eq_refl) in Q12, Q26;
    rewrite (EEo 19%nat 19%bv eq_refl) in Q19; rewrite (EEo 21%nat 21%bv eq_refl) in Q21;
    rewrite (EEo 22%nat 22%bv eq_refl) in Q22; rewrite (EEo 27%nat 27%bv eq_refl) in Q27;
    apply (HK5 cx fp k acc ly3 S3 W3 msx mdx HB HJ Hfrs Hmo);
    destruct (hw_fields_of_shape _ _ _ _ Hshape) as (HQpc & HQrv & HQsv & HQrom & HQfr & HQcs);
    assert (Hpregs' : pregs cx msx)
      by (split; [rewrite Q2, G2; reflexivity|]; split; [rewrite Q8, G8; reflexivity|];
          split; [rewrite Q9, G9; reflexivity|]; split; [rewrite Q27, G27; reflexivity|];
          split; [rewrite Q3, G3; reflexivity | rewrite Q4, G4; reflexivity]);
    destruct (hw_KD_keep cx fp k acc ly3 S3 W3 ms3 msx md3 PP_K5 b h buf HB HJ0 Hfrs HCUT Hgood Hpad Hsl Hglob Hrd
      HE HQpc HQrv HQsv HQrom HQfr HQcs Hpregs') as (Kbody & Kpad & Ksl & Kglob & Krd)
  end.
  exists b, h, buf, 24.
  split; [split; [exact Kbody|]|].
  { split; [exact Hk3|]. split; [exact Hacc|]. split; [exact HPerm|].
    split; [ etransitivity; [apply (proj1 (hw_md_fds _ _)) | exact Hfds]
           | etransitivity; [apply (proj2 (hw_md_fds _ _)) | exact Hfs] ]. }
  split; [exact Kpad|]. split; [exact H26|]. split; [exact Hgood|]. split; [lia|].
  split; [exact (hw_kind_nfit cx 24 Hc)|].
  split; [rewrite Q12, R10; reflexivity|]. split; [rewrite Q18; reflexivity|].
  split; [rewrite Q19, R19; reflexivity|]. split; [rewrite Q21, R21; reflexivity|].
  split; [rewrite Q22, R22; reflexivity|]. split; [rewrite Q26, R10; reflexivity|].
  split; [exact Ksl|]. split; [exact Kglob | exact Krd].
- (* blez not-taken: first > 0, a fit record, the loop enters at PP_K4 (i = 0, p = 24) *)
  rewrite hw_branch_ge, hw_sg_lit0, (hw_sg_reg E 10%nat (p_res cx (p_q cx 24)))
    in Hc by (first [rewrite (EEo 10%nat 10%bv eq_refl); exact R10 | apply hw_res_small]).
  apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK HWspan PP_K4;
    [ apply awr_ok_x_of0; eapply awr_ok_cons_stack_off with (n := 9%nat) (d := c_sp1 cx - spZ (c_regs cx));
      [ reflexivity | rewrite U9; lia | cbn [YP09.r_wlo hwR_KD]; unfold LLVMF_STK; lia | cbn [YP09.r_whi hwR_KD]; lia | apply awr_ok_nil ] |].
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => c_sp1 cx + 40 <= a < c_sp1 cx + 64) HFr
    ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
          repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW; rewrite ?U9 in HrrW; lia|]);
          destruct HinW)) as UN2.
  clear HF HFr HG.
  lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
    assert (HE : hw_eqon W3 (ms_mem ms3) m2 (hw_PKD (c_sp1 cx)))
      by (intros a (Ha1 & Ha2); rewrite (UN2 a Ha1 Ha2); exact (UN1 a Ha1 Ha2)) end.
  (* buf is a block of the call: below the allocator's ceiling *)
  pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). rewrite ?Z.add_0_r in HJi0.
  pose proof HJi0 as (HAR0 & _).
  assert (Hbuf_in : In (buf, p_bn cx) (ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym HPerm)); apply in_or_app; right; right; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hbuf_in) as (_ & Hbuf4096 & Hbufceil & _).
  pose proof (p_sizes cx) as (_ & _ & Hbn).
  pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [Hreq1 _].
  lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
    pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ msx HS eq_refl) as Hshape;
    cbn [ss_pc] in Hshape;
    prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
    prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9;
    prreg HS (12%bv : bv 5) Q12; prreg HS (18%bv : bv 5) Q18; prreg HS (19%bv : bv 5) Q19;
    prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22; prreg HS (23%bv : bv 5) Q23;
    prreg HS (25%bv : bv 5) Q25; prreg HS (27%bv : bv 5) Q27;
    rewrite (EEo 2%nat 2%bv eq_refl) in Q2; rewrite (EEo 3%nat 3%bv eq_refl) in Q3;
    rewrite (EEo 4%nat 4%bv eq_refl) in Q4; rewrite (EEo 8%nat 8%bv eq_refl) in Q8;
    rewrite (EEo 9%nat 9%bv eq_refl) in Q9; rewrite (EEo 10%nat 10%bv eq_refl) in Q12;
    rewrite (EEo 19%nat 19%bv eq_refl) in Q19; rewrite (EEo 21%nat 21%bv eq_refl) in Q21;
    rewrite (EEo 22%nat 22%bv eq_refl) in Q22; rewrite (EEo 27%nat 27%bv eq_refl) in Q27;
    (* the prologue's three slots, from the region's chunks at s1 + 40, 48, 56 *)
    assert (V40 : val_mem SEGS (mrestrict (w_H W3) (ms_mem msx)) (c_sp1 cx + 40) 8 3840)
      by (refine (hw_field_pi E _ (restrict (w_H W3) msx) 0 9 40 64 40 64 _ (c_sp1 cx) 40 8 (SLit 3840) 3840
            HS eq_refl U9 _ eq_refl _ _); cbn; [tauto | lia | lia]);
    assert (V56 : val_mem SEGS (mrestrict (w_H W3) (ms_mem msx)) (c_sp1 cx + 56) 8 4294967296000000)
      by (refine (hw_field_pi E _ (restrict (w_H W3) msx) 0 9 40 64 40 64 _ (c_sp1 cx) 56 8
            (SLit 4294967296000000) 4294967296000000 HS eq_refl U9 _ eq_refl _ _); cbn; [tauto | lia | lia]);
    assert (V48 : val_mem SEGS (mrestrict (w_H W3) (ms_mem msx)) (c_sp1 cx + 48) 8 (buf + 12))
      by (refine (hw_field_pi E _ (restrict (w_H W3) msx) 0 9 40 64 40 64 _ (c_sp1 cx) 48 8 (SOff 22 12) (buf + 12)
            HS eq_refl U9 _ _ _ _);
          [ cbn; tauto
          | cbn [sv_denot]; rewrite (EEo 22%nat 22%bv eq_refl), R22; unfold w64;
            rewrite unsigned_lit_small by lia; reflexivity
          | cbn; lia | cbn; lia ]);
    apply (HK4 cx fp k acc ly3 S3 W3 msx mdx HB HJ Hfrs Hmo);
    destruct (hw_fields_of_shape _ _ _ _ Hshape) as (HQpc & HQrv & HQsv & HQrom & HQfr & HQcs);
    assert (Hpregs' : pregs cx msx)
      by (split; [rewrite Q2, G2; reflexivity|]; split; [rewrite Q8, G8; reflexivity|];
          split; [rewrite Q9, G9; reflexivity|]; split; [rewrite Q27, G27; reflexivity|];
          split; [rewrite Q3, G3; reflexivity | rewrite Q4, G4; reflexivity]);
    destruct (hw_KD_keep cx fp k acc ly3 S3 W3 ms3 msx md3 PP_K4 b h buf HB HJ0 Hfrs HCUT Hgood Hpad Hsl Hglob Hrd
      HE HQpc HQrv HQsv HQrom HQfr HQcs Hpregs') as (Kbody & Kpad & Ksl & Kglob & Krd)
  end.
  exists b, h, buf, 0, 24.
  split; [split; [exact Kbody|]|].
  { split; [exact Hk3|]. split; [exact Hacc|]. split; [exact HPerm|].
    split; [ etransitivity; [apply (proj1 (hw_md_fds _ _)) | exact Hfds]
           | etransitivity; [apply (proj2 (hw_md_fds _ _)) | exact Hfs] ]. }
  split; [exact Kpad|]. split; [exact H26|]. split; [exact Hgood|].
  split; [lia|]. split; [lia|].
  split; [exact (hw_kind_fit cx 24 Hc)|].
  split; [left; split; reflexivity|].
  split; [rewrite Q12, R10; reflexivity|]. split; [rewrite Q18; reflexivity|].
  split; [rewrite Q19, R19; reflexivity|]. split; [rewrite Q21, R21; reflexivity|].
  split; [rewrite Q22, R22; reflexivity|]. split; [rewrite Q23; reflexivity|].
  split; [rewrite Q25; reflexivity|].
  split.
  { unfold p_lslots. split; [exact Ksl|]. unfold pslot. split; [|split].
    - apply rdword_of_val_mem; [exact V40 | lia].
    - apply rdword_of_val_mem; [exact V48 | lia].
    - change (1000000 * 2 ^ 32) with 4294967296000000. apply rdword_of_val_mem; [exact V56 | lia]. }
  split; [exact Kglob | exact Krd].
Qed.

(* ---- PP_KL2 (0x80fa4): the record loop's own pcap_source_next returned ---- *)
(* 0x80fa4 mv a2,a0 | 0x80fa8 mv a0,s10 | 0x80fac bgtz a2 -> PP_K4 (0x80b34) | 0x80fb0 j -> PP_K5 (0x8107c).
   The answer decides the cut: res > 0 is exactly a fit record (PWalk's W4), and res <= 0 exactly a
   non-fit one, which is where the record loop ends. *)
Lemma pe_KL2_at : forall POST n,
  at_cut (GI_K4 B MT KS) POST n ->
  pe_from SK B MT KS POST (GI_K5 B MT KS) ->
  at_cut (GI_KL2 B MT KS) POST n.
Proof.
intros POST n HK4 HK5 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG Hmeas.
destruct HG as (b & h & buf & jj & p & HCUT & Hpad & H26 & Hgood & Hj1 & Hjp & Hple
  & R10 & R18 & R19 & R21 & R22 & R23 & R25 & R26 & Hls & Hglob & Hrd).
pose proof HCUT as (HBODY & Hk3 & Hacc & HPerm & Hfds & Hfs).
pose proof HBODY as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsaved & Hhdr & Hshd & Hshlen & Hinp).
pose proof (hw_entry_body W3 ms3 PP_KL2 Hpc Hrv Hsv Hrom Hfreg Hfcsr) as HS.
set (E := Eimg (Ereg (ms_regs ms3) [w64 HW_SB])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r).
{ intros i r Hi. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hi. }
pose proof (hw_sh_nil E (mrestrict (w_H W3) (ms_mem ms3))) as SHOK.
paj_run_tok RUN HS HJ SHOK HWspan; [apply awr_ok_x_nil|].
pose proof (hw_mem_kept E _ _ _ eq_refl HF) as Hm0. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK HWspan.
- (* res > 0: a fit record; the loop goes round again at PP_K4 *)
  rewrite hw_branch_lt, hw_sg_lit0, (hw_sg_reg E 10%nat (p_res cx (p_q cx p)))
    in Hc by (first [rewrite (EEo 10%nat 10%bv eq_refl); exact R10 | apply hw_res_small]).
  apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK HWspan PP_K4; [apply awr_ok_x_nil|].
  pose proof (hw_mem_kept E _ _ _ eq_refl HF) as Hm1. clear HF HFr HG.
  pose proof (eq_trans Hm1 Hm0) as Hmem.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
    pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ msx HS eq_refl) as Hshape;
    cbn [ss_pc] in Hshape;
    prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
    prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (10%bv : bv 5) Q10;
    prreg HS (12%bv : bv 5) Q12; prreg HS (18%bv : bv 5) Q18; prreg HS (19%bv : bv 5) Q19;
    prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22; prreg HS (23%bv : bv 5) Q23;
    prreg HS (25%bv : bv 5) Q25; prreg HS (27%bv : bv 5) Q27;
    rewrite (EEo 2%nat 2%bv eq_refl) in Q2; rewrite (EEo 3%nat 3%bv eq_refl) in Q3;
    rewrite (EEo 4%nat 4%bv eq_refl) in Q4; rewrite (EEo 8%nat 8%bv eq_refl) in Q8;
    rewrite (EEo 9%nat 9%bv eq_refl) in Q9; rewrite (EEo 26%nat 26%bv eq_refl) in Q10;
    rewrite (EEo 10%nat 10%bv eq_refl) in Q12; rewrite (EEo 18%nat 18%bv eq_refl) in Q18;
    rewrite (EEo 19%nat 19%bv eq_refl) in Q19; rewrite (EEo 21%nat 21%bv eq_refl) in Q21;
    rewrite (EEo 22%nat 22%bv eq_refl) in Q22; rewrite (EEo 23%nat 23%bv eq_refl) in Q23;
    rewrite (EEo 25%nat 25%bv eq_refl) in Q25; rewrite (EEo 27%nat 27%bv eq_refl) in Q27;
    apply (HK4 cx fp k acc ly3 S3 W3 msx mdx HB HJ Hfrs Hmo) end.
  + destruct Hregs as (G2 & G8 & G9 & G27 & G3 & G4).
    exists b, h, buf, jj, p.
    split.
    { split.
      { destruct (hw_fields_of_shape _ _ _ _ Hshape) as (HQpc & HQrv & HQsv & HQrom & HQfr & HQcs).
        eapply (hw_body_mem cx fp PP_KL2 PP_K4);
        [ exact Hmem | exact HQpc | exact HQrv | exact HQsv | exact HQrom | exact HQfr | exact HQcs
        | split; [rewrite Q2, G2; reflexivity|]; split; [rewrite Q8, G8; reflexivity|];
          split; [rewrite Q9, G9; reflexivity|]; split; [rewrite Q27, G27; reflexivity|];
          split; [rewrite Q3, G3; reflexivity | rewrite Q4, G4; reflexivity]
        | exact HBODY ]. }
      split; [exact Hk3|]. split; [exact Hacc|]. split; [exact HPerm|].
      split; [ etransitivity; [apply (proj1 (hw_md_fds _ _)) | exact Hfds]
             | etransitivity; [apply (proj2 (hw_md_fds _ _)) | exact Hfs] ]. }
    split; [eapply hw_pspad_mem; [rewrite Hmem; reflexivity | exact Hpad]|].
    split; [exact H26|]. split; [exact Hgood|]. split; [lia|]. split; [exact Hjp|].
    split; [exact (hw_kind_fit cx p Hc)|].
    split; [right; split; [lia | rewrite Q10, R26; reflexivity]|].
    split; [rewrite Q12, R10; reflexivity|]. split; [rewrite Q18, R18; reflexivity|].
    split; [rewrite Q19, R19; reflexivity|]. split; [rewrite Q21, R21; reflexivity|].
    split; [rewrite Q22, R22; reflexivity|]. split; [rewrite Q23, R23; reflexivity|].
    split; [rewrite Q25, R25; reflexivity|].
    split; [eapply hw_plslots_mem; [rewrite Hmem; reflexivity | exact Hls]|].
    split; [eapply hw_pglob_mem; [rewrite Hmem; reflexivity | exact Hglob]
           |eapply hw_preader_mem; [rewrite Hmem; reflexivity | exact Hrd]].
  + unfold hw_meas, hw_pos in Hmeas |- *. rewrite Q18, R18. rewrite R18 in Hmeas. exact Hmeas.
- (* res <= 0: the record loop is over *)
  rewrite hw_branch_lt, hw_sg_lit0, (hw_sg_reg E 10%nat (p_res cx (p_q cx p)))
    in Hc by (first [rewrite (EEo 10%nat 10%bv eq_refl); exact R10 | apply hw_res_small]).
  apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK HWspan PP_K5; [apply awr_ok_x_nil|].
  pose proof (hw_mem_kept E _ _ _ eq_refl HF) as Hm1. clear HF HFr HG.
  pose proof (eq_trans Hm1 Hm0) as Hmem.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
    pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ msx HS eq_refl) as Hshape;
    cbn [ss_pc] in Hshape;
    prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
    prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9;
    prreg HS (12%bv : bv 5) Q12; prreg HS (18%bv : bv 5) Q18; prreg HS (19%bv : bv 5) Q19;
    prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22;
    prreg HS (26%bv : bv 5) Q26; prreg HS (27%bv : bv 5) Q27;
    rewrite (EEo 2%nat 2%bv eq_refl) in Q2; rewrite (EEo 3%nat 3%bv eq_refl) in Q3;
    rewrite (EEo 4%nat 4%bv eq_refl) in Q4; rewrite (EEo 8%nat 8%bv eq_refl) in Q8;
    rewrite (EEo 9%nat 9%bv eq_refl) in Q9;
    rewrite (EEo 10%nat 10%bv eq_refl) in Q12; rewrite (EEo 18%nat 18%bv eq_refl) in Q18;
    rewrite (EEo 19%nat 19%bv eq_refl) in Q19; rewrite (EEo 21%nat 21%bv eq_refl) in Q21;
    rewrite (EEo 22%nat 22%bv eq_refl) in Q22; rewrite (EEo 26%nat 26%bv eq_refl) in Q26;
    rewrite (EEo 27%nat 27%bv eq_refl) in Q27;
    apply (HK5 cx fp k acc ly3 S3 W3 msx mdx HB HJ Hfrs Hmo) end.
  destruct Hregs as (G2 & G8 & G9 & G27 & G3 & G4).
  exists b, h, buf, p.
  split.
  { split.
    { destruct (hw_fields_of_shape _ _ _ _ Hshape) as (HQpc & HQrv & HQsv & HQrom & HQfr & HQcs).
      eapply (hw_body_mem cx fp PP_KL2 PP_K5);
      [ exact Hmem | exact HQpc | exact HQrv | exact HQsv | exact HQrom | exact HQfr | exact HQcs
      | split; [rewrite Q2, G2; reflexivity|]; split; [rewrite Q8, G8; reflexivity|];
        split; [rewrite Q9, G9; reflexivity|]; split; [rewrite Q27, G27; reflexivity|];
        split; [rewrite Q3, G3; reflexivity | rewrite Q4, G4; reflexivity]
      | exact HBODY ]. }
    split; [exact Hk3|]. split; [exact Hacc|]. split; [exact HPerm|].
    split; [ etransitivity; [apply (proj1 (hw_md_fds _ _)) | exact Hfds]
           | etransitivity; [apply (proj2 (hw_md_fds _ _)) | exact Hfs] ]. }
  split; [eapply hw_pspad_mem; [rewrite Hmem; reflexivity | exact Hpad]|].
  split; [exact H26|]. split; [exact Hgood|]. split; [lia|].
  split; [exact (hw_kind_nfit cx p Hc)|].
  split; [rewrite Q12, R10; reflexivity|]. split; [rewrite Q18, R18; reflexivity|].
  split; [rewrite Q19, R19; reflexivity|]. split; [rewrite Q21, R21; reflexivity|].
  split; [rewrite Q22, R22; reflexivity|]. split; [rewrite Q26, R26; reflexivity|].
  split; [eapply hw_pslots_mem; [rewrite Hmem; reflexivity | exact (proj1 Hls)]|].
  split; [eapply hw_pglob_mem; [rewrite Hmem; reflexivity | exact Hglob]
         |eapply hw_preader_mem; [rewrite Hmem; reflexivity | exact Hrd]].
Qed.

End g.

(* ---- the walk: GI_KD -> GI_K5 ---- *)
(* The record loop, PP_K4 -> PP_K5 (the skip loop at PP_KR, the three bcmp calls, the record check, the loop's own
   pcap_source_next returning at PP_KL2, and the induction on the plain model's record walk), is pe_WalkR in
   lib/A/Prog/PcapHarnessWalkR.v, which Requires this file.  It enters here as this Section hypothesis, of
   pe_WalkR's exact type; lib/A/Prog/PcapEntryFinal.v discharges it with pe_WalkR (fin_WALKR). *)
Hypothesis WALKR : forall POST,
  pe_from SK B MT KS POST (GI_K5 B MT KS) -> pe_from SK B MT KS POST (GI_K4 B MT KS).

Theorem pe_Walk : forall POST,
  pe_from SK B MT KS POST (GI_K5 B MT KS) -> pe_from SK B MT KS POST (GI_KD B MT KS).
Proof.
  intros POST HK5 cx fp k acc ly3 S3 W3 ms3 md3 HB.
  exact (pe_KD_at (hw_gx_of_base cx HB) POST (WALKR POST HK5) HK5 cx fp k acc ly3 S3 W3 ms3 md3 HB).
Qed.

End c.
End b.
End a.
