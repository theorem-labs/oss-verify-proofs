(* nl_talk (reac_link_alias.c:37-93) on image A (fuzz_link.asan 0x88974, 1504 bytes, 376 instructions; listing
   (internal path) (internal record, sha256 628c2741aace)): the TOP of the walk. It assembles
   the five phases into `nl_talk_aproof : nl_talk_acontract SK pa_segs PCAP_RLO PCAP_RHI B`.

   The phases (lib/A/Prog/nl_talk_defs.v fixes their boundaries; each is `nt_from POST GI_next -> nt_from POST
   GI_self`, with the entry phase proving `nt_start POST`):
     nl_talk_entry.v  nt_entry : nt_from POST (nt_sock_inv B) -> nt_start POST
     nl_talk_sock.v   nt_sock  : nt_from POST (nt_recv_inv B) -> nt_from POST (nt_tail_inv B) -> nt_from POST (nt_sock_inv B)
     nl_talk_recv.v   nt_recv  : nt_from POST (nt_attr_inv B) -> nt_from POST (nt_exit_inv B) -> nt_from POST (nt_recv_inv B)
     nl_talk_attr2.v  nt_attr  : nt_from POST (nt_exit_inv B) -> nt_from POST (nt_attr_inv B)   (helpers: nl_talk_attr.v)
     nl_talk_exit.v   nt_exit  : nt_from POST (nt_tail_inv B) -> nt_from POST (nt_exit_inv B)
                      nt_tail  : nt_from (nt_post SK B) (nt_tail_inv B)
   so the assembly is acyclic: nt_tail, then nt_exit, then nt_attr, then nt_recv, then nt_sock, then nt_entry.

   Callee contracts, each a Section hypothesis of exactly the statement its owner proves (cited, never
   re-proved), with the lemma that discharges it:
     fuzz_socket_acontract / fuzz_send_acontract / fuzz_recv_acontract   lib/A/Prog/LinkWalkKernInst.v
     fuzz_close_acontract                                                lib/A/Prog/fuzz_close.v
     copy_attr_acontract                                                 lib/A/Prog/copy_attr.v
     RtErrnoLoc.aerrno_location_realizes (___errno_location 0x90a7c)     lib/A/Rt/RtErrnoLocClosed.v
                                                                         link_errno_location_closed
     astack_malloc_sz_realizes .. 9 (frame_alloc_9 0x3e15c)              lib/A/Rt/StackSideInst.v
                                                                         link_stack_malloc_9
     astack_free_realizes .. 9 (frame_release_9 0x3e2d4)                 lib/A/Rt/StackSideInst.v
                                                                         link_stack_free_9
     aset_shadow_realizes .. 0 / 0xf8 (meta_fill_00 0x55e74 /            lib/A/Rt/SetShadow.v
       meta_fill_f8 0x55f94)                                             link_set_shadow_00 / link_set_shadow_f8
   and the image instance (PI : PAImg link_listing) with its facts, each discharged at link's instance:
   LV : LinkVals and HSEGS : pa_segs = tfibsegs (lib/A/Prog/LinkImgInst.v pi_link_vals / pi_link_segs),
   LAWS : AR_laws pa_segs B (the frame), TL : PALib B, TB : AF0m.PcapSyms B (instance AD2l.PcapB_syms).
   nt_attr's premise that the relro window is image bytes is discharged here (nt_relro_img), from HSEGS.

   Released proofs (rule 24): none of nl_talk (lookups lookups/walk-lookups.md (internal record, sha256 98fff7967d93);
   the rule-24 walk check at 14:56Z confirmed it, disposition none: written new).
   Proves function nl_talk (image A, the asan build). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_talk_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_talk_defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import fuzz_close_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import SetShadowDef StackFreeDef AsStackSz.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import fuzz_socket_c fuzz_send_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtErrnoLoc.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import copy_attr_c fuzz_recv_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
  nl_talk_exit nl_talk_sock nl_talk_entry nl_talk_attr nl_talk_attr2 nl_talk_recv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
(* the image instance and its tables (discharged at link's PAImg instance: AR_laws by the frame, LinkVals and
   HSEGS by lib/A/Prog/LinkImgInst.v pi_link_vals / pi_link_segs, PcapSyms by AD2l.PcapB_syms) *)
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis TL : PALib B.
(* callee contracts, each discharged by the lemma its owner proves *)
Hypothesis CLOSE : fuzz_close_acontract SK pa_segs PCAP_RLO PCAP_RHI B.     (* fuzz_close.v fuzz_close_aproof *)
Hypothesis MF8 : aset_shadow_realizes pa_segs B (pa_sigma LS___asan_set_shadow_f8) 0xf8.
                                                          (* lib/A/Rt/SetShadow.v link_set_shadow_f8 *)
Hypothesis SFREE : astack_free_realizes pa_segs B (pa_sigma LS___asan_stack_free_9) 9.
                                                          (* lib/A/Rt/StackSideInst.v link_stack_free_9 *)
Hypothesis FSO : fuzz_socket_acontract SK pa_segs PCAP_RLO PCAP_RHI B.   (* the kernel-call walk's fuzz_socket_aproof *)
Hypothesis FSE : fuzz_send_acontract SK pa_segs PCAP_RLO PCAP_RHI B.     (* the kernel-call walk's fuzz_send_aproof *)
Hypothesis ERRNO : aerrno_location_realizes pa_segs B (pa_sigma LS____errno_location).
                                                          (* lib/A/Rt/RtErrnoLocClosed.v link_errno_location_closed *)
Hypothesis MF00 : aset_shadow_realizes pa_segs B (pa_sigma LS___asan_set_shadow_00) 0.
                                                          (* lib/A/Rt/SetShadow.v link_set_shadow_00 *)
Hypothesis ASM9 : astack_malloc_sz_realizes pa_segs B (pa_sigma LS___asan_stack_malloc_9) NT_CID.
                                                          (* lib/A/Rt/StackSideInst.v link_stack_malloc_9 *)
Hypothesis CA : copy_attr_acontract SK pa_segs PCAP_RLO PCAP_RHI B.     (* WalkCopyAttr copy_attr_aproof *)
Hypothesis RECV : fuzz_recv_acontract SK pa_segs PCAP_RLO PCAP_RHI B.   (* the kernel-call walk's fuzz_recv_aproof *)

(* The relro window is image bytes: a computation over the image's segments (nl_talk_entry.v nte_relro_cov),
   reached at pa_segs through HSEGS. *)
Lemma nt_relro_img : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img pa_segs a.
Proof. intros a Ha. rewrite HSEGS. exact (nte_in_img_of_cov tfibsegs _ _ a nte_relro_cov Ha). Qed.

(* The five phases, as their files prove them: nl_talk_entry.v, nl_talk_sock.v,
   nl_talk_recv.v, nl_talk_attr.v + nl_talk_attr2.v,
   nl_talk_exit.v. *)
Let NT_EXIT := nt_exit SK B LAWS LV TB HSEGS CLOSE MF8.
Let NT_TAIL := nt_tail SK B LAWS LV TB HSEGS SFREE.
Let NT_SOCK := nt_sock SK B LAWS LV TB HSEGS FSO FSE CLOSE ERRNO MF00.
Let NT_ENTRY := nt_entry SK B LAWS LV TL TB HSEGS ASM9 MF8.
Let NT_ATTR := nt_attr SK B LAWS LV TB HSEGS nt_relro_img CA.
Let NT_RECV := nt_recv SK B LAWS LV TB HSEGS RECV ERRNO.

(* The whole walk, from the entry slot to the Post. *)
Lemma nt_whole : nt_start SK B (nt_post SK B).
Proof.
  apply NT_ENTRY.
  apply NT_SOCK.
  - apply NT_RECV.
    + apply NT_ATTR. apply NT_EXIT. exact NT_TAIL.
    + apply NT_EXIT. exact NT_TAIL.
  - exact NT_TAIL.
Qed.

Theorem nl_talk_aproof : nl_talk_acontract SK pa_segs PCAP_RLO PCAP_RHI B.
Proof.
  unfold nl_talk_acontract, aleaf_rd.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HPRE HRD HP.
  pose proof HP as HP0.
  destruct HP as (kbs & req & HNLK & HWF & HOPEN & HOC & HCC & HRA & HHV & HERR & HRQ & HRL & HLEN
                  & HMR & HRAQ & HHVQ & HFRQ & HGQ & HBK & HBA & HEK & HEA & HKA & HKF & HAF & HCK & HCA).
  set (cx := mkNTCX G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs kbs req
                    (Ereg regs [])).
  assert (HBASE : nt_base SK B cx).
  { unfold nt_base. cbn [n_G n_XO n_OUT n_STK n_sp0 n_FP n_ly n_S n_W0 n_mem0 n_md0 n_own n_lyc n_Sc
      n_W n_memc n_mdc n_k n_regs n_kbs n_reqb n_E0 n_m n_Wr n_Rd n_req n_len].
    split; [exact HPRE|]. split; [exact HRD|]. split; [exact HP0|].
    split; [exact HNLK|]. split; [exact HRQ|]. split; [exact HRL|].
    split; [intros n r Hn; exact (ew_Ereg_nat regs [] n r Hn)|].
    exact (f_equal (@bv_unsigned 64) (ew_Ereg_nat regs [] 2%nat 2%bv eq_refl)). }
  pose proof (nt_whole cx HBASE) as HRUN.
  assert (HPC : pa_val A_TEXT + NT_entry = NL_TALK_A)
    by (rewrite (lv_text LV); reflexivity).
  rewrite HPC in HRUN.
  exact HRUN.
Qed.

End b.
End a.

About nl_talk_aproof.
Print Assumptions nl_talk_aproof.
