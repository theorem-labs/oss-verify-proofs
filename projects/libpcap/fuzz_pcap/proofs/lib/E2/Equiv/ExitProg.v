(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog HeapFull. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require Import HaltsAdq ExitBase ExitStdio ExitHeap ExitPcap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition S02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
Definition in02 (c : word) : Prop := In c S02.

Lemma in02_0 : in02 (exit_status 0).
Proof. left. apply bv_eq. reflexivity. Qed.
Lemma in02_2 : in02 (exit_status 2).
Proof. right. left. apply bv_eq. reflexivity. Qed.

Section WithCeil.
Context {CE : CEIL}.

Section Prog.
Context {H hptr : Type} (HO : HeapOps H hptr).
Hypothesis HN : heap_noexit HO.
Variable FO : FrameOps (H:=H) (hptr:=hptr).
Hypothesis FO_enter : forall A f (m : M (PState H hptr) A), mne m -> mne (fo_enter FO A f m).
Hypothesis FO_ret : forall A f (x : A), mne (fo_ret FO A f x).
Variable stk : stack_site -> Z.

#[local] Notation PS := (PState H hptr).
#[local] Notation get_lc := (@ps_libc H hptr).
#[local] Notation set_lc := (@set_libc H hptr).

(* [comment removed for export] *)
Lemma mne_set_errno_ps e : mne (set_errno_ps (H:=H) (hptr:=hptr) e).
Proof. unfold set_errno_ps. apply mne_set_errno. Qed.
Hint Resolve mne_set_errno_ps : mne.
Lemma mne_enomem_on_null r : mne (enomem_on_null (H:=H) (hptr:=hptr) r).
Proof. unfold enomem_on_null. mne_go. Qed.
Hint Resolve mne_enomem_on_null : mne.
Lemma mne_pmalloc n : mne (pmalloc HO n).
Proof. unfold pmalloc. apply mne_bind; [apply (hn_malloc HO HN)| intros r; apply mne_enomem_on_null]. Qed.
Lemma mne_pcalloc m n : mne (pcalloc HO m n).
Proof. unfold pcalloc. apply mne_bind; [apply (hn_calloc HO HN)| intros r; apply mne_enomem_on_null]. Qed.
Lemma mne_prealloc q n : mne (prealloc HO q n).
Proof. unfold prealloc. apply mne_bind; [apply (hn_realloc HO HN)| intros r; apply mne_enomem_on_null]. Qed.
Lemma mne_pfree q : mne (pfree HO q).
Proof. unfold pfree. apply (hn_free HO HN). Qed.
Hint Resolve mne_pmalloc mne_pcalloc mne_prealloc mne_pfree : mne.

(* [comment removed for export] *)
Lemma mne_s_fopen n w : mne (s_fopen HO n w).
Proof. unfold s_fopen. apply mne_fopen. exact mne_pmalloc. Qed.
Lemma mne_s_fclose h : mne (s_fclose HO h).
Proof. unfold s_fclose. apply mne_fclose. exact mne_pfree. Qed.
Lemma mne_s_fwrite h s : mne (s_fwrite HO h s).
Proof. unfold s_fwrite. apply mne_fwrite. Qed.
Lemma mne_s_fread h d n : mne (s_fread HO h d n).
Proof. unfold s_fread. apply mne_fread. Qed.
Lemma mne_s_ferror h : mne (s_ferror HO h).
Proof. unfold s_ferror. apply mne_ferror. Qed.
Lemma mne_s_fileno h : mne (s_fileno HO h).
Proof. unfold s_fileno. apply mne_fileno. Qed.
Lemma mne_s_fprintf h ps : mne (s_fprintf HO h ps).
Proof. unfold s_fprintf. apply mne_fprintf. Qed.
Lemma mne_s_printf ps : mne (s_printf (H:=H) (hptr:=hptr) ps).
Proof. unfold s_printf. apply mne_printf. Qed.
Lemma mne_s_remove p : mne (s_remove (H:=H) (hptr:=hptr) p).
Proof. unfold s_remove. apply mne_remove. Qed.
Lemma mne_s_unlink p : mne (s_unlink (H:=H) (hptr:=hptr) p).
Proof. unfold s_unlink. apply mne_unlink. Qed.
Lemma mne_s_mkstemp t : mne (s_mkstemp (H:=H) (hptr:=hptr) t).
Proof. unfold s_mkstemp. apply mne_mkstemp. Qed.
Lemma mne_s_close fd : mne (s_close (H:=H) (hptr:=hptr) fd).
Proof. unfold s_close. apply mne_close. Qed.
Lemma mne_s_get_errno : mne (s_get_errno (H:=H) (hptr:=hptr)).
Proof. unfold s_get_errno. apply mne_get_errno. Qed.
Lemma mne_s_stdio_exit : mne (s_stdio_exit (H:=H) (hptr:=hptr)).
Proof. unfold s_stdio_exit. apply mne_stdio_exit. Qed.

(* [comment removed for export] *)
Lemma prims_noexit : prims_ok (MOps (H:=H) (hptr:=hptr)) (prims HO FO stk) (fun A m => mne m).
Proof.
  constructor; cbn [mo_ret mo_bind mo_unr MOps prims e_fopen_r e_fopen_w e_fclose e_fread e_fwrite e_ferror e_fileno e_last_errno
                    e_fprintf e_printf e_malloc e_calloc e_realloc e_free e_mkstemp e_close_fd e_remove e_unlink
                    e_get_outfile e_set_outfile e_fenter e_fret].
  - intros A a. apply mne_ret.
  - intros A B m f Hm Hf. apply mne_bind; assumption.
  - intros A. apply mne_unr.
  - intros n. apply mne_s_fopen.
  - intros n. apply mne_s_fopen.
  - exact mne_s_fclose.
  - intros f d n. apply mne_bind; [apply mne_get| intros s; apply mne_s_fread].
  - exact mne_s_fwrite.
  - exact mne_s_ferror.
  - exact mne_s_fileno.
  - exact mne_s_get_errno.
  - exact mne_s_fprintf.
  - exact mne_s_printf.
  - exact mne_pmalloc.
  - exact mne_pcalloc.
  - exact mne_prealloc.
  - exact mne_pfree.
  - exact mne_s_mkstemp.
  - exact mne_s_close.
  - exact mne_s_remove.
  - exact mne_s_unlink.
  - apply mne_bind; [apply mne_get| intros s; apply mne_ret].
  - intros o. apply mne_upd.
  - exact FO_enter.
  - exact FO_ret.
Qed.

Lemma mne_fuzz_one data : mne (LLVMFuzzerTestOneInput MOps (prims HO FO stk) data).
Proof. exact (ok_LLVMFuzzerTestOneInput MOps (prims HO FO stk) (fun A m => mne m) prims_noexit data). Qed.

(* [comment removed for export] *)
Lemma harness_call_zero data : mall noexit (harness_call HO FO stk data) (fun rc => rc = 0).
Proof.
  unfold harness_call. apply mall_bind_true; [exact (mne_fuzz_one data)|]. intros _. apply mall_ret. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mne_emit_d_ps rc : mne (emit_d get_lc set_lc rc).
Proof. apply mne_emit_d. Qed.

Lemma call_loop_flag n : forall data bad,
  mall noexit (call_loop (emit_d get_lc set_lc) (harness_call HO FO stk) n data bad) (fun b => b = bad).
Proof.
  induction n as [|n IH]; intros data bad; cbn [call_loop]; [apply mall_ret; reflexivity|].
  eapply mall_bind; [apply harness_call_zero|]. intros rc ->.
  apply mall_bind_true; [apply mne_emit_d_ps|]. intros _.
  rewrite bad_rc_step0. apply IH.
Qed.

Lemma run_status config payload : mall noexit (run HO FO stk config payload) (fun r => r = 0 \/ r = 2).
Proof.
  unfold run, target_run. cbv zeta.
  eapply mall_bind with (Q := fun _ => True).
  { destruct (length payload =? 0)%nat; [apply mall_ret; exact I|].
    apply mall_bind_true; [apply mne_pmalloc|]. intros q. apply mall_ret. exact I. }
  intros [o|] _; [| apply mall_ret; right; reflexivity].
  eapply mall_bind; [apply call_loop_flag|]. intros bad ->.
  apply mall_bind_true; [destruct o; [apply mne_pfree| apply mne_ret]|]. intros _.
  apply mall_ret. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mne_diag d : mne (diag (H:=H) (hptr:=hptr) d).
Proof.
  destruct d; cbn [diag].
  - exact (mne_diag_usage _ _ _).
  - exact (mne_diag_cannot_open _ _ _).
  - exact (mne_diag_read_error _ _ _).
  - exact (mne_diag_oom _ _).
  - exact (mne_diag_too_big _ _).
  - exact (mne_diag_short_hdr _ _).
  - exact (mne_diag_cfg_overrun _ _).
Qed.
Hint Resolve mne_diag : mne.

Lemma mne_read_loop_body rs fd path st : mne (read_loop_body (diag (H:=H) (hptr:=hptr)) (pmalloc HO) (pfree HO) rs fd path st).
Proof. unfold read_loop_body. mne_go. Qed.
Hint Resolve mne_read_loop_body : mne.

Lemma mne_read_all rs path : mne (read_all (diag (H:=H) (hptr:=hptr)) (pmalloc HO) (pfree HO) rs path).
Proof. unfold read_all. mne_go. Qed.

Lemma main_status argv : mall noexit (main_prog HO FO stk argv) (fun r => r = 0 \/ r = 2).
Proof.
  unfold main_prog, main_model.
  destruct (negb (Z.of_nat (length argv) =? 2)).
  { apply mall_bind_true; [apply mne_diag|]. intros _. apply mall_ret. right; reflexivity. }
  apply mall_bind_true; [apply mne_read_all|]. intros [|buf content]; [apply mall_ret; right; reflexivity|].
  cbv zeta.
  destruct (zlength content <? HDR_MIN).
  { apply mall_bind_true; [apply mne_diag|]. intros _. apply mall_bind_true; [apply mne_pfree|]. intros _. apply mall_ret. right; reflexivity. }
  destruct (zlength content <? HDR_MIN + Z.land (le16 content) 32767).
  { apply mall_bind_true; [apply mne_diag|]. intros _. apply mall_bind_true; [apply mne_pfree|]. intros _. apply mall_ret. right; reflexivity. }
  eapply mall_bind; [apply run_status|]. intros status Hst.
  apply mall_bind_true; [apply mne_pfree|]. intros _. apply mall_ret.
  destruct (Z.testbit (le16 content) 15); [left; reflexivity| exact Hst].
Qed.

(* [comment removed for export] *)
Lemma mne_startup tb : mne (startup_model (set_tls_pin HO) tb).
Proof. unfold startup_model. mne_go. Qed.

Lemma exit_model_ok code : code = 0 \/ code = 2 ->
  mall (exits_ok in02) (exit_model (s_stdio_exit (H:=H) (hptr:=hptr)) code) (fun _ => True).
Proof.
  intros Hc. unfold exit_model. apply mall_bind_true; [apply mne_mall; apply mne_s_stdio_exit|]. intros _.
  apply mall_sys_true. cbn [exits_ok]. destruct Hc as [-> | ->]; [exact in02_0| exact in02_2].
Qed.

Lemma prog_ok tb argv : mall (exits_ok in02) (prog HO tb FO stk argv) (fun _ => True).
Proof.
  unfold prog. apply mall_bind_true; [apply mne_mall; apply mne_startup|]. intros _.
  eapply mall_bind.
  { intros s. eapply tall_mono; [apply (noexit_exits_ok in02)| intros r Hr; exact Hr| exact (main_status argv s)]. }
  intros code Hc. apply exit_model_ok. exact Hc.
Qed.

Theorem prog_exits_in tb h0 argv mo :
  exits_in nstep nexit (prog_itree HO tb h0 FO stk argv) mo in02.
Proof.
  unfold prog_itree, ebind. apply exits_in_bind. split.
  - eapply tall_exits_in. exact (prog_ok tb (argv_Z argv) (ps_init h0)).
  - intros tr [|[a s]] mo' _; [exact I| destruct a].
Qed.

End Prog.

(* [comment removed for export] *)
Lemma fo_nop_enter {H hptr : Type} : forall A f (m : M (PState H hptr) A), mne m -> mne (fo_enter fo_nop A f m).
Proof. intros A f m Hm. exact Hm. Qed.
Lemma fo_nop_ret {H hptr : Type} : forall A f (x : A), mne (St:=PState H hptr) (fo_ret fo_nop A f x).
Proof. intros A f x. apply mne_ret. Qed.

End WithCeil.
