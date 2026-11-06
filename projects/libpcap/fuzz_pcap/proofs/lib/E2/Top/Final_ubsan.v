(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Ceiling ImgSrc3 ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.EntryRnd.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require StartupFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant HeapFull. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StartupFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UPcapB__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UPcapA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.SimMain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.EquivMain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.EquivFinal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require Import TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Import EntryCeil.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_main_A__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blk__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkB__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pp_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_chkD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Ifaces_heap__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Stdio_glue_fo__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_core__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Stdio_final_pf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_main_A__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blk__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chk__U3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkB__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pp_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blk__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcapng_ai__U3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blk__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_chkD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require Ifaces_heap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Stdio_glue_fo__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Ifaces_heap__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_core__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Stdio_final_pf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module SRCM := Plain.M.
Module TGTM := Ubsan.M.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma image_ok_src3 : image_ok ssegs source_alloc_limit.
Proof.
  constructor.
  - exact (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Compose.floor_free_ssegs (CEILV := ceil_of_sp (Z_to_bv 64 0))).   (* [comment removed for export] *)
  - vm_compute. reflexivity.
  - vm_compute. discriminate.
  - vm_compute. discriminate.
  - vm_compute. discriminate.
Qed.

(* [comment removed for export] *)
Lemma image_ok_src3_lim : forall lim, BLIVE + RMAX <= lim -> image_ok ssegs lim.
Proof. intros lim H. destruct image_ok_src3 as [A B C D _]. exact (mkImageOk ssegs lim A B C D H). Qed.

Lemma image_ok_ubsan : image_ok usegs target_alloc_limit.
Proof.
  constructor.
  - exact (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Compose.TwB.floor_free_usegs (CEILV := ceil_of_sp (Z_to_bv 64 0))).
  - vm_compute. reflexivity.
  - vm_compute. discriminate.
  - vm_compute. discriminate.
  - vm_compute. discriminate.
Qed.

(* [comment removed for export] *)
Lemma sites_at_ok_S spB : 4304 <= spB -> spB + 8192 < 2^64 -> UPcapA.stk_ok (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.sites_at spB).
Proof. intros A B site. destruct site; cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.sites_at]; lia. Qed.
Lemma sites_at_ok_T spB : 4304 <= spB -> spB + 8192 < 2^64 -> UPcapA.stk_ok (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB.sites_at spB).
Proof. intros A B site. destruct site; cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB.sites_at]; lia. Qed.

(* [comment removed for export] *)
Definition spB (en : ExecEntry) : Z := Z.min (Z.max (bv_unsigned (en_sp en)) sp_window_lo) sp_window_hi - 4640.

Lemma spB_ok en : 4304 <= spB en /\ spB en + 8192 < 2^64.
Proof. unfold spB, sp_window_lo, sp_window_hi. lia. Qed.

Lemma spB_valid img en inp : valid_input inp -> valid_entry img en inp -> spB en = bv_unsigned (en_sp en) - 208 - 4432.
Proof.
  intros VI VE. destruct (valid_entry_sp _ _ _ VI VE) as (VL & VH & _). unfold spB. lia.
Qed.

Lemma sites_S_valid en inp : valid_input inp -> valid_entry (mkImage ssegs SRCM.init_pc SRCM.phdrs) en inp ->
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.sites_at (spB en) = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.ProgImpl.sites en.
Proof. intros VI VE. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.ProgImpl.sites, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.ProgImpl.sites_of, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.FUZZ_FRAME. rewrite (spB_valid _ _ _ VI VE). f_equal; lia. Qed.
Lemma sites_T_valid en inp : valid_input inp -> valid_entry (mkImage usegs TGTM.init_pc TGTM.phdrs) en inp ->
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB.sites_at (spB en) = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.ProgImpl.TwB.sites en.
Proof. intros VI VE. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.ProgImpl.TwB.sites, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.ProgImpl.TwB.sites_of, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB.FUZZ_FRAME. rewrite (spB_valid _ _ _ VI VE). f_equal; lia. Qed.

(* [comment removed for export] *)
Definition sec (en : ExecEntry) : Z := bv_unsigned (malloc_secret (en_draw en)).
Lemma sec_range en : 0 <= sec en < 2^64.
Proof. unfold sec. pose proof (bv_unsigned_in_range 64 (malloc_secret (en_draw en))) as H. change (bv_modulus 64) with (2^64) in H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Pieces.
  Context {CEILV : CEIL}.
  #[local] Notation KS := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Ifaces_heap.KS.
  #[local] Notation KT := U3.Ifaces_heap.KS.

  (* [comment removed for export] *)
  Let SFL_S := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_stdio_fp_law.
  Let HFL_S := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Ifaces_heap.KS_heap_frame_law.
  (* [comment removed for export] *)
  Let HCB_S : S3.GI.heap_cb_law KS := fun h R LB m b HH => HH.
  Let SCB_S : S3.GI.stdio_cb_law KS := fun l R FB m b HS => HS.
  Let HAL_S := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Ifaces_heap.KS_heap_addr_law.
  Let HPL_S := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Ifaces_heap.KS_heap_perm_law.
  (* [comment removed for export] *)
  Let VPR_S := S3.Stdio_final_pf.KS_vprintf_d.
  Let EPR_USAGE_S := S3.Stdio_final_pf.KS_eprintf_usage.
  Let EPR_OPEN_S := S3.Stdio_final_pf.KS_eprintf_cannot_open.
  Let EPR_READ_S := S3.Stdio_final_pf.KS_eprintf_read_error.
  Let EPR_BIG_S := S3.Stdio_final_pf.KS_eprintf_too_big.
  Let PRINTF_R_S := S3.Stdio_final_pf.KS_printf_failed_remove.
  Let PRINTF_O_S := S3.Stdio_final_pf.KS_printf_failed_open.
  Let FPRINTF_DD_S := S3.Stdio_final_pf.KS_fprintf_packet_length.
  Let FPRINTF_S_S := S3.Stdio_final_pf.KS_fprintf_couldnt_open.
  Let SNPRINTF_S := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.Stdio_glue_sn.snprintf_proof KS.
  Let VSNPRINTF_S := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.Stdio_glue_sn.vsnprintf4_proof KS.
  Let STRERROR_S := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_err.pcap_strerror_proof KS HFL_S SFL_S.
  Let FMT_S := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.F_fmt_errmsg.fmt_errmsg_proof KS HFL_S SFL_S VSNPRINTF_S SNPRINTF_S STRERROR_S.
  Let OPEN_COMMON_S := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.open_offline_common_proof full_ops KS stk HFL_S SFL_S (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Ifaces_heap.KS_calloc_o SFL_S) FMT_S.
  (* [comment removed for export] *)
  Let RBYTES_S := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_sfpcapng_rb.read_bytes_proof full_ops KS stk HFL_S SFL_S OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_fread_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_ferror_o FMT_S SNPRINTF_S.
  Let RBLOCK_S := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.F_sfpcapng_blk.read_block_proof full_ops KS stk HFL_S SFL_S HPL_S HAL_S OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_fread_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_ferror_o FMT_S SNPRINTF_S (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Ifaces_heap.KS_realloc_o SFL_S).
  Let ADDIF_S := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_ai.add_interface_proof full_ops KS stk HFL_S SFL_S HPL_S (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Ifaces_heap.KS_malloc_o SFL_S) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Ifaces_heap.KS_realloc_o SFL_S) SNPRINTF_S.
  Let CHK_NG_S := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.F_sfpcapng_chk.pcap_ng_check_header_proof full_ops KS stk HFL_S SFL_S HPL_S HAL_S (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Ifaces_heap.KS_free_o SFL_S) SNPRINTF_S OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_fread_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_ferror_o FMT_S (OPEN_COMMON_S stk) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Ifaces_heap.KS_malloc_o SFL_S) (RBYTES_S stk) (RBLOCK_S stk) (ADDIF_S stk).
  Let NP_NG_S := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_ngnext.pcap_ng_next_packet_proof full_ops KS stk HFL_S SFL_S HPL_S SNPRINTF_S OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_B__S3.F_pp_main.post_process_proof OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure.adjust_snapshot_proof (RBLOCK_S stk) (ADDIF_S stk).
  Let CHK_PCAP_S := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_chk.pcap_check_header_proof full_ops KS stk HFL_S SFL_S OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_fread_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_ferror_o
                                 FMT_S SNPRINTF_S HPL_S (OPEN_COMMON_S stk) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Ifaces_heap.KS_malloc_o SFL_S) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Ifaces_heap.KS_free_o SFL_S).
  Let FOPEN_OFFLINE_S := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.fopen_offline_proof full_ops KS stk HFL_S SFL_S OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_fread_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_ferror_o
                                      OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_fileno_o FMT_S SNPRINTF_S (CHK_PCAP_S stk) (CHK_NG_S stk).
  Let POPEN_S := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.open_offline_proof full_ops KS stk HFL_S SFL_S FMT_S HAL_S OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_fopen_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_fclose_o (FOPEN_OFFLINE_S stk).
  Let NP_PCAP_S := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_next.pcap_next_packet_proof full_ops KS stk HFL_S SFL_S HPL_S HAL_S OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_fread_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_ferror_o
                                FMT_S SNPRINTF_S (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Ifaces_heap.KS_realloc_o SFL_S) OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_B__S3.F_pp_main.post_process_proof.
  Let PNEXT_S := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex.next_ex_proof full_ops KS stk HFL_S SFL_S (NP_PCAP_S stk) (NP_NG_S stk).
  Let PSTATS_S := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.pcap_stats_proof KS HFL_S SFL_S.
  Let PCLOSE_S := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_close.pcap_close_proof full_ops KS stk HFL_S SFL_S OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_fclose_o (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Ifaces_heap.KS_free_o SFL_S).

  (* [comment removed for export] *)
  Let SFL_T := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_stdio_fp_law.
  Let HFL_T := U3.Ifaces_heap.KS_heap_frame_law.
  Let HCB_T : S3.GI.TwB.heap_cb_law KT := fun h R LB m b HH => HH.
  Let SCB_T : S3.GI.TwB.stdio_cb_law KT := fun l R FB m b HS => HS.
  Let HAL_T := U3.Ifaces_heap.KS_heap_addr_law.
  Let HPL_T := U3.Ifaces_heap.KS_heap_perm_law.
  Let VPR_T := S3.Stdio_final_pf.TwB.KS_vprintf_d.
  Let EPR_USAGE_T := S3.Stdio_final_pf.TwB.KS_eprintf_usage.
  Let EPR_OPEN_T := S3.Stdio_final_pf.TwB.KS_eprintf_cannot_open.
  Let EPR_READ_T := S3.Stdio_final_pf.TwB.KS_eprintf_read_error.
  Let EPR_BIG_T := S3.Stdio_final_pf.TwB.KS_eprintf_too_big.
  Let PRINTF_R_T := S3.Stdio_final_pf.TwB.KS_printf_failed_remove.
  Let PRINTF_O_T := S3.Stdio_final_pf.TwB.KS_printf_failed_open.
  Let FPRINTF_DD_T := S3.Stdio_final_pf.TwB.KS_fprintf_packet_length.
  Let FPRINTF_S_T := S3.Stdio_final_pf.TwB.KS_fprintf_couldnt_open.
  Let SNPRINTF_T := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.Stdio_glue_sn.TwB.snprintf_proof KT.
  Let VSNPRINTF_T := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core__S3.Stdio_glue_sn.TwB.vsnprintf4_proof KT.
  Let STRERROR_T := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_err.TwB.pcap_strerror_proof KT HFL_T SFL_T.
  Let FMT_T := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.F_fmt_errmsg.TwB.fmt_errmsg_proof KT HFL_T SFL_T VSNPRINTF_T SNPRINTF_T STRERROR_T.
  Let OPEN_COMMON_T := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB.open_offline_common_proof full_ops KT stk HFL_T SFL_T (U3.Ifaces_heap.KS_calloc_o SFL_T) FMT_T.
  Let CHK_PCAP_T := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chk__U3.F_sfpcap_chk.pcap_check_header_proof full_ops KT stk HFL_T SFL_T OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_fread_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_ferror_o
                                 FMT_T SNPRINTF_T HPL_T (OPEN_COMMON_T stk) (U3.Ifaces_heap.KS_malloc_o SFL_T) (U3.Ifaces_heap.KS_free_o SFL_T).
  Let RBYTES_T := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_sfpcapng_rb.TwB.read_bytes_proof full_ops KT stk HFL_T SFL_T OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_fread_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_ferror_o FMT_T SNPRINTF_T.
  Let RBLOCK_T := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.F_sfpcapng_blk.TwB.read_block_proof full_ops KT stk HFL_T SFL_T HPL_T HAL_T OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_fread_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_ferror_o FMT_T SNPRINTF_T (U3.Ifaces_heap.KS_realloc_o SFL_T).
  Let ADDIF_T := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcapng_ai__U3.F_sfpcapng_ai.add_interface_proof full_ops KT stk HFL_T SFL_T HPL_T (U3.Ifaces_heap.KS_malloc_o SFL_T) (U3.Ifaces_heap.KS_realloc_o SFL_T) SNPRINTF_T.
  Let CHK_NG_T := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.F_sfpcapng_chk.TwB.pcap_ng_check_header_proof full_ops KT stk HFL_T SFL_T HPL_T HAL_T (U3.Ifaces_heap.KS_free_o SFL_T) SNPRINTF_T OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_fread_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_ferror_o FMT_T (OPEN_COMMON_T stk) (U3.Ifaces_heap.KS_malloc_o SFL_T) (RBYTES_T stk) (RBLOCK_T stk) (ADDIF_T stk).
  Let NP_NG_T := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_ngnext.TwB.pcap_ng_next_packet_proof full_ops KT stk HFL_T SFL_T HPL_T SNPRINTF_T OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_B__S3.F_pp_main.TwB.post_process_proof OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure.TwB.adjust_snapshot_proof (RBLOCK_T stk) (ADDIF_T stk).
  Let FOPEN_OFFLINE_T := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB.fopen_offline_proof full_ops KT stk HFL_T SFL_T OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_fread_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_ferror_o
                                      OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_fileno_o FMT_T SNPRINTF_T (CHK_PCAP_T stk) (CHK_NG_T stk).
  Let POPEN_T := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB.open_offline_proof full_ops KT stk HFL_T SFL_T FMT_T HAL_T OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_fopen_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_fclose_o (FOPEN_OFFLINE_T stk).
  Let NP_PCAP_T := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_next.TwB.pcap_next_packet_proof full_ops KT stk HFL_T SFL_T HPL_T HAL_T OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_fread_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_ferror_o
                                FMT_T SNPRINTF_T (U3.Ifaces_heap.KS_realloc_o SFL_T) OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_B__S3.F_pp_main.TwB.post_process_proof.
  Let PNEXT_T := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex.TwB.next_ex_proof full_ops KT stk HFL_T SFL_T (NP_PCAP_T stk) (NP_NG_T stk).
  Let PSTATS_T := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB.pcap_stats_proof KT HFL_T SFL_T.
  Let PCLOSE_T := fun stk => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_close.TwB.pcap_close_proof full_ops KT stk HFL_T SFL_T OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_fclose_o (U3.Ifaces_heap.KS_free_o SFL_T).


  #[using="SFL_S HFL_S HCB_S SCB_S HAL_S HPL_S VPR_S EPR_USAGE_S EPR_OPEN_S EPR_READ_S EPR_BIG_S PRINTF_R_S PRINTF_O_S FPRINTF_DD_S FPRINTF_S_S SNPRINTF_S VSNPRINTF_S STRERROR_S FMT_S OPEN_COMMON_S RBYTES_S RBLOCK_S ADDIF_S CHK_NG_S NP_NG_S CHK_PCAP_S FOPEN_OFFLINE_S POPEN_S NP_PCAP_S PNEXT_S PSTATS_S PCLOSE_S"] Lemma impl_S_ce : forall (rnd0 : EntryDraw) en inp,
    valid_entry (mkImage ssegs SRCM.init_pc SRCM.phdrs) en inp -> valid_input inp ->
    OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.ProgImpl.EN_OK rnd0 en ->
    impl ssegs (at_node ssegs) (npeek ssegs)
         (prog_itree full_ops 0x339d0 (fheap_init (bv_unsigned (malloc_secret rnd0)) (reservedZ ssegs)) fo_nop (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.ProgImpl.sites en) (in_argv inp))
         (epost (fun (_ : unit) (_ : machine_state) => True)) (ms0 ssegs SRCM.init_pc SRCM.phdrs en inp).
  Proof.
    intros rnd0 en inp VE VI ENOK.
    exact (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.ProgImpl.prog_impl full_ops KS (fheap_init (bv_unsigned (malloc_secret rnd0)) (reservedZ ssegs)) OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_exit.STDIO_EXIT_FRAME rnd0
             OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.STDIO_EXIT_FRAME_range
             HFL_S SFL_S HCB_S SCB_S HAL_S (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Ifaces_heap.KS_heap_init_law rnd0) OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_stdio_init_law
             (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Ifaces_heap.KS_malloc SFL_S) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Ifaces_heap.KS_free SFL_S)
             VPR_S EPR_USAGE_S EPR_OPEN_S EPR_READ_S EPR_BIG_S OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_efwrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_stdio_exit
             OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.EQB_full OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_fopen_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_fclose_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_fwrite_o
             OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_remove_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_unlink_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_close_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.KS_mkstemp_o
             PRINTF_R_S PRINTF_O_S FPRINTF_DD_S FPRINTF_S_S POPEN_S PNEXT_S PSTATS_S PCLOSE_S en inp VE VI ENOK).
  Qed.

  #[using="SFL_T HFL_T HCB_T SCB_T HAL_T HPL_T VPR_T EPR_USAGE_T EPR_OPEN_T EPR_READ_T EPR_BIG_T PRINTF_R_T PRINTF_O_T FPRINTF_DD_T FPRINTF_S_T SNPRINTF_T VSNPRINTF_T STRERROR_T FMT_T OPEN_COMMON_T CHK_PCAP_T RBYTES_T RBLOCK_T ADDIF_T CHK_NG_T NP_NG_T FOPEN_OFFLINE_T POPEN_T NP_PCAP_T PNEXT_T PSTATS_T PCLOSE_T"] Lemma impl_T_ce : forall (rnd0 : EntryDraw) en inp,
    valid_entry (mkImage usegs TGTM.init_pc TGTM.phdrs) en inp -> valid_input inp ->
    OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.ProgImpl.TwB.EN_OK rnd0 en ->
    impl usegs (at_node usegs) (npeek usegs)
         (prog_itree full_ops 0x34190 (fheap_init (bv_unsigned (malloc_secret rnd0)) (reservedZ usegs)) fo_nop (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.ProgImpl.TwB.sites en) (in_argv inp))
         (epost (fun (_ : unit) (_ : machine_state) => True)) (ms0 usegs TGTM.init_pc TGTM.phdrs en inp).
  Proof.
    intros rnd0 en inp VE VI ENOK.
    exact (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.ProgImpl.TwB.prog_impl full_ops KT (fheap_init (bv_unsigned (malloc_secret rnd0)) (reservedZ usegs)) OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_exit.TwB.STDIO_EXIT_FRAME rnd0
             OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.STDIO_EXIT_FRAME_range
             HFL_T SFL_T HCB_T SCB_T HAL_T (U3.Ifaces_heap.KS_heap_init_law rnd0) OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_stdio_init_law
             (U3.Ifaces_heap.KS_malloc SFL_T) (U3.Ifaces_heap.KS_free SFL_T)
             VPR_T EPR_USAGE_T EPR_OPEN_T EPR_READ_T EPR_BIG_T OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_efwrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_stdio_exit
             OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.EQB_full OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_fopen_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_fclose_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_fwrite_o
             OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_remove_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_unlink_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_close_o OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Ifaces_heap__S3.Stdio_final.TwB.KS_mkstemp_o
             PRINTF_R_T PRINTF_O_T FPRINTF_DD_T FPRINTF_S_T POPEN_T PNEXT_T PSTATS_T PCLOSE_T en inp VE VI ENOK).
  Qed.
End Pieces.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tbS : ExecEntry -> Z := fun _ => 0x339d0.
Definition tbT : ExecEntry -> Z := fun _ => 0x34190.
Definition stkS : ExecEntry -> stack_site -> Z := fun en => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.sites_at (spB en).
Definition stkT : ExecEntry -> stack_site -> Z := fun en => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB.sites_at (spB en).

Lemma IMPL_S_final : exists QS, forall en inp, valid_entry (mkImage ssegs SRCM.init_pc SRCM.phdrs) en inp -> valid_input inp ->
  impl ssegs (at_node ssegs) (npeek ssegs) (treeS ssegs tbS stkS sec inp en) QS (ms0 ssegs SRCM.init_pc SRCM.phdrs en inp).
Proof.
  exists (epost (fun (_ : unit) (_ : machine_state) => True)). intros en inp VE VI.
  unfold treeS, ptree, tbS, stkS, sec. rewrite (sites_S_valid en inp VI VE).
  exact (impl_S_ce (CEILV := ceil_of_sp (en_sp en)) (en_draw en) en inp VE VI (conj (entry_ceil_le_top _ _ _ VI VE) eq_refl)).
Qed.

Lemma IMPL_T_final : exists QT, forall en inp, valid_entry (mkImage usegs TGTM.init_pc TGTM.phdrs) en inp -> valid_input inp ->
  impl usegs (at_node usegs) (npeek usegs) (treeT usegs tbT stkT sec inp en) QT (ms0 usegs TGTM.init_pc TGTM.phdrs en inp).
Proof.
  exists (epost (fun (_ : unit) (_ : machine_state) => True)). intros en inp VE VI.
  unfold treeT, ptree, tbT, stkT, sec. rewrite (sites_T_valid en inp VI VE).
  exact (impl_T_ce (CEILV := ceil_of_sp (en_sp en)) (en_draw en) en inp VE VI (conj (entry_ceil_le_top _ _ _ VI VE) eq_refl)).
Qed.

(* [comment removed for export] *)
Theorem fuzz_pcap_ubsan_scfg :
  strong_universal_error_free_T_scfg CFG (mkImage ssegs SRCM.init_pc SRCM.phdrs) (mkImage usegs TGTM.init_pc TGTM.phdrs).
Proof.
  apply (route_abs_main_final_scfg ssegs SRCM.init_pc SRCM.phdrs usegs TGTM.init_pc TGTM.phdrs tbS tbT stkS stkT sec sec
           sec_range sec_range image_ok_src3 image_ok_ubsan).
  - intros en inp _. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Compose.tls_in_image_ssegs.
  - intros en inp _. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Compose.TwB.tls_in_image_usegs.
  - intros en. destruct (spB_ok en) as [A B]. exact (sites_at_ok_S _ A B).
  - intros en. destruct (spB_ok en) as [A B]. exact (sites_at_ok_T _ A B).
  - exact IMPL_S_final.
  - exact IMPL_T_final.
Qed.

(* [comment removed for export] *)
Theorem fuzz_pcap_ubsan_main :
  strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
    ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage SRCM.loaded_segments SRCM.init_pc SRCM.phdrs) (mkImage TGTM.loaded_segments TGTM.init_pc TGTM.phdrs).
Proof.
  apply strong_universal_error_free_T_scfg_budgets_of_scfg. exact fuzz_pcap_ubsan_scfg.
Qed.
