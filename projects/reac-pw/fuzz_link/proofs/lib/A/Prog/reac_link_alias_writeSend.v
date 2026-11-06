(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module paths and module names changed; 1412 of its 1477 lines of code are new or changed and 1240 lines of the source are left out. *)
(* reac_link_alias_write (fuzz_link.asan 0x88f54, listing offset AF_reac_link_alias_write) on image A, THE SEND PIECE:
   from the SEND cut (+0x1f0, `mv s7, a0`) to the EXIT cut (+0x3a4), the request in the frame and nl_talk. It proves
   reac_link_alias_writeDefs.v's obligation `aw_send_obl` from `aw_exit_obl`.

   The walk, as the listing gives it:
     +0x1f0..+0x29c  s7 := the index, s6 := F + 32 (the request), the request's 37 shadow bytes in scope (s2 + 4 ..
                     s2 + 0x27 := 0, s2 + 0x28 := 4): a PLAIN run (the token engine refuses a writable shadow window);
                     it stops at the call of checked_memset (0x53214)
     +0x29c          checked_memset(req + 12, 0, 280): link_ajkit.v aj_gx_intrin_at, op OSet
     +0x2a0..+0x2d4  the five header stores into the request; a plain run to the call of checked_memcpy (0x52d78)
     +0x2d4          checked_memcpy(req + 36, alias, |alias|): aj_gx_intrin_at, op OCpy
     +0x2d8..+0x2fc  nlmsg_len := 32 + ((|alias| + 7) & 0x1fc) at req; a plain run to the call of nl_talk (0x88974)
     +0x2fc          nl_talk(req, nlmsg_len, 0, 0, 0, 0): nl_talk_c.v nl_talk_acontract under SRr_bind
     +0x300..+0x3a0  s5 := a0, the request's shadow out of scope again (0xf8); a plain run to the EXIT cut
   Each stage starts a fresh symbolic state whose atoms are the stage's registers (sr_atoms), so the stages share
   only the memory facts the walk carries (`aws_inv`: aw_base without the registers).

   Proves no function (kind: segment lemma of reac_link_alias_write's walk). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require LinkWalkCall YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkPi LinkWalkSide LinkWalkZsh LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_talk_c reac_link_alias_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_writeDefs reac_link_alias_writeSendA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m AB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* No global sink_head instance is in scope: every journal below is the Section's SK. *)
Fail Definition sink_head_probe_send : YI16.sink_head := _.

(* ---- the symbolic states of the stages: registers as atoms ---- *)
Definition aws_SB : Z := 0x7fff8000.
Definition aws_AF : Z := AF_reac_link_alias_write.
(* the frame's shadow, s2 (atom 18); the stores reach s2 + 4 .. s2 + 0x28 *)
Definition aws_SHR : YP09.region := YP09.mkRegion (Some 18%nat) 0 64 4 41 [].
Definition aws_shfact : afact := mkAF aws_SB (aws_SB + 2 ^ 44) 3.
Definition aws_ss4 : sstate := mkSS (aws_AF + 0x300) sr_atoms [aws_SHR] None (mkFacts [(18%nat, aws_shfact)] [] []).

Lemma aws_consts_val : SHADOW_OFF = aws_SB /\ kLowMemEnd = aws_SB /\ kLowShadowBeg = 0x7fff7000 /\
  kHighMemBeg = 0x10007fff8000 /\ kHighMemEnd = 0x800000000000 /\ YImgTop.IMG_LO = 0x10000 /\
  YImgTop.IMG_TOP = 0x654000 /\ pcap_img_end = 0x654000 /\ LA_G_NL = 0x5dcac0 /\ PCAP_RLO = 0xa1380 /\
  PCAP_RHI = 0xa26c8 /\ fs_frame_bytes AW_CID = 512 /\ fs_frame_bytes AW_CID / 8 = 64 /\ fs_frames AW_CID = 2048.
Proof. repeat split; reflexivity. Qed.

Ltac aws_c :=
  let C := fresh "C" in
  pose proof aws_consts_val as C;
  repeat match type of C with ?A /\ ?B => let C1 := fresh "C" in destruct C as [C1 C]; try rewrite C1 in * end;
  try rewrite C in *; unfold aws_SB, ASAN_CEIL in *.


Lemma aws_set_fs_set_fs : forall f g S, set_fs f (set_fs g S) = set_fs f S.
Proof. intros f g S. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
(* the denotation of a register atom of a stage's environment *)
Lemma aws_atom : forall (R : bvmap 5 word) (n : nat) (r : bv 5),
  Z.of_nat n = bv_unsigned r -> sv_denot (Eimg (Ereg R [])) (SOff n 0) = getr R r.
Proof.
  intros R n r H. cbn [sv_denot]. rewrite (ew_Eimg_Ereg_nat R [] n r H). rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  reflexivity.
Qed.

Lemma aws_ms_eta : forall ms : machine_state, ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr -> ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4. cbn in *. subst. reflexivity. Qed.
Variable B : asyms.
(* the image instance (discharged at PI_link, B := AD2l.PcapB): AR's laws (lib/A/PcapBFacts.v PcapB_LAWS), the listing's
   values (lib/A/Prog/LinkImgInst.v pi_link_vals), the start-up symbols (AD2l.PcapB_syms), the image's segments
   (LinkImgInst.v pi_link_segs) and the relro window inside the image (LinkImgInst.v link_relro_img). *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
(* the callee contracts: checked_memset (lib/A/AE2r.v asan_memset_realizes), checked_memcpy (lib/A/AE2q.v
   asan_memcpy_realizes), nl_talk (lib/A/Prog/nl_talk.v nl_talk_aproof) *)
Hypothesis AMSET : aintrin_realizes SEGS B OSet (pa_sigma LS___asan_memset).
Hypothesis AMCPY : aintrin_realizes SEGS B OCpy (pa_sigma LS___asan_memcpy).
Hypothesis NLT : nl_talk_acontract SK SEGS PCAP_RLO PCAP_RHI B.

(* what every journal says: its AR, and its window above the allocator's ceiling and below 2 ^ 47 *)
Lemma aws_aj_ar : forall G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k -> AR SEGS B ly' S' W' mem' md'.
Proof. intros G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJ & _) & _). exact (proj1 HJ). Qed.

Lemma aws_aj_row : forall G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k ->
  0 <= STK /\ 0 <= XO /\ alloc_ceiling <= sp0 - STK /\ sp0 + XO <= 2 ^ 47.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k (HSTK & HXO & (memS & HJ & _) & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _). lia.
Qed.

(* ---- the image's segments: g_nl and errno are writable at any memory, and the runtime's statics, errno and the
   write set are off the read-only set (computations over tfibsegs) ---- *)
Lemma aws_gnl_writable : forall m a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> writable_at SEGS m a.
Proof. rewrite HSEGS. intros m a Ha. apply LA_G_NL_writable. unfold NK_SIZE in Ha. exact Ha. Qed.

Lemma aws_errno_val : as_errno B = 0x631b6c.
Proof. rewrite (ts_errno B TB). reflexivity. Qed.

Lemma aws_wseg_errno : YK1d.wseg_ok tfibsegs (Z_to_bv 64 0x631b6c) (Z.to_nat 4) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma aws_errno_writable : forall m a, as_errno B <= a < as_errno B + 4 -> writable_at SEGS m a.
Proof.
  rewrite aws_errno_val, HSEGS. intros m.
  apply writable_at_of_wseg; [lia | lia | exact aws_wseg_errno].
Qed.

Lemma aws_ro_img : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> in_img SEGS a.
Proof. intros a [(s & Hs & _ & Hb) | Hr]; [exists s; split; [exact Hs | exact Hb] | exact (RELRO_IMG a Hr)]. Qed.

(* the read-only image facts across a callee whose write set is off the read-only set: akept's image clause (it
   excepts the runtime's statics and errno, which arodata_okP excepts too) *)
Lemma aws_arodata_call : forall lyc Sc (W : world SEGS) m W2 m2 slo shi (E : Z -> Prop),
  akept SEGS B lyc Sc W m W2 m2 slo shi E ->
  (forall a, E a -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) m) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) m2).
Proof.
  intros lyc Sc W m W2 m2 slo shi E (_ & _ & K3 & _) HE Hro a Ha Ho He.
  rewrite (K3 a (aws_ro_img a Ha) Ho He (fun HEa => HE a HEa Ha)). exact (Hro a Ha Ho He).
Qed.

(* the length word's ALU expression (+0x2d8..+0x2e0): 32 + ((|alias| + 7) & 0x1fc) *)
Lemma aws_denot_and508 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  sv_denot E (SAlu ALU_AND (SOff n 7) (SLit 508)) = Z_to_bv 64 (Z.land (v + 7) 508).
Proof.
  intros E n v Hn Hv. rewrite denot_lit_U. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v 7 Hn) by lia.
  change (zcanon 508) with 508. rewrite aws_land_508 by lia. apply zcanon_id. unfold M64. lia.
Qed.

Lemma aws_denot_len : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n 7) (SLit 508)) (SLit 32)) = Z_to_bv 64 (Z.land (v + 7) 508 + 32).
Proof.
  intros E n v Hn Hv. rewrite denot_lit_U. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 32) with 32.
  assert (HU : U E (SAlu ALU_AND (SOff n 7) (SLit 508)) = Z.land (v + 7) 508).
  { unfold U. rewrite (aws_denot_and508 E n v Hn Hv). apply unsigned_lit_small. rewrite aws_land_508 by lia. lia. }
  rewrite HU, aws_land_508 by lia. apply zcanon_id. unfold M64. lia.
Qed.

Lemma aws_len_val : forall v, 0 <= v < 256 -> Z.land (v + 7) 508 + 32 = 32 + nl_align (RTA_HDR + v).
Proof. intros v Hv. rewrite aws_land_508 by lia. unfold nl_align, RTA_HDR. lia. Qed.

(* a register's value through an own call's aregs_preserved *)
Lemma aws_pres : forall (R R2 : bvmap 5 word) (r : Z) v, aregs_preserved R R2 -> acallee_saved r ->
  getr R (Z_to_bv 5 r) = v -> getr R2 (Z_to_bv 5 r) = v.
Proof. intros R R2 r v P Hr H. rewrite (P r Hr). exact H. Qed.

Lemma aws_vm_keep : forall (m m' : word -> option byte) a (n : nat) v, val_mem SEGS m a n v ->
  (forall k, (k < n)%nat -> mbyte SEGS m' (a + Z.of_nat k) = mbyte SEGS m (a + Z.of_nat k)) -> val_mem SEGS m' a n v.
Proof. intros m m' a n v Hv Hk k Hlt. rewrite (Hk k Hlt). exact (Hv k Hlt). Qed.

(* ==========================================================================
   1. The call's context and the invariant every stage carries
   ========================================================================== *)
Section c.
Variable cx : awcx.
Variable fpos : Z.
#[local] Notation F := (aw_F cx fpos).
#[local] Notation SH := (aw_SH cx fpos).
#[local] Notation Eacc := (fun a => aw_E cx a \/ aside_rng (aw_lyc cx) AW_CID fpos a).
#[local] Notation AJ ly S W m md :=
  (ajournal_gx SEGS B (aw_G cx) (aw_XO cx) (aw_OUT cx) (aw_STK cx) (aw_sp0 cx) (aw_FP cx)
     (aw_ly cx) (aw_S cx) (aw_W0 cx) (aw_mem0 cx) (aw_md0 cx) ((AW_CID, fpos) :: aw_own cx) ly S W m md (aw_k cx)).

Hypothesis HPRE : aw_pre SK B cx.
Hypothesis HNIN : ~ In (AW_CID, fpos) (frames (aw_Sc cx)).
Hypothesis HS1 : exists S1 W1 mem1 md1, AR SEGS B (aw_lyc cx) S1 W1 mem1 md1 /\
  frames S1 = (AW_CID, fpos) :: frames (aw_Sc cx) /\ ablocks B (aw_lyc cx) S1 = ablocks B (aw_lyc cx) (aw_Sc cx).
(* the cut's strings, table and kernel bytes (aw_gi_send), at the call's memory *)
Variables (sn sa : list byte) (tab : list (list byte * Z)) (kbs : list byte).
Hypothesis HNK : anlk_at SEGS (aw_m0 cx) LA_G_NL kbs.
Hypothesis HIT : aiftab_at SEGS (aw_m0 cx) LA_G_NL kbs tab.
Hypothesis HSN : acstr_at SEGS (aw_m0 cx) (aw_name cx) sn.
Hypothesis HN0 : aw_name cx <> 0.
Hypothesis HSNE : sn <> [].
Hypothesis HSA : acstr_at SEGS (aw_m0 cx) (aw_alias cx) sa.
Hypothesis HA0 : aw_alias cx <> 0.
Hypothesis HAL : Z.of_nat (length sa) < ALIAS_MAX.
Hypothesis HIDX : index_of tab sn <> 0.
(* the EXIT piece (lib/A/Prog/reac_link_alias_writeExit.v): the walk from the EXIT cut to the Post *)
Hypothesis EXIT : aw_exit_obl SK B.

(* the call's journal, its G and its window *)
Lemma aws_pre_j : ajournal_gx SEGS B (aw_G cx) (aw_XO cx) (aw_OUT cx) (aw_STK cx) (aw_sp0 cx) (aw_FP cx)
  (aw_ly cx) (aw_S cx) (aw_W0 cx) (aw_mem0 cx) (aw_md0 cx) (aw_own cx)
  (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) (aw_mdc cx) (aw_k cx).
Proof. exact (proj1 (proj1 HPRE)). Qed.

Lemma aws_pre_g : gx_ok SEGS B (aw_G cx).
Proof. exact (proj1 (proj2 (proj1 HPRE))). Qed.

Lemma aws_pre_ar : AR SEGS B (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) (aw_mdc cx).
Proof. exact (aws_aj_ar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ aws_pre_j). Qed.

(* a plain run of the walk's own code on the caller's journal (LinkWalkSide.v paj_run_to_plain_x /
   paj_run_call_plain_x), its end state computed. The listing tree is read off the lemma's own type, so the run
   equation matches it syntactically (the Head piece's pattern). *)
Ltac aws_run_to HS HJ stop :=
  let RUNT := constr:(paj_run_to_plain_x SK B LAWS (aw_G cx) aws_pre_g (aw_XO cx) (aw_OUT cx)) in
  let T := type of RUNT in
  lazymatch T with context [sym_run_toN_pi ?tpi _ _ _] =>
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_run_toN_pi tpi FUEL stop ss) in
    lazymatch r with
    | (?ss', ?st) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_run_toN_pi tpi FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
      let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
      eapply (RUNT W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
      clear Hrun
    end
  end end.
Ltac aws_run_call HS HJ :=
  let RUNC := constr:(paj_run_call_plain_x SK B LAWS (aw_G cx) aws_pre_g (aw_XO cx) (aw_OUT cx)) in
  let T := type of RUNC in
  lazymatch T with context [sym_runN_pi ?tpi _ _] =>
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
    lazymatch r with
    | (?ss', PRS_call ?s) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', PRS_call s)) by (vm_compute; reflexivity);
      let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
      eapply (RUNC W FUEL E ss ss' s ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ);
      clear Hrun
    end
  end end.

Lemma aws_win : aw_sp cx mod 16 = 0 /\ alloc_ceiling <= aw_sp0 cx - aw_STK cx /\
  aw_sp0 cx - aw_STK cx <= aw_sp cx - 8560 /\ aw_sp cx <= aw_sp0 cx /\ aw_sp0 cx <= 2 ^ 47 /\
  aw_sp cx - 112 <= aw_sp1 cx <= aw_sp cx - 96 /\ aw_sp1 cx mod 32 = 0 /\ aw_sp1 cx mod 16 = 0.
Proof.
  destruct HPRE as ((HJ & _ & _ & _ & _ & _ & _ & H16 & Hlo & Hhi & _) & _ & _).
  destruct (aws_aj_row _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (R1 & R2 & R3 & R4).
  pose proof asan_consts as ((C1a & C1b) & _).
  rewrite REAC_LINK_ALIAS_WRITE_AK_val in Hlo.
  fold (aw_sp cx) in H16, Hlo, Hhi.
  destruct (sp1_facts (aw_sp cx - 96) ltac:(lia) ltac:(rewrite Zminus_mod, H16; reflexivity)) as (S1 & S2 & S3).
  unfold aw_sp1, AW_FRAME. repeat split; lia.
Qed.

(* the frame F, from the frame witness *)
Lemma aws_F : 4096 <= F /\ F + 512 <= alloc_ceiling /\ F mod 64 = 0 /\ in_app F 512 /\ off_img F 512 /\
  0 <= fpos < fs_frames AW_CID.
Proof.
  destruct HS1 as (S1 & W1 & mem1 & md1 & HAR & Hfr & _).
  assert (Hin : In (AW_CID, fpos) (frames S1)) by (rewrite Hfr; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ S1 W1 mem1 md1 _ _ HAR Hin) as (H1 & H2 & H3).
  destruct (frame_al64 SEGS B _ S1 W1 mem1 md1 _ _ HAR Hin) as (H4 & _).
  pose proof (frm_off_imgP B _ S1 W1 mem1 md1 _ _ HAR Hin) as H5.
  destruct HAR as [M _]. destruct (frame_facts B _ S1 _ _ _ M Hin) as (_ & H6 & _).
  change (fs_frame_bytes AW_CID) with 512 in *. unfold aw_F. exact (conj H1 (conj H2 (conj H4 (conj H3 (conj H5 H6))))).
Qed.

Lemma aws_SH_val : SH = aws_SB + F / 8 /\ SH mod 8 = 0 /\ aws_SB + 512 <= SH /\ SH + 64 <= kHighMemBeg /\
  SH + 64 <= alloc_ceiling.
Proof.
  destruct aws_F as (H1 & H2 & H3 & _). pose proof asan_consts as ((C1a & C1b) & _).
  unfold aw_SH. aws_c. repeat split; lia.
Qed.

(* the facts of the contract's Pre the stages read, at the call's memory *)
Lemma aws_pre_ajw : forall a, inFP (aw_wr cx) a ->
  ajw B (aw_G cx) (aw_XO cx) (aw_OUT cx) (aw_STK cx) (aw_sp0 cx) (aw_FP cx) (aw_ly cx) (aw_S cx)
    (aw_lyc cx) (aw_Sc cx) (aw_own cx) a.
Proof. destruct HPRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _) & _). exact H. Qed.

Lemma aws_pre_nro : forall a, inFP (aw_wr cx) a -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a.
Proof. destruct HPRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H) & _). exact H. Qed.

Lemma aws_wr_eq : forall a, inFP (aw_wr cx) a <-> LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4.
Proof.
  intros a. unfold aw_wr, reac_link_alias_write_awr. split.
  - intros (r & [<- | []] & H). exact H.
  - intros H. exists (LA_G_NL, LA_G_NL + NK_N_SENT + 4). split; [left; reflexivity | exact H].
Qed.

(* THE INVARIANT a stage carries: aw_base without the registers and the machine state's shape *)
Definition aws_inv (ly : alayout) (S : astate) (W : world SEGS) (m : word -> option byte) (md : Model) : Prop :=
  AJ ly S W m md /\
  frames S = (AW_CID, fpos) :: frames (aw_Sc cx) /\
  (exists fs, S = set_fs fs (aw_Sc cx)) /\
  Permutation (ablocks B ly S) (ablocks B (aw_lyc cx) (aw_Sc cx)) /\
  (forall c q, frame_addr ly c q = frame_addr (aw_lyc cx) c q) /\
  rdword (aview SEGS (w_H W) m) (aw_sp cx - 8) = Some (raZ (aw_regs cx)) /\
  (forall j, 0 <= j < 9 -> rdword (aview SEGS (w_H W) m) (aw_sp cx - 16 - 8 * j) =
     Some (bv_unsigned (getr (aw_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) /\
  rdword (aview SEGS (w_H W) m) (F + AW_FLAGPTR) = Some (aw_FL cx fpos) /\
  akept SEGS B (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) W m
    (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) Eacc /\
  m_fds md = m_fds (aw_mdc cx) /\ m_fs md = m_fs (aw_mdc cx) /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) m).

Lemma aws_inv_of_base : forall ly S W ms md, aw_base SK B cx fpos ly S W ms md -> aws_inv ly S W (ms_mem ms) md.
Proof.
  intros ly S W ms md (_ & _ & _ & _ & _ & HJ & Hfr & _ & Hfs & Hperm & _ & Hfa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & Hra & Hsv & Hfl & _ & _ & HK & Hfds & Hfs' & Hro).
  unfold aws_inv. repeat (split; [assumption|]). assumption.
Qed.

(* the frame and its shadow are present at every AR state where the frame is live *)
Lemma aws_frame_present : forall ly S (W : world SEGS) m md,
  AR SEGS B ly S W m md -> In (AW_CID, fpos) (frames S) -> frame_addr ly AW_CID fpos = F ->
  (forall a, F <= a < F + AW_FB -> apresent (w_H W) m a) /\
  (forall a, SH <= a < SH + AW_SHN -> apresent (w_H W) m a).
Proof.
  intros ly S W m md HAR Hin Hfa.
  destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & HF & HS).
  rewrite Hfa in HF, HS. change (fs_frame_bytes AW_CID) with 512 in HF, HS. change (512 / 8) with 64 in HS.
  split.
  - intros a Ha. exact (proj1 (HF a Ha)).
  - intros a Ha. unfold aw_SH in Ha. fold (aw_F cx fpos) in Ha.
    replace a with (shadow_addr F + (a - shadow_addr F)) by ring.
    apply (proj1 (HS (a - shadow_addr F) ltac:(unfold shadow_addr; unfold AW_SHN in Ha; lia))).
Qed.

Lemma aws_base_of_inv : forall ly S W ms md,
  ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs ->
  ms_fcsr ms = fp_csr ->
  getr (ms_regs ms) 2 = w64 (aw_sp1 cx) -> getr (ms_regs ms) 9 = w64 (aw_sp1 cx) ->
  getr (ms_regs ms) 8 = w64 (aw_sp cx) ->
  getr (ms_regs ms) 18 = w64 SH -> getr (ms_regs ms) 19 = w64 F -> getr (ms_regs ms) 24 = w64 F ->
  getr (ms_regs ms) 3 = getr (aw_regs cx) 3 -> getr (ms_regs ms) 4 = getr (aw_regs cx) 4 ->
  getr (ms_regs ms) 25 = getr (aw_regs cx) 25 -> getr (ms_regs ms) 26 = getr (aw_regs cx) 26 ->
  getr (ms_regs ms) 27 = getr (aw_regs cx) 27 ->
  aws_inv ly S W (ms_mem ms) md -> aw_base SK B cx fpos ly S W ms md.
Proof.
  intros ly S W ms md Hr Hs Hrom Hf Hc R2 R9 R8 R18 R19 R24 R3 R4 R25 R26 R27
    (HJ & Hfr & Hfs & Hperm & Hfa & Hra & Hsv & Hfl & HK & Hfds & Hfs' & Hro).
  pose proof (aws_aj_ar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin : In (AW_CID, fpos) (frames S)) by (rewrite Hfr; left; reflexivity).
  destruct (aws_frame_present ly S W (ms_mem ms) md HAR Hin (Hfa AW_CID fpos)) as [HFp HSp].
  unfold aw_base. cbv zeta. repeat (split; [assumption|]). assumption.
Qed.

(* ---- a step of the walk's own code or of a checked runtime call: the invariant at the new memory ---- *)
Lemma aws_inv_step : forall ly S W m md m' md' (X : Z -> Prop),
  aws_inv ly S W m md ->
  AJ ly S W m' md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, X a -> (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK <= a < aw_sp1 cx) \/ (F + 32 <= a < F + 324) \/
     (SH <= a < SH + 64)) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  aws_inv ly S W m' md'.
Proof.
  intros ly S W m md m' md' X (HJ & Hfr & Hfs & Hperm & Hfa & Hra & Hsv & Hfl & HK & Hfds & Hfs' & Hro)
    HJ' UN HX Hpres Efds Efs.
  destruct aws_win as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al & _).
  destruct aws_F as (F1 & F2 & F3 & F4 & F5 & F6).
  destruct aws_SH_val as (SH1 & SH2 & SH3 & SH4 & SH5).
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof REAC_LINK_ALIAS_WRITE_AK_val as HK8560.
  (* the bytes the step may change lie below sp1, in the request's part of F, or in F's shadow *)
  assert (Hstk : forall a, aw_sp cx - 80 <= a < aw_sp cx -> ~ X a).
  { intros a Ha HXa. destruct (HX a HXa) as [H|[H|H]]; lia. }
  assert (Hflag : forall a, F + 504 <= a < F + 512 -> ~ X a).
  { intros a Ha HXa. destruct (HX a HXa) as [H|[H|H]]; [lia | lia |].
    unfold off_img, in_app in F4, F5. aws_c. lia. }
  split; [exact HJ'|]. split; [exact Hfr|]. split; [exact Hfs|]. split; [exact Hperm|]. split; [exact Hfa|].
  split.
  { rewrite <- Hra. apply aws_rdword_eq. intros i Hi. apply UN; [lia | apply Hstk; lia]. }
  split.
  { intros j Hj. rewrite <- (Hsv j Hj). apply aws_rdword_eq. intros i Hi. apply UN; [lia | apply Hstk; lia]. }
  split.
  { rewrite <- Hfl. apply aws_rdword_eq. intros i Hi. unfold AW_FLAGPTR in *. apply UN; [lia | apply Hflag; lia]. }
  split.
  { eapply (akept_step SK SEGS B LAWS pa_segs_low (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) (aw_mdc cx) W m W m'
      (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) Eacc Eacc X aws_pre_ar);
      [lia | lia | exact HK | exact UN | intros a _ Ha; exact (Hpres a Ha) | intros a Ha; exact Ha |].
    intros a HXa. destruct (HX a HXa) as [H|[H|H]].
    - right. lia.
    - left. right. left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes AW_CID) with 512.
      fold (aw_F cx fpos). lia.
    - left. right. right. left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes AW_CID / 8) with 64.
      unfold aw_SH in H. fold (aw_F cx fpos). unfold shadow_addr. lia. }
  split; [rewrite Efds; exact Hfds|]. split; [rewrite Efs; exact Hfs'|].
  apply (aws_arodata_eq SEGS PCAP_RLO PCAP_RHI B _ _ Hro). intros a Hro_a.
  assert (Hi : in_img SEGS a).
  { destruct Hro_a as [(s & Hs & _ & Hb) | Hr]; [exists s; split; [exact Hs | exact Hb] | exact (RELRO_IMG a Hr)]. }
  pose proof (pa_img_range a Hi) as Hir.
  apply UN; [aws_c; lia|]. intros HXa. destruct (HX a HXa) as [H|[H|H]]; unfold off_img in F5; aws_c; lia.
Qed.

(* ---- the Pre's facts the stages read ---- *)
Lemma aws_pre_facts :
  nlk_wf kbs /\ nk_open kbs = 0 /\ nk_opened kbs + 1 < 2 ^ 31 /\ nk_closed kbs + 1 < 2 ^ 31 /\
  aerrno_ok SEGS B REAC_LINK_ALIAS_WRITE_AK (aw_regs cx) (aw_m0 cx) /\
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     au64_at SEGS (aw_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
     apart_gnl LA_G_NL p (Z.of_nat (length n2) + 1)) /\
  apart_frame (aw_regs cx) REAC_LINK_ALIAS_WRITE_AK (aw_alias cx) (Z.of_nat (length sa) + 1) /\
  apart_gnl LA_G_NL (aw_alias cx) (Z.of_nat (length sa) + 1) /\
  Z.of_nat (length sa) + 1 < 2 ^ 32 /\
  achk SEGS (aw_m0 cx) (aw_alias cx) (Z.of_nat (length sa) + 1).
Proof.
  destruct HPRE as (_ & _ & (kbs0 & tab0 & nm & al & NK0 & WF & OP & O1 & C1 & IT0 & _ & _ & ERR & SN & SA & TABC
    & _ & ALC & _)).
  assert (kbs0 = kbs) by exact (aws_anlk_unique _ _ _ _ _ NK0 HNK). subst kbs0.
  assert (tab0 = tab) by exact (aws_aiftab_unique _ _ _ _ _ IT0 HIT). subst tab0.
  assert (al = Some sa) by (apply (aws_astr_arg_unique _ _ _ _ _ SA); split; [exact HA0 | exact HSA]). subst al.
  destruct (ALC sa eq_refl) as (A1 & A2 & A3 & A4).
  refine (conj WF (conj OP (conj O1 (conj C1 (conj ERR (conj _ (conj A1 (conj A2 (conj A3 A4))))))))).
  intros i n2 ix p Hi Hp. exact (proj1 (proj2 (TABC i n2 ix p Hi Hp))).
Qed.

Lemma aws_rd_alias : forall a, aw_alias cx <= a <= aw_alias cx + Z.of_nat (length sa) ->
  akb SEGS B (aw_lyc cx) (aw_Sc cx) (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) a.
Proof.
  intros a Ha. apply (proj1 (proj2 HPRE)). right; left. split; [exact HA0|]. exists sa. split; [exact HSA | exact Ha].
Qed.

Lemma aws_rd_tab : forall i n2 ix p a, nth_error tab i = Some (n2, ix) ->
  au64_at SEGS (aw_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> acstr_at SEGS (aw_m0 cx) p n2 ->
  p <= a <= p + Z.of_nat (length n2) ->
  akb SEGS B (aw_lyc cx) (aw_Sc cx) (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) a.
Proof.
  intros i n2 ix p a H1 H2 H3 H4. apply (proj1 (proj2 HPRE)). right; right.
  exists kbs, tab, i, n2, ix, p. exact (conj HNK (conj HIT (conj H1 (conj H2 (conj H3 H4))))).
Qed.

(* a read-set byte keeps its value from the call to every memory the walk's akept reaches *)
Lemma aws_kept_akb : forall (W : world SEGS) m a,
  akept SEGS B (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) W m
    (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) Eacc ->
  akb SEGS B (aw_lyc cx) (aw_Sc cx) (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) a -> ~ aw_E cx a ->
  aview SEGS (w_H W) m a = aview SEGS (w_H (aw_W cx)) (aw_memc cx) a.
Proof.
  intros W m a HK Hb HnE.
  destruct aws_F as (_ & _ & _ & _ & _ & Hfp).
  eapply (akept_akb_gx SK SEGS B); [exact aws_pre_j | exact HK | exact Hb |].
  intros [H | H]; [exact (HnE H) |].
  assert (Hns : ~ aside_rng (aw_lyc cx) AW_CID fpos a).
  { eapply (akb_not_side SK SEGS B);
      first [exact LAWS | exact TB | exact pa_img_range | exact aws_pre_j | (unfold AW_CID; lia) | exact Hfp
            | exact HNIN | exact Hb]. }
  exact (Hns H).
Qed.

(* g_nl is an image byte outside the runtime's statics and errno (a computation at the image's segments) *)
Lemma aws_gnl_img : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. rewrite HSEGS, (ts_owned B TB), (ts_errno B TB). split; [|split].
  - assert (Hb : existsb (fun sg => (Z.of_N (seg_base sg) <=? LA_G_NL) &&
        (LA_G_NL + NK_SIZE <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs = true)
      by (vm_compute; reflexivity).
    apply existsb_exists in Hb as (sg & Hin & Hc). apply andb_true_iff in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
  - assert (Hb : forallb (fun r => (LA_G_NL + NK_SIZE <=? fst r) || (fst r + snd r <=? LA_G_NL))
        Tfib_owned_static = true) by (vm_compute; reflexivity).
    intros Hex. apply Exists_exists in Hex as (r & Hin & Hr). rewrite forallb_forall in Hb. specialize (Hb r Hin).
    apply orb_true_iff in Hb as [Hb|Hb]; apply Z.leb_le in Hb; unfold in_zr in Hr; lia.
  - assert (He : LA_G_NL + NK_SIZE <= TFIB_ERRNO) by (vm_compute; congruence). lia.
Qed.

(* the bytes of g_nl past the write set (the interface table) keep their value to every memory the akept reaches *)
Lemma aws_kept_gnl_tail : forall (W : world SEGS) m a,
  akept SEGS B (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) W m
    (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) Eacc ->
  LA_G_NL + NK_N_SENT + 4 <= a < LA_G_NL + NK_SIZE ->
  aview SEGS (w_H W) m a = aview SEGS (w_H (aw_W cx)) (aw_memc cx) a.
Proof.
  intros W m a (_ & _ & K3 & _) Ha.
  destruct (aws_gnl_img a ltac:(unfold NK_N_SENT, NK_SIZE in *; lia)) as (Hi & Ho & He).
  apply (K3 a Hi Ho He). intros [H | H].
  - unfold aw_E in H. apply aws_wr_eq in H. lia.
  - destruct HS1 as (S1 & W1 & mem1 & md1 & HAR & Hfr & _).
    assert (Hin : In (AW_CID, fpos) (frames S1)) by (rewrite Hfr; left; reflexivity).
    exact (proj2 (aside_rng_low SK SEGS B LAWS pa_segs_low _ S1 W1 mem1 md1 _ _ a HAR Hin H) Hi).
Qed.

(* the interface table at every memory the akept reaches (the read set's strings and g_nl's tail kept) *)
Lemma aws_tab_kept : forall (W : world SEGS) m kbs',
  akept SEGS B (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) W m
    (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) Eacc ->
  nk_n_if kbs' = nk_n_if kbs -> aiftab_at SEGS (rdW W m) LA_G_NL kbs' tab.
Proof.
  intros W m kbs' HK Hn.
  destruct aws_pre_facts as (_ & _ & _ & _ & _ & HTAB & _).
  pose proof HIT as (L1 & L80 & _).
  apply (aws_aiftab_keep SEGS (aw_m0 cx) _ kbs kbs' tab HIT Hn).
  - intros x Hx. apply (mbyte_of_aview SEGS). apply (aws_kept_gnl_tail W m x HK).
    unfold NK_IF_NAME, NK_N_SENT, NK_SIZE in *. lia.
  - intros x Hx. apply (mbyte_of_aview SEGS). apply (aws_kept_gnl_tail W m x HK).
    unfold NK_IF_INDEX, NK_N_SENT, NK_SIZE in *. lia.
  - intros i n2 ix p Hi Hp Hp64 x Hx. apply (mbyte_of_aview SEGS).
    destruct HIT as (_ & _ & E). destruct (E i n2 ix Hi) as (_ & p' & P' & _ & C' & _).
    pose proof (aws_au64_unique _ _ _ _ _ Hp P') as Ep. pose proof (aws_acstr_range _ _ _ _ C') as Rp.
    rewrite !Z.mod_small in Ep by lia. subst p'.
    apply (aws_kept_akb W m x HK (aws_rd_tab i n2 ix p x Hi Hp C' Hx)).
    unfold aw_E. rewrite aws_wr_eq. pose proof (HTAB i n2 ix p Hi Hp) as Hg. unfold apart_gnl, NK_SIZE, NK_N_SENT in *.
    lia.
Qed.

Lemma aws_frame_mbyte : forall E rs (m m' : word -> option byte) x,
  frame_of E rs m m' -> 0 <= x < 2 ^ 64 -> ~ in_wrange E rs x -> mbyte SEGS m' x = mbyte SEGS m x.
Proof. intros E rs m m' x HF Hx Hn. unfold mbyte. rewrite HF; [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn. Qed.

Lemma aws_frame_aview : forall E rs (H : word -> bool) (m m' : word -> option byte) x,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= x < 2 ^ 64 -> ~ in_wrange E rs x ->
  aview SEGS H m' x = aview SEGS H m x.
Proof.
  intros E rs H m m' x HF Hx Hn. apply (aview_eq_of SEGS). apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* the shadow region of a stage *)
Lemma aws_U18 : forall (R : bvmap 5 word), getr R 18 = w64 SH -> bv_unsigned (ew (Eimg (Ereg R [])) 18) = SH.
Proof.
  intros R H. destruct aws_SH_val as (_ & _ & H3 & H4 & _).
  assert (HB : 0 <= SH < 2 ^ 64) by (unfold kHighMemBeg, aws_SB in *; lia).
  rewrite (ew_Eimg_Ereg_nat R [] 18 (18%bv : bv 5) eq_refl), H. exact (unsigned_lit_small _ HB).
Qed.

Lemma aws_shr_ok : forall (W : world SEGS) m (R : bvmap 5 word), getr R 18 = w64 SH ->
  (forall a, SH <= a < SH + 64 -> apresent (w_H W) m a) ->
  region_ok SEGS (Eimg (Ereg R [])) (rdW W m) aws_SHR /\ afact_ok (Eimg (Ereg R [])) 18 aws_shfact.
Proof.
  intros W m R H18 Hp. pose proof (aws_U18 R H18) as U. destruct aws_SH_val as (SH1 & SH2 & SH3 & SH4 & SH5).
  destruct aws_F as (F1 & F2 & F3 & _). pose proof asan_consts as ((C1a & C1b) & _).
  split.
  - unfold region_ok, aws_SHR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U. unfold aws_SB, kHighMemBeg in *. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (YCbq.apresent_writable SEGS). apply Hp. lia.
  - unfold afact_ok, aws_shfact. cbn [af_lo af_hi af_al2]. rewrite U. change (2 ^ 3) with 8.
    unfold aws_SB in *. repeat split; lia.
Qed.

Lemma aws_not_wr_shr : forall (R : bvmap 5 word) x, bv_unsigned (ew (Eimg (Ereg R [])) 18) = SH ->
  ~ (SH + 4 <= x < SH + 41) -> ~ in_wrange (Eimg (Ereg R [])) [aws_SHR] x.
Proof.
  intros R x U Hx (r & [<- | []] & Hr). unfold aws_SHR in Hr.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U in Hr. lia.
Qed.

(* the writes of a run into F's shadow are writes the journal admits *)
Lemma aws_awr_shr : forall ly S W m md (R : bvmap 5 word),
  aws_inv ly S W m md -> getr R 18 = w64 SH ->
  awr_ok_x (Eimg (Ereg R [])) [aws_SHR] (aw_G cx) (aw_XO cx) (aw_OUT cx) (aw_STK cx) (aw_sp0 cx) (aw_FP cx)
    (ablocks B (aw_ly cx) (aw_S cx)) (ablocks B ly S) ly ((AW_CID, fpos) :: aw_own cx).
Proof.
  intros ly S W m md R (HJ & _ & _ & _ & Hfa & _) H18. pose proof (aws_U18 R H18) as U.
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. unfold aws_SHR in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U in Ha.
  left. eapply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low); [exact HJ | left; reflexivity |].
  right. unfold in_zr. cbn [fst snd]. rewrite (Hfa AW_CID fpos). change (fs_frame_bytes AW_CID / 8) with 64.
  fold (aw_F cx fpos). unfold aw_SH in Ha. unfold shadow_addr. lia.
Qed.

(* the facts nl_talk's Post gives of the kernel's bytes (the request is req_write) *)
Definition aws_nlpost (W : world SEGS) (m : word -> option byte) : Prop :=
  exists kbs', anlk_at SEGS (rdW W m) LA_G_NL kbs' /\ nlk_wf kbs'
    /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
    /\ nk_n_if kbs' = nk_n_if kbs
    /\ nk_socket_errno kbs' = 0
    /\ nk_send_errno kbs' = k_send (talk_after (nk_kstate kbs))
    /\ nk_next kbs' = Z.of_nat (k_next (talk_after (nk_kstate kbs)))
    /\ nk_sent kbs' = (if talk_owes (nk_kstate kbs) then owe (nk_sent kbs) (req_write (index_of tab sn) sa)
                       else nk_sent kbs)
    /\ nk_n_sent kbs' = Z.of_nat (length (nk_sent kbs'))
    /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
    /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
    /\ (nk_socket_errno kbs <> 0 -> nk_opened kbs' = nk_opened kbs)
    /\ (nk_socket_errno kbs = 0 -> nk_opened kbs' = nk_opened kbs + 1).

(* ---- what the stages carry beside aws_inv ---- *)
#[local] Notation RQ := (aw_F cx fpos + 32).

(* the registers the body keeps from the SEND cut to the EXIT cut *)
Definition aws_rb (R : bvmap 5 word) : Prop :=
  getr R 2 = w64 (aw_sp1 cx) /\ getr R 9 = w64 (aw_sp1 cx) /\ getr R 8 = w64 (aw_sp cx) /\
  getr R 18 = w64 SH /\ getr R 19 = w64 F /\ getr R 24 = w64 F /\
  getr R 3 = getr (aw_regs cx) 3 /\ getr R 4 = getr (aw_regs cx) 4 /\
  getr R 25 = getr (aw_regs cx) 25 /\ getr R 26 = getr (aw_regs cx) 26 /\ getr R 27 = getr (aw_regs cx) 27.

(* s4 = alias, s5 = |alias|, s6 = the request, s7 = the index (from +0x1f4 on) *)
Definition aws_rs (R : bvmap 5 word) : Prop :=
  getr R 20 = w64 (aw_alias cx) /\ getr R 21 = w64 (Z.of_nat (length sa)) /\
  getr R 22 = w64 RQ /\ getr R 23 = w64 (index_of tab sn).

Lemma aws_rb_pres : forall R R2, aws_rb R -> aregs_preserved R R2 -> aws_rb R2.
Proof.
  intros R R2 (H2 & H9 & H8 & H18 & H19 & H24 & H3 & H4 & H25 & H26 & H27) P.
  split; [exact (aws_pres R R2 2 _ P ltac:(unfold acallee_saved; lia) H2)|].
  split; [exact (aws_pres R R2 9 _ P ltac:(unfold acallee_saved; lia) H9)|].
  split; [exact (aws_pres R R2 8 _ P ltac:(unfold acallee_saved; lia) H8)|].
  split; [exact (aws_pres R R2 18 _ P ltac:(unfold acallee_saved; lia) H18)|].
  split; [exact (aws_pres R R2 19 _ P ltac:(unfold acallee_saved; lia) H19)|].
  split; [exact (aws_pres R R2 24 _ P ltac:(unfold acallee_saved; lia) H24)|].
  split; [exact (aws_pres R R2 3 _ P ltac:(unfold acallee_saved; lia) H3)|].
  split; [exact (aws_pres R R2 4 _ P ltac:(unfold acallee_saved; lia) H4)|].
  split; [exact (aws_pres R R2 25 _ P ltac:(unfold acallee_saved; lia) H25)|].
  split; [exact (aws_pres R R2 26 _ P ltac:(unfold acallee_saved; lia) H26)|].
  exact (aws_pres R R2 27 _ P ltac:(unfold acallee_saved; lia) H27).
Qed.

Lemma aws_rs_pres : forall R R2, aws_rs R -> aregs_preserved R R2 -> aws_rs R2.
Proof.
  intros R R2 (H20 & H21 & H22 & H23) P.
  split; [exact (aws_pres R R2 20 _ P ltac:(unfold acallee_saved; lia) H20)|].
  split; [exact (aws_pres R R2 21 _ P ltac:(unfold acallee_saved; lia) H21)|].
  split; [exact (aws_pres R R2 22 _ P ltac:(unfold acallee_saved; lia) H22)|].
  exact (aws_pres R R2 23 _ P ltac:(unfold acallee_saved; lia) H23).
Qed.

Lemma aws_aarg : forall (R : bvmap 5 word) (i : Z) v, getr R (Z_to_bv 5 (10 + i)) = w64 v -> 0 <= v < 2 ^ 64 ->
  aarg R i = v.
Proof. intros R i v H Hv. unfold aarg, argZ. rewrite H. apply unsigned_lit_small. exact Hv. Qed.

Lemma aws_spZ : forall (R : bvmap 5 word), getr R 2 = w64 (aw_sp1 cx) -> spZ R = aw_sp1 cx.
Proof.
  intros R H. destruct aws_win as (_ & Wc & Wlo & Whi & W47 & S1 & _). pose proof asan_consts as ((C1a & C1b) & _).
  unfold spZ. rewrite H. apply unsigned_lit_small. lia.
Qed.

(* nl_talk's write set with its two buffers NULL: g_nl up to n_sent, the call's own write set *)
Lemma aws_nlwr : forall (R : bvmap 5 word) m a, aarg R 2 = 0 -> aarg R 4 = 0 ->
  inFP (nl_talk_awr R m) a -> LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4.
Proof.
  intros R m a H2 H4 (r & Hr & Ha). unfold nl_talk_awr, aivl in Hr. rewrite H2, H4 in Hr.
  cbn [Z.eqb] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
Qed.

(* the request's shadow, in scope (+0x1f8..+0x28c): 0 at s2 + 4 .. s2 + 0x27, 4 at s2 + 0x28 *)
Definition aws_shb (W : world SEGS) (m : word -> option byte) : Prop :=
  (forall j, 4 <= j < 40 -> aview SEGS (w_H W) m (SH + j) = Some 0) /\ aview SEGS (w_H W) m (SH + 40) = Some 4.

(* F's shadow and g_nl are outside the window and the request *)
Lemma aws_far : forall a, (SH <= a < SH + 64) \/ (LA_G_NL <= a < LA_G_NL + NK_SIZE) ->
  0 <= a < 2 ^ 64 /\ ~ (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK <= a < aw_sp1 cx) /\ ~ (RQ <= a < RQ + 292).
Proof.
  intros a Ha.
  destruct aws_win as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al & _).
  destruct aws_F as (F1 & F2 & F3 & F4 & F5 & F6).
  destruct aws_SH_val as (SH1 & SH2 & SH3 & SH4 & SH5).
  pose proof asan_consts as ((C1a & C1b) & _ & C3 & C4 & C5).
  rewrite REAC_LINK_ALIAS_WRITE_AK_val.
  unfold in_app, off_img in F4, F5. aws_c. unfold LA_G_NL, NK_SIZE in Ha. lia.
Qed.

Lemma aws_keep : forall (W : world SEGS) m m' (X : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, X a -> (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK <= a < aw_sp1 cx) \/ (RQ <= a < RQ + 292)) ->
  forall a, (SH <= a < SH + 64) \/ (LA_G_NL <= a < LA_G_NL + NK_SIZE) ->
  aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
  intros W m m' X UN HX a Ha. destruct (aws_far a Ha) as (H1 & H2 & H3).
  apply UN; [exact H1|]. intros HXa. destruct (HX a HXa) as [H|H]; [exact (H2 H) | exact (H3 H)].
Qed.

Lemma aws_shb_keep : forall (W : world SEGS) m m' (X : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, X a -> (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK <= a < aw_sp1 cx) \/ (RQ <= a < RQ + 292)) ->
  aws_shb W m -> aws_shb W m'.
Proof.
  intros W m m' X UN HX (H1 & H2). split.
  - intros j Hj. rewrite (aws_keep W m m' X UN HX (SH + j) ltac:(left; lia)). exact (H1 j Hj).
  - rewrite (aws_keep W m m' X UN HX (SH + 40) ltac:(left; lia)). exact H2.
Qed.

Lemma aws_gnl_keep : forall (W : world SEGS) m m' (X : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, X a -> (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK <= a < aw_sp1 cx) \/ (RQ <= a < RQ + 292)) ->
  aw_gnl_kept cx W m -> aw_gnl_kept cx W m'.
Proof.
  intros W m m' X UN HX HG a Ha. rewrite (aws_keep W m m' X UN HX a (or_intror Ha)). exact (HG a Ha).
Qed.

(* the kernel's bytes, at a memory where g_nl is the call's *)
Lemma aws_nk_now : forall (W : world SEGS) m, aw_gnl_kept cx W m -> anlk_at SEGS (rdW W m) LA_G_NL kbs.
Proof.
  intros W m HG. apply (aws_anlk_move SEGS (aw_m0 cx) _ kbs HNK).
  - intros x Hx. unfold aw_m0. apply (mbyte_of_aview SEGS). apply HG. exact Hx.
  - intros x Hx. apply aws_gnl_writable. exact Hx.
Qed.

Lemma aws_pre_misc : getr (aw_regs cx) 3 = w64 (as_gp B) /\ getr (aw_regs cx) 4 = w64 (as_tp B) /\
  st_nev (aw_S cx) + aw_k cx + 0 <= EV_MAX /\ aside_room (aw_Sc cx) REAC_LINK_ALIAS_WRITE_ASIDE.
Proof.
  destruct HPRE as ((_ & _ & _ & _ & _ & Hgp & Htp & _ & _ & _ & Hnev & Hside & _) & _).
  exact (conj Hgp (conj Htp (conj Hnev Hside))).
Qed.

(* the class-3 frame's bytes are bytes this call's journal lets it (and its callees) write *)
Lemma aws_awr_F : forall ly S W m md a, aws_inv ly S W m md -> F <= a < F + 512 ->
  awr_byte (aw_STK cx) (aw_sp0 cx) (aw_FP cx) (ablocks B (aw_ly cx) (aw_S cx)) (ablocks B ly S) ly
    ((AW_CID, fpos) :: aw_own cx) a /\ ~ (aw_sp0 cx <= a < aw_sp0 cx + aw_XO cx).
Proof.
  intros ly S W m md a (HJ & _ & _ & _ & Hfa & _) Ha.
  apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AW_CID fpos a HJ
    (or_introl eq_refl)).
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite (Hfa AW_CID fpos). change (fs_frame_bytes AW_CID) with 512.
  exact Ha.
Qed.

(* ==========================================================================
   2. STAGE 4, after nl_talk (+0x300 .. +0x3a0): s5 := a0, the request's shadow := 0xf8, to the EXIT cut
   ========================================================================== *)
Lemma aws_stage4 : forall ly S W (R : bvmap 5 word) m md,
  aws_inv ly S W m md ->
  getr R 2 = w64 (aw_sp1 cx) -> getr R 9 = w64 (aw_sp1 cx) -> getr R 8 = w64 (aw_sp cx) ->
  getr R 18 = w64 SH -> getr R 19 = w64 F -> getr R 24 = w64 F ->
  getr R 3 = getr (aw_regs cx) 3 -> getr R 4 = getr (aw_regs cx) 4 ->
  getr R 25 = getr (aw_regs cx) 25 -> getr R 26 = getr (aw_regs cx) 26 -> getr R 27 = getr (aw_regs cx) 27 ->
  getr R 10 = w64 (talk_rc_lib (nk_kstate kbs)) ->
  aws_nlpost W m ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + (aws_AF + 0x300))) m (seg_rom SEGS)) md) (aw_post SK B cx).
Proof.
  intros ly S W R m md HI R2 R9 R8 R18 R19 R24 R3 R4 R25 R26 R27 R10 HNL.
  pose proof HI as (HJ & _).
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg R []))) by apply Eimg_env.
  pose proof (aws_U18 R R18) as U18.
  destruct (aws_frame_present ly S W m md (aws_aj_ar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)
    ltac:(destruct HI as (_ & Hfr & _); rewrite Hfr; left; reflexivity)
    ltac:(destruct HI as (_ & _ & _ & _ & Hfa & _); exact (Hfa AW_CID fpos))) as [_ HSp].
  assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg R [])) aws_ss4
    (restrict (w_H W) (mkst R (Z_to_bv 64 (BASE + (aws_AF + 0x300))) m (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold aws_ss4. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - destruct (aws_shr_ok W m R R18 (fun a Ha => HSp a ltac:(unfold AW_SHN; lia))) as [H1 _].
      apply Forall_cons; [exact H1 | apply Forall_nil].
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - destruct (aws_shr_ok W m R R18 (fun a Ha => HSp a ltac:(unfold AW_SHN; lia))) as [_ H2].
      cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [split; [exact H2 | exact I] | split; exact I]. }
  aws_run_to HS HJ (aws_AF + 0x3a4).
  { exact (aws_awr_shr ly S W m md R HI R18). }
  intros ms' mat' HS' HJ' HF HF' HG'. cbn [ms_mem mkst] in HF, HF', HG'.
  pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ ms' HS' eq_refl) as Ems. cbn [ss_pc] in Ems.
  prreg_raw HS' (21%bv : bv 5) Q21. prreg_raw HS' (2%bv : bv 5) Q2. prreg_raw HS' (9%bv : bv 5) Q9.
  prreg_raw HS' (8%bv : bv 5) Q8. prreg_raw HS' (18%bv : bv 5) Q18. prreg_raw HS' (19%bv : bv 5) Q19.
  prreg_raw HS' (24%bv : bv 5) Q24. prreg_raw HS' (3%bv : bv 5) Q3. prreg_raw HS' (4%bv : bv 5) Q4.
  prreg_raw HS' (25%bv : bv 5) Q25. prreg_raw HS' (26%bv : bv 5) Q26. prreg_raw HS' (27%bv : bv 5) Q27.
  rewrite (aws_atom R 10 (10%bv : bv 5) eq_refl) in Q21.
  rewrite (aws_atom R 2 (2%bv : bv 5) eq_refl) in Q2. rewrite (aws_atom R 9 (9%bv : bv 5) eq_refl) in Q9.
  rewrite (aws_atom R 8 (8%bv : bv 5) eq_refl) in Q8. rewrite (aws_atom R 18 (18%bv : bv 5) eq_refl) in Q18.
  rewrite (aws_atom R 19 (19%bv : bv 5) eq_refl) in Q19. rewrite (aws_atom R 24 (24%bv : bv 5) eq_refl) in Q24.
  rewrite (aws_atom R 3 (3%bv : bv 5) eq_refl) in Q3. rewrite (aws_atom R 4 (4%bv : bv 5) eq_refl) in Q4.
  rewrite (aws_atom R 25 (25%bv : bv 5) eq_refl) in Q25. rewrite (aws_atom R 26 (26%bv : bv 5) eq_refl) in Q26.
  rewrite (aws_atom R 27 (27%bv : bv 5) eq_refl) in Q27.
  set (mdx := with_vm_backing (m_vm_lazy md) mat' md) in *.
  destruct (wvb_fds_fs (m_vm_lazy md) mat' md) as [Efds Efs]. fold mdx in Efds, Efs.
  (* the invariant at the EXIT cut: the run wrote F's shadow only *)
  assert (HIx : aws_inv ly S W (ms_mem ms') mdx).
  { apply (aws_inv_step ly S W m md (ms_mem ms') mdx (fun a => SH + 4 <= a < SH + 41) HI HJ').
    - intros a Ha Hn. exact (aws_frame_aview _ _ (w_H W) m (ms_mem ms') a HF' Ha (aws_not_wr_shr R a U18 Hn)).
    - intros a Ha. right; right. lia.
    - intros a Ha. exact (apresent_grows _ _ _ a HG' Ha).
    - exact Efds.
    - exact Efs. }
  destruct (ms_shape_mkst SEGS ms' _ _ _ Ems) as (Sh1 & Sh2 & Sh3 & Sh4 & Sh5 & Sh6).
  apply (EXIT cx fpos ly S W ms' mdx HPRE).
  exists (talk_rc_lib (nk_kstate kbs)).
  split; [rewrite Sh6; unfold w64, AW_CUT_EXIT, aws_AF; reflexivity|].
  split; [rewrite Q21; exact R10|].
  split.
  { apply aws_base_of_inv; try assumption.
    - rewrite Q2; exact R2.
    - rewrite Q9; exact R9.
    - rewrite Q8; exact R8.
    - rewrite Q18; exact R18.
    - rewrite Q19; exact R19.
    - rewrite Q24; exact R24.
    - rewrite Q3; exact R3.
    - rewrite Q4; exact R4.
    - rewrite Q25; exact R25.
    - rewrite Q26; exact R26.
    - rewrite Q27; exact R27. }
  pose proof HIx as (_ & _ & _ & _ & _ & _ & _ & _ & HKx & _).
  destruct HNL as (kbs' & N1 & N2 & N3 & N4 & N5 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16).
  apply (aws_pf_talk cx W (ms_mem ms') kbs tab sn sa HNK HIT HSN HN0 HSNE HSA HA0 HAL HIDX).
  exists kbs'. split.
  { apply (aws_anlk_move SEGS (rdW W m) _ kbs' N1).
    - intros x Hx. apply (aws_frame_mbyte _ _ _ _ x HF'); [unfold LA_G_NL, NK_SIZE in *; lia|].
      apply (aws_not_wr_shr R x U18). destruct aws_SH_val as (_ & _ & SH3 & _).
      unfold LA_G_NL, NK_SIZE, aws_SB in *. lia.
    - intros x Hx. apply aws_gnl_writable. exact Hx. }
  split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|].
  split; [exact (aws_tab_kept W (ms_mem ms') kbs' HKx N5)|].
  split; [exact N7|]. split; [exact N8|]. split; [exact N9|]. split; [exact N10|]. split; [exact N11|].
  split; [exact N12|]. split; [exact N13|]. split; [exact N14|]. split; [exact N15 | exact N16].
Qed.

(* ==========================================================================
   3. +0x2fc nl_talk(req, len, 0, 0, 0, 0): its contract (nl_talk_c.v) on the caller's journal, then stage 4
   ========================================================================== *)
Lemma aws_talk : forall ly S W (R : bvmap 5 word) m md,
  aws_inv ly S W m md -> aws_rb R ->
  getr R 1 = Z_to_bv 64 (BASE + (aws_AF + 0x300)) ->
  getr R 10 = w64 RQ -> getr R 11 = w64 (32 + nl_align (RTA_HDR + Z.of_nat (length sa))) ->
  getr R 12 = w64 0 -> getr R 14 = w64 0 ->
  aw_gnl_kept cx W m -> aws_shb W m ->
  abytes SEGS (rdW W m) RQ (req_write (index_of tab sn) sa) ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 NL_TALK_A) m (seg_rom SEGS)) md) (aw_post SK B cx).
Proof.
  intros ly S W R m md HI HR Hra R10 R11 R12 R14 HG HSB HRQ.
  pose proof HI as (HJ & Hfr & Hfs & Hperm & Hfa & Hrav & Hsv & Hfl & HK & Hfds & Hfs' & Hro).
  pose proof HR as (R2 & R9 & R8 & R18 & R19 & R24 & R3 & R4 & R25 & R26 & R27).
  destruct aws_win as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al & S1al16).
  destruct aws_F as (F1 & F2 & F3 & F4 & F5 & F6).
  destruct aws_SH_val as (SH1 & SH2 & SH3 & SH4 & SH5).
  destruct aws_pre_misc as (Hgp & Htp & Hnev & Hside).
  destruct aws_pre_facts as (WF & OP & O1 & C1 & ERR & HTAB & APF & APG & AL32 & ACHK).
  pose proof (aws_aj_ar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin : In (AW_CID, fpos) (frames S)) by (rewrite Hfr; left; reflexivity).
  pose proof asan_consts as ((C1a & C1b) & _ & C3 & C4 & C5).
  pose proof REAC_LINK_ALIAS_WRITE_AK_val as HK8560. pose proof NL_TALK_AK_val as HK8448.
  pose proof pa_B_ok as (HB0 & HB1 & _).
  assert (HAF : aws_AF = 0x6d88) by reflexivity.
  assert (HL : 0 <= Z.of_nat (length sa) < 256) by (unfold ALIAS_MAX in HAL; lia).
  set (len := 32 + nl_align (RTA_HDR + Z.of_nat (length sa))) in *.
  assert (Hlen : 36 <= len <= 292) by (unfold len, nl_align, RTA_HDR; lia).
  assert (Hsp : spZ R = aw_sp1 cx) by exact (aws_spZ R R2).
  assert (A0 : aarg R 0 = RQ) by (apply (aws_aarg R 0 RQ R10); lia).
  assert (A1 : aarg R 1 = len) by (apply (aws_aarg R 1 len R11); lia).
  assert (A2 : aarg R 2 = 0) by (apply (aws_aarg R 2 0 R12); lia).
  assert (A4 : aarg R 4 = 0) by (apply (aws_aarg R 4 0 R14); lia).
  assert (Hfrm : frame_addr ly AW_CID fpos = F) by exact (Hfa AW_CID fpos).
  (* nl_talk's write set is this call's *)
  assert (HNW : forall a, inFP (nl_talk_awr R (rdW W m)) a -> aw_E cx a).
  { intros a Ha. unfold aw_E. apply aws_wr_eq. exact (aws_nlwr R _ a A2 A4 Ha). }
  eapply SRr_bind.
  { change (mkCfg (mkst R (Z_to_bv 64 NL_TALK_A) m (seg_rom SEGS)) md) with (cfg_at SEGS NL_TALK_A R m md).
    apply (NLT (aw_G cx) (aw_XO cx) (aw_OUT cx) (aw_STK cx) (aw_sp0 cx) (aw_FP cx) (aw_ly cx) (aw_S cx)
      (aw_W0 cx) (aw_mem0 cx) (aw_md0 cx) ((AW_CID, fpos) :: aw_own cx) ly S W m md (aw_k cx) R).
    - (* apre *)
      split; [exact HJ|]. split; [exact aws_pre_g|]. split; [exact Hro|].
      split; [rewrite Hra; apply ret_ok_codeptr_v; [rewrite HAF; lia | rewrite HAF; reflexivity]|].
      split; [unfold raZ; rewrite Hra, unsigned_lit_small; rewrite HAF; lia|].
      split; [rewrite R3; exact Hgp|]. split; [rewrite R4; exact Htp|].
      split; [rewrite Hsp; exact S1al16|].
      split; [rewrite Hsp, HK8448; lia|]. split; [rewrite Hsp; lia|].
      split; [exact Hnev|].
      split.
      { apply (aside_room_push (aw_Sc cx) S REAC_LINK_ALIAS_WRITE_ASIDE NL_TALK_ASIDE AW_CID fpos Hfr Hside).
        intros c' d' Hc. unfold NL_TALK_ASIDE in Hc. destruct Hc as [Ec | []]. injection Ec as <- <-.
        exists 1. split; [unfold REAC_LINK_ALIAS_WRITE_ASIDE; right; left; reflexivity | cbn; lia]. }
      split.
      { intros a Ha. pose proof (aws_nlwr R _ a A2 A4 Ha) as Hg.
        eapply LinkWalkCall.ajw_mono; [exact (aws_pre_ajw a (proj2 (aws_wr_eq a) Hg)) | | |].
        - intros bb mm Hbm. exact (Permutation_in _ (Permutation_sym Hperm) Hbm).
        - intros x Hx. right. exact Hx.
        - exact Hfa. }
      intros a Ha. exact (aws_pre_nro a (proj2 (aws_wr_eq a) (aws_nlwr R _ a A2 A4 Ha))).
    - (* the read set: the request, in this call's live frame *)
      intros a Ha. unfold nl_talk_ard, rd_ivl in Ha. rewrite A0, A1 in Ha.
      right; right; right. exists AW_CID, fpos. split; [exact Hin|].
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfrm. change (fs_frame_bytes AW_CID) with 512. lia.
    - (* the Pre *)
      unfold nl_talk_apre. exists kbs, (req_write (index_of tab sn) sa). rewrite A0, A1, A2, A4.
      split; [exact (aws_nk_now W m HG)|]. split; [exact WF|]. split; [exact OP|]. split; [exact O1|].
      split; [exact C1|].
      destruct (zsh_gnl_ard B TB SEGS ly S W m md HAR) as [ZG1 ZG2].
      split; [exact ZG1|]. split; [exact ZG2|].
      split.
      { destruct ERR as (E1 & E2 & E3 & E4 & E5).
        destruct (zsh_errno_ard B TB SEGS ly S W m md HAR) as [ZE1 _].
        pose proof aws_errno_val as Eerr.
        split; [exact E1|]. split; [intros i Hi; apply aws_errno_writable; lia|].
        split; [exact ZE1|]. split; [unfold apart_frame; rewrite Hsp, HK8448, Eerr; lia | exact E5]. }
      split; [exact HRQ|].
      split; [unfold len; exact (aws_req_write_length (index_of tab sn) sa)|].
      split; [unfold NL_SENT_LEN; lia|].
      split; [unfold amem_range, in_app in *; destruct F4 as (_ & [HF | (HF & _)]);
              [left; unfold kLowShadowBeg in HF; lia | right; lia]|].
      split; [exact (aws_req_ra (aview SEGS (w_H W) m) F RQ len ltac:(apply Z.mod_divide; [lia|];
                apply Z.mod_divide in F3; [|lia]; destruct F3 as [q Hq]; exists (8 * q); lia)
                ltac:(lia) (proj1 HSB) (proj2 HSB) ltac:(lia) ltac:(lia))|].
      split; [intros Hpos; apply (shadow_hull_vis_of_frame SEGS B LAWS ly S W m md AW_CID fpos RQ len HAR Hin);
              rewrite ?Hfrm; change (fs_frame_bytes AW_CID) with 512; lia|].
      split; [unfold apart_frame; rewrite Hsp, HK8448; left; lia|].
      split; [unfold apart_gnl, NK_SIZE, LA_G_NL; unfold off_img in F5; aws_c; lia|].
      split; [intros H0; exfalso; exact (H0 eq_refl)|]. split; [intros H0; exfalso; exact (H0 eq_refl)|].
      split; [intros H0; exfalso; exact (H0 eq_refl)|]. split; [intros H0; exfalso; exact (H0 eq_refl)|].
      split; [intros H0; exfalso; exact (H0 eq_refl)|]. split; [intros H0; exfalso; exact (H0 eq_refl)|].
      split; [intros H0; exfalso; exact (H0 eq_refl)|]. split; [intros H0; exfalso; exact (H0 eq_refl)|].
      intros H0; exfalso; exact (H0 eq_refl). }
  (* the return: nl_talk's Post, then stage 4 *)
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hfr2 & Hfds2 & Hfs2 & HK2 & _ & HS2 & Hperm2 & HPOST).
  rewrite Z.add_0_r in HJ2. rewrite Hsp, HK8448 in HK2. rewrite Hra.
  pose proof (HPOST kbs (req_write (index_of tab sn) sa) (aws_nk_now W m HG) ltac:(rewrite A0; exact HRQ)
    ltac:(rewrite A1; unfold len; exact (aws_req_write_length (index_of tab sn) sa))) as HP.
  cbv zeta in HP. destruct HP as (Hrc & HNL & _).
  pose proof (aws_rb_pres R regs2 HR HP2) as (Q2 & Q9 & Q8 & Q18 & Q19 & Q24 & Q3 & Q4 & Q25 & Q26 & Q27).
  assert (Hfa2 : forall c q, frame_addr ly2 c q = frame_addr (aw_lyc cx) c q).
  { intros c q. transitivity (frame_addr (aw_ly cx) c q).
    - eapply LinkWalkCall.aj_frame_addr. exact HJ2.
    - symmetry. eapply LinkWalkCall.aj_frame_addr. exact aws_pre_j. }
  (* what nl_talk kept of the saves and of the flag word *)
  assert (KS : forall a, aw_sp cx - 80 <= a < aw_sp cx -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) m a).
  { intros a Ha. destruct HK2 as (K1 & _). apply K1; [lia | lia |].
    intros HE. pose proof (aws_nlwr R _ a A2 A4 HE) as Hg. unfold LA_G_NL, NK_N_SENT in Hg. lia. }
  assert (KF : forall a, F + 504 <= a < F + 512 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) m a).
  { intros a Ha. destruct HK2 as (_ & _ & _ & K4 & _). apply (K4 AW_CID fpos a Hin).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfrm. change (fs_frame_bytes AW_CID) with 512. lia.
    - intros HE. pose proof (aws_nlwr R _ a A2 A4 HE) as Hg. unfold off_img in F5. aws_c.
      unfold LA_G_NL, NK_N_SENT in Hg. lia. }
  assert (HI2 : aws_inv ly2 S2 W2 mem2 md2).
  { split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfr|].
    split; [destruct Hfs as (fs & Hfs0); exists (st_fs S2); rewrite HS2 at 1; rewrite Hfs0; apply aws_set_fs_set_fs|].
    split; [exact (Permutation_trans Hperm2 Hperm)|]. split; [exact Hfa2|].
    split; [rewrite <- Hrav; apply aws_rdword_eq; intros i Hi; apply KS; lia|].
    split; [intros j Hj; rewrite <- (Hsv j Hj); apply aws_rdword_eq; intros i Hi; apply KS; lia|].
    split; [rewrite <- Hfl; apply aws_rdword_eq; intros i Hi; apply KF; unfold AW_FLAGPTR; lia|].
    split.
    { eapply (akept_trans_ly SK SEGS B LAWS pa_segs_low (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) ly S W m W2 mem2
        (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) (aw_sp1 cx - 8448) (aw_sp1 cx) Eacc _ Eacc);
        [rewrite HK8560; lia | lia | exact HK | exact HK2 | rewrite HK8560; lia | lia | | | exact Hfa | | ].
      - intros bb mm Hbm. exact (Permutation_in _ (Permutation_sym Hperm) Hbm).
      - intros f Hf. rewrite Hfr. right. exact Hf.
      - intros a H. exact H.
      - intros a H. left. exact (HNW a H). }
    split; [rewrite Hfds2; exact Hfds|]. split; [rewrite Hfs2; exact Hfs'|].
    exact (aws_arodata_call ly S W m W2 mem2 _ _ _ HK2 (fun a H => aws_pre_nro a (HNW a H)) Hro). }
  exact (aws_stage4 ly2 S2 W2 regs2 mem2 md2 HI2 Q2 Q9 Q8 Q18 Q19 Q24 Q3 Q4 Q25 Q26 Q27 Hrc HNL).
Qed.

(* ==========================================================================
   4. STAGE 3 (+0x2d8 .. +0x2fc): nlmsg_len := 32 + ((|alias| + 7) & 0x1fc) at the request, the arguments of
   nl_talk; the run stops at the call
   ========================================================================== *)
(* the request's bytes after checked_memcpy, but its length word *)
Definition aws_rq (W : world SEGS) (m : word -> option byte) : Prop :=
  val_mem SEGS (rdW W m) (RQ + 4) 4 327696 /\ val_mem SEGS (rdW W m) (RQ + 8) 4 1 /\
  val_mem SEGS (rdW W m) (RQ + 20) 4 (index_of tab sn) /\
  val_mem SEGS (rdW W m) (RQ + 32) 2 (Z.of_nat (length sa) + 4) /\ val_mem SEGS (rdW W m) (RQ + 34) 2 20 /\
  (forall i, (12 <= i < 20 \/ 24 <= i < 32 \/ 36 + Z.of_nat (length sa) <= i < 292) ->
     mbyte SEGS (rdW W m) (RQ + i) = Some (zb 0)) /\
  (forall i, (i < length sa)%nat -> mbyte SEGS (rdW W m) (RQ + 36 + Z.of_nat i) = nth_error sa i).

Lemma aws_rq_keep : forall (W : world SEGS) m m',
  (forall a, RQ + 4 <= a < RQ + 292 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  aws_rq W m -> aws_rq W m'.
Proof.
  intros W m m' K (V4 & V8 & V20 & V32 & V34 & ZZ & AA).
  assert (HL : Z.of_nat (length sa) < 256) by (unfold ALIAS_MAX in HAL; lia).
  assert (KM : forall a, RQ + 4 <= a < RQ + 292 -> mbyte SEGS (rdW W m') a = mbyte SEGS (rdW W m) a)
    by (intros a Ha; apply (mbyte_of_aview SEGS); apply K; exact Ha).
  split; [apply (aws_vm_keep _ _ _ _ _ V4); intros k Hk; apply KM; lia|].
  split; [apply (aws_vm_keep _ _ _ _ _ V8); intros k Hk; apply KM; lia|].
  split; [apply (aws_vm_keep _ _ _ _ _ V20); intros k Hk; apply KM; lia|].
  split; [apply (aws_vm_keep _ _ _ _ _ V32); intros k Hk; apply KM; lia|].
  split; [apply (aws_vm_keep _ _ _ _ _ V34); intros k Hk; apply KM; lia|].
  split; [intros i Hi; rewrite KM by lia; exact (ZZ i Hi)|].
  intros i Hi. rewrite KM; [exact (AA i Hi) | lia].
Qed.

Lemma aws_rb_of : forall R R', aws_rb R ->
  getr R' 2 = getr R 2 -> getr R' 9 = getr R 9 -> getr R' 8 = getr R 8 -> getr R' 18 = getr R 18 ->
  getr R' 19 = getr R 19 -> getr R' 24 = getr R 24 -> getr R' 3 = getr R 3 -> getr R' 4 = getr R 4 ->
  getr R' 25 = getr R 25 -> getr R' 26 = getr R 26 -> getr R' 27 = getr R 27 -> aws_rb R'.
Proof.
  intros R R' (H2 & H9 & H8 & H18 & H19 & H24 & H3 & H4 & H25 & H26 & H27) E2 E9 E8 E18 E19 E24 E3 E4 E25 E26 E27.
  unfold aws_rb. rewrite E2, E9, E8, E18, E19, E24, E3, E4, E25, E26, E27.
  repeat (split; [assumption|]). assumption.
Qed.

Lemma aws_not_wr1 : forall (R : bvmap 5 word) (n : nat) b lo hi wlo whi cs x,
  bv_unsigned (ew (Eimg (Ereg R [])) n) = b -> ~ (b + wlo <= x < b + whi) ->
  ~ in_wrange (Eimg (Ereg R [])) [YP09.mkRegion (Some n) lo hi wlo whi cs] x.
Proof.
  intros R n b lo hi wlo whi cs x U Hx (r & [<- | []] & Hr).
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U in Hr. apply Hx. lia.
Qed.

Lemma aws_U22 : forall (R : bvmap 5 word), getr R 22 = w64 RQ -> bv_unsigned (ew (Eimg (Ereg R [])) 22) = RQ.
Proof.
  intros R H. destruct aws_F as (F1 & F2 & _). pose proof asan_consts as ((C1a & C1b) & _).
  assert (HB : 0 <= RQ < 2 ^ 64) by lia.
  rewrite (ew_Eimg_Ereg_nat R [] 22 (22%bv : bv 5) eq_refl), H. exact (unsigned_lit_small _ HB).
Qed.

Definition aws_RQ3 : YP09.region := YP09.mkRegion (Some 22%nat) 0 4 0 4 [].
Definition aws_ss3 : sstate := mkSS (aws_AF + 0x2d8) sr_atoms [aws_RQ3] None (mkFacts [] [] []).

Lemma aws_stage3 : forall ly S W (R : bvmap 5 word) m md,
  aws_inv ly S W m md -> aws_rb R -> aws_rs R ->
  aw_gnl_kept cx W m -> aws_shb W m -> aws_rq W m ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + (aws_AF + 0x2d8))) m (seg_rom SEGS)) md) (aw_post SK B cx).
Proof.
  intros ly S W R m md HI HR HRS HG HSB HRQ.
  pose proof HI as (HJ & Hfr & _ & _ & Hfa & _).
  pose proof HRS as (R20 & R21 & R22 & R23).
  destruct aws_F as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HL : 0 <= Z.of_nat (length sa) < 256) by (unfold ALIAS_MAX in HAL; lia).
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg R []))) by apply Eimg_env.
  pose proof (aws_U22 R R22) as U22.
  pose proof (aws_aj_ar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin : In (AW_CID, fpos) (frames S)) by (rewrite Hfr; left; reflexivity).
  destruct (aws_frame_present ly S W m md HAR Hin (Hfa AW_CID fpos)) as [HFp _].
  assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg R [])) aws_ss3
    (restrict (w_H W) (mkst R (Z_to_bv 64 (BASE + (aws_AF + 0x2d8))) m (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold aws_ss3. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      unfold region_ok, aws_RQ3. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U22. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (YCbq.apresent_writable SEGS). apply HFp. unfold AW_FB. lia.
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
  aws_run_call HS HJ.
  { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. unfold aws_RQ3 in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U22 in Ha.
    left. exact (aws_awr_F ly S W m md a HI ltac:(lia)). }
  intros ms' mat' HS' HJ' HF HF' HG'. cbn [ms_mem mkst] in HF, HF', HG'.
  pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms' HS' eq_refl) as Ems. cbn [ss_pc setpc] in Ems.
  sreg HS' (1%bv : bv 5) Q1. sreg HS' (10%bv : bv 5) Q10. sreg HS' (11%bv : bv 5) Q11.
  sreg HS' (12%bv : bv 5) Q12. sreg HS' (14%bv : bv 5) Q14.
  sreg HS' (2%bv : bv 5) Q2. sreg HS' (9%bv : bv 5) Q9. sreg HS' (8%bv : bv 5) Q8.
  sreg HS' (18%bv : bv 5) Q18. sreg HS' (19%bv : bv 5) Q19. sreg HS' (24%bv : bv 5) Q24.
  sreg HS' (3%bv : bv 5) Q3. sreg HS' (4%bv : bv 5) Q4. sreg HS' (25%bv : bv 5) Q25.
  sreg HS' (26%bv : bv 5) Q26. sreg HS' (27%bv : bv 5) Q27.
  sregion HS' 0%nat HR3.
  rewrite (aws_atom R 22 (22%bv : bv 5) eq_refl) in Q10.
  rewrite (aws_atom R 2 (2%bv : bv 5) eq_refl) in Q2. rewrite (aws_atom R 9 (9%bv : bv 5) eq_refl) in Q9.
  rewrite (aws_atom R 8 (8%bv : bv 5) eq_refl) in Q8. rewrite (aws_atom R 18 (18%bv : bv 5) eq_refl) in Q18.
  rewrite (aws_atom R 19 (19%bv : bv 5) eq_refl) in Q19. rewrite (aws_atom R 24 (24%bv : bv 5) eq_refl) in Q24.
  rewrite (aws_atom R 3 (3%bv : bv 5) eq_refl) in Q3. rewrite (aws_atom R 4 (4%bv : bv 5) eq_refl) in Q4.
  rewrite (aws_atom R 25 (25%bv : bv 5) eq_refl) in Q25. rewrite (aws_atom R 26 (26%bv : bv 5) eq_refl) in Q26.
  rewrite (aws_atom R 27 (27%bv : bv 5) eq_refl) in Q27.
  assert (E21 : ew (Eimg (Ereg R [])) 21 = Z_to_bv 64 (Z.of_nat (length sa))).
  { rewrite (ew_Eimg_Ereg_nat R [] 21 (21%bv : bv 5) eq_refl). exact R21. }
  assert (DL : sv_denot (Eimg (Ereg R [])) (SAlu ALU_ADD (SAlu ALU_AND (SOff 21 7) (SLit 508)) (SLit 32)) =
    Z_to_bv 64 (32 + nl_align (RTA_HDR + Z.of_nat (length sa)))).
  { rewrite (aws_denot_len _ 21 (Z.of_nat (length sa)) E21 HL). rewrite aws_len_val by exact HL. reflexivity. }
  set (mdx := with_vm_backing (m_vm_lazy md) mat' md) in *.
  destruct (wvb_fds_fs (m_vm_lazy md) mat' md) as [Efds Efs]. fold mdx in Efds, Efs.
  (* the run wrote the length word only *)
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (RQ <= a < RQ + 4) ->
    aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) m a).
  { intros a Ha Hn. exact (aws_frame_aview _ _ (w_H W) m (ms_mem ms') a HF' Ha
      (aws_not_wr1 R 22 RQ 0 4 0 4 [] a U22 ltac:(lia))). }
  assert (HIx : aws_inv ly S W (ms_mem ms') mdx).
  { apply (aws_inv_step ly S W m md (ms_mem ms') mdx (fun a => RQ <= a < RQ + 4) HI HJ' UN).
    - intros a Ha. right; left. lia.
    - intros a Ha. exact (apresent_grows _ _ _ a HG' Ha).
    - exact Efds.
    - exact Efs. }
  assert (HX : forall a, RQ <= a < RQ + 4 ->
    (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK <= a < aw_sp1 cx) \/ (RQ <= a < RQ + 292)) by (intros a Ha; right; lia).
  pose proof (aws_shb_keep W m (ms_mem ms') _ UN HX HSB) as HSBx.
  pose proof (aws_gnl_keep W m (ms_mem ms') _ UN HX HG) as HGx.
  pose proof (aws_rq_keep W m (ms_mem ms') ltac:(intros a Ha; apply UN; lia) HRQ) as
    (V4 & V8 & V20 & V32 & V34 & ZZ & AA).
  pose proof (YC4b.field_of_region (segs := SEGS) (Eimg (Ereg R [])) _ 22 RQ _ 0 4 0 4 0 4%N
    (SAlu ALU_ADD (SAlu ALU_AND (SOff 21 7) (SLit 508)) (SLit 32)) (32 + nl_align (RTA_HDR + Z.of_nat (length sa)))
    HR3 U22 ltac:(cbn; repeat (first [left; reflexivity | right])) DL
    ltac:(unfold nl_align, RTA_HDR; cbn; lia) ltac:(cbn; lia)) as VL.
  rewrite Z.add_0_r in VL.
  assert (HAB : abytes SEGS (rdW W (ms_mem ms')) RQ (req_write (index_of tab sn) sa)).
  { apply (aws_req_bytes SEGS (rdW W (ms_mem ms')) RQ (index_of tab sn) sa); try lia;
      [exact VL | exact V4 | exact V8 | | exact V20 | | exact V32 | exact V34 | exact AA |].
    - intros i Hi. apply ZZ. lia.
    - intros i Hi. apply ZZ. lia.
    - intros i Hi. apply ZZ. unfold nl_align, RTA_HDR in Hi. lia. }
  assert (Hsig : pa_sigma LS_nl_talk = NL_TALK_A) by (rewrite (lv_sigma LV); reflexivity).
  rewrite Ems, Hsig.
  apply (aws_talk ly S W (ms_regs ms') (ms_mem ms') mdx HIx
    (aws_rb_of R (ms_regs ms') HR Q2 Q9 Q8 Q18 Q19 Q24 Q3 Q4 Q25 Q26 Q27)); try assumption.
  all: first [ rewrite Q1; exact (codeptr_val _ _ HEI) | rewrite Q10; exact R22 | rewrite Q11; exact DL
             | rewrite Q12; reflexivity | rewrite Q14; reflexivity ].
Qed.

(* ==========================================================================
   5. +0x2d4 checked_memcpy(req + 36, alias, |alias|): link_ajkit.v aj_gx_intrin_at, op OCpy, then stage 3
   ========================================================================== *)
(* the request's bytes after the header stores and checked_memset *)
Definition aws_rq0 (W : world SEGS) (m : word -> option byte) : Prop :=
  val_mem SEGS (rdW W m) (RQ + 4) 4 327696 /\ val_mem SEGS (rdW W m) (RQ + 8) 4 1 /\
  val_mem SEGS (rdW W m) (RQ + 20) 4 (index_of tab sn) /\
  val_mem SEGS (rdW W m) (RQ + 32) 2 (Z.of_nat (length sa) + 4) /\ val_mem SEGS (rdW W m) (RQ + 34) 2 20 /\
  (forall i, (12 <= i < 20 \/ 24 <= i < 32 \/ 36 <= i < 292) -> mbyte SEGS (rdW W m) (RQ + i) = Some (zb 0)).

Lemma aws_mbyte_eq : forall H H' (m m' : word -> option byte) a a',
  aview SEGS H' m' a' = aview SEGS H m a -> mbyte SEGS (mrestrict H' m') a' = mbyte SEGS (mrestrict H m) a.
Proof.
  intros H H' m m' a a' E.
  assert (E' : option_map (fun b : byte => bv_unsigned b) (mbyte SEGS (mrestrict H' m') a') =
               option_map (fun b : byte => bv_unsigned b) (mbyte SEGS (mrestrict H m) a)) by exact E.
  destruct (mbyte SEGS (mrestrict H' m') a') as [b'|], (mbyte SEGS (mrestrict H m) a) as [b|];
    cbn [option_map] in E'; try discriminate; [|reflexivity].
  injection E' as E'. f_equal. apply bv_eq. exact E'.
Qed.

Lemma aws_mbyte0 : forall H (m : word -> option byte) a, aview SEGS H m a = Some 0 ->
  mbyte SEGS (mrestrict H m) a = Some (zb 0).
Proof.
  intros H m a E.
  assert (E' : option_map (fun b : byte => bv_unsigned b) (mbyte SEGS (mrestrict H m) a) = Some 0) by exact E.
  destruct (mbyte SEGS (mrestrict H m) a) as [b|]; cbn [option_map] in E'; [|discriminate].
  injection E' as E'. f_equal. apply bv_eq. rewrite E'. unfold zb. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma aws_alias_byte : forall i, (i < length sa)%nat ->
  mbyte SEGS (aw_m0 cx) (aw_alias cx + Z.of_nat i) = nth_error sa i.
Proof.
  intros i Hi. destruct HSA as ((_ & _ & HB) & _).
  rewrite (HB i ltac:(rewrite length_app; cbn [length]; lia)). apply nth_error_app1. exact Hi.
Qed.

Lemma aws_alias_some : forall a, aw_alias cx <= a < aw_alias cx + Z.of_nat (length sa) ->
  aview SEGS (w_H (aw_W cx)) (aw_memc cx) a <> None.
Proof.
  intros a Ha.
  pose proof (aws_alias_byte (Z.to_nat (a - aw_alias cx)) ltac:(lia)) as Hb.
  rewrite Z2Nat.id in Hb by lia. replace (aw_alias cx + (a - aw_alias cx)) with a in Hb by lia.
  destruct (nth_error sa (Z.to_nat (a - aw_alias cx))) as [bb|] eqn:E.
  - intros HN. change (option_map (fun b : byte => bv_unsigned b) (mbyte SEGS (aw_m0 cx) a) = None) in HN.
    rewrite Hb in HN. discriminate.
  - apply nth_error_None in E. lia.
Qed.

Lemma aws_alias_notE : forall a, aw_alias cx <= a <= aw_alias cx + Z.of_nat (length sa) -> ~ aw_E cx a.
Proof.
  intros a Ha HE. unfold aw_E in HE. apply aws_wr_eq in HE.
  destruct aws_pre_facts as (_ & _ & _ & _ & _ & _ & _ & APG & _).
  unfold apart_gnl, NK_SIZE, NK_N_SENT in *. lia.
Qed.

Lemma aws_alias_now : forall (W : world SEGS) m a,
  akept SEGS B (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) W m
    (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) Eacc ->
  aw_alias cx <= a <= aw_alias cx + Z.of_nat (length sa) ->
  aview SEGS (w_H W) m a = aview SEGS (w_H (aw_W cx)) (aw_memc cx) a.
Proof. intros W m a HK Ha. exact (aws_kept_akb W m a HK (aws_rd_alias a Ha) (aws_alias_notE a Ha)). Qed.

Lemma aws_alias_not_side : forall a, aw_alias cx <= a <= aw_alias cx + Z.of_nat (length sa) ->
  ~ aside_rng (aw_lyc cx) AW_CID fpos a.
Proof.
  intros a Ha. destruct aws_F as (_ & _ & _ & _ & _ & Hfp).
  eapply (akb_not_side SK SEGS B);
    first [exact LAWS | exact TB | exact pa_img_range | exact aws_pre_j | (unfold AW_CID; lia) | exact Hfp
          | exact HNIN | exact (aws_rd_alias a Ha)].
Qed.

Lemma aws_F8 : F mod 8 = 0.
Proof.
  destruct aws_F as (_ & _ & F3 & _). apply Z.mod_divide; [lia|].
  apply Z.mod_divide in F3; [|lia]. destruct F3 as [q Hq]. exists (8 * q). lia.
Qed.

Lemma aws_cpy : forall ly S W (R : bvmap 5 word) m md,
  aws_inv ly S W m md -> aws_rb R -> aws_rs R ->
  getr R 1 = Z_to_bv 64 (BASE + (aws_AF + 0x2d8)) ->
  getr R 10 = w64 (RQ + 36) -> getr R 11 = w64 (aw_alias cx) -> getr R 12 = w64 (Z.of_nat (length sa)) ->
  aw_gnl_kept cx W m -> aws_shb W m -> aws_rq0 W m ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (pa_sigma LS___asan_memcpy)) m (seg_rom SEGS)) md) (aw_post SK B cx).
Proof.
  intros ly S W R m md HI HR HRS Hra R10 R11 R12 HG HSB HRQ.
  pose proof HI as (HJ & Hfr & Hfs & Hperm & Hfa & _ & _ & _ & HK & Hfds & Hfs' & _).
  pose proof HR as (R2 & R9 & R8 & R18 & R19 & R24 & R3 & R4 & R25 & R26 & R27).
  destruct aws_win as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al & S1al16).
  destruct aws_F as (F1 & F2 & F3 & F4 & F5 & F6).
  destruct aws_pre_misc as (Hgp & Htp & _ & _).
  destruct aws_pre_facts as (_ & _ & _ & _ & _ & _ & APF & APG & AL32 & ACHK).
  pose proof (aws_aj_ar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin : In (AW_CID, fpos) (frames S)) by (rewrite Hfr; left; reflexivity).
  pose proof asan_consts as ((C1a & C1b) & _ & C3 & C4 & C5).
  pose proof REAC_LINK_ALIAS_WRITE_AK_val as HK8560.
  pose proof pa_B_ok as (HB0 & HB1 & _).
  assert (HAF : aws_AF = 0x6d88) by reflexivity.
  assert (HL : 0 <= Z.of_nat (length sa) < 256) by (unfold ALIAS_MAX in HAL; lia).
  assert (Hsp : spZ R = aw_sp1 cx) by exact (aws_spZ R R2).
  assert (Hfrm : frame_addr ly AW_CID fpos = F) by exact (Hfa AW_CID fpos).
  destruct ACHK as (AMR & RA0 & SHV0).
  pose proof (aws_acstr_range SEGS _ _ _ HSA) as (Hx0 & Hx1).
  unfold apart_frame in APF. rewrite HK8560 in APF. change (spZ (aw_regs cx)) with (aw_sp cx) in APF.
  (* the alias's shadow at this memory: transported from the call by the read set (LinkWalkShadow.v) *)
  pose proof HJ as HJr. apply LinkWalkCall.aj_stk_row_eq in HJr. destruct HJr as (Ek1 & Ek2).
  pose proof aws_pre_j as HJc. apply LinkWalkCall.aj_stk_row_eq in HJc. destruct HJc as (Ec1 & Ec2).
  assert (Estk1 : ly_stk_lo ly = ly_stk_lo (aw_lyc cx)) by congruence.
  assert (Estk2 : ly_stk_hi ly = ly_stk_hi (aw_lyc cx)) by congruence.
  assert (Hbl : forall b mm, In (b, mm) (ablocks B (aw_lyc cx) (aw_Sc cx)) -> In (b, mm) (ablocks B ly S))
    by (intros b mm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
  assert (FM2 : fmiss (aw_lyc cx) (aw_Sc cx) (aside_rng (aw_lyc cx) AW_CID fpos)).
  { eapply fmiss_side;
      first [exact LAWS | exact TB | exact pa_img_range | exact aws_pre_ar | (unfold AW_CID; lia) | exact F6
            | exact HNIN]. }
  assert (FM : fmiss (aw_lyc cx) (aw_Sc cx) Eacc).
  { intros c q s Hcq Hs [HE | HA]; [|exact (FM2 c q s Hcq Hs HA)].
    unfold aw_E in HE. apply aws_wr_eq in HE.
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c q aws_pre_ar Hcq) as (Hf4 & _).
    unfold shadow_addr, SHADOW_OFF, LA_G_NL, NK_N_SENT in *. lia. }
  assert (TR : range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (aw_alias cx) (Z.of_nat (length sa) + 1) /\
               shadow_hull_vis (aview SEGS (w_H W) m) (aw_alias cx) (Z.of_nat (length sa) + 1)).
  { eapply (shadow_transport_akb SEGS B).
    all: first [ exact LAWS | exact TB | exact pa_img_range | exact aws_pre_ar | exact HAR | exact Estk1
               | exact Estk2 | exact Hbl | exact HK | exact FM | lia
               | (intros a Ha; apply aws_rd_alias; lia) | exact RA0 | exact SHV0 ]. }
  eapply SRr_bind.
  { apply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OCpy (pa_sigma LS___asan_memcpy) AMCPY
      (aw_G cx) (aw_XO cx) (aw_OUT cx) W R m (aw_STK cx) (aw_sp0 cx) (aw_FP cx) (aw_ly cx) (aw_S cx)
      (aw_W0 cx) (aw_mem0 cx) (aw_md0 cx) ((AW_CID, fpos) :: aw_own cx) ly S md (aw_k cx)
      (RQ + 36) (aw_alias cx) (Z.of_nat (length sa)) (getr R 1)).
    - exact aws_pre_g.
    - exact HJ.
    - exact R10.
    - exact R11.
    - exact R12.
    - lia.
    - lia.
    - lia.
    - rewrite Hsp. exact S1al16.
    - rewrite Hsp. unfold ESTACK. lia.
    - rewrite Hsp. lia.
    - rewrite R3. exact Hgp.
    - rewrite R4. exact Htp.
    - reflexivity.
    - rewrite Hra. apply ret_ok_codeptr_v; rewrite HAF; [lia | reflexivity].
    - intros a Ha. left. destruct (aws_awr_F ly S W m md a HI ltac:(lia)) as [H1 H2].
      split; [exact H1|]. split; [exact H2|]. rewrite Hsp. unfold ESTACK. lia.
    - unfold amem_range, in_app in *. destruct F4 as (_ & [HF | (HF & _)]);
        [left; unfold kLowShadowBeg in HF; lia | right; lia].
    - exact (aws_req_ra (aview SEGS (w_H W) m) F (RQ + 36) (Z.of_nat (length sa)) aws_F8 ltac:(lia)
        (proj1 HSB) (proj2 HSB) ltac:(lia) ltac:(lia)).
    - intros Hpos. apply (shadow_hull_vis_of_frame SEGS B LAWS ly S W m md AW_CID fpos (RQ + 36) _ HAR Hin);
        rewrite ?Hfrm; change (fs_frame_bytes AW_CID) with 512; lia.
    - cbv beta iota.
      split; [exact Hx0|].
      split; [unfold amem_range in AMR; destruct AMR as [AM | (_ & AM)]; lia|].
      split.
      { intros a Ha. split.
        - rewrite (aws_alias_now W m a HK ltac:(lia)). exact (aws_alias_some a Ha).
        - rewrite Hsp. unfold ESTACK. lia. }
      split.
      { destruct (Z_le_gt_dec (RQ + 36 + Z.of_nat (length sa)) (aw_alias cx)) as [Hle | Hgt]; [left; exact Hle|].
        destruct (Z_le_gt_dec (aw_alias cx + Z.of_nat (length sa)) (RQ + 36)) as [Hle2 | Hgt2]; [right; exact Hle2|].
        exfalso. apply (aws_alias_not_side (Z.max (aw_alias cx) (RQ + 36)) ltac:(lia)).
        left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes AW_CID) with 512.
        change (frame_addr (aw_lyc cx) AW_CID fpos) with F. lia. }
      split; [unfold amem_range in *; destruct AMR as [AM | (AM1 & AM)]; [left | right]; lia|].
      split; [intros y Hy; exact (proj1 TR y ltac:(lia))|].
      intros Hpos. apply (hull_of_gvis _ (aw_alias cx) (Z.of_nat (length sa)) Hpos).
      intros y Hy. exact (gvis_of_hull _ (aw_alias cx) (Z.of_nat (length sa) + 1) y (proj2 TR) ltac:(lia)). }
  (* the return of checked_memcpy *)
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10 & HCP & UN & HPR & HSBM).
  rewrite Hra.
  assert (Efd : m_fds md2 = m_fds md /\ m_fs md2 = m_fs md).
  { unfold same_but_materialized in HSBM. rewrite HSBM. apply wvb_fds_fs. }
  set (X := fun a => (RQ + 36 <= a < RQ + 36 + Z.of_nat (length sa)) \/ (aw_sp1 cx - ESTACK <= a < aw_sp1 cx)).
  assert (UN' : forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) m a).
  { intros a Ha Hn. apply UN; [exact Ha | intros H; apply Hn; left; exact H |].
    rewrite Hsp. intros H; apply Hn; right; exact H. }
  assert (HX : forall a, X a -> (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK <= a < aw_sp1 cx) \/ (RQ <= a < RQ + 292)).
  { intros a [Ha | Ha]; [right; lia | left; rewrite HK8560; unfold ESTACK in Ha; lia]. }
  assert (HIx : aws_inv ly S W mem2 md2).
  { apply (aws_inv_step ly S W m md mem2 md2 X HI HJ2 UN').
    - intros a Ha. destruct (HX a Ha) as [H | H]; [left; exact H | right; left; lia].
    - exact HPR.
    - exact (proj1 Efd).
    - exact (proj2 Efd). }
  assert (HRQ2 : aws_rq W mem2).
  { destruct HRQ as (V4 & V8 & V20 & V32 & V34 & ZZ).
    assert (KM : forall a, RQ <= a < RQ + 292 -> ~ (RQ + 36 <= a < RQ + 36 + Z.of_nat (length sa)) ->
      mbyte SEGS (rdW W mem2) a = mbyte SEGS (rdW W m) a).
    { intros a Ha Hn. apply (mbyte_of_aview SEGS). apply UN'; [lia|].
      intros [H | H]; [exact (Hn H) | unfold ESTACK in H; lia]. }
    split; [apply (aws_vm_keep _ _ _ _ _ V4); intros k Hk; apply KM; lia|].
    split; [apply (aws_vm_keep _ _ _ _ _ V8); intros k Hk; apply KM; lia|].
    split; [apply (aws_vm_keep _ _ _ _ _ V20); intros k Hk; apply KM; lia|].
    split; [apply (aws_vm_keep _ _ _ _ _ V32); intros k Hk; apply KM; lia|].
    split; [apply (aws_vm_keep _ _ _ _ _ V34); intros k Hk; apply KM; lia|].
    split; [intros i Hi; rewrite KM by lia; apply ZZ; lia|].
    intros i Hi.
    rewrite (aws_mbyte_eq (w_H (aw_W cx)) (w_H W) (aw_memc cx) mem2 (aw_alias cx + Z.of_nat i)
      (RQ + 36 + Z.of_nat i)); [exact (aws_alias_byte i Hi)|].
    rewrite (HCP (Z.of_nat i) ltac:(lia)). exact (aws_alias_now W m (aw_alias cx + Z.of_nat i) HK ltac:(lia)). }
  exact (aws_stage3 ly S W regs2 mem2 md2 HIx (aws_rb_pres R regs2 HR HP2) (aws_rs_pres R regs2 HRS HP2)
    (aws_gnl_keep W m mem2 X UN' HX HG) (aws_shb_keep W m mem2 X UN' HX HSB) HRQ2).
Qed.

(* ==========================================================================
   6. STAGE 2 (+0x2a0 .. +0x2d4): the five header stores; the run stops at the call of checked_memcpy
   ========================================================================== *)
Lemma aws_idx_range : 0 <= index_of tab sn < 2 ^ 31.
Proof.
  destruct HIT as (_ & _ & E).
  assert (G : forall tab', (forall i nm ix, nth_error tab' i = Some (nm, ix) -> 0 <= ix < 2 ^ 31) ->
    0 <= index_of tab' sn < 2 ^ 31).
  { induction tab' as [|[nm ix] t IH]; intros Ht; cbn [index_of]; [lia|].
    destruct (bl_eqb nm sn).
    - exact (Ht 0%nat nm ix eq_refl).
    - apply IH. intros i nm' ix' Hi. exact (Ht (S i) nm' ix' Hi). }
  apply G. intros i nm ix Hi. exact (proj1 (E i nm ix Hi)).
Qed.

(* a byte of a zeroed chunk of a region, as mbyte *)
Lemma aws_zero_of_region : forall (Ex : env) (m : word -> option byte) (r : YP09.region) base off len j,
  region_ok SEGS Ex m r -> base_val Ex (YP09.r_base r) = base ->
  In (YP09.mkChunk off (CZero len)) (YP09.r_chunks r) -> 0 <= j < len ->
  mbyte SEGS m (base + off + j) = Some (Z_to_bv 8 0).
Proof.
  intros Ex m r base off len j HR Hb Hin Hj.
  destruct HR as (_ & _ & _ & HCh). rewrite Forall_forall in HCh.
  pose proof (HCh _ Hin) as Hc. rewrite Hb in Hc.
  destruct (Hc j ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
  cbn [YP09.c_off YP09.c_val] in Hb1, Hb2. cbn in Hb1. injection Hb1 as <-. exact Hb2.
Qed.

Lemma aws_denot_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.

Lemma aws_ew : forall (R : bvmap 5 word) (n : nat) (r : bv 5) v, Z.of_nat n = bv_unsigned r ->
  getr R r = w64 v -> ew (Eimg (Ereg R [])) n = Z_to_bv 64 v.
Proof. intros R n r v Hn H. rewrite (ew_Eimg_Ereg_nat R [] n r Hn). exact H. Qed.

Definition aws_RQ2 : YP09.region := YP09.mkRegion (Some 22%nat) 0 292 0 292 [YP09.mkChunk 12 (CZero 280)].
Definition aws_ss2 : sstate := mkSS (aws_AF + 0x2a0) sr_atoms [aws_RQ2] None (mkFacts [] [] []).

Lemma aws_stage2 : forall ly S W (R : bvmap 5 word) m md,
  aws_inv ly S W m md -> aws_rb R -> aws_rs R ->
  aw_gnl_kept cx W m -> aws_shb W m ->
  (forall i, 12 <= i < 292 -> mbyte SEGS (rdW W m) (RQ + i) = Some (zb 0)) ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + (aws_AF + 0x2a0))) m (seg_rom SEGS)) md) (aw_post SK B cx).
Proof.
  intros ly S W R m md HI HR HRS HG HSB HZ.
  pose proof HI as (HJ & Hfr & _ & _ & Hfa & _).
  pose proof HRS as (R20 & R21 & R22 & R23).
  destruct aws_F as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HL : 0 <= Z.of_nat (length sa) < 256) by (unfold ALIAS_MAX in HAL; lia).
  pose proof aws_idx_range as HIR.
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg R []))) by apply Eimg_env.
  pose proof (aws_U22 R R22) as U22.
  pose proof (aws_aj_ar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin : In (AW_CID, fpos) (frames S)) by (rewrite Hfr; left; reflexivity).
  destruct (aws_frame_present ly S W m md HAR Hin (Hfa AW_CID fpos)) as [HFp _].
  assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg R [])) aws_ss2
    (restrict (w_H W) (mkst R (Z_to_bv 64 (BASE + (aws_AF + 0x2a0))) m (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold aws_ss2. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      unfold region_ok, aws_RQ2. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U22. split; [lia|]. split; [lia|]. split.
      + intros o Ho. apply (YCbq.apresent_writable SEGS). apply HFp. unfold AW_FB. lia.
      + apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi.
        replace (RQ + 12 + i) with (RQ + (12 + i)) by lia. apply HZ. lia.
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
  aws_run_call HS HJ.
  { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. unfold aws_RQ2 in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U22 in Ha.
    left. exact (aws_awr_F ly S W m md a HI ltac:(lia)). }
  intros ms' mat' HS' HJ' HF HF' HG'. cbn [ms_mem mkst] in HF, HF', HG'.
  pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms' HS' eq_refl) as Ems. cbn [ss_pc setpc] in Ems.
  sreg HS' (1%bv : bv 5) Q1. sreg HS' (10%bv : bv 5) Q10. sreg HS' (11%bv : bv 5) Q11.
  sreg HS' (12%bv : bv 5) Q12.
  sreg HS' (2%bv : bv 5) Q2. sreg HS' (9%bv : bv 5) Q9. sreg HS' (8%bv : bv 5) Q8.
  sreg HS' (18%bv : bv 5) Q18. sreg HS' (19%bv : bv 5) Q19. sreg HS' (24%bv : bv 5) Q24.
  sreg HS' (3%bv : bv 5) Q3. sreg HS' (4%bv : bv 5) Q4. sreg HS' (25%bv : bv 5) Q25.
  sreg HS' (26%bv : bv 5) Q26. sreg HS' (27%bv : bv 5) Q27.
  sreg HS' (20%bv : bv 5) Q20. sreg HS' (21%bv : bv 5) Q21. sreg HS' (22%bv : bv 5) Q22.
  sreg HS' (23%bv : bv 5) Q23.
  sregion HS' 0%nat HR2.
  rewrite (aws_atom R 20 (20%bv : bv 5) eq_refl) in Q11. rewrite (aws_atom R 21 (21%bv : bv 5) eq_refl) in Q12.
  rewrite (aws_atom R 2 (2%bv : bv 5) eq_refl) in Q2. rewrite (aws_atom R 9 (9%bv : bv 5) eq_refl) in Q9.
  rewrite (aws_atom R 8 (8%bv : bv 5) eq_refl) in Q8. rewrite (aws_atom R 18 (18%bv : bv 5) eq_refl) in Q18.
  rewrite (aws_atom R 19 (19%bv : bv 5) eq_refl) in Q19. rewrite (aws_atom R 24 (24%bv : bv 5) eq_refl) in Q24.
  rewrite (aws_atom R 3 (3%bv : bv 5) eq_refl) in Q3. rewrite (aws_atom R 4 (4%bv : bv 5) eq_refl) in Q4.
  rewrite (aws_atom R 25 (25%bv : bv 5) eq_refl) in Q25. rewrite (aws_atom R 26 (26%bv : bv 5) eq_refl) in Q26.
  rewrite (aws_atom R 27 (27%bv : bv 5) eq_refl) in Q27.
  rewrite (aws_atom R 20 (20%bv : bv 5) eq_refl) in Q20. rewrite (aws_atom R 21 (21%bv : bv 5) eq_refl) in Q21.
  rewrite (aws_atom R 22 (22%bv : bv 5) eq_refl) in Q22. rewrite (aws_atom R 23 (23%bv : bv 5) eq_refl) in Q23.
  pose proof (aws_ew R 21 (21%bv : bv 5) _ eq_refl R21) as E21.
  pose proof (aws_ew R 22 (22%bv : bv 5) _ eq_refl R22) as E22.
  pose proof (aws_ew R 23 (23%bv : bv 5) _ eq_refl R23) as E23.
  set (mdx := with_vm_backing (m_vm_lazy md) mat' md) in *.
  destruct (wvb_fds_fs (m_vm_lazy md) mat' md) as [Efds Efs]. fold mdx in Efds, Efs.
  (* the run wrote the request only *)
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (RQ <= a < RQ + 292) ->
    aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) m a).
  { intros a Ha Hn. exact (aws_frame_aview _ _ (w_H W) m (ms_mem ms') a HF' Ha
      (aws_not_wr1 R 22 RQ 0 292 0 292 _ a U22 ltac:(lia))). }
  assert (HIx : aws_inv ly S W (ms_mem ms') mdx).
  { apply (aws_inv_step ly S W m md (ms_mem ms') mdx (fun a => RQ <= a < RQ + 292) HI HJ' UN).
    - intros a Ha. right; left. lia.
    - intros a Ha. exact (apresent_grows _ _ _ a HG' Ha).
    - exact Efds.
    - exact Efs. }
  assert (HX : forall a, RQ <= a < RQ + 292 ->
    (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK <= a < aw_sp1 cx) \/ (RQ <= a < RQ + 292)) by (intros a Ha; right; lia).
  (* the request's bytes the region's chunks give *)
  assert (HRQ0 : aws_rq0 W (ms_mem ms')).
  { split; [exact (YC4b.field_of_region (segs := SEGS) _ _ 22 RQ _ 0 292 0 292 4 4%N (SLit 327696) 327696
       HR2 U22 ltac:(cbn; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (YC4b.field_of_region (segs := SEGS) _ _ 22 RQ _ 0 292 0 292 8 4%N (SLit 1) 1
       HR2 U22 ltac:(cbn; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (YC4b.field_of_region (segs := SEGS) _ _ 22 RQ _ 0 292 0 292 20 4%N (SOff 23 0) (index_of tab sn)
       HR2 U22 ltac:(cbn; repeat (first [left; reflexivity | right])) (sv_off0 _ 23 _ E23)
       ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (YC4b.field_of_region (segs := SEGS) _ _ 22 RQ _ 0 292 0 292 32 2%N (SOff 21 4)
       (Z.of_nat (length sa) + 4) HR2 U22 ltac:(cbn; repeat (first [left; reflexivity | right]))
       (aws_denot_off _ 21 _ 4 E21 ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (YC4b.field_of_region (segs := SEGS) _ _ 22 RQ _ 0 292 0 292 34 2%N (SLit 20) 20
       HR2 U22 ltac:(cbn; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    intros i [Hi | [Hi | Hi]].
    - pose proof (aws_zero_of_region _ _ _ RQ 12 8 (i - 12) HR2 ltac:(cbn [YP09.r_base base_val]; exact U22)
        ltac:(cbn; repeat (first [left; reflexivity | right])) ltac:(lia)) as Hz.
      replace (RQ + 12 + (i - 12)) with (RQ + i) in Hz by lia. exact Hz.
    - pose proof (aws_zero_of_region _ _ _ RQ 24 8 (i - 24) HR2 ltac:(cbn [YP09.r_base base_val]; exact U22)
        ltac:(cbn; repeat (first [left; reflexivity | right])) ltac:(lia)) as Hz.
      replace (RQ + 24 + (i - 24)) with (RQ + i) in Hz by lia. exact Hz.
    - pose proof (aws_zero_of_region _ _ _ RQ 36 256 (i - 36) HR2 ltac:(cbn [YP09.r_base base_val]; exact U22)
        ltac:(cbn; repeat (first [left; reflexivity | right])) ltac:(lia)) as Hz.
      replace (RQ + 36 + (i - 36)) with (RQ + i) in Hz by lia. exact Hz. }
  rewrite Ems.
  apply (aws_cpy ly S W (ms_regs ms') (ms_mem ms') mdx HIx
    (aws_rb_of R (ms_regs ms') HR Q2 Q9 Q8 Q18 Q19 Q24 Q3 Q4 Q25 Q26 Q27)).
  - split; [rewrite Q20; exact R20|]. split; [rewrite Q21; exact R21|].
    split; [rewrite Q22; exact R22 | rewrite Q23; exact R23].
  - rewrite Q1. exact (codeptr_val _ _ HEI).
  - rewrite Q10. exact (aws_denot_off _ 22 RQ 36 E22 ltac:(lia)).
  - rewrite Q11. exact R20.
  - rewrite Q12. exact R21.
  - exact (aws_gnl_keep W m (ms_mem ms') _ UN HX HG).
  - exact (aws_shb_keep W m (ms_mem ms') _ UN HX HSB).
  - exact HRQ0.
Qed.

(* ==========================================================================
   7. +0x29c checked_memset(req + 12, 0, 280): aj_gx_intrin_at, op OSet, then stage 2
   ========================================================================== *)
Lemma aws_set : forall ly S W (R : bvmap 5 word) m md,
  aws_inv ly S W m md -> aws_rb R -> aws_rs R ->
  getr R 1 = Z_to_bv 64 (BASE + (aws_AF + 0x2a0)) ->
  getr R 10 = w64 (RQ + 12) -> getr R 11 = w64 0 -> getr R 12 = w64 280 ->
  aw_gnl_kept cx W m -> aws_shb W m ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (pa_sigma LS___asan_memset)) m (seg_rom SEGS)) md) (aw_post SK B cx).
Proof.
  intros ly S W R m md HI HR HRS Hra R10 R11 R12 HG HSB.
  pose proof HI as (HJ & Hfr & _ & _ & Hfa & _).
  pose proof HR as (R2 & R9 & R8 & R18 & R19 & R24 & R3 & R4 & R25 & R26 & R27).
  destruct aws_win as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al & S1al16).
  destruct aws_F as (F1 & F2 & F3 & F4 & F5 & F6).
  destruct aws_pre_misc as (Hgp & Htp & _ & _).
  pose proof (aws_aj_ar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin : In (AW_CID, fpos) (frames S)) by (rewrite Hfr; left; reflexivity).
  pose proof asan_consts as ((C1a & C1b) & _ & C3 & C4 & C5).
  pose proof REAC_LINK_ALIAS_WRITE_AK_val as HK8560.
  pose proof pa_B_ok as (HB0 & HB1 & _).
  assert (HAF : aws_AF = 0x6d88) by reflexivity.
  assert (Hsp : spZ R = aw_sp1 cx) by exact (aws_spZ R R2).
  assert (Hfrm : frame_addr ly AW_CID fpos = F) by exact (Hfa AW_CID fpos).
  eapply SRr_bind.
  { apply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OSet (pa_sigma LS___asan_memset) AMSET
      (aw_G cx) (aw_XO cx) (aw_OUT cx) W R m (aw_STK cx) (aw_sp0 cx) (aw_FP cx) (aw_ly cx) (aw_S cx)
      (aw_W0 cx) (aw_mem0 cx) (aw_md0 cx) ((AW_CID, fpos) :: aw_own cx) ly S md (aw_k cx)
      (RQ + 12) 0 280 (getr R 1)).
    - exact aws_pre_g.
    - exact HJ.
    - exact R10.
    - exact R11.
    - exact R12.
    - lia.
    - lia.
    - lia.
    - rewrite Hsp. exact S1al16.
    - rewrite Hsp. unfold ESTACK. lia.
    - rewrite Hsp. lia.
    - rewrite R3. exact Hgp.
    - rewrite R4. exact Htp.
    - reflexivity.
    - rewrite Hra. apply ret_ok_codeptr_v; rewrite HAF; [lia | reflexivity].
    - intros a Ha. left. destruct (aws_awr_F ly S W m md a HI ltac:(lia)) as [H1 H2].
      split; [exact H1|]. split; [exact H2|]. rewrite Hsp. unfold ESTACK. lia.
    - unfold amem_range, in_app in *. destruct F4 as (_ & [HF | (HF & _)]);
        [left; unfold kLowShadowBeg in HF; lia | right; lia].
    - exact (aws_req_ra (aview SEGS (w_H W) m) F (RQ + 12) 280 aws_F8 ltac:(lia)
        (proj1 HSB) (proj2 HSB) ltac:(lia) ltac:(lia)).
    - intros Hpos. apply (shadow_hull_vis_of_frame SEGS B LAWS ly S W m md AW_CID fpos (RQ + 12) 280 HAR Hin);
        rewrite ?Hfrm; change (fs_frame_bytes AW_CID) with 512; lia.
    - exact I. }
  (* the return of checked_memset *)
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10 & HCP & UN & HPR & HSBM).
  rewrite Hra.
  assert (Efd : m_fds md2 = m_fds md /\ m_fs md2 = m_fs md).
  { unfold same_but_materialized in HSBM. rewrite HSBM. apply wvb_fds_fs. }
  set (X := fun a => (RQ + 12 <= a < RQ + 12 + 280) \/ (aw_sp1 cx - ESTACK <= a < aw_sp1 cx)).
  assert (UN' : forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) m a).
  { intros a Ha Hn. apply UN; [exact Ha | intros H; apply Hn; left; exact H |].
    rewrite Hsp. intros H; apply Hn; right; exact H. }
  assert (HX : forall a, X a -> (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK <= a < aw_sp1 cx) \/ (RQ <= a < RQ + 292)).
  { intros a [Ha | Ha]; [right; lia | left; rewrite HK8560; unfold ESTACK in Ha; lia]. }
  assert (HIx : aws_inv ly S W mem2 md2).
  { apply (aws_inv_step ly S W m md mem2 md2 X HI HJ2 UN').
    - intros a Ha. destruct (HX a Ha) as [H | H]; [left; exact H | right; left; lia].
    - exact HPR.
    - exact (proj1 Efd).
    - exact (proj2 Efd). }
  assert (HZ : forall i, 12 <= i < 292 -> mbyte SEGS (rdW W mem2) (RQ + i) = Some (zb 0)).
  { intros i Hi. apply aws_mbyte0. pose proof (HCP (i - 12) ltac:(lia)) as Hc.
    replace (RQ + 12 + (i - 12)) with (RQ + i) in Hc by lia. rewrite Hc. reflexivity. }
  exact (aws_stage2 ly S W regs2 mem2 md2 HIx (aws_rb_pres R regs2 HR HP2) (aws_rs_pres R regs2 HRS HP2)
    (aws_gnl_keep W m mem2 X UN' HX HG) (aws_shb_keep W m mem2 X UN' HX HSB) HZ).
Qed.

(* ==========================================================================
   8. STAGE 1 (+0x1f0 .. +0x29c): s7 := the index, s6 := F + 32, the request's 37 shadow bytes in scope; the
   run stops at the call of checked_memset
   ========================================================================== *)
Definition aws_ss1 : sstate :=
  mkSS (aws_AF + 0x1f0) sr_atoms [aws_SHR] None (mkFacts [(18%nat, aws_shfact)] [] []).

Lemma aws_shb_of_region : forall (W : world SEGS) E (m : word -> option byte) lo hi wlo whi cs,
  region_ok SEGS E (rdW W m) (YP09.mkRegion (Some 18%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 18) = SH ->
  (forall j, 4 <= j < 40 -> In (YP09.mkChunk j (CVal 1 (SLit 0))) cs) ->
  In (YP09.mkChunk 40 (CVal 1 (SLit 4))) cs ->
  aws_shb W m.
Proof.
  intros W E m lo hi wlo whi cs HR U Hz H4. split.
  - intros j Hj. apply (aview_byte_of_val SEGS (w_H W) m (SH + j) 0); [|lia].
    exact (YC4b.field_of_region (segs := SEGS) E _ 18 SH cs lo hi wlo whi j 1%N (SLit 0) 0 HR U (Hz j Hj) eq_refl
      ltac:(cbn; lia) ltac:(cbn; lia)).
  - apply (aview_byte_of_val SEGS (w_H W) m (SH + 40) 4); [|lia].
    exact (YC4b.field_of_region (segs := SEGS) E _ 18 SH cs lo hi wlo whi 40 1%N (SLit 4) 4 HR U H4 eq_refl
      ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

Lemma aws_stage1 : forall ly S W (R : bvmap 5 word) m md,
  aws_inv ly S W m md -> aws_rb R ->
  getr R 10 = w64 (index_of tab sn) -> getr R 20 = w64 (aw_alias cx) ->
  getr R 21 = w64 (Z.of_nat (length sa)) ->
  aw_gnl_kept cx W m ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + (aws_AF + 0x1f0))) m (seg_rom SEGS)) md) (aw_post SK B cx).
Proof.
  intros ly S W R m md HI HR R10 R20 R21 HG.
  pose proof HI as (HJ & Hfr & _ & _ & Hfa & _).
  pose proof HR as (R2 & R9 & R8 & R18 & R19 & R24 & R3 & R4 & R25 & R26 & R27).
  destruct aws_F as (F1 & F2 & F3 & F4 & F5 & F6).
  destruct aws_SH_val as (SH1 & SH2 & SH3 & SH4 & SH5).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg R []))) by apply Eimg_env.
  pose proof (aws_U18 R R18) as U18.
  pose proof (aws_aj_ar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin : In (AW_CID, fpos) (frames S)) by (rewrite Hfr; left; reflexivity).
  destruct (aws_frame_present ly S W m md HAR Hin (Hfa AW_CID fpos)) as [_ HSp].
  assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg R [])) aws_ss1
    (restrict (w_H W) (mkst R (Z_to_bv 64 (BASE + (aws_AF + 0x1f0))) m (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold aws_ss1. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - destruct (aws_shr_ok W m R R18 (fun a Ha => HSp a ltac:(unfold AW_SHN; lia))) as [H1 _].
      apply Forall_cons; [exact H1 | apply Forall_nil].
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - destruct (aws_shr_ok W m R R18 (fun a Ha => HSp a ltac:(unfold AW_SHN; lia))) as [_ H2].
      cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [split; [exact H2 | exact I] | split; exact I]. }
  aws_run_call HS HJ.
  { exact (aws_awr_shr ly S W m md R HI R18). }
  intros ms' mat' HS' HJ' HF HF' HG'. cbn [ms_mem mkst] in HF, HF', HG'.
  pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms' HS' eq_refl) as Ems. cbn [ss_pc setpc] in Ems.
  sreg HS' (1%bv : bv 5) Q1. sreg HS' (10%bv : bv 5) Q10. sreg HS' (11%bv : bv 5) Q11.
  sreg HS' (12%bv : bv 5) Q12.
  sreg HS' (2%bv : bv 5) Q2. sreg HS' (9%bv : bv 5) Q9. sreg HS' (8%bv : bv 5) Q8.
  sreg HS' (18%bv : bv 5) Q18. sreg HS' (19%bv : bv 5) Q19. sreg HS' (24%bv : bv 5) Q24.
  sreg HS' (3%bv : bv 5) Q3. sreg HS' (4%bv : bv 5) Q4. sreg HS' (25%bv : bv 5) Q25.
  sreg HS' (26%bv : bv 5) Q26. sreg HS' (27%bv : bv 5) Q27.
  sreg HS' (20%bv : bv 5) Q20. sreg HS' (21%bv : bv 5) Q21. sreg HS' (22%bv : bv 5) Q22.
  sreg HS' (23%bv : bv 5) Q23.
  sregion HS' 0%nat HR1.
  rewrite (aws_atom R 2 (2%bv : bv 5) eq_refl) in Q2. rewrite (aws_atom R 9 (9%bv : bv 5) eq_refl) in Q9.
  rewrite (aws_atom R 8 (8%bv : bv 5) eq_refl) in Q8. rewrite (aws_atom R 18 (18%bv : bv 5) eq_refl) in Q18.
  rewrite (aws_atom R 19 (19%bv : bv 5) eq_refl) in Q19. rewrite (aws_atom R 24 (24%bv : bv 5) eq_refl) in Q24.
  rewrite (aws_atom R 3 (3%bv : bv 5) eq_refl) in Q3. rewrite (aws_atom R 4 (4%bv : bv 5) eq_refl) in Q4.
  rewrite (aws_atom R 25 (25%bv : bv 5) eq_refl) in Q25. rewrite (aws_atom R 26 (26%bv : bv 5) eq_refl) in Q26.
  rewrite (aws_atom R 27 (27%bv : bv 5) eq_refl) in Q27.
  rewrite (aws_atom R 20 (20%bv : bv 5) eq_refl) in Q20. rewrite (aws_atom R 21 (21%bv : bv 5) eq_refl) in Q21.
  rewrite (aws_atom R 10 (10%bv : bv 5) eq_refl) in Q23.
  pose proof (aws_ew R 24 (24%bv : bv 5) _ eq_refl R24) as E24.
  set (mdx := with_vm_backing (m_vm_lazy md) mat' md) in *.
  destruct (wvb_fds_fs (m_vm_lazy md) mat' md) as [Efds Efs]. fold mdx in Efds, Efs.
  (* the run wrote the request's shadow only *)
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (SH + 4 <= a < SH + 41) ->
    aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) m a).
  { intros a Ha Hn. exact (aws_frame_aview _ _ (w_H W) m (ms_mem ms') a HF' Ha (aws_not_wr_shr R a U18 Hn)). }
  assert (HIx : aws_inv ly S W (ms_mem ms') mdx).
  { apply (aws_inv_step ly S W m md (ms_mem ms') mdx (fun a => SH + 4 <= a < SH + 41) HI HJ' UN).
    - intros a Ha. right; right. lia.
    - intros a Ha. exact (apresent_grows _ _ _ a HG' Ha).
    - exact Efds.
    - exact Efs. }
  assert (HGx : aw_gnl_kept cx W (ms_mem ms')).
  { intros a Ha. destruct (aws_far a (or_intror Ha)) as (Ha0 & _ & _).
    rewrite (UN a Ha0 ltac:(unfold aws_SB, LA_G_NL, NK_SIZE in *; lia)). exact (HG a Ha). }
  assert (HSBx : aws_shb W (ms_mem ms')).
  { apply (aws_shb_of_region W _ _ _ _ _ _ _ HR1 U18).
    - intros j Hj.
      assert (Ej : j = 4 + Z.of_nat (Z.to_nat (j - 4))) by lia.
      assert (Hk : (Z.to_nat (j - 4) < 36)%nat) by lia.
      rewrite Ej. clear Ej. generalize dependent (Z.to_nat (j - 4)). intros k Hk.
      do 36 (destruct k as [|k]; [cbn [In]; repeat (first [left; reflexivity | right]) |]). lia.
    - cbn [In]. repeat (first [left; reflexivity | right]). }
  rewrite Ems.
  apply (aws_set ly S W (ms_regs ms') (ms_mem ms') mdx HIx
    (aws_rb_of R (ms_regs ms') HR Q2 Q9 Q8 Q18 Q19 Q24 Q3 Q4 Q25 Q26 Q27)).
  - split; [rewrite Q20; exact R20|]. split; [rewrite Q21; exact R21|].
    split; [rewrite Q22; unfold w64; rewrite (aws_denot_off _ 24 F 32 E24 ltac:(lia)); reflexivity |
            rewrite Q23; exact R10].
  - rewrite Q1. exact (codeptr_val _ _ HEI).
  - rewrite Q10. unfold w64. rewrite (aws_denot_off _ 24 F 44 E24 ltac:(lia)). f_equal. lia.
  - rewrite Q11. reflexivity.
  - rewrite Q12. reflexivity.
  - exact HGx.
  - exact HSBx.
Qed.

(* ==========================================================================
   9. THE SEND CUT
   ========================================================================== *)
Lemma aws_send_cut : forall ly S W (ms : machine_state) md,
  ms_pc_val ms = w64 (BASE + AW_CUT_SEND) ->
  getr (ms_regs ms) 10 = w64 (index_of tab sn) -> getr (ms_regs ms) 20 = w64 (aw_alias cx) ->
  getr (ms_regs ms) 21 = w64 (Z.of_nat (length sa)) ->
  aw_gnl_kept cx W (ms_mem ms) -> aw_base SK B cx fpos ly S W ms md ->
  SRr SEGS W (mkCfg ms md) (aw_post SK B cx).
Proof.
  intros ly S W ms md Hpc R10 R20 R21 HG HB.
  pose proof HB as (Hr & Hs & Hrom & Hf & Hc & _ & _ & _ & _ & _ & _ & _ &
    R2 & R9 & R8 & R18 & R19 & R24 & R3 & R4 & R25 & R26 & R27 & _).
  rewrite (aws_ms_eta ms Hr Hs Hf Hc), Hpc, Hrom.
  exact (aws_stage1 ly S W (ms_regs ms) (ms_mem ms) md (aws_inv_of_base ly S W ms md HB)
    (conj R2 (conj R9 (conj R8 (conj R18 (conj R19 (conj R24 (conj R3 (conj R4 (conj R25 (conj R26 R27))))))))))
    R10 R20 R21 HG).
Qed.

End c.

(* THE SEND OBLIGATION from the EXIT one *)
Theorem aw_send : aw_exit_obl SK B -> aw_send_obl SK B.
Proof.
  intros EXIT cx fpos ly3 S3 W3 ms3 md3 HPRE
    (sn & sa & tab & kbs & Hpc & HNK & HIT & HSN & HN0 & HSNE & HSA & HA0 & HAL & R10 & HIDX & R20 & R21 & R22 & R23
     & HG & HB).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HNIN & _ & _ & HS1 & _).
  eapply aws_send_cut; eassumption.
Qed.

End b.
End a.

Print Assumptions aw_send.
About aw_send.
