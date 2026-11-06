(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v, with its module names changed; 1018 of its 1062 lines of code are new or changed and 265 lines of the source are left out. *)
(* attr_text (fuzz_link.c:168-172) on image A (fuzz_link.asan 0x86b18, 820 bytes; listing
   (internal path) (internal record, sha256 03340ee12716)): the shared part of the walk of
   lib/A/Prog/attr_text_c.v `attr_text_acontract` on link's program tables, through the walk kit
   lib/A/Prog/LinkWalk.v, the nl_w kit lib/A/Prog/LinkWalkNlw.v and the journal lifts of lib/A/Prog/link_ajkit.v
   and lib/A/Prog/LinkWalkStrS.v. The phases are lib/A/Prog/attr_text_p3.v, attr_text_p2.v, attr_text_p1.v; the
   entry phase and the top lemma `attr_text_aproof` are lib/A/Prog/attr_text.v.

   THE SHAPE OF THE WALK. The code joins at +0xec, +0x170, +0x1d4 and +0x244 (each room test's no-room arm stores
   full := 1 and jumps to the join), so the walk is a chain of phase lemmas, last phase first, as pcap's
   PcapSourceNext*.v do: `at_from GI` says "from any machine state GI describes the run reaches the contract's
   Post", and a phase lemma is `at_from GI_next -> at_from GI_self`. No path is walked twice.

   THE JOIN INVARIANT IS CONCRETE, not symbolic (pcap joins two symbolic states with its YC1g / YC1h surgery
   lemmas, which link's tree does not carry): `at_inv cx pc len n f ms md` names the pc, the seven live registers,
   the eight saved words of the frame, the journal, the struct nl_w through LinkWalkNlw.nlw_fields, and what the
   run has kept so far (`at_kept`). Each phase REBUILDS the symbolic state from the invariant (`at_entry_J`, with
   `pa_entry_st_ok_full`, as pcap's PcapSourceClose.cl_entry does at the entry) and runs from there; at the next
   join `at_inv_of` / `at_inv4_of` turn the machine state back into the invariant. So the phases share nothing but
   this Prop.

   THE SYMBOLIC STATE. Bx = SOff 32 0 (the shadow base, which the code loads through the .got cell 0xa19d0 ->
   0xaa438 and AR's const law fixes at SHADOW_OFF), Bspan = (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) as pcap uses.
   The shadow entries SH make the sixteen instrumented checks pass by computation: the loads of check C1 (the 8
   bytes of n) and C2 (the 4 bytes of full) at the entry [w + 4096, w + 4112), and the two byte checks of C3 at an
   entry [w + n, w + n + 2) on the arms that store into w->b (their slow path `a & 7 < s` is resolved by the
   engine's tokens). Each entry's `shent_ok` is the Pre's `range_addressable (ard m) SHADOW_OFF w NW_SIZE` on a
   sub-range, kept by every step because no step writes a shadow byte of the struct (`at_she_ok`), and its
   `app_apart` follows from `amem_range` (both arms of it: below kLowMemEnd = SHADOW_OFF, or at or above
   kHighMemBeg = SHADOW_OFF + 2 ^ 44). The engine resolves the address `w + n` (n read from memory) only through an
   alias `(w + n, SOff 35 0)` to the atom 35, which `at_extra` sets to w + n; the two-byte store then lands in a
   region based at atom 35, which is disjoint from the field region because the room test has decided n <= 4094.

   Proves no function (kind: segment lemma). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YK0e.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC85G.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkLeaf LinkWalkNlw LinkWalkSide attr_text_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* the listing offsets of the phase cuts (the function's own offsets; AF_attr_text + o is the listing offset) *)
Definition AT_J1 : Z := AF_attr_text + 0xec.      (* 0x86c04, the first join *)
Definition AT_J2 : Z := AF_attr_text + 0x170.     (* 0x86c88, the second join *)
Definition AT_J3 : Z := AF_attr_text + 0x1d4.     (* 0x86cec, the third join *)
Definition AT_J4 : Z := AF_attr_text + 0x244.     (* 0x86d5c, the epilogue *)

(* the frame: 64 bytes, with ra and s0..s6 saved at these offsets from the ENTRY sp *)
Definition AT_FRAME : Z := 64.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
(* The relro window: a Section variable here, because every lemma of this file holds for any window. The top
   lemma is stated at the CONSTANTS PCAP_RLO / PCAP_RHI of lib/A/Prog/PcapRelro.v (the kernel walk's cross-lane
   rule): no instance pins the PAImg fields pa_relro_lo / pa_relro_hi. *)
Variables rlo rhi : Z.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TL : PALib B.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ==========================================================================
   The call's context: everything the contract's premises fix, in one record, so that a phase lemma states one
   hypothesis instead of twenty (pcap's `ncx`, PcapSourceNextDefs.v:233-251).
   ========================================================================== *)

Record atcx : Type := mkATCX {
  c_G : list (Z * Z); c_XO : Z; c_OUT : list (Z * Z);
  c_STK : Z; c_sp0 : Z; c_FP : list (Z * Z);
  c_ly : alayout; c_S : astate; c_W0 : world SEGS; c_mem0 : word -> option byte; c_md0 : Model;
  c_own : list (Z * Z);
  c_lyc : alayout; c_Sc : astate; c_W : world SEGS; c_memc : word -> option byte; c_mdc : Model; c_k : Z;
  c_regs : bvmap 5 word;
  c_bs : list byte;        (* the Pre's byte list of the struct nl_w *)
  c_str : list byte        (* the Pre's string at a2 *)
}.

Definition c_w (cx : atcx) : Z := aarg (c_regs cx) 0.
Definition c_s (cx : atcx) : Z := aarg (c_regs cx) 2.
Definition c_sp (cx : atcx) : Z := spZ (c_regs cx).
Definition c_mem (cx : atcx) : word -> option byte := rdW (c_W cx) (c_memc cx).
Definition c_slen (cx : atcx) : Z := Z.of_nat (length (c_str cx)).
Definition c_n0 (cx : atcx) : Z := nw_n (c_bs cx).

(* the write set and the exception set of the Post *)
Definition c_Wr (cx : atcx) : list (Z * Z) := attr_text_awr (c_regs cx) (c_mem cx).
Definition c_E (cx : atcx) : Z -> Prop := fun a => inFP (c_Wr cx) a.

(* the contract's Post at this context *)
Definition at_post (cx : atcx) : world SEGS -> config -> Prop :=
  apost SK SEGS B ATTR_TEXT_AK 0 (c_E cx)
    (c_G cx) (c_XO cx) (c_OUT cx) (c_STK cx) (c_sp0 cx) (c_FP cx)
    (c_ly cx) (c_S cx) (c_W0 cx) (c_mem0 cx) (c_md0 cx) (c_own cx)
    (c_lyc cx) (c_Sc cx) (c_W cx) (c_memc cx) (c_mdc cx) (c_k cx) (c_regs cx)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       S2 = set_fs (st_fs S2) (c_Sc cx) /\ Permutation (ablocks B ly2 S2) (ablocks B (c_lyc cx) (c_Sc cx)) /\
       attr_text_apost SEGS (c_regs cx) (c_mem cx) regs2 (rdW W2 mem2)).

(* the premises: `apre` of link_amem.v, the read-set side condition of `aleaf_rd`, and the function's own Pre,
   with the two existential witnesses taken from the record *)
Definition at_base (cx : atcx) : Prop :=
  apre SK SEGS rlo rhi B ATTR_TEXT_AK 0 [] (c_Wr cx)
    (c_G cx) (c_XO cx) (c_OUT cx) (c_STK cx) (c_sp0 cx) (c_FP cx)
    (c_ly cx) (c_S cx) (c_W0 cx) (c_mem0 cx) (c_md0 cx) (c_own cx)
    (c_lyc cx) (c_Sc cx) (c_W cx) (c_memc cx) (c_mdc cx) (c_k cx) (c_regs cx)
  /\ (forall a, attr_text_ard SEGS (c_regs cx) (c_mem cx) a ->
        akb SEGS B (c_lyc cx) (c_Sc cx) (c_sp cx - ATTR_TEXT_AK) (c_sp cx) a)
  /\ anlw_at SEGS (c_mem cx) (c_w cx) (c_bs cx) /\ nlw_wf (c_bs cx)
  /\ c_s cx <> 0 /\ acstr_at SEGS (c_mem cx) (c_s cx) (c_str cx) /\ c_slen cx + 1 < 2 ^ 32
  /\ (exists slack, abytes SEGS (c_mem cx) (c_s cx + c_slen cx + 1) slack
        /\ (- (c_s cx + c_slen cx + 1)) mod 8 <= Z.of_nat (length slack))
  /\ apart (c_w cx) NW_SIZE (c_s cx) (c_slen cx + 1)
  /\ apart_frame (c_regs cx) ATTR_TEXT_AK (c_w cx) NW_SIZE
  /\ apart_frame (c_regs cx) ATTR_TEXT_AK (c_s cx) (c_slen cx + 1)
  /\ amem_range (c_w cx) NW_SIZE
  /\ range_addressable (ard SEGS (c_mem cx)) SHADOW_OFF (c_w cx) NW_SIZE
  /\ shadow_hull_vis (ard SEGS (c_mem cx)) (c_w cx) NW_SIZE
  /\ amem_range (c_s cx) (c_slen cx + 1)
  /\ range_addressable (ard SEGS (c_mem cx)) SHADOW_OFF (c_s cx) (c_slen cx + 1)
  /\ shadow_hull_vis (ard SEGS (c_mem cx)) (c_s cx) (c_slen cx + 1).

(* ==========================================================================
   What a phase carries
   ========================================================================== *)

(* What the run has kept so far, against the memory at the call: every byte off the window [sp - K, sp) and off
   the write set (the struct) keeps its view, presence grows, and the window is present. It is the premise
   LinkWalkSide.apost_leaf_AR asks at the `ret`. *)
Definition at_kept (cx : atcx) (mem3 : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp cx - ATTR_TEXT_AK <= a < c_sp cx) -> ~ c_E cx a ->
     aview SEGS (w_H (c_W cx)) mem3 a = aview SEGS (w_H (c_W cx)) (c_memc cx) a) /\
  (forall a, apresent (w_H (c_W cx)) (c_memc cx) a -> apresent (w_H (c_W cx)) mem3 a) /\
  (forall a, c_sp cx - ATTR_TEXT_AK <= a < c_sp cx -> apresent (w_H (c_W cx)) mem3 a).

(* The eight words the prologue saved, at their offsets below the entry sp. *)
Definition at_saved (cx : atcx) (mem3 : word -> option byte) : Prop :=
  val_mem SEGS (rdW (c_W cx) mem3) (c_sp cx - 8) 8 (raZ (c_regs cx)) /\
  val_mem SEGS (rdW (c_W cx) mem3) (c_sp cx - 16) 8 (bv_unsigned (getr (c_regs cx) 8)) /\
  val_mem SEGS (rdW (c_W cx) mem3) (c_sp cx - 24) 8 (bv_unsigned (getr (c_regs cx) 9)) /\
  val_mem SEGS (rdW (c_W cx) mem3) (c_sp cx - 32) 8 (bv_unsigned (getr (c_regs cx) 18)) /\
  val_mem SEGS (rdW (c_W cx) mem3) (c_sp cx - 40) 8 (bv_unsigned (getr (c_regs cx) 19)) /\
  val_mem SEGS (rdW (c_W cx) mem3) (c_sp cx - 48) 8 (bv_unsigned (getr (c_regs cx) 20)) /\
  val_mem SEGS (rdW (c_W cx) mem3) (c_sp cx - 56) 8 (bv_unsigned (getr (c_regs cx) 21)) /\
  val_mem SEGS (rdW (c_W cx) mem3) (c_sp cx - 64) 8 (bv_unsigned (getr (c_regs cx) 22)).

(* The registers the callee-saved set keeps untouched for the whole body: gp, tp, s7..s11. *)
Definition at_regs_kept (cx : atcx) (regs3 : bvmap 5 word) : Prop :=
  getr regs3 3 = getr (c_regs cx) 3 /\ getr regs3 4 = getr (c_regs cx) 4 /\
  getr regs3 23 = getr (c_regs cx) 23 /\ getr regs3 24 = getr (c_regs cx) 24 /\
  getr regs3 25 = getr (c_regs cx) 25 /\ getr regs3 26 = getr (c_regs cx) 26 /\
  getr regs3 27 = getr (c_regs cx) 27.

(* The machine state at a cut: the pc, the shape of the state, the live registers, the frame and the journal. *)
Definition at_shape (cx : atcx) (pc : Z) (ms3 : machine_state) : Prop :=
  ms_pc_val ms3 = w64 (BASE + pc) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  spZ (ms_regs ms3) = c_sp cx - AT_FRAME /\
  at_regs_kept cx (ms_regs ms3) /\ at_saved cx (ms_mem ms3).

(* The seven registers the body keeps live from +0x50 on: s0 = w + 4096, s1 = w, s2 = s, s3 = len,
   s4 = type, s5 = the shadow byte address of w + 4096, s6 = the shadow base. *)
Definition at_live (cx : atcx) (len : Z) (regs3 : bvmap 5 word) : Prop :=
  getr regs3 8 = w64 (c_w cx + NW_N) /\
  getr regs3 9 = w64 (c_w cx) /\
  getr regs3 18 = w64 (c_s cx) /\
  getr regs3 19 = w64 len /\
  getr regs3 20 = getr (c_regs cx) 11 /\
  getr regs3 21 = alu64 ALU_ADD (alu64 ALU_SRL (getr regs3 8) (w64 3)) (getr regs3 22) /\
  getr regs3 22 = w64 SHADOW_OFF.

(* THE JOIN INVARIANT. `n` and `f` are the struct's two fields now; `len` is the length the first room test
   compares (strlen(s) + (bare = 0)). *)
Definition at_inv (cx : atcx) (pc : Z) (len n f : Z)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  at_shape cx pc ms3 /\ at_live cx len (ms_regs ms3) /\
  ajournal_gx SEGS B (c_G cx) (c_XO cx) (c_OUT cx) (c_STK cx) (c_sp0 cx) (c_FP cx)
    (c_ly cx) (c_S cx) (c_W0 cx) (c_mem0 cx) (c_md0 cx) (c_own cx)
    (c_lyc cx) (c_Sc cx) (c_W cx) (ms_mem ms3) md3 (c_k cx) /\
  m_fds md3 = m_fds (c_mdc cx) /\ m_fs md3 = m_fs (c_mdc cx) /\
  nlw_fields SEGS (rdW (c_W cx) (ms_mem ms3)) (c_w cx) n f /\
  c_n0 cx <= n /\
  0 <= len /\ len <= c_slen cx + 1 /\
  at_kept cx (ms_mem ms3).

(* "From every state this invariant describes, the run reaches the contract's Post." *)
Definition at_from (GI : atcx -> Z -> Z -> Z -> machine_state -> Model -> Prop) : Prop :=
  forall cx len n f ms3 md3,
    at_base cx -> GI cx len n f ms3 md3 -> SRr SEGS (c_W cx) (mkCfg ms3 md3) (at_post cx).

(* ==========================================================================
   What every phase needs of the kit
   ========================================================================== *)

(* The allocator state of a leaf: a record is its own field update. *)
Lemma at_set_fs_self : forall S : astate, set_fs (st_fs S) S = S.
Proof. intros S. destruct S. reflexivity. Qed.

(* A machine state at a cut is the one `mkst` builds, so that pa_entry_st_ok_full applies to it. *)
Lemma at_ms_shape : forall (ms : machine_state) (pc : Z),
  ms_pc_val ms = w64 pc -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (w64 pc) (ms_mem ms) (seg_rom SEGS).
Proof.
  intros [rg fr pcv sv rv fc mm rm] pc H1 H2 H3 H4 H5 H6.
  cbn in H1, H2, H3, H4, H5, H6. subst. reflexivity.
Qed.

(* A value stays where the bytes under it did not change. *)
Lemma at_val_mem_keep : forall (m m' : word -> option byte) a (n : nat) v,
  (forall i, 0 <= i < Z.of_nat n -> mbyte SEGS m' (a + i) = mbyte SEGS m (a + i)) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof.
  intros m m' a n v Hk HV k Hk2.
  rewrite (Hk (Z.of_nat k) ltac:(lia)). exact (HV k Hk2).
Qed.

(* The eight saved words stay where the frame did not change. *)
Lemma at_saved_keep : forall cx (m m' : word -> option byte),
  (forall a, c_sp cx - AT_FRAME <= a < c_sp cx ->
     mbyte SEGS (rdW (c_W cx) m') a = mbyte SEGS (rdW (c_W cx) m) a) ->
  at_saved cx m -> at_saved cx m'.
Proof.
  intros cx m m' Hk (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
  unfold at_saved. unfold AT_FRAME in Hk.
  repeat split;
    [ eapply at_val_mem_keep; [| exact V1] | eapply at_val_mem_keep; [| exact V2]
    | eapply at_val_mem_keep; [| exact V3] | eapply at_val_mem_keep; [| exact V4]
    | eapply at_val_mem_keep; [| exact V5] | eapply at_val_mem_keep; [| exact V6]
    | eapply at_val_mem_keep; [| exact V7] | eapply at_val_mem_keep; [| exact V8] ];
    intros i Hi; apply Hk; lia.
Qed.

(* A byte a run keeps present is present (the run's mem_grows, on the restricted maps). *)
Lemma at_apres_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' a Hg (Hh & b & Hb). split; [exact Hh|].
  specialize (Hg (Z_to_bv 64 a)). unfold mrestrict in Hg. rewrite Hh in Hg.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [exists b'; reflexivity|].
  exfalso. apply Hg; [rewrite Hb; discriminate | reflexivity].
Qed.

(* aregs_preserved from the fifteen callee-saved registers, one by one. *)
Lemma at_aregs : forall (regs regs' : bvmap 5 word),
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
  getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
  getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
  getr regs' 27 = getr regs 27 ->
  aregs_preserved regs regs'.
Proof.
  intros regs regs' Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 r Hr.
  unfold acallee_saved in Hr.
  assert (Hv : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
               r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  assert (G : forall (k : Z) (rr : bv 5), r = k -> Z_to_bv 5 k = rr ->
            getr regs' rr = getr regs rr -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros k rr Hrk Hk Hq. subst r. rewrite Hk. exact Hq. }
  repeat match goal with Hq : _ \/ _ |- _ => destruct Hq end;
  first [ exact (G 2 2%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q2)
        | exact (G 3 3%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q3)
        | exact (G 4 4%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q4)
        | exact (G 8 8%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q8)
        | exact (G 9 9%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q9)
        | exact (G 18 18%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q18)
        | exact (G 19 19%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q19)
        | exact (G 20 20%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q20)
        | exact (G 21 21%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q21)
        | exact (G 22 22%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q22)
        | exact (G 23 23%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q23)
        | exact (G 24 24%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q24)
        | exact (G 25 25%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q25)
        | exact (G 26 26%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q26)
        | exact (G 27 27%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q27) ].
Qed.

(* The bytes the call writes miss the shadow band: `amem_range` puts the struct below kLowMemEnd = SHADOW_OFF
   or at or above kHighMemBeg = SHADOW_OFF + 2 ^ 44 (a run's w lies in a side frame, above the band). *)
Lemma at_E_band : forall cx, amem_range (c_w cx) NW_SIZE ->
  forall x, c_E cx x -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44).
Proof.
  intros cx HR x (r & Hin & Hx). unfold c_Wr, attr_text_awr in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[]]. cbn [fst snd] in Hx. fold (c_w cx) in Hx.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, NW_SIZE, SHADOW_OFF in *. lia.
Qed.

(* ==========================================================================
   PHASE 4: the epilogue (+0x244 .. +0x268 `ret`)
   ========================================================================== *)

(* The invariant at the last join: the body is done, only the frame and what the call keeps matter. *)
Definition at_inv4 (cx : atcx) (n f : Z) (ms3 : machine_state) (md3 : Model) : Prop :=
  at_shape cx AT_J4 ms3 /\
  ajournal_gx SEGS B (c_G cx) (c_XO cx) (c_OUT cx) (c_STK cx) (c_sp0 cx) (c_FP cx)
    (c_ly cx) (c_S cx) (c_W0 cx) (c_mem0 cx) (c_md0 cx) (c_own cx)
    (c_lyc cx) (c_Sc cx) (c_W cx) (ms_mem ms3) md3 (c_k cx) /\
  m_fds md3 = m_fds (c_mdc cx) /\ m_fs md3 = m_fs (c_mdc cx) /\
  nlw_fields SEGS (rdW (c_W cx) (ms_mem ms3)) (c_w cx) n f /\
  c_n0 cx <= n /\
  at_kept cx (ms_mem ms3).

(* its symbolic state: the frame's eight saved words, read back by the epilogue; no writable window and no
   shadow entry (the epilogue makes no check) *)
Definition at_fr_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 64 0 0
    [YP09.mkChunk 0x38 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x30 (CVal 8 (SOff 33 0));
     YP09.mkChunk 0x28 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x20 (CVal 8 (SOff 35 0));
     YP09.mkChunk 0x18 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x10 (CVal 8 (SOff 37 0));
     YP09.mkChunk 0x8 (CVal 8 (SOff 38 0)); YP09.mkChunk 0 (CVal 8 (SOff 39 0))].
Definition at_extra4 (cx : atcx) : list word :=
  [getr (c_regs cx) 1; getr (c_regs cx) 8; getr (c_regs cx) 9; getr (c_regs cx) 18;
   getr (c_regs cx) 19; getr (c_regs cx) 20; getr (c_regs cx) 21; getr (c_regs cx) 22].
Definition at_ss4 : sstate := mkSS AT_J4 sr_atoms [at_fr_region] None (mkFacts [] [] []).
Definition at_Bx0 : sv := SLit SHADOW_OFF.
Definition at_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* s5, the shadow byte address of w + NW_N that the code built at +0x50..+0x54, as the symbolic value every
   join must give it so that the engine's `match_x` still sees the `(x >> 3) + Bx` pattern. *)
Definition at_sh5 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 4096) (SLit 3)) (SOff 32 0).

Lemma at_sh5_regs : forall (E : env) (regs3 : bvmap 5 word) (wv : Z),
  ew E 9%nat = getr regs3 9 -> ew E 32%nat = getr regs3 22 ->
  getr regs3 9 = w64 wv -> 0 <= wv -> wv + NW_SIZE <= 2 ^ 64 ->
  getr regs3 8 = w64 (wv + NW_N) ->
  sv_denot E at_sh5 = alu64 ALU_ADD (alu64 ALU_SRL (getr regs3 8) (w64 3)) (getr regs3 22).
Proof.
  intros E regs3 wv H9 H32 Hw Hlo Hhi H8.
  unfold at_sh5. cbn [sv_denot]. rewrite H9, H32, Hw.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned, H8.
  f_equal. f_equal. unfold w64, NW_SIZE, NW_N in *.
  rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Theorem at_p4 : at_from (fun cx _ n f ms3 md3 => at_inv4 cx n f ms3 md3).
Proof.
intros cx len n f ms3 md3 HB HI.
destruct HB as (HPRE & HRD & HNLW & HWF & Hs0 & HSTR & HSLEN & HSLACK & HAP & HAPF1 & HAPF2 &
  HMR1 & HRA1 & HHV1 & HMR2 & HRA2 & HHV2).
destruct HPRE as (HJ0 & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside &
  Hajw & Hro).
destruct HI as (HSHAPE & HJ & HFDS & HFS & HFIELDS & HN0 & HKEPT).
destruct HSHAPE as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc & Hsp & HRK & HSAV).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (Hceil : alloc_ceiling <= c_sp0 cx - c_STK cx) by (eapply (aj_stk_ceiling SK SEGS B); exact HJ0).
pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (HAR0 & _).
assert (HSPlo : alloc_ceiling + ATTR_TEXT_AK <= c_sp cx) by (unfold c_sp in *; lia).
assert (HSPhi : c_sp cx < 2 ^ 64)
  by (unfold c_sp, spZ; pose proof (u64_range (getr (c_regs cx) 2)); lia).
assert (HAK : ATTR_TEXT_AK = 4160) by reflexivity.
(* the environment at the join *)
set (E := Eimg (Ereg (ms_regs ms3) (at_extra4 cx))).
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg (ms_regs ms3) (at_extra4 cx)) m)
  by (intros m Hm; subst E; apply Eimg_low; exact Hm).
assert (E2 : ew E 2%nat = getr (ms_regs ms3) 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 2 2%bv eq_refl)).
assert (U2 : bv_unsigned (ew E 2%nat) = c_sp cx - AT_FRAME) by (rewrite E2; exact Hsp).
assert (EX : forall j, (j < 8)%nat -> ew E (32 + j)%nat = nth j (at_extra4 cx) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
cbn [at_extra4 nth Nat.add] in E32, E33, E34, E35, E36, E37, E38, E39.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
destruct HSAV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
(* the eight saved words, as the frame region's chunks *)
assert (CHK : forall (od : Z) (m : nat) (x : word),
  ew E m = x -> val_mem SEGS (rdW (c_W cx) (ms_mem ms3)) (c_sp cx - AT_FRAME + od) 8 (bv_unsigned x) ->
  YP09.chunk_ok SEGS E (mrestrict (w_H (c_W cx)) (ms_mem ms3)) (c_sp cx - AT_FRAME)
    (YP09.mkChunk od (CVal 8 (SOff m 0)))).
{ intros od m x Hm HV.
  apply (chunk_ok_val SEGS E _ (c_sp cx - AT_FRAME) od 8%N (SOff m 0) (bv_unsigned x)).
  - cbn [sv_denot]. rewrite Z.add_0_r, Hm, Z_to_bv_bv_unsigned. reflexivity.
  - cbn [Z.of_N]. pose proof (u64_range x). lia.
  - cbn [Z.of_N]. lia.
  - exact HV. }
assert (HS : st_ok_pi SEGS pa_val E at_ss4 (restrict (w_H (c_W cx)) ms3)).
{ rewrite (at_ms_shape ms3 (BASE + AT_J4) Hpc Hrv Hsvc Hrom Hfr Hfc).
  rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold at_fr_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2.
    split; [unfold AT_FRAME in *; lia|].
    split; [unfold AT_FRAME in *; lia|].
    split; [intros o Ho; lia|].
    cbn [ms_mem restrict mkst].
    repeat (apply Forall_cons); [| | | | | | | | apply Forall_nil].
    + apply (CHK 0x38 32%nat (getr (c_regs cx) 1) E32).
      replace (c_sp cx - AT_FRAME + 0x38) with (c_sp cx - 8) by (unfold AT_FRAME; lia). exact V1.
    + apply (CHK 0x30 33%nat (getr (c_regs cx) 8) E33).
      replace (c_sp cx - AT_FRAME + 0x30) with (c_sp cx - 16) by (unfold AT_FRAME; lia). exact V2.
    + apply (CHK 0x28 34%nat (getr (c_regs cx) 9) E34).
      replace (c_sp cx - AT_FRAME + 0x28) with (c_sp cx - 24) by (unfold AT_FRAME; lia). exact V3.
    + apply (CHK 0x20 35%nat (getr (c_regs cx) 18) E35).
      replace (c_sp cx - AT_FRAME + 0x20) with (c_sp cx - 32) by (unfold AT_FRAME; lia). exact V4.
    + apply (CHK 0x18 36%nat (getr (c_regs cx) 19) E36).
      replace (c_sp cx - AT_FRAME + 0x18) with (c_sp cx - 40) by (unfold AT_FRAME; lia). exact V5.
    + apply (CHK 0x10 37%nat (getr (c_regs cx) 20) E37).
      replace (c_sp cx - AT_FRAME + 0x10) with (c_sp cx - 48) by (unfold AT_FRAME; lia). exact V6.
    + apply (CHK 0x8 38%nat (getr (c_regs cx) 21) E38).
      replace (c_sp cx - AT_FRAME + 0x8) with (c_sp cx - 56) by (unfold AT_FRAME; lia). exact V7.
    + apply (CHK 0 39%nat (getr (c_regs cx) 22) E39).
      replace (c_sp cx - AT_FRAME + 0) with (c_sp cx - 64) by (unfold AT_FRAME; lia). exact V8.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [cbn; exact I | split; [exact I | exact I]]. }
assert (SHOK : sh_ok SEGS at_Bx0 (@nil shent) E (mrestrict (w_H (c_W cx)) (ms_mem ms3)))
  by apply Forall_nil.
pose (RUN := paj_run_x SK B LAWS (c_G cx) HGok (c_XO cx) (c_OUT cx)).
pose (RET := paj_ret_at (PL := PL_link) (PI := PI)).
paj_run_tok RUN HS HJ SHOK at_span.
{ unfold at_ss4, at_fr_region. cbn [ss_mem].
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
(* The run only read: every byte is the byte it was at the join. *)
pose proof (kept_of_frame (segs := SEGS) E (ss_mem at_ss4) (w_H (c_W cx)) (ms_mem ms3) _
  (fun _ => False) HFr
  ltac:(intros bb wlo whi aa Hin Hrr; exfalso; vm_compute in Hin;
        repeat (destruct Hin as [Hq|Hin];
                [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]);
        destruct Hin)) as UN2.
lazymatch goal with
| HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
  (* every register, off the symbolic state *)
  assert (REG : forall (r : bv 5) (m : nat), sr_get (ss_regs ssx) r = SOff m 0 ->
            getr (ms_regs msc) r = Z_to_bv 64 (bv_unsigned (ew E m)));
  [ intros r m Hr; rewrite (st_ok_pi_restrict_reg (w_H (c_W cx)) E ssx msc r HS), Hr;
    cbn [sv_denot]; rewrite Z.add_0_r; reflexivity |];
  assert (REGK : forall (r : bv 5) (m : nat) (k : Z), sr_get (ss_regs ssx) r = SOff m k ->
            getr (ms_regs msc) r = Z_to_bv 64 (bv_unsigned (ew E m) + k));
  [ intros r m k Hr; rewrite (st_ok_pi_restrict_reg (w_H (c_W cx)) E ssx msc r HS), Hr;
    cbn [sv_denot]; reflexivity |];
  assert (ER : forall (j : nat) (r : bv 5), (j < 32)%nat -> Z.of_nat j = bv_unsigned r ->
            ew E j = getr (ms_regs ms3) r);
  [ intros j r Hj Hr; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ j r Hr) |];
  (* the memory at the end is the memory at the join *)
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp cx - ATTR_TEXT_AK <= a < c_sp cx) -> ~ c_E cx a ->
            aview SEGS (w_H (c_W cx)) (ms_mem msc) a = aview SEGS (w_H (c_W cx)) (c_memc cx) a);
  [ intros a Ha Hw He; rewrite (UN2 a Ha ltac:(intros [])); exact (proj1 HKEPT a Ha Hw He) |];
  assert (HPG : forall a, apresent (w_H (c_W cx)) (c_memc cx) a ->
            apresent (w_H (c_W cx)) (ms_mem msc) a);
  [ intros a Ha; exact (at_apres_grows _ _ _ a HG (proj1 (proj2 HKEPT) a Ha)) |];
  assert (HPW : forall a, c_sp cx - ATTR_TEXT_AK <= a < c_sp cx ->
            apresent (w_H (c_W cx)) (ms_mem msc) a);
  [ intros a Ha; exact (at_apres_grows _ _ _ a HG (proj2 (proj2 HKEPT) a Ha)) |];
  (* the struct's two fields at the end *)
  assert (HFIN : nlw_fields SEGS (rdW (c_W cx) (ms_mem msc)) (c_w cx) n f);
  [ pose proof HFIELDS as (Hw0 & Hwl & _);
    apply (nlw_fields_agree SEGS (rdW (c_W cx) (ms_mem ms3)) _ _ _ _ HFIELDS);
    intros i Hi; split;
    [ apply (mbyte_of_aview SEGS (w_H (c_W cx)) (w_H (c_W cx)));
      apply UN2; [unfold NW_SIZE in *; lia | intros []]
    | intros Hwb; exact (writable_at_grows SEGS _ _ _ HG Hwb) ] |];
  (* the fifteen callee-saved registers *)
  assert (HARP : aregs_preserved (c_regs cx) (ms_regs msc));
  [ apply at_aregs;
    [ rewrite (REGK 2%bv 2%nat 64 ltac:(vm_compute; reflexivity)), U2;
      replace (c_sp cx - AT_FRAME + 64) with (bv_unsigned (getr (c_regs cx) 2))
        by (unfold c_sp, spZ, AT_FRAME; lia);
      apply Z_to_bv_bv_unsigned
    | rewrite (REG 3%bv 3%nat ltac:(vm_compute; reflexivity)),
        (ER 3%nat 3%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned;
      exact (proj1 HRK)
    | rewrite (REG 4%bv 4%nat ltac:(vm_compute; reflexivity)),
        (ER 4%nat 4%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned;
      exact (proj1 (proj2 HRK))
    | rewrite (REG 8%bv 33%nat ltac:(vm_compute; reflexivity)), E33, Z_to_bv_bv_unsigned; reflexivity
    | rewrite (REG 9%bv 34%nat ltac:(vm_compute; reflexivity)), E34, Z_to_bv_bv_unsigned; reflexivity
    | rewrite (REG 18%bv 35%nat ltac:(vm_compute; reflexivity)), E35, Z_to_bv_bv_unsigned; reflexivity
    | rewrite (REG 19%bv 36%nat ltac:(vm_compute; reflexivity)), E36, Z_to_bv_bv_unsigned; reflexivity
    | rewrite (REG 20%bv 37%nat ltac:(vm_compute; reflexivity)), E37, Z_to_bv_bv_unsigned; reflexivity
    | rewrite (REG 21%bv 38%nat ltac:(vm_compute; reflexivity)), E38, Z_to_bv_bv_unsigned; reflexivity
    | rewrite (REG 22%bv 39%nat ltac:(vm_compute; reflexivity)), E39, Z_to_bv_bv_unsigned; reflexivity
    | rewrite (REG 23%bv 23%nat ltac:(vm_compute; reflexivity)),
        (ER 23%nat 23%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned;
      exact (proj1 (proj2 (proj2 HRK)))
    | rewrite (REG 24%bv 24%nat ltac:(vm_compute; reflexivity)),
        (ER 24%nat 24%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned;
      exact (proj1 (proj2 (proj2 (proj2 HRK))))
    | rewrite (REG 25%bv 25%nat ltac:(vm_compute; reflexivity)),
        (ER 25%nat 25%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned;
      exact (proj1 (proj2 (proj2 (proj2 (proj2 HRK)))))
    | rewrite (REG 26%bv 26%nat ltac:(vm_compute; reflexivity)),
        (ER 26%nat 26%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned;
      exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HRK))))))
    | rewrite (REG 27%bv 27%nat ltac:(vm_compute; reflexivity)),
        (ER 27%nat 27%bv ltac:(lia) eq_refl), Z_to_bv_bv_unsigned;
      exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HRK)))))) ] |];
  assert (R1 : getr (ms_regs msc) 1 = getr (c_regs cx) 1);
  [ rewrite (REG 1%bv 32%nat ltac:(vm_compute; reflexivity)), E32; apply Z_to_bv_bv_unsigned |];
  eapply (RET (c_W cx) _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  intros mat'
end.
(* the Post: LinkWalkSide.apost_leaf_AR (the heap-block shadow from AR at both ends of the journal) *)
cbn [ms_regs ms_mem]. rewrite R1, Hraw. unfold at_post.
eapply (apost_leaf_AR SK SEGS B LAWS pa_segs_low ATTR_TEXT_AK 0 (c_E cx)
  (c_G cx) (c_XO cx) (c_OUT cx) (c_STK cx) (c_sp0 cx) (c_FP cx) (c_ly cx) (c_S cx) (c_W0 cx) (c_mem0 cx)
  (c_md0 cx) (c_own cx) (c_lyc cx) (c_Sc cx) (c_W cx) (c_memc cx) (c_mdc cx) (c_k cx) (c_regs cx));
[ exact HJ0
| apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low); exact HJ
| lia | exact Hwlo | rewrite HAK; lia
| repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact HFDS
| repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact HFS
| exact HARP | exact UN | exact HPG | exact HPW | ].
cbv beta.
split; [symmetry; apply at_set_fs_self|].
split; [apply Permutation_refl|].
(* the nl_w Post *)
intros bs Hbs.
destruct (fields_of_anlw SEGS (c_mem cx) (c_w cx) (c_bs cx) HNLW HWF) as (VN0 & _ & (Hn0a & Hn0b) & _).
exact (nlw_post_of_fields SEGS (c_mem cx) (rdW (c_W cx) _) (c_w cx) (c_n0 cx) n f
         VN0 Hn0a HN0 HFIN bs Hbs).
Qed.



(* ==========================================================================
   THE STATE AT A JOIN (+0xec, +0x170, +0x1d4), shared by phases 1, 2 and 3
   ========================================================================== *)

(* atoms 32 = the shadow base, 33 = n, 34 = full, 35 = w + n (the alias atom of the arms that store into w->b),
   40..47 = the eight saved words *)
Definition at_extra (cx : atcx) (n f : Z) : list word :=
  [w64 SHADOW_OFF; w64 n; w64 f; w64 (c_w cx + n); w64 0; w64 0; w64 0; w64 0;
   getr (c_regs cx) 1; getr (c_regs cx) 8; getr (c_regs cx) 9; getr (c_regs cx) 18;
   getr (c_regs cx) 19; getr (c_regs cx) 20; getr (c_regs cx) 21; getr (c_regs cx) 22].

Definition at_fr : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 64 0 0
    [YP09.mkChunk 0x38 (CVal 8 (SOff 40 0)); YP09.mkChunk 0x30 (CVal 8 (SOff 41 0));
     YP09.mkChunk 0x28 (CVal 8 (SOff 42 0)); YP09.mkChunk 0x20 (CVal 8 (SOff 43 0));
     YP09.mkChunk 0x18 (CVal 8 (SOff 44 0)); YP09.mkChunk 0x10 (CVal 8 (SOff 45 0));
     YP09.mkChunk 0x8 (CVal 8 (SOff 46 0)); YP09.mkChunk 0 (CVal 8 (SOff 47 0))].
Definition at_fl : YP09.region :=
  YP09.mkRegion (Some 9%nat) 4096 4112 4096 4112
    [YP09.mkChunk 4096 (CVal 8 (SOff 33 0)); YP09.mkChunk 4104 (CVal 4 (SOff 34 0))].
Definition at_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms 8%bv (SOff 9 4096)) 21%bv at_sh5) 22%bv (SOff 32 0).
Definition at_facts : facts :=
  mkFacts [(9%nat, mkAF 0 (2 ^ 47 - 4113) 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 4096 0); (34%nat, mkAF 0 1 0)] [] [].
Definition at_ssJ (pc : Z) : sstate := mkSS pc at_regs [at_fr; at_fl] None at_facts.
Definition at_Bx : sv := SOff 32 0.
Definition at_SH : list shent := [mkSHE 9 4096 4112].

(* a register the symbolic file names by a value the machine already has *)
Lemma at_regs_ok_set : forall E sr regs (rd : bv 5) e,
  regs_ok E sr regs -> bv_eqb rd 0 = false -> sv_denot E e = getr regs rd ->
  regs_ok E (sr_set sr rd e) regs.
Proof.
  intros E sr regs rd e H H0 He r. destruct (bv_eqb r rd) eqn:Heq.
  - unfold bv_eqb in Heq. apply Z.eqb_eq, bv_eq in Heq. subst r. rewrite sr_get_set_same by exact H0.
    rewrite He. reflexivity.
  - rewrite sr_get_set_other by (intros ->; rewrite bv_eqb_refl in Heq; discriminate). apply H.
Qed.

(* the struct is apart from the shadow band, in both arms of amem_range *)
Lemma at_w_band : forall cx, amem_range (c_w cx) NW_SIZE ->
  forall x, c_w cx <= x < c_w cx + NW_SIZE -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44).
Proof.
  intros cx HR x Hx.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, NW_SIZE, SHADOW_OFF in *. lia.
Qed.

(* the shadow bytes of the struct are not bytes the call writes, so the Pre's range_addressable and
   shadow_hull_vis hold at every later state the kept clause describes *)
Lemma at_ra_keep : forall cx m3,
  amem_range (c_w cx) NW_SIZE -> 0 <= c_w cx ->
  alloc_ceiling + ATTR_TEXT_AK <= c_sp cx ->
  range_addressable (ard SEGS (c_mem cx)) SHADOW_OFF (c_w cx) NW_SIZE ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp cx - ATTR_TEXT_AK <= a < c_sp cx) -> ~ c_E cx a ->
     aview SEGS (w_H (c_W cx)) m3 a = aview SEGS (w_H (c_W cx)) (c_memc cx) a) ->
  range_addressable (ard SEGS (rdW (c_W cx) m3)) SHADOW_OFF (c_w cx) NW_SIZE.
Proof.
  intros cx m3 HR Hw0 Hsp HRA UN.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold c_mem in HRA. rewrite ard_aview. rewrite ard_aview in HRA.
  apply (ra_shadow_eq (aview SEGS (w_H (c_W cx)) (c_memc cx))); [exact HRA|].
  intros x Hx.
  assert (Hband : SHADOW_OFF <= shadow_addr x < SHADOW_OFF + 2 ^ 44).
  { unfold shadow_addr, SHADOW_OFF.
    assert (Hx2 : 0 <= x < 2 ^ 47)
      by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, NW_SIZE, SHADOW_OFF in *; lia).
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
  apply UN.
  - unfold SHADOW_OFF in *; lia.
  - unfold ATTR_TEXT_AK, ATTR_TEXT_AFRAME, ESTACK, SHADOW_OFF in *; lia.
  - intros HE. exact (at_E_band cx HR _ HE Hband).
Qed.

(* THE ENTRY STATE AT A JOIN. Every phase starts here: from the invariant's Props it builds the engine's
   st_ok_pi and sh_ok at `at_ssJ pc`, exactly as a Theorem Labs lane's cl_entry does at a function's entry. *)
Lemma at_entry_J : forall cx pc len n f ms3,
  at_base cx -> at_shape cx pc ms3 -> at_live cx len (ms_regs ms3) ->
  nlw_fields SEGS (rdW (c_W cx) (ms_mem ms3)) (c_w cx) n f ->
  at_kept cx (ms_mem ms3) ->
  bv_unsigned (ew (Eimg (Ereg (ms_regs ms3) (at_extra cx n f))) 2%nat) = c_sp cx - AT_FRAME
  /\ bv_unsigned (ew (Eimg (Ereg (ms_regs ms3) (at_extra cx n f))) 9%nat) = c_w cx
  /\ regs_ok (Eimg (Ereg (ms_regs ms3) (at_extra cx n f))) at_regs (ms_regs ms3)
  /\ st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) (at_extra cx n f))) (at_ssJ pc)
       (restrict (w_H (c_W cx)) ms3)
  /\ sh_ok SEGS at_Bx at_SH (Eimg (Ereg (ms_regs ms3) (at_extra cx n f)))
       (mrestrict (w_H (c_W cx)) (ms_mem ms3)).
Proof.
intros cx pc len n f ms3 HB HSHAPE HLIVE HFIELDS HKEPT.
destruct HB as (HPRE & HRD & HNLW & HWF & Hs0 & HSTR & HSLEN & HSLACK & HAP & HAPF1 & HAPF2 &
  HMR1 & HRA1 & HHV1 & HMR2 & HRA2 & HHV2).
destruct HPRE as (HJ0 & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside &
  Hajw & Hro).
destruct HSHAPE as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc & Hsp & HRK & HSAV).
destruct HLIVE as (L8 & L9 & L18 & L19 & L20 & L21 & L22).
pose proof HFIELDS as (Hw0 & Hwl & HPRES & HVN & HVF & (Hn0 & Hn1) & (Hf0 & Hf1)).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (Hceil : alloc_ceiling <= c_sp0 cx - c_STK cx) by (eapply (aj_stk_ceiling SK SEGS B); exact HJ0).
assert (HSPlo : alloc_ceiling + ATTR_TEXT_AK <= c_sp cx) by (unfold c_sp in *; lia).
assert (HSPhi : c_sp cx < 2 ^ 64)
  by (unfold c_sp, spZ; pose proof (u64_range (getr (c_regs cx) 2)); lia).
assert (HAK : ATTR_TEXT_AK = 4160) by reflexivity.
assert (HFRv : AT_FRAME = 64) by reflexivity.
set (E := Eimg (Ereg (ms_regs ms3) (at_extra cx n f))).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg (ms_regs ms3) (at_extra cx n f)) m)
  by (intros m Hm; subst E; apply Eimg_low; exact Hm).
assert (ER : forall (j : nat) (r : bv 5), (j < 32)%nat -> Z.of_nat j = bv_unsigned r ->
          ew E j = getr (ms_regs ms3) r)
  by (intros j r Hj Hr; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ j r Hr)).
assert (EX : forall j, (j < 16)%nat -> ew E (32 + j)%nat = nth j (at_extra cx n f) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 8%nat ltac:(lia)) as E40. pose proof (EX 9%nat ltac:(lia)) as E41.
pose proof (EX 10%nat ltac:(lia)) as E42. pose proof (EX 11%nat ltac:(lia)) as E43.
pose proof (EX 12%nat ltac:(lia)) as E44. pose proof (EX 13%nat ltac:(lia)) as E45.
pose proof (EX 14%nat ltac:(lia)) as E46. pose proof (EX 15%nat ltac:(lia)) as E47.
cbn [at_extra nth Nat.add] in E32, E33, E34, E40, E41, E42, E43, E44, E45, E46, E47.
pose proof (ER 2%nat 2%bv ltac:(lia) eq_refl) as E2.
pose proof (ER 9%nat 9%bv ltac:(lia) eq_refl) as E9.
assert (U2 : bv_unsigned (ew E 2%nat) = c_sp cx - AT_FRAME) by (rewrite E2; exact Hsp).
assert (U9 : bv_unsigned (ew E 9%nat) = c_w cx)
  by (rewrite E9, L9; unfold w64; apply unsigned_lit_small; unfold NW_SIZE in *; lia).
assert (U32 : bv_unsigned (ew E 32%nat) = SHADOW_OFF)
  by (rewrite E32; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33%nat) = n)
  by (rewrite E33; unfold w64; apply unsigned_lit_small; unfold NL_CHUNK_MAX in *; lia).
assert (U34 : bv_unsigned (ew E 34%nat) = f)
  by (rewrite E34; unfold w64; apply unsigned_lit_small; lia).
destruct HSAV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
assert (CHK : forall (od : Z) (m : nat) (x : word),
  ew E m = x -> val_mem SEGS (rdW (c_W cx) (ms_mem ms3)) (c_sp cx - AT_FRAME + od) 8 (bv_unsigned x) ->
  YP09.chunk_ok SEGS E (mrestrict (w_H (c_W cx)) (ms_mem ms3)) (c_sp cx - AT_FRAME)
    (YP09.mkChunk od (CVal 8 (SOff m 0)))).
{ intros od m x Hm HV.
  apply (chunk_ok_val SEGS E _ (c_sp cx - AT_FRAME) od 8%N (SOff m 0) (bv_unsigned x)).
  - cbn [sv_denot]. rewrite Z.add_0_r, Hm, Z_to_bv_bv_unsigned. reflexivity.
  - cbn [Z.of_N]. pose proof (u64_range x). lia.
  - cbn [Z.of_N]. lia.
  - exact HV. }
assert (HREGS : regs_ok E at_regs (ms_regs ms3)).
{ unfold at_regs. apply at_regs_ok_set; [apply at_regs_ok_set; [apply at_regs_ok_set | | ] | | ].
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + cbn [sv_denot]. rewrite E9, L9. unfold w64, NW_N, NW_SIZE in *.
    rewrite unsigned_lit_small by lia. exact (eq_sym L8).
  + vm_compute. reflexivity.
  + rewrite (at_sh5_regs E (ms_regs ms3) (c_w cx) E9 ltac:(rewrite E32, L22; reflexivity)
               L9 Hw0 Hwl L8). exact (eq_sym L21).
  + vm_compute. reflexivity.
  + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. exact (eq_sym L22). }
split; [exact U2|]. split; [exact U9|]. split; [exact HREGS|].
split.
{ rewrite (at_ms_shape ms3 (BASE + pc) Hpc Hrv Hsvc Hrom Hfr Hfc).
  rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact HREGS.
  - vm_compute. reflexivity.
  - (* the two regions *)
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold at_fr, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U2.
      split; [unfold AT_FRAME in *; lia|]. split; [unfold AT_FRAME in *; lia|].
      split; [intros o Ho; lia|].
      cbn [ms_mem restrict mkst].
      repeat (apply Forall_cons); [| | | | | | | | apply Forall_nil].
      * apply (CHK 0x38 40%nat (getr (c_regs cx) 1) E40).
        replace (c_sp cx - AT_FRAME + 0x38) with (c_sp cx - 8) by (unfold AT_FRAME; lia). exact V1.
      * apply (CHK 0x30 41%nat (getr (c_regs cx) 8) E41).
        replace (c_sp cx - AT_FRAME + 0x30) with (c_sp cx - 16) by (unfold AT_FRAME; lia). exact V2.
      * apply (CHK 0x28 42%nat (getr (c_regs cx) 9) E42).
        replace (c_sp cx - AT_FRAME + 0x28) with (c_sp cx - 24) by (unfold AT_FRAME; lia). exact V3.
      * apply (CHK 0x20 43%nat (getr (c_regs cx) 18) E43).
        replace (c_sp cx - AT_FRAME + 0x20) with (c_sp cx - 32) by (unfold AT_FRAME; lia). exact V4.
      * apply (CHK 0x18 44%nat (getr (c_regs cx) 19) E44).
        replace (c_sp cx - AT_FRAME + 0x18) with (c_sp cx - 40) by (unfold AT_FRAME; lia). exact V5.
      * apply (CHK 0x10 45%nat (getr (c_regs cx) 20) E45).
        replace (c_sp cx - AT_FRAME + 0x10) with (c_sp cx - 48) by (unfold AT_FRAME; lia). exact V6.
      * apply (CHK 0x8 46%nat (getr (c_regs cx) 21) E46).
        replace (c_sp cx - AT_FRAME + 0x8) with (c_sp cx - 56) by (unfold AT_FRAME; lia). exact V7.
      * apply (CHK 0 47%nat (getr (c_regs cx) 22) E47).
        replace (c_sp cx - AT_FRAME + 0) with (c_sp cx - 64) by (unfold AT_FRAME; lia). exact V8.
    + unfold at_fl, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9.
      split; [unfold NW_SIZE in *; lia|]. split; [unfold NW_SIZE in *; lia|].
      split.
      { intros o Ho. cbn [ms_mem restrict mkst].
        destruct (HPRES (o) ltac:(unfold NW_SIZE in *; lia)) as (_ & Hwb). exact Hwb. }
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS E _ (c_w cx) 4096 8%N (SOff 33 0) n);
          [ cbn [sv_denot]; rewrite Z.add_0_r, E33, Z_to_bv_bv_unsigned; reflexivity
          | cbn [Z.of_N]; unfold NL_CHUNK_MAX in *; lia | cbn [Z.of_N]; lia |].
        cbn [ms_mem restrict mkst]. unfold NW_N in HVN. exact HVN.
      * apply (chunk_ok_val SEGS E _ (c_w cx) 4104 4%N (SOff 34 0) f);
          [ cbn [sv_denot]; rewrite Z.add_0_r, E34, Z_to_bv_bv_unsigned; reflexivity
          | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
        cbn [ms_mem restrict mkst]. unfold NW_FULL in HVF. exact HVF.
  - (* the two regions are disjoint: apart_frame puts the struct outside [sp - K, sp) *)
    apply pairwise_disjoint_of_extents.
    unfold at_fr, at_fl, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U2, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold apart_frame, ATTR_TEXT_AK, ATTR_TEXT_AFRAME, ESTACK, AT_FRAME, NW_SIZE, c_sp in *.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  - (* the facts *)
    split; [|split; [exact I | exact I]].
    cbn [at_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U32, U33, U34. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, NW_SIZE, NL_CHUNK_MAX, SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
(* the shadow entry: the Pre's range_addressable on [w + 4096, w + 4112), and the struct misses the band *)
apply Forall_cons; [|apply Forall_nil].
unfold shent_ok, at_SH, at_Bx. cbn [she_m she_lo she_hi].
rewrite (U_atom E 32%nat SHADOW_OFF ltac:(rewrite E32; reflexivity) ltac:(unfold SHADOW_OFF; lia)).
rewrite (U_atom E 9%nat (c_w cx) ltac:(rewrite E9, L9; reflexivity) ltac:(unfold NW_SIZE in *; lia)).
split.
- rewrite <- (aview_rd_of SEGS).
  apply (range_addressable_sub (aview SEGS (w_H (c_W cx)) (ms_mem ms3)) SHADOW_OFF (c_w cx) NW_SIZE);
    [| lia | unfold NW_SIZE; lia].
  rewrite <- ard_aview.
  exact (at_ra_keep cx (ms_mem ms3) HMR1 Hw0 HSPlo HRA1 (proj1 HKEPT)).
- unfold app_apart. cbn [she_m she_lo she_hi].
  change (Z.min 4096 4112) with 4096. change (Z.max 4096 4112) with 4112.
  rewrite (U_atom E 32%nat SHADOW_OFF ltac:(rewrite E32; reflexivity) ltac:(unfold SHADOW_OFF; lia)).
  rewrite (U_atom E 9%nat (c_w cx) ltac:(rewrite E9, L9; reflexivity)
             ltac:(unfold NW_SIZE in *; lia)).
  intros a Ha. apply (at_w_band cx HMR1 a). unfold NW_SIZE. lia.
Qed.

(* ==========================================================================
   WHAT A PHASE DOES AT ITS END: one step as the kept clause sees it, the shadow entries, the registers, and back
   to the invariant
   ========================================================================== *)

Lemma at_w_range : forall cx, 0 <= c_w cx < 2 ^ 64.
Proof. intros cx. unfold c_w, aarg, argZ. apply u64_range. Qed.

(* a byte of the struct is a byte of the write set *)
Lemma at_E_in : forall cx a, c_w cx <= a < c_w cx + NW_SIZE -> c_E cx a.
Proof. intros cx a Ha. exists (c_w cx, c_w cx + NW_SIZE). split; [left; reflexivity | exact Ha]. Qed.

Lemma at_s_range : forall cx, 0 <= c_s cx < 2 ^ 64.
Proof. intros cx. unfold c_s, aarg, argZ. apply u64_range. Qed.

(* a byte of the write set is a byte of the struct *)
Lemma at_E_inv : forall cx a, c_E cx a -> c_w cx <= a < c_w cx + NW_SIZE.
Proof.
  intros cx a (r & Hin & Hx). unfold c_Wr, attr_text_awr in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[]]. cbn [fst snd] in Hx. exact Hx.
Qed.

(* the string's bytes and its NUL are visible at the call *)
Lemma at_str_vis : forall cx a, at_base cx -> c_s cx <= a < c_s cx + c_slen cx + 1 ->
  aview SEGS (w_H (c_W cx)) (c_memc cx) a <> None.
Proof.
  intros cx a HB Ha.
  destruct HB as (_ & _ & _ & _ & _ & HSTR & _).
  destruct HSTR as ((_ & _ & Hb) & _).
  unfold aview. unfold c_mem in Hb. unfold c_slen in Ha.
  replace a with (c_s cx + Z.of_nat (Z.to_nat (a - c_s cx))) by lia.
  rewrite (Hb (Z.to_nat (a - c_s cx)) ltac:(rewrite length_app; cbn [length]; lia)).
  destruct (nth_error (c_str cx ++ [zb 0]) (Z.to_nat (a - c_s cx))) eqn:Eb; [discriminate|].
  apply nth_error_None in Eb. rewrite length_app in Eb. cbn [length] in Eb. lia.
Qed.

(* ... and the kept clause keeps them: they are off the frame and off the struct *)
Lemma at_str_kept : forall cx m3 a, at_base cx -> at_kept cx m3 -> c_s cx <= a < c_s cx + c_slen cx + 1 ->
  aview SEGS (w_H (c_W cx)) m3 a = aview SEGS (w_H (c_W cx)) (c_memc cx) a.
Proof.
  intros cx m3 a HB HK Ha.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HAP & _ & HAPF2 & _ & _ & _ & HMR2 & _).
  pose proof (at_s_range cx) as Rs.
  apply (proj1 HK).
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HMR2. lia.
  - unfold apart_frame, c_sp in *. lia.
  - intros He. apply at_E_inv in He. unfold apart in HAP. lia.
Qed.

(* One step of the walk (a run of the engine, or a runtime call): every byte off the callee window
   [sp - K, sp - 64) and off the write set keeps its view, and presence grows. The frame [sp - 64, sp) is NOT
   excepted: no step writes it after the prologue. *)
Definition at_step (cx : atcx) (m1 m2 : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp cx - ATTR_TEXT_AK <= a < c_sp cx - AT_FRAME) -> ~ c_E cx a ->
     aview SEGS (w_H (c_W cx)) m2 a = aview SEGS (w_H (c_W cx)) m1 a) /\
  (forall a, apresent (w_H (c_W cx)) m1 a -> apresent (w_H (c_W cx)) m2 a).

Lemma at_step_refl : forall cx m, at_step cx m m.
Proof. intros cx m. split; intros; [reflexivity | assumption]. Qed.

Lemma at_step_trans : forall cx m1 m2 m3, at_step cx m1 m2 -> at_step cx m2 m3 -> at_step cx m1 m3.
Proof.
  intros cx m1 m2 m3 (U1 & P1) (U2 & P2). split.
  - intros a Ha Hw He. rewrite (U2 a Ha Hw He). exact (U1 a Ha Hw He).
  - intros a Hp. exact (P2 a (P1 a Hp)).
Qed.

(* a run of the engine whose written windows Zs lie in the struct *)
Lemma at_step_run : forall cx m1 m2 (Zs : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H (c_W cx)) m2 a = aview SEGS (w_H (c_W cx)) m1 a) ->
  (forall a, Zs a -> c_w cx <= a < c_w cx + NW_SIZE) ->
  mem_grows (rdW (c_W cx) m1) (rdW (c_W cx) m2) ->
  at_step cx m1 m2.
Proof.
  intros cx m1 m2 Zs UN HZ HG. split.
  - intros a Ha Hw He. apply UN; [exact Ha|]. intros Hz. exact (He (at_E_in cx a (HZ a Hz))).
  - intros a Hp. exact (at_apres_grows _ _ _ a HG Hp).
Qed.

(* a runtime call at sp - 64 (window ESTACK) whose destination [d, d + n) lies in the struct *)
Lemma at_step_call : forall cx m1 m2 d n,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (c_sp cx - AT_FRAME - ESTACK <= a < c_sp cx - AT_FRAME) ->
     aview SEGS (w_H (c_W cx)) m2 a = aview SEGS (w_H (c_W cx)) m1 a) ->
  (forall a, apresent (w_H (c_W cx)) m1 a -> apresent (w_H (c_W cx)) m2 a) ->
  c_w cx <= d -> d + n <= c_w cx + NW_SIZE ->
  at_step cx m1 m2.
Proof.
  intros cx m1 m2 d n UN HP Hd Hdn. split; [|exact HP].
  intros a Ha Hw He. apply UN; [exact Ha | |].
  - intros Hda. apply He. apply at_E_in. lia.
  - unfold ATTR_TEXT_AK, ATTR_TEXT_AFRAME, AT_FRAME, ESTACK in *. lia.
Qed.

Lemma at_kept_step : forall cx m1 m2, at_kept cx m1 -> at_step cx m1 m2 -> at_kept cx m2.
Proof.
  intros cx m1 m2 (K1 & K2 & K3) (UN & P). split; [|split].
  - intros a Ha Hw He. rewrite (UN a Ha ltac:(intros Hc; apply Hw; unfold AT_FRAME in Hc; lia) He).
    exact (K1 a Ha Hw He).
  - intros a Ha. exact (P a (K2 a Ha)).
  - intros a Ha. exact (P a (K3 a Ha)).
Qed.

(* A shadow entry [v + lo, v + hi) inside the struct holds at every memory the kept clause describes: no step
   writes a shadow byte of the struct (at_ra_keep), and the struct misses the shadow band (at_w_band). *)
Lemma at_she_ok : forall cx m3 E (k : nat) v lo hi,
  at_base cx -> at_kept cx m3 ->
  ew E k = w64 v -> ew E 32%nat = w64 SHADOW_OFF ->
  c_w cx <= v + lo -> v + hi <= c_w cx + NW_SIZE -> lo < hi -> 0 <= v < 2 ^ 64 ->
  shent_ok SEGS at_Bx E (mrestrict (w_H (c_W cx)) m3) (mkSHE k lo hi).
Proof.
intros cx m3 E k v lo hi HB HK Ek E32 Hl Hh Hlh Hv.
destruct HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMR1 & HRA1 & _).
destruct HPRE as (HJ0 & _ & _ & _ & _ & _ & _ & _ & Hwlo & _).
assert (Hceil : alloc_ceiling <= c_sp0 cx - c_STK cx) by (eapply (aj_stk_ceiling SK SEGS B); exact HJ0).
assert (HSPlo : alloc_ceiling + ATTR_TEXT_AK <= c_sp cx) by (unfold c_sp in *; lia).
pose proof (at_w_range cx) as Hw0.
unfold shent_ok, at_Bx. cbn [she_m she_lo she_hi].
rewrite (U_atom E 32%nat SHADOW_OFF E32 ltac:(unfold SHADOW_OFF; lia)), (U_atom E k v Ek Hv).
split.
- rewrite <- (aview_rd_of SEGS).
  apply (range_addressable_sub (aview SEGS (w_H (c_W cx)) m3) SHADOW_OFF (c_w cx) NW_SIZE); [| lia | lia].
  rewrite <- ard_aview. exact (at_ra_keep cx m3 HMR1 (proj1 Hw0) HSPlo HRA1 (proj1 HK)).
- unfold app_apart. cbn [she_m she_lo she_hi].
  rewrite (U_atom E 32%nat SHADOW_OFF E32 ltac:(unfold SHADOW_OFF; lia)), (U_atom E k v Ek Hv).
  rewrite Z.min_l by lia. rewrite Z.max_r by lia.
  intros a Ha. apply (at_w_band cx HMR1 a). lia.
Qed.

(* the shadow entries of a join *)
Lemma at_shok : forall cx m3 E,
  at_base cx -> at_kept cx m3 -> ew E 9%nat = w64 (c_w cx) -> ew E 32%nat = w64 SHADOW_OFF ->
  sh_ok SEGS at_Bx at_SH E (mrestrict (w_H (c_W cx)) m3).
Proof.
  intros cx m3 E HB HK E9 E32. pose proof (at_w_range cx) as Hw0.
  apply Forall_cons; [|apply Forall_nil].
  apply (at_she_ok cx m3 E 9 (c_w cx) 4096 4112 HB HK E9 E32); unfold NW_SIZE; lia.
Qed.

(* a value a region of the engine's state shows, as a val_mem of the memory *)
Lemma at_val_of_ss : forall E ss (H : word -> bool) msc i (nb : nat) b lo hi wlo whi cs od (w : N) e v,
  st_ok_pi SEGS pa_val E ss (restrict H msc) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some nb) lo hi wlo whi cs) ->
  bv_unsigned (ew E nb) = b -> In (YP09.mkChunk od (CVal w e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS (mrestrict H (ms_mem msc)) (b + od) (N.to_nat w) v.
Proof.
  intros E ss H msc i nb b lo hi wlo whi cs od w e v HS Hi Hb Hc He Hv Hw.
  assert (Hi' : nth_error (ss_mem (abs_ss pa_val ss)) i = Some (YP09.mkRegion (Some nb) lo hi wlo whi cs))
    by (destruct ss; exact Hi).
  pose proof (st_ok_region_nth (segs := SEGS) E (abs_ss pa_val ss) (restrict H msc) i _ HS Hi') as HR.
  cbn [ms_mem restrict] in HR.
  exact (field_of_region (segs := SEGS) E _ nb b cs lo hi wlo whi od w e v HR Hb Hc He Hv Hw).
Qed.

(* the registers of a join state, from the engine's state: each register whose symbolic value is still the one
   at_regs gives it holds the value it held at the join *)
Lemma at_regs_carry : forall cx n f (ms3 : machine_state) E' ss (H : word -> bool) msc (L : list (bv 5)),
  regs_ok (Eimg (Ereg (ms_regs ms3) (at_extra cx n f))) at_regs (ms_regs ms3) ->
  env_agree 48 (Eimg (Ereg (ms_regs ms3) (at_extra cx n f))) E' ->
  st_ok_pi SEGS pa_val E' ss (restrict H msc) ->
  forallb (fun r => sv_eqb (sr_get (ss_regs ss) r) (sr_get at_regs r)) L = true ->
  forall r, In r L -> getr (ms_regs msc) r = getr (ms_regs ms3) r.
Proof.
  intros cx n f ms3 E' ss H msc L HR HA HS HL r Hr.
  pose proof (proj1 (forallb_forall _ _) HL r Hr) as Hq. apply sv_eqb_eq in Hq.
  rewrite (st_ok_pi_restrict_reg H E' ss msc r HS), Hq.
  rewrite (sv_denot_agree 48 _ E' _ HA (sr_get_atoms 48 at_regs r ltac:(vm_compute; reflexivity))).
  symmetry. apply HR.
Qed.

(* the same at a call's state, which the engine gives as an st_ok of the absolute state *)
Lemma at_regs_carry_ok : forall cx n f (ms3 : machine_state) E' ss (H : word -> bool) msc (L : list (bv 5)),
  regs_ok (Eimg (Ereg (ms_regs ms3) (at_extra cx n f))) at_regs (ms_regs ms3) ->
  env_agree 48 (Eimg (Ereg (ms_regs ms3) (at_extra cx n f))) E' ->
  st_ok SEGS E' ss (restrict H msc) ->
  forallb (fun r => sv_eqb (sr_get (ss_regs ss) r) (sr_get at_regs r)) L = true ->
  forall r, In r L -> getr (ms_regs msc) r = getr (ms_regs ms3) r.
Proof.
  intros cx n f ms3 E' ss H msc L HR HA HS HL r Hr.
  pose proof (proj1 (forallb_forall _ _) HL r Hr) as Hq. apply sv_eqb_eq in Hq.
  rewrite (st_ok_restrict_reg SEGS H E' ss msc r HS), Hq.
  rewrite (sv_denot_agree 48 _ E' _ HA (sr_get_atoms 48 at_regs r ltac:(vm_compute; reflexivity))).
  symmetry. apply HR.
Qed.

Definition AT_LIVE_REGS : list (bv 5) := [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition AT_KEPT_REGS : list (bv 5) := [2; 3; 4; 23; 24; 25; 26; 27]%bv.

Ltac at_in := unfold AT_KEPT_REGS, AT_LIVE_REGS; cbn [In]; repeat (first [left; reflexivity | right]).

Lemma at_kept_regs_live : forall r, In r AT_KEPT_REGS -> In r AT_LIVE_REGS.
Proof.
  intros r Hr. unfold AT_KEPT_REGS in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [unfold AT_LIVE_REGS; at_in |]). destruct Hr.
Qed.

Lemma at_shape_of : forall cx pc0 pc ms3 regsX memX,
  at_base cx -> at_shape cx pc0 ms3 ->
  (forall r, In r AT_KEPT_REGS -> getr regsX r = getr (ms_regs ms3) r) ->
  at_step cx (ms_mem ms3) memX ->
  at_shape cx pc (mkst regsX (Z_to_bv 64 (BASE + pc)) memX (seg_rom SEGS)).
Proof.
intros cx pc0 pc ms3 regsX memX HB (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc & Hsp & HRK & HSAV) HR (UN & _).
destruct HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & HAPF1 & _).
destruct HPRE as (HJ0 & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _).
assert (Hceil : alloc_ceiling <= c_sp0 cx - c_STK cx) by (eapply (aj_stk_ceiling SK SEGS B); exact HJ0).
assert (HSPhi : c_sp cx < 2 ^ 64)
  by (unfold c_sp, spZ; pose proof (u64_range (getr (c_regs cx) 2)); lia).
destruct HRK as (K3 & K4 & K23 & K24 & K25 & K26 & K27).
unfold at_shape. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|].
split; [unfold spZ in *; rewrite (HR 2%bv ltac:(at_in)); exact Hsp|].
split.
- unfold at_regs_kept.
  rewrite (HR 3%bv ltac:(at_in)), (HR 4%bv ltac:(at_in)), (HR 23%bv ltac:(at_in)), (HR 24%bv ltac:(at_in)),
    (HR 25%bv ltac:(at_in)), (HR 26%bv ltac:(at_in)), (HR 27%bv ltac:(at_in)).
  exact (conj K3 (conj K4 (conj K23 (conj K24 (conj K25 (conj K26 K27)))))).
- apply (at_saved_keep cx (ms_mem ms3) memX); [|exact HSAV].
  intros a Ha. apply (mbyte_of_aview SEGS (w_H (c_W cx)) (w_H (c_W cx))).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HSPlo : alloc_ceiling + ATTR_TEXT_AK <= c_sp cx) by (unfold c_sp in *; lia).
  assert (HAK : ATTR_TEXT_AK = 4160) by reflexivity.
  apply UN.
  + unfold AT_FRAME in *. lia.
  + unfold AT_FRAME in *. lia.
  + intros He. destruct He as (r & Hin & Hx). unfold c_Wr, attr_text_awr in Hin. cbn [In] in Hin.
    destruct Hin as [<-|[]]. cbn [fst snd] in Hx. fold (c_w cx) in Hx.
    unfold apart_frame, ATTR_TEXT_AK, ATTR_TEXT_AFRAME, ESTACK, AT_FRAME, NW_SIZE, c_sp in *. lia.
Qed.

Lemma at_live_of : forall cx len0 len regs3 regsX,
  at_live cx len0 regs3 ->
  (forall r, In r AT_LIVE_REGS -> getr regsX r = getr regs3 r) ->
  getr regsX 19 = w64 len -> at_live cx len regsX.
Proof.
  intros cx len0 len regs3 regsX (L8 & L9 & L18 & L19 & L20 & L21 & L22) HR H19.
  unfold at_live.
  rewrite (HR 8%bv ltac:(at_in)), (HR 9%bv ltac:(at_in)), (HR 18%bv ltac:(at_in)), (HR 20%bv ltac:(at_in)),
    (HR 21%bv ltac:(at_in)), (HR 22%bv ltac:(at_in)).
  exact (conj L8 (conj L9 (conj L18 (conj H19 (conj L20 (conj L21 L22)))))).
Qed.

Lemma at_fields_of : forall cx m3 mX n0 f0 n f,
  nlw_fields SEGS (rdW (c_W cx) m3) (c_w cx) n0 f0 ->
  at_step cx m3 mX ->
  val_mem SEGS (rdW (c_W cx) mX) (c_w cx + NW_N) 8 n ->
  val_mem SEGS (rdW (c_W cx) mX) (c_w cx + NW_FULL) 4 f ->
  0 <= n <= NL_CHUNK_MAX -> 0 <= f <= 1 ->
  nlw_fields SEGS (rdW (c_W cx) mX) (c_w cx) n f.
Proof.
  intros cx m3 mX n0 f0 n f (Hw0 & Hwl & HP & _) (_ & PG) HVN HVF Hn Hf.
  split; [exact Hw0|]. split; [exact Hwl|].
  split; [|split; [exact HVN | split; [exact HVF | split; [exact Hn | exact Hf]]]].
  intros i Hi. destruct (HP i Hi) as ((b & Hb) & Hw). split.
  - exact (lw_mbyte_some_kept SEGS (w_H (c_W cx)) m3 mX _ b PG Hb).
  - exact (writable_kept (segs := SEGS) (w_H (c_W cx)) m3 mX _ (PG _) Hw).
Qed.

(* BACK TO THE INVARIANT at a join +0xec, +0x170 or +0x1d4 *)
Lemma at_inv_of : forall cx pc0 len0 n0 f0 ms3 pc len n f regsX memX mdX,
  at_base cx ->
  at_shape cx pc0 ms3 -> at_live cx len0 (ms_regs ms3) -> at_kept cx (ms_mem ms3) ->
  nlw_fields SEGS (rdW (c_W cx) (ms_mem ms3)) (c_w cx) n0 f0 ->
  (forall r, In r AT_LIVE_REGS -> getr regsX r = getr (ms_regs ms3) r) ->
  getr regsX 19 = w64 len ->
  at_step cx (ms_mem ms3) memX ->
  ajournal_gx SEGS B (c_G cx) (c_XO cx) (c_OUT cx) (c_STK cx) (c_sp0 cx) (c_FP cx)
    (c_ly cx) (c_S cx) (c_W0 cx) (c_mem0 cx) (c_md0 cx) (c_own cx)
    (c_lyc cx) (c_Sc cx) (c_W cx) memX mdX (c_k cx) ->
  m_fds mdX = m_fds (c_mdc cx) -> m_fs mdX = m_fs (c_mdc cx) ->
  val_mem SEGS (rdW (c_W cx) memX) (c_w cx + NW_N) 8 n ->
  val_mem SEGS (rdW (c_W cx) memX) (c_w cx + NW_FULL) 4 f ->
  0 <= n <= NL_CHUNK_MAX -> 0 <= f <= 1 -> c_n0 cx <= n -> 0 <= len <= c_slen cx + 1 ->
  at_inv cx pc len n f (mkst regsX (Z_to_bv 64 (BASE + pc)) memX (seg_rom SEGS)) mdX.
Proof.
  intros cx pc0 len0 n0 f0 ms3 pc len n f regsX memX mdX HB HSH HLV HK HF HR H19 HST HJ HFD HFS HVN HVF
    Hn Hf Hn0 Hlen.
  unfold at_inv. cbn [ms_regs ms_mem mkst].
  split; [exact (at_shape_of cx pc0 pc ms3 regsX memX HB HSH
                   (fun r Hr => HR r (at_kept_regs_live r Hr)) HST)|].
  split; [exact (at_live_of cx len0 len (ms_regs ms3) regsX HLV HR H19)|].
  split; [exact HJ|]. split; [exact HFD|]. split; [exact HFS|].
  split; [exact (at_fields_of cx (ms_mem ms3) memX n0 f0 n f HF HST HVN HVF Hn Hf)|].
  split; [exact Hn0|]. split; [lia|]. split; [lia|].
  exact (at_kept_step cx (ms_mem ms3) memX HK HST).
Qed.

(* BACK TO THE INVARIANT at the epilogue's join +0x244 *)
Lemma at_inv4_of : forall cx pc0 n0 f0 ms3 n f regsX memX mdX,
  at_base cx ->
  at_shape cx pc0 ms3 -> at_kept cx (ms_mem ms3) ->
  nlw_fields SEGS (rdW (c_W cx) (ms_mem ms3)) (c_w cx) n0 f0 ->
  (forall r, In r AT_KEPT_REGS -> getr regsX r = getr (ms_regs ms3) r) ->
  at_step cx (ms_mem ms3) memX ->
  ajournal_gx SEGS B (c_G cx) (c_XO cx) (c_OUT cx) (c_STK cx) (c_sp0 cx) (c_FP cx)
    (c_ly cx) (c_S cx) (c_W0 cx) (c_mem0 cx) (c_md0 cx) (c_own cx)
    (c_lyc cx) (c_Sc cx) (c_W cx) memX mdX (c_k cx) ->
  m_fds mdX = m_fds (c_mdc cx) -> m_fs mdX = m_fs (c_mdc cx) ->
  val_mem SEGS (rdW (c_W cx) memX) (c_w cx + NW_N) 8 n ->
  val_mem SEGS (rdW (c_W cx) memX) (c_w cx + NW_FULL) 4 f ->
  0 <= n <= NL_CHUNK_MAX -> 0 <= f <= 1 -> c_n0 cx <= n ->
  at_inv4 cx n f (mkst regsX (Z_to_bv 64 (BASE + AT_J4)) memX (seg_rom SEGS)) mdX.
Proof.
  intros cx pc0 n0 f0 ms3 n f regsX memX mdX HB HSH HK HF HR HST HJ HFD HFS HVN HVF Hn Hf Hn0.
  unfold at_inv4. cbn [ms_regs ms_mem mkst].
  split; [exact (at_shape_of cx pc0 AT_J4 ms3 regsX memX HB HSH HR HST)|].
  split; [exact HJ|]. split; [exact HFD|]. split; [exact HFS|].
  split; [exact (at_fields_of cx (ms_mem ms3) memX n0 f0 n f HF HST HVN HVF Hn Hf)|].
  split; [exact Hn0|].
  exact (at_kept_step cx (ms_mem ms3) memX HK HST).
Qed.

(* ==========================================================================
   The shadow facts of the Pre at a later memory, on any range off the shadow band
   ========================================================================== *)

Lemma at_band_of : forall x n y, amem_range x n -> 0 <= x -> x <= y < x + n ->
  SHADOW_OFF <= shadow_addr y < SHADOW_OFF + 2 ^ 44.
Proof.
  intros x n y HR Hx Hy. unfold shadow_addr.
  assert (Hy2 : 0 <= y < 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *; lia).
  pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound y 8 (2 ^ 44) ltac:(lia) ltac:(lia)). unfold SHADOW_OFF in *. lia.
Qed.

(* a byte of the shadow band is one the kept clause keeps *)
Lemma at_band_kept : forall cx m3 s,
  at_base cx -> at_kept cx m3 -> SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 ->
  aview SEGS (w_H (c_W cx)) m3 s = aview SEGS (w_H (c_W cx)) (c_memc cx) s.
Proof.
  intros cx m3 s HB HK Hs.
  destruct HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMR1 & _).
  destruct HPRE as (HJ0 & _ & _ & _ & _ & _ & _ & _ & Hwlo & _).
  assert (Hceil : alloc_ceiling <= c_sp0 cx - c_STK cx) by (eapply (aj_stk_ceiling SK SEGS B); exact HJ0).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  apply (proj1 HK).
  - unfold SHADOW_OFF in *. lia.
  - unfold c_sp, ATTR_TEXT_AK, ATTR_TEXT_AFRAME, ESTACK, SHADOW_OFF in *. lia.
  - intros HE. exact (at_E_band cx HMR1 s HE Hs).
Qed.

Lemma at_ra_keep2 : forall cx m3 x n,
  at_base cx -> at_kept cx m3 -> amem_range x n -> 0 <= x ->
  range_addressable (ard SEGS (c_mem cx)) SHADOW_OFF x n ->
  range_addressable (aview SEGS (w_H (c_W cx)) m3) SHADOW_OFF x n.
Proof.
  intros cx m3 x n HB HK HR Hx HRA.
  unfold c_mem in HRA. rewrite ard_aview in HRA.
  apply (ra_shadow_eq (aview SEGS (w_H (c_W cx)) (c_memc cx))); [exact HRA|].
  intros y Hy. exact (at_band_kept cx m3 _ HB HK (at_band_of x n y HR Hx Hy)).
Qed.

Lemma at_hull_keep : forall cx m3 x n,
  at_base cx -> at_kept cx m3 -> amem_range x n -> 0 <= x -> 0 < n ->
  shadow_hull_vis (ard SEGS (c_mem cx)) x n ->
  shadow_hull_vis (aview SEGS (w_H (c_W cx)) m3) x n.
Proof.
  intros cx m3 x n HB HK HR Hx Hn HHV s Hs.
  unfold c_mem in HHV. rewrite ard_aview in HHV.
  rewrite (at_band_kept cx m3 s HB HK); [exact (HHV s Hs)|].
  pose proof (at_band_of x n x HR Hx ltac:(lia)) as B1.
  pose proof (at_band_of x n (x + n - 1) HR Hx ltac:(lia)) as B2.
  unfold shadow_addr, SHADOW_OFF in *. lia.
Qed.

Lemma at_hull_sub : forall (rd : reader) x n y k,
  shadow_hull_vis rd x n -> 0 <= x -> x <= y -> y + k <= x + n -> 0 < k -> shadow_hull_vis rd y k.
Proof.
  intros rd x n y k H Hx Hy Hyk Hk s Hs. apply H. unfold shadow_addr in *.
  assert (E1 : x / 8 <= y / 8) by (apply Z.div_le_mono; lia).
  assert (E2 : (y + k - 1) / 8 <= (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (E3 : (SHADOW_OFF + x / 8) / 8 <= (SHADOW_OFF + y / 8) / 8) by (apply Z.div_le_mono; lia).
  assert (E4 : (SHADOW_OFF + (y + k - 1) / 8) / 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8)
    by (apply Z.div_le_mono; lia).
  lia.
Qed.

(* ==========================================================================
   The values of the engine's symbolic expressions
   ========================================================================== *)

Lemma at_denot : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. subst v. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma at_U_off : forall E (k : nat) c v r,
  ew E k = w64 v -> 0 <= v < 2 ^ 64 -> v + c = r -> 0 <= r < 2 ^ 64 -> U E (SOff k c) = r.
Proof.
  intros E k c v r Hk Hv Hr Hr2. rewrite U_SOff, Hk. unfold w64. rewrite unsigned_lit_small by lia.
  subst r. apply zcanon_id. unfold M64. lia.
Qed.

Lemma at_U_atom0 : forall E (k : nat) v, ew E k = w64 v -> 0 <= v < 2 ^ 64 -> U E (SOff k 0) = v.
Proof. intros E k v Hk Hv. apply U_atom; [exact Hk | exact Hv]. Qed.

Lemma at_U_lit : forall E z r, z = r -> 0 <= r < 2 ^ 64 -> U E (SLit z) = r.
Proof. intros E z r Hz Hr. subst. apply U_lit. lia. Qed.

Lemma at_U_add : forall E a b x y r,
  U E a = x -> U E b = y -> x + y = r -> 0 <= r < 2 ^ 64 -> U E (SAlu ALU_ADD a b) = r.
Proof. intros E a b x y r Ha Hb Hr Hr2. rewrite U_SAlu. cbn [zalu_raw]. subst. apply zcanon_id. unfold M64. lia. Qed.

Lemma at_U_sub : forall E a b x y r,
  U E a = x -> U E b = y -> x - y = r -> 0 <= r < 2 ^ 64 -> U E (SAlu ALU_SUB a b) = r.
Proof. intros E a b x y r Ha Hb Hr Hr2. rewrite U_SAlu. cbn [zalu_raw]. subst. apply zcanon_id. unfold M64. lia. Qed.

Lemma at_U_srl : forall E a x (k : Z) r,
  U E a = x -> 0 <= k < 64 -> x / 2 ^ k = r -> U E (SAlu ALU_SRL a (SLit k)) = r.
Proof.
  intros E a x k r Ha Hk Hr. rewrite U_SAlu, (U_lit E k) by lia. cbn [zalu_raw].
  change 63 with (Z.ones 6). rewrite (Z.land_ones k 6) by lia. rewrite (Z.mod_small k (2 ^ 6)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. pose proof (U_range E a) as R. unfold M64 in R.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)) as Hp.
  pose proof (Z.div_pos (U E a) (2 ^ k) ltac:(lia) ltac:(lia)).
  assert (U E a / 2 ^ k <= U E a) by (apply Z.div_le_upper_bound; nia).
  subst. apply zcanon_id. unfold M64. lia.
Qed.

(* `seqz`: sltiu rd, rs, 1 *)
Lemma at_U_seqz : forall E a x r,
  U E a = x -> (if x =? 0 then 1 else 0) = r -> U E (SAlu ALU_SLTU a (SLit 1)) = r.
Proof.
  intros E a x r Ha Hr. rewrite U_SAlu, (U_lit E 1) by lia. cbn [zalu_raw].
  pose proof (U_range E a) as R. subst.
  destruct (Z.eqb_spec (U E a) 0) as [H0|H0]; destruct (Z.ltb_spec (U E a) 1); try lia;
    apply zcanon_id; unfold M64; lia.
Qed.

(* NL_ALIGN: p := ((n + 3) srliw 2) slli 2 *)
Lemma at_U_P3 : forall E n,
  ew E 33%nat = w64 n -> 0 <= n <= 4096 ->
  U E (SAlu ALU_SLL (SAluw ALU_SRL (SOff 33 3) (SLit 2)) (SLit 2)) = 4 * ((n + 3) / 4).
Proof.
  intros E n Hn Hr.
  assert (Hx : U E (SOff 33 3) = n + 3) by (apply (at_U_off E 33 3 n); [exact Hn | lia | lia | lia]).
  pose proof (Z.div_pos (n + 3) 4 ltac:(lia) ltac:(lia)) as Q0.
  pose proof (Z.div_le_upper_bound (n + 3) 4 1025 ltac:(lia) ltac:(lia)) as Q1.
  assert (Hq : U E (SAluw ALU_SRL (SOff 33 3) (SLit 2)) = (n + 3) / 4).
  { rewrite U_of_S, S_SAluw, Hx, (U_lit E 2) by lia. cbn [zalu_raw].
    rewrite (Z.mod_small (n + 3) (2 ^ 32)) by lia. rewrite (Z.mod_small 2 (2 ^ 32)) by lia.
    change (Z.land 2 31) with 2. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
    rewrite swrap32_id by lia. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
  rewrite U_SAlu, Hq, (U_lit E 2) by lia. cbn [zalu_raw]. change (Z.land 2 63) with 2.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* environments: tokens are written at atoms 512.. and a call clobbers atoms from 48 on *)
Lemma at_ag_ewset : forall k E E' i w, (k <= i)%nat -> env_agree k E E' -> env_agree k E (ewset E' i w).
Proof.
  intros k E E' i w Hi [A D]. split; [|exact D].
  intros j Hj. rewrite ew_ewset_other by lia. apply A. exact Hj.
Qed.
End b.
End a.

(* ==========================================================================
   Tactics the phase files share (outside the sections, so that they survive them)
   ========================================================================== *)

Ltac at_inl := unfold AT_KEPT_REGS, AT_LIVE_REGS; cbn [In]; repeat (first [left; reflexivity | right]).

(* the value of a symbolic expression: atoms, literals, add, sub, srl, seqz, NL_ALIGN. An inner value is an evar
   that `reflexivity` fixes; the outer one is the target, which `lia` meets. *)
Ltac at_U :=
  first
  [ eapply at_U_P3; [eassumption | lia]
  | eapply at_U_atom0; [eassumption | lia]
  | eapply at_U_off; [eassumption | lia | first [reflexivity | lia] | lia]
  | eapply at_U_lit; [first [reflexivity | lia] | lia]
  | eapply at_U_add; [at_U | at_U | first [reflexivity | lia] | lia]
  | eapply at_U_sub; [at_U | at_U | first [reflexivity | lia] | lia]
  | eapply at_U_srl; [at_U | lia | first [reflexivity | lia]]
  | eapply at_U_seqz; [at_U | first [reflexivity | lia]] ].

Ltac at_agree := repeat (apply at_ag_ewset; [lia|]); apply env_agree_refl.

(* a register's value in the engine's state, by the value of its symbolic expression: leaves `U E e = v` *)
Ltac at_reg_val HS r :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?msc) =>
      rewrite (st_ok_restrict_reg segs H E ss msc r HS);
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e;
      unfold w64; apply at_denot
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?msc) =>
      rewrite (st_ok_pi_restrict_reg H E ss msc r HS);
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e;
      unfold w64; apply at_denot
  end.

(* the windows a run writes lie in Zs *)
Ltac at_frame_tac :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi x Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr;
     repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H in Hrr end; lia|]);
  destruct Hin.

(* the write obligation of a run: frame windows on the journal's window, struct windows on the write set *)
Ltac at_awr_tac Hajw :=
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H in Ha end;
      first [ lia
            | apply Hajw; apply at_E_in; unfold NW_SIZE in *; lia
            | left; split; [left; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.
