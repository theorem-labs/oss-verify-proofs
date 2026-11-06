(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module paths changed; 599 of its 833 lines of code are new or changed and 2508 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/RecStubU.v, with its module paths and module names changed; 444 of its 497 lines of code are new or changed and 780 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/SlotItCK.v; 330 of its 390 lines of code are new or changed and 437 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/SlotItB3qh.v, with its module paths and numbers changed; 526 of its 771 lines of code are new or changed and 145 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/AG/SlotItB3h.v, with its module names changed; 72 of its 109 lines of code are new or changed and 734 lines of the source are left out. *)
(* lib/Prog/SlotItSt.v with the agreement room cap CAP_AG (lib/SlotAgree.v) for CAPMAX. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL0g YL01 YL00 YI14 YI16 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require KindBGlue BlocksNodup.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP SlotSpec SlotGlue SlotRuns HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Import SlotCallees SlotIter SlotEnd SlotItBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Slot SlotInv SlotRec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecTail.
Import ListNotations.
Local Open Scope Z_scope.

(* The message at cursor (p, n) of the input block (p0, n0) holding pl: its header, its start and length, its
   bytes; the recorder facts of the walk with the message's own blocks X; the state after the message handler
   returned (pc 0x14184). *)

Section St.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound).
Hypothesis FG : Slot.frame_given B API LS SH SK ra empty.
Hypothesis PRE : lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b.
Hypothesis RG2 : spZ rg = S.

Notation CF := (SlotInv.CF B (API rc) S rg mem0 md0 L0 A0).
Notation FB := (SlotInv.FB S).

Definition m_hdr (p n : Z) : list byte := firstn (Z.to_nat (hdr_n n)) (skipn (Z.to_nat (p - p0)) pl).
Definition m_src (p n : Z) : Z := p + hdr_n n.
Definition m_len (p n : Z) : Z := msg_len n (m_hdr p n).
Definition m_D (p n : Z) : list byte := firstn (Z.to_nat (m_len p n)) (skipn (Z.to_nat (m_src p n - p0)) pl).

(* The recorder facts of RF, with the message's blocks X live besides the entry blocks and the recorder's. *)
Definition RFX (L : layout) (A : astate) (mem : word -> option byte) (R : rstate) (O : list (Z * Z)) (q : Z)
    (X : list (Z * Z)) : Prop :=
  g_rec_rep rsegs L A mem R O /\ r_spill R = (0, []) /\
  Mem.bytes_at rsegs mem CommandModel.G_QUIT (Mem.le4 (Z_to_bv 64 q)) /\ 0 <= q < 2 ^ 32 /\
  (forall a k, In (a, k) (blocks L0 A0) -> ~ In a (map fst O)) /\
  (forall pn, In pn (blocks L A) -> In pn (blocks L0 A0) \/ In pn O \/ In pn X) /\
  (forall pn, In pn X -> In pn (blocks L A) /\ ~ In pn (blocks L0 A0) /\ ~ In (fst pn) (map fst O)) /\
  (length O <= SlotInv.O_MAX)%nat.

Definition qv (quit : bool) : Z := if quit then 1 else 0.

(* The loop registers and locals kept from the loop head to the frees. *)
Definition LR (m p n : Z) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  getr regs 8 = Z_to_bv 64 (m_src p n) /\ getr regs 9 = Z_to_bv 64 (m_len p n) /\
  getr regs 22 = Z_to_bv 64 m /\ getr regs 24 = Z_to_bv 64 (n - hdr_n n) /\
  getr regs 25 = Z_to_bv 64 MASK /\ getr regs 27 = Z_to_bv 64 32 /\
  0 <= m <= 31 /\ 0 < n /\ p0 <= p /\ p + n = p0 + n0.

(* After the message handler returned (pc 0x14184): the recorder holds the run of the message on R0 (the
   recorder with the header's refuse and code, cleared), s2 and s3 the state and host words of R0. *)
Definition stA (m p n : Z) (R0 : rstate) (c : config) : Prop :=
  exists (fx : FPState) L A regs mem md O R1 x quit,
    c = mkCfg (@mkst fx regs (Z_to_bv 64 0x14184) mem (seg_rom rsegs)) md /\
    CF fx L A regs mem md /\ SlotInv.rcap A /\
    vr_run (rec_clear R0) (m_D p n) = (R1, x, quit) /\
    RFX L A mem R1 O (qv quit) [] /\
    LR m p n regs mem /\ getr regs 23 = Z_to_bv 64 n /\
    getr regs 18 = Z_to_bv 64 (r_state R0) /\ getr regs 19 = Z_to_bv 64 (r_host R0) /\
    (exists jsv jw, rw_cells rsegs mem FB (LOC0 jsv) /\ rw_cells rsegs mem (FB + 40) [CB 32 jw]) /\
    msg_props R0 (m_D p n).

Lemma it_nth_firstn : forall (l : list byte) k i, (i < k)%nat -> nth_error (firstn k l) i = nth_error l i.
Proof. induction l as [|x l IH]; intros k i H; destruct k; destruct i; cbn; try reflexivity; try lia. apply IH. lia. Qed.

Lemma it_nth_skipn : forall (l : list byte) k i, nth_error (skipn k l) i = nth_error l (k + i).
Proof. induction l as [|x l IH]; intros k i; destruct k; cbn; try reflexivity; [destruct i; reflexivity | apply IH]. Qed.

(* The input block: live, with its entry bytes pl. *)
Lemma it_inblk : forall fx L A regs mem md, CF fx L A regs mem md -> 0 < n0 ->
  In (p0, n0) (blocks L A) /\ In (p0, n0) (blocks L0 A0) /\ 4096 <= p0 /\ p0 + n0 <= alloc_ceiling /\
  Z.of_nat (length pl) = n0 /\
  forall i, 0 <= i < n0 -> mbyte rsegs mem (p0 + i) = nth_error pl (Z.to_nat i).
Proof.
  intros fx L A regs mem md (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EB & _) Hn.
  pose proof (it_SEGS B API LS SH SK ra empty FG) as SEGS.
  destruct PRE as ((HM0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HB & _) & HL & HD & _).
  destruct HB as [[Hz _]|[_ (q & Hq & Hp)]]; [lia|].
  assert (IB0 : In (p0, n0) (blocks L0 A0)).
  { rewrite <- Hp. exact (RecTail.user_in_blocks L0 A0 q n0 Hq). }
  destruct (EB p0 n0 IB0) as [IB K].
  destruct (block_facts B _ (aa_laws (API rc)) _ _ _ _ _ _ 0 HM0 IB0 ltac:(lia)) as (_ & R1 & R2 & _).
  split; [exact IB|]. split; [exact IB0|]. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. rewrite (K i Hi). unfold blk_data in HD. rewrite SEGS in HD. apply HD. lia.
Qed.

Lemma it_in_bytes : forall fx L A regs mem md, CF fx L A regs mem md -> 0 < n0 ->
  forall k len, 0 <= k -> 0 <= len -> k + len <= n0 ->
  Mem.bytes_at rsegs mem (p0 + k) (firstn (Z.to_nat len) (skipn (Z.to_nat k) pl)).
Proof.
  intros fx L A regs mem md HC Hn k len Hk Hl Hkl.
  destruct (it_inblk fx L A regs mem md HC Hn) as (_ & _ & H1 & H2 & HL & HB).
  assert (EL : length (firstn (Z.to_nat len) (skipn (Z.to_nat k) pl)) = Z.to_nat len).
  { rewrite length_firstn, length_skipn. lia. }
  split; [lia|]. split; [rewrite EL; pose proof alloc_ceiling_lt; lia|].
  intros i Hi. rewrite EL in Hi. rewrite <- mbyte_mrd.
  replace (p0 + k + Z.of_nat i) with (p0 + (k + Z.of_nat i)) by ring.
  rewrite (HB (k + Z.of_nat i)) by lia.
  rewrite it_nth_firstn by lia. rewrite it_nth_skipn. f_equal. lia.
Qed.

Lemma m_hdr_len : forall p n, 0 < n -> p0 <= p -> p + n = p0 + n0 ->
  Z.of_nat (length pl) = n0 -> length (m_hdr p n) = Z.to_nat (hdr_n n).
Proof.
  intros p n Hn Hp Hpn HL. unfold m_hdr, hdr_n. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma m_len_range : forall p n, 0 < n -> 0 <= m_len p n <= 8192 /\ m_len p n <= n - hdr_n n.
Proof.
  intros p n Hn. unfold m_len, msg_len, hdr_n.
  pose proof (sr_hbyte_range (m_hdr p n) 1). pose proof (sr_hbyte_range (m_hdr p n) 2). lia.
Qed.

Lemma m_D_len : forall p n, 0 < n -> p0 <= p -> p + n = p0 + n0 -> Z.of_nat (length pl) = n0 ->
  Z.of_nat (length (m_D p n)) = m_len p n.
Proof.
  intros p n Hn Hp Hpn HL. pose proof (m_len_range p n Hn). unfold m_D, m_src, hdr_n in *.
  rewrite length_firstn, length_skipn. lia.
Qed.

End St.
