(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module paths and module names changed; 896 of its 958 lines of code are new or changed and 1243 lines of the source are left out. *)
(* nl_talk on image A (fuzz_link.asan 0x88974; listing (internal path)
   (internal record, sha256 628c2741aace)), THE ATTRIBUTE PHASE, part 1: the cut invariants, the symbolic states built
   from them, the byte views carried across a run and across a copy_attr call, and the two concrete tails (the step's
   `bge` at +0x470 and the exit at +0x4dc). Part 2 (nl_talk_attr2.v) holds the two loops and the phase lemma nt_attr.

   The cuts, as listing offsets from nl_talk:
     +0x314  NT_attr   the phase's entry (nl_talk_defs.v nt_attr_inv);
     +0x338  NT_aloop  the attribute loop head (na_c1);
     +0x3ac  NT_info   the nested loop head (na_c3);
     +0x470  NA_bge    the attribute loop's `bge a4, s6` (na_c2), stepped concretely;
     +0x4dc  NT_exit   every exit (nl_talk_defs.v nt_exit_inv).
   Between two cuts the walk is a symbolic run (LinkPaLib.v paj_run_tok / psrr_branch_tok) from a state built from
   the cut's invariant; the two copy_attr calls are applied under SRr_bind.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality Classical.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkWseg LinkWalkCall LinkWalkShadow link_aro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_talk_c copy_attr_c nl_talk_defs nl_talk_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   0. Values the walk meets (no image)
   ========================================================================== *)

Definition NA_bge : Z := AF_nl_talk + 0x470.    (* 0x88de4 `bge a4, s6` of the attribute loop's step *)

(* the symbolic value of a register, by the value of its atom *)
Lemma na_U_al : forall E (nl ns : nat) l, ew E nl = Z_to_bv 64 l -> 0 <= l <= 65535 ->
  ew E ns = Z_to_bv 64 131068 ->
  U E (SAlu ALU_AND (SOff nl 3) (SOff ns 0)) = nl_align l.
Proof.
  intros E nl ns l Hl Hr Hs. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom_off E nl l 3 Hl) by lia. rewrite (U_atom E ns 131068 Hs) by lia.
  rewrite (nt_nl_align_land l Hr). pose proof (nt_nl_align_ge l ltac:(lia)). apply zcanon_id. unfold M64. lia.
Qed.

Lemma na_U_addp : forall E (n : nat) p e, ew E n = Z_to_bv 64 p -> 0 <= p -> p + U E e < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff n 0) e) = p + U E e.
Proof.
  intros E n p e Hn H0 H1. rewrite U_SAlu. cbn [zalu_raw]. pose proof (U_range E e).
  rewrite (U_atom E n p Hn) by (unfold M64 in *; lia). apply zcanon_id. unfold M64 in *. lia.
Qed.

Lemma na_S_subw : forall E (n : nat) x e, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 31 -> 0 <= U E e < 2 ^ 31 ->
  Sg E (SAluw ALU_SUB (SOff n 0) e) = x - U E e.
Proof.
  intros E n x e Hn Hx He. rewrite S_SAluw. cbn [zalu_raw].
  rewrite (U_atom E n x Hn) by lia. rewrite !Z.mod_small by lia.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

Lemma na_denot_of_S : forall E e v, Sg E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof.
  intros E e v H. rewrite denot_lit_U, U_of_S, H. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite Z.mod_mod by (unfold bv_modulus; lia). reflexivity.
Qed.

Lemma na_branch_lt : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros E a b. reflexivity. Qed.
Lemma na_branch_ge : forall E a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. intros E a b. reflexivity. Qed.

Lemma na_S_atom : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> - 2 ^ 63 <= v < 2 ^ 63 -> Sg E (SOff n 0) = v.
Proof.
  intros E n v Hn Hv. rewrite S_SOff, Hn, Z.add_0_r, Z_to_bv_unsigned, bv_swrap_wrap'.
  apply bv_swrap_small. change (bv_half_modulus 64) with (2 ^ 63). lia.
Qed.

Lemma na_S_lit : forall E z, - 2 ^ 63 <= z < 2 ^ 63 -> Sg E (SLit z) = z.
Proof. intros E z Hz. rewrite S_SLit. apply bv_swrap_small. change (bv_half_modulus 64) with (2 ^ 63). lia. Qed.

(* environments: the atoms below k stay when fresh atoms are set at k or above *)
Lemma na_ag_trans : forall k E1 E2 E3, env_agree k E1 E2 -> env_agree k E2 E3 -> env_agree k E1 E3.
Proof. intros k E1 E2 E3 [A1 D1] [A2 D2]. split; [intros nn Hn; rewrite A2 by exact Hn; apply A1; exact Hn | congruence]. Qed.
Lemma na_ag_le : forall k k' E E', (k' <= k)%nat -> env_agree k E E' -> env_agree k' E E'.
Proof. intros k k' E E' Hk [A D]. split; [intros nn Hn; apply A; lia | exact D]. Qed.
Lemma na_ag_ewset : forall k E n w, (k <= n)%nat -> env_agree k E (ewset E n w).
Proof. intros k E n w Hk. split; [|reflexivity]. intros nn Hn. rewrite ew_ewset_other by lia. reflexivity. Qed.
Lemma na_ag_reg : forall k regs EXT E (nn : nat) (r : bv 5),
  (32 <= k)%nat -> env_agree k (Ereg regs EXT) E -> Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs r.
Proof.
  intros k regs EXT E nn r Hk [A _] Hr. pose proof (u5_range r) as R.
  rewrite A by lia. exact (ew_Ereg_nat regs EXT nn r Hr).
Qed.
Lemma na_ag_ext : forall k regs EXT E (nn : nat) j,
  env_agree k (Ereg regs EXT) E -> nn = (32 + j)%nat -> (nn < k)%nat -> ew E nn = nth j EXT (Z_to_bv 64 0).
Proof. intros k regs EXT E nn j [A _] -> Hj. rewrite A by lia. exact (ew_Ereg_extra regs EXT j). Qed.

(* a run whose regions write nothing leaves the memory as it was *)
Lemma na_frame_ro : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> m' = m.
Proof.
  intros E rs m m' HF Hro. apply functional_extensionality. intros x. apply HF.
  intros (r & Hin & Hr). rewrite Forall_forall in Hro. pose proof (Hro r Hin). lia.
Qed.

(* an 8-byte word read through two readers that agree on its bytes *)
Lemma na_rdword_ext : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H. unfold rdword.
  rewrite <- (Z.add_0_r a) at 1 2.
  rewrite (H 0), (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. rewrite Z.add_0_r. reflexivity.
Qed.


(* ==========================================================================
   0b. The symbolic states of the cuts
   atoms: 2 = sp, 9 = s1 (the realigned sp), 21 = s5 (the shadow base, also the runner's base Bx),
   26 = s10 (the attribute), 27 = s11 (the nested attribute); 32, 33 = the attribute's length and type,
   34 .. 37 = alias, alias_n, kind, kind_n (the spill slots at s1 + 8, 16, 48, 56), 38, 39 = the nested
   attribute's length and type.
   ========================================================================== *)

Definition na_Bx : sv := SOff 21 0.
Definition na_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition na_spf : afact := mkAF (2 ^ 46 - 512) (2 ^ 47) 5.
Definition na_pf : afact := mkAF 4096 (2 ^ 47 - 4096) 0.
Definition na_hf : afact := mkAF 0 65535 0.
Definition na_spill : YP09.region := YP09.mkRegion (Some 9%nat) 8 64 0 0
  [YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0));
   YP09.mkChunk 48 (CVal 8 (SOff 36 0)); YP09.mkChunk 56 (CVal 8 (SOff 37 0))].
Definition na_hdr (n la lt : nat) : YP09.region := YP09.mkRegion (Some n) 0 4 0 0
  [YP09.mkChunk 0 (CVal 2 (SOff la 0)); YP09.mkChunk 2 (CVal 2 (SOff lt 0))].
Definition na_shx (n : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 21 0).

Definition na_fac1 : facts := mkFacts
  [(21%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (26%nat, na_pf); (32%nat, na_hf); (33%nat, na_hf);
   (9%nat, na_spf); (2%nat, na_spf)] [] [].
Definition na_ss1 : sstate := mkSS NT_aloop sr_atoms [na_spill; na_hdr 26 32 33] None na_fac1.
Definition na_SH1 : list shent := [mkSHE 26 0 4].

Definition na_fac3 : facts := mkFacts
  [(21%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (26%nat, na_pf); (27%nat, na_pf); (32%nat, na_hf); (33%nat, na_hf);
   (38%nat, na_hf); (39%nat, na_hf); (9%nat, na_spf); (2%nat, na_spf)] [] [].
Definition na_ss3 : sstate := mkSS NT_info (sr_set sr_atoms (25%bv : bv 5) (na_shx 26))
  [na_spill; na_hdr 26 32 33; na_hdr 27 38 39] None na_fac3.
Definition na_SH3 : list shent := [mkSHE 26 0 4; mkSHE 27 0 4].

(* NT_astep (+0x454): s9 holds the attribute's shadow address, as the head computed it *)
Definition na_ss2 : sstate := mkSS NT_astep (sr_set sr_atoms (25%bv : bv 5) (na_shx 26)) [na_spill; na_hdr 26 32 33] None na_fac1.

(* NT_istep (+0x400): s3 holds the nested attribute's shadow address, as the nested head computed it *)
Definition na_ss4 : sstate := mkSS NT_istep (sr_set (sr_set sr_atoms (25%bv : bv 5) (na_shx 26)) (19%bv : bv 5) (na_shx 27))
  [na_spill; na_hdr 26 32 33; na_hdr 27 38 39] None na_fac3.

Definition na_spill0 : YP09.region := YP09.mkRegion (Some 9%nat) 8 64 8 24 [].
Definition na_fac0 : facts := mkFacts [(9%nat, na_spf); (2%nat, na_spf)] [] [].
Definition na_ss0 : sstate := mkSS NT_attr sr_atoms [na_spill0] None na_fac0.

Lemma na_as_small_eq : forall f (c : list byte) off left a, left < 4 -> attr_scan f c off left a = a.
Proof. intros f c off left a H. exact (nt_as_small f off left a H). Qed.

Lemma na_bge_val : forall x, - 2 ^ 63 <= x < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 3) (Z_to_bv 64 x) = (x <? 4).
Proof.
  intros x Hx. cbn [branch_taken]. unfold bv_lts. rewrite !nt_signed64 by lia.
  destruct (Z.ltb_spec 3 x); destruct (Z.ltb_spec x 4); try lia; reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img pa_segs a.
Hypothesis CA : copy_attr_acontract SK pa_segs PCAP_RLO PCAP_RHI B.

(* ==========================================================================
   1. Byte views carried from one memory to another
   ========================================================================== *)

(* a writable byte stays writable when its value is kept and it is not a read-only byte: off the image by its
   presence, on the image by its writable segment (LinkWalkWseg.v) *)
Lemma na_wr_kept : forall (W W' : world SEGS) m m' a, 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a ->
  writable_at SEGS (rdW W m) a -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a ->
  writable_at SEGS (rdW W' m') a.
Proof.
  intros W W' m m' a Ha Hv Hw Hro.
  destruct (classic (in_img SEGS a)) as [Hi | Hni].
  - destruct Hi as (sg & Hin & Hr).
    assert (Hws : seg_writable sg = true).
    { destruct (seg_writable sg) eqn:E; [reflexivity|]. exfalso. apply Hro. left. exists sg. auto. }
    pose proof (wseg_writable_tfib (rdW W' m') a) as Hx. rewrite <- HSEGS in Hx. apply Hx. exists sg. auto.
  - assert (Hp : apresent (w_H W) m a).
    { unfold writable_at, wview, mrestrict in Hw. unfold apresent.
      destruct (w_H W (Z_to_bv 64 a)) eqn:EH.
      - exfalso. destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 a)) 1) as [sg|] eqn:Ef; [|exact (Hw eq_refl)].
        apply Hni. destruct (find_segment_hit _ _ _ _ Ef) as (Hin & H1 & H2).
        rewrite unsigned_lit_small in H1, H2 by lia. exists sg. split; [exact Hin | lia].
      - split; [reflexivity|]. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [exists b; reflexivity|].
        exfalso. destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 a)) 1) as [sg|] eqn:Ef; [|exact (Hw eq_refl)].
        apply Hni. destruct (find_segment_hit _ _ _ _ Ef) as (Hin & H1 & H2).
        rewrite unsigned_lit_small in H1, H2 by lia. exists sg. split; [exact Hin | lia]. }
    apply (apresent_writable SEGS). exact (apresent_transfer SEGS _ _ _ _ a Ha Hni Hv Hp).
Qed.

Lemma na_abytes_kept : forall (W W' : world SEGS) m m' b bs,
  abytes SEGS (rdW W m) b bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> aview SEGS (w_H W') m' (b + i) = aview SEGS (w_H W) m (b + i)) ->
  abytes SEGS (rdW W' m') b bs.
Proof.
  intros W W' m m' b bs (H0 & H1 & H2) Hv. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (mbyte_of_aview SEGS _ _ _ _ _ (Hv (Z.of_nat i) ltac:(lia))). exact (H2 i Hi).
Qed.

Lemma na_au8arr_kept : forall (W W' : world SEGS) m m' b bs,
  au8arr SEGS (rdW W m) b bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> aview SEGS (w_H W') m' (b + i) = aview SEGS (w_H W) m (b + i)) ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ in_roP SEGS PCAP_RLO PCAP_RHI (b + i)) ->
  au8arr SEGS (rdW W' m') b bs.
Proof.
  intros W W' m m' b bs (HB & HW) Hv Hro. pose proof HB as (H0 & H1 & _).
  split; [exact (na_abytes_kept W W' m m' b bs HB Hv)|].
  intros i Hi. apply (na_wr_kept W W' m m' (b + i)); [lia | exact (Hv i Hi) | exact (HW i Hi) | exact (Hro i Hi)].
Qed.

Lemma na_abuf_kept : forall (W W' : world SEGS) m m' b n,
  abuf SEGS (rdW W m) b n ->
  (forall i, 0 <= i < n -> aview SEGS (w_H W') m' (b + i) = aview SEGS (w_H W) m (b + i)) ->
  (forall i, 0 <= i < n -> ~ in_roP SEGS PCAP_RLO PCAP_RHI (b + i)) ->
  abuf SEGS (rdW W' m') b n.
Proof.
  intros W W' m m' b n (junk & Hl & HU) Hv Hro. exists junk. split; [exact Hl|].
  apply (na_au8arr_kept W W' m m' b junk HU); intros i Hi; [apply Hv | apply Hro]; lia.
Qed.

Lemma na_acstr_kept : forall (W W' : world SEGS) m m' b s,
  acstr_at SEGS (rdW W m) b s ->
  (forall i, 0 <= i <= Z.of_nat (length s) -> aview SEGS (w_H W') m' (b + i) = aview SEGS (w_H W) m (b + i)) ->
  acstr_at SEGS (rdW W' m') b s.
Proof.
  intros W W' m m' b s (HB & HN) Hv. split; [|exact HN].
  apply (na_abytes_kept W W' m m' b _ HB). intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hv. lia.
Qed.

Lemma na_nt_at_kept : forall (W W' : world SEGS) (ms ms' : machine_state) a v,
  nt_at W ms a v ->
  (forall i, 0 <= i < 8 -> aview SEGS (w_H W') (ms_mem ms') (a + i) = aview SEGS (w_H W) (ms_mem ms) (a + i)) ->
  nt_at W' ms' a v.
Proof. intros W W' ms ms' a v H Hv. unfold nt_at in *. rewrite (na_rdword_ext _ _ a Hv). exact H. Qed.

(* ==========================================================================
   2. The two caller buffers along the walk
   ========================================================================== *)

(* a buffer that holds the text of the last attribute copied into it, or what the entry memory m0 held *)
Definition na_buf (m0 m : word -> option byte) (b n : Z) (o : option (list byte)) : Prop :=
  (b <> 0 -> 1 <= n -> abuf SEGS m b n) /\
  match o with
  | Some pay => b <> 0 -> 1 <= n -> acstr_at SEGS m b (cut_text pay n)
  | None => b <> 0 -> forall s, Z.of_nat (length s) < n -> acstr_at SEGS m0 b s -> acstr_at SEGS m b s
  end.

Definition na_bufs (cx : ntcx) (m : word -> option byte) (a : attrs) : Prop :=
  na_buf (n_m cx) m (n_kind cx) (n_kindn cx) (a_kind a) /\
  na_buf (n_m cx) m (n_alias cx) (n_aliasn cx) (a_alias a).

Lemma na_bufs_init : forall cx m, nt_bufs_same cx m -> na_bufs cx m no_attrs.
Proof.
  intros cx m (K1 & K2 & K3 & K4). unfold na_bufs, na_buf. cbn [a_kind a_alias no_attrs].
  split; split; assumption.
Qed.

Lemma na_bufs_fin : forall cx m, na_bufs cx m (talk_attrs (n_K0 cx)) -> nt_bufs_fin cx m.
Proof.
  intros cx m ((K3 & K1) & (K4 & K2)). unfold nt_bufs_fin.
  destruct (a_kind (talk_attrs (n_K0 cx))) as [pk|] eqn:Ek;
  destruct (a_alias (talk_attrs (n_K0 cx))) as [pa|] eqn:Ea.
  - split; [intros pay Hp; injection Hp as <-; exact K1|].
    split; [intros pay Hp; injection Hp as <-; exact K2|].
    split; [intros Hp; discriminate Hp|]. split; [intros Hp; discriminate Hp|]. split; assumption.
  - split; [intros pay Hp; injection Hp as <-; exact K1|]. split; [intros pay Hp; discriminate Hp|].
    split; [intros Hp; discriminate Hp|]. split; [intros _; exact K2|]. split; assumption.
  - split; [intros pay Hp; discriminate Hp|]. split; [intros pay Hp; injection Hp as <-; exact K2|].
    split; [intros _; exact K1|]. split; [intros Hp; discriminate Hp|]. split; assumption.
  - split; [intros pay Hp; discriminate Hp|]. split; [intros pay Hp; discriminate Hp|].
    split; [intros _; exact K1|]. split; [intros _; exact K2|]. split; assumption.
Qed.

(* a buffer whose bytes keep their value and stay writable keeps its state *)
Lemma na_buf_kept : forall (W W' : world SEGS) m0 m m' b n o,
  na_buf m0 (rdW W m) b n o ->
  (b <> 0 -> 1 <= n -> forall i, 0 <= i < n -> aview SEGS (w_H W') m' (b + i) = aview SEGS (w_H W) m (b + i)) ->
  (b <> 0 -> 1 <= n -> forall i, 0 <= i < n -> ~ in_roP SEGS PCAP_RLO PCAP_RHI (b + i)) ->
  na_buf m0 (rdW W' m') b n o.
Proof.
  intros W W' m m0 m' b n o (HA & HS) Hv Hro. split.
  - intros Hb Hn. exact (na_abuf_kept W W' m0 m' b n (HA Hb Hn) (Hv Hb Hn) (Hro Hb Hn)).
  - destruct o as [pay|].
    + intros Hb Hn. apply (na_acstr_kept W W' m0 m' b _ (HS Hb Hn)). intros i Hi. apply (Hv Hb Hn).
      pose proof (cut_text_len pay n Hn). lia.
    + intros Hb s Hs H0. apply (na_acstr_kept W W' m0 m' b s (HS Hb s Hs H0)). intros i Hi.
      apply (Hv Hb ltac:(lia)). lia.
Qed.

(* ==========================================================================
   3. The state at the cuts of the phase
   ========================================================================== *)

(* What holds at every cut of the phase and does not move during it: the journal, the body's registers, the
   machine frame's saves, the class-9 frame's header and shadow, the spill slots of the earlier phases, the
   bookkeeping and the kept clause, g_nl as the receives left it, the model's facts, and the receive buffer with
   the chunk c in it. *)
Definition na_core (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) (c rest bs : list byte) : Prop :=
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 /\
  nt_regs cx fp ms3 /\ nt_saved cx W3 ms3 /\ nt_header cx fp W3 ms3 /\ nt_slots0 cx fp W3 ms3 /\
  nt_at W3 ms3 (n_sp1 cx + NS_SH4) (nSH cx fp + 4) /\
  nt_at W3 ms3 (n_sp1 cx + NS_FK) (nF cx fp) /\
  nt_at W3 ms3 (n_sp1 cx + NS_FD) NL_FD /\
  nt_frame_shadow cx fp 0 W3 ms3 /\
  nt_jbk B cx fp k2 ly3 S3 md3 /\ nt_kept B cx (n_E cx) fp W3 (ms_mem ms3) /\
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL bs /\
  nt_gnl_open cx bs true (Z.of_nat (k_next (talk_after (n_K0 cx)))) /\
  talk_owes (n_K0 cx) = true /\ talk_rc_lib (n_K0 cx) = 0 /\
  abytes SEGS (rdW W3 (ms_mem ms3)) (nBUF cx fp) (c ++ rest) /\
  Z.of_nat (length (c ++ rest)) = NT_BUFLEN /\ (length c <= Z.to_nat NL_CHUNK_MAX)%nat /\
  abuf SEGS (rdW W3 (ms_mem ms3)) (nBUF cx fp) NT_BUFLEN.

(* the two spill slots this phase writes (+0x320, +0x324) *)
Definition na_slots (cx : ntcx) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  nt_at W3 ms3 (n_sp1 cx + NS_ALIAS) (n_alias cx) /\ nt_at W3 ms3 (n_sp1 cx + NS_ALIASN) (n_aliasn cx).

(* NT_aloop (+0x338): the attribute at aoff with aleft bytes left, the accumulator a so far *)
Definition na_c1 (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
    (md3 : Model) (c rest bs : list byte) (f : nat) (aoff aleft : Z) (a : attrs) : Prop :=
  na_core cx fp k2 ly3 S3 W3 ms3 md3 c rest bs /\ na_slots cx W3 ms3 /\ nt_shape NT_aloop ms3 /\
  getr (ms_regs ms3) 26 = w64 (nBUF cx fp + aoff) /\ getr (ms_regs ms3) 22 = w64 aleft /\
  getr (ms_regs ms3) 20 = w64 131068 /\ getr (ms_regs ms3) 13 = w64 4 /\ getr (ms_regs ms3) 14 = w64 3 /\
  0 <= aoff /\ 4 <= aleft /\ aoff + aleft <= Z.of_nat (length c) /\ (Z.to_nat aleft < f)%nat /\
  talk_attrs (n_K0 cx) = attr_scan f c aoff aleft a /\
  na_bufs cx (rdW W3 (ms_mem ms3)) a.

(* NA_bge (+0x470): the step computed the next attribute p and the bytes left `left` (s10, s6) *)
Definition na_c2 (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
    (md3 : Model) (c rest bs : list byte) (f : nat) (p left : Z) (a : attrs) : Prop :=
  na_core cx fp k2 ly3 S3 W3 ms3 md3 c rest bs /\ na_slots cx W3 ms3 /\ nt_shape NA_bge ms3 /\
  getr (ms_regs ms3) 26 = w64 (nBUF cx fp + p) /\ getr (ms_regs ms3) 22 = w64 left /\
  getr (ms_regs ms3) 20 = w64 131068 /\ getr (ms_regs ms3) 13 = w64 4 /\ getr (ms_regs ms3) 14 = w64 3 /\
  0 <= p /\ - 65536 <= left /\ p + left <= Z.of_nat (length c) /\ (4 <= left -> (Z.to_nat left < f)%nat) /\
  talk_attrs (n_K0 cx) = attr_scan f c p left a /\
  na_bufs cx (rdW W3 (ms_mem ms3)) a.

(* NT_info (+0x3ac): inside the IFLA_LINKINFO at aoff, the nested attribute at ioff with ileft bytes left, the
   kind so far k; al is the alias so far, and the outer walk goes on after this attribute *)
Definition na_c3 (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
    (md3 : Model) (c rest bs : list byte) (f g : nat) (aoff aleft ioff ileft : Z)
    (k al : option (list byte)) : Prop :=
  na_core cx fp k2 ly3 S3 W3 ms3 md3 c rest bs /\ na_slots cx W3 ms3 /\ nt_shape NT_info ms3 /\
  getr (ms_regs ms3) 26 = w64 (nBUF cx fp + aoff) /\ getr (ms_regs ms3) 22 = w64 aleft /\
  getr (ms_regs ms3) 25 = w64 (SHADOW_OFF + (nBUF cx fp + aoff) / 8) /\
  getr (ms_regs ms3) 27 = w64 (nBUF cx fp + ioff) /\ getr (ms_regs ms3) 23 = w64 ileft /\
  getr (ms_regs ms3) 20 = w64 131068 /\ getr (ms_regs ms3) 13 = w64 4 /\ getr (ms_regs ms3) 14 = w64 3 /\
  0 <= aoff /\ 8 <= rd16 c aoff <= aleft /\ aoff + aleft <= Z.of_nat (length c) /\
  aoff + 4 <= ioff /\ ioff + ileft = aoff + rd16 c aoff /\ 4 <= ileft /\ (Z.to_nat ileft < g)%nat /\
  aleft <= Z.of_nat f /\
  talk_attrs (n_K0 cx) =
    attr_scan f c (aoff + nl_align (rd16 c aoff)) (aleft - nl_align (rd16 c aoff)) (Attrs (kind_scan g c ioff ileft k) al) /\
  na_bufs cx (rdW W3 (ms_mem ms3)) (Attrs k al).

(* the machine state at a cut is a plain state at the cut's pc *)
Lemma na_ms_eta : forall pc (ms : machine_state), nt_shape pc ms ->
  ms = mkst (ms_regs ms) (w64 (BASE + pc)) (ms_mem ms) (seg_rom SEGS).
Proof.
  intros pc [r fr pcv sv rv fc m ro] (H1 & H2 & H3 & H4 & H5 & H6). cbn in *. subst. reflexivity.
Qed.

(* the core holds of a state with the same memory and the same body registers *)
Lemma na_core_ms : forall cx fp k2 ly3 S3 W3 ms ms' md3 c rest bs,
  na_core cx fp k2 ly3 S3 W3 ms md3 c rest bs -> ms_mem ms' = ms_mem ms -> nt_regs cx fp ms' ->
  na_core cx fp k2 ly3 S3 W3 ms' md3 c rest bs.
Proof.
  intros cx fp k2 ly3 S3 W3 ms ms' md3 c rest bs H Hm HR.
  unfold na_core, nt_saved, nt_header, nt_slots0, nt_at, nt_frame_shadow in *. rewrite Hm. tauto.
Qed.

Lemma na_slots_ms : forall cx W3 ms ms', na_slots cx W3 ms -> ms_mem ms' = ms_mem ms -> na_slots cx W3 ms'.
Proof. intros cx W3 ms ms' H Hm. unfold na_slots, nt_at in *. rewrite Hm. exact H. Qed.

(* the core holds after the model is materialised *)
Lemma na_core_md : forall cx fp k2 ly3 S3 W3 ms3 md3 c rest bs X,
  na_core cx fp k2 ly3 S3 W3 ms3 md3 c rest bs ->
  na_core cx fp k2 ly3 S3 W3 ms3 (with_vm_backing (m_vm_lazy md3) X md3) c rest bs.
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 c rest bs X (HJ & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & HJB & H).
  split; [exact (ajournal_gx_materialize (SK := SK) SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X HJ)|].
  do 8 (split; [assumption|]).
  split; [|exact H].
  unfold nt_jbk in *. rewrite (proj1 (wvb_fds_fs (m_vm_lazy md3) X md3)), (proj2 (wvb_fds_fs (m_vm_lazy md3) X md3)).
  exact HJB.
Qed.

(* ==========================================================================
   4. The exit (+0x4dc) and the step's `bge` (+0x470)
   ========================================================================== *)

Lemma na_exit : forall POST cx fp k2 ly3 S3 W3 ms3 md3 c rest bs,
  nt_from SK B POST (nt_exit_inv B) -> nt_base SK B cx ->
  na_core cx fp k2 ly3 S3 W3 ms3 md3 c rest bs ->
  nt_shape NT_exit ms3 -> getr (ms_regs ms3) 27 = w64 0 ->
  na_bufs cx (rdW W3 (ms_mem ms3)) (talk_attrs (n_K0 cx)) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST cx fp k2 ly3 S3 W3 ms3 md3 c rest bs HX HB
    (HJ & HR & HSV & HH & HS0 & HA1 & HA2 & HA3 & HFS & HJB & HK & HG & HGO & HOW & HRC & _) Hsh H27 Hbf.
  pose proof HJB as (_ & _ & _ & Hfrs & _).
  apply (HX cx fp k2 ly3 S3 W3 ms3 md3 HB HJ Hfrs).
  unfold nt_exit_inv. split; [exact Hsh|]. split; [exact HR|]. split; [exact HSV|]. split; [exact HH|].
  split; [exact HA1|]. split; [exact HA2|]. split; [exact HA3|].
  split; [rewrite HRC; exact H27|]. split; [exact HFS|]. split; [exact HJB|]. split; [exact HK|].
  split; [exists bs; split; [exact HG | rewrite HOW; exact HGO]|].
  split; [exact HOW|]. exact (na_bufs_fin cx _ Hbf).
Qed.

(* the four instructions the concrete tail steps *)
Lemma na_fetch_bge : fetch_word SEGS (Z_to_bv 64 (BASE + NA_bge)) = Some (Z_to_bv 32 0x05675663).
Proof. apply pa_fetch_pw. vm_compute. reflexivity. Qed.
Lemma na_dec_bge : decode_any (Z_to_bv 32 0x05675663) =
  Some (Branch BC_GE (14%bv : bv 5) (22%bv : bv 5) (0x4c%bv : bv 13), 4%Z).
Proof. lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end. Qed.
Lemma na_fetch_loop : fetch_word SEGS (Z_to_bv 64 (BASE + (NA_bge + 4))) = Some (Z_to_bv 32 0xec5ff06f).
Proof. apply pa_fetch_pw. vm_compute. reflexivity. Qed.
Lemma na_dec_loop : decode_any (Z_to_bv 32 0xec5ff06f) = Some (Jal (0%bv : bv 5) (0x1ffec4%bv : bv 21), 4%Z).
Proof. lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end. Qed.
Lemma na_fetch_rc0 : fetch_word SEGS (Z_to_bv 64 (BASE + NT_adone)) = Some (Z_to_bv 32 0x00000d93).
Proof. apply pa_fetch_pw. vm_compute. reflexivity. Qed.
Lemma na_dec_rc0 : decode_any (Z_to_bv 32 0x00000d93) =
  Some (OpImm ALU_ADD (27%bv : bv 5) (0%bv : bv 5) (0%bv : bv 12), 4%Z).
Proof. lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end. Qed.
Lemma na_fetch_jx : fetch_word SEGS (Z_to_bv 64 (BASE + (NT_adone + 4))) = Some (Z_to_bv 32 0x01c0006f).
Proof. apply pa_fetch_pw. vm_compute. reflexivity. Qed.
Lemma na_dec_jx : decode_any (Z_to_bv 32 0x01c0006f) = Some (Jal (0%bv : bv 5) (0x1c%bv : bv 21), 4%Z).
Proof. lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end. Qed.
Lemma na_ecall_bge : is_ecall (Z_to_bv 32 0x05675663) = false. Proof. vm_compute. reflexivity. Qed.
Lemma na_ecall_loop : is_ecall (Z_to_bv 32 0xec5ff06f) = false. Proof. vm_compute. reflexivity. Qed.
Lemma na_ecall_rc0 : is_ecall (Z_to_bv 32 0x00000d93) = false. Proof. vm_compute. reflexivity. Qed.
Lemma na_ecall_jx : is_ecall (Z_to_bv 32 0x01c0006f) = false. Proof. vm_compute. reflexivity. Qed.

Lemma na_pc_add : forall k d, 0 <= k < 2 ^ 40 -> k + d < 2 ^ 40 -> 0 <= k + d ->
  v_addi (Z_to_bv 64 (BASE + k)) d = Z_to_bv 64 (BASE + (k + d)).
Proof.
  intros k d Hk Hd Hd0. pose proof pa_B_ok as (HB0 & HB1 & _). unfold v_addi. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. lia.
Qed.


Lemma na_pc_addw : forall k d, 0 <= k < 2 ^ 40 -> k + d < 2 ^ 40 -> 0 <= k + d ->
  v_addi (w64 (BASE + k)) d = w64 (BASE + (k + d)).
Proof. intros k d H1 H2 H3. exact (na_pc_add k d H1 H2 H3). Qed.

(* the concrete tail of a turn: `bge a4, s6` (+0x470); taken: s11 := 0 (+0x4bc), `j` (+0x4c0) to the exit;
   not taken: `j` (+0x474) back to the loop head *)
Lemma na_c2_step : forall POST (f : nat) cx fp,
  nt_from SK B POST (nt_exit_inv B) -> nt_base SK B cx ->
  (forall k2 ly3 S3 W3 ms3 md3 c rest bs aoff aleft a,
     na_c1 cx fp k2 ly3 S3 W3 ms3 md3 c rest bs f aoff aleft a -> SRr SEGS W3 (mkCfg ms3 md3) (POST cx)) ->
  forall k2 ly3 S3 W3 ms3 md3 c rest bs p left a,
  na_c2 cx fp k2 ly3 S3 W3 ms3 md3 c rest bs f p left a -> SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST f cx fp HX HB K1 k2 ly3 S3 W3 ms3 md3 c rest bs p left a
    (HC & HSl & Hsh & R26 & R22 & R20 & R13 & R14 & Hp0 & Hl0 & Hpl & Hfu & HM & HBF).
  rewrite (na_ms_eta NA_bge ms3 Hsh). set (rg := ms_regs ms3) in *. set (mm := ms_mem ms3) in *.
  assert (HCm : na_core cx fp k2 ly3 S3 W3 (mkst rg (w64 (BASE + NA_bge)) mm (seg_rom SEGS)) md3 c rest bs)
    by (apply (na_core_ms cx fp k2 ly3 S3 W3 ms3); [exact HC | reflexivity | exact (proj1 (proj2 HC))]).
  assert (HSm : na_slots cx W3 (mkst rg (w64 (BASE + NA_bge)) mm (seg_rom SEGS)))
    by (apply (na_slots_ms cx W3 ms3); [exact HSl | reflexivity]).
  assert (Hlc : (length c <= Z.to_nat NL_CHUNK_MAX)%nat)
    by (destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlc & _); exact Hlc).
  unfold NL_CHUNK_MAX in Hlc.
  clearbody rg mm. clear HC HSl.
  assert (BT : branch_taken BC_GE (getr rg (14%bv : bv 5)) (getr rg (22%bv : bv 5)) = (left <? 4)).
  { change (getr rg (14%bv : bv 5)) with (getr rg 14).
    change (getr rg (22%bv : bv 5)) with (getr rg 22). rewrite R14, R22. unfold w64.
    apply na_bge_val. lia. }
  destruct (Z_lt_le_dec left 4) as [Hlt | Hge].
  - (* the walk ends: rc := 0 and the exit *)
    eapply (SRr_step SEGS pa_wx W3); [reflexivity | |].
    { rewrite restrict_mkst_fx. eapply step_branch_tk_gen; [exact na_fetch_bge | exact na_ecall_bge | exact na_dec_bge |].
      rewrite BT. apply Z.ltb_lt. exact Hlt. }
    intros md' Hsame. rewrite (same_but_materialized_wvb md3 md' Hsame). rewrite unrestrict_mkst_mrestrict.
    change (bv_signed (0x4c%bv : bv 13)) with 0x4c. unfold btgt. rewrite (na_pc_addw NA_bge 0x4c) by (unfold NA_bge, AF_nl_talk; lia).
    change (NA_bge + 0x4c) with NT_adone.
    eapply (SRr_step SEGS pa_wx W3); [reflexivity | |].
    { rewrite restrict_mkst_fx. eapply step_addi; [exact na_fetch_rc0 | exact na_ecall_rc0 | exact na_dec_rc0]. }
    intros md'' Hsame2. rewrite (same_but_materialized_wvb _ md'' Hsame2). rewrite unrestrict_mkst_mrestrict.
    replace (bv_eqb (27%bv : bv 5) 0) with false by reflexivity.
    rewrite (na_pc_addw NT_adone 4) by (unfold NT_adone, AF_nl_talk; lia).
    eapply (SRr_step SEGS pa_wx W3); [reflexivity | |].
    { rewrite restrict_mkst_fx. eapply step_jal_x0; [exact na_fetch_jx | exact na_ecall_jx | exact na_dec_jx]. }
    intros md3' Hsame3. rewrite (same_but_materialized_wvb _ md3' Hsame3). rewrite unrestrict_mkst_mrestrict.
    change (bv_signed (0x1c%bv : bv 21)) with 0x1c. unfold btgt. rewrite (na_pc_addw (NT_adone + 4) 0x1c) by (unfold NT_adone, AF_nl_talk; lia).
    change (NT_adone + 4 + 0x1c) with NT_exit.
    set (rg2 := regupd rg 27 (v_addi (getr rg 0) (bv_signed (0%bv : bv 12)))).
    assert (G27 : getr rg2 27 = w64 0) by (subst rg2; getr_resolve; reflexivity).
    pose proof HCm as (_ & (Q2 & Q8 & Q9 & Q18 & Q21 & Q24 & Q3 & Q4) & _).
    cbn [ms_regs mkst] in Q2, Q8, Q9, Q18, Q21, Q24, Q3, Q4.
    apply (na_exit POST cx fp k2 ly3 S3 W3 _ _ c rest bs HX HB).
    + apply na_core_md. apply na_core_md. apply na_core_md.
      apply (na_core_ms cx fp k2 ly3 S3 W3 _ _ md3 c rest bs HCm); [reflexivity|].
      cbn [ms_regs mkst]. unfold nt_regs. cbn [ms_regs mkst]. subst rg2. rewrite !getr_other by reg_neq_tac. tauto.
    + repeat split; reflexivity.
    + exact G27.
    + rewrite (na_as_small_eq f c p left a) in HM by lia. rewrite HM. exact HBF.
  - (* the next attribute: back to the loop head *)
    eapply (SRr_step SEGS pa_wx W3); [reflexivity | |].
    { rewrite restrict_mkst_fx. eapply step_branch_ft_gen; [exact na_fetch_bge | exact na_ecall_bge | exact na_dec_bge |].
      rewrite BT. apply Z.ltb_ge. exact Hge. }
    intros md' Hsame. rewrite (same_but_materialized_wvb md3 md' Hsame). rewrite unrestrict_mkst_mrestrict.
    rewrite (na_pc_addw NA_bge 4) by (unfold NA_bge, AF_nl_talk; lia).
    eapply (SRr_step SEGS pa_wx W3); [reflexivity | |].
    { rewrite restrict_mkst_fx. eapply step_jal_x0; [exact na_fetch_loop | exact na_ecall_loop | exact na_dec_loop]. }
    intros md'' Hsame2. rewrite (same_but_materialized_wvb _ md'' Hsame2). rewrite unrestrict_mkst_mrestrict.
    change (bv_signed (0x1ffec4%bv : bv 21)) with (-0x13c). unfold btgt.
    rewrite (na_pc_addw (NA_bge + 4) (-0x13c)) by (unfold NA_bge, AF_nl_talk; lia).
    change (NA_bge + 4 + -0x13c) with NT_aloop.
    apply (K1 k2 ly3 S3 W3 _ _ c rest bs p left a).
    split; [apply na_core_md; apply na_core_md; apply (na_core_ms cx fp k2 ly3 S3 W3 _ _ md3 c rest bs HCm); [reflexivity | exact (proj1 (proj2 HCm))]|].
    split; [apply (na_slots_ms cx W3 _ _ HSm); reflexivity|].
    split; [repeat split; reflexivity|].
    cbn [ms_regs ms_mem mkst].
    split; [exact R26|]. split; [exact R22|]. split; [exact R20|]. split; [exact R13|]. split; [exact R14|].
    split; [exact Hp0|]. split; [exact Hge|]. split; [exact Hpl|]. split; [exact (Hfu Hge)|].
    split; [exact HM | exact HBF].
Qed.

(* ==========================================================================
   5. The geometry of a cut, and the symbolic states built from it
   ========================================================================== *)

Lemma na_fsz : fs_frame_bytes NT_CID = 32768.
Proof. reflexivity. Qed.

Lemma na_reg_u : forall (rg : bvmap 5 word) (r : bv 5) v, getr rg r = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (getr rg r) = v.
Proof. intros rg r v H Hv. rewrite H. unfold w64. apply unsigned_lit_small. exact Hv. Qed.

(* the frame, the stack, and the class-9 frame's place in the state *)
Lemma na_geom : forall cx fp k2 ly3 S3 W3 ms3 md3 c rest bs,
  nt_base SK B cx -> na_core cx fp k2 ly3 S3 W3 ms3 md3 c rest bs ->
  AR SEGS B ly3 S3 W3 (ms_mem ms3) md3 /\ In (NT_CID, fp) (frames S3) /\
  frame_addr ly3 NT_CID fp = nF cx fp /\
  4096 <= nF cx fp /\ nF cx fp + 32768 <= alloc_ceiling /\ nF cx fp mod 64 = 0 /\
  in_app (nF cx fp) 32768 /\
  alloc_ceiling + NL_TALK_AK <= spZ (n_regs cx) /\ spZ (n_regs cx) <= 2 ^ 47 /\ spZ (n_regs cx) mod 16 = 0 /\
  spZ (n_regs cx) - 208 <= n_sp1 cx <= spZ (n_regs cx) - 192 /\ n_sp1 cx mod 32 = 0 /\
  n_sp0 cx - n_STK cx <= spZ (n_regs cx) - NL_TALK_AK /\ spZ (n_regs cx) <= n_sp0 cx.
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 c rest bs HB HC.
  pose proof HC as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HJB & _).
  pose proof HJB as (_ & _ & _ & Hfrs & _ & Hfa & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
  assert (Hin : In (NT_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 NT_CID fp HAR Hin) as (Hf1 & Hf2 & Hf3).
  destruct (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 NT_CID fp HAR Hin) as (Ha64 & _).
  pose proof HB as (HPRE & _). pose proof HPRE as (HJc & _ & _ & _ & _ & _ & _ & H16 & Hwlo & Hwhi & _).
  destruct (ajournal_gx_row SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (R1 & R2 & R3 & R4).
  pose proof (Hfa NT_CID fp) as EF. rewrite na_fsz in *. unfold nF.
  assert (Hsp : 0 <= spZ (n_regs cx) - NL_TALK_AFRAME) by (unfold NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK in *; lia).
  destruct (nt_sp1_range (spZ (n_regs cx)) Hsp H16) as (S1 & S2 & S3').
  unfold n_sp1. rewrite <- EF.
  unfold NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK in *.
  split; [exact HAR|]. split; [exact Hin|]. split; [reflexivity|].
  split; [lia|]. split; [lia|]. split; [exact Ha64|]. split; [exact Hf3|].
  split; [lia|]. split; [lia|]. split; [exact H16|]. split; [lia|]. split; [exact S2|].
  split; lia.
Qed.

(* the shadow of the receive buffer is zero: every range of it is addressable *)
Lemma na_ra_buf : forall cx fp W3 ms3 q k,
  nt_frame_shadow cx fp 0 W3 ms3 -> nF cx fp mod 64 = 0 ->
  nBUF cx fp <= q -> q + k <= nBUF cx fp + NT_BUFLEN ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF q k.
Proof.
  intros cx fp W3 ms3 q k (_ & HZ & _) H64 Hq Hk x Hx. exists 0. split; [|left; reflexivity].
  unfold nBUF, NT_BUFOFF, NT_BUFLEN, nSH, shadow_of_addr in *.
  set (F := nF cx fp) in *.
  assert (E : SHADOW_OFF + x / 8 = SHADOW_OFF + F / 8 + 4 + (x / 8 - F / 8 - 4)) by lia.
  rewrite E. apply HZ. pose proof (Z.div_mod F 64 ltac:(lia)). split.
  - assert (F / 8 + 4 <= x / 8) by (apply Z.div_le_lower_bound; lia). lia.
  - assert (x / 8 < F / 8 + 4 + 2048) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* the region of the spill slots *)
Lemma na_spill_ok : forall E (W : world SEGS) m sp1 al aln kd kdn,
  bv_unsigned (ew E 9) = sp1 -> 0 <= sp1 -> sp1 + 64 <= 2 ^ 64 ->
  ew E 34 = w64 al -> ew E 35 = w64 aln -> ew E 36 = w64 kd -> ew E 37 = w64 kdn ->
  0 <= al < 2 ^ 64 -> 0 <= aln < 2 ^ 64 -> 0 <= kd < 2 ^ 64 -> 0 <= kdn < 2 ^ 64 ->
  rdword (aview SEGS (w_H W) m) (sp1 + 8) = Some al -> rdword (aview SEGS (w_H W) m) (sp1 + 16) = Some aln ->
  rdword (aview SEGS (w_H W) m) (sp1 + 48) = Some kd -> rdword (aview SEGS (w_H W) m) (sp1 + 56) = Some kdn ->
  region_ok SEGS E (rdW W m) na_spill.
Proof.
  intros E W m sp1 al aln kd kdn H9 H0 H64 E34 E35 E36 E37 R1 R2 R3 R4 V1 V2 V3 V4.
  unfold region_ok, na_spill. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite H9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E _ sp1 8 8 (SOff 34 0) al); [exact (sv_off0 E 34 al E34) | cbn; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W) m _ _ V1).
  - apply (chunk_ok_val SEGS E _ sp1 16 8 (SOff 35 0) aln); [exact (sv_off0 E 35 aln E35) | cbn; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W) m _ _ V2).
  - apply (chunk_ok_val SEGS E _ sp1 48 8 (SOff 36 0) kd); [exact (sv_off0 E 36 kd E36) | cbn; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W) m _ _ V3).
  - apply (chunk_ok_val SEGS E _ sp1 56 8 (SOff 37 0) kdn); [exact (sv_off0 E 37 kdn E37) | cbn; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W) m _ _ V4).
Qed.

(* the region of an attribute's 4-byte header *)
Lemma na_hdr_ok : forall E (m : word -> option byte) (n la lt : nat) p l t,
  bv_unsigned (ew E n) = p -> 0 <= p -> p + 4 <= 2 ^ 64 ->
  ew E la = w64 l -> ew E lt = w64 t -> 0 <= l < 65536 -> 0 <= t < 65536 ->
  val_mem SEGS m p 2 l -> val_mem SEGS m (p + 2) 2 t ->
  region_ok SEGS E m (na_hdr n la lt).
Proof.
  intros E m n la lt p l t Hn H0 H4 El Et Rl Rt Vl Vt.
  unfold region_ok, na_hdr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Hn. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E _ p 0 2 (SOff la 0) l); [exact (sv_off0 E la l El) | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Vl.
  - apply (chunk_ok_val SEGS E _ p 2 2 (SOff lt 0) t); [exact (sv_off0 E lt t Et) | cbn; lia | cbn; lia |].
    exact Vt.
Qed.

(* the shadow entry of an attribute's header *)
Lemma na_shent_ok : forall E (W : world SEGS) m (n : nat) p,
  ew E 21 = w64 SHADOW_OFF -> ew E n = w64 p -> 0 <= p -> p + 4 < kLowMemEnd \/ kHighMemBeg <= p ->
  p + 4 < 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF p 4 ->
  shent_ok SEGS na_Bx E (rdW W m) (mkSHE n 0 4).
Proof.
  intros E W m n p E21 En H0 Happ H47 HRA. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  assert (UB : U E na_Bx = SHADOW_OFF) by (unfold na_Bx; apply U_atom; [exact E21 | unfold SHADOW_OFF; lia]).
  assert (UA : U E (SOff n 0) = p) by (apply U_atom; [exact En | lia]).
  rewrite UB, UA. split.
  - rewrite Z.add_0_r, Z.sub_0_r. rewrite <- (aview_rd_of SEGS). exact HRA.
  - intros x Hx. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
    unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* ==========================================================================
   6. The two copy_attr calls (+0x38c on the alias buffer, +0x3f4 on the kind buffer)
   ========================================================================== *)

(* the 16-bit length a Pre names is the one the chunk holds *)
Lemma na_u16_same : forall (m : word -> option byte) a l l',
  val_mem SEGS m a 2 l -> val_mem SEGS m a 2 l' -> 0 <= l < 65536 -> 0 <= l' < 65536 -> l = l'.
Proof.
  intros m a l l' H H' R R'.
  destruct (mbyte SEGS m (a + Z.of_nat 0)) as [b0|] eqn:E0; [|pose proof (H 0%nat ltac:(lia)); congruence].
  destruct (mbyte SEGS m (a + Z.of_nat 1)) as [b1|] eqn:E1; [|pose proof (H 1%nat ltac:(lia)); congruence].
  assert (X : forall v, val_mem SEGS m a 2 v -> 0 <= v < 65536 -> bytes_le_to_Z [b0; b1] = v).
  { intros v Hv Rv. apply (lw_bytes_of_vals 2 [b0; b1] v eq_refl ltac:(cbn; lia)).
    intros kk Hkk. destruct kk as [|[|kk]]; [| |lia]; cbn [nth_error].
    - rewrite <- E0. exact (Hv 0%nat ltac:(lia)).
    - rewrite <- E1. exact (Hv 1%nat ltac:(lia)). }
  rewrite <- (X l H R), <- (X l' H' R'). reflexivity.
Qed.

(* a byte of a byte list in memory is present *)
Lemma na_abytes_some : forall (m : word -> option byte) base bs b,
  abytes SEGS m base bs -> base <= b < base + Z.of_nat (length bs) -> mbyte SEGS m b <> None.
Proof.
  intros m base bs b (H0 & H1 & H2) Hb.
  pose proof (H2 (Z.to_nat (b - base)) ltac:(lia)) as E.
  replace (base + Z.of_nat (Z.to_nat (b - base))) with b in E by lia.
  rewrite E. destruct (nth_error bs (Z.to_nat (b - base))) eqn:En; [discriminate|].
  apply nth_error_None in En. lia.
Qed.

(* the shadow hull of a range of the receive buffer lies in the frame's 2084 shadow bytes *)
Lemma na_hull_buf : forall cx fp v W3 ms3 x n,
  nt_frame_shadow cx fp v W3 ms3 -> nF cx fp mod 64 = 0 ->
  nBUF cx fp <= x -> x + n <= nBUF cx fp + NT_BUFLEN -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms3)) x n.
Proof.
  intros cx fp v W3 ms3 x n (H1 & H2 & H3) H64 Hx Hxn Hn s Hs.
  unfold shadow_addr in Hs. unfold nBUF, NT_BUFOFF, NT_BUFLEN in *. unfold nSH, shadow_of_addr in H1, H2, H3.
  set (F := nF cx fp) in *. clearbody F.
  assert (Lo : SHADOW_OFF + F / 8 <= s) by (unfold SHADOW_OFF in *; lia).
  assert (Hi : s < SHADOW_OFF + F / 8 + 2084) by (unfold SHADOW_OFF in *; lia).
  destruct (Z_lt_le_dec (s - (SHADOW_OFF + F / 8)) 4) as [A|A].
  - replace s with (SHADOW_OFF + F / 8 + (s - (SHADOW_OFF + F / 8))) by lia.
    rewrite H1 by lia. discriminate.
  - destruct (Z_lt_le_dec (s - (SHADOW_OFF + F / 8)) 2052) as [A'|A'].
    + replace s with (SHADOW_OFF + F / 8 + 4 + (s - (SHADOW_OFF + F / 8) - 4)) by lia.
      rewrite H2 by lia. discriminate.
    + replace s with (SHADOW_OFF + F / 8 + 2052 + (s - (SHADOW_OFF + F / 8) - 2052)) by lia.
      rewrite H3 by lia. discriminate.
Qed.

(* g_nl is image bytes of a writable segment, outside the runtime's statics *)
Lemma na_gnl_img : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ in_roP SEGS PCAP_RLO PCAP_RHI a.
Proof.
  intros a Ha. unfold NK_SIZE in Ha. split; [|split].
  - rewrite HSEGS. pose proof tfib_shape as Hsh.
    destruct (nth_error tfibsegs 3) as [sg|] eqn:Es.
    + exists sg. split; [exact (nth_error_In _ _ Es)|].
      assert (Hm : nth_error (map (fun s => (seg_lo s, seg_hi s, seg_writable s)) tfibsegs) 3 =
                   Some (seg_lo sg, seg_hi sg, seg_writable sg)) by (rewrite nth_error_map, Es; reflexivity).
      rewrite Hsh in Hm. cbn [nth_error] in Hm. injection Hm as E1 E2 E3. unfold seg_lo, seg_hi in *.
      unfold LA_G_NL in Ha. lia.
    + exfalso. assert (Hn : nth_error (map (fun s => (seg_lo s, seg_hi s, seg_writable s)) tfibsegs) 3 = None)
        by (rewrite nth_error_map, Es; reflexivity). rewrite Hsh in Hn. discriminate.
  - rewrite (ts_owned B TB). intro HX. apply Exists_exists in HX as (r & Hr & Hin).
    assert (Hown : forallb (fun r : Z * Z => (LA_G_NL + 271992 <=? fst r) || (fst r + snd r <=? LA_G_NL))
                     Tfib_owned_static = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in Hown. specialize (Hown r Hr).
    apply orb_prop in Hown as [H1|H1]; apply Z.leb_le in H1; unfold in_zr in Hin; lia.
  - rewrite HSEGS. apply LA_G_not_ro. apply inG_LA_G_NL. exact Ha.
Qed.

(* an off-image byte is not a read-only byte *)
Lemma na_not_ro_off : forall a, ~ in_img SEGS a -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a.
Proof.
  intros a Hni [(sg & Hsg & _ & Hr) | Hr]; apply Hni; [exists sg; split; [exact Hsg | exact Hr] | exact (RELRO_IMG a Hr)].
Qed.

Lemma na_aarg : forall (rg : bvmap 5 word) (r : bv 5) i v, Z_to_bv 5 (10 + i) = r ->
  getr rg r = w64 v -> 0 <= v < 2 ^ 64 -> aarg rg i = v.
Proof. intros rg r i v Hr Hg Hv. unfold aarg, argZ. rewrite Hr, Hg. unfold w64. apply unsigned_lit_small. exact Hv. Qed.

Lemma na_aivl_in : forall p n a, inFP [aivl p n] a -> p <> 0 /\ p <= a < p + n.
Proof.
  intros p n a (r & [<- | []] & Hr). unfold aivl in Hr. cbn [fst snd] in Hr.
  destruct (Z.eqb_spec p 0); [lia | split; [assumption | lia]].
Qed.

Lemma na_in_aivl : forall p n a, p <> 0 -> p <= a < p + n -> inFP [aivl p n] a.
Proof.
  intros p n a Hp Ha. exists (aivl p n). split; [left; reflexivity|]. unfold aivl. cbn [fst snd].
  destruct (Z.eqb_spec p 0); [contradiction | lia].
Qed.

(* THE CALL: copy_attr (0x89438) on the attribute at nBUF + aoff, into the buffer (out, n); (out', n') is the other
   buffer. The callee's Pre comes from nt_base and the cut; its Post gives the cut back, the copied text in the
   buffer, and the other buffer as it was. *)
Lemma na_call_gen : forall cx fp k2 ly3 S3 W3 rg mm md3 c rest bs aoff retk out n o out' n' o' Q,
  nt_base SK B cx ->
  na_core cx fp k2 ly3 S3 W3 (mkst rg (w64 (BASE + AF_copy_attr)) mm (seg_rom SEGS)) md3 c rest bs ->
  na_buf (n_m cx) (rdW W3 mm) out n o -> na_buf (n_m cx) (rdW W3 mm) out' n' o' ->
  getr rg 10 = w64 (nBUF cx fp + aoff) -> getr rg 11 = w64 out -> getr rg 12 = w64 n ->
  getr rg 1 = w64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  0 <= out < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  0 <= aoff -> 4 <= rd16 c aoff -> aoff + rd16 c aoff <= Z.of_nat (length c) ->
  (forall a, inFP [aivl out n] a -> inFP (n_Wr cx) a) ->
  (forall a, inFP [aivl out' n'] a -> inFP (n_Wr cx) a) ->
  (out <> 0 -> apart_frame (n_regs cx) NL_TALK_AK out n /\ apart_gnl LA_G_NL out n) ->
  (out <> 0 -> 1 <= n -> achk SEGS (n_m cx) out n) ->
  (out' <> 0 -> apart (as_errno B) 4 out' n') ->
  (out' <> 0 -> apart_frame (n_regs cx) NL_TALK_AK out' n') ->
  (out <> 0 -> 1 <= n -> out' <> 0 -> 1 <= n' -> apart out n out' n') ->
  (out' <> 0 -> 1 <= n' -> achk SEGS (n_m cx) out' n') ->
  (forall a, inFP (n_Wr cx) a -> a < kLowMemEnd \/ kHighMemBeg <= a) ->
  (forall ly2 S2 W2 regs2 mem2 md2,
     na_core cx fp k2 ly2 S2 W2 (mkst regs2 (w64 (BASE + retk)) mem2 (seg_rom SEGS)) md2 c rest bs ->
     aregs_preserved rg regs2 ->
     (forall a, n_sp1 cx <= a < spZ (n_regs cx) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mm a) ->
     na_buf (n_m cx) (rdW W2 mem2) out n (Some (slice c (aoff + RTA_HDR) (rd16 c aoff - RTA_HDR))) ->
     na_buf (n_m cx) (rdW W2 mem2) out' n' o' ->
     SRr SEGS W2 (mkCfg (mkst regs2 (w64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (mkst rg (w64 (BASE + AF_copy_attr)) mm (seg_rom SEGS)) md3) Q.
Proof.
  intros cx fp k2 ly3 S3 W3 rg mm md3 c rest bs aoff retk out n o out' n' o' Q
    HB HC HBo HBo' G10 G11 G12 G1 Hrk Hrk2 Ho Hn Ha0 Hl4 Hlc P1 P2 P3 P5 P6 P7 P8 P9 HWapp KONT.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof pa_B_ok as (HB0 & HB1 & _). assert (HBlo : 65536 <= BASE) by exact pa_base_lo.
  pose proof (na_geom cx fp k2 ly3 S3 W3 _ md3 c rest bs HB HC) as
    (HAR3 & Hin9 & Hfa9 & HF4 & HFc & HF64 & HFapp & Hsp & Hsp47 & Hsp16 & Hsp1 & Hsp132 & Hwin1 & Hwin2).
  cbn [ms_mem ms_regs mkst] in HAR3.
  unfold NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK in Hsp, Hwin1.
  pose proof HB as (HPRE & _ & HNP & _).
  pose proof HPRE as (HJc & HGok & _ & _ & _ & Hgp & Htp & _ & _ & _ & Hev & _ & Hajw & Hro).
  destruct HNP as (kbs & req & _ & _ & _ & _ & _ & _ & _ & HERR & _).
  pose proof HERR as (_ & _ & _ & _ & HERRg).
  pose proof HC as (HJ & HR & HSV & HH & HS0 & HA1 & HA2 & HA3 & HFS & HJB & HK & HG & HGO & HOW & HRC & HBY & HBL & HCL & HBUF).
  cbn [ms_mem ms_regs mkst] in HJ, HR, HSV, HH, HS0, HA1, HA2, HA3, HFS, HK, HG, HBY, HBUF.
  pose proof HR as (R2 & R8 & R9 & R18 & R21 & R24 & R3 & R4). cbn [ms_regs mkst] in R2, R8, R9, R18, R21, R24, R3, R4.
  pose proof HJB as (Hk2 & Hperm & Hsetfs & Hfrs & Hnin & Hfa & Hwit & Hfds & Hfs).
  pose proof HK as (HKA & HROD3 & _).
  pose proof (aj_window_bounds SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (Hw0 & _ & _ & _).
  destruct (frame_facts B ly3 S3 (aview SEGS (w_H W3) mm) NT_CID fp (proj1 HAR3) Hin9) as (Hc9 & Hfp9 & _).
  destruct (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (Rl3 & Rh3).
  destruct (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (Rlc & Rhc).
  assert (Hblk : forall b m, In (b, m) (ablocks B (n_lyc cx) (n_Sc cx)) -> In (b, m) (ablocks B ly3 S3))
    by (intros b0 m0 Hb0; exact (Permutation_in _ (Permutation_sym Hperm) Hb0)).
  assert (Hfrm : forall c0 q0, In (c0, q0) (frames (n_Sc cx)) -> In (c0, q0) (frames S3))
    by (intros c0 q0 Hq; rewrite Hfrs; right; exact Hq).
  assert (Hlen0 : (length c <= 4096)%nat) by (unfold NL_CHUNK_MAX in HCL; exact HCL).
  pose proof (nt_rd16_range c aoff Ha0 ltac:(lia)) as Hlr.
  destruct (nt_attr_pre_bytes SEGS (rdW W3 mm) (nBUF cx fp) c rest aoff HBY Ha0 ltac:(unfold RTA_HDR; lia) Hlc)
    as (Hau & Hpay & Hpayl).
  assert (Usp : spZ rg = n_sp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  assert (A0 : aarg rg 0 = nBUF cx fp + aoff) by (apply (na_aarg rg 10%bv); [apply bv_eq; reflexivity | exact G10 | unfold nBUF, NT_BUFOFF; lia]).
  assert (A1 : aarg rg 1 = out) by (apply (na_aarg rg 11%bv); [apply bv_eq; reflexivity | exact G11 | exact Ho]).
  assert (A2 : aarg rg 2 = n) by (apply (na_aarg rg 12%bv); [apply bv_eq; reflexivity | exact G12 | exact Hn]).
  assert (EWr : copy_attr_awr rg (rdW W3 mm) = [aivl out n]) by (unfold copy_attr_awr; rewrite A1, A2; reflexivity).
  (* the buffers are not bytes of the class-9 frame *)
  assert (NB : forall a, inFP [aivl out n] a -> ~ aside_rng (n_lyc cx) NT_CID fp a).
  { intros a Ha. destruct (na_aivl_in out n a Ha) as (Hout & Hai).
    pose proof (proj1 (P5 Hout ltac:(lia))) as Hamr. unfold amem_range in Hamr.
    apply (ajw_not_side SK SEGS B LAWS pa_img_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HGok HJc Hc9 Hfp9 Hnin).
    - exact (Hajw a (P1 a Ha)).
    - unfold kLowMemEnd, kHighMemBeg in *; lia. }
  (* the attribute is in the class-9 frame *)
  assert (Hfrm_attr : nF cx fp + 32 <= nBUF cx fp + aoff /\ nBUF cx fp + aoff + rd16 c aoff <= nF cx fp + 4128)
    by (unfold nBUF, NT_BUFOFF; lia).
  pose proof CA as CA'. unfold copy_attr_acontract, aleaf_rd in CA'.
  assert (HCFG : mkCfg (mkst rg (w64 (BASE + AF_copy_attr)) mm (seg_rom SEGS)) md3 = cfg_at SEGS COPY_ATTR_A rg mm md3)
    by (unfold cfg_at; rewrite (lv_text LV); reflexivity).
  rewrite HCFG. clear HCFG.
  eapply SRr_bind;
    [ apply (CA' (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx)
               (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 mm md3 k2 rg) | ].
  { (* apre *)
    unfold apre. rewrite EWr.
    split; [exact HJ|]. split; [exact HGok|]. split; [exact HROD3|].
    split; [rewrite G1; apply ret_ok_codeptr_v; lia|].
    split; [unfold raZ; rewrite G1; unfold w64; rewrite unsigned_lit_small by lia; lia|].
    split; [rewrite R3; exact Hgp|]. split; [rewrite R4; exact Htp|].
    split; [rewrite Usp; lia|]. split; [rewrite Usp; unfold NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK in *; lia|].
    split; [rewrite Usp; lia|]. split; [rewrite Hk2; lia|].
    split; [apply Forall_nil|].
    split.
    - intros a Ha. apply (ajw_mono B _ _ _ _ _ _ _ _ (n_lyc cx) (n_Sc cx) (n_own cx) ly3 S3 ((NT_CID, fp) :: n_own cx) a
        (Hajw a (P1 a Ha)) Hblk (fun x Hx => or_intror Hx) Hfa).
    - intros a Ha. exact (Hro a (P1 a Ha)). }
  { (* the read set: the attribute's bytes, in the class-9 frame *)
    intros a (l' & Hl' & Hl'r & Ha'). rewrite A0 in Hl', Ha'.
    assert (El : l' = rd16 c aoff) by (apply (na_u16_same _ _ _ _ Hl' Hau); unfold RTA_HDR in *; lia).
    right; right; right. exists NT_CID, fp. split; [exact Hin9|].
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa9, na_fsz. unfold rd_ivl in Ha'. lia. }
  { (* copy_attr's Pre *)
    unfold copy_attr_apre. rewrite A0, A1, A2.
    change (ard SEGS (rdW W3 mm)) with (aview SEGS (w_H W3) mm).
    exists (rd16 c aoff), (slice c (aoff + RTA_HDR) (rd16 c aoff - RTA_HDR)).
    split; [exact Hau|]. split; [unfold RTA_HDR; lia|]. split; [exact Hpay|]. split; [exact Hpayl|].
    split; [unfold nBUF, NT_BUFOFF; lia|].
    split; [unfold amem_range, in_app, ASAN_CEIL in *; unfold kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *; lia|].
    split; [unfold apart_frame; rewrite Usp; unfold NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK in *; lia|].
    split; [apply (na_ra_buf cx fp W3 (mkst rg (w64 (BASE + AF_copy_attr)) mm (seg_rom SEGS))); [exact HFS | exact HF64 | lia | unfold NT_BUFLEN, nBUF, NT_BUFOFF in *; lia]|].
    split; [apply (na_ra_buf cx fp W3 (mkst rg (w64 (BASE + AF_copy_attr)) mm (seg_rom SEGS))); [exact HFS | exact HF64 | unfold RTA_HDR; lia | unfold RTA_HDR, NT_BUFLEN, nBUF, NT_BUFOFF in *; lia]|].
    split; [intros Hp; apply (na_hull_buf cx fp 0 W3 (mkst rg (w64 (BASE + AF_copy_attr)) mm (seg_rom SEGS))); [exact HFS | exact HF64 | unfold RTA_HDR; lia | unfold RTA_HDR, NT_BUFLEN, nBUF, NT_BUFOFF in *; lia | exact Hp]|].
    split.
    { intros b0 Hb0. unfold aview. intro Hnone.
      apply (na_abytes_some (rdW W3 mm) (nBUF cx fp) (c ++ rest) b0 HBY).
      - unfold NT_BUFLEN in HBL. rewrite HBL. unfold nBUF, NT_BUFOFF in *. lia.
      - destruct (mbyte SEGS (rdW W3 mm) b0); [discriminate | reflexivity]. }
    intros Hout Hn1.
    destruct (P3 Hout) as (Hapf & _). destruct (P5 Hout Hn1) as (Hamr & HRAo & HHo).
    split; [unfold apart_frame in Hapf |- *; rewrite Usp; unfold NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK in *; lia|].
    split.
    { unfold apart. destruct (Z_le_gt_dec (out + n) (nBUF cx fp + aoff + RTA_HDR)) as [Hx|Hx]; [left; exact Hx|].
      destruct (Z_le_gt_dec (nBUF cx fp + aoff + RTA_HDR + (rd16 c aoff - RTA_HDR)) out) as [Hy|Hy]; [right; exact Hy|].
      exfalso.
      apply (NB (Z.max out (nBUF cx fp + aoff + RTA_HDR))
               (na_in_aivl out n (Z.max out (nBUF cx fp + aoff + RTA_HDR)) Hout ltac:(unfold RTA_HDR in *; lia))).
      left. unfold in_zr, frame_rng. cbn [fst snd]. fold (nF cx fp). rewrite na_fsz. unfold RTA_HDR in *. lia. }
    split; [exact (proj1 HBo Hout Hn1)|].
    split; [exact Hamr|].
    pose proof HJc as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HARc & _).
    assert (HFM : fmiss (n_lyc cx) (n_Sc cx) (fun a => n_E cx a \/ aside_rng (n_lyc cx) NT_CID fp a)).
    { apply fmiss_or.
      - apply (fmiss_app SEGS B LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) _ HARc).
        exact HWapp.
      - exact (fmiss_side SEGS B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) NT_CID fp HARc Hc9 Hfp9 Hnin). }
    change (ard SEGS (n_m cx)) with (aview SEGS (w_H (n_W cx)) (n_memc cx)) in HRAo, HHo.
    apply (shadow_transport SEGS B LAWS TB pa_img_range (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx)
      ly3 S3 W3 mm md3 _ _ _ out n HARc HAR3 ltac:(rewrite Rl3, Rlc; reflexivity) ltac:(rewrite Rh3, Rhc; reflexivity)
      Hblk HKA HFM ltac:(lia)).
    - intros x Hx. apply (sclass_of_ajw SK SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x HGok HJc).
      + exact (Hajw x (P1 x (na_in_aivl out n x Hout Hx))).
      + unfold amem_range in Hamr. unfold kLowMemEnd, kHighMemBeg in *; lia.
    - exact HRAo.
    - exact (HHo). }
  (* the return *)
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & HAP & Hfr2 & Hfd2 & Hfs2 & HKC & _ & Hsf2 & Hperm2 & HPOST).
  subst c2. rewrite G1. rewrite Z.add_0_r in HJ2.
  rewrite EWr, Usp in HKC. unfold copy_attr_apost in HPOST. rewrite A0, A1, A2 in HPOST.
  assert (Hsp1c : alloc_ceiling <= n_sp1 cx - COPY_ATTR_AK)
    by (unfold NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK in *; lia).
  (* the words of nl_talk's own frame *)
  assert (KS : forall a, n_sp1 cx <= a < spZ (n_regs cx) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mm a).
  { intros a Ha. apply (proj1 HKC a); [lia | lia |].
    intros HE. destruct (na_aivl_in out n a HE) as (Hout & Hai). destruct (P3 Hout) as (Hapf & _).
    unfold apart_frame, NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK in Hapf. lia. }
  (* the class-9 frame's bytes and its shadow *)
  assert (KF : forall a, nF cx fp <= a < nF cx fp + 32768 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mm a).
  { intros a Ha. apply (proj1 (proj2 (proj2 (proj2 HKC))) NT_CID fp a Hin9).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa9, na_fsz. lia.
    - intros HE. apply (NB a HE). left. unfold in_zr, frame_rng. cbn [fst snd]. fold (nF cx fp). rewrite na_fsz. lia. }
  assert (KFS : forall i, 0 <= i < 4096 -> aview SEGS (w_H W2) mem2 (nSH cx fp + i) = aview SEGS (w_H W3) mm (nSH cx fp + i)).
  { intros i Hi. apply (proj1 (proj2 (proj2 (proj2 HKC))) NT_CID fp (nSH cx fp + i) Hin9).
    - right. unfold in_zr. cbn [fst snd]. rewrite Hfa9, na_fsz. unfold nSH, shadow_of_addr, shadow_addr. lia.
    - intros HE. apply (NB _ HE). right; left. unfold in_zr. cbn [fst snd]. fold (nF cx fp). rewrite na_fsz.
      unfold nSH, shadow_of_addr, shadow_addr. lia. }
  (* the other buffer *)
  assert (KB' : forall a, inFP [aivl out' n'] a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mm a).
  { intros a Ha. destruct (na_aivl_in out' n' a Ha) as (Hout' & Hai').
    pose proof (proj1 (P9 Hout' ltac:(lia))) as Hamr'. unfold amem_range in Hamr'.
    pose proof (P7 Hout') as Hapf'. pose proof (P6 Hout') as Herr'.
    apply (akept_akb_gx SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ HKC).
    - apply (ajw_akb SK SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx)
        ly3 S3 _ _ a HGok HJc (Hajw a (P2 a Ha))).
      + unfold apart_frame, NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK in *. lia.
      + unfold kLowMemEnd, kHighMemBeg in *; lia.
      + unfold apart in Herr'. lia.
      + rewrite Rl3, Rlc. reflexivity.
      + rewrite Rh3, Rhc. reflexivity.
      + exact Hblk.
      + exact Hfrm.
      + exact Hfa.
    - intros HE. destruct (na_aivl_in out n a HE) as (Hout & Hai).
      pose proof (P8 Hout ltac:(lia) Hout' ltac:(lia)) as Hap. unfold apart in Hap. lia. }
  (* g_nl *)
  assert (KG : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mm a).
  { intros a Ha. destruct (na_gnl_img a Ha) as (Hi & Hno & _).
    apply (proj1 (proj2 (proj2 HKC)) a Hi Hno).
    - unfold apart_gnl in HERRg. lia.
    - intros HE. destruct (na_aivl_in out n a HE) as (Hout & Hai). destruct (P3 Hout) as (_ & Hag).
      unfold apart_gnl in Hag. lia. }
  assert (Hfa2 : forall c0 p0, frame_addr ly2 c0 p0 = frame_addr (n_lyc cx) c0 p0).
  { intros c0 p0.
    rewrite (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c0 p0 HJ2)).
    rewrite (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c0 p0 HJc)).
    reflexivity. }
  assert (Hrng : forall a i, n_sp1 cx <= a -> a + 8 <= spZ (n_regs cx) -> 0 <= i < 8 ->
    aview SEGS (w_H W2) mem2 (a + i) = aview SEGS (w_H W3) mm (a + i)) by (intros a i H1 H2 Hi; apply KS; lia).
  assert (Frng : forall a i, nF cx fp <= a -> a + 8 <= nF cx fp + 32768 -> 0 <= i < 8 ->
    aview SEGS (w_H W2) mem2 (a + i) = aview SEGS (w_H W3) mm (a + i)) by (intros a i H1 H2 Hi; apply KF; lia).
  set (ms3 := mkst rg (w64 (BASE + AF_copy_attr)) mm (seg_rom SEGS)) in *.
  apply (KONT ly2 S2 W2 regs2 mem2 md2).
  - unfold na_core. cbn [ms_mem ms_regs mkst].
    split; [exact HJ2|].
    split.
    { unfold nt_regs. cbn [ms_regs mkst].
      split; [rewrite <- R2; exact (HAP 2 ltac:(unfold acallee_saved; lia))|].
      split; [rewrite <- R8; exact (HAP 8 ltac:(unfold acallee_saved; lia))|].
      split; [rewrite <- R9; exact (HAP 9 ltac:(unfold acallee_saved; lia))|].
      split; [rewrite <- R18; exact (HAP 18 ltac:(unfold acallee_saved; lia))|].
      split; [rewrite <- R21; exact (HAP 21 ltac:(unfold acallee_saved; lia))|].
      split; [rewrite <- R24; exact (HAP 24 ltac:(unfold acallee_saved; lia))|].
      split; [rewrite <- R3; exact (HAP 3 ltac:(unfold acallee_saved; lia))|].
      rewrite <- R4; exact (HAP 4 ltac:(unfold acallee_saved; lia)). }
    split.
    { destruct HSV as (HS1 & HS2). split.
      - apply (na_nt_at_kept W3 W2 ms3 _ _ _ HS1). intros i Hi. apply Hrng; [lia | lia | exact Hi].
      - intros j Hj. apply (na_nt_at_kept W3 W2 ms3 _ _ _ (HS2 j Hj)). intros i Hi. apply Hrng; [lia | lia | exact Hi]. }
    split.
    { destruct HH as (H1 & H2 & H3 & H4). rewrite na_fsz in H4. unfold nt_header. rewrite na_fsz.
      split; [apply (na_nt_at_kept W3 W2 ms3 _ _ _ H1); intros i Hi; apply Frng; [lia | lia | exact Hi]|].
      split; [apply (na_nt_at_kept W3 W2 ms3 _ _ _ H2); intros i Hi; apply Frng; [lia | lia | exact Hi]|].
      split; [apply (na_nt_at_kept W3 W2 ms3 _ _ _ H3); intros i Hi; apply Frng; [lia | lia | exact Hi]|].
      apply (na_nt_at_kept W3 W2 ms3 _ _ _ H4); intros i Hi; apply Frng; [lia | lia | exact Hi]. }
    split.
    { destruct HS0 as (H1 & H2 & H3). unfold NS_KIND, NS_KINDN, NS_F in *.
      split; [apply (na_nt_at_kept W3 W2 ms3 _ _ _ H1); intros i Hi; apply Hrng; [lia | lia | exact Hi]|].
      split; [apply (na_nt_at_kept W3 W2 ms3 _ _ _ H2); intros i Hi; apply Hrng; [lia | lia | exact Hi]|].
      apply (na_nt_at_kept W3 W2 ms3 _ _ _ H3); intros i Hi; apply Hrng; [lia | lia | exact Hi]. }
    unfold NS_SH4, NS_FK, NS_FD in *.
    split; [apply (na_nt_at_kept W3 W2 ms3 _ _ _ HA1); intros i Hi; apply Hrng; [lia | lia | exact Hi]|].
    split; [apply (na_nt_at_kept W3 W2 ms3 _ _ _ HA2); intros i Hi; apply Hrng; [lia | lia | exact Hi]|].
    split; [apply (na_nt_at_kept W3 W2 ms3 _ _ _ HA3); intros i Hi; apply Hrng; [lia | lia | exact Hi]|].
    split.
    { destruct HFS as (H1 & H2 & H3). unfold nt_frame_shadow. cbn [ms_mem mkst].
      split; [intros i Hi; rewrite (KFS i ltac:(lia)); exact (H1 i Hi)|].
      split; [intros i Hi; rewrite <- Z.add_assoc, (KFS (4 + i) ltac:(lia)), Z.add_assoc; exact (H2 i Hi)|].
      intros i Hi; rewrite <- Z.add_assoc, (KFS (2052 + i) ltac:(lia)), Z.add_assoc; exact (H3 i Hi). }
    split.
    { unfold nt_jbk.
      split; [exact Hk2|]. split; [exact (Permutation_trans Hperm2 Hperm)|].
      split; [exact (set_fs_trans S3 S2 (n_Sc cx) Hsetfs Hsf2)|].
      split; [rewrite Hfr2; exact Hfrs|]. split; [exact Hnin|]. split; [exact Hfa2|]. split; [exact Hwit|].
      split; [rewrite Hfd2; exact Hfds | rewrite Hfs2; exact Hfs]. }
    split.
    { unfold nt_kept. split; [|split; [|intros a Ha; exact Ha]].
      - assert (Hsl : alloc_ceiling <= spZ (n_regs cx) - NL_TALK_AK)
          by (unfold NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK; lia).
        assert (Hsh : spZ (n_regs cx) <= 2 ^ 64) by lia.
        assert (Hsl1 : spZ (n_regs cx) - NL_TALK_AK <= n_sp1 cx - COPY_ATTR_AK)
          by (unfold NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK; lia).
        assert (Hsh1 : n_sp1 cx <= spZ (n_regs cx)) by lia.
        apply (akept_trans_ly SK SEGS B LAWS pa_segs_low (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) ly3 S3 W3 mm W2 mem2
          (spZ (n_regs cx) - NL_TALK_AK) (spZ (n_regs cx)) (n_sp1 cx - COPY_ATTR_AK) (n_sp1 cx)
          (fun a => n_E cx a \/ aside_rng (n_lyc cx) NT_CID fp a) (fun a => inFP [aivl out n] a)
          (fun a => n_E cx a \/ aside_rng (n_lyc cx) NT_CID fp a) Hsl Hsh HKA HKC Hsl1 Hsh1).
        + exact Hblk.
        + intros f0 Hf0. destruct f0 as [c0 q0]. exact (Hfrm c0 q0 Hf0).
        + exact Hfa.
        + intros a Ha; exact Ha.
        + intros a Ha. left. exact (P1 a Ha).
      - intros a Hro' Ho' He'.
        assert (Hi : in_img SEGS a)
          by (destruct Hro' as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (RELRO_IMG a Hr)]).
        rewrite (proj1 (proj2 (proj2 HKC)) a Hi Ho' He').
        + exact (HROD3 a Hro' Ho' He').
        + intros HE. exact (Hro a (P1 a HE) Hro'). }
    split.
    { destruct HG as (HU & HLn). split; [|exact HLn].
      apply (na_au8arr_kept W3 W2 mm mem2 LA_G_NL bs HU).
      - intros i Hi. apply KG. rewrite HLn in Hi. lia.
      - intros i Hi. rewrite HLn in Hi. exact (proj2 (proj2 (na_gnl_img (LA_G_NL + i) ltac:(unfold NK_SIZE in *; lia)))). }
    split; [exact HGO|]. split; [exact HOW|]. split; [exact HRC|].
    split.
    { apply (na_abytes_kept W3 W2 mm mem2 _ _ HBY). intros i Hi. apply KF.
      unfold NT_BUFLEN in HBL. rewrite HBL in Hi. unfold nBUF, NT_BUFOFF. lia. }
    split; [exact HBL|]. split; [exact HCL|].
    { apply (na_abuf_kept W3 W2 mm mem2 _ _ HBUF).
      - intros i Hi. apply KF. unfold NT_BUFLEN in Hi. unfold nBUF, NT_BUFOFF. lia.
      - intros i Hi. apply na_not_ro_off.
        apply (proj2 (aside_rng_low SK SEGS B LAWS pa_segs_low ly3 S3 W3 mm md3 NT_CID fp (nBUF cx fp + i) HAR3 Hin9 ltac:(
          left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfa9, na_fsz; unfold NT_BUFLEN in Hi; unfold nBUF, NT_BUFOFF; lia))). }
  - exact HAP.
  - exact KS.
  - split.
    + intros Hout Hn1. exact (proj2 HPOST Hout Hn1).
    + intros Hout Hn1. apply (proj1 HPOST Hout Hn1 (rd16 c aoff) _ Hau ltac:(unfold RTA_HDR in *; lia) Hpay Hpayl).
  - apply (na_buf_kept W3 W2 (n_m cx) mm mem2 out' n' o' HBo').
    + intros Hout' Hn1 i Hi. apply KB'. apply na_in_aivl; [exact Hout' | lia].
    + intros Hout' Hn1 i Hi. exact (Hro (out' + i) (P2 (out' + i) (na_in_aivl out' n' (out' + i) Hout' ltac:(lia)))).
Qed.

Lemma na_aarg_range : forall regs i, 0 <= aarg regs i < 2 ^ 64.
Proof. intros regs i. unfold aarg, argZ. apply u64_range. Qed.

(* the call at either site: isal = true at +0x38c (the alias buffer), false at +0x3f4 (the kind buffer) *)
Lemma na_call : forall (isal : bool) cx fp k2 ly3 S3 W3 rg mm md3 c rest bs aoff retk k al Q,
  nt_base SK B cx ->
  na_core cx fp k2 ly3 S3 W3 (mkst rg (w64 (BASE + AF_copy_attr)) mm (seg_rom SEGS)) md3 c rest bs ->
  na_bufs cx (rdW W3 mm) (Attrs k al) ->
  getr rg 10 = w64 (nBUF cx fp + aoff) ->
  getr rg 11 = w64 (if isal then n_alias cx else n_kind cx) ->
  getr rg 12 = w64 (if isal then n_aliasn cx else n_kindn cx) ->
  getr rg 1 = w64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  0 <= aoff -> 4 <= rd16 c aoff -> aoff + rd16 c aoff <= Z.of_nat (length c) ->
  (forall ly2 S2 W2 regs2 mem2 md2,
     na_core cx fp k2 ly2 S2 W2 (mkst regs2 (w64 (BASE + retk)) mem2 (seg_rom SEGS)) md2 c rest bs ->
     aregs_preserved rg regs2 ->
     (forall a, n_sp1 cx <= a < spZ (n_regs cx) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mm a) ->
     na_bufs cx (rdW W2 mem2)
       (if isal then Attrs k (Some (slice c (aoff + RTA_HDR) (rd16 c aoff - RTA_HDR)))
        else Attrs (Some (slice c (aoff + RTA_HDR) (rd16 c aoff - RTA_HDR))) al) ->
     SRr SEGS W2 (mkCfg (mkst regs2 (w64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (mkst rg (w64 (BASE + AF_copy_attr)) mm (seg_rom SEGS)) md3) Q.
Proof.
  intros isal cx fp k2 ly3 S3 W3 rg mm md3 c rest bs aoff retk k al Q HB HC (HBK & HBA) G10 G11 G12 G1 Hrk Hrk2
    Ha0 Hl4 Hlc KONT.
  pose proof HB as (_ & _ & HNP & _).
  destruct HNP as (kbs & req & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & HKE & HAE & HKA & HKF & HAF & HKC & HAC).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (WK : forall a, inFP [aivl (n_kind cx) (n_kindn cx)] a -> inFP (n_Wr cx) a).
  { intros a (r & [<- | []] & Hr). exists (aivl (n_kind cx) (n_kindn cx)). split; [right; left; reflexivity | exact Hr]. }
  assert (WA : forall a, inFP [aivl (n_alias cx) (n_aliasn cx)] a -> inFP (n_Wr cx) a).
  { intros a (r & [<- | []] & Hr). exists (aivl (n_alias cx) (n_aliasn cx)). split; [right; right; left; reflexivity | exact Hr]. }
  assert (HWapp : forall a, inFP (n_Wr cx) a -> a < kLowMemEnd \/ kHighMemBeg <= a).
  { intros a (r & Hin & Hr). unfold n_Wr, nl_talk_awr in Hin.
    destruct Hin as [<- | [<- | [<- | []]]].
    - cbn [fst snd] in Hr. unfold LA_G_NL, NK_N_SENT, kLowMemEnd in *. lia.
    - destruct (na_aivl_in (aarg (n_regs cx) 2) (aarg (n_regs cx) 3) a
        (ex_intro _ (aivl (aarg (n_regs cx) 2) (aarg (n_regs cx) 3)) (conj (or_introl eq_refl) Hr))) as (Hk0 & Hai).
      assert (Hn3 : 1 <= aarg (n_regs cx) 3) by lia. destruct (HKC Hk0 Hn3) as (Hamr & _). unfold amem_range in Hamr. unfold kLowMemEnd, kHighMemBeg in *. lia.
    - destruct (na_aivl_in (aarg (n_regs cx) 4) (aarg (n_regs cx) 5) a
        (ex_intro _ (aivl (aarg (n_regs cx) 4) (aarg (n_regs cx) 5)) (conj (or_introl eq_refl) Hr))) as (Hk0 & Hai).
      assert (Hn5 : 1 <= aarg (n_regs cx) 5) by lia. destruct (HAC Hk0 Hn5) as (Hamr & _). unfold amem_range in Hamr. unfold kLowMemEnd, kHighMemBeg in *. lia. }
  pose proof (na_aarg_range (n_regs cx) 2) as Rk. pose proof (na_aarg_range (n_regs cx) 3) as Rkn.
  pose proof (na_aarg_range (n_regs cx) 4) as Ra. pose proof (na_aarg_range (n_regs cx) 5) as Ran.
  destruct isal.
  - apply (na_call_gen cx fp k2 ly3 S3 W3 rg mm md3 c rest bs aoff retk (n_alias cx) (n_aliasn cx) al
      (n_kind cx) (n_kindn cx) k Q HB HC HBA HBK G10 G11 G12 G1 Hrk Hrk2 Ra Ran Ha0 Hl4 Hlc WA WK HAF HAC HKE
      (fun H => proj1 (HKF H))).
    + intros H1 H2 H3 H4. pose proof (HKA H3 H4 H1 H2) as Hap. unfold apart, n_alias, n_aliasn, n_kind, n_kindn in *. lia.
    + exact HKC.
    + exact HWapp.
    + intros ly2 S2 W2 regs2 mem2 md2 HC2 HP2 HS2 HA2 HK2. apply (KONT ly2 S2 W2 regs2 mem2 md2 HC2 HP2 HS2).
      split; assumption.
  - apply (na_call_gen cx fp k2 ly3 S3 W3 rg mm md3 c rest bs aoff retk (n_kind cx) (n_kindn cx) k
      (n_alias cx) (n_aliasn cx) al Q HB HC HBK HBA G10 G11 G12 G1 Hrk Hrk2 Rk Rkn Ha0 Hl4 Hlc WK WA HKF HKC HAE
      (fun H => proj1 (HAF H)) HKA HAC HWapp).
    intros ly2 S2 W2 regs2 mem2 md2 HC2 HP2 HS2 HK2 HA2. apply (KONT ly2 S2 W2 regs2 mem2 md2 HC2 HP2 HS2).
    split; assumption.
Qed.

End b.
End a.
