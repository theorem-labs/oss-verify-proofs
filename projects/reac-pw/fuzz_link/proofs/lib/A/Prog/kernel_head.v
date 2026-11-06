(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 494 of its 550 lines of code are new or changed and 1249 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_msg0_kit.v, with its module paths and module names changed; 912 of its 1010 lines of code are new or changed and 452 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: kernel's chunk-loop HEAD, kin_head (+0x51c) -> kin_msg0 (+0x594) / kin_raw (+0x1f30) / kin_mz (+0x1e7c)
   (link-a/plan/kernel-plan.md (internal record, sha256 440bf3b40ab7) section 4; link-a/plan/kernel-lanes.md (internal record, sha256 18c8d69749d5)).

   WHAT THE CODE DOES HERE (listing (internal path) (internal record, sha256 7bc02d6772b3); the
   inlined fuzz_u8 of the mode byte):
     +0x51c  lbu a0, 0(s8); beqz a0        the instrumented check of the cursor's n word (s8 = shadow(a0 + 8))
     +0x528  ld a0, 0(s3)                  n, the bytes left (s3 = a0 + 8)
     +0x52c  bnez a0 -> +0x534, else j +0x1e7c: the empty cursor, kin_mz (no byte written)
     +0x534  lbu a1, 0(s8); beqz a1        the check again, for the store
     +0x540  sd n - 1, 8(s2)               the cursor's n
     +0x548  ld a0, 0xc0(s1); lbu a0, 0(a0); beqz a0   the check of the cursor's p word (slot KS_CSH = shadow(a0))
     +0x558  ld a0, 0(s2); sd p + 1, 0(s2) the cursor's p
     +0x564  the instrumented check of the input byte at p: a1 := lb ((p >> 3) + s4); `beqz a1` -> +0x578; else
             +0x574 j +0x2110: `andi a2, a0, 7; bge a2, a1` -> the error path +0x2648, else j +0x578
     +0x578  lbu a0, 0(a0): the mode byte d; a0 := d & 1; a1 := 4097; sd a1, 0xa8(s1) (slot KS_ROOM)
     +0x58c  beqz a0 -> +0x594 (kin_msg0); else +0x590 j +0x1f30 (kin_raw).

   THE PROOF. The state at +0x51c is rebuilt from kin_head: registers sr_atoms over Eimg (Ereg regs [p; n; d; q; s])
   (p, n the cursor's words, d the mode byte, q = shadow(p), s the shadow byte of p) with s3 := a0 + 8 and s8 :=
   the shadow address expression of a0 + 8 (so the cursor's checks resolve against the SH entry (a0, 0, 16)); the
   cursor's 16 bytes, the spill slots [s1 + 0xa8, s1 + 0xc8) (window 0xa8 .. 0xb0), the byte at p and its shadow
   byte as regions; the alias (p >> 3) + s4 = q, so the input byte's check reads the shadow byte from its region.
   Its slow path is out of line (+0x2110), so the run splits on the shadow byte up front: s = 0, or s <> 0 with
   (p & 7) < s (saddr_ok of the input's range_addressable), and on the mode bit; each case is one run whose branches
   the engine decides from the facts' conditions, ending at the cut. The empty cursor (n = 0) is a fifth run, with
   no writable window. Every cut is read off the end state: the cursor's two words and the slot KS_ROOM from the
   regions, the registers from the symbolic state, every other clause of kat by kernel_kit.v's frame lemmas over the
   run's frame (it writes only the cursor, in kernel's write set, and [s1 + 0xa8, s1 + 0xb0), in kernel's window):
   kh_after, kh_land.
   The shadow facts the checks need (the cursor's range_addressable, the input byte's shadow byte) come from kbase at
   the call and are moved to the current state over kkept's akept (kh_saddr_move, the saddr half of LinkWalkShadow.v
   sbyte_transport: kbase gives the cursor's range_addressable but not its shadow_hull_vis).

   Section hypotheses: LAWS : AR_laws pa_segs B (the lib/A frame), for the run instances; TB : PcapSyms B (AF0m.v,
   discharged at the frame's B by AD2l.PcapB_syms), for LinkWalkShadow.v img_sh_eq.
   Released proofs (rule 24): this proves no function (kind: segment lemma of kernel's walk); the walk of kernel had
   its search (lookups/walk-lookups.md (internal record, sha256 98fff7967d93): disposition none, written new; confirmed by the rule-24 walk check at 14:56Z).
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
PcapRelro kernel_c kernel_img kernel_defs kernel_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at +0x51c ----
   Atoms 0..31: the registers at the cut; 32 = p (the cursor's p word), 33 = n (its n word), 34 = d (the byte at p),
   35 = q = shadow(p), 36 = s (the shadow byte at q). *)
Definition hd_Bx : sv := SOff 20 0.
Definition hd_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the shadow address of atom r + c: (x >> 3) + s4 *)
Definition hd_sh (r : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff r c) (SLit 3)) (SOff 20 0).
(* s3 = a0 + 8, s8 = shadow(a0 + 8) *)
Definition hd_regs : list sv := sr_set (sr_set sr_atoms (Z_to_bv 5 19) (SOff 18 8)) (Z_to_bv 5 24) (hd_sh 18 8).
Definition hd_cur (w : Z) (nv : sv) : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 16 0 w [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 nv)].
Definition hd_slots : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xa8 0xc8 0xa8 0xb0 [YP09.mkChunk 0xc0 (CVal 8 (hd_sh 18 0))].
Definition hd_in : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition hd_ish : YP09.region := YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))].
Definition hd_atoms : list (nat * afact) :=
  [(18%nat, mkAF 0 (2 ^ 47 - 16) 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (34%nat, mkAF 0 255 0); (36%nat, mkAF 0 7 0)].
Definition hd_alias : list (sv * sv) := [(hd_sh 32 0, SOff 35 0)].
(* the conditions that decide the run's branches: n <> 0 (+0x52c), the input byte's check (+0x570, +0x2114), the
   mode bit (+0x58c) *)
Definition hd_cmode (raw : bool) : acond :=
  mkAC (if raw then BC_NE else BC_EQ) (SAlu ALU_AND (SOff 34 0) (SLit 1)) (SLit 0).
Definition hd_cs (fast raw : bool) : list acond :=
  if fast then [mkAC BC_NE (SOff 33 0) (SLit 0); mkAC BC_EQ (SOff 36 0) (SLit 0); hd_cmode raw]
  else [mkAC BC_NE (SOff 33 0) (SLit 0); mkAC BC_NE (SOff 36 0) (SLit 0);
        mkAC BC_LT (SAlu ALU_AND (SOff 32 0) (SLit 7)) (SOff 36 0); hd_cmode raw].
Definition hd_rs1 : smem := [hd_cur 16 (SOff 33 0); hd_slots; hd_in; hd_ish].
Definition hd_ss1 (cs : list acond) : sstate := mkSS (kpc KP_HEAD) hd_regs hd_rs1 None (mkFacts hd_atoms cs hd_alias).
(* the empty cursor: n = 0, nothing written *)
Definition hd_rs0 : smem := [hd_cur 0 (SLit 0)].
Definition hd_ss0 : sstate := mkSS (kpc KP_HEAD) hd_regs hd_rs0 None (mkFacts hd_atoms [] hd_alias).
Definition hd_SH : list shent := [mkSHE 18 0 16].
(* the registers of kregs0 and kregs_chunk, which the phase does not write *)
Definition hd_keepz : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25].

Ltac hd_inl := cbn [In]; repeat (first [left; reflexivity | right]).

(* `blt` on two small values *)
Lemma kh_blt : forall a b, 0 <= a < 8 -> 0 <= b < 8 -> a < b ->
  branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof.
  intros a b Ha Hb Hab.
  assert (Ga : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7) by lia.
  assert (Gb : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7) by lia.
  clear Ha Hb.
  destruct Ga as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
    destruct Gb as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
    first [exfalso; lia | vm_compute; reflexivity].
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
Hypothesis TB : PcapSyms B.                                  (* AF0m.v; AD2l.PcapB_syms at the frame's B *)

Definition hd_E (ms : machine_state) (p n d s : Z) : env :=
  Eimg (Ereg (ms_regs ms) [w64 p; w64 n; w64 d; w64 (SHADOW_OFF + p / 8); w64 s]).

(* ---- byte, word and engine helpers ---- *)

Lemma kh_ms_shape : forall (ms : machine_state) (pc : Z),
  ms_pc_val ms = w64 pc -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (w64 pc) (ms_mem ms) (seg_rom SEGS).
Proof.
  intros [rg fr pcv sv rv fc mm rm] pc H1 H2 H3 H4 H5 H6.
  cbn in H1, H2, H3, H4, H5, H6. subst. reflexivity.
Qed.

Lemma kh_rdword_range : forall (H : word -> bool) (m : word -> option byte) a v,
  rdword (aview SEGS H m) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
  intros H m a v Hv.
  assert (R : forall x b, aview SEGS H m x = Some b -> 0 <= b < 256).
  { intros x b Hb. destruct (aview_byte SEGS H m x b Hb) as (_ & _ & _ & Hr). exact Hr. }
  unfold rdword in Hv.
  destruct (aview SEGS H m a) as [b0|] eqn:E0; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 1)) as [b1|] eqn:E1; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 2)) as [b2|] eqn:E2; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 3)) as [b3|] eqn:E3; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 4)) as [b4|] eqn:E4; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 5)) as [b5|] eqn:E5; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 6)) as [b6|] eqn:E6; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 7)) as [b7|] eqn:E7; [|cbv iota beta in Hv; discriminate Hv].
  cbv iota beta in Hv. injection Hv as <-.
  apply R in E0. apply R in E1. apply R in E2. apply R in E3.
  apply R in E4. apply R in E5. apply R in E6. apply R in E7. lia.
Qed.

(* a spill slot's 8 bytes as a chunk of the state's region, and back *)
Lemma kh_chunk_rd : forall E (H : word -> bool) (mm : word -> option byte) base off e v,
  sv_denot E e = Z_to_bv 64 v -> rdword (aview SEGS H mm) (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict H mm) base (YP09.mkChunk off (CVal 8 e)).
Proof.
  intros E H mm base off e v He Hr.
  pose proof (kh_rdword_range H mm (base + off) v Hr) as Hv.
  apply (chunk_ok_val SEGS E (mrestrict H mm) base off 8 e v He).
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
  - change (Z.of_N 8) with 8. lia.
  - exact (val_mem_of_rdword SEGS H mm (base + off) v Hr).
Qed.

Lemma kh_rd_of_region : forall E (H : word -> bool) (mm : word -> option byte) n b cs lo hi wlo whi off e v,
  region_ok SEGS E (mrestrict H mm) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H mm) (b + off) = Some v.
Proof.
  intros E H mm n b cs lo hi wlo whi off e v HR Hb Hin He Hv.
  apply (rdword_of_val_mem SEGS H mm (b + off) v); [|exact Hv].
  apply (field_of_region (segs := SEGS) E (mrestrict H mm) n b cs lo hi wlo whi off 8 e v HR Hb Hin He).
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
  - change (Z.of_N 8) with 8. lia.
Qed.

(* a byte of memory as a one-byte value *)
Lemma kh_val1 : forall (m : word -> option byte) a (b : byte),
  mbyte SEGS m a = Some b -> val_mem SEGS m a 1 (bv_unsigned b).
Proof.
  intros m a b Hb k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb.
  pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  rewrite le_byte_small by (change (2 ^ (8 * Z.of_nat 1)) with 256; lia).
  change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* the shadow address expression of atom n + c *)
Lemma kh_denot_sh : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v -> 0 <= c -> v + c < 2 ^ 64 ->
  ew E 20%nat = Z_to_bv 64 SHADOW_OFF ->
  sv_denot E (hd_sh n c) = Z_to_bv 64 (SHADOW_OFF + (v + c) / 8).
Proof.
  intros E n v c Hn Hv Hc Hvc H20. unfold hd_sh. rewrite denot_lit_U. f_equal.
  assert (Hd : 0 <= (v + c) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
  change (Z.land (zcanon 3) 63) with 3.
  rewrite (U_atom_off E n v c Hn ltac:(lia) ltac:(lia)).
  rewrite (U_atom_off E 20 SHADOW_OFF 0 H20 ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)).
  rewrite Z.add_0_r. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.

(* The registers a run does not write: the same symbolic value at its start and at its end. *)
Lemma kh_reg_same : forall E ss0 ss1 (H : word -> bool) (ms0 ms1 : machine_state) (l : list Z),
  st_ok_pi SEGS pa_val E ss0 (restrict H ms0) -> st_ok_pi SEGS pa_val E ss1 (restrict H ms1) ->
  forallb (fun k => sv_eqb (sr_get (ss_regs ss1) (Z_to_bv 5 k)) (sr_get (ss_regs ss0) (Z_to_bv 5 k))) l = true ->
  forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) l = true -> getr (ms_regs ms1) r = getr (ms_regs ms0) r.
Proof.
  intros E ss0 ss1 H ms0 ms1 l HS0 HS1 Hl r Hr.
  apply existsb_exists in Hr as (k & Hk & Hrk). apply Z.eqb_eq in Hrk.
  rewrite forallb_forall in Hl. pose proof (Hl k Hk) as Hs. apply sv_eqb_eq in Hs.
  assert (Er : r = Z_to_bv 5 k) by (rewrite <- Hrk; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite (st_ok_pi_restrict_reg H E ss1 ms1 r HS1), (st_ok_pi_restrict_reg H E ss0 ms0 r HS0), Er, Hs.
  reflexivity.
Qed.

(* THE SHADOW BYTE OF A READ-SET BYTE at a later state: LinkWalkShadow.v sbyte_transport's saddr half, which needs no
   shadow_hull_vis at the call (kbase gives the cursor's range_addressable, not its hull). *)
Lemma kh_saddr_move : forall lyc Sc (W : world SEGS) memc mdc ly2 S2 (W2 : world SEGS) mem2 md2 slo shi
    (E : Z -> Prop) x,
  AR SEGS B lyc Sc W memc mdc -> AR SEGS B ly2 S2 W2 mem2 md2 ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2)) ->
  akept SEGS B lyc Sc W memc W2 mem2 slo shi E -> fmiss lyc Sc E ->
  akb SEGS B lyc Sc slo shi x ->
  saddr (aview SEGS (w_H W) memc) x -> saddr (aview SEGS (w_H W2) mem2) x.
Proof.
  intros lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E x HAR1 HAR2 Elo Ehi Hbl HK HE Hc Hs1.
  pose proof HAR1 as (M1 & _). pose proof HAR2 as (M2 & _).
  destruct Hc as [(Hst & _) | [(b & m & Hin & Hb) | [(Hi & _ & _) | (c & q & Hin & Hf)]]].
  - (* the real stack: zero at every AR state *)
    pose proof (proj1 (Forall_forall _ _) (am_zshadow B ly2 S2 _ M2) (ly_stk_lo ly2, ly_stk_hi ly2 - ly_stk_lo ly2)
      ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ.
    cbn [fst snd] in HZ. unfold zero_shadow, shadow_of_addr in HZ.
    pose proof (am_layout B ly2 S2 _ M2) as LO. destruct (lo_top _ LO) as (_ & _ & _ & _ & Pl & Ph & _).
    unfold page_aligned in Pl, Ph. rewrite Elo, Ehi in *.
    exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + ly_stk_lo lyc / 8 + (x / 8 - ly_stk_lo lyc / 8)) by lia.
    apply HZ. lia.
  - (* a heap block still alive *)
    pose proof (Hbl b m Hin) as Hin2.
    destruct (al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hin2) as [HBS _].
    exact (block_shadow_range _ _ _ _ x 1 HBS ltac:(lia) ltac:(lia) x ltac:(lia)).
  - (* the image *)
    pose proof (pa_img_range x Hi) as Hi'. rewrite img_end_val in Hi'.
    assert (Hsx : SHADOW_OFF + 0x2000 <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 0xca800)
      by (unfold shadow_of_addr; lia).
    destruct (img_sh_eq B TB lyc Sc _ ly2 S2 _ _ M1 M2 Hsx) as [Eq _].
    destruct Hs1 as (v & Hv & Hok). exists v. rewrite Eq. split; [exact Hv | exact Hok].
  - (* a side frame of the call *)
    pose proof HK as (_ & _ & _ & K4 & _).
    unfold in_zr, frame_rng in Hf. cbn [fst snd] in Hf.
    destruct (frame_facts B lyc Sc _ c q M1 Hin) as (_ & _ & Happ & _ & PF & _ & _ & Hoff & H64 & Hb64 & _).
    unfold page_aligned in PF. unfold in_app, kFakeStackSize in Happ.
    destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc c q HAR1 Hin) as (Hf4096 & Hfceil & _).
    pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
    assert (HF64 : frame_addr lyc c q mod 64 = 0) by (unfold frame_addr; lia).
    assert (KS : forall s, shadow_addr x / 8 * 8 <= s < shadow_addr x / 8 * 8 + 8 ->
      aview SEGS (w_H W2) mem2 s = aview SEGS (w_H W) memc s).
    { intros s Hs.
      assert (Hsf : shadow_addr (frame_addr lyc c q) <= s < shadow_addr (frame_addr lyc c q) + fs_frame_bytes c / 8)
        by (unfold shadow_addr, SHADOW_OFF in *; lia).
      apply (K4 c q s Hin).
      - right. unfold in_zr. cbn [fst snd]. exact Hsf.
      - exact (HE c q s Hin Hsf). }
    destruct Hs1 as (v & Hv & Hok). exists v. split; [|exact Hok].
    rewrite (KS (shadow_of_addr SHADOW_OFF x)); [exact Hv|]. unfold shadow_of_addr, shadow_addr, SHADOW_OFF. lia.
Qed.

(* ---- the phase's context: kin_head at +0x51c ---- *)
Section h.
Variable cx : kcx.
Variables fpos k2 : Z.
Variable ly3 : alayout.
Variable S3 : astate.
Variable W3 : world SEGS.
Variable ms3 : machine_state.
Variable md3 : Model.
Variables c ci j adv : Z.
Hypothesis HB : kbase SK B cx.
Hypothesis HJ3 : ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx)
  (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2.
Hypothesis HK : kat B cx fpos KP_HEAD (kregs_chunk cx fpos ci) (kslots_setup cx fpos c) (kfsh 0xf8 0xf8 0xf3) true
  adv (Some j) k2 ly3 S3 W3 ms3 md3.

(* the bytes the run may write: the cursor and the slot KS_ROOM *)
Definition hd_X (a : Z) : Prop := ka0 cx <= a < ka0 cx + 16 \/ ksp1 cx + 0xa8 <= a < ksp1 cx + 0xb0.

Lemma kh_geo :
  alloc_ceiling <= ly_stk_lo (k_lyc cx) /\ ly_stk_hi (k_lyc cx) <= 2 ^ 47 /\
  ly_stk_lo (k_lyc cx) <= k_sp0 cx - k_STK cx /\ k_sp0 cx <= ly_stk_hi (k_lyc cx) /\
  k_sp0 cx - k_STK cx <= ksp cx - 4640 /\ ksp cx <= k_sp0 cx /\
  ksp cx - 384 < ksp1 cx <= ksp cx - 352 /\ ksp1 cx mod 32 = 0 /\ KERNEL_AK = 4640.
Proof.
  pose proof HB as (HPRE & _).
  pose proof HPRE as (HJ0 & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _).
  pose proof HJ0 as (HSTK0 & HXO0 & _).
  pose proof HJ0 as HROW. eapply ajournal_gx_row in HROW. destruct HROW as (Hrow1 & Hrow2 & Hrow3 & Hrow4).
  assert (HKA : KERNEL_AK = 4640) by reflexivity.
  change (spZ (k_regs cx)) with (ksp cx) in Hwlo, Hwhi. rewrite HKA in Hwlo.
  assert (Hs1 : ksp cx - 384 < ksp1 cx <= ksp cx - 352) by (unfold ksp1, ksp1_of, KN_MFRAME; lia).
  assert (Hs1al : ksp1 cx mod 32 = 0) by (unfold ksp1, ksp1_of; rewrite Z.mul_comm; apply Z_mod_mult).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [exact Hs1al | exact HKA].
Qed.

(* the call's AR, the current AR, the stack rows, the blocks *)
Lemma kh_AR0 : AR SEGS B (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx).
Proof. pose proof HB as ((HJ0 & _) & _). pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). exact (proj1 HJi). Qed.

Lemma kh_AR3 : AR SEGS B ly3 S3 W3 (ms_mem ms3) md3.
Proof. pose proof HJ3 as (_ & _ & (memS & HJi & _) & _). exact (proj1 HJi). Qed.

Lemma kh_row : ly_stk_lo ly3 = ly_stk_lo (k_lyc cx) /\ ly_stk_hi ly3 = ly_stk_hi (k_lyc cx).
Proof.
  pose proof HB as ((HJ0 & _) & _).
  pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (_ & Hly0 & _).
  destruct Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo0 & Ehi0 & _).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (_ & Hly3 & _).
  destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo3 & Ehi3 & _).
  split; congruence.
Qed.

Lemma kh_fa : forall cid pos, frame_addr ly3 cid pos = frame_addr (k_lyc cx) cid pos.
Proof.
  intros cid pos. pose proof HB as ((HJ0 & _) & _).
  pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (_ & Hly0 & _).
  destruct Hly0 as (_ & _ & _ & _ & _ & EF0 & _).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (_ & Hly3 & _).
  destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
  unfold frame_addr. rewrite EF0, EF3. reflexivity.
Qed.

Lemma kh_blocks : forall b m, In (b, m) (ablocks B (k_lyc cx) (k_Sc cx)) -> In (b, m) (ablocks B ly3 S3).
Proof.
  intros b m Hin. pose proof HK as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & Hperm & _) & _).
  exact (Permutation_in _ (Permutation_sym Hperm) Hin).
Qed.

(* A byte of kernel's read set: an application byte below 2 ^ 47, and not a byte of F (its range, its shadow, its
   flag byte: LinkWalkSide.v aside_rng; LinkWalkSide.v akept_drop_side's argument) *)
Lemma kh_akb : forall a, akb SEGS B (k_lyc cx) (k_Sc cx) (ksp cx - KERNEL_AK) (ksp cx) a ->
  (0 <= a < 2 ^ 47 /\ (a < kLowMemEnd \/ kHighMemBeg <= a)) /\ ~ aside_rng (k_lyc cx) KN_CID fpos a.
Proof.
  intros a Hb.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct kh_geo as (Hlo & Hhi & _).
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & Hjbk & _).
  destruct Hjbk as (_ & _ & _ & _ & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Eab1) & _).
  assert (Hin1 : In (KN_CID, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
  pose proof (aside_rng_low SK SEGS B LAWS pa_segs_low (k_lyc cx) S1 W1 mem1 md1 KN_CID fpos) as Hlow.
  destruct (frames_bounds SEGS B LAWS (k_lyc cx) S1 W1 mem1 md1 KN_CID fpos HAR1 Hin1) as (Hf4 & Hfc & _).
  destruct (al_flag _ _ LAWS (k_lyc cx) S1 W1 mem1 md1 KN_CID fpos HAR1 Hin1) as (_ & Hfo & _ & _).
  pose proof (fs_frame_bytes_nonneg KN_CID) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr (k_lyc cx) KN_CID fpos) ltac:(lia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr (k_lyc cx) KN_CID fpos + fs_frame_bytes KN_CID) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr (k_lyc cx) KN_CID fpos) (fs_frame_bytes KN_CID) Hnn) as Hse.
  pose proof ASAN_CEIL_range as [CR _].
  destruct Hb as [(H1 & H2) | [(b & m & Hbm & Hr) | [(Hi & Hns & He) | (cid & pos & Hin & Hr)]]].
  - (* the real-stack row *)
    split; [split; [lia | right; lia] |]. intros Hs. pose proof (proj1 (Hlow a HAR1 Hin1 Hs)). lia.
  - (* a heap block of the call *)
    assert (Hb1 : In (b, m) (ablocks B (k_lyc cx) S1)) by (rewrite Eab1; exact Hbm).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR1 Hb1) as (_ & H4096 & Hbc & Hbapp & Hpo & _ & _).
    pose proof (in_app_addr _ _ a Hbapp Hr) as Hap. unfold app_addr, kLowShadowBeg, ASAN_CEIL in Hap.
    split; [split; lia|].
    intros [Hs | [Hs | Hs]].
    + pose proof (sep_block_frame SEGS B LAWS (k_lyc cx) S1 W1 mem1 md1 b m KN_CID fpos HAR1 Hb1 Hin1) as Hd.
      unfold zdisjoint, in_zr, frame_rng in Hd, Hs. cbn [fst snd] in Hd, Hs. lia.
    + unfold in_zr in Hs. cbn [fst snd] in Hs. lia.
    + exact (proj2 (Hpo a Hr) (eq_ind_r (fun x => aowned B (k_lyc cx) S1 x) Hfo Hs)).
  - (* an image byte *)
    pose proof (pa_segs_low a Hi) as Hal. split; [split; lia|].
    intros Hs. exact (proj2 (Hlow a HAR1 Hin1 Hs) Hi).
  - (* a side frame of the call *)
    assert (Hin' : In (cid, pos) (frames S1)) by (rewrite Hfrs1; right; exact Hin).
    destruct (frames_bounds SEGS B LAWS (k_lyc cx) S1 W1 mem1 md1 cid pos HAR1 Hin') as (Hf4' & Hfc' & Happ').
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    pose proof (in_app_addr _ _ a Happ' Hr) as Hap. unfold app_addr, kLowShadowBeg, ASAN_CEIL in Hap.
    split; [split; lia|].
    intros Hs.
    apply in_split in Hin as (l2 & l3 & El).
    pose proof (sep_frames_pos SEGS B LAWS (k_lyc cx) S1 W1 mem1 md1 (KN_CID, fpos) (cid, pos) [] l2 l3 HAR1
      ltac:(rewrite Hfrs1, El; reflexivity)) as Hd.
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
    destruct (al_frames _ _ LAWS (k_lyc cx) S1 W1 mem1 md1 cid pos HAR1 Hin') as (_ & _ & Hfb' & _).
    destruct Hs as [Hs | [Hs | Hs]]; unfold in_zr, frame_rng in Hs; cbn [fst snd] in Hs.
    + lia.
    + lia.
    + subst a. exact (proj2 (Hfb' _ Hr) Hfo).
Qed.

(* the cursor's 16 bytes and the input's bytes are read-set bytes *)
Lemma kh_cur : forall x, ka0 cx <= x < ka0 cx + 16 ->
  akb SEGS B (k_lyc cx) (k_Sc cx) (ksp cx - KERNEL_AK) (ksp cx) x.
Proof.
  intros x Hx. pose proof HB as (_ & HRD & _). apply HRD. left. unfold ka0 in Hx. exact Hx.
Qed.

Lemma kh_in : forall x, k_wp cx <= x < k_wp cx + k_wn cx ->
  akb SEGS B (k_lyc cx) (k_Sc cx) (ksp cx - KERNEL_AK) (ksp cx) x.
Proof.
  intros x Hx. pose proof HB as (_ & HRD & _ & _ & _ & HWP & HWN & HWPr & HWNr & _). apply HRD.
  right; left. exists (k_wp cx), (k_wn cx).
  split; [exact HWP|]. split; [exact HWN|]. split; [exact HWPr|]. split; [exact HWNr | lia].
Qed.

(* kernel_apre's facts the phase uses, at kbase's cursor words *)
Lemma kh_pre :
  apart_frame (k_regs cx) KERNEL_AK (ka0 cx) 16 /\ apart_gnl LA_G_NL (ka0 cx) 16 /\
  apart (ka0 cx) 16 LA_LONG_ALIAS (LONG_ALIAS_SIZE + 3) /\
  range_addressable (ard SEGS (km0 cx)) SHADOW_OFF (ka0 cx) 16 /\
  amem_range (k_wp cx) (k_wn cx) /\ range_addressable (ard SEGS (km0 cx)) SHADOW_OFF (k_wp cx) (k_wn cx) /\
  kernel_apart (k_regs cx) (k_wp cx) (k_wn cx).
Proof.
  pose proof HB as (_ & _ & HKP & _ & _ & HWP & HWN & HWPr & HWNr & _).
  destruct HKP as (kbs' & _ & _ & _ & _ & (wp' & wn' & HP1 & HN1 & HP1r & HN1r & _ & HAMR & HRAi & _ & HAPi) &
    _ & HRAc & HAPF & HAPG & HAPL & _).
  assert (Ep : wp' = k_wp cx).
  { pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ HP1 HP1r) as R1.
    pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ HWP HWPr) as R2.
    unfold ka0 in R2. congruence. }
  assert (En : wn' = k_wn cx).
  { pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ HN1 HN1r) as R1.
    pose proof (rdword_of_val_mem SEGS (w_H (k_W cx)) (k_memc cx) _ _ HWN HWNr) as R2.
    unfold ka0 in R2. congruence. }
  subst wp' wn'.
  split; [exact HAPF|]. split; [exact HAPG|]. split; [exact HAPL|]. split; [exact HRAc|].
  split; [exact HAMR|]. split; [exact HRAi | exact HAPi].
Qed.

(* a byte of kernel's write set: an application byte below 2 ^ 47; outside the cursor, an image byte *)
Lemma kh_kE : forall x, kE cx x ->
  (0 <= x < 2 ^ 47 /\ (x < kLowMemEnd \/ kHighMemBeg <= x)) /\ (ka0 cx <= x < ka0 cx + 16 \/ x < kLowMemEnd).
Proof.
  intros x (r & Hr & Hx). pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold kernel_awr in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hx.
  - unfold LA_G_NL, NK_CHUNK, NK_OPEN in Hx. split; [split; lia | right; lia].
  - unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE in Hx. split; [split; lia | right; lia].
  - change (aarg (k_regs cx) 0) with (ka0 cx) in Hx.
    split; [exact (proj1 (kh_akb x (kh_cur x Hx))) | left; exact Hx].
Qed.

(* the exception set of kkept's akept misses the shadow of every frame of the call *)
Lemma kh_fmiss : fmiss (k_lyc cx) (k_Sc cx) (fun a => kE cx a \/ aside_rng (k_lyc cx) KN_CID fpos a).
Proof.
  apply fmiss_or.
  - apply (fmiss_app SEGS B LAWS (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx) (kE cx) kh_AR0).
    intros a Ha. exact (proj2 (proj1 (kh_kE a Ha))).
  - pose proof HK as (_ & _ & _ & _ & _ & _ & _ & Hjbk & _).
    destruct Hjbk as (_ & _ & _ & Hnin & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & _) & _).
    assert (Hin1 : In (KN_CID, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
    pose proof HAR1 as (M1 & _).
    destruct (frame_facts B (k_lyc cx) S1 _ KN_CID fpos M1 Hin1) as (Cc & Cp & _).
    eapply fmiss_side; [exact kh_AR0 | exact Cc | exact Cp | exact Hnin].
Qed.

(* a read-set byte's shadow at the current state, from the call's *)
Lemma kh_saddr_now : forall x, akb SEGS B (k_lyc cx) (k_Sc cx) (ksp cx - KERNEL_AK) (ksp cx) x ->
  saddr (aview SEGS (w_H (k_W cx)) (k_memc cx)) x -> saddr (aview SEGS (w_H W3) (ms_mem ms3)) x.
Proof.
  intros x Hx Hs. pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & (Kak & _) & _).
  destruct kh_row as (Elo & Ehi).
  exact (kh_saddr_move (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx) ly3 S3 W3 (ms_mem ms3) md3
    (ksp cx - KERNEL_AK) (ksp cx) _ x kh_AR0 kh_AR3 Elo Ehi kh_blocks Kak kh_fmiss Hx Hs).
Qed.

(* the cursor is addressable at the current state *)
Lemma kh_ra_cur : range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (ka0 cx) 16.
Proof.
  destruct kh_pre as (_ & _ & _ & HRAc & _).
  intros x Hx. exact (kh_saddr_now x (kh_cur x Hx) (HRAc x Hx)).
Qed.

(* the input byte at p = wp + adv: its shadow byte and its value at the current state *)
Lemma kh_sb : adv < k_wn cx -> exists s,
  aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF (k_wp cx + adv)) = Some s /\
  saddr_ok (k_wp cx + adv) s.
Proof.
  intros Hadv. pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Hadv0 & _) & _).
  destruct kh_pre as (_ & _ & _ & _ & _ & HRAi & _).
  exact (kh_saddr_now (k_wp cx + adv) (kh_in (k_wp cx + adv) ltac:(lia)) (HRAi (k_wp cx + adv) ltac:(lia))).
Qed.

Lemma kh_db : adv < k_wn cx -> exists b, mbyte SEGS (rdW W3 (ms_mem ms3)) (k_wp cx + adv) = Some b.
Proof.
  intros Hadv.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & (Kak & _) & (Hadv0 & _) & _).
  pose proof HB as ((HJ0 & _) & _ & _ & _ & _ & _ & _ & _ & _ & HD & HDL & _).
  destruct kh_pre as (_ & _ & _ & _ & _ & _ & (_ & HAPG & HAPL & HAPC)).
  unfold apart_gnl, apart in HAPG, HAPL, HAPC.
  destruct HD as (_ & _ & HD).
  assert (Hi : (Z.to_nat adv < length (k_d cx))%nat) by lia.
  destruct (nth_error (k_d cx) (Z.to_nat adv)) as [b|] eqn:Eb;
    [|apply nth_error_None in Eb; lia].
  exists b. pose proof (HD (Z.to_nat adv) Hi) as Hm. rewrite Eb, Z2Nat.id in Hm by lia.
  rewrite <- Hm. apply (mbyte_of_aview SEGS (w_H (k_W cx)) (w_H W3) (k_memc cx) (ms_mem ms3) (k_wp cx + adv)).
  apply (akept_akb_gx SK SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx)
    (k_W0 cx) (k_mem0 cx) (k_md0 cx) (k_own cx) (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx) (k_k cx)
    W3 (ms_mem ms3) (ksp cx - KERNEL_AK) (ksp cx) _ (k_wp cx + adv) HJ0 Kak (kh_in (k_wp cx + adv) ltac:(lia))).
  intros [HE | HS].
  - destruct HE as (r & Hr & Hx). unfold kernel_awr in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hx.
    + unfold NK_CHUNK, NK_OPEN, NK_SIZE in Hx, HAPG. lia.
    + unfold LONG_ALIAS_SIZE in Hx, HAPL. lia.
    + lia.
  - exact (proj2 (kh_akb (k_wp cx + adv) (kh_in (k_wp cx + adv) ltac:(lia))) HS).
Qed.

(* the cursor's bytes may be written: the call's ajw, moved to the current journal *)
Lemma kh_awr_cur : forall a, ka0 cx <= a < ka0 cx + 16 ->
  (awr_byte (k_STK cx) (k_sp0 cx) (k_FP cx) (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3
     ((KN_CID, fpos) :: k_own cx) a /\ ~ (k_sp0 cx <= a < k_sp0 cx + k_XO cx)) \/
  inG (k_G cx) a \/ (inFP (k_OUT cx) a /\ k_sp0 cx <= a < k_sp0 cx + k_XO cx).
Proof.
  intros a Ha.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & _) & _).
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & Hperm & _) & _).
  assert (HE : inFP (kernel_awr (k_regs cx) (km0 cx)) a).
  { exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16). split; [unfold kernel_awr; hd_inl |].
    cbn [fst snd]. unfold ka0 in Ha. lia. }
  destruct (Hajw a HE) as [[Haw Hnout] | [HGa | Hout]]; [left; split; [|exact Hnout] | right; left; exact HGa |
    right; right; exact Hout].
  destruct Haw as [Hw | [(Hfp & b0 & n0 & Hbn & Hr) | [(b0 & n0 & Hbn & Hnb & Hr) | (cid & pos & Hown & Hr)]]].
  - left. exact Hw.
  - right; left. split; [exact Hfp|]. exists b0, n0. split; [|exact Hr].
    exact (Permutation_in _ (Permutation_sym Hperm) Hbn).
  - right; right; left. exists b0, n0. split; [exact (Permutation_in _ (Permutation_sym Hperm) Hbn)|].
    split; [exact Hnb | exact Hr].
  - right; right; right. exists cid, pos. split; [right; exact Hown|]. rewrite kh_fa. exact Hr.
Qed.

(* THE LANDING: the run wrote only the cursor and the slot KS_ROOM; kernel_kit.v's frame lemmas carry every clause of
   kat but the cursor's, which the run set *)
Lemma kh_land : forall (ms' : machine_state) md' pc' adv' (X : Z -> Prop) (nl : list (Z * Z)),
  kms pc' ms' ->
  (forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) hd_keepz = true ->
     getr (ms_regs ms') r = getr (ms_regs ms3) r) ->
  (forall a, X a -> hd_X a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  0 <= adv' <= k_wn cx ->
  au64_at SEGS (rdW W3 (ms_mem ms')) (ka0 cx) (k_wp cx + adv') ->
  au64_at SEGS (rdW W3 (ms_mem ms')) (ka0 cx + 8) (k_wn cx - adv') ->
  kslots_eq cx W3 ms' nl ->
  kat B cx fpos pc' (kregs_chunk cx fpos ci) (kslots_setup cx fpos c ++ nl) (kfsh 0xf8 0xf8 0xf3) true adv'
    (Some j) k2 ly3 S3 W3 ms' md'.
Proof.
  intros ms' md' pc' adv' X nl Hkms HR HX UN HP Hfd Hfs Hadv' Hp' Hn' Hnl.
  pose proof HK as (_ & Hkr0 & Hkre & Hksv & Hkfr & Hksh & Hksl & Hkjbk & Hkkept & Hkcur & Hkg & Hkla).
  destruct kh_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & HKA).
  destruct kh_pre as (HAPF & HAPG & HAPL & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold apart_frame, apart_gnl, apart in HAPF, HAPG, HAPL.
  change (spZ (k_regs cx)) with (ksp cx) in HAPF. rewrite HKA in HAPF.
  (* F and its shadow *)
  pose proof Hkjbk as (_ & _ & _ & _ & (S1 & W1 & mem1 & md1 & HAR1 & Hfr1 & _) & _).
  assert (HinF : In (KN_CID, fpos) (frames S1)) by (rewrite Hfr1; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS (k_lyc cx) S1 W1 mem1 md1 KN_CID fpos HAR1 HinF) as (Hfa0 & Hfa1 & _).
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  assert (HFb : 4096 <= kF cx fpos /\ kF cx fpos + 16384 <= alloc_ceiling) by (unfold kF; lia).
  assert (HFSH : SHADOW_OFF + 512 <= kFSH cx fpos /\ kFSH cx fpos + 0x448 <= 0x10007fff8000)
    by (unfold kFSH, shadow_of_addr; unfold SHADOW_OFF; lia).
  (* the cursor: an application byte below 2 ^ 47, outside F *)
  assert (CA : forall x, ka0 cx <= x < ka0 cx + 16 ->
            (0 <= x < 2 ^ 47 /\ (x < kLowMemEnd \/ kHighMemBeg <= x)) /\ ~ aside_rng (k_lyc cx) KN_CID fpos x)
    by (intros x Hx; exact (kh_akb x (kh_cur x Hx))).
  assert (FNC : forall a, kF cx fpos <= a < kF cx fpos + 16384 -> ~ (ka0 cx <= a < ka0 cx + 16)).
  { intros a Ha Hc. apply (proj2 (CA a Hc)). left. unfold in_zr, frame_rng. cbn [fst snd].
    unfold kF in Ha. rewrite Hfb. lia. }
  (* a range that meets neither the cursor nor the slot KS_ROOM misses X *)
  assert (MISS : forall lo hi, (forall a, lo <= a < hi -> ka0 cx <= a < ka0 cx + 16 -> False) ->
            (forall a, lo <= a < hi -> ksp1 cx + 0xa8 <= a < ksp1 cx + 0xb0 -> False) ->
            forall a, lo <= a < hi -> ~ X a).
  { intros lo hi M1 M2 a Ha HXa. destruct (HX a HXa) as [Hc | Hs]; [exact (M1 a Ha Hc) | exact (M2 a Ha Hs)]. }
  assert (Msv : forall a, ksp cx - 104 <= a < ksp cx -> ~ X a) by (apply MISS; intros a Ha Hc; lia).
  assert (Mhd : forall a, kF cx fpos <= a < kF cx fpos + 24 -> ~ X a).
  { apply MISS; intros a Ha Hc; [exact (FNC a ltac:(lia) Hc) | lia]. }
  assert (Mfl : forall a, kF cx fpos + fs_frame_bytes KN_CID - 8 <= a < kF cx fpos + fs_frame_bytes KN_CID -> ~ X a).
  { apply MISS; intros a Ha Hc; rewrite Hfb in Ha; [exact (FNC a ltac:(lia) Hc) | lia]. }
  assert (Hl : Z.of_nat (length (kfsh 0xf8 0xf8 0xf3)) = 0x448) by (rewrite kfsh_length; reflexivity).
  assert (Msh : forall a, kFSH cx fpos <= a < kFSH cx fpos + Z.of_nat (length (kfsh 0xf8 0xf8 0xf3)) -> ~ X a).
  { rewrite Hl. apply MISS; intros a Ha Hc.
    - destruct (CA a Hc) as ((_ & [Hq | Hq]) & _); rewrite ?C3, ?C5 in Hq; unfold SHADOW_OFF in HFSH; lia.
    - lia. }
  pose proof (kslots_okb_spec (kslots_setup cx fpos c) eq_refl) as SOK.
  pose proof (kslots_avoidb_spec 0xa8 0xb0 (kslots_setup cx fpos c) eq_refl) as SAV.
  assert (Msl : forall ov, In ov (kslots_setup cx fpos c) -> 0 <= fst ov <= 0xf0 /\
            (forall a, ksp1 cx + fst ov <= a < ksp1 cx + fst ov + 8 -> ~ X a)).
  { intros ov Hov. pose proof (SOK ov Hov) as S1'. pose proof (SAV ov Hov) as S2'.
    split; [exact S1'|]. apply MISS; intros a Ha Hc; lia. }
  assert (Mgn : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ X a).
  { apply MISS; intros a Ha Hc; [lia | unfold LA_G_NL, NK_SIZE in Ha; lia]. }
  assert (Mla : forall a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + LONG_ALIAS_SIZE -> ~ X a).
  { apply MISS; intros a Ha Hc; [lia | unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE in Ha; lia]. }
  assert (HXin : forall a, X a -> kX_in cx fpos a).
  { intros a HXa. unfold kX_in. destruct (HX a HXa) as [Hc | Hs].
    - left. unfold kE, inFP. exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16).
      split; [unfold kernel_awr; hd_inl | cbn [fst snd]; unfold ka0 in Hc; lia].
    - right; right; right. rewrite HKA. lia. }
  pose proof (kfsh_fits 0xf8 0xf8 0xf3) as Hfits.
  pose proof (kk_grows_of_apresent _ _ _ _ HP) as HG.
  unfold kat.
  refine (conj Hkms (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))).
  - (* kregs0 *)
    unfold kregs0 in Hkr0 |- *.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); rewrite HR by (vm_compute; reflexivity);
      tauto.
  - (* kregs_eq *)
    unfold kregs_eq, kregs_chunk in Hkre |- *. rewrite !Forall_cons_iff in Hkre.
    destruct Hkre as (R19 & R21 & R22 & R24 & R25 & _). cbn [fst snd] in R19, R21, R22, R24, R25.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; rewrite HR by (vm_compute; reflexivity);
      assumption.
  - eapply ksaved_frame with (X := X); eassumption.
  - eapply kframe_frame with (X := X); eassumption.
  - eapply kshadow_frame with (X := X); eassumption.
  - unfold kslots_eq. apply Forall_app. split; [|exact Hnl].
    change (kslots_eq cx W3 ms' (kslots_setup cx fpos c)).
    eapply kslots_frame with (X := X) (sl := kslots_setup cx fpos c); try apply incl_refl; eassumption.
  - eapply kjbk_md; eassumption.
  - eapply kkept_frame with (X := X); eassumption.
  - (* kcursor: the run's words *)
    destruct Hkcur as (_ & _ & _ & HCW).
    split; [exact Hadv'|]. split; [exact Hp'|]. split; [exact Hn'|].
    intros i Hi. exact (writable_at_grows SEGS _ _ _ HG (HCW i Hi)).
  - eapply kgnl_frame with (X := X); eassumption.
  - eapply kla_frame with (X := X); eassumption.
Qed.

(* the environment's atoms *)
Lemma kh_Ef : forall p nv d s,
  ew (hd_E ms3 p nv d s) 18%nat = w64 (ka0 cx) /\ ew (hd_E ms3 p nv d s) 9%nat = w64 (ksp1 cx) /\
  ew (hd_E ms3 p nv d s) 20%nat = w64 SHADOW_OFF /\ ew (hd_E ms3 p nv d s) 32%nat = w64 p /\
  ew (hd_E ms3 p nv d s) 33%nat = w64 nv /\ ew (hd_E ms3 p nv d s) 34%nat = w64 d /\
  ew (hd_E ms3 p nv d s) 35%nat = w64 (SHADOW_OFF + p / 8) /\ ew (hd_E ms3 p nv d s) 36%nat = w64 s.
Proof.
  intros p nv d s. pose proof HK as (_ & Hkr0 & _).
  destruct Hkr0 as (R2 & R9 & R8 & R3 & R4 & R18 & R20).
  assert (ER : forall (jj : nat) (r : bv 5), Z.of_nat jj = bv_unsigned r -> ew (hd_E ms3 p nv d s) jj = getr (ms_regs ms3) r)
    by (intros jj r Hj; exact (ew_Eimg_Ereg_nat _ _ jj r Hj)).
  assert (EXT : forall jj, (jj < 5)%nat -> ew (hd_E ms3 p nv d s) (32 + jj) =
            nth jj [w64 p; w64 nv; w64 d; w64 (SHADOW_OFF + p / 8); w64 s] (Z_to_bv 64 0))
    by (intros jj Hj; unfold hd_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  split; [rewrite (ER 18%nat 18%bv eq_refl); exact R18|].
  split; [rewrite (ER 9%nat 9%bv eq_refl); exact R9|].
  split; [rewrite (ER 20%nat 20%bv eq_refl); exact R20|].
  split; [exact (EXT 0%nat ltac:(lia))|]. split; [exact (EXT 1%nat ltac:(lia))|].
  split; [exact (EXT 2%nat ltac:(lia))|]. split; [exact (EXT 3%nat ltac:(lia))|].
  exact (EXT 4%nat ltac:(lia)).
Qed.

(* the shadow entry of the cursor *)
Lemma kh_shok : forall p nv d s, sh_ok SEGS hd_Bx hd_SH (hd_E ms3 p nv d s) (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
  intros p nv d s. destruct (kh_Ef p nv d s) as (E18 & _ & E20 & _).
  pose proof (CAp := fun x Hx => proj1 (kh_akb x (kh_cur x Hx))).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (CAp (ka0 cx) ltac:(lia)) as (Ha0 & _). pose proof (CAp (ka0 cx + 15) ltac:(lia)) as (Ha15 & _).
  apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. unfold hd_Bx.
  rewrite (U_atom _ 20 SHADOW_OFF E20) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom _ 18 (ka0 cx) E18) by lia.
  split.
  - rewrite <- (aview_rd_of SEGS). rewrite Z.add_0_r. replace (16 - 0) with 16 by lia. exact kh_ra_cur.
  - intros a Ha. change (Z.min 0 16) with 0 in Ha. change (Z.max 0 16) with 16 in Ha.
    destruct (CAp a ltac:(lia)) as (_ & [Hq | Hq]); unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *; lia.
Qed.

(* the run's writes are bytes the journal admits *)
Lemma kh_awr1 : forall E, base_val E (Some 18%nat) = ka0 cx -> base_val E (Some 9%nat) = ksp1 cx ->
  awr_ok_x E hd_rs1 (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (ablocks B (k_ly cx) (k_S cx))
    (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros E BV18 BV9. destruct kh_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & HKA).
  unfold hd_rs1.
  apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]]]].
  - intros x Hx. unfold hd_cur in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV18 in Hx.
    apply kh_awr_cur. lia.
  - intros x Hx. unfold hd_slots in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV9 in Hx.
    left. split; [left; lia | lia].
  - intros x Hx. unfold hd_in in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia.
  - intros x Hx. unfold hd_ish in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia.
Qed.

Lemma kh_awr0 : forall E,
  awr_ok_x E hd_rs0 (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (ablocks B (k_ly cx) (k_S cx))
    (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros E. unfold hd_rs0. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros x Hx. unfold hd_cur in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia.
Qed.

(* THE STATE AT +0x51c, n >= 1: the four cases of the input byte's shadow byte and of the mode bit *)
Lemma kh_seat1 : forall (fast raw : bool) s (b : byte),
  adv < k_wn cx ->
  aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF (k_wp cx + adv)) = Some s ->
  saddr_ok (k_wp cx + adv) s ->
  mbyte SEGS (rdW W3 (ms_mem ms3)) (k_wp cx + adv) = Some b ->
  (if fast then s = 0 else s <> 0) ->
  (if raw then bv_unsigned b mod 2 <> 0 else bv_unsigned b mod 2 = 0) ->
  st_ok_pi SEGS pa_val (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) (bv_unsigned b) s) (hd_ss1 (hd_cs fast raw))
    (restrict (w_H W3) ms3).
Proof.
  intros fast raw s b Hadv Hs Hsok Hb Hf Hr.
  pose proof HK as (Hkms & Hkr0 & Hkre & _ & _ & _ & Hksl & _ & _ & Hkcur & _ & _).
  destruct Hkms as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  unfold kregs_eq, kregs_chunk in Hkre. rewrite !Forall_cons_iff in Hkre.
  destruct Hkre as (R19 & R21 & R22 & R24 & R25 & _). cbn [fst snd] in R19, R21, R22, R24, R25.
  unfold kslots_eq in Hksl. rewrite Forall_forall in Hksl.
  pose proof (Hksl (KS_CSH, shadow_of_addr SHADOW_OFF (ka0 cx)) ltac:(unfold kslots_setup; hd_inl)) as SL_CSH.
  cbn [fst snd] in SL_CSH. pose proof (kh_rdword_range _ _ _ _ SL_CSH) as Rg_CSH.
  destruct Hkcur as (Hadv0 & HCP & HCN & HCW).
  destruct kh_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & HKA).
  destruct kh_pre as (HAPF & _ & _ & _ & HAMR & _ & (HAPFi & _ & _ & HAPCi)).
  unfold apart_frame, apart in HAPF, HAPFi, HAPCi. unfold amem_range in HAMR.
  change (spZ (k_regs cx)) with (ksp cx) in HAPF, HAPFi.
  change (aarg (k_regs cx) 0) with (ka0 cx) in HAPF, HAPCi. rewrite HKA in HAPF, HAPFi.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (CAp := fun x Hx => proj1 (kh_akb x (kh_cur x Hx))).
  pose proof (CAp (ka0 cx) ltac:(lia)) as (Ha0 & Hc0). pose proof (CAp (ka0 cx + 15) ltac:(lia)) as (Ha15 & Hc15).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _).
  pose proof (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HPRES.
  pose proof (bv_unsigned_in_range 8 b) as Hbr. change (bv_modulus 8) with 256 in Hbr.
  (* the shadow byte s, as a byte *)
  unfold aview in Hs.
  destruct (mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (shadow_of_addr SHADOW_OFF (k_wp cx + adv)))
    as [bs|] eqn:Ebs; [|discriminate Hs].
  cbn [option_map] in Hs. injection Hs as Hs.
  assert (Hsr : 0 <= s < 8) by (pose proof (bv_unsigned_in_range 8 bs); unfold saddr_ok in Hsok; lia).
  destruct (kh_Ef (k_wp cx + adv) (k_wn cx - adv) (bv_unsigned b) s)
    as (E18 & E9 & E20 & E32 & E33 & E34 & E35 & E36).
  remember (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) (bv_unsigned b) s) as E eqn:HEdef.
  assert (BV : forall nn v, ew E nn = w64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some nn) = v).
  { intros nn v Hn Hv. cbn [base_val]. rewrite Hn. unfold w64. apply unsigned_lit_small. exact Hv. }
  assert (Hp64 : 0 <= k_wp cx + adv /\ k_wp cx + adv + 1 <= 2 ^ 47) by (unfold kLowMemEnd, kHighMemEnd in HAMR; lia).
  pose proof (BV 18%nat (ka0 cx) E18 ltac:(lia)) as BV18. pose proof (BV 9%nat (ksp1 cx) E9 ltac:(lia)) as BV9.
  pose proof (BV 32%nat (k_wp cx + adv) E32 ltac:(lia)) as BV32.
  assert (Hq : SHADOW_OFF <= SHADOW_OFF + (k_wp cx + adv) / 8 < SHADOW_OFF + 2 ^ 44)
    by (split; [pose proof (Z.div_pos (k_wp cx + adv) 8 ltac:(lia) ltac:(lia)); lia |
                pose proof (Z.div_lt_upper_bound (k_wp cx + adv) 8 (2 ^ 44) ltac:(lia) ltac:(lia)); lia]).
  pose proof (BV 35%nat (SHADOW_OFF + (k_wp cx + adv) / 8) E35 ltac:(unfold SHADOW_OFF in *; lia)) as BV35.
  rewrite (kh_ms_shape ms3 (BASE + kpc KP_HEAD) Hpc Hrv Hsvc Hrom Hfrg Hfcs), restrict_mkst_fx.
  assert (HS0 : st_ok_pi SEGS pa_val E (mkSS (kpc KP_HEAD) sr_atoms hd_rs1 None
                 (mkFacts hd_atoms (hd_cs fast raw) hd_alias))
                 (mkst (ms_regs ms3) (w64 (BASE + kpc KP_HEAD)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS))).
  { apply pa_entry_st_ok_full.
    - rewrite HEdef. unfold hd_E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold hd_rs1. repeat apply Forall_cons; [..|apply Forall_nil].
      + unfold hd_cur, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV18. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (HCW o Ho)|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * apply (chunk_ok_val SEGS E _ (ka0 cx) 0 8 (SOff 32 0) (k_wp cx + adv));
            [apply sv_off0; exact E32 | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact HCP].
        * apply (chunk_ok_val SEGS E _ (ka0 cx) 8 8 (SOff 33 0) (k_wn cx - adv));
            [apply sv_off0; exact E33 | cbn; lia | cbn; lia | exact HCN].
      + unfold hd_slots, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV9. split; [lia|]. split; [lia|].
        split; [intros o Ho; apply (kn_apresent_writable SEGS); apply HPRES; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (kh_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xc0 (hd_sh 18 0) (shadow_of_addr SHADOW_OFF (ka0 cx)));
          [|exact SL_CSH].
        rewrite (kh_denot_sh E 18 (ka0 cx) 0 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20).
        rewrite Z.add_0_r. reflexivity.
      + unfold hd_in, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (k_wp cx + adv) 0 1 (SOff 34 0) (bv_unsigned b));
          [apply sv_off0; exact E34 | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact (kh_val1 _ _ _ Hb)].
      + unfold hd_ish, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV35. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|].
        split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (SHADOW_OFF + (k_wp cx + adv) / 8) 0 1 (SOff 36 0) s);
          [apply sv_off0; exact E36 | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r, <- Hs. exact (kh_val1 _ _ _ Ebs).
    - apply pairwise_disjoint_of_extents.
      unfold hd_rs1, hd_cur, hd_slots, hd_in, hd_ish, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV18, BV9, BV32, BV35.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - Hadv Hadv0 HAPF HAPFi HAPCi HAMR Hc0 Hc15 Ha0 Ha15 Hp64 Hq G1 G2 G3 G4 G5 G6 G7 C1a C3 C5.
      unfold kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *.
      repeat split; lia.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split].
      + unfold hd_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E18, E9, E20, E34, E36. unfold w64.
        rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
        change (2 ^ 0) with 1. change (2 ^ 5) with 32. rewrite !Z.mod_1_r.
        unfold SHADOW_OFF.
        repeat split; first [lia | exact G8 | exact I].
      + assert (D33 : sv_denot E (SOff 33 0) = Z_to_bv 64 (k_wn cx - adv)) by (apply sv_off0; exact E33).
        assert (D36 : sv_denot E (SOff 36 0) = Z_to_bv 64 s) by (apply sv_off0; exact E36).
        assert (D0 : sv_denot E (SLit 0) = Z_to_bv 64 0) by reflexivity.
        assert (Dmode : sv_denot E (SAlu ALU_AND (SOff 34 0) (SLit 1)) = Z_to_bv 64 (bv_unsigned b mod 2)).
        { rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
          rewrite (U_atom_off E 34 (bv_unsigned b) 0 E34 ltac:(lia) ltac:(lia)), Z.add_0_r.
          change (zcanon 1) with 1.
          assert (Hl1 : Z.land (bv_unsigned b) 1 = bv_unsigned b mod 2)
            by (change 1 with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
          rewrite Hl1. apply zcanon_id. unfold M64. pose proof (Z.mod_pos_bound (bv_unsigned b) 2). lia. }
        assert (Dslow : sv_denot E (SAlu ALU_AND (SOff 32 0) (SLit 7)) = Z_to_bv 64 ((k_wp cx + adv) mod 8)).
        { rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
          rewrite (U_atom_off E 32 (k_wp cx + adv) 0 E32 ltac:(lia) ltac:(lia)), Z.add_0_r.
          change (zcanon 7) with 7.
          assert (Hl7 : Z.land (k_wp cx + adv) 7 = (k_wp cx + adv) mod 8)
            by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
          rewrite Hl7. apply zcanon_id. unfold M64. pose proof (Z.mod_pos_bound (k_wp cx + adv) 8). lia. }
        assert (BEQ : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
                  branch_taken BC_EQ (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y)).
        { intros x y Hx Hy. unfold branch_taken, bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. }
        assert (BNE : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
                  branch_taken BC_NE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x =? y)).
        { intros x y Hx Hy. change BC_NE with (neg_bc BC_EQ). rewrite branch_taken_neg, BEQ by assumption.
          reflexivity. }
        pose proof (Z.mod_pos_bound (bv_unsigned b) 2 ltac:(lia)) as Hm2.
        pose proof (Z.mod_pos_bound (k_wp cx + adv) 8 ltac:(lia)) as Hm8.
        destruct fast, raw; cbv iota in Hf, Hr; unfold hd_cs, hd_cmode; cbn [conds_ok]; unfold acond_ok;
          cbn [ac_c ac_a ac_b];
          rewrite ?D33, ?D36, ?D0, ?Dmode, ?Dslow;
          repeat match goal with |- _ /\ _ => split end;
          try exact I;
          first [ rewrite BNE by lia; apply negb_true_iff, Z.eqb_neq; lia
                | rewrite BEQ by lia; apply Z.eqb_eq; lia
                | apply kh_blt; unfold saddr_ok in Hsok; lia ].
      + unfold hd_alias. cbn [alias_ok]. split; [|exact I].
        rewrite (kh_denot_sh E 32 (k_wp cx + adv) 0 E32 ltac:(lia) ltac:(lia) ltac:(lia) E20).
        rewrite (sv_off0 E 35 _ E35). rewrite Z.add_0_r. reflexivity. }
  assert (HD19 : sv_denot E (SOff 18 8) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 19))).
  { rewrite R19. cbn [sv_denot]. rewrite E18. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (HD24 : sv_denot E (hd_sh 18 8) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 24))).
  { rewrite R24, (kh_denot_sh E 18 (ka0 cx) 8 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20).
    unfold w64, kS8, shadow_of_addr. reflexivity. }
  pose proof (ast_ok_pi_set_reg_fp E _ _ (Z_to_bv 5 (Z.of_nat 19)) (SOff 18 8) HS0 eq_refl HD19) as HS1.
  pose proof (ast_ok_pi_set_reg_fp E _ _ (Z_to_bv 5 (Z.of_nat 24)) (hd_sh 18 8) HS1 eq_refl HD24) as HS2.
  exact HS2.
Qed.

(* THE STATE AT +0x51c, n = 0 *)
Lemma kh_seat0 : k_wn cx - adv = 0 ->
  st_ok_pi SEGS pa_val (hd_E ms3 (k_wp cx + adv) 0 0 0) hd_ss0 (restrict (w_H W3) ms3).
Proof.
  intros Hn0.
  pose proof HK as (Hkms & Hkr0 & Hkre & _ & _ & _ & _ & _ & _ & Hkcur & _ & _).
  destruct Hkms as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  unfold kregs_eq, kregs_chunk in Hkre. rewrite !Forall_cons_iff in Hkre.
  destruct Hkre as (R19 & R21 & R22 & R24 & R25 & _). cbn [fst snd] in R19, R21, R22, R24, R25.
  destruct Hkcur as (Hadv0 & HCP & HCN & HCW). rewrite Hn0 in HCN.
  destruct kh_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & HKA).
  destruct kh_pre as (_ & _ & _ & _ & HAMR & _). unfold amem_range in HAMR.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (CAp := fun x Hx => proj1 (kh_akb x (kh_cur x Hx))).
  pose proof (CAp (ka0 cx) ltac:(lia)) as (Ha0 & _). pose proof (CAp (ka0 cx + 15) ltac:(lia)) as (Ha15 & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _).
  destruct (kh_Ef (k_wp cx + adv) 0 0 0) as (E18 & E9 & E20 & E32 & E33 & E34 & E35 & E36).
  remember (hd_E ms3 (k_wp cx + adv) 0 0 0) as E eqn:HEdef.
  assert (Hp64 : 0 <= k_wp cx + adv <= 2 ^ 47) by (unfold kLowMemEnd, kHighMemEnd in HAMR; lia).
  assert (BV18 : base_val E (Some 18%nat) = ka0 cx).
  { cbn [base_val]. rewrite E18. unfold w64. apply unsigned_lit_small. lia. }
  rewrite (kh_ms_shape ms3 (BASE + kpc KP_HEAD) Hpc Hrv Hsvc Hrom Hfrg Hfcs), restrict_mkst_fx.
  assert (HS0 : st_ok_pi SEGS pa_val E (mkSS (kpc KP_HEAD) sr_atoms hd_rs0 None (mkFacts hd_atoms [] hd_alias))
                 (mkst (ms_regs ms3) (w64 (BASE + kpc KP_HEAD)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS))).
  { apply pa_entry_st_ok_full.
    - rewrite HEdef. unfold hd_E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold hd_rs0. apply Forall_cons; [|apply Forall_nil].
      unfold hd_cur, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite BV18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (chunk_ok_val SEGS E _ (ka0 cx) 0 8 (SOff 32 0) (k_wp cx + adv));
          [apply sv_off0; exact E32 | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact HCP].
      + apply (chunk_ok_val SEGS E _ (ka0 cx) 8 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact HCN].
    - unfold hd_rs0. cbn [pairwise_disjoint all_disjoint]. tauto.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split].
      + unfold hd_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E18, E9, E20, E34, E36. unfold w64.
        rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
        change (2 ^ 0) with 1. change (2 ^ 5) with 32. rewrite !Z.mod_1_r.
        unfold SHADOW_OFF.
        repeat split; first [lia | exact G8 | exact I].
      + exact I.
      + unfold hd_alias. cbn [alias_ok]. split; [|exact I].
        rewrite (kh_denot_sh E 32 (k_wp cx + adv) 0 E32 ltac:(lia) ltac:(lia) ltac:(lia) E20).
        rewrite (sv_off0 E 35 _ E35). rewrite Z.add_0_r. reflexivity. }
  assert (HD19 : sv_denot E (SOff 18 8) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 19))).
  { rewrite R19. cbn [sv_denot]. rewrite E18. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (HD24 : sv_denot E (hd_sh 18 8) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 24))).
  { rewrite R24, (kh_denot_sh E 18 (ka0 cx) 8 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20).
    unfold w64, kS8, shadow_of_addr. reflexivity. }
  pose proof (ast_ok_pi_set_reg_fp E _ _ (Z_to_bv 5 (Z.of_nat 19)) (SOff 18 8) HS0 eq_refl HD19) as HS1.
  pose proof (ast_ok_pi_set_reg_fp E _ _ (Z_to_bv 5 (Z.of_nat 24)) (hd_sh 18 8) HS1 eq_refl HD24) as HS2.
  exact HS2.
Qed.

(* the slot KS_ROOM and the cursor's words at a run's end, off its regions *)
Lemma kh_room : forall E (msF : machine_state) lo hi wlo whi cs,
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem msF)) (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 9%nat) = ksp1 cx -> In (YP09.mkChunk 0xa8 (CVal 8 (SLit 4097))) cs ->
  kslots_eq cx W3 msF [(KS_ROOM, 4097)].
Proof.
  intros E msF lo hi wlo whi cs HR Hb Hin. unfold kslots_eq. apply Forall_cons; [|apply Forall_nil].
  cbn [fst snd]. exact (kh_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) cs lo hi wlo whi 0xa8 (SLit 4097)
    4097 HR Hb Hin eq_refl ltac:(lia)).
Qed.

Lemma kh_curw : forall E (msF : machine_state) lo hi wlo whi cs off e v,
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem msF)) (YP09.mkRegion (Some 18%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 18%nat) = ka0 cx -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  au64_at SEGS (rdW W3 (ms_mem msF)) (ka0 cx + off) v.
Proof.
  intros E msF lo hi wlo whi cs off e v HR Hb Hin He Hv.
  exact (field_of_region (segs := SEGS) E _ 18%nat (ka0 cx) cs lo hi wlo whi off 8 e v HR Hb Hin He
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hv) ltac:(change (Z.of_N 8) with 8; lia)).
Qed.

Lemma kh_apres_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' a Hg (Hh & b & Hb). split; [exact Hh|].
  specialize (Hg (Z_to_bv 64 a)). unfold mrestrict in Hg. rewrite Hh in Hg.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [exists b'; reflexivity|].
  exfalso. apply Hg; [rewrite Hb; discriminate | reflexivity].
Qed.

(* the run's writable windows: the cursor and the slot KS_ROOM (n >= 1), nothing (n = 0) *)
Lemma kh_win1 : forall E, base_val E (Some 18%nat) = ka0 cx -> base_val E (Some 9%nat) = ksp1 cx ->
  forall bb wlo whi a, In (bb, wlo, whi) (windows hd_rs1) -> base_val E bb + wlo <= a < base_val E bb + whi -> hd_X a.
Proof.
  intros E BV18 BV9 bb wlo whi a Hin Ha.
  assert (Hw : windows hd_rs1 = [(Some 18%nat, 0, 16); (Some 9%nat, 168, 176); (Some 32%nat, 0, 0); (Some 35%nat, 0, 0)])
    by (vm_compute; reflexivity).
  rewrite Hw in Hin. cbn [In] in Hin. unfold hd_X.
  destruct Hin as [Hq | [Hq | [Hq | [Hq | []]]]]; injection Hq as <- <- <-.
  - rewrite BV18 in Ha. left. lia.
  - rewrite BV9 in Ha. right. lia.
  - lia.
  - lia.
Qed.

Lemma kh_win0 : forall E bb wlo whi a, In (bb, wlo, whi) (windows hd_rs0) ->
  base_val E bb + wlo <= a < base_val E bb + whi -> hd_X a.
Proof.
  intros E bb wlo whi a Hin Ha.
  assert (Hw : windows hd_rs0 = [(Some 18%nat, 0, 0)]) by (vm_compute; reflexivity).
  rewrite Hw in Hin. cbn [In] in Hin.
  destruct Hin as [Hq | []]; injection Hq as <- <- <-. lia.
Qed.

(* THE END OF A RUN: the cut at its stop pc, from the end state (its pc, the registers it did not write, its frame) *)
Lemma kh_after : forall E ss0 ss' (msF : machine_state) md' (pcF adv' : Z) nl,
  st_ok_pi SEGS pa_val E ss0 (restrict (w_H W3) ms3) ->
  st_ok_pi SEGS pa_val E ss' (restrict (w_H W3) msF) ->
  ss_resv ss' = None -> ss_pc ss' = kpc pcF ->
  forallb (fun k => sv_eqb (sr_get (ss_regs ss') (Z_to_bv 5 k)) (sr_get (ss_regs ss0) (Z_to_bv 5 k))) hd_keepz = true ->
  frame_of E (ss_mem ss0) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem msF)) ->
  (forall bb wlo whi a, In (bb, wlo, whi) (windows (ss_mem ss0)) -> base_val E bb + wlo <= a < base_val E bb + whi ->
     hd_X a) ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem msF)) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  0 <= adv' <= k_wn cx ->
  au64_at SEGS (rdW W3 (ms_mem msF)) (ka0 cx) (k_wp cx + adv') ->
  au64_at SEGS (rdW W3 (ms_mem msF)) (ka0 cx + 8) (k_wn cx - adv') ->
  kslots_eq cx W3 msF nl ->
  kat B cx fpos pcF (kregs_chunk cx fpos ci) (kslots_setup cx fpos c ++ nl) (kfsh 0xf8 0xf8 0xf3) true adv'
    (Some j) k2 ly3 S3 W3 msF md'.
Proof.
  intros E ss0 ss' msF md' pcF adv' nl HS0 HS Hrv Hpc Hkeep HFr HW HG Hfd Hfs Hadv' Hp' Hn' Hnl.
  assert (HKMS : kms pcF msF).
  { pose proof (st_ok_pi_restrict_mkst (w_H W3) E ss' msF HS Hrv) as Hsh. rewrite Hpc in Hsh.
    unfold kms. rewrite Hsh. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
    repeat split; reflexivity. }
  apply (kh_land msF md' pcF adv' hd_X nl HKMS
    (kh_reg_same E ss0 ss' (w_H W3) ms3 msF hd_keepz HS0 HS Hkeep) (fun a Ha => Ha)
    (kept_of_frame (segs := SEGS) E (ss_mem ss0) (w_H W3) (ms_mem ms3) (ms_mem msF) hd_X HFr HW)
    (fun a Hp => kh_apres_grows _ _ _ a HG Hp) Hfd Hfs Hadv' Hp' Hn' Hnl).
Qed.

(* after a run of the n >= 1 state to its stop pcF: the cut, adv + 1 bytes read, slot KS_ROOM = 4097 *)
Ltac kh_end1 CONT pcF HS HS0 HJ E BV18u BV9u DP DN :=
  let msF := fresh "msF" in
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end;
  repeat rewrite wvb_collapse in HJ;
  apply (CONT msF _ HJ);
  let HR0 := fresh "HR0" in let HR1 := fresh "HR1" in
  spregion HS 0%nat HR0; spregion HS 1%nat HR1;
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
    eapply (kh_after E _ _ msF _ pcF _ [(KS_ROOM, 4097)] HS0 HS eq_refl ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) HFr (kh_win1 E BV18u BV9u) HG) end;
  [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
  | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
  | lia
  | let VP := fresh "VP" in
    pose proof (kh_curw E msF _ _ _ _ _ 0 (SOff 32 1) _ HR0 BV18u ltac:(hd_inl) DP ltac:(lia)) as VP;
    rewrite Z.add_0_r in VP; exact VP
  | exact (kh_curw E msF _ _ _ _ _ 8 (SOff 33 (-1)) _ HR0 BV18u ltac:(hd_inl) DN ltac:(lia))
  | exact (kh_room E msF _ _ _ _ _ HR1 BV9u ltac:(hd_inl)) ].

(* THE PHASE at this context: the five runs and their cuts *)
Lemma kh_go : forall (Q : world SEGS -> config -> Prop),
  (forall ms' md', ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx)
       (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
     kat B cx fpos KP_MZ (kregs_chunk cx fpos ci) (kslots_setup cx fpos c) (kfsh 0xf8 0xf8 0xf3) true (k_wn cx)
       (Some j) k2 ly3 S3 W3 ms' md' ->
     SRr SEGS W3 (mkCfg ms' md') Q) ->
  (forall ms' md', ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx)
       (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
     kat B cx fpos KP_MSG0 (kregs_chunk cx fpos ci) (kslots_setup cx fpos c ++ [(KS_ROOM, 4097)])
       (kfsh 0xf8 0xf8 0xf3) true (adv + 1) (Some j) k2 ly3 S3 W3 ms' md' ->
     SRr SEGS W3 (mkCfg ms' md') Q) ->
  (forall ms' md', ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx)
       (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
     kat B cx fpos KP_RAW (kregs_chunk cx fpos ci) (kslots_setup cx fpos c ++ [(KS_ROOM, 4097)])
       (kfsh 0xf8 0xf8 0xf3) true (adv + 1) (Some j) k2 ly3 S3 W3 ms' md' ->
     SRr SEGS W3 (mkCfg ms' md') Q) ->
  SRr SEGS W3 (mkCfg ms3 md3) Q.
Proof.
  intros Q CMZ CMSG CRAW.
  pose proof HB as ((HJ0 & HGok & _) & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _).
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Hadv0 & _) & _).
  destruct kh_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & HKA).
  destruct kh_pre as (_ & _ & _ & _ & HAMR & _). unfold amem_range in HAMR.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (CAp := fun x Hx => proj1 (kh_akb x (kh_cur x Hx))).
  pose proof (CAp (ka0 cx) ltac:(lia)) as (Ha0 & _). pose proof (CAp (ka0 cx + 15) ltac:(lia)) as (Ha15 & _).
  assert (Hp64 : 0 <= k_wp cx + adv /\ k_wp cx + adv <= 2 ^ 47) by (unfold kLowMemEnd, kHighMemEnd in HAMR; lia).
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  destruct (Z.eq_dec (k_wn cx - adv) 0) as [Hn0 | Hn1].
  - (* n = 0: +0x51c .. +0x530, j +0x1e7c; nothing written *)
    remember (hd_E ms3 (k_wp cx + adv) 0 0 0) as E eqn:HEdef.
    assert (HS : st_ok_pi SEGS pa_val E hd_ss0 (restrict (w_H W3) ms3)) by (rewrite HEdef; exact (kh_seat0 Hn0)).
    assert (EF : ew E 18%nat = w64 (ka0 cx) /\ ew E 32%nat = w64 (k_wp cx + adv)).
    { rewrite HEdef. destruct (kh_Ef (k_wp cx + adv) 0 0 0) as (E18 & _ & _ & E32 & _). tauto. }
    destruct EF as (E18 & E32).
    assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; unfold hd_E; apply Eimg_env).
    assert (BV18u : bv_unsigned (ew E 18%nat) = ka0 cx) by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
    assert (SHOK : sh_ok SEGS hd_Bx hd_SH E (mrestrict (w_H W3) (ms_mem ms3))) by (rewrite HEdef; apply kh_shok).
    pose proof HS as HS0. pose proof HJ3 as HJ.
    paj_run_to_tok RUNTO HS HJ SHOK hd_span (kpc KP_MZ).
    { exact (kh_awr0 E). }
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
    repeat rewrite wvb_collapse in HJ.
    apply (CMZ msF _ HJ).
    spregion HS 0%nat HR0.
    rewrite <- (app_nil_r (kslots_setup cx fpos c)).
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
      eapply (kh_after E _ _ msF _ KP_MZ _ [] HS0 HS eq_refl ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) HFr (kh_win0 E) HG) end.
    + repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
    + repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
    + lia.
    + replace (k_wp cx + k_wn cx) with (k_wp cx + adv) by lia.
      pose proof (kh_curw E msF _ _ _ _ _ 0 (SOff 32 0) _ HR0 BV18u ltac:(hd_inl) (sv_off0 E 32 _ E32) ltac:(lia))
        as VP.
      rewrite Z.add_0_r in VP. exact VP.
    + replace (k_wn cx - k_wn cx) with 0 by lia.
      exact (kh_curw E msF _ _ _ _ _ 8 (SLit 0) 0 HR0 BV18u ltac:(hd_inl) eq_refl ltac:(lia)).
    + unfold kslots_eq. apply Forall_nil.
  - (* n >= 1: the input byte's check, the mode byte, slot KS_ROOM := 4097, on to +0x594 or +0x1f30 *)
    assert (Hadv : adv < k_wn cx) by lia.
    destruct (kh_sb Hadv) as (s & Hs & Hsok). destruct (kh_db Hadv) as (b & Hb).
    assert (GO : forall (fast raw : bool), (if fast then s = 0 else s <> 0) ->
              (if raw then bv_unsigned b mod 2 <> 0 else bv_unsigned b mod 2 = 0) -> SRr SEGS W3 (mkCfg ms3 md3) Q).
    { intros fast raw Hf Hr.
      remember (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) (bv_unsigned b) s) as E eqn:HEdef.
      assert (HS : st_ok_pi SEGS pa_val E (hd_ss1 (hd_cs fast raw)) (restrict (w_H W3) ms3))
        by (rewrite HEdef; exact (kh_seat1 fast raw s b Hadv Hs Hsok Hb Hf Hr)).
      assert (EF : ew E 18%nat = w64 (ka0 cx) /\ ew E 9%nat = w64 (ksp1 cx) /\
                   ew E 32%nat = w64 (k_wp cx + adv) /\ ew E 33%nat = w64 (k_wn cx - adv)).
      { rewrite HEdef. destruct (kh_Ef (k_wp cx + adv) (k_wn cx - adv) (bv_unsigned b) s)
          as (E18 & E9 & _ & E32 & E33 & _). tauto. }
      destruct EF as (E18 & E9 & E32 & E33).
      assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; unfold hd_E; apply Eimg_env).
      assert (BV18u : bv_unsigned (ew E 18%nat) = ka0 cx) by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
      assert (BV9u : bv_unsigned (ew E 9%nat) = ksp1 cx) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
      assert (SHOK : sh_ok SEGS hd_Bx hd_SH E (mrestrict (w_H W3) (ms_mem ms3))) by (rewrite HEdef; apply kh_shok).
      assert (DP : sv_denot E (SOff 32 1) = Z_to_bv 64 (k_wp cx + (adv + 1))).
      { cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
      assert (DN : sv_denot E (SOff 33 (-1)) = Z_to_bv 64 (k_wn cx - (adv + 1))).
      { cbn [sv_denot]. rewrite E33. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
      pose proof HS as HS0. pose proof HJ3 as HJ.
      destruct fast, raw.
      + (* the shadow byte 0, the mode bit 1: the raw path *)
        paj_run_to_tok RUNTO HS HJ SHOK hd_span (kpc KP_RAW).
        { exact (kh_awr1 E BV18u BV9u). }
        kh_end1 CRAW KP_RAW HS HS0 HJ E BV18u BV9u DP DN.
      + (* the shadow byte 0, the mode bit 0: the message path *)
        paj_run_to_tok RUNTO HS HJ SHOK hd_span (kpc KP_MSG0).
        { exact (kh_awr1 E BV18u BV9u). }
        kh_end1 CMSG KP_MSG0 HS HS0 HJ E BV18u BV9u DP DN.
      + (* the shadow byte s <> 0 with (p & 7) < s (+0x2110), the mode bit 1 *)
        paj_run_to_tok RUNTO HS HJ SHOK hd_span (kpc KP_RAW).
        { exact (kh_awr1 E BV18u BV9u). }
        kh_end1 CRAW KP_RAW HS HS0 HJ E BV18u BV9u DP DN.
      + (* the shadow byte s <> 0 with (p & 7) < s, the mode bit 0 *)
        paj_run_to_tok RUNTO HS HJ SHOK hd_span (kpc KP_MSG0).
        { exact (kh_awr1 E BV18u BV9u). }
        kh_end1 CMSG KP_MSG0 HS HS0 HJ E BV18u BV9u DP DN. }
    destruct (Z.eq_dec s 0) as [Hs0 | Hs0]; destruct (Z.eq_dec (bv_unsigned b mod 2) 0) as [Hm0 | Hm0].
    + exact (GO true false Hs0 Hm0).
    + exact (GO true true Hs0 Hm0).
    + exact (GO false false Hs0 Hm0).
    + exact (GO false true Hs0 Hm0).
Qed.

End h.

Theorem kn_head : forall POST (Rc : kcx -> Z -> Prop),
  kfrom SK B POST (kin_raw B Rc) -> kfrom SK B POST (kin_msg0 B Rc) -> kfrom SK B POST (kin_mz B Rc) ->
  kfrom SK B POST (kin_head B Rc).
Proof.
  intros POST Rc HRAW HMSG HMZ cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & adv & HRcv & Hcr & Hci & Hj & HK).
  apply (kh_go cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv HB HJ HK (POST cx)).
  - intros ms' md' HJ' HK'. apply (HMZ cx fpos k2 ly3 S3 W3 ms' md' HB HJ' Hfrm).
    exists c, ci, j. split; [exact HRcv|]. split; [exact Hcr|]. split; [exact Hci|]. split; [exact Hj | exact HK'].
  - intros ms' md' HJ' HK'. apply (HMSG cx fpos k2 ly3 S3 W3 ms' md' HB HJ' Hfrm).
    exists c, ci, j, (adv + 1). split; [exact HRcv|]. split; [exact Hcr|]. split; [exact Hci|].
    split; [exact Hj | exact HK'].
  - intros ms' md' HJ' HK'. apply (HRAW cx fpos k2 ly3 S3 W3 ms' md' HB HJ' Hfrm).
    exists c, ci, j, (adv + 1). split; [exact HRcv|]. split; [exact Hcr|]. split; [exact Hci|].
    split; [exact Hj | exact HK'].
Qed.

End b.
End a.

Print Assumptions kn_head.
