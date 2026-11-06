(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the parts of sup_quarantine_clear's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan) that need no callee statement: the walk's points in B's listing, the listing's 22 slots,
   the 32-byte frame, the symbolic states and seeds of its segments, the verb literal and the model's step. In the
   form of lib/A/Prog/sup_quarantine_clear_s2.v (the A walk's seeds, a working branch f2402580166),
   re-derived on B's code, which differs from A's (below). *)

(* sup_quarantine_clear on B (recorder.c:411-417; entry BASE + AF_sup_quarantine_clear = 0x8bdb0, 22 instructions,
   88 bytes; measured with capstone on the .symtab entry of fuzz_command.asan-ubsan, sha256 658cefbe...):
     0x8bdb0 .. 0x8bdc4  addi sp,sp,-32; sd ra,24(sp); sd s0,16(sp); sd s1,8(sp); mv s0,a0; li a0,11
     0x8bdc8             jal record                      (0x8a728)
     0x8bdcc .. 0x8bdd0  mv s1,a0; mv a1,s0
     0x8bdd4             jal arg_s                       (0x8a820)
     0x8bdd8 .. 0x8bde0  auipc a0,0xfff96; addi a0,a0,0x68 (= 0x21e40, "quarantine_clear"); li a1,16
     0x8bde4             jal rec_shape_of                (0x896d4)
     0x8bde8 .. 0x8be00  li a2,1; mv a1,a0; mv a0,s1; ld ra,24(sp); ld s0,16(sp); ld s1,8(sp); addi sp,sp,32
     0x8be04             j answer                        (0x8aa10, the tail jump)
   No branch, no loop, no inline ASan check (no call of an __asan_report entry), no UBSan trap site (no unimp or ebreak), no
   load or store through an auipc base (the one auipc forms the literal's address: listing PHi a0 167, then
   PAddHi a0 a0 167 (A_OBJ 70) 0x0, which sets a0 to the object atom; cmd_val_objs gives its value, and the A_HI
   value 0x21dd8 is not used). A's code (0x8b844, 91 instructions) inlined record() (the slot and spill arms,
   rec_calls_free) and the stores of fn, nargs and args[0] with their 4 inline checks, and called xstrdup; B calls
   record() and arg_s() instead, which carry those checks themselves. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_calls_free_c record_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas CmdRecAns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the walk's points in the listing *)
Definition SQB_E : Z := AF_sup_quarantine_clear.            (* the entry (0x8bdb0) *)
Definition SQB_RETR : Z := AF_sup_quarantine_clear + 0x1c.  (* after the call of record (0x8bdcc) *)
Definition SQB_RETA : Z := AF_sup_quarantine_clear + 0x28.  (* after the call of arg_s (0x8bdd8) *)
Definition SQB_RETS : Z := AF_sup_quarantine_clear + 0x38.  (* after the call of rec_shape_of (0x8bde8) *)
Definition SQB_TAIL : Z := AF_sup_quarantine_clear + 0x54.  (* the tail jump to answer (0x8be04) *)
Definition SQB_FRAME : Z := 32.
(* the function the call records (REC_QUARANTINE_CLEAR, the `li a0,11` before the call of record) *)
Definition SQB_FN : Z := 11.
(* the verb "quarantine_clear": the image literal at 0x21e40 (CmdRo's RO_lit_21e40), the listing's object 70 *)
Definition SQB_VERB : Z := 0x21e40.
Definition SQB_VOBJ : nat := A_OBJ 70.
Definition sqcb_verb : list byte := bstr "quarantine_clear"%string.

(* the function's 22 slots in B's listing (lib/B/Prog/CmdList.v:5743-5764) *)
Definition sqcb_code : ptable csym := [
PW 0xfe010113; PW 0x113c23; PW 0x813823; PW 0x913423; PW 0x50413; PW 0xb00513;
PCall CS_record (1%bv : bv 5);
PW 0x50493; PW 0x40593;
PCall CS_arg_s (1%bv : bv 5);
PHi (10%bv : bv 5) 167; PAddHi (10%bv : bv 5) (10%bv : bv 5) 167 (A_OBJ 70) 0x0; PW 0x1000593;
PCall CS_rec_shape_of (1%bv : bv 5);
PW 0x100613; PW 0x50593; PW 0x48513; PW 0x1813083; PW 0x1013403; PW 0x813483; PW 0x2010113;
PTail CS_answer].

Lemma sqcb_listing : firstn 22 (skipn (Z.to_nat (SQB_E / 4)) cmd_listing) = sqcb_code.
Proof. vm_compute. reflexivity. Qed.

(* the call targets and the tail jump, against the image's address map (CmdAddr.v's cmd_sigma) *)
Lemma sqcb_callees :
cmd_sigma CS_sup_quarantine_clear = 0x8bdb0 /\ cmd_sigma CS_record = 0x8a728 /\ cmd_sigma CS_arg_s = 0x8a820 /\
cmd_sigma CS_rec_shape_of = 0x896d4 /\ cmd_sigma CS_answer = 0x8aa10 /\ cmd_text + SQB_E = 0x8bdb0.
Proof. vm_compute. repeat split. Qed.

(* the model's step: record(11) with which's copy, the verb's shape, answer with changes = 1 *)
Lemma sqcb_m : forall R which,
sup_quarantine_clear_m R which =
rec_answer (rec_record R SQB_FN [sarg which]) (SQB_FN, [sarg which]) (shape_of sqcb_verb) true.
Proof. reflexivity. Qed.

Lemma sqcb_verb_len : Z.of_nat (length sqcb_verb) = 16.
Proof. reflexivity. Qed.

(* atoms above the 32 registers: 32, 33, 34 the entry values of ra, s0, s1, which the 32-byte frame holds *)
Definition sqcb_saved : list Z := [1; 8; 9].
Definition sqcb_extra (regs0 : bvmap 5 word) : list word := map (fun r => getr regs0 (Z_to_bv 5 r)) sqcb_saved.
Definition sqcb_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].

(* regions: the frame at the entry (the prologue writes it), and the frame after the prologue (it holds the entry's
   ra, s0, s1 at sp + 24, 16, 8; no segment after the prologue writes it) *)
Definition sqcb_stack0 : YP09.region := YP09.mkRegion (Some 2%nat) (- SQB_FRAME) 0 (- SQB_FRAME) 0 [].
Definition sqcb_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 SQB_FRAME 0 0
  (map (fun j => YP09.mkChunk (24 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 3)).

Definition sqcb_ssA : sstate := mkSS SQB_E sr_atoms [sqcb_stack0] None sqcb_facts.
Definition sqcb_ssF (pc : Z) (sregs : list sv) : sstate := mkSS pc sregs [sqcb_frame] None sqcb_facts.

Lemma sqcb_bytes_eq : forall (rd : reader) a l l', abytes_atR rd a l -> map bv_unsigned l = map bv_unsigned l' ->
abytes_atR rd a l'.
Proof.
intros rd a l l' H E i Hi.
assert (Hl : length l = length l') by (rewrite <- (length_map bv_unsigned l), E, length_map; reflexivity).
rewrite (H i) by lia. f_equal.
rewrite <- (map_nth bv_unsigned l (Z_to_bv 8 0) i), <- (map_nth bv_unsigned l' (Z_to_bv 8 0) i), E. reflexivity.
Qed.

Lemma sqcb_bytes_prefix : forall (rd : reader) a l l2, abytes_atR rd a (l ++ l2) -> abytes_atR rd a l.
Proof. intros rd a l l2 H i Hi. rewrite (H i) by (rewrite length_app; lia). rewrite app_nth1 by exact Hi. reflexivity. Qed.

Lemma sqcb_no_zero : forall l : list byte, forallb (fun b => negb (bv_unsigned b =? 0)) l = true -> ~ In (Z_to_bv 8 0) l.
Proof.
intros l H Hin. rewrite forallb_forall in H. specialize (H _ Hin). vm_compute in H. discriminate.
Qed.

(* the verb's bytes and terminator are the image's wherever cmd_ro_ok holds *)
Lemma sqcb_verb_at : forall rd, cmd_ro_ok rd -> astr_atR rd SQB_VERB sqcb_verb.
Proof.
intros rd [HRB _]. unfold cmd_ro_bytes in HRB.
assert (HL : abytes_atR rd 0x21e40 RO_lit_21e40).
{ repeat match type of HRB with
  | abytes_atR _ 0x21e40 _ /\ _ => exact (proj1 HRB)
  | _ /\ _ => apply proj2 in HRB
  end. }
split; [apply (sqcb_bytes_eq _ _ _ _ HL); vm_compute; reflexivity|].
apply sqcb_no_zero. vm_compute. reflexivity.
Qed.

(* the verb's 16 bytes, the form rec_shape_of's premise asks *)
Lemma sqcb_verb_bytes : forall rd, cmd_ro_ok rd -> abytes_atR rd SQB_VERB sqcb_verb.
Proof. intros rd H. exact (sqcb_bytes_prefix _ _ _ _ (proj1 (sqcb_verb_at rd H))). Qed.

(* its 17 bytes are read-only wherever cmd_ro_in holds *)
Lemma sqcb_verb_ro : forall ro : Z -> Prop, cmd_ro_in ro -> forall i, 0 <= i < 17 -> ro (SQB_VERB + i).
Proof.
intros ro HROIN. unfold cmd_ro_in in HROIN. unfold SQB_VERB.
repeat match type of HROIN with
| (forall i, 0 <= i < 17 -> _ (0x21e40 + i)) /\ _ => exact (proj1 HROIN)
| _ /\ _ => apply proj2 in HROIN
end.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).

(* the literal's object atom has the literal's address *)
Lemma sqcb_vobj : cmd_val_objs -> VAL SQB_VOBJ = SQB_VERB.
Proof. intros VOBJS. unfold SQB_VOBJ. rewrite (VOBJS 70%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* the three return points are code pointers *)
Lemma sqcb_ret_ok : forall k, k = SQB_RETR \/ k = SQB_RETA \/ k = SQB_RETS -> YK0s.ret_ok (Z_to_bv 64 (BASE + k)).
Proof.
intros k Hk. apply ret_ok_codeptr_v;
destruct Hk as [-> | [-> | ->]]; unfold SQB_RETR, SQB_RETA, SQB_RETS, AF_sup_quarantine_clear;
first [lia | reflexivity].
Qed.

Lemma sqcb_ret_val : forall k, k = SQB_RETR \/ k = SQB_RETA \/ k = SQB_RETS ->
bv_unsigned (Z_to_bv 64 (BASE + k)) = BASE + k.
Proof.
intros k Hk. pose proof pa_B_ok as (HB0 & HB1 & _).
destruct Hk as [-> | [-> | ->]]; unfold SQB_RETR, SQB_RETA, SQB_RETS, AF_sup_quarantine_clear;
rewrite unsigned_lit_small; lia.
Qed.

(* the 32-byte frame holds the entry's ra, s0, s1 at sp1 + 24, 16, 8 *)
Definition sqcb_frame_at (m : word -> option byte) (sp1 : Z) (regs0 : bvmap 5 word) : Prop :=
forall j r, nth_error sqcb_saved j = Some r ->
val_mem SEGS m (sp1 + 24 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 r))).

(* every atom of the walk's environment: the registers of the current state, then the frame's three words *)
Definition sqcb_E (regs1 regs0 : bvmap 5 word) : env := Eimg (Ereg regs1 (sqcb_extra regs0)).

Lemma sqcb_U_atom : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff m 0) = v.
Proof.
intros E m v Hm Hv. unfold U. cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned.
apply unsigned_lit_small. exact Hv.
Qed.

Lemma sqcb_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

Lemma sqcb_E_reg : forall regs1 regs0 k (r : bv 5), Z.of_nat k = bv_unsigned r ->
ew (sqcb_E regs1 regs0) k = getr regs1 r.
Proof.
intros regs1 regs0 k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold sqcb_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk.
Qed.

Lemma sqcb_E_extra : forall regs1 regs0 j, (j < 3)%nat ->
ew (sqcb_E regs1 regs0) (32 + j) = nth j (sqcb_extra regs0) (Z_to_bv 64 0).
Proof.
intros regs1 regs0 j Hj. unfold sqcb_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra.
Qed.

Lemma sqcb_E_extra_at : forall regs1 regs0 k, (32 <= k < 35)%nat ->
ew (sqcb_E regs1 regs0) k = nth (k - 32) (sqcb_extra regs0) (Z_to_bv 64 0).
Proof.
intros regs1 regs0 k Hk. replace k with (32 + (k - 32))%nat at 1 by lia. apply sqcb_E_extra. lia.
Qed.

Lemma sqcb_E_img : forall regs1 regs0, img_env VAL A_LIM (sqcb_E regs1 regs0).
Proof. intros. unfold sqcb_E. apply Eimg_env. Qed.

(* the literal's atom in every environment of the walk *)
Lemma sqcb_E_verb : forall regs1 regs0, cmd_val_objs -> ew (sqcb_E regs1 regs0) SQB_VOBJ = Z_to_bv 64 SQB_VERB.
Proof.
intros regs1 regs0 VOBJS. unfold sqcb_E. rewrite Eimg_img by (unfold SQB_VOBJ, A_OBJ, A_TEXT, A_LIM; lia).
rewrite (sqcb_vobj VOBJS). reflexivity.
Qed.

Lemma sqcb_facts_ok : forall regs1 regs0,
2 ^ 46 <= bv_unsigned (getr regs1 2) <= 2 ^ 47 -> bv_unsigned (getr regs1 2) mod 16 = 0 ->
facts_ok (sqcb_E regs1 regs0) sqcb_facts.
Proof.
intros regs1 regs0 Hsp Hsp16.
set (E := sqcb_E regs1 regs0).
assert (E2 : ew E 2 = Z_to_bv 64 (bv_unsigned (getr regs1 2)))
  by (subst E; rewrite (sqcb_E_reg _ _ 2 2%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned).
unfold facts_ok, sqcb_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [|split; [exact I | exact I]].
split; [|exact I].
apply (sqcb_afact E 2%nat (bv_unsigned (getr regs1 2))); [exact E2 | lia | lia | change (2 ^ 4) with 16; exact Hsp16 | lia].
Qed.

(* the seed of a segment after the prologue (after record, after arg_s, after rec_shape_of): the frame and its
   three saved registers *)
Lemma sqcb_seed : forall pc sregs (W1 : world SEGS) (regs1 regs0 : bvmap 5 word) mem1,
2 ^ 46 <= bv_unsigned (getr regs1 2) <= 2 ^ 47 - SQB_FRAME -> bv_unsigned (getr regs1 2) mod 16 = 0 ->
regs_ok (sqcb_E regs1 regs0) sregs regs1 ->
sqcb_frame_at (mrestrict (w_H W1) mem1) (bv_unsigned (getr regs1 2)) regs0 ->
st_ok_pi SEGS VAL (sqcb_E regs1 regs0) (sqcb_ssF pc sregs)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS))).
Proof.
intros pc sregs W1 regs1 regs0 mem1 Hsp Hsp16 HREG HFR.
set (sp1 := bv_unsigned (getr regs1 2)) in *.
set (E := sqcb_E regs1 regs0) in *.
assert (E2 : bv_unsigned (ew E 2) = sp1) by (subst E sp1; rewrite (sqcb_E_reg _ _ 2 2%bv eq_refl); reflexivity).
unfold sqcb_ssF. rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- exact HREG.
- vm_compute. reflexivity.
- unfold sqcb_frame. repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E2. unfold SQB_FRAME in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  lazymatch goal with |- Forall ?P ?l => let l2 := eval vm_compute in l in change (Forall P l2) end.
  repeat apply Forall_cons; try apply Forall_nil;
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?k 0))) =>
  let j := eval compute in (k - 32)%nat in let r := eval compute in (nth j sqcb_saved 0) in
  apply (chunk_ok_val SEGS E _ sp1 off 8 (SOff k 0) (bv_unsigned (getr regs0 (Z_to_bv 5 r))));
  [ cbn [sv_denot]; rewrite Z.add_0_r; subst E;
    rewrite (sqcb_E_extra_at regs1 regs0 k ltac:(lia)); cbn [Nat.sub nth sqcb_extra sqcb_saved map app];
    rewrite Z_to_bv_bv_unsigned; reflexivity
  | pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 r))) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; cbn; lia
  | cbn; lia
  | replace (sp1 + off) with (sp1 + 24 - 8 * Z.of_nat j) by (cbn; lia); exact (HFR j r eq_refl) ] end.
- apply pairwise_disjoint_of_extents. unfold sqcb_frame, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- apply (sqcb_facts_ok regs1 regs0); [unfold SQB_FRAME in Hsp; fold sp1; lia | exact Hsp16].
Qed.

(* the seed at the entry: the frame the prologue writes *)
Lemma sqcb_seed_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem,
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - SQB_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (sqcb_E regs regs) sqcb_ssA
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + SQB_E)) mem (seg_rom SEGS))).
Proof.
intros W regs mem Hsp Hsp16 Hpres.
set (E := sqcb_E regs regs).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (sqcb_E_reg _ _ 2 2%bv eq_refl); reflexivity).
unfold sqcb_ssA. rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- subst E. unfold sqcb_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sqcb_stack0.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite E2. unfold SQB_FRAME in *. split; [lia|]. split; [lia|]. split.
  { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
  constructor.
- apply pairwise_disjoint_of_extents. unfold sqcb_stack0, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- exact (sqcb_facts_ok regs regs ltac:(unfold spZ in Hsp; lia) Hsp16).
Qed.

End f.
End d.

(* ---------- part 2: the recorder's representation across the walk's journals ---------- *)
(* In the form of lib/A/Prog/sup_quarantine_clear_s1.v and _s3.v (a working branch f2402580166) and
   lib/A/Prog/RecBLemmas.v over B's lib/B/Prog/CmdRep.v (which is A's CmdRep at B's addresses). *)

Lemma sqcb_aval_keep : forall rd rd' a n v, aval_mem rd a n v ->
  (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.

Lemma sqcb_aval_eq : forall rd a b n v, aval_mem rd a n v -> a = b -> aval_mem rd b n v.
Proof. intros rd a b n v H E. subst b. exact H. Qed.

Lemma sqcb_bytes_keep : forall rd rd' a l, abytes_atR rd a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H K i Hi. rewrite K by lia. exact (H i Hi). Qed.

Lemma sqcb_str_keep : forall rd rd' p s, astr_atR rd p s ->
  (forall x, p <= x < p + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' p s.
Proof.
  intros rd rd' p s [H1 H2] K. split; [|exact H2].
  apply (sqcb_bytes_keep rd); [exact H1|]. intros x Hx. apply K. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma sqcb_call_keep : forall bl bl' rd rd' a c P, acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  acall_at bl' rd' a c P.
Proof.
  intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) KA KP.
  unfold acall_at, CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
  refine (conj H1 (conj H2 (conj H3 (conj _ (conj _ (conj H6 _)))))).
  - apply (sqcb_aval_keep rd); [exact H4|]. intros x Hx. apply KA. lia.
  - apply (sqcb_aval_keep rd); [exact H5|]. intros x Hx. apply KA. lia.
  - intros k s pn Es Ep. destruct (H7 k s pn Es Ep) as (G1 & G2 & G3 & G4 & G5).
    assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
    destruct (KP pn ltac:(eapply nth_error_In; exact Ep)) as [Kin Kx].
    refine (conj _ (conj G2 (conj Kin (conj G4 _)))).
    + apply (sqcb_aval_keep rd); [exact G1|]. intros x Hx. apply KA. lia.
    + apply (sqcb_str_keep rd); [exact G5|]. intros x Hx. apply Kx. lia.
Qed.

Lemma sqcb_answer_keep : forall bl bl' rd rd' gr t q, aanswer_at bl rd gr t q ->
  (forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  aanswer_at bl' rd' gr t q.
Proof.
  intros bl bl' rd rd' gr t q H KA KP.
  destruct t as [x|]; destruct q as [pn|]; cbn [aanswer_at] in H |- *; try contradiction.
  - destruct H as (N1 & N2 & N3 & N4 & N5 & N6).
    destruct (KP pn ltac:(cbn; left; reflexivity)) as [Kin Kx].
    refine (conj _ (conj N2 (conj Kin (conj N4 (conj _ N6))))).
    + apply (sqcb_aval_keep rd); [exact N1|]. intros y Hy. apply KA. lia.
    + apply (sqcb_str_keep rd); [exact N5|]. intros y Hy. apply Kx. lia.
  - apply (sqcb_aval_keep rd); [exact H|]. intros y Hy. apply KA. lia.
Qed.

Lemma sqcb_reply_keep : forall bl bl' rd rd' gr y q, areply_at bl rd gr y q ->
  (forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY + 16 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  areply_at bl' rd' gr y q.
Proof.
  intros bl bl' rd rd' gr y q H KA KP.
  destruct y as [x|]; destruct q as [pn|]; cbn [areply_at] in H |- *; try contradiction;
    unfold OFF_REPLY, OFF_REPLY_SIZE in *.
  - destruct H as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    destruct (KP pn ltac:(cbn; left; reflexivity)) as [Kin Kx].
    refine (conj _ (conj _ (conj P3 (conj P4 (conj Kin (conj P6 (conj _ P8))))))).
    + apply (sqcb_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (sqcb_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
    + apply (sqcb_bytes_keep rd); [exact P7|]. intros z Hz. apply Kx. lia.
  - destruct H as [P1 P2]. split.
    + apply (sqcb_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (sqcb_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
Qed.

Lemma sqcb_scalars_keep : forall rd rd' gr R, ag1_scalars rd gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + 920 <= x < gr + 924 \/ gr + 944 <= x < gr + 960 -> rd' x = rd x) ->
  ag1_scalars rd' gr R.
Proof.
  intros rd rd' gr R (X1 & X2 & X3 & X4 & X5 & X6) K.
  unfold ag1_scalars, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
  all: apply (sqcb_aval_keep rd); [eassumption|]; intros z Hz; apply K; lia.
Qed.

Lemma sqcb_in_calls : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
  intros Q i P pn E H. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
  split; [eapply nth_error_In; exact E | exact H].
Qed.

Lemma sqcb_in_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.

Lemma sqcb_in_reply : forall Q pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q).
Proof.
  intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact H.
Qed.

(* arep_at reads the reader only at g_rec, record.spill and the bytes of the recorder's own blocks, and the block
   list only at those blocks *)
Lemma sqcb_arep_at_ext : forall bl bl' rd rd' gr sc R Q,
  arep_at bl rd gr sc R Q ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl') ->
  (forall a, (gr <= a < gr + REC_SIZE) \/ (sc <= a < sc + SC_SIZE) \/
             (exists pn, In pn (lay_blocks Q) /\ fst pn <= a < fst pn + snd pn) -> rd' a = rd a) ->
  arep_at bl' rd' gr sc R Q.
Proof.
  intros bl bl' rd rd' gr sc R Q (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HP & HX & HW) KL K.
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn bl' /\
             forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x).
  { intros pn Hpn. split; [exact (KL pn Hpn)|]. intros x Hx. apply K. right. right. exists pn.
    split; [exact Hpn | exact Hx]. }
  assert (KR : forall x, gr <= x < gr + REC_SIZE -> rd' x = rd x) by (intros x Hx; apply K; left; exact Hx).
  assert (KS : forall x, sc <= x < sc + SC_SIZE -> rd' x = rd x) by (intros x Hx; apply K; right; left; exact Hx).
  unfold REC_SIZE, SC_SIZE in KR, KS.
  refine (conj G1 (conj G2 (conj G3 (conj _ (conj _ (conj _ (conj _ HW))))))).
  - refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
    + apply (sqcb_aval_keep rd); [exact C3|]. intros x Hx. apply KR. unfold OFF_NCALLS in Hx. lia.
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (sqcb_call_keep bl _ rd); [exact Hc | |].
      * intros x Hx. apply KR. unfold OFF_CALLS, CALL_SIZE in *. lia.
      * intros pn Hpn. apply KQ. exact (sqcb_in_calls Q i P pn EP Hpn).
    + apply (sqcb_call_keep bl _ rd); [exact C5 | |].
      * intros x Hx. apply KS. unfold CALL_SIZE in Hx. lia.
      * intros pn Hpn. apply KQ. apply sqcb_in_spill. exact Hpn.
  - apply (sqcb_answer_keep bl _ rd); [exact HA | |].
    + intros x Hx. apply KR. unfold OFF_ANSWER in Hx. lia.
    + intros pn Hpn. apply KQ. apply rca_in_answer. exact Hpn.
  - apply (sqcb_reply_keep bl _ rd); [exact HP | |].
    + intros x Hx. apply KR. unfold OFF_REPLY in Hx. lia.
    + intros pn Hpn. apply KQ. apply sqcb_in_reply. exact Hpn.
  - apply (sqcb_scalars_keep rd); [exact HX|]. intros x Hx. apply KR. lia.
Qed.

Lemma sqcb_acall_at_in : forall bl rd a c P, acall_at bl rd a c P -> forall pn, In pn P -> In pn bl.
Proof.
intros bl rd a c P (_ & _ & HL & _ & _ & _ & H6) pn Hpn.
destruct (In_nth_error P pn Hpn) as (k & Hk).
assert (Hlt : (k < length (snd c))%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Hk; discriminate).
destruct (nth_error (snd c) k) as [s|] eqn:Hs; [|apply nth_error_Some in Hlt; contradiction].
exact (proj1 (proj2 (proj2 (H6 k s pn Hs Hk)))).
Qed.

(* every block the representation names is a live block *)
Lemma sqcb_lay_blocks_in : forall bl rd gr sc R Q, arep_at bl rd gr sc R Q -> forall pn, In pn (lay_blocks Q) -> In pn bl.
Proof.
intros bl rd gr sc R Q (_ & _ & _ & HC & HA & HR & _ & _) pn Hpn.
unfold lay_blocks in Hpn. apply in_app_or in Hpn as [Hc | Hpn]; [|apply in_app_or in Hpn as [Hs | Hpn]; [|apply in_app_or in Hpn as [Ha | Hr]]].
- apply in_concat in Hc as (P & HP & Hin). destruct (In_nth_error _ _ HP) as (i & Hi).
  destruct HC as (_ & HlenQ & _ & Hcalls & _).
  assert (Hlt : (i < length (r_calls R))%nat) by (rewrite <- HlenQ; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc'; [|apply nth_error_Some in Hlt; contradiction].
  exact (sqcb_acall_at_in _ _ _ _ _ (proj1 (Hcalls i c P Hc' Hi)) pn Hin).
- destruct HC as (_ & _ & _ & _ & Hsp & _). exact (sqcb_acall_at_in _ _ _ _ _ Hsp pn Hs).
- unfold aanswer_at in HA. destruct (r_answer R) as [xa|], (l_answer Q) as [pa|]; cbn [oblk In] in Ha; try contradiction.
  destruct Ha as [<- | []]. exact (proj1 (proj2 (proj2 HA))).
- unfold areply_at in HR. destruct (r_reply R) as [xr|], (l_reply Q) as [pr|]; cbn [oblk In] in Hr; try contradiction.
  destruct Hr as [<- | []]. exact (proj1 (proj2 (proj2 (proj2 (proj2 HR))))).
Qed.

(* the answer the recorder holds: its address in g_rec.answer, and its block one of the representation's *)
Definition sqcb_old (Q : rlay) : Z := match l_answer Q with Some pn => fst pn | None => 0 end.

Lemma sqcb_old_at : forall bl rd R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
aval_mem rd (A_G_REC + OFF_ANSWER) 8 (sqcb_old Q) /\ (forall pn, l_answer Q = Some pn -> In pn (lay_blocks Q)).
Proof.
intros bl rd R Q (_ & _ & _ & _ & HA & _). unfold sqcb_old. split.
- unfold aanswer_at in HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [pn|]; try contradiction;
  [exact (proj1 HA) | exact HA].
- intros pn Hpn. apply rca_in_answer. rewrite Hpn. left. reflexivity.
Qed.

(* the slot record() returns: an entry of g_rec's call table, or record.spill *)
Lemma sqcb_slot_bounds : forall R, (length (r_calls R) <= 16)%nat ->
((A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_G_REC + REC_SIZE) \/ rec_slot R = A_REC_SPILL) /\
A_G_REC + OFF_CALLS <= rec_slot R <= A_REC_SPILL.
Proof.
intros R H. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L];
unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, A_REC_SPILL;
[split; [left; split; lia | lia] | split; [right; reflexivity | lia]].
Qed.

(* the slot fact answer's pre asks (answer_c.v): the call just recorded is in the table's slot or is the spill *)
Lemma sqcb_answer_slot : forall R x,
(exists k, nth_error (r_calls (rec_record R SQB_FN [x])) k = Some (SQB_FN, [x]) /\
   rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
(rec_slot R = A_REC_SPILL /\ (SQB_FN, [x]) = r_spill (rec_record R SQB_FN [x])).
Proof.
intros R x. unfold rec_slot, rec_record. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L].
- left. exists (length (r_calls R)). cbn [set_calls r_calls]. split; [|reflexivity].
  rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
- right. cbn [set_spill r_spill]. split; reflexivity.
Qed.

(* every block of the recorder has a positive size *)
Lemma sqcb_call_blocks : forall bl rd a c P pn, acall_at bl rd a c P -> In pn P -> In pn bl /\ 0 < snd pn.
Proof.
  intros bl rd a c P pn (_ & _ & Hl & _ & _ & _ & Hk) Hin.
  destruct (In_nth_error P pn Hin) as [k Ek].
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- Hl; apply nth_error_Some; rewrite Ek; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (Hk k s pn Es Ek) as (_ & _ & G3 & G4 & _). split; [exact G3 | lia].
Qed.

Lemma sqcb_blocks_pos : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) -> 0 < snd pn.
Proof.
  intros bl rd gr sc R Q pn (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HP & _ & _) Hin.
  unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply in_concat in Hin as (P & HP' & Hpn).
    destruct (In_nth_error _ _ HP') as [i Ei].
    assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    destruct (C4 i c P Ec Ei) as [Hc _]. exact (proj2 (sqcb_call_blocks _ _ _ _ _ _ Hc Hpn)).
  - apply in_app_or in Hin as [Hin|Hin]; [exact (proj2 (sqcb_call_blocks _ _ _ _ _ _ C5 Hin))|].
    apply in_app_or in Hin as [Hin|Hin].
    + revert HA Hin. destruct (r_answer R) as [x|]; destruct (l_answer Q) as [qn|];
        cbn [aanswer_at oblk In]; intros HA Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HA as (_ & _ & _ & N4 & _). lia.
    + revert HP Hin. destruct (r_reply R) as [x|]; destruct (l_reply Q) as [qn|];
        cbn [areply_at oblk In]; intros HP Hin; try contradiction.
      destruct Hin as [<-|[]]. destruct HP as (_ & _ & _ & P4 & _ & P6 & _).
      destruct x as [|b x]; [exfalso; apply P4; reflexivity|]. cbn [length] in P6. lia.
Qed.

(* the walk's footprint (the statement's): g_rec, record.spill, the recorder's blocks *)
Definition sqcb_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Lemma sqcb_PG_grec : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | unfold REC_SIZE in Ha; cbn [fst snd]; lia]. Qed.

Lemma sqcb_PG_spill : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | unfold SC_SIZE in Ha; cbn [fst snd]; lia]. Qed.

Lemma sqcb_PG_slot : forall R a, (length (r_calls R) <= 16)%nat -> rec_slot R <= a < rec_slot R + CALL_SIZE ->
inFP cmd_PG a /\ inFP (sqcb_FP []) a.
Proof.
intros R a HR Ha. destruct (sqcb_slot_bounds R HR) as ([(H1 & H2) | H1] & _).
- assert (Hg : A_G_REC <= a < A_G_REC + REC_SIZE) by (unfold A_G_REC, OFF_CALLS, REC_SIZE in *; lia).
  split; [exact (sqcb_PG_grec a Hg)|]. apply inFP_cons. left. exact Hg.
- assert (Hs : A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) by (rewrite H1 in Ha; unfold SC_SIZE, CALL_SIZE in *; lia).
  split; [exact (sqcb_PG_spill a Hs)|]. apply inFP_cons. right. apply inFP_cons. left. exact Hs.
Qed.

Lemma sqcb_FP_O : forall O a, inFP (sqcb_FP []) a -> inFP (sqcb_FP O) a.
Proof.
intros O a Ha. unfold sqcb_FP in *. apply inFP_cons in Ha as [Ha | Ha]; [apply inFP_cons; left; exact Ha|].
apply inFP_cons in Ha as [Ha | Ha]; [apply inFP_cons; right; apply inFP_cons; left; exact Ha|].
exfalso. exact (inFP_nil a Ha).
Qed.

Lemma sqcb_inFP_cases : forall O a, inFP (sqcb_FP O) a ->
inFP cmd_PG a \/ exists b n, In (b, n) O /\ b <= a < b + req_size n.
Proof.
intros O a Ha. unfold sqcb_FP in Ha. apply inFP_cons in Ha as [Ha | Ha]; [left; exact (sqcb_PG_grec a Ha)|].
apply inFP_cons in Ha as [Ha | Ha]; [left; exact (sqcb_PG_spill a Ha)|].
right. exact (inFP_ablocks_fp_inv O a Ha).
Qed.

Lemma sqcb_PG_low : forall a, inFP cmd_PG a -> 0x10000 <= a < 0x606000.
Proof.
intros a (r & Hr & Ha). unfold cmd_PG in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in Ha; lia.
Qed.

(* the verb literal's read-only checks, decided on the record's lists *)
Lemma sqcb_verb_addr : cmd_addr_b SQB_VERB 17 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sqcb_verb_hull : cmd_hull_b SQB_VERB 17 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sqcb_verb_end : In (SQB_VERB + Z.of_nat (length sqcb_verb)) cmd_ro_ends.
Proof.
change (SQB_VERB + Z.of_nat (length sqcb_verb)) with 0x21e50. unfold cmd_ro_ends.
repeat first [left; reflexivity | right].
Qed.

Lemma sqcb_verb_owned : forallb (fun r => (fst r + snd r <=? SQB_VERB) || (SQB_VERB + 17 <=? fst r)) Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sqcb_verb_errno : ((TFIB_ERRNO + 4 <=? SQB_VERB) || (SQB_VERB + 17 <=? TFIB_ERRNO)) = true.
Proof. vm_compute. reflexivity. Qed.

Section e2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

Lemma sqcb_rec_repA_ext : forall ly S rd ly' S' rd' R O,
  rec_repA B ly S rd R O ->
  (forall pn, In pn O -> In pn (ablocks B ly' S')) ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
             (exists pn, In pn O /\ fst pn <= a < fst pn + snd pn) -> rd' a = rd a) ->
  rec_repA B ly' S' rd' R O.
Proof.
  intros ly S rd ly' S' rd' R O (Q & HR & HO) KB K. exists Q. split; [|exact HO].
  apply (sqcb_arep_at_ext (ablocks B ly S) _ rd _ _ _ _ _ HR).
  - intros pn Hpn. apply KB. apply HO. exact Hpn.
  - intros a [Ha|[Ha|(pn & Hpn & Ha)]]; apply K;
      [left; exact Ha | right; left; exact Ha | right; right; exists pn; split; [apply HO; exact Hpn | exact Ha]].
Qed.

Lemma sqcb_rec_repA_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O (Q & HQ & HO) pn Hpn. exact (sqcb_lay_blocks_in _ _ _ _ _ _ HQ pn (proj1 (HO pn) Hpn)). Qed.

Lemma sqcb_rec_repA_pos : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> 0 < snd pn.
Proof. intros ly S rd R O (Q & HA & HO) pn Hpn. apply HO in Hpn. exact (sqcb_blocks_pos _ _ _ _ _ _ pn HA Hpn). Qed.

Lemma sqcb_argA_kept : forall ly S (rd rd' : reader) ro O p v, astr_argA B ly S rd ro O p (Some v) ->
(forall i, 0 <= i < Z.of_nat (length v) + 1 -> rd' (p + i) = rd (p + i)) -> astr_argA B ly S rd' ro O p (Some v).
Proof.
intros ly S rd rd' ro O p v H K. cbn [astr_argA] in H |- *. destruct H as (H0 & Hs & Hl & Hr).
split; [exact H0|]. split; [|split; [exact Hl | exact Hr]].
apply (sqcb_str_keep rd); [exact Hs|]. intros x Hx. replace x with (p + (x - p)) by lia. apply K. lia.
Qed.

Lemma sqcb_blk_bounds : forall ly S (W : world SEGS) mem md b m, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> 4096 <= b /\ b + req_size m <= alloc_ceiling /\ 0 <= m /\ m <= req_size m /\ 1 <= req_size m.
Proof.
intros ly S W mem md b m HAR Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [Hq1 Hq2]. lia.
Qed.

Lemma sqcb_blk_apart : forall ly S (W : world SEGS) mem md b m p n, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
b + req_size m <= p \/ p + req_size n <= b.
Proof.
intros ly S W mem md b m p n HAR H1 H2 Hne.
pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR H1 H2 Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma sqcb_same_start : forall ly S (W : world SEGS) mem md pn an, AR SEGS B ly S W mem md ->
In pn (ablocks B ly S) -> In an (ablocks B ly S) -> fst pn = fst an -> pn = an.
Proof.
intros ly S W mem md [b m] [b' m'] HAR H1 H2 Hf. cbn [fst] in Hf. subst b'.
destruct (recb_pair_dec (b, m) (b, m')) as [E | Hne]; [exact E|]. exfalso.
destruct (sqcb_blk_bounds ly S W mem md b m HAR H1) as (_ & _ & _ & _ & R1).
destruct (sqcb_blk_bounds ly S W mem md b m' HAR H2) as (_ & _ & _ & _ & R2).
destruct (sqcb_blk_apart ly S W mem md b m b m' HAR H1 H2 Hne); lia.
Qed.

(* a live block is listed once *)
Lemma sqcb_dup_false : forall ly S (W : world SEGS) mem md L1 L2 pn, AR SEGS B ly S W mem md ->
Permutation (ablocks B ly S) (L1 ++ L2) -> In pn L1 -> In pn L2 -> False.
Proof.
intros ly S W mem md L1 L2 pn HAR HP H1 H2.
pose proof H1 as H1'.
apply in_split in H1 as (a1 & b1 & ->). apply in_split in H2 as (a2 & b2 & ->).
assert (HP' : Permutation (ablocks B ly S) (pn :: pn :: (a1 ++ b1 ++ a2 ++ b2))).
{ eapply Permutation_trans; [exact HP|].
  rewrite <- app_assoc. cbn [app].
  eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
  replace (a1 ++ b1 ++ a2 ++ pn :: b2) with ((a1 ++ b1 ++ a2) ++ pn :: b2) by (rewrite <- !app_assoc; reflexivity).
  eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
  rewrite <- !app_assoc. reflexivity. }
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md pn pn _ HAR HP') as D.
assert (Hin : In pn (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact H1').
destruct pn as [b m].
destruct (sqcb_blk_bounds ly S W mem md b m HAR Hin) as (_ & _ & _ & _ & Hr1).
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

Lemma sqcb_bsum_nonneg : forall ly S (W : world SEGS) mem md L, AR SEGS B ly S W mem md ->
(forall pn, In pn L -> In pn (ablocks B ly S)) -> 0 <= bsum L.
Proof.
intros ly S W mem md L HAR HL. induction L as [|[b m] L IH]; [unfold bsum; cbn; lia|].
rewrite bsum_cons. cbn [snd].
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR (HL (b, m) (or_introl eq_refl))) as (_ & _ & _ & _ & _ & _ & Hm).
assert (IH' := IH (fun pn Hpn => HL pn (or_intror Hpn))). lia.
Qed.

Lemma sqcb_FP_low : forall ly S (W : world SEGS) mem md O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> inFP (sqcb_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O a HAR HO Ha. pose proof asan_consts as (C1 & _).
destruct (sqcb_inFP_cases O a Ha) as [HP | (b & n & Hin & Hba)].
- pose proof (sqcb_PG_low a HP). lia.
- destruct (sqcb_blk_bounds ly S W mem md b n HAR (HO _ Hin)) as (_ & Hb & _). lia.
Qed.

(* what a callee's journal keeps *)
Lemma sqcb_keep_img : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a ->
in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn Hi Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply F3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [apply sink_closed_pos; exact HF | exact Hn]].
Qed.

Lemma sqcb_keep_stack : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
(forall b, inFP FP1 b -> b < alloc_ceiling) -> alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK1 <= a < sp1) ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Ha Hw.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
apply F1; [exact Ha | exact Hw | intros Hf; specialize (HF a Hf); lia].
Qed.

Lemma sqcb_keep_blk : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 b m i,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m -> ~ inFP FP1 (b + i) ->
rdW W2 mem2 (b + i) = rdW Wc memc (b + i).
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 b m i HJ H1 H2 Hi Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). exact (F2 b m i H1 H2 Hi Hn).
Qed.

Lemma sqcb_achain_kept : forall STK sp0 FP ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k v ch,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
achain ly (rdW W mem) sp0 v ch -> achain ly' (rdW W' mem') sp0 v ch.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k v ch HJ HF Hc.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hs0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
apply (achain_ly_top ly ly'); [exact Etop|].
apply (achain_kept ly (rdW W mem) (rdW W' mem') sp0 v ch sp0 Hc); [lia | lia |].
intros a Ha. apply F1; [lia | lia | intros Hf; specialize (HF a Hf); lia].
Qed.

(* the callee-saved registers, one by one *)
Lemma sqcb_pres : forall (r1 r2 : bvmap 5 word),
(forall n, In n [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r2 (Z_to_bv 5 n) = getr r1 (Z_to_bv 5 n)) ->
aregs_preserved r1 r2.
Proof.
intros r1 r2 H r Hr. apply H. unfold acallee_saved in Hr. cbn [In].
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [tauto | tauto | tauto | tauto | tauto |].
assert (H0 : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct H0 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; tauto.
Qed.

(* g_rec, record.spill and g_quitting as the footprint list cmd_PG and as the record's TFIB_PROG_STATIC *)
Lemma sqcb_PG_tfib : forall a, inFP cmd_PG a -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a (r & Hr & Ha). unfold TFIB_PROG_STATIC.
unfold cmd_PG in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha;
unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in Ha;
[apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd];
unfold in_zr; cbn [fst snd]; lia.
Qed.

Section h.
Hypothesis HB : CmdBSyms B.
(* the record's static facts the walk carries, in the forms and under the names of a Theorem Labs lane's CmdRecFacts groups
   (lib/B/Prog/CmdRecRest.v cmd_prog_img, cmd_ro_prog_apart; CmdRecRo.v ROB), stated there at the concrete image *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a.
Context {ROB : ro_below_ofl SEGS RLO RHI}.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC.

Lemma sqcb_keep_prog : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a -> inFP cmd_PG a ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn HP.
destruct (recb_prog_unowned_m B HB cmd_prog_img a (sqcb_PG_tfib a HP)) as (H1 & H2 & H3).
exact (sqcb_keep_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ HF Hn H1 H2 H3).
Qed.

(* a byte of g_rec or record.spill in the walk's footprint: the walk (and a callee) may write it *)
Lemma sqcb_awr_prog : forall STK sp O bl0 blc fr0 ly own a, inFP cmd_PG a -> inFP (sqcb_FP O) a ->
awr_byte SEGS B STK sp (sqcb_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own a HP Hf.
right; right; right; right; left. split; [exact Hf|].
split; [exact (rca_HPROG B HB a HP) | exact (cmd_prog_img a (sqcb_PG_tfib a HP))].
Qed.

Lemma sqcb_relro_img : forall a, RLO <= a < RHI -> in_img SEGS a.
Proof. intros a Ha. exact (proj1 (cmd_ro_prog_apart a (or_intror Ha))). Qed.

(* arodata_okP along the walk's journal: the walk's footprint (g_rec, record.spill, the recorder's blocks) is off
   the read-only range *)
Lemma sqcb_aro : forall STK ly S (W : world SEGS) mem md O lyc Sc Wc memc mdc own k sp,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp (sqcb_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros STK ly S W mem md O lyc Sc Wc memc mdc own k sp HAR HO HJ HR.
apply (arodata_ok_journalP SEGS RLO RHI sqcb_relro_img (RO := ROB) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); [|exact HR].
intros a Hro Hfp. destruct (sqcb_inFP_cases O a Hfp) as [HP | (b & n & Hin & Ha)].
- exact (proj2 (cmd_ro_prog_apart a Hro) (sqcb_PG_tfib a HP)).
- apply (recb_heap_noimg_m B ly S W mem md b n a HAR (HO _ Hin) Ha). exact (proj1 (cmd_ro_prog_apart a Hro)).
Qed.

(* a byte range none of whose bytes the runtime owns and which is not the errno cell, decided on the record's lists *)
Lemma sqcb_unowned_rng : forall lo n,
forallb (fun r => (fst r + snd r <=? lo) || (lo + n <=? fst r)) Tfib_owned_static = true ->
((TFIB_ERRNO + 4 <=? lo) || (lo + n <=? TFIB_ERRNO)) = true ->
forall a, lo <= a < lo + n -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros lo n Hf He a Ha. rewrite (ts_owned B HB), (ts_errno B HB). split.
- intros Hex. apply Exists_exists in Hex as (r & Hr & Hz). rewrite forallb_forall in Hf. specialize (Hf r Hr).
  unfold in_zr in Hz. apply orb_true_iff in Hf as [Hf | Hf]; apply Z.leb_le in Hf; lia.
- apply orb_true_iff in He as [He | He]; apply Z.leb_le in He; lia.
Qed.

(* the verb "quarantine_clear" as a read-only string argument (rec_shape_of's premise, astr_argA's read-only arm) *)
Lemma sqcb_verb_argA : forall ly S rd O, cmd_ro_in (in_roP SEGS RLO RHI) -> cmd_ro_ok rd ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) O SQB_VERB (Some sqcb_verb).
Proof.
intros ly S rd O HROIN HRO. cbn [astr_argA]. split; [unfold SQB_VERB; lia|]. split; [exact (sqcb_verb_at rd HRO)|].
split; [vm_compute; congruence|]. right. split.
- intros i Hi. change (Z.of_nat (length sqcb_verb) + 1) with 17 in Hi. split.
  + exact (sqcb_verb_ro _ HROIN i Hi).
  + exact (sqcb_unowned_rng SQB_VERB 17 sqcb_verb_owned sqcb_verb_errno (SQB_VERB + i) ltac:(lia)).
- split; [exact sqcb_verb_addr|]. split; [exact sqcb_verb_hull | exact sqcb_verb_end].
Qed.
End h.
End e2.

Print Assumptions sqcb_listing.
Print Assumptions sqcb_verb_at.
Print Assumptions sqcb_seed.
Print Assumptions sqcb_seed_entry.
Print Assumptions sqcb_verb_argA.
Print Assumptions sqcb_aro.

