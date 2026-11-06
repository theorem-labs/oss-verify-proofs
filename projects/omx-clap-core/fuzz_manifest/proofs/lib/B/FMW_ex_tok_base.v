(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 848 of its 931 lines of code are new or changed and 1841 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_hp_kit.v, with its module paths and module names changed; 305 of its 367 lines of code are new or changed and 869 lines of the source are left out. *)
(* G4 IMAGE B (fm.asan-ubsan, pin ca61e5c9eabc0050): the base of ex_seg_T (lib/B/FMW_ex_base.v): expected's ex_token
   (fuzz_manifest.c:96-113, inlined at 0x816dc .. 0x818ac of B's expected, listing
   (internal path) lines 294-421). The shape follows image A's
   lib/A/FMW_ex_tok_base.v (06d82004dc3); every pc, register and frame offset below is B's. B keeps the scan in other
   registers than A: the loop index j in s8, s10 = ~text - j (B's UBSan bound for text + j), the pointer text + j in s1
   (made per iteration), text in a6 (re-made after each call, with a7 = 6 and t1 = the mask), and the answer in s7 = 1
   (0x81904 `mv a0, s7`). The token walk is cut at four more pcs; each cut carries a semantic invariant, and each
   sub-segment builds its own symbolic state from it:
     TK_LH 0x81730 the loop head at index j (s8 = j, s10 = ~text - j), fuzz_manifest.c:103;
     TK_N  0x817a4 `continue` at index j: j + 1, the loop test, back to TK_LH or out to EX_L;
     TK_B  0x817c8 the left boundary test (j > 0, s1 = text + j) after the three matches, :109;
     TK_E  0x81834 the right boundary test, :109-111.
   After the setup 0x816f4 .. 0x8172c the frame holds F+0x10 = ll + 1 + nl, F+0x50 = len, F+8 = F+0 = text + 1 + nl +
   ll, F+0x18 = ll (besides F+0x20 = local = uri + nl2, F+0x40 = close = text + close of ex_at_T); registers s4 = text +
   name, s5 = nl, s2 = ll + 1 + nl, s6 = text + nl, s7 = 1, a6 = text; s0 = -1, s3 = 5, s11 = ' ' (ex_sregs). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_ex_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the token walk's cut pcs (B) ---- *)
Definition TK_LH : Z := 0x81730.
Definition TK_N : Z := 0x817a4.
Definition TK_B : Z := 0x817c8.
Definition TK_E : Z := 0x81834.

(* ---- string kit (copied from G5's lib/A/FMW_kitS.v, a Theorem Labs lane, with credit; renamed; as image A's tok_base) ---- *)
(* the shadow hull of a sub-range lies in the hull of the range (G5 shadow_hull_vis_sub) *)
Lemma tk_hull_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr, SHADOW_OFF in *.
assert (M1 : (2147450880 + x / 8) / 8 <= (2147450880 + x' / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1); lia).
assert (M2 : (2147450880 + (x' + n' - 1) / 8) / 8 <= (2147450880 + (x + n - 1) / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)); lia).
lia.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* a suffix of a C string is a C string with the same NUL (G5 cstr_ok_suffix) *)
Lemma tk_cstr_suffix : forall (W : world tfibsegs) mem p0 l0 k, (k <= length l0)%nat ->
  cstr_ok tfibsegs W mem p0 l0 -> cstr_ok tfibsegs W mem (p0 + Z.of_nat k) (skipn k l0).
Proof.
intros W mem p0 l0 k Hk ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
assert (Hlen : Z.of_nat (length (skipn k l0)) = Z.of_nat (length l0) - Z.of_nat k) by (rewrite length_skipn; lia).
assert (Eend : p0 + Z.of_nat k + Z.of_nat (length (skipn k l0)) = p0 + Z.of_nat (length l0)) by lia.
split; [split|].
- rewrite <- (firstn_skipn k l0) in Hg. rewrite <- app_assoc in Hg. apply (YI00.garr8_app tfibsegs) in Hg as [_ Hg].
  rewrite length_firstn in Hg. replace (Nat.min k (length l0)) with k in Hg by lia. exact Hg.
- rewrite <- (firstn_skipn k l0) in Hnz. apply Forall_app in Hnz as [_ Hnz]. exact Hnz.
- split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|].
  split; [intros x Hx; apply Hra; lia|].
  split; [apply (tk_hull_sub _ p0 (Z.of_nat (length l0) + 1)); [exact Hhv | lia | lia | lia]|].
  intros a Ha. rewrite Eend in Ha. exact (Htl a Ha).
Qed.

(* a byte of a C string as the bcmp contract reads it *)
Lemma tk_aview_byte : forall (W : world tfibsegs) mem a v,
  val_mem tfibsegs (rdW W mem) a 1 v -> 0 <= v < 256 -> aview tfibsegs (w_H W) mem a = Some v.
Proof.
intros W mem a v Hv Hr. unfold aview. pose proof (Hv 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0. rewrite le_byte_small by (cbn; lia). cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned.
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.

(* a memory fact over [a, a + n) moves to a memory with the same view there *)
Lemma tk_val_move : forall (W : world tfibsegs) mem mem' a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview tfibsegs (w_H W) mem' x = aview tfibsegs (w_H W) mem x) ->
  val_mem tfibsegs (rdW W mem) a n v -> val_mem tfibsegs (rdW W mem') a n v.
Proof.
intros W mem mem' a n v HA Hv k Hk. rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W) mem mem'); [apply Hv; exact Hk|].
apply HA. lia.
Qed.
End k.

(* ---- the U value of a branch operand: linear normal form (YN3v lin_nf), then the atoms' values ---- *)
Ltac tk_lin_in H :=
  repeat match type of H with context [U ?E ?v] =>
    let r := eval vm_compute in (lin_nf v) in
    lazymatch r with Some (?l, ?c) =>
      rewrite (lin_nf_sound E v l c ltac:(vm_compute; reflexivity)) in H end end;
  cbn [lin_denot] in H.
(* every atom read back through the walk's havoc layers (ew_havoc_old) to its entry value, by the hypotheses
   V : bv_unsigned (ew E n) = v in context *)
Ltac tk_vals_in H :=
  repeat first [rewrite ew_havoc_old in H by lia | progress cbn [ew ewset Nat.eqb] in H];
  repeat match goal with V : bv_unsigned (ew ?E ?n) = _ |- _ =>
    lazymatch type of H with context [bv_unsigned (ew E n)] => rewrite V in H end end;
  rewrite ?Z.mul_1_l, ?Z.add_0_r in H;
  repeat (rewrite Z.mod_small in H by (unfold M64; lia)).
(* the trap arm of a UBSan guard (FMTrapB.v's classes; taken or not-taken arm): its condition over U, then lia *)
Ltac tk_kill H :=
  exfalso;
  first [ rewrite branch_eq_U in H | rewrite branch_ne_U in H | rewrite branch_ltu_U in H
        | rewrite branch_geu_U in H ];
  fm_U_lits H;
  first [ apply Z.eqb_eq in H | apply Z.ltb_lt in H | apply Z.eqb_neq in H | apply Z.ltb_ge in H
        | apply negb_true_iff in H; first [apply Z.eqb_neq in H | apply Z.ltb_ge in H]
        | apply negb_false_iff in H; first [apply Z.eqb_eq in H | apply Z.ltb_lt in H]
        | idtac ];
  tk_lin_in H; tk_vals_in H; lia.

(* ---- walk tactics (FMW_plain.v fw_reg / pl_mk / pl_g / pl_av, renamed) ---- *)
Ltac tk_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.
Ltac tk_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
Ltac tk_g HS :=
  lazymatch goal with |- getr _ ?r = _ => tk_reg HS r end;
  cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
(* the goal U E v = x by v's linear normal form and the atoms' values *)
Ltac tk_lin_goal :=
  lazymatch goal with |- U ?E ?v = _ =>
    let r := eval vm_compute in (lin_nf v) in
    lazymatch r with Some (?l, ?c) =>
      rewrite (lin_nf_sound E v l c ltac:(vm_compute; reflexivity)); cbn [lin_denot] end end;
  repeat first [rewrite ew_havoc_old by lia | progress cbn [ew ewset Nat.eqb]];
  repeat match goal with V : bv_unsigned (ew ?E ?n) = _ |- _ =>
    lazymatch goal with |- context [bv_unsigned (ew E n)] => rewrite V end end;
  rewrite ?Z.mul_1_l, ?Z.add_0_r;
  first [rewrite Z.mod_small by (unfold M64; lia); lia | idtac].
(* a register of the walk's final state whose value is a linear form of the entry atoms *)
Ltac tk_Ug HS :=
  lazymatch goal with |- getr _ ?r = _ => tk_reg HS r end;
  unfold w64; apply fw_sv_U; tk_lin_goal.
(* a run's frame names no writable window: the view is unchanged (FMW_plain.v pl_av) *)
Ltac tk_av W mem1 :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let AVn := fresh "AVn" in
    pose proof (fw_nowin tfibsegs _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as AVn;
    lazymatch goal with AV : forall a, _ -> aview _ _ m0 a = aview _ _ mem1 a |- _ =>
      let AV2 := fresh "AV" in
      assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) mem1 a)
        by (intros a Ha; rewrite (AVn a Ha); exact (AV a Ha));
      clear AV AVn; rename AV2 into AV end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H : context [with_vm_backing (m_vm_lazy (with_vm_backing _ _ _)) _ _] |- _ =>
    rewrite wvb_collapse in H end.

(* ---- the parameters ex_at_T fixes: the declaration at i (decl = DFound name nl ns nl2 close), d ---- *)
Record tkp := mkTKP { tk_i : nat; tk_d : nat; tk_f : nat; tk_name : nat; tk_nl : nat; tk_ns : nat; tk_nl2 : nat;
  tk_close : nat }.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ll = strlen (local), local = uri + nl2; the two strings ex_token compares (fuzz_manifest.c:166) *)
Definition tk_ll (cx : ecx) (p : tkp) : nat := (length (cx_ub cx) - tk_nl2 p)%nat.
Definition tk_pre (cx : ecx) (p : tkp) : list Z := firstn (tk_nl p) (skipn (tk_name p) (cx_tb cx)).
Definition tk_loc (cx : ecx) (p : tkp) : list Z := skipn (tk_nl2 p) (cx_ub cx).
(* B's UBSan bound register: s10 = ~text - j *)
Definition tk_nt (cx : ecx) (j : nat) : Z := 2 ^ 64 - 1 - cx_t cx - Z.of_nat j.

(* the scan's state at the declaration (ex_at_T's pure part) *)
Definition tk_ctx (cx : ecx) (p : tkp) : Prop :=
  ex_base B cx /\ ex_scan cx (tk_i p) (tk_d p) (tk_f p) /\ (tk_i p < length (cx_tb cx))%nat /\
  (S (tk_d p) <= 16)%nat /\
  ManifestModel.decl (cx_tb cx) (tk_i p) =
    ManifestModel.DFound (tk_name p) (tk_nl p) (tk_ns p) (tk_nl2 p) (tk_close p) /\
  ManifestModel.matches (cx_tb cx) (cx_ub cx) (tk_ns p) (tk_nl2 p) = true.

(* what every token cut keeps in memory: the journal and the rest of ex_com, the scan's slots (declared = d + 1),
   ex_at_T's local and close, and the five slots B's setup stores (0x816fc, 0x81700, 0x81718, 0x8171c, 0x81724) *)
Definition tk_mem (cx : ecx) (p : tkp) ly3 S3 (W3 : world tfibsegs) (regs3 : bvmap 5 word)
  (mem3 : word -> option byte) (md3 : Model) : Prop :=
  tk_ctx cx p /\ ex_com B cx ly3 S3 W3 regs3 mem3 md3 /\ ex_slots cx W3 mem3 (S (tk_d p)) /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 0x20) 8 (cx_u cx + Z.of_nat (tk_nl2 p)) /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 0x40) 8 (cx_t cx + Z.of_nat (tk_close p)) /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 0x10) 8 (Z.of_nat (tk_ll cx p) + 1 + Z.of_nat (tk_nl p)) /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 0x50) 8 (Z.of_nat (length (cx_tb cx))) /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 8) 8 (cx_t cx + 1 + Z.of_nat (tk_nl p) + Z.of_nat (tk_ll cx p)) /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 0x18) 8 (Z.of_nat (tk_ll cx p)) /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx) 8 (cx_t cx + 1 + Z.of_nat (tk_nl p) + Z.of_nat (tk_ll cx p)).

(* the registers every token cut keeps: s0 = -1, s3 = 5, s11 = ' ' (ex_sregs), s7 = 1 (the answer), s4 = text + name,
   s5 = nl, s2 = ll + 1 + nl, s6 = text + nl, a6 = text *)
Definition tk_regs (cx : ecx) (p : tkp) (regs3 : bvmap 5 word) : Prop :=
  getr regs3 8 = w64 (2 ^ 64 - 1) /\ getr regs3 19 = w64 5 /\ getr regs3 27 = w64 32 /\
  getr regs3 23 = w64 1 /\
  getr regs3 20 = w64 (cx_t cx + Z.of_nat (tk_name p)) /\ getr regs3 21 = w64 (Z.of_nat (tk_nl p)) /\
  getr regs3 18 = w64 (Z.of_nat (tk_ll cx p) + 1 + Z.of_nat (tk_nl p)) /\
  getr regs3 22 = w64 (cx_t cx + Z.of_nat (tk_nl p)) /\
  getr regs3 16 = w64 (cx_t cx).
(* the caller-saved constants B re-makes after each bcmp (0x8174c .. 0x81754, 0x81794 .. 0x8179c): a7 = 6, t1 = mask *)
Definition tk_cr (regs3 : bvmap 5 word) : Prop :=
  getr regs3 17 = w64 6 /\ getr regs3 6 = w64 EX_MASK1.
(* the loop's registers at index j: s8 = j, s10 = ~text - j *)
Definition tk_jr (cx : ecx) (j : nat) (regs3 : bvmap 5 word) : Prop :=
  getr regs3 24 = w64 (Z.of_nat j) /\ getr regs3 26 = w64 (tk_nt cx j).

(* the loop's model facts at index j: the loop test held (fuzz_manifest.c:103), no token before j *)
Definition tk_bound (cx : ecx) (p : tkp) (j : nat) : Prop :=
  (j + tk_nl p + 1 + tk_ll cx p <= length (cx_tb cx))%nat.
Definition tk_none (cx : ecx) (p : tkp) (j : nat) : Prop :=
  forall j', (j' < j)%nat -> ManifestModel.token_at (cx_tb cx) (tk_pre cx p) (tk_loc cx p) j' = false.
(* the three matches of :107-108 at j *)
Definition tk_mid (cx : ecx) (p : tkp) (j : nat) : Prop :=
  firstn (tk_nl p) (skipn j (cx_tb cx)) = tk_pre cx p /\
  ManifestModel.byte_at (cx_tb cx) (j + tk_nl p) = 58 /\
  firstn (tk_ll cx p) (skipn (j + tk_nl p + 1) (cx_tb cx)) = tk_loc cx p.
(* the left boundary of :109 (token_at's j-case) *)
Definition tk_leftb (cx : ecx) (j : nat) : bool :=
  match j with
  | O => true
  | S j' => negb (ManifestModel.name_char (ManifestModel.byte_at (cx_tb cx) j')) &&
            negb (ManifestModel.byte_at (cx_tb cx) j' =? 46)
  end.

(* ---- the cuts ---- *)
(* TK_LH 0x81730: s8 = j, s10 = ~text - j *)
Definition tk_at_LH (cx : ecx) (p : tkp) (j : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  tk_mem cx p ly3 S3 W3 regs3 mem3 md3 /\ tk_regs cx p regs3 /\ tk_jr cx j regs3 /\
  tk_bound cx p j /\ tk_none cx p j.
(* TK_N 0x817a4: no token at j either; a7, t1 re-made *)
Definition tk_at_N (cx : ecx) (p : tkp) (j : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  tk_mem cx p ly3 S3 W3 regs3 mem3 md3 /\ tk_regs cx p regs3 /\ tk_cr regs3 /\ tk_jr cx j regs3 /\
  tk_bound cx p j /\ tk_none cx p (S j).
(* TK_B 0x817c8: the three matches hold at j > 0; s1 = text + j *)
Definition tk_at_B (cx : ecx) (p : tkp) (j : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  tk_mem cx p ly3 S3 W3 regs3 mem3 md3 /\ tk_regs cx p regs3 /\ tk_cr regs3 /\ tk_jr cx j regs3 /\
  getr regs3 9 = w64 (cx_t cx + Z.of_nat j) /\ (0 < j)%nat /\
  tk_bound cx p j /\ tk_none cx p j /\ tk_mid cx p j.
(* TK_E 0x81834: the three matches and the left boundary hold at j *)
Definition tk_at_E (cx : ecx) (p : tkp) (j : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  tk_mem cx p ly3 S3 W3 regs3 mem3 md3 /\ tk_regs cx p regs3 /\ tk_cr regs3 /\ tk_jr cx j regs3 /\
  tk_bound cx p j /\ tk_none cx p j /\ tk_mid cx p j /\ tk_leftb cx j = true.

(* a continuation: every state satisfying P at pc reaches expected's post *)
Definition tk_k (cx : ecx) (pc : Z)
  (P : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) : Prop :=
  forall ly3 S3 W3 regs3 mem3 md3, P ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs pc regs3 mem3 md3) (ex_post B cx).

(* ---- the sub-segments ---- *)
(* EX_T 0x816dc .. TK_LH at j = 0 (strlen local, strlen text, the first loop test, the setup), or out through
   0x8166c .. 0x816a0 to EX_L at close + 1 when len < ll + nl + 1 (token false) *)
Definition tk_seg_T0 : Prop :=
  forall cx i d f name nl ns nl2 close,
  ex_seg_L_from B cx i -> tk_k cx TK_LH (tk_at_LH cx (mkTKP i d f name nl ns nl2 close) 0) ->
  tk_k cx EX_T (fun ly3 S3 W3 regs3 mem3 md3 => ex_at_T B cx i d f name nl ns nl2 close ly3 S3 W3 regs3 mem3 md3).
(* TK_LH .. bcmp (text + j, text + name, nl), text[j + nl] = ':', bcmp (text + j + nl + 1, local, ll): a mismatch goes
   to TK_N; all three match: j = 0 goes to TK_E, j > 0 to TK_B *)
Definition tk_seg_LH : Prop :=
  forall cx p j,
  tk_k cx TK_N (tk_at_N cx p j) -> tk_k cx TK_E (tk_at_E cx p j) -> tk_k cx TK_B (tk_at_B cx p j) ->
  tk_k cx TK_LH (tk_at_LH cx p j).
(* TK_B .. text[j - 1] a name character or '.': TK_N; else TK_E *)
Definition tk_seg_B : Prop :=
  forall cx p j,
  tk_k cx TK_N (tk_at_N cx p j) -> tk_k cx TK_E (tk_at_E cx p j) -> tk_k cx TK_B (tk_at_B cx p j).
(* TK_E .. text[j + nl + 1 + ll] a name character: TK_N; else a0 = s7 = 1 (0x81904) and EX_R (token true) *)
Definition tk_seg_E : Prop :=
  forall cx p j, ex_seg_R B -> tk_k cx TK_N (tk_at_N cx p j) -> tk_k cx TK_E (tk_at_E cx p j).
(* TK_N .. j + 1: the loop test holds: TK_LH at j + 1; else out to EX_L at close + 1 (token false) *)
Definition tk_seg_N : Prop :=
  forall cx p j,
  ex_seg_L_from B cx (tk_i p) -> tk_k cx TK_LH (tk_at_LH cx p (S j)) -> tk_k cx TK_N (tk_at_N cx p j).

(* ---- pure model facts the sub-segments share (as image A's) ---- *)
Lemma tk_pre_len : forall cx p, tk_ctx cx p -> length (tk_pre cx p) = tk_nl p.
Proof.
intros cx p (_ & _ & _ & _ & Hdc & _). unfold tk_pre.
pose proof (expected_m.decl_found _ _ _ _ _ _ _ Hdc) as (D1 & D2 & D3 & D4 & D5).
rewrite length_firstn, length_skipn. lia.
Qed.
Lemma tk_loc_len : forall cx p, length (tk_loc cx p) = tk_ll cx p.
Proof. intros cx p. unfold tk_loc, tk_ll. apply length_skipn. Qed.
Lemma tk_decl_facts : forall cx p, tk_ctx cx p ->
  (tk_name p + tk_nl p < tk_ns p)%nat /\ (tk_i p < tk_ns p)%nat /\ tk_close p = (tk_ns p + tk_nl2 p)%nat /\
  (tk_close p < length (cx_tb cx))%nat /\ (tk_nl2 p < length (cx_ub cx))%nat.
Proof.
intros cx p (_ & _ & _ & _ & Hdc & Hm).
pose proof (expected_m.decl_found _ _ _ _ _ _ _ Hdc) as (D1 & D2 & D3 & D4 & D5).
unfold ManifestModel.matches in Hm. apply andb_prop in Hm as [Hm _]. apply andb_prop in Hm as [Hm _].
apply Nat.ltb_lt in Hm. tauto.
Qed.

(* the scan after a declaration whose token is absent: index close + 1, declared d + 1 *)
Lemma tk_scan_next : forall cx p, tk_ctx cx p ->
  ManifestModel.token (cx_tb cx) (tk_pre cx p) (tk_loc cx p) = false ->
  (tk_i p < S (tk_close p))%nat /\ ex_scan cx (S (tk_close p)) (S (tk_d p)) (pred (tk_f p)).
Proof.
intros cx [i d f name nl ns nl2 close] (_ & (Hi & Hd & Hf & Hu & Hres) & Hit & Hsd & Hdc & Hm) Htk.
cbn [tk_i tk_d tk_f tk_name tk_nl tk_ns tk_nl2 tk_close] in *. unfold tk_pre, tk_loc in Htk.
cbn [tk_name tk_nl tk_nl2] in Htk.
destruct f as [|f']; [lia|].
pose proof (expected_m.decl_found _ _ _ _ _ _ _ Hdc) as (D1 & D2 & D3 & D4 & D5).
rewrite (expected_m.scan_step _ _ _ _ _ Hit) in Hres. unfold expected_m.sstep in Hres. rewrite Hdc, Hm in Hres.
assert (E16 : (16 <? S d)%nat = false) by (apply Nat.ltb_ge; lia). rewrite E16, Htk in Hres.
cbn [pred]. split; [lia|]. unfold ex_scan. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hu | exact Hres].
Qed.
(* the scan after a declaration whose token is present: expected answers 1 *)
Lemma tk_scan_one : forall cx p, tk_ctx cx p ->
  ManifestModel.token (cx_tb cx) (tk_pre cx p) (tk_loc cx p) = true -> cx_res cx = 1.
Proof.
intros cx [i d f name nl ns nl2 close] (_ & (Hi & Hd & Hf & Hu & Hres) & Hit & Hsd & Hdc & Hm) Htk.
cbn [tk_i tk_d tk_f tk_name tk_nl tk_ns tk_nl2 tk_close] in *. unfold tk_pre, tk_loc in Htk.
cbn [tk_name tk_nl tk_nl2] in Htk.
destruct f as [|f']; [lia|].
rewrite (expected_m.scan_step _ _ _ _ _ Hit) in Hres. unfold expected_m.sstep in Hres. rewrite Hdc, Hm in Hres.
assert (E16 : (16 <? S d)%nat = false) by (apply Nat.ltb_ge; lia). rewrite E16, Htk in Hres. exact Hres.
Qed.

(* the loop ran out: no token *)
Lemma tk_none_false : forall cx p n, tk_ctx cx p -> tk_none cx p n ->
  (length (cx_tb cx) < n + tk_nl p + 1 + tk_ll cx p)%nat ->
  ManifestModel.token (cx_tb cx) (tk_pre cx p) (tk_loc cx p) = false.
Proof.
intros cx p n HX Hn Hl. apply (expected_m.token_false_of _ _ _ n Hn).
rewrite (tk_pre_len cx p HX), tk_loc_len. exact Hl.
Qed.
Lemma tk_none_S : forall cx p j, tk_none cx p j ->
  ManifestModel.token_at (cx_tb cx) (tk_pre cx p) (tk_loc cx p) j = false -> tk_none cx p (S j).
Proof.
intros cx p j Hn Hj j' Hj'. destruct (Nat.eq_dec j' j) as [->|Hne]; [exact Hj|]. apply Hn. lia.
Qed.
Lemma tk_true : forall cx p j,
  ManifestModel.token_at (cx_tb cx) (tk_pre cx p) (tk_loc cx p) j = true ->
  ManifestModel.token (cx_tb cx) (tk_pre cx p) (tk_loc cx p) = true.
Proof. intros cx p j H. exact (expected_m.token_true_of _ _ _ j H). Qed.

(* token_at at j from the three matches and the two boundaries (fuzz_manifest.c:107-111) *)
Lemma tk_at_mid : forall cx p j, tk_ctx cx p -> tk_bound cx p j -> tk_mid cx p j ->
  ManifestModel.token_at (cx_tb cx) (tk_pre cx p) (tk_loc cx p) j =
  tk_leftb cx j &&
  negb (ManifestModel.name_char (ManifestModel.byte_at (cx_tb cx) (j + tk_nl p + 1 + tk_ll cx p))).
Proof.
intros cx p j HX Hb (M1 & M2 & M3). unfold ManifestModel.token_at.
rewrite (tk_pre_len cx p HX), tk_loc_len.
assert (Hle : (j + tk_nl p + 1 + tk_ll cx p <=? length (cx_tb cx))%nat = true) by (apply Nat.leb_le; exact Hb).
rewrite Hle, M1, M2, M3, !ManifestModel.zl_eqb_refl. cbn [andb Z.eqb Pos.eqb].
unfold tk_leftb. reflexivity.
Qed.
Lemma tk_at_pre : forall cx p j, tk_ctx cx p -> firstn (tk_nl p) (skipn j (cx_tb cx)) <> tk_pre cx p ->
  ManifestModel.token_at (cx_tb cx) (tk_pre cx p) (tk_loc cx p) j = false.
Proof.
intros cx p j HX H. unfold ManifestModel.token_at. rewrite (tk_pre_len cx p HX).
destruct (ManifestModel.zl_eqb (firstn (tk_nl p) (skipn j (cx_tb cx))) (tk_pre cx p)) eqn:E.
- apply ManifestModel.zl_eqb_eq in E. contradiction.
- rewrite !andb_false_r. reflexivity.
Qed.
Lemma tk_at_colon : forall cx p j, tk_ctx cx p -> ManifestModel.byte_at (cx_tb cx) (j + tk_nl p) <> 58 ->
  ManifestModel.token_at (cx_tb cx) (tk_pre cx p) (tk_loc cx p) j = false.
Proof.
intros cx p j HX H. unfold ManifestModel.token_at. rewrite (tk_pre_len cx p HX).
apply Z.eqb_neq in H. rewrite H. rewrite !andb_false_r. cbn [andb]. reflexivity.
Qed.
Lemma tk_at_loc : forall cx p j, tk_ctx cx p ->
  firstn (tk_ll cx p) (skipn (j + tk_nl p + 1) (cx_tb cx)) <> tk_loc cx p ->
  ManifestModel.token_at (cx_tb cx) (tk_pre cx p) (tk_loc cx p) j = false.
Proof.
intros cx p j HX H. unfold ManifestModel.token_at. rewrite (tk_pre_len cx p HX), tk_loc_len.
destruct (ManifestModel.zl_eqb (firstn (tk_ll cx p) (skipn (j + tk_nl p + 1) (cx_tb cx))) (tk_loc cx p)) eqn:E.
- apply ManifestModel.zl_eqb_eq in E. contradiction.
- rewrite !andb_false_r. cbn [andb]. reflexivity.
Qed.

(* ---- the frame and the strings: B's frame is 240 bytes, STK_expected = 240 + 8224 ---- *)
Lemma tk_bounds : forall cx, ex_base B cx ->
  cx_F cx mod 16 = 0 /\ alloc_ceiling + STK_expected - 240 <= cx_F cx /\ cx_F cx + 240 <= 2 ^ 47 /\
  2 ^ 46 <= cx_F cx /\
  4096 <= cx_t cx /\ cx_t cx + Z.of_nat (length (cx_tb cx)) + 8 <= alloc_ceiling /\
  4096 <= cx_u cx /\ cx_u cx + Z.of_nat (length (cx_ub cx)) + 8 <= alloc_ceiling /\
  (length (cx_ub cx) <= 255)%nat.
Proof.
  intros cx ((HPRE & _) & _ & _ & _ & Ct & Cu & _ & _ & Hlen & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof Ct as (_ & Ht4 & Htc & _). pose proof Cu as (_ & Hu4 & Huc & _).
  pose proof asan_consts as (C1 & _).
  assert (HSTK : STK_expected = 240 + 8224) by reflexivity.
  unfold cx_F, cx_sp in *.
  split; [replace (spZ (cx_regs cx) - 240) with (spZ (cx_regs cx) + (-15) * 16) by lia;
          rewrite Z_mod_plus_full; exact Hal16|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Ht4|]. split; [exact Htc|]. split; [exact Hu4|].
  split; [exact Huc | exact Hlen].
Qed.

(* ---- moving tk_mem across a step that writes only [lo, F) (a run that writes nothing: lo = F; a runtime call at
   sp = F: lo = F - its stack) and keeps sp, gp, tp, s9 ---- *)
Lemma tk_mem_move : forall cx p ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 lo,
  tk_mem cx p ly3 S3 W3 regs3 mem3 md3 ->
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem4 md4 0 ->
  alloc_ceiling <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < cx_F cx) ->
     aview tfibsegs (w_H W3) mem4 a = aview tfibsegs (w_H W3) mem3 a) ->
  getr regs4 2 = w64 (cx_F cx) -> getr regs4 3 = getr (cx_regs cx) 3 -> getr regs4 4 = getr (cx_regs cx) 4 ->
  getr regs4 25 = w64 SHADOW_OFF ->
  tk_mem cx p ly3 S3 W3 regs4 mem4 md4.
Proof.
intros cx p ly3 S3 W3 regs3 mem3 md3 regs4 mem4 md4 lo
  (HX & HC & HSL & V20 & V40 & V10 & V50 & V8 & V18 & V0) HJ4 Hlo AV R2 R3 R4 R25.
pose proof HX as (HB & _).
pose proof (tk_bounds cx HB) as (HFm & HFlo & HFhi & HF46 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_expected = 240 + 8224) by reflexivity.
assert (KL : fw_low tfibsegs (w_H W3) mem3 mem4) by (intros a Ha; apply AV; lia).
assert (KH : forall a v, cx_F cx <= a -> a + 8 <= cx_F cx + 240 ->
  val_mem tfibsegs (rdW W3 mem3) a 8 v -> val_mem tfibsegs (rdW W3 mem4) a 8 v).
{ intros a v Ha Hb. apply tk_val_move. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply AV; lia. }
destruct HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25' & HSV & HRO & HCt & HCu & HKt & HKu).
split; [exact HX|]. split.
{ split; [exact HJ4|]. split; [exact Hbl|].
  split; [exact (fw_glob_low tfibsegs W3 mem3 mem4 _ _ _ _ KL HGL)|].
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R25|].
  split.
  { unfold ex_saved_ok in *. rewrite Forall_forall in HSV |- *. intros s Hs.
    assert (Ho : 136 <= fst s <= 232)
      by (cbv [EX_SAVED In] in Hs; repeat (destruct Hs as [<-|Hs]; [cbn [fst]; lia|]); destruct Hs).
    apply KH; [lia | lia | exact (HSV s Hs)]. }
  split; [exact (fw_rodata_low tfibsegs B _ mem3 mem4 fmw_segs_low KL HRO)|].
  split; [exact (fw_cstr_low tfibsegs W3 mem3 mem4 _ _ KL HCt)|].
  split; [exact (fw_cstr_low tfibsegs W3 mem3 mem4 _ _ KL HCu)|].
  split; [exact HKt | exact HKu]. }
split.
{ destruct HSL as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & S10).
  split; [apply KH; [lia | lia | exact S1]|]. split; [apply KH; [lia | lia | exact S2]|].
  split; [apply KH; [lia | lia | exact S3']|]. split; [apply KH; [lia | lia | exact S4]|].
  split; [apply KH; [lia | lia | exact S5]|]. split; [apply KH; [lia | lia | exact S6]|].
  split; [apply KH; [lia | lia | exact S7]|]. split; [apply KH; [lia | lia | exact S8]|].
  split; [apply KH; [lia | lia | exact S9]|].
  apply KH; [lia | lia | exact S10]. }
split; [apply KH; [lia | lia | exact V20]|]. split; [apply KH; [lia | lia | exact V40]|].
split; [apply KH; [lia | lia | exact V10]|]. split; [apply KH; [lia | lia | exact V50]|].
split; [apply KH; [lia | lia | exact V8]|]. split; [apply KH; [lia | lia | exact V18]|].
apply KH; [lia | lia | exact V0].
Qed.
End c.
