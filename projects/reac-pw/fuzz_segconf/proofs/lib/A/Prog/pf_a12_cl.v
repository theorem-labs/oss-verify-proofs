(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 327 of its 371 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a7_w3_c.v, with its module paths and module names changed; 316 of its 361 lines of code are new or changed and 326 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): ONE strcasecmp call of segment A12 of
   reac_segconf_parse_file's walk (0x88370 "yes", 0x88388 "true", 0x883d4 "no", 0x883e8 "false"), stepped from the
   state at the trampoline to the return address with the mid-walk invariant a12_I (lib/A/Prog/pf_a12_k.v) rebuilt
   there. The step is PaArt.v's aj_art_at around the interceptor's contract (lib/A/Prog/pf_a12_c.v a12_sc_pre, at
   the interceptor owner's row 10, RtSeg.astrcasecmp_realizes); art_post's presence clause is moved into the answer so that
   aj_art_at hands it back. After the call, pf_base comes back by a12_sc_after (pf_a5_k.v a5_move0), the spine and
   the value in buf by pf_a12_keep.v (every byte they read lies below alloc_ceiling, the call writes only its
   scratch window [s1 - 2 ESTACK, s1) above it), and the callee-saved registers by aregs_preserved.
   Segment A12's proof, by the G3 walk owner, 2026-10-30. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaFx SegAddr SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_pieces pf_a5_k pf_a6_k
pf_a12_pure pf_a12_k pf_a12_keep pf_a12_c.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the runtime record facts of the image: api_env, which aj_art_at asks for (trim_s.v:124's TL) *)
Hypothesis TL : PALib B.
(* the interceptor owner's interface row 10, at the listing's strcasecmp trampoline (pf_pieces.v's segment list for A12) *)
Hypothesis ASC : forall fx0 : YK11.FPState,
  @RtSeg.astrcasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcasecmp).
Let errno_low := pal_env B TL.

Section s.
Context {fx : YK11.FPState}.

(** *** The branch on the interceptor's answer, as the token executor leaves it *)
Lemma a12_br_eq0 : forall E k z b, ew E k = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff k 0)) (sv_denot E (SLit 0)) = b -> (z =? 0) = b.
Proof.
intros E k z b H Hz Hc. rewrite branch_eq_U, (U_atom E k z H Hz), U_lit in Hc by lia. exact Hc.
Qed.

Lemma a12_a0_br : forall (rX1 : bvmap 5 word) v pos val b,
  branch_taken BC_EQ (sv_denot (a12_E rX1 v pos val) (SOff 10 0))
    (sv_denot (a12_E rX1 v pos val) (SLit 0)) = b ->
  (bv_unsigned (getr rX1 10) =? 0) = b.
Proof.
intros rX1 v pos val b Hc.
apply (a12_br_eq0 (a12_E rX1 v pos val) 10 (bv_unsigned (getr rX1 10)) b); [| | exact Hc].
- unfold a12_E. rewrite (ew_Eimg_Ereg_nat rX1 (a12_extra v pos val) 10 10%bv eq_refl).
  symmetry. apply Z_to_bv_bv_unsigned.
- pose proof (bv_unsigned_in_range 64 (getr rX1 10)) as H.
  change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.

Lemma a12_a0_zero : forall (rX1 : bvmap 5 word), (bv_unsigned (getr rX1 10) =? 0) = true ->
  getr rX1 10 = w64 0.
Proof.
intros rX1 H. apply Z.eqb_eq in H. apply bv_eq. rewrite H. unfold w64. vm_compute. reflexivity.
Qed.

Lemma a12_a0_nz : forall (rX1 : bvmap 5 word), (bv_unsigned (getr rX1 10) =? 0) = false ->
  getr rX1 10 <> w64 0.
Proof.
intros rX1 H E. apply Z.eqb_neq in H. apply H. rewrite E. unfold w64. vm_compute. reflexivity.
Qed.
(** *** The registers a run of A12 must leave alone for the mid-walk invariant to survive it: sp / gp / tp /
    s0 / s1 / s6 (pf_base's list) and s2 / s3 / s4 / s5 / s8 / s9 / s10 / s11 (a12_I's). s7 is NOT among them:
    the code writes parse_bool's answer into it. *)
Definition a12_KEPT : list (bv 5) :=
  [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv.

(** The seed's environment agrees with the plain register environment below 32. *)
Lemma a12_ag0 : forall (rX : bvmap 5 word) v pos val,
  env_agree 32 (Ereg rX (a12_extra v pos val)) (a12_E rX v pos val).
Proof.
intros rX v pos val. split;
  [intros k Hk; unfold a12_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity].
Qed.

(** The value's first byte is a byte. *)
Lemma a12_val0_rng : forall (W : world SEGS) mem vp val, sa_str (aview SEGS (w_H W) mem) vp val ->
  0 <= nth 0 val 0 < 256.
Proof.
intros W mem vp val ((Hz & _) & _).
pose proof (Hz 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as H.
change (Z.of_nat 0) with 0 in H. rewrite Z.add_0_r in H.
replace (nth 0 (val ++ [0]) 0) with (nth 0 val 0) in H by (destruct val; reflexivity).
destruct (aview_byte SEGS (w_H W) mem vp (nth 0 val 0) H) as (_ & _ & _ & Hr). exact Hr.
Qed.

(** The value's second byte is a byte. *)
Lemma a12_val1_rng : forall (W : world SEGS) mem vp val, sa_str (aview SEGS (w_H W) mem) vp val ->
  0 <= nth 1 val 0 < 256.
Proof.
intros W mem vp val HS.
destruct (Nat.lt_ge_cases 1 (length val)) as [Hl|Hl]; [|rewrite nth_overflow by lia; lia].
destruct HS as ((Hz & _) & _).
pose proof (Hz 1%nat ltac:(rewrite length_app; cbn [length]; lia)) as H.
change (Z.of_nat 1) with 1 in H. rewrite (app_nth1 val [0] 0 Hl) in H.
destruct (aview_byte SEGS (w_H W) mem (vp + 1) (nth 1 val 0) H) as (_ & _ & _ & Hr). exact Hr.
Qed.

(** *** The branch on a byte of the value against a literal (0x883a8 `bne s3, '1'`, 0x883f4 `bne s3, '0'`,
    and the `beqz` of the value's second byte) *)
Lemma a12_br_ne : forall E k z c b, ew E k = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff k 0)) (sv_denot E (SLit c)) = b -> negb (z =? c) = b.
Proof.
intros E k z c b H Hz Hc Hb. rewrite branch_ne_U, (U_atom E k z H Hz), U_lit in Hb by lia. exact Hb.
Qed.

Lemma a12_ew33 : forall (rX : bvmap 5 word) v pos val,
  ew (a12_E rX v pos val) 33 = Z_to_bv 64 (nth 0 val 0).
Proof.
intros rX v pos val. unfold a12_E.
rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra rX (a12_extra v pos val) 1).
Qed.

Lemma a12_ew34 : forall (rX : bvmap 5 word) v pos val,
  ew (a12_E rX v pos val) 34 = Z_to_bv 64 (nth 1 val 0).
Proof.
intros rX v pos val. unfold a12_E.
rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra rX (a12_extra v pos val) 2).
Qed.

(** *** The same transport as a12_step, for a run that also writes s3 (0x883a0 `lbu s3, 0(s9)`) *)
Definition a12_KEPT3 : list (bv 5) := [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 25; 26; 27]%bv.
Lemma a12_kept3_sub : forall r, In r a12_KEPT3 -> In r a12_KEPT.
Proof.
intros r H. unfold a12_KEPT3 in H. unfold a12_KEPT. cbn [In] in H |- *. tauto.
Qed.

Lemma a12_step3 : forall n v pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d gi vp val z3 z3'
    (rX' : bvmap 5 word) (mdq : Model),
  a12_I B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdq 0 ->
  (forall r, In r a12_KEPT3 -> getr rX' r = getr rX r) ->
  getr rX' 19 = w64 z3' ->
  a12_I B n v pos lyc Sc Wc rX' memc mdq cf nm o ln d gi vp val z3'.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 z3' rX' mdq HI HJq HK H19.
pose proof HI as (HB & HMID & HST & HVstr & HVinb & HRG).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof HB as (HCX & (HJ0 & Hly' & HFS & HPERM & HSV & HFL & HFRM & _) & HOBJ & HSL & HFSH).
assert (HFI' : pf_rg rX' (a5_FI B v)).
{ unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
  assert (Hm : In (Z_to_bv 5 (fst rv)) a12_KEPT3).
  { unfold a5_FI in Hin. cbn [In] in Hin. unfold a12_KEPT3. cbn [In].
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst];
      repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]). }
  rewrite (HK _ Hm). exact (HFI rv Hin). }
split; [|split; [exact HMID | split; [exact HST | split; [exact HVstr | split; [exact HVinb|]]]]].
- split; [exact HCX|]. split; [|exact (conj HOBJ (conj HSL HFSH))].
  exact (conj HJq (conj Hly' (conj HFS (conj HPERM (conj HSV (conj HFL (conj HFRM HFI'))))))).
- unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
  unfold PF_RM in Hin. cbn [app In] in Hin.
  destruct Hin as [<-|[Hin|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
  + cbn [fst snd]. transitivity (getr rX 18).
    * exact (HK 18%bv ltac:(unfold a12_KEPT3; cbn [In]; tauto)).
    * exact (HRG (18, 0x23) ltac:(unfold PF_RM; cbn [app In]; tauto)).
  + rewrite <- Hin. cbn [fst snd]. exact H19.
  + cbn [fst snd]. transitivity (getr rX 24).
    * exact (HK 24%bv ltac:(unfold a12_KEPT3; cbn [In]; tauto)).
    * exact (HRG (24, p_c v) ltac:(unfold PF_RM; cbn [app In]; tauto)).
  + cbn [fst snd]. transitivity (getr rX 27).
    * exact (HK 27%bv ltac:(unfold a12_KEPT3; cbn [In]; tauto)).
    * exact (HRG (27, pf_SH v pos) ltac:(unfold PF_RM; cbn [app In]; tauto)).
  + cbn [fst snd]. transitivity (getr rX 21).
    * exact (HK 21%bv ltac:(unfold a12_KEPT3; cbn [In]; tauto)).
    * exact (HRG (21, p_t v + Z.of_nat (pf_next (p_s v) o)) ltac:(unfold PF_RM; cbn [app In]; tauto)).
  + cbn [fst snd]. transitivity (getr rX 26).
    * exact (HK 26%bv ltac:(unfold a12_KEPT3; cbn [In]; tauto)).
    * exact (HRG (26, ln + 1) ltac:(unfold PF_RM; cbn [app In]; tauto)).
  + cbn [fst snd]. transitivity (getr rX 20).
    * exact (HK 20%bv ltac:(unfold a12_KEPT3; cbn [In]; tauto)).
    * exact (HRG (20, seg_spec.rseg_addr (p_c v) gi) ltac:(unfold PF_RM; cbn [app In]; tauto)).
  + cbn [fst snd]. transitivity (getr rX 25).
    * exact (HK 25%bv ltac:(unfold a12_KEPT3; cbn [In]; tauto)).
    * exact (HRG (25, vp) ltac:(unfold PF_RM; cbn [app In]; tauto)).
Qed.

(* the a12_step3 list with s7, for a stretch that writes s3 but not parse_bool's answer *)
Definition a12_KEPT37 : list (bv 5) := 23%bv :: a12_KEPT3.
Lemma a12_kept37_sub3 : forall r, In r a12_KEPT3 -> In r a12_KEPT37.
Proof. intros r H. right. exact H. Qed.

(* the same list with s7, for a stretch that does not write parse_bool's answer *)
Definition a12_KEPT7 : list (bv 5) := 23%bv :: a12_KEPT.
Lemma a12_kept7_sub : forall r, In r a12_KEPT -> In r a12_KEPT7.
Proof. intros r H. right. exact H. Qed.

Lemma a12_step : forall n v pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d gi vp val z3
    (rX' : bvmap 5 word) (mdq : Model),
  a12_I B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdq 0 ->
  (forall r, In r a12_KEPT -> getr rX' r = getr rX r) ->
  a12_I B n v pos lyc Sc Wc rX' memc mdq cf nm o ln d gi vp val z3.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 rX' mdq HI HJq HK.
pose proof HI as (HB & HMID & HST & HVstr & HVinb & HRG).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof HB as (HCX & (HJ0 & Hly' & HFS & HPERM & HSV & HFL & HFRM & _) & HOBJ & HSL & HFSH).
assert (HFI' : pf_rg rX' (a5_FI B v)).
{ unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
  assert (Hm : In (Z_to_bv 5 (fst rv)) a12_KEPT).
  { unfold a5_FI in Hin. cbn [In] in Hin. unfold a12_KEPT. cbn [In].
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst];
      repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]). }
  rewrite (HK _ Hm). exact (HFI rv Hin). }
split; [|split; [exact HMID | split; [exact HST | split; [exact HVstr | split; [exact HVinb|]]]]].
- split; [exact HCX|]. split; [|exact (conj HOBJ (conj HSL HFSH))].
  exact (conj HJq (conj Hly' (conj HFS (conj HPERM (conj HSV (conj HFL (conj HFRM HFI'))))))).
- unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
  assert (Hm : In (Z_to_bv 5 (fst rv)) a12_KEPT).
  { unfold PF_RM in Hin. cbn [app In] in Hin. unfold a12_KEPT. cbn [In].
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [fst];
      repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]). }
  rewrite (HK _ Hm). exact (HRG rv Hin).
Qed.
(** *** What every run of A12 needs besides the seed: the environment is an image environment, and the inline
    checks' shadow entries hold. *)
Lemma a12_ei : forall (rX : bvmap 5 word) v pos val, img_env VAL A_LIM (a12_E rX v pos val).
Proof. intros rX v pos val. unfold a12_E. apply Eimg_env. Qed.

Lemma a12_in_app_sub : forall lo len lo' len', in_app lo len -> lo <= lo' -> lo' + len' <= lo + len ->
  0 <= len' -> in_app lo' len'.
Proof. intros lo len lo' len' (H1 & H2) Ha Hb Hc. split; [lia|]. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. Qed.

Lemma a12_shok_I : forall n v pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d gi vp val z3 (two : bool),
  a12_I B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 ->
  (if two then (1 <= length val)%nat else True) ->
  sh_ok SEGS a12_Bx (if two then a12_SH2 else a12_SH1) (a12_E rX v pos val) (mrestrict (w_H Wc) memc).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 two HI Htwo.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HI as (HB & HMID & HST & HVstr & HVinb & HRG).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hfin & G & HFP & HSP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof HB as (_ & _ & HOBJ & _ & HFSH).
pose proof HOBJ as (_ & _ & _ & HAc & HCH0 & _).
pose proof HST as (HRC & HOKcur & _ & _).
assert (Hgi32 : (gi < 32)%nat)
  by (destruct HRC as (bs & _ & (_ & Hn32 & _)); cbn [pf_cur_ok] in HOKcur; lia).
destruct (a6_frame B v pos lyc Sc Wc rX memc mdc (proj1 (proj2 HB))) as (_ & HF1 & HF2 & HF3 & HFapp & _).
change (fs_frame_bytes 5) with 2048 in HF2, HFapp.
destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HCH0
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hc1 & Hc2 & Hc3 & Hc4 & Hcapp).
unfold pf_inb, PF_O_BUF in HVinb.
unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.SEG_C_SIZE in *.
assert (Hgi' : 0 <= Z.of_nat gi <= 31) by lia.
(* the three atoms the entries name *)
assert (E22 : ew (a12_E rX v pos val) 22 = Z_to_bv 64 SHADOW_OFF)
  by (unfold a12_E; rewrite (ew_Eimg_Ereg_nat rX _ 22 22%bv eq_refl);
      exact (a5_rg_get rX _ 22 _ HFI ltac:(cbn [a5_FI In]; tauto))).
assert (E25 : ew (a12_E rX v pos val) 25 = Z_to_bv 64 vp)
  by (unfold a12_E; rewrite (ew_Eimg_Ereg_nat rX _ 25 25%bv eq_refl);
      exact (a5_rg_get rX _ 25 _ HRG ltac:(cbn [PF_RM app In]; tauto))).
assert (E20 : ew (a12_E rX v pos val) 20 = Z_to_bv 64 (p_c v + 356 * Z.of_nat gi))
  by (unfold a12_E; rewrite (ew_Eimg_Ereg_nat rX _ 20 20%bv eq_refl);
      exact (a5_rg_get rX _ 20 _ HRG ltac:(cbn [PF_RM app In]; tauto))).
assert (U22 : U (a12_E rX v pos val) a12_Bx = SHADOW_OFF)
  by (unfold a12_Bx; apply (U_atom _ 22 SHADOW_OFF E22); unfold SHADOW_OFF; lia).
assert (U25 : U (a12_E rX v pos val) (SOff 25 0) = vp)
  by (apply (U_atom _ 25 vp E25); lia).
assert (U20 : U (a12_E rX v pos val) (SOff 20 0) = p_c v + 356 * Z.of_nat gi)
  by (apply (U_atom _ 20 _ E20); lia).
(* the value's bytes, inside buf, and cur's two words, inside the block *)
pose proof (a12_ra_buf v pos (rdW Wc memc) HF3 HFSH) as HRAbuf.
unfold PF_O_BUF in HRAbuf.
pose proof HAc as (_ & _ & _ & HRAc & _).
destruct two.
- apply (a12_shok2 (a12_E rX v pos val) Wc memc v pos gi vp U22 U25 U20).
  + exact (range_addressable_sub (rdW Wc memc) SHADOW_OFF (pf_F v pos + 64) 512 vp 2 HRAbuf
             ltac:(lia) ltac:(lia)).
  + exact (range_addressable_sub (rdW Wc memc) SHADOW_OFF (p_c v) 16616
             (p_c v + 356 * Z.of_nat gi + seg_spec.RS_IGNORE) 8 HRAc
             ltac:(unfold seg_spec.RS_IGNORE; lia) ltac:(unfold seg_spec.RS_IGNORE; lia)).
  + exact (a12_in_app_sub (pf_F v pos) 2048 vp 2 HFapp ltac:(lia) ltac:(lia) ltac:(lia)).
  + exact (a12_in_app_sub bc (req_size mc) (p_c v + 356 * Z.of_nat gi + seg_spec.RS_IGNORE) 8 Hcapp
             ltac:(unfold seg_spec.RS_IGNORE; lia) ltac:(unfold seg_spec.RS_IGNORE; lia) ltac:(lia)).
- apply (a12_shok1 (a12_E rX v pos val) Wc memc v pos gi vp U22 U25 U20).
  + exact (range_addressable_sub (rdW Wc memc) SHADOW_OFF (pf_F v pos + 64) 512 vp 1 HRAbuf
             ltac:(lia) ltac:(lia)).
  + exact (range_addressable_sub (rdW Wc memc) SHADOW_OFF (p_c v) 16616
             (p_c v + 356 * Z.of_nat gi + seg_spec.RS_IGNORE) 8 HRAc
             ltac:(unfold seg_spec.RS_IGNORE; lia) ltac:(unfold seg_spec.RS_IGNORE; lia)).
  + exact (a12_in_app_sub (pf_F v pos) 2048 vp 1 HFapp ltac:(lia) ltac:(lia) ltac:(lia)).
  + exact (a12_in_app_sub bc (req_size mc) (p_c v + 356 * Z.of_nat gi + seg_spec.RS_IGNORE) 8 Hcapp
             ltac:(unfold seg_spec.RS_IGNORE; lia) ltac:(unfold seg_spec.RS_IGNORE; lia) ltac:(lia)).
Qed.
Lemma a12_call : forall (s : list Z) (RET : Z) n v pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d gi vp val
    z3 (rXc : bvmap 5 word) (mdq : Model) (Q : world SEGS -> config -> Prop),
  a12_I B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdq 0 ->
  In s PARSE_FILE_LITS ->
  (forall r, In r a12_KEPT -> getr rXc r = getr rX r) ->
  getr rXc 1 = Z_to_bv 64 (BASE + RET) -> YK0s.ret_ok (getr rXc 1) ->
  getr rXc 10 = w64 vp -> getr rXc 11 = w64 (seg_litA_rc s) ->
  (forall (rX' : bvmap 5 word) memc' mdc',
     a12_I B n v pos lyc Sc Wc rX' memc' mdc' cf nm o ln d gi vp val z3 ->
     aregs_preserved rXc rX' ->
     (getr rX' 10 = w64 0 <-> SegModel.strcasecmp val s = 0) ->
     SRr SEGS Wc (mkCfg (mkst rX' (Z_to_bv 64 (BASE + RET)) memc' (seg_rom SEGS)) mdc') Q) ->
  SRr SEGS Wc (mkCfg (mkst rXc (Z_to_bv 64 (SIG SS___interceptor_trampoline_strcasecmp)) memc (seg_rom SEGS)) mdq) Q.
Proof.
intros s RET n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 rXc mdq Q
  HI HJq Hs HKR R1 Hra R10 R11 HK.
pose proof (a12_step n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 rXc mdq HI HJq HKR) as HIq.
pose proof HIq as (HBq & HMID & HST & HVstr & HVinb & HRGq).
pose proof (a5_geo B v pos lyc Sc Wc rXc memc mdq PF_SC_LINE HBq) as (HAR & Hly & Hfin & G & HFP & HSP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a5_fi_regs B v pos lyc Sc Wc rXc memc mdq PF_SC_LINE HBq) as HFIc.
pose proof HBq as (_ & _ & HOBJ & _ & _).
pose proof HOBJ as (_ & _ & _ & _ & HCH0 & _).
pose proof STK_values as (_ & SRF & _ & SPF & _).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (a6_s1 (pf_sp0 v) G3) as (S1a & S1b & S1c & S1d). rewrite <- a6_s1_eq in S1a, S1b, S1c, S1d.
destruct (a6_heap_bounds B lyc Sc Wc memc mdq (p_c v) seg_spec.SEG_C_SIZE HAR HCH0
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hc1 & Hc2 & Hc3 & Hc4 & _).
assert (C2 : getr rXc 2 = w64 (pf_s1 v))
  by exact (a5_rg_get rXc _ 2 _ HFIc ltac:(cbn [a5_FI In]; tauto)).
assert (C3 : getr rXc 3 = w64 (as_gp B))
  by exact (a5_rg_get rXc _ 3 _ HFIc ltac:(cbn [a5_FI In]; tauto)).
assert (C4 : getr rXc 4 = w64 (as_tp B))
  by exact (a5_rg_get rXc _ 4 _ HFIc ltac:(cbn [a5_FI In]; tauto)).
assert (Csp : spZ rXc = pf_s1 v).
{ unfold spZ. rewrite C2. unfold w64. apply unsigned_lit_small. lia. }
(* the call: aj_art_at around the interceptor's contract, presence moved into the answer *)
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False)
    (SIG SS___interceptor_trampoline_strcasecmp) Wc rXc memc STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdq 0
    (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + RET))
    (fun regs' mem' => (getr regs' 10 = w64 0 <-> SegModel.strcasecmp val s = 0) /\
       (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) mem' a)) HJq).
  - rewrite Csp. lia.
  - exact S1d.
  - lia.
  - rewrite Hes. lia.
  - rewrite SPF, Hes. lia.
  - exact R1.
  - intros a [].
  - eapply SRr_mono.
    { exact (a12_sc_pre B ASC v pos lyc Sc Wc rXc memc mdq rXc vp val s HBq Hs HVstr HVinb Csp Hra C3 C4 R10 R11). }
    cbv beta. intros W' c' _ (HW & regs' & mem' & md' & Hc & HAR' & HP' & Hsm & HQ & Hfr & Hpr & Hscr).
    split; [exact HW|]. exists regs', mem', md'.
    split; [exact Hc|]. split; [exact HAR'|]. split; [exact HP'|]. split; [exact Hsm|].
    split; [exact (conj HQ Hpr)|]. split; [exact Hfr|]. split; [exact Hpr | exact Hscr]. }
(* back at the return address, at the same FP state *)
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (Ha02 & HPRES) & HK2).
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HK2 by lia.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 2 * ESTACK <= a < pf_s1 v) ->
  rdW Wc mem2 a = rdW Wc memc a) by (intros a Ha Hn; exact (HK2 a Ha Hn (fun H => H))).
assert (HFI2 : pf_rg regs2 (a5_FI B v)) by exact (a5_rg_pres rXc regs2 _ HP2 (a5_FI_cs B v) HFIc).
pose proof (a12_sc_after B v pos lyc Sc Wc rXc memc mdq mem2 md2 regs2 HBq HJ2 KM HPRES HFI2) as HB2.
assert (KL : forall x, 0 <= x < alloc_ceiling -> rdW Wc mem2 x = rdW Wc memc x)
  by (intros x Hx; apply KM; [lia | rewrite Hes; lia]).
apply (HK regs2 mem2 md2); [| exact HP2 | exact Ha02].
split; [exact HB2|]. split; [exact HMID|]. split.
{ apply (a12_st_keep v pos (rdW Wc memc) (rdW Wc mem2) cf (Some gi) nm _ HST); try lia. exact KL. }
split.
{ apply (a12_str_keep (rdW Wc memc) (rdW Wc mem2) vp val HVstr). intros x Hx. apply KL.
  unfold pf_inb, PF_O_BUF in HVinb.
  pose proof (Z.mod_pos_bound (vp + Z.of_nat (length val)) 8 ltac:(lia)). lia. }
split; [exact HVinb|].
apply (a5_rg_pres rXc regs2 _ HP2); [|exact HRGq].
unfold PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
Qed.

End s.
End e.
End f.
End d.
