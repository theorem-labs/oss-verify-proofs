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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 532 of its 583 lines of code are new or changed and 402 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A: segment A5 of reac_segconf_parse_file, the pieces HEAD / R1 / R2 of
   lib/A/Prog/pf_a5_d.v (segment A5's proof, 2026-10-30).
   proves no function (kind: segment lemma of reac_segconf_parse_file's image-A walk: segment A5's HEAD / R1 / R2
   pieces; the function's rule-24 record is
   the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md).
   The code (the unit's internal record, commit dfb49d6ad789, path records/segp/dis/
   reac_segconf_parse_file.fuzz_segconf.asan.s):
     HEAD 0x87ddc addi a1,zero,0xa; mv a0,s9; 0x87de4 jal the strchr trampoline (return 0x87de8 = R1).
     R1   0x87de8 mv s5,a0; beqz a0,0x87e00.
          a0 <> 0: sub s7,s5,s9; beqz s5 (decided: not taken); addi s5,s5,1; j 0x87e14 (= Q3).
          a0 = 0: 0x87e00 mv a0,s9; 0x87e04 jal the strlen trampoline (return 0x87e08 = R2).
     R2   0x87e08 mv s7,a0; bnez s5 (s5 = 0: not taken); add s5,s9,s7; falls to 0x87e14 (= Q3).
   Each piece: a fresh seed at its pc (every register its own atom, no region: these instructions touch no memory,
   as trim_s.v's seed), a token run of the symbolic executor (SegPaLib.v paj_run_tok / paj_run_to_tok, the branch
   by psrr_branch_tok), the interceptor call through lib/A/Prog/PaArt.v aj_art_at (as trim_s.v's strlen call), and
   the next point's INV rebuilt with pf_a5_k.v's a5_move0 (a5h_step below). The functional facts are the plain
   proof's (lib/Prog/pf_p2.v `head`, 04f2be60e018): strchr's answer is pf_line's end (a5h_break_first /
   a5h_break_none over SegModel.break_nl), and pf_next by pfA_facts.v L_next_holds.
   Section hypotheses: ASTRCHR (the interceptor owner's row 6, RtSeg.astrchr_realizes at the listing's strchr
   trampoline), ASTRLEN (row 16, RtString.astrlen_realizes at the listing's strlen trampoline), TL (the listing's
   runtime record: aj_art_at needs its pal_env). No SSPX and no VRO: the transport is a5_move0. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtShadow.
(* the interceptor owner's rows 6 and 16: RtSeg.astrchr_realizes, RtString.astrlen_realizes *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaSB PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_d pf_a2_k pf_a5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= pure facts ======================= *)
(* strchr(p, '\n')'s first index is the length of break_nl's line *)
Lemma a5h_break_first : forall p j, RtSeg.first_at p 10 j -> j = length (fst (break_nl p)) /\ (j < length p)%nat.
Proof.
induction p as [|b r IH]; intros j (Hl & Hn & Hf); cbn [length] in Hl; [lia|].
cbn [break_nl]. destruct (b =? 10) eqn:Eb.
- apply Z.eqb_eq in Eb. destruct j as [|j].
  + cbn. split; [reflexivity | lia].
  + exfalso. apply Hf. cbn [firstn]. left. exact Eb.
- apply Z.eqb_neq in Eb. destruct j as [|j]; [cbn [nth] in Hn; congruence|].
  assert (H' : RtSeg.first_at r 10 j).
  { split; [lia|]. split; [exact Hn|]. intros Hi. apply Hf. cbn [firstn]. right. exact Hi. }
  destruct (IH j H') as [E1 E2].
  destruct (break_nl r) as [l q] eqn:Er. try rewrite Er in E1. cbn in E1 |- *. split; lia.
Qed.
(* no '\n': the line is the whole rest *)
Lemma a5h_break_none : forall p, ~ In 10 p -> fst (break_nl p) = p.
Proof.
induction p as [|b r IH]; intros Hn; [reflexivity|].
cbn [break_nl]. assert (Eb : (b =? 10) = false) by (apply Z.eqb_neq; intros E; apply Hn; left; exact E).
rewrite Eb. pose proof (IH (fun H => Hn (or_intror H))) as IH'.
destruct (break_nl r) as [l q] eqn:Er. try rewrite Er in IH'. cbn in IH' |- *. rewrite IH'. reflexivity.
Qed.
Lemma a5h_map_skipn : forall {A C : Type} (f : A -> C) n l, map f (skipn n l) = skipn n (map f l).
Proof. intros A C f n. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.
Lemma a5h_zs_skipn : forall (l : list Z) o, seg_spec.zs (seg_spec.zb l) = l ->
  map (fun b : byte => bv_unsigned b) (skipn o (seg_spec.zb l)) = skipn o l.
Proof. intros l o H. rewrite a5h_map_skipn. f_equal. exact H. Qed.
Lemma a5h_m16o : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. assert (Ha16 : a mod 16 = 0).
{ apply Z.mod_divide in Ha; [|lia]. destruct Ha as [k Hk]. rewrite Hk. replace (k * 32) with ((2 * k) * 16) by lia.
  apply Z_mod_mult. }
rewrite Zminus_mod, Ha16, Hb. reflexivity.
Qed.
Lemma a5h_set_fs_id : forall s, s = set_fs (st_fs s) s.
Proof. intros s. destruct s. reflexivity. Qed.
(* a register named by a bv literal and by Z_to_bv 5 k (pf_a2.v pa2_bvr, both ways) *)
Lemma a5h_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma a5h_bvr2 : forall (rr : bvmap 5 word) (r : bv 5) k v, getr rr r = v -> bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v.
Proof. intros rr r k v H Hr. subst k. rewrite Z_to_bv_bv_unsigned. exact H. Qed.
Lemma a5h_spZ : forall (rX : bvmap 5 word) x, getr rX (Z_to_bv 5 2) = w64 x -> 0 <= x < 2 ^ 64 -> spZ rX = x.
Proof.
intros rX x H Hx. unfold spZ. match goal with |- context [getr rX ?r] => rewrite (a5h_bvr rX r 2 _ eq_refl H) end.
unfold w64. apply unsigned_lit_small. exact Hx.
Qed.
(* the alu terms of the runs over known values (trim_s.v tr_add_lit) *)
Lemma a5h_add : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b Ha Hb. apply bv_eq. rewrite alu64_unsigned, !Z_to_bv_unsigned. cbn [zalu_raw].
rewrite (bv_wrap_small 64 a) by (unfold bv_modulus; cbn; lia).
rewrite (bv_wrap_small 64 b) by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.
(* the executor writes `sub` as a + b * (-1) *)
Lemma a5h_subm : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  alu64 ALU_ADD (Z_to_bv 64 a) (mul_div M_MUL (Z_to_bv 64 b) (Z_to_bv 64 (-1))) = Z_to_bv 64 (a - b).
Proof.
intros a b Ha Hb. apply bv_eq. rewrite alu64_unsigned, mul_div_unsigned, !Z_to_bv_unsigned. cbn [zalu_raw zmd_raw].
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small a), (Z.mod_small b) by lia.
rewrite Zplus_mod_idemp_r.
change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
replace (a + b * (2 ^ 64 - 1)) with ((a - b) + b * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. reflexivity.
Qed.
(* a branch over two known values *)
Lemma a5h_br_eq : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_EQ (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. Qed.
Lemma a5h_br_ne : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_NE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x =? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. Qed.

(* the token executor's shadow base: s6 (no inline check runs in these pieces) *)
Definition a5h_Bx : sv := SOff 22 0.

Ltac a5h_in := unfold a5_FI, PF_RL; cbn [In app]; repeat first [left; reflexivity | right].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the fresh seed: every register its own atom, no region (trim_s.v's ta_ss) *)
Lemma a5h_seed : forall pc (rX : bvmap 5 word) (W : world SEGS) memc,
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros pc rX W memc. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
  [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | split; [exact I | split; exact I]].
Qed.
(* the reader reads an address modulo 2 ^ 64 *)
Lemma a5h_view_mod : forall (H : word -> bool) mem a, aview SEGS H mem a = aview SEGS H mem (a mod 2 ^ 64).
Proof.
intros H mem a. unfold aview, mbyte. replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod.
reflexivity.
Qed.

(* strchr's answer at p = t + o is a5_nl v o (the plain proof's bridge_strchr + L_break_nl) *)
Lemma a5h_nl_reg : forall (v : pfv) o (regs : bvmap 5 word), (o < length (p_s v))%nat ->
  ((getr regs 10 = w64 0 /\ ~ In 10 (map (fun b : byte => bv_unsigned b) (skipn o (seg_spec.zb (p_s v))))) \/
   (exists j, RtSeg.first_at (map (fun b : byte => bv_unsigned b) (skipn o (seg_spec.zb (p_s v)))) 10 j /\
      getr regs 10 = w64 (p_t v + Z.of_nat o + Z.of_nat j))) ->
  map (fun b : byte => bv_unsigned b) (skipn o (seg_spec.zb (p_s v))) = skipn o (p_s v) ->
  getr regs (Z_to_bv 5 10) = w64 (a5_nl v o).
Proof.
intros v o regs Ho H HZ. rewrite HZ in H.
unfold a5_nl, a5_len, pf_line.
destruct H as [(H0 & Hn) | (j & Hj & Hr)].
- rewrite (a5h_break_none _ Hn), length_skipn.
  replace ((o + (length (p_s v) - o) <? length (p_s v))%nat) with false by (symmetry; apply Nat.ltb_ge; lia).
  eapply a5h_bvr2; [exact H0 | reflexivity].
- destruct (a5h_break_first _ _ Hj) as (Ej & Hjl). rewrite length_skipn in Hjl. rewrite <- Ej.
  replace ((o + j <? length (p_s v))%nat) with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite Nat2Z.inj_add, Z.add_assoc. eapply a5h_bvr2; [exact Hr | reflexivity].
Qed.
Lemma a5h_nl1 : forall (v : pfv) o, a5_nl v o <> 0 ->
  (o + a5_len v o < length (p_s v))%nat /\ a5_nl v o = p_t v + Z.of_nat (o + a5_len v o).
Proof.
intros v o H. unfold a5_nl in *. destruct (o + a5_len v o <? length (p_s v))%nat eqn:E;
  [|exfalso; apply H; reflexivity].
split; [apply Nat.ltb_lt; exact E | reflexivity].
Qed.
Lemma a5h_nl0 : forall (v : pfv) o, a5_nl v o = 0 -> 0 < p_t v -> (o < length (p_s v))%nat ->
  (o + a5_len v o = length (p_s v))%nat.
Proof.
intros v o H Ht Ho. unfold a5_nl in H. destruct (o + a5_len v o <? length (p_s v))%nat eqn:E;
  [change (p_t v + Z.of_nat (o + a5_len v o) = 0) in H; lia|].
apply Nat.ltb_ge in E. destruct (L_next_holds (p_s v) o Ho) as (_ & _ & Hle & Heq).
unfold a5_len in E. rewrite Heq in Hle.
replace ((o + length (pf_line (p_s v) o) <? length (p_s v))%nat) with false in Hle
  by (symmetry; apply Nat.ltb_ge; exact E).
unfold a5_len. lia.
Qed.
Lemma a5h_next : forall (v : pfv) o, (o < length (p_s v))%nat ->
  pf_next (p_s v) o = (o + a5_len v o + (if (o + a5_len v o <? length (p_s v))%nat then 1 else 0))%nat.
Proof. intros v o Ho. destruct (L_next_holds (p_s v) o Ho) as (_ & _ & _ & Heq). exact Heq. Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the interceptor owner's row 6 at the listing's strchr trampoline (image A 0x43a28) *)
Hypothesis ASTRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strchr).
(* the interceptor owner's row 16 at the listing's strlen trampoline (image A 0x43a0c) *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
(* the listing's runtime record (SegPaLib.v PALib): aj_art_at needs its errno cell, pal_env *)
Hypothesis TL : PALib B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Ltac a5h_awr := lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  apply awr_ok_nil.
(* a register the run left as its own atom, read from the seed's list R (pf_a2.v pa2_atom) *)
Ltac a5h_atom HS EE rX R :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    let H := fresh "Hr" in prreg HS (Z_to_bv 5 k) H; rewrite H; clear H;
    transitivity (getr rX (Z_to_bv 5 k)); [apply EE; reflexivity | apply (a5_rg_get rX _ k _ R); a5h_in] end.
(* the same after a call that preserves the callee-saved registers *)
Ltac a5h_cs HP HS EE rX R :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    rewrite (HP k ltac:(unfold acallee_saved; lia)); a5h_atom HS EE rX R end.
(* a register's term after the run *)
Ltac a5h_get HS :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    let H := fresh "Hv" in prreg HS (Z_to_bv 5 k) H; rewrite H; clear H end.

(* the text's block: the text lies in the application range, below alloc_ceiling *)
Lemma a5h_tpos : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  4096 <= p_t v /\ p_t v + Z.of_nat (length (p_s v)) + 1 <= alloc_ceiling.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc HB.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & _).
pose proof (a5_text B _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & (b & m & Hb & Hb1 & Hb2) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hk).
pose proof (req_size_pos m (proj1 Hk)) as [_ Hreq]. unfold pf_len in Hb2. lia.
Qed.

(* the premises of strchr / strlen at p = t + o (window stk), from a cut state: the text's rest as astr_at
   (sa_strz_bytes, astr_atR_skipn), aread_ok inside its heap block (aread_ok_of_block), the band room past it
   (the block is in the application range), the tail after the NUL (sa_str), the read-only view (a5_rom) *)
Lemma a5h_str_pre : forall v pos lyc Sc Wc rX memc mdc sc o stk,
  pf_base B v pos lyc Sc Wc rX memc mdc sc -> (o < length (p_s v))%nat -> 0 <= stk <= 2 * ESTACK ->
  0 < p_t v + Z.of_nat o /\
  astr_at SEGS Wc memc (p_t v + Z.of_nat o) (skipn o (seg_spec.zb (p_s v))) /\
  aread_ok SEGS stk Wc rX memc (p_t v + Z.of_nat o) (astr_len (skipn o (seg_spec.zb (p_s v))) + 1) /\
  amem_range (p_t v + Z.of_nat o) (astr_len (skipn o (seg_spec.zb (p_s v))) + 8) /\
  atail_vis SEGS Wc memc (p_t v + Z.of_nat o + astr_len (skipn o (seg_spec.zb (p_s v)))) /\
  rt_rom_view SEGS B Wc memc /\
  astr_len (skipn o (seg_spec.zb (p_s v))) = Z.of_nat (length (p_s v)) - Z.of_nat o /\
  map (fun b : byte => bv_unsigned b) (skipn o (seg_spec.zb (p_s v))) = skipn o (p_s v).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc o stk HB Ho Hstk.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
pose proof (a5_text B _ _ _ _ _ _ _ _ _ HB) as (NZ & HL65 & HSTR & HADDR & HHT & HHC).
pose proof (a5_rom B _ _ _ _ _ _ _ _ _ HB) as HROM.
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
destruct HHT as (b & m & Hb & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (Hp16 & Hp4096 & Hpceil & Happ & Hpres & _ & Hk).
pose proof (req_size_pos m (proj1 Hk)) as [_ Hreq].
unfold pf_len in Hb2.
assert (Hsp : spZ rX = pf_s1 v).
{ apply a5h_spZ; [apply (a5_rg_get rX _ 2 _ HFI); a5h_in | lia]. }
pose proof HSTR as (HSZ & HTAIL).
destruct (sa_strz_bytes SEGS (w_H Wc) memc (p_t v) (p_s v) HSZ) as (HBY & HNZ & HZS).
assert (HLS : astr_len (skipn o (seg_spec.zb (p_s v))) = Z.of_nat (length (p_s v)) - Z.of_nat o).
{ unfold astr_len, seg_spec.zb. rewrite length_skipn, length_map. lia. }
split; [lia|].
split.
{ apply astr_atR_view.
  assert (HA : astr_atR (rdW Wc memc) (p_t v) (seg_spec.zb (p_s v))) by exact (conj HBY HNZ).
  apply (astr_atR_skipn _ _ _ o HA). unfold seg_spec.zb. rewrite length_map. lia. }
split.
{ rewrite HLS.
  apply (aread_ok_of_block SEGS B LAWS stk lyc Sc Wc rX memc mdc b m (p_t v + Z.of_nat o)
    (Z.of_nat (length (p_s v)) - Z.of_nat o + 1) HAR Hb); [lia | lia | lia | rewrite Hsp; lia]. }
split.
{ rewrite HLS. unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd. lia. }
split.
{ rewrite HLS.
  replace (p_t v + Z.of_nat o + (Z.of_nat (length (p_s v)) - Z.of_nat o)) with (p_t v + Z.of_nat (length (p_s v)))
    by lia.
  exact HTAIL. }
split; [exact HROM|]. split; [exact HLS|].
apply a5h_zs_skipn. exact HZS.
Qed.

(* the cut state after a run that writes nothing (stk = 0) or after an interceptor call whose window is
   [s1 - stk, s1): pf_base and the line context at the new memory, by pf_a5_k.v's a5_move0 and a5_keep_ln *)
Lemma a5h_step : forall v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc' stk,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  0 <= stk <= 2 * ESTACK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - stk <= a < pf_s1 v) -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_rg rX' (a5_FI B v) ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' sc /\
  (forall n cf cur nm o ln d, a5_ln n v pos (rdW Wc memc) cf cur nm o ln d ->
     a5_ln n v pos (rdW Wc memc') cf cur nm o ln d).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc' stk HB HJ' Hstk HK HRG.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
pose proof (a5_text B _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & HC).
pose proof HB as (_ & _ & _ & _ & HF).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
rewrite SPF in G1.
assert (HKW : forall a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos true true a -> rdW Wc memc' a = rdW Wc memc a).
{ intros a Ha Hn. apply HK; [exact Ha|]. intros Hw. apply Hn. unfold a5_Wrx. left. rewrite SPF. lia. }
assert (HV : forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None).
{ intros a Hv. rewrite a5h_view_mod in Hv. rewrite a5h_view_mod.
  assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  destruct (Z_lt_le_dec (a mod 2 ^ 64) (pf_s1 v - stk)) as [Hlo|Hlo]; [rewrite HK by lia; exact Hv|].
  destruct (Z_lt_le_dec (a mod 2 ^ 64) (pf_s1 v)) as [Hhi|Hhi]; [|rewrite HK by lia; exact Hv].
  apply (aview_some_of_apresent SEGS).
  pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  apply Hpres. rewrite SPF. lia. }
assert (HF' : pf_fsh (rdW Wc memc') (pf_SH v pos) sc).
{ intros i Hi. rewrite HK; [exact (HF i Hi) | |].
  - unfold kLowMemEnd, kHighShadowEnd in *. lia.
  - unfold kHighShadowEnd in G12. intros Hw. lia. }
split.
- apply (a5_move0 B v pos lyc Sc Wc rX memc mdc sc Sc Wc rX' memc' mdc' sc HB HJ');
    [exists (st_fs Sc); apply a5h_set_fs_id | apply Permutation_refl | exact HKW | exact HV | exact HRG | exact HF'].
- intros n cf cur nm o ln d HL. eapply (a5_keep_ln B v pos lyc Sc Wc memc mdc Wc memc'); eassumption.
Qed.

(* ======================= HEAD 0x87ddc -> R1 0x87de8 (strchr) ======================= *)
Lemma a5_head_ok : forall n, H_R1 B n -> H_HEAD B n.
Proof.
intros n HR1 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
destruct HI as (HB & HL1 & Ho & Hn & HST & HRG).
assert (HLN : a5_ln n v pos (rdW Wc memc) cf cur nm o ln d) by exact (conj HL1 (conj Ho (conj Hn HST))).
clear HL1 Hn HST.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (_ & (HJ & _) & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
destruct (a5h_tpos v pos lyc Sc Wc rX memc mdc PF_SC_HEAD HB) as (Ht0 & Ht47).
assert (RA : pf_rg rX (a5_FI B v ++ PF_RL v pos ++
    [(25, p_t v + Z.of_nat o); (26, ln); (20, pf_cur_ptr (p_c v) cur)])) by (apply a5_rg_app; split; assumption).
assert (Hal16 : (pf_s1 v - pf_sp0 v) mod 16 = 0) by exact (a5h_m16o _ _ G5 G3).
(* the seed *)
pose proof (a5h_seed PF_HEAD rX Wc memc) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX []))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg rX [])) k = getr rX r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
revert HS HEI EE. generalize (Eimg (Ereg rX [])) as E. intros E HS HEI EE.
assert (E2 : ew E 2 = Z_to_bv 64 (pf_s1 v))
  by (rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl); apply (a5_rg_get rX _ 2 _ RA); a5h_in).
assert (E3 : ew E 3 = Z_to_bv 64 (as_gp B))
  by (rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl); apply (a5_rg_get rX _ 3 _ RA); a5h_in).
assert (E4 : ew E 4 = Z_to_bv 64 (as_tp B))
  by (rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl); apply (a5_rg_get rX _ 4 _ RA); a5h_in).
assert (E25 : ew E 25 = Z_to_bv 64 (p_t v + Z.of_nat o))
  by (rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl); apply (a5_rg_get rX _ 25 _ RA); a5h_in).
assert (SHOK : sh_ok SEGS a5h_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at, w64.
(* 0x87ddc addi a1,zero,0xa; 0x87de0 mv a0,s9; 0x87de4 jal the strchr trampoline *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ a5h_awr. }
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
clear HFr HG HF.
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
rewrite E2 in Q2. rewrite E3 in Q3. rewrite E4 in Q4. rewrite E25 in Q10.
assert (R1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + A5_R1)) by (rewrite R1; reflexivity).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite R1'; apply ret_ok_codeptr_v; [unfold A5_R1, AF_reac_segconf_parse_file; lia | reflexivity]).
assert (Hsp1 : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v))
  by (unfold spZ; rewrite Q2; rewrite unsigned_lit_small by lia; lia).
assert (RFI1 : pf_rg (ms_regs ms) (a5_FI B v)).
{ unfold pf_rg, a5_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; a5h_atom HS EE rX RA. }
destruct (a5h_step v pos lyc Sc Wc rX memc mdc PF_SC_HEAD (ms_regs ms) (ms_mem ms) mdv 0 HB HJ
  ltac:(rewrite HES; lia) ltac:(intros a Ha _; exact (KM1 a Ha)) RFI1) as (HB1 & HLN1).
destruct (a5h_str_pre v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv PF_SC_HEAD o (2 * ESTACK) HB1 Ho
  ltac:(rewrite HES; lia)) as (Hx0 & HSTR1 & HRD1 & HMR1 & HTV1 & HROM1 & HLS & HZS).
(* the call *)
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False)
    (SIG SS___interceptor_trampoline_strchr) Wc (ms_regs ms) (ms_mem ms) STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdv 0
    (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + A5_R1)) _ HJ Hsp1 Hal16 ltac:(lia) ltac:(rewrite HES; lia)
    ltac:(rewrite SPF, HES; lia) R1' (fun a (H : False) => False_ind _ H)).
  apply (ASTRCHR fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (p_t v + Z.of_nat o) 10 (skipn o (seg_spec.zb (p_s v)))).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
      (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc (ms_mem ms) mdv 0 (ms_regs ms)
      (pf_s1 v - pf_sp0 v) HJ Hsp1 Hal16 ltac:(lia) ltac:(rewrite HES; lia) ltac:(rewrite SPF, HES; lia) HraT Q3 Q4).
  - rewrite Q10. reflexivity.
  - rewrite Q11. reflexivity.
  - lia.
  - exact Hx0.
  - exact HSTR1.
  - exact HRD1.
  - exact HMR1.
  - exact HTV1.
  - exact HROM1. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & HK2).
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A5_R1)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + A5_R1) regs2 mem2 md2).
destruct (a5h_step v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv PF_SC_HEAD regs2 mem2 md2 (2 * ESTACK) HB1 HJ2
  ltac:(rewrite HES; lia) ltac:(intros a Ha Hn'; apply HK2; [exact Ha | lia | cbv beta; tauto])
  (a5_rg_pres _ _ _ HP2 (a5_FI_cs B v) RFI1)) as (HB2 & HLN2).
apply (HR1 v pos lyc Sc Wc regs2 mem2 md2 cf cur nm o ln d).
split; [exact HB2|]. split; [exact (HLN2 _ _ _ _ _ _ _ (HLN1 _ _ _ _ _ _ _ HLN))|].
apply a5_rg_app. split.
- unfold pf_rg, PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; a5h_cs HP2 HS EE rX RA.
- repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
  1-3: a5h_cs HP2 HS EE rX RA.
  exact (a5h_nl_reg v o regs2 Ho Ha02 HZS).
Qed.

(* ======================= R2 0x87e08 -> Q3 0x87e14 ======================= *)
Lemma a5_r2_ok : forall n, H_Q3 B n -> H_R2 B n.
Proof.
intros n HQ3 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
destruct HI as (HB & HLN & Hend & HRG).
pose proof HLN as (_ & Ho & _ & _).
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (_ & (HJ & _) & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
destruct (a5h_tpos v pos lyc Sc Wc rX memc mdc PF_SC_HEAD HB) as (Ht0 & Ht47).
assert (RA : pf_rg rX (a5_FI B v ++ PF_RL v pos ++
    [(25, p_t v + Z.of_nat o); (26, ln); (20, pf_cur_ptr (p_c v) cur); (21, 0); (10, Z.of_nat (a5_len v o))]))
  by (apply a5_rg_app; split; assumption).
pose proof (a5h_seed A5_R2 rX Wc memc) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX []))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg rX [])) k = getr rX r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
revert HS HEI EE. generalize (Eimg (Ereg rX [])) as E. intros E HS HEI EE.
assert (E10 : ew E 10 = Z_to_bv 64 (Z.of_nat (a5_len v o)))
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); apply (a5_rg_get rX _ 10 _ RA); a5h_in).
assert (E21 : ew E 21 = Z_to_bv 64 0)
  by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl); apply (a5_rg_get rX _ 21 _ RA); a5h_in).
assert (E25 : ew E 25 = Z_to_bv 64 (p_t v + Z.of_nat o))
  by (rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl); apply (a5_rg_get rX _ 25 _ RA); a5h_in).
assert (SHOK : sh_ok SEGS a5h_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at, w64.
(* 0x87e08 mv s7,a0; 0x87e0c bnez s5 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ a5h_awr. }
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
clear HFr HG HF.
lazymatch type of HS with context [restrict _ ?m] => rename m into msA end.
set (mdA := with_vm_backing _ _ _) in *; clearbody mdA.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* s5 <> 0: not this path (s5 = strchr's 0) *)
  exfalso. prreg_norm Hc. rewrite E21 in Hc. rewrite a5h_br_ne in Hc by lia. cbn in Hc. discriminate Hc.
- (* 0x87e10 add s5,s9,s7; Q3 *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan A5_Q3.
  { a5h_awr. }
  assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc (ms_mem msA) a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) (ms_mem msA) (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
  clear HFr HG HF.
  set (mdB := with_vm_backing _ _ _) in *; clearbody mdB.
  pmkst HS.
  assert (RFI : pf_rg (ms_regs ms) (a5_FI B v)).
  { unfold pf_rg, a5_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; a5h_atom HS EE rX RA. }
  destruct (a5h_step v pos lyc Sc Wc rX memc mdc PF_SC_HEAD (ms_regs ms) (ms_mem ms) mdB 0 HB HJ
    ltac:(rewrite HES; lia) ltac:(intros a Ha _; rewrite (KM2 a Ha); exact (KM1 a Ha)) RFI) as (HB2 & HLN2).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
    apply (HQ3 v pos lyc Sc Wc rg mm mdn cf cur nm o ln d) end.
  split; [exact HB2|]. split; [exact (HLN2 _ _ _ _ _ _ _ HLN)|].
  apply a5_rg_app. split.
  + unfold pf_rg, PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; a5h_atom HS EE rX RA.
  + repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    1-3: a5h_atom HS EE rX RA.
    * (* s5 = s9 + s7 = t + o + len = t + pf_next s o *)
      a5h_get HS. rewrite E25, E10. rewrite a5h_add by lia.
      rewrite (a5h_next v o Ho).
      replace ((o + a5_len v o <? length (p_s v))%nat) with false by (symmetry; apply Nat.ltb_ge; lia).
      unfold w64. f_equal. lia.
    * (* s7 = len *)
      a5h_get HS. rewrite E10. reflexivity.
Qed.

(* ======================= R1 0x87de8 -> Q3 0x87e14 or R2 0x87e08 (strlen) ======================= *)
Lemma a5_r1_ok : forall n, H_R2 B n -> H_Q3 B n -> H_R1 B n.
Proof.
intros n HR2 HQ3 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
destruct HI as (HB & HLN & HRG).
pose proof HLN as (_ & Ho & _ & _).
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (_ & (HJ & _) & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
destruct (a5h_tpos v pos lyc Sc Wc rX memc mdc PF_SC_HEAD HB) as (Ht0 & Ht47).
assert (Hnlr : 0 <= a5_nl v o < 2 ^ 64).
{ unfold a5_nl. destruct (o + a5_len v o <? length (p_s v))%nat eqn:E; cbv iota; [apply Nat.ltb_lt in E|]; lia. }
assert (RA : pf_rg rX (a5_FI B v ++ PF_RL v pos ++
    [(25, p_t v + Z.of_nat o); (26, ln); (20, pf_cur_ptr (p_c v) cur); (10, a5_nl v o)]))
  by (apply a5_rg_app; split; assumption).
assert (Hal16 : (pf_s1 v - pf_sp0 v) mod 16 = 0) by exact (a5h_m16o _ _ G5 G3).
pose proof (a5h_seed A5_R1 rX Wc memc) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX []))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg rX [])) k = getr rX r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
revert HS HEI EE. generalize (Eimg (Ereg rX [])) as E. intros E HS HEI EE.
assert (E2 : ew E 2 = Z_to_bv 64 (pf_s1 v))
  by (rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl); apply (a5_rg_get rX _ 2 _ RA); a5h_in).
assert (E3 : ew E 3 = Z_to_bv 64 (as_gp B))
  by (rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl); apply (a5_rg_get rX _ 3 _ RA); a5h_in).
assert (E4 : ew E 4 = Z_to_bv 64 (as_tp B))
  by (rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl); apply (a5_rg_get rX _ 4 _ RA); a5h_in).
assert (E10 : ew E 10 = Z_to_bv 64 (a5_nl v o))
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); apply (a5_rg_get rX _ 10 _ RA); a5h_in).
assert (E25 : ew E 25 = Z_to_bv 64 (p_t v + Z.of_nat o))
  by (rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl); apply (a5_rg_get rX _ 25 _ RA); a5h_in).
assert (SHOK : sh_ok SEGS a5h_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at, w64.
(* 0x87de8 mv s5,a0; 0x87dec beqz a0 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ a5h_awr. }
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
clear HFr HG HF.
lazymatch type of HS with context [restrict _ ?m] => rename m into msA end.
set (mdA := with_vm_backing _ _ _) in *; clearbody mdA.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* a0 = 0: the line ends the text; 0x87e00 mv a0,s9; 0x87e04 jal the strlen trampoline *)
  prreg_norm Hc. rewrite E10 in Hc. rewrite a5h_br_eq in Hc by lia. apply Z.eqb_eq in Hc. rename Hc into Hnl0.
  assert (Hend : (o + a5_len v o = length (p_s v))%nat) by (apply (a5h_nl0 v o Hnl0); lia).
  paj_run_tok RUN HS HJ SHOK Bspan.
  { a5h_awr. }
  assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc (ms_mem msA) a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) (ms_mem msA) (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
  clear HFr HG HF.
  set (mdB := with_vm_backing _ _ _) in *; clearbody mdB.
  pmkst HS.
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10.
  rewrite E2 in Q2. rewrite E3 in Q3. rewrite E4 in Q4. rewrite E25 in Q10.
  assert (R1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + A5_R2)) by (rewrite R1; reflexivity).
  assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1))
    by (rewrite R1'; apply ret_ok_codeptr_v; [unfold A5_R2, AF_reac_segconf_parse_file; lia | reflexivity]).
  assert (Hsp1 : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v))
    by (unfold spZ; rewrite Q2; rewrite unsigned_lit_small by lia; lia).
  assert (RFI1 : pf_rg (ms_regs ms) (a5_FI B v)).
  { unfold pf_rg, a5_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; a5h_atom HS EE rX RA. }
  destruct (a5h_step v pos lyc Sc Wc rX memc mdc PF_SC_HEAD (ms_regs ms) (ms_mem ms) mdB 0 HB HJ
    ltac:(rewrite HES; lia) ltac:(intros a Ha _; rewrite (KM2 a Ha); exact (KM1 a Ha)) RFI1) as (HB1 & HLN1).
  destruct (a5h_str_pre v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdB PF_SC_HEAD o ESTACK HB1 Ho
    ltac:(rewrite HES; lia)) as (Hx0 & HSTR1 & HRD1 & HMR1 & HTV1 & HROM1 & HLS & HZS).
  eapply SRr_bind.
  { eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low ESTACK (fun _ => False)
      (SIG SS___interceptor_trampoline_strlen) Wc (ms_regs ms) (ms_mem ms) STK_reac_segconf_parse_file (pf_sp0 v)
      (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdB 0
      (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + A5_R2)) _ HJ Hsp1 Hal16 ltac:(lia) ltac:(rewrite HES; lia)
      ltac:(rewrite SPF, HES; lia) R1' (fun a (H : False) => False_ind _ H)).
    apply (ASTRLEN fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdB (p_t v + Z.of_nat o) (skipn o (seg_spec.zb (p_s v)))).
    - exact (ecall_pre_stk_at SEGS B ESTACK STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
        (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc (ms_mem ms) mdB 0 (ms_regs ms)
        (pf_s1 v - pf_sp0 v) HJ Hsp1 Hal16 ltac:(lia) ltac:(lia) ltac:(rewrite SPF, HES; lia) HraT Q3 Q4).
    - rewrite Q10. reflexivity.
    - exact Hx0.
    - exact HSTR1.
    - exact HRD1.
    - exact HTV1.
    - exact HROM1. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & HK2).
  change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A5_R2)) mem2 (seg_rom SEGS)) md2)
    with (cfg_at SEGS (BASE + A5_R2) regs2 mem2 md2).
  destruct (a5h_step v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdB PF_SC_HEAD regs2 mem2 md2 ESTACK HB1 HJ2
    ltac:(rewrite HES; lia) ltac:(intros a Ha Hn'; apply HK2; [exact Ha | lia | cbv beta; tauto])
    (a5_rg_pres _ _ _ HP2 (a5_FI_cs B v) RFI1)) as (HB2 & HLN2).
  apply (HR2 v pos lyc Sc Wc regs2 mem2 md2 cf cur nm o ln d).
  split; [exact HB2|]. split; [exact (HLN2 _ _ _ _ _ _ _ (HLN1 _ _ _ _ _ _ _ HLN))|]. split; [exact Hend|].
  apply a5_rg_app. split.
  + unfold pf_rg, PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; a5h_cs HP2 HS EE rX RA.
  + repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    1-3: a5h_cs HP2 HS EE rX RA.
    * (* s5 = strchr's 0 *)
      rewrite (HP2 21 ltac:(unfold acallee_saved; lia)). a5h_get HS. rewrite E10, Hnl0. reflexivity.
    * (* a0 = strlen(p) = len *)
      rewrite HLS in Ha02.
      replace (Z.of_nat (a5_len v o)) with (Z.of_nat (length (p_s v)) - Z.of_nat o) by lia.
      eapply a5h_bvr2; [exact Ha02 | reflexivity].
- (* a0 <> 0: a '\n' ends the line; 0x87df0 sub s7,s5,s9; beqz s5; addi s5,s5,1; j Q3 *)
  prreg_norm Hc. rewrite E10 in Hc. rewrite a5h_br_eq in Hc by lia. apply Z.eqb_neq in Hc.
  destruct (a5h_nl1 v o Hc) as (Hlt & Hnlv). clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan A5_Q3.
  { a5h_awr. }
  assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc (ms_mem msA) a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) (ms_mem msA) (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
  clear HFr HG HF.
  set (mdB := with_vm_backing _ _ _) in *; clearbody mdB.
  pmkst HS.
  assert (RFI : pf_rg (ms_regs ms) (a5_FI B v)).
  { unfold pf_rg, a5_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; a5h_atom HS EE rX RA. }
  destruct (a5h_step v pos lyc Sc Wc rX memc mdc PF_SC_HEAD (ms_regs ms) (ms_mem ms) mdB 0 HB HJ
    ltac:(rewrite HES; lia) ltac:(intros a Ha _; rewrite (KM2 a Ha); exact (KM1 a Ha)) RFI) as (HB2 & HLN2).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
    apply (HQ3 v pos lyc Sc Wc rg mm mdn cf cur nm o ln d) end.
  split; [exact HB2|]. split; [exact (HLN2 _ _ _ _ _ _ _ HLN)|].
  apply a5_rg_app. split.
  + unfold pf_rg, PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; a5h_atom HS EE rX RA.
  + repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    1-3: a5h_atom HS EE rX RA.
    * (* s5 = nl + 1 = t + pf_next s o *)
      a5h_get HS. rewrite E10, Hnlv. rewrite unsigned_lit_small by lia.
      rewrite (a5h_next v o Ho).
      replace ((o + a5_len v o <? length (p_s v))%nat) with true by (symmetry; apply Nat.ltb_lt; exact Hlt).
      unfold w64. f_equal. lia.
    * (* s7 = nl - p = len *)
      a5h_get HS. rewrite E10, E25, Hnlv. rewrite a5h_subm by lia.
      unfold w64. f_equal. lia.
Qed.
End e.
End f.
End d.
