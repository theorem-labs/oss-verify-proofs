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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 472 of its 518 lines of code are new or changed and 407 lines of the source are left out. *)
(* reac_declared_vlan_split on fuzz_segconf image A: the points K3 (0x89c6c, after the strtol wrapper) and K4
   (0x89cd0, after the strlen wrapper).
   K3: `mv s5,a0`, a0 = v - 4095, a1 = -4094, `bgeu` 0x89c80 (vs_range_test). Out of range: `li a0,0` and on to the
   epilogue KR with vlan_split = None (vs_none_range). In range: `sub s4,s4,s2` (s4 = di), the two plen tests 0x89cbc,
   0x89cc4 (not taken: di < |s| <= 15), `mv a0,s2`, `jal` the strlen wrapper (RtString.astrlen_realizes, ESTACK
   window) on the segment, then K4 with a0 = |s|.
   K4: a0 = |s| - 16, a1 = -17, `bltu` 0x89cd8 (not taken: vs_len_test), a0 = parent, a1 = segment, a2 = di, `jal`
   the checked memcpy (aintrin_realizes OCpy through PaCall.aj_intrin_atS), then K5 with parent[0 .. di) = s[0 .. di)
   and only those bytes written outside the stack window. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_k reac_declared_vlan_split_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_r reac_declared_vlan_split_h.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* strtol10 of a run of digits is below 10 ^ (its length) *)
Lemma vsb_fold_lt : forall l v, 0 <= v -> forallb SegModel.isdigit l = true ->
  fold_left SegModel.dstep l v < (v + 1) * 10 ^ Z.of_nat (length l).
Proof.
induction l as [|d l IH]; intros v Hv H; cbn [fold_left length forallb] in *.
- change (10 ^ Z.of_nat 0) with 1. lia.
- apply andb_true_iff in H as [Hd Hl]. apply SegModel.isdigit_range in Hd.
  assert (Hs : 0 <= SegModel.dstep v d <= 10 * v + 9) by (unfold SegModel.dstep; lia).
  specialize (IH (SegModel.dstep v d) ltac:(lia) Hl).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  set (P := 10 ^ Z.of_nat (length l)) in *.
  assert (HP : 0 <= P) by (subst P; apply Z.pow_nonneg; lia).
  nia.
Qed.
Lemma vsb_strtol_lt : forall l, forallb SegModel.isdigit l = true -> (length l <= 15)%nat ->
  0 <= SegModel.strtol10 l < 10 ^ 15.
Proof.
intros l Hd Hl. rewrite SegModel.strtol10_fold. split.
- apply (SegModel.fold_dstep_ge l 0); [lia | exact Hd].
- pose proof (vsb_fold_lt l 0 ltac:(lia) Hd) as H.
  assert (10 ^ Z.of_nat (length l) <= 10 ^ 15) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
(* the shadow hull of a sub-range lies inside the hull of the range *)
Lemma vsb_hull_sub : forall rd x n x' n', shadow_hull_vis rd x n -> 0 <= x -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
  shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H0 H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (SHADOW_OFF + x / 8) (SHADOW_OFF + x' / 8) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_le_mono (SHADOW_OFF + (x' + n' - 1) / 8) (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia) ltac:(lia)) as D4.
lia.
Qed.

(* the value the code computes for s4 = s4 - s2 (and for s4 + c) from s4 = segment + d and s2 = segment *)
Lemma vsb_U_s4 : forall E n18 n20 seg d z,
  ew E n18 = Z_to_bv 64 seg -> ew E n20 = Z_to_bv 64 (seg + d) ->
  0 <= seg -> 0 <= d -> seg + d < 2 ^ 64 -> zcanon z = 2 ^ 64 - 1 ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff n18 0) (SLit z)) (SOff n20 0)) = d.
Proof.
intros E n18 n20 seg d z H18 H20 Hs Hd Hsd Hz.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, Hz.
rewrite (U_atom E n18 seg H18) by lia. rewrite (U_atom E n20 (seg + d) H20) by lia.
unfold zcanon, M64.
rewrite (Z.add_mod_idemp_l (seg * (2 ^ 64 - 1)) (seg + d) (2 ^ 64)) by lia.
replace (seg * (2 ^ 64 - 1) + (seg + d)) with (d + seg * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma vsb_U_a1 : forall E n18 n20 seg d z c,
  ew E n18 = Z_to_bv 64 seg -> ew E n20 = Z_to_bv 64 (seg + d) ->
  0 <= seg -> 0 <= d -> seg + d < 2 ^ 64 -> 0 <= c -> d + c < 2 ^ 64 -> zcanon z = 2 ^ 64 - 1 ->
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff n18 0) (SLit z)) (SLit c)) (SOff n20 0)) = d + c.
Proof.
intros E n18 n20 seg d z c H18 H20 Hs Hd Hsd Hc Hdc Hz.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite !U_SLit, Hz.
rewrite (U_atom E n18 seg H18) by lia. rewrite (U_atom E n20 (seg + d) H20) by lia.
unfold zcanon, M64. rewrite (Z.mod_small c (2 ^ 64)) by lia.
rewrite (Z.add_mod_idemp_l ((seg * (2 ^ 64 - 1)) mod 2 ^ 64 + c) (seg + d) (2 ^ 64)) by lia.
rewrite <- Z.add_assoc.
rewrite (Z.add_mod_idemp_l (seg * (2 ^ 64 - 1)) (c + (seg + d)) (2 ^ 64)) by lia.
replace (seg * (2 ^ 64 - 1) + (c + (seg + d))) with (d + c + seg * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a register a run to a call left as an atom *)
Lemma vsb_reg_c : forall E ss (ms : machine_state) (H : word -> bool) n (r : bv 5) (w : word),
  st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w -> getr (ms_regs ms) r = w.
Proof using.
intros E ss ms H n r w HS Hr Hn. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* the body's registers carried over a stretch that keeps sp, gp, tp, s0 .. s3, s6 .. s11 *)
Lemma vsb_regs_of : forall e (regs0 regs1 : bvmap 5 word), vs_regs e regs0 ->
  (forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ 22 <= r <= 27 ->
   getr regs1 (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)) ->
  vs_regs e regs1.
Proof using.
intros e regs0 regs1 (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27) HK.
split; [unfold spZ; change (getr regs1 2) with (getr regs1 (Z_to_bv 5 2)); rewrite (HK 2 ltac:(lia)); exact Hsp|].
split; [change (getr regs1 3) with (getr regs1 (Z_to_bv 5 3)); rewrite (HK 3 ltac:(lia)); exact G3|].
split; [change (getr regs1 4) with (getr regs1 (Z_to_bv 5 4)); rewrite (HK 4 ltac:(lia)); exact G4|].
split; [change (getr regs1 8) with (getr regs1 (Z_to_bv 5 8)); rewrite (HK 8 ltac:(lia)); exact G8|].
split; [change (getr regs1 9) with (getr regs1 (Z_to_bv 5 9)); rewrite (HK 9 ltac:(lia)); exact G9|].
split; [change (getr regs1 18) with (getr regs1 (Z_to_bv 5 18)); rewrite (HK 18 ltac:(lia)); exact G18|].
split; [change (getr regs1 19) with (getr regs1 (Z_to_bv 5 19)); rewrite (HK 19 ltac:(lia)); exact G19|].
split; [change (getr regs1 22) with (getr regs1 (Z_to_bv 5 22)); rewrite (HK 22 ltac:(lia)); exact G22|].
intros r Hr. rewrite (HK r ltac:(lia)). exact (G27 r Hr).
Qed.

(* every byte a run over the frame alone reaches reads as before it *)
Ltac vsb_kept Hfr :=
  apply vs_view_ext; intros ?a ?Ha;
  exact (kept_of_frame _ _ _ _ _ (fun _ => False) Hfr
    ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn in Hrr; lia|]); destruct Hin)
    _ ltac:(eassumption) (fun x => x)).

Section e.
Variable B : asyms.
Variables gotw guard : Z.
Hypothesis TL : PALib B.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

(* where the segment lies: below the allocator's ceiling, so below every stack window *)
Lemma vsb_loc_facts : forall ly S W mem md q n, AR SEGS B ly S W mem md -> 0 < n -> sa_loc SEGS B ly S q n ->
  4096 <= q /\ q + n <= alloc_ceiling.
Proof using.
intros ly S W mem md q n HAR Hn HL. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HL as [(b & m & Hin & H1 & H2) | [(cid & pos & Hin & Hc & H1 & H2) | HI]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & B0 & B1 & _ & _ & _ & Bm).
  pose proof (req_size_pos m ltac:(lia)) as [Q1 Q2]. lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (F0 & F1 & F2). lia.
- destruct (HI q ltac:(lia)) as (Hq & _). destruct (HI (q + n - 1) ltac:(lia)) as (Hq' & _).
  pose proof (pa_img_range q Hq). pose proof (pa_img_range _ Hq'). unfold kImgEnd in *. lia.
Qed.

(* PaArt.aj_art_at, with art_post's presence conjunct kept *)
Lemma vsb_art_at : forall stk (Eb : Z -> Prop) pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw
  (Qr : bvmap 5 word -> (word -> option byte) -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= stk -> stk - o <= STK ->
  getr regsT 1 = raw ->
  (forall a, Eb a -> as_errno B <= a < as_errno B + 4) ->
  SRr SEGS W (cfg_at SEGS pc regsT memT mdc) (art_post SEGS B stk lyc Sc W regsT memT mdc Eb Qr) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
   c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
   ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
   aregs_preserved regsT regs2 /\ Qr regs2 mem2 /\
   (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> ~ Eb a ->
    aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
   (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof using TL.
intros stk Eb pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw Qr HJ Hsp Hal Hneg Hstk Hbud Hraw HEb HC.
eapply SRr_mono.
- apply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) stk Eb pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
    (fun r m => Qr r m /\ (forall a, apresent (w_H W) memT a -> apresent (w_H W) m a)) HJ Hsp Hal Hneg Hstk Hbud Hraw HEb).
  eapply SRr_mono; [exact HC|].
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & HQ & Hfr & Hpres2 & Hscr).
  split; [reflexivity|]. exists regs2, mem2, md2.
  exact (conj eq_refl (conj HAR2 (conj HP (conj Hsame (conj (conj HQ Hpres2) (conj Hfr (conj Hpres2 Hscr))))))).
- intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & (HQ & Hpres2) & Hfr).
  split; [reflexivity|]. exists regs2, mem2, md2.
  exact (conj eq_refl (conj HJ2 (conj HP (conj HQ (conj Hfr Hpres2))))).
Qed.

Lemma vs_K3 : vs_KR_stmt B gotw guard -> vs_K4_stmt B gotw guard -> vs_K3_stmt B gotw guard.
Proof using ASTRLEN TL.
intros HKR HK4. unfold vs_K3_stmt. intros e regs' mem' md' di HE HC Hdi Hdi0 Hne Hdig R10 R20.
pose proof HE as (HPRE & HROD & H10 & B10 & H11 & B11 & H12 & H13 & B13 & HSP & Hnev).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HC as (HJ & HR & HSL & HK & HPR).
pose proof HR as (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27).
pose proof HSP as (Hs0 & Hstr & Hlen & Hsadd & Hamr & Hsloc & Hp0 & Hcap & Hpdst & Hpadd & Hpdisj & Hv0 & Hv2 & Hvdst & Hvadd & Hvdisj & Hssp).
assert (HVS : STK_reac_declared_vlan_split = 12352) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (@pa_B_ok _ _ PI) as HBASE. pose proof (pa_base_lo (L := seg_listing)) as HBLO.
unfold e_sp in *.
assert (Hnul : SegModel.nulfree (e_s e)) by exact (proj2 (proj1 Hstr)).
pose proof (vs_di_lt _ _ Hnul Hdi) as Hdil.
assert (Htl : (length (vs_tail e di) <= 15)%nat) by (unfold vs_tail; rewrite length_skipn; lia).
pose proof (vsb_strtol_lt _ Hdig Htl) as Hvb.
set (v := SegModel.strtol10 (vs_tail e di)) in *.
destruct (vsb_loc_facts _ _ _ _ _ (e_seg e) (Z.of_nat (length (e_s e)) + 1) HAR ltac:(lia) Hsloc) as (Sg0 & Sg1).
set (E := Eimg (Ereg regs' (vs_xs (e_regs e) ++ []))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EV : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs' r)
  by (intros n r Hn; subst E; apply vs_EE; exact Hn).
assert (HS : st_ok_pi SEGS VAL E (vs_ssK VS_K3 [])
  (restrict (w_H (e_W e)) (mkst regs' (Z_to_bv 64 (BASE + VS_K3)) mem' (seg_rom SEGS)))).
{ apply vs_seedK; [replace (spZ regs' + 64) with (spZ (e_regs e)) by lia; exact HSL | lia | | exact G22 | exact I].
  rewrite Hsp. replace (spZ (e_regs e) - 64) with (spZ (e_regs e) + (-4) * 16) by lia.
  rewrite Z_mod_plus_full. exact Hal16. }
unfold vs_goal, vs_cfg.
(* 0x89c6c .. 0x89c7c: s5 = v, a0 = v - 4095, a1 = -4094; the run stops at the range test 0x89c80 *)
paj_run_shc RUNP RUNC HS HJ.
{ vs_awr_ro. }
assert (KR1 : forall a, rdW (e_W e) (ms_mem ms) a = rdW (e_W e) mem' a) by (vsb_kept HFr).
rename HG into HG1. clear HF HFr. rename ms into m1.
psrr_branch_pi RUNP BR HS.
- (* in range: on to 0x89cb0 *)
  assert (Hvr : 1 <= v <= 4094).
  { rewrite branch_geu_U, U_lit, U_SOff, (EV 10%nat 10%bv eq_refl), R10 in Hc by lia.
    unfold w64, zcanon, M64 in Hc. rewrite unsigned_lit_small in Hc by lia.
    apply negb_true_iff, Z.ltb_ge in Hc.
    pose proof (vs_range_test v ltac:(lia)) as Hrt.
    assert (Hx : (2 ^ 64 - 4094 <=? (v - 4095) mod 2 ^ 64) = true).
    { apply Z.leb_le. replace (v - 4095) with (v + -4095) by lia. lia. }
    rewrite Hx in Hrt. symmetry in Hrt. apply andb_true_iff in Hrt as [Y1 Y2].
    apply Z.leb_le in Y1. apply Z.leb_le in Y2. lia. }
  clear Hc.
  paj_run_shc RUNP RUNC HS HJ.
  { vs_awr_ro. }
  assert (KR2 : forall a, rdW (e_W e) (ms_mem ms) a = rdW (e_W e) (ms_mem m1) a) by (vsb_kept HFr).
  rename HG into HG2. clear HF HFr. rename ms into m2.
  assert (EV18 : ew E 18 = Z_to_bv 64 (e_seg e)) by (rewrite (EV 18%nat 18%bv eq_refl), G18; reflexivity).
  assert (EV20 : ew E 20 = Z_to_bv 64 (e_seg e + Z.of_nat di)) by (rewrite (EV 20%nat 20%bv eq_refl), R20; reflexivity).
  assert (U19 : U E (SOff 19 0) = 16) by (apply U_atom; [rewrite (EV 19%nat 19%bv eq_refl), G19; reflexivity | lia]).
  (* 0x89cbc: plen + 1 >u cap, not taken *)
  psrr_branch_pi RUNP BR HS.
  { exfalso. rewrite branch_ltu_U, U19 in Hc.
    rewrite (vsb_U_a1 E 18 20 (e_seg e) (Z.of_nat di) _ 1 EV18 EV20) in Hc by (first [lia | reflexivity]).
    apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  paj_run_shc RUNP RUNC HS HJ.
  { vs_awr_ro. }
  assert (KR3 : forall a, rdW (e_W e) (ms_mem ms) a = rdW (e_W e) (ms_mem m2) a) by (vsb_kept HFr).
  rename HG into HG3. clear HF HFr. rename ms into m3.
  (* 0x89cc4: plen + 1 >u 16, not taken *)
  psrr_branch_pi RUNP BR HS.
  { exfalso. rewrite branch_ltu_U, U_lit in Hc by lia.
    rewrite (vsb_U_a1 E 18 20 (e_seg e) (Z.of_nat di) _ 1 EV18 EV20) in Hc by (first [lia | reflexivity]).
    apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  paj_run_shc RUNP RUNC HS HJ.
  { vs_awr_ro. }
  assert (KR4 : forall a, rdW (e_W e) (ms_mem ms) a = rdW (e_W e) (ms_mem m3) a) by (vsb_kept HFr).
  rename HG into HG4. clear HF HFr. rename ms into mc.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10.
  assert (Hspc : spZ (ms_regs mc) = spZ (e_regs e) + -64).
  { unfold spZ at 1. rewrite Q2, (EV 2%nat 2%bv eq_refl). change (bv_unsigned (getr regs' 2)) with (spZ regs'). lia. }
  assert (Q3' : getr (ms_regs mc) 3 = w64 (as_gp B)) by (rewrite Q3, (EV 3%nat 3%bv eq_refl), G3; exact Hgp).
  assert (Q4' : getr (ms_regs mc) 4 = w64 (as_tp B)) by (rewrite Q4, (EV 4%nat 4%bv eq_refl), G4; exact Htp).
  assert (HraT : YK0s.ret_ok (getr (ms_regs mc) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  (* every byte outside the stack window reads at the call as at the entry *)
  assert (KO : kept_out (rdW (e_W e) (e_mem e)) (rdW (e_W e) (ms_mem mc)) (spZ (e_regs e) - STK_reac_declared_vlan_split) (spZ (e_regs e))).
  { intros a Ha Hw. rewrite KR4, KR3, KR2, KR1. exact (HK a Ha Hw (fun x => x)). }
  assert (Hkhs : kHighShadowEnd <= spZ (e_regs e) - STK_reac_declared_vlan_split) by lia.
  destruct Hsadd as (A0 & A1 & A2 & A3 & A4).
  destruct (sa_strz_bytes SEGS _ _ _ _ (proj1 Hstr)) as (Hby & Hnz & _).
  assert (Hlz : length (seg_spec.zb (e_s e)) = length (e_s e)) by (unfold seg_spec.zb; apply length_map).
  assert (HSTR : astr_at SEGS (e_W e) (ms_mem mc) (e_seg e) (seg_spec.zb (e_s e))).
  { split; [|exact Hnz]. intros i Hi. rewrite length_app, Hlz in Hi. cbn [length] in Hi.
    rewrite (KO (e_seg e + Z.of_nat i)) by lia. apply Hby. rewrite length_app, Hlz. cbn [length]. lia. }
  assert (HRD : aread_ok SEGS ESTACK (e_W e) (ms_regs mc) (ms_mem mc) (e_seg e) (astr_len (seg_spec.zb (e_s e)) + 1)).
  { unfold astr_len. rewrite Hlz.
    split; [lia|]. split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - destruct HSTR as [Hb _]. assert (Hi : (Z.to_nat (a - e_seg e) < length (seg_spec.zb (e_s e) ++ [Z_to_bv 8 0]))%nat)
          by (rewrite length_app, Hlz; cbn [length]; lia).
        pose proof (Hb _ Hi) as X. rewrite Z2Nat.id in X by lia. replace (e_seg e + (a - e_seg e)) with a in X by lia.
        rewrite X. discriminate.
      - unfold ascratch_stk. rewrite Hspc, Hes. lia. }
    split; [unfold amem_range in *; lia|]. split.
    - exact (range_addressable_kept_win _ _ _ _ (e_seg e) (Z.of_nat (length (e_s e)) + 1) KO Hkhs ltac:(lia) ltac:(lia) A3).
    - intros _. exact (shadow_hull_vis_kept_win _ _ _ _ (e_seg e) (Z.of_nat (length (e_s e)) + 1) KO Hkhs ltac:(lia) ltac:(lia) ltac:(lia) (A4 ltac:(lia))). }
  assert (HTAIL : atail_vis SEGS (e_W e) (ms_mem mc) (e_seg e + astr_len (seg_spec.zb (e_s e)))).
  { unfold astr_len. rewrite Hlz. intros a Ha.
    pose proof ASAN_CEIL_range as (_ & Hc8). unfold ASAN_CEIL in Hc8.
    pose proof (Z.div_mod (e_seg e + Z.of_nat (length (e_s e))) 8 ltac:(lia)) as D1.
    pose proof (Z.mod_pos_bound (e_seg e + Z.of_nat (length (e_s e))) 8 ltac:(lia)) as D2.
    pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as D3.
    assert (Hlt : a < alloc_ceiling) by lia.
    rewrite (KO a) by lia. exact (proj2 Hstr a Ha). }
  assert (HROM : rt_rom_view SEGS B (e_W e) (ms_mem mc)).
  { intros a (sg & Hsg & Hw & Hr) Ho He.
    pose proof (pa_img_range a (ex_intro _ sg (conj Hsg Hr))) as Hia.
    rewrite (KO a) by (unfold kImgEnd in Hia; lia).
    exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He). }
  (* the strlen wrapper on the segment *)
  eapply SRr_bind.
  { eapply (vsb_art_at ESTACK (fun _ => False) (SIG SS___interceptor_trampoline_strlen)
      (e_W e) (ms_regs mc) (ms_mem mc) STK_reac_declared_vlan_split (spZ (e_regs e)) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) []
      (e_ly e) (e_S e) _ 0 (-64) _ _ HJ Hspc eq_refl ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(rewrite Hes, HVS; lia) Q1
      (fun a (H : False) => False_ind _ H)).
    apply (ASTRLEN fx (e_ly e) (e_S e) (e_W e) (ms_regs mc) (ms_mem mc) _ (e_seg e) (seg_spec.zb (e_s e))).
    - exact (ecall_pre_stk_at SEGS B ESTACK STK_reac_declared_vlan_split (spZ (e_regs e)) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) []
        (e_ly e) (e_S e) (e_W e) (ms_mem mc) _ 0 (ms_regs mc) (-64) HJ Hspc eq_refl ltac:(lia) ltac:(lia)
        ltac:(rewrite Hes, HVS; lia) HraT Q3' Q4').
    - rewrite Q10, (EV 18%nat 18%bv eq_refl). exact G18.
    - lia.
    - exact HSTR.
    - exact HRD.
    - exact HTAIL.
    - exact HROM. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2 & HPR2).
  assert (RC : forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ 22 <= r <= 27 ->
    getr regs2 (Z_to_bv 5 r) = getr regs' (Z_to_bv 5 r)).
  { intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)).
    assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 22 \/ r = 23 \/
      r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hcases as [-> | Hcases]); try subst r;
    lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
      let n := eval compute in (Z.to_nat k) in
      apply (vsb_reg_c _ _ _ _ n _ _ HS); [vm_compute; reflexivity | apply EV; reflexivity] end. }
  apply (HK4 e regs2 mem2 md2 di v HE).
  + split; [exact HJ2|]. split; [exact (vsb_regs_of e regs' regs2 HR RC)|]. split.
    { apply (vs_slots_kept (rdW (e_W e) mem')); [exact HSL|]. intros a Ha. unfold e_sp in Ha.
      rewrite HK2; [rewrite KR4, KR3, KR2, KR1; reflexivity | lia | rewrite Hes; lia | tauto]. }
    split.
    { intros a Ha Hw _. unfold e_sp in Hw. rewrite HK2; [| exact Ha | rewrite Hes; lia | tauto].
      exact (KO a Ha Hw). }
    intros a Ha. apply HPR2. apply (apresent_grows _ _ _ a HG4). apply (apresent_grows _ _ _ a HG3).
    apply (apresent_grows _ _ _ a HG2). apply (apresent_grows _ _ _ a HG1). exact (HPR a Ha).
  + exact Hdi.
  + exact Hdi0.
  + exact Hne.
  + exact Hdig.
  + reflexivity.
  + exact Hvr.
  + rewrite HQ2. unfold astr_len. rewrite Hlz. reflexivity.
  + change (getr regs2 20) with (getr regs2 (Z_to_bv 5 20)). rewrite (HP2 20 ltac:(unfold acallee_saved; lia)).
    rewrite (st_ok_restrict_reg SEGS _ _ _ _ _ HS).
    lazymatch goal with |- sv_denot _ (sr_get ?a ?r) = _ => let x := eval vm_compute in (sr_get a r) in change (sr_get a r) with x end.
    rewrite denot_lit_U, (vsb_U_s4 E 18 20 (e_seg e) (Z.of_nat di) _ EV18 EV20) by (first [lia | reflexivity]). reflexivity.
  + change (getr regs2 21) with (getr regs2 (Z_to_bv 5 21)). rewrite (HP2 21 ltac:(unfold acallee_saved; lia)).
    apply (vsb_reg_c _ _ _ _ 10%nat _ _ HS); [vm_compute; reflexivity | rewrite (EV 10%nat 10%bv eq_refl); exact R10].
- (* out of range: li a0,0, on to the epilogue *)
  assert (Hvs : SegModel.vlan_split (e_s e) = None).
  { rewrite branch_geu_U, U_lit, U_SOff, (EV 10%nat 10%bv eq_refl), R10 in Hc by lia.
    unfold w64, zcanon, M64 in Hc. rewrite unsigned_lit_small in Hc by lia.
    apply negb_false_iff, Z.ltb_lt in Hc.
    pose proof (vs_range_test v ltac:(lia)) as Hrt.
    assert (Hx : (2 ^ 64 - 4094 <=? (v - 4095) mod 2 ^ 64) = false).
    { apply Z.leb_gt. replace (v - 4095) with (v + -4095) by lia. lia. }
    rewrite Hx in Hrt.
    rewrite (vs_code_eq _ Hnul Hlen). apply (vs_none_range _ di Hdi).
    change (skipn (S di) (e_s e)) with (vs_tail e di). fold v.
    destruct (Z.leb_spec 1 v); destruct (Z.leb_spec v 4094); cbn [andb] in Hrt; try discriminate Hrt;
      apply orb_true_iff; first [left; apply Z.ltb_lt; lia | right; apply Z.ltb_lt; lia]. }
  clear Hc.
  paj_run_to_sh RUNTOP HS HJ VS_KR.
  { vs_awr_ro. }
  assert (KR2 : forall a, rdW (e_W e) (ms_mem ms) a = rdW (e_W e) (ms_mem m1) a) by (vsb_kept HFr).
  clear HF HFr.
  pmkst HS.
  apply (vs_exit_KR B gotw guard HKR e (e_ly e) (e_S e) (e_W e) regs' mem' (ms_regs ms) (ms_mem ms) _ 0 HE HR HSL HJ).
  + intros r Hr.
    assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hcases as [-> | Hcases]); try subst r;
    lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
      let n := eval compute in (Z.to_nat k) in
      eapply (vs_reg_atom _ _ _ _ _ n _ HS); [apply EV; reflexivity | vm_compute; reflexivity] end.
  + intros a Ha. rewrite KR2, KR1. reflexivity.
  + pose proof (st_ok_pi_restrict_reg (w_H (e_W e)) _ _ ms 10%bv HS) as F10.
    lazymatch type of F10 with _ = sv_denot _ (sr_get ?a ?r) =>
      let x := eval vm_compute in (sr_get a r) in change (sr_get a r) with x in F10 end.
    rewrite F10. reflexivity.
  + intros regs'' md'' H10''. unfold vs_Q. rewrite Hvs. split; [exact H10''|]. split; [exact I|]. split.
    * apply (vs_kept_step _ _ _ mem').
      -- exact (vs_kept_ctxW B e (fun _ => False) _ regs' mem' md' HC (fun a (H : False) => False_ind _ H)).
      -- intros a Ha Hw He. rewrite KR2, KR1. reflexivity.
    * split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs (e_S e)). destruct (e_S e); reflexivity.
Qed.

Lemma vs_K4 : vs_K5_stmt B gotw guard -> vs_K4_stmt B gotw guard.
Proof using AMEMCPY.
intros HK5. unfold vs_K4_stmt. intros e regs' mem' md' di v HE HC Hdi Hdi0 Hne Hdig Hv Hvr R10 R20 R21.
pose proof HE as (HPRE & HROD & H10 & B10 & H11 & B11 & H12 & H13 & B13 & HSP & Hnev).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HC as (HJ & HR & HSL & HK & HPR).
pose proof HR as (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27).
pose proof HSP as (Hs0 & Hstr & Hlen & Hsadd & Hamr & Hsloc & Hp0 & Hcap & Hpdst & Hpadd & Hpdisj & Hv0 & Hv2 & Hvdst & Hvadd & Hvdisj & Hssp).
assert (HVS : STK_reac_declared_vlan_split = 12352) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (@pa_B_ok _ _ PI) as HBASE. pose proof (pa_base_lo (L := seg_listing)) as HBLO.
unfold e_sp in *.
assert (Hnul : SegModel.nulfree (e_s e)) by exact (proj2 (proj1 Hstr)).
pose proof (vs_di_lt _ _ Hnul Hdi) as Hdil.
assert (Hcopy : split_copy (e_s e) = Some di)
  by (apply vs_copy_some; [exact Hnul | exact Hlen | exact Hdi | exact Hdi0 | exact Hne | exact Hdig | unfold vs_tail in Hv; lia]).
destruct (vsb_loc_facts _ _ _ _ _ (e_seg e) (Z.of_nat (length (e_s e)) + 1) HAR ltac:(lia) Hsloc) as (Sg0 & Sg1).
destruct (vs_dst_facts B _ _ _ _ _ _ _ _ 16 HAR Hstk ltac:(lia) Hpdst) as (Plo & Phi & Pplace).
set (E := Eimg (Ereg regs' (vs_xs (e_regs e) ++ []))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EV : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs' r)
  by (intros n r Hn; subst E; apply vs_EE; exact Hn).
assert (HS : st_ok_pi SEGS VAL E (vs_ssK VS_K4 [])
  (restrict (w_H (e_W e)) (mkst regs' (Z_to_bv 64 (BASE + VS_K4)) mem' (seg_rom SEGS)))).
{ apply vs_seedK; [replace (spZ regs' + 64) with (spZ (e_regs e)) by lia; exact HSL | lia | | exact G22 | exact I].
  rewrite Hsp. replace (spZ (e_regs e) - 64) with (spZ (e_regs e) + (-4) * 16) by lia.
  rewrite Z_mod_plus_full. exact Hal16. }
unfold vs_goal, vs_cfg.
(* 0x89cd0, 0x89cd4: a0 = len - 16, a1 = -17; the run stops at the length test 0x89cd8 *)
paj_run_shc RUNP RUNC HS HJ.
{ vs_awr_ro. }
assert (KR1 : forall a, rdW (e_W e) (ms_mem ms) a = rdW (e_W e) mem' a) by (vsb_kept HFr).
rename HG into HG1. clear HF HFr. rename ms into m1.
psrr_branch_pi RUNP BR HS.
{ (* taken only for len >= 16, which split_pre excludes *)
  exfalso. rewrite branch_ltu_U, U_lit, U_SOff, (EV 10%nat 10%bv eq_refl), R10 in Hc by lia.
  unfold w64, zcanon, M64 in Hc. rewrite unsigned_lit_small in Hc by lia.
  apply Z.ltb_lt in Hc. pose proof (vs_len_test (Z.of_nat (length (e_s e))) ltac:(lia)) as X.
  apply Z.ltb_ge in X. replace (Z.of_nat (length (e_s e)) + -16) with (Z.of_nat (length (e_s e)) - 16) in Hc by lia. lia. }
clear Hc.
(* 0x89cdc .. 0x89ce4: a0 = parent, a1 = segment, a2 = di; the run stops at the checked memcpy *)
paj_run_shc RUNP RUNC HS HJ.
{ vs_awr_ro. }
assert (KR2 : forall a, rdW (e_W e) (ms_mem ms) a = rdW (e_W e) (ms_mem m1) a) by (vsb_kept HFr).
rename HG into HG2. clear HF HFr. rename ms into mc.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
assert (Hspc : spZ (ms_regs mc) = spZ (e_regs e) + -64).
{ unfold spZ at 1. rewrite Q2, (EV 2%nat 2%bv eq_refl). change (bv_unsigned (getr regs' 2)) with (spZ regs'). lia. }
assert (Q3' : getr (ms_regs mc) 3 = w64 (as_gp B)) by (rewrite Q3, (EV 3%nat 3%bv eq_refl), G3; exact Hgp).
assert (Q4' : getr (ms_regs mc) 4 = w64 (as_tp B)) by (rewrite Q4, (EV 4%nat 4%bv eq_refl), G4; exact Htp).
assert (Ra0 : getr (ms_regs mc) 10 = w64 (e_parent e)) by (rewrite Q10, (EV 9%nat 9%bv eq_refl); exact G9).
assert (Ra1 : getr (ms_regs mc) 11 = w64 (e_seg e)) by (rewrite Q11, (EV 18%nat 18%bv eq_refl); exact G18).
assert (Ra2 : getr (ms_regs mc) 12 = w64 (Z.of_nat di)) by (rewrite Q12, (EV 20%nat 20%bv eq_refl); exact R20).
(* every byte outside the stack window reads at the call as at the entry *)
assert (KO : kept_out (rdW (e_W e) (e_mem e)) (rdW (e_W e) (ms_mem mc)) (spZ (e_regs e) - STK_reac_declared_vlan_split) (spZ (e_regs e))).
{ intros a Ha Hw. rewrite KR2, KR1. exact (HK a Ha Hw (fun x => x)). }
assert (Hkhs : kHighShadowEnd <= spZ (e_regs e) - STK_reac_declared_vlan_split) by lia.
destruct Hsadd as (A0 & A1 & A2 & A3 & A4).
destruct Hpadd as (P0 & P1 & P2 & P3 & P4).
pose proof Hstr as ((Hzs & Hnz) & Htail).
assert (Hsp' : forall i, (i < length (e_s e))%nat -> rdW (e_W e) (ms_mem mc) (e_seg e + Z.of_nat i) = Some (nth i (e_s e) 0)).
{ intros i Hi. rewrite (KO (e_seg e + Z.of_nat i)) by lia.
  pose proof (Hzs i ltac:(rewrite length_app; cbn [length]; lia)) as X. rewrite app_nth1 in X by lia. exact X. }
assert (Hspan : sa_disj (e_seg e) (Z.of_nat di) (e_parent e) (Z.of_nat di)).
{ unfold sa_disj, seg_spec.cstr_span in *.
  pose proof (Z.mod_pos_bound (- (e_seg e + Z.of_nat (length (e_s e)) + 1)) 8 ltac:(lia)). lia. }
(* the checked memcpy of di bytes from the segment to parent *)
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIG SS___asan_memcpy) (AMEMCPY fx)
    (e_W e) (ms_regs mc) (ms_mem mc) STK_reac_declared_vlan_split (spZ (e_regs e)) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) []
    (e_ly e) (e_S e) _ 0 (e_parent e) (e_seg e) (Z.of_nat di) (-64) (Z_to_bv 64 (BASE + 20408)) HJ Ra0 Ra1 Ra2).
  - lia.
  - lia.
  - lia.
  - exact Hspc.
  - reflexivity.
  - lia.
  - rewrite Hes, HVS. lia.
  - exact Q3'.
  - exact Q4'.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split.
    + apply (vs_dst_awr B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) (e_regs e) STK_reac_declared_vlan_split (e_FP e) (e_ly e) (e_S e) []
        (e_parent e) 16 a HAR Hpdst eq_refl (Permutation_refl _)); [| lia].
      unfold e_FP, split_W. rewrite Hcopy. exists (e_parent e, e_parent e + Z.of_nat di + 1).
      split; [apply in_or_app; left; left; reflexivity | cbn [fst snd]; lia].
    + rewrite Hes. destruct Pplace as [(_ & Pc) | (Pc & _)]; lia.
  - intros a Ha _ Hcase.
    destruct Hpdst as [((cid & pos & Hfin & Hcid & F1 & F2) & _) | [((b & m & Hbin & Bb1 & Bb2) & _) | (Rs1 & Rs2 & Rpres & _)]].
    + exfalso. destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hfin) as (F3 & F4 & _).
      destruct Hcase as [(_ & Himg) | Hsp2]; [exact (frm_img SEGS B LAWS _ _ _ _ _ cid pos a HAR Hfin ltac:(lia) Himg) | lia].
    + exfalso. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hbin) as (_ & B0 & B1 & _ & _ & _ & Bm).
      pose proof (req_size_pos m ltac:(lia)) as [Rq1 Rq2].
      destruct Hcase as [(_ & Himg) | Hsp2]; [exact (blk_img SEGS B LAWS _ _ _ _ _ b m a HAR Hbin ltac:(lia) Himg) | lia].
    + apply (apresent_writable SEGS). apply (apresent_grows _ _ _ a HG2). apply (apresent_grows _ _ _ a HG1). apply HPR.
      replace a with (e_parent e + (a - e_parent e)) by lia. apply Rpres. lia.
  - unfold amem_range in *. lia.
  - apply (range_addressable_sub _ _ (e_parent e) 16); [| lia | lia].
    exact (range_addressable_kept_win _ _ _ _ (e_parent e) 16 KO Hkhs ltac:(lia) ltac:(lia) P3).
  - intros Hn0. apply (vsb_hull_sub _ (e_parent e) 16); [| lia | lia | lia | lia].
    exact (shadow_hull_vis_kept_win _ _ _ _ (e_parent e) 16 KO Hkhs ltac:(lia) ltac:(lia) ltac:(lia) (P4 ltac:(lia))).
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - replace a with (e_seg e + Z.of_nat (Z.to_nat (a - e_seg e))) by lia. rewrite Hsp' by lia. discriminate.
      - rewrite Hspc, Hes. lia. }
    split; [unfold sa_disj in Hspan; lia|]. split; [unfold amem_range in *; lia|]. split.
    + apply (range_addressable_sub _ _ (e_seg e) (Z.of_nat (length (e_s e)) + 1)); [| lia | lia].
      exact (range_addressable_kept_win _ _ _ _ (e_seg e) (Z.of_nat (length (e_s e)) + 1) KO Hkhs ltac:(lia) ltac:(lia) A3).
    + intros Hn0. apply (vsb_hull_sub _ (e_seg e) (Z.of_nat (length (e_s e)) + 1)); [| lia | lia | lia | lia].
      exact (shadow_hull_vis_kept_win _ _ _ _ (e_seg e) (Z.of_nat (length (e_s e)) + 1) KO Hkhs ltac:(lia) ltac:(lia) ltac:(lia) (A4 ltac:(lia))). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff & Hfr & Hpres2 & Hsame).
cbv beta iota in Heff.
assert (RC : forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ 22 <= r <= 27 ->
  getr regs2 (Z_to_bv 5 r) = getr regs' (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)).
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hcases as [-> | Hcases]); try subst r;
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    let n := eval compute in (Z.to_nat k) in
    apply (vsb_reg_c _ _ _ _ n _ _ HS); [vm_compute; reflexivity | apply EV; reflexivity] end. }
assert (Hwin : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (e_regs e) - STK_reac_declared_vlan_split <= a < spZ (e_regs e)) ->
  ~ (e_parent e <= a < e_parent e + Z.of_nat di) -> rdW (e_W e) mem2 a = rdW (e_W e) (e_mem e) a).
{ intros a Ha Hw Hp. rewrite Hfr; [| exact Ha | exact Hp | rewrite Hes; lia]. exact (KO a Ha Hw). }
apply (HK5 e regs2 mem2 md2 di v HE).
- split; [exact HJ2|]. split; [apply (vsb_regs_of e regs' regs2 HR); intros r Hr; apply RC; lia|]. split.
  { apply (vs_slots_kept (rdW (e_W e) mem')); [exact HSL|]. intros a Ha. unfold e_sp in Ha.
    rewrite Hfr; [rewrite KR2, KR1; reflexivity | lia | destruct Pplace as [(_ & Pc) | (Pc & _)]; lia | rewrite Hes; lia]. }
  split; [exact Hwin|].
  intros a Ha. apply Hpres2. apply (apresent_grows _ _ _ a HG2). apply (apresent_grows _ _ _ a HG1). exact (HPR a Ha).
- exact Hdi.
- exact Hdi0.
- exact Hne.
- exact Hdig.
- exact Hv.
- exact Hvr.
- change (getr regs2 20) with (getr regs2 (Z_to_bv 5 20)). rewrite (RC 20 ltac:(lia)). exact R20.
- change (getr regs2 21) with (getr regs2 (Z_to_bv 5 21)). rewrite (RC 21 ltac:(lia)). exact R21.
- intros i Hi. rewrite (Heff (Z.of_nat i) ltac:(lia)). exact (Hsp' i ltac:(lia)).
Qed.
End e.
End f.
End d.
