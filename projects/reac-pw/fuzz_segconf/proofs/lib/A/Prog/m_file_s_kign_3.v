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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 447 of its 496 lines of code are new or changed and 404 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_KIGNP: the pieces KI_R3 0x86984 and KI_R5 0x869dc
   (lib/A/Prog/m_file_s_kign_m.v). The KIGNP segment lane (the KIGNP byte sub-lane) of the G2 walk owner's G2.
   proves no function (kind: segment lemma of m_file's walk: S_MF_KIGNP's KI_R3 and KI_R5 pieces).

   KI_R3 (after ieq(v, vl, "true"), s6 = 1): 0x86984 `bnez a0,0x869e4`; a hit loads g = 136(s1) at 0x869e4 and
   reaches KI_HIT with b = true. A miss: 0x86988 a0 = 1, a3 = 136(s1), `bne s4,a0,0x869b0`; for vl = 1 the inline
   load1 check of v (0x86994 .. 0x869a0, slow path 0x86e54), `lbu a0,0(s5)` and `beq a0,'1'` to KI_HIT (b = true);
   else 0x869b0 (KI_NO) sets up ieq(v, vl, "no") (0x869c0) and returns to KI_R4 (ki3_s_no).
   KI_R5 (after ieq(v, vl, "false")): 0x869dc `beqz a0,0x86c84`; a hit sets s6 = 0 (0x869e0), loads g and reaches
   KI_HIT with b = false. A miss: 0x86c84 s6 = s8 = line + 1, s8 = FAKE = 104(s1), a0 = 1, a3 = 136(s1),
   `bne s4,a0,0x86cc0`; for vl = 1 the load1 check (0x86c98 .. 0x86ca4, slow path 0x86e60), `lbu` and
   `bne a0,'0',0x86cc0`; a '0' sets s8 = line + 1, s6 = 0 and jumps to KI_HIT (b = false); else 0x86cc0 (MK_REFUSE of
   lib/A/Prog/m_file_s_kmod_m.v, m_refuse of the line).
   The seed (m_file_sd.v mf_seed) keeps two read-only regions: the spill slots 104(s1) (FAKE, atom 34) and 136(s1)
   (g, atom 37) (ki3_slots), and the text byte at v = p + ov (atom 21, its value the extra atom 52; ki3_txt, by
   mf_txt_region). No run writes a byte (ki3_frame_ro), so the cut facts carry over each run by m_file_k.v's
   mf_keep_run0 (ki3_carry). The load1 check leaves the obligation that [v, v + 1) is addressable, from mf_loop's
   sa_addr of the text left. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q YN1h.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_sd m_file_k ieq_c m_file_iq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_kign_t m_file_s_kign_m m_file_s_kign_1.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_kmod_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* 0x869b0: the "no" test is set up (KI_R3's misses join here) *)
Definition KI_NO : Z := AF_m_file + 0xaf4.
(* the text byte at v = s5 (atom 21), its value the seed's extra atom 52 *)
Definition ki3_txt : YP09.region := YP09.mkRegion (Some 21%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 52 0))].
(* the spill slots 104(s1) = FAKE (atom 34) and 136(s1) = g (atom 37), read only *)
Definition ki3_slots : YP09.region :=
  YP09.mkRegion (Some 2%nat) 104 144 0 0 [YP09.mkChunk 104 (CVal 8 (SOff 34 0)); YP09.mkChunk 136 (CVal 8 (SOff 37 0))].

(* the write-permission goal of a run whose regions are all read-only *)
Ltac ki3_awr :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
(* a register the run left at the seed's atom k: its value at the seed through EE (fresh atoms of a run are above
   the seed's, ewset) *)
Ltac ki3_ew Q := repeat (rewrite ew_ewset_other in Q by lia).
Ltac ki3_rg HS EE k r := let Q := fresh "Q" in prreg HS r Q; ki3_ew Q; rewrite Q; rewrite (EE k r eq_refl).
Lemma ki3_U_ewset : forall E k w x, YN1h.sv_free k x = true -> U (ewset E k w) x = U E x.
Proof. intros E k w x H. unfold U. rewrite YN1h.sv_denot_ewset_free by exact H. reflexivity. Qed.
Ltac ki3_U H := repeat (rewrite ki3_U_ewset in H by reflexivity).
(* a callee-saved register of mf_regs_at the run left alone *)
Ltac ki3_regs HS EE E32 B2 B9 B18 :=
  lazymatch goal with |- getr _ ?r = getr _ _ =>
    let Q := fresh "Q" in prreg HS r Q; ki3_ew Q; rewrite Q;
    first [ apply EE; vm_compute; reflexivity
          | rewrite (EE 2%nat (2%bv : bv 5) eq_refl), B2, B9; reflexivity
          | rewrite E32, B18; reflexivity ] end.

(* byte x of the text left rest at p (its NUL at x = |rest|) *)
Lemma ki3_txt_byte : forall rd p rest x, sa_str rd p rest -> (x <= length rest)%nat ->
  rd (p + Z.of_nat x) = Some (nth x rest 0).
Proof.
intros rd p rest x ((HZ & _) & _) Hx.
rewrite (HZ x ltac:(rewrite length_app; cbn [length]; lia)).
destruct (Nat.eq_dec x (length rest)) as [->|Hne].
- rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. rewrite nth_overflow by lia. reflexivity.
- rewrite app_nth1 by lia. reflexivity.
Qed.

(* the slots region is a read-only part of the seed's slot region *)
Lemma ki3_slots_sub : submem [ki3_slots] (mf_regions true true [] false false [] false MF_LOW_ON).
Proof.
unfold mf_regions. apply submem_drop. apply submem_keep; [|apply submem_nil].
unfold subregion, ki3_slots, mf_r_slots. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|].
intros ch Hch. unfold mf_cell_chunks. cbn [app In] in *.
destruct Hch as [<- | [<- | []]]; repeat (first [left; reflexivity | right]).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a run over a state whose regions are all read-only changed no byte *)
Lemma ki3_frame_ro : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hro a. unfold aview, mbyte. rewrite HF; [reflexivity|].
intros (r & Hin & Hr). pose proof (proj1 (forallb_forall _ _) Hro r Hin) as Hw. apply Z.leb_le in Hw. lia.
Qed.

(* the seed's atoms 32 (SB), 34 (FAKE = FB) and 37 (g) *)
Lemma ki3_e32 : forall regs1 v lyc pos cur np xs, ew (mfE regs1 v lyc pos cur np xs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof.
intros. pose proof (mfE_extra regs1 v lyc pos cur np xs 0 ltac:(unfold A_TEXT; lia)) as X.
cbn [Nat.add nth mf_extra map app] in X. exact X.
Qed.
Lemma ki3_e34 : forall regs1 v lyc pos cur np xs, ew (mfE regs1 v lyc pos cur np xs) 34 = w64 (frame_addr lyc 1 pos).
Proof.
intros. pose proof (mfE_extra regs1 v lyc pos cur np xs 2 ltac:(unfold A_TEXT; lia)) as X.
cbn [Nat.add nth mf_extra map app] in X. exact X.
Qed.
Lemma ki3_e37 : forall regs1 v lyc pos gi np xs,
  ew (mfE regs1 v lyc pos (Some gi) np xs) 37 = w64 (seg_spec.mseg_addr (mv_c v) gi).
Proof.
intros. pose proof (mfE_extra regs1 v lyc pos (Some gi) np xs 5 ltac:(unfold A_TEXT; lia)) as X.
cbn [Nat.add nth mf_extra map app] in X. exact X.
Qed.

Section e.
Variable B : asyms.
(* the shared Section hypotheses (the m_file cut-statement lane's list (a)) these pieces use *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstA.STK_ieq SegInstA.RLO_A SegInstA.RHI_A.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the cut facts at the end of a run that changed no byte (the run's frame over read-only regions) *)
Ltac ki3_carry CX CORE CELLS LOOP NP :=
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict (w_H ?W) ?m0) (mrestrict (w_H ?W) ?m1),
    HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m1 ?md1 _ |- _ =>
    let K := fresh "K" in
    pose proof (ki3_frame_ro _ _ (w_H W) m0 m1 HFr ltac:(vm_compute; reflexivity)) as K;
    let C1 := fresh "CORE" in let C2 := fresh "CELLS" in let N1 := fresh "NPk" in let L1 := fresh "LPk" in
    destruct (mf_keep_run0 B _ _ _ _ _ _ _ _ _ _ _ _ CX CORE CELLS HJ (fun a _ => K a)) as (C1 & C2 & N1 & L1);
    let N2 := fresh "NP" in let L2 := fresh "LOOP" in
    pose proof (N1 _ NP) as N2; pose proof (L1 _ _ _ _ _ LOOP) as L2;
    clear K N1 L1 HFr CORE CELLS NP LOOP;
    repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx end;
    repeat match goal with Hx : mem_grows _ _ |- _ => clear Hx end;
    rename C1 into CORE; rename C2 into CELLS; rename N2 into NP; rename L2 into LOOP
  end.
(* ki_vbase at the end of a run that left s5, s4, s8 and the registers of mf_regs_at at the seed's atoms *)
Ltac ki3_vb CX LS FRM CORE CELLS RA Hn Hr LOOP Hovl Hvv NP HS EE E32 B2 B9 B18 R21 R20 R24 :=
  unfold ki_vbase;
  refine (conj CX (conj LS (conj FRM (conj CORE (conj CELLS (conj _ (conj Hn (conj Hr (conj LOOP (conj Hovl
    (conj Hvv (conj NP _))))))))))));
  [ apply (mf_regs_at_of _ _ _ _ _ _ RA); ki3_regs HS EE E32 B2 B9 B18
  | split; [ki3_rg HS EE 21%nat (21%bv : bv 5); exact R21|];
    split; [ki3_rg HS EE 20%nat (20%bv : bv 5); exact R20|];
    ki3_rg HS EE 24%nat (24%bv : bv 5); exact R24 ].

(* the seed at a K cut's pc with the regions ki3_txt and ki3_slots and the fact of atom 21 *)
Lemma ki3_seed : forall v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov pc,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
  mf_regs_at B v lyc pos regs1 -> mf_loop v Wc memc mcc (Some gi) line p rest -> mf_np v memc Wc (mf_next p rest) ->
  getr regs1 21 = w64 (p + Z.of_nat ov) -> (ov <= length rest)%nat ->
  st_ok_pi SEGS VAL (mfE regs1 v lyc pos (Some gi) (mf_next p rest) [nth ov rest 0])
    (add_atom (mkSS pc sr_mf [ki3_txt; ki3_slots] None mf_facts) 21 (mkAF 4096 (2 ^ 47 - 8) 0))
    (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov pc CX CORE CELLS RA LOOP NP R21 Hov.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof LOOP as (_ & _ & _ & HSTR & (Hp0 & Hp1 & _) & LCUR & _). unfold mf_cur_ok in LCUR.
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE LCUR) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (b := nth ov rest 0).
assert (Hb : rdW Wc memc (p + Z.of_nat ov) = Some b) by (apply ki3_txt_byte; [exact HSTR | exact Hov]).
pose proof (ki_aview_byte _ _ _ _ _ Hb) as Hb8.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) (mf_next p rest) [b] pc true true []
  false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) (Forall_nil _)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
set (E := mfE regs1 v lyc pos (Some gi) (mf_next p rest) [b]) in *.
pose proof (st_ok_pi_submem E (ss_mf pc true true [] false false [] false MF_LOW_ON) _ [ki3_slots] HS0 ki3_slots_sub
  eq_refl) as HS1.
clear HS0.
assert (E52 : ew E 52 = Z_to_bv 64 b)
  by (unfold E; apply (mfE_xs regs1 v lyc pos (Some gi) (mf_next p rest) [b] 0); unfold A_TEXT; lia).
destruct (mf_txt_region B v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) (mf_next p rest) [b] 21
  (p + Z.of_nat ov) 1 [YP09.mkChunk 0 (CVal 1 (SOff 52 0))] line p rest true true [] false false [] false
  CX CORE RB LOOP) as (ROK & RDJ & RFT).
{ rewrite (mfE_reg regs1 v lyc pos (Some gi) (mf_next p rest) [b] 21 21%bv eq_refl), R21. reflexivity. }
{ lia. } { lia. } { lia. }
{ constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (p + Z.of_nat ov) 0 1 (SOff 52 0) b).
  - cbn [sv_denot]. rewrite E52, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 1)) with 256. lia.
  - cbn. lia.
  - rewrite Z.add_0_r. exact (mf_val1_of_aview (w_H Wc) memc _ _ Hb). }
fold E in ROK, RDJ, RFT.
pose proof (st_ok_pi_add_region E _ _ ki3_txt HS1 eq_refl ROK
  (all_disjoint_sub E ki3_txt ki3_txt _ _ (subregion_refl _) ki3_slots_sub RDJ)) as HS2.
clear HS1.
exact (st_ok_pi_add_fact E _ _ 21%nat _ HS2 RFT).
Qed.

(* 0x869b0 (KI_NO): ieq(v, vl, "no") (0x869b0 .. 0x869c0), then KI_R4 *)
Lemma ki3_s_no : forall n, KI_R4_stmt B n ->
  forall v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv,
  ki_vbase B n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
  mf_fin (ki_val mcc gi vv (line + 1), Some gi) line rest = mf_final v ->
  ieq vv S_yes = false -> ieq vv S_true = false -> ~ (length vv = 1%nat /\ hd0 vv = 49) ->
  mf_at B v Wc regs1 memc mdc KI_NO.
Proof.
intros n R4s v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv VB FIN NY NT N1.
pose proof VB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & Hovl & Hvv & NP & R21 & R20 & R24).
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (ki_line_le rest) as Hml.
pose proof (ki_seed0 B VOBJS v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest KI_NO CX CORE CELLS RA LOOP NP) as HS.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np []) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
pose proof CORE as (HJ & _).
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  apply awr_ok_nil. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
assert (HPc : aregs_preserved regs1 (ms_regs ms)).
{ eapply (ki_pres E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) eq_refl RB).
  - intros r. exact (st_ok_restrict_reg SEGS (w_H Wc) E _ ms r HS).
  - vm_compute. reflexivity. }
pose proof RA as (R2 & R3 & R4 & R8 & _).
assert (Q2 : getr (ms_regs ms) 2 = w64 (mf_s1 (mv_sp v))) by (rewrite <- R2; exact (HPc 2 ltac:(unfold acallee_saved; lia))).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite <- R3; exact (HPc 3 ltac:(unfold acallee_saved; lia))).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite <- R4; exact (HPc 4 ltac:(unfold acallee_saved; lia))).
assert (Q8 : getr (ms_regs ms) 8 = w64 (mv_sp v)) by (rewrite <- R8; exact (HPc 8 ltac:(unfold acallee_saved; lia))).
assert (Q10 : getr (ms_regs ms) 10 = w64 (p + Z.of_nat ov)).
{ rewrite (ki_st_reg SEGS _ _ _ _ 10%bv 21%nat HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 21 (Z_to_bv 5 21) eq_refl). exact R21. }
assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat vl)).
{ rewrite (ki_st_reg SEGS _ _ _ _ 11%bv 20%nat HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 20 (Z_to_bv 5 20) eq_refl). exact R20. }
assert (Q12 : getr (ms_regs ms) 12 = w64 (SegInstA.seg_litA_fz S_no)).
{ rewrite (ki_st_reg SEGS _ _ _ _ 12%bv (A_OBJ 23) HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_img regs1 v lyc pos (Some gi) np [] (A_OBJ 23) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (mf_lit_obj VOBJS S_no 23 ltac:(unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]))).
  reflexivity. }
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + KI_R4)).
{ rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 1%bv HS).
  lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
    transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
  exact (codeptr_val E KI_R4 HEI). }
rewrite (SIGP SS_ieq ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_ieq) with AF_ieq by (vm_compute; reflexivity).
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
  as (CORE' & CELLS' & NPk & LPk).
pose proof (NPk np NP) as NP'. pose proof (LPk mcc (Some gi) line p rest LOOP) as LOOP'.
destruct (ki_slice_facts B v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc (Some gi) line p rest ov vl CX CORE' LOOP'
  ltac:(lia)) as (SB & SZ & SL & SA & SH & S0).
rewrite Hvv in SB, SZ, SL.
refine (mf_ieq_call B RELRO IEQ v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos MF_LOW_ON mcc (Some gi)
  line p rest np KI_R4 (p + Z.of_nat ov) (Z.of_nat vl) (seg_spec.zb vv) S_no CX LS CORE' CELLS' LOOP' NP'
  Q2 Q3 Q4 Q8 Q1 _ _ _ Q10 Q11 Q12 S0 SB SL SA SH _).
- unfold KI_R4, AF_m_file; lia.
- unfold KI_R4, AF_m_file; reflexivity.
- unfold M_FILE_LITS; repeat (first [left; reflexivity | right]).
- intros S2 W2 regs2 mem2 md2 Hwle LS2 CORE2 CELLS2 LOOP2 NP2 HP2 A02 K2.
  assert (HP12 : aregs_preserved regs1 regs2) by exact (aregs_preserved_trans _ _ _ HPc HP2).
  rewrite SZ in A02.
  apply (R4s v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest ov vl vv).
  + unfold ki_vbase.
    refine (conj CX (conj LS2 (conj FRM (conj CORE2 (conj CELLS2 (conj (mf_regs_keep B v lyc pos regs1 regs2 RA HP12)
      (conj Hn (conj Hr (conj LOOP2 (conj Hovl (conj Hvv (conj NP2 _)))))))))))).
    split; [transitivity (getr regs1 21); [exact (HP12 21 ltac:(unfold acallee_saved; lia)) | exact R21]|].
    split; [transitivity (getr regs1 20); [exact (HP12 20 ltac:(unfold acallee_saved; lia)) | exact R20]|].
    transitivity (getr regs1 24); [exact (HP12 24 ltac:(unfold acallee_saved; lia)) | exact R24].
  + exact FIN.
  + exact NY.
  + exact NT.
  + exact N1.
  + exact A02.
Qed.

(* KI_R3 0x86984: `bnez a0` on ieq(v, vl, "true"); a hit or v = "1" goes to KI_HIT with b = true, else KI_NO *)
Lemma ki_s_r3 : forall n, KI_HIT_stmt B n -> KI_R4_stmt B n -> KI_R3_stmt B n.
Proof.
intros n HIT R4s v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv VB FIN NY A0 S6.
pose proof VB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & Hovl & Hvv & NP & R21 & R20 & R24).
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RB as (B2 & B8 & B9 & B18).
pose proof (ki_line_le rest) as Hml.
pose proof LOOP as (_ & _ & _ & HSTR & (Hp0 & Hp1 & _) & _ & _ & Hl0 & Hl1 & _).
assert (Hlv : length vv = vl) by (rewrite <- Hvv, length_firstn, length_skipn; lia).
pose proof (ki3_seed v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov KI_R3 CX CORE CELLS RA LOOP NP R21
  ltac:(lia)) as HS1.
set (b := nth ov rest 0) in *.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np [b]) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
assert (EE : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> ew E k0 = getr regs1 r)
  by (intros k0 r Hk; unfold E; apply mfE_reg; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (unfold E; apply ki3_e32).
assert (E52 : ew E 52 = Z_to_bv 64 b)
  by (unfold E; apply (mfE_xs regs1 v lyc pos (Some gi) np [b] 0); unfold A_TEXT; lia).
assert (Hb : rdW Wc memc (p + Z.of_nat ov) = Some b) by (apply ki3_txt_byte; [exact HSTR | lia]).
pose proof (ki_aview_byte _ _ _ _ _ Hb) as Hb8.
assert (U21 : U E (SOff 21 0) = p + Z.of_nat ov)
  by (apply U_atom; [rewrite (EE 21%nat 21%bv eq_refl), R21; reflexivity | lia]).
assert (U20 : U E (SOff 20 0) = Z.of_nat vl)
  by (apply U_atom; [rewrite (EE 20%nat 20%bv eq_refl), R20; reflexivity | lia]).
assert (U52 : U E (SExt false 8 (SOff 52 0)) = b).
{ rewrite U_zext, (U_atom E 52 b E52) by lia. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia. }
assert (UB : U E (SOff 32 0) = SHADOW_OFF) by (apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
pose proof CORE as (HJ & _).
destruct (ieq vv S_true) eqn:ETR; cbn [seg_spec.b2z] in A0.
- (* "true": a0 = 1, `bnez` to 0x869e4: a3 = g, KI_HIT with b = true *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_HIT.
  { ki3_awr. }
  ki3_carry CX CORE CELLS LOOP NP.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
    replace kk with KI_HIT by (unfold KI_HIT, AF_m_file; reflexivity) end.
  apply (HIT v lyc Sc Wc _ _ _ pos mcc gi line p rest ov vl vv true).
  + ki3_vb CX LS FRM CORE CELLS RA Hn Hr LOOP Hovl Hvv NP HS EE E32 B2 B9 B18 R21 R20 R24.
  + unfold ki_val in FIN. rewrite (ki_dec_true vv ETR) in FIN. exact FIN.
  + let Q := fresh "Q" in prreg HS (13%bv : bv 5) Q; ki3_ew Q; rewrite Q. unfold E. apply ki3_e37.
  + ki3_rg HS EE 22%nat (22%bv : bv 5). exact S6.
- (* "true" missed: a0 = 0; a0 = 1, a3 = g, `bne s4,a0` *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { ki3_awr. }
  ki3_carry CX CORE CELLS LOOP NP.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* vl <> 1: to KI_NO *)
    rewrite branch_ne_U in Hc. ki3_U Hc. rewrite U20, U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_NO.
    { ki3_awr. }
    ki3_carry CX CORE CELLS LOOP NP.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
      replace kk with KI_NO by (unfold KI_NO, AF_m_file; reflexivity) end.
    apply (ki3_s_no n R4s v lyc Sc Wc _ _ _ pos mcc gi line p rest ov vl vv).
    * ki3_vb CX LS FRM CORE CELLS RA Hn Hr LOOP Hovl Hvv NP HS EE E32 B2 B9 B18 R21 R20 R24.
    * exact FIN.
    * exact NY.
    * exact ETR.
    * intros (H1 & _). apply Hc. rewrite <- Hlv, H1. reflexivity.
  + (* vl = 1: the load1 check of v, `lbu a0,0(s5)`, `beq a0,'1'` *)
    rewrite branch_ne_U in Hc. ki3_U Hc. rewrite U20, U_lit in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
    assert (Hv1 : vl = 1%nat) by lia.
    assert (Hhd : hd0 vv = b) by (rewrite <- Hvv, Hv1; apply ki_hd0_slice; lia).
    paj_run_tok RUN HS HJ SHOK Bspan.
    { try (constructor; [|constructor]; unfold ob_holds; cbn [ob_x ob_n]).
      repeat (rewrite ki3_U_ewset by reflexivity).
      rewrite U21.
      pose proof LOOP as (_ & _ & _ & _ & HA & _).
      apply (obl_of_range SEGS _ _ _ (SOff 32 0) _ 1 p (Z.of_nat (length rest) + 1)); [|exact UB|lia|lia].
      exact (proj1 (proj2 (proj2 (proj2 HA)))). }
    { ki3_awr. }
    ki3_carry CX CORE CELLS LOOP NP.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* v[0] = '1': KI_HIT with b = true *)
      rewrite branch_eq_U in Hc0. ki3_U Hc0. rewrite U52, U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_HIT.
      { ki3_awr. }
      ki3_carry CX CORE CELLS LOOP NP.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
        replace kk with KI_HIT by (unfold KI_HIT, AF_m_file; reflexivity) end.
      apply (HIT v lyc Sc Wc _ _ _ pos mcc gi line p rest ov vl vv true).
      -- ki3_vb CX LS FRM CORE CELLS RA Hn Hr LOOP Hovl Hvv NP HS EE E32 B2 B9 B18 R21 R20 R24.
      -- unfold ki_val in FIN. rewrite (ki_dec_one vv ltac:(lia) ltac:(rewrite Hhd; exact Hc0)) in FIN. exact FIN.
      -- let Q := fresh "Q" in prreg HS (13%bv : bv 5) Q; ki3_ew Q; rewrite Q. unfold E. apply ki3_e37.
      -- ki3_rg HS EE 22%nat (22%bv : bv 5). exact S6.
    * (* else: to KI_NO *)
      rewrite branch_eq_U in Hc0. ki3_U Hc0. rewrite U52, U_lit in Hc0 by lia. apply Z.eqb_neq in Hc0.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_NO.
      { ki3_awr. }
      ki3_carry CX CORE CELLS LOOP NP.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
        replace kk with KI_NO by (unfold KI_NO, AF_m_file; reflexivity) end.
      apply (ki3_s_no n R4s v lyc Sc Wc _ _ _ pos mcc gi line p rest ov vl vv).
      -- ki3_vb CX LS FRM CORE CELLS RA Hn Hr LOOP Hovl Hvv NP HS EE E32 B2 B9 B18 R21 R20 R24.
      -- exact FIN.
      -- exact NY.
      -- exact ETR.
      -- intros (_ & H2). apply Hc0. rewrite <- Hhd. exact H2.
Qed.

(* KI_R5 0x869dc: `beqz a0` on ieq(v, vl, "false"); a hit or v = "0" goes to KI_HIT with b = false, else MK_REFUSE *)
Lemma ki_s_r5 : forall n, KI_HIT_stmt B n -> MK_REFUSE_stmt B n -> KI_R5_stmt B n.
Proof.
intros n HIT REF v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv VB FIN NY NT N1 NN A0.
pose proof VB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & Hovl & Hvv & NP & R21 & R20 & R24).
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RB as (B2 & B8 & B9 & B18).
pose proof (ki_line_le rest) as Hml.
pose proof LOOP as (_ & _ & _ & HSTR & (Hp0 & Hp1 & _) & _ & _ & Hl0 & Hl1 & _).
assert (Hlv : length vv = vl) by (rewrite <- Hvv, length_firstn, length_skipn; lia).
pose proof (ki3_seed v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov KI_R5 CX CORE CELLS RA LOOP NP R21
  ltac:(lia)) as HS1.
set (b := nth ov rest 0) in *.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np [b]) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
assert (EE : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> ew E k0 = getr regs1 r)
  by (intros k0 r Hk; unfold E; apply mfE_reg; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (unfold E; apply ki3_e32).
assert (E52 : ew E 52 = Z_to_bv 64 b)
  by (unfold E; apply (mfE_xs regs1 v lyc pos (Some gi) np [b] 0); unfold A_TEXT; lia).
assert (Hb : rdW Wc memc (p + Z.of_nat ov) = Some b) by (apply ki3_txt_byte; [exact HSTR | lia]).
pose proof (ki_aview_byte _ _ _ _ _ Hb) as Hb8.
assert (U21 : U E (SOff 21 0) = p + Z.of_nat ov)
  by (apply U_atom; [rewrite (EE 21%nat 21%bv eq_refl), R21; reflexivity | lia]).
assert (U20 : U E (SOff 20 0) = Z.of_nat vl)
  by (apply U_atom; [rewrite (EE 20%nat 20%bv eq_refl), R20; reflexivity | lia]).
assert (U52 : U E (SExt false 8 (SOff 52 0)) = b).
{ rewrite U_zext, (U_atom E 52 b E52) by lia. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia. }
assert (UB : U E (SOff 32 0) = SHADOW_OFF) by (apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
pose proof CORE as (HJ & _).
destruct (ieq vv S_false) eqn:EFA; cbn [seg_spec.b2z] in A0.
- (* "false": a0 = 1; s6 = 0, a3 = g, KI_HIT with b = false *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_HIT.
  { ki3_awr. }
  ki3_carry CX CORE CELLS LOOP NP.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
    replace kk with KI_HIT by (unfold KI_HIT, AF_m_file; reflexivity) end.
  apply (HIT v lyc Sc Wc _ _ _ pos mcc gi line p rest ov vl vv false).
  + ki3_vb CX LS FRM CORE CELLS RA Hn Hr LOOP Hovl Hvv NP HS EE E32 B2 B9 B18 R21 R20 R24.
  + unfold ki_val in FIN. rewrite (ki_dec_false vv NY NT N1 EFA) in FIN. exact FIN.
  + let Q := fresh "Q" in prreg HS (13%bv : bv 5) Q; ki3_ew Q; rewrite Q. unfold E. apply ki3_e37.
  + let Q := fresh "Q" in prreg HS (22%bv : bv 5) Q; rewrite Q. reflexivity.
- (* "false" missed: a0 = 0; `beqz` to 0x86c84: s6 = line + 1, s8 = FAKE, a0 = 1, a3 = g, `bne s4,a0` *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { ki3_awr. }
  ki3_carry CX CORE CELLS LOOP NP.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* vl <> 1: m_refuse *)
    rewrite branch_ne_U in Hc. ki3_U Hc. rewrite U20, U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan MK_REFUSE.
    { ki3_awr. }
    ki3_carry CX CORE CELLS LOOP NP.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
      replace kk with MK_REFUSE by (unfold MK_REFUSE, AF_m_file; reflexivity) end.
    apply (REF v lyc Sc Wc _ _ _ pos mcc gi line p rest ov vl vv).
    * unfold mk_base.
      refine (conj CX (conj LS (conj FRM (conj CORE (conj CELLS (conj _ (conj Hn (conj Hr (conj LOOP (conj Hovl
        (conj Hvv (conj NP _)))))))))))).
      -- apply (mf_regs_at_of _ _ _ _ _ _ RA); ki3_regs HS EE E32 B2 B9 B18.
      -- split.
         ++ let Q := fresh "Q" in prreg HS (24%bv : bv 5) Q; ki3_ew Q; rewrite Q. unfold E. apply ki3_e34.
         ++ let Q := fresh "Q" in prreg HS (22%bv : bv 5) Q; ki3_ew Q; rewrite Q, (EE 24%nat 24%bv eq_refl).
            exact R24.
    * unfold ki_val in FIN.
      rewrite (ki_dec_none vv NY NT N1 NN EFA ltac:(intros (H1 & _); apply Hc; rewrite <- Hlv, H1; reflexivity))
        in FIN.
      exact FIN.
  + (* vl = 1: the load1 check of v, `lbu a0,0(s5)`, `bne a0,'0'` *)
    rewrite branch_ne_U in Hc. ki3_U Hc. rewrite U20, U_lit in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
    assert (Hv1 : vl = 1%nat) by lia.
    assert (Hhd : hd0 vv = b) by (rewrite <- Hvv, Hv1; apply ki_hd0_slice; lia).
    paj_run_tok RUN HS HJ SHOK Bspan.
    { try (constructor; [|constructor]; unfold ob_holds; cbn [ob_x ob_n]).
      repeat (rewrite ki3_U_ewset by reflexivity).
      rewrite U21.
      pose proof LOOP as (_ & _ & _ & _ & HA & _).
      apply (obl_of_range SEGS _ _ _ (SOff 32 0) _ 1 p (Z.of_nat (length rest) + 1)); [|exact UB|lia|lia].
      exact (proj1 (proj2 (proj2 (proj2 HA)))). }
    { ki3_awr. }
    ki3_carry CX CORE CELLS LOOP NP.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* v[0] <> '0': m_refuse *)
      rewrite branch_ne_U in Hc0. ki3_U Hc0. rewrite U52, U_lit in Hc0 by lia. apply negb_true_iff, Z.eqb_neq in Hc0.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan MK_REFUSE.
      { ki3_awr. }
      ki3_carry CX CORE CELLS LOOP NP.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
        replace kk with MK_REFUSE by (unfold MK_REFUSE, AF_m_file; reflexivity) end.
      apply (REF v lyc Sc Wc _ _ _ pos mcc gi line p rest ov vl vv).
      -- unfold mk_base.
         refine (conj CX (conj LS (conj FRM (conj CORE (conj CELLS (conj _ (conj Hn (conj Hr (conj LOOP (conj Hovl
           (conj Hvv (conj NP _)))))))))))).
         ++ apply (mf_regs_at_of _ _ _ _ _ _ RA); ki3_regs HS EE E32 B2 B9 B18.
         ++ split.
            ** let Q := fresh "Q" in prreg HS (24%bv : bv 5) Q; ki3_ew Q; rewrite Q. unfold E. apply ki3_e34.
            ** let Q := fresh "Q" in prreg HS (22%bv : bv 5) Q; ki3_ew Q; rewrite Q, (EE 24%nat 24%bv eq_refl).
               exact R24.
      -- unfold ki_val in FIN.
         rewrite (ki_dec_none vv NY NT N1 NN EFA ltac:(intros (_ & H2); apply Hc0; rewrite <- Hhd; exact H2)) in FIN.
         exact FIN.
    * (* v[0] = '0': s8 = line + 1, s6 = 0, KI_HIT with b = false *)
      rewrite branch_ne_U in Hc0. ki3_U Hc0. rewrite U52, U_lit in Hc0 by lia. apply negb_false_iff, Z.eqb_eq in Hc0.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_HIT.
      { ki3_awr. }
      ki3_carry CX CORE CELLS LOOP NP.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
        replace kk with KI_HIT by (unfold KI_HIT, AF_m_file; reflexivity) end.
      apply (HIT v lyc Sc Wc _ _ _ pos mcc gi line p rest ov vl vv false).
      -- ki3_vb CX LS FRM CORE CELLS RA Hn Hr LOOP Hovl Hvv NP HS EE E32 B2 B9 B18 R21 R20 R24.
      -- unfold ki_val in FIN.
         rewrite (ki_dec_zero vv NY NT N1 ltac:(lia) ltac:(rewrite Hhd; exact Hc0)) in FIN. exact FIN.
      -- let Q := fresh "Q" in prreg HS (13%bv : bv 5) Q; ki3_ew Q; rewrite Q. unfold E. apply ki3_e37.
      -- let Q := fresh "Q" in prreg HS (22%bv : bv 5) Q; rewrite Q. reflexivity.
Qed.

End e.
End f.
End d.
