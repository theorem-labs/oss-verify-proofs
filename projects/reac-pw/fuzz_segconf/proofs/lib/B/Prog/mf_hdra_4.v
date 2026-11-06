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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 424 of its 474 lines of code are new or changed and 403 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140), segment S_MF_HDRA of lib/B/Prog/m_file_m.v:
   the point walk RIEQ 0x86558 (ieq's return) -> REF 0x867c0 / RS2 0x865a4 (lib/B/Prog/mf_hdra_m.v). A walk lane
   of the image-B m_file-family owner's G2B (a point agent, on a working branch).
   proves no function (kind: segment lemma of m_file's image-B walk: the point RIEQ -> REF / RS2 of segment S_MF_HDRA).

   hda_rieq : forall n, HDA_REF_stmt B n -> HDA_RS2_stmt B n -> HDA_RIEQ_stmt B n
   THE CODE (the neutral listing of m_file in image B lines 264-283, 739-741; b = p + q1, be = p + r1 in the
   cells 208 / 200, mf_hdra_t.v hda_q1 / hda_r1):
     0x86558  `beqz a0,867c0`        a0 = ieq's answer: 0 -> REF (m_header refuses: mf_hdra_t.v hd_ix_ieq)
     0x8655c  `ld a0,208(s1)`, 0x86560 `addi a0,a0,7`, 0x86564 `li a1,8`
     0x86568  `bltu a0,a1,86e84`     the UBSan trap (b + 7 <u 8): its taken edge is refuted at the branch by
                                     psrr_branch_tok from 4096 <= p <= b and b + 7 <= p + |rest| < 2 ^ 63 (the text
                                     block's place, m_file_k.v mf_loop_blk / the allocator's al_blocks, and mf_loop's
                                     sa_addr p (|rest| + 1))
     0x8656c  `srli a1,a0,3`, 0x86570 `add a1,a1,s2`, 0x86574 `lb a1,0(a1)`, 0x86578 `bnez a1,86cc4`: the
                                     instrumented check of b[7] (the slow path 0x86cc4-0x86ccc and the error path
                                     0x86f14, a call of errpath_load1, are not reached): decided by the shadow entry
                                     mkSHE 52 0 8 of [b, b + 8) (m_file_sd.v mf_she_at, from mf_loop's sa_addr
                                     range_addressable of the text and mf_txt_app for the shadow span)
     0x8657c  `lbu a1,0(a0)`         b[7] = nth (q1 + 7) rest 0 (the text region of atom 52, [0, 8), its chunk 7)
     0x86580  `li a2,9`, 0x86584 `beq a1,a2,8658c`, 0x86588 `bne a1,s5,867c0` (s5 = 0x20): neither '\t' nor ' '
                                     -> REF (m_header refuses: hd_ix_sp)
     0x8658c  `ld a1,200(s1)`, 0x86590 `sd a0,192(s1)`, 0x86594 `sd a1,184(s1)`, 0x86598 / 0x8659c a0 = s1 + 192,
              a1 = s1 + 184
     0x865a0  `jal strip`            m_file_rf.v mf_jal_step at AF_m_file + 0x460, the target by SIGP, the call by
                                     m_file_strip.v mf_strip_call over the text's [q1 + 7, r1): 192(s1) = p + q2,
                                     184(s1) = p + r2 at 0x865a4 = RS2 (the same FP state: strip's post is apost_base)
   THE RUN: the token executor over m_file_sd.v's mf_seed at RIEQ with xs = [b; be; b[7]] (atoms 52, 53, 54), the
   caller chunks 200 / 208 = atoms 53 / 52, the frame cells' window narrowed to [184, 200) (the two stores), the text
   region of atom 52 added (m_file_sd.v mf_txt_region). The runs up to the trap check no shadow byte (the empty
   shadow list); the run through the check takes the entry mkSHE 52 0 8, built at that run's memory, and the fact
   b in [4096, 2 ^ 47 - 8] on atom 52 (mf_txt_region). The cut facts after a run are m_file_k.v's mf_keep_run_s
   with RW a := s1 + 160 <= a < s1 + 216 (hd4_line_keep); the new cells 192 / 184 are the final state's chunks
   (st_ok_pi_region_nth, field_of_region; hd4_slots).
   POSITIONAL NAMES (checked against the listing by what each is): the cells 208 / 200 = b / be (0x86520 / 0x86524,
   0x8655c / 0x8658c), 192 / 184 = nm / ne (0x86590 / 0x86594), s5 = x21 = 0x20, s11 = x27 = line + 1, s2 = x18 = the
   shadow base, the jal 0x865a0 = AF_m_file + 0x460 = HDA_J_STRIP2 (slot PCall SS_strip 1 by vm_compute), its return
   0x865a4 = HDA_RS2, REF 0x867c0 = HDA_REF; atoms 52 .. 54 are m_file_sd.v's xs atoms 52 + i.
   Section hypotheses: VOBJS (the seed), SIGP (the jal's target), STRIP (strip_contract at BASE + AF_strip and
   SegInstB.STK_strip, at every FP state). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaNoChain PaArt PaFx SegObj SegGlob SegPgBase SegBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k strip_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_refuse_c m_file_rf m_file_strip.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_hdra_t mf_hdra_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the byte the executor loads with `lbu` from a one-byte chunk holding atom n = b *)
Lemma hd4_U_byte : forall E (n : nat) b, ew E n = Z_to_bv 64 b -> 0 <= b < 256 -> U E (SExt false 8 (SOff n 0)) = b.
Proof.
intros E n b Hn Hb. rewrite U_SExt, (U_atom E n b Hn ltac:(lia)). change (Z.of_N 8) with 8.
rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
Qed.

(* the state's form, computed *)
Ltac hd4_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
(* the goal's pc as the named point *)
Ltac hd4_pc pc := lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?k)) _ _) _) _ =>
  let Hk := fresh in assert (Hk : k = pc) by (vm_compute; reflexivity); rewrite Hk; clear Hk end.
(* the run's write permission: the frame cells (base atom 2 = s1, window [184, 200)) are the caller's real stack
   below sp0, every other region read-only (mf_front_4.v fr4_awr) *)
Ltac hd4_awr v U2v HSTKv :=
  lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
  repeat first
    [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat (mf_s1 (mv_sp v) - mv_sp v));
        [ reflexivity | rewrite ?ew_ewset_other by lia; rewrite U2v; ring
        | cbn [YP09.r_wlo YP09.r_whi]; try rewrite HSTKv; unfold mf_s1; lia
        | cbn [YP09.r_wlo YP09.r_whi]; unfold mf_s1; lia |] ];
  apply awr_ok_nil.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the reader after a run equals the start reader mc outside [s1 + 160, s1 + 216) (K, updated); the run's frame
   hypotheses and the machine states no hypothesis names any more are dropped, the current one named ms
   (mf_front_4.v fr4_k at this file's set) *)
Ltac hd4_k v mc K HS HJ U2v :=
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict (w_H ?W) ?m0) (mrestrict _ ?m1) |- _ =>
    let K1 := fresh "K" in
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 160 <= a < mf_s1 (mv_sp v) + 216) ->
      aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mc a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hna := fresh "Hna" in
      intros a Ha Hna; transitivity (aview SEGS (w_H W) m0 a); [|exact (K a Ha Hna)];
      refine (kept_of_frame Ex rs (w_H W) m0 m1 (fun x => mf_s1 (mv_sp v) + 160 <= x < mf_s1 (mv_sp v) + 216)
        HFr _ a Ha Hna);
      let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
      let Hinw := fresh "Hinw" in let Hr := fresh "Hr" in
      intros bb wlo whi x Hinw Hr; vm_compute in Hinw; cbv beta;
      repeat (let Hq := fresh "Hq" in destruct Hinw as [Hq | Hinw];
        [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?ew_ewset_other in Hr by lia; rewrite ?U2v in Hr;
         lia |]); destruct Hinw
    | clear K; rename K1 into K ] end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with old : machine_state |- _ =>
    lazymatch type of HS with context [old] => fail | _ => clear old end end;
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => try rename msx into ms end;
  lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ =>
    let md := fresh "md" in set (md := d) in *; clearbody md end.
(* the cells 192 / 184 at the jal 0x865a0: the final state's chunks (atom 52 + 7 = b + 7 from 0x86590, atom 53 = be
   from 0x86594) in the frame cells' region (region 2), read out by field_of_region *)
Ltac hd4_slots v Wc p q1 r1 HS U2v E52 E53 V192 V184 :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    let r2 := eval vm_compute in (nth 2 (ss_mem ssx) (mf_r_slots true false [])) in
    let HRf := fresh "HRf" in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 2 r2 HS eq_refl) as HRf;
    cbn [ms_mem restrict mkst] in HRf;
    pose proof (field_of_region (segs := SEGS) Ex _ 2%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 192 8%N (SOff 52 7)
      (p + Z.of_nat (q1 + 7)) HRf ltac:(rewrite ?ew_ewset_other by lia; exact U2v)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E52, unsigned_lit_small by lia; f_equal; lia)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(change (Z.of_N 8) with 8; lia)) as V192;
    pose proof (field_of_region (segs := SEGS) Ex _ 2%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 184 8%N (SOff 53 0)
      (p + Z.of_nat r1) HRf ltac:(rewrite ?ew_ewset_other by lia; exact U2v)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E53, unsigned_lit_small by lia; f_equal; lia)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(change (Z.of_N 8) with 8; lia)) as V184;
    change (N.to_nat 8) with 8%nat in V192, V184; clear HRf
  end.
(* the byte b[7] (atom 54) and s5 = 0x20 (atom 21) as Z values in a branch condition, at the run's environment
   (the token run adds atoms from 1024 on: ew_ewset_other) *)
Ltac hd4_byte Hc b7 E54 Hb7r :=
  lazymatch type of Hc with context [U ?Ex (SExt false 8 (SOff 54 0))] =>
    rewrite (hd4_U_byte Ex 54 b7 ltac:(rewrite ?ew_ewset_other by lia; exact E54) Hb7r) in Hc end.
Ltac hd4_s5 Hc EE R21 :=
  lazymatch type of Hc with context [U ?Ex (SOff 21 0)] =>
    rewrite (U_atom Ex 21 32 ltac:(rewrite ?ew_ewset_other by lia; rewrite (EE 21%nat 21%bv eq_refl), R21; reflexivity)
      ltac:(lia)) in Hc end.

Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
(* the jal's target (lib/B/Prog/SegObj.v; the lane's shared list) *)
Hypothesis SIGP : seg_sig_prog.
(* the callee, at every FP state (the image-B m_file segment table's strip row) *)
Hypothesis STRIP : forall fx0 : YK11.FPState, strip_contract (fx := fx0) SEGS B (BASE + AF_strip) SegInstB.STK_strip.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the line's facts across a run that writes only [s1 + 160, s1 + 216) (m_file_k.v mf_keep_run_s with that set, as
   mf_front_4.v fr4_keep), the next line's address 152(s1) included *)
Lemma hd4_line_keep : forall n v lyc Sc (Wc : world SEGS) memc mdc pos mcc cur line p rest mem2 md2,
  hda_line B n v lyc Sc Wc memc mdc pos mcc cur line p rest ->
  ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem2 md2 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 160 <= a < mf_s1 (mv_sp v) + 216) ->
     rdW Wc mem2 a = rdW Wc memc a) ->
  hda_line B n v lyc Sc Wc mem2 md2 pos mcc cur line p rest.
Proof.
intros n v lyc Sc Wc memc mdc pos mcc cur line p rest mem2 md2 HL HJ2 K.
pose proof HL as (CX & LS & FRM & CORE & CELLS & Hn & Hne & LOOP & NP).
set (RW := fun a => mf_s1 (mv_sp v) + 160 <= a < mf_s1 (mv_sp v) + 216) in K.
pose proof CORE as (HJ & _ & _ & VSH & _ & _ & Hmc & _).
pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Sp1.
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Bk1 & Bk2 & _).
pose proof (Z.mod_pos_bound (mv_sp v - 320) 32 ltac:(lia)) as M32.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
assert (RWok : forall a, RW a -> mf_rw v lyc pos a)
  by (intros a Ha; unfold mf_rw; unfold RW in Ha; right; right; right; right; right; lia).
assert (RWS : mf_rws v RW) by (intros a Ha _; right; unfold RW in Ha; lia).
destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur mem2 md2 RW MF_LOW_OFF cur mcc CX CORE CELLS
  HJ2 K RWok RWS) as (C1 & C2 & C3).
- intros i Hi. apply (mf_val_keep Wc Wc memc mem2 RW _ 1 _ K);
    [unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia | | exact (VSH i Hi)].
  intros k Hk HR. unfold RW, mf_s1 in HR. change (Z.of_nat 1) with 1 in Hk. unfold SHADOW_OFF in HR. lia.
- apply (mf_val_keep Wc Wc memc mem2 RW _ 8 _ K);
    [unfold mf_s1; lia | change (Z.of_nat 8) with 8; unfold mf_s1; lia | | exact V136].
  intros k Hk HR. unfold RW in HR. change (Z.of_nat 8) with 8 in Hk. lia.
- apply (mf_mconf_keep Wc Wc memc mem2 RW _ _ K); [lia | unfold seg_spec.SEG_M_SIZE in *; lia | | exact Hmc].
  intros a Ha HR. unfold RW, mf_s1 in HR. unfold seg_spec.SEG_M_SIZE in *. lia.
- refine (conj CX (conj LS (conj FRM (conj C1 (conj C2 (conj Hn (conj Hne (conj (C3 _ _ _ _ _ LOOP) _)))))))).
  unfold mf_np, mf_slot in NP |- *.
  apply (mf_val_keep Wc Wc memc mem2 RW _ 8 _ K);
    [unfold mf_s1; lia | change (Z.of_nat 8) with 8; unfold mf_s1; lia | | exact NP].
  intros k Hk HR. unfold RW in HR. change (Z.of_nat 8) with 8 in Hk. lia.
Qed.

(* 0x865a0 `jal strip` to RS2 0x865a4: the jal step (m_file_rf.v mf_jal_step, the target BASE + AF_strip by SIGP) and
   the call (m_file_strip.v mf_strip_call at the cells 192 / 184 over the text's [q1 + 7, r1)); strip's post gives
   192(s1) = p + q2 and 184(s1) = p + r2 (mf_hdra_t.v hda_q2 / hda_r2), every cut fact kept, the same FP state *)
Lemma hd4_jal : forall n, HDA_RS2_stmt B n ->
  forall v lyc Sc Wc (regs : bvmap 5 word) memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z)
    (rest : list Z) (i j : nat),
  hda_line B n v lyc Sc Wc memc mdc pos mcc cur line p rest -> mf_regs_at B v lyc pos regs ->
  hda_hdr v mcc line rest i j -> hda_close rest i j ->
  (hda_q1 rest i j + 8 <= hda_r1 rest i j)%nat ->
  ieq (slice (hda_q1 rest i j) (hda_q1 rest i j + 7) rest) S_segment = true ->
  sp_tab (nth (hda_q1 rest i j + 7) rest 0) = true ->
  mf_slot v memc Wc 192 (p + Z.of_nat (hda_q1 rest i j + 7)) ->
  mf_slot v memc Wc 184 (p + Z.of_nat (hda_r1 rest i j)) ->
  getr regs 10 = w64 (mf_s1 (mv_sp v) + 192) -> getr regs 11 = w64 (mf_s1 (mv_sp v) + 184) ->
  getr regs 27 = w64 (line + 1) ->
  SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + HDA_J_STRIP2)) memc (seg_rom SEGS)) mdc) (MF_POST B v).
Proof.
intros n RS2 v lyc Sc Wc regs memc mdc pos mcc cur line p rest i j HL RA HH HC H8 HIEQ HSP S192 S184 R10 R11 R27.
pose proof HL as (CX & LS & FRM & CORE & CELLS & Hn & Hne & LOOP & NP).
pose proof HH as (HL512 & Hij & HjL & HSL & HLB & HFIN).
pose proof HC as (HMC & H2).
pose proof (hd_line_le rest) as HLr.
pose proof (hd_q1r1 rest i j ltac:(lia) H2) as (Q1a & Q1b).
pose proof (hd_strip_le rest (hda_q1 rest i j + 7) (hda_r1 rest i j) ltac:(lia)) as HSL7.
pose proof pa_segs_low as Hsegs.
apply (mf_jal_step Wc regs memc mdc _ HDA_J_STRIP2 SS_strip);
  [vm_compute; reflexivity | unfold HDA_J_STRIP2, AF_m_file; lia |].
intros mat'.
assert (SIGR : pa_sigma SS_strip = BASE + AF_strip).
{ rewrite (SIGP SS_strip) by (unfold seg_prog_syms; cbn [In]; tauto). f_equal; try (vm_compute; reflexivity). }
rewrite SIGR.
set (mdc' := with_vm_backing (m_vm_lazy mdc) mat' mdc).
set (regsc := regupd regs 1%bv (Z_to_bv 64 (BASE + (HDA_J_STRIP2 + 4)))).
pose proof CORE as (HJ1 & CR1).
pose proof (ajournal_materialize SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ1) as HJ1'. fold mdc' in HJ1'.
assert (CORE' : mf_core B v lyc Sc Wc memc mdc' pos MF_LOW_OFF mcc) by exact (conj HJ1' CR1).
assert (GR : forall r : bv 5, r <> 1%bv -> getr regsc r = getr regs r)
  by (intros r Hr; apply mf_getr_upd1; exact Hr).
assert (RAc : mf_regs_at B v lyc pos regsc).
{ apply (mf_regs_at_of B v lyc pos regs regsc RA); apply GR; discriminate. }
apply (mf_strip_call B STRIP v lyc Sc Wc regsc memc mdc' pos MF_LOW_OFF mcc cur line p rest (mf_next p rest)
  (HDA_J_STRIP2 + 4) 192 184 (hda_q1 rest i j + 7) (hda_r1 rest i j) CX LS CORE' CELLS LOOP NP RAc).
- apply mf_getr_upd1_same.
- unfold HDA_J_STRIP2, AF_m_file; lia.
- vm_compute. reflexivity.
- lia.
- lia.
- vm_compute. reflexivity.
- lia.
- lia.
- vm_compute. reflexivity.
- lia.
- rewrite GR by discriminate. exact R10.
- rewrite GR by discriminate. exact R11.
- lia.
- exact S192.
- exact S184.
- intros S2 W2 regs2 mem2 md2 HWle LS2 CORE2 CELLS2 LOOP2 NP2 RA2 HPR V192 V184 _.
  replace (HDA_J_STRIP2 + 4) with HDA_RS2 by (unfold HDA_J_STRIP2, HDA_RS2; lia).
  apply (RS2 v lyc S2 W2 regs2 mem2 md2 pos mcc cur line p rest i j).
  + exact (conj CX (conj LS2 (conj FRM (conj CORE2 (conj CELLS2 (conj Hn (conj Hne (conj LOOP2 NP2)))))))).
  + exact RA2.
  + exact HH.
  + exact HC.
  + exact H8.
  + exact HIEQ.
  + exact HSP.
  + replace (p + Z.of_nat (hda_q2 rest i j)) with
      (p + Z.of_nat (hda_q1 rest i j + 7) +
       Z.of_nat (strip_lead (slice (hda_q1 rest i j + 7) (hda_r1 rest i j) rest))) by (unfold hda_q2; lia).
    exact V192.
  + replace (p + Z.of_nat (hda_r2 rest i j)) with
      (p + Z.of_nat (hda_r1 rest i j) -
       Z.of_nat (strip_trail (slice (hda_q1 rest i j + 7) (hda_r1 rest i j) rest))) by (unfold hda_r2; lia).
    exact V184.
  + transitivity (getr regsc 27); [exact (HPR 27 ltac:(unfold acallee_saved; lia))|].
    rewrite GR by discriminate. exact R27.
Qed.

Lemma hda_rieq : forall n, HDA_REF_stmt B n -> HDA_RS2_stmt B n -> HDA_RIEQ_stmt B n.
Proof.
intros n REF RS2. unfold HDA_RIEQ_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j HL RA HH HC H8 S208 S200 R10 R21 R27.
pose proof HL as (CX & LS & FRM & CORE & CELLS & Hn & Hne & LOOP & NP).
pose proof HH as (HL512 & Hij & HjL & HSL & HLB & HFIN).
pose proof HC as (HMC & H2).
pose proof (hd_line_le rest) as HLr.
pose proof (hd_q1r1 rest i j ltac:(lia) H2) as (Q1a & Q1b).
pose proof CORE as (HJ & _).
pose proof HJ as (HAR & _).
destruct (mf_sp0 B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in S1.
pose proof LOOP as (_ & _ & _ & LSTR & LADDR & Lcur & _).
pose proof LADDR as (PA1 & PA2 & _ & PRA & _).
destruct (mf_loop_blk B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP)
  as (bt & mt & Hbt & Hbt1 & Hbt2 & Htp).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bt mt HAR Hbt) as (_ & Bt4096 & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE Lcur) as HCUR.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP) as HNP.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof (Z.mod_pos_bound (mv_sp v - 320) 32 ltac:(lia)) as M32.
set (q1 := hda_q1 rest i j) in *. set (r1 := hda_r1 rest i j) in *.
assert (Hq7 : (q1 + 7 <= length rest)%nat) by lia.
(* b[7], the byte the code tests *)
set (b7 := nth (q1 + 7) rest 0).
assert (HB7 : rdW Wc memc (p + Z.of_nat (q1 + 7)) = Some b7) by exact (st_txt_byte _ p rest (q1 + 7) LSTR Hq7).
pose proof (st_aview_range Wc memc _ _ HB7) as Hb7r.
(* the seed: xs = [b; be; b[7]] (atoms 52, 53, 54), the cells 200 / 208 = atoms 53 / 52 *)
set (xs := [p + Z.of_nat q1; p + Z.of_nat r1; b7]).
pose proof (mfE_xs regs1 v lyc pos cur (mf_next p rest) xs 0 ltac:(unfold A_TEXT; lia)) as E52.
pose proof (mfE_xs regs1 v lyc pos cur (mf_next p rest) xs 1 ltac:(unfold A_TEXT; lia)) as E53.
pose proof (mfE_xs regs1 v lyc pos cur (mf_next p rest) xs 2 ltac:(unfold A_TEXT; lia)) as E54.
cbn [Nat.add nth xs] in E52, E53, E54.
assert (FSLX : Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur (mf_next p rest) xs) (mrestrict (w_H Wc) memc)
  (mf_s1 (mv_sp v))) [YP09.mkChunk 200 (CVal 8 (SOff 53 0)); YP09.mkChunk 208 (CVal 8 (SOff 52 0))]).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (mf_chunk_atom _ _ _ 200 53 0 (p + Z.of_nat r1) E53); [lia | lia | rewrite Z.add_0_r; exact S200].
  - apply (mf_chunk_atom _ _ _ 208 52 0 (p + Z.of_nat q1) E52); [lia | lia | rewrite Z.add_0_r; exact S208]. }
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) xs HDA_RIEQ
  true true [YP09.mkChunk 200 (CVal 8 (SOff 53 0)); YP09.mkChunk 208 (CVal 8 (SOff 52 0))] false false [] false
  CX CORE RB (fun _ => CELLS) HCUR (fun _ => NP) HNP ltac:(unfold MF_LOW_OFF; lia) FSLX (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
(* the text region of atom 52: [b, b + 8), its byte 7 = atom 54 *)
assert (FCS : Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur (mf_next p rest) xs) (mrestrict (w_H Wc) memc)
  (p + Z.of_nat q1)) [YP09.mkChunk 7 (CVal 1 (SOff 54 0))]).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (p + Z.of_nat q1) 7 1 (SOff 54 0) b7).
  - cbn [sv_denot]. rewrite E54, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 1)) with 256. lia.
  - change (Z.of_N 1) with 1. lia.
  - replace (p + Z.of_nat q1 + 7) with (p + Z.of_nat (q1 + 7)) by lia.
    exact (mf_val1_of_aview (w_H Wc) memc _ b7 HB7). }
destruct (mf_txt_region B v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) xs 52 (p + Z.of_nat q1) 8
  [YP09.mkChunk 7 (CVal 1 (SOff 54 0))] line p rest true true
  [YP09.mkChunk 200 (CVal 8 (SOff 53 0)); YP09.mkChunk 208 (CVal 8 (SOff 52 0))] false false [] false
  CX CORE RB LOOP E52 ltac:(lia) ltac:(lia) ltac:(lia) FCS) as (RT & DT & FT).
(* the shadow base atom (the shadow entry of [b, b + 8) is built after the first run, at its memory) *)
pose proof (mfE_U32 regs1 v lyc pos cur (mf_next p rest) xs) as U32.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (mfE regs1 v lyc pos cur (mf_next p rest) xs) k = getr regs1 r)
  by (intros; apply mfE_reg; assumption).
pose proof (mfE_extra regs1 v lyc pos cur (mf_next p rest) xs 0 ltac:(unfold A_TEXT; lia)) as E32.
cbn [Nat.add nth mf_extra map app] in E32.
assert (HEI : img_env VAL A_LIM (mfE regs1 v lyc pos cur (mf_next p rest) xs)) by (unfold mfE; apply Eimg_env).
set (E := mfE regs1 v lyc pos cur (mf_next p rest) xs) in *.
clearbody E.
(* the text region of atom 52 added (region 0), then the frame cells (now region 2) written only at [184, 200) *)
assert (HS1 := st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 52%nat) 0 8 0 0 [YP09.mkChunk 7 (CVal 1 (SOff 54 0))])
  HS0 ltac:(vm_compute; reflexivity)).
specialize (HS1 RT DT). clear HS0 RT DT.
hd4_norm HS1.
pose proof (st_ok_pi_region_nth E _ _ 2 _ HS1 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 2 r (set_window r 184 200) HS1 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 184 200 HR1
      ltac:(destruct HR1 as (_ & _ & HW & _); intros o Ho; apply HW; cbn [YP09.r_wlo YP09.r_whi]; lia))) as HS end.
clear HS1 HR1. hd4_norm HS.
(* the first runs check no shadow byte: the empty shadow list *)
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64, mf_s1; apply unsigned_lit_small; lia).
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 160 <= a < mf_s1 (mv_sp v) + 216) ->
  rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
assert (U10 : U E (SOff 10 0) = seg_spec.b2z (ieq (slice q1 (q1 + 7) rest) S_segment)).
{ apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity | unfold seg_spec.b2z; destruct (ieq _ _); lia]. }
assert (U21 : U E (SOff 21 0) = 32) by (apply U_atom; [rewrite (EE 21%nat 21%bv eq_refl), R21; reflexivity | lia]).
assert (U52 : U E (SOff 52 7) = p + Z.of_nat q1 + 7) by (apply (U_atom_off E 52 (p + Z.of_nat q1) 7 E52); lia).
unfold mf_at.
destruct (ieq (slice q1 (q1 + 7) rest) S_segment) eqn:HIEQ; unfold seg_spec.b2z in U10.
2:{
(* ======== ieq = 0: 0x86558 `beqz a0` taken, m_header refuses (hd_ix_ieq), to REF ======== *)
psrr_branch_tok RUN BR HS SHOK Bspan.
2:{ (* not taken would need a0 = ieq's answer = 0 <> 0 *)
    exfalso. rewrite branch_eq_U, U10 in Hc. rewrite ?U_lit, ?U_SLit in Hc by lia. cbn in Hc. discriminate Hc. }
paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_REF; [hd4_awr v U2 HSTK|].
hd4_k v memc K HS HJ U2.
pose proof (hd4_line_keep n v lyc Sc Wc memc mdc pos mcc cur line p rest _ _ HL HJ K) as HL'.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
  - rewrite Q2. apply EE. reflexivity.
  - rewrite Q3. apply EE. reflexivity.
  - rewrite Q4. apply EE. reflexivity.
  - rewrite Q8. apply EE. reflexivity.
  - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
  - rewrite Q18, E32, R18. reflexivity.
  - rewrite Q23. apply EE. reflexivity.
  - rewrite Q24. apply EE. reflexivity.
  - rewrite Q19. apply EE. reflexivity.
  - rewrite Q22. apply EE. reflexivity.
  - rewrite Q25. apply EE. reflexivity. }
pmkst HS. hd4_pc HDA_REF.
apply (REF v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest HL' RA').
- rewrite <- HFIN, (hd_ix_ieq rest i j ltac:(lia) HC mcc (line + 1) H8 HIEQ). reflexivity.
- rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27. }
(* ======== ieq = 1: 0x86558 `beqz a0` not taken ======== *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* taken would need a0 = ieq's answer = 1 = 0 *)
  exfalso. rewrite branch_eq_U, U10 in Hc. rewrite ?U_lit, ?U_SLit in Hc by lia. cbn in Hc. discriminate Hc. }
clear Hc.
(* 0x8655c .. 0x86564: a0 = b + 7, a1 = 8; stop at the trap branch 0x86568 *)
paj_run_tok RUN HS HJ SHOK Bspan; [hd4_awr v U2 HSTK|].
hd4_k v memc K HS HJ U2.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* the UBSan trap 0x86568, taken iff b + 7 <u 8: refuted by U52 (U of a0 = b + 7, with p + |rest| + 1 <= 2 ^ 63 from
     mf_loop's sa_addr) and 4096 <= bt <= p <= b (the text block bt of mf_loop_blk, al_blocks' 4096 lower bound) *)
  exfalso. rewrite branch_ltu_U, U52 in Hc. rewrite U_lit in Hc by lia. apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* the shadow entry of [b, b + 8) at the run's memory (m_file_sd.v mf_she_at: the text range addressable, mf_loop's
   sa_addr kept by hd4_line_keep; outside the shadow span, mf_txt_app) *)
pose proof (hd4_line_keep n v lyc Sc Wc memc mdc pos mcc cur line p rest _ _ HL HJ K) as HL1.
pose proof HL1 as (_ & _ & _ & _ & _ & _ & _ & LOOP1 & _).
pose proof LOOP1 as (_ & _ & _ & _ & (_ & _ & _ & PRA1 & _) & _).
clear SHOK.
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 52 0 8] E (mrestrict (w_H Wc) (ms_mem ms))).
{ unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (mf_she_at E Wc (ms_mem ms) 52 (p + Z.of_nat q1) 8 U32 E52 ltac:(lia) ltac:(lia)).
  - apply (range_addressable_sub _ SHADOW_OFF p (Z.of_nat (length rest) + 1) (p + Z.of_nat q1) 8 PRA1); lia.
  - intros x Hx. apply (mf_txt_app B v Wc (ms_mem ms) mcc cur line p rest CX LOOP1). lia. }
clear HL1 LOOP1 PRA1.
(* the fact on atom 52 (b in [4096, 2 ^ 47 - 8], mf_txt_region), then 0x8656c .. 0x86580: the check of b[7]
   (shadow entry mkSHE 52 0 8), `lbu a1,0(a0)`, `li a2,9`; stop at 0x86584 *)
apply (st_ok_pi_add_fact E _ _ 52 (mkAF 4096 (2 ^ 47 - 8) 0)) in HS; [|exact FT]. hd4_norm HS.
paj_run_tok RUN HS HJ SHOK Bspan; [hd4_awr v U2 HSTK|].
hd4_k v memc K HS HJ U2.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* 0x86584 `beq a1,a2` taken: b[7] = '\t' *)
  rewrite branch_eq_U in Hc. hd4_byte Hc b7 E54 Hb7r.
  rewrite U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  assert (HSP : sp_tab b7 = true) by (unfold sp_tab; rewrite Hc; reflexivity).
  clear Hc.
  (* 0x8658c .. 0x8659c: 192(s1) = b + 7, 184(s1) = be, a0 = s1 + 192, a1 = s1 + 184; stop at the jal 0x865a0 *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_J_STRIP2; [hd4_awr v U2 HSTK|].
  hd4_k v memc K HS HJ U2.
  pose proof (hd4_line_keep n v lyc Sc Wc memc mdc pos mcc cur line p rest _ _ HL HJ K) as HL'.
  hd4_slots v Wc p q1 r1 HS U2 E52 E53 V192 V184.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
  prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
  { apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
    - rewrite Q2. apply EE. reflexivity.
    - rewrite Q3. apply EE. reflexivity.
    - rewrite Q4. apply EE. reflexivity.
    - rewrite Q8. apply EE. reflexivity.
    - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
    - rewrite Q18, E32, R18. reflexivity.
    - rewrite Q23. apply EE. reflexivity.
    - rewrite Q24. apply EE. reflexivity.
    - rewrite Q19. apply EE. reflexivity.
    - rewrite Q22. apply EE. reflexivity.
    - rewrite Q25. apply EE. reflexivity. }
  pmkst HS. hd4_pc HDA_J_STRIP2.
  apply (hd4_jal n RS2 v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest i j HL' RA' HH HC H8 HIEQ HSP
    V192 V184).
  + rewrite Q10; rewrite ?ew_ewset_other by lia; rewrite U2. reflexivity.
  + rewrite Q11; rewrite ?ew_ewset_other by lia; rewrite U2. reflexivity.
  + rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
- (* 0x86584 not taken: b[7] <> '\t' *)
  rewrite branch_eq_U in Hc. hd4_byte Hc b7 E54 Hb7r.
  rewrite U_lit in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into H9.
  paj_run_tok RUN HS HJ SHOK Bspan; [hd4_awr v U2 HSTK|].
  hd4_k v memc K HS HJ U2.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* 0x86588 `bne a1,s5` taken: b[7] is neither '\t' nor ' ', m_header refuses (hd_ix_sp), to REF *)
    rewrite branch_ne_U in Hc. hd4_byte Hc b7 E54 Hb7r. hd4_s5 Hc EE R21.
    apply negb_true_iff, Z.eqb_neq in Hc.
    assert (HSP : sp_tab b7 = false)
      by (unfold sp_tab; apply orb_false_iff; split; apply Z.eqb_neq; lia).
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_REF; [hd4_awr v U2 HSTK|].
    hd4_k v memc K HS HJ U2.
    pose proof (hd4_line_keep n v lyc Sc Wc memc mdc pos mcc cur line p rest _ _ HL HJ K) as HL'.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
    prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
    prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
    assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
    { apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
      - rewrite Q2. apply EE. reflexivity.
      - rewrite Q3. apply EE. reflexivity.
      - rewrite Q4. apply EE. reflexivity.
      - rewrite Q8. apply EE. reflexivity.
      - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
      - rewrite Q18, E32, R18. reflexivity.
      - rewrite Q23. apply EE. reflexivity.
      - rewrite Q24. apply EE. reflexivity.
      - rewrite Q19. apply EE. reflexivity.
      - rewrite Q22. apply EE. reflexivity.
      - rewrite Q25. apply EE. reflexivity. }
    pmkst HS. hd4_pc HDA_REF.
    apply (REF v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest HL' RA').
    * rewrite <- HFIN, (hd_ix_sp rest i j ltac:(lia) HC mcc (line + 1) H8 HIEQ HSP). reflexivity.
    * rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
  + (* 0x86588 not taken: b[7] = ' ' *)
    rewrite branch_ne_U in Hc. hd4_byte Hc b7 E54 Hb7r. hd4_s5 Hc EE R21.
    apply negb_false_iff, Z.eqb_eq in Hc.
    assert (HSP : sp_tab b7 = true) by (unfold sp_tab; rewrite Hc; reflexivity).
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_J_STRIP2; [hd4_awr v U2 HSTK|].
    hd4_k v memc K HS HJ U2.
    pose proof (hd4_line_keep n v lyc Sc Wc memc mdc pos mcc cur line p rest _ _ HL HJ K) as HL'.
    hd4_slots v Wc p q1 r1 HS U2 E52 E53 V192 V184.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
    prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
    prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
    prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
    assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
    { apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
      - rewrite Q2. apply EE. reflexivity.
      - rewrite Q3. apply EE. reflexivity.
      - rewrite Q4. apply EE. reflexivity.
      - rewrite Q8. apply EE. reflexivity.
      - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
      - rewrite Q18, E32, R18. reflexivity.
      - rewrite Q23. apply EE. reflexivity.
      - rewrite Q24. apply EE. reflexivity.
      - rewrite Q19. apply EE. reflexivity.
      - rewrite Q22. apply EE. reflexivity.
      - rewrite Q25. apply EE. reflexivity. }
    pmkst HS. hd4_pc HDA_J_STRIP2.
    apply (hd4_jal n RS2 v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest i j HL' RA' HH HC H8 HIEQ
      HSP V192 V184).
    * rewrite Q10; rewrite ?ew_ewset_other by lia; rewrite U2. reflexivity.
    * rewrite Q11; rewrite ?ew_ewset_other by lia; rewrite U2. reflexivity.
    * rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
Qed.
(* inside the Sections: the walk's Section hypotheses as its assumptions *)
About hda_rieq.
Print Assumptions hda_rieq.
End e.
End f.
End d.

About hda_rieq.
Print Assumptions hda_rieq.
