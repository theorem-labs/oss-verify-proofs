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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 184 of its 225 lines of code are new or changed and 412 lines of the source are left out. *)
(* reac_segconf_parse_file (image B, 0x87e38), segment B10a: the first two runs. P0 = ROLE 0x88630-0x8864c (low's
   eight shadow cells in scope, a plain run: b10_role_ok : B10_P1_stmt n -> H_ROLE n) and P1 = 0x88650-0x88670 with
   the slow arm 0x88fb4-0x88fbc / error call 0x89280 (val from slot 0x70, check B#16 covered by val's shadow entry,
   val[0], `beqz`: b10_p1_ok : B10_EXIT_stmt n -> (forall k, B10_LOOP_k n k) -> B10_P1_stmt n). The B10a segment lane of
   the image-B G3 walk owner, 2026-10-30; ADAPTED from the image-A G3 walk owner's image-A kit lib/A/Prog/pf_a10a_k.v (commit
   73bafa8e5cd9) and the image-A G3 walk owner's lib/A/Prog/pf_a2.v (the plain run that writes the frame's shadow
   cells, read back with pa2_cell_of_region's form), re-derived on image B's code. No trap site lies in P0 or P1. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegGlob SegInstB
  refuse_c reac_segconf_parse_file_c pf_pieces trim_k pf_seg_B10a_k pf_seg_B10a_s pf_seg_B10a_x.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the awr obligation of a run whose regions are all read-only *)
Ltac b10_awr0 :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* after a run of b10_ss1 that writes nothing: the memory is memc *)
Ltac b10_after0 memc KSp KSname msname :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo ?rs (mrestrict ?Hh ?m0) (mrestrict _ (ms_mem ?msn)) |- _ =>
    assert (KSname : forall a, 0 <= a < 2 ^ 64 -> aview SEGS Hh (ms_mem msn) a = aview SEGS Hh memc a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          rewrite (kept_of_frame (segs := SEGS) Eo rs Hh m0 (ms_mem msn) (fun _ => False) HFr);
          [ exact (KSp a Ha)
          | let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
            intros b wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (let Hq := fresh "Hq" in
                    destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
            destruct Hin
          | exact Ha | tauto ]);
    clear KSp;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
    rename msn into msname
  end.

Lemma b10_p1_ok : forall n, B10_EXIT_stmt B n -> (forall k, B10_LOOP_k B n k) -> B10_P1_stmt B n.
Proof.
intros n HEXIT HLOOP. unfold B10_P1_stmt, b10_at.
intros v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc HM.
pose proof (b10_mid_facts B LAWS n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc _ HM)
  as (R9 & R20 & R26 & Hs1 & Hs1e & W70 & W30 & WA0 & NZ & VB & VR & Hb1 & Hb2 & F4096 & F47 & Fc & Fapp &
      RAV & RAL & Fp & HFA & Hin & NSB).
pose proof HM as (HKV & Hrole & HJ & KM & Z0 & LW & Hkl & Hk63 & HK).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (b10_r_low64_len val NZ) as RLL.
unfold PF_O_BUF in Hb1, Hb2.
set (c0 := nth 0 val 0) in *.
assert (Hc0 : 0 <= c0 < 256).
{ destruct val as [|x r]; [unfold c0; cbn; lia|]. exact (VR 0%nat ltac:(cbn; lia)). }
assert (V0 : rdW Wc memc vp = Some c0) by (pose proof (VB 0%nat ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X).
pose proof (b10_entry1 Wc regs1 memc (pf_s1 v) vp c0 R9 R20 W70 V0 Hc0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 [w64 vp; Z_to_bv 64 c0]))) by apply Eimg_env.
assert (HA0 : env_agree 32 (Ereg regs1 [w64 vp; Z_to_bv 64 c0]) (Eimg (Ereg regs1 [w64 vp; Z_to_bv 64 c0])))
  by (split; [intros n0 Hn0; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (E20 : ew (Eimg (Ereg regs1 [w64 vp; Z_to_bv 64 c0])) 20 = Z_to_bv 64 SB)
  by (rewrite (ew_Eimg_Ereg_nat regs1 _ 20 (Z_to_bv 5 20) eq_refl); exact R20).
assert (E32 : ew (Eimg (Ereg regs1 [w64 vp; Z_to_bv 64 c0])) 32 = Z_to_bv 64 vp)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew (Eimg (Ereg regs1 [w64 vp; Z_to_bv 64 c0])) 33 = Z_to_bv 64 c0)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
revert HS HEI HA0 E20 E32 E33. generalize (Eimg (Ereg regs1 [w64 vp; Z_to_bv 64 c0])) as E0.
intros E0 HS HEI HA0 E20 E32 E33.
assert (UB : U E0 b10_Bx = SHADOW_OFF) by (unfold b10_Bx; rewrite (U_atom E0 20 SB E20) by (unfold SB; lia); reflexivity).
assert (SHOK : sh_ok SEGS b10_Bx b10_SH1 E0 (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, b10_SH1. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E0 b10_Bx 32%nat vp (Z.of_nat (length val) + 1) vp 0 1 RAV UB
    ltac:(apply U_atom; [exact E32 | lia])); [lia | lia |].
  intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx. apply NSB. lia. }
assert (KS0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
(* 0x88650 .. 0x88668: val, check B#16 (covered), val[0], up to `beqz a2` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ b10_awr0. }
b10_after0 memc KS0 KS1 ms1.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* val[0] = 0: val is empty; EXIT with a3 = 0 (0x888bc) *)
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    pose proof (b10_br_eq_lit En 33 c0 0 true (b10_ag_ew E0 En 40 33 _ ltac:(env_agree_chain (env_agree_refl 40 E0)) ltac:(lia) E33)
      ltac:(lia) ltac:(lia) Hc) as Hz end.
  apply Z.eqb_eq in Hz. clear Hc.
  assert (HL : length val = 0%nat).
  { destruct val as [|x r]; [reflexivity|]. exfalso. apply NZ. left. exact Hz. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B10_EXIT.
  { b10_awr0. }
  b10_after0 memc KS1 KS2 ms2.
  lazymatch goal with HS' : st_ok_pi _ _ ?En _ _ |- _ =>
    assert (HAE : env_agree 40 E0 En) by (env_agree_chain (env_agree_refl 40 E0)) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ B10_KZb HS (b10_ag32 _ _ _ _ 40 ltac:(lia) HA0 HAE)
    ltac:(vm_compute; reflexivity)) as HKb.
  cbn [ms_regs restrict] in HKb.
  b10_reg HS (Z_to_bv 5 13) N13.
  pmkst HS.
  assert (RL : length (r_low val 0 64) = 0%nat) by (rewrite RLL; lia).
  apply (HEXIT v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val (ms_regs ms2) (ms_mem ms2) _).
  + rewrite RL.
    exact (b10_mid_step B LAWS n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc 0
      (ms_regs ms2) (ms_mem ms2) _ 0 HM HJ (fun a Ha _ => KS2 a Ha) (or_introl eq_refl) Hkl Hk63 (b10_kz_of _ _ HKb)).
  + rewrite RL, N13. reflexivity.
- (* val[0] <> 0: LOOP with li = 0 (0x8866c `li a6,0`, 0x88670 `addi a1,a0,1`) *)
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    pose proof (b10_br_eq_lit En 33 c0 0 false (b10_ag_ew E0 En 40 33 _ ltac:(env_agree_chain (env_agree_refl 40 E0)) ltac:(lia) E33)
      ltac:(lia) ltac:(lia) Hc) as Hz end.
  apply Z.eqb_neq in Hz. clear Hc.
  assert (HL : (0 < length val)%nat) by (destruct val as [|x r]; [exfalso; apply Hz; reflexivity | cbn; lia]).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B10_LOOP.
  { b10_awr0. }
  b10_after0 memc KS1 KS2 ms2.
  lazymatch goal with HS' : st_ok_pi _ _ ?En _ _ |- _ =>
    assert (HAE : env_agree 40 E0 En) by (env_agree_chain (env_agree_refl 40 E0)) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ B10_KZb HS (b10_ag32 _ _ _ _ 40 ltac:(lia) HA0 HAE)
    ltac:(vm_compute; reflexivity)) as HKb.
  cbn [ms_regs restrict] in HKb.
  b10_reg HS (Z_to_bv 5 10) N10. b10_reg HS (Z_to_bv 5 11) N11.
  b10_reg HS (Z_to_bv 5 12) N12. b10_reg HS (Z_to_bv 5 16) N16.
  pmkst HS.
  apply (HLOOP 0%nat v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val (ms_regs ms2) (ms_mem ms2) _).
  + exact (b10_mid_step B LAWS n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc 0
      (ms_regs ms2) (ms_mem ms2) _ 0 HM HJ (fun a Ha _ => KS2 a Ha) (or_introl eq_refl) Hkl Hk63 (b10_kz_of _ _ HKb)).
  + exact HL.
  + rewrite (b10_reg_atom _ _ _ 32 0 vp N10 (b10_ag_ew E0 _ 40 32 _ HAE ltac:(lia) E32) ltac:(lia)).
    f_equal. lia.
  + rewrite (b10_reg_atom _ _ _ 32 1 vp N11 (b10_ag_ew E0 _ 40 32 _ HAE ltac:(lia) E32) ltac:(lia)).
    reflexivity.
  + rewrite (b10_reg_atom _ _ _ 33 0 c0 N12 (b10_ag_ew E0 _ 40 33 _ HAE ltac:(lia) E33) ltac:(lia)).
    f_equal. unfold c0. lia.
  + rewrite N16. reflexivity.
Qed.

(* the cells P0 writes: SH + 80 .. SH + 87, each the byte 0 (the chunks of the run's one region, in the
   executor's order) *)
Definition B10_P0_CS : list YP09.chunk :=
  [YP09.mkChunk 83 (CVal 1 (SLit 0)); YP09.mkChunk 82 (CVal 1 (SLit 0)); YP09.mkChunk 81 (CVal 1 (SLit 0));
   YP09.mkChunk 80 (CVal 1 (SLit 0)); YP09.mkChunk 87 (CVal 1 (SLit 0)); YP09.mkChunk 86 (CVal 1 (SLit 0));
   YP09.mkChunk 85 (CVal 1 (SLit 0)); YP09.mkChunk 84 (CVal 1 (SLit 0))].
Lemma b10_p0_chunks : forall od, 80 <= od < 88 -> In (YP09.mkChunk od (CVal 1 (SLit 0))) B10_P0_CS.
Proof.
intros od Hod.
assert (H : od = 80 \/ od = 81 \/ od = 82 \/ od = 83 \/ od = 84 \/ od = 85 \/ od = 86 \/ od = 87) by lia.
unfold B10_P0_CS.
repeat (destruct H as [-> | H]; [cbn [In]; repeat (first [left; reflexivity | right]) |]).
subst od. cbn [In]. repeat (first [left; reflexivity | right]).
Qed.

Lemma b10_role_ok : forall n, B10_P1_stmt B n -> H_ROLE B n.
Proof.
intros n HP1. unfold H_ROLE.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val HKV Hrole.
pose proof (b10_geo B LAWS n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val HKV)
  as (Gsp & Gsp47 & Gs1 & Gs32 & F32 & Fapp & Foff & F4096 & Fc & F47).
pose proof HKV as ((HCX & HFI & _) & _ & _ & _ & _ & HRG).
pose proof HFI as (HJ & Hly & _ & _ & _ & _ & _ & _ & _ & HRG0).
destruct (b10_frame B LAWS v pos lyc Sc Wc memc mdc HJ Hly) as (Hin & _ & _ & _ & _ & _ & _ & _ & Fsh & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (R21 : getr rX (Z_to_bv 5 21) = w64 (pf_SH v pos)) by (apply (b10_rg_in rX _ 21 _ HRG); b10_in).
assert (HSH : 0 <= pf_SH v pos /\ pf_SH v pos + 256 <= 2 ^ 64).
{ unfold pf_SH, shadow_addr, SHADOW_OFF. pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)). unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp. lia. }
assert (HPS : forall i, 0 <= i < 8 -> apresent (w_H Wc) memc (pf_SH v pos + 80 + i)).
{ intros i Hi. replace (pf_SH v pos + 80 + i) with (pf_SH v pos + (80 + i)) by lia. apply Fsh. lia. }
pose proof (b10_entry0 Wc rX memc (pf_SH v pos) R21 ltac:(lia) ltac:(lia) HPS) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX []))) by apply Eimg_env.
assert (HA0 : env_agree 32 (Ereg rX []) (Eimg (Ereg rX [])))
  by (split; [intros n0 Hn0; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (U21 : bv_unsigned (ew (Eimg (Ereg rX [])) 21) = pf_SH v pos)
  by (rewrite (ew_Eimg_Ereg_nat rX _ 21 (Z_to_bv 5 21) eq_refl), R21; apply unsigned_lit_small; lia).
unfold cfg_at.
(* 0x88630 .. 0x8864c: low's eight shadow cells in scope; a plain run to 0x88650 *)
paj_run_to_sh RUNTOP HS HJ B10_P1.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  eapply awr_ok_cons_gen with (n := 21%nat); [reflexivity | exact U21 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
  exists 5, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
  change (fs_frame_bytes 5 / 8) with 256. unfold pf_SH, pf_F in Ha. rewrite Hly. lia. }
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
(* the bytes the run kept: all but low's eight cells *)
assert (KS : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_SH v pos + 80 <= a < pf_SH v pos + 88) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hne.
  apply (kept_of_frame (segs := SEGS) (Eimg (Ereg rX [])) _ (w_H Wc) memc (ms_mem ms)
    (fun a' => pf_SH v pos + 80 <= a' < pf_SH v pos + 88) HFr); [|exact Ha | exact Hne].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  destruct Hin' as [Hq | []]; injection Hq as <- <- <-; cbn [base_val] in Hrr. rewrite U21 in Hrr. lia. }
(* the cells it wrote *)
assert (Z0 : forall i, 0 <= i < 8 -> rdW Wc (ms_mem ms) (pf_SH v pos + 80 + i) = Some 0).
{ intros i Hi.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx _ =>
    assert (HN : nth_error (ss_mem ssx) 0 = Some (YP09.mkRegion (Some 21%nat) 80 88 80 88 B10_P0_CS))
      by (vm_compute; reflexivity);
    pose proof (b10_rbyte Ex ssx ms (w_H Wc) 21%nat 0%nat 80 88 80 88 B10_P0_CS (80 + i) (SLit 0) (pf_SH v pos) HS
      HN (b10_p0_chunks (80 + i) ltac:(lia)) U21) as V end.
  replace (pf_SH v pos + 80 + i) with (pf_SH v pos + (80 + i)) by lia. rewrite V, U_SLit. reflexivity. }
pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ B10_KZb HS HA0 ltac:(vm_compute; reflexivity)) as HKb.
cbn [ms_regs restrict] in HKb.
pmkst HS.
apply (HP1 v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val (ms_regs ms) (ms_mem ms) mdv).
exact (b10_mid_init B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val (ms_regs ms) (ms_mem ms) mdv
  HKV Hrole HJ KS Z0 (b10_kz_of _ _ HKb)).
Qed.
End e.
End f.
End d.
