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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 207 of its 254 lines of code are new or changed and 406 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_HDRA: the walk of REF2 (0x8652c, the header's refusal after
   the header bytes' checks: be - b < 8, ieq "segment" false, b[7] not '\t' or ' ') to TAIL 0x86cf8:
     0x8652c `ld s5,128(s1)`       s5 = c (slot 128, atom 33)
     0x86530 `mv a0,s5; mv s6,s7; mv a1,s7`   a0 = c, s6 = a1 = line + 1
     0x8653c `jal m_refuse`        m_file_rf.v's mf_refuse_step (knock = false, mcl = mcc)
     0x86540 `sd zero,136(s1)`     cur := NULL
     0x86544 `ld s10,120(s1)`      s10 = shadow(FB) again (slot 120, atom 36): mf_regs_at holds again
     `j 0x86bdc; ld a7,144(s1); j 0x86cf8`   a7 := the next line's address, TAIL
   REF2 enters with hda_regs only (s10 borrowed by the header strip); the call needs only sp, gp, tp and s0. To the
   call: the seed with its slots read-only (m_file_s_hdra_w.v), one token run; no byte changes. After the call
   (hda13_cont, at the FP state the call returns): the seed with the slot region writable only at 136(s1), one token
   run to TAIL, the cut facts carried by m_file_k.v's mf_keep_run_s (136(s1) now holds NULL = cur None). The same
   shape as REF1's walk m_file_s_hdra_12.v. The HDRA segment lane of the G2 walk owner's G2. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_sd m_file_k
  m_file_mdl m_refuse_c m_file_rf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
m_file_s_hdra_t m_file_s_hdra_m m_file_s_hdra_e m_file_s_hdra_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the `jal m_refuse` of REF2 *)
Definition hda13_j : Z := AF_m_file + 0x680.   (* 0x8653c *)

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
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

(* 0x86540 .. TAIL: the state m_refuse returns, the block holding the refusal's model mcc, the line done (line, the
   next line's text rest at p); 136(s1) still holds the line's cur; s10 any (hda_regs) *)
Lemma hda13_cont : forall n, MF_TAIL_stmt B n ->
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_cur_ok mcc cur ->
mf_np v memc Wc p -> hda_regs B v lyc pos regs1 ->
(length rest < n)%nat -> mf_loop v Wc memc mcc None line p rest ->
fst (m_lines (mcc, None) line (lines rest)) = mf_final v ->
getr regs1 21 = w64 (mv_c v) -> getr regs1 22 = w64 line ->
mf_at B v Wc regs1 memc mdc (hda13_j + 4).
Proof.
intros n TL v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CX LS FRM CORE CELLS HCUR NP RG Hn LOOP HFIN
  R21 R22.
pose proof RG as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R24).
(* where things lie *)
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
destruct (mf_s1_facts B v CX) as (HS1 & _ & _).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
pose proof asan_consts as (C1 & _).
destruct (mf_c_entry B v CX) as (bc & mbc & _ & Hbc1 & Hbc2 & Hbc3 & Hbc4 & _).
unfold seg_spec.SEG_M_SIZE in Hbc2.
pose proof CORE as (HJ & _ & _ & VSH & _ & _ & HMC & _).
pose proof HJ as (HARc & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HARc Hfin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFceil.
pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)) as HF8a.
pose proof (Z.div_le_upper_bound (frame_addr lyc 1 pos) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as HF8b.
pose proof LOOP as (_ & _ & _ & _ & (Hp0 & Hp1 & _) & _).
(* the seed at 0x86540, the slot region writable only at 136(s1) *)
assert (RB : mf_regs_base v regs1) by (repeat split; assumption).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE HCUR) as Hcur.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur p [] (hda13_j + 4)
  true true [] false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) ltac:(lia)
  ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
pose proof (hda_E32 regs1 v lyc pos cur p []) as E32.
pose proof (mfE_extra regs1 v lyc pos cur p [] 4 ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E36.
pose proof (mfE_extra regs1 v lyc pos cur p [] 6 ltac:(unfold A_TEXT; lia)) as E38.
cbn [Nat.add nth mf_extra map app] in E38.
set (E := mfE regs1 v lyc pos cur p []) in HS0, E32, E36, E38.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
assert (EE : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew E k0 = getr regs1 r0)
  by (intros k0 r0 Hk; subst E; apply mfE_reg; exact Hk).
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v)).
{ rewrite (EE 2%nat 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
pose proof (st_ok_pi_region_nth E _ _ 1 (mf_r_slots true true []) HS0 eq_refl) as ROK0.
assert (ROK : region_ok SEGS E
  (ms_mem (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + (hda13_j + 4))) memc (seg_rom SEGS))))
  (set_window (mf_r_slots true true []) 136 144)).
{ apply region_ok_rewindow; [exact ROK0|].
  destruct ROK0 as (_ & _ & Hw & _). intros o0 Ho0. apply Hw. cbn. lia. }
pose proof (ast_ok_pi_set_region E _ _ 1 (mf_r_slots true true []) (set_window (mf_r_slots true true []) 136 144)
  HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity) ROK) as HS.
clear HS0 ROK ROK0.
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let s := eval vm_compute in ss in change ss with s in HS end.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
unfold mf_at.
(* `sd zero,136(s1)`, `ld s10,120(s1)`, `j 0x86bdc`, `ld a7,144(s1)`, `j 0x86cf8` *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_TAIL;
[ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat (mf_s1 (mv_sp v) - mv_sp v));
  [ reflexivity | rewrite U2; lia | cbn [YP09.r_wlo]; rewrite HSTK; lia | cbn [YP09.r_whi]; lia |];
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]);
  apply awr_ok_nil
| ].
pmkst HS.
(* every byte but 136(s1) .. 143(s1) is kept *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 136 <= a < mf_s1 (mv_sp v) + 144) ->
  rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha HnR.
  refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms)
    (fun x => mf_s1 (mv_sp v) + 136 <= x < mf_s1 (mv_sp v) + 144) HFr _ a Ha HnR).
  intros b wlo whi x Hin Hr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; try rewrite U2 in Hr; lia |]).
  destruct Hin. }
(* 136(s1) holds NULL *)
assert (V136 : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (mf_s1 (mv_sp v) + 136) 8 (mf_cur_ptr (mv_c v) None)).
{ pose proof (st_ok_pi_region_nth E _ _ 1 _ HS eq_refl) as HR1. cbn [restrict ms_mem] in HR1.
  pose proof (field_of_region E _ 2%nat (mf_s1 (mv_sp v)) _ 24 160 136 144 136 8%N (SLit 0) 0 HR1 U2
    ltac:(cbn; left; reflexivity)) as V.
  apply V.
  - reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia. }
set (RW := fun a : Z => mf_s1 (mv_sp v) + 136 <= a < mf_s1 (mv_sp v) + 144).
assert (RWok : forall a, RW a -> mf_rw v lyc pos a).
{ intros a Ha. unfold RW in Ha. unfold mf_rw. right; right; right; right; right. lia. }
assert (RWS : mf_rws v RW).
{ unfold mf_rws. intros a Ha _. unfold RW in Ha. right. lia. }
assert (VSH' : forall i, 4 <= i < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 MF_LOW_OFF).
{ intros i Hi. apply (mf_val_keep Wc Wc memc (ms_mem ms) RW _ 1 _ K1); [| | | exact (VSH i Hi)].
  - unfold SHADOW_OFF. lia.
  - change (Z.of_nat 1) with 1. unfold SHADOW_OFF. lia.
  - intros k Hk HR. change (Z.of_nat 1) with 1 in Hk. unfold RW in HR. unfold SHADOW_OFF in HR. lia. }
assert (MC1 : sa_mconf (rdW Wc (ms_mem ms)) (mv_c v) mcc).
{ apply (mf_mconf_keep Wc Wc memc (ms_mem ms) RW (mv_c v) _ K1); [lia | unfold seg_spec.SEG_M_SIZE; lia | | exact HMC].
  intros a Ha HR. unfold RW in HR. unfold seg_spec.SEG_M_SIZE in Ha. lia. }
destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur (ms_mem ms) _ RW MF_LOW_OFF None mcc
  CX CORE CELLS HJ K1 RWok RWS VSH' V136 MC1) as (CORE_T & CELLS_T & LOOPK).
(* the registers at TAIL: hda_regs kept, s10 = shadow(FB) from 120(s1), so mf_regs_at again *)
assert (HRm : hda_regs B v lyc pos (ms_regs ms)) by (hda_regs_carry HS EE E32 RG).
assert (Q26 : getr (ms_regs ms) 26 = w64 (SHADOW_OFF + frame_addr lyc 1 pos / 8)).
{ prreg HS (26%bv : bv 5) Q. rewrite Q, E36. reflexivity. }
assert (RAT : mf_regs_at B v lyc pos (ms_regs ms)).
{ destruct HRm as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & X25 & _). unfold mf_regs_at. repeat split; assumption. }
(* TAIL *)
apply (TL v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc None line p rest CX LS FRM CORE_T CELLS_T RAT).
- hda_rg HS EE 24%nat (24%bv : bv 5). exact R24.
- exact Hn.
- exact (LOOPK mcc None line p rest LOOP).
- exact HFIN.
- prreg HS (17%bv : bv 5) Q17. rewrite Q17, E38. reflexivity.
- hda_rg HS EE 21%nat (21%bv : bv 5). exact R21.
- hda_rg HS EE 22%nat (22%bv : bv 5). exact R22.
Qed.
End e.
End f.
End d.

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
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstA.STK_m_refuse SegInstA.RLO_A SegInstA.RHI_A SegInstA.seg_litA_fz SegInstA.gotwA SegInstA.guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

Lemma hda_ref2 : forall n, MF_TAIL_F B n -> HDA_REF2_stmt B n.
Proof.
intros n TL. unfold HDA_REF2_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest HL HR HFIN R23.
pose proof HL as (CX & LS & FRM & CORE & CELLS & Hlen & Hne & LOOP & NP).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R24).
assert (RB : mf_regs_base v regs1) by (repeat split; assumption).
pose proof LOOP as (_ & _ & _ & _ & _ & HCOK & LK0 & _).
(* the seed at REF2, the slots read-only *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [] HDA_REF2
  true true [] false false [] false CX CORE RB (fun _ => CELLS) (mf_cur_range B _ _ _ _ _ _ _ _ _ _ CX CORE HCOK)
  (fun _ => NP) (hda_np64 _ _ _ _ _ _ _ _ LOOP) ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
pose proof (hda_ro_slots _ _ _ _ _ _ _ _ _ _ _ HS0 ltac:(vm_compute; reflexivity)) as HS. clear HS0.
pose proof CORE as (HJ & _).
pose proof (mfE_extra regs1 v lyc pos cur (mf_next p rest) [] 1 ltac:(unfold A_TEXT; lia)) as E33.
cbn [Nat.add nth mf_extra map app] in E33.
set (E := mfE regs1 v lyc pos cur (mf_next p rest) []) in HS, E33.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
assert (EE : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew E k0 = getr regs1 r0)
  by (intros k0 r0 Hk; subst E; apply mfE_reg; exact Hk).
pose proof (hda_E32 regs1 v lyc pos cur (mf_next p rest) []) as E32. fold E in E32.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
unfold mf_at.
(* `ld s5,128(s1); mv a0,s5; mv s6,s7; mv a1,s7` up to the `jal` *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan hda13_j; [hda_awr_ro|].
pose proof (hda_frame_ro E _ (w_H Wc) memc (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
pose proof (hda_line_carry B n v lyc Sc Wc memc mdc (ms_mem ms) _ pos mcc cur line p rest HL HJ KA) as HL'.
pmkst HS.
assert (HRm : hda_regs B v lyc pos (ms_regs ms)) by (hda_regs_carry HS EE E32 HR).
assert (R21' : getr (ms_regs ms) 21 = w64 (mv_c v)).
{ prreg HS (21%bv : bv 5) Q21. rewrite Q21, E33. reflexivity. }
assert (R22' : getr (ms_regs ms) 22 = w64 (line + 1)).
{ prreg HS (22%bv : bv 5) Q22. rewrite Q22, (EE 23%nat 23%bv eq_refl). exact R23. }
assert (R10' : getr (ms_regs ms) 10 = w64 (mv_c v)).
{ prreg HS (10%bv : bv 5) Q10. rewrite Q10, E33. reflexivity. }
assert (R11' : getr (ms_regs ms) 11 = w64 (line + 1)).
{ prreg HS (11%bv : bv 5) Q11. rewrite Q11, (EE 23%nat 23%bv eq_refl). exact R23. }
pose proof HL' as (_ & _ & _ & CORE' & CELLS' & _ & _ & LOOP' & NP').
pose proof HRm as (P2 & P3 & P4 & P8 & _).
(* m_refuse (c, line + 1) *)
apply (mf_refuse_step B SIGP SSP RELRO M_REFUSE v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos MF_LOW_OFF mcc mcc false
  cur line p rest (mf_next p rest) hda13_j CX LS FRM (mf_corek_of_core B _ _ _ _ _ _ _ _ _ CORE') CELLS' NP'
  P2 P3 P4 P8 LOOP' Hne eq_refl LK0 ltac:(vm_compute; reflexivity) ltac:(unfold hda13_j, AF_m_file; lia) R10' R11'
  (mf_kept_le_refuse mcc (line + 1) false None (line + 1) (lines (mf_rest rest)) (mf_final v) I HFIN)).
intros fx1 ly2 S2 W2 regs2 mem2 md2 Hrel LS2 CORE2 CELLS2 NP2 LOOP2 HKS.
pose proof (m_refuse_sizes mcc (line + 1) false) as (_ & HKL).
assert (LOOPn : mf_loop v W2 mem2 (m_refuse mcc (line + 1) false) None (line + 1) (mf_next p rest) (mf_rest rest)).
{ apply (mf_loop_next v W2 mem2 mcc cur line p rest (m_refuse mcc (line + 1) false) None LOOP2 Hne).
  - unfold m_refuse. cbn [mc_refused]. lia.
  - unfold m_refuse. cbn [mc_overflow]. lia.
  - lia.
  - exact I. }
pose proof LS as (Ely & _). pose proof LS2 as (Ely2 & _).
pose proof HRm as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & X25 & X24).
assert (RG2 : hda_regs B v ly2 pos regs2).
{ unfold hda_regs. rewrite Ely2, <- Ely.
  split; [transitivity (getr (ms_regs ms) 2); [exact (HKS 2 ltac:(unfold acallee_saved; lia)) | exact X2]|].
  split; [transitivity (getr (ms_regs ms) 3); [exact (HKS 3 ltac:(unfold acallee_saved; lia)) | exact X3]|].
  split; [transitivity (getr (ms_regs ms) 4); [exact (HKS 4 ltac:(unfold acallee_saved; lia)) | exact X4]|].
  split; [transitivity (getr (ms_regs ms) 8); [exact (HKS 8 ltac:(unfold acallee_saved; lia)) | exact X8]|].
  split; [transitivity (getr (ms_regs ms) 9); [exact (HKS 9 ltac:(unfold acallee_saved; lia)) | exact X9]|].
  split; [transitivity (getr (ms_regs ms) 18); [exact (HKS 18 ltac:(unfold acallee_saved; lia)) | exact X18]|].
  split; [transitivity (getr (ms_regs ms) 19); [exact (HKS 19 ltac:(unfold acallee_saved; lia)) | exact X19]|].
  split; [transitivity (getr (ms_regs ms) 25); [exact (HKS 25 ltac:(unfold acallee_saved; lia)) | exact X25]|].
  transitivity (getr (ms_regs ms) 24); [exact (HKS 24 ltac:(unfold acallee_saved; lia)) | exact X24]. }
assert (K21 : getr regs2 21 = getr (ms_regs ms) 21) by exact (HKS 21 ltac:(unfold acallee_saved; lia)).
assert (K22 : getr regs2 22 = getr (ms_regs ms) 22) by exact (HKS 22 ltac:(unfold acallee_saved; lia)).
assert (Hn' : (length (mf_rest rest) < n)%nat).
{ destruct (mf_break_snd rest) as (_ & HB2 & _). specialize (HB2 Hne). unfold mf_rest. lia. }
exact (hda13_cont (fx := fx1) B VOBJS n (TL fx1) v ly2 S2 W2 regs2 mem2 md2 pos (m_refuse mcc (line + 1) false) cur
  (line + 1) (mf_next p rest) (mf_rest rest) CX LS2 (PaFx.fxrel_frm0 fx fx1 FRM Hrel) CORE2 CELLS2
  (mf_cur_ok_refuse mcc cur (line + 1) false HCOK) NP2 RG2 Hn' LOOPn HFIN
  ltac:(rewrite K21; exact R21') ltac:(rewrite K22; exact R22')).
Qed.
End e.
End f.
End d.
