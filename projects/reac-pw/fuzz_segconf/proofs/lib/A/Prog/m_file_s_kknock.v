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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 494 of its 542 lines of code are new or changed and 405 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc): segment S_MF_KKNOCKP of its walk (KKNOCK 0x86b20 -> KDONE
   0x86cd0; the G2 walk owner's guide/MF-CUTS-A.md sections 2 and 4). The LONGP / KKNOCKP segment lane of the G2 walk owner's G2.
   The segment is cut at KK_HIT 0x86b38 and KK_MISS 0x86be4 (lib/A/Prog/m_file_s_kknock_d.v):
   lib/A/Prog/m_file_s_kknock_h.v proves KK_HITX from KDONE (the store kept_knock[n_kept] = 1 and m_refuse 0x86ccc);
   this file proves the rest and closes the segment:
   - kk_knock (KKNOCK -> KK_HIT / KK_MISS): 0x86b20 auipc / addi a2 = "knock" (listing object 25), a0 = s11 = k,
     a1 = s6 = kl, the call 0x86b30 `jal ieq` (m_file_iq.v's mf_ieq_call), then 0x86b34 `beqz a0`: ieq's answer 1
     falls to KK_HIT, 0 goes to KK_MISS. The K cut's model mk_disp with "role", "model", "ignore" missed is
     m_refuse mcc (line + 1) (ieq k "knock") (kk_disp).
   - kk_miss (KK_MISS -> KDONE): 0x86be4 s5 = 128(s1) = c, a0 = s5, s6 = s8 = line + 1, a1 = s8, the call 0x86bf4
     `jal m_refuse` (m_file_rf.v's mf_refuse_step, knock false), then kk_aft at the returned FP state.
   - kk_aft (0x86bf8 -> KDONE): 0x86bf8 `j 0x86a3c`, 0x86a3c s8 = 104(s1) = FAKE, 0x86a40 `j` KDONE.
   The runs use m_file_sd.v's mf_seed with its spill slots read-only (they store nothing); the ieq call's set-up
   drops the seed's regions (as m_file_s_kign_1.v's ki_s_kign, the KIGNP segment lane, whose helpers kk_st_reg,
   kk_slice_facts, kk_pres, kk_bytes_of_zs are copied here).
   - s_mf_kknockp : S_MF_KKNOCKP B, from kk_knock, m_file_s_kknock_h.v's kk_hit and kk_miss at every FP state.
   Section hypotheses, from the shared list of m_file_m.v change 3, verbatim: VOBJS, SIGP, SSP, RELRO, IEQ
   (ieq_contract), M_REFUSE (m_refuse_contract). Closed against G2 FINAL at 6f783602b5e3. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_refuse_c ieq_c m_file_c m_file_m m_file_sd m_file_k m_file_mdl m_file_rf
  m_file_iq m_file_s_kknock_d m_file_s_kknock_h.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* every region of the state is read-only: a run from it writes nothing (check_reply_s7.v cr7_awr) *)
Ltac mf_awr_ro :=
lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
  let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* the state's form, computed *)
Ltac mf_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.


(* every region of the state is read-only: a run from it writes nothing (check_reply_s7.v cr7_awr) *)
Ltac kk_awr_ro :=
lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
  let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* the state's form, computed *)
Ltac kk_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.

Definition KK_AFT : Z := AF_m_file + 0xd3c.    (* 0x86bf8, the unknown key's m_refuse returns here *)
Definition KK_RJAL : Z := AF_m_file + 0xd38.   (* 0x86bf4 `jal m_refuse` *)
Definition KK_IJAL : Z := AF_m_file + 0xc74.   (* 0x86b30 `jal ieq` *)
Definition KK_IRET : Z := AF_m_file + 0xc78.   (* 0x86b34, ieq returns here *)

(* the K cut's model with "role", "model", "ignore" missed *)
Lemma kk_disp : forall c gi k v line, ieq k S_role = false -> ieq k S_model = false -> ieq k S_ignore = false ->
  mk_disp c gi k v line = m_refuse c line (ieq k S_knock).
Proof.
intros c gi k v line E1 E2 E3. unfold mk_disp. rewrite E1, E2, E3. destruct (ieq k S_knock); reflexivity.
Qed.


(* ============== bytes of the text (m_file_s_kign_t.v ki_line_le .. ki_bytes_of_zs, the KIGNP segment lane) ============== *)
Lemma kk_line_le : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
unfold mf_line. induction rest as [|b r IH]; cbn [break_nl]; [cbn; lia|].
destruct (b =? NL); [cbn; lia|]. destruct (break_nl r) as [l q] eqn:E. cbn [fst] in IH |- *. cbn [length]. lia.
Qed.
Lemma kk_aview_byte : forall segs H mem a v, aview segs H mem a = Some v -> 0 <= v < 256.
Proof.
intros segs H mem a v E. unfold aview in E.
destruct (mbyte segs (mrestrict H mem) a) as [b|]; [|discriminate]. cbn in E. injection E as <-.
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.
Lemma kk_zs_zb : forall l, Forall (fun z => 0 <= z < 256) l -> seg_spec.zs (seg_spec.zb l) = l.
Proof.
induction l as [|x r IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H as [Hx Hr].
unfold seg_spec.zs, seg_spec.zb in *. cbn [map]. rewrite IH by exact Hr. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hx.
Qed.
Lemma kk_bytes_of_zs : forall segs H mem a (l : list Z), sa_zs (aview segs H mem) a l ->
  sa_bytes (aview segs H mem) a (seg_spec.zb l) /\ seg_spec.zs (seg_spec.zb l) = l /\
  Forall (fun z => 0 <= z < 256) l.
Proof.
intros segs H mem a l HZ.
assert (HR : Forall (fun z => 0 <= z < 256) l).
{ apply Forall_forall. intros z Hz. apply In_nth with (d := 0) in Hz as (i & Hi & <-).
  exact (kk_aview_byte segs H mem _ _ (HZ i Hi)). }
split; [|split; [exact (kk_zs_zb l HR) | exact HR]].
intros i Hi. unfold seg_spec.zb in Hi. rewrite length_map in Hi. rewrite (HZ i Hi). f_equal.
unfold seg_spec.zb. rewrite (nth_indep _ ZB0 (Z_to_bv 8 0)) by (rewrite length_map; exact Hi).
rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
symmetry. apply Z.mod_small. exact (proj1 (Forall_forall _ _) HR _ (nth_In _ _ Hi)).
Qed.

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
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* 0x86bf8 -> KDONE: s8 = 104(s1) = FAKE *)
Lemma kk_aft : forall n, MF_KDONE_stmt B n ->
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at B v lyc pos regs1 ->
(length rest < n)%nat -> mf_loop v Wc memc mcc cur line p rest ->
fst (m_lines (mcc, cur) line (lines rest)) = mf_final v ->
mf_np v memc Wc p -> getr regs1 21 = w64 (mv_c v) -> getr regs1 22 = w64 line ->
mf_at B v Wc regs1 memc mdc KK_AFT.
Proof.
intros n KDONE v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CX LS FRM CORE CELLS RA Hn LOOP MOD NP R21 R22.
pose proof CORE as (HJ & HPerm & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_loop_blk B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc cur line p rest CX CORE LOOP)
  as (bt & mt & Hbt & Hbt1 & Hbt2 & Htp).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bt mt HAR Hbt) as (_ & Bt4096 & Btceil & _).
destruct (mf_sp0 B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in S1.
pose proof LOOP as (_ & _ & _ & _ & _ & Hcurok & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc cur CX CORE Hcurok) as Hcur.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.mod_pos_bound (mv_sp v - 288) 32 ltac:(lia)) as M32.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
assert (Hp64 : 0 <= p < 2 ^ 64) by lia.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc cur p [] KK_AFT true true [] false false
  [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hp64 ltac:(unfold MF_LOW_ON; lia) (Forall_nil _)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos cur p []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos cur p []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34.
cbn [Nat.add nth mf_extra map app] in E32, E34.
(* the spill slots read-only *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
clear HS0 HR1. kk_norm HS1.
unfold mf_at.
paj_run_to_sh RUNTOP HS1 HJ MF_KDONE.
{ kk_awr_ro. }
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
  assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
  [ intros a Ha; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) (fun _ => False) HFr _ a Ha (fun x => x));
    intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
    repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; lia |]); destruct Hinw | ] end.
cbn [ms_mem mkst] in K0.
set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc cur (ms_mem ms) mdw CX CORE CELLS HJ K0)
  as (CORE' & CELLS' & NPk & LOOPK).
prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4. prreg HS1 (8%bv : bv 5) Q8.
prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (18%bv : bv 5) Q18. prreg HS1 (19%bv : bv 5) Q19. prreg HS1 (25%bv : bv 5) Q25.
prreg HS1 (26%bv : bv 5) Q26. prreg HS1 (24%bv : bv 5) Q24.
prreg HS1 (21%bv : bv 5) Q21. prreg HS1 (22%bv : bv 5) Q22.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
  - rewrite Q2. apply EE. reflexivity.
  - rewrite Q3. apply EE. reflexivity.
  - rewrite Q4. apply EE. reflexivity.
  - rewrite Q8. apply EE. reflexivity.
  - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
  - rewrite Q18, E32, R18. reflexivity.
  - rewrite Q19. apply EE. reflexivity.
  - rewrite Q25. apply EE. reflexivity.
  - rewrite Q26. apply EE. reflexivity. }
pmkst HS1.
apply (KDONE v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos mcc cur line p rest CX LS FRM CORE' CELLS' RA'
  ltac:(rewrite Q24, E34; reflexivity) Hn (LOOPK mcc cur line p rest LOOP) MOD (NPk p NP)).
+ rewrite Q21, (EE 21%nat 21%bv eq_refl). exact R21.
+ rewrite Q22, (EE 22%nat 22%bv eq_refl). exact R22.
Qed.
End e.
End f.
End d.

(* ============================ KK_MISS -> KDONE and the ieq answer's split ============================ *)
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a register the symbolic state still names by an atom (m_file_s_kign_1.v ki_st_reg) *)
Lemma kk_st_reg : forall segs E ss (H : word -> bool) ms (r : bv 5) (n : nat),
  st_ok segs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
intros segs E ss H ms r n HS Hr. rewrite (st_ok_restrict_reg segs H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Section f2.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e2.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
(* the shared hypotheses (m_file_m.v change 3, decision (a), amended) this file needs, verbatim *)
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstA.STK_ieq SegInstA.RLO_A SegInstA.RHI_A.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstA.STK_m_refuse SegInstA.RLO_A SegInstA.RHI_A SegInstA.seg_litA_fz SegInstA.gotwA SegInstA.guardA.


(* the text left's sub-range [o, o + n) inside the line: its bytes as list byte, addressable, in the text block
   (m_file_s_kign_1.v ki_slice_facts) *)
Lemma kk_slice_facts : forall v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest o n,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_loop v Wc memc mcc cur line p rest ->
  (o + n <= length rest)%nat ->
  sa_bytes (rdW Wc memc) (p + Z.of_nat o) (seg_spec.zb (firstn n (skipn o rest))) /\
  seg_spec.zs (seg_spec.zb (firstn n (skipn o rest))) = firstn n (skipn o rest) /\
  Z.of_nat (length (seg_spec.zb (firstn n (skipn o rest)))) = Z.of_nat n /\
  sa_addr (rdW Wc memc) (p + Z.of_nat o) (Z.of_nat n) /\ sa_heap B lyc Sc (p + Z.of_nat o) (Z.of_nat n) /\
  p + Z.of_nat o <> 0.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest o n CX CORE LOOP Hon.
pose proof LOOP as (L1 & L2 & L3 & ((LZ & LN) & LT) & LADDR & _).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _).
assert (HZ : sa_zs (rdW Wc memc) (p + Z.of_nat o) (firstn n (skipn o rest))).
{ intros i Hi. rewrite length_firstn, length_skipn in Hi.
  replace (p + Z.of_nat o + Z.of_nat i) with (p + Z.of_nat (o + i)) by lia.
  rewrite (LZ (o + i)%nat) by (rewrite length_app; cbn [length]; lia).
  f_equal. rewrite nth_firstn. destruct (Nat.ltb_spec i n) as [Hlt|Hge]; [|lia].
  rewrite nth_skipn. apply app_nth1. lia. }
destruct (kk_bytes_of_zs SEGS (w_H Wc) memc _ _ HZ) as (HB & HZB & _).
destruct (mf_txt_heap_now B v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (bt & mt & Hin & Hb & He).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt HAR Hin) as (_ & Hbt4096 & Hbtceil & _ & _ & _ & Hmt).
pose proof (req_size_pos mt ltac:(lia)) as [_ Hrt].
assert (Hlen : length (seg_spec.zb (firstn n (skipn o rest))) = n).
{ unfold seg_spec.zb. rewrite length_map, length_firstn, length_skipn. lia. }
pose proof LADDR as (A0 & A1 & AM & ARA & AHV).
assert (Hpe : p + Z.of_nat (length rest) <= mv_t v + Z.of_nat (length (mv_s v))) by (rewrite L3; lia).
assert (Hpt : mv_t v <= p) by (rewrite L3; lia).
split; [exact HB|]. split; [exact HZB|]. split; [rewrite Hlen; reflexivity|]. split.
- split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|]. split.
  + exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc bt mt (p + Z.of_nat o) (Z.of_nat n) HAR Hin
      ltac:(lia) ltac:(lia)).
  + intros Hn. exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memc mdc bt mt (p + Z.of_nat o) (Z.of_nat n) HAR
      Hin ltac:(lia) ltac:(lia) Hn).
- split; [exists bt, mt; split; [exact Hin | lia] | lia].
Qed.

(* the callee-saved registers of a state whose symbolic registers are the seed's on CALLEE_SAVED
   (m_file_s_kign_1.v ki_pres) *)
Lemma kk_pres : forall E R regs1 v lyc pos cur np xs (rr : bvmap 5 word),
  E = mfE regs1 v lyc pos cur np xs -> mf_regs_base v regs1 ->
  (forall r, getr rr r = sv_denot E (sr_get R r)) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get R r) (sr_get sr_mf r)) CALLEE_SAVED = true ->
  aregs_preserved regs1 rr.
Proof.
intros E R regs1 v lyc pos cur np xs rr HE RB HR HC r Hr.
pose proof (mf_regs_ok v regs1 lyc pos cur np xs RB) as HO. rewrite <- HE in HO.
rewrite HR, HO. f_equal. apply sv_eqb_eq.
assert (Hin : In (Z_to_bv 5 r) CALLEE_SAVED).
{ unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    unfold CALLEE_SAVED; cbn [In]; first [ tauto | intuition (apply bv_eq; reflexivity) ]. }
exact (proj1 (forallb_forall _ _) HC _ Hin).
Qed.

(* the seed at a K cut's pc with its regions dropped (m_file_s_kign_1.v ki_seed0) *)
Lemma kk_seed0 : forall v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest pc,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
  mf_regs_at B v lyc pos regs1 -> mf_loop v Wc memc mcc (Some gi) line p rest -> mf_np v memc Wc (mf_next p rest) ->
  st_ok_pi SEGS VAL (mfE regs1 v lyc pos (Some gi) (mf_next p rest) []) (mkSS pc sr_mf [] None mf_facts)
    (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest pc CX CORE CELLS RA LOOP NP.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE LCUR) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) (mf_next p rest) [] pc true true []
  false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) (Forall_nil _)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
exact (st_ok_pi_submem _ (ss_mf pc true true [] false false [] false MF_LOW_ON) _ [] HS0 (submem_nil _) eq_refl).
Qed.

(* KK_IRET 0x86b34: `beqz a0` on ieq's answer kn: 1 falls to KK_HIT, 0 goes to KK_MISS *)
Lemma kk_iret : forall n, KK_HITX_stmt B n -> KK_MISSX_stmt B n ->
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (kn : bool),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mf_fin (m_refuse mcc (line + 1) kn, Some gi) line rest = mf_final v ->
getr regs1 24 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
getr regs1 10 = w64 (seg_spec.b2z kn) ->
mf_at B v Wc regs1 memc mdc KK_IRET.
Proof.
intros n HIT MISS v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest kn CX LS FRM CORE CELLS RA Hn Hr LOOP FIN R24 NP A0.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (kk_seed0 v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest KK_IRET CX CORE CELLS RA LOOP NP) as HS1.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np []) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
pose proof CORE as (HJ & _).
destruct kn; cbn [seg_spec.b2z] in A0.
- pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KK_HIT.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    apply awr_ok_nil. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
  assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
    by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
  assert (HPc : aregs_preserved regs1 (ms_regs ms)).
  { eapply (kk_pres E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) eq_refl RB).
    - intros r. exact (st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS).
    - vm_compute. reflexivity. }
  destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
    as (CORE' & CELLS' & NPk & LPk).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
    replace kk with KK_HIT by (unfold KK_HIT, AF_m_file; reflexivity) end.
  apply (HIT v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest CX LS FRM CORE' CELLS'
    (mf_regs_keep B v lyc pos regs1 (ms_regs ms) RA HPc) Hn Hr (LPk mcc (Some gi) line p rest LOOP) FIN).
  + transitivity (getr regs1 24); [exact (HPc 24 ltac:(unfold acallee_saved; lia)) | exact R24].
  + exact (NPk _ NP).
- pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KK_MISS.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    apply awr_ok_nil. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
  assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
    by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
  assert (HPc : aregs_preserved regs1 (ms_regs ms)).
  { eapply (kk_pres E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) eq_refl RB).
    - intros r. exact (st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS).
    - vm_compute. reflexivity. }
  destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
    as (CORE' & CELLS' & NPk & LPk).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
    replace kk with KK_MISS by (unfold KK_MISS, AF_m_file; reflexivity) end.
  apply (MISS v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest CX LS FRM CORE' CELLS'
    (mf_regs_keep B v lyc pos regs1 (ms_regs ms) RA HPc) Hn Hr (LPk mcc (Some gi) line p rest LOOP) FIN).
  + transitivity (getr regs1 24); [exact (HPc 24 ltac:(unfold acallee_saved; lia)) | exact R24].
  + exact (NPk _ NP).
Qed.

(* KKNOCK 0x86b20: ieq(k, kl, "knock"), then kk_iret (m_file_s_kign_1.v ki_s_kign's set-up) *)
Lemma kk_knock : forall n, KK_HITX_stmt B n -> KK_MISSX_stmt B n -> MF_KKNOCK_stmt B n.
Proof.
intros n HIT MISS. unfold MF_KKNOCK_stmt, MF_KAT_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv
  CX LS FRM CORE CELLS RA Hn Hr LOOP KV MISSED FIN R27 R22 R21 R20 R23 R24 NP.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof KV as (KV1 & KV2 & KV3 & KV4).
pose proof (kk_line_le rest) as Hml.
pose proof (kk_seed0 v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest MF_KKNOCK CX CORE CELLS RA LOOP NP) as HS.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np []) in *.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
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
{ eapply (kk_pres E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) eq_refl RB).
  - intros r. exact (st_ok_restrict_reg SEGS (w_H Wc) E _ ms r HS).
  - vm_compute. reflexivity. }
pose proof RA as (R2 & R3 & R4 & R8 & _).
assert (Q2 : getr (ms_regs ms) 2 = w64 (mf_s1 (mv_sp v))) by (rewrite <- R2; exact (HPc 2 ltac:(unfold acallee_saved; lia))).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite <- R3; exact (HPc 3 ltac:(unfold acallee_saved; lia))).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite <- R4; exact (HPc 4 ltac:(unfold acallee_saved; lia))).
assert (Q8 : getr (ms_regs ms) 8 = w64 (mv_sp v)) by (rewrite <- R8; exact (HPc 8 ltac:(unfold acallee_saved; lia))).
assert (Q10 : getr (ms_regs ms) 10 = w64 (p + Z.of_nat ok)).
{ rewrite (kk_st_reg SEGS _ _ _ _ 10%bv 27%nat HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 27 (Z_to_bv 5 27) eq_refl). exact R27. }
assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat kl)).
{ rewrite (kk_st_reg SEGS _ _ _ _ 11%bv 22%nat HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 22 (Z_to_bv 5 22) eq_refl). exact R22. }
assert (Q12 : getr (ms_regs ms) 12 = w64 (SegInstA.seg_litA_fz S_knock)).
{ rewrite (kk_st_reg SEGS _ _ _ _ 12%bv (A_OBJ 25) HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_img regs1 v lyc pos (Some gi) np [] (A_OBJ 25) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (mf_lit_obj VOBJS S_knock 25 ltac:(unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]))).
  reflexivity. }
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + KK_IRET)).
{ rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 1%bv HS).
  lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
    transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
  exact (codeptr_val E KK_IRET HEI). }
rewrite (SIGP SS_ieq ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_ieq) with AF_ieq by (vm_compute; reflexivity).
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
  as (CORE' & CELLS' & NPk & LPk).
pose proof (NPk np NP) as NP'. pose proof (LPk mcc (Some gi) line p rest LOOP) as LOOP'.
destruct (kk_slice_facts v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc (Some gi) line p rest ok kl CX CORE' LOOP'
  ltac:(lia)) as (SB & SZ & SL & SA & SH & S0).
rewrite KV3 in SB, SZ, SL.
pose proof MISSED as M0. apply Forall_cons_iff in M0 as [MR M1]. apply Forall_cons_iff in M1 as [MM M2].
apply Forall_cons_iff in M2 as [MI _].
rewrite (kk_disp mcc gi k vv (line + 1) MR MM MI) in FIN.
refine (mf_ieq_call B RELRO IEQ v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos MF_LOW_ON mcc (Some gi)
  line p rest np KK_IRET (p + Z.of_nat ok) (Z.of_nat kl) (seg_spec.zb k) S_knock CX LS CORE' CELLS' LOOP' NP'
  Q2 Q3 Q4 Q8 Q1 _ _ _ Q10 Q11 Q12 S0 SB SL SA SH _).
- unfold KK_IRET, AF_m_file; lia.
- unfold KK_IRET, AF_m_file; reflexivity.
- unfold M_FILE_LITS; repeat (first [left; reflexivity | right]).
- intros S2 W2 regs2 mem2 md2 Hwle LS2 CORE2 CELLS2 LOOP2 NP2 HP2 A02 K2.
  assert (HP12 : aregs_preserved regs1 regs2) by exact (aregs_preserved_trans _ _ _ HPc HP2).
  rewrite SZ in A02.
  exact (kk_iret n HIT MISS v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest (ieq k S_knock) CX LS2 FRM CORE2 CELLS2
    (mf_regs_keep B v lyc pos regs1 regs2 RA HP12) Hn Hr LOOP2 FIN
    ltac:(transitivity (getr regs1 24); [exact (HP12 24 ltac:(unfold acallee_saved; lia)) | exact R24]) NP2 A02).
Qed.

(* KK_MISS 0x86be4: s5 = c, a0 = s5, s6 = a1 = s8 = line + 1, m_refuse 0x86bf4, then kk_aft *)
Lemma kk_miss : forall n, (forall fx0 : YK11.FPState, MF_KDONE_stmt (fx := fx0) B n) -> KK_MISSX_stmt B n.
Proof.
intros n KDONE. unfold KK_MISSX_stmt, KK_ATX_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP MOD R24 NP.
pose proof CORE as (HJ & HPerm & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_sp0 B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in S1.
pose proof LOOP as (_ & _ & _ & _ & _ & Hcurok & Hk0 & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE Hcurok) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.mod_pos_bound (mv_sp v - 288) 32 ltac:(lia)) as M32.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
assert (Hcok2 : mf_cur_ok (m_refuse mcc (line + 1) false) (Some gi)) by (apply mf_cur_ok_refuse; exact Hcurok).
change (mf_fin (m_refuse mcc (line + 1) false, Some gi) line rest) with
  (fst (m_lines (m_refuse mcc (line + 1) false, Some gi) (line + 1) (lines (mf_rest rest)))) in MOD.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) (mf_next p rest) [] KK_MISS true true
  [] false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia)
  (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos (Some gi) (mf_next p rest) []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat ->
  ew E (32 + j) = nth j (mf_extra v lyc pos (Some gi) (mf_next p rest) []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 1%nat ltac:(unfold A_TEXT; lia)) as E33.
cbn [Nat.add nth mf_extra map app] in E32, E33.
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
clear HS0 HR1. kk_norm HS1.
unfold mf_at.
paj_run_to_sh RUNTOP HS1 HJ KK_RJAL.
{ kk_awr_ro. }
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
  assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
  [ intros a Ha; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) (fun _ => False) HFr _ a Ha (fun x => x));
    intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
    repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; lia |]); destruct Hinw | ] end.
cbn [ms_mem mkst] in K0.
set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdw CX CORE CELLS HJ K0)
  as (CORE' & CELLS' & NPk & LOOPK).
prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4. prreg HS1 (8%bv : bv 5) Q8.
prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (18%bv : bv 5) Q18. prreg HS1 (19%bv : bv 5) Q19. prreg HS1 (25%bv : bv 5) Q25.
prreg HS1 (26%bv : bv 5) Q26. prreg HS1 (21%bv : bv 5) Q21. prreg HS1 (22%bv : bv 5) Q22.
prreg HS1 (10%bv : bv 5) Q10. prreg HS1 (11%bv : bv 5) Q11.
assert (RA2 : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
  - rewrite Q2. apply EE. reflexivity.
  - rewrite Q3. apply EE. reflexivity.
  - rewrite Q4. apply EE. reflexivity.
  - rewrite Q8. apply EE. reflexivity.
  - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
  - rewrite Q18, E32, R18. reflexivity.
  - rewrite Q19. apply EE. reflexivity.
  - rewrite Q25. apply EE. reflexivity.
  - rewrite Q26. apply EE. reflexivity. }
pmkst HS1.
pose proof (mf_regs_at_call B v lyc pos _ RA2) as (S2r & S3r & S4r & S8r).
assert (Q10' : getr (ms_regs ms) 10 = w64 (mv_c v)) by (rewrite Q10, E33; reflexivity).
assert (Q11' : getr (ms_regs ms) 11 = w64 (line + 1)) by (rewrite Q11, (EE 24%nat 24%bv eq_refl); exact R24).
assert (Q21' : getr (ms_regs ms) 21 = w64 (mv_c v)) by (rewrite Q21, E33; reflexivity).
assert (Q22' : getr (ms_regs ms) 22 = w64 (line + 1)) by (rewrite Q22, (EE 24%nat 24%bv eq_refl); exact R24).
change (Z_to_bv 64 (BASE + 7872)) with (Z_to_bv 64 (BASE + KK_RJAL)).
apply (mf_refuse_step B SIGP SSP RELRO M_REFUSE v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos MF_LOW_ON mcc mcc false
  (Some gi) line p rest (mf_next p rest) KK_RJAL CX LS FRM (mf_corek_of_core B v lyc Sc Wc _ _ pos MF_LOW_ON mcc CORE')
  CELLS' (NPk _ NP) S2r S3r S4r S8r (LOOPK mcc (Some gi) line p rest LOOP) Hne eq_refl Hk0).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact Q10'.
- exact Q11'.
- exact (mf_kept_le_refuse mcc (line + 1) false (Some gi) (line + 1) (lines (mf_rest rest)) (mf_final v) Hcok2 MOD).
- intros fx1 ly2 S2' W2 regs2 mem2 md2 Hfx LS2 CORE3 CELLS3 NP3 LOOP3 CS.
  assert (Ely2 : ly2 = lyc) by (destruct LS as (Ea & _); destruct LS2 as (Eb & _); congruence).
  subst ly2.
  replace (KK_RJAL + 4) with KK_AFT by (unfold KK_RJAL, KK_AFT; lia).
  pose proof (mf_regs_at_kept B v lyc pos (ms_regs ms) regs2 RA2 CS) as RA3.
  assert (C21 : getr regs2 21 = getr (ms_regs ms) 21) by exact (CS 21 ltac:(unfold acallee_saved; lia)).
  assert (C22 : getr regs2 22 = getr (ms_regs ms) 22) by exact (CS 22 ltac:(unfold acallee_saved; lia)).
  apply (kk_aft (fx := fx1) B VOBJS n (KDONE fx1) v lyc S2' W2 regs2 mem2 md2 pos (m_refuse mcc (line + 1) false)
    (Some gi) (line + 1) (mf_next p rest) (mf_rest rest) CX LS2 (fxrel_frm0 fx fx1 FRM Hfx) CORE3 CELLS3 RA3).
  + destruct (mf_break_snd rest) as (_ & Hlt & _). specialize (Hlt Hne). unfold mf_rest. lia.
  + apply (mf_loop_next v W2 mem2 mcc (Some gi) line p rest (m_refuse mcc (line + 1) false) (Some gi) LOOP3 Hne).
    * unfold m_refuse. cbn [mc_refused]. lia.
    * unfold m_refuse. cbn [mc_overflow]. lia.
    * exact (proj1 (proj2 (m_refuse_sizes mcc (line + 1) false))).
    * exact Hcok2.
  + exact MOD.
  + exact NP3.
  + rewrite C21. exact Q21'.
  + rewrite C22. exact Q22'.
Qed.
End e2.
End f2.
End d2.

(* S_MF_KKNOCKP at every FP state (m_file_m.v's shape) *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstA.STK_ieq SegInstA.RLO_A SegInstA.RHI_A.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstA.STK_m_refuse SegInstA.RLO_A SegInstA.RHI_A SegInstA.seg_litA_fz SegInstA.gotwA SegInstA.guardA.
Lemma s_mf_kknockp : S_MF_KKNOCKP B.
Proof.
intros n KD fx0.
apply (kk_knock (fx := fx0) B VOBJS SIGP RELRO IEQ n).
- exact (kk_hit (fx := fx0) B VOBJS SIGP SSP RELRO M_REFUSE n KD).
- exact (kk_miss (fx := fx0) B VOBJS SIGP SSP RELRO M_REFUSE n KD).
Qed.
End i.
End h.
End g.
