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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 474 of its 524 lines of code are new or changed and 403 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B9_s11.v; 502 of its 617 lines of code are new or changed and 409 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): four pieces of segment B7
   of reac_segconf_parse_file's walk, the first, second, fifth and sixth conjuncts of B7_S_REF
   (lib/B/Prog/pf_seg_B7_m.v). A B7 sub-lane of the image-B G3 walk owner, 2026-10-30. proves no function (kind: segment
   lemma of reac_segconf_parse_file's walk, image B).
     b7ref_clr_ok  : HA_TAIL B n -> H_CLR B n     (pf_pieces.v)
     b7ref_call_ok : HA_CLR B n -> H_CALL B n     (pf_seg_B7_m.v)
     b7ref_href_ok : HA_CALL B n -> H_HREF B n    (pf_pieces.v)
     b7ref_unk_ok  : HA_CALL B n -> H_UNK B n     (pf_seg_B7_m.v)
   ADAPTED from the image-A G3 walk owner's image-A A7 segment lane (a working branch, lib/A/Prog/pf_a7_cr.v a7c_clr and
   pf_a7_u.v a7u_unk) and from the image-B G3 walk owner's image-B piece lib/B/Prog/pf_seg_B10b_j.v (the B10b segment lane, the seed and
   the plain run to a cut), re-derived on image B's code. Image B keeps c in the slot s1 + 0xc8 (A: in s8) and cur in
   the slot s1 + 0xc0 (A: in s4), so the runs below read and write those slots through a region on s1's atom.
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), 15 instructions, no inline check, no UBSan trap
   branch, one call:
     CLR   0x885fc  sd zero,192(s1)          cur's slot := NULL, then TAIL 0x88600
     CALL  0x885f8  jal 892f8 <refuse>       returns at 0x885fc = CLR
     HREF  0x885ec  ld a0,200(s1)            a0 = c (slot 0xc8, pf_fi)
           0x885f0  mv a1,s6                 a1 = lineno = ln + 1 (PF_RM)
           0x885f4  mv a3,s7                 a3 = the string argument (INV_HREF's xp); falls into CALL
     UNK   0x88508  auipc a0,0xfff99
           0x8850c  addi a2,a0,-72           a2 = 0x214c0 = seg_litA_rc F_unknown (listing object 42, .str.7)
           0x88510  ld a0,200(s1)            a0 = c
           0x88514  mv a1,s6                 a1 = ln + 1
           0x88518  mv a3,s3                 a3 = the body (INV_UNK's bp)
           0x8851c  j 0x885f8                CALL
   The walk: each piece seeds the state at its cut (every register its own atom; the slot 0xc8 a read-only region on
   s1's atom holding c's extra atom 32, for HREF / UNK; the slot 0xc0 a writable region on s1's atom, for CLR), runs
   the plain executor to the next cut (PaLibF.v paj_run_to_sh) or to the call (PaCallRun.v paj_run_shc), and
   rebuilds the next cut's state: pf_base by b7r_base_keep (a run writes at most the slot s1 + 0xc0, which lies above
   the allocator's ceiling and is none of pf_base's slots); the call through PaFx.v's cl_callSF with refuse_contract
   (premises from pf_seg_B7_s.v's b7_refuse_site_885f8, frame chain pf_seg_B7_ch.v's b7_chain), and INV_CLR at the FP
   state refuse returned from pf_seg_B7_k.v's b7k_keeps_refuse and b7k_base_move.
   Section hypotheses: VRO and SSPX (b7k_base_move after the refuse call), SIGP (the call target), OBJ (the F_unknown
   literal), REFUSE (the callee). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr
  SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
  PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB
  pf_pieces pf_seg_B7_f pf_seg_B7_d pf_seg_B7_s pf_seg_B7_k pf_seg_B7_ch pf_seg_B7_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools (pf_seg_B10b_j.v's b10j_ tools) ---------- *)
Lemma b7r_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma b7r_rg : forall rX L r v, pf_rg rX L -> In (r, v) L -> getr rX (Z_to_bv 5 r) = w64 v.
Proof. intros rX L r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma b7r_rg_pres : forall r1 r2 L, aregs_preserved r1 r2 -> Forall (fun rv => acallee_saved (fst rv)) L ->
  pf_rg r1 L -> pf_rg r2 L.
Proof.
intros r1 r2 L HP HC H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HP (fst rv) (HC rv Hin)). exact (H rv Hin).
Qed.
Ltac b7r_in := cbn [In app]; repeat first [left; reflexivity | right].
(* a register of the state after a run, as the executor wrote it *)
Ltac b7r_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b7r_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.

(* ---------- the seeds ---------- *)
(* c's slot s1 + 0xc8 (pf_fi), read-only, holding the extra atom 32 = c *)
Definition b7r_slot_c : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xc8 0xd0 0 0 [YP09.mkChunk 0xc8 (CVal 8 (SOff 32 0))].
Definition b7r_ss_ld (pc : Z) : sstate := mkSS pc sr_atoms [b7r_slot_c] None (mkFacts [] [] []).
(* cur's slot s1 + 0xc0, writable (CLR stores NULL there) *)
Definition b7r_slot_cur : YP09.region := YP09.mkRegion (Some 9%nat) 0xc0 0xc8 0xc0 0xc8 [].
Definition b7r_ss_clr : sstate := mkSS PF_CLR sr_atoms [b7r_slot_cur] None (mkFacts [] [] []).
(* the call: no memory is read or written *)
Definition b7r_ss_call : sstate := mkSS B7_CALL sr_atoms [] None (mkFacts [] [] []).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Hypothesis REFUSE : forall fx0 : YK11.FPState, refuse_contract (fx := fx0) SEGS B (BASE + AF_refuse) STK_refuse
  RLO_A RHI_A seg_litA_rc gotwA guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ---------- readers that agree below the allocator's ceiling (reac_segconf_parse.v's *_low) ---------- *)
Lemma b7r_str_low : forall (rd rd' : reader) p s, sa_str rd p s -> 0 <= p ->
  p + Z.of_nat (length s) < alloc_ceiling -> (forall a, 0 <= a < alloc_ceiling -> rd' a = rd a) -> sa_str rd' p s.
Proof.
intros rd rd' p s [[Hz Hn] Ht] Hp Hl K.
pose proof alloc_ceiling_value as [_ HM].
assert (HT : p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8 <= alloc_ceiling)
  by (apply tail_below; [lia | exact HM]).
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
  rewrite K by lia. exact (Hz i Hi).
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
  rewrite K by lia. exact (Ht x Hx).
Qed.
Lemma b7r_rconf_low : forall (rd rd' : reader) c rcs, sa_rconf rd c rcs -> 0 <= c ->
  c + seg_spec.SEG_C_SIZE <= alloc_ceiling -> (forall a, 0 <= a < alloc_ceiling -> rd' a = rd a) -> sa_rconf rd' c rcs.
Proof.
intros rd rd' c rcs (bs & Hb & Henc) H0 H1 K. exists bs. split; [|exact Henc].
intros i Hi. destruct Henc as [Hl _]. rewrite K by lia. exact (Hb i Hi).
Qed.
Lemma b7r_ssp_low : forall (rd rd' : reader), sa_ssp rd gotwA guardA ->
  (forall x, 0 <= x < alloc_ceiling -> rd' x = rd x) -> sa_ssp rd' gotwA guardA.
Proof.
intros rd rd' (G1 & g & G2) K. pose proof asan_consts as (C1 & _).
split.
- rewrite <- G1. apply rdword_ext. intros k Hk. apply K. unfold gotwA. lia.
- exists g. rewrite <- G2. apply rdword_ext. intros k Hk. apply K. unfold guardA. lia.
Qed.

(* ---------- what a run of B7's own code keeps: every byte but cur's slot s1 + 0xc0 ---------- *)
Definition b7r_slot (v : pfv) (a : Z) : Prop := pf_s1 v + 0xc0 <= a < pf_s1 v + 0xc8.
Definition b7r_kept (v : pfv) (rd rd' : reader) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ b7r_slot v a -> rd' a = rd a.

Section x. Context {fx : YK11.FPState}.
Let RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.
(* c is the first extra atom of the seed's environment *)
Lemma b7r_ew32 : forall (rX : bvmap 5 word) c, ew (Eimg (Ereg rX [c])) 32 = c.
Proof. intros rX c. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra rX [c] 0). Qed.
(* the slots s1 + N that pf_base names are 8-byte words apart from cur's slot s1 + 0xc0 *)
Lemma b7r_PF_SL_offs : forall v pos ov, In ov (PF_SL v pos) ->
  (0 <= fst ov /\ fst ov + 8 <= 0xc0) \/ (0xc8 <= fst ov /\ fst ov + 8 <= 0xe0).
Proof.
intros v pos ov H. unfold PF_SL in H. cbn [In] in H.
repeat (destruct H as [<- | H]; [cbn [fst]; lia|]). destruct H.
Qed.

(* cur's slot is above the allocator's ceiling, so every byte below it is kept *)
Lemma b7r_low : forall v pos lyc Sc Wc rX memc mdc sc (rd rd' : reader),
  pf_base B v pos lyc Sc Wc rX memc mdc sc -> b7r_kept v rd rd' ->
  forall a, 0 <= a < alloc_ceiling -> rd' a = rd a.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc rd rd' HB K a Ha. pose proof HB as (HCX & _).
destruct (b7k_cx B v HCX) as (_ & _ & _ & _ & Hceil & Hslo & H47 & Hsp16).
pose proof (b7k_s1 (pf_sp0 v) Hsp16) as (S1a & _). rewrite <- b7k_s1_eq in S1a.
pose proof alloc_ceiling_lt as Hac.
apply K; [lia | unfold b7r_slot; lia].
Qed.

(* pf_base at the same frame state after a run that kept every byte but cur's slot *)
Lemma b7r_base_keep : forall v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc',
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  b7r_kept v (rdW Wc memc) (rdW Wc memc') ->
  (forall r, In r [2; 3; 4; 8; 9; 20] -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' sc.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc' HB HJ' K KR.
pose proof (b7r_low v pos lyc Sc Wc rX memc mdc sc _ _ HB K) as KL.
destruct HB as (CX & FI & OBJc & SL & FSH).
destruct (b7k_cx B v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (b7k_frame B v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (b7k_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- b7k_s1_eq in S1a, S1b, S1c, S1d.
destruct FI as (HJ & Hly & HSf & HPerm & HSV & HFLW & HFRM & HTF & HC8 & HRG).
destruct OBJc as (STR & AT & HT & AC & HC & CAT & LITS & ROD & SSP).
pose proof (proj1 HJ') as HAR'. pose proof (proj1 HJ) as HAR.
pose proof alloc_ceiling_lt as Hac.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
    rdW Wc memc' a = rdW Wc memc a).
{ intros a Ha _ _. pose proof (pa_img_range a Ha) as Hr. unfold kImgEnd in Hr. apply KL. lia. }
split; [exact CX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exact HSf|]. split; [exact HPerm|].
  split.
  { intros j r Hj. rewrite <- (HSV j r Hj). apply rdword_ext. intros k Hk.
    pose proof (proj1 (nth_error_Some PF_SAVED j) ltac:(rewrite Hj; discriminate)) as Hj13.
    unfold PF_SAVED in Hj13. cbn [length] in Hj13.
    apply K; [lia | unfold b7r_slot; lia]. }
  split.
  { rewrite <- HFLW. apply rdword_ext. intros k Hk. apply KL. lia. }
  split; [exact HFRM|]. split; [exact HTF|].
  split.
  { unfold pf_sl in *. apply Forall_cons; [|apply Forall_nil]. apply Forall_inv in HC8. cbn [fst snd] in *.
    rewrite <- HC8. apply rdword_ext. intros k Hk. apply K; [lia | unfold b7r_slot; lia]. }
  unfold pf_rg in *. rewrite Forall_forall in HRG |- *. intros rv Hin.
  rewrite (KR (fst rv)); [exact (HRG rv Hin)|].
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]). destruct Hin. }
split.
{ destruct (b7k_heap_bounds B lyc Sc Wc memc mdc (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
    as (bt & mt & Hint & Hbt1 & Hbt2 & Hbt3 & Hbt4 & _).
  split; [apply (b7r_str_low _ _ _ _ STR); [lia | lia | exact KL]|].
  split; [exact (b7k_heap_addr B lyc Sc Wc memc' mdc' _ _ HAR' HT ltac:(unfold pf_len; lia))|].
  split; [exact HT|].
  split; [exact (b7k_heap_addr B lyc Sc Wc memc' mdc' _ _ HAR' HC ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
  split; [exact HC|].
  split; [exact (b7k_cat_move B _ Wc memc' CAT KI)|].
  split; [intros x Hx; exact (b7k_lit_move B _ Wc memc' _ _ (LITS x Hx) KI)|].
  split; [|exact (b7r_ssp_low _ _ SSP KL)].
  intros a Hro Ho He. rewrite KL; [exact (ROD a Hro Ho He)|].
  destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
  - assert (Hi : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
    pose proof (pa_img_range a Hi) as Hrg. unfold kImgEnd in Hrg. lia.
  - unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. lia. }
split.
{ unfold pf_sl in *. rewrite Forall_forall in SL |- *. intros ov Hov. rewrite <- (SL ov Hov).
  apply rdword_ext. intros k Hk. pose proof (b7r_PF_SL_offs v pos ov Hov) as Ho.
  apply K; [lia | unfold b7r_slot; lia]. }
intros i Hi. rewrite KL; [exact (FSH i Hi)|].
unfold pf_SH, shadow_addr, SHADOW_OFF.
pose proof (Z.div_lt_upper_bound (pf_F v pos) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
pose proof (Z.div_pos (pf_F v pos) 8 ltac:(lia) ltac:(lia)).
lia.
Qed.

(* c's state and cur_name, kept by such a run *)
Lemma b7r_st0_keep : forall v pos lyc Sc Wc rX memc mdc sc memc' cf nm k,
  pf_base B v pos lyc Sc Wc rX memc mdc sc -> b7r_kept v (rdW Wc memc) (rdW Wc memc') ->
  pf_st0 v pos (rdW Wc memc) cf nm k -> pf_st0 v pos (rdW Wc memc') cf nm k.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc memc' cf nm k HB K (HRC & HNM & HCNT).
pose proof (b7r_low v pos lyc Sc Wc rX memc mdc sc _ _ HB K) as KL.
pose proof HB as (_ & HFI & HOBJ & _).
destruct (b7k_frame B v pos lyc Sc Wc rX memc mdc HFI) as (_ & HF4 & HFc & _).
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
pose proof HOBJ as (_ & _ & _ & _ & HC & _).
destruct (b7k_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE (proj1 (proj1 HFI)) HC
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & _ & Hc1 & Hc2 & Hc3 & Hc4 & _).
split; [apply (b7r_rconf_low _ _ _ _ HRC); [lia | lia | exact KL]|].
split; [|exact HCNT].
apply (b7k_nm_move v pos _ _ nm HNM). intros a Ha. apply KL. lia.
Qed.

(* a C string in buf, kept by such a run *)
Lemma b7r_buf_str_keep : forall v pos lyc Sc Wc rX memc mdc sc memc' xp x,
  pf_base B v pos lyc Sc Wc rX memc mdc sc -> b7r_kept v (rdW Wc memc) (rdW Wc memc') ->
  pf_inb (pf_F v pos + PF_O_BUF) xp x -> sa_str (rdW Wc memc) xp x -> sa_str (rdW Wc memc') xp x.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc memc' xp x HB K (HI1 & HI2) HS.
pose proof (b7r_low v pos lyc Sc Wc rX memc mdc sc _ _ HB K) as KL.
pose proof HB as (_ & HFI & _).
destruct (b7k_frame B v pos lyc Sc Wc rX memc mdc HFI) as (_ & HF4 & HFc & _).
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
unfold PF_O_BUF in HI1, HI2.
apply (b7r_str_low _ _ _ _ HS); [lia | lia | exact KL].
Qed.

(* the part of a cut pf_seg_B7_d.v's b7_st names, out of pf_base *)
Lemma b7r_st_of_base : forall v pos lyc Sc Wc rX memc mdc,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE -> b7_st B v pos lyc Sc Wc memc mdc.
Proof.
intros v pos lyc Sc Wc rX memc mdc (HCX & (HJ & Hly & _ & Hperm & _) & HOBJ & _ & HFSH).
constructor; [exact HCX | exact HJ | exact Hly | exact Hperm | exact HOBJ | exact HFSH].
Qed.

(* ---------- the seeds ---------- *)
Lemma b7r_seed_ld : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc (pc : Z),
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [Z_to_bv 64 (p_c v)])) (b7r_ss_ld pc)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v pos lyc Sc Wc rX memc mdc pc HB.
pose proof HB as (HCX & HFI & _).
destruct (b7k_cx B v HCX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
pose proof (b7k_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- b7k_s1_eq in S1a, S1b, S1c, S1d.
destruct HFI as (_ & _ & _ & _ & _ & _ & _ & _ & HC8 & HRG).
pose proof HCX as (_ & _ & _ & Hc64 & _).
pose proof alloc_ceiling_lt as Hac. pose proof asan_consts as (C1 & _).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b7r_rg rX _ 9 _ HRG); b7r_in).
assert (U9 : bv_unsigned (ew (Eimg (Ereg rX [Z_to_bv 64 (p_c v)])) 9) = pf_s1 v).
{ rewrite (ew_Eimg_Ereg_nat rX _ 9 (Z_to_bv 5 9) eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
assert (H8 : rdword (rdW Wc memc) (pf_s1 v + 0xc8) = Some (p_c v)).
{ unfold pf_sl in HC8. apply Forall_inv in HC8. exact HC8. }
rewrite restrict_mkst_fx. unfold b7r_ss_ld. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, b7r_slot_c.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (pf_s1 v) 0xc8 8%N (SOff 32 0) (p_c v)).
  + cbn [sv_denot]. rewrite b7r_ew32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  + cbn. lia.
  + exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ H8).
- cbn. tauto.
- split; [exact I | split; exact I].
Qed.

Lemma b7r_seed_clr : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) b7r_ss_clr
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_CLR)) memc (seg_rom SEGS))).
Proof.
intros v pos lyc Sc Wc rX memc mdc HB.
pose proof HB as (HCX & HFI & _).
destruct (b7k_cx B v HCX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
pose proof (b7k_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- b7k_s1_eq in S1a, S1b, S1c, S1d.
destruct HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HRG).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof alloc_ceiling_lt as Hac. pose proof asan_consts as (C1 & _).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b7r_rg rX _ 9 _ HRG); b7r_in).
assert (U9 : bv_unsigned (ew (Eimg (Ereg rX [])) 9) = pf_s1 v).
{ rewrite (ew_Eimg_Ereg_nat rX _ 9 (Z_to_bv 5 9) eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. unfold b7r_ss_clr. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, b7r_slot_cur.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). apply HPRES. rewrite SPF. lia.
- cbn. tauto.
- split; [exact I | split; exact I].
Qed.

Lemma b7r_seed_call : forall (Wc : world SEGS) (rX : bvmap 5 word) memc,
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) b7r_ss_call
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B7_CALL)) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc. rewrite restrict_mkst_fx. unfold b7r_ss_call. apply pa_entry_st_ok_full;
  [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | split; [exact I | split; exact I]].
Qed.

(* the F_unknown literal a2 holds at the call: listing object 42 is .str.7 (0x214c0) *)
Lemma b7r_lit : forall E, img_env VAL A_LIM E -> ew E (A_OBJ 42) = w64 (seg_litA_rc F_unknown).
Proof.
intros E HE. rewrite (img_env_atomP E (A_OBJ 42) HE) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
rewrite (OBJ 42%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

(* ---------- CLR 0x885fc: sd zero,192(s1); TAIL ---------- *)
Lemma b7r_clr : forall n, HA_TAIL B n -> H_CLR (fx := fx) B n.
Proof.
intros n TAIL v pos lyc Sc Wc rX memc mdc cf nm o ln d HI.
destruct HI as (HB & HMID & HST & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b7k_cx B v HCX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
pose proof (b7k_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- b7k_s1_eq in S1a, S1b, S1c, S1d.
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof alloc_ceiling_lt as Hac. pose proof asan_consts as (C1 & _).
unfold PF_RL, PF_RM in HRG.
pose proof (b7r_seed_clr v pos lyc Sc Wc rX memc mdc HB) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b7r_rg rX _ 9 _ HRG0); b7r_in).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v).
{ rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
unfold cfg_at. change (w64 (BASE + PF_CLR)) with (Z_to_bv 64 (BASE + PF_CLR)).
(* 0x885fc sd zero,192(s1), to TAIL 0x88600 *)
paj_run_to_sh RUNTO HS HJ PF_TAIL.
{ intros a (r & Hr & Ha). cbn [b7r_ss_clr ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [b7r_slot_cur YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha.
  unfold awr_byte. left. rewrite SPF. lia. }
cbn [ms_mem mkst] in HFr, HG, HF.
b7r_clear_md.
(* what the run kept: every byte but cur's slot *)
assert (K1 : b7r_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ intros a Ha Hn. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) memc (ms_mem ms) (b7r_slot v) HFr);
    [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite U9 in Hrr;
    unfold b7r_slot; lia |]).
  destruct Hin'. }
(* what it wrote: cur's slot holds 0 *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) b7r_slot_cur) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
cbn [ms_mem restrict] in HR0.
assert (HC0 : rdword (rdW Wc (ms_mem ms)) (pf_s1 v + 0xc0) = Some 0).
{ apply (rdword_of_val_mem SEGS); [|lia].
  pose proof (field_of_region_any E _ 9%nat (pf_s1 v) _ _ _ _ _ 0xc0 8%N (SLit 0) HR0 U9
    ltac:(cbn; tauto) ltac:(cbn; lia)) as V.
  replace (bv_unsigned (sv_denot E (SLit 0)) mod 2 ^ (8 * Z.of_N 8)) with 0 in V by (cbn [sv_denot]; reflexivity).
  exact V. }
clear HFr HG HF HR0.
(* the registers at TAIL: the store writes none *)
assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b7r_rreg HS; rewrite b7r_den_atom0; apply EE; reflexivity |]). destruct Hr. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_TAIL) rg mm mdx) end.
unfold pf_postm.
apply (TAIL fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf None nm (pf_next (p_s v) o) (ln + 1) d).
destruct HMID as (Ho & Hn & HCTX).
split; [|split; [exact HCTX|split; [|split]]].
- apply (b7r_base_keep v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_regs ms) (ms_mem ms) mdv HB HJ K1).
  intros r Hr. apply QK. cbn [In] in Hr |- *. tauto.
- pose proof (pf_next_skipn_lt (p_s v) o Ho). lia.
- destruct (b7r_st0_keep v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_mem ms) cf nm _ HB K1 HST)
    as (HRC & HNM & HCNT).
  split; [exact HRC|]. split; [exact I|]. split; [exact HNM|]. split; [exact HCNT|]. exact HC0.
- unfold pf_rg, PF_RL. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    (rewrite QK; [apply (b7r_rg rX _ _ _ HRG); b7r_in | b7r_in]).
Qed.

(* ---------- CALL 0x885f8: jal refuse; back at CLR 0x885fc at the FP state refuse returned ---------- *)
Lemma b7r_call : forall n, HA_CLR B n -> H_CALL (fx := fx) B n.
Proof.
intros n CLR v pos lyc Sc Wc rX memc mdc cf nm o ln d f x xp HI.
destruct HI as (HB & HMID & HST & HRG & Hfc & HSTR & HINB & HRA).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b7k_cx B v HCX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
pose proof (b7k_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- b7k_s1_eq in S1a, S1b, S1c, S1d.
pose proof HFI as (HJ & Hly & HSc & HPERM & HSV & HFL & HFRM & HTF & HC8 & HRG0).
pose proof HMID as (Ho & _ & _).
pose proof STK_values as (_ & SRF & _ & SPF & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof alloc_ceiling_lt as Hac. pose proof asan_consts as (AC1 & _).
pose proof HOBJ as (_ & _ & _ & _ & HCH0 & _).
destruct (b7k_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE (proj1 HJ) HCH0
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hc1 & Hc2 & _).
(* the registers the cut names *)
assert (R2 : getr rX (Z_to_bv 5 2) = w64 (pf_s1 v)) by (apply (b7r_rg rX _ 2 _ HRG0); b7r_in).
assert (R3 : getr rX (Z_to_bv 5 3) = w64 (as_gp B)) by (apply (b7r_rg rX _ 3 _ HRG0); b7r_in).
assert (R4 : getr rX (Z_to_bv 5 4) = w64 (as_tp B)) by (apply (b7r_rg rX _ 4 _ HRG0); b7r_in).
assert (R8 : getr rX (Z_to_bv 5 8) = w64 (pf_sp0 v)) by (apply (b7r_rg rX _ 8 _ HRG0); b7r_in).
assert (R10 : getr rX (Z_to_bv 5 10) = w64 (p_c v)) by (apply (b7r_rg rX _ 10 _ HRA); b7r_in).
assert (R11 : getr rX (Z_to_bv 5 11) = w64 (ln + 1)) by (apply (b7r_rg rX _ 11 _ HRA); b7r_in).
assert (R12 : getr rX (Z_to_bv 5 12) = w64 (seg_litA_rc f)) by (apply (b7r_rg rX _ 12 _ HRA); b7r_in).
assert (R13 : getr rX (Z_to_bv 5 13) = w64 xp) by (apply (b7r_rg rX _ 13 _ HRA); b7r_in).
(* the seed at CALL, no region *)
pose proof (b7r_seed_call Wc rX memc) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (HAE : env_agree 32 (Ereg rX []) E).
{ split; [|reflexivity]. intros n0 Hn0. subst E. apply Eimg_low. unfold A_TEXT. lia. }
unfold cfg_at. change (w64 (BASE + B7_CALL)) with (Z_to_bv 64 (BASE + B7_CALL)).
(* 0x885f8 jal refuse *)
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ intros a (r & Hr & _). cbn [b7r_ss_call ss_mem In] in Hr. destruct Hr. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
assert (K1 : b7r_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ intros a Ha _. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
clear HF HFr HG.
pmkst HS.
(* the callee-saved registers are the cut's; ra is CLR; a0 .. a3 the cut's *)
pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ rX [] HS HAE ltac:(vm_compute; reflexivity)) as HPR.
assert (C2 : getr (ms_regs ms) 2 = w64 (pf_s1 v)).
{ transitivity (getr rX (Z_to_bv 5 2)); [exact (HPR 2 ltac:(unfold acallee_saved; lia)) | exact R2]. }
assert (C3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ transitivity (getr rX (Z_to_bv 5 3)); [exact (HPR 3 ltac:(unfold acallee_saved; lia)) | exact R3]. }
assert (C4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ transitivity (getr rX (Z_to_bv 5 4)); [exact (HPR 4 ltac:(unfold acallee_saved; lia)) | exact R4]. }
assert (C8 : getr (ms_regs ms) 8 = w64 (pf_sp0 v)).
{ transitivity (getr rX (Z_to_bv 5 8)); [exact (HPR 8 ltac:(unfold acallee_saved; lia)) | exact R8]. }
assert (Csp : spZ (ms_regs ms) = pf_s1 v).
{ unfold spZ. rewrite C2. unfold w64. apply unsigned_lit_small. lia. }
prreg HS (Z_to_bv 5 1) Q1. prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 11) Q11.
prreg HS (Z_to_bv 5 12) Q12. prreg HS (Z_to_bv 5 13) Q13.
assert (C1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + PF_CLR)).
{ etransitivity; [exact Q1|]. unfold PF_CLR, AF_reac_segconf_parse_file. reflexivity. }
assert (C10 : getr (ms_regs ms) 10 = w64 (p_c v)).
{ etransitivity; [exact Q10|]. rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl). exact R10. }
assert (C11 : getr (ms_regs ms) 11 = w64 (ln + 1)).
{ etransitivity; [exact Q11|]. rewrite (EE 11%nat (Z_to_bv 5 11) eq_refl). exact R11. }
assert (C12 : getr (ms_regs ms) 12 = w64 (seg_litA_rc f)).
{ etransitivity; [exact Q12|]. rewrite (EE 12%nat (Z_to_bv 5 12) eq_refl). exact R12. }
assert (C13 : getr (ms_regs ms) 13 = w64 xp).
{ etransitivity; [exact Q13|]. rewrite (EE 13%nat (Z_to_bv 5 13) eq_refl). exact R13. }
(* the cut's facts at the call state *)
assert (KRc : forall r, In r [2; 3; 4; 8; 9; 20] -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. apply HPR. unfold acallee_saved. cbn [In] in Hr. lia. }
assert (HBc : pf_base B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq PF_SC_LINE)
  by exact (b7r_base_keep v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_regs ms) (ms_mem ms) mdq HB HJ K1 KRc).
destruct (b7r_st0_keep v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_mem ms) cf nm _ HB K1 HST)
  as (HRCc & HNMc & HCNT).
pose proof (b7r_buf_str_keep v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_mem ms) xp x HB K1 HINB HSTR) as HSTRc.
pose proof (b7r_st_of_base v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq HBc) as Hb7.
destruct (b7_chain B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq _ HBc) as [ch1 HCH].
(* VERIFY rule 1j-bis at 0x885f8: refuse_contract's premises besides afn_pre (pf_seg_B7_s.v) *)
pose proof (b7_refuse_site_885f8 B v pos lyc Sc Wc (ms_mem ms) mdq (ms_regs ms) cf o ln d n f xp x Hb7 HRCc
  (b7_cnt_zero cf (p_s v) o Ho HCNT) HMID HFRM Hfc C10 C11 C12 C13 HSTRc HINB)
  as (ROD & _ & Hc64 & _ & Hl64 & _ & Hf64 & RPRE & ROOM & EV).
rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callSF (fx := fx) B LAWS Wc (ms_regs ms) (ms_mem ms) _ STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdq 0
    STK_refuse (refuse_W (p_c v) cf) EV_refuse (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + PF_CLR)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       sa_rconf (rdW W2 mem2) (p_c v) (refuse cf (ln + 1) f [AS x]) /\ sa_noalloc B lyc Sc ly2 S2) HJ).
  - rewrite Csp. lia.
  - exact S1d.
  - lia.
  - rewrite SRF. lia.
  - rewrite SRF, SPF. lia.
  - exact C3.
  - exact C4.
  - exact C1.
  - apply ret_ok_codeptr_v; [unfold PF_CLR, AF_reac_segconf_parse_file; lia | reflexivity].
  - rewrite unsigned_lit_small by (unfold PF_CLR, AF_reac_segconf_parse_file; lia).
    unfold PF_CLR, AF_reac_segconf_parse_file. lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
    unfold s0Z. rewrite C8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH.
  - intros HPRE1. eapply SRr_mono.
    { exact (REFUSE fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq ch1 (p_c v) (ln + 1) (seg_litA_rc f) (ln + 1) cf
        f [AS x] HPRE1 ROD C10 Hc64 C11 Hl64 C12 Hf64 RPRE ROOM EV). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. split; [rewrite C1; reflexivity|].
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. left. split; [exact (b7k_refuse_W_sub _ _ a Ha)|].
    apply b7k_refuse_W_in_block in Ha. exists bc, mc. split; [exact Hinc|].
    unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia. }
(* back at 0x885fc = CLR, at the FP state fx1 refuse returned *)
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (HRC2 & HNA2)).
unfold pf_postm, PF_POSTr.
eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HJc2 by lia.
replace (0 + EV_refuse) with 0 in HJ2 by (unfold EV_refuse; lia).
destruct HNA2 as (HP2b & Hly2 & HS2).
pose proof (b7k_keeps_refuse B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq PF_SC_LINE cf ly2 S2 W2 mem2 md2 EV_refuse
  HBc HJc2 HP2b) as HK.
assert (HB2 : pf_base (fx := fx1) B v pos ly2 S2 W2 regs2 mem2 md2 PF_SC_LINE).
{ apply (b7k_base_move (fx := fx) B VRO SSPX fx1 v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq PF_SC_LINE ly2 S2 W2
    regs2 mem2 md2 HBc Hfx1 HJ2 Hly2 HS2 HP2b HK).
  intros r Hr. apply HP2. unfold acallee_saved. cbn [In] in Hr. lia. }
assert (HPR2 : aregs_preserved rX regs2) by exact (aregs_preserved_trans _ _ _ HPR HP2).
assert (HINV2 : INV_CLR (fx := fx1) B n v pos ly2 S2 W2 regs2 mem2 md2 (refuse cf (ln + 1) f [AS x]) nm o ln d).
{ split; [exact HB2|]. split; [exact HMID|]. split.
  - split; [exact HRC2|]. split.
    + destruct HK as (_ & _ & _ & K4). apply (b7k_nm_move v pos (rdW Wc (ms_mem ms)) _ nm HNMc).
      intros a Ha. apply K4. left. exact Ha.
    + exact (b7_cnt_refuse_next cf (ln + 1) f [AS x] (p_s v) o Ho HCNT).
  - apply (b7r_rg_pres rX regs2 _ HPR2); [|exact HRG].
    unfold PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst];
      unfold acallee_saved; lia. }
exact (CLR fx1 v pos ly2 S2 W2 regs2 mem2 md2 (refuse cf (ln + 1) f [AS x]) nm o ln d HINV2).
Qed.

(* ---------- HREF 0x885ec: ld a0,200(s1); mv a1,s6; mv a3,s7; then CALL ---------- *)
Lemma b7r_href : forall n, HA_CALL B n -> H_HREF (fx := fx) B n.
Proof.
intros n CALL v pos lyc Sc Wc rX memc mdc cf nm o ln d f fa args xp HI.
destruct HI as (HB & HMID & HST & HREF & HRG).
destruct HREF as (Hf & Hfa & x & Hargs & HSTR & HINB). subst fa args.
pose proof HB as (HCX & (HJ & _) & _).
unfold PF_RL, PF_RM in HRG.
pose proof (b7r_seed_ld v pos lyc Sc Wc rX memc mdc PF_HREF HB) as HS.
set (E := Eimg (Ereg rX [Z_to_bv 64 (p_c v)])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E32 : ew E 32 = Z_to_bv 64 (p_c v)) by (subst E; apply b7r_ew32).
unfold cfg_at. change (w64 (BASE + PF_HREF)) with (Z_to_bv 64 (BASE + PF_HREF)).
(* 0x885ec .. 0x885f4, to CALL 0x885f8 *)
paj_run_to_sh RUNTO HS HJ B7_CALL.
{ intros a (r & Hr & Ha). cbn [b7r_ss_ld ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [b7r_slot_c YP09.r_wlo YP09.r_whi] in Ha. exfalso. lia. }
cbn [ms_mem mkst] in HFr, HG, HF.
b7r_clear_md.
assert (K1 : b7r_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ intros a Ha _. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]).
  destruct Hin'. }
clear HFr HG HF.
(* the registers at CALL *)
assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22; 12] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b7r_rreg HS; rewrite b7r_den_atom0; apply EE; reflexivity |]). destruct Hr. }
assert (Q10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (p_c v)).
{ b7r_rreg HS. rewrite b7r_den_atom0. exact E32. }
assert (Q11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (ln + 1)).
{ b7r_rreg HS. rewrite b7r_den_atom0, (EE 22%nat (Z_to_bv 5 22) eq_refl). apply (b7r_rg rX _ 22 _ HRG). b7r_in. }
assert (Q13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 xp).
{ b7r_rreg HS. rewrite b7r_den_atom0, (EE 23%nat (Z_to_bv 5 23) eq_refl). apply (b7r_rg rX _ 23 _ HRG). b7r_in. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B7_CALL) rg mm mdx) end.
apply (CALL fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d f x xp).
split.
{ apply (b7r_base_keep v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_regs ms) (ms_mem ms) mdv HB HJ K1).
  intros r Hr. apply QK. cbn [In] in Hr |- *. tauto. }
split; [exact HMID|].
split; [exact (b7r_st0_keep v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_mem ms) cf nm _ HB K1 HST)|].
split.
{ unfold pf_rg, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    (rewrite QK; [apply (b7r_rg rX _ _ _ HRG); b7r_in | b7r_in]). }
split; [destruct Hf as [-> | [-> | ->]]; [right; left | left | right; right; left]; reflexivity|].
split; [exact (b7r_buf_str_keep v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_mem ms) xp x HB K1 HINB HSTR)|].
split; [exact HINB|].
unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
- exact Q10.
- exact Q11.
- rewrite QK; [apply (b7r_rg rX _ 12 _ HRG); b7r_in | b7r_in].
- exact Q13.
Qed.

(* ---------- UNK 0x88508: a2 = F_unknown's literal; ld a0,200(s1); mv a1,s6; mv a3,s3; j CALL ---------- *)
Lemma b7r_unk : forall n, HA_CALL B n -> H_UNK (fx := fx) B n.
Proof.
intros n CALL v pos lyc Sc Wc rX memc mdc cf nm o ln d bp body HI.
destruct HI as ((HB & HMID & HST & _ & HRG) & HSTR & HINB & HRH & HR19).
unfold b7_post. rewrite HRH.
pose proof HB as (HCX & (HJ & _) & _).
unfold PF_RL, PF_RM in HRG.
pose proof (b7r_seed_ld v pos lyc Sc Wc rX memc mdc B7_UNK HB) as HS.
set (E := Eimg (Ereg rX [Z_to_bv 64 (p_c v)])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E32 : ew E 32 = Z_to_bv 64 (p_c v)) by (subst E; apply b7r_ew32).
unfold cfg_at. change (w64 (BASE + B7_UNK)) with (Z_to_bv 64 (BASE + B7_UNK)).
(* 0x88508 .. 0x8851c, to CALL 0x885f8 *)
paj_run_to_sh RUNTO HS HJ B7_CALL.
{ intros a (r & Hr & Ha). cbn [b7r_ss_ld ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [b7r_slot_c YP09.r_wlo YP09.r_whi] in Ha. exfalso. lia. }
cbn [ms_mem mkst] in HFr, HG, HF.
b7r_clear_md.
assert (K1 : b7r_kept v (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ intros a Ha _. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]).
  destruct Hin'. }
clear HFr HG HF.
(* the registers at CALL *)
assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b7r_rreg HS; rewrite b7r_den_atom0; apply EE; reflexivity |]). destruct Hr. }
assert (Q10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (p_c v)).
{ b7r_rreg HS. rewrite b7r_den_atom0. exact E32. }
assert (Q11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (ln + 1)).
{ b7r_rreg HS. rewrite b7r_den_atom0, (EE 22%nat (Z_to_bv 5 22) eq_refl). apply (b7r_rg rX _ 22 _ HRG). b7r_in. }
assert (Q13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 bp).
{ b7r_rreg HS. rewrite b7r_den_atom0, (EE 19%nat (Z_to_bv 5 19) eq_refl). apply (b7r_rg rX _ 19 _ HR19). b7r_in. }
prreg HS (Z_to_bv 5 12) P12.
assert (Q12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (seg_litA_rc F_unknown)).
{ rewrite P12. change 283%nat with (A_OBJ 42). exact (b7r_lit _ HEI). }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B7_CALL) rg mm mdx) end.
apply (CALL fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d F_unknown body bp).
split.
{ apply (b7r_base_keep v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_regs ms) (ms_mem ms) mdv HB HJ K1).
  intros r Hr. apply QK. cbn [In] in Hr |- *. tauto. }
split; [exact HMID|].
split; [exact (b7r_st0_keep v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_mem ms) cf nm _ HB K1 HST)|].
split.
{ unfold pf_rg, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    (rewrite QK; [apply (b7r_rg rX _ _ _ HRG); b7r_in | b7r_in]). }
split; [right; right; right; reflexivity|].
split; [exact (b7r_buf_str_keep v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_mem ms) bp body HB K1 HINB HSTR)|].
split; [exact HINB|].
unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
- exact Q10.
- exact Q11.
- exact Q12.
- exact Q13.
Qed.
End x.

(** ** The four pieces of B7_S_REF (pf_seg_B7_m.v) this file proves, at every ambient FP state *)
Theorem b7ref_clr_ok : forall (f0 : YK11.FPState) (n : nat), HA_TAIL B n -> H_CLR (fx := f0) B n.
Proof. intros f0 n T. exact (b7r_clr (fx := f0) n T). Qed.
Theorem b7ref_call_ok : forall (f0 : YK11.FPState) (n : nat), HA_CLR B n -> H_CALL (fx := f0) B n.
Proof. intros f0 n T. exact (b7r_call (fx := f0) n T). Qed.
Theorem b7ref_href_ok : forall (f0 : YK11.FPState) (n : nat), HA_CALL B n -> H_HREF (fx := f0) B n.
Proof. intros f0 n T. exact (b7r_href (fx := f0) n T). Qed.
Theorem b7ref_unk_ok : forall (f0 : YK11.FPState) (n : nat), HA_CALL B n -> H_UNK (fx := f0) B n.
Proof. intros f0 n T. exact (b7r_unk (fx := f0) n T). Qed.
End d.
