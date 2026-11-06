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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 206 of its 257 lines of code are new or changed and 402 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140), segment S_MF_HDRA: the point walk RS2 ->
   REF3 / HFIND (a walk lane of the image-B m_file-family owner's G2B, a piece agent). proves no function (kind: segment lemma of
   m_file's image-B walk: the point RS2 -> REF3 / HFIND of segment S_MF_HDRA).
   THE CODE (the neutral listing of m_file in image B lines 283-290; nm = p + q2, ne = p + r2, mf_hdra_t.v's
   hda_q2 / hda_r2, in the frame cells 192(s1) / 184(s1) the second strip wrote):
     0x865a4 `ld a0,184(s1)`        a0 := ne
     0x865a8 `ld a1,192(s1)`        a1 := nm
     0x865ac `li s4,511`            s4 := 511 (REF3 and HFIND both ask it)
     0x865b0 `beq a0,a1,86b40`      the name is empty: to REF3 0x86b40
     0x865b4 `sub s10,a0,a1`        s10 := n = ne - nm
     0x865b8 `li a0,16`
     0x865bc `bgeu s10,a0,86b40`    n >= 16: to REF3
     0x865c0                        HFIND (m_file_m.v MF_HFIND_stmt, o = q2, the name slice q2 r2 rest)
   No call, no store, no instrumented check and no UBSan trap branch in these eight instructions.
   THE PROOF. The shared seed (m_file_sd.v mf_seed) at HDA_RS2 with the two frame cells given as the caller chunks
   slx (192(s1) = atom 52 = p + q2, 184(s1) = atom 53 = p + r2, mf_chunk_atom from the statement's mf_slot facts),
   the frame-cell region [16, 216) made read-only (set_window, as image A's hda_ro_slots and image B's mf_tail.v), so
   every run's windows are empty and kept_of_frame keeps every byte; one token run to the `beq`, its two edges
   (psrr_branch_tok); on the fall-through a token run to the `bgeu` and its two edges; each edge ends with a token
   run to its target. The cut facts are carried over the whole walk by m_file_k.v's mf_carry_eq (hd5_line_carry).
   The model: the two refusals are mf_hdra_t.v's hd_ix_name (r2 = q2, or 16 <= r2 - q2), the fall-through is
   hd_ix_find, and hd_name_run gives MF_HFIND_stmt's name facts. The branch values are read through the engine's
   linear normal form (lin_nf_sound) of the compared expressions. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_hdra_t mf_hdra_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the seed's caller chunks: 192(s1) = nm (atom 52 = nth 0 xs), 184(s1) = ne (atom 53 = nth 1 xs) *)
Definition hd5_slx : list YP09.chunk := [YP09.mkChunk 192 (CVal 8 (SOff 52 0)); YP09.mkChunk 184 (CVal 8 (SOff 53 0))].

(* every region of the state is read-only: a run from it writes nothing (image B's mf_tail.v mft_awr_ro) *)
Ltac hd5_awr :=
lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
  let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* the state's form, computed *)
Ltac hd5_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
(* a value read from a token run's extended environment, at an atom below the fresh ones *)
Ltac hd5_ew Q := repeat (rewrite ew_ewset_other in Q by lia).
(* the bytes a run over read-only regions kept: all of them (its windows are empty) *)
Ltac hd5_kept HS K :=
  lazymatch type of HS with st_ok_pi ?segs _ _ _ _ =>
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
    assert (K : forall a, 0 <= a < 2 ^ 64 -> aview segs H (ms_mem msc) a = aview segs H m0 a);
    [ intros a Ha; refine (kept_of_frame Ex rs H m0 (ms_mem msc) (fun _ => False) HFr _ a Ha (fun x => x));
      intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
      repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; lia |]); destruct Hinw
    | clear HFr ] end end.
(* two such steps in a row *)
Ltac hd5_comp K2 K1 K :=
  pose proof (fun (a : Z) (Ha : 0 <= a < 2 ^ 64) => eq_trans (K2 a Ha) (K1 a Ha)) as K; clear K1 K2.
(* a register's symbolic value, not unfolded (prreg without prreg_norm) *)
Ltac hd5_rsv HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* every U E x of H in the engine's linear normal form *)
Ltac hd5_lin H :=
  repeat lazymatch type of H with
  | context [U ?E ?x] =>
      let l := eval vm_compute in (lin_nf x) in
      lazymatch l with
      | Some (?la, ?ca) => rewrite (lin_nf_sound E x la ca ltac:(vm_compute; reflexivity)) in H
      end
  end;
  cbn [lin_denot] in H.
(* every X mod M64 of H as a fresh m with X = M64 * q + m, 0 <= m < M64 *)
Ltac hd5_mods H :=
  repeat lazymatch type of H with
  | context [?X mod M64] =>
      let m := fresh "m" in
      pose proof (Z.div_mod X M64 ltac:(unfold M64; lia));
      pose proof (Z.mod_pos_bound X M64 ltac:(unfold M64; lia));
      set (m := X mod M64) in *; clearbody m
  end.
(* a branch condition as linear facts over the two cells' values *)
Ltac hd5_cond Hc U52 U53 :=
  rewrite ?branch_eq_U, ?branch_ne_U, ?branch_geu_U, ?branch_ltu_U in Hc;
  rewrite ?negb_true_iff, ?negb_false_iff in Hc;
  rewrite ?Z.eqb_eq, ?Z.eqb_neq, ?Z.ltb_lt, ?Z.ltb_ge in Hc;
  hd5_lin Hc; hd5_ew Hc; rewrite ?U52, ?U53 in Hc; hd5_mods Hc; unfold M64 in *.
(* a register mf_regs_at names, kept by the run: x9 = s1 is atom 2, x18 = SB atom 32, the others their own atoms *)
Ltac hd5_keepreg HS EE E32 R2 R9 R18 :=
  lazymatch goal with
  | |- getr _ ?r = getr _ ?r =>
     let Q := fresh "Q" in prreg HS r Q; hd5_ew Q; rewrite Q;
     first [ apply EE; reflexivity
           | rewrite (EE 2%nat 2%bv eq_refl), R2, R9; reflexivity
           | rewrite E32, R18; reflexivity ]
  end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.      (* mf_seed asks it *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the line's facts across a run that changed no byte (image A's hda_line_carry, over m_file_k.v's mf_carry_eq) *)
Lemma hd5_line_carry : forall n v lyc Sc Wc memc mdc memc' mdc' pos mcc cur line p rest,
  hda_line B n v lyc Sc Wc memc mdc pos mcc cur line p rest ->
  ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  hda_line B n v lyc Sc Wc memc' mdc' pos mcc cur line p rest.
Proof.
intros n v lyc Sc Wc memc mdc memc' mdc' pos mcc cur line p rest
  (CX & LS & FRM & CORE & CELLS & Hlen & Hne & LOOP & NP) HJ K.
destruct (mf_carry_eq B v lyc Sc Wc memc mdc memc' mdc' pos MF_LOW_OFF mcc mcc cur line p rest CX CORE HJ K LOOP)
  as (CORE' & LOOP' & CELLSK & NPK).
exact (conj CX (conj LS (conj FRM (conj CORE' (conj (CELLSK cur CELLS) (conj Hlen (conj Hne (conj LOOP' (NPK _ NP))))))))).
Qed.

(* an 8-byte frame cell across a run that changed no byte *)
Lemma hd5_slot_carry : forall v Wc memc memc' off x,
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  mf_slot v memc Wc off x -> mf_slot v memc' Wc off x.
Proof.
intros v Wc memc memc' off x K S. unfold mf_slot in *.
pose proof (mf_aview_all (w_H Wc) memc memc' K) as KA.
exact (val_mem_moved SEGS (w_H Wc) (w_H Wc) memc memc' (mf_s1 (mv_sp v) + off) (mf_s1 (mv_sp v) + off) 8 x
  (fun k _ => KA (mf_s1 (mv_sp v) + off + k)) S).
Qed.

(* RS2 0x865a4 -> REF3 0x86b40 (the name is empty or 16 bytes or more) / HFIND 0x865c0 *)
Lemma hda_rs2 : forall n, HDA_REF3_stmt B n -> MF_HFIND_stmt B n -> HDA_RS2_stmt B n.
Proof.
intros n REF3 HFIND. unfold HDA_RS2_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j HL RA HH HC H8 HI HSP S192 S184 R27.
pose proof HL as (CX & LS & FRM & CORE & CELLS & Hlen & Hne & LOOP & NP).
pose proof HH as (HL512 & Hij & HjL & HSL & HLB & HFIN).
pose proof HC as (HM & H2).
assert (Hij' : (i < j <= length (mf_line rest))%nat) by lia.
pose proof (hd_line_le rest) as HLr.
pose proof (hd_q1r1 rest i j Hij' H2) as (Q1a & Q1b).
pose proof (hd_q2r2 rest i j Hij' H2 ltac:(lia)) as (Q2a & Q2b).
pose proof (hd_name_run rest i j Hij' H2 ltac:(lia)) as (NRlen & NRle & NRfs).
pose proof LOOP as (_ & _ & _ & _ & (Hp0 & Hp63 & _) & HCOK & _ & Hl0 & Hl1 & _).
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE HCOK) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LOOP) as Hnp.
assert (Hq64 : 0 <= p + Z.of_nat (hda_q2 rest i j) < 2 ^ 64) by lia.
assert (Hr64 : 0 <= p + Z.of_nat (hda_r2 rest i j) < 2 ^ 64) by lia.
(* ===== the seed at RS2: 192(s1) = atom 52 = nm, 184(s1) = atom 53 = ne ===== *)
assert (FSLX : Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur (mf_next p rest)
    [p + Z.of_nat (hda_q2 rest i j); p + Z.of_nat (hda_r2 rest i j)]) (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v)))
  hd5_slx).
{ unfold hd5_slx. constructor; [|constructor; [|constructor]].
  - apply (mf_chunk_atom _ _ _ 192 52 0 (p + Z.of_nat (hda_q2 rest i j))).
    + exact (mfE_xs regs1 v lyc pos cur (mf_next p rest)
        [p + Z.of_nat (hda_q2 rest i j); p + Z.of_nat (hda_r2 rest i j)] 0 ltac:(unfold A_TEXT; lia)).
    + lia.
    + lia.
    + rewrite Z.add_0_r. exact S192.
  - apply (mf_chunk_atom _ _ _ 184 53 0 (p + Z.of_nat (hda_r2 rest i j))).
    + exact (mfE_xs regs1 v lyc pos cur (mf_next p rest)
        [p + Z.of_nat (hda_q2 rest i j); p + Z.of_nat (hda_r2 rest i j)] 1 ltac:(unfold A_TEXT; lia)).
    + lia.
    + lia.
    + rewrite Z.add_0_r. exact S184. }
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest)
  [p + Z.of_nat (hda_q2 rest i j); p + Z.of_nat (hda_r2 rest i j)] HDA_RS2 true true hd5_slx false false [] false
  CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_OFF; lia) FSLX (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
pose proof (mfE_extra regs1 v lyc pos cur (mf_next p rest)
  [p + Z.of_nat (hda_q2 rest i j); p + Z.of_nat (hda_r2 rest i j)] 0 ltac:(unfold A_TEXT; lia)) as E32.
cbn [Nat.add nth mf_extra map app] in E32.
pose proof (mfE_xs regs1 v lyc pos cur (mf_next p rest)
  [p + Z.of_nat (hda_q2 rest i j); p + Z.of_nat (hda_r2 rest i j)] 0 ltac:(unfold A_TEXT; lia)) as E52.
pose proof (mfE_xs regs1 v lyc pos cur (mf_next p rest)
  [p + Z.of_nat (hda_q2 rest i j); p + Z.of_nat (hda_r2 rest i j)] 1 ltac:(unfold A_TEXT; lia)) as E53.
cbn [Nat.add nth] in E52, E53.
set (E := mfE regs1 v lyc pos cur (mf_next p rest)
  [p + Z.of_nat (hda_q2 rest i j); p + Z.of_nat (hda_r2 rest i j)]) in HS0, E32, E52, E53.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (intros; apply mfE_reg; assumption).
clearbody E.
assert (U52 : bv_unsigned (ew E 52) = p + Z.of_nat (hda_q2 rest i j)) by (rewrite E52; apply unsigned_lit_small; lia).
assert (U53 : bv_unsigned (ew E 53) = p + Z.of_nat (hda_r2 rest i j)) by (rewrite E53; apply unsigned_lit_small; lia).
(* the frame cells read-only: no run of this walk writes a byte *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS end.
clear HS0 HR1. hd5_norm HS.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
pose proof CORE as (HJ & _).
unfold mf_at.
(* ===== 0x865a4 .. 0x865ac: one token run, stuck at the `beq` 0x865b0 ===== *)
paj_run_tok RUN HS HJ SHOK Bspan; [hd5_awr|].
hd5_kept HS K1.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* ne = nm: the name is empty, to REF3 *)
  hd5_cond Hc U52 U53.
  assert (HE0 : hda_r2 rest i j = hda_q2 rest i j) by lia.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_REF3; [hd5_awr|].
  hd5_kept HS K2. hd5_comp K2 K1 K.
  pose proof (hd5_line_carry n v lyc Sc Wc memc mdc _ _ pos mcc cur line p rest HL HJ K) as HL'.
  prreg HS (20%bv : bv 5) Q20. hd5_ew Q20. prreg HS (27%bv : bv 5) Q27. hd5_ew Q27.
  pmkst HS.
  apply (REF3 v lyc Sc Wc _ _ _ pos mcc cur line p rest HL').
  + apply (mf_regs_at_of B v lyc pos regs1 _ RA); hd5_keepreg HS EE E32 R2 R9 R18.
  + rewrite <- HFIN, (hd_ix_name rest i j Hij' HC mcc (line + 1) H8 HI HSP (or_introl HE0)). reflexivity.
  + rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
  + rewrite Q20. reflexivity.
- (* ne <> nm: n = ne - nm, `li a0,16`, stuck at the `bgeu` 0x865bc *)
  hd5_cond Hc U52 U53.
  assert (HN0 : hda_r2 rest i j <> hda_q2 rest i j) by lia.
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [hd5_awr|].
  hd5_kept HS K2. hd5_comp K2 K1 K12.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* n >= 16: to REF3 *)
    hd5_cond Hc U52 U53.
    assert (HG16 : (16 <= hda_r2 rest i j - hda_q2 rest i j)%nat) by lia.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_REF3; [hd5_awr|].
    hd5_kept HS K3. hd5_comp K3 K12 K.
    pose proof (hd5_line_carry n v lyc Sc Wc memc mdc _ _ pos mcc cur line p rest HL HJ K) as HL'.
    prreg HS (20%bv : bv 5) Q20. hd5_ew Q20. prreg HS (27%bv : bv 5) Q27. hd5_ew Q27.
    pmkst HS.
    apply (REF3 v lyc Sc Wc _ _ _ pos mcc cur line p rest HL').
    * apply (mf_regs_at_of B v lyc pos regs1 _ RA); hd5_keepreg HS EE E32 R2 R9 R18.
    * rewrite <- HFIN, (hd_ix_name rest i j Hij' HC mcc (line + 1) H8 HI HSP (or_intror HG16)). reflexivity.
    * rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
    * rewrite Q20. reflexivity.
  + (* 0 < n < 16: to HFIND *)
    hd5_cond Hc U52 U53.
    assert (HRG : (hda_q2 rest i j < hda_r2 rest i j < hda_q2 rest i j + 16)%nat) by lia.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_HFIND; [hd5_awr|].
    hd5_kept HS K3. hd5_comp K3 K12 K.
    pose proof (hd5_line_carry n v lyc Sc Wc memc mdc _ _ pos mcc cur line p rest HL HJ K) as HL'.
    pose proof HL' as (_ & _ & _ & CORE' & CELLS' & _ & _ & LOOP' & NP').
    pose proof (hd5_slot_carry v Wc memc _ 192 _ K S192) as S192'.
    prreg HS (11%bv : bv 5) Q11. hd5_ew Q11. prreg HS (20%bv : bv 5) Q20. hd5_ew Q20.
    prreg HS (27%bv : bv 5) Q27. hd5_ew Q27. hd5_rsv HS (26%bv : bv 5) Q26.
    pmkst HS.
    apply (HFIND v lyc Sc Wc _ _ _ pos mcc cur line p rest (hda_q2 rest i j)
      (slice (hda_q2 rest i j) (hda_r2 rest i j) rest) CX LS FRM CORE' CELLS').
    * apply (mf_regs_at_of B v lyc pos regs1 _ RA); hd5_keepreg HS EE E32 R2 R9 R18.
    * exact Hlen.
    * exact Hne.
    * exact LOOP'.
    * rewrite NRlen. lia.
    * exact NRle.
    * exact NRfs.
    * rewrite <- HFIN, (hd_ix_find rest i j Hij' HC mcc (line + 1) H8 HI HSP HRG). reflexivity.
    * rewrite Q11, E52. reflexivity.
    * exact S192'.
    * rewrite Q26, denot_lit_U. unfold w64. f_equal.
      lazymatch goal with |- U ?E' ?x = _ => remember (U E' x) as u eqn:Hu end.
      hd5_lin Hu. hd5_ew Hu. rewrite ?U52, ?U53 in Hu. hd5_mods Hu. rewrite NRlen. unfold M64 in *. lia.
    * rewrite Q20. reflexivity.
    * rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
    * exact NP'.
Qed.
End e.
End f.
End d.

(* the lemma and what it rests on *)
About hda_rs2.
Print Assumptions hda_rs2.
