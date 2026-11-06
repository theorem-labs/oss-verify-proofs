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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 558 of its 606 lines of code are new or changed and 405 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a5_k.v, with its module paths changed; 385 of its 518 lines of code are new or changed and 473 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the kit of
   segment B11c of reac_segconf_parse_file's walk (0x88bd0-0x88c80, KREFM and LOWOUT -> TAIL; the B11c segment lane of
   the image-B G3 walk owner, 2026-10-30). proves no function (kind: segment lemma kit).
   ADAPTED from the image-A G3 walk owner's image-A lemmas lib/A/Prog/pf_a10b_j.v (commit c6f2a9302a3c, the
   geometry of a cut state and what a run that writes only frame shadow cells keeps: pj_geo, pj_out and the pj_k_
   and pj_keep_ lemmas) and lib/A/Prog/pf_a5_k.v (commit 385fd095481f, a5_chain): the same statements
   re-derived at image B's frame (352 bytes, realigned: s1 = (sp0 - 0x160) & -32, so sp0 - 368 <= s1 <= sp0 - 352;
   STK_reac_segconf_parse_file = 12832; B's 23 setup slots at s1 + 0x00 .. s1 + 0xd8, pf_pieces.v PF_SL).
   Also: the frame shadow scopes B11c changes (pf_pieces.v pf_shb: model low cells 0x5c-0x5e, known cells
   0x64-0x81 and ntok cell 0x8a), and the addressability of a range of the class-5 frame whose shadow cells are 0.
   Section hypotheses: none. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- arithmetic and small tools ---------- *)
Lemma b11_m16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof. intros a b Ha Hb. rewrite Zminus_mod, Ha, Hb. reflexivity. Qed.
Lemma b11_round32 : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= x - x mod 32 <= x /\ (x - x mod 32) mod 32 = 0 /\ (x - x mod 32) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (E : x - x mod 32 = 32 * (x / 32)) by lia. rewrite E.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
(* a byte outside an 8-aligned range [F, F + 2048) has its shadow outside the range's 256 cells *)
Lemma b11_granule : forall F x, F mod 8 = 0 -> ~ (F <= x < F + 2048) -> 0 <= x ->
  ~ (F / 8 <= x / 8 < F / 8 + 256).
Proof.
intros F x HF Hx H0 [H1 H2]. apply Hx.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx. rewrite HF in DF. lia.
Qed.
Lemma b11_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma b11_zrange : forall (f : Z -> bool) lo (n : nat),
  forallb (fun k => f (lo + Z.of_nat k)) (seq 0 n) = true -> forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
intros f lo n H i Hi. rewrite forallb_forall in H.
specialize (H (Z.to_nat (i - lo)) ltac:(apply in_seq; lia)).
replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i in H by lia. exact H.
Qed.
Lemma b11_rg : forall rX L r v, pf_rg rX L -> In (r, v) L -> getr rX (Z_to_bv 5 r) = w64 v.
Proof. intros rX L r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Ltac b11_in := cbn [In app]; repeat first [left; reflexivity | right].
Ltac b11_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b11_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
Lemma b11_w64_u : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. lia. Qed.

(* ---------- the frame shadow scopes B11c changes (pf_pieces.v pf_shb) ---------- *)
(* model low's three cells (0x5c-0x5e): 0x00 in PF_SC_L146, 0xf8 in PF_SC_LINE; every other cell the same *)
Lemma b11_shb_line : forall i, 0x5c <= i < 0x5f -> pf_shb PF_SC_LINE i = 0xf8.
Proof.
intros i Hi. apply Z.eqb_eq. revert i Hi.
apply (b11_zrange (fun i => pf_shb PF_SC_LINE i =? 0xf8) 0x5c 3). vm_compute. reflexivity.
Qed.
Lemma b11_shb_line_same : forall i, ~ (0x5c <= i < 0x5f) -> pf_shb PF_SC_LINE i = pf_shb PF_SC_L146 i.
Proof.
intros i Hi. unfold pf_shb, PF_SC_LINE, PF_SC_L146. cbn [sc_cn sc_buf sc_low sc_l146 sc_known].
destruct (i <? 4); [reflexivity|]. destruct (i <? 6); [reflexivity|]. destruct (i <? 8); [reflexivity|].
destruct (i <? 72); [reflexivity|]. destruct (i <? 80); [reflexivity|]. destruct (i <? 88); [reflexivity|].
destruct (i <? 92) eqn:E92; [reflexivity|].
destruct (i <? 95) eqn:E95; [|reflexivity].
apply Z.ltb_ge in E92. apply Z.ltb_lt in E95. lia.
Qed.
(* known's 30 cells (0x64-0x81) and ntok's cell (0x8a): 0x00 in PF_SC_KNOWN, 0xf8 in PF_SC_L146 *)
Definition b11_kcell (i : Z) : Prop := (0x64 <= i < 0x82) \/ i = 0x8a.
Lemma b11_shb_l146_k : forall i, 0x64 <= i < 0x82 -> pf_shb PF_SC_L146 i = 0xf8.
Proof.
intros i Hi. apply Z.eqb_eq. revert i Hi.
apply (b11_zrange (fun i => pf_shb PF_SC_L146 i =? 0xf8) 0x64 30). vm_compute. reflexivity.
Qed.
Lemma b11_shb_l146_n : pf_shb PF_SC_L146 0x8a = 0xf8.
Proof. vm_compute. reflexivity. Qed.
Lemma b11_shb_l146_same : forall i, ~ b11_kcell i -> pf_shb PF_SC_L146 i = pf_shb PF_SC_KNOWN i.
Proof.
intros i Hi. unfold b11_kcell in Hi. unfold pf_shb, PF_SC_L146, PF_SC_KNOWN. cbn [sc_cn sc_buf sc_low sc_l146 sc_known].
destruct (i <? 4); [reflexivity|]. destruct (i <? 6); [reflexivity|]. destruct (i <? 8); [reflexivity|].
destruct (i <? 72); [reflexivity|]. destruct (i <? 80); [reflexivity|]. destruct (i <? 88); [reflexivity|].
destruct (i <? 92); [reflexivity|]. destruct (i <? 95); [reflexivity|]. destruct (i <? 100) eqn:E100; [reflexivity|].
destruct (i <? 130) eqn:E130.
{ apply Z.ltb_ge in E100. apply Z.ltb_lt in E130. exfalso. apply Hi. left. lia. }
destruct (i <? 138) eqn:E138; [reflexivity|]. destruct (i <? 139) eqn:E139; [|reflexivity].
apply Z.ltb_ge in E138. apply Z.ltb_lt in E139. exfalso. apply Hi. right. lia.
Qed.
(* in PF_SC_KNOWN the cells of cur_name (4, 5), buf (8 .. 71) and known (100 .. 129) are 0 *)
Lemma b11_shb_known0 : forall i, (4 <= i < 6 \/ 8 <= i < 72 \/ 100 <= i < 130) -> pf_shb PF_SC_KNOWN i = 0.
Proof.
intros i Hi. apply Z.eqb_eq.
destruct Hi as [Hi | [Hi | Hi]]; revert i Hi;
  [apply (b11_zrange (fun i => pf_shb PF_SC_KNOWN i =? 0) 4 2)
  | apply (b11_zrange (fun i => pf_shb PF_SC_KNOWN i =? 0) 8 64)
  | apply (b11_zrange (fun i => pf_shb PF_SC_KNOWN i =? 0) 100 30)]; vm_compute; reflexivity.
Qed.

(* ---------- reading a region the run wrote ---------- *)
Definition b11_cell_ok (cs : list YP09.chunk) (od v : Z) : bool :=
  existsb (fun c => match YP09.c_val c with
    | CVal w (SLit z) => (YP09.c_off c =? od) && (N.eqb w 1) && (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0) =? v)
    | _ => false end) cs.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma b11_cell_of_region : forall E H m n b lo hi wlo whi cs od v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> b11_cell_ok cs od v = true -> aview SEGS H m (b + od) = Some v.
Proof.
intros E H m n b lo hi wlo whi cs od v HR Hb Hc.
apply existsb_exists in Hc as (c & Hin & Hc).
destruct c as [o [w e | | | ]]; cbn [YP09.c_val YP09.c_off] in Hc; try discriminate.
destruct e; try discriminate.
apply andb_prop in Hc as [Hc Hv]. apply andb_prop in Hc as [Ho Hw].
apply Z.eqb_eq in Ho. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hv. subst o w.
unfold region_ok in HR. cbv zeta in HR. cbn [YP09.r_base YP09.r_chunks base_val] in HR.
destruct HR as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2). cbn [cbyte YP09.c_val YP09.c_off sv_denot] in Hb1, Hb2.
injection Hb1 as <-. rewrite Hb, Z.add_0_r in Hb2.
unfold aview. rewrite Hb2. cbn [option_map]. rewrite Hv. reflexivity.
Qed.

Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* B's 23 setup slots (pf_pieces.v PF_SL) lie at s1 + 0x00 .. s1 + 0xd8 *)
Lemma b11_SL_offs : forall v pos ov, In ov (PF_SL v pos) -> 0 <= fst ov <= 0xd8.
Proof.
intros v pos ov H. unfold PF_SL in H. cbn [In] in H.
repeat (destruct H as [<- | H]; [cbn [fst]; lia|]). destruct H.
Qed.

(* ---------- the geometry of a cut state ---------- *)
Definition b11_Wr (v : pfv) (pos a : Z) : Prop := pf_SH v pos <= a < pf_SH v pos + 144.
Definition b11_kept (v : pfv) (pos : Z) (rd rd' : reader) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ b11_Wr v pos a -> rd' a = rd a) /\
  (forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> rd' a <> None).
Definition b11_geoP (v : pfv) (pos : Z) : Prop :=
  alloc_ceiling + 12832 <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\ pf_sp0 v mod 16 = 0 /\
  pf_sp0 v - 368 <= pf_s1 v <= pf_sp0 v - 352 /\ pf_s1 v mod 32 = 0 /\ pf_s1 v mod 16 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\
  (pf_F v pos + 2048 <= 0x7fff7000 \/ 0x10007fff8000 <= pf_F v pos) /\
  (forall a, 0x10000 <= a < kImgEnd -> ~ (pf_F v pos <= a < pf_F v pos + 2048)).
Lemma b11_geo : forall v pos lyc Sc Wc rX memc mdc, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  b11_geoP v pos /\ In (5, pos) (frames Sc) /\ frame_addr lyc 5 pos = pf_F v pos /\
  frames Sc = (5, pos) :: frames (p_S v) /\ AR SEGS B lyc Sc Wc memc mdc.
Proof.
intros v pos lyc Sc Wc rX memc mdc HCX HFI.
destruct HCX as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _). rewrite ESTK in Hslo.
destruct HFI as (HJ & Hly & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (H32 & Happ & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (Hf0 & Hfc & _).
assert (EF : frame_addr lyc 5 pos = pf_F v pos) by (subst lyc; reflexivity).
pose proof asan_consts as (C1 & _).
change (fs_frame_bytes 5) with 2048 in Hfc, Happ.
rewrite EF in H32, Happ, Hf0, Hfc.
change (spZ (p_regs v)) with (pf_sp0 v) in Hal, Hslo, Hshi.
assert (Hsp : 0 <= pf_sp0 v) by lia.
pose proof (b11_round32 (pf_sp0 v - 352) ltac:(lia) ltac:(apply b11_m16; [exact Hal | reflexivity])) as (R1 & R2 & R3).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
split; [|split; [exact Hin | split; [exact EF | split; [exact Hfrs | exact HAR]]]].
unfold b11_geoP, pf_s1.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [exact R2|]. split; [exact R3|].
split; [lia|]. split; [lia|]. split; [exact H32|]. split; [lia|].
pose proof HAR as (_ & LG & _).
pose proof (pa_img_cover lyc Sc mdc LG) as [IC1 IC2].
intros a Ha Hf. rewrite <- EF in Hf.
destruct (al_client_img _ _ LAWS lyc Sc Wc memc mdc a HAR
  ltac:(right; left; exists 5, pos; split; [exact Hin | change (fs_frame_bytes 5) with 2048; exact Hf])) as (Hz & _).
apply Hz. unfold in_zr. unfold kImgEnd in *. lia.
Qed.
Lemma b11_SHb : forall v pos, b11_geoP v pos ->
  pf_SH v pos = SHADOW_OFF + pf_F v pos / 8 /\ 0x7fff8000 + 512 <= pf_SH v pos /\
  pf_SH v pos + 256 <= 0x10007fff8000 /\ pf_F v pos = 8 * (pf_F v pos / 8) /\ pf_SH v pos mod 4 = 0.
Proof.
intros v pos (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _). pose proof asan_consts as (C1 & _).
assert (F8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
assert (F4' : (pf_F v pos / 8) mod 4 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia.
  rewrite Z.div_mul by lia. replace (4 * q) with (q * 4) by lia. apply Z_mod_mult. }
unfold pf_SH, shadow_addr, SHADOW_OFF.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
rewrite Zplus_mod, F4'. reflexivity.
Qed.

Section k.
Variable v : pfv.
Variable pos : Z.
Hypothesis G : b11_geoP v pos.
(* a byte the run never touches, nor its shadow cell: below the allocator's ceiling, an application byte, and
   outside the class-5 frame *)
Definition b11_out (x : Z) : Prop :=
  4096 <= x < alloc_ceiling /\ (x < 0x7fff7000 \/ 0x10007fff8000 <= x) /\ ~ (pf_F v pos <= x < pf_F v pos + 2048).
Lemma b11_out_nw : forall x, b11_out x ->
  0 <= x < 2 ^ 64 /\ ~ b11_Wr v pos x /\ 0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ b11_Wr v pos (SHADOW_OFF + x / 8).
Proof.
intros x (Hx1 & Hx2 & Hx3).
pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _).
assert (F8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (b11_granule (pf_F v pos) x F8 Hx3 ltac:(lia)) as Gr.
unfold b11_Wr, pf_SH, shadow_addr, SHADOW_OFF.
split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.
Lemma b11_out_img : forall x, 0x10000 <= x < kImgEnd -> b11_out x.
Proof.
intros x Hx. pose proof G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I1). pose proof asan_consts as (C1 & _).
unfold kImgEnd in *. split; [lia|]. split; [lia|]. exact (I1 x Hx).
Qed.
Lemma b11_out_inimg : forall x, in_img SEGS x -> b11_out x.
Proof. intros x Hx. apply b11_out_img. exact (pa_img_range x Hx). Qed.
(* the real stack (the saved registers, the slots) and the class-5 frame's own bytes are outside the cells *)
Lemma b11_stack_nw : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ b11_Wr v pos a.
Proof.
intros a Ha. destruct (b11_SHb v pos G) as (_ & SH1 & SH2 & _). pose proof asan_consts as (C1 & _).
unfold b11_Wr. lia.
Qed.
Lemma b11_frame_nw : forall a, pf_F v pos <= a < pf_F v pos + 2048 -> 0 <= a < 2 ^ 64 /\ ~ b11_Wr v pos a.
Proof.
intros a Ha. pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (b11_SHb v pos G) as (_ & SH1 & SH2 & _). pose proof asan_consts as (C1 & _).
unfold b11_Wr. lia.
Qed.

Section r.
Variables rd rd' : reader.
Hypothesis K : b11_kept v pos rd rd'.
Lemma b11_k_byte : forall x, b11_out x -> rd' x = rd x.
Proof. intros x Hx. destruct (b11_out_nw x Hx) as (H0 & H1 & _). exact (proj1 K x H0 H1). Qed.
Lemma b11_k_shadow : forall x, b11_out x -> rd' (SHADOW_OFF + x / 8) = rd (SHADOW_OFF + x / 8).
Proof. intros x Hx. destruct (b11_out_nw x Hx) as (_ & _ & H0 & H1). exact (proj1 K _ H0 H1). Qed.
Lemma b11_k_zs : forall p l, (forall i, (i < length l)%nat -> b11_out (p + Z.of_nat i)) -> sa_zs rd p l -> sa_zs rd' p l.
Proof. intros p l Ho H i Hi. rewrite (b11_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma b11_k_bytes : forall p l, (forall i, (i < length l)%nat -> b11_out (p + Z.of_nat i)) -> sa_bytes rd p l -> sa_bytes rd' p l.
Proof. intros p l Ho H i Hi. rewrite (b11_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma b11_k_rdword : forall a, (forall k, 0 <= k < 8 -> b11_out (a + k)) -> rdword rd' a = rdword rd a.
Proof. intros a Ho. apply rdword_ext. intros k Hk. exact (b11_k_byte _ (Ho k Hk)). Qed.
Lemma b11_k_tail : forall e, 0 <= e -> e + 8 <= 2 ^ 64 -> sa_tail rd e -> sa_tail rd' e.
Proof.
intros e H0 H1 H x Hx. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
exact (proj2 K x ltac:(lia) (H x Hx)).
Qed.
Lemma b11_k_hull : forall q n, 0 <= q -> q + n <= 2 ^ 63 -> 0 < n -> shadow_hull_vis rd q n -> shadow_hull_vis rd' q n.
Proof.
intros q n H0 H1 Hn H s Hs. apply (proj2 K s); [|exact (H s Hs)].
unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (q + n - 1) 8 ltac:(lia)).
pose proof (Z.div_pos (2147450880 + q / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
lia.
Qed.
Lemma b11_k_str : forall p s, (forall x, p <= x < p + (Z.of_nat (length s) + 1) -> b11_out x) -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros p s Ho [[Hz Hn] Ht].
destruct (Ho (p + Z.of_nat (length s)) ltac:(lia)) as (He & _).
pose proof asan_consts as (C1 & _).
split; [split; [|exact Hn] | exact (b11_k_tail (p + Z.of_nat (length s)) ltac:(lia) ltac:(lia) Ht)].
apply (b11_k_zs p (s ++ [0])); [|exact Hz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Ho. lia.
Qed.
Lemma b11_k_addr : forall q n, (forall x, q <= x < q + n -> b11_out x) -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros q n Ho (H0 & H1 & H2 & H3 & H4). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [|intros Hn; exact (b11_k_hull _ _ H0 H1 Hn (H4 Hn))].
intros x Hx. destruct (H3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in *. rewrite (b11_k_shadow x (Ho x Hx)). exact Hs.
Qed.
Lemma b11_k_lit : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (Ha & Hs & Hp & Hr & Hi). split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
apply (b11_k_str a s); [|exact Hs]. intros x Hx. apply b11_out_inimg. exact (proj1 (Hi x ltac:(lia))).
Qed.
Lemma b11_k_cat : forall cat, sa_cat SEGS B rd cat -> sa_cat SEGS B rd' cat.
Proof.
intros cat (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (b11_k_lit tp _ Hl)].
assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (b11_k_rdword (pin_spec.row_addr cat i)); [exact Htp|].
intros k Hk. apply b11_out_inimg. apply Hi. unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.
Lemma b11_k_rod : arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros H a Hro Ho He. rewrite (b11_k_byte a); [exact (H a Hro Ho He)|].
destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
- apply b11_out_inimg. exists sg. split; [exact Hsg | exact Hr].
- apply b11_out_img. unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
Qed.
Lemma b11_k_ssp : sa_ssp rd gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros (G1 & g & G2).
assert (Ho : forall a, 0x10000 <= a /\ a + 8 <= kImgEnd -> forall k, 0 <= k < 8 -> b11_out (a + k))
  by (intros a Ha k Hk; apply b11_out_img; lia).
split; [rewrite (b11_k_rdword gotwA); [exact G1 | apply Ho; unfold gotwA, kImgEnd; lia]|].
exists g. rewrite (b11_k_rdword guardA); [exact G2 | apply Ho; unfold guardA, kImgEnd; lia].
Qed.
End r.
End k.

(* a range inside a live heap block of the cut's state lies outside the frame *)
Lemma b11_out_heap : forall v pos lyc Sc (Wc : world SEGS) memc mdc b m x,
  b11_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  In (b, m) (ablocks B lyc Sc) -> b <= x < b + req_size m -> b11_out v pos x.
Proof.
intros v pos lyc Sc Wc memc mdc b m x HG HAR Hin EF Hb Hx.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & H4 & Hc & Happ & _).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. change (fs_frame_bytes 5) with 2048 in Hd.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
unfold b11_out. lia.
Qed.
Lemma b11_out_sa_heap : forall v pos lyc Sc (Wc : world SEGS) memc mdc q n x,
  b11_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  sa_heap B lyc Sc q n -> q <= x < q + n -> b11_out v pos x.
Proof.
intros v pos lyc Sc Wc memc mdc q n x HG HAR Hin EF (b & m & Hb & H1 & H2) Hx.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr].
apply (b11_out_heap v pos lyc Sc Wc memc mdc b m x HG HAR Hin EF Hb). lia.
Qed.

(* ---------- the cut's objects, carried across a run that writes only the frame's 144 shadow cells ---------- *)
Lemma b11_keep_obj : forall v pos lyc Sc (Wc : world SEGS) memc mdc rd rd',
  b11_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  b11_kept v pos rd rd' -> pf_obj B v lyc Sc rd -> pf_obj B v lyc Sc rd'.
Proof.
intros v pos lyc Sc Wc memc mdc rd rd' HG HAR Hin EF K (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
assert (Ht : forall x, p_t v <= x < p_t v + pf_len v -> b11_out v pos x)
  by (intros x Hx; exact (b11_out_sa_heap v pos lyc Sc Wc memc mdc _ _ x HG HAR Hin EF H3 Hx)).
assert (Hc : forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE -> b11_out v pos x)
  by (intros x Hx; exact (b11_out_sa_heap v pos lyc Sc Wc memc mdc _ _ x HG HAR Hin EF H5 Hx)).
split; [apply (b11_k_str v pos HG rd rd' K); [intros x Hx; apply Ht; unfold pf_len; lia | exact H1]|].
split; [exact (b11_k_addr v pos HG rd rd' K _ _ Ht H2)|]. split; [exact H3|].
split; [exact (b11_k_addr v pos HG rd rd' K _ _ Hc H4)|]. split; [exact H5|].
split; [exact (b11_k_cat v pos HG rd rd' K _ H6)|].
split; [intros x Hx; exact (b11_k_lit v pos HG rd rd' K _ _ (H7 x Hx))|].
split; [exact (b11_k_rod v pos HG rd rd' K H8) | exact (b11_k_ssp v pos HG rd rd' K H9)].
Qed.
Lemma b11_keep_rconf : forall v pos lyc Sc (Wc : world SEGS) memc mdc rd rd' cf,
  b11_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  b11_kept v pos rd rd' -> sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  sa_rconf rd (p_c v) cf -> sa_rconf rd' (p_c v) cf.
Proof.
intros v pos lyc Sc Wc memc mdc rd rd' cf HG HAR Hin EF K Hh (bs & Hb & Henc).
exists bs. split; [|exact Henc]. apply (b11_k_bytes v pos HG rd rd' K); [|exact Hb].
intros i Hi. destruct Henc as [Hl _].
apply (b11_out_sa_heap v pos lyc Sc Wc memc mdc _ _ _ HG HAR Hin EF Hh). lia.
Qed.
Lemma b11_keep_saved : forall v pos rd rd' regs, b11_geoP v pos -> b11_kept v pos rd rd' ->
  pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros v pos rd rd' regs HG K H j r Hj. rewrite (rdword_ext rd rd'); [exact (H j r Hj)|].
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
pose proof HG as (S1 & S2 & _). pose proof asan_consts as (C1 & _).
intros k Hk. apply (proj1 K); [lia|]. apply (b11_stack_nw v pos HG). lia.
Qed.
Lemma b11_keep_flag : forall v pos rd rd', b11_geoP v pos -> b11_kept v pos rd rd' ->
  rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos) ->
  rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos).
Proof.
intros v pos rd rd' HG K H. rewrite (rdword_ext rd rd'); [exact H|]. change (fs_frame_bytes 5) with 2048.
intros k Hk. destruct (b11_frame_nw v pos HG (pf_F v pos + 2048 - 8 + k) ltac:(lia)) as (H0 & H1).
exact (proj1 K _ H0 H1).
Qed.
(* any slot list at s1 whose offsets are those of the frame's 0xe0 spill bytes *)
Lemma b11_keep_slots : forall v pos rd rd' (L : list (Z * Z)), b11_geoP v pos -> b11_kept v pos rd rd' ->
  Forall (fun ov => 0 <= fst ov <= 0xd8) L -> pf_sl rd (pf_s1 v) L -> pf_sl rd' (pf_s1 v) L.
Proof.
intros v pos rd rd' L HG K HO H. unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
pose proof (HO ov Hov) as Ho.
pose proof HG as (S1 & S2 & S3 & S4 & _). pose proof asan_consts as (C1 & _).
rewrite (rdword_ext rd rd'); [exact (H ov Hov)|].
intros k Hk. apply (proj1 K); [lia|]. apply (b11_stack_nw v pos HG). lia.
Qed.
Lemma b11_keep_sl : forall v pos rd rd', b11_geoP v pos -> b11_kept v pos rd rd' ->
  pf_sl rd (pf_s1 v) (PF_SL v pos) -> pf_sl rd' (pf_s1 v) (PF_SL v pos).
Proof.
intros v pos rd rd' HG K H. apply (b11_keep_slots v pos rd rd' _ HG K); [|exact H].
apply Forall_forall. exact (b11_SL_offs v pos).
Qed.
Lemma b11_keep_nm : forall v pos rd rd' nm, b11_geoP v pos -> b11_kept v pos rd rd' ->
  pf_nm rd (pf_F v pos + PF_O_CN) nm -> pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof.
intros v pos rd rd' nm HG K (f & Hb & Henc). exists f. split; [|exact Henc].
intros i Hi. destruct Henc as [Hl _]. rewrite Hl in Hi. unfold PF_O_CN.
destruct (b11_frame_nw v pos HG (pf_F v pos + 0x20 + Z.of_nat i) ltac:(lia)) as (H0 & H1).
rewrite (proj1 K _ H0 H1). exact (Hb i ltac:(lia)).
Qed.
Lemma b11_keep_sa_str_frame : forall v pos rd rd' q s, b11_geoP v pos -> b11_kept v pos rd rd' ->
  pf_F v pos <= q -> q + Z.of_nat (length s) + 8 <= pf_F v pos + 2048 -> sa_str rd q s -> sa_str rd' q s.
Proof.
intros v pos rd rd' q s HG K Hq Hqs [[Hz Hn] Ht].
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  destruct (b11_frame_nw v pos HG (q + Z.of_nat i) ltac:(lia)) as (H0 & H1).
  rewrite (proj1 K _ H0 H1). exact (Hz i Hi).
- intros x Hx. pose proof (Z.mod_pos_bound (q + Z.of_nat (length s)) 8 ltac:(lia)).
  destruct (b11_frame_nw v pos HG x ltac:(lia)) as (H0 & H1).
  rewrite (proj1 K _ H0 H1). exact (Ht x Hx).
Qed.

(* ---------- a range of the class-5 frame whose shadow cells are 0 is addressable ---------- *)
(* the frame's cells as pf_fsh gives them: cell i of SH is the shadow byte of F + 8 i *)
Lemma b11_sh_cell : forall v pos x, b11_geoP v pos -> pf_F v pos <= x < pf_F v pos + 2048 ->
  shadow_of_addr SHADOW_OFF x = pf_SH v pos + (x - pf_F v pos) / 8.
Proof.
intros v pos x HG Hx.
destruct (b11_SHb v pos HG) as (ESH & _ & _ & EF & _).
pose proof HG as (_ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
replace x with (pf_F v pos + (x - pf_F v pos)) at 1 by lia.
rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (x - pf_F v pos) HF8).
reflexivity.
Qed.
Lemma b11_addr_frame : forall v pos (rd : reader) sc q n, b11_geoP v pos -> pf_fsh rd (pf_SH v pos) sc ->
  pf_F v pos + 32 <= q -> 0 <= n -> q + n <= pf_F v pos + 1088 ->
  (forall x, q <= x < q + n -> pf_shb sc ((x - pf_F v pos) / 8) = 0) ->
  sa_addr rd q n.
Proof.
intros v pos rd sc q n HG HF Hq Hn Hqn HZ.
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (b11_SHb v pos HG) as (ESH & SH1 & SH2 & EF & SH4).
pose proof alloc_ceiling_lt as HC.
assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
split; [lia|]. split; [lia|].
split.
{ apply amem_range_high; [lia| |lia]. destruct F4 as [F4|F4]; [left; lia | right; lia]. }
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  rewrite (b11_sh_cell v pos x HG ltac:(lia)).
  assert (B0 : 0 <= (x - pf_F v pos) / 8 < 144) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (HF ((x - pf_F v pos) / 8) B0). f_equal. exact (HZ x Hx).
- intros Hn0 s Hs.
  assert (E1 : shadow_addr q = pf_SH v pos + (q - pf_F v pos) / 8)
    by exact (b11_sh_cell v pos q HG ltac:(lia)).
  assert (E2 : shadow_addr (q + n - 1) = pf_SH v pos + (q + n - 1 - pf_F v pos) / 8)
    by exact (b11_sh_cell v pos (q + n - 1) HG ltac:(lia)).
  assert (B1 : 4 <= (q - pf_F v pos) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (B2 : (q + n - 1 - pf_F v pos) / 8 < 136) by (apply Z.div_lt_upper_bound; lia).
  rewrite E1, E2 in Hs.
  pose proof (Z.div_mod (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as M2.
  pose proof (Z.div_mod (pf_SH v pos) 4 ltac:(lia)) as D4. rewrite SH4 in D4.
  assert (Hlo : pf_SH v pos <= s).
  { (* the hull's first word: SH is 4-aligned and the first cell is at least 4 *)
    assert (Q : (pf_SH v pos + (q - pf_F v pos) / 8) / 8 * 8 >= pf_SH v pos) by lia. lia. }
  assert (Hhi : s < pf_SH v pos + 144) by lia.
  replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia.
  rewrite (HF (s - pf_SH v pos) ltac:(lia)). discriminate.
Qed.
(* a range of the class-5 frame lies in a live side-stack frame *)
Lemma b11_fframe : forall v pos lyc Sc q n, In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  pf_F v pos <= q -> 0 <= n -> q + n <= pf_F v pos + 2048 -> sa_fframe lyc Sc q n.
Proof.
intros v pos lyc Sc q n Hin EF Hq Hn Hqn. exists 5, pos. split; [exact Hin|]. split; [lia|].
rewrite EF. change (fs_frame_bytes 5) with 2048. lia.
Qed.

(* ---------- the frame chain at a call made at s1 (s0 = sp0, the frame pointer) ---------- *)
(* the prologue's record (ra at sp0 - 8, the entry s0 at sp0 - 16, pf_saved) on afn_pre's chain, which the
   journal keeps above sp0 (pf_a5_k.v a5_chain, B's frame) *)
Lemma b11_rcw_in : forall c a, inFP (seg_spec.RC_PARSE_W c) a -> c <= a < c + seg_spec.SEG_C_SIZE.
Proof.
intros c a (r & Hr & Ha). unfold seg_spec.RC_PARSE_W in Hr.
unfold seg_spec.SEG_C_SIZE, seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.RC_READING,
  seg_spec.RC_GEN in *.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
Qed.
Lemma b11_chain : forall v pos lyc Sc Wc rX memc mdc, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  exists ch1, achain lyc (rdW Wc memc) (pf_s1 v) (pf_sp0 v) ch1.
Proof.
intros v pos lyc Sc Wc rX memc mdc HCX HFI.
destruct (b11_geo v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & _ & _ & _ & HAR).
pose proof HFI as (HJ & Hly & _ & _ & HSV & _).
pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & (fe & HPF) & _).
pose proof HPRE as (HAR0 & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal & _ & _ & _ & Hshi & H47 & _ & Htop & Htop2).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
subst lyc.
destruct HPF as (HRP & _). destruct HRP as (_ & _ & _ & (bc & mc & Hbc & Hc1 & Hc2) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR0 Hbc) as (_ & _ & Hcc & _ & _ & _ & Hm).
pose proof (req_size_pos mc (proj1 Hm)) as [_ Hreq].
pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
change (spZ (p_regs v)) with (pf_sp0 v) in *.
destruct (Z_lt_le_dec (pf_sp0 v) (ly_top (p_ly v) - 16)) as [Hlt | Hge].
- exists ((pf_sp0 v, raZ (p_regs v), s0Z (p_regs v)) :: p_ch v).
  apply (achain_push (p_ly v) (rdW (p_W v) (p_mem v)) (rdW Wc memc) (pf_sp0 v) (s0Z (p_regs v)) (raZ (p_regs v))
    (p_ch v) (pf_s1 v) Hch).
  + lia.
  + intros a Ha. apply F1; [lia | rewrite SPF; lia |].
    intros Hf. apply b11_rcw_in in Hf. unfold seg_spec.SEG_C_SIZE in *. lia.
  + assert (E1 : Z_to_bv 5 1 = (1%bv : bv 5)) by (apply bv_eq; reflexivity).
    pose proof (HSV 0%nat 1 eq_refl) as H1. rewrite E1 in H1.
    replace (pf_sp0 v - 8 - 8 * Z.of_nat 0) with (pf_sp0 v - 8) in H1 by lia. exact H1.
  + assert (E8 : Z_to_bv 5 8 = (8%bv : bv 5)) by (apply bv_eq; reflexivity).
    pose proof (HSV 1%nat 8 eq_refl) as H8. rewrite E8 in H8.
    replace (pf_sp0 v - 8 - 8 * Z.of_nat 1) with (pf_sp0 v - 16) in H8 by lia. exact H8.
  + exact Hra4.
  + lia.
  + pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)) as D16. rewrite Hal, Z.add_0_r in D16. rewrite D16.
    replace (16 * (pf_sp0 v / 16)) with (2 * (pf_sp0 v / 16) * 8) by lia. apply Z_mod_mult.
  + exact Hlt.
  + lia.
- exists []. left. split; [right; left; lia | reflexivity].
Qed.
End d.
