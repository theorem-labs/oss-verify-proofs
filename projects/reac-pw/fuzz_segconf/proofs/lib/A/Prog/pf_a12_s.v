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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 153 of its 187 lines of code are new or changed and 419 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the call of refuse in segment A12 of
   reac_segconf_parse_file's walk (the ignore key, IGN 0x88364 -> RS3 / PROV2; pf_pieces.v S_A12), at 0x8842c
   (pf_a12_k.v's listing offset A12_REF), and the cut's facts back after it. Written 2026-10-30. No instruction is
   walked here.

   The call (the unit's internal record, commit dfb49d6ad789, path records/segp/dis/reac_segconf_parse_file.fuzz_segconf.asan.s,
   0x88414-0x88430): a2 = 0x21900 = seg_litA_rc
   F_badignore (auipc / addi 0x88414 / 0x88418), a0 = s8 = c, a1 = s10 = ln + 1, a3 = slot s1 + 0x50 = cur_name
   = pf_F v pos + PF_O_CN, a4 = s9 = vp (the value in buf); `jal refuse` 0x8842c, `j RS3` 0x88430. SegModel's
   call: refuse cf (ln + 1) F_badignore [AS nm; AS val].

   a12_ref_site (VERIFY rule 1j-bis): from the cut pf_base at PF_SC_LINE and the site's registers, every
   premise of refuse_contract after afn_pre (arodata_okP, the ranges of a0 / a1 / a2, refuse_pre, sa_room, the
   event bound). No Section hypothesis: arodata_okP and sa_ssp are pf_obj's conjuncts at the site's own state,
   sa_frm0 is pf_fi's. The statement carries no frame chain (achain): the walk (pf_a12.v) builds the one
   PaFx.cl_callSF asks with pf_a5_k.a5_chain itself.
     - the format: In F_badignore REFUSE_FORMATS and its conversion kinds by computation; In F_badignore
       PARSE_FILE_LITS (reac_segconf_parse_file_c.v:126-128, position 22), so sa_lit and the address bound
       from pf_obj's literal clause and the literal's sa_pinned at the cut's AR state;
     - the two %s arguments: cur_name [F + 0x20, F + 0x30) (shadow cells 4..5) and val in buf (cells 8..71),
       both in scope at PF_SC_LINE, both in the LIVE class-5 frame (refuse_va_locs' sa_fframe arm,
       SegABase.v:204-206), their read spans apart from the stack below sp (above alloc_ceiling) and from
       refusal[n] / c->refused (in the block c, which YCbq.sep_block_frame keeps apart from the frame): the
       shared pf_a6_k.a6_obj_arg at [0x20, 0x30) and pf_a6_k.a6_buf_arg (its instance at buf). a6_obj_arg
       takes cur_name's string as sa_str; a12s_nm_str gives it from the cut's pf_nm (seg_spec.cstr_enc 16);
     - rc_refused cf + 1 < 2 ^ 32 from pf_cnt cf 0; 0 <= ln + 1 <= 65535 from pf_mid's line account and the
       text bound of reader_pre (pf_a6_k.a6_cx).
   The structure of the site lemma follows segment A7's pf_a7_s.v (a7_refuse_site_ok, commit
   980fbe9c6015).

   a12_ref_after: the cut's facts at refuse's exit state, through segment A6's kit (pf_a6_k.v): a6_keeps_refuse
   (the agreements refuse's journal gives: its footprint refuse_W lies in the block c; the class-5 frame and its
   shadow by the journal's FRAMES clause), a6_base_move (pf_base rebuilt at the exit state: the shadow of the
   text and of the block c RE-DERIVED from AR there, a6_heap_addr), a6_nm_move (cur_name, in the frame).
   Section hypotheses, taken for a12_ref_after ONLY (lib/A/Prog/reac_segconf_parse.v:132 / :137's shapes), both
   forced by pf_a6_k.a6_base_move (Section hypotheses of pf_a6_k.v's Section e): VRO (pf_a5_k.a5_ro_img, the
   read-only view's bytes are image bytes) and SSPX (sa_ssp at the exit state: the GOT word gotwA is an owned
   static the journal does not keep), until listing stage 2's SegRecCells.seg_rec_cells discharges them. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaArtOwn PaFx PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
SegPgBase SegABase SegGlob SegInstA SegObj refuse_c reac_segconf_parse_file_c pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a5_k pf_a6_k.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* cur_name's 16 bytes hold nm (pf_nm, seg_spec.cstr_enc 16): with cur_name 8-aligned, nm is a C string there
   with its slack (sa_str), the form pf_a6_k.a6_obj_arg takes; the slack stays in the 16 bytes *)
Lemma a12s_nm_str : forall (rd : reader) (a : Z) (nm : list Z), pf_nm rd a nm -> a mod 8 = 0 ->
  sa_str rd a nm /\ (length nm < 16)%nat.
Proof.
intros rd a nm (f & Hb & (Hl & Hlt & Hn0 & Hfz)) Ha8.
assert (E : seg_spec.zs f = (nm ++ [0]) ++ skipn (S (length nm)) (seg_spec.zs f))
  by (rewrite <- Hfz; symmetry; apply firstn_skipn).
assert (Hby : forall i, (i < 16)%nat -> rd (a + Z.of_nat i) = Some (nth i (seg_spec.zs f) 0)).
{ intros i Hi. rewrite (Hb i) by lia. f_equal. unfold seg_spec.zs.
  rewrite (nth_indep (map bv_unsigned f) 0 (bv_unsigned ZB0)) by (rewrite length_map; lia).
  symmetry. apply map_nth. }
split; [|exact Hlt].
split.
- split; [|exact Hn0]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (Hby i) by lia. rewrite E, app_nth1 by (rewrite length_app; cbn [length]; lia). reflexivity.
- intros y Hy.
  pose proof (Z.div_mod (a + Z.of_nat (length nm)) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (a + Z.of_nat (length nm)) 8 ltac:(lia)) as D2.
  pose proof (Z.div_mod a 8 ltac:(lia)) as D3. rewrite Ha8, Z.add_0_r in D3.
  replace y with (a + Z.of_nat (Z.to_nat (y - a))) by lia.
  rewrite (Hby (Z.to_nat (y - a))) by lia. discriminate.
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

(* ---- VERIFY rule 1j-bis: the call of refuse at 0x8842c, refuse(c, ln + 1, F_badignore, cur_name, val) ----
   Every premise of refuse_contract after afn_pre, at image A's numbers, over the call's registers regsc (gi,
   ret_ok, gp, tp and sp are the walk's call-state facts; refuse_pre reads none of them) *)
Lemma a12_ref_site : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc (regsc : bvmap 5 word)
    cf nm o ln d n (gi : nat) vp val,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  sa_rconf (rdW Wc memc) (p_c v) cf -> pf_cnt cf 0 -> pf_mid v o ln d n ->
  pf_nm (rdW Wc memc) (pf_F v pos + PF_O_CN) nm ->
  sa_str (rdW Wc memc) vp val -> pf_inb (pf_F v pos + PF_O_BUF) vp val ->
  spZ regsc = pf_s1 v -> YK0s.ret_ok (getr regsc 1) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 10 = w64 (p_c v) -> getr regsc 11 = w64 (ln + 1) ->
  getr regsc 12 = w64 (seg_litA_rc F_badignore) ->
  getr regsc 13 = w64 (pf_F v pos + PF_O_CN) -> getr regsc 14 = w64 vp ->
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\
  0 <= p_c v < 2 ^ 64 /\ 0 <= ln + 1 < 2 ^ 64 /\ 0 <= seg_litA_rc F_badignore < 2 ^ 64 /\
  refuse_pre SEGS B seg_litA_rc gotwA guardA lyc Sc regsc (rdW Wc memc) (p_c v) (ln + 1)
    (seg_litA_rc F_badignore) [getr regsc 13; getr regsc 14; getr regsc 15; getr regsc 16; getr regsc 17]
    cf (ln + 1) F_badignore [AS nm; AS val] /\
  sa_room Sc /\ st_nev Sc + EV_refuse <= EV_MAX.
Proof.
intros v pos lyc Sc Wc rX memc mdc regsc cf nm o ln d n gi vp val HB RC CNT MID NM Hvs Hvb
  _ _ _ _ _ _ _ H13 H14.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hfin & G & _).
pose proof HB as (CX & FI & OBJ & _ & _).
destruct (a6_cx B v CX) as (Hc0 & Hc16 & HLS & _ & Hceil & _ & _ & _).
pose proof CX as (_ & _ & _ & Hc64 & _ & _ & _ & _ & _ & Hroom & Hev).
pose proof FI as (HJ & _ & _ & _ & _ & _ & HFRM & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & Hnev & _).
pose proof OBJ as (_ & _ & _ & AC & HC & _ & LITS & ROD & SSP).
pose proof MID as (_ & _ & LCX).
destruct (pf_lctx_ln _ _ _ _ LCX) as (Hln & Hnx).
assert (Hl1 : 0 <= ln + 1 <= 65535) by lia.
destruct (a6_heap_bounds B _ _ _ _ _ _ _ HAR HC ltac:(unfold seg_spec.SEG_C_SIZE; lia))
  as (bc & mc & Hinc & Hcb1 & Hcb2 & _).
(* the format: a literal of parse_file's module (PARSE_FILE_LITS position 22) *)
assert (HLin : In F_badignore PARSE_FILE_LITS).
{ unfold PARSE_FILE_LITS. apply in_or_app. left. do 22 apply in_cons. apply in_eq. }
pose proof (LITS F_badignore HLin) as HLL.
pose proof HLL as (Hlp & _ & Hpin & _).
pose proof (Hpin _ _ _ _ _ HAR) as (_ & Hlhi & _).
(* the forbidden ranges of refuse_pre's sa_va_args: the stack above alloc_ceiling, two ranges in the block c *)
assert (HWl : Forall (fun iv => alloc_ceiling <= fst iv \/
    (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= fst iv /\ snd iv <= b + req_size m))
  [(ly_stk_lo lyc, spZ regsc);
   (seg_spec.refusal_addr (p_c v) (length (rc_refusal cf)),
    seg_spec.refusal_addr (p_c v) (length (rc_refusal cf)) + seg_spec.RC_REFUSAL_LEN);
   (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)]).
{ destruct RC as (bs & _ & (_ & _ & _ & _ & HL8 & _)).
  constructor; [left; cbn [fst]; rewrite Hly; exact Hceil|].
  constructor; [right; exists bc, mc; split; [exact Hinc|]; cbn [fst snd];
    unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.SEG_C_SIZE in *; lia|].
  constructor; [right; exists bc, mc; split; [exact Hinc|]; cbn [fst snd];
    unfold seg_spec.RC_REFUSED, seg_spec.SEG_C_SIZE in *; lia|].
  constructor. }
(* the two %s arguments: cur_name (a3, the object [F + 0x20, F + 0x30), cells 4..5 at 0 in PF_SC_LINE) and val
   in buf (a4) *)
assert (HCN8 : (pf_F v pos + PF_O_CN) mod 8 = 0).
{ pose proof G as (_ & _ & _ & _ & _ & _ & _ & HF32 & _).
  pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as DF. rewrite HF32, Z.add_0_r in DF.
  unfold PF_O_CN. replace (pf_F v pos + 0x20) with ((4 * (pf_F v pos / 32) + 4) * 8) by lia.
  apply Z_mod_mult. }
destruct (a12s_nm_str _ _ _ NM HCN8) as [HNS HNL].
assert (HCELL : forall i, 0x20 / 8 <= i < 0x30 / 8 -> pf_shb PF_SC_LINE i = 0).
{ intros i Hi. change (0x20 / 8) with 4 in Hi. change (0x30 / 8) with 6 in Hi. unfold pf_shb.
  destruct (i <? 4) eqn:E1; [apply Z.ltb_lt in E1; lia|].
  destruct (i <? 6) eqn:E2; [reflexivity | apply Z.ltb_ge in E2; lia]. }
destruct (a6_obj_arg B v pos lyc Sc Wc rX memc mdc PF_SC_LINE 0x20 0x30 (pf_F v pos + PF_O_CN) nm _ HB
  ltac:(lia) eq_refl eq_refl ltac:(lia) HCELL HNS ltac:(unfold PF_O_CN; lia) ltac:(unfold PF_O_CN; lia) HWl)
  as (VN & LN).
destruct (a6_buf_arg B v pos lyc Sc Wc rX memc mdc PF_SC_LINE vp val _ HB eq_refl eq_refl Hvs Hvb HWl)
  as (VV & LV).
split; [exact ROD|].
split; [exact Hc64|].
split; [lia|].
split; [lia|].
split.
- unfold refuse_pre.
  split; [lia|]. split; [exact Hc16|]. split; [exact RC|]. split; [exact HC|]. split; [exact AC|].
  split; [destruct CNT as [CN1 _]; lia|].
  split; [lia|]. split; [reflexivity|].
  split; [unfold seg_spec.REFUSE_FORMATS; do 11 apply in_cons; apply in_eq|].
  split; [cbn [map seg_spec.arg_is_s]; vm_compute; reflexivity|].
  split; [lia|]. split; [reflexivity|]. split; [exact HLL|].
  split; [cbn [sa_va_args]; rewrite H13, H14; exact (conj VN (conj VV I))|].
  split; [cbn [refuse_va_locs]; rewrite H13, H14; exact (conj LN (conj LV I))|].
  split; [exact HFRM|]. split; [exact SSP|].
  intros y Hy. apply LITS. unfold PARSE_FILE_LITS. apply in_or_app. right. exact Hy.
- split; [unfold sa_room; unfold sa_room_n in Hroom; rewrite Hfrs; cbn [app length]; lia|].
  unfold EV_refuse; unfold EV_reac_segconf_parse_file in Hev; lia.
Qed.

(* ---- the cut's facts after the call (piece A6's kit) ---- *)
Section r.
(* forced by pf_a6_k.a6_base_move (its pf_a5_k.a5_ro_img: the read-only view at the exit state is kept through the
   image bytes, which needs the listing's relro range); reac_segconf_parse.v:132's shape *)
Hypothesis VRO : seg_val_relro (PI := PI).
(* forced by pf_a6_k.a6_base_move (pf_obj's sa_ssp at the exit state: the GOT word gotwA is an owned static,
   which refuse's journal does not keep); the contract writer's route A, discharged by SegRecCells.seg_rec_cells
   after listing stage 2; reac_segconf_parse.v:137's shape *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

(* refuse returned (cl_callSF: at the FP state fx1, fxrel fx fx1) with its journal from the call state and parse_file's
   journal at the exit state; the exit registers rX' hold pf_fi's list (a5_FI) *)
Lemma a12_ref_after : forall (fx1 : YK11.FPState) v pos lyc Sc (Wc : world SEGS) rX memc mdc
    ly2 S2 (W2 : world SEGS) mem2 md2 (rX' : bvmap 5 word) cf,
  pf_base (fx := fx) B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  fxrel fx fx1 ->
  ajournal SEGS B STK_refuse (pf_s1 v) (refuse_W (p_c v) cf) lyc Sc Wc memc mdc []
    ly2 S2 W2 mem2 md2 EV_refuse ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
    (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] ly2 S2 W2 mem2 md2 0 ->
  sa_noalloc B lyc Sc ly2 S2 ->
  pf_rg rX' (a5_FI B v) ->
  pf_base (fx := fx1) B v pos ly2 S2 W2 rX' mem2 md2 PF_SC_LINE /\
  (forall nm, pf_nm (rdW Wc memc) (pf_F v pos + PF_O_CN) nm -> pf_nm (rdW W2 mem2) (pf_F v pos + PF_O_CN) nm) /\
  pf_sl (rdW W2 mem2) (pf_s1 v) (PF_SL v pos) /\
  pf_fsh (rdW W2 mem2) (pf_SH v pos) PF_SC_LINE.
Proof.
intros fx1 v pos lyc Sc Wc rX memc mdc ly2 S2 W2 mem2 md2 rX' cf HB HFX HJr HJ2 (HP2 & Hly2 & HS2) HRG.
pose proof (a6_keeps_refuse B v pos lyc Sc Wc rX memc mdc PF_SC_LINE cf ly2 S2 W2 mem2 md2 EV_refuse HB HJr HP2)
  as HK.
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HRX.
assert (G : forall r x, In (r, x) (a5_FI B v) -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r x Hin. rewrite (a5_rg_get rX' _ r x HRG Hin), (a5_rg_get rX _ r x HRX Hin). reflexivity. }
assert (KR : forall r, In r [2; 3; 4; 8; 9; 22] -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; eapply G; unfold a5_FI; cbn [In];
    repeat (first [left; reflexivity | right]). }
pose proof (a6_base_move B VRO SSPX fx1 v pos lyc Sc Wc rX memc mdc PF_SC_LINE ly2 S2 W2 rX' mem2 md2
  HB HFX HJ2 Hly2 HS2 HP2 HK KR) as HB2.
split; [exact HB2|].
split.
- intros nm Hnm. apply (a6_nm_move v pos _ _ nm Hnm).
  intros a Ha. destruct HK as (_ & _ & _ & K4). apply K4. left. exact Ha.
- destruct HB2 as (_ & _ & _ & SL2 & FSH2). split; [exact SL2 | exact FSH2].
Qed.
End r.

End e.
End f.
End d.
