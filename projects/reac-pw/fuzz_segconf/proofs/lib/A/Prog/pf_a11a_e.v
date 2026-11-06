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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 491 of its 538 lines of code are new or changed and 406 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the ENTRY of segment A11a of reac_segconf_parse_file's
   walk, from the segment's start pc MODEL (0x8826c) to the fold loop's head LOOP (0x8829c) or to ZST (0x8851c).
   Part of segment A11a's proof (its entry), by the G3 walk owner, 2026-10-30. Proves no function (a segment lemma of
   reac_segconf_parse_file's image-A walk). The cut statements are lib/A/Prog/pf_a11a_k.v's.

     a11a_model_ok  0x8826c .. 0x88274  `sb zero, 0x5c(s11)` / 0x5d / 0x5e: low146's three shadow cells go from
                    0xf8 to 0x00, the frame's scope moves from PF_SC_LINE to PF_SC_L146. These three stores
                    write the shadow band, so this run is the PLAIN executor (lib/A/Prog/PaLibF.v
                    paj_run_to_sh), seeded with one writable region on s11's atom over cells [0x5c, 0x5f)
                    (lib/A/Prog/pf_a2.v pa2_s2's shape). The cut's facts are carried by a11e_base_scope.
     a11a_chk_ok    0x88278 .. 0x88298  check #18 (load1 at s9 = vp, the obligation route: vp lies in buf,
                    whose 64 shadow cells are 0 at both scopes), a2 = val[0], s4 = slot 0x30 = low146,
                    `beqz a2`: val[0] = 0 runs 0x88518 (a3 = 0) to ZST with li = 0, else a0 = 0, a1 = vp + 1
                    and LOOP with li = 0. The token executor (SegPaLib.v paj_run_tok), seeded with the byte
                    at vp (atom 32) and slot 0x30 (atom 33) as read-only regions (trim_l.v tl_entry's shape).

   The transport of the cut's facts across both runs is a11e_base_scope / a11e_cx_move, stated over this
   segment's write set (the three shadow cells SH + 92 .. 94) and proved from piece A2's pf_a2_g.v keep lemmas,
   which need no Section hypothesis. No Section hypothesis here either. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_pieces pf_a2_g pf_a2 pf_a11a_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require pf_a5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(** ** The frame's shadow at the two scopes: they differ only at low146's cells 92 .. 94
    (the low146 twins of pf_a5_k.v's a5_shb_buf / a5_shb_in) *)
Lemma a11e_shb_l146_out : forall sc b i, ~ (92 <= i < 95) ->
  pf_shb (PFSc (sc_cn sc) (sc_buf sc) (sc_low sc) b (sc_known sc)) i = pf_shb sc i.
Proof.
intros [cn bf lw l1 kn] b i H. unfold pf_shb. cbn [sc_cn sc_buf sc_low sc_l146 sc_known].
destruct (i <? 4); [reflexivity|]. destruct (i <? 6); [reflexivity|]. destruct (i <? 8); [reflexivity|].
destruct (i <? 72); [reflexivity|]. destruct (i <? 80); [reflexivity|]. destruct (i <? 88); [reflexivity|].
destruct (i <? 92) eqn:E3; [reflexivity|].
destruct (i <? 95) eqn:E4; [|reflexivity]. apply Z.ltb_ge in E3. apply Z.ltb_lt in E4. lia.
Qed.
Lemma a11e_shb_l146_in : forall sc i, 92 <= i < 95 -> pf_shb sc i = pf_io (sc_l146 sc).
Proof.
intros sc i H. unfold pf_shb.
replace (i <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 6) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 72) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 80) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 88) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 92) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 95) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma a11e_shb_l146 : forall i, ~ (92 <= i < 95) -> pf_shb PF_SC_L146 i = pf_shb PF_SC_LINE i.
Proof. intros i H. exact (a11e_shb_l146_out PF_SC_LINE true i H). Qed.
Lemma a11e_shb_l146_0 : forall i, 92 <= i < 95 -> pf_shb PF_SC_L146 i = 0.
Proof. intros i H. rewrite (a11e_shb_l146_in PF_SC_L146 i H). reflexivity. Qed.

(** ** Small engine facts (trim_s.v tr_br_eq0, trim_k.v tr_ag_ew / tr_ag32, verbatim) *)
Lemma a11e_br_eq0 : forall E n v b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> (v =? 0) = b.
Proof.
intros E n v b H Hv Hc. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit in Hc by lia. exact Hc.
Qed.
Lemma a11e_ag_ew : forall E0 E (k n : nat) v, env_agree k E0 E -> (n < k)%nat -> ew E0 n = Z_to_bv 64 v -> ew E n = Z_to_bv 64 v.
Proof. intros E0 E k n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
Lemma a11e_ag32 : forall (regs1 : bvmap 5 word) extra E0 E (k : nat), (32 <= k)%nat ->
  env_agree 32 (Ereg regs1 extra) E0 -> env_agree k E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E k Hk H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.

(** ** Register lists *)
Lemma a11e_rg_all : forall (rX rX' : bvmap 5 word) (l : list Z) L,
  (forall k, In k l -> getr rX' (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k)) ->
  Forall (fun rv => In (fst rv) l) L -> pf_rg rX L -> pf_rg rX' L.
Proof.
intros rX rX' l L HK HL H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HK _ (HL rv Hin)). exact (H rv Hin).
Qed.
Lemma a11e_rg_one : forall (rX rX' : bvmap 5 word) (l : list Z) L r x,
  (forall k, In k l -> getr rX' (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k)) ->
  pf_rg rX L -> In (r, x) L -> In r l -> getr rX' (Z_to_bv 5 r) = w64 x.
Proof.
intros rX rX' l L r x HK H Hin Hr. rewrite (HK r Hr). exact (proj1 (Forall_forall _ _) H (r, x) Hin).
Qed.
(* the registers the two runs never write *)
Definition A11E_KM : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition A11E_KC : list Z := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27].
Ltac a11e_inS := solve [cbn [In app A11E_KC A11E_KM]; repeat first [left; reflexivity | right]].

(** ** The two seeds *)
(* MODEL (0x8826c): every register its own atom; low146's three shadow cells, writable, on s11's atom 27 *)
Definition a11e_mss : sstate :=
  mkSS PF_MODEL sr_atoms [YP09.mkRegion (Some 27%nat) 0x5c 0x5f 0x5c 0x5f []] None (mkFacts [] [] []).
(* CHK (0x88278): every register its own atom; the byte at s9 = vp (atom 32, read-only) and slot s1 + 0x30
   (atom 33 = low146, read-only); s6 = atom 22 is the shadow base of check #18 *)
Definition a11e_cregions : smem :=
  [ YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))];
    YP09.mkRegion (Some 9%nat) 0x30 0x38 0 0 [YP09.mkChunk 0x30 (CVal 8 (SOff 33 0))] ].
Definition a11e_cfacts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF SB SB 0); (25%nat, mkAF 4096 (2 ^ 47 - 1) 0);
            (32%nat, mkAF 0 255 0) ] [] [].
Definition a11e_css : sstate := mkSS A11_CHK sr_atoms a11e_cregions None a11e_cfacts.
Definition a11e_Bx : sv := SOff 22 0.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(** ** The segment's write set and what keeps outside it *)
Definition a11e_W3 (v : pfv) (pos a : Z) : Prop := pf_SH v pos + 92 <= a < pf_SH v pos + 95.
Definition a11e_kept (v : pfv) (pos : Z) (rd rd' : reader) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ a11e_W3 v pos a -> rd' a = rd a) /\
  (forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> rd' a <> None).

Lemma a11e_kept_tot : forall v pos (rd rd' : reader), (forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a) ->
  a11e_kept v pos rd rd'.
Proof. intros v pos rd rd' KM. split; [intros a Ha _; exact (KM a Ha) | intros a Ha Hv; rewrite (KM a Ha); exact Hv]. Qed.

Lemma a11e_kept_pa2 : forall v pos rd rd', a11e_kept v pos rd rd' -> pa2_kept v pos rd rd'.
Proof.
intros v pos rd rd' [K V]. split; [|exact V].
intros a Ha Hn. apply K; [exact Ha|]. intros Hw. apply Hn. unfold pa2_Wr. right; right. unfold a11e_W3 in Hw. lia.
Qed.

(* pf_a2.v pa2_SHb, with F mod 8 = 0 *)
Lemma a11e_SHb : forall v pos, pa2_geoP v pos ->
  pf_SH v pos = SHADOW_OFF + pf_F v pos / 8 /\ 0x7fff8000 + 512 <= pf_SH v pos /\
  pf_SH v pos + 256 <= 0x10007fff8000 /\ pf_F v pos mod 8 = 0.
Proof.
intros v pos (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _). pose proof asan_consts as (C1 & _).
assert (F8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
split; [reflexivity|]. unfold pf_SH, shadow_addr, SHADOW_OFF. split; [lia|]. split; [lia | exact F8].
Qed.

(* a byte of the frame, or of the spill area above s1, is an address outside the write set *)
Lemma a11e_frame_nw : forall v pos a, pa2_geoP v pos -> pf_F v pos <= a < pf_F v pos + 2048 ->
  0 <= a < 2 ^ 64 /\ ~ a11e_W3 v pos a.
Proof.
intros v pos a G Ha. pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (a11e_SHb v pos G) as (_ & SH1 & SH2 & _). pose proof asan_consts as (C1 & _).
unfold a11e_W3. split; [lia|]. destruct F4 as [F4 | F4]; lia.
Qed.
Lemma a11e_slot_nw : forall v pos a, pa2_geoP v pos -> pf_s1 v <= a < pf_s1 v + 0xc0 ->
  0 <= a < 2 ^ 64 /\ ~ a11e_W3 v pos a.
Proof.
intros v pos a G Ha. pose proof G as (S1 & S2 & S3 & S4 & _).
destruct (a11e_SHb v pos G) as (_ & SH1 & SH2 & _). pose proof asan_consts as (C1 & _).
unfold a11e_W3. lia.
Qed.

(* buf's 512 bytes are addressable whenever buf is in scope (its 64 shadow cells 8 .. 71 are 0) *)
Lemma a11e_buf_ra : forall (rd : reader) v pos sc, pf_F v pos mod 8 = 0 -> sc_buf sc = true ->
  pf_fsh rd (pf_SH v pos) sc -> range_addressable rd SHADOW_OFF (pf_F v pos + PF_O_BUF) 512.
Proof.
intros rd v pos sc H8 Hb H. apply zero_shadow_range.
- unfold PF_O_BUF. rewrite Z.add_mod, H8 by lia. reflexivity.
- reflexivity.
- unfold zero_shadow. intros i Hi. change (512 / 8) with 64 in Hi.
  rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) PF_O_BUF H8).
  change (shadow_of_addr SHADOW_OFF (pf_F v pos)) with (pf_SH v pos). change (PF_O_BUF / 8) with 8.
  rewrite <- Z.add_assoc. rewrite (H (8 + i) ltac:(lia)). rewrite pf_a5_k.a5_shb_in by lia. rewrite Hb. reflexivity.
Qed.

Section k.
Variables (v : pfv) (pos : Z) (rd rd' : reader).
Hypothesis GEO : pa2_geoP v pos.
Hypothesis K : a11e_kept v pos rd rd'.

(* a C string inside the frame, with its tail granule *)
Lemma a11e_k_str : forall p s, pf_F v pos <= p -> p + Z.of_nat (length s) + 8 <= pf_F v pos + 2048 ->
  sa_str rd p s -> sa_str rd' p s.
Proof.
intros p s H1 H2 [[Hz Hn] Ht]. split; [split; [|exact Hn]|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  destruct (a11e_frame_nw v pos (p + Z.of_nat i) GEO ltac:(lia)) as [Ha Hw].
  rewrite (proj1 K _ Ha Hw). apply Hz. rewrite length_app. cbn [length]. lia.
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)) as M.
  destruct (a11e_frame_nw v pos x GEO ltac:(lia)) as [Ha _].
  exact (proj2 K x Ha (Ht x Hx)).
Qed.
(* cur_name at F + 0x20 *)
Lemma a11e_k_nm : forall nm, pf_nm rd (pf_F v pos + PF_O_CN) nm -> pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof.
intros nm (f & Hb & He). exists f. split; [|exact He].
pose proof (proj1 He) as Hl.
intros i Hi. rewrite Hl in Hi.
destruct (a11e_frame_nw v pos (pf_F v pos + PF_O_CN + Z.of_nat i) GEO ltac:(unfold PF_O_CN; lia)) as [Ha Hw].
rewrite (proj1 K _ Ha Hw). apply Hb. rewrite Hl. exact Hi.
Qed.
(* spill slots s1 + o, 0 <= o <= 0xb8 *)
Lemma a11e_k_sl : forall L, Forall (fun ov => 0 <= fst ov <= 0xb8) L -> pf_sl rd (pf_s1 v) L -> pf_sl rd' (pf_s1 v) L.
Proof.
intros L HL H. unfold pf_sl in *. rewrite Forall_forall in *. intros [o x] Hin.
specialize (H _ Hin). specialize (HL _ Hin). cbn [fst snd] in *.
rewrite (rdword_ext rd rd'); [exact H|].
intros k Hk. destruct (a11e_slot_nw v pos (pf_s1 v + o + k) GEO ltac:(lia)) as [Ha Hw].
exact (proj1 K _ Ha Hw).
Qed.
(* the split key line in buf *)
Lemma a11e_k_kv : forall line kp vp key val, pf_kv rd v pos line kp vp key val -> pf_kv rd' v pos line kp vp key val.
Proof.
intros line kp vp key val (HE & HK & HKi & HV & HVi).
pose proof HKi as (Hk1 & Hk2). pose proof HVi as (Hv1 & Hv2). unfold PF_O_BUF in Hk1, Hk2, Hv1, Hv2.
split; [exact HE|].
split; [apply a11e_k_str; [lia | lia | exact HK]|].
split; [exact HKi|].
split; [apply a11e_k_str; [lia | lia | exact HV]|].
exact HVi.
Qed.
End k.

(* the frame's shadow across a run that changed no byte *)
Lemma a11e_fsh_tot : forall v pos (rd rd' : reader) sc, pa2_geoP v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a) -> pf_fsh rd (pf_SH v pos) sc -> pf_fsh rd' (pf_SH v pos) sc.
Proof.
intros v pos rd rd' sc G KM H i Hi. destruct (a11e_SHb v pos G) as (_ & SH1 & SH2 & _).
rewrite KM by lia. exact (H i Hi).
Qed.

(* the registers a run leaves as their own atoms keep their values (pf_a7_q.v a7_regs_kept, any env) *)
Lemma a11e_regs_kept : forall E ss (H : word -> bool) ms (rX : bvmap 5 word) extra (l : list Z),
  st_ok_pi SEGS VAL E ss (restrict H ms) -> env_agree 32 (Ereg rX extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    (map (Z_to_bv 5) l) = true ->
  forall k, In k l -> getr (ms_regs ms) (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k).
Proof.
intros E ss H ms rX extra l HS HA Hl k Hk.
exact (regs_kept_of_st_ok_pi E ss (restrict H ms) rX extra (map (Z_to_bv 5) l) HS HA Hl (Z_to_bv 5 k) (in_map _ _ _ Hk)).
Qed.

(** ** The CHK seed (trim_l.v tl_entry's shape) *)
Definition a11e_cE (rX : bvmap 5 word) (C L : Z) : env := Eimg (Ereg rX [Z_to_bv 64 C; Z_to_bv 64 L]).

Lemma a11e_centry : forall (W : world SEGS) (rX : bvmap 5 word) memc s1 vp C L,
  getr rX (Z_to_bv 5 9) = w64 s1 -> getr rX (Z_to_bv 5 22) = w64 SB -> getr rX (Z_to_bv 5 25) = w64 vp ->
  2 ^ 46 <= s1 -> s1 + 0x38 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  4096 <= vp <= 2 ^ 47 - 1 -> vp + 1 <= s1 + 0x30 ->
  0 <= C <= 255 -> rdW W memc vp = Some C ->
  0 <= L < 2 ^ 64 -> rdword (rdW W memc) (s1 + 0x30) = Some L ->
  st_ok_pi SEGS VAL (a11e_cE rX C L) a11e_css (restrict (w_H W) (mkst rX (Z_to_bv 64 (BASE + A11_CHK)) memc (seg_rom SEGS))).
Proof.
intros W rX memc s1 vp C L H9 H22 H25 Hs1 Hs2 Hs3 Hvp Hout HC HrdC HL K30.
set (E := a11e_cE rX C L).
assert (E9 : ew E 9 = Z_to_bv 64 s1)
  by (subst E; unfold a11e_cE; rewrite (ew_Eimg_Ereg_nat rX _ 9 (Z_to_bv 5 9) eq_refl); exact H9).
assert (E22 : ew E 22 = Z_to_bv 64 SB)
  by (subst E; unfold a11e_cE; rewrite (ew_Eimg_Ereg_nat rX _ 22 (Z_to_bv 5 22) eq_refl); exact H22).
assert (E25 : ew E 25 = Z_to_bv 64 vp)
  by (subst E; unfold a11e_cE; rewrite (ew_Eimg_Ereg_nat rX _ 25 (Z_to_bv 5 25) eq_refl); exact H25).
assert (E32 : ew E 32 = Z_to_bv 64 C)
  by (subst E; unfold a11e_cE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 L)
  by (subst E; unfold a11e_cE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
rewrite restrict_mkst_fx. unfold a11e_css. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold a11e_cregions. constructor; [|constructor; [|constructor]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E25, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
    destruct (aview_byte SEGS (w_H W) memc vp C HrdC) as (b & Hb & Hv & _).
    exists b. split.
    * cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E32.
      rewrite !Z.add_0_r, (unsigned_lit_small C), (unsigned_lit_small C) by lia. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
      subst C. apply Z_to_bv_bv_unsigned.
    * rewrite !Z.add_0_r. exact Hb.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ s1 0x30 8%N (SOff 33 0) L).
    * cbn [sv_denot]. rewrite E33, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * lia.
    * exact (val_mem_of_rdword SEGS (w_H W) memc _ _ K30).
- unfold a11e_cregions. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
  rewrite E25, E9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I].
  cbn [a11e_cfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E22, E25, E32, !unsigned_lit_small by (unfold SB; lia).
  try change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(** ** The transport: pf_base after a run that wrote at most the three cells SH + 92 .. 94, at a new scope *)
Lemma a11e_base_scope : forall v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc' sc',
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  a11e_kept v pos (rdW Wc memc) (rdW Wc memc') ->
  pf_rg rX' [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (22, SHADOW_OFF)] ->
  pf_fsh (rdW Wc memc') (pf_SH v pos) sc' ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' sc'.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc' sc' HB HJ' K HRG HFSH.
destruct HB as (HCX & HFI & HOBJ & HSL & _).
destruct (pa2_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (GEO & Hin & EF & _ & HAR).
pose proof (a11e_kept_pa2 v pos _ _ K) as K2.
destruct HFI as (_ & Hly & HSc & HP0 & HSV & HFL & HFRM & _).
split; [exact HCX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HP0|].
  split; [exact (pa2_keep_saved v pos _ _ _ GEO K2 HSV)|].
  split; [exact (pa2_keep_flag v pos _ _ GEO K2 HFL)|].
  split; [exact HFRM | exact HRG]. }
split; [exact (pa2_keep_obj B v pos lyc Sc Wc memc mdc _ _ GEO HAR Hin EF K2 HOBJ)|].
split; [|exact HFSH].
apply (a11e_k_sl v pos _ _ GEO K); [|exact HSL].
unfold PF_SL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia.
Qed.

(* the same for what every internal cut of A11a carries (pf_a11a_k.v a11_cx), at scope PF_SC_L146 *)
Lemma a11e_cx_move : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val sc rX' memc' mdc',
  pf_base B v pos lyc Sc Wc rX memc mdc sc -> pf_mid v o ln d n ->
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) ->
  sa_str (rdW Wc memc) vp val -> pf_inb (pf_F v pos + PF_O_BUF) vp val ->
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, seg_spec.rseg_addr (p_c v) gi)] ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  a11e_kept v pos (rdW Wc memc) (rdW Wc memc') ->
  pf_rg rX' [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (22, SHADOW_OFF)] ->
  pf_fsh (rdW Wc memc') (pf_SH v pos) PF_SC_L146 ->
  a11_cx B n v pos lyc Sc Wc rX' memc' mdc' cf nm o ln d gi vp val.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val sc rX' memc' mdc' HB HMID HST HSTR HINB HSL HJ' K HRG HFSH.
pose proof HB as (HCX & HFI & HOBJ & _).
destruct (pa2_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (GEO & Hin & EF & _ & HAR).
pose proof (a11e_kept_pa2 v pos _ _ K) as K2.
pose proof HOBJ as (_ & _ & _ & _ & HC5 & _).
pose proof HINB as (Hb1 & Hb2). unfold PF_O_BUF in Hb1, Hb2.
split; [exact (a11e_base_scope v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc' PF_SC_L146 HB HJ' K HRG HFSH)|].
split; [exact HMID|].
split.
{ destruct HST as (HRC & HCO & HNM & HCN).
  split; [exact (pa2_keep_rconf B v pos lyc Sc Wc memc mdc _ _ cf GEO HAR Hin EF K2 HC5 HRC)|].
  split; [exact HCO|]. split; [exact (a11e_k_nm v pos _ _ GEO K nm HNM)|]. exact HCN. }
split; [apply (a11e_k_str v pos _ _ GEO K); [lia | lia | exact HSTR]|].
split; [exact HINB|].
apply (a11e_k_sl v pos _ _ GEO K); [|exact HSL].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia.
Qed.

(** ** Tactics *)
Ltac a11e_awr := lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* after a token run that writes nothing (trim_l.v tl_after, without the presence fact): the environment agrees
   with E0 below k (HAE), the memory reads as the cut's (KM) *)
Ltac a11e_after E0 HAE KM :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)),
    HG : mem_grows (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)) |- _ =>
    lazymatch type of HAE with env_agree ?k _ _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in
    assert (HAEn : env_agree k E0 En) by (env_agree_chain HAE);
    assert (KMn : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H _) (ms_mem msn) a = aview SEGS (w_H _) _ a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          rewrite (kept_of_frame (segs := SEGS) Eo _ _ m0 (ms_mem msn) (fun _ => False) HFr);
          [ exact (KM a Ha)
          | let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
            intros b wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
            destruct Hin
          | exact Ha | tauto ]);
    clear HFr HG HAE KM; rename HAEn into HAE; rename KMn into KM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
    end
  end.
Ltac a11e_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
Ltac a11e_rgk HK HL := eapply (a11e_rg_one _ _ _ _ _ _ HK HL); [a11e_inS | a11e_inS].

(** ** CHK, 0x88278 .. 0x88298 *)
(* 0x88278 .. 0x88298: check #18, the first byte of the value, s4 = low146, the empty-value branch *)
Theorem a11a_chk_ok : forall n : nat,
  (forall j : nat, A11_ZST_stmt B n j) -> A11_LOOP_stmt B n 0 -> A11_CHK_stmt B n.
Proof.
intros n HZST HLOOP. unfold A11_CHK_stmt.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val HI.
destruct HI as (HCXa & HKV & HRG).
destruct HCXa as (HB & HMID & HST & HSTR & HINB & HSL0).
pose proof HB as (HCX & HFI & HOBJ & HSLS & HFSH).
destruct (pa2_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (GEO & Hin & EF & _ & HAR).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & HRGF).
pose proof GEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (a11e_SHb v pos GEO) as (ESH & SH1 & SH2 & F8).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HINB as (Hvp1 & Hvp2). unfold PF_O_BUF in Hvp1, Hvp2.
unfold PF_RL, PF_RM in HRG. cbn [app] in HRG.
(* the registers the seed names *)
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (pf_a5_k.a5_rg_get rX _ 9 _ HRGF); a11e_inS).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF) by (apply (pf_a5_k.a5_rg_get rX _ 22 _ HRGF); a11e_inS).
assert (R25 : getr rX (Z_to_bv 5 25) = w64 vp) by (apply (pf_a5_k.a5_rg_get rX _ 25 _ HRG); a11e_inS).
(* the byte at vp (val[0], or the NUL when val is empty) and slot 0x30 *)
assert (Hnf : ~ In 0 val) by exact (proj2 (proj1 HSTR)).
assert (VC : rdW Wc memc vp = Some (nth 0 val 0)).
{ destruct HSTR as ((HZ & _) & _). pose proof (HZ 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as V.
  cbn [Z.of_nat] in V. rewrite Z.add_0_r in V. rewrite V. destruct val; reflexivity. }
destruct (aview_byte SEGS (w_H Wc) memc vp _ VC) as (_ & _ & _ & HCr).
assert (K30 : rdword (rdW Wc memc) (pf_s1 v + 0x30) = Some (pf_F v pos + PF_O_L146)).
{ exact (proj1 (Forall_forall _ _) HSLS (0x30, pf_F v pos + PF_O_L146) ltac:(unfold PF_SL; a11e_inS)). }
(* buf is addressable (buf is in scope at PF_SC_L146) *)
assert (HRA : range_addressable (rdW Wc memc) SHADOW_OFF (pf_F v pos + PF_O_BUF) 512)
  by exact (a11e_buf_ra _ v pos PF_SC_L146 F8 eq_refl HFSH).
(* the seed *)
pose proof (a11e_centry Wc rX memc (pf_s1 v) vp (nth 0 val 0) (pf_F v pos + PF_O_L146) R9 R22 R25
  ltac:(lia) ltac:(lia) S5 ltac:(lia) ltac:(lia) ltac:(lia) VC ltac:(unfold PF_O_L146; lia) K30) as HS.
assert (HEI : img_env VAL A_LIM (a11e_cE rX (nth 0 val 0) (pf_F v pos + PF_O_L146))) by (unfold a11e_cE; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg rX [Z_to_bv 64 (nth 0 val 0); Z_to_bv 64 (pf_F v pos + PF_O_L146)])
                (a11e_cE rX (nth 0 val 0) (pf_F v pos + PF_O_L146)))
  by (split; [intros k Hk; unfold a11e_cE; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r ->
    ew (a11e_cE rX (nth 0 val 0) (pf_F v pos + PF_O_L146)) k = getr rX r)
  by (intros k r Hk; unfold a11e_cE; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew (a11e_cE rX (nth 0 val 0) (pf_F v pos + PF_O_L146)) 32 = Z_to_bv 64 (nth 0 val 0))
  by (unfold a11e_cE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew (a11e_cE rX (nth 0 val 0) (pf_F v pos + PF_O_L146)) 33 = Z_to_bv 64 (pf_F v pos + PF_O_L146))
  by (unfold a11e_cE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
revert HS HEI HA0 EE E32 E33. generalize (a11e_cE rX (nth 0 val 0) (pf_F v pos + PF_O_L146)) as E0.
intros E0 HS HEI HA0 EE E32 E33.
assert (E22 : ew E0 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl); exact R22).
assert (E25 : ew E0 25 = Z_to_bv 64 vp) by (rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl); exact R25).
pose proof (env_agree_refl 34 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
assert (SHOK : sh_ok SEGS a11e_Bx [] E0 (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + A11_CHK)) with (Z_to_bv 64 (BASE + A11_CHK)).
(* 0x88278 .. 0x88290: check #18 (the obligation that vp is addressable), lbu a2, ld s4, up to `beqz a2` *)
paj_run_tok RUN HS HJ SHOK Bspan;
  [ cbn [ms_mem]; unfold a11e_Bx; rewrite (U_atom _ 22 SB E22), (U_atom _ 25 _ E25) by (unfold SB; lia);
    rewrite SB_SHADOW_OFF;
    exact (range_addressable_sub _ _ (pf_F v pos + PF_O_BUF) 512 vp 1 HRA ltac:(unfold PF_O_BUF; lia)
      ltac:(unfold PF_O_BUF; lia)) ..
  | a11e_awr | ].
a11e_after E0 HAE KM.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* val[0] = 0: 0x88518 `mv a3, zero`, then ZST with li = 0 *)
  pose proof (a11e_br_eq0 _ 32 _ _ (a11e_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) Hc) as L0.
  apply Z.eqb_eq in L0. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan A11_ZST. { a11e_awr. }
  a11e_after E0 HAE KM.
  pose proof (a11e_regs_kept _ _ _ _ rX _ A11E_KC HS (a11e_ag32 _ _ _ _ 34 ltac:(lia) HA0 HAE)
    ltac:(vm_compute; reflexivity)) as HK.
  prreg HS (Z_to_bv 5 13) N13. prreg HS (Z_to_bv 5 20) N20.
  first [rewrite E33 in N20 | rewrite (a11e_ag_ew _ _ _ 33 _ HAE ltac:(lia) E33) in N20].
  assert (Hlen0 : 0%nat = length (r_low val 0 24)).
  { clear - L0 Hnf. destruct val as [|x r]; [reflexivity|].
    cbn [nth] in L0. subst x. exfalso. apply Hnf. left. reflexivity. }
  pmkst HS.
  lazymatch goal with |- SRr ?S ?W (mkCfg (mkst ?rg ?pcw ?mm ?rom) ?mdn) ?Q =>
    change (SRr S W (cfg_at SEGS (BASE + A11_ZST) rg mm mdn) Q) end.
  apply (HZST 0%nat v pos lyc Sc Wc _ _ _ cf nm o ln d gi vp val).
  split.
  { eapply (a11e_cx_move n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val PF_SC_L146);
      [exact HB | exact HMID | exact HST | exact HSTR | exact HINB | exact HSL0 | exact HJ
      | exact (a11e_kept_tot v pos _ _ KM) | | exact (a11e_fsh_tot v pos _ _ PF_SC_L146 GEO KM HFSH)].
    unfold pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; a11e_rgk HK HRGF. }
  split; [exact Hlen0|]. split; [unfold A11_CAP; lia|]. split; [intros j Hj; exfalso; lia|].
  unfold pf_rg, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    first [exact N13 | exact N20 | a11e_rgk HK HRG | rewrite N13; vm_compute; reflexivity].
- (* val[0] <> 0: 0x88294 a0 = 0, 0x88298 a1 = vp + 1, then LOOP with li = 0 *)
  pose proof (a11e_br_eq0 _ 32 _ _ (a11e_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) Hc) as L0.
  apply Z.eqb_neq in L0. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan A11_LOOP. { a11e_awr. }
  a11e_after E0 HAE KM.
  pose proof (a11e_regs_kept _ _ _ _ rX _ A11E_KC HS (a11e_ag32 _ _ _ _ 34 ltac:(lia) HA0 HAE)
    ltac:(vm_compute; reflexivity)) as HK.
  prreg HS (Z_to_bv 5 10) N10. prreg HS (Z_to_bv 5 11) N11. prreg HS (Z_to_bv 5 12) N12.
  prreg HS (Z_to_bv 5 20) N20.
  first [rewrite E33 in N20 | rewrite (a11e_ag_ew _ _ _ 33 _ HAE ltac:(lia) E33) in N20].
  first [rewrite E32 in N12 | rewrite (a11e_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) in N12].
  first [rewrite E25 in N11 | rewrite (a11e_ag_ew _ _ _ 25 _ HAE ltac:(lia) E25) in N11].
  rewrite unsigned_lit_small in N11 by lia.
  assert (Hlen1 : (0 < length val)%nat).
  { clear - L0. destruct val as [|x r]; [cbn [nth] in L0; lia | cbn [length]; lia]. }
  pmkst HS.
  lazymatch goal with |- SRr ?S ?W (mkCfg (mkst ?rg ?pcw ?mm ?rom) ?mdn) ?Q =>
    change (SRr S W (cfg_at SEGS (BASE + A11_LOOP) rg mm mdn) Q) end.
  apply (HLOOP v pos lyc Sc Wc _ _ _ cf nm o ln d gi vp val).
  split.
  { eapply (a11e_cx_move n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val PF_SC_L146);
      [exact HB | exact HMID | exact HST | exact HSTR | exact HINB | exact HSL0 | exact HJ
      | exact (a11e_kept_tot v pos _ _ KM) | | exact (a11e_fsh_tot v pos _ _ PF_SC_L146 GEO KM HFSH)].
    unfold pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; a11e_rgk HK HRGF. }
  split; [unfold A11_CAP; lia|]. split; [exact Hlen1|]. split; [intros j Hj; exfalso; lia|].
  unfold pf_rg, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    first [exact N10 | exact N11 | exact N12 | exact N20 | a11e_rgk HK HRG | rewrite N10; vm_compute; reflexivity].
Qed.

(** ** MODEL, 0x8826c .. 0x88274 *)
(* 0x8826c .. 0x88274: the three shadow stores that put low146 in scope *)
Theorem a11a_model_ok : forall n : nat,
  A11_CHK_stmt B n -> forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val,
  INV_KV B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_MODEL) rX memc mdc) (a11_post B v cf gi nm val o ln).
Proof.
intros n HCHK v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val HI.
destruct HI as (HB & HMID & HST & HKV & HSL0 & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSLS & HFSH).
destruct (pa2_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (GEO & Hin & EF & _ & HAR).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & HRGF).
destruct (a11e_SHb v pos GEO) as (ESH & SH1 & SH2 & F8).
pose proof HKV as (_ & _ & _ & HVS & HVI).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (_ & _ & _ & Hsh).
rewrite EF in Hsh. change (fs_frame_bytes 5 / 8) with 256 in Hsh.
change (shadow_addr (pf_F v pos)) with (pf_SH v pos) in Hsh.
unfold PF_RL, PF_RM in HRG. cbn [app] in HRG.
assert (R27 : getr rX (Z_to_bv 5 27) = w64 (pf_SH v pos)) by (apply (pf_a5_k.a5_rg_get rX _ 27 _ HRG); a11e_inS).
set (E := Eimg (Ereg rX [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg rX []) E)
  by (subst E; split; [intros k Hk; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (U27 : bv_unsigned (ew E 27) = pf_SH v pos)
  by (subst E; rewrite (ew_Eimg_Ereg_nat rX [] 27 (Z_to_bv 5 27) eq_refl), R27; unfold w64;
      apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E a11e_mss
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_MODEL)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold a11e_mss. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U27.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o0 Ho0. apply (apresent_writable SEGS). exact (proj1 (Hsh o0 ltac:(lia))).
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + PF_MODEL)) with (Z_to_bv 64 (BASE + PF_MODEL)).
(* the plain run: the three stores, written into low146's cells in the frame's own shadow *)
paj_run_to_sh RUNTOP HS HJ A11_CHK.
{ intros a (r & Hr & Ha). unfold a11e_mss in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
  rewrite EF. change (fs_frame_bytes 5 / 8) with 256. change (shadow_addr (pf_F v pos)) with (pf_SH v pos).
  rewrite U27 in Ha. lia. }
cbn [ms_mem mkst] in HFr, HG, HF.
a11e_clear_md.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ a11e_W3 v pos a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) E (ss_mem a11e_mss) (w_H Wc) memc (ms_mem ms) (a11e_W3 v pos) HFr);
    [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U27 in Hrr;
    unfold a11e_W3; lia |]).
  destruct Hin'. }
assert (V3 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
assert (KK : a11e_kept v pos (rdW Wc memc) (rdW Wc (ms_mem ms)))
  by (split; [exact K3 | intros a _ Hv; exact (V3 a Hv)]).
(* the three cells the run wrote *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
cbn [ms_mem restrict] in HR0.
assert (C3 : forall i, 92 <= i < 95 -> rdW Wc (ms_mem ms) (pf_SH v pos + i) = Some 0).
{ intros i Hi. apply (pa2_cell_of_region E (w_H Wc) (ms_mem ms) 27 _ _ _ _ _ _ i _ HR0 U27). revert i Hi.
  apply (pa2_zrange (fun i => pa2_cell_ok _ i 0) 92 3). vm_compute. reflexivity. }
(* the frame's shadow at the new scope *)
assert (FSH' : pf_fsh (rdW Wc (ms_mem ms)) (pf_SH v pos) PF_SC_L146).
{ intros i Hi. destruct (Z_lt_le_dec i 92) as [H92 | H92]; [|destruct (Z_lt_le_dec i 95) as [H95 | H95]].
  - rewrite K3 by (try unfold a11e_W3; lia). rewrite a11e_shb_l146 by lia. exact (HFSH i Hi).
  - rewrite (C3 i ltac:(lia)). rewrite (a11e_shb_l146_0 i ltac:(lia)). reflexivity.
  - rewrite K3 by (try unfold a11e_W3; lia). rewrite a11e_shb_l146 by lia. exact (HFSH i Hi). }
(* the registers: the three stores write none *)
pose proof (a11e_regs_kept E _ (w_H Wc) ms rX [] A11E_KM HS HA0 ltac:(vm_compute; reflexivity)) as HK.
pmkst HS.
lazymatch goal with |- SRr ?S ?W (mkCfg (mkst ?rg ?pcw ?mm ?rom) ?mdn) ?Q =>
  change (SRr S W (cfg_at SEGS (BASE + A11_CHK) rg mm mdn) Q) end.
apply (HCHK v pos lyc Sc Wc _ _ _ cf nm o ln d gi kp vp key val).
split.
{ eapply (a11e_cx_move n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val PF_SC_LINE);
    [exact HB | exact HMID | exact HST | exact HVS | exact HVI | exact HSL0 | exact HJ | exact KK | | exact FSH'].
  apply (a11e_rg_all rX _ A11E_KM _ HK); [|exact HRGF].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; a11e_inS. }
split; [exact (a11e_k_kv v pos _ _ GEO KK _ _ _ _ _ HKV)|].
unfold PF_RL, PF_RM. cbn [app].
apply (a11e_rg_all rX _ A11E_KM _ HK); [|exact HRG].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; a11e_inS.
Qed.

End e.
End f.
End d.
