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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 343 of its 392 lines of code are new or changed and 404 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B12 of
   reac_segconf_parse_file's walk, the exit piece STORE (reac_segconf.c:278-279, `cur->ignore = b; cur->ignore_set = 1`,
   then the provenance snprintf's arguments R:280): STORE 0x88df8 -> PROV2 0x88e4c, the statement B12_STORE_stmt of
   lib/B/Prog/pf_seg_B12_k.v. A B12 sub-lane of the image-B G3 walk owner, 2026-10-30. proves no function (kind: segment lemma of
   reac_segconf_parse_file's walk, piece STORE of segment B12). ADAPTED from a working branch + U piece walks
   (lib/U/Prog/pf_p8.v: the trap T31 and the two stores), re-derived on image B's code
   (the neutral excerpt reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s).
   THE CODE (21 hot instructions 0x88df8-0x88e48; the cold arms 0x89044-0x89060 and the error calls 0x892ac / 0x892b0
   are not reached):
     0x88df8 `andi a0,a3,3`; 0x88dfc `bnez a0` -> unimp 0x891c8 (UBSan trap T31): a3 = cur = c + 356 gi (premise),
       c mod 16 = 0 (pf_tf), so cur & 3 = 0: the run stops at the branch, the taken side is refuted (U_and_lit);
     0x88e00 `ld a3,192(s1)` (cur, slot 0xc0); check B#33 0x88e04-0x88e14 (store4 at cur + 24; slow arm 0x89044-0x89050,
       error call 0x892ac errpath_store4) and check B#34 0x88e1c-0x88e2c (store4 at cur + 28; slow arm 0x89054-0x89060,
       error call 0x892b0): both decided by the token executor from the shadow entry b12s_SH of cur's [24, 32) (c's
       sa_addr in pf_obj, kept to the cut's memory; [24, 32) is application memory, b12x_geo);
     0x88e18 `sw s3,24(a3)` (ignore = b), 0x88e30 `li a0,1`, 0x88e34 `sw a0,28(a3)` (ignore_set = 1): the writable
       region on cur's atom (awr_ok: the footprint RC_PARSE_W c, c's live block);
     0x88e38 a0 = cur + 0x100 (&seg[gi].ignore_file), 0x88e3c/0x88e40 a2 = "%s" (0x21340, listing object 35),
       0x88e44 a1 = 96, 0x88e48 a3 = c->reading (slot 0x48); falls into PROV2 0x88e4c, where HA_PROV2 is applied to
       INV_PROV2 (c's bytes rebuilt with P8.p8_rconf_ign, the rest by the keep family pf_seg_B12_x.v).
   UBSan trap sites: T31 (0x88dfc). Inline checks: B#33, B#34. Calls: none (PROV2's snprintf is the next segment's).
   Section hypothesis: OBJ (seg_val_objs: the "%s" literal's listing object 35). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require pf_p8_lemmas pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegGlob SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B12_k pf_seg_B12_x pf_seg_B12_n.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module P8 := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.pf_p8_lemmas.
Module PA := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.pfA_facts.
Module LM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.

(** ** Byte lists *)
Lemma b12s_upd_nth : forall (cs bs : list byte) k i d, (k + length bs <= length cs)%nat ->
  nth i (LM.upd_bytes cs k bs) d =
  if (i <? k)%nat then nth i cs d else if (i <? k + length bs)%nat then nth (i - k) bs d else nth i cs d.
Proof.
intros cs bs k i d H. unfold LM.upd_bytes.
destruct (Nat.ltb_spec i k) as [H1|H1].
- rewrite app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
  destruct (Nat.ltb_spec i k); [reflexivity | lia].
- rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
  replace (Nat.min k (length cs)) with k by lia.
  destruct (Nat.ltb_spec i (k + length bs)) as [H2|H2].
  + rewrite app_nth1 by lia. reflexivity.
  + rewrite app_nth2 by lia. rewrite nth_skipn. f_equal. lia.
Qed.
Lemma b12s_upd_len : forall (cs bs : list byte) k, (k + length bs <= length cs)%nat ->
  length (LM.upd_bytes cs k bs) = length cs.
Proof.
intros cs bs k H. unfold LM.upd_bytes. rewrite !length_app, length_firstn, length_skipn. lia.
Qed.

(** ** The counters and the current entry after an entry edit *)
Lemma b12s_cnt_upd : forall rc gi g k k', pf_cnt rc k -> (k' <= k)%nat -> pf_cnt (r_upd rc gi g) k'.
Proof. intros rc gi g k k' [H1 H2] Hk. unfold pf_cnt, r_upd, r_set_segs in *. cbn [rc_refused rc_overflow]. lia. Qed.
Lemma b12s_cur_upd : forall rc gi g i, pf_cur_ok rc (Some i) -> pf_cur_ok (r_upd rc gi g) (Some i).
Proof. intros rc gi g i H. unfold pf_cur_ok, r_upd, r_set_segs in *. cbn [rc_seg]. rewrite P8.p8_len_upd. exact H. Qed.

(** ** The seed at STORE 0x88df8 (every register its own atom). Regions: the two slots it reads on s1's atom 9 (read
    only: 0x48 c->reading, 0xc0 cur as the extra atoms 33 and 32) and cur's bytes [24, 32) on atom 32 (written: ignore,
    ignore_set). Facts: s4 (atom 20) is the shadow base, cur (atom 32) is a 4-aligned pointer. *)
Definition b12s_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 0x48 0xc8 0 0
      [YP09.mkChunk 0x48 (CVal 8 (SOff 33 0)); YP09.mkChunk 0xc0 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 32%nat) 24 32 24 32 [] ].
Definition b12s_facts : facts :=
  mkFacts [(20%nat, mkAF SB SB 0); (32%nat, mkAF 4096 (2 ^ 47 - 64) 2)] [] [].
Definition b12s_ss : sstate := mkSS B12_STORE sr_atoms b12s_regions None b12s_facts.
(* the one shadow entry: cur's [24, 32) is addressable, so the token executor decides checks B#33 and B#34 *)
Definition b12s_SH : list shent := [mkSHE 32 24 32].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition b12s_xs (e : b12e (PI := PI)) : list word := [w64 (b12_cur e); w64 (p_c (e_v e) + seg_spec.RC_READING)].
Definition b12s_E (regs1 : bvmap 5 word) (e : b12e (PI := PI)) : env := Eimg (Ereg regs1 (b12s_xs e)).

Section e.
Variable B : asyms.
Hypothesis OBJ : seg_val_objs (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* cur's 8 bytes [24, 32) lie in c's seg table, inside c's live block *)
Lemma b12s_cur_geo : forall e regs1 memc1 mdc1, b12_ent B e -> b12_mid B e regs1 memc1 mdc1 ->
  p_c (e_v e) <= b12_cur e /\ b12_cur e + 356 <= p_c (e_v e) + seg_spec.RC_N /\ b12_cur e mod 4 = 0 /\
  b12x_wok (e_v e) (b12_cur e + 24) /\
  exists bq mq, In (bq, mq) (ablocks B (e_ly e) (e_S e)) /\ bq <= p_c (e_v e) /\
    p_c (e_v e) + seg_spec.SEG_C_SIZE <= bq + mq /\ mq <= req_size mq.
Proof.
intros e regs1 memc1 mdc1 HE HM.
pose proof (b12_geo B e regs1 memc1 mdc1 HE HM) as G.
destruct G as (Hin & EF & Hly & HF1 & HF2 & HF64 & HFa & Hc1 & Hc2 & Hc16 & Hheap & Hgi32 & Hgi & Hs1a & Hs1b
  & Hsp47 & Hs1m & Hsp16 & Hv1 & Hv2 & HAR & Hs1c).
assert (Hcur : b12_cur e = p_c (e_v e) + 356 * Z.of_nat (e_gi e)) by reflexivity.
destruct Hheap as (bq & mq & Hinq & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bq mq HAR Hinq) as (_ & _ & _ & _ & _ & _ & Hmq).
pose proof (req_size_pos mq ltac:(lia)) as [_ Hrq].
unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE, b12x_wok in *.
split; [lia|]. split; [lia|]. split.
{ rewrite Hcur. apply Z.mod_divide in Hc16 as [q Hq]; [|lia]. rewrite Hq.
  replace (q * 16 + 356 * Z.of_nat (e_gi e)) with ((4 * q + 89 * Z.of_nat (e_gi e)) * 4) by lia. apply Z_mod_mult. }
split; [left; unfold seg_spec.SEG_C_SIZE; lia|].
exists bq, mq. split; [exact Hinq|]. split; [lia|]. split; [lia | exact Hrq].
Qed.

(* a byte of cur's [24, 32) is one the walk may write: in the footprint RC_PARSE_W c, in c's live block *)
Lemma b12s_awr_byte : forall e regs1 memc1 mdc1 bl0 fr0 ly own a, b12_ent B e -> b12_mid B e regs1 memc1 mdc1 ->
  b12_cur e + 24 <= a < b12_cur e + 32 ->
  awr_byte SEGS B STK_reac_segconf_parse_file (pf_sp0 (e_v e)) (seg_spec.RC_PARSE_W (p_c (e_v e))) bl0
    (ablocks B (e_ly e) (e_S e)) fr0 ly own a.
Proof.
intros e regs1 memc1 mdc1 bl0 fr0 ly own a HE HM Ha.
destruct (b12s_cur_geo e regs1 memc1 mdc1 HE HM) as (C1 & C2 & _ & _ & bq & mq & Hinq & Hb1 & Hb2 & Hrq).
unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *.
right; left. split.
- exists (p_c (e_v e), p_c (e_v e) + seg_spec.RC_N + 4). split.
  + unfold seg_spec.RC_PARSE_W. left. reflexivity.
  + cbn [fst snd]. unfold seg_spec.RC_N. lia.
- exists bq, mq. split; [exact Hinq | lia].
Qed.

Lemma b12s_seed : forall e regs1 memc1 mdc1, b12_ent B e -> b12_mid B e regs1 memc1 mdc1 ->
  st_ok_pi SEGS VAL (b12s_E regs1 e) b12s_ss
    (restrict (w_H (e_W e)) (mkst regs1 (Z_to_bv 64 (BASE + B12_STORE)) memc1 (seg_rom SEGS))).
Proof.
intros e regs1 memc1 mdc1 HE HM.
pose proof (b12_geo B e regs1 memc1 mdc1 HE HM) as G.
destruct G as (Hin & EF & Hly & HF1 & HF2 & HF64 & HFa & Hc1 & Hc2 & Hc16 & Hheap & Hgi32 & Hgi & Hs1a & Hs1b
  & Hsp47 & Hs1m & Hsp16 & Hv1 & Hv2 & HAR & Hs1c).
destruct (b12s_cur_geo e regs1 memc1 mdc1 HE HM) as (C1 & C2 & C4 & _ & bq & mq & Hinq & Hb1 & Hb2 & Hrq).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bq mq HAR Hinq) as (_ & _ & _ & _ & Hpres & _).
destruct (b12_slots B e regs1 memc1 mdc1 HE HM) as (_ & S48 & _ & SC0 & _).
pose proof alloc_ceiling_value as (Hac & _). assert (ES : ESTACK = 4096) by reflexivity.
assert (R9 : getr regs1 (Z_to_bv 5 9) = w64 (pf_s1 (e_v e)))
  by (apply (b12_kreg B e regs1 memc1 mdc1 9 _ HE HM); unfold B12_KEPT; cbn [In app]; tauto).
assert (R20 : getr regs1 (Z_to_bv 5 20) = w64 SHADOW_OFF)
  by (apply (b12_kreg B e regs1 memc1 mdc1 20 _ HE HM); unfold B12_KEPT; cbn [In app]; tauto).
set (E := b12s_E regs1 e).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold b12s_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (b12s_xs e) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold b12s_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
cbn [Nat.add nth b12s_xs] in E32, E33. clear EX.
assert (E9 : ew E 9 = w64 (pf_s1 (e_v e))) by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl); exact R9).
assert (E20 : ew E 20 = w64 SHADOW_OFF) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
unfold seg_spec.RC_READING, seg_spec.SEG_C_SIZE, seg_spec.RC_N in *.
rewrite restrict_mkst_fx. unfold b12s_ss. apply pa_entry_st_ok_full.
- subst E. unfold b12s_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b12s_regions. constructor; [|constructor; [|constructor]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat constructor.
    * apply (chunk_ok_val SEGS E _ (pf_s1 (e_v e)) 0x48 8 (SOff 33 0) (p_c (e_v e) + 16512));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
        | lia | lia | exact (val_mem_of_rdword SEGS (w_H (e_W e)) memc1 _ _ S48)].
    * apply (chunk_ok_val SEGS E _ (pf_s1 (e_v e)) 0xc0 8 (SOff 32 0) (b12_cur e));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
        | lia | lia | exact (val_mem_of_rdword SEGS (w_H (e_W e)) memc1 _ _ SC0)].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hpres (b12_cur e + o) ltac:(lia))).
- unfold b12s_regions. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
  rewrite E9, E32. unfold w64. rewrite !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I].
  cbn [b12s_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E20, E32. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  rewrite C4. unfold SB, SHADOW_OFF. repeat split; lia.
Qed.

(* a check obligation of a run that started at a memory agreeing with rd outside [w, w + 8) *)
Lemma b12s_ra : forall (rd rd' : reader) w x n,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (w <= a < w + 8) -> rd' a = rd a) ->
  (forall y, SHADOW_OFF <= y < kHighMemBeg -> ~ (w <= y < w + 8)) ->
  0 <= x -> x + n <= 2 ^ 47 -> range_addressable rd SHADOW_OFF x n -> range_addressable rd' SHADOW_OFF x n.
Proof.
intros rd rd' w x n K G H0 H1 H y Hy. destruct (H y Hy) as (s & Hs & Hok). exists s. split; [|exact Hok].
assert (Hb : SHADOW_OFF <= shadow_of_addr SHADOW_OFF y < kHighMemBeg).
{ unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg. pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound y 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
rewrite K; [exact Hs | unfold kHighMemBeg, SHADOW_OFF in *; lia | exact (G _ Hb)].
Qed.

(* after a run: the environment agrees with E0 below 48 (HAE), the memory is mbase outside [w, w + 8) (KM); Uw reads
   atom 32 (cur) at any environment that agrees with E0 *)
Ltac b12s_after E0 HAE KM Uw w mbase :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict ?hh ?m0) (mrestrict _ (ms_mem ?msn)),
    HG : mem_grows (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)) |- _ =>
    lazymatch type of HAE with env_agree ?k _ _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in let Uo := fresh "Uo" in
    assert (Uo : bv_unsigned (ew Eo 32) = w - 24) by (rewrite (Uw Eo HAE); lia);
    assert (HAEn : env_agree k E0 En) by (env_agree_chain HAE);
    assert (KMn : forall a, 0 <= a < 2 ^ 64 -> ~ (w <= a < w + 8) ->
                    aview SEGS hh (ms_mem msn) a = aview SEGS hh mbase a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in intros a Ha Hw;
          rewrite (kept_of_frame (segs := SEGS) Eo _ _ m0 (ms_mem msn) (fun a0 => w <= a0 < w + 8) HFr);
          [ exact (KM a Ha Hw)
          | let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
            intros b wlo whi a' Hin Hrr; vm_compute in Hin; cbv beta;
            repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
              [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Uo in Hrr; lia |]);
            destruct Hin
          | exact Ha | exact Hw ]);
    clear HFr HG HAE KM Uo; rename HAEn into HAE; rename KMn into KM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
    end
  end.

Ltac b12s_awr HE HM Uw HAE :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  apply awr_ok_cons_ro; [cbn; lia|];
  lazymatch type of HE with b12_ent _ ?e =>
  lazymatch type of HM with b12_mid _ _ ?regs1 ?memc1 ?mdc1 =>
  eapply awr_ok_cons_gen with (n := 32%nat) (b := b12_cur e); [reflexivity | exact (Uw _ HAE) | | apply awr_ok_nil];
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply (b12s_awr_byte e regs1 memc1 mdc1); [exact HE | exact HM | lia]
  end end.

(* byte k of a chunk the run wrote into a region (pf_a2.v's region read-back, any width) *)
Lemma b12s_byte_of_chunk : forall E (H : word -> bool) m n b0 lo hi wlo whi cs od (w : N) v k,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b0 ->
  In (YP09.mkChunk od (CVal w v)) cs -> Z.of_N w <= 8 -> (k < N.to_nat w)%nat ->
  aview SEGS H m (b0 + od + Z.of_nat k) =
    Some (Z.shiftr (bv_unsigned (sv_denot E v) mod 2 ^ (8 * Z.of_N w) mod 2 ^ (8 * Z.of_nat (N.to_nat w)))
            (8 * Z.of_nat k) mod 256).
Proof.
intros E H m n b0 lo hi wlo whi cs od w v k HR Hb Hin Hw Hk.
pose proof (field_of_region_any (segs := SEGS) E (mrestrict H m) n b0 cs lo hi wlo whi od w v HR Hb Hin Hw) as HV.
unfold aview. rewrite (HV k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YO0f.le_byte.
apply Z.mod_mod. lia.
Qed.

(* a literal's listing object at an image environment (lib/B/Prog/pf_seg_B12_n.v b12_obj) *)
Lemma b12s_obj : forall E k, img_env VAL A_LIM E -> (k < length seg_objs)%nat -> (A_TEXT <= A_OBJ k < A_LIM)%nat ->
  ew E (A_OBJ k) = w64 (nth k seg_objs 0).
Proof. intros E k HE Hk Hr. rewrite (img_env_atomP E (A_OBJ k) HE Hr). rewrite (OBJ k Hk). reflexivity. Qed.

(** ** STORE 0x88df8 -> PROV2 0x88e4c *)
Lemma b12_store_ok : B12_STORE_stmt B.
Proof.
unfold B12_STORE_stmt.
intros e b regs1 memc1 mdc1 HE HM HPB R19 R13.
pose proof (b12_geo B e regs1 memc1 mdc1 HE HM) as G.
destruct G as (Hin & EF & Hly & HF1 & HF2 & HF64 & HFa & Hc1 & Hc2 & Hc16 & Hheap & Hgi32 & Hgi & Hs1a & Hs1b
  & Hsp47 & Hs1m & Hsp16 & Hv1 & Hv2 & HAR & Hs1c).
destruct (b12s_cur_geo e regs1 memc1 mdc1 HE HM) as (C1 & C2 & C4 & HW & _).
pose proof (b12x_geo B e regs1 memc1 mdc1 (b12_cur e + 24) HE HM HW) as GX.
pose proof alloc_ceiling_value as (Hac & _). assert (ES : ESTACK = 4096) by reflexivity.
unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *.
pose proof (b12s_seed e regs1 memc1 mdc1 HE HM) as HS.
assert (HEI : img_env VAL A_LIM (b12s_E regs1 e)) by (unfold b12s_E; apply Eimg_env).
assert (HA0' : env_agree 32 (Ereg regs1 (b12s_xs e)) (b12s_E regs1 e))
  by (split; [intros n0 Hn0; unfold b12s_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (b12s_E regs1 e) n = getr regs1 r)
  by (intros n r Hn; unfold b12s_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 2)%nat -> ew (b12s_E regs1 e) (32 + j) = nth j (b12s_xs e) (Z_to_bv 64 0))
  by (intros j Hj; unfold b12s_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
cbn [Nat.add nth b12s_xs] in E32, E33. clear EX.
assert (E13 : ew (b12s_E regs1 e) 13 = getr regs1 13) by (apply EE; reflexivity).
assert (E19 : ew (b12s_E regs1 e) 19 = getr regs1 19) by (apply EE; reflexivity).
assert (E20 : ew (b12s_E regs1 e) 20 = w64 SHADOW_OFF).
{ rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl).
  apply (b12_kreg B e regs1 memc1 mdc1 20 _ HE HM); unfold B12_KEPT; cbn [In app]; tauto. }
revert HS HEI HA0' EE E13 E19 E20 E32 E33. generalize (b12s_E regs1 e) as E0.
intros E0 HS HEI HA0' EE E13 E19 E20 E32 E33.
pose proof (env_agree_refl 48 E0) as HAE.
assert (Uw : forall E', env_agree 48 E0 E' -> bv_unsigned (ew E' 32) = b12_cur e).
{ intros E' HA. rewrite (b12_ag_ew E0 E' 48 32 _ HA ltac:(lia) E32). unfold w64. apply unsigned_lit_small. lia. }
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (b12_cur e + 24 <= a < b12_cur e + 24 + 8) ->
  rdW (e_W e) memc1 a = rdW (e_W e) memc1 a) by (intros; reflexivity).
(* the shadow entry of cur's [24, 32): c's sa_addr (pf_obj) kept to memc1; [24, 32) is application memory *)
assert (SHOK : sh_ok SEGS b12_Bx b12s_SH E0 (mrestrict (w_H (e_W e)) memc1)).
{ pose proof HE as (HI & _). destruct HI as ((_ & _ & HOBJ & _) & _).
  destruct HOBJ as (_ & _ & _ & (_ & _ & _ & HRAc & _) & _).
  pose proof HM as (_ & HKO & _).
  assert (HRA : range_addressable (rdW (e_W e) memc1) SHADOW_OFF (b12_cur e + 24) 8).
  { apply (range_addressable_kept_win (rdW (e_W e) (e_mem e)) (rdW (e_W e) memc1)
      (pf_s1 (e_v e) - 2 * ESTACK) (pf_s1 (e_v e))).
    - intros s Hs Hn. exact (HKO s Hs Hn).
    - pose proof asan_consts as (_ & K1 & _). lia.
    - lia.
    - lia.
    - apply (range_addressable_sub _ _ (p_c (e_v e)) seg_spec.SEG_C_SIZE);
        [exact HRAc | unfold seg_spec.SEG_C_SIZE; lia | unfold seg_spec.SEG_C_SIZE; lia]. }
  pose proof GX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GXs & _).
  unfold sh_ok, b12s_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H (e_W e)) memc1 E0 b12_Bx 32%nat (b12_cur e + 24) 8 (b12_cur e) 24 32 HRA).
  - unfold b12_Bx. apply (U_atom _ 20 SHADOW_OFF E20). unfold SHADOW_OFF. lia.
  - apply (U_atom _ 32 (b12_cur e) E32). lia.
  - lia.
  - lia.
  - intros x Hx Hs. change (Z.min 24 32) with 24 in Hx. change (Z.max 24 32) with 32 in Hx.
    apply (GXs x); [unfold kHighMemBeg, SHADOW_OFF in *; lia | lia]. }
pose proof HM as (HJ & _ & _).
unfold b12_at.
(* 0x88df8 andi a0,a3,3 (a3 = cur), stopped at T31 *)
paj_run_tok RUN HS HJ SHOK Bspan. { b12s_awr HE HM Uw HAE. }
b12s_after E0 HAE KM Uw (b12_cur e + 24) memc1.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* T31 (0x88dfc `bnez a0` -> unimp 0x891c8): cur mod 4 = 0, so cur & 3 = 0 and the trap branch is not taken *)
  exfalso.
  assert (E13' : ew E0 13 = Z_to_bv 64 (b12_cur e)) by (rewrite E13, R13; reflexivity).
  pose proof (b12_ag_ew _ _ _ 13 _ HAE ltac:(lia) E13') as E13n.
  rewrite branch_ne_U, U_and_lit, (U_atom _ 13 (b12_cur e) E13n), U_lit in Hc by lia.
  assert (L3 : Z.land (b12_cur e) 3 = 0).
  { change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact C4. }
  rewrite L3 in Hc. discriminate Hc.
- (* 0x88e00 .. 0x88e48: a3 = cur (slot 0xc0), check B#33 (decided by the shadow entry: the slow arm 0x89044 and the
     error call 0x892ac are not reached), `sw s3,24(a3)`, check B#34 (slow arm 0x89054, error call 0x892b0),
     `sw 1,28(a3)`, a0 = cur + 0x100, a2 = "%s", a1 = 96, a3 = c->reading (slot 0x48); stop at PROV2 0x88e4c *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_PROV2. { b12s_awr HE HM Uw HAE. }
  b12s_after E0 HAE KM Uw (b12_cur e + 24) memc1.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ => rename msx into ms2; rename mdx into md2 end.
  (* the two words the run wrote, byte by byte: region 1 holds (28, CVal 4 (SLit 1)) and (24, CVal 4 (SOff 19 0)) *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H (e_W e)) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
    pose proof (Uw Ex HAE) as U32n;
    pose proof (b12_ag_ew _ Ex _ 19 _ HAE ltac:(lia) (eq_trans E19 R19)) as E19n end.
  cbn [ms_mem restrict] in HR1.
  assert (W8 : forall j, (j < 8)%nat ->
    rdW (e_W e) (ms_mem ms2) (b12_cur e + 24 + Z.of_nat j) = Some (bv_unsigned (nth j (P8.p8_ign_bytes b) ZB0))).
  { intros j Hj. destruct (Nat.lt_ge_cases j 4) as [Hj4 | Hj4].
    - rewrite (b12s_byte_of_chunk _ _ _ 32 (b12_cur e) _ _ _ _ _ 24 4 (SOff 19 0) j HR1 U32n
        ltac:(cbn [In]; right; left; reflexivity) ltac:(lia) ltac:(change (N.to_nat 4) with 4%nat; lia)).
      cbn [sv_denot]. rewrite E19n.
      destruct b; destruct j as [|[|[|[|j]]]]; try lia; vm_compute; reflexivity.
    - replace (b12_cur e + 24 + Z.of_nat j) with (b12_cur e + 28 + Z.of_nat (j - 4)) by lia.
      rewrite (b12s_byte_of_chunk _ _ _ 32 (b12_cur e) _ _ _ _ _ 28 4 (SLit 1) (j - 4) HR1 U32n
        ltac:(cbn [In]; left; reflexivity) ltac:(lia) ltac:(change (N.to_nat 4) with 4%nat; lia)).
      destruct b; destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try lia; vm_compute; reflexivity. }
  (* every other byte as at IGN *)
  assert (KP : b12x_kept (e_v e) (b12_cur e + 24) (rdW (e_W e) (e_mem e)) (rdW (e_W e) (ms_mem ms2)))
    by (exact (b12x_kept_step (e_v e) (b12_cur e + 24) _ _ _ (b12x_kept_mid B e regs1 memc1 mdc1 HM) KM)).
  (* the registers: B12_KEPT as at IGN, a0 .. a3 the snprintf arguments *)
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ B12_KEPTb HS (b12_ag _ _ _ _ 48 ltac:(lia) HA0' HAE)
    ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  assert (HR' : forall r, In r B12_KEPT -> getr (ms_regs ms2) (Z_to_bv 5 r) = getr (e_rX e) (Z_to_bv 5 r)).
  { intros r Hr. rewrite (HK _ (b12_keptb r Hr)). pose proof HM as (_ & _ & HRm). exact (HRm r Hr). }
  prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 11) Q11. prreg HS (Z_to_bv 5 12) Q12. prreg HS (Z_to_bv 5 13) Q13.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_PROV2) rg mm mdx) end.
  (* the post: r_key's ignore branch with parse_bool val = Some b *)
  unfold b12_post. rewrite (b12_spine B e HE), HPB. cbv beta iota.
  pose proof HE as (HI & _ & _ & _ & _ & HPV).
  destruct HI as (_ & HMID & HST & _ & _ & _).
  destruct HST as (HRC & HCUR & HNM & HCNT & HC0).
  pose proof HMID as (Ho & _ & _).
  apply (HPV fx (e_v e) (e_pos e) (e_ly e) (e_S e) (e_W e) (ms_regs ms2) (ms_mem ms2) md2 (e_cf e) (e_nm e)
    (e_o e) (e_ln e) (e_d e) b (e_gi e)).
  split; [|split; [exact HMID | split]].
  + (* pf_base at PF_SC_LINE, from IGN's *)
    exact (b12x_base B e regs1 memc1 mdc1 (b12_cur e + 24) (ms_regs ms2) (ms_mem ms2) md2 HE HM HW HJ KP HR').
  + (* pf_st over pf_prov_mid (PIgn b) cf gi *)
    split; [|split; [|split; [|split]]].
    * (* c's bytes: IGN's with seg[gi]'s [24, 32) the two words written (P8.p8_rconf_ign) *)
      destruct HRC as (bs & Hbs & Henc). pose proof Henc as (HL & _).
      exists (LM.upd_bytes bs (356 * e_gi e + 24) (P8.p8_ign_bytes b)).
      split; [|exact (P8.p8_rconf_ign (e_cf e) bs (e_gi e) b Henc HCUR)].
      unfold seg_spec.SEG_C_SIZE in HL.
      assert (HU : (356 * e_gi e + 24 + length (P8.p8_ign_bytes b) <= length bs)%nat)
        by (rewrite P8.p8_ign_bytes_len; lia).
      assert (Hcur : b12_cur e = p_c (e_v e) + 356 * Z.of_nat (e_gi e)) by reflexivity.
      intros i Hi. rewrite (b12s_upd_len _ _ _ HU) in Hi. rewrite (b12s_upd_nth _ _ _ _ _ HU).
      rewrite P8.p8_ign_bytes_len.
      destruct (Nat.ltb_spec i (356 * e_gi e + 24)) as [H1 | H1];
        [|destruct (Nat.ltb_spec i (356 * e_gi e + 24 + 8)) as [H2 | H2]].
      -- rewrite KM by lia. rewrite (b12_kept B e regs1 memc1 mdc1) by (first [exact HE | exact HM | lia]).
         exact (Hbs i Hi).
      -- replace (p_c (e_v e) + Z.of_nat i) with (b12_cur e + 24 + Z.of_nat (i - (356 * e_gi e + 24))) by lia.
         apply W8. lia.
      -- rewrite KM by lia. rewrite (b12_kept B e regs1 memc1 mdc1) by (first [exact HE | exact HM | lia]).
         exact (Hbs i Hi).
    * unfold pf_prov_mid. apply b12s_cur_upd. exact HCUR.
    * exact (b12x_keep_nm _ _ _ _ _ GX KP _ HNM).
    * unfold pf_prov_mid. apply (b12s_cnt_upd _ _ _ _ _ HCNT).
      pose proof (PA.pf_next_skipn_lt (p_s (e_v e)) (e_o e) Ho). lia.
    * exact (b12x_keep_slot _ _ _ _ _ GX KP 0xc0 _ ltac:(lia) HC0).
  + (* the registers: PF_RL ++ PF_RM as at IGN, a0 = &seg[gi].ignore_file, a1 = 96, a2 = "%s", a3 = c->reading *)
    destruct (b12x_regs B e (ms_regs ms2) HE HR') as (_ & HRG2).
    unfold pf_rg in *. apply Forall_app in HRG2 as (HRL & HRM).
    apply Forall_app. split; [exact HRL|]. apply Forall_app. split; [exact HRM|].
    lazymatch goal with HEn : img_env _ _ ?Ex, HAEx : env_agree 48 E0 ?Ex |- _ =>
    repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    [ rewrite Q10; unfold w64; f_equal;
      first [rewrite (Uw _ HAEx) | rewrite (Uw _ (env_agree_refl 48 E0))];
      unfold b12_cur, seg_spec.RS_IGNORE_FILE; lia
    | rewrite Q11; reflexivity
    | rewrite Q12; pose proof b12_lits as (_ & _ & _ & _ & _ & L6 & _ & _ & _ & _ & _ & L35 & _);
      rewrite L6, <- L35;
      first [apply (b12s_obj _ 35 HEn) | apply (b12s_obj _ 35 HEI)]; vm_compute; lia
    | rewrite Q13; first [exact E33 | exact (b12_ag_ew _ _ _ 33 _ HAEx ltac:(lia) E33)] ]
    end.
Qed.

End e.
End f.
End d.
