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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 387 of its 459 lines of code are new or changed and 381 lines of the source are left out. *)
(* reac_segconf_ignored on fuzz_segconf image B (fuzz_segconf.asan-ubsan, entry 0x89b78 = BASE +
   AF_reac_segconf_ignored, 26 instructions, 16-byte frame, no side-stack frame): the walk that proves its contract
   (lib/B/Prog/reac_segconf_ignored_c.v, image B's copy of the FINAL contract 6f783602b5e3). It is the image-B port of
   lib/A/Prog/reac_segconf_ignored.v (commit 5be18a4b2783), written from that walk's step plan
   (plan-reac_segconf_ignored.md (image A's walk record) at da1732b794c6) before the A walk's text landed: the Rocq text is
   in the form of image A's closed walk of the sibling query lib/A/Prog/reac_segconf_role.v
   (commit 3e8a17ad1bc0): an entry seed, the shadow-token executor (paj_run_tok,
   psrr_branch_tok), the call of reac_segconf_find through its contract (PaNoChain.cl_callS_wide) and the return
   through paj_ret_at. The landed A walk keeps the same symbolic states (the field region on atom 44 at [24, 28)
   with the literal flag, its shadow entry, atom 44's fact).

   Image A against image B: B is A's 23 instructions at other addresses plus 3 words: after `beqz a0` (0x89b94),
   UBSan's alignment test `andi a1,a0,3` (0x89b98), `bnez a1` (0x89b9c) to the `unimp` at 0x89bcc.

   Atoms: 0..31 the entry registers, 32 the shadow base SB. Regions at the entry: the frame (16 bytes), the GOT word
   of the shadow-base cell (A_OBJ 0 = 0xa3210 in image B's object table) and the cell (A_OBJ 12 = 0xac7b8). After
   the call (atoms 40..55 the clobbered registers, 44 = a0 = find's result p): the ignore field of the entry found,
   p + 0x18, as a region based at p, with the literal flag 0 or 1.

   Every edge to the error path or the trap, and the fact that refutes it:
     0x89b9c bnez a1 (after andi a1,a0,3) -> unimp 0x89bcc: decided not taken by the run itself (PaShadow's
       sym_step_pi_tok; YP0m.s_and_ptr over atom 44's fact, af_al2 = 2), the fact added after the call from
       p = c + 356 i with c mod 16 = 0 (query_pre). Nothing else reaches 0x89bcc: the word before it is `ret`.
     0x89bb0 bnez a1 (shadow byte of p + 0x18) -> slow arm 0x89bd0 .. 0x89bd8, errpath_load4 at 0x89bdc: the shadow
       token (tok_branch_pi) over the entry mkSHE 44 24 28 (ign_shent), from range_addressable_of_block on c's
       live block after the call (find's sa_noalloc keeps the block list).
     0x89b94 beqz a0: both arms walked (find's NULL; the entry found, p >= c > 0). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaSB PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_segconf_find_c reac_segconf_ignored_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_segconf_ignored_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* Image B's numbers, image B's instance file's (lib/B/Prog/SegInstB.v), under the names the proofs below use:
   reac_segconf_find's window SegInstB.STK_reac_segconf_find (its 64-byte frame, 0x89a84 `addi sp,sp,-64`, and the
   strcmp wrapper's 2 * ESTACK window, the call 0x89b18), this function's SegInstB.STK_reac_segconf_ignored (its
   16-byte frame, 0x89b78 `addi sp,sp,-16`, above find's window). The read-only range is SegInstB.RLO_A / RHI_A, the
   B listing's SegGlob.SEG_RLO / SEG_RHI (image B's .data.rel.ro start and .got end). *)
#[local] Notation STK_reac_segconf_find_B := SegInstB.STK_reac_segconf_find (only parsing).
#[local] Notation STK_reac_segconf_ignored_B := SegInstB.STK_reac_segconf_ignored (only parsing).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the entry seed: the frame, the GOT word, the shadow-base cell; the facts on sp and on SB *)
Definition ign_Bx : sv := SOff 32 0.
Definition ign_regions : smem := [stack_region 16; got_regionP; bcell_regionP 32].
Definition ign_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0)] [] [].
Definition ss_ign : sstate := mkSS AF_reac_segconf_ignored sr_atoms ign_regions None ign_facts.
Definition ign_extra : list word := [Z_to_bv 64 SB].
Definition EC (regs : bvmap 5 word) : env := Eimg (Ereg regs ign_extra).
Section e.
Variable B : asyms.
(* the callee: reac_segconf_find's contract at its entry, image B's stack number and the same read-only range *)
Hypothesis FIND : forall fx0 : YK11.FPState,
  @reac_segconf_find_contract fx0 rc SK SEGS B (BASE + AF_reac_segconf_find) SegInstB.STK_reac_segconf_find
    SegInstB.RLO_A SegInstB.RHI_A.
(* the record: the GOT word and the shadow-base cell are the listing's objects 0 and 12 *)
Hypothesis TL : PALib B.
(* every program function's call target against the listing's base (SegObj.seg_sig_prog) *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

Lemma ign_aview_mod : forall H (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof using.
intros H m a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.
(* a run that writes only [lo, hi), mapped bytes above the image, keeps the read-only view *)
Lemma ign_aro_frame : forall (W : world SEGS) (mem m : word -> option byte) lo hi,
arodata_okP SEGS SegInstB.RLO_A SegInstB.RHI_A B (rdW W mem) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rdW W m a = rdW W mem a) ->
(forall a, lo <= a < hi -> rdW W mem a <> None) ->
kImgEnd <= lo -> hi <= 2 ^ 64 ->
arodata_okP SEGS SegInstB.RLO_A SegInstB.RHI_A B (rdW W m).
Proof using.
intros W mem m lo hi H Hk Hp Hlo Hhi a Hro Ho He.
pose proof (H a Hro Ho He) as Ha.
assert (Ea : Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64)).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity. }
rewrite ign_aview_mod in Ha |- *. rewrite Ea in Ha |- *.
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ra.
set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' lo) as [Hl | Hl]; [rewrite Hk by lia; exact Ha|].
destruct (Z_lt_le_dec a' hi) as [Hh | Hh]; [|rewrite Hk by lia; exact Ha].
exfalso. apply (Hp a' ltac:(lia)). rewrite Ha.
destruct (seg_rom SEGS (Z_to_bv 64 a')) as [b|] eqn:Eb; [|reflexivity].
exfalso. pose proof (seg_rom_in_img SEGS a' Ra ltac:(rewrite Eb; discriminate)) as Himg.
pose proof (pa_img_range a' Himg). lia.
Qed.
(* an object of the program lies below the allocator's ceiling *)
Lemma ign_loc_low : forall ly S W mem md q n, AR SEGS B ly S W mem md -> sa_loc SEGS B ly S q n -> 0 < n ->
4096 <= q /\ q + n <= alloc_ceiling.
Proof using.
intros ly S W mem md q n HAR [(b & m & Hin & Hb1 & Hb2) | [(cid & pos & Hin & Hc & Hf1 & Hf2) | Himg]] Hn.
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4 & Hce & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (H4 & Hce & _). lia.
- destruct (Himg q ltac:(lia)) as (I1 & _ & _). destruct (Himg (q + n - 1) ltac:(lia)) as (I2 & _ & _).
  pose proof (pa_img_range q I1). pose proof (pa_img_range _ I2). pose proof asan_consts as (C1 & _).
  unfold kImgEnd in *. lia.
Qed.
(* the shadow facts of a range below the ceiling read only below lo *)
Lemma ign_addr_agree : forall (rd rd' : reader) q n lo,
(forall a, 0 <= a < lo -> rd' a = rd a) -> 0 <= q -> q + n <= alloc_ceiling -> alloc_ceiling + 16 <= lo ->
sa_addr rd q n -> sa_addr rd' q n.
Proof using.
intros rd rd' q n lo Hk Hq Hqn Hlo (A0 & A1 & A2 & A3 & A4).
pose proof asan_consts as (C1 & _).
assert (HAC : alloc_ceiling / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split.
- intros x Hx. destruct (A3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok]. rewrite Hk; [exact Hs|].
  assert (x / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  assert (0 <= x / 8) by (apply Z.div_pos; lia).
  unfold shadow_of_addr, SHADOW_OFF. lia.
- intros Hn s Hs. rewrite Hk; [exact (A4 Hn s Hs)|].
  unfold shadow_addr, SHADOW_OFF in Hs.
  assert ((q + n - 1) / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  assert (0 <= q / 8) by (apply Z.div_pos; lia).
  assert ((2147450880 + (q + n - 1) / 8) / 8 * 8 <= 2147450880 + (q + n - 1) / 8)
    by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
  assert (0 <= (2147450880 + q / 8) / 8 * 8) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia).
  lia.
Qed.
(* find's premise query_pre holds for a reader that agrees below lo *)
Lemma ign_qp_agree : forall ly S W mem md (rd' : reader) c name rcs nm lo,
AR SEGS B ly S W mem md ->
query_pre SEGS B ly S (rdW W mem) c name rcs nm ->
(forall a, 0 <= a < lo -> rd' a = rdW W mem a) -> alloc_ceiling + 16 <= lo ->
query_pre SEGS B ly S rd' c name rcs nm.
Proof using.
intros ly S W mem md rd' c name rcs nm lo HAR (Hc0 & Hc16 & (bs & HB & HE) & HCH & HCA & Hn0 & HNS & HNL & HNA & HN32)
  Hk Hlo.
pose proof asan_consts as (C1 & _).
destruct (ign_loc_low ly S W mem md c seg_spec.SEG_C_SIZE HAR (or_introl HCH) ltac:(unfold seg_spec.SEG_C_SIZE; lia))
  as [Lc1 Lc2].
destruct (ign_loc_low ly S W mem md name (Z.of_nat (length nm) + 1) HAR HNL ltac:(lia)) as [Ln1 Ln2].
pose proof HE as (HL & _). unfold seg_spec.SEG_C_SIZE in HL, Lc2.
refine (conj Hc0 (conj Hc16 (conj _ (conj HCH (conj _ (conj Hn0 (conj _ (conj HNL (conj _ HN32))))))))).
- exists bs. split; [|exact HE]. intros i Hi. rewrite Hk; [exact (HB i Hi)|]. lia.
- exact (ign_addr_agree _ _ c seg_spec.SEG_C_SIZE lo Hk ltac:(lia) ltac:(unfold seg_spec.SEG_C_SIZE; lia) Hlo HCA).
- destruct HNS as ((HZ & HNZ) & HT). split; [split; [|exact HNZ] |].
  + intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite Hk; [exact (HZ i ltac:(rewrite length_app; cbn [length]; lia))|]. lia.
  + intros x Hx. pose proof (Z.mod_pos_bound (name + Z.of_nat (length nm)) 8 ltac:(lia)). rewrite Hk; [exact (HT x Hx)|]. lia.
- exact (ign_addr_agree _ _ name (Z.of_nat (length nm) + 1) lo Hk ltac:(lia) Ln2 Hlo HNA).
Qed.

(* the symbolic state at the entry is sound for the machine state the contract gives *)
Lemma ign_entry : forall ly S W (regs : bvmap 5 word) mem md ch,
afn_pre SEGS B STK_reac_segconf_ignored_B ly S W regs mem md ch ->
st_ok_pi SEGS VAL (EC regs) ss_ign
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_segconf_ignored)) mem (seg_rom SEGS)))
/\ sh_ok SEGS ign_Bx [] (EC regs) (mrestrict (w_H W) mem).
Proof using TL.
intros ly S W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_reac_segconf_ignored_B = 8272) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 0 ltac:(lia)) as HO0. pose proof (pa_obj_img 12 ltac:(lia)) as HO12.
unfold kImgEnd in HO0, HO12.
pose proof (pal_got_cell B TL) as HGC.
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
rewrite restrict_mkst_fx.
set (E := EC regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs ign_extra) n)
  by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some n) = w).
{ intros n w Hn Hw. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hw. }
assert (B0 : base_val E (Some (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply VB; [exact EO0 | lia]).
assert (B12 : base_val E (Some (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply VB; [exact EO12 | lia]).
split.
- unfold ss_ign. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold ign_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
    * rewrite B0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite B12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SHADOW_OFF);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + apply pairwise_disjoint_of_extents.
    unfold ign_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B0, B12. cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite WS in Hslo.
    clear - Hslo Hceil C1 HO0 HO12 HGC. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [ign_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    rewrite WS in Hslo. unfold SB. clear - Hal16 Hslo Hshi H47 C1 Hceil. repeat split; first [lia | reflexivity].
- unfold sh_ok. constructor.
Qed.

(* the ignore field of the entry found, p + 0x18, as a region based at find's result (atom 44): the literal flag *)
Definition R_IGN (fl : Z) : YP09.region :=
  YP09.mkRegion (Some 44%nat) 24 28 0 0 [YP09.mkChunk 24 (CVal 4 (SLit fl))].
Lemma ign_val_mem : forall H (mem : word -> option byte) a n v,
sa_val (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof using.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [bb|] eqn:Hb; [|discriminate].
cbn in Hv. injection Hv as Hv. rewrite <- (Z_to_bv_bv_unsigned _ bb) at 1. do 2 f_equal. exact Hv.
Qed.
(* the shadow entry of the ignore field: its 4 bytes lie in a live block, addressable *)
Lemma ign_shent : forall E (W' : world SEGS) mem' p b len,
ew E 32 = Z_to_bv 64 SB -> ew E 44 = Z_to_bv 64 p ->
range_addressable (rdW W' mem') SHADOW_OFF (p + 24) 4 -> in_app b len -> b <= p -> p + 28 <= b + len ->
shent_ok SEGS ign_Bx E (mrestrict (w_H W') mem') (mkSHE 44 24 28).
Proof using.
intros E W' mem' p b len H32 H44 RA Happ Hb1 Hb2.
pose proof asan_consts as (C1 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
apply (shent_ok_of_range SEGS (w_H W') mem' E ign_Bx 44 (p + 24) 4 p 24 28 RA).
- unfold ign_Bx. rewrite (U_atom E 32 SB H32) by (unfold SB; lia). reflexivity.
- apply U_atom; [exact H44 | lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.
Ltac ign_fld_ok A44 RD :=
  unfold region_ok, R_IGN;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  rewrite A44, unsigned_lit_small by lia;
  split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
  apply Forall_cons;
  [ eapply (chunk_ok_val SEGS _ _ _ 24 4 (SLit _) _);
      [ reflexivity | zside | zside | exact (ign_val_mem _ _ _ _ _ RD) ]
  | apply Forall_nil ].
Ltac ign_fld_disj A44 Usp1 :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; try unfold R_IGN; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite A44, Usp1, unsigned_lit_small by lia; split; [lia | exact I].
Lemma ign_beq0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof using. intros E n v Hn Hv. rewrite branch_eq_U, (U_atom E n v Hn Hv), U_SLit. reflexivity. Qed.
Ltac ign_agree32 HAE1 :=
  lazymatch goal with |- env_agree 32 _ _ =>
    let HA1 := fresh "HA1" in let HD1 := fresh "HD1" in
    destruct HAE1 as [HA1 HD1]; split;
    [ let n := fresh "n" in let Hn := fresh "Hn" in
      intros n Hn; cbn [extK]; rewrite ?ew_ewset_other by lia; apply HA1; lia
    | cbn [extK]; rewrite ?ed_ewset; exact HD1 ] end.
(* the write windows of a run: only the frame, based at atom 2 (sp) *)
Ltac ign_win Usp :=
  let b0 := fresh "b0" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
  intros b0 wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr; revert Hrr; cbn [extK]; rewrite ?ew_ewset_other by lia;
     rewrite ?Usp; intros Hrr; cbv beta; lia |]);
  destruct Hin.
(* the return's ra, journal and callee-saved registers (apost_base's first three conjuncts after the config) *)
Ltac ign_head HS HJ R1 HAG F1 Hra HAE1 regs :=
  split; [cbn [ms_regs]; rewrite R1; cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite (proj1 HAG 1%nat) by lia;
          rewrite F1, Hra; reflexivity|];
  split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs ign_extra HS);
          [first [exact HAE1 | ign_agree32 HAE1] | vm_compute; reflexivity]|].

Theorem reac_segconf_ignored_walk :
  reac_segconf_ignored_contract SEGS B (BASE + AF_reac_segconf_ignored) SegInstB.STK_reac_segconf_ignored
    SegInstB.RLO_A SegInstB.RHI_A.
Proof using FIND TL SIGP.
unfold reac_segconf_ignored_contract.
intros ly S W regs mem md ch c name rcs nm HPRE HROD H10 Rc H11 Rn HQP Hev.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_reac_segconf_ignored_B = 8272) by reflexivity.
destruct (ign_entry ly S W regs mem md ch HPRE) as [HS SHOK].
pose proof (ajournal_init SEGS B STK_reac_segconf_ignored_B [] ly S W regs mem md ch HPRE) as HJ.
remember (EC regs) as E0 eqn:HE0.
assert (HEI : img_env VAL A_LIM E0) by (rewrite HE0; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E0 n = ew (Ereg regs ign_extra) n)
  by (intros n Hn; rewrite HE0; unfold EC; apply Eimg_low; exact Hn).
assert (F1 : ew E0 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (F3 : ew E0 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (F4 : ew E0 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (F2 : ew E0 2 = Z_to_bv 64 (spZ regs))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (F10 : ew E0 10 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (F11 : ew E0 11 = Z_to_bv 64 name) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (F32 : ew E0 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HAE : env_agree 32 (Ereg regs ign_extra) E0)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | rewrite HE0; reflexivity]).
assert (Usp0 : bv_unsigned (ew E0 2) = spZ regs) by (rewrite F2; apply unsigned_lit_small; unfold spZ; apply bv_unsigned_in_range).
clear HE0 EL.
unfold cfg_at. change (w64 (BASE + AF_reac_segconf_ignored)) with (Z_to_bv 64 (BASE + AF_reac_segconf_ignored)).
(* 0x89b78 .. 0x89b90: the frame, the saves of ra and s0, s0 := the shadow base through the GOT word, and the call
   of reac_segconf_find *)
paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac; exact Usp0 |].
(* the run wrote the frame only *)
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 16 <= a < spZ regs) HFr
  ltac:(ign_win Usp0)) as UN1.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (Qsp : spZ (ms_regs ms) = spZ regs + -16)
  by (unfold spZ at 1; rewrite Q2, Usp0; rewrite unsigned_lit_small by lia; lia).
pmkst HS.
(* find's premises at the call, from the entry's: the run wrote only the frame [sp - 16, sp) *)
assert (HROc : arodata_okP SEGS SegInstB.RLO_A SegInstB.RHI_A B (rdW W (ms_mem ms))).
{ apply (ign_aro_frame W mem (ms_mem ms) (spZ regs - 16) (spZ regs) HROD).
  - intros a Ha Hn. exact (UN1 a Ha Hn).
  - intros a Ha. apply (aview_some_of_apresent SEGS). apply Hpres. rewrite WS. lia.
  - pose proof asan_consts as (C1' & _). unfold kImgEnd. rewrite WS in Hslo. lia.
  - lia. }
assert (HQPc : query_pre SEGS B ly S (rdW W (ms_mem ms)) c name rcs nm).
{ apply (ign_qp_agree ly S W mem md _ c name rcs nm (spZ regs - 16) HAR HQP); [|rewrite WS in Hslo; lia].
  intros a Ha. apply UN1; lia. }
(* the frame chain at s0 = SB: below the allocator's ceiling, so the empty chain *)
assert (Hch1 : achain ly (rdW W (ms_mem ms)) (spZ regs + -16) (s0Z (ms_regs ms)) []).
{ apply achain_low. unfold s0Z. rewrite Q8, F32, unsigned_lit_small by (unfold SB; lia). unfold SB. lia. }
pose proof pa_B_ok as HBo.
(* 0x89b90: jal reac_segconf_find, through find's contract *)
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs ms) (ms_mem ms) _ STK_reac_segconf_ignored_B (spZ regs) []
    ly S W mem md [] ly S _ 0 STK_reac_segconf_find_B [] EV_reac_segconf_find (-16) (Z_to_bv 64 (BASE + 19924)) []
    (fun ly' S' W' regs' mem' md' => getr regs' 10 = w64 (seg_spec.find_ptr c rcs nm) /\
       sa_kept SEGS W (ms_mem ms) W' mem' (ms_regs ms) STK_reac_segconf_find_B (fun _ => False) /\ sa_noalloc B ly S ly' S') HJ).
  - exact Qsp.
  - reflexivity.
  - lia.
  - unfold STK_reac_segconf_find_B, ESTACK. lia.
  - rewrite WS. unfold STK_reac_segconf_find_B, ESTACK. lia.
  - rewrite Q3, F3. exact Hgp.
  - rewrite Q4, F4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - exact Hch1.
  - intros HPRE1.
    rewrite (SIGP SS_reac_segconf_find) by (unfold seg_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
    change (seg_af SS_reac_segconf_find) with AF_reac_segconf_find.
    eapply SRr_mono.
    { apply (FIND fx ly S W (ms_regs ms) (ms_mem ms) _ [] c name rcs nm HPRE1 HROc);
        [rewrite Q10, F10; reflexivity | exact Rc | rewrite Q11, F11; reflexivity | exact Rn | exact HQPc | exact Hev]. }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. rewrite Q1. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a (r & Hr & _). destruct Hr.
  - intros ? ? ? ? ? ? _ a (r & Hr & _). destruct Hr. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & (Ha03 & HKF & HNA3)).
(* after the call the reader is the entry's outside this function's stack window *)
assert (UN3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_reac_segconf_ignored_B <= a < spZ regs) ->
  rdW W3 mem3 a = rdW W mem a).
{ intros a Ha Hn. rewrite WS in Hn. rewrite (HKF a Ha); [| rewrite Qsp; unfold STK_reac_segconf_find_B, ESTACK; lia | tauto].
  apply UN1; [exact Ha | cbv beta; lia]. }
(* back at 0x89b94: the frame region is kept (find wrote below sp - 16 only) *)
jafter_call_keep_pi HS 40%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0%nat] HS2.
lazymatch type of HS2 with ?P -> _ => assert (HQ : P); [| specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply region_kept_stack_sub; [exact HJc3 | exact HJ3 | exact Usp0 | lia | rewrite WS; lia | lia | lia | lia |].
  intros a Ha (r & Hr & _). destruct Hr. }
rewrite <- restrict_mkst_fx in HS2. clear HS SHOK HFr HG. rename HF into HF1.
assert (HEI1 : img_env VAL A_LIM (havoc E0 40 (map (getr regs3) CLOB)))
  by (apply img_env_havoc; [exact HEI | apply Nat.leb_le; vm_compute; reflexivity]).
assert (HAG : env_agree 40 E0 (havoc E0 40 (map (getr regs3) CLOB)))
  by (apply env_agree_havoc_ge; [lia | split; [intros; reflexivity | reflexivity]]).
assert (E44 : ew (havoc E0 40 (map (getr regs3) CLOB)) 44 = getr regs3 10)
  by (rewrite (ew_havoc_new E0 40 _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia); reflexivity).
remember (havoc E0 40 (map (getr regs3) CLOB)) as E1 eqn:HE1. clear HE1.
assert (HAE1 : env_agree 32 (Ereg regs ign_extra) E1).
{ destruct HAE as [HA1 HD1]. destruct HAG as [HA2 HD2].
  split; [intros n Hn; rewrite HA2 by lia; apply HA1; lia | congruence]. }
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite (proj1 HAG 2%nat) by lia; exact Usp0).
unfold YK0s.ret_ok in Hra.
unfold seg_spec.find_ptr, seg_spec.rseg_addr, seg_spec.RSEG_SIZE in Ha03.
destruct (r_find rcs nm) as [i|] eqn:RF.
2:{ (* find returned NULL: a0 = 0, `beqz a0` at 0x89b94 to the epilogue, and the return of 0 *)
  assert (RI : r_ignored rcs nm = false) by (unfold r_ignored; rewrite RF; reflexivity).
  rewrite RI.
  pose proof (st_ok_pi_set_reg _ _ _ (10%bv : bv 5) (SLit 0) HS2
    ltac:(intros Hz; apply (f_equal bv_unsigned) in Hz; discriminate Hz)
    ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite Ha03; reflexivity)) as HS3.
  clear HS2.
  assert (SHOK3 : sh_ok SEGS ign_Bx [] E1 (mrestrict (w_H W3) mem3)) by constructor.
  paj_run_tok RUN HS3 HJ3 SHOK3 Bspan; [awr_ok_tac; exact Usp1 |].
  eapply (RET W3 _ _ _ _ _ HS3 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  prreg HS3 (1%bv : bv 5) R1. prreg HS3 (10%bv : bv 5) R10.
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 16 <= a < spZ regs) HFr
    ltac:(ign_win Usp1)) as UN4.
  unfold apost_base. eexists _, _, _, _, _.
  ign_head HS3 HJ3 R1 HAG F1 Hra HAE1 regs.
  split; [cbn [ms_regs]; rewrite R10; reflexivity|].
  split; [|exact HNA3].
  intros a Ha Hn _. rewrite WS in Hn. rewrite UN4 by (first [exact Ha | cbv beta; lia]). apply UN3; [exact Ha | rewrite WS; lia]. }
(* find returned p = c + 356 i, the entry i of the table *)
pose proof HQP as (Hc0 & Hc16 & HRC & HCH & HCA & _).
destruct (ign_find_bound _ c rcs nm i HRC RF) as [Hi Hi32].
pose proof (ign_rd_ignore (rdW W mem) c rcs i HRC Hi) as HIGN. unfold seg_spec.RS_IGNORE in HIGN.
destruct HCH as (b & m & Hbin & Hb1 & Hb2). unfold seg_spec.SEG_C_SIZE in Hb2.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hbin) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrm].
assert (Hp4 : (c + 356 * Z.of_nat i) mod 4 = 0).
{ replace (c + 356 * Z.of_nat i) with ((4 * (c / 16) + 89 * Z.of_nat i) * 4)
    by (pose proof (Z.div_mod c 16 ltac:(lia)); lia).
  apply Z.mod_mul. lia. }
set (p := c + 356 * Z.of_nat i) in *.
assert (Hp : c <= p /\ p + 356 <= c + 16616) by (subst p; lia).
pose proof (HNA3) as (HPerm & Hly3 & _).
assert (Hbin3 : In (b, m) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hbin).
pose proof (proj1 HJ3) as HAR3.
(* the ignore field, read through the reader after the call *)
assert (RD24 : sa_val (rdW W3 mem3) (p + 24) 4 (seg_spec.b2z (rs_ignore (r_seg rcs i)))).
{ intros k Hk. rewrite UN3; [exact (HIGN k Hk) | lia | rewrite WS; lia]. }
(* its 4 bytes are addressable at the call's return: they lie in the live block of c *)
assert (RA24 : range_addressable (rdW W3 mem3) SHADOW_OFF (p + 24) 4)
  by (apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 b m); [exact HAR3 | exact Hbin3 | lia | lia]).
assert (A32 : ew E1 32 = Z_to_bv 64 SB) by (rewrite (proj1 HAG 32%nat) by lia; exact F32).
assert (A44 : ew E1 44 = Z_to_bv 64 p) by (rewrite E44, Ha03; reflexivity).
(* atom 44's fact: p in [0, 2 ^ 47 - 28], p mod 4 = 0 (the UBSan test at 0x89b98 reads its low two bits) *)
pose proof (st_ok_pi_add_fact _ _ _ 44%nat (mkAF 0 (2 ^ 47 - 28) 2) HS2
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite A44, unsigned_lit_small by lia; change (2 ^ 2) with 4; lia))
  as HS4.
clear HS2.
assert (SHOK4 : sh_ok SEGS ign_Bx [mkSHE 44 24 28] E1 (mrestrict (w_H W3) mem3)).
{ constructor; [|constructor].
  exact (ign_shent E1 W3 mem3 p b (req_size m) A32 A44 RA24 Hbapp ltac:(lia) ltac:(lia)). }
assert (RI : r_ignored rcs nm = rs_ignore (r_seg rcs i)) by (unfold r_ignored; rewrite RF; reflexivity).
rewrite RI.
destruct (rs_ignore (r_seg rcs i)) eqn:IG.
- (* ignore = 1 *)
  pose proof (st_ok_pi_add_region _ _ _ (R_IGN 1) HS4 eq_refl
    ltac:(ign_fld_ok A44 RD24) ltac:(ign_fld_disj A44 Usp1)) as HS5.
  clear HS4.
  (* 0x89b94 beqz a0: p <> 0, not taken *)
  psrr_branch_tok RUN BR HS5 SHOK4 Bspan.
  { exfalso. rewrite (ign_beq0 _ 44 p A44 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc. lia. }
  clear Hc.
  (* 0x89b98 .. 0x89bc8: the UBSan test (decided by atom 44's fact), p + 0x18, the check (its slow arm passes),
     lw, snez, the epilogue *)
  paj_run_tok RUN HS5 HJ3 SHOK4 Bspan; [awr_ok_tac; exact Usp1 |].
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 16 <= a < spZ regs) HFr
    ltac:(ign_win Usp1)) as UN4.
  eapply (RET W3 _ _ _ _ _ HS5 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  prreg HS5 (1%bv : bv 5) R1. prreg HS5 (10%bv : bv 5) R10.
  unfold apost_base. eexists _, _, _, _, _.
  ign_head HS5 HJ3 R1 HAG F1 Hra HAE1 regs.
  split; [cbn [ms_regs]; rewrite R10; reflexivity|].
  split; [|exact HNA3].
  intros a Ha Hn _. rewrite WS in Hn. rewrite UN4 by (first [exact Ha | cbv beta; lia]). apply UN3; [exact Ha | rewrite WS; lia].
- (* ignore = 0 *)
  pose proof (st_ok_pi_add_region _ _ _ (R_IGN 0) HS4 eq_refl
    ltac:(ign_fld_ok A44 RD24) ltac:(ign_fld_disj A44 Usp1)) as HS5.
  clear HS4.
  psrr_branch_tok RUN BR HS5 SHOK4 Bspan.
  { exfalso. rewrite (ign_beq0 _ 44 p A44 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc. lia. }
  clear Hc.
  paj_run_tok RUN HS5 HJ3 SHOK4 Bspan; [awr_ok_tac; exact Usp1 |].
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 16 <= a < spZ regs) HFr
    ltac:(ign_win Usp1)) as UN4.
  eapply (RET W3 _ _ _ _ _ HS5 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  prreg HS5 (1%bv : bv 5) R1. prreg HS5 (10%bv : bv 5) R10.
  unfold apost_base. eexists _, _, _, _, _.
  ign_head HS5 HJ3 R1 HAG F1 Hra HAE1 regs.
  split; [cbn [ms_regs]; rewrite R10; reflexivity|].
  split; [|exact HNA3].
  intros a Ha Hn _. rewrite WS in Hn. rewrite UN4 by (first [exact Ha | cbv beta; lia]). apply UN3; [exact Ha | rewrite WS; lia].
Qed.
End e.
End f.
End d.
Print Assumptions reac_segconf_ignored_walk.
About reac_segconf_ignored_walk.
