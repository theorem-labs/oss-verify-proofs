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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 656 of its 702 lines of code are new or changed and 407 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan): sub-walk FOUND of segment A8b of reac_segconf_parse_file's
   walk, `pfa8b_found : forall n, HA_A8B_JOIN B n -> H_FOUND B n` (2026-10-30).
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk); the rule-24 record is the unit's
   internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md (reuse
   verdict: none, written new).

   THE CODE (the unit's internal record, commit dfb49d6ad789, path records/segp/dis/reac_segconf_parse_file.fuzz_segconf.asan.s),
   FOUND 0x88964 .. 0x889b0:
     0x88964 srli a0,s7,3; add a0,a0,s6; lb a0,0(a0); bnez a0,0x88b78    check #36 (load4 seg[i].seen_gen)
     0x88974 ld a3,0x38(s1); lb a1,0(a3)                                check #37 (load4 c->gen; slot 0x38 holds
                                                                        the shadow address of c->gen)
     0x8897c lw a0,0x160(s4); ld s8,0x90(s1); ld s3,0x98(s1); bnez a1,0x88b88
     0x8898c ld a1,0x40(s1); lw a1,0(a1)                                a1 = c->gen
     0x88994 bne a0,a1,0x889b4                                          seen_gen <> gen: JOIN, no refusal
     0x88998 a2 = 0x21620 F_twice; a0 = s8 = c; a1 = s10; a3 = s9 = name; jal 0x88da4 <refuse>
     0x889b0 ld a3,0x38(s1)                                             then JOIN (0x889b4)

   THE WALK. One token run from FOUND (lib/A/Prog/SegPaLib.v paj_run_tok) over a seed with three read-only
   regions: the spill slots 0x38 (pf_a8b_q.v's pfq_sh term on the atom 32 = c, which the token executor's
   match_x recognises), 0x40, 0x90, 0x98 at s1; seg[i].seen_gen at s4 (atom 33); c->gen at c (atom 34). The
   shadow entries [s7, s7 + 8) and the block [c, c + SEG_C_SIZE) decide checks #36 and #37 (the shadow byte is
   the literal 0, so the slow blocks 0x88b78 / 0x88b88 are never reached). The run stops at the `bne`, which
   psrr_branch_tok splits on seen_gen = gen (both are lw's sign extensions, fnd_sext_eqb):
   - not equal: a token run to JOIN; the memory is the cut's, so INV_A8B_JOIN holds with cf;
   - equal: a plain run to the jal; refuse through PaFx.v's cl_callSF with refuse_contract at BASE + AF_refuse
     (the call target pa_sigma SS_refuse by SegObj.seg_sig_prog, the frame chain from pf_a5_k.a5_chain,
     refuse_pre from fnd_ref_pre, in the shape of pf_a6_k.v's refuse_site_ok_87e74); after the call pf_base at
     the FP state refuse returned from pf_a6_k.v's a6_keeps_refuse / a6_base_move, cur_name from a6_nm_move,
     the name in buf from the journal's frames clause (a6_keeps' last clause); then a plain run of the one
     `ld a3,0x38(s1)` from a fresh seed at 0x889b0 to JOIN, where INV_A8B_JOIN holds with
     refuse cf (ln + 1) F_twice [AS name]; the post is lifted from that FP state by srr_apost_baseF_lift.
   The model step is pf_a8b_m.pfa8b_step_found; pf_a8b_m.pfa8b_refuse_seg keeps rc_seg and rc_gen across the
   refusal, and fnd_cnt_refuse gives the next line's counter room (INV_A8B_JOIN's budget, pf_a8b_d.v; the
   budget was this line's until d60ebb8b416c, which this sub-walk's stop case changed).

   Section hypotheses:
     REF   refuse_contract at BASE + AF_refuse, at every FP state (A8b's callee, pf_pieces.v's segment list);
     SIGP  SegObj.seg_sig_prog (the call target pa_sigma SS_refuse is BASE + AF_refuse);
     OBJ   SegObj.seg_val_objs (the auipc / addi pair's object atom A_OBJ 68 is seg_litA_rc F_twice);
     VRO   SegObj.seg_val_relro, and
     SSPX  the stack-protector cells at every AR state (lib/A/Prog/reac_segconf_parse.v:137's shape): both
           FORCED by pf_a6_k.v's a6_base_move after the refuse call at 0x889ac, and used nowhere else.
           refuse's post gives only its journal, which keeps an image byte only when it is not one of
           `as_owned_static B` (YCbq.v:479); whether the GOT word 0xa36d8 and the guard 0x5ff078 are owned
           statics is a record fact of listing stage 2 (SegRecCells.seg_rec_cells, after the contract writer's AF0m),
           which discharges SSPX; arodata_okP after refuse needs pa_relro_img over RLO_A .. RHI_A, which is
           VRO (the pinned instance gives it by computation).
   The seen_gen / gen reads and the shadow-address term are pf_a8b_q.v's pfq_rd32_field / pfq_rd32_gen /
   pfq_sh_denot. Copied with attribution: fnd_val_mem_of_sa and fnd_u_reg are a8_val_mem_of_sa and a8_u_reg
   of lib/A/Prog/pf_a8a.v at commit 29edc5f7c819 (another prover's branch, so not Required). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtFormat RtPFCmd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstA pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a8b_d pf_a8b_m pf_a8b_q pf_a5_k pf_a6_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(** ** The symbolic states *)
(* the sp atoms (s1 is 32-aligned in [2^46, 2^47]) and a pointer below alloc_ceiling *)
Definition fnd_spF : afact := mkAF (2 ^ 46) (2 ^ 47) 5.
Definition fnd_ptr (al : Z) : afact := mkAF 4096 (2 ^ 47 - 2 ^ 15) al.
(* the shadow address of c->gen as the token executor's match_x shape, over the atom 32 = c and s6 *)
Definition fnd_shterm : sv := pfq_sh 32 seg_spec.RC_GEN.
(* FOUND 0x88964: the slots s1 + 0x38 .. 0x98 the stretch reads, seg[i].seen_gen at s4 = atom 20 (its value the
   atom 33), c->gen at c = atom 32 (its value the atom 34); nothing writable *)
Definition fnd_slots : YP09.region := YP09.mkRegion (Some 9%nat) 0x38 0xa0 0 0
  [YP09.mkChunk 0x38 (CVal 8 fnd_shterm);
   YP09.mkChunk 0x40 (CVal 8 (SOff 32 seg_spec.RC_GEN));
   YP09.mkChunk 0x90 (CVal 8 (SOff 32 0));
   YP09.mkChunk 0x98 (CVal 8 (SOff 27 8))].
Definition fnd_sg : YP09.region := YP09.mkRegion (Some 20%nat) seg_spec.RS_SEEN_GEN (seg_spec.RS_SEEN_GEN + 4) 0 0
  [YP09.mkChunk seg_spec.RS_SEEN_GEN (CVal 4 (SOff 33 0))].
Definition fnd_gen : YP09.region := YP09.mkRegion (Some 32%nat) seg_spec.RC_GEN (seg_spec.RC_GEN + 4) 0 0
  [YP09.mkChunk seg_spec.RC_GEN (CVal 4 (SOff 34 0))].
Definition fnd_F : facts := mkFacts [(2%nat, fnd_spF); (9%nat, fnd_spF); (20%nat, fnd_ptr 2); (22%nat, mkAF SB SB 0);
  (23%nat, fnd_ptr 2); (32%nat, fnd_ptr 4); (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition fnd_ss : sstate := mkSS PF_FOUND sr_atoms [fnd_slots; fnd_sg; fnd_gen] None fnd_F.
Definition fnd_Bx : sv := pfq_Bx.
(* check #36 reads the shadow of [s7, s7 + 4), check #37 that of [c + RC_GEN, + 4) *)
Definition fnd_SH : list shent := [mkSHE 23 0 8; mkSHE 32 0 seg_spec.SEG_C_SIZE].
(* 0x889b0 after refuse: the slot 0x38, its value the atom 32 *)
Definition fnd_j0slot : YP09.region := YP09.mkRegion (Some 9%nat) 0x38 0x40 0 0 [YP09.mkChunk 0x38 (CVal 8 (SOff 32 0))].
Definition fnd_ssj : sstate := mkSS PF_A8B_J0 sr_atoms [fnd_j0slot] None (mkFacts [(2%nat, fnd_spF); (9%nat, fnd_spF)] [] []).
(* lib/A/Prog/pf_a8a.v a8_val_mem_of_sa (commit 29edc5f7c819) *)
Lemma fnd_val_mem_of_sa : forall segs H mem a n v, sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.
(* seg[i].seen_gen and c->gen through sa_rconf *)
Lemma fnd_fields : forall (rd : reader) c cf i, sa_rconf rd c cf -> (i < length (rc_seg cf))%nat ->
  sa_val rd (seg_spec.rseg_addr c i + seg_spec.RS_SEEN_GEN) 4 (rs_seen_gen (nth i (rc_seg cf) rseg_d)) /\
  sa_val rd (c + seg_spec.RC_GEN) 4 (rc_gen cf) /\
  0 <= rs_seen_gen (nth i (rc_seg cf) rseg_d) < 2 ^ 32 /\ 0 <= rc_gen cf < 2 ^ 32.
Proof.
intros rd c cf i SRC Hi.
pose proof SRC as (bs & Hb & Henc).
pose proof Henc as (Lbs & L32 & HSEG & _ & _ & _ & _ & _ & _ & _ & HGEN).
pose proof (HSEG i Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSG).
unfold seg_spec.SEG_C_SIZE in Lbs.
unfold seg_spec.fldz in HSG. change (Z.to_nat seg_spec.RS_SEEN_GEN) with 352%nat in HSG.
change (Z.to_nat 4) with 4%nat in HSG. rewrite pfa8b_fld_fld in HSG by lia.
split; [|split; [|split]].
- replace (seg_spec.rseg_addr c i + seg_spec.RS_SEEN_GEN) with (c + Z.of_nat (356 * i + 352))
    by (unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_SEEN_GEN; lia).
  exact (pfq_rd32_field rd c bs (356 * i + 352) _ Hb HSG ltac:(lia)).
- exact (pfq_rd32_gen rd c cf SRC).
- exact (proj1 HSG).
- exact (proj1 HGEN).
Qed.
Lemma fnd_sl_get : forall (rd : reader) b L off v, pf_sl rd b L -> In (off, v) L -> rdword rd (b + off) = Some v.
Proof. intros rd b L off v H Hin. unfold pf_sl in H. rewrite Forall_forall in H. exact (H _ Hin). Qed.
Lemma fnd_mod4 : forall c k, c mod 16 = 0 -> (c + 4 * k) mod 4 = 0.
Proof.
intros c k H. pose proof (Z.div_mod c 16 ltac:(lia)) as D.
replace (c + 4 * k) with ((4 * (c / 16) + k) * 4) by lia. apply Z_mod_mult.
Qed.
(* lw sign-extends; for two u32 values the extensions agree iff the values do *)
Lemma fnd_swrap32 : forall x, 0 <= x < 2 ^ 32 ->
  zcanon (bv_swrap 32 (x mod 2 ^ Z.of_N 32)) = if x <? 2 ^ 31 then x else x + (2 ^ 64 - 2 ^ 32).
Proof.
intros x Hx. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small x (2 ^ 32)) by lia.
unfold bv_swrap, bv_half_modulus, bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
change (2 ^ 32 / 2) with (2 ^ 31).
destruct (Z.ltb_spec x (2 ^ 31)).
- rewrite (Z.mod_small (x + 2 ^ 31) (2 ^ 32)) by lia. replace (x + 2 ^ 31 - 2 ^ 31) with x by lia.
  apply zcanon_id. unfold M64. lia.
- rewrite <- (Z.mod_unique (x + 2 ^ 31) (2 ^ 32) 1 (x + 2 ^ 31 - 2 ^ 32)) by lia.
  unfold zcanon, M64. symmetry. apply Z.mod_unique with (q := -1); lia.
Qed.
Lemma fnd_sext_eqb : forall E x y, bv_unsigned (ew E 33) = x -> bv_unsigned (ew E 34) = y ->
  0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  (U E (SExt true 32 (SOff 33 0)) =? U E (SExt true 32 (SOff 34 0))) = (x =? y).
Proof.
intros E x y Hx Hy Rx Ry. rewrite !U_SExt, !U_SOff, Hx, Hy, !Z.add_0_r.
rewrite (zcanon_id x) by (unfold M64; lia). rewrite (zcanon_id y) by (unfold M64; lia).
rewrite (fnd_swrap32 x Rx), (fnd_swrap32 y Ry).
destruct (Z.ltb_spec x (2 ^ 31)), (Z.ltb_spec y (2 ^ 31)), (Z.eqb_spec x y);
  first [reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia | exfalso; lia].
Qed.
(* the counter room: the next line's after this line's, with or without the refusal *)
Lemma fnd_refuse_cnt : forall cf l f a,
  rc_refused (refuse cf l f a) = rc_refused cf + 1 /\ rc_overflow (refuse cf l f a) = rc_overflow cf.
Proof.
intros cf l f a. unfold refuse. cbv zeta.
repeat match goal with |- context [if ?b then _ else _] => destruct b end; split; reflexivity.
Qed.
Lemma fnd_cnt_next : forall cf (s : list Z) o, (o < length s)%nat -> pf_cnt cf (length (skipn o s)) ->
  pf_cnt cf (length (skipn (pf_next s o) s)).
Proof. intros cf s o Ho (H1 & H2). pose proof (pf_next_skipn_lt s o Ho) as L. split; lia. Qed.
Lemma fnd_cnt_refuse : forall cf l f a (s : list Z) o, (o < length s)%nat -> pf_cnt cf (length (skipn o s)) ->
  pf_cnt (refuse cf l f a) (length (skipn (pf_next s o) s)).
Proof.
intros cf l f a s o Ho (H1 & H2). pose proof (pf_next_skipn_lt s o Ho) as L.
destruct (fnd_refuse_cnt cf l f a) as [E1 E2]. unfold pf_cnt. rewrite E1, E2. split; lia.
Qed.
(* readers *)
Lemma fnd_str_in : forall (rd rd' : reader) p s lo hi, (forall a, lo <= a < hi -> rd' a = rd a) ->
  lo <= p -> p + Z.of_nat (length s) + 8 <= hi -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros rd rd' p s lo hi K H0 H1 [[Hz Hn] Ht]. split; [split; [|exact Hn]|].
- intros j Hj. pose proof Hj as Hj'. rewrite length_app in Hj'. cbn [length] in Hj'.
  rewrite K by lia. exact (Hz j Hj).
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)) as M.
  rewrite K by lia. exact (Ht x Hx).
Qed.
Lemma fnd_rg_ins : forall rX A a C, pf_rg rX (A ++ C) -> getr rX (Z_to_bv 5 (fst a)) = w64 (snd a) ->
  pf_rg rX (A ++ a :: C).
Proof.
intros rX A a C H Ha. unfold pf_rg in *. rewrite Forall_app in H |- *. destruct H as [H1 H2].
split; [exact H1 | constructor; [exact Ha | exact H2]].
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* lib/A/Prog/pf_a8a.v a8_u_reg (commit 29edc5f7c819) *)
Lemma fnd_u_reg : forall (rX : bvmap 5 word) extra n v, (n < 32)%nat -> getr rX (Z_to_bv 5 (Z.of_nat n)) = w64 v ->
  0 <= v < 2 ^ 64 -> bv_unsigned (ew (Eimg (Ereg rX extra)) n) = v.
Proof.
intros rX extra n v Hn Hr Hv. rewrite (ew_Eimg_Ereg_nat rX extra n (Z_to_bv 5 (Z.of_nat n))).
- rewrite Hr. unfold w64. apply unsigned_lit_small. lia.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small; lia.
Qed.
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Definition fnd_E (rX : bvmap 5 word) (c sg g : Z) : env := Eimg (Ereg rX [w64 c; w64 sg; w64 g]).
Definition fnd_Ej (rX : bvmap 5 word) (x : Z) : env := Eimg (Ereg rX [w64 x]).

Section c. Context {fx : YK11.FPState}.

(* the state at FOUND satisfies fnd_ss, and the two shadow entries hold *)
Lemma fnd_seed : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i,
  INV_FOUND B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i ->
  st_ok_pi SEGS VAL (fnd_E rX (p_c v) (rs_seen_gen (nth i (rc_seg cf) rseg_d)) (rc_gen cf)) fnd_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_FOUND)) memc (seg_rom SEGS))) /\
  sh_ok SEGS fnd_Bx fnd_SH (fnd_E rX (p_c v) (rs_seen_gen (nth i (rc_seg cf) rseg_d)) (rc_gen cf))
    (mrestrict (w_H Wc) memc).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i (HB & HM & (SRC & SNM & SCNT) & HS & HI & HL & HF & HR).
pose proof (pfa8b_find_lt _ _ _ HF) as Hi.
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin5 & G & _ & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof HB as (HCX & _ & HOB & HSL & _).
pose proof HOB as (_ & _ & _ & OCA & OCH & _).
destruct (a6_cx B v HCX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR OCH
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hc1 & Hc2 & Hc3 & Hc4 & Hcapp).
pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
pose proof STK_values as (_ & _ & _ & SPF & _).
destruct (fnd_fields _ _ _ _ SRC Hi) as (VSG & VG & RSG & RG).
pose proof (pfa8b_seg_in (p_c v) i 0 356 ltac:(destruct SRC as (bs & _ & (_ & L32 & _)); lia) ltac:(lia) ltac:(lia)
  ltac:(lia)) as (Si1 & Si2).
unfold seg_spec.SEG_C_SIZE, seg_spec.RC_N in *.
set (sg := rs_seen_gen (nth i (rc_seg cf) rseg_d)) in *. set (g := rc_gen cf) in *.
set (E := fnd_E rX (p_c v) sg g).
assert (U2 : bv_unsigned (ew E 2) = pf_s1 v)
  by (apply (fnd_u_reg rX _ 2); [lia | exact (a5_rg_get rX _ 2 _ HFI ltac:(cbn; tauto)) | lia]).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (apply (fnd_u_reg rX _ 9); [lia | exact (a5_rg_get rX _ 9 _ HFI ltac:(cbn; tauto)) | lia]).
assert (U22 : bv_unsigned (ew E 22) = SB)
  by (apply (fnd_u_reg rX _ 22); [lia | exact (a5_rg_get rX _ 22 _ HFI ltac:(cbn; tauto)) | unfold SB; lia]).
assert (U20 : bv_unsigned (ew E 20) = seg_spec.rseg_addr (p_c v) i)
  by (apply (fnd_u_reg rX _ 20); [lia | exact (a5_rg_get rX _ 20 _ HR ltac:(cbn; tauto))
     | unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE in *; lia]).
assert (U23 : bv_unsigned (ew E 23) = seg_spec.rseg_addr (p_c v) i + seg_spec.RS_SEEN_GEN)
  by (apply (fnd_u_reg rX _ 23); [lia | exact (a5_rg_get rX _ 23 _ HR ltac:(cbn; tauto))
     | unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_SEEN_GEN in *; lia]).
assert (U27 : bv_unsigned (ew E 27) = pf_SH v pos)
  by (apply (fnd_u_reg rX _ 27); [lia | exact (a5_rg_get rX _ 27 _ HR ltac:(cbn; tauto))
     | unfold kHighShadowEnd in *; lia]).
assert (E32 : ew E 32 = w64 (p_c v))
  by (subst E; unfold fnd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = w64 sg)
  by (subst E; unfold fnd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (E34 : ew E 34 = w64 g)
  by (subst E; unfold fnd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
assert (U32 : bv_unsigned (ew E 32) = p_c v) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = sg) by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = g) by (rewrite E34; unfold w64; apply unsigned_lit_small; lia).
assert (Hsoff : forall nn z x, bv_unsigned (ew E nn) = x -> sv_denot E (SOff nn z) = Z_to_bv 64 (x + z))
  by (intros nn z x Hx; cbn [sv_denot]; rewrite Hx; reflexivity).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; unfold fnd_E; rewrite (ew_Eimg_Ereg_nat rX _ 22 22%bv eq_refl);
      exact (a5_rg_get rX _ 22 _ HFI ltac:(cbn; tauto))).
assert (UB : U E fnd_Bx = SHADOW_OFF)
  by (rewrite <- SB_SHADOW_OFF; unfold fnd_Bx, pfq_Bx; rewrite U_SOff, U22, Z.add_0_r; apply zcanon_small;
      unfold SB, M64; lia).
split.
- rewrite restrict_mkst_fx. unfold fnd_ss. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * unfold region_ok, fnd_slots.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      -- apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x38 8 _ (shadow_addr (p_c v + seg_spec.RC_GEN)));
           [exact (pfq_sh_denot E 32 (p_c v) seg_spec.RC_GEN E32 E22 ltac:(lia) ltac:(unfold seg_spec.RC_GEN; lia)
              ltac:(unfold seg_spec.RC_GEN; lia))
           | unfold shadow_addr, SHADOW_OFF, seg_spec.RC_GEN; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
             split; [pose proof (Z.div_pos (p_c v + 16608) 8 ltac:(lia) ltac:(lia)); lia
                    | pose proof (Z.div_le_upper_bound (p_c v + 16608) 8 (p_c v + 16608) ltac:(lia) ltac:(lia)); lia]
           | cbn; lia |].
         apply val_mem_of_rdword. apply (fnd_sl_get _ _ _ _ _ HSL). unfold PF_SL. cbn [In]. tauto.
      -- apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x40 8 _ (p_c v + seg_spec.RC_GEN));
           [exact (Hsoff 32%nat _ _ U32) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.RC_GEN; lia
           | cbn; lia |].
         apply val_mem_of_rdword. apply (fnd_sl_get _ _ _ _ _ HSL). unfold PF_SL. cbn [In]. tauto.
      -- apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x90 8 _ (p_c v));
           [rewrite (Hsoff 32%nat _ _ U32), Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
           | cbn; lia |].
         apply val_mem_of_rdword. apply (fnd_sl_get _ _ _ _ _ HSL). unfold PF_SL. cbn [In]. tauto.
      -- apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x98 8 _ (pf_SH v pos + 8));
           [exact (Hsoff 27%nat _ _ U27) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold kHighShadowEnd in *; lia
           | cbn; lia |].
         apply val_mem_of_rdword. apply (fnd_sl_get _ _ _ _ _ HSL). unfold PF_SL. cbn [In]. tauto.
    * unfold region_ok, fnd_sg.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U20.
      unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_SEEN_GEN in *.
      split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (p_c v + 356 * Z.of_nat i) 352 4 (SOff 33 0) sg);
        [rewrite (Hsoff 33%nat 0 sg U33), Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      exact (fnd_val_mem_of_sa SEGS _ _ _ _ _ VSG).
    * unfold region_ok, fnd_gen.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
      unfold seg_spec.RC_GEN in *.
      split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (p_c v) 16608 4 (SOff 34 0) g);
        [rewrite (Hsoff 34%nat 0 g U34), Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      exact (fnd_val_mem_of_sa SEGS _ _ _ _ _ VG).
  + apply pairwise_disjoint_of_extents. unfold fnd_slots, fnd_sg, fnd_gen, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U20, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_SEEN_GEN, seg_spec.RC_GEN in *. repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok fnd_F]. unfold afact_ok, fnd_spF, fnd_ptr. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U20, U22, U23, U32, U33, U34.
    assert (M20 : seg_spec.rseg_addr (p_c v) i mod 2 ^ 2 = 0)
      by (unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE; change (2 ^ 2) with 4;
          replace (p_c v + 356 * Z.of_nat i) with (p_c v + 4 * (89 * Z.of_nat i)) by lia; apply fnd_mod4; exact Hc16).
    assert (M23 : (seg_spec.rseg_addr (p_c v) i + seg_spec.RS_SEEN_GEN) mod 2 ^ 2 = 0)
      by (unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_SEEN_GEN; change (2 ^ 2) with 4;
          replace (p_c v + 356 * Z.of_nat i + 352) with (p_c v + 4 * (89 * Z.of_nat i + 88)) by lia;
          apply fnd_mod4; exact Hc16).
    rewrite M20, M23. change (2 ^ 4) with 16. rewrite Hc16. change (2 ^ 5) with 32. rewrite G5.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_SEEN_GEN, SB in *. repeat split; lia.
- unfold sh_ok, fnd_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + eapply (shent_ok_of_range SEGS (w_H Wc) memc E fnd_Bx 23%nat (p_c v) 16616
      (seg_spec.rseg_addr (p_c v) i + seg_spec.RS_SEEN_GEN) 0 8 (proj1 (proj2 (proj2 (proj2 OCA)))) UB);
      [rewrite U_SOff, U23, Z.add_0_r; apply zcanon_small; unfold M64, seg_spec.rseg_addr, seg_spec.RSEG_SIZE,
         seg_spec.RS_SEEN_GEN in *; lia
      | unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_SEEN_GEN in *; lia
      | unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_SEEN_GEN in *; lia |].
    intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
    unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_SEEN_GEN in *.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
  + eapply (shent_ok_of_range SEGS (w_H Wc) memc E fnd_Bx 32%nat (p_c v) 16616 (p_c v) 0 16616
      (proj1 (proj2 (proj2 (proj2 OCA)))) UB);
      [rewrite U_SOff, U32, Z.add_0_r; apply zcanon_small; unfold M64; lia | lia | lia |].
    intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

(* pf_base after a run that wrote no memory: the journal it returned, the registers of pf_fi's list kept *)
Lemma fnd_still : forall v pos lyc Sc Wc rX memc mdc rX' mdc',
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc' 0 ->
  (forall r, In r [2; 3; 4; 8; 9; 22] -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_base B v pos lyc Sc Wc rX' memc mdc' PF_SC_LINE.
Proof.
intros v pos lyc Sc Wc rX memc mdc rX' mdc' HB HJ' KR.
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
destruct HB as (HCX & (HJ & Hly & HFS & HPERM & HSV & HFL & HFRM & _) & HOBJ & HSL & HFSH).
split; [exact HCX|]. split; [|exact (conj HOBJ (conj HSL HFSH))].
refine (conj HJ' (conj Hly (conj HFS (conj HPERM (conj HSV (conj HFL (conj HFRM _))))))).
unfold pf_rg in *. rewrite Forall_forall in HFI |- *. intros rv Hin. rewrite KR; [exact (HFI rv Hin)|].
cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]). destruct Hin.
Qed.

(* VERIFY rule 1j-bis, edge reac_segconf_parse_file -> refuse at 0x889ac (refuse(c, lineno, F_twice, name)):
   the cut at the call state gives refuse_contract's premises over the call's registers regsc (the shape of
   pf_a6_k.v's refuse_site_ok_87e74; the one %s argument, name, lies in buf: a6_buf_arg) *)
Lemma fnd_ref_pre : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name (regsc : bvmap 5 word),
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE -> pf_mid v o ln d n ->
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn o (p_s v))) ->
  sa_str (rdW Wc memc) np name -> pf_inb (pf_F v pos + PF_O_BUF) np name ->
  spZ regsc = pf_s1 v -> getr regsc 13 = w64 np ->
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\
  refuse_pre SEGS B seg_litA_rc gotwA guardA lyc Sc regsc (rdW Wc memc) (p_c v) (ln + 1) (seg_litA_rc F_twice)
    [getr regsc 13; getr regsc 14; getr regsc 15; getr regsc 16; getr regsc 17] cf (ln + 1) F_twice [AS name] /\
  sa_room Sc /\ st_nev Sc + EV_refuse <= EV_MAX.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name regsc HB MID ST HSs HIb Hsp R13.
pose proof HB as (CX & FI & OBJ & SL & FSH).
destruct (a6_cx B v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
pose proof FI as (HJ & Hly & _ & _ & _ & _ & HFRM & HRG).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & Hnev & _).
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hroom & Hev).
destruct OBJ as (STR & AT & HT & AC & HC & CAT & LITS & ROD & SSP).
destruct ST as (RC & NM & CNT).
destruct MID as (Ho & Hn & (Hno & Hlines & Hln & Hle)).
pose proof (pf_next_le (p_s v) o Ho) as HNL.
pose proof asan_consts as (C1 & _).
split; [exact ROD|].
split.
- unfold refuse_pre.
  split; [lia|]. split; [exact Hc16|]. split; [exact RC|]. split; [exact HC|]. split; [exact AC|].
  split; [destruct CNT as [CN1 _]; lia|].
  split; [lia|]. split; [reflexivity|].
  assert (HWl : Forall (fun iv => alloc_ceiling <= fst iv \/
      (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= fst iv /\ snd iv <= b + req_size m))
      [(ly_stk_lo lyc, spZ regsc);
       (seg_spec.refusal_addr (p_c v) (length (rc_refusal cf)),
        seg_spec.refusal_addr (p_c v) (length (rc_refusal cf)) + seg_spec.RC_REFUSAL_LEN);
       (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)]).
  { destruct (a6_heap_bounds B _ _ _ _ _ (p_c v) seg_spec.SEG_C_SIZE HAR HC ltac:(unfold seg_spec.SEG_C_SIZE; lia))
      as (bc & mc & Hinc & Hc1 & Hc2 & _).
    destruct RC as (bs & _ & (_ & _ & _ & _ & HL8 & _)).
    constructor; [left; cbn [fst]; rewrite Hly; lia|].
    constructor; [right; exists bc, mc; split; [exact Hinc|]; cbn [fst snd];
      unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.SEG_C_SIZE in *; lia|].
    constructor; [right; exists bc, mc; split; [exact Hinc|]; cbn [fst snd];
      unfold seg_spec.RC_REFUSED, seg_spec.SEG_C_SIZE in *; lia|].
    constructor. }
  destruct (a6_buf_arg B v pos lyc Sc Wc rX memc mdc PF_SC_LINE np name _ HB eq_refl eq_refl HSs HIb HWl)
    as [HVA HLOC].
  assert (HL : In F_twice PARSE_FILE_LITS)
    by (unfold PARSE_FILE_LITS; apply in_or_app; left; cbn [In]; repeat (first [left; reflexivity | right])).
  pose proof (LITS F_twice HL) as HLL.
  split; [unfold seg_spec.REFUSE_FORMATS; cbn [In]; repeat (first [left; reflexivity | right])|].
  split; [vm_compute; reflexivity|].
  split; [destruct HLL as (Hp & _); lia|]. split; [reflexivity|]. split; [exact HLL|].
  split; [cbn [sa_va_args]; rewrite R13; exact (conj HVA I)|].
  split; [cbn [refuse_va_locs]; rewrite R13; exact (conj HLOC I)|].
  split; [exact HFRM|]. split; [exact SSP|].
  intros y Hy. apply LITS. unfold PARSE_FILE_LITS. apply in_or_app. right. exact Hy.
- split.
  + unfold sa_room. unfold sa_room_n in Hroom. rewrite Hfrs. cbn [app length]. lia.
  + unfold EV_refuse. unfold EV_reac_segconf_parse_file in Hev. lia.
Qed.

(* the state at 0x889b0 after refuse satisfies fnd_ssj: the slot 0x38 holds x *)
Lemma fnd_seedj : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 x,
  getr regs (Z_to_bv 5 2) = w64 s1 -> getr regs (Z_to_bv 5 9) = w64 s1 -> 2 ^ 46 <= s1 <= 2 ^ 47 ->
  s1 mod 32 = 0 -> 0 <= x < 2 ^ 64 -> rdword (rdW W mem) (s1 + 0x38) = Some x ->
  st_ok_pi SEGS VAL (fnd_Ej regs x) fnd_ssj
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + PF_A8B_J0)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 x R2 R9 Hs Hs32 Hx Hw.
assert (U2 : bv_unsigned (ew (fnd_Ej regs x) 2) = s1) by (apply (fnd_u_reg regs _ 2); [lia | exact R2 | lia]).
assert (U9 : bv_unsigned (ew (fnd_Ej regs x) 9) = s1) by (apply (fnd_u_reg regs _ 9); [lia | exact R9 | lia]).
assert (E32 : ew (fnd_Ej regs x) 32 = w64 x)
  by (unfold fnd_Ej; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U32 : bv_unsigned (ew (fnd_Ej regs x) 32) = x) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold fnd_ssj. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, fnd_j0slot.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ s1 0x38 8 (SOff 32 0) x);
    [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
  apply val_mem_of_rdword. exact Hw.
- apply pairwise_disjoint_of_extents. cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, fnd_spF. cbn [af_lo af_hi af_al2].
  rewrite U2, U9. change (2 ^ 5) with 32. rewrite Hs32. repeat split; lia.
Qed.

End c.

(* the program callee (pf_pieces.v's segment list for A8b), at image A's numbers, at every FP state *)
Hypothesis REF : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the listing's facts over the walk's abstract instance (SegObj.v; the pinned instance gives each by
   computation): the call target, the object atoms *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
(* FORCED by pf_a6_k.v's a6_base_move after the refuse call at 0x889ac, used nowhere else (see the head
   comment): the read-only range is the listing's *)
Hypothesis VRO : seg_val_relro (PI := PI).
(* the stack-protector cells at every AR state: the image-A owner's route A, the shape of
   lib/A/Prog/reac_segconf_parse.v; discharged by SegRecCells.seg_rec_cells when listing stage 2 compiles. FORCED
   by a6_base_move after the refuse call (refuse's journal keeps no owned static), used nowhere else. *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

(* the literal a2 holds at the call: listing object 68 is F_twice's text (SegInstA.v's map) *)
Lemma fnd_lit : forall E, img_env VAL A_LIM E -> ew E (A_OBJ 68) = w64 (seg_litA_rc F_twice).
Proof.
intros E HE. rewrite (img_env_atomP E (A_OBJ 68) HE) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
rewrite (OBJ 68%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

(* a run whose regions have no write window left the memory as it was *)
Local Ltac fnd_frame HF Hm :=
  lazymatch type of HF with frame_of _ ?rs ?m ?m' =>
    assert (Hm : m' = m);
    [ apply functional_extensionality; intros x; rewrite HF; [reflexivity|];
      let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
      intros (r & Hr & Ha); vm_compute in Hr;
      repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|]);
      destruct Hr
    | ] end.
Local Ltac fnd_awr :=
  lazymatch goal with |- awr_ok ?sgs ?Bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sgs Bb Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Local Ltac fnd_ms_name msN :=
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msN end.
Local Ltac fnd_md_name mdN :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdN := dM) in *; clearbody mdN end.
Local Ltac fnd_prreg0 HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* membership of a register in a list of bv literals (the literals' well-formedness proofs differ) *)
Local Ltac fnd_bvin := cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]).

Section s.
Context {fx : YK11.FPState}.
Let RUN := paj_run (fx := fx) B LAWS.
Let RUNTO := paj_run_to (fx := fx) B LAWS.
Let BR := paj_branch (fx := fx) (PI := PI).

Lemma pfa8b_found : forall n : nat, HA_A8B_JOIN B n -> H_FOUND (fx := fx) B n.
Proof.
intros n HJN. unfold H_FOUND.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i HI.
destruct (fnd_seed n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i HI) as [HS SHOK].
destruct HI as (HB & HM & HST & HSs & HIb & HL & Hfnd & HR).
pose proof (pfa8b_find_lt _ _ _ Hfnd) as Hi.
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin5 & G & _ & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof HB as (HCX & (HJ & _) & HOB & HSL & HFSH).
pose proof HOB as (_ & _ & _ & OCA & OCH & _).
destruct (a6_cx B v HCX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR OCH
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hc1 & Hc2 & Hc3 & Hc4 & Hcapp).
pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
pose proof STK_values as (_ & SRF & _ & SPF & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (fnd_fields _ _ _ _ (proj1 HST) Hi) as (_ & _ & RSG & RG).
pose proof HM as (Ho & _ & (_ & _ & Hln & Hle)).
pose proof (pf_next_le (p_s v) o Ho) as HNL.
pose proof (pfa8b_o_ok v G3) as (O16 & O0 & O336).
unfold seg_spec.SEG_C_SIZE in *.
rewrite (pfa8b_step_found cf nm name (ln + 1) i Hfnd). cbv zeta.
set (sg := rs_seen_gen (nth i (rc_seg cf) rseg_d)) in *. set (g := rc_gen cf) in *.
assert (HEI : img_env VAL A_LIM (fnd_E rX (p_c v) sg g)) by apply Eimg_env.
assert (HA : env_agree 32 (Ereg rX [w64 (p_c v); w64 sg; w64 g]) (fnd_E rX (p_c v) sg g)).
{ split; [|reflexivity]. intros k Hk. unfold fnd_E. apply Eimg_low. unfold A_TEXT. lia. }
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (fnd_E rX (p_c v) sg g) k = getr rX r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew (fnd_E rX (p_c v) sg g) 32 = w64 (p_c v))
  by (unfold fnd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew (fnd_E rX (p_c v) sg g) 33 = w64 sg)
  by (unfold fnd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (E34 : ew (fnd_E rX (p_c v) sg g) 34 = w64 g)
  by (unfold fnd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
assert (U22 : bv_unsigned (ew (fnd_E rX (p_c v) sg g) 22) = SB)
  by (apply (fnd_u_reg rX _ 22); [lia | exact (a5_rg_get rX _ 22 _ HFI ltac:(cbn; tauto)) | unfold SB; lia]).
assert (U27 : bv_unsigned (ew (fnd_E rX (p_c v) sg g) 27) = pf_SH v pos)
  by (apply (fnd_u_reg rX _ 27); [lia | exact (a5_rg_get rX _ 27 _ HR ltac:(cbn; tauto))
     | unfold kHighShadowEnd in *; lia]).
assert (U32 : bv_unsigned (ew (fnd_E rX (p_c v) sg g) 32) = p_c v)
  by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew (fnd_E rX (p_c v) sg g) 33) = sg)
  by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (fnd_E rX (p_c v) sg g) 34) = g)
  by (rewrite E34; unfold w64; apply unsigned_lit_small; lia).
assert (E22 : ew (fnd_E rX (p_c v) sg g) 22 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EE 22%nat 22%bv eq_refl); exact (a5_rg_get rX _ 22 _ HFI ltac:(cbn; tauto))).
revert HS SHOK HEI HA EE E22 E32 E33 E34 U22 U27 U32 U33 U34.
generalize (fnd_E rX (p_c v) sg g) as E. intros E HS SHOK HEI HA EE E22 E32 E33 E34 U22 U27 U32 U33 U34.
change (cfg_at SEGS (BASE + PF_FOUND) rX memc mdc)
  with (mkCfg (mkst rX (Z_to_bv 64 (BASE + PF_FOUND)) memc (seg_rom SEGS)) mdc).
(* 0x88964 .. 0x88994: checks #36 and #37 decided by the shadow entries, the five loads, up to the bne *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ fnd_awr. }
fnd_ms_name ms1. fnd_md_name md1.
fnd_frame HF Hm1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* seen_gen <> gen: 0x889b4 = JOIN, with cf *)
  assert (Hne : sg <> g).
  { rewrite branch_ne_U, (fnd_sext_eqb E sg g U33 U34 RSG RG) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    exact Hc. }
  rewrite (proj2 (Z.eqb_neq sg g) Hne). clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_A8B_JOIN.
  { fnd_awr. }
  fnd_ms_name ms2. fnd_md_name md2.
  fnd_frame HF Hm2. rewrite Hm1 in Hm2. rewrite Hm2 in HJ. clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi _ _ _ rX _
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 25%bv; 26%bv; 27%bv] HS HA
    ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
  prreg HS (Z_to_bv 5 19 : bv 5) Q19. prreg HS (Z_to_bv 5 24 : bv 5) Q24.
  fnd_prreg0 HS (Z_to_bv 5 13 : bv 5) Q13.
  pmkst HS. rewrite Hm2.
  assert (HB2 : pf_base B v pos lyc Sc Wc (ms_regs ms2) memc md2 PF_SC_LINE).
  { apply (fnd_still v pos lyc Sc Wc rX memc mdc (ms_regs ms2) md2 HB HJ).
    intros r Hr. apply KR. cbn [In] in Hr |- *.
    repeat (destruct Hr as [<- | Hr]; [fnd_bvin|]). destruct Hr. }
  change (BASE + 15488) with (BASE + PF_A8B_JOIN).
  apply (HJN fx v pos lyc Sc Wc (ms_regs ms2) memc md2 cf nm o ln d np name i).
  split; [exact HB2|]. split; [exact HM|].
  split; [destruct HST as (X1 & X2 & X3); exact (conj X1 (conj X2 (fnd_cnt_next cf (p_s v) o Ho X3)))|].
  split; [exact HSs|]. split; [exact HIb|]. split; [exact HL|]. split; [exact Hi|].
  unfold pf_rg, PF_RM. cbn [app].
  repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
  + rewrite (KR (Z_to_bv 5 18) ltac:(fnd_bvin)). exact (a5_rg_get rX _ 18 _ HR ltac:(cbn; tauto)).
  + rewrite Q19, U27. reflexivity.
  + rewrite Q24, E32. reflexivity.
  + rewrite (KR (Z_to_bv 5 27) ltac:(fnd_bvin)). exact (a5_rg_get rX _ 27 _ HR ltac:(cbn; tauto)).
  + rewrite (KR (Z_to_bv 5 20) ltac:(fnd_bvin)). exact (a5_rg_get rX _ 20 _ HR ltac:(cbn; tauto)).
  + rewrite (KR (Z_to_bv 5 25) ltac:(fnd_bvin)). exact (a5_rg_get rX _ 25 _ HR ltac:(cbn; tauto)).
  + rewrite Q13. exact (pfq_sh_denot E 32 (p_c v) seg_spec.RC_GEN E32 E22 ltac:(lia)
      ltac:(unfold seg_spec.RC_GEN; lia) ltac:(unfold seg_spec.RC_GEN; lia)).
  + rewrite (KR (Z_to_bv 5 21) ltac:(fnd_bvin)).
    exact (a5_rg_get rX _ 21 _ HR ltac:(cbn [PF_RM app In]; tauto)).
  + rewrite (KR (Z_to_bv 5 26) ltac:(fnd_bvin)).
    exact (a5_rg_get rX _ 26 _ HR ltac:(cbn [PF_RM app In]; tauto)).
- (* seen_gen = gen: refuse(c, lineno, F_twice, name) at 0x889ac *)
  assert (Heq : sg = g).
  { rewrite branch_ne_U, (fnd_sext_eqb E sg g U33 U34 RSG RG) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    exact Hc. }
  rewrite (proj2 (Z.eqb_eq sg g) Heq). clear Hc.
  (* 0x88998 .. 0x889ac: a2 = F_twice's literal, a0 = s8 = c, a1 = s10 = lineno, a3 = s9 = name, the call *)
  paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
  { fnd_awr. }
  fnd_ms_name ms2. fnd_md_name md2.
  fnd_frame HF Hm2. rewrite Hm1 in Hm2. rewrite Hm2 in HJ. clear HF HFr HG.
  pmkst HS. rewrite Hm2.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ rX _
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 25%bv; 26%bv; 27%bv] HS HA
    ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
  prreg HS (Z_to_bv 5 19 : bv 5) Q19. prreg HS (Z_to_bv 5 24 : bv 5) Q24.
  assert (R2 : getr (ms_regs ms2) 2 = w64 (pf_s1 v)).
  { rewrite (KR 2%bv ltac:(fnd_bvin)). exact (a5_rg_get rX _ 2 _ HFI ltac:(cbn [a5_FI In]; tauto)). }
  assert (R3 : getr (ms_regs ms2) 3 = w64 (as_gp B)).
  { rewrite (KR 3%bv ltac:(fnd_bvin)). exact (a5_rg_get rX _ 3 _ HFI ltac:(cbn [a5_FI In]; tauto)). }
  assert (R4 : getr (ms_regs ms2) 4 = w64 (as_tp B)).
  { rewrite (KR 4%bv ltac:(fnd_bvin)). exact (a5_rg_get rX _ 4 _ HFI ltac:(cbn [a5_FI In]; tauto)). }
  assert (R8 : getr (ms_regs ms2) 8 = w64 (pf_sp0 v)).
  { rewrite (KR 8%bv ltac:(fnd_bvin)). exact (a5_rg_get rX _ 8 _ HFI ltac:(cbn [a5_FI In]; tauto)). }
  assert (Csp : spZ (ms_regs ms2) = pf_s1 v).
  { unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. lia. }
  assert (C1 : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + PF_A8B_J0)).
  { rewrite Q1. unfold PF_A8B_J0, AF_reac_segconf_parse_file. reflexivity. }
  assert (C10 : getr (ms_regs ms2) 10 = w64 (p_c v)) by (rewrite Q10; exact E32).
  assert (C11 : getr (ms_regs ms2) 11 = w64 (ln + 1)).
  { rewrite Q11, (EE 26%nat 26%bv eq_refl). exact (a5_rg_get rX _ 26 _ HR ltac:(cbn [PF_RM app In]; tauto)). }
  assert (C12 : getr (ms_regs ms2) 12 = w64 (seg_litA_rc F_twice)).
  { rewrite Q12. change 309%nat with (A_OBJ 68). exact (fnd_lit _ HEI). }
  assert (C13 : getr (ms_regs ms2) 13 = w64 np).
  { rewrite Q13, (EE 25%nat 25%bv eq_refl). exact (a5_rg_get rX _ 25 _ HR ltac:(cbn; tauto)). }
  assert (KRc : forall r, In r [2; 3; 4; 8; 9; 22] -> getr (ms_regs ms2) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. apply KR. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [fnd_bvin|]). destruct Hr. }
  pose proof (fnd_still v pos lyc Sc Wc rX memc mdc (ms_regs ms2) md2 HB HJ KRc) as HBc.
  (* the registers the cut names, at the call *)
  assert (HRGc : pf_rg (ms_regs ms2) ([(18, 0x23); (19, pf_SH v pos + 8); (24, p_c v); (27, pf_SH v pos);
                   (20, seg_spec.rseg_addr (p_c v) i); (25, np)] ++ PF_RM v o ln)).
  { unfold pf_rg, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    - rewrite (KR (Z_to_bv 5 18) ltac:(fnd_bvin)). exact (a5_rg_get rX _ 18 _ HR ltac:(cbn; tauto)).
    - rewrite Q19, U27. reflexivity.
    - rewrite Q24, E32. reflexivity.
    - rewrite (KR (Z_to_bv 5 27) ltac:(fnd_bvin)). exact (a5_rg_get rX _ 27 _ HR ltac:(cbn; tauto)).
    - rewrite (KR (Z_to_bv 5 20) ltac:(fnd_bvin)). exact (a5_rg_get rX _ 20 _ HR ltac:(cbn; tauto)).
    - rewrite (KR (Z_to_bv 5 25) ltac:(fnd_bvin)). exact (a5_rg_get rX _ 25 _ HR ltac:(cbn; tauto)).
    - rewrite (KR (Z_to_bv 5 21) ltac:(fnd_bvin)).
      exact (a5_rg_get rX _ 21 _ HR ltac:(cbn [PF_RM app In]; tauto)).
    - rewrite (KR (Z_to_bv 5 26) ltac:(fnd_bvin)).
      exact (a5_rg_get rX _ 26 _ HR ltac:(cbn [PF_RM app In]; tauto)). }
  destruct (a5_chain B v pos lyc Sc Wc (ms_regs ms2) memc md2 PF_SC_LINE HBc) as [ch1 HCH].
  destruct (fnd_ref_pre n v pos lyc Sc Wc (ms_regs ms2) memc md2 cf nm o ln d np name (ms_regs ms2) HBc HM HST HSs
    HIb Csp C13) as (ROD & RPRE & ROOM & EV).
  assert (Hf64 : 0 <= seg_litA_rc F_twice < 2 ^ 64).
  { assert (Hfv : seg_litA_rc F_twice = 0x21620) by (vm_compute; reflexivity). rewrite Hfv. lia. }
  rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
  eapply SRr_bind.
  { eapply (cl_callSF (fx := fx) B LAWS Wc (ms_regs ms2) memc _ STK_reac_segconf_parse_file (pf_sp0 v)
      (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc md2 0
      STK_refuse (refuse_W (p_c v) cf) EV_refuse (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + PF_A8B_J0)) ch1
      (fun ly2 S2 W2 regs2 mem2 md2 =>
         sa_rconf (rdW W2 mem2) (p_c v) (refuse cf (ln + 1) F_twice [AS name]) /\ sa_noalloc B lyc Sc ly2 S2) HJ).
    - rewrite Csp. lia.
    - exact O16.
    - exact O0.
    - rewrite SRF. lia.
    - rewrite SRF, SPF. lia.
    - exact R3.
    - exact R4.
    - exact C1.
    - apply ret_ok_codeptr_v; [unfold PF_A8B_J0, AF_reac_segconf_parse_file; lia | reflexivity].
    - rewrite unsigned_lit_small by (unfold PF_A8B_J0, AF_reac_segconf_parse_file; lia).
      unfold PF_A8B_J0, AF_reac_segconf_parse_file. lia.
    - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
      unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH.
    - intros HPRE1. eapply SRr_mono.
      { exact (REF fx lyc Sc Wc (ms_regs ms2) memc md2 ch1 (p_c v) (ln + 1) (seg_litA_rc F_twice) (ln + 1) cf
          F_twice [AS name] HPRE1 ROD C10 ltac:(lia) C11 ltac:(lia) C12 Hf64 RPRE ROOM EV). }
      cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
      exists fx', ly', S', regs', mem', md'. split; [rewrite C1; reflexivity|].
      split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
    - intros a Ha. left. split; [exact (a6_refuse_W_sub _ _ a Ha)|].
      apply a6_refuse_W_in_block in Ha. exists bc, mc. split; [exact Hinc|].
      unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW in *. lia. }
  (* back at 0x889b0, at the FP state fx1 refuse returned *)
  cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md3 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (HRC2 & HNA2)).
  unfold pf_postm, PF_POSTr.
  eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
  replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HJc2 by lia.
  replace (0 + EV_refuse) with 0 in HJ2 by (unfold EV_refuse; lia).
  destruct HNA2 as (HP2b & Hly2 & HS2).
  pose proof (a6_keeps_refuse B v pos lyc Sc Wc (ms_regs ms2) memc md2 PF_SC_LINE cf ly2 S2 W2 mem2 md3 EV_refuse
    HBc HJc2 HP2b) as HK.
  (* pf_base at the returned state: the heap facts re-derived from AR there (a6_base_move; VRO, SSPX) *)
  assert (HB3 : pf_base (fx := fx1) B v pos ly2 S2 W2 regs2 mem2 md3 PF_SC_LINE).
  { apply (a6_base_move (fx := fx) B VRO SSPX fx1 v pos lyc Sc Wc (ms_regs ms2) memc md2 PF_SC_LINE ly2 S2 W2 regs2
      mem2 md3 HBc Hfx1 HJ2 Hly2 HS2 HP2b HK).
    intros r Hr. apply HP2. unfold acallee_saved. cbn [In] in Hr. lia. }
  subst ly2.
  assert (HCS : Forall (fun rv => acallee_saved (fst rv))
    ([(18, 0x23); (19, pf_SH v pos + 8); (24, p_c v); (27, pf_SH v pos); (20, seg_spec.rseg_addr (p_c v) i);
      (25, np)] ++ PF_RM v o ln)).
  { unfold PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. }
  pose proof (a5_rg_pres (ms_regs ms2) regs2 _ HP2 HCS HRGc) as HRG2.
  pose proof HK as (_ & _ & _ & K4).
  assert (KF : forall a, pf_F v pos <= a < pf_F v pos + fs_frame_bytes 5 -> rdW W2 mem2 a = rdW Wc memc a)
    by (intros a Ha; apply K4; left; exact Ha).
  (* the facts of the cut after the refusal, at the returned state *)
  set (cf2 := refuse cf (ln + 1) F_twice [AS name]).
  assert (HST2 : pf_st0 v pos (rdW W2 mem2) cf2 nm (length (skipn (pf_next (p_s v) o) (p_s v)))).
  { destruct HST as (X1 & X2 & X3). split; [exact HRC2|]. split.
    - exact (a6_nm_move v pos (rdW Wc memc) _ nm X2 KF).
    - exact (fnd_cnt_refuse cf (ln + 1) F_twice [AS name] (p_s v) o Ho X3). }
  assert (HSs2 : sa_str (rdW W2 mem2) np name).
  { destruct HIb as [Hb1 Hb2]. unfold PF_O_BUF in Hb1, Hb2.
    apply (fnd_str_in (rdW Wc memc) _ np name (pf_F v pos) (pf_F v pos + 2048)); [|lia|lia|exact HSs].
    intros a Ha. apply KF. change (fs_frame_bytes 5) with 2048. exact Ha. }
  (* 0x889b0: ld a3,0x38(s1), from a fresh seed, to JOIN *)
  pose proof HB3 as (_ & (_ & _ & _ & _ & _ & _ & _ & HRF3) & _ & HSL3 & _).
  assert (Hxr : 0 <= shadow_addr (p_c v + seg_spec.RC_GEN) < 2 ^ 64).
  { unfold shadow_addr, SHADOW_OFF, seg_spec.RC_GEN.
    pose proof (Z.div_pos (p_c v + 16608) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (p_c v + 16608) 8 (p_c v + 16608) ltac:(lia) ltac:(lia)). lia. }
  pose proof (fnd_seedj (fx := fx1) W2 regs2 mem2 (pf_s1 v) (shadow_addr (p_c v + seg_spec.RC_GEN))
    (a5_rg_get regs2 _ 2 _ HRF3 ltac:(cbn; tauto)) (a5_rg_get regs2 _ 9 _ HRF3 ltac:(cbn; tauto)) ltac:(lia) G5 Hxr
    (fnd_sl_get _ _ _ 0x38 (shadow_addr (p_c v + seg_spec.RC_GEN)) HSL3 ltac:(unfold PF_SL; cbn [In]; tauto))) as HSj.
  assert (HEIj : img_env VAL A_LIM (fnd_Ej regs2 (shadow_addr (p_c v + seg_spec.RC_GEN)))) by apply Eimg_env.
  assert (HAj : env_agree 32 (Ereg regs2 [w64 (shadow_addr (p_c v + seg_spec.RC_GEN))])
                  (fnd_Ej regs2 (shadow_addr (p_c v + seg_spec.RC_GEN)))).
  { split; [|reflexivity]. intros k Hk. unfold fnd_Ej. apply Eimg_low. unfold A_TEXT. lia. }
  assert (E32j : ew (fnd_Ej regs2 (shadow_addr (p_c v + seg_spec.RC_GEN))) 32 =
                 w64 (shadow_addr (p_c v + seg_spec.RC_GEN)))
    by (unfold fnd_Ej; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  revert HSj HEIj HAj E32j. generalize (fnd_Ej regs2 (shadow_addr (p_c v + seg_spec.RC_GEN))) as Ej.
  intros Ej HSj HEIj HAj E32j.
  change (BASE + PF_A8B_J0) with (BASE + 15484) in HSj |- *.
  paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx1) B LAWS) HSj HJ2 PF_A8B_JOIN.
  { fnd_awr. }
  fnd_ms_name ms3. fnd_md_name md4.
  fnd_frame HF Hm3. rewrite Hm3 in HJ2. clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 24%bv; 25%bv; 26%bv; 27%bv] HSj HAj
    ltac:(vm_compute; reflexivity)) as KR3. cbn [ms_regs restrict] in KR3.
  prreg HSj (Z_to_bv 5 13 : bv 5) Q13j.
  pmkst HSj. rewrite Hm3.
  assert (HB4 : pf_base (fx := fx1) B v pos lyc S2 W2 (ms_regs ms3) mem2 md4 PF_SC_LINE).
  { apply (fnd_still (fx := fx1) v pos lyc S2 W2 regs2 mem2 md3 (ms_regs ms3) md4 HB3 HJ2).
    intros r Hr. apply KR3. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [fnd_bvin|]). destruct Hr. }
  change (BASE + 15488) with (BASE + PF_A8B_JOIN).
  apply (HJN fx1 v pos lyc S2 W2 (ms_regs ms3) mem2 md4 cf2 nm o ln d np name i).
  split; [exact HB4|]. split; [exact HM|]. split; [exact HST2|].
  split; [exact HSs2|]. split; [exact HIb|]. split; [exact HL|].
  split; [unfold cf2; rewrite (proj1 (pfa8b_refuse_seg cf (ln + 1) F_twice [AS name])); exact Hi|].
  change ([(18, 0x23); (19, pf_SH v pos + 8); (24, p_c v); (27, pf_SH v pos); (20, seg_spec.rseg_addr (p_c v) i);
           (25, np); (13, shadow_addr (p_c v + seg_spec.RC_GEN))] ++ PF_RM v o ln)
    with ([(18, 0x23); (19, pf_SH v pos + 8); (24, p_c v); (27, pf_SH v pos); (20, seg_spec.rseg_addr (p_c v) i);
           (25, np)] ++ (13, shadow_addr (p_c v + seg_spec.RC_GEN)) :: PF_RM v o ln).
  apply fnd_rg_ins.
  + unfold pf_rg in HRG2 |- *. rewrite Forall_forall in HRG2 |- *. intros rv Hin. rewrite <- (HRG2 rv Hin).
    apply KR3. unfold PF_RM in Hin. cbn [app In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [fnd_bvin|]). destruct Hin.
  + cbn [fst snd]. rewrite Q13j. exact E32j.
Qed.

End s.
End e.
End f.
End d.
