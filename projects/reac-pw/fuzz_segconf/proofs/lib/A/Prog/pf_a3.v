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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 571 of its 618 lines of code are new or changed and 406 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): SEGMENT A3 of reac_segconf_parse_file's walk,
   `pf_a3_holds : S_A3 B` (lib/A/Prog/pf_pieces.v). Segment A3's proof, 2026-10-30.

   FRAME 0x87cc4 -> HEAD 0x87ddc or DONE 0x88bb8; 80 instructions (0x87cc4-0x87ddc and the two cold check
   blocks 0x88c68-0x88c90), checks #1 and #2, one snprintf call (0x87ce8) and one checked memset (0x87d4c).

     0x87cc4 add s5,s8,a0            s5 = c + 0x4080 = &c->reading
     0x87cc8 bnez s3                 the label: s3 = lp, or the literal "reac-pw.conf" (0x21360) at 0x87cd0
     0x87cd4 a2 = "%s" 0x21340; a1 = 96; a0 = s5; a3 = the label
     0x87ce8 jal snprintf            c->reading = snprintf_s 96 F_s [AS L]
     0x87cec check #1 (load4 of c->gen, slow block 0x88c68); 0x87d00-0x87d14 c->gen++
     0x87d18 ld s3,0x98(s1)          s3 = SH + 8
     0x87d1c beqz s9                 dead: reader_pre gives t <> 0
     0x87d20-0x87d34 the slots 0x38 0x80 0x58 0x40 0x68, a0 = F + 0x20
     0x87d38 sb zero,4(s11); sb zero,5(s11)   cur_name's two shadow cells in scope
     0x87d4c jal __asan_memset       memset(cur_name, 0, 16)
     0x87d50 check #2 (load1 of text[0], slow block 0x88c80)
     0x87d60 lbu a0,0(s9); 0x87d64-0x87d6c slot 0x60 = (c + RC_N) / 8
     0x87d70 beqz a0                 -> DONE 0x88bb8 (the text is empty), else
     0x87d74-0x87dd8 the loop constants and the remaining slots; HEAD 0x87ddc

   THE ENGINE. The walk re-seeds a symbolic state (SegPaLib.pa_entry_st_ok_full) at each of five program
   points and runs the verified executor between them; every region hangs off a register atom, so the seed
   needs no register rewriting (regs_ok_Eimg_Ereg). The two inline checks are token runs with NO region
   (a region whose write window meets the shadow band breaks sh_static_ok, AWALK-FORM.md section 5 item 3);
   the runs that write are plain runs. The extra atoms are 32 = c->gen's old value and 33 = the text's first
   byte. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtPFShared RtPFCmd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaArtOwn PaFx PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a3_f pf_a3_d pf_a3_k pf_a3_w.
(* pf_a5_k.v: the register-list moves a5_rg_get / a5_rg_pres / a5_rg_incl; pf_a6_k.v: a6_w64_u and a6_heap_addr;
   pf_a8b_t.v: a C string's bytes over the ASan reader *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require pf_a5_k pf_a6_k pf_a8b_t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the offsets of struct reac_segconf and the frame's objects as hypotheses lia can use *)
Local Ltac a3_k :=
  pose proof (eq_refl : seg_spec.SEG_C_SIZE = 16616);
  pose proof (eq_refl : seg_spec.RC_N = 11392);
  pose proof (eq_refl : seg_spec.RC_READING = 16512);
  pose proof (eq_refl : seg_spec.RC_GEN = 16608);
  pose proof (eq_refl : seg_spec.RC_OVERFLOW = 13520);
  pose proof (eq_refl : seg_spec.RS_SEEN_GEN = 352);
  pose proof (eq_refl : PF_O_CN = 32); pose proof (eq_refl : PF_O_BUF = 64);
  pose proof (eq_refl : PF_O_LOW = 640); pose proof (eq_refl : PF_O_L146 = 736);
  pose proof (eq_refl : PF_O_KNOWN = 800); pose proof (eq_refl : PF_O_NTOK = 1104);
  assert (HFB5 : fs_frame_bytes 5 = 2048) by (vm_compute; reflexivity).
(* a register of a symbolic state, NOT normalised (prreg's cbn would unfold an SAlu's denotation) *)
Local Ltac a3_raw HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms (Z_to_bv 5 r) HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 r)) in
    change (sr_get (ss_regs ss) (Z_to_bv 5 r)) with e in Hr; cbn [ms_regs restrict mkst] in Hr
  end.

Section d. Context {rc : YM05.RunCeil}.
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

(* the callees of this segment, at every FP state (pf_pieces.v's list for A3) *)
Hypothesis SNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis MSET : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OSet (SIGMA SS___asan_memset).
(* the listing's facts over the walk's abstract instance (SegObj.v) *)
Hypothesis OBJ : seg_val_objs (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ======================= 0. the image objects this segment names ======================= *)
Lemma a3_obj_at : forall (E : env) (i : nat), img_env VAL A_LIM E -> (i < 78)%nat ->
  ew E (A_OBJ i) = w64 (nth i seg_objs 0).
Proof.
intros E i HE Hi. rewrite (img_env_atomP E (A_OBJ i) HE) by (unfold A_OBJ, A_TEXT, A_LIM in *; lia).
rewrite (OBJ i ltac:(unfold seg_objs; cbn [length]; lia)). reflexivity.
Qed.
Lemma a3_sbase : nth 34 seg_objs 0 = seg_litA_rc S_base.
Proof. vm_compute. reflexivity. Qed.
Lemma a3_fs : nth 35 seg_objs 0 = seg_litA_rc F_s.
Proof. vm_compute. reflexivity. Qed.

(* ======================= 1. the blocks and the frame at an allocator state ======================= *)
(* s5 = a0 = c + 0x4080 at the call: the sum of two register atoms *)
Lemma a3_denot_add : forall (E : env) (m n : nat) (a b : Z),
  bv_unsigned (ew E m) = a -> bv_unsigned (ew E n) = b -> 0 <= a + b < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff m 0) (SOff n 0)) = w64 (a + b).
Proof.
intros E m n a b Ha Hb Hab.
pose proof (bv_unsigned_in_range 64 (ew E m)) as Rm. pose proof (bv_unsigned_in_range 64 (ew E n)) as Rn.
rewrite Ha in Rm. rewrite Hb in Rn. change (bv_modulus 64) with (2 ^ 64) in Rm, Rn.
unfold w64. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SOff m 0) (SOff n 0)))). f_equal.
change (U E (SAlu ALU_ADD (SOff m 0) (SOff n 0)) = a + b).
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Ha, Hb, !Z.add_0_r.
rewrite (zcanon_small a) by lia. rewrite (zcanon_small b) by lia. apply zcanon_small. lia.
Qed.
(* the end of a C string's 8-byte read span (seg_spec.cstr_span) is the first 8-aligned address after its NUL *)
Lemma a3_span_end : forall (w : Z) (s : list Z),
  w + seg_spec.cstr_span w s = (w + Z.of_nat (length s)) - (w + Z.of_nat (length s)) mod 8 + 8.
Proof.
intros w s. unfold seg_spec.cstr_span.
pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8 ltac:(lia)) as M1.
pose proof (Z.mod_pos_bound (- (w + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as M2.
pose proof (Z.div_mod (w + Z.of_nat (length s)) 8 ltac:(lia)) as D1.
pose proof (Z.div_mod (- (w + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as D2.
lia.
Qed.
Lemma a3_span_le : forall (w A : Z) (s : list Z), w + Z.of_nat (length s) + 1 <= A -> A mod 4096 = 0 ->
  w + seg_spec.cstr_span w s <= A.
Proof.
intros w A s H HA. rewrite a3_span_end.
pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (w + Z.of_nat (length s)) 8 ltac:(lia)) as D1.
pose proof (Z.div_mod A 4096 ltac:(lia)) as DA. rewrite HA in DA.
lia.
Qed.
Lemma a3_block_low : forall ly S (W : world SEGS) mem md (q n : Z),
  AR SEGS B ly S W mem md -> sa_heap B ly S q n -> 0 <= n -> 4096 <= q /\ q + n <= alloc_ceiling.
Proof.
intros ly S W mem md q n HAR (b & m & Hin & Hb & Hq) Hn.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq]. split; lia.
Qed.
Lemma a3_app_ceil : forall lo len, in_app lo len -> lo + len <= alloc_ceiling.
Proof.
intros lo len (_ & HA). pose proof asan_consts as (C1 & _).
unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. destruct HA as [Hl | (_ & Hh)]; lia.
Qed.
(* the label's 8-byte read span is in application memory, in each of the three places it may lie *)
Lemma a3_lab_amem : forall ly S (W : world SEGS) mem md (lp : Z) (l : list Z),
  AR SEGS B ly S W mem md ->
  (sa_heap B ly S lp (Z.of_nat (length l) + 1) \/ sa_fframe ly S lp (Z.of_nat (length l) + 1)
     \/ sa_img SEGS B lp (Z.of_nat (length l) + 1)) ->
  (length l <= 65535)%nat ->
  amem_range lp (Z.of_nat (length l) + 8).
Proof.
intros ly S W mem md lp l HAR Hw Hl.
apply Nat2Z.inj_le in Hl. assert (E : Z.of_nat 65535 = 65535) by (vm_compute; reflexivity). rewrite E in Hl.
destruct Hw as [(b & m & Hin & Hb & Hbm) | [(cid & pos & Hin & Hcid & Hf1 & Hf2) | Hi]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & _ & _ & Happ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
  apply (a3_amem_slack b (req_size m)); [exact Happ | lia | lia | lia].
- destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & Happ & _).
  apply (a3_amem_slack (frame_addr ly cid pos) (fs_frame_bytes cid)); [exact Happ | lia | lia | lia].
- destruct (Hi lp ltac:(lia)) as (Himg & _). pose proof (pa_img_range _ Himg) as Hr.
  unfold amem_range, kImgEnd, kLowMemEnd in *. left. lia.
Qed.
(* the same three places put the label's bytes and NUL below the allocator's ceiling *)
Lemma a3_lab_ceil : forall ly S (W : world SEGS) mem md (lp : Z) (l : list Z),
  AR SEGS B ly S W mem md ->
  (sa_heap B ly S lp (Z.of_nat (length l) + 1) \/ sa_fframe ly S lp (Z.of_nat (length l) + 1)
     \/ sa_img SEGS B lp (Z.of_nat (length l) + 1)) ->
  (length l <= 65535)%nat ->
  lp + Z.of_nat (length l) + 1 <= alloc_ceiling.
Proof.
intros ly S W mem md lp l HAR Hw Hl.
apply Nat2Z.inj_le in Hl. assert (E : Z.of_nat 65535 = 65535) by (vm_compute; reflexivity). rewrite E in Hl.
pose proof asan_consts as (C1 & _).
destruct Hw as [(b & m & Hin & Hb & Hbm) | [(cid & pos & Hin & Hcid & Hf1 & Hf2) | Hi]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & _ & Hceil & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hreq]. lia.
- destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & Happ & _).
  pose proof (a3_app_ceil _ _ Happ). lia.
- destruct (Hi lp ltac:(lia)) as (Himg & _). pose proof (pa_img_range _ Himg) as Hr.
  unfold kImgEnd in Hr. lia.
Qed.

(* ---- what a call that writes no image byte keeps of the caller's pinned objects, read-only view and
   stack-protector cells: all their bytes lie in [0x10000, kImgEnd) (the image-keep half of pf_a5_k.v's
   a5_keep_lit / a5_keep_cat / a5_keep_rod0 / a5_keep_ssp, restated over a reader that agrees there) ---- *)
Section ki.
Variables (rd : reader) (W' : world SEGS) (mem' : word -> option byte).
Hypothesis HKI : forall a, 0x10000 <= a < kImgEnd -> rdW W' mem' a = rd a.
Lemma a3_keep_lit : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B (rdW W' mem') a s.
Proof.
intros a s (Ha & ((Hz & Hn) & _) & Hp & Hr & Hi).
split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS _ _ _ Hr)].
intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
destruct (Hi (a + Z.of_nat i) ltac:(lia)) as (Himg & _ & _).
rewrite HKI; [exact (Hz i Hi') | exact (pa_img_range _ Himg)].
Qed.
Lemma a3_keep_cat : sa_cat SEGS B rd catA -> sa_cat SEGS B (rdW W' mem') catA.
Proof.
intros (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (a3_keep_lit tp _ Hl)].
rewrite (rdword_ext rd); [exact Htp|].
intros k Hk. assert (Hn' : Z.of_nat i < 11) by (unfold pin_spec.CAT_N in Hn; lia).
apply HKI. apply pa_img_range. refine (proj1 (Hi (pin_spec.row_addr catA i + k) _)).
unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.
Lemma a3_keep_rod : arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B (rdW W' mem').
Proof.
intros HR a Hro Ho He.
assert (Hlow : 0x10000 <= a < kImgEnd).
{ destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
  - apply pa_img_range. exists sg. split; [exact Hsg | exact Hr].
  - unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. unfold kImgEnd. lia. }
rewrite HKI by exact Hlow. exact (HR a Hro Ho He).
Qed.
Lemma a3_keep_ssp : sa_ssp rd gotwA guardA -> sa_ssp (rdW W' mem') gotwA guardA.
Proof.
intros (S1 & g & S2).
assert (KW : forall a, 0x10000 <= a -> a + 8 <= kImgEnd -> rdword (rdW W' mem') a = rdword rd a).
{ intros a H1 H2. apply rdword_ext. intros k Hk. apply HKI. lia. }
split; [rewrite KW; [exact S1 | unfold gotwA; lia | unfold gotwA, kImgEnd; lia]|].
exists g. rewrite KW; [exact S2 | unfold guardA; lia | unfold guardA, kImgEnd; lia].
Qed.
End ki.

Lemma a3E_reg : forall v rX (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (a3wE v rX) k = getr rX r.
Proof.
intros v rX k r Hk. pose proof (bv_unsigned_in_range 5 r) as H5. change (bv_modulus 5) with 32 in H5.
unfold a3wE. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk.
Qed.
(* ======================= 2. the walk ======================= *)
Lemma a3_rg' : forall (rX : bvmap 5 word) L (r z : Z) (b : bv 5),
  pf_rg rX L -> In (r, z) L -> Z_to_bv 5 r = b -> getr rX b = w64 z.
Proof. intros rX L r z b H Hin <-. exact (pf_a5_k.a5_rg_get rX L r z H Hin). Qed.

Section s.
Context {fx : YK11.FPState}.

(* the pointer the code passes in a3; the TEXT a3_LT is pf_a3_d's *)
Definition a3_LP (v : pfv) : Z := match p_lab v with Some _ => p_lp v | None => seg_litA_rc S_base end.

(* a segment proved at the FP state a call returned is the segment at the entry's *)
Lemma a3_post_lift : forall (fx1 : YK11.FPState) (W0 : world SEGS) (cfg : config) (v : pfv),
  PaFx.fxrel fx fx1 ->
  SRr SEGS W0 cfg (PF_POST (fx := fx1) B v) -> SRr SEGS W0 cfg (PF_POST (fx := fx) B v).
Proof. intros fx1 W0 cfg v H HS. unfold PF_POST in *. eapply srr_apost_baseF_lift; eassumption. Qed.
Lemma a3_postr_lift : forall (fx1 : YK11.FPState) (W0 : world SEGS) (cfg : config) (v : pfv) (cf : rconf),
  PaFx.fxrel fx fx1 ->
  SRr SEGS W0 cfg (PF_POSTr (fx := fx1) B v cf) -> SRr SEGS W0 cfg (PF_POSTr (fx := fx) B v cf).
Proof. intros fx1 W0 cfg v cf H HS. unfold PF_POSTr in *. eapply srr_apost_baseF_lift; eassumption. Qed.

(* the registers at the snprintf call (0x87ce8): its arguments a0..a3, and every callee-saved register the cut
   a3_ret1 names (s5 = &c->reading, set at 0x87cc4) *)
Definition a3_CRG (v : pfv) (pos : Z) : list (Z * Z) :=
  [(10, p_c v + seg_spec.RC_READING); (11, 96); (12, seg_litA_rc F_s); (13, a3_LP v);
   (2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (22, SHADOW_OFF);
   (23, pf_F v pos); (24, p_c v); (25, p_t v); (26, p_c v + seg_spec.RC_GEN);
   (27, pf_SH v pos); (21, p_c v + seg_spec.RC_READING)].

(* the label the snprintf reads, at FRAME: the caller's (reac_segconf_parse_file_pre's Some arm, pf_lab's
   place) or the image literal "reac-pw.conf" (0x21360, 12 bytes) *)
Lemma a3_lab_facts : forall v pos Sc (Wc : world SEGS) rX memc mdc,
  INV_FRAME (fx := fx) B v pos (p_ly v) Sc Wc rX memc mdc ->
  sa_str (rdW Wc memc) (a3_LP v) (a3_LT v) /\
  sa_addr (rdW Wc memc) (a3_LP v) (Z.of_nat (length (a3_LT v)) + 1) /\
  (length (a3_LT v) <= 65535)%nat /\ 0 < a3_LP v /\
  amem_range (a3_LP v) (Z.of_nat (length (a3_LT v)) + 8) /\
  a3_LP v + seg_spec.cstr_span (a3_LP v) (a3_LT v) <= alloc_ceiling /\
  sa_disj (a3_LP v) (seg_spec.cstr_span (a3_LP v) (a3_LT v)) (p_c v + seg_spec.RC_READING) 96.
Proof.
intros v pos Sc Wc rX memc mdc HINV.
a3_k.
pose proof asan_consts as (C1 & _).
pose proof alloc_ceiling_value as (_ & HAC4).
pose proof HINV as (HCX & HFI & HOBJ & HLAB & _).
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & HRP) & _).
pose proof (proj1 (proj1 HFI)) as HARc.
pose proof HOBJ as (_ & _ & _ & _ & Hhc & _ & HLITS & _).
pose proof HLAB as (HOSTR & HLOC).
assert (HLIT_S : sa_lit SEGS B (rdW Wc memc) (seg_litA_rc S_base) S_base)
  by (apply HLITS; unfold PARSE_FILE_LITS; apply in_or_app; left; cbn [In]; tauto).
pose proof HRP as (_ & _ & HM).
unfold a3_LP, a3_LT.
destruct (p_lab v) as [l|] eqn:Elab.
- cbn [sa_ostr] in HOSTR. destruct HOSTR as (Hne & Hstr).
  destruct HLOC as (Hwhere & Haddr). destruct HM as (Hlen & _ & _ & Hdj).
  pose proof Haddr as (Hlp0 & _).
  split; [exact Hstr|]. split; [exact Haddr|]. split; [exact Hlen|]. split; [lia|].
  split; [exact (a3_lab_amem _ _ _ _ _ (p_lp v) l HARc Hwhere Hlen)|].
  split; [apply a3_span_le; [exact (a3_lab_ceil _ _ _ _ _ (p_lp v) l HARc Hwhere Hlen) | exact HAC4]|].
  exact Hdj.
- destruct HLIT_S as (Hpos & Hstr & Hpin & _).
  pose proof Hhc as (bc & mc & Hbin & Hbc & Hcm).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HARc Hbin) as (_ & Hb4096 & _ & _ & _ & _ & Hmc).
  pose proof (req_size_pos mc ltac:(lia)) as [_ Hreq].
  assert (Hoff : off_img bc (req_size mc)) by (eapply blk_off_imgP; [exact HARc | exact Hbin]).
  unfold off_img in Hoff.
  assert (EL : seg_litA_rc S_base = 0x21360) by (vm_compute; reflexivity).
  assert (EN : Z.of_nat (length S_base) = 12) by (vm_compute; reflexivity).
  assert (ES : seg_spec.cstr_span (seg_litA_rc S_base) S_base = 16) by (vm_compute; reflexivity).
  split; [exact Hstr|]. split; [exact (Hpin _ _ _ _ _ HARc)|].
  split; [apply Nat.leb_le; vm_compute; reflexivity|]. split; [exact Hpos|].
  rewrite ES, EN, EL.
  split; [unfold amem_range, kLowMemEnd; left; lia|]. split; [lia|].
  unfold sa_disj. lia.
Qed.

(* THE CALL at 0x87ce8 and the cut a3_ret1 at its return 0x87cec. The run from FRAME wrote nothing (memc) and
   left the registers a3_CRG; snprintf writes c->reading (at most 96 bytes) and its own stack window
   [s1 - 8192, s1), and keeps every other byte (a3_snp_site): every object a3_ret1 names lies outside both. *)
Lemma a3_at_call : forall v pos Sc (Wc : world SEGS) (rX regsT : bvmap 5 word) memc mdc mdT,
  INV_FRAME (fx := fx) B v pos (p_ly v) Sc Wc rX memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] (p_ly v) Sc Wc memc mdT 0 ->
  getr regsT 1 = Z_to_bv 64 (BASE + PF_RET1) ->
  pf_rg regsT (a3_CRG v pos) ->
  (forall (Sc' : astate) (Wc' : world SEGS) (rX' : bvmap 5 word) memc' mdc' (fx1 : YK11.FPState),
     PaFx.fxrel fx fx1 -> a3_ret1 (fx := fx1) B v pos Sc' Wc' rX' memc' mdc' ->
     SRr SEGS Wc' (mkCfg (@mkst fx1 rX' (Z_to_bv 64 (BASE + PF_RET1)) memc' (seg_rom SEGS)) mdc')
       (PF_POST (fx := fx) B v)) ->
  SRr SEGS Wc (mkCfg (@mkst fx regsT (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_snprintf)) memc (seg_rom SEGS))
    mdT) (PF_POST (fx := fx) B v).
Proof.
intros v pos Sc Wc rX regsT memc mdc mdT HINV HJT RA HRGT HAFTER.
a3_k.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as HAC.
pose proof STK_values as (_ & SREF & _ & SPF & _).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (a3_lab_facts v pos Sc Wc rX memc mdc HINV) as (HLs & HLa & HLlen & HLpos & HLam & HLce & HLdj).
pose proof HINV as (HCX & HFI & HOBJ & HLAB & HRC & HSL & HFSH & HRG).
pose proof HCX as (HPRE & HROD & E10 & Hc64 & E11 & Ht64 & E12 & Hlp64 & (fe & HRP) & HROOM & HEV).
pose proof HRP as (HRDR & _).
pose proof HRDR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDJt & _).
clear HRDR HRP fe.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFI as (HJ & _ & (fS & HSc) & HPerm & HSV & HFL & HFRM & HRGf).
pose proof HOBJ as (Hst & Hat & Hht & Hac & Hhc & HCAT & HLITS & HROD1 & HSSP).
pose proof (proj1 HJ) as HARc.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
change (spZ (p_regs v)) with (pf_sp0 v) in *.
rewrite SPF in Hslo.
assert (Hfin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 5 pos HARc Hfin) as (HFal & HFapp & _ & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 5 pos HARc Hfin) as (HF4096 & HFceil & _).
change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in *.
change (fs_frame_bytes 5) with 2048 in *.
(* the block c *)
pose proof Hhc as (bc & mc & Hbin & Hbc & Hcm).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HARc Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hmc).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hreq].
pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc bc mc 5 pos HARc Hbin Hfin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hsep. change (fs_frame_bytes 5) with 2048 in Hsep.
assert (Hoffb : off_img bc (req_size mc)) by (eapply blk_off_imgP; [exact HARc | exact Hbin]).
unfold off_img in Hoffb.
assert (Hoffc : off_img (p_c v) seg_spec.SEG_C_SIZE) by (unfold off_img; lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
destruct (a3_block_low (p_ly v) Sc Wc memc mdc (p_t v) (pf_len v) HARc Hht ltac:(unfold pf_len; lia))
  as [Ht4096 Htceil].
(* the geometry of the call: sp = s1, o = s1 - sp0 *)
assert (HSP : alloc_ceiling + 12800 <= pf_sp0 v <= 2 ^ 47) by lia.
assert (Hs1e : pf_s1 v = pf_sp0 v - 0x140 - (pf_sp0 v - 0x140) mod 32) by reflexivity.
assert (M16 : (pf_sp0 v - 0x140) mod 32 = 0 \/ (pf_sp0 v - 0x140) mod 32 = 16).
{ pose proof (Z.mod_pos_bound (pf_sp0 v - 0x140) 32 ltac:(lia)).
  assert (E16 : (pf_sp0 v - 0x140) mod 16 = 0).
  { replace (pf_sp0 v - 0x140) with (pf_sp0 v + (-20) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
  pose proof (Z.div_mod (pf_sp0 v - 0x140) 32 ltac:(lia)) as D32.
  pose proof (Z.div_mod (pf_sp0 v - 0x140) 16 ltac:(lia)) as D16. lia. }
assert (HS1 : pf_sp0 v - 352 <= pf_s1 v <= pf_sp0 v - 320) by lia.
assert (Ho16 : (pf_s1 v - pf_sp0 v) mod 16 = 0).
{ destruct M16 as [E | E];
    [replace (pf_s1 v - pf_sp0 v) with (-320) by lia | replace (pf_s1 v - pf_sp0 v) with (-336) by lia];
    reflexivity. }
(* the registers at the call *)
assert (G : forall (r : Z) (b : bv 5) z, In (r, z) (a3_CRG v pos) -> Z_to_bv 5 r = b -> getr regsT b = w64 z)
  by (intros r b z Hin Hb; exact (a3_rg' regsT _ r z b HRGT Hin Hb)).
assert (G10 : getr regsT 10 = w64 (p_c v + seg_spec.RC_READING))
  by (apply (G 10); [unfold a3_CRG; cbn [In]; tauto | apply bv_eq; reflexivity]).
assert (G11 : getr regsT 11 = w64 96) by (apply (G 11); [unfold a3_CRG; cbn [In]; tauto | apply bv_eq; reflexivity]).
assert (G12 : getr regsT 12 = w64 (seg_litA_rc F_s))
  by (apply (G 12); [unfold a3_CRG; cbn [In]; tauto | apply bv_eq; reflexivity]).
assert (G13 : getr regsT 13 = w64 (a3_LP v))
  by (apply (G 13); [unfold a3_CRG; cbn [In]; tauto | apply bv_eq; reflexivity]).
assert (G3 : getr regsT 3 = w64 (as_gp B))
  by (apply (G 3); [unfold a3_CRG; cbn [In]; tauto | apply bv_eq; reflexivity]).
assert (G4 : getr regsT 4 = w64 (as_tp B))
  by (apply (G 4); [unfold a3_CRG; cbn [In]; tauto | apply bv_eq; reflexivity]).
assert (G2 : getr regsT 2 = w64 (pf_s1 v))
  by (apply (G 2); [unfold a3_CRG; cbn [In]; tauto | apply bv_eq; reflexivity]).
assert (Hsp : spZ regsT = pf_sp0 v + (pf_s1 v - pf_sp0 v)).
{ unfold spZ. rewrite G2. rewrite pf_a6_k.a6_w64_u by lia. lia. }
assert (RAok : YK0s.ret_ok (Z_to_bv 64 (BASE + PF_RET1))).
{ apply ret_ok_codeptr_v; unfold PF_RET1, PF_FRAME, AF_reac_segconf_parse_file; [lia | reflexivity]. }
assert (HLITF : sa_lit SEGS B (rdW Wc memc) (seg_litA_rc F_s) F_s)
  by (apply HLITS; unfold PARSE_FILE_LITS; apply in_or_app; left; cbn [In]; tauto).
(* ---- 0x87ce8 jal snprintf(&c->reading, 96, "%s", L) ---- *)
eapply SRr_bind.
{ exact (a3_snp_site (fx := fx) B SNP Wc regsT memc (pf_sp0 v) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v)
    (p_ly v) Sc mdT 0 (p_c v) (a3_LP v) (a3_LT v) pos (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + PF_RET1))
    (SIGMA SS___interceptor_trampoline_snprintf) HJT G10 G11 G12 G13 G3 G4 RA RAok Hsp Ho16 ltac:(lia)
    ltac:(rewrite SPF, Hes; lia) ltac:(rewrite Hes; lia) Hhc Hac ltac:(lia) ltac:(lia) Hoffc
    HLs HLa HLlen HLpos HLam HLce HLdj HLITF HSSP HROD1 HFRM eq_refl). }
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HP & Hby & Hkeep).
apply (HAFTER Sc Wc regs2 mem2 md2 fx1 Hfx).
pose proof (proj1 HJ2) as HAR2.
pose proof (a3_Tw_len (a3_LT v)) as HTw.
(* the call's keep clause, its two written ranges widened to [s1 - 8192, s1) and c->reading's 96 bytes *)
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 8192 <= a < pf_s1 v) ->
  ~ (p_c v + seg_spec.RC_READING <= a < p_c v + seg_spec.RC_READING + 96) -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha Hn1 Hn2. apply Hkeep; [exact Ha | rewrite Hes; lia | lia]. }
assert (HKI : forall a, 0x10000 <= a < kImgEnd -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha. unfold kImgEnd in Ha. apply HK; lia. }
unfold a3_ret1.
split; [exact HCX|]. split; [exact HJ2|]. split; [exists fS; exact HSc|]. split; [exact HPerm|].
(* the saved registers at sp0 - 8 - 8 j: above s1 *)
split.
{ intros j r Hj.
  assert (Hj13 : (j < 13)%nat)
    by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
  rewrite (rdword_ext (rdW Wc memc)); [exact (HSV j r Hj)|]. intros k Hk. apply HK; lia. }
(* the flag word at F + 2040: in the class-5 frame, apart from c's block *)
split.
{ change (fs_frame_bytes 5) with 2048.
  rewrite (rdword_ext (rdW Wc memc)); [exact HFL|]. intros k Hk. apply HK; lia. }
split; [exact (PaFx.fxrel_frm0 fx fx1 HFRM Hfx)|].
(* the callee-saved registers, s5 = &c->reading among them *)
split.
{ apply (pf_a5_k.a5_rg_pres regsT regs2 _ HP).
  - repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
  - apply (pf_a5_k.a5_rg_incl regsT (a3_CRG v pos)); [|exact HRGT].
    intros x Hx. unfold a3_CRG. cbn [In] in Hx |- *. tauto. }
(* the objects: the text's bytes and the image bytes kept, c's and t's addressability from the new AR *)
split.
{ unfold sa_disj in HDJt.
  pose proof (a3_span_end (p_t v) (p_s v)) as Esp.
  pose proof (Z.mod_pos_bound (p_t v + Z.of_nat (length (p_s v))) 8 ltac:(lia)) as Me.
  assert (Htl : p_t v + Z.of_nat (length (p_s v)) + 1 <= alloc_ceiling) by (unfold pf_len in Htceil; lia).
  split.
  { destruct Hst as ((Hz & Hn) & Htl8). split; [split; [|exact Hn]|].
    - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
      rewrite HK; [exact (Hz i Hi) | lia | lia | lia].
    - intros x Hx. rewrite HK; [exact (Htl8 x Hx) | lia | lia | lia]. }
  split; [exact (pf_a6_k.a6_heap_addr B (p_ly v) Sc Wc mem2 md2 (p_t v) (pf_len v) HAR2 Hht ltac:(unfold pf_len; lia))|].
  split; [exact Hht|].
  split; [exact (pf_a6_k.a6_heap_addr B (p_ly v) Sc Wc mem2 md2 (p_c v) seg_spec.SEG_C_SIZE HAR2 Hhc ltac:(lia))|].
  split; [exact Hhc|].
  split; [exact (a3_keep_cat (rdW Wc memc) Wc mem2 HKI HCAT)|].
  split; [intros x Hx; exact (a3_keep_lit (rdW Wc memc) Wc mem2 HKI _ _ (HLITS x Hx))|].
  split; [exact (a3_keep_rod (rdW Wc memc) Wc mem2 HKI HROD1) | exact (a3_keep_ssp (rdW Wc memc) Wc mem2 HKI HSSP)]. }
(* c's record: the reading field holds snprintf's text, every other byte of c is kept *)
split.
{ unfold a3_rd1.
  assert (HLnz : ~ In 0 (a3_LT v)) by (destruct HLs as ((_ & Hn) & _); exact Hn).
  pose proof (pf_a8b_t.pfa8b_bytes_range_aview SEGS (w_H Wc) memc (a3_LP v) (a3_LT v) HLs) as HLr.
  assert (HTin : forall x, In x (a3_Tw (a3_LT v)) -> In x (a3_LT v)).
  { intros x Hx. unfold a3_Tw in Hx. rewrite <- (firstn_skipn 95 (a3_LT v)). apply in_or_app. left. exact Hx. }
  apply (a3f_rconf_reading (rdW Wc memc) (rdW Wc mem2) (p_c v) (p_rcs v) (a3_Tw (a3_LT v)) HRC).
  - lia.
  - intros Hz0. exact (HLnz (HTin 0 Hz0)).
  - rewrite Forall_forall in HLr |- *. intros x Hx. pose proof (HLr x (HTin x Hx)). lia.
  - exact Hby.
  - intros a Ha Hd. apply Hkeep; [lia | rewrite Hes; lia | exact Hd]. }
(* the two slots 0x88 and 0x98: above s1 *)
split.
{ assert (KS : forall off, 0 <= off <= 0xb8 ->
    rdword (rdW Wc mem2) (pf_s1 v + off) = rdword (rdW Wc memc) (pf_s1 v + off)).
  { intros off Hoff. apply rdword_ext. intros k Hk. apply HK; lia. }
  unfold pf_sl in HSL |- *.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
  - rewrite KS by lia. exact (Forall_inv HSL).
  - rewrite KS by lia. exact (Forall_inv (Forall_inv_tail HSL)). }
(* the frame's 144 shadow cells: in the shadow band, below the stack, apart from c's block *)
{ assert (HSH : pf_SH v pos = SHADOW_OFF + pf_F v pos / 8) by reflexivity.
  assert (HF8 : 0 <= pf_F v pos / 8) by (apply Z.div_pos; lia).
  assert (HF8h : pf_F v pos / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  assert (HAC8 : alloc_ceiling / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  change (0x7fffff800000 / 8) with 0xffffff00000 in HAC8.
  unfold SHADOW_OFF in HSH.
  intros i Hi. rewrite HK; [exact (HFSH i Hi) | lia | lia | lia]. }
Qed.

(* the 16 registers of a3_CRG at the call, from the run's symbolic state HS and the atom facts D10 .. A27; the
   label's a3 is left to the branch *)
Local Ltac a3_crg HS D10 O35 A2 A3 A4 A8 A9 A22 A23 A24 A25 A26 A27 :=
  unfold pf_rg, a3_CRG; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  [ let Q := fresh "Q" in a3_raw HS 10 Q; rewrite Q; exact D10
  | let Q := fresh "Q" in prreg HS (Z_to_bv 5 11) Q; exact Q
  | let Q := fresh "Q" in prreg HS (Z_to_bv 5 12) Q; rewrite Q; exact O35
  | idtac
  | let Q := fresh "Q" in prreg HS (Z_to_bv 5 2) Q; rewrite Q; exact A2
  | let Q := fresh "Q" in prreg HS (Z_to_bv 5 3) Q; rewrite Q; exact A3
  | let Q := fresh "Q" in prreg HS (Z_to_bv 5 4) Q; rewrite Q; exact A4
  | let Q := fresh "Q" in prreg HS (Z_to_bv 5 8) Q; rewrite Q; exact A8
  | let Q := fresh "Q" in prreg HS (Z_to_bv 5 9) Q; rewrite Q; exact A9
  | let Q := fresh "Q" in prreg HS (Z_to_bv 5 22) Q; rewrite Q; exact A22
  | let Q := fresh "Q" in prreg HS (Z_to_bv 5 23) Q; rewrite Q; exact A23
  | let Q := fresh "Q" in prreg HS (Z_to_bv 5 24) Q; rewrite Q; exact A24
  | let Q := fresh "Q" in prreg HS (Z_to_bv 5 25) Q; rewrite Q; exact A25
  | let Q := fresh "Q" in prreg HS (Z_to_bv 5 26) Q; rewrite Q; exact A26
  | let Q := fresh "Q" in prreg HS (Z_to_bv 5 27) Q; rewrite Q; exact A27
  | let Q := fresh "Q" in a3_raw HS 21 Q; rewrite Q; exact D10 ].

Lemma a3_main : (forall fx0 : YK11.FPState, A3_RET1_stmt (fx := fx0) B) ->
  (forall n, HA_HEAD B n) -> HA_DONE B -> H_FRAME (fx := fx) B.
Proof.
intros RET1 HEADS HDONE v pos lyc Sc Wc rX memc mdc HINV.
a3_k.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as HAC.
pose proof STK_values as (_ & SREF & _ & SPF & _).
pose proof HINV as (HCX & HFI & HOBJ & HLAB & HRC & HSL & HFSH & HRG).
pose proof HCX as (HPRE & HROD & E10 & Hc64 & E11 & Ht64 & E12 & Hlp64 & (fe & HRP) & HROOM & HEV).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFI as (HJ & Hly & (fS & HSc) & HPerm & HSV & HFL & HFRM & HRGf).
pose proof HOBJ as (Hst & Hat & Hht & Hac & Hhc & HCAT & HLITS & HROD1 & HSSP).
pose proof (proj1 HJ) as HARc.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
subst lyc.
change (spZ (p_regs v)) with (pf_sp0 v) in *.
rewrite SPF in Hslo.
assert (Hfin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 5 pos HARc Hfin) as (HFal & HFhi & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 5 pos HARc Hfin) as (HF4096 & HFceil & HFapp).
change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in *.
change (fs_frame_bytes 5) with 2048 in *. change (2048 / 8) with 256 in HFSpres.
destruct (a3_block_low (p_ly v) Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HARc Hhc ltac:(lia))
  as [Hc4096 Hcceil].
destruct (a3_block_low (p_ly v) Sc Wc memc mdc (p_t v) (pf_len v) HARc Hht ltac:(unfold pf_len; lia))
  as [Ht4096 Htceil].
(* the registers at FRAME *)
assert (R2 : getr rX (Z_to_bv 5 2) = w64 (pf_s1 v)) by (apply (pf_a5_k.a5_rg_get rX _ 2 _ HRGf); cbn [In]; tauto).
assert (R3 : getr rX (Z_to_bv 5 3) = w64 (as_gp B)) by (apply (pf_a5_k.a5_rg_get rX _ 3 _ HRGf); cbn [In]; tauto).
assert (R4 : getr rX (Z_to_bv 5 4) = w64 (as_tp B)) by (apply (pf_a5_k.a5_rg_get rX _ 4 _ HRGf); cbn [In]; tauto).
assert (R8 : getr rX (Z_to_bv 5 8) = w64 (pf_sp0 v)) by (apply (pf_a5_k.a5_rg_get rX _ 8 _ HRGf); cbn [In]; tauto).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (pf_a5_k.a5_rg_get rX _ 9 _ HRGf); cbn [In]; tauto).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF)
  by (apply (pf_a5_k.a5_rg_get rX _ 22 _ HRGf); cbn [In]; tauto).
assert (R27 : getr rX (Z_to_bv 5 27) = w64 (pf_SH v pos))
  by (apply (pf_a5_k.a5_rg_get rX _ 27 _ HRG); cbn [In]; tauto).
assert (R10 : getr rX (Z_to_bv 5 10) = w64 0x4080) by (apply (pf_a5_k.a5_rg_get rX _ 10 _ HRG); cbn [In]; tauto).
assert (R23 : getr rX (Z_to_bv 5 23) = w64 (pf_F v pos))
  by (apply (pf_a5_k.a5_rg_get rX _ 23 _ HRG); cbn [In]; tauto).
assert (R24 : getr rX (Z_to_bv 5 24) = w64 (p_c v)) by (apply (pf_a5_k.a5_rg_get rX _ 24 _ HRG); cbn [In]; tauto).
assert (R25 : getr rX (Z_to_bv 5 25) = w64 (p_t v)) by (apply (pf_a5_k.a5_rg_get rX _ 25 _ HRG); cbn [In]; tauto).
assert (R19 : getr rX (Z_to_bv 5 19) = w64 (p_lp v)) by (apply (pf_a5_k.a5_rg_get rX _ 19 _ HRG); cbn [In]; tauto).
assert (R26 : getr rX (Z_to_bv 5 26) = w64 (p_c v + seg_spec.RC_GEN))
  by (apply (pf_a5_k.a5_rg_get rX _ 26 _ HRG); cbn [In]; tauto).
(* the geometry of the cut *)
assert (HSP : alloc_ceiling + 12800 <= pf_sp0 v <= 2 ^ 47) by lia.
assert (Hs1m : 0 <= (pf_sp0 v - 0x140) mod 32 < 32) by (apply Z.mod_pos_bound; reflexivity).
assert (Hs1e : pf_s1 v = pf_sp0 v - 0x140 - (pf_sp0 v - 0x140) mod 32) by reflexivity.
assert (HS1 : pf_sp0 v - 352 <= pf_s1 v <= pf_sp0 v - 320) by lia.
assert (HSH : pf_SH v pos = SHADOW_OFF + pf_F v pos / 8) by reflexivity.
assert (HF0 : 0 <= pf_F v pos) by lia.
assert (HFc : pf_F v pos <= alloc_ceiling) by lia.
assert (HF8 : 0 <= pf_F v pos / 8) by (apply Z.div_pos; [exact HF0 | reflexivity]).
assert (HF8h : pf_F v pos / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; [reflexivity | exact HFc]).
assert (HACle : alloc_ceiling <= 0x7fffff800000) by lia.
assert (HAC8 : alloc_ceiling / 8 <= 0x7fffff800000 / 8)
  by (apply Z.div_le_mono; [reflexivity | exact HACle]).
change (0x7fffff800000 / 8) with 0xffffff00000 in HAC8.
(* ---- the label the snprintf reads: its text, its pointer, its facts at the cut ---- *)
pose proof HLAB as (HOSTR & HLOC).
assert (HLIT_S : sa_lit SEGS B (rdW Wc memc) (seg_litA_rc S_base) S_base)
  by (apply HLITS; unfold PARSE_FILE_LITS; apply in_or_app; left; cbn [In]; tauto).
assert (HLIT_F : sa_lit SEGS B (rdW Wc memc) (seg_litA_rc F_s) F_s)
  by (apply HLITS; unfold PARSE_FILE_LITS; apply in_or_app; left; cbn [In]; tauto).
assert (HLTSTR : sa_str (rdW Wc memc) (a3_LP v) (a3_LT v) /\
                 sa_addr (rdW Wc memc) (a3_LP v) (Z.of_nat (length (a3_LT v)) + 1) /\
                 (length (a3_LT v) <= 65535)%nat /\ 0 < a3_LP v).
{ unfold a3_LP, a3_LT. pose proof HRP as (_ & _ & HM).
  destruct (p_lab v) as [l|] eqn:Elab.
  - cbn [sa_ostr] in HOSTR. destruct HOSTR as (Hne & Hstr).
    destruct HLOC as (_ & Haddr). destruct HM as (Hlen & _).
    split; [exact Hstr|]. split; [exact Haddr|]. split; [exact Hlen | lia].
  - destruct HLIT_S as (Hpos & Hstr & Hpin & _).
    split; [exact Hstr|]. split; [exact (Hpin _ _ _ _ _ HARc)|].
    split; [apply Nat.leb_le; vm_compute; reflexivity | exact Hpos]. }
destruct HLTSTR as (HLs & HLa & HLlen & HLpos).
clear HRP fe.
(* ---- the seed at FRAME, and the run to the snprintf call ---- *)
assert (HEI : img_env VAL A_LIM (a3wE v rX)) by apply a3wE_img.
assert (U24 : bv_unsigned (ew (a3wE v rX) 24%nat) = p_c v).
{ rewrite (a3E_reg v rX 24 (Z_to_bv 5 24) ltac:(vm_compute; reflexivity)), R24. apply pf_a6_k.a6_w64_u. lia. }
assert (U25 : bv_unsigned (ew (a3wE v rX) 25%nat) = p_t v).
{ rewrite (a3E_reg v rX 25 (Z_to_bv 5 25) ltac:(vm_compute; reflexivity)), R25. apply pf_a6_k.a6_w64_u. lia. }
assert (U19 : bv_unsigned (ew (a3wE v rX) 19%nat) = p_lp v).
{ rewrite (a3E_reg v rX 19 (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), R19. apply pf_a6_k.a6_w64_u. lia. }
(* the registers at FRAME as the seed's atoms; s5 = a0 = 0x4080 + c (0x87cc4 `add s5, s8, a0`) *)
assert (A2 : ew (a3wE v rX) 2%nat = w64 (pf_s1 v))
  by (rewrite (a3E_reg v rX 2 (Z_to_bv 5 2) ltac:(vm_compute; reflexivity)); exact R2).
assert (A3 : ew (a3wE v rX) 3%nat = w64 (as_gp B))
  by (rewrite (a3E_reg v rX 3 (Z_to_bv 5 3) ltac:(vm_compute; reflexivity)); exact R3).
assert (A4 : ew (a3wE v rX) 4%nat = w64 (as_tp B))
  by (rewrite (a3E_reg v rX 4 (Z_to_bv 5 4) ltac:(vm_compute; reflexivity)); exact R4).
assert (A8 : ew (a3wE v rX) 8%nat = w64 (pf_sp0 v))
  by (rewrite (a3E_reg v rX 8 (Z_to_bv 5 8) ltac:(vm_compute; reflexivity)); exact R8).
assert (A9 : ew (a3wE v rX) 9%nat = w64 (pf_s1 v))
  by (rewrite (a3E_reg v rX 9 (Z_to_bv 5 9) ltac:(vm_compute; reflexivity)); exact R9).
assert (A22 : ew (a3wE v rX) 22%nat = w64 SHADOW_OFF)
  by (rewrite (a3E_reg v rX 22 (Z_to_bv 5 22) ltac:(vm_compute; reflexivity)); exact R22).
assert (A23 : ew (a3wE v rX) 23%nat = w64 (pf_F v pos))
  by (rewrite (a3E_reg v rX 23 (Z_to_bv 5 23) ltac:(vm_compute; reflexivity)); exact R23).
assert (A24 : ew (a3wE v rX) 24%nat = w64 (p_c v))
  by (rewrite (a3E_reg v rX 24 (Z_to_bv 5 24) ltac:(vm_compute; reflexivity)); exact R24).
assert (A25 : ew (a3wE v rX) 25%nat = w64 (p_t v))
  by (rewrite (a3E_reg v rX 25 (Z_to_bv 5 25) ltac:(vm_compute; reflexivity)); exact R25).
assert (A26 : ew (a3wE v rX) 26%nat = w64 (p_c v + seg_spec.RC_GEN))
  by (rewrite (a3E_reg v rX 26 (Z_to_bv 5 26) ltac:(vm_compute; reflexivity)); exact R26).
assert (A27 : ew (a3wE v rX) 27%nat = w64 (pf_SH v pos))
  by (rewrite (a3E_reg v rX 27 (Z_to_bv 5 27) ltac:(vm_compute; reflexivity)); exact R27).
assert (A19 : ew (a3wE v rX) 19%nat = w64 (p_lp v))
  by (rewrite (a3E_reg v rX 19 (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)); exact R19).
assert (D10 : sv_denot (a3wE v rX) (SAlu ALU_ADD (SOff 10 0) (SOff 24 0)) = w64 (p_c v + seg_spec.RC_READING)).
{ rewrite (a3_denot_add (a3wE v rX) 10 24 0x4080 (p_c v)).
  - f_equal. lia.
  - rewrite (a3E_reg v rX 10 (Z_to_bv 5 10) ltac:(vm_compute; reflexivity)), R10. apply pf_a6_k.a6_w64_u. lia.
  - exact U24.
  - lia. }
(* a2 = "%s" (listing object 35, 0x21340) and, on the NULL label, a3 = "reac-pw.conf" (object 34, 0x21360) *)
assert (O35 : ew (a3wE v rX) 276%nat = w64 (seg_litA_rc F_s)).
{ pose proof (a3_obj_at (a3wE v rX) 35 HEI ltac:(lia)) as O. rewrite a3_fs in O. exact O. }
assert (O34 : ew (a3wE v rX) 275%nat = w64 (seg_litA_rc S_base)).
{ pose proof (a3_obj_at (a3wE v rX) 34 HEI ltac:(lia)) as O. rewrite a3_sbase in O. exact O. }
(* the hand-off: the rest of the segment, at the FP state the snprintf returned *)
assert (HAFTER : forall (Sc' : astate) (Wc' : world SEGS) (rX' : bvmap 5 word) memc' mdc'
                        (fx1 : YK11.FPState),
  PaFx.fxrel fx fx1 -> a3_ret1 (fx := fx1) B v pos Sc' Wc' rX' memc' mdc' ->
  SRr SEGS Wc' (mkCfg (@mkst fx1 rX' (Z_to_bv 64 (BASE + PF_RET1)) memc' (seg_rom SEGS)) mdc')
    (PF_POST (fx := fx) B v)).
{ intros Sc' Wc' rX' memc' mdc' fx1 Hfx Hret.
  apply (a3_post_lift fx1); [exact Hfx|].
  exact (RET1 fx1 HEADS HDONE v pos Sc' Wc' rX' memc' mdc' Hret). }
unfold cfg_at. change (w64 (BASE + PF_FRAME)) with (Z_to_bv 64 (BASE + PF_FRAME)).
destruct (p_lab v) as [l|] eqn:Elab.
- (* the label is the caller's: s3 = lp <> 0, `bnez s3` taken *)
  assert (HLP : a3_LP v = p_lp v) by (unfold a3_LP; rewrite Elab; reflexivity).
  assert (HG1 : facts_ok (a3wE v rX) (mkFacts [(19%nat, mkAF 1 (2 ^ 64 - 1) 0)] [] [])).
  { split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19.
    rewrite Z.pow_0_r, Z.mod_1_r. rewrite HLP in HLpos. split; [lia|]. split; [reflexivity | lia]. }
  pose proof (a3w_seed (fx := fx) v rX Wc memc PF_FRAME [] (mkFacts [(19%nat, mkAF 1 (2 ^ 64 - 1) 0)] [] [])
    ltac:(reflexivity) (Forall_nil _) ltac:(cbn; exact I) HG1) as HS.
  paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
  { apply awr_ok_nil. }
  assert (EM : ms_mem ms = memc) by (eapply frame_of_read_only; [|exact HF]; reflexivity).
  prreg HS (1%bv : bv 5) Q1.
  assert (HRGT : pf_rg (ms_regs ms) (a3_CRG v pos)).
  { a3_crg HS D10 O35 A2 A3 A4 A8 A9 A22 A23 A24 A25 A26 A27.
    prreg HS (Z_to_bv 5 13) Q13. rewrite Q13, HLP. exact A19. }
  pmkst HS. rewrite EM in HJ |- *.
  exact (a3_at_call v pos Sc Wc rX (ms_regs ms) memc mdc _ HINV HJ Q1 HRGT HAFTER).
- (* the label is NULL: s3 is pinned to 0, `bnez s3` not taken, s3 becomes the literal 0x21360 *)
  assert (HLP : a3_LP v = seg_litA_rc S_base) by (unfold a3_LP; rewrite Elab; reflexivity).
  assert (Hlp0 : p_lp v = 0) by (pose proof HLAB as (HO & _); rewrite Elab in HO; exact HO).
  pose proof (a3w_seed (fx := fx) v rX Wc memc PF_FRAME [] (mkFacts [] [] [])
    ltac:(reflexivity) (Forall_nil _) ltac:(cbn; exact I) ltac:(cbn; repeat split; exact I)) as HS.
  pose proof (st_ok_pi_restrict_reg (fx := fx) (w_H Wc) (a3wE v rX) _ _ (Z_to_bv 5 19) HS) as Hrr.
  apply (st_ok_pi_pin_reg' (a3wE v rX) _ _ (Z_to_bv 5 19) 0) in HS;
    [| rewrite restrict_mkst_fx; cbn [ms_regs mkst]; rewrite R19, Hlp0; reflexivity | vm_compute; reflexivity].
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
  { apply awr_ok_nil. }
  assert (EM : ms_mem ms = memc) by (eapply frame_of_read_only; [|exact HF]; reflexivity).
  prreg HS (1%bv : bv 5) Q1.
  assert (HRGT : pf_rg (ms_regs ms) (a3_CRG v pos)).
  { a3_crg HS D10 O35 A2 A3 A4 A8 A9 A22 A23 A24 A25 A26 A27.
    prreg HS (Z_to_bv 5 13) Q13. rewrite Q13, HLP. exact O34. }
  pmkst HS. rewrite EM in HJ |- *.
  exact (a3_at_call v pos Sc Wc rX (ms_regs ms) memc mdc _ HINV HJ Q1 HRGT HAFTER).
Qed.
End s.

(* FRAME 0x87cc4 -> HEAD 0x87ddc or DONE 0x88bb8: a3_main walks to the snprintf's return and a3_ret1_ok
   (lib/A/Prog/pf_a3_w.v) walks from it. *)
Theorem pf_a3_holds : S_A3 B.
Proof.
intros f0 HEADS HDONE.
exact (a3_main (fx := f0) (fun fx0 => a3_ret1_ok B MSET OBJ (fx := fx0)) HEADS HDONE).
Qed.

End e.
End f.
End d.

