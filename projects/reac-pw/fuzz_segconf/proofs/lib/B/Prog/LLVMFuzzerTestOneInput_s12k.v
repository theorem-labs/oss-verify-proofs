(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first stretch of the inlined words_of of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86760 .. 0x867b4: strnlen of the message, the three mallocs stored at 120/128/136(sp) and their NULL tests reloaded from the frame), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s41.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (a call and back, the caller's facts carried past it) and A/ACh6.v (a segment from one point of the function to the next, the next point's statement a premise). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_s41.v, with its module paths, module names and numbers changed; 2758 of its 2894 lines of code are new or changed and 886 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/LLVMFuzzerTestOneInput_s20.v, with its module paths and module names changed; 351 of its 706 lines of code are new or changed and 2539 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the kit of the walk
   of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0; segments S01 and S02,
   LLVMFuzzerTestOneInput_s12.v), and the calloc call step every calloc site of the harness walk takes.

   THE FORM: the image-B twin of image A's lib/A/Prog/LLVMFuzzerTestOneInput_s12k.v (image A's S01 / S02 commit
   119b28fad68f): the same lemmas under the same names, over image B's kit copies (lib/B) and image B's cut
   statements (lib/B/Prog/LLVMFuzzerTestOneInput_defs.v), with image B's frame (352 bytes, S1 = (SP0 - 352) & -32;
   the shadow base kept at 200(s1), SH(FR) at 184(s1)):
   - acalloc04_sub: the walk form of image B's row-13 rule RtSegCalloc.aseg_calloc04_rule (pc_calloc cstk)
     (lib/B/Rt/RtSegCalloc.v, the image-B wrapper owner's commit ae8b6d1202c7, with the premise m * n <= YGCalloc.PRIM_MAX), beside
     PaCall.v's amalloc04_sub: the inner journal opened by ajournal_sub_init at window cstk and joined by
     ajournal_sub_tok, the rule's post plus that inner journal. Generic in segs.
   - lt_malloc_at / lt_calloc_at: one allocator call of the harness from a point where lt_core holds (sp = s1 = S1,
     the frame, the image facts, the blocks, the budget), to the call's return with lt_core at k + 1, one block more
     (newest first), the budget charged one event, the stack above S1 kept; in the form of fuzz_command's
     lib/A/Prog/LLVMFuzzerTestOneInput_s41.v aw_malloc_loc (origin/ossv/recipes 501c0d516c69).
   - lk_img_kept: lt_img at a later reader at an AR state that keeps every image byte the runtime does not own; the
     form of image A's S00 walk's s10_lt_img_kept (image A's S00 commit 52ff1753c784), RELRO in the image from
     image B's record SegRecBase.seg_img_facts (lib/B/Prog/SegRecBase.v: cif_relro_img), in place of the twin's
     HRELRO; the stack-protector cells (the .got word gotwA holds guardA, guardA readable; gotwA is runtime-owned in
     the regenerated listing, the image-B listing owner's commit ec20d5d4e1df) from AR at the later state by SegRecCells.seg_rec_cells, in
     place of the twin's HSSP.
   - S01's own pieces (image B only; the twin's file has no S01 yet): the seed shapes ss_s01 / ss_s01z and their
     seed lemmas s01_seed / s01_seedz (fuzz_command's lib/B/Prog/LLVMFuzzerTestOneInput_s23.v lhh_seed with the s1
     slots, the payload's first shadow byte as a region and the cell mod40A), the header's quantities per payload
     shape (s01_hdr0 .. s01_hdr3), the values the code computes for cap and nfiles (s01_U_cap, s01_U_nf), and the
     reader of a word the run wrote into the slots (s01_rd_slot).
   Statement text and proofs only about the walk's own points: no other function of the binary is proved here.

   Section hypotheses beyond the statement's B / MT (AR_laws is image B's kit's YG0q.AR_laws_ok, as the twin takes
   it since 734c2dd5a567): MTL (ameter_laws), TL (PALib: the malloc trampoline is the kit's wrapper entry), IMGF
   (image B's record SegRecBase.seg_img_facts), HSY (the record of image B's symbols YF0m.SegBSyms, which
   SegRecCells.seg_rec_cells takes), AMALLOC4 (fuzz_command's form), ACALLOC4 at the calloc trampoline with the
   window cstk and HCSTK (the twin's text from the image-A G1 walk owner, 17:57Z). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YGCalloc YG0q YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaSB SegGlob PaDenot PaLibF PaLibG.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegRecCells.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegRecBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSegCalloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* every lemma below takes all its Section's variables and hypotheses, in their order, so a caller (the S01 and S02
   segment lemmas) passes one fixed argument list *)
Set Default Proof Using "All".

(* ============================== the calloc rule's walk form (generic in segs) ============================== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section g.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variable MT : ameter_ops.
Variables pc_calloc cstk : Z.
(* PaCall.v's amalloc04_sub with the calloc rule: a0 = m, a1 = n, the window cstk in place of ASTACK, the zero
   bytes of the new block in the post *)
Lemma acalloc04_sub : RtSegCalloc.aseg_calloc04_rule segs B MT pc_calloc cstk ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (m n : Z) (o : Z) raw ch,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 m -> getr regsT 11 = w64 n ->
0 <= m -> 0 <= n -> m * n < MALLOC_MAX -> m * n <= YGCalloc.PRIM_MAX -> blocks_bytes Sc + m * n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= cstk -> cstk - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
mo_ok MT Sc (mo_malloc MT (m * n)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc_calloc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, m * n)] /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - cstk) (sp0 + o) (fun a => res <= a < res + req_size (m * n)) /\
(forall i, 0 <= i < m * n -> aview segs (w_H W2) mem2 (res + i) = Some 0) /\
mo_le MT Sc S2 (mo_malloc MT (m * n)) /\
ajournal segs B cstk (sp0 + o) [] lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 1).
Proof.
intros AC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k m n o raw ch HJ Ha0 Ha1 Hm Hn Hmn Hprim Hlive Hsp
  Ho16 Ho Hc0 Hstk Hgp Htp Hra Hraw Hnev Hch MOK.
pose proof (ajournal_sub_init segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k cstk (sp0 + o) [] o
  HJ eq_refl Ho16 Ho Hc0 Hstk) as HJ1.
eapply SRr_mono.
{ eapply (AC W regsT memT cstk (sp0 + o) [] lyc Sc W memT mdc [] lyc Sc mdc 0 m n 0 raw ch HJ1 Ha0 Ha1 Hm Hn Hmn Hprim
    Hlive);
  first [exact Hgp | exact Htp | exact Hra | exact Hraw | exact Hnev | exact Hch | exact MOK | reflexivity | lia | idtac]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP & Hres & Hfr & Hr4 & Hbl & HK & Hz & MLE).
exists ly2, S2, regs2, mem2, md2, res. split; [reflexivity|].
split.
{ change own with ([] ++ own). eapply (ajournal_sub_tok segs B LAWS segs_low); [exact HJ | exact HJ2 | lia | lia |].
  intros a (r & Hr & _). destruct Hr. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|]. split; [exact Hr4|]. split; [exact Hbl|].
replace (sp0 + o + 0 - cstk) with (sp0 + o - cstk) in HK by lia. replace (sp0 + o + 0) with (sp0 + o) in HK by lia.
split; [exact HK|]. split; [exact Hz|]. split; [exact MLE|]. replace (0 + 1) with 1 in HJ2 by reflexivity. exact HJ2.
Qed.
End g.
End c.

(* ============================== lists, words, registers ============================== *)
(* blocks_bytes is the sum of the live blocks' sizes (fuzz_command lib/A/Prog/LLVMFuzzerTestOneInput_defs.v:218-229) *)
Fixpoint lk_bsum (bl : list (Z * Z)) : Z := match bl with [] => 0 | b :: l => snd b + lk_bsum l end.
Lemma lk_bsum_app : forall l1 l2, lk_bsum (l1 ++ l2) = lk_bsum l1 + lk_bsum l2.
Proof. induction l1 as [|b l IH]; intros l2; cbn [lk_bsum app]; [reflexivity | rewrite IH; ring]. Qed.
Lemma lk_bsum_perm : forall l1 l2, Permutation l1 l2 -> lk_bsum l1 = lk_bsum l2.
Proof. intros l1 l2 H. induction H; cbn [lk_bsum]; [reflexivity | rewrite IHPermutation; reflexivity | ring | congruence]. Qed.
(* a callee-saved register a call keeps *)
Lemma lk_pres_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
(* a word every byte of which two readers agree on *)
Lemma lk_word_kept : forall (rd rd' : reader) a v,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.

(* ============================== segment S01 (K84f4c -> K85068): the seed's shape ============================== *)
(* The symbolic state at 0x84f4c: every register its own atom (sr_atoms); atoms 32, 33, 34 the payload's bytes 0,
   1, 2; atom 35 the address SHADOW_OFF + p / 8 of the payload's first shadow byte (the alias of (s8 >> 3) + t0, which
   the token runner's shadow_norm also finds for p + 1 and p + 2: the same granule); atom 36 that shadow byte.
   Regions: the s1 slots 24 .. 112 the code writes (24, 32, 56, 104), the h = min(n, 3) payload bytes at s8
   (atom 24), the shadow byte (atom 35; the literal 0 when it is 0, because the engine decides an equality from a
   literal and not from a one-point range), the cell mod40A (listing object 4: ld a3 at 0x84f80). Facts: s1 (atom 9)
   at 2 ^ 46 or above and 32-aligned (its window apart from the shadow band); p (atom 24) at 4096 or above and
   16-aligned (UBSan's p + 1, p + 2, p + 3 tests 0x84f5c, 0x84fa8, 0x85024, and the low bits (p + k) & 7 = k of the
   checks' slow blocks 0x86058, 0x86090, 0x860a0); n (atom 20) in [nlo, nhi]; the bytes; the shadow byte in
   [slo, shi] (checks 1-3 are `lb; beqz OK; j SLOW` with SLOW `andi; bge ERR; j OK`: a nonzero shadow byte s goes
   the slow way and the compare (p + k) & 7 >= s fails because k < s). *)
Definition s01_chunks : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 1 (SOff 32 0)); YP09.mkChunk 1 (CVal 1 (SOff 33 0)); YP09.mkChunk 2 (CVal 1 (SOff 34 0))].
Definition s01_slots : YP09.region := YP09.mkRegion (Some 9%nat) 24 112 24 112 [].
Definition s01_pay (h : Z) : YP09.region := YP09.mkRegion (Some 24%nat) 0 h 0 0 (firstn (Z.to_nat h) s01_chunks).
Definition s01_shv (lit0 : bool) : sv := if lit0 then SLit 0 else SOff 36 0.
Definition s01_shr (lit0 : bool) : YP09.region :=
  YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (s01_shv lit0))].
Definition s01_m40 : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 4)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit LTOI_MOD40))].
Definition s01_facts (nlo nhi slo shi : Z) : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (24%nat, mkAF 4096 0x7fffff800000 4); (20%nat, mkAF nlo nhi 0);
            (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (36%nat, mkAF slo shi 0) ]
    [] [ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 24 0) (SLit 3)) (SOff 5 0), SOff 35 0) ].
Definition ss_s01 (h nlo nhi slo shi : Z) (lit0 : bool) : sstate :=
  mkSS LO_K84f4c sr_atoms [s01_slots; s01_pay h; s01_shr lit0; s01_m40] None (s01_facts nlo nhi slo shi).
(* n = 0: no payload byte and no shadow byte is read (beqz s4 at 0x84f50 to 0x84fec) *)
Definition ss_s01z : sstate :=
  mkSS LO_K84f4c sr_atoms [s01_slots] None (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Definition s01_extra (b0 b1 b2 sa s : Z) : list word := map (Z_to_bv 64) [b0; b1; b2; sa; s].

(* the header's quantities for the four shapes of the payload (SegModel.decode, SegModel.v:289-293): cap = byte 0
   mod 40, flags = byte 1, nfiles = 1 + byte 2 mod 4 (0 for a missing byte), the cursor after the three bytes *)
Lemma s01_dec_files_len : forall k inp, length (SegModel.dec_files k inp) = k.
Proof.
induction k as [|k IH]; intros inp; [reflexivity|]. cbn [SegModel.dec_files].
destruct (SegModel.fuzz_u8 inp) as [lb i1]. destruct (SegModel.fuzz_u16 i1) as [len i2].
destruct (SegModel.fuzz_take i2 len) as [q i3]. cbn [length]. rewrite IH. reflexivity.
Qed.
Lemma s01_hdr0 : seg_spec.seg_cap [] = 0 /\ seg_spec.seg_flags [] = 0 /\ seg_spec.seg_nfiles [] = 1 /\
  seg_spec.seg_cur_n [] 0 = 0 /\ forall p, seg_spec.seg_cur_at [] p 0 = p.
Proof.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
intros p. unfold seg_spec.seg_cur_at. cbn. lia.
Qed.
Lemma s01_hdr1 : forall x0 : byte,
  seg_spec.seg_cap [x0] = bv_unsigned x0 mod 40 /\ seg_spec.seg_flags [x0] = 0 /\ seg_spec.seg_nfiles [x0] = 1 /\
  seg_spec.seg_cur_n [x0] 0 = 0 /\ forall p, seg_spec.seg_cur_at [x0] p 0 = p + 1.
Proof.
intros x0. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
intros p. unfold seg_spec.seg_cur_at. cbn. lia.
Qed.
Lemma s01_hdr2 : forall x0 x1 : byte,
  seg_spec.seg_cap [x0; x1] = bv_unsigned x0 mod 40 /\ seg_spec.seg_flags [x0; x1] = bv_unsigned x1 /\
  seg_spec.seg_nfiles [x0; x1] = 1 /\ seg_spec.seg_cur_n [x0; x1] 0 = 0 /\
  forall p, seg_spec.seg_cur_at [x0; x1] p 0 = p + 2.
Proof.
intros x0 x1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
intros p. unfold seg_spec.seg_cur_at. cbn. lia.
Qed.
Lemma s01_hdr3 : forall (x0 x1 x2 : byte) rest,
  seg_spec.seg_cap (x0 :: x1 :: x2 :: rest) = bv_unsigned x0 mod 40 /\
  seg_spec.seg_flags (x0 :: x1 :: x2 :: rest) = bv_unsigned x1 /\
  seg_spec.seg_nfiles (x0 :: x1 :: x2 :: rest) = 1 + bv_unsigned x2 mod 4 /\
  seg_spec.seg_cur_n (x0 :: x1 :: x2 :: rest) 0 = Z.of_nat (length rest) /\
  forall p, seg_spec.seg_cur_at (x0 :: x1 :: x2 :: rest) p 0 = p + 3.
Proof.
intros x0 x1 x2 rest.
assert (HL : length (seg_spec.seg_cur (x0 :: x1 :: x2 :: rest) 0) = length rest)
  by (unfold seg_spec.seg_cur, seg_spec.seg_hdr, seg_spec.seg_in, seg_spec.zs; cbn; apply length_map).
split; [reflexivity|]. split; [reflexivity|]. split.
{ unfold seg_spec.seg_nfiles, seg_spec.seg_files, seg_spec.seg_pay, SegModel.decode, seg_spec.seg_in, seg_spec.zs.
  cbn [map SegModel.fuzz_u8 SegModel.p_files]. rewrite s01_dec_files_len.
  pose proof (Z.mod_pos_bound (bv_unsigned x2) 4 ltac:(lia)). rewrite Z2Nat.id by lia. reflexivity. }
split; [unfold seg_spec.seg_cur_n; rewrite HL; reflexivity|].
intros p. unfold seg_spec.seg_cur_at. rewrite HL. cbn [length]. lia.
Qed.
(* the values the code computes: cap = u8 - mulhu(u8, mod40) * 40 (0x84f88 .. 0x84f94; the run carries the cell's
   value LTOI_MOD40 as its literal) and nfiles = (u8 & 3) + 1 (0x85050 .. 0x85054) *)
Lemma s01_U_cap : forall E (n : nat) b, ew E n = Z_to_bv 64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_SUB (SOff n 0) (SMd M_MUL (SMd M_MULHU (SOff n 0) (SLit 0x0666666666666667)) (SLit 40))) = b mod 40.
Proof.
intros E n b Hn Hb. change 0x0666666666666667 with LTOI_MOD40.
pose proof (Z.div_mod b 40 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound b 40 ltac:(lia)) as Hmb.
assert (Hq : b * LTOI_MOD40 / 2 ^ 64 = b / 40).
{ unfold LTOI_MOD40. symmetry. apply (Z.div_unique _ _ _ (b * 0x0666666666666667 - b / 40 * 2 ^ 64)); [|ring]. lia. }
assert (Hq0 : 0 <= b / 40 <= 6) by lia.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite !U_SLit.
rewrite (U_atom E n b Hn) by lia.
change (zcanon LTOI_MOD40) with LTOI_MOD40. change (zcanon 40) with 40. change (Z.of_N 64) with 64.
rewrite Z.shiftr_div_pow2 by lia. rewrite Hq.
rewrite (zcanon_id (b / 40)) by (unfold M64; lia).
rewrite (zcanon_id (b / 40 * 40)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma s01_U_nf : forall E (n : nat) b, ew E n = Z_to_bv 64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_ADD (SAlu ALU_AND (SOff n 0) (SLit 3)) (SLit 1)) = 1 + b mod 4.
Proof.
intros E n b Hn Hb.
assert (HL : Z.land b 3 = b mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
pose proof (Z.mod_pos_bound b 4 ltac:(lia)) as Hm.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_and_lit by lia. rewrite (U_atom E n b Hn) by lia.
rewrite U_SLit. change (zcanon 1) with 1. rewrite HL. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma lk_blocks_bytes : forall B ly S, blocks_bytes S = lk_bsum (ablocks B ly S).
Proof.
intros B ly S. unfold blocks_bytes, ablocks, blocks. induction (st_chunks S) as [|c cs IH]; [reflexivity|].
cbn [fold_right List.filter]. destruct (is_alloc c); cbn [map lk_bsum snd fst]; [rewrite IH; reflexivity | exact IH].
Qed.
(* the frame address of a journal's target layout is the entry's *)
Lemma lk_frame_addr : forall B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S (W : world SEGS) mem md k,
  ajournal SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
  forall cid pos, frame_addr ly cid pos = frame_addr ly0 cid pos.
Proof.
intros B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k HJ cid pos.
destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity.
Qed.
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).

(* ---- the S01 seed: the state at 0x84f4c is an instance of ss_s01 / ss_s01z (fuzz_command's
   lib/B/Prog/LLVMFuzzerTestOneInput_s23.v lhh_seed, with the s1 slots, the shadow byte and the cell mod40A) ---- *)
Definition s01_E (regs : bvmap 5 word) (b0 b1 b2 sa s : Z) : env := Eimg (Ereg regs (s01_extra b0 b1 b2 sa s)).
Lemma s01_E_facts : forall regs b0 b1 b2 sa s,
  (forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s01_E regs b0 b1 b2 sa s) n = getr regs rr) /\
  ew (s01_E regs b0 b1 b2 sa s) 32 = Z_to_bv 64 b0 /\ ew (s01_E regs b0 b1 b2 sa s) 33 = Z_to_bv 64 b1 /\
  ew (s01_E regs b0 b1 b2 sa s) 34 = Z_to_bv 64 b2 /\ ew (s01_E regs b0 b1 b2 sa s) 35 = Z_to_bv 64 sa /\
  ew (s01_E regs b0 b1 b2 sa s) 36 = Z_to_bv 64 s.
Proof.
intros regs b0 b1 b2 sa s. unfold s01_E.
split; [|split; [|split; [|split; [|split]]]].
- intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0).
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1).
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2).
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 3).
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 4).
Qed.
(* a byte the reader shows, as a 1-byte value; a value the reader shows, as the restricted memory's bytes
   (fuzz_command lib/B/Prog/LLVMFuzzerTestOneInput_s23.v lhh_aval1 / lhh_val_of_aval) *)
Lemma s01_val1 : forall (rd : reader) a v, rd a = Some v -> 0 <= v < 256 -> sa_val rd a 1 v.
Proof.
intros rd a v H Hv k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, H. f_equal.
unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small v 256 Hv). reflexivity.
Qed.
Lemma s01_val_of_sa : forall (H : word -> bool) (mem : word -> option byte) a n v,
  sa_val (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.
(* a 1-byte chunk of a region from the byte the reader shows *)
Lemma s01_chunk1 : forall (W : world SEGS) mem E base off e v,
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 256 -> rdW W mem (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 1 e)).
Proof.
intros W mem E base off e v He Hv Hrd.
apply (YI04.chunk_ok_val SEGS E _ base off 1 e v He); [simpl; lia | simpl; lia |].
apply s01_val_of_sa. exact (s01_val1 _ _ _ Hrd Hv).
Qed.
Lemma s01_seed : forall (h nlo nhi slo shi : Z) (lit0 : bool) (W : world SEGS) (regs : bvmap 5 word) mem
    b0 b1 b2 p s s1,
  1 <= h <= 3 -> (lit0 = true -> s = 0) ->
  getr regs 9 = w64 s1 -> 2 ^ 46 <= s1 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  (forall a, s1 + 24 <= a < s1 + 112 -> apresent (w_H W) mem a) ->
  getr regs 24 = w64 p -> 4096 <= p <= 0x7fffff800000 -> p mod 16 = 0 -> p + h <= s1 ->
  (p + h <= 0x10000 \/ 0x602000 <= p) -> (p + h <= SHADOW_OFF \/ kHighMemBeg <= p) ->
  getr regs 5 = w64 SHADOW_OFF ->
  nlo <= bv_unsigned (getr regs 20) <= nhi ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= slo -> slo <= s <= shi -> shi < 128 ->
  rdW W mem p = Some b0 -> (1 < h -> rdW W mem (p + 1) = Some b1) -> (2 < h -> rdW W mem (p + 2) = Some b2) ->
  rdW W mem (SHADOW_OFF + p / 8) = Some s ->
  VAL (A_OBJ 4) = mod40A -> sa_val (rdW W mem) mod40A 8 LTOI_MOD40 ->
  st_ok_pi SEGS VAL (s01_E regs b0 b1 b2 (SHADOW_OFF + p / 8) s) (ss_s01 h nlo nhi slo shi lit0)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K84f4c)) mem (seg_rom SEGS))).
Proof.
intros h nlo nhi slo shi lit0 W regs mem b0 b1 b2 p s s1 Hh Hl0 R9 Hs1 Hs1al Hpres R24 Hp Hpal Hps1 Hpimg Hpsh R5 R20
  B0 B1 B2 Hslo Hs Hshi H0 H1 H2 HSH HV4 HM40.
destruct (s01_E_facts regs b0 b1 b2 (SHADOW_OFF + p / 8) s) as (EEo & E32 & E33 & E34 & E35 & E36).
assert (E4 : ew (s01_E regs b0 b1 b2 (SHADOW_OFF + p / 8) s) (A_OBJ 4) = Z_to_bv 64 (VAL (A_OBJ 4)))
  by (unfold s01_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
remember (s01_E regs b0 b1 b2 (SHADOW_OFF + p / 8) s) as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E24 : ew E 24 = Z_to_bv 64 p) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
assert (E5 : ew E 5 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 5%nat 5%bv eq_refl); exact R5).
assert (E20 : ew E 20 = getr regs 20) by (apply EEo; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Hsa : SHADOW_OFF <= SHADOW_OFF + p / 8 <= SHADOW_OFF + 0x7fffff800000 / 8)
  by (split; [pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)); lia | apply Z.add_le_mono_l, Z.div_le_mono; lia]).
assert (Hsa' : p + h <= SHADOW_OFF + p / 8 \/ SHADOW_OFF + p / 8 + 1 <= p).
{ unfold SHADOW_OFF, kHighMemBeg in *. destruct Hpsh as [Hq | Hq]; [left; lia | right].
  pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.mod_pos_bound p 8 ltac:(lia)). lia. }
unfold SHADOW_OFF in Hsa.
unfold ss_s01. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- rewrite HE. unfold s01_E. apply regs_ok_Eimg_Ereg.
- assert (h = 1 \/ h = 2 \/ h = 3) as [-> | [-> | ->]] by lia; destruct lit0; vm_compute; reflexivity.
- unfold s01_slots, s01_pay, s01_shr, s01_m40.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
  unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 9%nat s1 E9) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB 24%nat p E24) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    assert (C0 : YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) p (YP09.mkChunk 0 (CVal 1 (SOff 32 0))))
      by (apply (s01_chunk1 W mem E p 0 _ b0); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | exact B0 | rewrite Z.add_0_r; exact H0]).
    assert (h = 1 \/ h = 2 \/ h = 3) as [-> | [-> | ->]] by lia; unfold s01_chunks;
      [change (Z.to_nat 1) with 1%nat | change (Z.to_nat 2) with 2%nat | change (Z.to_nat 3) with 3%nat];
      cbn [firstn]; repeat apply Forall_cons; try apply Forall_nil; try exact C0.
    * apply (s01_chunk1 W mem E p 1 _ b1); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | exact B1 | exact (H1 ltac:(lia))].
    * apply (s01_chunk1 W mem E p 1 _ b1); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | exact B1 | exact (H1 ltac:(lia))].
    * apply (s01_chunk1 W mem E p 2 _ b2); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | exact B2 | exact (H2 ltac:(lia))].
  + rewrite (VB 35%nat (SHADOW_OFF + p / 8) E35) by (unfold SHADOW_OFF; lia).
    split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (s01_chunk1 W mem E _ 0 _ s); [| lia | rewrite Z.add_0_r; exact HSH].
    destruct lit0; cbn [s01_shv sv_denot].
    * rewrite (Hl0 eq_refl). reflexivity.
    * rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + rewrite (VB (A_OBJ 4) (VAL (A_OBJ 4)) E4) by (pose proof (pa_val_range (A_OBJ 4)); lia). rewrite HV4.
    split; [unfold mod40A; lia|]. split; [unfold mod40A; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (YI04.chunk_ok_val SEGS E _ mod40A 0 8 (SLit LTOI_MOD40) LTOI_MOD40);
      [reflexivity | unfold LTOI_MOD40; simpl; lia | simpl; lia |].
    rewrite Z.add_0_r. apply s01_val_of_sa. exact HM40.
- apply pairwise_disjoint_of_extents.
  unfold s01_slots, s01_pay, s01_shr, s01_m40, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 9%nat s1 E9) by lia. rewrite (VB 24%nat p E24) by lia.
  rewrite (VB 35%nat (SHADOW_OFF + p / 8) E35) by (unfold SHADOW_OFF; lia).
  rewrite (VB (A_OBJ 4) (VAL (A_OBJ 4)) E4) by (pose proof (pa_val_range (A_OBJ 4)); lia). rewrite HV4.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold mod40A, SHADOW_OFF in *.
  repeat split; lia.
- split; [|split; [exact I|]].
  2: { cbn [f_alias alias_ok s01_facts]. split; [|exact I].
       exact (shadow_decl_ok E 24 5 35 p SHADOW_OFF E24 ltac:(lia) E5 E35). }
  cbn [f_atoms atoms_ok s01_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E24, E20, E32, E33, E34, E36. rewrite !unsigned_lit_small by lia.
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.
Lemma s01_seedz : forall (W : world SEGS) (regs : bvmap 5 word) mem s1,
  getr regs 9 = w64 s1 -> 2 ^ 46 <= s1 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  (forall a, s1 + 24 <= a < s1 + 112 -> apresent (w_H W) mem a) ->
  st_ok_pi SEGS VAL (s01_E regs 0 0 0 0 0) ss_s01z
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K84f4c)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 R9 Hs1 Hs1al Hpres.
destruct (s01_E_facts regs 0 0 0 0 0) as (EEo & _).
remember (s01_E regs 0 0 0 0 0) as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
unfold ss_s01z. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- rewrite HE. unfold s01_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold s01_slots, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, unsigned_lit_small by lia. change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.
(* ---- readers of the state a run reaches (image A's S00 walk's s10_rd_chunk8, chain_words_s1.v:103-111) ---- *)
Lemma s01_rd_chunk8 : forall E H mem base off a e v cs,
  Forall (YP09.chunk_ok SEGS E (mrestrict H mem) base) cs -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  a = base + off -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros E H mem base off a e v cs Hc Hin -> He Hv. rewrite Forall_forall in Hc. specialize (Hc _ Hin).
apply rdword_of_val_mem; [|exact Hv].
apply (val_of_chunk_ok SEGS E _ base off 8 e v Hc He); [exact Hv | cbn; lia].
Qed.
(* a word of the s1 slots region (the run's region 0) *)
Lemma s01_rd_slot : forall E ss ms (W : world SEGS) cs s1 off e v,
  st_ok SEGS E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 9%nat) 24 112 24 112 cs) ->
  bv_unsigned (ew E 9) = s1 -> In (YP09.mkChunk off (CVal 8 e)) cs -> U E e = v ->
  rdword (rdW W (ms_mem ms)) (s1 + off) = Some v.
Proof.
intros E ss ms W cs s1 off e v HS Hn E9 Hin HU.
pose proof (st_ok_region_nth E ss _ 0 _ HS Hn) as (_ & _ & _ & C).
cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in C. rewrite E9 in C.
apply (s01_rd_chunk8 E (w_H W) (ms_mem ms) s1 off _ e v cs C Hin eq_refl).
- rewrite <- HU. apply denot_lit_U.
- pose proof (U_range E e) as Hr. unfold M64 in Hr. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the allocator record's laws: image B's kit proves them (lib/B/YG0q.v AR_laws_ok), as the twin takes them *)
#[local] Notation LAWS := (YG0q.AR_laws_ok SEGS B).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* image B's facts about the image and its segments (lib/B/Prog/SegRecBase.v): RELRO in the image, the guard's ROM
   bytes; and the record of image B's symbols (lib/B/YF0m.v), which SegRecCells.seg_rec_cells takes for the
   stack-protector cells at an AR state *)
Hypothesis IMGF : seg_img_facts SEGS B.
Hypothesis HSY : YF0m.SegBSyms B.
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Variable cstk : Z.
Hypothesis HCSTK : 0 <= cstk /\ LTOI_FRAME_MAX + cstk <= STK_LLVMFuzzerTestOneInput.
Hypothesis ACALLOC4 : forall fx0 : YK11.FPState,
  @RtSegCalloc.aseg_calloc04_rule fx0 rc SK SEGS B MT (pa_sigma SS___interceptor_trampoline_calloc) cstk.

(* the entry sp and the realigned base S1 (andi sp,sp,-32 at 0x84e00 after addi sp,sp,-352) *)
Lemma lk_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - LTOI_FRAME_MAX <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 352.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME, LTOI_FRAME_MAX in *.
set (s := spZ (x_regs cx)) in *. clearbody s.
repeat split; lia.
Qed.

(* a live block of a state is a harness block of that state: at or above 4096, 16-aligned, addressable *)
Lemma lk_hblk : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> lt_hblk B ly S (rdW W mem) a n.
Proof.
intros ly S W mem md a n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4096 & Hceil & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hn0).
Qed.

(* the image facts of a point carried to a later reader at an AR state that agrees on every image byte the runtime
   does not own (all of seg_himg's objects are such bytes, sa_img; RELRO by cif_relro_img) and on the ROM bytes; the
   stack-protector cells from AR at the later state (SegRecCells.seg_rec_cells) *)
Lemma lk_lit_kept : forall (W W' : world SEGS) mem mem' a s,
  (forall x, a <= x < a + (Z.of_nat (length s) + 1) -> rdW W' mem' x = rdW W mem x) ->
  sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s.
Proof.
intros W W' mem mem' a s HK (Ha & ((Hzs & Hn0) & _) & Hpin & Hrt & Himg).
split; [exact Ha|]. split; [split; [split; [|exact Hn0] | exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hrt)]|].
- intros i Hi. rewrite HK; [exact (Hzs i Hi)|]. rewrite length_app in Hi. cbn [length] in Hi. lia.
- split; [exact Hpin|]. split; [exact Hrt | exact Himg].
Qed.
Lemma lk_img_kept : forall cx (W W' : world SEGS) mem mem' ly' S' md',
  lt_img B cx (rdW W mem) ->
  AR SEGS B ly' S' W' mem' md' ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W' mem' a = rdW W mem a) ->
  lt_img B cx (rdW W' mem').
Proof.
intros cx W W' mem mem' ly' S' md' (HRO & HIMG & HGI) HAR' HK.
assert (KI : forall q n, sa_img SEGS B q n -> forall x, q <= x < q + n -> rdW W' mem' x = rdW W mem x).
{ intros q n Hq x Hx. destruct (Hq x Hx) as (H1 & H2 & H3). exact (HK x H1 H2 H3). }
assert (KL : forall a s, sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s).
{ intros a s Hl. apply (lk_lit_kept W W' mem mem' a s); [|exact Hl].
  destruct Hl as (_ & _ & _ & _ & Himg). exact (KI _ _ Himg). }
destruct HIMG as (Hm40 & Hm40i & Hfz & Hrc & Hcat & Hcata & Hw & Hrl & _ & Hpin & Hrt & Hli & Hd1 & Hd2 & Hd3).
split; [|split].
- intros a Hro Ho He. rewrite (HK a); [exact (HRO a Hro Ho He) | | exact Ho | exact He].
  destruct Hro as [(s & Hs & _ & Hr) | Hrr]; [exists s; split; [exact Hs | exact Hr] | exact (@cif_relro_img SK SEGS B IMGF a Hrr)].
- split; [intros k Hk; rewrite (KI _ 8 Hm40i) by lia; exact (Hm40 k Hk)|].
  split; [exact Hm40i|].
  split; [intros s Hs; destruct (Hfz s Hs) as [H1 H2]; exact (conj (KL _ _ H1) H2)|].
  split; [intros s Hs; destruct (Hrc s Hs) as [H1 H2]; exact (conj (KL _ _ H1) H2)|].
  split.
  { destruct Hcat as (Hcp & Hci & Hrows). split; [exact Hcp|]. split; [exact Hci|].
    intros i Hi. destruct (Hrows i Hi) as (tp & Htp & Hl). exists tp. split; [|exact (KL _ _ Hl)].
    apply (lk_word_kept (rdW W mem)); [|exact Htp]. intros x Hx. apply (KI _ _ Hci).
    unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, pin_spec.CAT_N in *. lia. }
  split; [exact Hcata|].
  split.
  { destruct Hw as (Hwp & Hwi & Hws). split; [exact Hwp|]. split; [exact Hwi|].
    intros i Hi. destruct (Hws i Hi) as (wp & Hwp' & Hl). exists wp. split; [|exact (KL _ _ Hl)].
    apply (lk_word_kept (rdW W mem)); [|exact Hwp']. intros x Hx. apply (KI _ _ Hwi). lia. }
  split.
  { destruct Hrl as (Hrp & Hri & Hrs). split; [exact Hrp|]. split; [exact Hri|].
    intros i Hi k Hk. rewrite (KI _ _ Hri) by lia. exact (Hrs i Hi k Hk). }
  split; [exact (proj1 (proj2 (SegRecCells.seg_rec_cells SEGS B LAWS HSY IMGF ly' S' W' mem' md' HAR')))|].
  split; [exact Hpin|]. split; [exact Hrt|]. split; [exact Hli|].
  split; [exact Hd1|]. split; [exact Hd2 | exact Hd3].
- intros i Hi. rewrite (KI _ _ Hli) by (unfold LONGL_W, LONGL_N; lia). exact (HGI i Hi).
Qed.

(* a chain for the call's chain_pre: the stack from S1 to the layout's top is mapped (the entry's astack_pres
   carried by the journal; longl, the footprint, is below the stack), and s0 = SP0 is at least S1 + 352 *)
Lemma lk_chain : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o -> 4096 <= raZ regs ->
  exists ch, chain_pre ly (rdW W mem) regs ch.
Proof.
intros cx ly S W regs mem md k o HB HF Hra.
pose proof (lk_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HF as (HJ & R2 & _ & _ & R8 & _).
pose proof HB as (_ & HPRES & _).
pose proof asan_consts as (C1 & _).
assert (Esp : spZ regs = x_s1 cx)
  by (unfold spZ; rewrite R2; unfold w64; rewrite YP03.unsigned_lit_small by lia; reflexivity).
assert (Es0 : s0Z regs = x_sp0 cx)
  by (unfold s0Z; rewrite R8; unfold w64; rewrite YP03.unsigned_lit_small by lia; reflexivity).
apply chain_pre_any; [exact Hra| |].
- rewrite Esp. apply (astack_rd_mono ly _ (x_sp0 cx - STK_LLVMFuzzerTestOneInput)); [lia|].
  apply astack_rd_of_pres.
  apply (astack_pres_journal SEGS B pa_segs_low STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k HJ HPRES).
  intros a (r & Hr & Ha) Ha2. exfalso. unfold ltoi_PG in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  unfold longlA, A_LONGL, LONGL_N in Ha. lia.
- rewrite Esp, Es0. lia.
Qed.

(* the facts of a point after one allocator call of the harness at sp = S1: the journal from the entry goes on with
   one event, the kept registers and every byte the facts read are the same, the new block joins the harness's
   (newest first), the budget pays one event *)
Lemma lk_after_alloc : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 res nb slo,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  1 <= rem -> 0 <= nb <= 65536 ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 (k + 1) ->
  aregs_preserved regsT regs2 -> frames S2 = frames S ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, nb)] ->
  acall_kept SEGS B ly S W memT W2 mem2 slo (x_s1 cx) (fun a => res <= a < res + req_size nb) ->
  mo_le MT S S2 (mo_malloc MT nb) ->
  lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT nb) (rem - 1) o ((res, nb) :: O) /\
  lt_hblk B ly2 S2 (rdW W2 mem2) res nb /\
  (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a).
Proof.
intros cx ly S W regsT memT md k acc rem o O ly2 S2 W2 regs2 mem2 md2 res nb slo HB HC Hrem Hnb HJ2 HP Hfr2 Hbl HKc MLE.
pose proof (lk_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof (proj1 HJ2) as HAR2.
pose proof HKc as (K1 & _ & K3 & K4 & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ASAN_CEIL_range as (CR & _).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (HinF2 : In (LT_FCLS, x_fpos cx) (frames S2)) by (rewrite Hfr2; exact HinF).
assert (HinB2 : In (res, nb) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by exact (lk_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (EF2 : frame_addr ly2 LT_FCLS (x_fpos cx) = x_fr cx) by exact (lk_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W memT md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res nb HAR2 HinB2) as (_ & Hr4096 & Hrceil & Hrapp & _ & _ & _).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 res nb LT_FCLS (x_fpos cx) HAR2 HinB2 HinF2) as Hsep.
rewrite EF2, F512 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
(* the stack above S1 *)
assert (KS : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a).
{ intros a Ha. pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR.
  apply K1; [split; [lia | exact (proj2 Ha)] |]. intros [_ Hc]. lia. }
(* the frame's bytes *)
assert (KF : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W2 mem2 a = rdW W memT a).
{ intros a Ha. apply (K4 LT_FCLS (x_fpos cx) a HinF).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, F512. lia.
  - cbv beta. intros Hr. lia. }
(* the frame's shadow bytes *)
assert (KH : forall i, 0 <= i < 64 -> rdW W2 mem2 (x_sh cx + i) = rdW W memT (x_sh cx + i)).
{ intros i Hi. apply (K4 LT_FCLS (x_fpos cx) _ HinF).
  - right. unfold in_zr. cbn [fst snd]. rewrite EF, F512. unfold x_sh. lia.
  - cbv beta. intros Hr. unfold in_app, kLowShadowBeg, ASAN_CEIL in Hrapp. unfold x_sh, shadow_addr, SHADOW_OFF in Hr.
    pose proof (req_size_pos nb ltac:(lia)) as [Hq1 _]. lia. }
split; [|split; [exact (lk_hblk ly2 S2 W2 mem2 md2 res nb HAR2 HinB2) | exact KS]].
split; [|split; [|split]].
- (* the frame *)
  split; [exact HJ2|].
  rewrite (lk_pres_reg _ _ 2%bv 2 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (lk_pres_reg _ _ 3%bv 3 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (lk_pres_reg _ _ 4%bv 4 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (lk_pres_reg _ _ 8%bv 8 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (lk_pres_reg _ _ 9%bv 9 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (lk_word_kept (rdW W memT)); [|exact (HSV i r Hi)]. intros x Hx. apply KS. lia. }
  split; [apply (lk_word_kept (rdW W memT)); [|exact HH0]; intros x Hx; apply KF; lia|].
  split; [apply (lk_word_kept (rdW W memT)); [|exact HH8]; intros x Hx; apply KF; lia|].
  split; [apply (lk_word_kept (rdW W memT)); [|exact HH16]; intros x Hx; apply KF; unfold LT_FLAGW; lia|].
  split; [apply (lk_word_kept (rdW W memT)); [|exact HFL]; intros x Hx; apply KF; unfold LT_FLAGW in *; lia|].
  split; [apply (lk_word_kept (rdW W memT)); [|exact H200]; intros x Hx; apply KS; lia|].
  split.
  { intros i Hi. rewrite (lt_fsh_len o) in Hi. rewrite KH by lia. exact (HSH i ltac:(rewrite lt_fsh_len; exact Hi)). }
  apply (lk_word_kept (rdW W memT)); [|exact H184]; intros x Hx; apply KS; lia.
- (* the image facts *)
  exact (lk_img_kept cx W W2 memT mem2 ly2 S2 md2 HI HAR2 K3).
- (* the blocks *)
  unfold lt_blocks in *. rewrite Hbl.
  eapply Permutation_trans; [apply Permutation_app_tail; exact HBL|].
  cbn [app]. apply Permutation_sym. apply Permutation_cons_append.
- (* the budget *)
  destruct HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (mo_malloc_mono MT MTL nb 65536 ltac:(lia)) as M1.
  pose proof (mo_malloc_nonneg MT MTL nb ltac:(lia)) as M0.
  pose proof (mo_free_nonneg MT MTL) as M3.
  assert (HU : mo_malloc MT nb <= LT_U MT) by (unfold LT_U; lia).
  unfold lt_bud. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ B4 MLE)|]. split; [lia|].
  set (U := LT_U MT) in *. clearbody U. nia.
Qed.

(* the facts of a point carried across a run of the walk that writes at most the s1 slots [S1 + lo, S1 + hi) below
   184(s1), keeps sp, gp, tp, s0, s1 and the allocator state (its journal from the entry at the same count) *)
Lemma lk_core_run : forall cx ly S (W : world SEGS) regs mem md k acc rem o O regs' mem' md' lo hi,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + lo <= a < x_s1 cx + hi) -> rdW W mem' a = rdW W mem a) ->
  0 <= lo <= hi -> hi <= 184 ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  lt_core B MT cx ly S W regs' mem' md' k acc rem o O.
Proof.
intros cx ly S W regs mem md k acc rem o O regs' mem' md' lo hi HB HC HJ' HK Hlo Hhi P2 P3 P4 P8 P9.
pose proof (lk_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR.
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by exact (lk_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
assert (KA : forall a, 0 <= a < x_s1 cx + lo \/ x_s1 cx + hi <= a < 2 ^ 64 -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply HK.
  - destruct Ha as [Ha | Ha]; split; lia.
  - intros [Hc1 Hc2]. destruct Ha as [Ha | Ha]; lia. }
split; [|split; [|split]].
- split; [exact HJ'|].
  rewrite P2, P3, P4, P8, P9.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (lk_word_kept (rdW W mem)); [|exact (HSV i r Hi)]. intros x Hx. apply KA. right. lia. }
  split; [apply (lk_word_kept (rdW W mem)); [|exact HH0]; intros x Hx; apply KA; left; lia|].
  split; [apply (lk_word_kept (rdW W mem)); [|exact HH8]; intros x Hx; apply KA; left; lia|].
  split; [apply (lk_word_kept (rdW W mem)); [|exact HH16]; intros x Hx; apply KA; left; lia|].
  split; [apply (lk_word_kept (rdW W mem)); [|exact HFL]; intros x Hx; apply KA; left; unfold LT_FLAGW in *; lia|].
  split; [apply (lk_word_kept (rdW W mem)); [|exact H200]; intros x Hx; apply KA; right; lia|].
  split.
  { intros i Hi. rewrite KA; [exact (HSH i Hi)|]. left. rewrite (lt_fsh_len o) in Hi.
    unfold x_sh, shadow_addr, SHADOW_OFF. lia. }
  apply (lk_word_kept (rdW W mem)); [|exact H184]; intros x Hx; apply KA; right; lia.
- apply (lk_img_kept cx W W mem mem' ly S md' HI (proj1 HJ')).
  intros a Ha _ _. apply KA. left. pose proof (pa_segs_low a Ha). lia.
- exact HBL.
- exact HBUD.
Qed.

(* the premises an allocator call of the harness asks, from lt_core at the call *)
Lemma lk_call_pre : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O nb,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  1 <= rem -> 0 <= nb <= 65536 -> lk_bsum O + nb <= LIVE_LTOI ->
  spZ regsT = x_sp0 cx + (x_s1 cx - x_sp0 cx) /\ (x_s1 cx - x_sp0 cx) mod 16 = 0 /\ x_s1 cx - x_sp0 cx <= 0 /\
  - LTOI_FRAME_MAX <= x_s1 cx - x_sp0 cx /\
  getr regsT 3 = w64 (as_gp B) /\ getr regsT 4 = w64 (as_tp B) /\ st_nev S < EV_MAX /\
  blocks_bytes S + nb <= LIVE_MAX /\ mo_ok MT S (mo_malloc MT nb).
Proof.
intros cx ly S W regsT memT md k acc rem o O nb HB HC Hrem Hnb Hsum.
pose proof (lk_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HC as (HF & _ & HBL & HBUD).
pose proof HF as (HJ & R2 & R3 & R4 & _).
pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & Hlive & Hmo).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof asan_consts as (C1 & _).
pose proof (mo_malloc_mono MT MTL nb 65536 ltac:(lia)) as M1.
pose proof (mo_malloc_nonneg MT MTL nb ltac:(lia)) as M0.
pose proof (mo_free_nonneg MT MTL) as M3.
assert (HU : mo_malloc MT nb <= LT_U MT) by (unfold LT_U; lia).
assert (HRU : LT_U MT <= rem * LT_U MT) by nia.
split; [unfold spZ; rewrite R2; unfold w64; rewrite YP03.unsigned_lit_small by lia; lia|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite R3; exact Hgp0|]. split; [rewrite R4; exact Htp0|].
split; [unfold EV_LTOI in *; lia|].
split.
{ rewrite (lk_blocks_bytes B ly S), (lk_bsum_perm _ _ HBL), lk_bsum_app.
  unfold x_bl0. rewrite <- (lk_blocks_bytes B (x_ly cx) (x_S cx)). unfold LIVE_LTOI in *. lia. }
apply (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) acc (mo_malloc MT nb) MTL Hmo B4 M0). lia.
Qed.

(* ---- one call of the malloc wrapper (the trampoline the listing's PCall names) from a point where lt_core holds ---- *)
Lemma lt_malloc_at : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O nb raw Q,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  1 <= rem -> 0 <= nb <= 65536 -> lk_bsum O + nb <= LIVE_LTOI ->
  getr regsT 10 = w64 nb -> getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2 res,
     lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT nb) (rem - 1) o ((res, nb) :: O) ->
     lt_hblk B ly2 S2 (rdW W2 mem2) res nb ->
     aregs_preserved regsT regs2 -> getr regs2 10 = w64 res ->
     (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a) ->
     SRr SEGS W2 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_malloc)) memT (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regsT memT md k acc rem o O nb raw Q HB HC Hrem Hnb Hsum H10 H1 Hraw Hra4 HK.
destruct (lk_call_pre cx ly S W regsT memT md k acc rem o O nb HB HC Hrem Hnb Hsum)
  as (Hsp & Ho16 & Ho0 & Hom & Hgp & Htp & Hnev & Hlv & MOK).
pose proof HC as (HF & _).
pose proof (proj1 HF) as HJ.
pose proof ltoi_stk_room as HSR.
destruct (lk_chain cx ly S W regsT memT md k o HB HF ltac:(unfold raZ; rewrite H1; exact Hra4)) as (ch & Hch).
rewrite (pal_malloc B TL).
eapply SRr_bind.
{ exact (amalloc04_sub SEGS B LAWS pa_segs_low MT (AMALLOC4 fx) W regsT memT STK_LLVMFuzzerTestOneInput (x_sp0 cx)
    (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k nb
    (x_s1 cx - x_sp0 cx) raw ch HJ H10 ltac:(unfold MALLOC_MAX; lia) Hlv Hsp Ho16 Ho0 ltac:(lia) Hgp Htp H1 Hraw
    Hnev Hch MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HPr & Hres & Hfr & _ & Hbl & HKp & MLE & _).
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HKp by ring.
destruct (lk_after_alloc cx ly S W regsT memT md k acc rem o O ly2 S2 W2 regs2 mem2 md2 res nb _
  HB HC Hrem Hnb HJ2 HPr Hfr Hbl HKp MLE) as (HC2 & HH2 & HK2).
exact (HK ly2 S2 W2 regs2 mem2 md2 res HC2 HH2 HPr Hres HK2).
Qed.

(* ---- one call of the calloc wrapper (row 13, at the calloc trampoline) from a point where lt_core holds; the
   product m * n within YGCalloc.PRIM_MAX (64512), the row's primary-size premise ---- *)
Lemma lt_calloc_at : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O (m n : Z) raw Q,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  1 <= rem -> 0 <= m -> 0 <= n -> m * n <= 64512 -> lk_bsum O + m * n <= LIVE_LTOI ->
  getr regsT 10 = w64 m -> getr regsT 11 = w64 n -> getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2 res,
     lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT (m * n)) (rem - 1) o ((res, m * n) :: O) ->
     lt_hblk B ly2 S2 (rdW W2 mem2) res (m * n) ->
     zero_atA (rdW W2 mem2) res (m * n) ->
     aregs_preserved regsT regs2 -> getr regs2 10 = w64 res ->
     (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a) ->
     SRr SEGS W2 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_calloc)) memT (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regsT memT md k acc rem o O m n raw Q HB HC Hrem Hm Hn Hmn Hsum H10 H11 H1 Hraw Hra4 HK.
assert (Hmn0 : 0 <= m * n) by nia.
destruct (lk_call_pre cx ly S W regsT memT md k acc rem o O (m * n) HB HC Hrem ltac:(lia) Hsum)
  as (Hsp & Ho16 & Ho0 & Hom & Hgp & Htp & Hnev & Hlv & MOK).
pose proof HC as (HF & _).
pose proof (proj1 HF) as HJ.
destruct HCSTK as [Hc0 Hc1].
destruct (lk_chain cx ly S W regsT memT md k o HB HF ltac:(unfold raZ; rewrite H1; exact Hra4)) as (ch & Hch).
eapply SRr_bind.
{ exact (acalloc04_sub SEGS B LAWS pa_segs_low MT (pa_sigma SS___interceptor_trampoline_calloc) cstk (ACALLOC4 fx)
    W regsT memT STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k m n (x_s1 cx - x_sp0 cx) raw ch HJ H10 H11 Hm Hn
    ltac:(unfold MALLOC_MAX; lia) ltac:(unfold YGCalloc.PRIM_MAX; lia) Hlv Hsp Ho16 Ho0 Hc0 ltac:(lia) Hgp Htp H1 Hraw
    Hnev Hch MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HPr & Hres & Hfr & _ & Hbl & HKp & Hz & MLE & _).
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HKp by ring.
destruct (lk_after_alloc cx ly S W regsT memT md k acc rem o O ly2 S2 W2 regs2 mem2 md2 res (m * n) _
  HB HC Hrem ltac:(lia) HJ2 HPr Hfr Hbl HKp MLE) as (HC2 & HH2 & HK2).
exact (HK ly2 S2 W2 regs2 mem2 md2 res HC2 HH2 Hz HPr Hres HK2).
Qed.

End e.
End f.
End d.
