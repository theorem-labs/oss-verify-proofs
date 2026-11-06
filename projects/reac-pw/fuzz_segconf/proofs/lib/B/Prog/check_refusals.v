(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of check_refusal's ASan walk (plugin-hostd/fuzz_command, 0x87f08), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (wcb_entry) and A/AChc.v: the symbolic entry state with the GOT words of g_rec and g_quitting, the two read fields of g_rec and the word g_quitting, the shadow entries that make the three inline checks vanish, and the seed lemma; plus the transport of the read-only facts across the function's own frame writes. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_refusal_s1.v, with its module paths and module names changed; 291 of its 372 lines of code are new or changed and 152 lines of the source are left out. *)
(* The image-B port of lib/A/Prog/check_refusals.v (commit 3ecb113f2867): the ASan + UBSan walk
   of check_refusals on image B of reac-pw/fuzz_segconf (fuzz_segconf.asan-ubsan, BASE + AF_check_refusals =
   0x8736c, 64 instructions, 16-byte frame, no call, 4 inline checks of 4-byte loads, 1 UBSan trap branch), against
   check_refusals_contract (lib/B/Prog/check_refusals_c.v, the B copy of FINAL 6f783602b5e3) at
   A_check_refusals := BASE + AF_check_refusals (the listing's entry) and STK_check_refusals :=
   SegInstB.STK_check_refusals (16: the frame `addi sp,sp,-16` at 0x8736c; the code calls nothing on a path that
   returns; image B's instance file lib/B/Prog/SegInstB.v). ADAPTED: B's code is
   A's plus the UBSan alignment test at the entry (0x87374-0x87380) and with c + 0x34c8 formed before the first
   check (0x87390, 0x87398) and c + 0x34cc as a0 + 4 (0x8739c); the runs stop at the same instructions at B's
   addresses (AF + 0x64, 0x8c, 0x94).

   The UBSan trap branch: `andi a2,a0,7; andi a3,a1,3; or a2,a2,a3; bnez a2` (0x87374-0x87380) to the `unimp` at
   0x8741c. c mod 16 = 0 and mm mod 16 = 0 (check_refusals_pre) are the alignment facts (2^4) of atoms 10 and 11 in
   cr_facts, so the engine folds each `andi` to 0 (YP0m.s_and_ptr), the `or` to 0, and decides the `bnez` not taken
   inside run 1. No other branch reaches 0x8741c; it follows only `jal abort` 0x87418, on the dead abort arm.

   The four words: c->n_refusals (c + 0x34c8) and m->n_kept (m + 0x23ac) carry one atom (34), c->refused
   (c + 0x34cc) and m->refused (m + 0x2008) another (33): SegModel.check_refusals rc mc = true makes each pair the
   same value, so the two `lw` of a pair give the same symbolic word and both `bne` to the abort call (0x873d4,
   0x87404) are decided not taken inside the run. The contract does not say that c's block and m's block are
   apart, so at each moment only one of the four 4-byte words is a region of the symbolic state: the walk runs
   0x8736c .. 0x873d0 with c->refused, then 0x873d0 .. 0x873f8 with m->refused, then 0x873f8 .. 0x87400 with
   c->n_refusals, then 0x87400 .. the return with m->n_kept, and swaps the region between the runs (cr_swap). The
   bytes of each word are kept from the entry by the journal's live-block clause.

   The inline checks: the shadow entries are c's whole block [c, c + 16616) and m's [m, m + 9236) (sa_addr of the
   contract), so the engine reads each checked shadow byte as 0 (YCbn.covered at width 8) and each `bnez` to a slow
   block falls through; the error calls (errpath_load4 at 0x87430, 0x87444, 0x87454, 0x87468) are on no path.

   The post's sa_kept (window [sp - 16, sp), empty footprint): each of the four runs ends with a frame fact
   (PaDenot.kept_of_frame) over its regions, whose only write window is the stack region's [sp - 16, sp) (the one
   store, `sd ra,8(sp)` at 0x87370); the four keeps compose to the exit. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaDenot PaSB PaLibG.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase check_refusals_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma cr_nth_firstn : forall (l : list byte) n k, (k < n)%nat -> nth k (firstn n l) ZB0 = nth k l ZB0.
Proof.
intros l n. revert l. induction n as [|n IH]; intros l k Hk; [lia|].
destruct l as [|x l]; [destruct k; reflexivity|]. destruct k as [|k]; [reflexivity|].
cbn [firstn nth]. apply IH. lia.
Qed.
Lemma cr_nth_skipn : forall (l : list byte) o k, nth k (skipn o l) ZB0 = nth (o + k) l ZB0.
Proof.
intros l o. revert l. induction o as [|o IH]; intros l k; [reflexivity|].
destruct l as [|x l]; [destruct k; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

(* the 4-byte u32 field at offset off of a byte block, read through the reader *)
Lemma cr_fld : forall (rd : reader) a bs off v,
sa_bytes rd a bs -> 0 <= off -> off + 4 <= Z.of_nat (length bs) ->
seg_spec.u32_enc v (seg_spec.fldz off 4 bs) -> sa_val rd (a + off) 4 v.
Proof.
intros rd a bs off v Hb Ho Hl [Hv Hf] k Hk.
assert (Hn : nth k (seg_spec.fldz off 4 bs) ZB0 = nth (Z.to_nat off + k) bs ZB0).
{ unfold seg_spec.fldz, seg_spec.fld. rewrite cr_nth_firstn by lia. apply cr_nth_skipn. }
specialize (Hb (Z.to_nat off + k)%nat ltac:(lia)).
replace (a + Z.of_nat (Z.to_nat off + k)) with (a + off + Z.of_nat k) in Hb by lia.
rewrite Hb, <- Hn, Hf. f_equal.
unfold OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small v) by lia.
unfold le_byte. rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat 4))) by (cbn; lia).
do 4 (destruct k as [|k]; [cbn [nth Z_to_le_bytes]; rewrite Z_to_bv_unsigned; unfold bv_wrap;
  change (bv_modulus 8) with 256; rewrite ?Z.shiftr_shiftr by lia; reflexivity|]).
lia.
Qed.

(* a field read through the world's view is the same field of the restricted memory (fuzz_command's
   cr_val_of_aval) *)
Lemma cr_val_of_sa : forall segs H (mem : word -> option byte) a n v,
sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.

Definition CR_SB : Z := 0x7fff8000.
Definition CRx : sv := SOff 32 0.
Definition CRspan : Z * Z := (CR_SB, CR_SB + 2 ^ 44 - 1).
(* the highest c and m their blocks allow (sa_addr's amem_range: the block ends below kHighMemEnd) *)
Definition CR_CHI : Z := 2 ^ 47 - 1 - seg_spec.SEG_C_SIZE.
Definition CR_MHI : Z := 2 ^ 47 - 1 - seg_spec.SEG_M_SIZE.
(* atoms: 10 c and 11 m (the entry's a0, a1), 32 the shadow base, 33 the refused count, 34 the refusal count *)
Definition cr_rB : YP09.region :=
YP09.mkRegion (Some 10%nat) seg_spec.RC_REFUSED (seg_spec.RC_REFUSED + 4) 0 0
  [YP09.mkChunk seg_spec.RC_REFUSED (CVal 4 (SOff 33 0))].
Definition cr_rC : YP09.region :=
YP09.mkRegion (Some 11%nat) seg_spec.MC_REFUSED (seg_spec.MC_REFUSED + 4) 0 0
  [YP09.mkChunk seg_spec.MC_REFUSED (CVal 4 (SOff 33 0))].
Definition cr_rA : YP09.region :=
YP09.mkRegion (Some 10%nat) seg_spec.RC_NREF (seg_spec.RC_NREF + 4) 0 0
  [YP09.mkChunk seg_spec.RC_NREF (CVal 4 (SOff 34 0))].
Definition cr_rD : YP09.region :=
YP09.mkRegion (Some 11%nat) seg_spec.MC_NKEPT (seg_spec.MC_NKEPT + 4) 0 0
  [YP09.mkChunk seg_spec.MC_NKEPT (CVal 4 (SOff 34 0))].
Definition cr_regions : smem := [ stack_region 16; cr_rB; got_regionP; bcell_regionP 32 ].
Definition cr_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 0 CR_CHI 4); (11%nat, mkAF 0 CR_MHI 4);
  (32%nat, mkAF CR_SB CR_SB 0); (33%nat, mkAF 0 (2^32-1) 0); (34%nat, mkAF 0 (2^32-1) 0) ] [] [].
Definition ss_cr : sstate := mkSS AF_check_refusals sr_atoms cr_regions None cr_facts.
Definition cr_SH : list shent := [mkSHE 10 0 seg_spec.SEG_C_SIZE; mkSHE 11 0 seg_spec.SEG_M_SIZE].
Definition cr_extra (vR vN : Z) : list word := map (Z_to_bv 64) [CR_SB; vR; vN].

(* the range [q, q + n) lies off the shadow band [CR_SB, CR_SB + 2^44) *)
Definition cr_app (q n : Z) : Prop := forall x, q <= x < q + n -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Lemma cr_app_of_amem : forall q n, amem_range q n -> cr_app q n.
Proof. intros q n Ha x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ha. unfold SHADOW_OFF. lia. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the symbolic state after a run, with its one heap word swapped: the stack region stays, the read-only and the
   other word's regions go *)
Lemma cr_swap : forall segs val E ss ms r0 rest rx,
st_ok_pi segs val E ss ms -> ss_mem ss = r0 :: rest ->
regions_wf [r0; rx] = true -> region_ok segs E (ms_mem ms) rx -> extent_disjoint E r0 rx ->
st_ok_pi segs val E (mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) [r0; rx] (ss_resv ss) (ss_facts ss)) ms.
Proof using.
intros segs val E ss ms r0 rest rx HS Hm Hwf Hrx Hd.
unfold st_ok_pi, abs_ss, setpc, st_ok in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hw & Hok & Hpd) & H9).
rewrite Hm in Hok. pose proof (Forall_inv Hok) as Hr0.
repeat (split; [assumption|]). split; [|exact H9].
split; [exact Hwf|]. split; [constructor; [exact Hr0 | constructor; [exact Hrx | constructor]]|].
cbn [pairwise_disjoint all_disjoint]. tauto.
Qed.

Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition cr_E (regs : bvmap 5 word) (vR vN : Z) : env := Eimg (Ereg regs (cr_extra vR vN)).
Section e.
Variable B : asyms.
(* the record's facts: the allocator laws (live blocks, their shadow, the const cells of the shadow base), and the
   listing's link from its objects A_OBJ 0 / A_OBJ 12 to the record's GOT word and shadow-base cell *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.

(* a word inside a live block keeps its bytes along the walk: the journal's live-block clause (FP = []) *)
Lemma cr_heap_kept : forall STK sp0 ly S (W : world SEGS) mem md mem' md' k q n a w v,
ajournal SEGS B STK sp0 [] ly S W mem md [] ly S W mem' md' k ->
sa_heap B ly S q n -> q <= a -> a + Z.of_nat w <= q + n ->
sa_val (rdW W mem) a w v -> sa_val (rdW W mem') a w v.
Proof using.
intros STK sp0 ly S W mem md mem' md' k q n a w v HJ (b & mb & Hin & Hb1 & Hb2) Hqa Haw Hv.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (Hr : mb <= req_size mb) by (unfold req_size; destruct (Z.eqb_spec mb 0); lia).
intros i Hi. specialize (Hv i Hi).
replace (a + Z.of_nat i) with (b + (a + Z.of_nat i - b)) in * by lia.
rewrite (F2 b mb (a + Z.of_nat i - b) Hin Hin ltac:(lia) ltac:(intros X; exact (inFP_nil _ X))). exact Hv.
Qed.

(* a live block lies above 0x10000-or-past-the-image, below the stack window and off the shadow band *)
Lemma cr_heap_place : forall ly S (W : world SEGS) mem md regs q n,
AR SEGS B ly S W mem md -> astk_ok SegInstB.STK_check_refusals ly (spZ regs) -> sa_heap B ly S q n -> 0 <= n ->
4096 <= q /\ q + n <= spZ regs - SegInstB.STK_check_refusals /\ (q + n <= 0x10000 \/ kImgEnd <= q).
Proof using LAWS.
intros ly S W mem md regs q n HAR Hstk (b & mb & Hin & Hb1 & Hb2) Hn.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (al_blocks _ _ LAWS ly S W mem md b mb HAR Hin) as (H16 & H4096 & Hc & Hia & Hpres & Hnd & Hk).
pose proof (blk_off_imgP B ly S W mem md b mb HAR Hin) as Hoff. unfold off_img in Hoff.
assert (Hr : mb <= req_size mb) by (unfold req_size; destruct (Z.eqb_spec mb 0); lia).
unfold kImgEnd. lia.
Qed.

Lemma cr_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem ly S md c mm vR vN,
AR SEGS B ly S W mem md ->
astk_ok SegInstB.STK_check_refusals ly (spZ regs) ->
(forall a, spZ regs - SegInstB.STK_check_refusals <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 c -> getr regs 11 = w64 mm ->
0 <= c <= CR_CHI -> c mod 16 = 0 -> 0 <= mm <= CR_MHI -> mm mod 16 = 0 ->
0 <= vR < 2 ^ 32 -> 0 <= vN < 2 ^ 32 ->
sa_val (rdW W mem) (c + seg_spec.RC_REFUSED) 4 vR ->
c + seg_spec.SEG_C_SIZE <= spZ regs - SegInstB.STK_check_refusals ->
(c + seg_spec.SEG_C_SIZE <= 0x10000 \/ kImgEnd <= c) ->
range_addressable (rdW W mem) SHADOW_OFF c seg_spec.SEG_C_SIZE -> cr_app c seg_spec.SEG_C_SIZE ->
range_addressable (rdW W mem) SHADOW_OFF mm seg_spec.SEG_M_SIZE -> cr_app mm seg_spec.SEG_M_SIZE ->
st_ok_pi SEGS VAL (cr_E regs vR vN) ss_cr
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_refusals)) mem (seg_rom SEGS)))
/\ sh_ok SEGS CRx cr_SH (cr_E regs vR vN) (mrestrict (w_H W) mem).
Proof using LAWS TL.
intros W regs mem ly S md c mm vR vN HAR Hstk Hpres H10 H11 Rc Hc16 Rm Hm16 RvR RvN FB Hcs Hco ZC AC ZM AM.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pal_got_cell B TL) as HGC.
pose proof (pa_obj_img 0 ltac:(lia)) as HO0. pose proof (pa_obj_img 12 ltac:(lia)) as HO12.
unfold CR_CHI, CR_MHI, SegInstB.STK_check_refusals, kImgEnd, seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *.
set (E := cr_E regs vR vN).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold cr_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cr_extra vR vN)) n)
  by (intros n Hn; subst E; unfold cr_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 mm) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 CR_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 vR) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 vN) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold cr_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold cr_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 0)) as RV0. pose proof (pa_val_range (A_OBJ 12)) as RV12.
split.
- unfold ss_cr. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold cr_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cr_regions, cr_rB, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB 10%nat c E10) by lia. unfold seg_spec.RC_REFUSED. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ c 0x34cc 4 _ vR); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (cr_val_of_sa SEGS _ mem _ 4 vR FB).
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) CR_SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold CR_SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + apply pairwise_disjoint_of_extents. unfold cr_regions, cr_rB, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat c E10), (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0), (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia.
    cbn [base_val]. rewrite Usp. unfold seg_spec.RC_REFUSED.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 Hstk0 Hcs Hco HGC HO0 HO12 Rc. clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [cr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E11, E32, E33, E34, !unsigned_lit_small by (unfold CR_SB; lia).
    unfold CR_SB, CR_CHI, CR_MHI, seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil Hal16 C1 Hstk0 Rc Rm Hc16 Hm16 RvR RvN. clear. intros.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
- unfold sh_ok, cr_SH. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W) mem E CRx 10 c 16616 c 0 16616 ZC).
    * unfold U, CRx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold CR_SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    * lia. * lia.
    * intros x Hx. apply AC. cbn in Hx. lia.
  + apply (shent_ok_of_range SEGS (w_H W) mem E CRx 11 mm 9236 mm 0 9236 ZM).
    * unfold U, CRx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold CR_SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    * lia. * lia.
    * intros x Hx. apply AM. cbn in Hx. lia.
Qed.

(* the region of one heap word at a later state of the walk: its bytes kept by the journal, apart from the stack
   region by the block's place *)
Lemma cr_word_region : forall STK sp0 ly S (W : world SEGS) mem md mem' md' k E (nb : nat) base q n off sv v,
ajournal SEGS B STK sp0 [] ly S W mem md [] ly S W mem' md' k ->
sa_heap B ly S q n -> bv_unsigned (ew E nb) = base -> q <= base + off -> base + off + 4 <= q + n ->
0 <= base + off -> base + off + 4 <= 2 ^ 64 ->
sv_denot E sv = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
sa_val (rdW W mem) (base + off) 4 v ->
region_ok SEGS E (mrestrict (w_H W) mem') (YP09.mkRegion (Some nb) off (off + 4) 0 0 [YP09.mkChunk off (CVal 4 sv)]).
Proof using.
intros STK sp0 ly S W mem md mem' md' k E nb base q n off sv v HJ HH Hb Hq1 Hq2 Hlo Hhi Hsv Hv Hval.
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ base off 4 sv v Hsv ltac:(cbn; lia) ltac:(cbn; lia)).
apply cr_val_of_sa. exact (cr_heap_kept STK sp0 ly S W mem md mem' md' k q n (base + off) 4 v HJ HH Hq1 Hq2 Hval).
Qed.

(* what a run keeps: every byte outside [lo, hi), when each window of the run's regions lies inside [lo, hi)
   (kept_of_frame over the run's frame fact HFr) *)
Ltac cr_keep HFr K lo hi Usp :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m2 a = aview SEGS H m1 a)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => lo <= x < hi) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
                [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; cbv beta; lia|]);
        destruct Hin
      | exact Hx0 | exact Hn0 ]) end.

Theorem check_refusals_walk : check_refusals_contract SEGS B (BASE + AF_check_refusals) SegInstB.STK_check_refusals.
Proof using LAWS TL.
pose proof (paj_run_to B LAWS) as RUNTO. pose proof (paj_run B LAWS) as RUN.
pose proof (paj_ret_at (PL := PL_seg) (PI := PI)) as RET.
unfold check_refusals_contract, check_refusals_pre.
intros ly S W regs mem md ch c mm rcs mcs HPRE H10 Rc0 H11 Rm0
  (Hc0 & Hc16 & (bc & BC & HC) & HHc & HAc & Hm0 & Hm16 & (bm & BM & HM) & HHm & HAm & Hok) HEV.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
(* the four words: u32 fields of rconf_enc / mconf_encp, equal in pairs by SegModel.check_refusals *)
destruct HC as (HLc & _ & _ & _ & _ & _ & HNc & HRc & _).
destruct HM as (HLm & _ & _ & _ & _ & HRm & _ & _ & _ & HNm & _).
unfold SegModel.check_refusals in Hok. apply andb_prop in Hok as [Href Hlen].
apply Z.eqb_eq in Href. apply Nat.eqb_eq in Hlen.
rewrite <- Href in HRm. rewrite <- Hlen in HNm.
set (vR := SegModel.rc_refused rcs) in *. set (vN := Z.of_nat (length (SegModel.rc_refusal rcs))) in *.
assert (RvR : 0 <= vR < 2 ^ 32) by exact (proj1 HRc).
assert (RvN : 0 <= vN < 2 ^ 32) by exact (proj1 HNc).
unfold seg_spec.SEG_C_SIZE in HLc. unfold seg_spec.SEG_M_SIZE in HLm.
pose proof (cr_fld _ c bc seg_spec.RC_NREF vN BC ltac:(unfold seg_spec.RC_NREF; lia) ltac:(unfold seg_spec.RC_NREF; lia) HNc) as FA.
pose proof (cr_fld _ c bc seg_spec.RC_REFUSED vR BC ltac:(unfold seg_spec.RC_REFUSED; lia) ltac:(unfold seg_spec.RC_REFUSED; lia) HRc) as FB.
pose proof (cr_fld _ mm bm seg_spec.MC_REFUSED vR BM ltac:(unfold seg_spec.MC_REFUSED; lia) ltac:(unfold seg_spec.MC_REFUSED; lia) HRm) as FC.
pose proof (cr_fld _ mm bm seg_spec.MC_NKEPT vN BM ltac:(unfold seg_spec.MC_NKEPT; lia) ltac:(unfold seg_spec.MC_NKEPT; lia) HNm) as FD.
clear HNc HRc HRm HNm BC BM HLc HLm.
(* the blocks: where they lie and their shadow *)
destruct HAc as (Hc0' & Hc63 & AMc & ZC & _). destruct HAm as (Hm0' & Hm63 & AMm & ZM & _).
pose proof (cr_app_of_amem _ _ AMc) as AC. pose proof (cr_app_of_amem _ _ AMm) as AM.
assert (Rc : 0 <= c <= CR_CHI) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AMc; unfold CR_CHI, seg_spec.SEG_C_SIZE in *; lia).
assert (Rm : 0 <= mm <= CR_MHI) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AMm; unfold CR_MHI, seg_spec.SEG_M_SIZE in *; lia).
destruct (cr_heap_place ly S W mem md regs c seg_spec.SEG_C_SIZE HAR Hstk HHc ltac:(unfold seg_spec.SEG_C_SIZE; lia))
  as (Hc4096 & Hcs & Hco).
destruct (cr_heap_place ly S W mem md regs mm seg_spec.SEG_M_SIZE HAR Hstk HHm ltac:(unfold seg_spec.SEG_M_SIZE; lia))
  as (Hm4096 & Hms & Hmo).
destruct (cr_entry W regs mem ly S md c mm vR vN HAR Hstk Hpres H10 H11 Rc Hc16 Rm Hm16 RvR RvN FB Hcs Hco ZC AC ZM AM)
  as [HS SHOK].
pose proof (ajournal_init SEGS B SegInstB.STK_check_refusals [] ly S W regs mem md ch HPRE) as HJ.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (cr_E regs vR vN) n = ew (Ereg regs (cr_extra vR vN)) n)
  by (intros n Hn; unfold cr_E; apply Eimg_low; exact Hn).
assert (HED : ed (cr_E regs vR vN) = ed (Ereg regs (cr_extra vR vN))) by reflexivity.
assert (HEI : img_env VAL A_LIM (cr_E regs vR vN)) by (unfold cr_E; apply Eimg_env).
remember (cr_E regs vR vN) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E1 : ew E 1 = getr regs 1) by (apply EEo; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 mm) by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
assert (E33 : ew E 33 = Z_to_bv 64 vR) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 vN) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (U10 : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = mm) by (rewrite E11; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (cr_extra vR vN)) E).
{ split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | exact HED]. }
clear HE EL HED.
unfold SegInstB.STK_check_refusals, CR_CHI, CR_MHI, seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *.
unfold cfg_at, w64.
(* run 1, 0x8736c .. 0x873d0: the frame (ra at sp - 8), the UBSan test `andi a2,a0,7; andi a3,a1,3; or; bnez a2`
   (0x87374-0x87380: atoms 10 and 11 are 16-aligned, so a2 is 0 and the branch to the `unimp` at 0x8741c is decided
   not taken), the shadow base through the GOT word 0xa3210 and the cell 0xac7b8, a0 := c + 0x34c8,
   a2 := c + 0x34cc, its check (vanishes: c's shadow entry), m + 0x2008, its check (vanishes), a2 := c->refused *)
paj_run_to_tok RUNTO HS HJ SHOK CRspan (AF_check_refusals + 0x64).
{ awr_ok_tac. exact Usp. }
cr_keep HFr K1 (spZ regs - 16) (spZ regs) Usp. clear HF HFr HG.
(* the swap: m->refused in place of c->refused (and of the GOT word and the cell, read once) *)
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  let r0 := eval vm_compute in (hd (stack_region 0) (ss_mem ss)) in
  let rest := eval vm_compute in (tl (ss_mem ss)) in
  pose proof (cr_swap SEGS VAL E ss _ r0 rest cr_rC HS eq_refl ltac:(vm_compute; reflexivity)) as HSw end.
specialize (HSw (cr_word_region _ _ ly S W mem md _ _ _ E 11 mm mm 9236 seg_spec.MC_REFUSED (SOff 33 0) vR HJ HHm U11
  ltac:(unfold seg_spec.MC_REFUSED; lia) ltac:(unfold seg_spec.MC_REFUSED; lia) ltac:(unfold seg_spec.MC_REFUSED; lia)
  ltac:(unfold seg_spec.MC_REFUSED; lia)
  ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) RvR FC)).
specialize (HSw ltac:(unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val cr_rC]; rewrite Usp, U11;
  unfold seg_spec.MC_REFUSED; lia)).
cbn [ss_pc ss_regs ss_fregs ss_resv ss_facts] in HSw. clear HS. rename HSw into HS.
(* run 2, 0x873d0 .. 0x873f8: a4 := m->refused, `bne a2, a4` decided not taken (one atom); the check of c + 0x34c8
   (vanishes), m + 0x23ac and its check (vanishes) *)
paj_run_to_tok RUNTO HS HJ SHOK CRspan (AF_check_refusals + 0x8c).
{ awr_ok_tac. exact Usp. }
cr_keep HFr K2 (spZ regs - 16) (spZ regs) Usp. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  let r0 := eval vm_compute in (hd (stack_region 0) (ss_mem ss)) in
  let rest := eval vm_compute in (tl (ss_mem ss)) in
  pose proof (cr_swap SEGS VAL E ss _ r0 rest cr_rA HS eq_refl ltac:(vm_compute; reflexivity)) as HSw end.
specialize (HSw (cr_word_region _ _ ly S W mem md _ _ _ E 10 c c 16616 seg_spec.RC_NREF (SOff 34 0) vN HJ HHc U10
  ltac:(unfold seg_spec.RC_NREF; lia) ltac:(unfold seg_spec.RC_NREF; lia) ltac:(unfold seg_spec.RC_NREF; lia)
  ltac:(unfold seg_spec.RC_NREF; lia)
  ltac:(cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) RvN FA)).
specialize (HSw ltac:(unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val cr_rA]; rewrite Usp, U10;
  unfold seg_spec.RC_NREF; lia)).
cbn [ss_pc ss_regs ss_fregs ss_resv ss_facts] in HSw. clear HS. rename HSw into HS.
(* run 3, 0x873f8 .. 0x87400: a0 := c->n_refusals, the `bnez` of m + 0x23ac's check falls through *)
paj_run_to_tok RUNTO HS HJ SHOK CRspan (AF_check_refusals + 0x94).
{ awr_ok_tac. exact Usp. }
cr_keep HFr K3 (spZ regs - 16) (spZ regs) Usp. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  let r0 := eval vm_compute in (hd (stack_region 0) (ss_mem ss)) in
  let rest := eval vm_compute in (tl (ss_mem ss)) in
  pose proof (cr_swap SEGS VAL E ss _ r0 rest cr_rD HS eq_refl ltac:(vm_compute; reflexivity)) as HSw end.
specialize (HSw (cr_word_region _ _ ly S W mem md _ _ _ E 11 mm mm 9236 seg_spec.MC_NKEPT (SOff 34 0) vN HJ HHm U11
  ltac:(unfold seg_spec.MC_NKEPT; lia) ltac:(unfold seg_spec.MC_NKEPT; lia) ltac:(unfold seg_spec.MC_NKEPT; lia)
  ltac:(unfold seg_spec.MC_NKEPT; lia)
  ltac:(cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) RvN FD)).
specialize (HSw ltac:(unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val cr_rD]; rewrite Usp, U11;
  unfold seg_spec.MC_NKEPT; lia)).
cbn [ss_pc ss_regs ss_fregs ss_resv ss_facts] in HSw. clear HS. rename HSw into HS.
(* run 4, 0x87400 .. 0x87410: a1 := m->n_kept, `bne a0, a1` decided not taken (one atom); ra back from sp + 8,
   sp += 16, stopped at the `ret` *)
paj_run_tok RUN HS HJ SHOK CRspan.
{ awr_ok_tac. exact Usp. }
cr_keep HFr K4 (spZ regs - 16) (spZ regs) Usp. clear HF HFr HG.
prreg HS (1%bv : bv 5) F1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split; [rewrite F1, E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (cr_extra vR vN) HS); [exact HAE | vm_compute; reflexivity]|].
split.
{ intros a Ha Hn _. exact (eq_trans (K4 a Ha Hn) (eq_trans (K3 a Ha Hn) (eq_trans (K2 a Ha Hn) (K1 a Ha Hn)))). }
unfold sa_noalloc. split; [apply Permutation_refl|]. split; [reflexivity|].
exists (st_fs S). destruct S; reflexivity.
Qed.
End e.
End f.
End d.
Print Assumptions check_refusals_walk.
About check_refusals_walk.
