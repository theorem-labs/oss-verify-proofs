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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 947 of its 1060 lines of code are new or changed and 340 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of m_refuse on fuzz_segconf.asan (image A, entry 0x877d0, 308 bytes,
   77 instructions, a 48-byte frame, no side-stack frame): m_refuse_contract of lib/A/Prog/m_refuse_c.v at image A's
   numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the entry, SRr of apost_baseF at the return,
   over `Context {PI : PAImg seg_listing}`). New text; the patterns are the released walks' (origin/ossv/recipes
   501c0d516c69: fuzz_command lib/A/Prog/xstrdup.v and rec_code_declared.v for the seed and the runs,
   sup_chain_s5.v and check_reply_s4.v for the step through the snprintf wrapper) and the pilot
   lib/A/Prog/reac_box_catalogueA.v.
   The statement's image numbers: the entry BASE + AF_m_refuse and the snprintf trampoline
   SIGMA SS___interceptor_trampoline_snprintf (listing terms); STK_m_refuse, RLO_A / RHI_A, seg_litA_fz, gotwA /
   guardA from lib/A/Prog/SegInstA.v.
   The code, from the listing (dis/m_refuse.fuzz_segconf.asan.s):
   - entry to 0x87824: the frame stores, the shadow base through the GOT word (listing object 0 -> object 12), the
     instrumented check of n_kept at c + 0x23ac (a load of the shadow byte at ((c + 0x23ac) >> 3) + the shadow base
     and a compare): the shadow entry mr_SH makes the byte 0, so the error path (a call of errpath_load4) is not
     reached; lw n_kept; blt 7, n_kept.
   - n_kept = 8 (7 < n_kept): 0x87888 to the ret: the instrumented check of refused (c + 0x2008), refused + 1.
   - n_kept <= 7: a0 = kept[n_kept] = c + 0x200c + 112 n_kept, a3 = c->reading (c + 0x23b4), blez line:
     line = 0: snprintf(a0, 112, "%s: " (.str.7, object 28), reading) at 0x87870, return to 0x87874;
     0 < line: snprintf(a0, 112, "%s:%d: " (.str.6, object 27), reading, line) at 0x8785c, return to 0x87860,
     j 0x87874. The call is stepped by mr_snp (RtFormat.asnprintf_realizes through PaFx.v's aj_art_own_atF and
     srr_art_postF_of_pf); the walk goes on at the FP state the wrapper returns (srr_after_artF).
   - 0x87874 to the ret: the instrumented check of n_kept again, n_kept + 1, then refused + 1 as above.
   The block after the call: m_refuseA_enc.v (mr_enc_lt8 / mr_enc_ge8, the text bridge mr_pf_line / mr_pf_noline /
   mr_sn_text). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q YN2e YO0a YO0b YO0c YN0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaNoChain PaArt PaArtOwn PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtPFCmd RtPFShared RtPFPf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_refuse_c m_refuseA_enc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================================== byte facts, no state ===================================== *)
Lemma mr_le_byte_bv : forall v w k, (k < w)%nat ->
Z_to_bv 8 (YG0f.le_byte v w k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
intros v w k Hk. apply bv_eq. rewrite !Z_to_bv_unsigned.
change (bv_wrap 8 ?x) with (x mod 2 ^ 8).
apply Z.bits_inj'. intros i Hi. rewrite !YO0a.testbit_mod_pow2 by lia.
destruct (i <? 8) eqn:E; [|reflexivity]. cbn [andb]. apply Z.ltb_lt in E.
unfold YG0f.le_byte. change 256 with (2 ^ 8). rewrite YO0a.testbit_mod_pow2 by lia.
rewrite (proj2 (Z.ltb_lt i 8)) by lia. cbn [andb].
rewrite !Z.shiftr_spec by lia. rewrite YO0a.testbit_mod_pow2 by lia.
replace (i + 8 * Z.of_nat k <? 8 * Z.of_nat w) with true; [reflexivity|].
symmetry. apply Z.ltb_lt. nia.
Qed.
(* the 4 bytes of a u32 field through a reader that holds the block's bytes *)
Lemma mr_val4 : forall (rd : reader) c bs off v, sa_bytes rd c bs -> seg_spec.u32_enc v (seg_spec.fldz off 4 bs) ->
0 <= off -> off + 4 <= Z.of_nat (length bs) -> sa_val rd (c + off) 4 v.
Proof.
intros rd c bs off v HB [Hv Hf] Ho Hl k Hk.
assert (Hi : (Z.to_nat off + k < length bs)%nat) by lia.
replace (c + off + Z.of_nat k) with (c + Z.of_nat (Z.to_nat off + k)) by lia.
rewrite (HB _ Hi). f_equal.
assert (Hn : nth (Z.to_nat off + k) bs ZB0 = nth k (seg_spec.fldz off 4 bs) ZB0).
{ unfold seg_spec.fldz, seg_spec.fld. rewrite nth_firstn. change (Z.to_nat 4) with 4%nat.
  replace (k <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk).
  rewrite nth_skipn. reflexivity. }
rewrite Hn, Hf. unfold Mem.le4.
rewrite (nth_error_nth _ _ _ (YN2e.Z_to_le_bytes_nth 4 _ k Hk)).
replace (bv_unsigned (Z_to_bv 64 v)) with v by (rewrite unsigned_lit_small by lia; reflexivity).
rewrite <- (mr_le_byte_bv v 4 k Hk). rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. apply Z.mod_small. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
(* a reader's sa_val is val_mem of the restricted memory *)
Lemma mr_val_mem : forall segs H mem a n v, sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v HV k Hk. destruct (aview_byte segs H mem _ _ (HV k Hk)) as (b & Hb & Hv & _).
rewrite Hb. f_equal. rewrite <- (Z_to_bv_bv_unsigned _ b) at 1. f_equal. exact (eq_sym Hv).
Qed.
(* the footprint's cells *)
Lemma mr_inFP_rf : forall c mc a, c + seg_spec.MC_REFUSED <= a < c + seg_spec.MC_REFUSED + 4 -> inFP (m_refuse_W c mc) a.
Proof.
intros c mc a Ha. exists (c + seg_spec.MC_REFUSED, c + seg_spec.MC_REFUSED + 4). split; [|exact Ha].
unfold m_refuse_W. apply in_or_app. right. left. reflexivity.
Qed.
Lemma mr_inFP_nk : forall c mc a, Z.of_nat (length (mc_kept mc)) < 8 ->
c + seg_spec.MC_NKEPT <= a < c + seg_spec.MC_NKEPT + 4 -> inFP (m_refuse_W c mc) a.
Proof.
intros c mc a H8 Ha. exists (c + seg_spec.MC_NKEPT, c + seg_spec.MC_NKEPT + 4). split; [|exact Ha].
unfold m_refuse_W. apply in_or_app. left. rewrite (proj2 (Z.ltb_lt _ _) H8). right. left. reflexivity.
Qed.
Lemma mr_inFP_kept : forall c mc a, Z.of_nat (length (mc_kept mc)) < 8 ->
seg_spec.kept_addr c (length (mc_kept mc)) <= a < seg_spec.kept_addr c (length (mc_kept mc)) + seg_spec.MC_KEPT_LEN ->
inFP (m_refuse_W c mc) a.
Proof.
intros c mc a H8 Ha. exists (seg_spec.kept_addr c (length (mc_kept mc)),
  seg_spec.kept_addr c (length (mc_kept mc)) + seg_spec.MC_KEPT_LEN). split; [|exact Ha].
unfold m_refuse_W. apply in_or_app. left. rewrite (proj2 (Z.ltb_lt _ _) H8). left. reflexivity.
Qed.
Lemma mr_set_fs_id : forall S, S = set_fs (st_fs S) S.
Proof. intros S. destruct S. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* atoms: 0..31 the registers at the entry, 32 the shadow base, 33 n_kept, 34 refused *)
Definition mrBx : sv := SOff 32 0.
(* refused (c + 0x2008, written) and n_kept (c + 0x23ac, read-only until the snprintf call returns) *)
Definition mr_rf : YP09.region :=
YP09.mkRegion (Some 10%nat) 0x2008 0x200c 0x2008 0x200c [YP09.mkChunk 0x2008 (CVal 4 (SOff 34 0))].
Definition mr_nk_ro : YP09.region :=
YP09.mkRegion (Some 10%nat) 0x23ac 0x23b0 0x23ac 0x23ac [YP09.mkChunk 0x23ac (CVal 4 (SOff 33 0))].
(* n_kept once snprintf has returned on the n_kept < 8 path: written by n_kept++ (0x87884) *)
Definition mr_nk_w : YP09.region :=
YP09.mkRegion (Some 10%nat) 0x23ac 0x23b0 0x23ac 0x23b0 [YP09.mkChunk 0x23ac (CVal 4 (SOff 33 0))].
Definition mr_regions : smem := [ stack_region 48; got_regionP; bcell_regionP 32; mr_rf; mr_nk_ro ].
Definition mr_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, PTR 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 8 0);
          (34%nat, mkAF 0 4294967294 0) ] [] [].
Definition mr_ss0 : sstate := mkSS AF_m_refuse sr_atoms mr_regions None mr_facts.
(* the shadow entries: refused's and n_kept's granules (covered asks the 8 bytes from the checked address) *)
Definition mr_SH : list shent := [ mkSHE 10 0x2008 0x2010; mkSHE 10 0x23ac 0x23b4 ].
Definition mr_extra (n r : Z) : list word := [Z_to_bv 64 SB; Z_to_bv 64 n; Z_to_bv 64 r].
Definition mrE (regs : bvmap 5 word) (n r : Z) : env := Eimg (Ereg regs (mr_extra n r)).
Section e.
Variable B : asyms.
#[local] Notation RLO := SegInstA.RLO_A.
#[local] Notation RHI := SegInstA.RHI_A.
Hypothesis TL : PALib B.
Hypothesis VOBJS : seg_val_objs.
(* the snprintf wrapper (the interceptor-layer owner's interface row 4), at every FP state *)
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
@asnprintf_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_snprintf) SegInstA.gotwA SegInstA.guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

(* where the mconf block lies *)
Lemma mr_c_where : forall ly S W regs mem md ch c,
afn_pre SEGS B SegInstA.STK_m_refuse ly S W regs mem md ch -> c mod 16 = 0 -> sa_heap B ly S c seg_spec.SEG_M_SIZE ->
exists b m, In (b, m) (ablocks B ly S) /\ b <= c /\ c + seg_spec.SEG_M_SIZE <= b + req_size m /\
4096 <= c /\ c + seg_spec.SEG_M_SIZE + 12 <= alloc_ceiling /\ (c + seg_spec.SEG_M_SIZE <= 0x10000 \/ kImgEnd <= c) /\
(c + seg_spec.SEG_M_SIZE <= kLowShadowBeg \/ kHighMemBeg <= c) /\
(forall a, c <= a < c + seg_spec.SEG_M_SIZE -> apresent (w_H W) mem a /\ ~ aowned B ly S a).
Proof.
intros ly S W regs mem md ch c HPRE Hc16 (b & m & Hin & Hb1 & Hb2).
pose proof HPRE as (HAR & _).
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hm).
pose proof (blk_off_imgP B ly S W mem md b m HAR Hin) as Himg.
pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2].
pose proof (@YG0f.ASAN_CEIL_range _) as [CR1 CR2]. unfold YG0f.ASAN_CEIL in CR1, CR2.
assert (Ec : c = 16 * (c / 16)) by (pose proof (Z.div_mod c 16 ltac:(lia)) as Hd; rewrite Hc16 in Hd; lia).
assert (Ea : alloc_ceiling = 4096 * (alloc_ceiling / 4096))
  by (pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as Hd; rewrite CR2 in Hd; lia).
unfold in_app in Hbapp. unfold off_img in Himg. unfold seg_spec.SEG_M_SIZE in *.
exists b, m. split; [exact Hin|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [unfold kImgEnd; lia|]. split; [lia|].
intros a Ha. apply Hbpres. lia.
Qed.

(* the entry state *)
Lemma mr_entry : forall ly S W regs mem md ch c n r,
afn_pre SEGS B SegInstA.STK_m_refuse ly S W regs mem md ch ->
getr regs 10 = w64 c -> c mod 16 = 0 -> sa_heap B ly S c seg_spec.SEG_M_SIZE ->
sa_addr (rdW W mem) c seg_spec.SEG_M_SIZE ->
sa_val (rdW W mem) (c + 0x23ac) 4 n -> 0 <= n <= 8 ->
sa_val (rdW W mem) (c + 0x2008) 4 r -> 0 <= r <= 4294967294 ->
st_ok_pi SEGS VAL (mrE regs n r) mr_ss0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_m_refuse)) mem (seg_rom SEGS)))
/\ sh_ok SEGS mrBx mr_SH (mrE regs n r) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch c n r HPRE H10 Hc16 HHEAP HADDR VNK Hn VRF Hr.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HSTK : SegInstA.STK_m_refuse = 8240) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (mr_c_where ly S W regs mem md ch c HPRE Hc16 HHEAP)
  as (b & m & Hin & Hb1 & Hb2 & Hc4096 & Hcceil & Hcimg & Hcband & Hcpres).
destruct HADDR as (_ & _ & _ & HRA & _).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
unfold kImgEnd, seg_spec.SEG_M_SIZE in *.
rewrite restrict_mkst_fx.
set (E := mrE regs n r).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (mr_extra n r)) k)
by (intros k Hk; subst E; unfold mrE; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E0o : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (subst E; unfold mrE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
by (subst E; unfold mrE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; lia).
assert (USB : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (Un : bv_unsigned (ew E 33) = n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (Ur : bv_unsigned (ew E 34) = r) by (rewrite E34; apply unsigned_lit_small; lia).
assert (UBx : U E mrBx = SHADOW_OFF).
{ unfold mrBx. rewrite U_SOff, E32, Z.add_0_r, unsigned_lit_small by (unfold SB; lia).
  rewrite zcanon_id by (unfold SB, M64; lia). reflexivity. }
assert (U10 : U E (SOff 10 0) = c).
{ rewrite U_SOff, E10, Z.add_0_r, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
split.
- unfold mr_ss0. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold mr_regions, stack_region, got_regionP, bcell_regionP, mr_rf, mr_nk_ro.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite HSTK. lia.
    * cbn [base_val]. rewrite E0o, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 0)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * cbn [base_val]. rewrite E12, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 mrBx SB);
      [cbn [sv_denot mrBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * cbn [base_val]. rewrite Uc. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hcpres (c + o) ltac:(lia)))|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ c 0x2008 4 (SOff 34 0) r);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (mr_val_mem SEGS (w_H W) mem _ 4 r VRF).
    * cbn [base_val]. rewrite Uc. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ c 0x23ac 4 (SOff 33 0) n);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (mr_val_mem SEGS (w_H W) mem _ 4 n VNK).
  + apply pairwise_disjoint_of_extents.
    unfold mr_regions, stack_region, got_regionP, bcell_regionP, mr_rf, mr_nk_ro, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
    rewrite Uc, Usp, E0o, E12, !unsigned_lit_small
      by (pose proof (pa_val_range (A_OBJ 0)); pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite HSTK in Hslo.
    destruct Hcimg as [Hci | Hci]; repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [mr_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uc, USB, Un, Ur.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    pose proof (@YG0f.ASAN_CEIL_range _) as [CR1 CR2]. unfold YG0f.ASAN_CEIL in CR1, CR2.
    rewrite HSTK in Hslo.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; lia.
- unfold sh_ok, mr_SH. repeat apply Forall_cons; try apply Forall_nil;
  unfold shent_ok, app_apart; cbn [she_m she_lo she_hi];
  rewrite UBx, U10; rewrite <- (aview_rd_of SEGS); (split;
  [ eapply (range_addressable_sub _ _ _ _ _ _ HRA); lia
  | intros a Ha; cbn [Z.min Z.max] in Ha; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia ]).
Qed.

(* the branch at 0x87824, blt a1 (7), a0 (n_kept) *)
Lemma mr_br_lt7 : forall E v, ew E 33 = Z_to_bv 64 v -> 0 <= v <= 8 ->
branch_taken BC_LT (sv_denot E (SLit 7)) (sv_denot E (SOff 33 0)) = (7 <? v).
Proof.
intros E v H Hv. rewrite YO0c.branch_lt.
change (bv_unsigned (sv_denot E (SOff 33 0))) with (U E (SOff 33 0)).
rewrite (U_atom E 33 v H) by lia.
cbn [sv_denot]. rewrite unsigned_lit_small by lia.
rewrite !YO0b.s64_small by lia. reflexivity.
Qed.
(* the same when the loaded value's range lets the executor drop the sign extension: the chunk is SOff k 1 *)
Lemma mr_soff1 : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v -> v + 1 < 2 ^ 32 ->
bv_unsigned (sv_denot E (SOff k 1)) mod 2 ^ (8 * Z.of_N 4) = v + 1.
Proof.
intros E k v H Hv Hv1. cbn [sv_denot]. rewrite H.
replace (bv_unsigned (Z_to_bv 64 v) + 1) with (v + 1) by (rewrite unsigned_lit_small by lia; lia).
rewrite unsigned_lit_small by lia. change (8 * Z.of_N 4) with 32. apply Z.mod_small. lia.
Qed.
(* lw / addi 1 / sw of a u32 counter below 2^32 - 1: the cell's new 4 bytes hold counter + 1 *)
Lemma mr_inc32 : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v -> v + 1 < 2 ^ 32 ->
bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff k 0)) (SLit 1))) mod 2 ^ (8 * Z.of_N 4) = v + 1.
Proof.
intros E k v H Hv Hv1. cbn [sv_denot]. rewrite H.
replace (bv_unsigned (Z_to_bv 64 v) + 0) with v by (rewrite unsigned_lit_small by lia; lia).
change (8 * Z.of_N 4) with 32. rewrite YN0d.ctr_chunk_mod by lia. apply Z.mod_small. lia.
Qed.
(* a val_mem of the restricted memory is the reader's sa_val *)
Lemma mr_sa_val_of : forall segs H mem a n v, val_mem segs (mrestrict H mem) a n v -> sa_val (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* every write window of a run's regions is a byte the journal lets m_refuse write: the frame, or refused /
   n_kept / kept[n_kept] in the mconf block (the footprint, in a live block) *)
Ltac mr_awr Usp Uc HSTK :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [ reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo]; rewrite HSTK; lia | cbn [YP09.r_whi]; lia |]
  | eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 10%nat _);
    [ reflexivity | exact Uc
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; left;
      lazymatch goal with Hb : In (?b, ?m) (ablocks B _ _), Hb2 : _ <= ?b + req_size ?m |- _ =>
      split;
      [ first [ apply mr_inFP_rf; unfold seg_spec.MC_REFUSED; lia
              | apply mr_inFP_nk; [assumption | unfold seg_spec.MC_NKEPT; lia]
              | apply mr_inFP_kept; [assumption | unfold seg_spec.kept_addr, seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN; lia] ]
      | exists b, m; split; [exact Hb | lia] ] end |] ].

(* the branch at 0x8784c, blez a4 (line) *)
Lemma mr_br_ge0 : forall E v, ew E 11 = Z_to_bv 64 v -> 0 <= v <= 65536 ->
branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff 11 0)) = negb (0 <? v).
Proof.
intros E v H Hv. rewrite YO0c.branch_ge.
change (bv_unsigned (sv_denot E (SOff 11 0))) with (U E (SOff 11 0)).
rewrite (U_atom E 11 v H) by lia.
cbn [sv_denot]. rewrite unsigned_lit_small by lia.
rewrite !YO0b.s64_small by lia. reflexivity.
Qed.
(* a0 at the snprintf call: c + 0x200c + 112 n_kept = &kept[n_kept] *)
Lemma mr_a0_kept : forall E c n, ew E 10 = Z_to_bv 64 c -> ew E 33 = Z_to_bv 64 n -> 0 <= c -> c + 9236 < 2 ^ 63 ->
0 <= n <= 8 ->
alu64 ALU_ADD (Z_to_bv 64 (bv_unsigned (ew E 10) + 8204)) (mul_div M_MUL (ew E 33) (Z_to_bv 64 112)) =
w64 (c + 8204 + 112 * n).
Proof.
intros E c n H10 H33 Hc0 Hc Hn. apply bv_eq. rewrite alu64_unsigned, mul_div_unsigned.
rewrite H10, H33. cbn [zalu_raw zmd_raw]. unfold w64.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
repeat match goal with |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)) by lia end.
lia.
Qed.

Lemma mr_rdword_kept : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma mr_argZ3 : forall regs : bvmap 5 word, argZ regs 3 = bv_unsigned (getr regs 13).
Proof. intros regs. unfold argZ. assert (E : Z_to_bv 5 (10 + 3) = (13%bv : bv 5)) by (apply bv_eq; reflexivity). rewrite E. reflexivity. Qed.
Lemma mr_argZ4 : forall regs : bvmap 5 word, argZ regs 4 = bv_unsigned (getr regs 14).
Proof. intros regs. unfold argZ. assert (E : Z_to_bv 5 (10 + 4) = (14%bv : bv 5)) by (apply bv_eq; reflexivity). rewrite E. reflexivity. Qed.
Lemma mr_sn_len : forall T, RtPFShared.sn_len (112 - 1) T = Z.min (Z.of_nat (length T)) 111 + 1.
Proof.
intros T. unfold RtPFShared.sn_len, RtPFShared.sn_bytes. rewrite length_app, length_firstn. cbn [length].
change (Z.to_nat (112 - 1)) with 111%nat. lia.
Qed.

(* the snprintf call (0x8785c or 0x87870): snprintf(kept[n_kept], 112, F, c->reading[, line]) through the row-4
   contract RtFormat.asnprintf_realizes, stepped by PaFx.v's aj_art_own_atF / srr_art_postF_of_pf
   (fuzz_command's check_reply_s4.v:352-363 pattern): the destination is in the footprint and a live block *)
Lemma mr_snp : forall W regsT memT mdc ly S mem md regs ch c line mc knock bs F ps args T raw,
afn_pre SEGS B SegInstA.STK_m_refuse ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
m_refuse_pre SEGS B ly S (rdW W mem) SegInstA.seg_litA_fz SegInstA.gotwA SegInstA.guardA c line mc knock ->
sa_bytes (rdW W mem) c bs -> seg_spec.mconf_encp knock mc bs ->
ajournal SEGS B SegInstA.STK_m_refuse (spZ regs) (m_refuse_W c mc) ly S W mem md [] ly S W memT mdc 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (spZ regs - 48 <= a < spZ regs) ->
  rdW W memT a = rdW W mem a) ->
spZ regsT = spZ regs - 48 -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
Z.of_nat (length (mc_kept mc)) < 8 ->
getr regsT 10 = w64 (seg_spec.kept_addr c (length (mc_kept mc))) -> getr regsT 11 = w64 112 ->
In F M_REFUSE_LITS -> getr regsT 12 = w64 (SegInstA.seg_litA_fz F) ->
getr regsT 13 = w64 (c + seg_spec.MC_READING) -> getr regsT 14 = w64 line ->
RtPFPf.pf_parse F = Some ps -> Forall RtPFCmd.pf_cmd_piece ps -> RtPFShared.pf_prec_pos ps args ->
RtPFPf.pf_text ps args = Some T ->
args = RtPFPf.APtr (mc_reading mc) :: (if 0 <? line then [RtPFPf.AInt line] else []) ->
Z.of_nat (length T) <= 200 ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 /\
 c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal SEGS B SegInstA.STK_m_refuse (spZ regs) (m_refuse_W c mc) ly S W mem md [] ly S W mem2 md2 0 /\
 aregs_preserved regsT regs2 /\
 (getr regs2 10 = w64 (Z.of_nat (length T)) /\
  forall i, 0 <= i < RtPFShared.sn_len (112 - 1) T ->
   rdW W mem2 (seg_spec.kept_addr c (length (mc_kept mc)) + i) =
   Some (nth (Z.to_nat i) (RtPFShared.sn_bytes (112 - 1) T) 0)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 - RtPFCmd.CMD_SNP_K <= a < spZ regs - 48) ->
  ~ (seg_spec.kept_addr c (length (mc_kept mc)) <= a <
     seg_spec.kept_addr c (length (mc_kept mc)) + RtPFShared.sn_len (112 - 1) T) ->
  rdW W mem2 a = rdW W memT a)).
Proof.
intros W regsT memT mdc ly S mem md regs ch c line mc knock bs F ps args T raw
  HPRE HROD HMR HBS HENC HJ KEEPT Tsp T1 Traw T3 T4 Hlt T10 T11 HinF T12 T13 T14 Hparse Hpieces Hprec Htext Hargs HlenT.
destruct HMR as (Hc0 & Hc16 & HHEAP & HADDR & HMC & HTAIL & Hline & Href & HFRM & HSSP & HLIT).
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : SegInstA.STK_m_refuse = 8240) by reflexivity.
assert (HK : RtPFCmd.CMD_SNP_K = 8192) by reflexivity.
destruct (mr_c_where ly S W regs mem md ch c HPRE Hc16 HHEAP)
  as (b & m & Hin & Hb1 & Hb2 & Hc4096 & Hcceil & Hcimg & Hcband & Hcpres).
unfold seg_spec.SEG_M_SIZE in Hb2, Hcceil, Hcimg, Hcband, Hcpres, HTAIL.
pose proof (proj1 HJ) as HARc.
destruct (al_blocks _ _ LAWS ly S W memT mdc b m HARc Hin) as (_ & _ & _ & _ & Hbpres & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2].
set (n := Z.of_nat (length (mc_kept mc))) in *.
set (d := seg_spec.kept_addr c (length (mc_kept mc))) in *.
assert (Hd : d = c + 8204 + 112 * n) by (unfold d, n, seg_spec.kept_addr, seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN; lia).
set (w := RtPFShared.sn_len (112 - 1) T) in *.
assert (Hw : 1 <= w <= 112) by (unfold w; rewrite mr_sn_len; lia).
set (f := SegInstA.seg_litA_fz F) in *.
assert (Hn0 : 0 <= n) by (unfold n; lia).
(* the reading *)
destruct (mr_reading_at _ c bs knock mc HBS HENC) as (HRB & HRZ & HRL).
set (rdg := mc_reading mc) in *.
set (wr := c + seg_spec.MC_READING) in *.
assert (Hwr : wr = c + 9140) by (unfold wr, seg_spec.MC_READING; lia).
assert (Ec : c = 16 * (c / 16)) by (pose proof (Z.div_mod c 16 ltac:(lia)) as Hq; rewrite Hc16 in Hq; lia).
assert (Ese : (wr + Z.of_nat (length rdg)) - (wr + Z.of_nat (length rdg)) mod 8 =
  8 * ((wr + Z.of_nat (length rdg)) / 8)) by (pose proof (Z.div_mod (wr + Z.of_nat (length rdg)) 8 ltac:(lia)); lia).
assert (Hse : RtPFShared.str_end wr rdg <= c + 9240).
{ unfold RtPFShared.str_end. rewrite Ese. lia. }
assert (Hse0 : wr + Z.of_nat (length rdg) < RtPFShared.str_end wr rdg).
{ unfold RtPFShared.str_end. pose proof (Z.mod_pos_bound (wr + Z.of_nat (length rdg)) 8 ltac:(lia)). lia. }
assert (Hse8 : RtPFShared.str_end wr rdg <= wr + Z.of_nat (length rdg) + 8).
{ unfold RtPFShared.str_end. pose proof (Z.mod_pos_bound (wr + Z.of_nat (length rdg)) 8 ltac:(lia)). lia. }
assert (Htl : (c + 9236 - 1) mod 8 = 3).
{ rewrite Ec. replace (16 * (c / 16) + 9236 - 1) with (3 + (2 * (c / 16) + 1154) * 8) by lia.
  rewrite Z_mod_plus_full. reflexivity. }
(* the scratch window and the entry's precondition at the call *)
destruct (ecall_pre_stk_at SEGS B RtPFCmd.CMD_SNP_K SegInstA.STK_m_refuse (spZ regs) (m_refuse_W c mc) ly S W mem md []
  ly S W memT mdc 0 regsT (-48) HJ ltac:(lia) eq_refl ltac:(lia) ltac:(rewrite HK; unfold ESTACK; lia)
  ltac:(rewrite HK, HSTK; lia) ltac:(rewrite T1; exact Traw) T3 T4) as (HEC & HSLO & HSCR).
pose proof (ASNPRINTF fx) as HA.
unfold asnprintf_realizes, RtPFCmd.asnprintf_sh, RtPFCmd.cmd_asnprintf_realizes in HA.
(* image facts at the call *)
assert (KIMG : forall a, 0x10000 <= a < kImgEnd -> rdW W memT a = rdW W mem a).
{ intros a Ha. apply KEEPT; unfold kImgEnd in *; [lia | lia | rewrite HSTK in Hslo; lia]. }
assert (HROM : RtDefs.rt_rom_view SEGS B W memT).
{ intros a (sg & Hsg & Hwr' & Hr) Ho He.
  pose proof (pa_img_range a (ex_intro _ sg (conj Hsg Hr))) as Hia.
  rewrite (KIMG a Hia).
  exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hwr' Hr)))) Ho He). }
destruct HSSP as (HG1 & cval & HG2).
assert (HG1' : rdword (rdW W memT) SegInstA.gotwA = Some SegInstA.guardA).
{ rewrite (mr_rdword_kept (rdW W mem)); [exact HG1|]. intros i Hi. apply KIMG. unfold SegInstA.gotwA, kImgEnd. lia. }
assert (HG2' : rdword (rdW W memT) SegInstA.guardA = Some cval).
{ rewrite (mr_rdword_kept (rdW W mem)); [exact HG2|]. intros i Hi. apply KIMG. unfold SegInstA.guardA, kImgEnd. lia. }
(* the literal *)
destruct (HLIT F HinF) as (Hf0 & ((HFZ & HFnz) & HFT) & HFP & HFR & HFI).
destruct (HFP ly S W memT mdc HARc) as (Hfa0 & Hfa63 & HFAM & HFRA & HFHV).
assert (HFimg : 0x10000 <= f /\ f + Z.of_nat (length F) + 1 <= RtPFCmd.CMD_GOTW /\ F <> []).
{ destruct HinF as [<- | [<- | []]]; unfold f; vm_compute; (split; [discriminate|]); (split; [discriminate|]); discriminate. }
(* the snprintf contract *)
eapply SRr_mono.
{ eapply (aj_art_own_atF SEGS B LAWS pa_segs_low RtPFCmd.CMD_SNP_K (fun a => d <= a < d + w)
    (SIGMA SS___interceptor_trampoline_snprintf) W regsT memT SegInstA.STK_m_refuse (spZ regs) (m_refuse_W c mc)
    ly S W mem md [] ly S mdc 0 (-48) raw _ HJ).
  - lia.
  - reflexivity.
  - lia.
  - rewrite HK; lia.
  - rewrite HK, HSTK; lia.
  - exact T1.
  - intros a Ha. right; left. split.
    + apply mr_inFP_kept; [exact Hlt | unfold seg_spec.MC_KEPT_LEN; fold d; lia].
    + exists b, m. split; [exact Hin | lia].
  - apply (srr_art_postF_of_pf SEGS B RtPFCmd.CMD_SNP_K ly S W regsT memT mdc _ d w
      (RtPFShared.sn_bytes (112 - 1) T) (Z.of_nat (length T)) HSCR).
    pose proof (proj1 HENC) as Hlen. unfold seg_spec.SEG_M_SIZE in Hlen.
    assert (Hsp' : spZ regsT - RtPFCmd.CMD_SNP_K >= c + 9248) by (rewrite Tsp, HK; rewrite HSTK in Hslo; lia).
    assert (Hdw : d + w <= c + 9100) by (rewrite Hd; lia).
    assert (Hoff : d + w <= 0x10000 \/ kImgEnd <= d) by (destruct Hcimg; [left | right]; lia).
    assert (U13 : bv_unsigned (getr regsT 13) = wr) by (rewrite T13; unfold w64; apply unsigned_lit_small; lia).
    assert (U14 : bv_unsigned (getr regsT 14) = line) by (rewrite T14; unfold w64; apply unsigned_lit_small; lia).
    assert (HRDK : forall a, c + 9140 <= a < c + 9240 -> rdW W memT a = rdW W mem a).
    { intros a Ha. apply KEEPT; [lia | lia | rewrite HSTK in Hslo; lia]. }
    apply (HA ly S W regsT memT mdc d 112 f [] (map (argZ regsT) [3; 4; 5; 6; 7] ++ []) T cval HEC HSLO HSCR T10 T11 T12
      HROM).
    + unfold RtPFCmd.CMD_SNP_CR. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    + unfold RtPFCmd.CMD_SNP_CR, RtPFShared.snp_out. fold w.
      repeat (apply Forall_cons; [repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; unfold kImgEnd in Hoff; lia|]); apply Forall_nil|]).
      apply Forall_nil.
    + exact HG1'.
    + exact HG2'.
    + unfold SegInstA.gotwA; lia.
    + unfold SegInstA.gotwA; lia.
    + unfold SegInstA.guardA; lia.
    + unfold SegInstA.guardA; lia.
    + unfold RtPFShared.snp_out. fold w.
      repeat (apply Forall_cons; [unfold zdisjoint, SegInstA.gotwA; cbn [fst snd]; unfold kImgEnd in Hoff; lia|]). apply Forall_nil.
    + unfold RtPFShared.snp_out. fold w.
      repeat (apply Forall_cons; [unfold zdisjoint, SegInstA.guardA; cbn [fst snd]; unfold kImgEnd in Hoff; lia|]). apply Forall_nil.
    + split; [reflexivity | intros i Hi; cbn [length] in Hi; lia].
    + cbn [length Z.of_nat]. lia.
    + unfold RtPFShared.snp_out. fold w. cbn [length Z.of_nat].
      repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|]). apply Forall_nil.
    + (* the format family *)
      exists F, ps, args.
      split.
      { unfold RtPFShared.fmt_at. split; [lia|]. split.
        - intros i Hi. rewrite (KIMG (f + i)).
          + replace (f + i) with (f + Z.of_nat (Z.to_nat i)) by lia. apply HFZ. rewrite length_app. cbn [length]. lia.
          + destruct (HFI (f + i) ltac:(lia)) as (Himg & _). pose proof (pa_img_range _ Himg). lia.
        - split.
          + unfold RtPFShared.snp_out. fold w.
            repeat (apply Forall_cons; [unfold zdisjoint, RtPFCmd.CMD_GOTW in *; cbn [fst snd]; unfold kImgEnd in Hoff; lia|]).
            apply Forall_nil.
          + split; [exact HFAM|]. split; [exact HFRA | apply HFHV; lia]. }
      split; [exact Hparse|]. split; [exact Hpieces|].
      split.
      { subst args. cbn [map app]. rewrite mr_argZ3, mr_argZ4, U13, U14.
        assert (HPTR : RtPFShared.pf_arg_asan (rdW W memT) (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ regsT) d w) wr
          (RtPFPf.APtr rdg)).
        { cbn [RtPFShared.pf_arg_asan]. split; [exact HRZ|]. split; [lia|]. split; [lia|]. split.
          - intros i Hi. rewrite HRDK by lia. exact (HRB i Hi).
          - split.
            + intros x Hx. rewrite HRDK by lia.
              destruct (Z_lt_le_dec x (c + 9236)) as [Hx1 | Hx1].
              * replace x with (c + Z.of_nat (Z.to_nat (x - c))) by lia.
                rewrite HBS by lia. discriminate.
              * apply HTAIL. rewrite Htl. lia.
            + split.
              { unfold RtPFShared.snp_out. fold w.
                repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|]). apply Forall_nil. }
              split; [apply (amem_range_of_block SEGS B LAWS ly S W memT mdc b m); [exact HARc | exact Hin | lia | lia]|].
              split; [apply (range_addressable_of_block SEGS B LAWS ly S W memT mdc b m); [exact HARc | exact Hin | lia | lia]|].
              apply (shadow_hull_vis_of_block SEGS B LAWS ly S W memT mdc b m); [exact HARc | exact Hin | lia | lia | lia]. }
        destruct (0 <? line); cbn [RtPFShared.pf_args_asan RtPFShared.pf_arg_asan];
          (split; [exact HPTR|]); [split; [split; [lia | reflexivity] | exact I] | exact I]. }
      split; [exact Htext|]. split; [exact Hprec|].
      split; [unfold RtPFCmd.CMD_IMG_LO; lia|]. split; [exact (proj1 (proj2 HFimg))|].
      pose proof (amem8_of_block SEGS B LAWS ly S W memT mdc b m wr (Z.of_nat (length rdg) + 1) HARc Hin
        ltac:(lia) ltac:(lia) ltac:(lia)) as HAM8.
      split.
      { subst args. cbn [map app]. rewrite mr_argZ3, U13.
        destruct (0 <? line); cbn [RtPFCmd.cmd_args_slack]; (split; [|first [exact I | reflexivity]]);
        unfold amem_range in *; lia. }
      split; [exact (proj2 (proj2 HFimg))|].
      subst args. cbn [map app]. rewrite mr_argZ3, U13.
      destruct (0 <? line); cbn [RtPFCmd.cmd_args_amem]; (split; [|first [exact I | reflexivity]]);
      unfold amem_range in *; lia.
    + lia.
    + lia.
    + lia.
    + fold w. lia.
    + unfold RtPFShared.snp_out. fold w. cbn [pairwise]. split; [|split; [apply Forall_nil | exact I]].
      apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
    + fold w. intros a Ha. destruct (Hbpres a ltac:(lia)) as [Hp Hno]. split; [apply (apresent_writable SEGS); exact Hp|].
      split; [exact Hno|]. unfold ESTACK. lia.
    + fold w. exact (amem8_of_block SEGS B LAWS ly S W memT mdc b m d w HARc Hin ltac:(lia) ltac:(lia) ltac:(lia)).
    + fold w. apply (range_addressable_of_block SEGS B LAWS ly S W memT mdc b m); [exact HARc | exact Hin | lia | lia].
    + fold w. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W memT mdc b m); [exact HARc | exact Hin | lia | lia | lia].
    + fold w. unfold zdisjoint, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI. cbn [fst snd]. unfold kImgEnd in *. lia.
    + exact HFRM. }
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HP2 & HQ2 & HK2).
split; [reflexivity|]. exists fx1, regs2, mem2, md2.
split; [exact Hfx|]. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact HQ2|].
intros a Ha H1 H2. apply (HK2 a Ha); [lia | exact H2].
Qed.

Theorem m_refuse_walk : m_refuse_contract SEGS B (BASE + AF_m_refuse) SegInstA.STK_m_refuse RLO RHI
  SegInstA.seg_litA_fz SegInstA.gotwA SegInstA.guardA.
Proof.
unfold m_refuse_contract.
intros ly S W regs mem md ch c line mc knock HPRE HROD H10 Hc64 H11 HMR HEV.
pose proof HMR as HMR0.
destruct HMR as (Hc0 & Hc16 & HHEAP & HADDR & HMC & HTAIL & Hline & Href & HFRM & HSSP & HLIT).
destruct HMC as (bs & HBS & HENC).
pose proof HENC as (Hlen & _ & _ & _ & _ & Hrf & Hkl & _ & _ & Hnk & _ & _).
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : SegInstA.STK_m_refuse = 8240) by reflexivity.
set (n := Z.of_nat (length (mc_kept mc))) in *.
set (r := mc_refused mc) in *.
assert (Hn8 : 0 <= n <= 8) by (unfold n; lia).
assert (Hr32 : 0 <= r <= 4294967294) by (destruct Hrf as [Hr _]; lia).
pose proof (mr_val4 _ c bs seg_spec.MC_NKEPT n HBS Hnk ltac:(unfold seg_spec.MC_NKEPT; lia)
  ltac:(rewrite Hlen; unfold seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE; lia)) as VNK.
pose proof (mr_val4 _ c bs seg_spec.MC_REFUSED r HBS Hrf ltac:(unfold seg_spec.MC_REFUSED; lia)
  ltac:(rewrite Hlen; unfold seg_spec.MC_REFUSED, seg_spec.SEG_M_SIZE; lia)) as VRF.
unfold seg_spec.MC_NKEPT in VNK. unfold seg_spec.MC_REFUSED in VRF.
destruct (mr_c_where ly S W regs mem md ch c HPRE Hc16 HHEAP)
  as (b & m & Hin & Hb1 & Hb2 & Hc4096 & Hcceil & Hcimg & Hcband & Hcpres).
unfold seg_spec.SEG_M_SIZE in Hb2, Hcceil, Hcimg, Hcband, Hcpres.
destruct (mr_entry ly S W regs mem md ch c n r HPRE H10 Hc16 HHEAP HADDR VNK Hn8 VRF Hr32) as [HS SHOK].
pose proof (ajournal_init SEGS B SegInstA.STK_m_refuse (m_refuse_W c mc) ly S W regs mem md ch HPRE) as HJ.
remember (mrE regs n r) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mrE; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (mr_extra n r)) k)
by (intros k Hk; subst E; unfold mrE; apply Eimg_low; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 line)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HAE : env_agree 32 (Ereg regs (mr_extra n r)) E)
by (split; [intros k Hk; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; lia).
clear HE.
(* a run whose regions are the entry's (writes only the frame and refused) keeps every other byte *)
assert (KF : forall rs m1 m2, frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  windows rs = windows (ss_mem mr_ss0) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (spZ regs - 48 <= a < spZ regs) ->
  rdW W m2 a = rdW W m1 a).
{ intros rs m1 m2 HFx Hrs a Ha H1 H2.
  refine (kept_of_frame E rs (w_H W) m1 m2
    (fun x => (c + 8200 <= x < c + 8204) \/ (spZ regs - 48 <= x < spZ regs)) HFx _ a Ha _);
  [| intros [Hq|Hq]; auto].
  intros bb wlo whi x Hin' Hr. rewrite Hrs in Hin'. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hr;
    first [rewrite Uc in Hr; left; lia | rewrite Usp in Hr; right; lia | exfalso; lia] |]).
  destruct Hin'. }
unfold cfg_at. change (w64 (BASE + AF_m_refuse)) with (Z_to_bv 64 (BASE + AF_m_refuse)).
paj_run_tok RUN HS HJ SHOK Bspan; [ mr_awr Usp Uc HSTK | ].
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* 7 < n_kept: n_kept = 8, straight to refused++ (0x87888) *)
  rewrite (mr_br_lt7 _ n E33 Hn8) in Hc. apply Z.ltb_lt in Hc. assert (Hn8' : n = 8) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [ mr_awr Usp Uc HSTK | ].
  (* the refused cell holds refused + 1 *)
  lazymatch goal with
  | HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
    pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msc) 3%nat _ HSx eq_refl) as HR3;
    cbn [restrict ms_mem] in HR3;
    pose proof (field_of_region_any E _ 10%nat c _ _ _ _ _ 8200 4%N _ HR3 Uc ltac:(cbn; left; reflexivity) ltac:(lia))
      as VpR
  end.
  rewrite (mr_inc32 E 34 r E34 ltac:(lia) Href) in VpR. change (N.to_nat 4) with 4%nat in VpR.
  (* every byte outside refused and the frame is kept *)
  lazymatch goal with
  | HF1 : frame_of E _ (mrestrict _ mem) (mrestrict _ (ms_mem ?m1)),
    HF2 : frame_of E _ (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)) |- _ =>
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (spZ regs - 48 <= a < spZ regs) ->
      rdW W (ms_mem m2) a = rdW W mem a);
    [ intros a Ha H1 H2;
      assert (Zs : forall bb wlo whi x, In (bb, wlo, whi) (windows (ss_mem mr_ss0)) ->
        base_val E bb + wlo <= x < base_val E bb + whi -> (c + 8200 <= x < c + 8204) \/ (spZ regs - 48 <= x < spZ regs));
      [ intros bb wlo whi x Hin' Hr; vm_compute in Hin';
        repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hr;
          first [rewrite Uc in Hr; left; lia | rewrite Usp in Hr; right; lia | exfalso; lia] |]);
        destruct Hin' | ];
      rewrite (kept_of_frame E _ (w_H W) (ms_mem m1) (ms_mem m2) _ HF2 Zs a Ha ltac:(intros [Hq|Hq]; auto));
      exact (kept_of_frame E _ (w_H W) mem (ms_mem m1) _ HF1 Zs a Ha ltac:(intros [Hq|Hq]; auto))
    | ]
  end.
  (* the ret *)
  lazymatch goal with
  | HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    prreg HSx (1%bv : bv 5) R1;
    eapply (RET W _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity));
    intros mat'; apply (apost_baseF_of_base SEGS); unfold apost_base;
    exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
    split; [cbn [ms_regs]; rewrite R1, E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|];
    split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJx|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (mr_extra n r) HSx); [exact HAE | vm_compute; reflexivity]|]
  end.
  split.
  { apply (mr_enc_ge8 (rdW W mem) _ c bs knock mc line HBS HENC Href ltac:(fold n; lia)).
    - apply mr_sa_val_of. unfold seg_spec.MC_REFUSED. exact VpR.
    - intros a Ha H1. unfold seg_spec.MC_REFUSED, seg_spec.SEG_M_SIZE in *. rewrite HSTK in Hslo.
      apply KEEP; lia. }
  split.
  { intros a Ha HnS HnE. apply KEEP; [exact Ha | | rewrite HSTK in HnS; lia].
    intros Hq. apply HnE. right; right. unfold seg_spec.MC_REFUSED. lia. }
  split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs S). apply mr_set_fs_id.
- (* n_kept <= 7: the snprintf of the address into kept[n_kept] *)
  rewrite (mr_br_lt7 _ n E33 Hn8) in Hc. apply Z.ltb_ge in Hc. assert (Hlt8 : n < 8) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [ mr_awr Usp Uc HSTK | ].
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* line <= 0: line = 0, snprintf(kept[n_kept], 112, "%s: " (.str.7), c->reading) at 0x87870 *)
    rewrite (mr_br_ge0 E line E11 Hline) in Hc. apply negb_true_iff in Hc. apply Z.ltb_ge in Hc.
    assert (Hl0 : line = 0) by lia. clear Hc.
    paj_run_tok RUN HS HJ SHOK Bspan; [ mr_awr Usp Uc HSTK | ].
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14.
    assert (Tsp : spZ (ms_regs ms1) = spZ regs - 48).
    { unfold spZ at 1. rewrite Q2, Usp. rewrite unsigned_lit_small by (rewrite HSTK in Hslo; lia). lia. }
    assert (T3 : getr (ms_regs ms1) 3 = w64 (as_gp B))
      by (rewrite Q3, EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl); exact Hgp).
    assert (T4 : getr (ms_regs ms1) 4 = w64 (as_tp B))
      by (rewrite Q4, EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl); exact Htp).
    assert (T10 : getr (ms_regs ms1) 10 = w64 (seg_spec.kept_addr c (length (mc_kept mc)))).
    { rewrite Q10, (mr_a0_kept E c n E10 E33 ltac:(lia) ltac:(lia) Hn8).
      unfold seg_spec.kept_addr, seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN. fold n. try (f_equal; lia). }
    assert (T12 : getr (ms_regs ms1) 12 = w64 (SegInstA.seg_litA_fz F_addr)).
    { rewrite Q12, (img_env_atomP E 269 HEI ltac:(unfold A_TEXT, A_LIM; lia)).
      change (VAL 269) with (VAL (A_OBJ 28)). rewrite (VOBJS 28%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. }
    assert (T13 : getr (ms_regs ms1) 13 = w64 (c + seg_spec.MC_READING)) by (rewrite Q13, Uc; reflexivity).
    assert (T14 : getr (ms_regs ms1) 14 = w64 line) by (rewrite Q14, E11; reflexivity).
    assert (Traw : YK0s.ret_ok (Z_to_bv 64 (BASE + 11072))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
    (* every byte but refused and the frame, from the entry to the call *)
    lazymatch goal with
    | HF1 : frame_of E _ (mrestrict _ mem) (mrestrict _ (ms_mem ?m1)),
      HF2 : frame_of E _ (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)),
      HF3 : frame_of E _ (mrestrict _ (ms_mem ?m2)) (mrestrict _ (ms_mem ms1)) |- _ =>
      assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (spZ regs - 48 <= a < spZ regs) ->
        rdW W (ms_mem ms1) a = rdW W mem a)
      by (intros a Ha H1 H2;
          rewrite (KF _ _ _ HF3 ltac:(vm_compute; reflexivity) a Ha H1 H2);
          rewrite (KF _ _ _ HF2 ltac:(vm_compute; reflexivity) a Ha H1 H2);
          exact (KF _ _ _ HF1 ltac:(vm_compute; reflexivity) a Ha H1 H2))
    end.
    (* the text snprintf prints *)
    destruct (mr_reading_at _ c bs knock mc HBS HENC) as (_ & HRZ & HRL).
    assert (HRN : ~ In 0 (mc_reading mc)).
    { intros H0. rewrite Forall_forall in HRZ. specialize (HRZ 0 H0). lia. }
    destruct (mr_pf_noline (mc_reading mc) HRN) as (ps & Hparse & Hpieces & Hprec & Htext).
    assert (HlenT : Z.of_nat (length (fmt F_addr [AS (mc_reading mc)])) <= 200).
    { rewrite fmt_addr, length_app. pose proof (cut_nul_len (mc_reading mc)). cbn [length]. lia. }
    pose proof (mr_sn_len (fmt F_addr [AS (mc_reading mc)])) as Hsn.
    assert (HT : (if 0 <? line then fmt F_addr_line [AS (mc_reading mc); AI line] else fmt F_addr [AS (mc_reading mc)])
      = fmt F_addr [AS (mc_reading mc)]) by (rewrite Hl0; reflexivity).
    eapply (srr_after_artF SEGS W _ (Z_to_bv 64 (BASE + 11072)) _ B SegInstA.STK_m_refuse (m_refuse_W c mc) regs ly S W
      mem md EV_m_refuse).
    { exact (mr_snp W (ms_regs ms1) (ms_mem ms1) _ ly S mem md regs ch c line mc knock bs F_addr ps
        [RtPFPf.APtr (mc_reading mc)] _ _ HPRE HROD HMR0 HBS HENC HJ KEEPC Tsp Q1 Traw T3 T4 Hlt8 T10 Q11
        ltac:(right; left; reflexivity) T12 T13 T14 Hparse Hpieces Hprec Htext
        ltac:(rewrite Hl0; reflexivity) HlenT). }
    intros fx1 regs2 mem2 md2 Hfx (HJ2 & HP2 & (HR10 & HBY) & HK2).
    pose proof (PaFx.st_ok_restrict_xfx fx fx1 _ _ _ _ _ HS eq_refl) as HSf. clear HS. rename HSf into HS.
    jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3]%nat HS2.
    assert (Hd : seg_spec.kept_addr c (length (mc_kept mc)) = c + 8204 + 112 * n)
      by (unfold seg_spec.kept_addr, seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN; fold n; lia).
    rewrite Hd in HBY, HK2.
    pose proof (proj1 HJ2) as HAR2.
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
    destruct (al_blocks _ _ LAWS ly S W mem2 md2 b m HAR2 Hin) as (_ & _ & _ & _ & Hbpres2 & _).
    assert (V0 : VAL (A_OBJ 0) = 0xa2a50) by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
    assert (V12 : VAL (A_OBJ 12) = 0xabff8) by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
    assert (EO0 : bv_unsigned (ew E (A_OBJ 0)) = 0xa2a50)
      by (rewrite (img_env_atomP E (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V0; reflexivity).
    assert (EO12 : bv_unsigned (ew E (A_OBJ 12)) = 0xabff8)
      by (rewrite (img_env_atomP E (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V12; reflexivity).
    lazymatch type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict]. rewrite HSTK in Hslo, Hpres2.
      repeat apply Forall_cons; try apply Forall_nil; split;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha;
        rewrite ?Usp, ?Uc in Ha; change (ew E 241) with (ew E (A_OBJ 0)) in Ha;
        change (ew E 253) with (ew E (A_OBJ 12)) in Ha; rewrite ?EO0, ?EO12 in Ha.
      - apply (mbyte_of_aview SEGS). apply HK2; unfold RtPFCmd.CMD_SNP_K, ESTACK in *; lia.
      - intros _. apply (apresent_writable SEGS). apply Hpres2. lia.
      - apply (mbyte_of_aview SEGS). apply HK2; unfold RtPFCmd.CMD_SNP_K, ESTACK, kImgEnd in *; destruct Hcimg; lia.
      - lia.
      - apply (mbyte_of_aview SEGS). apply HK2; unfold RtPFCmd.CMD_SNP_K, ESTACK, kImgEnd in *; destruct Hcimg; lia.
      - lia.
      - apply (mbyte_of_aview SEGS). apply HK2; unfold RtPFCmd.CMD_SNP_K, ESTACK in *; lia.
      - intros _. apply (apresent_writable SEGS). apply (proj1 (Hbpres2 a ltac:(lia))). }
    clear HS. rewrite <- (restrict_mkst_fx (fx := fx1)) in HS2. rename HS2 into HS.
    remember (havoc E 35 (map (getr regs2) CLOB)) as Ef eqn:HEf in HS.
    assert (HEIf : img_env VAL A_LIM Ef) by (rewrite HEf; apply img_env_havoc; [exact HEI | cbv; lia]).
    assert (OLDf : forall k, (k < 35)%nat -> ew Ef k = ew E k)
      by (intros k Hk; rewrite HEf; apply YN3v.ew_havoc_old; exact Hk).
    assert (Uspf : bv_unsigned (ew Ef 2) = spZ regs) by (rewrite OLDf by lia; exact Usp).
    assert (Ucf : bv_unsigned (ew Ef 10) = c) by (rewrite OLDf by lia; exact Uc).
    assert (HAEf : env_agree 32 (Ereg regs (mr_extra n r)) Ef).
    { destruct HAE as [HA1 HA2]. split; [intros k Hk; rewrite OLDf by lia; apply HA1; exact Hk|].
      rewrite HEf. exact HA2. }
    (* n_kept becomes a written region; it lies outside what snprintf wrote *)
    assert (HKN : forall a, c + 9132 <= a < c + 9136 -> rdW W mem2 a = rdW W mem a).
    { intros a Ha. rewrite HSTK in Hslo. rewrite HK2 by (unfold RtPFCmd.CMD_SNP_K, ESTACK; lia). apply KEEPC; lia. }
    assert (VNK2 : sa_val (rdW W mem2) (c + 9132) 4 n).
    { intros k Hk. rewrite HKN by lia. apply VNK. exact Hk. }
    assert (EO0f : bv_unsigned (ew Ef (A_OBJ 0)) = 0xa2a50)
      by (rewrite (img_env_atomP Ef (A_OBJ 0) HEIf ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V0; reflexivity).
    assert (EO12f : bv_unsigned (ew Ef (A_OBJ 12)) = 0xabff8)
      by (rewrite (img_env_atomP Ef (A_OBJ 12) HEIf ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V12; reflexivity).
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
      assert (HRn : region_ok SEGS Ef (ms_mem msx) mr_nk_w);
      [| assert (HDn : all_disjoint Ef mr_nk_w (ss_mem ssx));
         [| pose proof (st_ok_pi_add_region Ef _ _ mr_nk_w HS eq_refl HRn HDn) as HSn ] ]
    end.
    { unfold region_ok, mr_nk_w. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      cbn [ms_mem restrict]. rewrite Ucf. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hbpres2 (c + o) ltac:(lia)))|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS Ef _ c 0x23ac 4 (SOff 33 0) n).
      - cbn [sv_denot]. rewrite OLDf by lia. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside.
      - exact (mr_val_mem SEGS (w_H W) mem2 _ 4 n VNK2). }
    { lazymatch goal with |- all_disjoint _ _ (ss_mem ?ssx) =>
        let rs := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with rs end.
      apply all_disjoint_of_extents. unfold mr_nk_w.
      unfold extent_of_region; cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint].
      change (ew Ef 241) with (ew Ef (A_OBJ 0)). change (ew Ef 253) with (ew Ef (A_OBJ 12)).
      rewrite Ucf, Uspf, EO0f, EO12f. unfold zdisj. cbn [fst snd]. rewrite HSTK in Hslo.
      unfold kImgEnd in Hcimg. destruct Hcimg; repeat split; lia. }
    clear HS. rename HSn into HS.
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => let v := eval vm_compute in ssx in change ssx with v in HS end.
    assert (SHOKf : sh_ok SEGS mrBx mr_SH Ef (mrestrict (w_H W) mem2)).
    { assert (E32 : ew E 32 = Z_to_bv 64 SB)
        by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
      assert (UBx : U Ef mrBx = SHADOW_OFF).
      { unfold mrBx. rewrite U_SOff, OLDf by lia.
        rewrite E32, Z.add_0_r, unsigned_lit_small by (unfold SB; lia).
        rewrite zcanon_id by (unfold SB, M64; lia). reflexivity. }
      assert (U10 : U Ef (SOff 10 0) = c).
      { rewrite U_SOff, Ucf, Z.add_0_r. apply zcanon_id. unfold M64. lia. }
      pose proof (range_addressable_of_block SEGS B LAWS ly S W mem2 md2 b m c 9236 HAR2 Hin ltac:(lia) ltac:(lia)) as HRA2.
      unfold sh_ok, mr_SH. repeat apply Forall_cons; try apply Forall_nil;
      unfold shent_ok, app_apart; cbn [she_m she_lo she_hi];
      rewrite UBx, U10; rewrite <- (aview_rd_of SEGS); (split;
      [ eapply (range_addressable_sub _ _ _ _ _ _ HRA2); lia
      | intros a Ha; cbn [Z.min Z.max] in Ha; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia ]). }
    pose proof (paj_run (fx := fx1) B LAWS) as RUNf.
    paj_run_tok RUNf HS HJ2 SHOKf Bspan; [ mr_awr Uspf Ucf HSTK | ].
    (* the cells the tail wrote: n_kept + 1, refused + 1 *)
    lazymatch goal with
    | HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
      pose proof (st_ok_pi_region_nth Ef ssx (restrict (w_H W) msc) 0%nat _ HSx eq_refl) as HRn0;
      pose proof (st_ok_pi_region_nth Ef ssx (restrict (w_H W) msc) 4%nat _ HSx eq_refl) as HRr4;
      cbn [restrict ms_mem] in HRn0, HRr4;
      pose proof (field_of_region_any Ef _ 10%nat c _ _ _ _ _ 9132 4%N _ HRn0 Ucf ltac:(cbn; left; reflexivity)
        ltac:(lia)) as VpN;
      pose proof (field_of_region_any Ef _ 10%nat c _ _ _ _ _ 8200 4%N _ HRr4 Ucf ltac:(cbn; left; reflexivity)
        ltac:(lia)) as VpR
    end.
    rewrite (mr_soff1 Ef 33 n ltac:(rewrite OLDf by lia; exact E33) ltac:(lia) ltac:(lia)) in VpN.
    rewrite (mr_inc32 Ef 34 r ltac:(rewrite OLDf by lia; exact E34) ltac:(lia) Href) in VpR.
    change (N.to_nat 4) with 4%nat in VpN, VpR.
    (* the tail keeps every byte but its frame, n_kept and refused *)
    lazymatch goal with
    | HFx : frame_of Ef _ (mrestrict _ mem2) (mrestrict _ (ms_mem ?mf)) |- _ =>
      assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (c + 9132 <= a < c + 9136) ->
        ~ (spZ regs - 48 <= a < spZ regs) -> rdW W (ms_mem mf) a = rdW W mem2 a);
      [ intros a Ha H1 H2 H3;
        refine (kept_of_frame Ef _ (w_H W) mem2 (ms_mem mf)
          (fun x => (c + 8200 <= x < c + 8204) \/ (c + 9132 <= x < c + 9136) \/ (spZ regs - 48 <= x < spZ regs))
          HFx _ a Ha _);
        [ intros bb wlo whi x Hin' Hr; vm_compute in Hin';
          repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hr;
            first [ rewrite Ucf in Hr; first [left; lia | right; left; lia]
                  | rewrite Uspf in Hr; right; right; lia | exfalso; lia ] |]);
          destruct Hin'
        | intros [Hq|[Hq|Hq]]; auto ]
      | ]
    end.
    destruct (mr_sn_text mc line) as [HSB HSL].
    rewrite HT in HSB, HSL. rewrite HSB in HBY. rewrite HSL in HBY, HK2.
    pose proof (mr_text_ok bs knock mc line HENC) as [HTN HTL].
    rewrite HSTK in Hslo.
    (* the ret *)
    pose proof (paj_ret_at (fx := fx1) (PL := PL_seg) (PI := PI)) as RETf.
    lazymatch goal with
    | HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      prreg HSx (1%bv : bv 5) R1;
      eapply (RETf W _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity));
      intros mat'; apply (apost_baseF_of_base (fx := fx1) SEGS); unfold apost_base;
      exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
      split; [cbn [ms_regs]; rewrite R1, OLDf, E1 by lia; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|];
      split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJx|];
      split; [eapply (aregs_preserved_of_st_ok SEGS _ Ef _ _ regs (mr_extra n r) HSx); [exact HAEf | vm_compute; reflexivity]|]
    end.
    split.
    { apply (mr_enc_lt8 (rdW W mem) _ c bs knock mc line HBS HENC Href Hlt8).
      - intros i Hi. rewrite Hd. rewrite KEEPF by lia. rewrite HBY by lia. reflexivity.
      - apply mr_sa_val_of. unfold seg_spec.MC_NKEPT. fold n. exact VpN.
      - apply mr_sa_val_of. unfold seg_spec.MC_REFUSED. exact VpR.
      - intros a Ha H1 H2 H3. unfold seg_spec.MC_NKEPT, seg_spec.MC_REFUSED, seg_spec.SEG_M_SIZE in *. rewrite Hd in H1.
        rewrite KEEPF by lia. rewrite HK2 by (unfold RtPFCmd.CMD_SNP_K, ESTACK; lia). apply KEEPC; lia. }
    split.
    { intros a Ha HnS HnE. rewrite HSTK in HnS.
      assert (H1 : ~ (c + 8200 <= a < c + 8204)) by (intros Hq; apply HnE; right; right; unfold seg_spec.MC_REFUSED; lia).
      assert (H2 : ~ (c + 9132 <= a < c + 9136)) by (intros Hq; apply HnE; right; left; unfold seg_spec.MC_NKEPT; lia).
      assert (H3 : ~ (c + 8204 + 112 * n <= a < c + 8204 + 112 * n + 112))
        by (intros Hq; apply HnE; left; rewrite Hd; unfold seg_spec.MC_KEPT_LEN; lia).
      rewrite KEEPF by lia. rewrite HK2 by (unfold RtPFCmd.CMD_SNP_K, ESTACK; lia). apply KEEPC; lia. }
    split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs S). apply mr_set_fs_id.
  + (* 0 < line: snprintf(kept[n_kept], 112, "%s:%d: " (.str.6), c->reading, line) at 0x8785c *)
    rewrite (mr_br_ge0 E line E11 Hline) in Hc. apply negb_false_iff in Hc. apply Z.ltb_lt in Hc.
    paj_run_tok RUN HS HJ SHOK Bspan; [ mr_awr Usp Uc HSTK | ].
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14.
    assert (Tsp : spZ (ms_regs ms1) = spZ regs - 48).
    { unfold spZ at 1. rewrite Q2, Usp. rewrite unsigned_lit_small by (rewrite HSTK in Hslo; lia). lia. }
    assert (T3 : getr (ms_regs ms1) 3 = w64 (as_gp B))
      by (rewrite Q3, EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl); exact Hgp).
    assert (T4 : getr (ms_regs ms1) 4 = w64 (as_tp B))
      by (rewrite Q4, EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl); exact Htp).
    assert (T10 : getr (ms_regs ms1) 10 = w64 (seg_spec.kept_addr c (length (mc_kept mc)))).
    { rewrite Q10, (mr_a0_kept E c n E10 E33 ltac:(lia) ltac:(lia) Hn8).
      unfold seg_spec.kept_addr, seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN. fold n. try (f_equal; lia). }
    assert (T12 : getr (ms_regs ms1) 12 = w64 (SegInstA.seg_litA_fz F_addr_line)).
    { rewrite Q12, (img_env_atomP E 268 HEI ltac:(unfold A_TEXT, A_LIM; lia)).
      change (VAL 268) with (VAL (A_OBJ 27)). rewrite (VOBJS 27%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. }
    assert (T13 : getr (ms_regs ms1) 13 = w64 (c + seg_spec.MC_READING)) by (rewrite Q13, Uc; reflexivity).
    assert (T14 : getr (ms_regs ms1) 14 = w64 line) by (rewrite Q14, E11; reflexivity).
    assert (Traw : YK0s.ret_ok (Z_to_bv 64 (BASE + 11052))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
    (* every byte but refused and the frame, from the entry to the call *)
    lazymatch goal with
    | HF1 : frame_of E _ (mrestrict _ mem) (mrestrict _ (ms_mem ?m1)),
      HF2 : frame_of E _ (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)),
      HF3 : frame_of E _ (mrestrict _ (ms_mem ?m2)) (mrestrict _ (ms_mem ms1)) |- _ =>
      assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (spZ regs - 48 <= a < spZ regs) ->
        rdW W (ms_mem ms1) a = rdW W mem a)
      by (intros a Ha H1 H2;
          rewrite (KF _ _ _ HF3 ltac:(vm_compute; reflexivity) a Ha H1 H2);
          rewrite (KF _ _ _ HF2 ltac:(vm_compute; reflexivity) a Ha H1 H2);
          exact (KF _ _ _ HF1 ltac:(vm_compute; reflexivity) a Ha H1 H2))
    end.
    (* the text snprintf prints *)
    destruct (mr_reading_at _ c bs knock mc HBS HENC) as (_ & HRZ & HRL).
    assert (HRN : ~ In 0 (mc_reading mc)).
    { intros H0. rewrite Forall_forall in HRZ. specialize (HRZ 0 H0). lia. }
    destruct (mr_pf_line (mc_reading mc) line HRN ltac:(lia)) as (ps & Hparse & Hpieces & Hprec & Htext).
    assert (HlenT : Z.of_nat (length (fmt F_addr_line [AS (mc_reading mc); AI line])) <= 200).
    { rewrite fmt_addr_line, !length_app. pose proof (cut_nul_len (mc_reading mc)).
      assert (HD5 : (length (dec line) <= 5)%nat).
      { unfold dec. replace (line <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
        pose proof (dec_go_len 4 20 line [] ltac:(cbn; lia) ltac:(lia)) as Hd5. cbn [length] in Hd5. lia. }
      cbn [length]. lia. }
    pose proof (mr_sn_len (fmt F_addr_line [AS (mc_reading mc); AI line])) as Hsn.
    assert (HT : (if 0 <? line then fmt F_addr_line [AS (mc_reading mc); AI line] else fmt F_addr [AS (mc_reading mc)])
      = fmt F_addr_line [AS (mc_reading mc); AI line])
      by (replace (0 <? line) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
    eapply (srr_after_artF SEGS W _ (Z_to_bv 64 (BASE + 11052)) _ B SegInstA.STK_m_refuse (m_refuse_W c mc) regs ly S W
      mem md EV_m_refuse).
    { exact (mr_snp W (ms_regs ms1) (ms_mem ms1) _ ly S mem md regs ch c line mc knock bs F_addr_line ps
        [RtPFPf.APtr (mc_reading mc); RtPFPf.AInt line] _ _ HPRE HROD HMR0 HBS HENC HJ KEEPC Tsp Q1 Traw T3 T4 Hlt8 T10
        Q11 ltac:(left; reflexivity) T12 T13 T14 Hparse Hpieces Hprec Htext
        ltac:(replace (0 <? line) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity) HlenT). }
    intros fx1 regs2 mem2 md2 Hfx (HJ2 & HP2 & (HR10 & HBY) & HK2).
    pose proof (PaFx.st_ok_restrict_xfx fx fx1 _ _ _ _ _ HS eq_refl) as HSf. clear HS. rename HSf into HS.
    jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3]%nat HS2.
    assert (Hd : seg_spec.kept_addr c (length (mc_kept mc)) = c + 8204 + 112 * n)
      by (unfold seg_spec.kept_addr, seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN; fold n; lia).
    rewrite Hd in HBY, HK2.
    pose proof (proj1 HJ2) as HAR2.
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
    destruct (al_blocks _ _ LAWS ly S W mem2 md2 b m HAR2 Hin) as (_ & _ & _ & _ & Hbpres2 & _).
    assert (V0 : VAL (A_OBJ 0) = 0xa2a50) by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
    assert (V12 : VAL (A_OBJ 12) = 0xabff8) by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
    assert (EO0 : bv_unsigned (ew E (A_OBJ 0)) = 0xa2a50)
      by (rewrite (img_env_atomP E (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V0; reflexivity).
    assert (EO12 : bv_unsigned (ew E (A_OBJ 12)) = 0xabff8)
      by (rewrite (img_env_atomP E (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V12; reflexivity).
    lazymatch type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict]. rewrite HSTK in Hslo, Hpres2.
      repeat apply Forall_cons; try apply Forall_nil; split;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha;
        rewrite ?Usp, ?Uc in Ha; change (ew E 241) with (ew E (A_OBJ 0)) in Ha;
        change (ew E 253) with (ew E (A_OBJ 12)) in Ha; rewrite ?EO0, ?EO12 in Ha.
      - apply (mbyte_of_aview SEGS). apply HK2; unfold RtPFCmd.CMD_SNP_K, ESTACK in *; lia.
      - intros _. apply (apresent_writable SEGS). apply Hpres2. lia.
      - apply (mbyte_of_aview SEGS). apply HK2; unfold RtPFCmd.CMD_SNP_K, ESTACK, kImgEnd in *; destruct Hcimg; lia.
      - lia.
      - apply (mbyte_of_aview SEGS). apply HK2; unfold RtPFCmd.CMD_SNP_K, ESTACK, kImgEnd in *; destruct Hcimg; lia.
      - lia.
      - apply (mbyte_of_aview SEGS). apply HK2; unfold RtPFCmd.CMD_SNP_K, ESTACK in *; lia.
      - intros _. apply (apresent_writable SEGS). apply (proj1 (Hbpres2 a ltac:(lia))). }
    clear HS. rewrite <- (restrict_mkst_fx (fx := fx1)) in HS2. rename HS2 into HS.
    remember (havoc E 35 (map (getr regs2) CLOB)) as Ef eqn:HEf in HS.
    assert (HEIf : img_env VAL A_LIM Ef) by (rewrite HEf; apply img_env_havoc; [exact HEI | cbv; lia]).
    assert (OLDf : forall k, (k < 35)%nat -> ew Ef k = ew E k)
      by (intros k Hk; rewrite HEf; apply YN3v.ew_havoc_old; exact Hk).
    assert (Uspf : bv_unsigned (ew Ef 2) = spZ regs) by (rewrite OLDf by lia; exact Usp).
    assert (Ucf : bv_unsigned (ew Ef 10) = c) by (rewrite OLDf by lia; exact Uc).
    assert (HAEf : env_agree 32 (Ereg regs (mr_extra n r)) Ef).
    { destruct HAE as [HA1 HA2]. split; [intros k Hk; rewrite OLDf by lia; apply HA1; exact Hk|].
      rewrite HEf. exact HA2. }
    (* n_kept becomes a written region; it lies outside what snprintf wrote *)
    assert (HKN : forall a, c + 9132 <= a < c + 9136 -> rdW W mem2 a = rdW W mem a).
    { intros a Ha. rewrite HSTK in Hslo. rewrite HK2 by (unfold RtPFCmd.CMD_SNP_K, ESTACK; lia). apply KEEPC; lia. }
    assert (VNK2 : sa_val (rdW W mem2) (c + 9132) 4 n).
    { intros k Hk. rewrite HKN by lia. apply VNK. exact Hk. }
    assert (EO0f : bv_unsigned (ew Ef (A_OBJ 0)) = 0xa2a50)
      by (rewrite (img_env_atomP Ef (A_OBJ 0) HEIf ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V0; reflexivity).
    assert (EO12f : bv_unsigned (ew Ef (A_OBJ 12)) = 0xabff8)
      by (rewrite (img_env_atomP Ef (A_OBJ 12) HEIf ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V12; reflexivity).
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
      assert (HRn : region_ok SEGS Ef (ms_mem msx) mr_nk_w);
      [| assert (HDn : all_disjoint Ef mr_nk_w (ss_mem ssx));
         [| pose proof (st_ok_pi_add_region Ef _ _ mr_nk_w HS eq_refl HRn HDn) as HSn ] ]
    end.
    { unfold region_ok, mr_nk_w. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      cbn [ms_mem restrict]. rewrite Ucf. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hbpres2 (c + o) ltac:(lia)))|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS Ef _ c 0x23ac 4 (SOff 33 0) n).
      - cbn [sv_denot]. rewrite OLDf by lia. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside.
      - exact (mr_val_mem SEGS (w_H W) mem2 _ 4 n VNK2). }
    { lazymatch goal with |- all_disjoint _ _ (ss_mem ?ssx) =>
        let rs := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with rs end.
      apply all_disjoint_of_extents. unfold mr_nk_w.
      unfold extent_of_region; cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint].
      change (ew Ef 241) with (ew Ef (A_OBJ 0)). change (ew Ef 253) with (ew Ef (A_OBJ 12)).
      rewrite Ucf, Uspf, EO0f, EO12f. unfold zdisj. cbn [fst snd]. rewrite HSTK in Hslo.
      unfold kImgEnd in Hcimg. destruct Hcimg; repeat split; lia. }
    clear HS. rename HSn into HS.
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => let v := eval vm_compute in ssx in change ssx with v in HS end.
    assert (SHOKf : sh_ok SEGS mrBx mr_SH Ef (mrestrict (w_H W) mem2)).
    { assert (E32 : ew E 32 = Z_to_bv 64 SB)
        by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
      assert (UBx : U Ef mrBx = SHADOW_OFF).
      { unfold mrBx. rewrite U_SOff, OLDf by lia.
        rewrite E32, Z.add_0_r, unsigned_lit_small by (unfold SB; lia).
        rewrite zcanon_id by (unfold SB, M64; lia). reflexivity. }
      assert (U10 : U Ef (SOff 10 0) = c).
      { rewrite U_SOff, Ucf, Z.add_0_r. apply zcanon_id. unfold M64. lia. }
      pose proof (range_addressable_of_block SEGS B LAWS ly S W mem2 md2 b m c 9236 HAR2 Hin ltac:(lia) ltac:(lia)) as HRA2.
      unfold sh_ok, mr_SH. repeat apply Forall_cons; try apply Forall_nil;
      unfold shent_ok, app_apart; cbn [she_m she_lo she_hi];
      rewrite UBx, U10; rewrite <- (aview_rd_of SEGS); (split;
      [ eapply (range_addressable_sub _ _ _ _ _ _ HRA2); lia
      | intros a Ha; cbn [Z.min Z.max] in Ha; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia ]). }
    pose proof (paj_run (fx := fx1) B LAWS) as RUNf.
    paj_run_tok RUNf HS HJ2 SHOKf Bspan; [ mr_awr Uspf Ucf HSTK | ].
    (* the cells the tail wrote: n_kept + 1, refused + 1 *)
    lazymatch goal with
    | HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
      pose proof (st_ok_pi_region_nth Ef ssx (restrict (w_H W) msc) 0%nat _ HSx eq_refl) as HRn0;
      pose proof (st_ok_pi_region_nth Ef ssx (restrict (w_H W) msc) 4%nat _ HSx eq_refl) as HRr4;
      cbn [restrict ms_mem] in HRn0, HRr4;
      pose proof (field_of_region_any Ef _ 10%nat c _ _ _ _ _ 9132 4%N _ HRn0 Ucf ltac:(cbn; left; reflexivity)
        ltac:(lia)) as VpN;
      pose proof (field_of_region_any Ef _ 10%nat c _ _ _ _ _ 8200 4%N _ HRr4 Ucf ltac:(cbn; left; reflexivity)
        ltac:(lia)) as VpR
    end.
    rewrite (mr_soff1 Ef 33 n ltac:(rewrite OLDf by lia; exact E33) ltac:(lia) ltac:(lia)) in VpN.
    rewrite (mr_inc32 Ef 34 r ltac:(rewrite OLDf by lia; exact E34) ltac:(lia) Href) in VpR.
    change (N.to_nat 4) with 4%nat in VpN, VpR.
    (* the tail keeps every byte but its frame, n_kept and refused *)
    lazymatch goal with
    | HFx : frame_of Ef _ (mrestrict _ mem2) (mrestrict _ (ms_mem ?mf)) |- _ =>
      assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 8200 <= a < c + 8204) -> ~ (c + 9132 <= a < c + 9136) ->
        ~ (spZ regs - 48 <= a < spZ regs) -> rdW W (ms_mem mf) a = rdW W mem2 a);
      [ intros a Ha H1 H2 H3;
        refine (kept_of_frame Ef _ (w_H W) mem2 (ms_mem mf)
          (fun x => (c + 8200 <= x < c + 8204) \/ (c + 9132 <= x < c + 9136) \/ (spZ regs - 48 <= x < spZ regs))
          HFx _ a Ha _);
        [ intros bb wlo whi x Hin' Hr; vm_compute in Hin';
          repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hr;
            first [ rewrite Ucf in Hr; first [left; lia | right; left; lia]
                  | rewrite Uspf in Hr; right; right; lia | exfalso; lia ] |]);
          destruct Hin'
        | intros [Hq|[Hq|Hq]]; auto ]
      | ]
    end.
    destruct (mr_sn_text mc line) as [HSB HSL].
    rewrite HT in HSB, HSL. rewrite HSB in HBY. rewrite HSL in HBY, HK2.
    pose proof (mr_text_ok bs knock mc line HENC) as [HTN HTL].
    rewrite HSTK in Hslo.
    (* the ret *)
    pose proof (paj_ret_at (fx := fx1) (PL := PL_seg) (PI := PI)) as RETf.
    lazymatch goal with
    | HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      prreg HSx (1%bv : bv 5) R1;
      eapply (RETf W _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity));
      intros mat'; apply (apost_baseF_of_base (fx := fx1) SEGS); unfold apost_base;
      exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
      split; [cbn [ms_regs]; rewrite R1, OLDf, E1 by lia; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|];
      split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJx|];
      split; [eapply (aregs_preserved_of_st_ok SEGS _ Ef _ _ regs (mr_extra n r) HSx); [exact HAEf | vm_compute; reflexivity]|]
    end.
    split.
    { apply (mr_enc_lt8 (rdW W mem) _ c bs knock mc line HBS HENC Href Hlt8).
      - intros i Hi. rewrite Hd. rewrite KEEPF by lia. rewrite HBY by lia. reflexivity.
      - apply mr_sa_val_of. unfold seg_spec.MC_NKEPT. fold n. exact VpN.
      - apply mr_sa_val_of. unfold seg_spec.MC_REFUSED. exact VpR.
      - intros a Ha H1 H2 H3. unfold seg_spec.MC_NKEPT, seg_spec.MC_REFUSED, seg_spec.SEG_M_SIZE in *. rewrite Hd in H1.
        rewrite KEEPF by lia. rewrite HK2 by (unfold RtPFCmd.CMD_SNP_K, ESTACK; lia). apply KEEPC; lia. }
    split.
    { intros a Ha HnS HnE. rewrite HSTK in HnS.
      assert (H1 : ~ (c + 8200 <= a < c + 8204)) by (intros Hq; apply HnE; right; right; unfold seg_spec.MC_REFUSED; lia).
      assert (H2 : ~ (c + 9132 <= a < c + 9136)) by (intros Hq; apply HnE; right; left; unfold seg_spec.MC_NKEPT; lia).
      assert (H3 : ~ (c + 8204 + 112 * n <= a < c + 8204 + 112 * n + 112))
        by (intros Hq; apply HnE; left; rewrite Hd; unfold seg_spec.MC_KEPT_LEN; lia).
      rewrite KEEPF by lia. rewrite HK2 by (unfold RtPFCmd.CMD_SNP_K, ESTACK; lia). apply KEEPC; lia. }
    split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs S). apply mr_set_fs_id.
Qed.
(* inside the Sections, so the Section hypotheses (the snprintf wrapper's row 4, PALib, seg_val_objs) show as its
   assumptions *)
About m_refuse_walk.
Print Assumptions m_refuse_walk.
End e.
End f.
End d.
