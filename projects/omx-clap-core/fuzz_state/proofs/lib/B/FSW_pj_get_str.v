(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img's image range set to libreac/fuzz_boxreg's own (Reusable/YImgTop.v IMG_LO, IMG_TOP). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YCbq.v, with its module paths and module names changed; 234 of its 308 lines of code are new or changed and 2888 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_frame.v from a working branch
   2767db174a0, same lemma names; imports point at lib/B's image files (YB1v, YB1w, YF0x, FSH_Base, FSH_Rt, FSPstat,
   FSH_Fn_reader and the other lib/B FSW files); the image-agnostic FSupoison, FSupoisonU, FSH_YC20, FSH_Gen stay lib/A's.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_frame.v; 494 of its 531 lines of code are new or changed and 271 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_rd.v from a working branch
   2767db174a0, same lemma names; imports point at lib/B's image files (YB1v, YB1w, YF0x, FSH_Base, FSH_Rt, FSPstat,
   FSH_Fn_reader and the other lib/B FSW files); the image-agnostic FSupoison, FSupoisonU, FSH_YC20, FSH_Gen stay lib/A's.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_rd.v; 297 of its 351 lines of code are new or changed and 477 lines of the source are left out. *)
(* pj_get_str (B 0x83a54, pf.c:364-369) on fs.asan-ubsan (image B, sha256 5ac5ce0954f8...), 34 words: its ASan
   contract lib/B/FSH_Fn_reader.v pj_get_str_spec, proved by a symbolic walk of IMAGE B's OWN machine code over the
   lib/B walk kit (FSW_K / FSW_ret / FSW_rd, the image-B twins of lib/A's), in the per-function form of the released
   donor cgif_file_fuzzer as ported by a Theorem Labs lane.
   rule 24: pj_get_str (image B) is CONFIRMED to have no released ASan-image proof (reuse search by name with control,
   by every address (B 0x83894 pj_get, 0x83a54 pj_get_str, 0x83e58 pj_string, 0x83f1c pj_object) and over the named
   cold branches, outputs (internal path), r24-B3.txt, r24-cold-B3.txt,
   r24-cold-pjget-free.txt, chk-cold-extra.txt; confirmed by the read-only checker a Theorem Labs lane, chk-B4-summary.txt:
   `pj_get_str B: CONFIRM`). Its released proofs are the plain lib/Prog/pj_get_str.v and the ubsan lib/U one; the
   bespoke evt-form B proof of a working branch lib/B/Prog/pj_get_str.v is read as a TEMPLATE only (segments and
   shadow-check pcs of B's code), not imported and not bridged. This is a RE-WALK of B's code, not a port of A's: the
   image-A walk lib/A/FSW_pj_get_str.v (a working branch b3097a2a998) is the template for the kit usage, the premise
   discharges and the post; no lib/A walk-kit or lib/A image-content file is loaded here (image-closure content rule).
   The code (MEASURED, (internal path)):
     0x83a54 `addi sp,sp,-16; sd ra,8(sp); sd s0,0(sp)`; the shadow base into s0 through the GOT
     (`auipc a2; ld a2,432(a2)` = the GOT word 0x9fc10 -> the cell 0xa8438 -> SHADOW_OFF, `ld s0,0(a2)`);
     0x83a6c `jal pj_get` (ra 0x83a70); 0x83a70 `beqz a0, 0x83ab8`;
     0x83a74 `andi a1,a0,7; bnez a1, 0x83ac8` (the UBSan alignment check of the 4-byte load; 0x83ac8 is the function's
       one UBSan trap, `unimp`);
     0x83a7c the inline ASan check of the 4-byte load at a0 (`srli a2,a0,3; add a2,a2,s0; lb a2,0(a2)`, `bnez a2` to the
       slow check 0x83acc `addi a1,a1,3; blt a1,a2, 0x83a8c` / __asan_report_load4 0x83ad4);
     0x83a8c `lw a1,0(a0)` (the kid's type), `li a2,4; bne a1,a2, 0x83ab4` (0x83ab4 `li a0,0`);
     0x83a98 `addi a0,a0,16`, the inline check of the 8-byte load (`srli; add; lbu`, `bnez` to __asan_report_load8
       0x83ad8), 0x83aac `ld a0,0(a0)` (the string pointer), `j 0x83ab8`;
     0x83ab8 the epilogue and 0x83ac4 `ret`.
   UBSAN / ASAN CHECK BRANCHES, each ruled out by a NAMED premise (none is open):
     - 0x83a78 `bnez a1, 0x83ac8` (unimp, UBSan misaligned 4-byte load of the kid's type): on the a0 = 0 path the walk
       never reaches it (`beqz a0` at 0x83a70 is taken). On the hit path a0 = z0 = kids + 56 i, where pj_get_spec's
       post (Section hypothesis PJGET) gives rd_get_hit (rd_get_res: z0 = kids + 56 i, kids the o + 24 field) and
       rnode's rd_blocks_ok (kids's block is FSH_Gen.fs_rblock: kids mod 16 = 0); so z0 mod 8 = 0 (Zb below), the
       walk gives atom 10 the fact al2 = 3 (8-aligned), the engine folds `andi a1,a0,7` to the literal 0
       (Reusable/YP0m.v s_and_ptr) and the branch is decided not taken.
     - 0x83a88 `bnez a2, 0x83acc` (slow check, then __asan_report_load4 0x83ad4): the token run's shadow entry
       mkSHE 10 0 24 covers the kid's first 24 bytes, so the shadow byte of z0 reads 0 (YCbn.v tok_load, `covered`)
       and the branch is not taken; the entry's addressability is pgs_body_addressable: the kid lies in the body of
       the kids block (pj_get_spec's post: rnode / pj_node's kids block (kids, 56 cap), z0 + 56 <= kids + 56 cap),
       whose granules are addressable in the AR memory (YCbq.range_addressable_of_block) and covered by no head of U
       (FSupoisonU.fs_heads, the premise of pj_get_str_spec, carried as FH2).
     - 0x83aa8 `bnez a1, 0x83ad8` (__asan_report_load8): the same shadow entry covers [z0 + 16, z0 + 24).
   The walk: entry FSW_K.fsw_entryT, the journal over the unpoisoned memory, FSW_K.fsw_aj_run_toU up to A_pj_get; the
   callee's fpreU (FSW_ret.fsw_fpreU_at) and the reader premises carried to the call memory (FSW_rd.rnode_below,
   pobj_below, FSW_K.cstr_ok_below, fs_glob_below); SRr_bind with pj_get's contract (Section hypothesis PJGET); the resume
   (FSW_K.fsw_after_callU), then two paths:
   - a0 = 0 (o = 0, a non-object, or no member named kname): the branch decided by SRr_sym_branch, one run to `ret`.
   - a0 = z0, the hit kid: the resume state gains a read-only region for the kid's first 24 bytes at atom 10 (type word
     literal, str pointer an extra atom; FSW_pj.fsw_pj_part_okR with fsw_pj_chunk4 / fsw_pj_chunk8 from the kid's pj_hdr,
     YI0n.st_ok_add_region') and the facts of atoms 10 (the kid, 8-aligned) and 8 (s0 = SHADOW_OFF); one TOKEN run
     (FSW_K.fsw_aj_run_tokU, Bx := SOff 8 0, the s0 register, one shent for the kid's 24 bytes) decides the UBSan check
     and both inline ASan checks as above, so neither the trap nor a report call is reached.
   Final return through FSW_ret.fsw_retU; the answer mirrors the plain proof lib/Prog/pj_get_str.v.
   The needle k: cstr_ok and cstr_kept go to pj_get at the same layout and state and come back from pj_get's post.
   Local lemmas (no kit copy): the PjStruct transport below alloc_ceiling (pgs_u64_below, pgs_cstr_below), the kid
   addressability (pgs_body_addressable), same_below from a run's write windows (pgs_same_below_wr). The struct pj
   field-to-chunk lemmas are the lib/B kit's FSW_pj.v.
   SK is the Section's abstract Context (no sink_head instance is in scope at the file level): the theorem holds at
   every sink head, in particular at build B's FSH_Base.fsB_sink_head. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_ret FSW_rd FSW_pj FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSW_pj_get_str_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the header of any node *)
Lemma pgs_node_hdr : forall m lblk p t D, PjStruct.pj_node tfibsegs m lblk p t D ->
  exists num str kids keys n cap, PjStruct.pj_hdr tfibsegs m p (PjTree.tag t) num str kids keys n cap.
Proof.
intros m lblk p t D H. destruct t; cbn [PjStruct.pj_node] in H;
  destruct H as (_ & _ & num & str & kids & keys & n & cap & HH & _); exists num, str, kids, keys, n, cap; exact HH.
Qed.

(* a run whose write windows all lie at or above lo leaves memory below lo unchanged (the FSH_check_reject_clean.v
   template's same_below_wr) *)
Lemma pgs_same_below_wr : forall E rs (m m' : word -> option byte) lo,
  frame_of E rs m m' -> (forall a, in_wrange E rs a -> lo <= a) -> lo <= 2 ^ 64 -> same_below m m' lo.
Proof.
intros E rs m m' lo HF Hw H64 x Hx. apply HF. rewrite unsigned_lit_small by lia. intros Hin.
pose proof (Hw _ Hin). lia.
Qed.

(* the resumed frame's chunks: ra at 8, s0 at 0, the walk's extra atoms 32 and 33 *)
Definition pgs_cs : list YP09.chunk := [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
(* the hit kid's first 24 bytes at atom 10: the type word (a literal) and the string pointer (extra atom 34) *)
Definition pgs_kid (ty : Z) : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 24 0 0 [YP09.mkChunk 0 (CVal 4 (SLit ty)); YP09.mkChunk 16 (CVal 8 (SOff 34 0))].
(* the callee-saved registers at the return: sp back up by the frame, s0 reloaded (atom 33), the rest kept *)
Definition pgs_expect (r : bv 5) : sv :=
  match bv_unsigned r with 2 => SOff 2 16 | 8 => SOff 33 0 | z => SOff (Z.to_nat z) 0 end.
Lemma pgs_chk : forall regs2 (ra s0 : word) rest m b,
  val_mem tfibsegs m (b + 8) 8 (bv_unsigned ra) -> val_mem tfibsegs m (b + 0) 8 (bv_unsigned s0) ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (ra :: s0 :: rest)) m b) pgs_cs.
Proof.
intros regs2 ra s0 rest m b Vra Vs0. unfold pgs_cs. constructor; [|constructor; [|constructor]].
- apply (chunk_ok_val tfibsegs _ _ _ 8 8%N (SOff 32 0) (bv_unsigned ra)); [| apply u64_range | cbn; lia | exact Vra].
  rewrite fsw_SOff0. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth]. symmetry. apply Z_to_bv_bv_unsigned.
- apply (chunk_ok_val tfibsegs _ _ _ 0 8%N (SOff 33 0) (bv_unsigned s0)); [| apply u64_range | cbn; lia | exact Vs0].
  rewrite fsw_SOff0. change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. cbn [nth]. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Section L. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ---- PjStruct facts across same_below m m' alloc_ceiling ---- *)
Lemma pgs_u64_below : forall H m m' a v, same_below m m' alloc_ceiling -> 0 <= a -> a + 8 <= alloc_ceiling ->
  PjStruct.pj_u64 tfibsegs (mrestrict H m) a v -> PjStruct.pj_u64 tfibsegs (mrestrict H m') a v.
Proof.
intros H m m' a v Hs Ha Hb Hv. apply (PjStruct.pj_u64_eq tfibsegs (mrestrict H m) (mrestrict H m') a v Hv).
intros x Hx. apply (fsw_mrestrict_below H m m' x Hs). lia.
Qed.
Lemma pgs_cstr_below : forall H m m' (lblk : Z -> Z -> Prop) a n s, same_below m m' alloc_ceiling -> 0 <= a ->
  a + n <= alloc_ceiling ->
  PjStruct.pj_cstr tfibsegs (mrestrict H m) lblk a n s -> PjStruct.pj_cstr tfibsegs (mrestrict H m') lblk a n s.
Proof.
intros H m m' lblk a n s Hs Ha Hb (Hl & Hn & HF & HB). split; [exact Hl|]. split; [exact Hn|]. split; [exact HF|].
apply (PjStruct.pj_bytes_eq tfibsegs (mrestrict H m) (mrestrict H m') a _ HB).
intros x Hx. apply (fsw_mrestrict_below H m m' x Hs). rewrite length_map, length_app in Hx. cbn [length] in Hx. lia.
Qed.

(* ---- the body of a live block past its 16-byte head is addressable on the MACHINE's memory: AR (over the unpoisoned
   memory) makes its granules addressable (YCbq.range_addressable_of_block), and no head of U covers them, because each
   head is the start of a live block (FSupoisonU.fs_heads) and live blocks are pairwise disjoint (AR_blocks_law) ---- *)
Lemma pgs_body_addressable : forall B ly S U (W : world tfibsegs) mem md P n z len,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  In (P, n) (ablocks B ly S) -> P + 16 <= z -> 0 <= len -> z + len <= P + req_size n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF z len.
Proof.
intros B ly S U W mem md P n z len HARU FH Hin Hz Hl Hn.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md P n z len HAR Hin ltac:(lia) Hn)
  as HRA.
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md P n HAR Hin) as (HP16 & HP4096 & HPc & _ & _ & PW & _).
pose proof asan_consts as (C1 & _).
intros x Hx. destruct (HRA x Hx) as (s & Es & Hok). exists s. split; [|exact Hok].
assert (NI : in_ush U (bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x))) = false).
{ rewrite wz by (unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
  destruct (in_ush U (shadow_of_addr SHADOW_OFF x)) eqn:EU; [|reflexivity]. exfalso.
  apply in_ush_spec in EU as ((h & q) & Hr & Hs). cbn [fst snd] in Hs.
  destruct (FH (h, q) Hr) as (E16 & m & Hm & M16). cbn [fst snd] in E16, Hm. subst q.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md h m HAR Hm) as (Hh16 & _).
  unfold shadow_addr, shadow_of_addr in Hs. change (16 / 8) with 2 in Hs.
  assert (Hxg : h <= x < h + 16) by (Z.div_mod_to_equations; lia).
  destruct (Z.eq_dec h P) as [->|NE]; [lia|].
  assert (I1 : In (h, req_size m) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
    by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (h, m)); exact Hm).
  assert (I2 : In (P, req_size n) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
    by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (P, n)); exact Hin).
  destruct (pairwise_In2 zdisjoint _ _ _ PW I1 I2 ltac:(intros E; injection E; intros _ E'; exact (NE E')))
    as [D|D]; unfold zdisjoint in D; cbn [fst snd] in D; lia. }
rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem _ NI). exact Es.
Qed.
End L.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the image facts of the reader Section (lib/B/FSH_Fn_reader.v Section c, Hypothesis IMG; owner S0 / the final build-B
   asyms instance); unused by this walk *)
Hypothesis IMG : fs_img_facts tfibsegs B.
(* owner RELOC: S0's FsShadowSyms for build B (lib/B/FSH_Base.v: as_got_shadow B = 0x9fc10, as_shadow_cell B =
   0xa8438), discharged by build B's relocated start-up / TfibB instance *)
Hypothesis HSS : FsShadowSyms B.
(* owner READER (a Theorem Labs lane, the image-B pj_get walk): pj_get's ASan contract, lib/B/FSH_Fn_reader.v
   pj_get_spec (B 0x83894) *)
Hypothesis PJGET : @pj_get_spec fx rc SK tfibsegs B.

Theorem pj_get_str_holds : @pj_get_str_spec fx rc SK tfibsegs B.
Proof.
destruct HSS as [Hgot Hcell].
intros ly S U W regs mem md ch o k kname t D UL live peak cnt fail HPRE FH H10 H11 HO HK HKk HGl.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
destruct HPRE as [HAPU HRO].
pose proof (fsw_sp B _ ly S U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HAPU as (HAP & _ & _).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_ARU B _ ly S U W regs mem md ch HAPU) as HARU.
assert (FS : STK_pj_get_str = ltac:(let v := eval vm_compute in (STK_pj_get_str) in exact v)) by (vm_compute; reflexivity).
assert (FG : STK_pj_get = ltac:(let v := eval vm_compute in (STK_pj_get) in exact v)) by (vm_compute; reflexivity).
rewrite FS in Hceil.
assert (OB : o <> 0 -> 0 <= o /\ o + 56 <= alloc_ceiling).
{ intros O0. destruct HO as [HO|(_ & HPo)]; [contradiction|].
  pose proof (fsw_pobj_low B ly S W (unpoison U mem) md mem o HAR HPo) as (L1 & L2). lia. }
pose proof (fsw_entryT B STK_pj_get_str 16 ly S U W regs mem md ch A_pj_get_str Hgot Hcell HAPU
  ltac:(lia) ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init tfibsegs B STK_pj_get_str [] ly S W regs (unpoison U mem) md ch HAP) as HJ.
assert (Usp : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 A_pj_get_str) with (Z_to_bv 64 A_pj_get_str).
(* ---- 0x83a54 .. the call of pj_get at 0x83a6c ---- *)
fsw_aj_run_toU pj_get_str_tbl_ok HS HJ HARU A_pj_get.
{ awr_ok_tac. exact Usp. }
rename ms into msC. rename HS into HSc.
assert (SB1 : same_below mem (ms_mem msC) alloc_ceiling).
{ apply (pgs_same_below_wr (Ereg regs fs_extraT) _ mem (ms_mem msC) alloc_ceiling HF); [|lia].
  intros a (r & Hin & Hr). cbn [fss0T fsT_regions ss_mem In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]];
    cbn [fstk fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [rewrite Usp in Hr | | ];
    lia. }
clear HF HFr HG.
pose proof (fsw_reg_lit _ _ _ msC 1%bv 0x83a70 HSc ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (fsw_reg_off _ _ _ msC 2%bv 2 (-16) (spZ regs) HSc ltac:(vm_compute; reflexivity) Usp ltac:(lia)) as R2.
pose proof (fsw_reg_atom _ regs fs_extraT _ msC 3%bv 3%bv 3 HSc ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fsw_reg_atom _ regs fs_extraT _ msC 4%bv 4%bv 4 HSc ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fsw_reg_extra _ regs fs_extraT _ msC 8%bv 0 HSc ltac:(vm_compute; reflexivity)) as R8.
unfold fs_extraT in R8. cbn [nth] in R8.
pose proof (fsw_reg_atom _ regs fs_extraT _ msC 10%bv 10%bv 10 HSc ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fsw_reg_atom _ regs fs_extraT _ msC 11%bv 11%bv 11 HSc ltac:(vm_compute; reflexivity) eq_refl) as R11.
assert (Hspc : spZ (ms_regs msC) = spZ regs - 16) by (unfold spZ at 1; rewrite R2; lia).
(* the callee's pre at the call *)
pose proof (fsw_fpreU_at B STK_pj_get_str (spZ regs) ly S U W mem md ly S W (ms_mem msC) _ 0 (ms_regs msC) STK_pj_get
  (-16) [] HJ HARU (arodata_below B W mem (ms_mem msC) SB1 HRO) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)
  ltac:(lia)
  ltac:(rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity)
  ltac:(unfold raZ; rewrite R1, unsigned_lit_small by lia; lia)
  ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp)
  ltac:(apply achain_low; unfold s0Z; rewrite R8, unsigned_lit_small by (unfold SHADOW_OFF; lia);
        unfold SHADOW_OFF; lia)) as HPREc.
assert (HOc : o = 0 \/ rnode tfibsegs B ly S W (ms_mem msC) UL o t D /\ pobj tfibsegs B ly S W (ms_mem msC) o).
{ destruct HO as [HO|(HN & HPo)]; [left; exact HO | right].
  pose proof (fsw_pobj_low B ly S W (unpoison U mem) md mem o HAR HPo) as (Lo1 & Lo2).
  split; [exact (rnode_below B ly S W (unpoison U mem) md mem (ms_mem msC) UL o t D HAR SB1 ltac:(lia) Lo2 HN)
         | exact (pobj_below B ly S W (unpoison U mem) md mem (ms_mem msC) o HAR SB1 HPo)]. }
pose proof (cstr_ok_below W mem (ms_mem msC) k kname SB1 HK) as HKc.
pose proof (fs_glob_below W mem (ms_mem msC) live peak cnt fail SB1 HGl) as HGc.
(* the frame's saved ra and s0, read at the call *)
pose proof (fsw_region_nth (Ereg regs fs_extraT) _ _ 0 _ HSc eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pose proof (fsw_field (Ereg regs fs_extraT) _ 2 (spZ regs) _ _ _ _ _ (-8) 8%N (SOff 1 0) (raZ regs) HR0 Usp
  ltac:(cbn; tauto)
  ltac:(rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 1 1%bv eq_refl); unfold raZ; symmetry;
        apply Z_to_bv_bv_unsigned)
  ltac:(unfold raZ; apply u64_range) ltac:(cbn; lia)) as Vra.
pose proof (fsw_field (Ereg regs fs_extraT) _ 2 (spZ regs) _ _ _ _ _ (-16) 8%N (SOff 8 0) (s0Z regs) HR0 Usp
  ltac:(cbn; tauto)
  ltac:(rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT 8 8%bv eq_refl); unfold s0Z; symmetry;
        apply Z_to_bv_bv_unsigned)
  ltac:(unfold s0Z; apply u64_range) ltac:(cbn; lia)) as Vs0.
clear HR0.
(* ---- pj_get (PJGET) ---- *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ msC HSc eq_refl). cbn [ss_pc].
eapply SRr_bind;
  [exact (PJGET ly S U W (ms_regs msC) (ms_mem msC) _ [] o k kname t D UL live peak cnt fail HPREc FH
            ltac:(rewrite R10; exact H10) ltac:(rewrite R11; exact H11) HOc HKc HKk HGc) |].
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & OK2 & PO2 & HP2 & HQ2).
rewrite R1.
destruct HQ2 as (Hbl2 & HK2 & HKk2 & HG2 & HRES).
assert (Esp2 : forall xs, bv_unsigned (ew (Ereg regs2 xs) 2) = spZ regs + -16).
{ intros xs. rewrite (ew_Ereg_nat regs2 xs 2 2%bv eq_refl).
  rewrite (fsw_pres _ _ 2%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)). rewrite R2. lia. }
assert (E8 : forall xs, ew (Ereg regs2 xs) 8 = Z_to_bv 64 SHADOW_OFF).
{ intros xs. rewrite (ew_Ereg_nat regs2 xs 8 8%bv eq_refl).
  rewrite (fsw_pres _ _ 8%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)). exact R8. }
assert (FH2 : FSupoisonU.fs_heads B ly2 S2 U) by (intros r Hr; rewrite Hbl2; exact (FH r Hr)).
assert (CHK : forall rest, Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (getr regs 1 :: getr regs 8 :: rest))
  (mrestrict (w_H W) (ms_mem msC)) (spZ regs - 16)) pgs_cs).
{ intros rest. apply pgs_chk.
  - replace (spZ regs - 16 + 8) with (spZ regs + -8) by lia. exact Vra.
  - replace (spZ regs - 16 + 0) with (spZ regs + -16) by lia. exact Vs0. }
(* the two paths: a0 = 0, or the hit kid *)
assert (PATH :
  (getr regs2 10 = w64 0 /\
   (o = 0 \/ o <> 0 /\ rnode tfibsegs B ly2 S2 W2 mem2 UL o t D /\
      forall m, rd_get_str_res tfibsegs m (fun a n => In (a, n) UL) o t D kname 0)) \/
  (o <> 0 /\ rnode tfibsegs B ly2 S2 W2 mem2 UL o t D /\
   exists members i v kids Di z0, t = PjTree.JObj members /\ getr regs2 10 = w64 z0 /\
     nth_error members i = Some (kname, v) /\
     (forall j nm u, (j < i)%nat -> nth_error members j = Some (nm, u) -> nm <> kname) /\
     PjStruct.pj_u64 tfibsegs (mrestrict (w_H W2) mem2) (o + 24) kids /\ z0 = kids + 56 * Z.of_nat i /\
     PjStruct.pj_node tfibsegs (mrestrict (w_H W2) mem2) (fun a n => In (a, n) UL) z0 v Di /\ incl Di D)).
{ destruct HRES as [(O0 & Z0) | (O0 & HN2 & z0 & Z0 & GR)].
  - left. split; [exact Z0 | left; exact O0].
  - destruct t as [ | | | txt bits | s | items | members]; cbn [rd_get_res] in GR.
    1-6: subst z0; left; split; [exact Z0|]; right; split; [exact O0|]; split; [exact HN2|];
         intros m; cbn [rd_get_str_res]; reflexivity.
    destruct GR as [(MISS & ->) | HIT].
    + left. split; [exact Z0|]. right. split; [exact O0|]. split; [exact HN2|].
      intros m. cbn [rd_get_str_res]. left. split; [exact MISS | reflexivity].
    + unfold rd_get_hit in HIT. destruct HIT as (i & v & kids & Di & Ei & Hpre & HK24 & Ez & Hv & Hinc).
      right. split; [exact O0|]. split; [exact HN2|].
      exists members, i, v, kids, Di, z0. split; [reflexivity|]. repeat (split; [eassumption|]). exact Hinc. }
pose proof HJc as (HARc2 & _).
clear HRES.
destruct PATH as [(Z0 & RZ) | (O0 & HN2 & members & i & v & kids & Di & z0 & -> & Z0 & Ei & Hpre & HK24 & Ez & Hv & Hinc)].
- (* ==== a0 = 0: `beqz a0` (0x83a70) taken, the epilogue 0x83ab8, `ret` 0x83ac4 ==== *)
  destruct (fsw_after_callU B STK_pj_get_str (spZ regs) ly S U W mem md ly S U (ms_mem msC) _ 0 STK_pj_get 16
    (ms_regs msC) ly2 S2 U W2 regs2 mem2 md2 0 [getr regs 1; getr regs 8] pgs_cs 0x83a70 HJ HARU HJc OK2 PO2 HP2
    Hspc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(repeat constructor; cbn; lia) (CHK [])) as [HJ2 HS2].
  pose proof (Esp2 [getr regs 1; getr regs 8]) as Esp.
  pose proof HJ2 as (HAR2 & _).
  assert (HARU2 : ARU tfibsegs B ly2 S2 U W2 mem2 md2) by (split; [exact HAR2 | split; [exact OK2 | exact PO2]]).
  eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0); [exact HS2 | intros _ HS3 | intros Hb _].
  2: { exfalso. rewrite fsw_SOff0, (ew_Ereg_nat regs2 _ 10 10%bv eq_refl), Z0 in Hb. vm_compute in Hb.
       discriminate Hb. }
  clear HS2.
  fsw_aj_runU pj_get_str_tbl_ok HS3 HJ2 HARU2.
  { fsw_awr_ret Esp 16. }
  fsw_sb Esp.
  pose proof (fsw_reg_extra _ regs2 [getr regs 1; getr regs 8] _ ms 1%bv 0 HS3 ltac:(vm_compute; reflexivity)) as R1F.
  cbn [nth] in R1F.
  pose proof (fsw_reg_atom _ regs2 [getr regs 1; getr regs 8] _ ms 10%bv 10%bv 10 HS3
    ltac:(vm_compute; reflexivity) eq_refl) as R10F.
  eapply (fsw_retU B pj_get_str_tbl pj_get_str_tbl_ok W2 _ _ ms);
    [exact HS3 | reflexivity | vm_compute; reflexivity | rewrite R1F; exact Hra | exact HJ2 | exact HARU2
    | apply (fsw_preserved _ _ _ ms regs pgs_expect HS3); [vm_compute; reflexivity | fsw_cs_cases pgs_expect HSc HP2 Esp]
    | ].
  intros matf. cbv beta.
  split; [exact Hbl2|].
  split; [exact (cstr_ok_below W2 mem2 (ms_mem ms) k kname SB HK2)|].
  split; [exact HKk2|].
  split; [exact (fs_glob_below W2 mem2 (ms_mem ms) live peak cnt fail SB HG2)|].
  assert (A0 : getr (ms_regs ms) 10 = w64 0) by (rewrite R10F; exact Z0).
  destruct RZ as [O0 | (O0 & HN2 & HRZ)]; [left; split; [exact O0 | exact A0] | right].
  split; [exact O0|].
  split; [exact (rnode_below B ly2 S2 W2 (unpoison U mem2) md2 mem2 (ms_mem ms) UL o t D HAR2 SB
                   (proj1 (OB O0)) (proj2 (OB O0)) HN2)|].
  exists 0. split; [exact A0 | apply HRZ].
- (* ==== a0 = z0, the hit kid ==== *)
  pose proof (OB O0) as (Lo1 & Lo2).
  pose proof HN2 as (HPN & HBK & HINC).
  pose proof HPN as HPN'. cbn [PjStruct.pj_node] in HPN'.
  destruct HPN' as (_ & _ & num & str & kids' & keys & nn & cap & HH & Hstr0 & Hnn & Hncap & Hcap & Di0 & ED0 & Hmems).
  pose proof HH as (_ & _ & _ & _ & HK24' & _).
  pose proof (PjStruct.pj_u64_uniq tfibsegs _ _ _ _ HK24 HK24') as <-.
  assert (Hil : (i < length members)%nat) by (apply nth_error_Some; rewrite Ei; discriminate).
  destruct Hcap as [(C0 & _) | (CP & Lk & Ly)]; [lia|].
  pose proof (HBK kids (56 * cap) Lk) as HKB.
  pose proof HKB as (Hkin & Hk16 & Hkpos & _).
  pose proof (fsw_rblock_low B ly2 S2 W2 _ md2 mem2 kids (56 * cap) HARc2 HKB) as (Kl1 & Kl2).
  unfold HEAD in *.
  assert (RQ : req_size (56 * cap + 16) = 56 * cap + 16)
    by (unfold req_size; destruct (Z.eqb_spec (56 * cap + 16) 0); lia).
  destruct (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U mem2) md2 (kids - 16) (56 * cap + 16) HARc2 Hkin)
    as (_ & _ & _ & Happ & _).
  rewrite RQ in Happ.
  (* the UBSan alignment check 0x83a74 / 0x83a78: z0 = kids + 56 i (pj_get's rd_get_hit) with kids mod 16 = 0
     (fs_rblock of the kids block, rnode's rd_blocks_ok), so z0 is 8-aligned and the trap 0x83ac8 is not reached *)
  assert (Zb : kids <= z0 /\ z0 + 56 <= kids + 56 * cap /\ z0 mod 8 = 0).
  { subst z0. split; [lia|]. split; [nia|]. Z.div_mod_to_equations. lia. }
  destruct (pgs_node_hdr _ _ _ _ _ Hv) as (num2 & str2 & kids2 & keys2 & n2 & cap2 & HH2).
  pose proof HH2 as (_ & HT & _ & HS16 & _).
  set (xs := [getr regs 1; getr regs 8; Z_to_bv 64 str2]).
  destruct (fsw_after_callU B STK_pj_get_str (spZ regs) ly S U W mem md ly S U (ms_mem msC) _ 0 STK_pj_get 16
    (ms_regs msC) ly2 S2 U W2 regs2 mem2 md2 0 xs pgs_cs 0x83a70 HJ HARU HJc OK2 PO2 HP2
    Hspc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(repeat constructor; cbn; lia) (CHK [Z_to_bv 64 str2])) as [HJ2 HS2].
  pose proof (Esp2 xs) as Esp.
  pose proof HJ2 as (HAR2 & _).
  assert (HARU2 : ARU tfibsegs B ly2 S2 U W2 mem2 md2) by (split; [exact HAR2 | split; [exact OK2 | exact PO2]]).
  assert (E10 : ew (Ereg regs2 xs) 10 = Z_to_bv 64 z0) by (rewrite (ew_Ereg_nat regs2 xs 10 10%bv eq_refl); exact Z0).
  assert (U10 : bv_unsigned (ew (Ereg regs2 xs) 10) = z0) by (rewrite E10; apply wz; lia).
  (* the kid's region and the facts of atoms 10 and 8 *)
  assert (RK : region_ok tfibsegs (Ereg regs2 xs) (mrestrict (w_H W2) mem2) (pgs_kid (PjTree.tag v))).
  { unfold pgs_kid.
    apply (fsw_pj_part_okR tfibsegs _ _ 10 z0 z0 0 24 _ ltac:(lia) ltac:(lia) U10 ltac:(lia) ltac:(lia)).
    constructor; [|constructor; [|constructor]].
    - apply (fsw_pj_chunk4 tfibsegs _ _ z0 0 _ (PjTree.tag v)); [rewrite Z.add_0_r; exact HT | reflexivity].
    - apply (fsw_pj_chunk8 tfibsegs _ _ z0 16 _ str2); [exact HS16|].
      rewrite fsw_SOff0. change 34%nat with (32 + 2)%nat. rewrite ew_Ereg_extra. reflexivity. }
  pose proof (st_ok_add_region' tfibsegs _ _ _ (pgs_kid (PjTree.tag v)) HS2 eq_refl RK
    ltac:(cbn [ss_mem fss_ret all_disjoint]; split; [|exact I];
          unfold extent_disjoint, pgs_kid, fstk_ret;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U10, Esp; left; lia)) as HS3.
  (* atom 10 is 8-aligned (al2 = 3, from Zb): the engine folds `andi a1,a0,7` (0x83a74) to 0 *)
  pose proof (st_ok_add_fact tfibsegs _ _ _ 10 (mkAF 4096 0x7fffff800000 3) HS3
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U10; change (2 ^ 3) with 8; lia)) as HS4.
  pose proof (st_ok_add_fact tfibsegs _ _ _ 8 (mkAF SHADOW_OFF SHADOW_OFF 0) HS4
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (E8 xs), wz by (unfold SHADOW_OFF; lia);
          rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS5.
  clear HS2 HS3 HS4.
  (* the token run's shadow entry: the kid's 24 bytes are addressable *)
  pose proof (pgs_body_addressable B ly2 S2 U W2 mem2 md2 (kids - 16) (56 * cap + 16) z0 24 HARU2 FH2 Hkin
    ltac:(lia) ltac:(lia) ltac:(rewrite RQ; lia)) as RAZ.
  assert (SHOK : sh_ok tfibsegs (SOff 8 0) [mkSHE 10 0 24] (Ereg regs2 xs) (mrestrict (w_H W2) mem2)).
  { unfold sh_ok. constructor; [|constructor].
    apply (shent_ok_of_range tfibsegs (w_H W2) mem2 (Ereg regs2 xs) (SOff 8 0) 10 z0 24 z0 0 24 RAZ).
    - apply U_atom; [exact (E8 xs) | unfold SHADOW_OFF; lia].
    - apply U_atom; [exact E10 | lia].
    - lia.
    - lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx.
      unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
  (* the type word is a literal of the run: one case per constructor *)
  destruct v as [ | | | txt bits | s | items | mems]; cbn [PjTree.tag] in HS5.
  all: fsw_aj_run_tokU pj_get_str_tbl_ok HS5 HJ2 HARU2 SHOK fs_Bspan.
  all: try (cbn [add_atom ss_mem fss_ret]; apply awr_ok_cons_ro; [cbn; lia|];
            eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -16);
            [reflexivity | exact Esp | cbn; lia | cbn; lia | apply awr_ok_nil]).
  all: assert (SBf : same_below mem2 (ms_mem ms) alloc_ceiling)
         by (apply (pgs_same_below_wr (Ereg regs2 xs) _ mem2 (ms_mem ms) alloc_ceiling HF); [|lia];
             intros a (r & Hin & Hr); cbn [add_atom ss_mem fss_ret In] in Hin;
             destruct Hin as [<- | [<- | []]];
             cbn [pgs_kid fstk_ret YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia | rewrite Esp in Hr; lia]).
  all: pose proof (fsw_reg_extra _ regs2 xs _ ms 1%bv 0 HS5 ltac:(vm_compute; reflexivity)) as R1F.
  all: eapply (fsw_retU B pj_get_str_tbl pj_get_str_tbl_ok W2 _ _ ms);
    [exact HS5 | reflexivity | vm_compute; reflexivity | rewrite R1F; exact Hra | exact HJ2 | exact HARU2
    | apply (fsw_preserved _ _ _ ms regs pgs_expect HS5); [vm_compute; reflexivity | fsw_cs_cases pgs_expect HSc HP2 Esp]
    | ].
  all: intros matf; cbv beta.
  all: split; [exact Hbl2|].
  all: split; [exact (cstr_ok_below W2 mem2 (ms_mem ms) k kname SBf HK2)|].
  all: split; [exact HKk2|].
  all: split; [exact (fs_glob_below W2 mem2 (ms_mem ms) live peak cnt fail SBf HG2)|].
  all: right; split; [exact O0|].
  all: split; [exact (rnode_below B ly2 S2 W2 (unpoison U mem2) md2 mem2 (ms_mem ms) UL o (PjTree.JObj members) D
                       HAR2 SBf Lo1 Lo2 HN2)|].
  1-4, 6-7:
    (exists 0; split;
     [ exact (fsw_reg_lit _ _ _ ms 10%bv 0 HS5 ltac:(vm_compute; reflexivity) ltac:(lia))
     | cbn [rd_get_str_res]; right; do 3 eexists; split; [exact Ei|]; split; [exact Hpre|];
       split; [exact (pgs_u64_below _ _ _ (o + 24) kids SBf ltac:(lia) ltac:(lia) HK24) | reflexivity] ]).
  (* the string kid *)
  exists str2. split.
  { rewrite (fsw_reg_extra _ regs2 xs _ ms 10%bv 2 HS5 ltac:(vm_compute; reflexivity)). reflexivity. }
  cbn [rd_get_str_res]. right. exists i, (PjTree.JStr s), kids. split; [exact Ei|]. split; [exact Hpre|].
  split; [exact (pgs_u64_below _ _ _ (o + 24) kids SBf ltac:(lia) ltac:(lia) HK24)|].
  cbn [PjStruct.pj_node] in Hv.
  destruct Hv as (_ & _ & num3 & str3 & kids3 & keys3 & n3 & cap3 & HH3 & _ & _ & _ & _ & kk & Hc3 & ED).
  pose proof HH3 as (_ & _ & _ & HS16' & _).
  pose proof (PjStruct.pj_u64_uniq tfibsegs _ _ _ _ HS16 HS16') as <-.
  split; [rewrite <- Ez; exact (pgs_u64_below _ _ _ (z0 + 16) str2 SBf ltac:(lia) ltac:(lia) HS16)|].
  pose proof Hc3 as (Hlk & _).
  pose proof (fsw_rblock_low B ly2 S2 W2 _ md2 mem2 str2 kk HARc2 (HBK str2 kk Hlk)) as (Sl1 & Sl2). unfold HEAD in Sl1.
  exists kk. split; [exact (pgs_cstr_below _ _ _ _ str2 kk s SBf ltac:(lia) Sl2 Hc3)|].
  apply Hinc. rewrite ED. left. reflexivity.
Qed.
End W.
