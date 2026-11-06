(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_pool_config (plugin-hostd/fuzz_command, image
   fuzz_command.asan-ubsan, entry BASE + AF_sup_pool_config = 0x8bed0, 127 instructions): it proves a Theorem Labs lane's
   `tsup_pool_config_spec` (lib/B/Prog/sup_pool_config_c.v, a working branch 707acd856cb; the same text as at
   f490061c104) in the form of
   cgif_file_fuzzer's per-function walks: afn_pre at the entry, the symbolic executor over the position-abstract
   listing up to each call, the runtime's rules at the runtime calls (__asan_stack_malloc_0, the snprintf wrapper,
   the frame's release by its flag byte), the callee contracts record_c, arg_s_c, rec_shape_of_c and answer_c at the
   program calls (through cl_callS_wide / cl_callS_na), the return through paj_ret_at, and apost_base at the end.

   It is the B re-walk of the A walk lib/A/Prog/sup_pool_config.v (a working branch c4f188792bb),
   whose B code differs: B calls record() and arg_s() where A inlined record() and called xstrdup, and B inlines
   arg_i, so this function owns arg_i's class-0 side-stack frame (64 bytes, b = frame + 32) and its snprintf. The
   frame code (prologue, realignment `andi sp,sp,-32`, __asan_stack_malloc_0, header and shadow f1 f1 f1 f1 | f8 f8 |
   f3 f3, b unpoisoned around the snprintf and the second arg_s, the release through the flag byte) is arg_i's ASan
   walk's (lib/A/Prog/arg_i.v, a working branch 12dc52bfe84) and answer_code's ASan walk's
   (lib/A/Prog/answer_code.v, a working branch 2ba4488ce71); the B kit usage is socket_send's B walk
   (lib/B/Prog/socket_send.v, a working branch a470f91dbfb).

   Report and trap edges: none. The function has no `jal __asan_report_*`, no `unimp`, no UBSan handler call
   (capstone over the pin's .symtab, gen/traps.B.summary row `sup_pool_config 0`). Its branches: 0x8bf30 `beqz a2`
   on the use-after-return flag, read through the GOT word 0xa5fa8 at the record's const cell 0xb0c40 (= 1, lib/B/YF0m.v
   z4 (ANum 0xb0c40) 0x1, AR's const-cell law al_const; the executor decides it not taken); 0x8bf4c `bnez s2` and
   0x8c040 `beqz s2` on the side-stack frame (nonzero, __asan_stack_malloc_0's post; decided by the frame atom's
   fact), so the real-stack fallback 0x8bf50-0x8bf68 with its page probe and the real-stack release 0x8c074-0x8c090
   are not reached. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_pool_config.v, with its module paths and module names changed; 234 of its 315 lines of code are new or changed and 1983 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): the kit of segment S00 of the
   walk of the test harness's entry function LLVMFuzzerTestOneInput (0x84d34), file group _s10.

   THE FORM: plugin-hostd/fuzz_command's lib/A/Prog/chain_words_s1.v (origin/ossv/recipes 501c0d516c69), the
   class-3 side-stack frame walk: the entry seed with the use-after-return flag cell and the shadow-base cell
   (cw_entry, :142-222), the readers of the symbolic state at a cut (cw_reg_atom, cw_rd_chunk8, cw_saved_ok,
   :97-132) and the window skeleton lemma (cw_awr_skel, :233-235), with segconf's frame: 320 bytes realigned to 32
   (s1 = (sp - 320) & -32 of 0x84d74), the shadow base kept at 176(s1) (0x84d9c), and the 36 entry shadow bytes
   read back as SegABase.sa_zs (s10_zs_ok).

   lt_img (the image facts of every cut, LLVMFuzzerTestOneInput_defs.v) reads image bytes the runtime does not own,
   ROM bytes, and the stack-protector cells: s10_lt_img_kept carries it to any later reader at an AR state that keeps
   the image bytes the runtime does not own. lt_img's text does not give two facts at a later reader; s10_img names
   them, each a field of the listing owner's per-image record SegRecBase.seg_img_facts, so the close gives s10_img from that
   record: RELRO is in the image (cif_relro_img; RLO_A / RHI_A are SEG_RLO / SEG_RHI) and the guard's bytes have ROM
   bytes (cif_guard_rom, guardA = 0x5ff078). The stack-protector GOT word gotwA (0xa36d8) is runtime-owned (image A's
   start-up file lib/A/AF0m.v owns it), so its value at the later reader comes from AR, not from the reader before:
   the GOT word is a constant cell of AR that holds guardA (SegRecCells.crf_guard_got_chk, SegRecBase.seg_word_chk),
   under the walk hypothesis BSYM : AF0m.SegBSyms B, as SegRecCells.seg_ssp derives it (the image-A owner, 19:10Z). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YI04 YI09 YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YI16 YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF PaLibG PaLibH PaSB PaDenot PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require m_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegRecBase SegRecCells.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================== the entry state (0x84d34) ============================== *)
(* atoms of the entry state: 0-31 the registers, 32 the shadow base SB, 33 the realigned stack pointer
   s1 = (sp - 320) & -32 of 0x84d74, 34 the use-after-return flag cell *)
Notation N_SB := 32%nat (only parsing). Notation N_SP1 := 33%nat (only parsing). Notation N_UAR := 34%nat (only parsing).
Definition s10_sp1 (sp0 : Z) : Z := (sp0 - 320) - (sp0 - 320) mod 32.
(* the stores of 0x84d34 .. 0x84d9c: the zero word at sp - 320 (0x84d38), the 13 saved registers at
   [sp - 104, sp) (0x84d3c .. 0x84d6c), and 176(s1) .. 216(s1) (the shadow base at 0x84d9c, the frame base at
   0x84de0); s1 is sp - 320 or sp - 336, so the three are pairwise disjoint *)
Definition s10_stk_lo : YP09.region := YP09.mkRegion (Some 2%nat) (-320) (-312) (-320) (-312) [].
Definition s10_stk_hi : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [].
Definition s10_stk_s1 : YP09.region := YP09.mkRegion (Some N_SP1) 176 216 176 216 [].
Definition s10_regions0 : smem :=
[ s10_stk_lo; s10_stk_hi; s10_stk_s1; got_regionP; bcell_regionP N_SB; uar_got_regionP N_UAR; uar_cell_regionP N_UAR ].
Definition s10_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (N_SP1, mkAF (2^46) (2^47) 5); (N_SB, mkAF SB SB 0); (N_UAR, mkAF 0x10000 0x601000 2) ].
Definition s10_alias0 : list (sv * sv) := [ (SAlu ALU_AND (SOff 2 (-320)) (SLit (-32)), SOff N_SP1 0) ].
Definition ss_s10 : sstate := mkSS AF_LLVMFuzzerTestOneInput sr_atoms s10_regions0 None (mkFacts s10_atoms0 [] s10_alias0).
Definition s10_extra (sp0 uar : Z) : list word := map (Z_to_bv 64) [SB; s10_sp1 sp0; uar].
(* the shadow band of the token runner (fuzz_command's LEspan) *)
Definition s10_span : Z * Z := (SB, SB + 2 ^ 44 - 1).

Lemma s10_sp1_facts : forall sp0, sp0 mod 16 = 0 ->
s10_sp1 sp0 mod 32 = 0 /\ (s10_sp1 sp0 = sp0 - 320 \/ s10_sp1 sp0 = sp0 - 336).
Proof.
intros sp0 H. unfold s10_sp1. pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as M.
assert (Hm : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
{ pose proof (Z.div_mod (sp0 - 320) 32 ltac:(lia)) as D. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
  rewrite H in D2. lia. }
split; [|lia].
replace ((sp0 - 320) - (sp0 - 320) mod 32) with (32 * ((sp0 - 320) / 32))
  by (pose proof (Z.div_mod (sp0 - 320) 32 ltac:(lia)); lia).
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma s10_sp1_and : forall sp0, 0 <= sp0 - 320 < 2 ^ 64 ->
alu64 ALU_AND (Z_to_bv 64 (sp0 - 320)) (Z_to_bv 64 (-32)) = Z_to_bv 64 (s10_sp1 sp0).
Proof.
intros sp0 H. rewrite and_lit_Z. f_equal. rewrite zcanon_id by (unfold M64; lia).
change (zsigned64 (-32)) with (- 2 ^ 5). rewrite land_neg_pow2 by lia. reflexivity.
Qed.

(* ============================== reading the symbolic state back at a cut ============================== *)
Section rd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
(* a register that holds an atom (chain_words_s1.v:97-102) *)
Lemma s10_reg_atom : forall (H : word -> bool) E ss ms (r : bv 5) n,
st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
intros H E ss ms r n HS Hr. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* an 8-byte chunk of a region (chain_words_s1.v:103-111, for any value) *)
Lemma s10_rd_chunk8 : forall E H mem base off a e v cs,
Forall (YP09.chunk_ok SEGS E (mrestrict H mem) base) cs -> In (YP09.mkChunk off (CVal 8 e)) cs ->
a = base + off -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros E H mem base off a e v cs Hc Hin -> He Hv. rewrite Forall_forall in Hc. specialize (Hc _ Hin).
apply rdword_of_val_mem; [|exact Hv].
apply (val_of_chunk_ok SEGS E _ base off 8 e v Hc He); [exact Hv | cbn; lia].
Qed.
(* a saved register (fuzz_command lib/A/Prog/LLVMFuzzerTestOneInput_s10.v:207-226, over the region's chunks) *)
Lemma s10_saved_one : forall E H mem cs sp (regs : bvmap 5 word) (r : bv 5) off,
Forall (YP09.chunk_ok SEGS E (mrestrict H mem) sp) cs ->
In (YP09.mkChunk (- off) (CVal 8 (SOff (Z.to_nat (bv_unsigned r)) 0))) cs ->
ew E (Z.to_nat (bv_unsigned r)) = getr regs r ->
rdword (aview SEGS H mem) (sp - off) = Some (bv_unsigned (getr regs r)).
Proof.
intros E H mem cs sp regs r off Hc Hin Er.
pose proof (bv_unsigned_in_range 64 (getr regs r)) as Rr. change (bv_modulus 64) with (2 ^ 64) in Rr.
apply (s10_rd_chunk8 E H mem sp (- off) _ (SOff (Z.to_nat (bv_unsigned r)) 0) _ cs Hc Hin); [lia | | exact Rr].
cbn [sv_denot]. rewrite Er, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* 1-byte literal chunks: the shadow bytes the entry stores (0x84e1c .. 0x84eb0), found by a boolean check *)
Definition s10_c1 (c : YP09.chunk) (off : Z) : option Z :=
match c with
| YP09.mkChunk o (CVal w (SLit z)) =>
  if (Z.eqb o off && N.eqb w 1)%bool then Some (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0)) else None
| _ => None
end.
Fixpoint s10_lit1 (cs : list YP09.chunk) (off : Z) : option Z :=
match cs with
| [] => None
| c :: cs' => match s10_c1 c off with Some v => Some v | None => s10_lit1 cs' off end
end.
Fixpoint s10_zs_b (cs : list YP09.chunk) (off : Z) (l : list Z) : bool :=
match l with
| [] => true
| x :: l' => match s10_lit1 cs off with Some v => Z.eqb v x && s10_zs_b cs (off + 1) l' | None => false end
end.
Lemma s10_lit1_in : forall cs off v, s10_lit1 cs off = Some v ->
exists z, In (YP09.mkChunk off (CVal 1 (SLit z))) cs /\ v = bv_unsigned (byte_of_word (Z_to_bv 64 z) 0).
Proof.
induction cs as [|c cs IH]; intros off v H; cbn [s10_lit1] in H; [discriminate H|].
destruct (s10_c1 c off) as [v'|] eqn:Ec.
- injection H as <-. destruct c as [o cv]. destruct cv as [w e| len | len | d s len]; cbn [s10_c1] in Ec;
  try discriminate Ec.
  destruct e; try discriminate Ec.
  destruct ((o =? off) && (w =? 1)%N)%bool eqn:Eb; [|discriminate Ec].
  apply andb_prop in Eb as [E1 E2]. apply Z.eqb_eq in E1. apply N.eqb_eq in E2. subst o w.
  injection Ec as <-. exists z. split; [left; reflexivity | reflexivity].
- destruct (IH off v H) as (z & Hin & Hv). exists z. split; [right; exact Hin | exact Hv].
Qed.
Lemma s10_zs_ok : forall E H mem base cs l off,
Forall (YP09.chunk_ok SEGS E (mrestrict H mem) base) cs -> s10_zs_b cs off l = true ->
sa_zs (aview SEGS H mem) (base + off) l.
Proof.
intros E H mem base cs l. induction l as [|x l IH]; intros off Hc Hb i Hi; cbn [length] in Hi; [lia|].
cbn [s10_zs_b] in Hb. destruct (s10_lit1 cs off) as [v|] eqn:Ev; [|discriminate Hb].
apply andb_prop in Hb as [Hx Hl]. apply Z.eqb_eq in Hx. subst x.
destruct i as [|i].
- cbn [nth]. destruct (s10_lit1_in cs off v Ev) as (z & Hin & ->).
  rewrite Forall_forall in Hc. destruct (Hc _ Hin 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
  cbn [YP09.c_off YP09.c_val YP09.cbyte sv_denot] in Hb1, Hb2. injection Hb1 as <-.
  rewrite Z.add_0_r in Hb2. unfold aview. rewrite Z.add_0_r, Hb2. reflexivity.
- cbn [nth]. replace (base + off + Z.of_nat (Datatypes.S i)) with ((base + (off + 1)) + Z.of_nat i) by lia.
  apply (IH (off + 1) Hc Hl i). lia.
Qed.
End rd.
(* awr_ok reads only the regions' bases and windows (chain_words_s1.v:233-235) *)
Lemma s10_awr_skel : forall segs B Ex rs rs' STK sp0 FP bl0 blc fr0 lyx own,
skeleton rs' = skeleton rs -> awr_ok segs B Ex rs STK sp0 FP bl0 blc fr0 lyx own ->
awr_ok segs B Ex rs' STK sp0 FP bl0 blc fr0 lyx own.
Proof. intros segs B Ex rs rs' STK sp0 FP bl0 blc fr0 lyx own Hsk H a Ha. apply H. exact (in_wrange_skeleton Ex rs' rs a Hsk Ha). Qed.

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
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.

(* the entry seed: the symbolic state at LLVMFuzzerTestOneInput's entry (0x84d34), chain_words_s1.v's cw_entry with
   segconf's 320-byte frame, its 13 saved registers and the slot 176(s1) .. 216(s1) *)
Lemma s10_entry : forall W ly S regs mem md ch,
afn_pre SEGS B STK_LLVMFuzzerTestOneInput ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (s10_extra (spZ regs) (as_uar_cell B)))) ss_s10
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md ch HPRE.
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
set (sp0 := spZ regs) in *.
destruct (s10_sp1_facts sp0 Hal16) as (Hs1al & Hs1).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (s10_extra sp0 (as_uar_cell B)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (s10_extra sp0 (as_uar_cell B)) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth s10_extra map] in E32, E33, E34. clear EX.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12. pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
unfold kImgEnd in Hob0, Hob1, Hob12, Huar.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (HS1R : 0 <= s10_sp1 sp0 < 2 ^ 64) by (destruct Hs1 as [Hq | Hq]; rewrite Hq; lia).
unfold ss_s10. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s10_regions0, s10_stk_lo, s10_stk_hi, s10_stk_s1, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB N_SP1 (s10_sp1 sp0) E33) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. destruct Hs1 as [Hq | Hq]; lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff N_SB 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff N_UAR 0) (as_uar_cell B));
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
  + rewrite (VB N_UAR (as_uar_cell B) E34) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold s10_regions0, s10_stk_lo, s10_stk_hi, s10_stk_s1, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP,
    extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB N_SP1 (s10_sp1 sp0) E33), (VB N_UAR (as_uar_cell B) E34) by lia.
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HSTK Hob0 Hob1 Hob12 Huar Hsep Hs1. clear. intros.
  rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
  repeat split; first [ assumption | (apply or_comm; assumption) | lia ].
- split; [|split; [exact I|]].
  2: { cbn [f_alias alias_ok s10_alias0]. split; [|exact I]. cbn [sv_denot]. rewrite Usp, E33, Z.add_0_r, Z_to_bv_bv_unsigned.
       rewrite <- (s10_sp1_and sp0) by lia. reflexivity. }
  cbn [f_atoms atoms_ok s10_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HSTK Huar Huar4 Hs1al Hs1 Hal16. clear. unfold SB. intros.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End e.

(* ============================== lt_img at a later reader ============================== *)
Section img.
Variable B : asyms.
(* the two image facts lt_img needs at a later reader (the head comment says which fields of
   SegRecBase.seg_img_facts give them) *)
Record s10_img : Prop := mkS10Img {
  s10i_relro : forall a, RLO_A <= a < RHI_A -> in_img SEGS a;
  s10i_guard : forall a, guardA <= a < guardA + 8 -> seg_rom SEGS (Z_to_bv 64 a) <> None }.
Hypothesis IMGS : s10_img.
(* the record's symbols: the stack-protector GOT word is one of AR's constant cells (SegRecBase.seg_word_chk) *)
Hypothesis BSYM : AF0m.SegBSyms B.
(* a ROM byte is shown by every reader (SegRecBase.v crf_rom_view_some / crf_rdword_some) *)
Lemma s10_rom_view_some : forall (H : word -> bool) mem a, seg_rom SEGS (Z_to_bv 64 a) <> None -> aview SEGS H mem a <> None.
Proof.
intros H mem a Hr. unfold aview, mbyte. destruct (mrestrict H mem (Z_to_bv 64 a)) as [b|]; [cbn; discriminate|].
destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b|] eqn:E; [cbn; discriminate | congruence].
Qed.
Lemma s10_rdword_some : forall (rd : reader) a, (forall k, 0 <= k < 8 -> rd (a + k) <> None) -> exists v, rdword rd a = Some v.
Proof.
intros rd a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
pose proof (H 1 ltac:(lia)) as H1. pose proof (H 2 ltac:(lia)) as H2. pose proof (H 3 ltac:(lia)) as H3.
pose proof (H 4 ltac:(lia)) as H4. pose proof (H 5 ltac:(lia)) as H5. pose proof (H 6 ltac:(lia)) as H6.
pose proof (H 7 ltac:(lia)) as H7.
destruct (rd a) as [b0|]; [|congruence]. destruct (rd (a + 1)) as [b1|]; [|congruence].
destruct (rd (a + 2)) as [b2|]; [|congruence]. destruct (rd (a + 3)) as [b3|]; [|congruence].
destruct (rd (a + 4)) as [b4|]; [|congruence]. destruct (rd (a + 5)) as [b5|]; [|congruence].
destruct (rd (a + 6)) as [b6|]; [|congruence]. destruct (rd (a + 7)) as [b7|]; [|congruence].
eexists; reflexivity.
Qed.
(* the stack-protector cells at an AR state: SegRecCells.seg_ssp's proof, with s10i_guard for its cif_guard_rom *)
Lemma s10_ssp_ar : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Proof.
intros ly S W mem md HAR. split.
- exact (SegRecBase.seg_word_chk SEGS B (YG0q.AR_laws_ok SEGS B) BSYM ly S W mem md _ _ HAR
    SegRecCells.crf_guard_got_chk).
- apply s10_rdword_some. intros k Hk. apply s10_rom_view_some. apply (s10i_guard IMGS). lia.
Qed.
(* lt_img reads image bytes the runtime does not own, ROM bytes (which every reader shows) and the stack-protector
   cells (AR's, s10_ssp_ar): a reader at an AR state that keeps those image bytes keeps lt_img *)
Lemma s10_lt_img_kept : forall cx (W' : world SEGS) mem' (rd : reader) {ly' S' md'},
AR SEGS B ly' S' W' mem' md' ->
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 rdW W' mem' a = rd a) ->
lt_img B cx rd -> lt_img B cx (rdW W' mem').
Proof.
intros cx W' mem' rd ly' S' md' HAR K (HRO & HIM & HGI).
assert (KI : forall q n, sa_img SEGS B q n -> forall a, q <= a < q + n -> rdW W' mem' a = rd a).
{ intros q n0 Hq a Ha. destruct (Hq a Ha) as (H1 & H2 & H3). exact (K a H1 H2 H3). }
assert (KW : forall q n a, sa_img SEGS B q n -> q <= a -> a + 8 <= q + n -> rdword (rdW W' mem') a = rdword rd a).
{ intros q n0 a Hq H1 H2. apply rdword_ext. intros k Hk. apply (KI q n0 Hq). lia. }
assert (KL : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B (rdW W' mem') a s).
{ intros a s (Ha & ((Hz & Hn0) & _) & Hp & Hr & Hi). split; [exact Ha|]. split; [split; [split|]|].
  - intros i Hix. rewrite length_app in Hix. cbn [length] in Hix. rewrite (KI _ _ Hi); [exact (Hz i ltac:(rewrite length_app; cbn [length]; lia))|].
    lia.
  - exact Hn0.
  - exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hr).
  - split; [exact Hp|]. split; [exact Hr | exact Hi]. }
split; [|split].
- (* arodata_okP: every byte it reads is an image byte the runtime does not own *)
  intros a Hro Ho He. rewrite <- (HRO a Hro Ho He). apply K; [|exact Ho | exact He].
  destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
  exact (s10i_relro IMGS a Hr).
- destruct HIM as (Hm40 & Hm40i & HLF & HLR & (Hcp & Hci & Hcr) & HCa & (Hwp & Hwi & Hwr) & (Hrp & Hri & Hrr) & _
    & HLP & HLT & HLI & HD1 & HD2 & HD3).
  split; [|split; [exact Hm40i|]].
  { intros k Hk. rewrite (KI _ _ Hm40i); [exact (Hm40 k Hk) | lia]. }
  split; [intros s Hs; destruct (HLF s Hs) as [Hl Ha]; exact (conj (KL _ _ Hl) Ha)|].
  split; [intros s Hs; destruct (HLR s Hs) as [Hl Ha]; exact (conj (KL _ _ Hl) Ha)|].
  split.
  { split; [exact Hcp|]. split; [exact Hci|]. intros i Hi. destruct (Hcr i Hi) as (tp & Htp & Hl).
    exists tp. split; [|exact (KL _ _ Hl)]. rewrite (KW _ _ _ Hci); [exact Htp | |];
    unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, pin_spec.CAT_N in *; lia. }
  split; [exact HCa|].
  split.
  { split; [exact Hwp|]. split; [exact Hwi|]. intros i Hi. destruct (Hwr i Hi) as (wp & Hwp' & Hl).
    exists wp. split; [|exact (KL _ _ Hl)]. rewrite (KW _ _ _ Hwi); [exact Hwp' | lia | lia]. }
  split.
  { split; [exact Hrp|]. split; [exact Hri|]. intros i Hi k Hk. rewrite (KI _ _ Hri); [exact (Hrr i Hi k Hk) | lia]. }
  split; [exact (s10_ssp_ar ly' S' W' mem' md' HAR)|].
  split; [exact HLP|]. split; [exact HLT|]. split; [exact HLI|]. split; [exact HD1|]. split; [exact HD2 | exact HD3].
- intros i Hi. rewrite (KI _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HIM))))))))))))).
  + exact (HGI i Hi).
  + unfold LONGL_W, LONGL_N. lia.
Qed.
End img.
End f.
End d.
