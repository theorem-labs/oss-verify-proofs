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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 622 of its 662 lines of code are new or changed and 413 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): piece 1 of segment S14 of the
   walk of the test harness's entry function LLVMFuzzerTestOneInput (0x84d34), file group _s22a: the statement
   s22_p1_stmt of LLVMFuzzerTestOneInput_s22k.v, from the head of the inlined m_declared loop at turn i (cut
   K858f4 i, 0x858f4) to the continue join (S22_JOIN, 0x859c4) when m->seg[i].ignore is set, or to the return of
   the strrchr wrapper (S22_VR, 0x85930) when it is not.

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep, output in the walk's shared brief; checker (fresh, read-only): CONFIRM; none:
   written new); this file is one piece of one segment lemma of its walk.

   THE FORM: plugin-hostd/fuzz_command's lib/A/Prog/chain_words_s1.v (a plain run through the stores to the frame's
   shadow, the region fshadow_region, its write permission by awr_byte's in_frames disjunct) and
   LLVMFuzzerTestOneInput_s45.v (a string wrapper taken by PaArt.aj_art_at), at origin/ossv/recipes 501c0d516c69.
   The code (dis:754-768 of dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan.s):
   - 0x858f4 .. 0x858fc: sb zero,4(s5); sb zero,5(s5); sb s4,6(s5): v's three shadow bytes 00 00 04 (v in scope);
   - 0x85900 .. 0x85908: s3 := m + (i << 8) = &m->seg[i] (an alias of the seed names it as s6's atom), a0 := s3 + 24;
   - 0x8590c .. 0x85918: the instrumented check of the 4-byte word at a0: the seed holds its shadow byte (0, the
     block m is addressable over the whole granule) through an alias of (a0 >> 3) + a5, so the run reads 0 and
     bnez a1 falls through; the slow block 0x85b90 is never entered;
   - 0x8591c .. 0x85920: lw a0,0(a0) (m->seg[i].ignore, seg_spec.mseg_enc's flag), bnez a0: split; taken: one step
     to the join 0x859c4, closed by S22_JOIN_stmt with x_decl (S i) = x_decl i (s22_decl_step_skip, ignore set);
   - 0x85924 .. 0x8592c: a1 := 46, a0 := s3, jal of the strrchr wrapper, taken by RtSeg.astrrchr_realizes through
     PaArt.aj_art_at over the segment's name (s22_name_str), closed by S22_VR_stmt with the answer turned into
     SegModel.strrchr's by s22_strrchr_none / s22_strrchr_some.
   Every cut fact between the two points is carried by p1_keep: the run writes only v's three shadow bytes and the
   wrapper only its scratch window below s1. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF PaLibG PaLibH PaSB PaDenot PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_s10k LLVMFuzzerTestOneInput_s22k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at 0x858f4 ----
   Every register is its own atom but s4 = 4 (pinned, so the shadow byte it stores is a literal). Extra atoms: 32 = g,
   the word m->seg[i].ignore (0 or 1); 33 = the shadow byte's address of &m->seg[i].ignore. Regions: 0 the frame's
   36 + 28 shadow bytes at s5 (atom 21), written only in [4, 7) (v's three bytes); 1 the ignore word at s6 + 24 (atom
   22 = &m->seg[i]); 2 its shadow byte (atom 33). Aliases: m + (i << 8) is s6's atom; (s6 + 24 >> 3) + a5 is atom
   33. *)
Definition p1_r0 : YP09.region := fshadow_region 21 3 4 7 [].
Definition p1_r1 : YP09.region := YP09.mkRegion (Some 22%nat) 24 28 0 0 [YP09.mkChunk 24 (CVal 4 (SOff 32 0))].
Definition p1_r2 : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition p1_al_s3 : sv * sv := (SAlu ALU_ADD (SOff 16 0) (SAlu ALU_SLL (SOff 25 0) (SLit 8)), SOff 22 0).
Definition p1_al_sh : sv * sv := (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 24) (SLit 3)) (SOff 15 0), SOff 33 0).
Definition p1_facts : facts := mkFacts [(32%nat, mkAF 0 1 0)] [] [p1_al_s3; p1_al_sh].
Definition p1_sr : list sv := sr_set sr_atoms 20%bv (SLit 4).
Definition ss_p1 : sstate := mkSS LO_K858f4 p1_sr [p1_r0; p1_r1; p1_r2] None p1_facts.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition p1_E (regs : bvmap 5 word) (xs : list Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) xs)).

Lemma p1_E_reg : forall regs xs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (p1_E regs xs) n = getr regs r.
Proof.
intros regs xs n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold p1_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma p1_E_extra : forall regs xs j, (j < length xs)%nat -> (32 + j < A_TEXT)%nat ->
  ew (p1_E regs xs) (32 + j) = Z_to_bv 64 (nth j xs 0).
Proof.
intros regs xs j Hj Hj2. unfold p1_E. rewrite Eimg_low by exact Hj2.
rewrite ew_Ereg_extra. apply map_nth.
Qed.

(* a value read through the reader is a value of the restricted memory (_s19's s19_val_mem) *)
Lemma p1_val_mem : forall H mem a n v, sa_val (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; [|cbn [option_map] in Hv; discriminate].
cbn [option_map] in Hv. injection Hv as Hv. f_equal.
first [ rewrite <- Hv
      | change (YG0f.le_byte v n k) with (YO0f.le_byte v n k) in *; rewrite <- Hv
      | change (YO0f.le_byte v n k) with (YG0f.le_byte v n k) in *; rewrite <- Hv
      | unfold YG0f.le_byte, YO0f.le_byte in *; rewrite <- Hv ].
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma p1_chunk4 : forall (W : world SEGS) mem E base off (n : nat) v,
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> sa_val (rdW W mem) (base + off) 4 v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 4 (SOff n 0))).
Proof.
intros W mem E base off n v En Hv Hrd.
apply (chunk_ok_val SEGS E _ base off 4 _ v); [| change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); exact Hv | zside |].
- cbn [sv_denot]. rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- exact (p1_val_mem _ _ _ 4 _ Hrd).
Qed.
Lemma p1_chunk1z : forall (W : world SEGS) mem E base,
  rdW W mem base = Some 0 -> YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk 0 (CVal 1 (SLit 0))).
Proof.
intros W mem E base Hb.
apply (chunk_ok_val SEGS E _ base 0 1 _ 0); [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | zside |].
apply (p1_val_mem _ _ _ 1 0). intros k Hk. destruct k as [|k]; [|lia]. rewrite Z.add_0_r, Z.add_0_r. exact Hb.
Qed.
Lemma p1_regs_ok_set : forall E sr regs (r : bv 5) e, regs_ok E sr regs -> bv_eqb r 0 = false ->
  getr regs r = sv_denot E e -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hr0 Hv r'. specialize (Hr r'). unfold sr_set. rewrite Hr0.
unfold sr_get in *. destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. exact Hv.
Qed.

(* ---- seed: the state at 0x858f4 is an instance of ss_p1 ---- *)
Lemma p1_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem sh x mq iz g,
  getr regs 15 = w64 SHADOW_OFF -> getr regs 16 = w64 mq -> getr regs 20 = w64 4 ->
  getr regs 21 = w64 sh -> getr regs 22 = w64 x -> getr regs 25 = w64 iz ->
  x = mq + 256 * iz -> 0 <= mq -> 0 <= iz < 32 -> x + 32 <= 2 ^ 47 -> 0 <= g <= 1 ->
  SHADOW_OFF <= sh -> sh + 64 <= 2 ^ 47 ->
  (forall o, 4 <= o < 7 -> apresent (w_H W) mem (sh + o)) ->
  sa_val (rdW W mem) (x + 24) 4 g ->
  rdW W mem (SHADOW_OFF + (x + 24) / 8) = Some 0 ->
  (sh + 64 <= x + 24 \/ x + 28 <= sh) ->
  (sh + 64 <= SHADOW_OFF + (x + 24) / 8 \/ SHADOW_OFF + (x + 24) / 8 + 1 <= sh) ->
  (x + 28 <= SHADOW_OFF + (x + 24) / 8 \/ SHADOW_OFF + (x + 24) / 8 + 1 <= x + 24) ->
  st_ok_pi SEGS VAL (p1_E regs [g; SHADOW_OFF + (x + 24) / 8]) ss_p1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K858f4)) mem (seg_rom SEGS))).
Proof.
intros W regs mem sh x mq iz g R15 R16 R20 R21 R22 R25 Hx Hmq Hiz Hx47 Hg Hsh Hsh47 Hpres Hval Hshb D01 D02 D12.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
pose proof (Z.div_pos (x + 24) 8 ltac:(lia) ltac:(lia)) as Hd0.
pose proof (Z.div_le_upper_bound (x + 24) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as Hd1.
set (shb := SHADOW_OFF + (x + 24) / 8) in *.
set (E := p1_E regs [g; shb]).
assert (EE : forall k (r : bv 5) v, Z.of_nat k = bv_unsigned r -> getr regs r = w64 v -> 0 <= v < 2 ^ 64 ->
  ew E k = Z_to_bv 64 v /\ bv_unsigned (ew E k) = v).
{ intros k r v Hk0 Hr Hv. assert (Ek : ew E k = getr regs r) by exact (p1_E_reg regs _ k r Hk0).
  rewrite Ek, Hr. split; [reflexivity|]. apply unsigned_lit_small. exact Hv. }
destruct (EE 15%nat 15%bv SHADOW_OFF eq_refl R15 ltac:(unfold SHADOW_OFF; lia)) as [E15 U15].
destruct (EE 16%nat 16%bv mq eq_refl R16 ltac:(lia)) as [E16 U16].
destruct (EE 21%nat 21%bv sh eq_refl R21 ltac:(lia)) as [E21 U21].
destruct (EE 22%nat 22%bv x eq_refl R22 ltac:(lia)) as [E22 U22].
destruct (EE 25%nat 25%bv iz eq_refl R25 ltac:(lia)) as [E25 U25].
assert (E32 : ew E 32 = Z_to_bv 64 g) by exact (p1_E_extra regs [g; shb] 0 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (E33 : ew E 33 = Z_to_bv 64 shb) by exact (p1_E_extra regs [g; shb] 1 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (U32 : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = shb) by (rewrite E33; apply unsigned_lit_small; unfold shb, SHADOW_OFF in *; lia).
unfold ss_p1. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold p1_sr. apply p1_regs_ok_set; [unfold E, p1_E; apply regs_ok_Eimg_Ereg | reflexivity |].
  rewrite R20. reflexivity.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok, p1_r0, p1_r1, p1_r2, fshadow_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + change (fs_frame_bytes 3 / 8) with 64. rewrite U21. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil]. exact (p1_chunk4 W mem E x 24 32 g E32 ltac:(lia) Hval).
  + rewrite U33. split; [unfold shb, SHADOW_OFF in *; lia|]. split; [unfold shb, SHADOW_OFF in *; lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil]. exact (p1_chunk1z W mem E shb Hshb).
- apply pairwise_disjoint_of_extents. unfold p1_r0, p1_r1, p1_r2, fshadow_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (fs_frame_bytes 3 / 8) with 64. rewrite U21, U22, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. lia.
- split; [|split; [exact I|]].
  + cbn [p1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32.
    rewrite Z.pow_0_r, Z.mod_1_r. repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
  + cbn [p1_facts f_alias alias_ok p1_al_s3 p1_al_sh]. split; [|split; [|exact I]].
    * apply bv_eq. change (U E (SAlu ALU_ADD (SOff 16 0) (SAlu ALU_SLL (SOff 25 0) (SLit 8))) = U E (SOff 22 0)).
      rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 16 mq E16), (U_atom E 25 iz E25), (U_atom E 22 x E22) by lia.
      rewrite U_lit by lia. change (Z.land 8 63) with 8. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
      rewrite (zcanon_small (iz * 256)) by lia. rewrite zcanon_small by lia. lia.
    * rewrite (denot_shx E 22 15 24 x SHADOW_OFF E22 E15) by (unfold SHADOW_OFF; lia).
      cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* the entry's sp and the base register s1 (_s19's s19_bounds) *)
Lemma p1_bounds : forall (B : asyms) (MT : ameter_ops) cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 336 <= x_s1 cx <= x_sp0 cx - 320.
Proof.
intros B MT cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold STK_LLVMFuzzerTestOneInput in Hslo.
unfold x_s1, x_sp0, LT_FRAME. set (s := spZ (x_regs cx)) in *.
pose proof (Z.div_mod s 16 ltac:(lia)) as D1. pose proof (Z.div_mod (s - 320) 32 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (s - 320) 32 ltac:(lia)) as M2.
split; [exact Hal|]. split; [lia|]. split; [lia|]. split.
- replace (s - 320 - (s - 320) mod 32) with ((s - 320) / 32 * 32) by lia. apply Z.mod_mul. lia.
- lia.
Qed.

(* ---- facts carried from one reader to another that agrees on their bytes (_s19's s19_*_kept) ---- *)
Lemma p1_rdword_kept : forall (rd rd' : reader) a v, (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) ->
  rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a HK). exact H. Qed.
Lemma p1_val_kept : forall (rd rd' : reader) a n v,
  (forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> sa_val rd a n v -> sa_val rd' a n v.
Proof. intros rd rd' a n v HK H k Hk. rewrite (HK k Hk). exact (H k Hk). Qed.
Lemma p1_bytes_kept : forall (rd rd' : reader) a bs,
  (forall i, (i < length bs)%nat -> rd' (a + Z.of_nat i) = rd (a + Z.of_nat i)) -> sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs HK H i Hi. rewrite (HK i Hi). exact (H i Hi). Qed.

(* the frame's shadow with v in scope: the entry pattern of LFO_N but bytes 4 .. 6, which the code wrote 00 00 04 *)
Lemma p1_fsh_nv : forall (rd rd' : reader) xs,
  sa_zs rd xs (lt_fsh LFO_N) ->
  (forall j, 0 <= j < 36 -> ~ (4 <= j < 7) -> rd' (xs + j) = rd (xs + j)) ->
  sa_zs rd' (xs + 4) [0; 0; 4] -> sa_zs rd' xs (lt_fsh LFO_NV).
Proof.
intros rd rd' xs H HK HV j Hj. rewrite lt_fsh_len in Hj.
destruct (Nat.lt_ge_cases j 4) as [Hj4 | Hj4]; [| destruct (Nat.lt_ge_cases j 7) as [Hj7 | Hj7]].
- rewrite HK by lia. rewrite (H j ltac:(rewrite lt_fsh_len; lia)). f_equal.
  do 4 (destruct j as [|j]; [reflexivity|]). lia.
- pose proof (HV (j - 4)%nat ltac:(cbn [length]; lia)) as Hv.
  replace (xs + 4 + Z.of_nat (j - 4)) with (xs + Z.of_nat j) in Hv by lia.
  rewrite Hv. f_equal.
  do 4 (destruct j as [|j]; [lia|]). do 3 (destruct j as [|j]; [reflexivity|]). lia.
- rewrite HK by lia. rewrite (H j ltac:(rewrite lt_fsh_len; lia)). f_equal.
  do 7 (destruct j as [|j]; [lia|]). do 29 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

(* the s1 slots of the loop's head lie in [s1 + 8, s1 + 192) *)
Lemma p1_L_offs : forall cx i c m mt o v, In (o, v) (s22_L cx i c m mt) -> 0 <= o <= 184.
Proof.
intros cx i c m mt o v Hin. apply (in_map fst) in Hin. cbn [fst] in Hin.
change (map fst (s22_L cx i c m mt)) with
  [8; 24; 32; 48; 56; 144; 160; 168; 184; 96; 104; 112; 120; 128; 136; 152] in Hin.
cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [lia|]). destruct Hin.
Qed.

(* a callee-saved register is what it was at the call (_s19's s19_pres) *)
Lemma p1_pres : forall regs regs2 (r : bv 5), aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) ->
  getr regs2 r = getr regs r.
Proof. intros regs regs2 r HP Hr. pose proof (HP _ Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac p1_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis ASTRRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrrchr_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_strrchr).
Let SMP : stack_malloc_progressP B := fun s cid HW Hc Hn => ml_stack_malloc_progress _ ML s cid HW Hc Hn.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* a harness block at a later state of the same allocator: its addressability is AR's (AR_shadow_law) *)
Lemma p1_hblk : forall ly S (W : world SEGS) mem mem2 md2 p n,
  lt_hblk B ly S (rdW W mem) p n -> AR SEGS B ly S W mem2 md2 -> lt_hblk B ly S (rdW W mem2) p n.
Proof.
intros ly S W mem mem2 md2 p n (Hin & H4 & H16 & (H0 & H63 & Hm & _ & _)) HAR2.
destruct (al_blocks _ _ LAWS ly S W mem2 md2 p n HAR2 Hin) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
split; [exact Hin|]. split; [exact H4|]. split; [exact H16|].
split; [exact H0|]. split; [exact H63|]. split; [exact Hm|]. split.
- exact (range_addressable_of_block SEGS B LAWS ly S W mem2 md2 p n p n HAR2 Hin ltac:(lia) ltac:(lia)).
- intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem2 md2 p n p n HAR2 Hin ltac:(lia) ltac:(lia) Hn0).
Qed.

(* what every point of S14 keeps (s22_inv) carries to a later state of the same allocator that holds the same
   journal, sp / gp / tp / s0 / s1, and every byte but the frame's 64 shadow bytes and the scratch window of a
   runtime call below s1; the frame's shadow is the new state's own *)
Lemma p1_keep : forall cx i c m tab mt o o2 ly S W regs mem md k acc regs2 mem2 md2,
  lt_base B MT cx ->
  s22_inv B MT cx i c m tab mt o (s22_L cx i c m mt) ly S W regs mem md k acc ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem2 md2 k ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx <= a < x_sh cx + 64) -> ~ (x_s1 cx - 2 * ESTACK <= a < x_s1 cx) ->
     rdW W mem2 a = rdW W mem a) ->
  sa_zs (rdW W mem2) (x_sh cx) (lt_fsh o2) ->
  s22_inv B MT cx i c m tab mt o2 (s22_L cx i c m mt) ly S W regs2 mem2 md2 k acc.
Proof.
intros cx i c m tab mt o o2 ly S W regs mem md k acc regs2 mem2 md2 HBASE HINV HJ2 R2 R3 R4 R8 R9 HK HZS.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
destruct (p1_bounds B MT cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
destruct HINV as (Hi & Hdecl & HCORE & HC & HM & HT & HMT & HSL & HCM & HTABS).
destruct HCORE as (HFR & HIMG & HBL & HBUD).
destruct HFR as (HJ & F2 & F3 & F4 & F8 & F9 & FSV & FH0 & FH8 & FH16 & FFL & F176 & FSH).
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ2) as HAR2.
assert (HFin : In (LT_FCLS, x_fpos cx) (frames S)).
{ destruct HJ as (_ & _ & _ & _ & _ & Hfr & _). rewrite Hfr. left. reflexivity. }
assert (HFA : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
{ destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & HF & _).
  unfold x_fr, frame_addr. rewrite HF. reflexivity. }
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR HFin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes LT_FCLS) with 512 in HFceil, HFapp. rewrite HFA in HF4096, HFceil, HFapp.
assert (HXSH : x_sh cx = SHADOW_OFF + x_fr cx / 8) by reflexivity.
unfold in_app, ASAN_CEIL in HFapp.
(* the bytes the facts read: application bytes below the allocation ceiling, and the real stack from s1 up *)
assert (KA : forall a, 0 <= a -> (a < kLowShadowBeg \/ (kHighMemBeg <= a /\ a < alloc_ceiling)) ->
  rdW W mem2 a = rdW W mem a).
{ intros a Ha Hr. apply HK; unfold kLowShadowBeg, kHighMemBeg, ESTACK in *; rewrite ?HXSH; lia. }
assert (KS : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W mem2 a = rdW W mem a).
{ intros a Ha. apply HK; unfold kLowShadowBeg, kHighMemBeg, ESTACK in *; rewrite ?HXSH; lia. }
assert (KB : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + n -> rdW W mem2 a = rdW W mem a).
{ intros p n a Hin Ha. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H4 & Hc & Happ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]. unfold in_app, ASAN_CEIL in Happ. apply KA; lia. }
assert (KF : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W mem2 a = rdW W mem a).
{ intros a Ha. apply KA; lia. }
split; [exact Hi|]. split; [exact Hdecl|].
split; [split; [|split; [|split]]|].
- (* lt_frame *)
  split; [exact HJ2|]. split; [rewrite R2; exact F2|]. split; [rewrite R3; exact F3|]. split; [rewrite R4; exact F4|].
  split; [rewrite R8; exact F8|]. split; [rewrite R9; exact F9|].
  split.
  { intros i0 r Hi0. apply (p1_rdword_kept (rdW W mem)); [|exact (FSV i0 r Hi0)].
    assert (Hi13 : (i0 < length LT_SAVED)%nat)
      by (apply (proj1 (nth_error_Some LT_SAVED i0)); rewrite Hi0; discriminate).
    change (length LT_SAVED) with 13%nat in Hi13. intros kk Hk. apply KS. lia. }
  split; [apply (p1_rdword_kept (rdW W mem)); [intros kk Hk; apply KF; lia | exact FH0]|].
  split; [apply (p1_rdword_kept (rdW W mem)); [intros kk Hk; apply KF; lia | exact FH8]|].
  split; [apply (p1_rdword_kept (rdW W mem)); [intros kk Hk; apply KF; lia | exact FH16]|].
  split; [apply (p1_rdword_kept (rdW W mem)); [intros kk Hk; apply KF; unfold LT_FLAGW; lia | exact FFL]|].
  split; [apply (p1_rdword_kept (rdW W mem)); [intros kk Hk; apply KS; lia | exact F176]|].
  exact HZS.
- (* lt_img: the image bytes lie below 0x601000 *)
  apply (s10_lt_img_kept B IMGS BSYM cx W mem2 (rdW W mem) HAR2); [|exact HIMG].
  intros a Himg _ _. pose proof (pa_img_range _ Himg) as HIR. unfold kImgEnd in HIR.
  apply KA; unfold kLowShadowBeg; lia.
- exact HBL.
- exact HBUD.
- split; [exact (p1_hblk ly S W mem mem2 md2 c _ HC HAR2)|].
  split; [exact (p1_hblk ly S W mem mem2 md2 m _ HM HAR2)|].
  split; [exact (p1_hblk ly S W mem mem2 md2 tab _ HT HAR2)|].
  split; [exact (p1_hblk ly S W mem mem2 md2 mt _ HMT HAR2)|].
  split.
  { intros o0 v Hin. apply (p1_rdword_kept (rdW W mem)); [|exact (HSL o0 v Hin)].
    pose proof (p1_L_offs cx i c m mt o0 v Hin) as Ho. intros kk Hk. apply KS. lia. }
  split.
  { destruct HCM as [(bs & Hb & He) (bm & Hbm & Hem)]. split.
    - exists bs. split; [|exact He]. apply (p1_bytes_kept (rdW W mem)); [|exact Hb]. intros i0 Hi0.
      destruct He as (Hl & _). apply (KB c seg_spec.SEG_C_SIZE); [exact (proj1 HC) | lia].
    - exists bm. split; [|exact Hem]. apply (p1_bytes_kept (rdW W mem)); [|exact Hbm]. intros i0 Hi0.
      destruct Hem as (Hl & _). apply (KB m seg_spec.SEG_M_SIZE); [exact (proj1 HM) | lia]. }
  destruct HTABS as (Hcap & (rb & Hrb & Hre) & Hguard & Hn & (mb & Hmb & Hme) & Hlen).
  split; [exact Hcap|]. split.
  { exists rb. split; [|exact Hre]. apply (p1_bytes_kept (rdW W mem)); [|exact Hrb]. intros i0 Hi0.
    destruct Hre as (Hl & _). apply (KB tab (x_tabn cx)); [exact (proj1 HT) | unfold x_tabn, seg_spec.RVLAN_SIZE; lia]. }
  split.
  { unfold sa_guardtab in *. apply (p1_bytes_kept (rdW W mem)); [|exact Hguard]. intros i0 Hi0.
    change (length seg_spec.GUARD_BYTES) with 18%nat in Hi0.
    apply (KB tab (x_tabn cx)); [exact (proj1 HT) | unfold x_tabn, seg_spec.RVLAN_SIZE in *; lia]. }
  split.
  { apply (p1_val_kept (rdW W mem)); [|exact Hn]. intros kk Hk. apply KF. unfold FO_N. lia. }
  split; [|exact Hlen].
  exists mb. split; [|exact Hme]. apply (p1_bytes_kept (rdW W mem)); [|exact Hmb]. intros i0 Hi0.
  destruct Hme as (Hl & _). apply (KB mt (x_mtn cx)); [exact (proj1 HMT) | unfold x_mtn, seg_spec.MVLAN_SIZE; lia].
Qed.

(* the call of the strrchr wrapper (row 11, RtSeg.astrrchr_realizes) as a step of the walk's journal, through
   PaArt.aj_art_at (fuzz_command's aj_strspn_at_loc, lib/A/Prog/LLVMFuzzerTestOneInput_s45.v:253-282) *)
Lemma p1_strrchr_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x s (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 46 -> 0 < x ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  astr_at SEGS W memT x s ->
  aread_ok SEGS (2 * ESTACK) W regsT memT x (astr_len s + 1) ->
  amem_range x (astr_len s + 8) ->
  atail_vis SEGS W memT (x + astr_len s) ->
  rt_rom_view SEGS B W memT ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_strrchr)) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
  aregs_preserved regsT regs2 /\
  ((getr regs2 10 = w64 0 /\ ~ In 46 (seg_spec.zs s)) \/
   (exists j, RtSeg.last_at (seg_spec.zs s) 46 j /\ getr regs2 10 = w64 (x + Z.of_nat j))) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> ~ False ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x s o raw
  HJ Ha0 Ha1 Hx Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hs Hrd Hm Htl Hrom.
assert (ESTACK = 4096) as Hes by reflexivity.
apply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False) _ W regsT memT
  STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
  (fun regs2 _ => (getr regs2 10 = w64 0 /\ ~ In 46 (seg_spec.zs s)) \/
     (exists j, RtSeg.last_at (seg_spec.zs s) 46 j /\ getr regs2 10 = w64 (x + Z.of_nat j)))
  HJ Hsp Hal Hneg ltac:(lia) Hbud Hra (fun a F => False_ind _ F)).
apply (ASTRRCHR fx lyc Sc W regsT memT mdc x 46 s); try assumption; try lia.
apply (ecall_pre_stk_at SEGS B (2 * ESTACK) STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg
  ltac:(lia) Hbud); [rewrite Hra; exact Hraw | exact Hgp | exact Htp].
Qed.

Lemma s22_p1 : s22_p1_stmt B MT.
Proof using All.
intros i HJOIN HVR cx ly S W regs mem md k acc c m tab mt HBASE HFRM Hi HCORE HcB Hm Htab Hmt
  R15 R16 R20 R21 R22 R23 R24 R25 R26 R27 Hdecl HSL HCM HTABS.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (HINV : s22_inv B MT cx i c m tab mt LFO_N (s22_L cx i c m mt) ly S W regs mem md k acc)
  by exact (conj Hi (conj Hdecl (conj HCORE (conj HcB (conj Hm (conj Htab (conj Hmt (conj HSL (conj HCM HTABS))))))))).
destruct (p1_bounds B MT cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & F2 & F3 & F4 & F8 & F9 & FSV & FH0 & FH8 & FH16 & FFL & F176 & FSH).
pose proof (proj1 HJ) as HAR.
assert (HFin : In (LT_FCLS, x_fpos cx) (frames S)).
{ destruct HJ as (_ & _ & _ & _ & _ & Hfr & _). rewrite Hfr. left. reflexivity. }
assert (HFA : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
{ destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & HF & _).
  unfold x_fr, frame_addr. rewrite HF. reflexivity. }
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR HFin) as (_ & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR HFin) as (HF4096 & HFceil & _).
destruct (frame_al64 SEGS B _ _ _ _ _ _ _ HAR HFin) as (HF64 & _ & _).
change (fs_frame_bytes LT_FCLS) with 512 in HFapp, HFpres, HFSpres, HFceil. change (512 / 8) with 64 in HFSpres.
rewrite HFA in HFapp, HFpres, HFSpres, HF4096, HFceil, HF64.
(* the block m and turn i's segment in it *)
destruct Hm as (HinM & Hm4 & Hm16 & HaM).
destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR HinM) as (_ & _ & HMceil & HMapp & HMpres & _ & _).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE LT_FCLS (x_fpos cx) HAR HinM HFin) as HMF.
rewrite HFA in HMF. change (fs_frame_bytes LT_FCLS) with 512 in HMF.
change (req_size seg_spec.SEG_M_SIZE) with 9236 in HMceil, HMapp, HMpres, HMF.
assert (Hi32 : (i < 32)%nat).
{ destruct HCM as (_ & (bs & _ & Henc)). destruct Henc as (_ & Hle & _). unfold x_mcF in Hi. lia. }
destruct (s22_mseg_at cx i c m (rdW W mem) HCM Hi) as (f & Hf & Henc).
set (x := seg_spec.mseg_addr m i) in *.
assert (Hx : x = m + 256 * Z.of_nat i) by (unfold x, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
remember (if SegModel.ms_ignore (x_seg cx i) then 1 else 0) as g eqn:Hgdef.
assert (Hg : 0 <= g <= 1) by (rewrite Hgdef; destruct (SegModel.ms_ignore (x_seg cx i)); lia).
assert (Hig : sa_val (rdW W mem) (x + 24) 4 g).
{ pose proof Henc as (Hflen & _ & _ & _ & Hfig & _).
  intros kk Hkk.
  assert (Hidx : (24 + kk < length f)%nat) by lia.
  pose proof (Hf (24 + kk)%nat Hidx) as Hb.
  replace (x + 24 + Z.of_nat kk) with (x + Z.of_nat (24 + kk)) by lia.
  rewrite Hb. f_equal.
  unfold seg_spec.flag_enc, seg_spec.fldz, seg_spec.fld in Hfig.
  change (Z.to_nat seg_spec.MS_IGNORE) with 24%nat in Hfig. change (Z.to_nat 4) with 4%nat in Hfig.
  assert (Hn : nth (24 + kk) f ZB0 = nth kk (firstn 4 (skipn 24 f)) ZB0).
  { rewrite nth_firstn. destruct (Nat.ltb_spec kk 4); [|lia]. rewrite nth_skipn. reflexivity. }
  rewrite Hn, Hfig, Hgdef. clear - Hkk.
  destruct (SegModel.ms_ignore (x_seg cx i)); do 4 (destruct kk as [|kk]; [vm_compute; reflexivity|]); lia. }
assert (Hshb : rdW W mem (SHADOW_OFF + (x + 24) / 8) = Some 0).
{ pose proof (range_addressable_of_block SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE (x + 24) 8 HAR HinM
    ltac:(lia) ltac:(change (req_size seg_spec.SEG_M_SIZE) with 9236; lia)) as HRA.
  destruct (HRA (x + 24) ltac:(lia)) as (s0 & Hs0 & Hok0).
  destruct (HRA (x + 31) ltac:(lia)) as (s7 & Hs7 & Hok7).
  unfold shadow_of_addr in Hs0, Hs7.
  assert (Hq : (x + 31) / 8 = (x + 24) / 8) by lia.
  rewrite Hq, Hs0 in Hs7. injection Hs7 as <-.
  rewrite Hs0. unfold saddr_ok in Hok7. destruct Hok7 as [-> | Hok7]; [reflexivity | lia]. }
assert (HXSH : x_sh cx = SHADOW_OFF + x_fr cx / 8) by reflexivity.
assert (HSHR : kLowShadowBeg <= x_sh cx /\ x_sh cx + 64 <= kHighMemBeg).
{ rewrite HXSH. unfold in_app, ASAN_CEIL in HFapp. unfold kLowShadowBeg, kHighMemBeg in *. lia. }
assert (HSHb : 0 <= x_sh cx /\ x_sh cx + 64 <= x_s1 cx - 2 * ESTACK) by (rewrite HXSH; unfold ESTACK; lia).
pose proof (p1_seed W regs mem (x_sh cx) x m (Z.of_nat i) g R15 R16 R20 R21 R22 R25 Hx ltac:(lia) ltac:(lia)
  ltac:(lia) Hg ltac:(rewrite HXSH; lia) ltac:(rewrite HXSH; lia)
  ltac:(intros o Ho; exact (proj1 (HFSpres o ltac:(lia)))) Hig Hshb) as HS.
assert (HMFd : m + 9236 <= x_fr cx \/ x_fr cx + 512 <= m) by (unfold zdisjoint in HMF; cbn [fst snd] in HMF; exact HMF).
clear HMF.
specialize (HS
  ltac:(unfold in_app, ASAN_CEIL in HMapp; unfold kLowShadowBeg, kHighMemBeg in *; lia)
  ltac:(rewrite HXSH; lia)
  ltac:(unfold in_app, ASAN_CEIL in HMapp; unfold kLowShadowBeg, kHighMemBeg in *; lia)).
remember (p1_E regs [g; SHADOW_OFF + (x + 24) / 8]) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k0 r Hk0; rewrite HE; exact (p1_E_reg regs _ k0 r Hk0)).
assert (U21 : bv_unsigned (ew E 21) = x_sh cx).
{ rewrite (EE 21%nat 21%bv eq_refl), R21. apply unsigned_lit_small. rewrite HXSH. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 g)
  by (rewrite HE; exact (p1_E_extra regs [g; _] 0 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia))).
assert (WS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
pose proof HBASE as (HPRE0 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
(* what the code below may write: v's three shadow bytes, in the frame's shadow (awr_byte's in_frames) *)
assert (AWR1 : awr_ok SEGS B E (ss_mem ss_p1) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
  (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly S) (frames (x_S cx)) ly [(LT_FCLS, x_fpos cx)]).
{ change (ss_mem ss_p1) with [p1_r0; p1_r1; p1_r2].
  eapply awr_ok_cons_gen with (n := 21%nat) (b := x_sh cx); [reflexivity | exact U21 | |].
  { intros a Ha. unfold p1_r0, fshadow_region in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    right; right; right; left. exists LT_FCLS, (x_fpos cx).
    split; [left; reflexivity|]. right. rewrite HFA. unfold in_zr. cbn [fst snd].
    change (fs_frame_bytes LT_FCLS / 8) with 64. change (shadow_addr (x_fr cx)) with (x_sh cx). lia. }
  apply awr_ok_cons_ro; [unfold p1_r1; cbn; lia|]. apply awr_ok_cons_ro; [unfold p1_r2; cbn; lia|].
  apply awr_ok_nil. }
unfold cfg_at. change (w64 (BASE + LO_K858f4)) with (Z_to_bv 64 (BASE + LO_K858f4)).
(* 0x858f4 .. 0x85920: v's three shadow bytes, s3 := &m->seg[i], the check of the ignore word (its shadow byte is the
   literal 0 of region 2, so bnez a1 falls through), a0 := m->seg[i].ignore; the run stops at bnez a0 *)
paj_run_sh RUNP HS HJ.
{ exact AWR1. }
rename HF into HF1, HFr into HFr1, HG into HG1.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md1 := mm) in *; clearbody md1 end.
rename ms into ms1. cbn [ms_mem mkst] in HFr1.
(* the run wrote only v's three shadow bytes *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) -> rdW W (ms_mem ms1) a = rdW W mem a).
{ intros a Ha Hn. apply (kept_of_frame E _ (w_H W) mem _ (fun y => x_sh cx + 4 <= y < x_sh cx + 7) HFr1);
    [| exact Ha | exact Hn].
  intros b wlo whi y Hin Hy.
  lazymatch type of Hin with In _ (windows ?rs) => let w := eval vm_compute in (windows rs) in
    change (In (b, wlo, whi) w) in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hy; rewrite ?U21 in Hy; cbv beta; lia |]).
  destruct Hin. }
(* the frame's 36 shadow bytes are the entry pattern but v's, which are now 00 00 04 *)
assert (KJ : forall rd', sa_zs rd' (x_sh cx + 4) [0; 0; 4] ->
  (forall j, 0 <= j < 36 -> ~ (4 <= j < 7) -> rd' (x_sh cx + j) = rdW W mem (x_sh cx + j)) ->
  sa_zs rd' (x_sh cx) (lt_fsh LFO_NV))
  by (intros rd' HV HKj; exact (p1_fsh_nv (rdW W mem) rd' (x_sh cx) FSH HKj HV)).
psrr_branch_pi RUNP BR HS.
- (* bnez a0 taken: m->seg[i].ignore is set; one step to the join 0x859c4 *)
  rewrite branch_ne_U in Hc. rewrite (U_atom E 32 g E32), U_lit in Hc by lia.
  assert (Hign : SegModel.ms_ignore (x_seg cx i) = true).
  { destruct (SegModel.ms_ignore (x_seg cx i)) eqn:Hb; [reflexivity|].
    rewrite Hgdef in Hc; try rewrite Hb in Hc; vm_compute in Hc; discriminate Hc. }
  paj_run_to_sh RUNTOP HS HJ S22_JOIN.
  { lazymatch type of AWR1 with awr_ok _ _ _ ?rsA _ _ _ _ _ _ _ _ =>
      apply (s10_awr_skel _ _ _ rsA); [vm_compute; reflexivity | exact AWR1] end. }
  rename HF into HF2, HFr into HFr2, HG into HG2.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md2 := mm) in *; clearbody md2 end.
  rename ms into msK. cbn [ms_mem mkst] in HFr2.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) ->
    rdW W (ms_mem msK) a = rdW W (ms_mem ms1) a).
  { intros a Ha Hn. apply (kept_of_frame E _ (w_H W) (ms_mem ms1) _ (fun y => x_sh cx + 4 <= y < x_sh cx + 7) HFr2);
      [| exact Ha | exact Hn].
    intros b wlo whi y Hin Hy.
    lazymatch type of Hin with In _ (windows ?rs) => let w := eval vm_compute in (windows rs) in
      change (In (b, wlo, whi) w) in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hy; rewrite ?U21 in Hy; cbv beta; lia |]).
    destruct Hin. }
  assert (HV2 : sa_zs (rdW W (ms_mem msK)) (x_sh cx + 4) [0; 0; 4]).
  { assert (RK : forall i0 r, nth_error (ss_mem ltac:(lazymatch type of HS with st_ok_pi _ _ _ ?s _ => exact s end)) i0 = Some r ->
      region_ok SEGS E (mrestrict (w_H W) (ms_mem msK)) r)
      by (intros i0 r Hi0; exact (st_ok_pi_region_nth E _ (restrict (w_H W) msK) i0 r HS Hi0)).
    lazymatch type of HS with st_ok_pi _ _ _ ?ssB _ =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
      pose proof (RK 0%nat r0 ltac:(vm_compute; reflexivity)) as RSH end.
    destruct RSH as (_ & _ & _ & CSH). cbn [YP09.r_base YP09.r_chunks base_val] in CSH. rewrite U21 in CSH.
    exact (s10_zs_ok E (w_H W) (ms_mem msK) (x_sh cx) _ [0; 0; 4] 4 CSH ltac:(vm_compute; reflexivity)). }
  (* the registers at the join *)
  prreg HS (2%bv : bv 5) P2. rewrite (EE 2%nat 2%bv eq_refl) in P2.
  prreg HS (3%bv : bv 5) P3. rewrite (EE 3%nat 3%bv eq_refl) in P3.
  prreg HS (4%bv : bv 5) P4. rewrite (EE 4%nat 4%bv eq_refl) in P4.
  prreg HS (8%bv : bv 5) P8. rewrite (EE 8%nat 8%bv eq_refl) in P8.
  prreg HS (9%bv : bv 5) P9. rewrite (EE 9%nat 9%bv eq_refl) in P9.
  prreg HS (15%bv : bv 5) P15. rewrite (EE 15%nat 15%bv eq_refl), R15 in P15.
  prreg HS (16%bv : bv 5) P16. rewrite (EE 16%nat 16%bv eq_refl), R16 in P16.
  prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. rewrite (EE 21%nat 21%bv eq_refl), R21 in P21.
  prreg HS (22%bv : bv 5) P22. rewrite (EE 22%nat 22%bv eq_refl), R22 in P22.
  prreg HS (23%bv : bv 5) P23. rewrite (EE 23%nat 23%bv eq_refl), R23 in P23.
  prreg HS (24%bv : bv 5) P24. rewrite (EE 24%nat 24%bv eq_refl), R24 in P24.
  prreg HS (25%bv : bv 5) P25. rewrite (EE 25%nat 25%bv eq_refl), R25 in P25.
  prreg HS (26%bv : bv 5) P26. rewrite (EE 26%nat 26%bv eq_refl), R26 in P26.
  prreg HS (27%bv : bv 5) P27. rewrite (EE 27%nat 27%bv eq_refl), R27 in P27.
  pmkst HS.
  change (SRr SEGS W (cfg_at SEGS (BASE + S22_JOIN) (ms_regs msK) (ms_mem msK) md2) (lt_post B MT cx)).
  apply (HJOIN cx ly S W (ms_regs msK) (ms_mem msK) md2 k acc c m tab mt HBASE HFRM).
  + (* turn i adds nothing: the segment is ignored *)
    unfold x_decl. apply s22_decl_step_skip; [exact Hi | exact Hdecl | left; exact Hign].
  + apply (p1_keep cx i c m tab mt LFO_N LFO_NV ly S W regs mem md k acc (ms_regs msK) (ms_mem msK) md2
      HBASE HINV HJ P2 P3 P4 P8 P9).
    * intros a Ha H1 _. rewrite (K2 a Ha ltac:(lia)). exact (K1 a Ha ltac:(lia)).
    * apply KJ; [exact HV2|]. intros j Hj Hn.
      rewrite K2 by lia. apply K1; lia.
  + exact P15.
  + exact P16.
  + exact P20.
  + exact P21.
  + exact P24.
  + unfold s22_rk. repeat split; assumption.
- (* bnez a0 not taken: m->seg[i].ignore is clear *)
  rewrite branch_ne_U in Hc. rewrite (U_atom E 32 g E32), U_lit in Hc by lia.
  assert (Hign : SegModel.ms_ignore (x_seg cx i) = false).
  { destruct (SegModel.ms_ignore (x_seg cx i)) eqn:Hb; [|reflexivity].
    rewrite Hgdef in Hc; try rewrite Hb in Hc; vm_compute in Hc; discriminate Hc. }
  (* 0x85920 .. 0x8592c: bnez a0 falls through, a1 := 46, a0 := s3 = &m->seg[i], the jal of the strrchr wrapper *)
  paj_run_shc RUNP RUNC HS HJ.
  { lazymatch type of AWR1 with awr_ok _ _ _ ?rsA _ _ _ _ _ _ _ _ =>
      apply (s10_awr_skel _ _ _ rsA); [vm_compute; reflexivity | exact AWR1] end. }
  rename HF into HF2, HFr into HFr2, HG into HG2.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (mdT := mm) in *; clearbody mdT end.
  rename ms into msT. cbn [ms_mem mkst] in HFr2.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) ->
    rdW W (ms_mem msT) a = rdW W (ms_mem ms1) a).
  { intros a Ha Hn. apply (kept_of_frame E _ (w_H W) (ms_mem ms1) _ (fun y => x_sh cx + 4 <= y < x_sh cx + 7) HFr2);
      [| exact Ha | exact Hn].
    intros b wlo whi y Hin Hy.
    lazymatch type of Hin with In _ (windows ?rs) => let w := eval vm_compute in (windows rs) in
      change (In (b, wlo, whi) w) in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hy; rewrite ?U21 in Hy; cbv beta; lia |]).
    destruct Hin. }
  assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) -> rdW W (ms_mem msT) a = rdW W mem a)
    by (intros a Ha Hn; rewrite (K2 a Ha Hn); exact (K1 a Ha Hn)).
  assert (HVT : sa_zs (rdW W (ms_mem msT)) (x_sh cx + 4) [0; 0; 4]).
  { assert (RK : forall i0 r, nth_error (ss_mem ltac:(lazymatch type of HS with st_ok _ _ ?s _ => exact s end)) i0 = Some r ->
      region_ok SEGS E (mrestrict (w_H W) (ms_mem msT)) r)
      by (intros i0 r Hi0; exact (st_ok_region_nth E _ (restrict (w_H W) msT) i0 r HS Hi0)).
    lazymatch type of HS with st_ok _ _ ?ssB _ =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
      pose proof (RK 0%nat r0 ltac:(vm_compute; reflexivity)) as RSH end.
    destruct RSH as (_ & _ & _ & CSH). cbn [YP09.r_base YP09.r_chunks base_val] in CSH. rewrite U21 in CSH.
    exact (s10_zs_ok E (w_H W) (ms_mem msT) (x_sh cx) _ [0; 0; 4] 4 CSH ltac:(vm_compute; reflexivity)). }
  (* the registers at the jal *)
  prreg HS (1%bv : bv 5) P1.
  prreg HS (2%bv : bv 5) P2. rewrite (EE 2%nat 2%bv eq_refl) in P2.
  prreg HS (3%bv : bv 5) P3. rewrite (EE 3%nat 3%bv eq_refl) in P3.
  prreg HS (4%bv : bv 5) P4. rewrite (EE 4%nat 4%bv eq_refl) in P4.
  prreg HS (8%bv : bv 5) P8. rewrite (EE 8%nat 8%bv eq_refl) in P8.
  prreg HS (9%bv : bv 5) P9. rewrite (EE 9%nat 9%bv eq_refl) in P9.
  prreg HS (10%bv : bv 5) P10. rewrite (EE 22%nat 22%bv eq_refl), R22 in P10.
  prreg HS (11%bv : bv 5) P11.
  prreg HS (19%bv : bv 5) P19. rewrite (EE 22%nat 22%bv eq_refl), R22 in P19.
  prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. rewrite (EE 21%nat 21%bv eq_refl), R21 in P21.
  prreg HS (22%bv : bv 5) P22. rewrite (EE 22%nat 22%bv eq_refl), R22 in P22.
  prreg HS (23%bv : bv 5) P23. rewrite (EE 23%nat 23%bv eq_refl), R23 in P23.
  prreg HS (24%bv : bv 5) P24. rewrite (EE 24%nat 24%bv eq_refl), R24 in P24.
  prreg HS (25%bv : bv 5) P25. rewrite (EE 25%nat 25%bv eq_refl), R25 in P25.
  prreg HS (26%bv : bv 5) P26. rewrite (EE 26%nat 26%bv eq_refl), R26 in P26.
  prreg HS (27%bv : bv 5) P27. rewrite (EE 27%nat 27%bv eq_refl), R27 in P27.
  pmkst HS.
  (* the string: the segment's name in m (s22_name_str), unchanged by the run *)
  destruct (s22_name_str cx i c m (rdW W mem) HCM Hi) as (Hnstr & Hnlen & Hnul).
  set (nm := SegModel.ms_name (x_seg cx i)) in *.
  destruct (sa_strz_bytes SEGS (w_H W) mem x nm Hnstr) as (Hnb & Hn0 & Hzs).
  assert (Hlz : length (seg_spec.zb nm) = length nm) by (unfold seg_spec.zb; apply length_map).
  assert (Hsl : astr_len (seg_spec.zb nm) = Z.of_nat (length nm)) by (unfold astr_len; rewrite Hlz; reflexivity).
  pose proof (proj1 HJ) as HART.
  destruct (al_blocks _ _ LAWS ly S W (ms_mem msT) mdT m seg_spec.SEG_M_SIZE HART HinM)
    as (_ & _ & _ & _ & HMpresT & _ & _).
  change (req_size seg_spec.SEG_M_SIZE) with 9236 in HMpresT.
  assert (HspT : spZ (ms_regs msT) = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
  { unfold spZ. rewrite P2, F2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (Ho16 : (x_s1 cx - x_sp0 cx) mod 16 = 0).
  { pose proof (Z.div_mod (x_sp0 cx) 16 ltac:(lia)) as D1.
    replace (x_s1 cx - x_sp0 cx) with ((x_s1 cx / 32 * 2 - x_sp0 cx / 16) * 16).
    - apply Z.mod_mul. lia.
    - pose proof (Z.div_mod (x_s1 cx) 32 ltac:(lia)) as D2. lia. }
  assert (HSTR : astr_at SEGS W (ms_mem msT) x (seg_spec.zb nm)).
  { split; [|exact Hn0]. intros j Hj. rewrite length_app, Hlz in Hj. cbn [length] in Hj.
    rewrite (KT (x + Z.of_nat j)); [exact (Hnb j ltac:(rewrite length_app, Hlz; cbn [length]; lia)) | lia |].
    unfold in_app, ASAN_CEIL in HMapp. unfold kLowShadowBeg, kHighMemBeg in *. lia. }
  assert (HROM : rt_rom_view SEGS B W (ms_mem msT)).
  { destruct HIMG as (HRO & _ & _). intros a Hr Ho He.
    assert (Himg : in_img SEGS a) by (destruct Hr as (sg & Hsg & _ & Ha); exists sg; split; [exact Hsg | exact Ha]).
    pose proof (pa_img_range _ Himg) as HIR. unfold kImgEnd in HIR.
    rewrite (KT a ltac:(lia) ltac:(unfold kLowShadowBeg in *; lia)).
    apply HRO; [left; exact Hr | exact Ho | exact He]. }
  eapply SRr_bind.
  { exact (p1_strrchr_at W (ms_regs msT) (ms_mem msT) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
      (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S mdT k x (seg_spec.zb nm)
      (x_s1 cx - x_sp0 cx) (Z_to_bv 64 (BASE + S22_VR)) HJ P10 P11 ltac:(lia) HspT Ho16 ltac:(lia)
      ltac:(rewrite WS; unfold ESTACK; lia)
      ltac:(rewrite P3, F3; exact Hgp0) ltac:(rewrite P4, F4; exact Htp0)
      ltac:(rewrite P1; reflexivity) ltac:(apply ret_ok_codeptr_v; [unfold S22_VR; lia | reflexivity])
      HSTR
      ltac:(rewrite Hsl; apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) ly S W (ms_regs msT) (ms_mem msT) mdT m
              seg_spec.SEG_M_SIZE x _ HART HinM); unfold seg_spec.SEG_M_SIZE, ESTACK in *; lia)
      ltac:(rewrite Hsl; apply (amem_range_of_block SEGS B LAWS ly S W (ms_mem msT) mdT m seg_spec.SEG_M_SIZE x _
              HART HinM); [lia | change (req_size seg_spec.SEG_M_SIZE) with 9236; lia])
      ltac:(rewrite Hsl; intros a Ha; pose proof (Z.mod_pos_bound (x + Z.of_nat (length nm)) 8 ltac:(lia));
            apply (aview_some_of_apresent SEGS); apply (proj1 (HMpresT a ltac:(lia))))
      HROM). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ3 & HP3 & HQ3 & HK3).
  change (SRr SEGS W (cfg_at SEGS (BASE + S22_VR) regs2 mem2 md2) (lt_post B MT cx)).
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - 2 * ESTACK <= a < x_s1 cx) -> rdW W mem2 a = rdW W (ms_mem msT) a)
    by (intros a Ha Hn; apply HK3; [exact Ha | lia | tauto]).
  (* the registers after the call: s2 .. s11, sp, gp, tp, s0, s1 are callee-saved *)
  assert (G2 : getr regs2 2 = getr regs 2) by (rewrite (p1_pres _ _ 2%bv HP3) by p1_cs; exact P2).
  assert (G3 : getr regs2 3 = getr regs 3) by (rewrite (p1_pres _ _ 3%bv HP3) by p1_cs; exact P3).
  assert (G4 : getr regs2 4 = getr regs 4) by (rewrite (p1_pres _ _ 4%bv HP3) by p1_cs; exact P4).
  assert (G8 : getr regs2 8 = getr regs 8) by (rewrite (p1_pres _ _ 8%bv HP3) by p1_cs; exact P8).
  assert (G9 : getr regs2 9 = getr regs 9) by (rewrite (p1_pres _ _ 9%bv HP3) by p1_cs; exact P9).
  assert (G19 : getr regs2 19 = w64 x) by (rewrite (p1_pres _ _ 19%bv HP3) by p1_cs; exact P19).
  assert (G20 : getr regs2 20 = w64 4) by (rewrite (p1_pres _ _ 20%bv HP3) by p1_cs; exact P20).
  assert (G21 : getr regs2 21 = w64 (x_sh cx)) by (rewrite (p1_pres _ _ 21%bv HP3) by p1_cs; exact P21).
  assert (G22 : getr regs2 22 = w64 x) by (rewrite (p1_pres _ _ 22%bv HP3) by p1_cs; exact P22).
  assert (G23 : getr regs2 23 = w64 (-8)) by (rewrite (p1_pres _ _ 23%bv HP3) by p1_cs; exact P23).
  assert (G24 : getr regs2 24 = w64 tab) by (rewrite (p1_pres _ _ 24%bv HP3) by p1_cs; exact P24).
  assert (G25 : getr regs2 25 = w64 (Z.of_nat i)) by (rewrite (p1_pres _ _ 25%bv HP3) by p1_cs; exact P25).
  assert (G26 : getr regs2 26 = w64 (- x)) by (rewrite (p1_pres _ _ 26%bv HP3) by p1_cs; exact P26).
  assert (G27 : getr regs2 27 = w64 x) by (rewrite (p1_pres _ _ 27%bv HP3) by p1_cs; exact P27).
  assert (HINV3 : s22_inv B MT cx i c m tab mt LFO_NV (s22_L cx i c m mt) ly S W regs2 mem2 md2 k acc).
  { apply (p1_keep cx i c m tab mt LFO_N LFO_NV ly S W regs mem md k acc regs2 mem2 md2
      HBASE HINV HJ3 G2 G3 G4 G8 G9).
    - intros a Ha H1 H2. rewrite (K3 a Ha H2). exact (KT a Ha ltac:(lia)).
    - apply KJ.
      + intros j Hj. rewrite K3 by (cbn [length] in Hj; lia). exact (HVT j Hj).
      + intros j Hj Hn. rewrite K3 by lia. apply KT; lia. }
  rewrite Hzs in HQ3.
  destruct HQ3 as [(H10 & Hnin) | (j & Hlast & H10)].
  + apply (HVR cx ly S W regs2 mem2 md2 k acc c m tab mt 0 HBASE HFRM HINV3 Hign).
    * left. split; [reflexivity | exact (s22_strrchr_none nm 46 Hnul Hnin)].
    * exact H10.
    * exact G19.
    * exact G20.
    * exact G21.
    * exact G24.
    * unfold s22_rk. repeat split; assumption.
  + apply (HVR cx ly S W regs2 mem2 md2 k acc c m tab mt (x + Z.of_nat j) HBASE HFRM HINV3 Hign).
    * right. exists j. split; [exact (s22_strrchr_some nm 46 j Hnul Hlast) | reflexivity].
    * exact H10.
    * exact G19.
    * exact G20.
    * exact G21.
    * exact G24.
    * unfold s22_rk. repeat split; assumption.
Qed.

End e.
End f.
End d.
Print Assumptions s22_p1.
