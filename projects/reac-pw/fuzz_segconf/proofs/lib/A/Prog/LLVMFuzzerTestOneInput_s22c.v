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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 573 of its 614 lines of code are new or changed and 412 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): piece 3 of segment S14 of the
   walk of the test harness's entry function LLVMFuzzerTestOneInput (0x84d34), file group _s22c: the digit loop
   of the inlined m_split, 0x85974 <- 0x859a8, and its exit 0x859fc .. 0x85a14; the statement s22_p3_stmt of
   LLVMFuzzerTestOneInput_s22k.v (S22_JOIN i -> S22_VP i -> S22_VD i).

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep; checker (fresh, read-only): CONFIRM; none: written new)

   THE FORM: plugin-hostd/fuzz_command's lib/A/Prog/LLVMFuzzerTestOneInput_s43.v (origin/ossv/recipes 501c0d516c69,
   the trim loop: a seed holding only the byte a pass reads, the symbolic engine's runs and their branches, one pass
   per induction step). The code (dis:786-803 and 820-826 of the neutral excerpt), one pass:
   - 0x85974 .. 0x85978, run 1: a4 := a3 - 58; bltu a4, a7 (a7 = -10) splits: taken when a3 is not a digit
     (s22c_ltu58), m_digits fails, so m_split does, and turn i adds nothing: the join 0x859c4;
   - 0x8597c .. 0x85988, run 2: s2 := s2 * 10 + (a3 & 15) = SegModel.dstep s2 a3 (s22c_U_s2); bltu t1, s2
     (t1 = 4094) splits: taken when the value passed 4094 (s22_digits_none_big): the join;
   - 0x8598c .. 0x859a8, run 3: the 1-byte check of a1 (the seed's shadow entry over the byte, from m's block; the
     slow block 0x859b0 passes), lbu a3, 0(a2) (the byte after the t + 1 digits read, or the name's NUL), a1 and
     a2 up by one; bnez a3 splits: taken back to 0x85974 with t + 1 digits read (the induction hypothesis);
   - 0x859ac, 0x859fc, run 4: j; beqz s2 splits: taken when the value is 0 (m_split's vid < 1 test): the join;
   - 0x85a00 .. 0x85a14, run 5: s4 := a0 - s3 = di, a0 := a0 + s10, a1 := a0 + seqz a0 = di, a2 := s6,
     a0 := s11: the parent loop's head 0x85a18 at t = 0 (S22_VP).
   No run writes memory (the seed's one region has no write window), so every reader fact of s22_inv carries over
   unchanged (s22c_rd_all, s22c_inv_k). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_s10k LLVMFuzzerTestOneInput_s22k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the seed at 0x85974: every register its own atom but t0 = 10, t1 = 4094, a7 = -10 (literals, so the run keeps
   them) and a2 = a1 (atom 11, the next byte's address); one read-only region, that byte, whose value is atom 32;
   facts: a5 = the shadow base (the check's Bx), a1 inside the allocator's range, a3 and the next byte bytes, s2 at
   most 4094; one shadow entry, the next byte, for the 1-byte check at 0x8598c ---- *)
Definition VDx : sv := SOff 15 0.
Definition VDspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition vd_reg : YP09.region := YP09.mkRegion (Some 11%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition vd_facts : facts :=
  mkFacts [ (15%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (11%nat, mkAF 4096 0x7fffff800000 0); (13%nat, mkAF 0 255 0);
            (18%nat, mkAF 0 4094 0); (32%nat, mkAF 0 255 0) ] [] [].
Definition vd_sregs : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms (5%bv : bv 5) (SLit 10)) (6%bv : bv 5) (SLit 4094))
    (17%bv : bv 5) (SLit 18446744073709551606)) (12%bv : bv 5) (SOff 11 0).
Definition ss_vd : sstate := mkSS S22_VD vd_sregs [vd_reg] None vd_facts.
Definition vd_SH : list shent := [mkSHE 11 0 1].
(* the registers a run keeps: for the join and the next turn of the loop (with a0 and s4), for the parent loop's
   head (without them) *)
Definition s22c_kl : list (bv 5) := [2; 3; 4; 8; 9; 10; 15; 16; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition s22c_klp : list (bv 5) := [2; 3; 4; 8; 9; 15; 16; 19; 21; 22; 23; 24; 25; 26; 27]%bv.

(* ---- the code's tests against SegModel, byte by byte (one vm_compute over [0, 256), as the kit's s22_dig_b) ---- *)
(* 0x85974 .. 0x85978: a4 := a3 - 58 is below a7 = -10 as an unsigned 64-bit value exactly when a3 is not a digit *)
Lemma s22c_ltu58 : forall d, 0 <= d < 256 ->
  (zcanon (d + -58) <? zcanon 18446744073709551606) = negb (SegModel.isdigit d).
Proof. apply s22_byte_all. vm_compute. reflexivity. Qed.

(* 0x85980: a3 & 15 is the digit's value d - 48 *)
Lemma s22c_and15 : forall d, 0 <= d < 256 -> SegModel.isdigit d = true -> Z.land d 15 = d - 48.
Proof.
intros d Hd Hdig.
assert (H : (negb (SegModel.isdigit d) || (Z.land d 15 =? d - 48))%bool = true).
{ clear Hdig. revert d Hd.
  apply (s22_byte_all (fun d => (negb (SegModel.isdigit d) || (Z.land d 15 =? d - 48))%bool) (fun _ => true)).
  vm_compute. reflexivity. }
rewrite Hdig in H. cbn [negb orb] in H. apply Z.eqb_eq. exact H.
Qed.

(* m_split fails when m_digits of the tail fails, or gives 0 *)
Lemma s22c_split_none : forall name di, SegModel.strrchr name 46 = Some di ->
  SegModel.m_digits (skipn (Datatypes.S di) name) 0 = None -> SegModel.m_split name = None.
Proof.
intros name di Hs Hd. unfold SegModel.m_split. rewrite Hs.
destruct (_ || _)%bool; [reflexivity|]. rewrite Hd. reflexivity.
Qed.
Lemma s22c_split_zero : forall name di, SegModel.strrchr name 46 = Some di ->
  SegModel.m_digits (skipn (Datatypes.S di) name) 0 = Some 0 -> SegModel.m_split name = None.
Proof.
intros name di Hs Hd. unfold SegModel.m_split. rewrite Hs.
destruct (_ || _)%bool; [reflexivity|]. rewrite Hd. reflexivity.
Qed.

Lemma s22c_nth_skipn : forall {A} (l : list A) j i d, nth i (skipn j l) d = nth (j + i) l d.
Proof.
intros A l. induction l as [|x l IH]; intros [|j] i d; cbn;
  [destruct i; reflexivity | destruct i; reflexivity | reflexivity | apply IH].
Qed.

(* one more digit: the running value and the digit test over firstn (S t) *)
Lemma s22c_fold_S : forall l t, (t < length l)%nat ->
  fold_left SegModel.dstep (firstn (Datatypes.S t) l) 0 =
  SegModel.dstep (fold_left SegModel.dstep (firstn t l) 0) (nth t l 0).
Proof. intros l t Ht. rewrite (s22_firstn_S l t 0 Ht), fold_left_app. reflexivity. Qed.
Lemma s22c_all_S : forall l t, (t < length l)%nat -> forallb SegModel.isdigit (firstn t l) = true ->
  SegModel.isdigit (nth t l 0) = true -> forallb SegModel.isdigit (firstn (Datatypes.S t) l) = true.
Proof.
intros l t Ht H1 H2. rewrite (s22_firstn_S l t 0 Ht), forallb_app, H1, andb_true_l. cbn [forallb].
rewrite H2. reflexivity.
Qed.


Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma vd_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem a b d v,
  getr regs 5 = w64 10 -> getr regs 6 = w64 4094 -> getr regs 17 = w64 (-10) ->
  getr regs 11 = w64 a -> getr regs 12 = w64 a -> getr regs 13 = w64 d ->
  getr regs 15 = w64 SHADOW_OFF -> getr regs 18 = w64 v ->
  4096 <= a <= 0x7fffff800000 -> 0 <= b <= 255 -> 0 <= d <= 255 -> 0 <= v <= 4094 ->
  rdW W mem a = Some b ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 b])) ss_vd
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S22_VD)) mem (seg_rom SEGS))).
Proof.
intros W regs mem a b d v H5 H6 H17 H11 H12 H13 H15 H18 Ra Rb Rd Rv HV.
set (E := Eimg (Ereg regs [Z_to_bv 64 b])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E11 : ew E 11 = Z_to_bv 64 a) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E13 : ew E 13 = Z_to_bv 64 d) by (rewrite (EE 13%nat 13%bv eq_refl); exact H13).
assert (E15 : ew E 15 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 15%nat 15%bv eq_refl); exact H15).
assert (E18 : ew E 18 = Z_to_bv 64 v) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 b)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
unfold ss_vd. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold vd_sregs.
  apply regs_ok_rereg; [|reflexivity|].
  2: { rewrite H12. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  apply regs_ok_rereg; [|reflexivity|].
  2: { rewrite H17. cbn [sv_denot]. unfold w64. apply Z_to_bv64_eq_mod. reflexivity. }
  apply regs_ok_rereg; [|reflexivity|].
  2: { rewrite H6. reflexivity. }
  apply regs_ok_rereg; [|reflexivity|].
  2: { rewrite H5. reflexivity. }
  subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, vd_reg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E11, unsigned_lit_small by lia. split; [lia|]. split; [lia|].
  split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ a 0 1 (SOff 32 0) b);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
  rewrite Z.add_0_r. intros kk Hk. replace kk with 0%nat by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
  unfold aview in HV.
  destruct (mbyte SEGS (mrestrict (w_H W) mem) a) as [bb|] eqn:Eb; cbn in HV; [|discriminate HV].
  injection HV as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 bb), Hb. f_equal. f_equal.
  cbv [YO0f.le_byte YG0f.le_byte]. change (8 * Z.of_nat (N.to_nat 1)) with 8. change (8 * Z.of_nat 0) with 0.
  change (2 ^ 8) with 256. rewrite Z.shiftr_0_r. rewrite (Z.mod_small b 256) by lia.
  rewrite (Z.mod_small b 256) by lia. reflexivity.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok vd_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E15, E11, E13, E18, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
Qed.

Lemma vd_shok : forall (W : world SEGS) (regs : bvmap 5 word) mem a b,
  getr regs 15 = w64 SHADOW_OFF -> getr regs 11 = w64 a -> 0 <= a < 2 ^ 64 ->
  range_addressable (rdW W mem) SHADOW_OFF a 1 ->
  (a < SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= a) ->
  sh_ok SEGS VDx vd_SH (Eimg (Ereg regs [Z_to_bv 64 b])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem a b H15 H11 Ra RA Hband. unfold sh_ok, vd_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem _ VDx 11 a 1 a 0 1 RA).
- unfold VDx. apply U_atom; [rewrite (ew_Eimg_Ereg_nat regs _ 15%nat 15%bv eq_refl); exact H15 | unfold SHADOW_OFF; lia].
- apply U_atom; [rewrite (ew_Eimg_Ereg_nat regs _ 11%nat 11%bv eq_refl); exact H11 | lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. lia.
Qed.

(* a byte a reader shows is below 256 *)
Lemma s22c_rd_byte : forall (H : word -> bool) mem a v, aview SEGS H mem a = Some v -> 0 <= v < 256.
Proof.
intros H mem a v Hv. unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) a) as [bb|]; cbn in Hv; [|discriminate Hv].
injection Hv as <-. pose proof (bv_unsigned_in_range 8 bb) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.

(* the byte at index k of a C string, its NUL included *)
Lemma s22c_strz_at : forall (rd : reader) p s k, sa_strz rd p s -> (k <= length s)%nat ->
  rd (p + Z.of_nat k) = Some (nth k (s ++ [0]) 0).
Proof. intros rd p s k [Hz _] Hk. apply Hz. rewrite length_app. cbn [length]. lia. Qed.

(* a run whose regions have no write window keeps every byte the reader shows *)
Lemma s22c_rd_all : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hf Hro a. unfold aview, mbyte. rewrite Hf; [reflexivity|].
intros (r & Hin & Hr). rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.

(* a harness block's facts at a reader that shows the same bytes *)
Lemma s22c_hblk_k : forall B ly S (rd rd' : reader) a n, (forall x, rd' x = rd x) ->
  lt_hblk B ly S rd a n -> lt_hblk B ly S rd' a n.
Proof.
intros B ly S rd rd' a n K (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [exact H6|]. split; [intros x Hx; rewrite K; exact (H7 x Hx)|].
intros Hn s Hs. rewrite K. exact (H8 Hn s Hs).
Qed.

(* the registers a run leaves as atoms of the seed *)
Lemma s22c_regs_kept : forall E ss (ms : machine_state) (H : word -> bool) (regs : bvmap 5 word) extra
  (l : list (bv 5)),
  st_ok_pi SEGS VAL E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) l = true ->
  forall r, In r l -> getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms H regs extra l HS HA Hl r Hr.
exact (regs_kept_of_st_ok_pi E ss (restrict H ms) regs extra l HS HA Hl r Hr).
Qed.
Lemma s22c_ea_set : forall E0 E n w, (32 <= n)%nat -> env_agree 32 E0 E -> env_agree 32 E0 (ewset E n w).
Proof.
intros E0 E n w Hn [H1 H2].
split; [intros j Hj; rewrite ew_ewset_other by lia; exact (H1 j Hj) | rewrite ed_ewset; exact H2].
Qed.
Lemma s22c_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c Hn. cbn [sv_denot]. rewrite Hn. apply Z_to_bv64_eq_mod. rewrite Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* 0x8597c .. 0x85984: s2 := s2 * 10 + (a3 & 15) is SegModel.dstep *)
Lemma s22c_U_s2 : forall E v d, ew E 18 = Z_to_bv 64 v -> ew E 13 = Z_to_bv 64 d -> 0 <= v <= 4094 ->
  0 <= d < 256 -> SegModel.isdigit d = true ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff 18 0) (SLit 10)) (SAlu ALU_AND (SOff 13 0) (SLit 15))) = SegModel.dstep v d.
Proof.
intros E v d H18 H13 Hv Hd Hdig.
pose proof (s22c_and15 d Hd Hdig) as Ha. pose proof (SegModel.isdigit_range d Hdig) as Hr.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_and_lit by lia.
rewrite (U_atom E 18 v H18) by lia. rewrite (U_atom E 13 d H13) by lia. rewrite U_SLit, Ha.
rewrite (zcanon_id 10) by (unfold M64; lia). rewrite (zcanon_id (v * 10)) by (unfold M64; lia).
unfold SegModel.dstep. apply zcanon_id. unfold M64. lia.
Qed.

(* 0x85a00: s4 := a0 - s3 *)
Lemma s22c_U_s4 : forall E p di, ew E 10 = Z_to_bv 64 (p + di) -> ew E 19 = Z_to_bv 64 p ->
  0 <= p -> 0 <= di -> p + di < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SOff 19 0) (SLit (-1)))) = di.
Proof.
intros E p di H10 H19 Hp Hdi Hr.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E 10 (p + di) H10) by lia. rewrite (U_atom E 19 p H19) by lia. rewrite U_SLit.
unfold zcanon, M64. rewrite Zplus_mod_idemp_r.
replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
replace (p + di + p * (2 ^ 64 - 1)) with (di + p * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* 0x85a04 .. 0x85a0c: a0 := a0 + s10, a1 := a0 + seqz a0 *)
Lemma s22c_U_a1 : forall E p di, ew E 10 = Z_to_bv 64 (p + di) -> ew E 26 = Z_to_bv 64 (- p) ->
  0 < p -> 1 <= di -> p + di < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SOff 26 0))
         (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 10 0) (SOff 26 0)) (SLit 1))) = di.
Proof.
intros E p di H10 H26 Hp Hdi Hr.
assert (Hs : U E (SAlu ALU_ADD (SOff 10 0) (SOff 26 0)) = di).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 10 (p + di) H10) by lia.
  rewrite U_SOff, H26, Z.add_0_r, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. rewrite Zplus_mod_idemp_r.
  replace (p + di + - p) with di by ring. apply Z.mod_small. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite Hs. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hs, U_lit by lia.
destruct (Z.ltb_spec di 1) as [Hlt|_]; [lia|].
rewrite (zcanon_id 0) by (unfold M64; lia). rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia.
Qed.

(* turn i adds nothing when the name does not split *)
Lemma s22c_decl : forall cx i, (i < length (SegModel.mc_seg (x_mcF cx)))%nat -> 0 <= fst (x_decl cx i) ->
  SegModel.m_split (SegModel.ms_name (x_seg cx i)) = None -> x_decl cx (Datatypes.S i) = x_decl cx i.
Proof. intros cx i Hi Hpos Hs. unfold x_decl. apply s22_decl_step_skip; [exact Hi | exact Hpos | right; exact Hs]. Qed.

Ltac s22c_ew := repeat (rewrite ew_ewset_other by lia).
Ltac s22c_EA EA := repeat (apply s22c_ea_set; [lia|]); exact EA.
Ltac s22c_in := try unfold s22c_kl; try unfold s22c_klp; repeat first [left; reflexivity | right].
Ltac s22c_side := first [assumption | (s22c_ew; assumption) | lia].
Ltac s22c_reg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H
  end.
(* after a run: the reader is the one at the start of the piece (no region has a write window) *)
Ltac s22c_mem KA :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    let K := fresh "K" in
    pose proof (s22c_rd_all _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as K;
    let KA2 := fresh "KA" in
    pose proof (fun x => eq_trans (K x) (KA x)) as KA2;
    clear K KA HFr; rename KA2 into KA
  end;
  repeat lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
  lazymatch goal with HG : mem_grows _ _ |- _ => clear HG end;
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?dd |} _ =>
    tryif is_var dd then idtac else (let x := fresh "mdv" in set (x := dd) in *; clearbody x) end.

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
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* what every point of S14 keeps, at a later state with the same journal, the frame registers and the same reader *)
Lemma s22c_inv_k : forall cx i c m tab mt o L ly S W regs mem md k acc regs' mem' md',
  s22_inv B MT cx i c m tab mt o L ly S W regs mem md k acc ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  (forall a, rdW W mem' a = rdW W mem a) ->
  s22_inv B MT cx i c m tab mt o L ly S W regs' mem' md' k acc.
Proof.
intros cx i c m tab mt o L ly S W regs mem md k acc regs' mem' md' HI HJ' K2 K3 K4 K8 K9 KA.
destruct HI as (Hi & Hpos & (HF & HIMG & HBL & HBUD) & Hc & Hm & Ht & Hmt & HSL & HCM & HTB).
destruct HF as (_ & F2 & F3 & F4 & F8 & F9 & FSV & FH0 & FH8 & FH16 & FFL & FSB & FZS).
assert (KW : forall a0, rdword (rdW W mem') a0 = rdword (rdW W mem) a0)
  by (intros a0; apply rdword_ext; intros kk _; apply KA).
assert (KB : forall a0 bs, sa_bytes (rdW W mem) a0 bs -> sa_bytes (rdW W mem') a0 bs)
  by (intros a0 bs Hb j Hj; rewrite KA; exact (Hb j Hj)).
split; [exact Hi|]. split; [exact Hpos|]. split.
{ split; [|split; [|split; [exact HBL | exact HBUD]]].
  - split; [exact HJ'|]. rewrite K2, K3, K4, K8, K9, !KW.
    split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F8|]. split; [exact F9|].
    split; [intros j r Hj; rewrite KW; exact (FSV j r Hj)|].
    split; [exact FH0|]. split; [exact FH8|]. split; [exact FH16|]. split; [exact FFL|]. split; [exact FSB|].
    intros j Hj. rewrite KA. exact (FZS j Hj).
  - exact (s10_lt_img_kept B IMGS BSYM cx W mem' (rdW W mem) (proj1 HJ') (fun a0 _ _ _ => KA a0) HIMG). }
split; [exact (s22c_hblk_k B ly S _ _ c _ KA Hc)|].
split; [exact (s22c_hblk_k B ly S _ _ m _ KA Hm)|].
split; [exact (s22c_hblk_k B ly S _ _ tab _ KA Ht)|].
split; [exact (s22c_hblk_k B ly S _ _ mt _ KA Hmt)|].
split; [intros o0 v0 Hin; rewrite KW; exact (HSL o0 v0 Hin)|].
split.
{ destruct HCM as [(bs1 & B1 & EN1) (bs2 & B2 & EN2)].
  split; [exists bs1; exact (conj (KB _ _ B1) EN1) | exists bs2; exact (conj (KB _ _ B2) EN2)]. }
destruct HTB as (T1 & (bs1 & B1 & EN1) & G & V & (bs2 & B2 & EN2) & T6).
split; [exact T1|]. split; [exists bs1; exact (conj (KB _ _ B1) EN1)|].
split; [exact (KB _ _ G)|]. split; [intros j Hj; rewrite KA; exact (V j Hj)|].
split; [exists bs2; exact (conj (KB _ _ B2) EN2) | exact T6].
Qed.

(* the continue join 0x859c4, reached with turn i adding nothing *)
Lemma s22c_join : forall i cx ly S W regs mem md k acc c m tab mt regs' mem' md',
  S22_JOIN_stmt B MT i -> lt_base B MT cx -> sa_frm0 ->
  s22_inv B MT cx i c m tab mt LFO_NV (s22_L cx i c m mt) ly S W regs mem md k acc ->
  x_decl cx (Datatypes.S i) = x_decl cx i ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall r, In r s22c_kl -> getr regs' r = getr regs r) ->
  (forall a, rdW W mem' a = rdW W mem a) ->
  getr regs 15 = w64 SHADOW_OFF -> getr regs 16 = w64 m -> getr regs 20 = w64 4 ->
  getr regs 21 = w64 (x_sh cx) -> getr regs 24 = w64 tab -> s22_rk m i regs ->
  SRr SEGS W (cfg_at SEGS (BASE + S22_JOIN) regs' mem' md') (lt_post B MT cx).
Proof.
intros i cx ly S W regs mem md k acc c m tab mt regs' mem' md' HJN HB0 HFRM HINV Hdecl HJ' KR KA
  R15 R16 R20 R21 R24 (K22 & K23 & K25 & K26 & K27).
apply (HJN cx ly S W regs' mem' md' k acc c m tab mt HB0 HFRM Hdecl).
- apply s22c_inv_k with (1 := HINV) (2 := HJ'); [apply KR; s22c_in .. | exact KA].
- rewrite KR by s22c_in. exact R15.
- rewrite KR by s22c_in. exact R16.
- rewrite KR by s22c_in. exact R20.
- rewrite KR by s22c_in. exact R21.
- rewrite KR by s22c_in. exact R24.
- unfold s22_rk. rewrite !KR by s22c_in. tauto.
Qed.

(* S22_VD_stmt with the number of bytes left to read, n + t = the tail's length: the loop's measure *)
Definition s22c_vdn (i n : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z) (di t : nat) (v : Z),
  (length (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))) = n + t)%nat ->
  lt_base B MT cx -> sa_frm0 ->
  s22_inv B MT cx i c m tab mt LFO_NV (s22_L cx i c m mt) ly S W regs mem md k acc ->
  SegModel.ms_ignore (x_seg cx i) = false ->
  SegModel.strrchr (SegModel.ms_name (x_seg cx i)) 46 = Some di -> (di <> 0)%nat ->
  (t < length (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))))%nat ->
  forallb SegModel.isdigit (firstn t (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i)))) = true ->
  v = fold_left SegModel.dstep (firstn t (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i)))) 0 ->
  0 <= v <= 4094 ->
  getr regs 5 = w64 10 -> getr regs 6 = w64 4094 -> getr regs 17 = w64 (-10) ->
  getr regs 10 = w64 (seg_spec.mseg_addr m i + Z.of_nat di) ->
  getr regs 11 = w64 (seg_spec.mseg_addr m i + Z.of_nat (Datatypes.S di) + Z.of_nat t + 1) ->
  getr regs 12 = w64 (seg_spec.mseg_addr m i + Z.of_nat (Datatypes.S di) + Z.of_nat t + 1) ->
  getr regs 13 = w64 (nth t (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))) 0) ->
  getr regs 15 = w64 SHADOW_OFF -> getr regs 16 = w64 m -> getr regs 18 = w64 v ->
  getr regs 19 = w64 (seg_spec.mseg_addr m i) -> getr regs 20 = w64 4 ->
  getr regs 21 = w64 (x_sh cx) -> getr regs 24 = w64 tab -> s22_rk m i regs ->
  SRr SEGS W (cfg_at SEGS (BASE + S22_VD) regs mem md) (lt_post B MT cx).

(* one pass of the digit loop, from 0x85974 with t digits read: to the join, back to 0x85974 with t + 1, or out
   through 0x859fc to the parent loop's head 0x85a18 *)
Lemma s22c_pass : forall i n, S22_JOIN_stmt B MT i -> S22_VP_stmt B MT i -> s22c_vdn i n ->
  s22c_vdn i (Datatypes.S n).
Proof.
intros i n HJN HVP IH cx ly S W regs mem md k acc c m tab mt di t v Hlen HB0 HFRM HINV Hign Hstr Hdi0 Ht Hall Hv Hvr
  R5 R6 R17 R10 R11 R12 R13 R15 R16 R18 R19 R20 R21 R24 Hrk.
pose proof HINV as (Hi & Hpos & HCORE & _ & HHm & _ & _ & _ & HCM & _).
pose proof HCORE as ((HJ & _) & _).
pose proof (proj1 HJ) as HAR.
pose proof HHm as (Hmin & Hm4096 & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR Hmin) as (_ & _ & Hmceil & Hmapp & _ & _ & _).
assert (Hreq : req_size seg_spec.SEG_M_SIZE = 9236) by reflexivity.
rewrite Hreq in Hmceil, Hmapp.
pose proof (s22_name_str cx i c m (rdW W mem) HCM Hi) as (Hnz & Hn16 & Hnf).
assert (Hi32 : (i < 32)%nat).
{ pose proof HCM as (_ & (mbs & _ & (_ & H32 & _))). unfold x_mcF in Hi. lia. }
pose proof ASAN_CEIL_range as (HCE & _). unfold ASAN_CEIL in HCE.
assert (EA : seg_spec.mseg_addr m i = m + 256 * Z.of_nat i) by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
pose proof Hrk as (K22 & K23 & K25 & K26 & K27).
set (name := SegModel.ms_name (x_seg cx i)) in *.
assert (HtL : (Datatypes.S di + t < length name)%nat) by (rewrite length_skipn in Ht; lia).
set (d := nth t (skipn (Datatypes.S di) name) 0) in *.
assert (Ed : d = nth (Datatypes.S di + t) (name ++ [0]) 0)
  by (unfold d; rewrite s22c_nth_skipn, app_nth1 by lia; reflexivity).
pose proof (s22c_strz_at _ _ _ (Datatypes.S di + t) Hnz ltac:(lia)) as Hdrd. rewrite <- Ed in Hdrd.
pose proof (s22c_rd_byte _ _ _ _ Hdrd) as Rd.
pose proof (s22c_strz_at _ _ _ (Datatypes.S di + t + 1) Hnz ltac:(lia)) as Hbrd.
set (b := nth (Datatypes.S di + t + 1) (name ++ [0]) 0) in *.
pose proof (s22c_rd_byte _ _ _ _ Hbrd) as Rb.
replace (seg_spec.mseg_addr m i + Z.of_nat (Datatypes.S di + t + 1))
  with (seg_spec.mseg_addr m i + Z.of_nat (Datatypes.S di) + Z.of_nat t + 1) in Hbrd by lia.
(* the byte the pass reads at a1 = a2 lies in m's block, apart from the shadow band *)
assert (Ha : 4096 <= seg_spec.mseg_addr m i + Z.of_nat (Datatypes.S di) + Z.of_nat t + 1 <= 0x7fffff800000) by lia.
assert (Hband : seg_spec.mseg_addr m i + Z.of_nat (Datatypes.S di) + Z.of_nat t + 1 < SHADOW_OFF \/
                SHADOW_OFF + 17592186044416 <= seg_spec.mseg_addr m i + Z.of_nat (Datatypes.S di) + Z.of_nat t + 1).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hmapp. unfold SHADOW_OFF. lia. }
assert (RA : range_addressable (rdW W mem) SHADOW_OFF
               (seg_spec.mseg_addr m i + Z.of_nat (Datatypes.S di) + Z.of_nat t + 1) 1).
{ apply (range_addressable_of_block SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE);
    [exact HAR | exact Hmin | lia | rewrite Hreq; lia]. }
pose proof (vd_seed W regs mem _ b d v R5 R6 R17 R11 R12 R13 R15 R18 Ha ltac:(lia) ltac:(lia) Hvr Hbrd) as HS.
pose proof (vd_shok W regs mem _ b R15 R11 ltac:(lia) RA Hband) as SHOK.
pose proof (Eimg_env (Ereg regs [Z_to_bv 64 b])) as HEI.
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew (Eimg (Ereg regs [Z_to_bv 64 b])) n0 = getr regs r)
  by (intros n0 r Hn0; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E32 : ew (Eimg (Ereg regs [Z_to_bv 64 b])) 32 = Z_to_bv 64 b)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EA0 : env_agree 32 (Ereg regs [Z_to_bv 64 b]) (Eimg (Ereg regs [Z_to_bv 64 b])))
  by (split; [intros n0 Hn0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
remember (Eimg (Ereg regs [Z_to_bv 64 b])) as E0 eqn:HE0. clear HE0.
assert (E10 : ew E0 10 = Z_to_bv 64 (seg_spec.mseg_addr m i + Z.of_nat di))
  by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E11 : ew E0 11 = Z_to_bv 64 (seg_spec.mseg_addr m i + Z.of_nat (Datatypes.S di) + Z.of_nat t + 1))
  by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E13 : ew E0 13 = Z_to_bv 64 d) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (E18 : ew E0 18 = Z_to_bv 64 v) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E0 19 = Z_to_bv 64 (seg_spec.mseg_addr m i)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E22 : ew E0 22 = Z_to_bv 64 (seg_spec.mseg_addr m i)) by (rewrite (EE 22%nat 22%bv eq_refl); exact K22).
assert (E26 : ew E0 26 = Z_to_bv 64 (- seg_spec.mseg_addr m i)) by (rewrite (EE 26%nat 26%bv eq_refl); exact K26).
assert (E27 : ew E0 27 = Z_to_bv 64 (seg_spec.mseg_addr m i)) by (rewrite (EE 27%nat 27%bv eq_refl); exact K27).
assert (KA : forall x, rdW W mem x = rdW W mem x) by (intros x; reflexivity).
unfold cfg_at. change (w64 (BASE + S22_VD)) with (Z_to_bv 64 (BASE + S22_VD)).
(* 0x85974 .. 0x85978: a4 := a3 - 58; bltu a4, a7 (a7 = -10) *)
paj_run_tok RUN HS HJ SHOK VDspan.
{ awr_ok_tac. }
s22c_mem KA.
psrr_branch_tok RUN BR HS SHOK VDspan.
- (* a3 is not a digit: m_digits fails, so m_split does; on to the join 0x859c4 *)
  assert (Hnd : SegModel.isdigit d = false).
  { rewrite branch_ltu_U, U_SOff, U_SLit, E13, unsigned_lit_small in Hc by lia.
    rewrite (s22c_ltu58 d Rd) in Hc. apply negb_true_iff in Hc. exact Hc. }
  clear Hc.
  pose proof (s22c_split_none name di Hstr (s22_digits_none_nondigit _ t Ht Hnd)) as Hspl.
  paj_run_to_tok RUNTO HS HJ SHOK VDspan S22_JOIN.
  { awr_ok_tac. }
  s22c_mem KA. pmkst HS.
  lazymatch goal with HS : st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
    exact (s22c_join i cx ly S W regs mem md k acc c m tab mt (ms_regs msf) (ms_mem msf) _ HJN HB0 HFRM HINV
      (s22c_decl cx i Hi Hpos Hspl) HJ
      (s22c_regs_kept Ef ssf msf (w_H W) regs [Z_to_bv 64 b] s22c_kl HS ltac:(s22c_EA EA0)
        ltac:(vm_compute; reflexivity))
      KA R15 R16 R20 R21 R24 Hrk)
  end.
- (* a3 is a digit *)
  assert (Hdig : SegModel.isdigit d = true).
  { rewrite branch_ltu_U, U_SOff, U_SLit, E13, unsigned_lit_small in Hc by lia.
    rewrite (s22c_ltu58 d Rd) in Hc. apply negb_false_iff in Hc. exact Hc. }
  clear Hc.
  (* 0x8597c .. 0x85988: s2 := s2 * 10 + (a3 & 15); bltu t1, s2 (t1 = 4094) *)
  paj_run_tok RUN HS HJ SHOK VDspan.
  { awr_ok_tac. }
  s22c_mem KA.
  psrr_branch_tok RUN BR HS SHOK VDspan.
  + (* the value passed 4094: m_digits fails; on to the join *)
    assert (Hbig : 4094 < SegModel.dstep v d).
    { rewrite branch_ltu_U, U_lit, (s22c_U_s2 _ v d) in Hc by s22c_side. apply Z.ltb_lt in Hc. exact Hc. }
    clear Hc.
    assert (Hbig' : 4094 < fold_left SegModel.dstep (firstn (Datatypes.S t) (skipn (Datatypes.S di) name)) 0)
      by (rewrite s22c_fold_S, <- Hv by exact Ht; exact Hbig).
    pose proof (s22c_split_none name di Hstr (s22_digits_none_big _ t Ht Hbig')) as Hspl.
    paj_run_to_tok RUNTO HS HJ SHOK VDspan S22_JOIN.
    { awr_ok_tac. }
    s22c_mem KA. pmkst HS.
    lazymatch goal with HS : st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
      exact (s22c_join i cx ly S W regs mem md k acc c m tab mt (ms_regs msf) (ms_mem msf) _ HJN HB0 HFRM HINV
        (s22c_decl cx i Hi Hpos Hspl) HJ
        (s22c_regs_kept Ef ssf msf (w_H W) regs [Z_to_bv 64 b] s22c_kl HS ltac:(s22c_EA EA0)
          ltac:(vm_compute; reflexivity))
        KA R15 R16 R20 R21 R24 Hrk)
    end.
  + (* the value is at most 4094 *)
    assert (Hle : SegModel.dstep v d <= 4094).
    { rewrite branch_ltu_U, U_lit, (s22c_U_s2 _ v d) in Hc by s22c_side. apply Z.ltb_ge in Hc. exact Hc. }
    clear Hc.
    (* 0x8598c .. 0x859a8: the 1-byte check of a1 (its shadow entry: the slow block 0x859b0 passes), lbu a3, 0(a2),
       a1 += 1, a2 += 1; bnez a3 *)
    paj_run_tok RUN HS HJ SHOK VDspan.
    { awr_ok_tac. }
    s22c_mem KA.
    psrr_branch_tok RUN BR HS SHOK VDspan.
    * (* the next byte is not the NUL: back to the head 0x85974 with t + 1 digits read *)
      assert (Hb0 : b <> 0).
      { rewrite branch_ne_U, (U_atom _ 32 b), U_lit in Hc by s22c_side.
        apply negb_true_iff, Z.eqb_neq in Hc. exact Hc. }
      clear Hc.
      assert (HtL1 : (Datatypes.S di + t + 1 < length name)%nat).
      { destruct (Nat.eq_dec (Datatypes.S di + t + 1) (length name)) as [Heq|Hne]; [|lia].
        exfalso. apply Hb0. unfold b. rewrite Heq, app_nth2, Nat.sub_diag by lia. reflexivity. }
      assert (Ebn : b = nth (Datatypes.S t) (skipn (Datatypes.S di) name) 0)
        by (unfold b; rewrite s22c_nth_skipn, app_nth1 by lia; f_equal; lia).
      paj_run_to_tok RUNTO HS HJ SHOK VDspan S22_VD.
      { awr_ok_tac. }
      s22c_mem KA. pmkst HS.
      s22c_reg HS (5%bv : bv 5) Q5. s22c_reg HS (6%bv : bv 5) Q6. s22c_reg HS (17%bv : bv 5) Q17.
      s22c_reg HS (11%bv : bv 5) Q11. s22c_reg HS (12%bv : bv 5) Q12. s22c_reg HS (13%bv : bv 5) Q13.
      s22c_reg HS (18%bv : bv 5) Q18.
      cbn [sv_denot] in Q5, Q6, Q17.
      rewrite (s22c_den_off _ 11 (seg_spec.mseg_addr m i + Z.of_nat (Datatypes.S di) + Z.of_nat t + 1) 1) in Q11, Q12
        by (s22c_ew; exact E11).
      rewrite (s22c_den_off _ 32 b 0) in Q13 by (s22c_ew; exact E32).
      rewrite denot_lit_U, (s22c_U_s2 _ v d) in Q18 by s22c_side.
      lazymatch goal with HS : st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msf) |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdf |} _ =>
        pose proof (s22c_regs_kept Ef ssf msf (w_H W) regs [Z_to_bv 64 b] s22c_kl HS ltac:(s22c_EA EA0)
          ltac:(vm_compute; reflexivity)) as KR;
        change (SRr SEGS W (cfg_at SEGS (BASE + S22_VD) (ms_regs msf) (ms_mem msf) mdf) (lt_post B MT cx));
        apply (IH cx ly S W (ms_regs msf) (ms_mem msf) mdf k acc c m tab mt di (Datatypes.S t) (SegModel.dstep v d))
      end.
      all: try change (SegModel.ms_name (x_seg cx i)) with name.
      { lia. }
      { exact HB0. }
      { exact HFRM. }
      { apply s22c_inv_k with (1 := HINV) (2 := HJ); [apply KR; s22c_in .. | exact KA]. }
      { exact Hign. }
      { exact Hstr. }
      { exact Hdi0. }
      { rewrite length_skipn. lia. }
      { apply s22c_all_S; [exact Ht | exact Hall | exact Hdig]. }
      { rewrite s22c_fold_S by exact Ht. rewrite <- Hv. reflexivity. }
      { pose proof (SegModel.isdigit_range d Hdig). unfold SegModel.dstep in *. lia. }
      { exact Q5. }
      { exact Q6. }
      { rewrite Q17. unfold w64. apply Z_to_bv64_eq_mod. reflexivity. }
      { rewrite KR by s22c_in. exact R10. }
      { rewrite Q11. unfold w64. f_equal. lia. }
      { rewrite Q12. unfold w64. f_equal. lia. }
      { rewrite Q13, Z.add_0_r, Ebn. reflexivity. }
      { rewrite KR by s22c_in. exact R15. }
      { rewrite KR by s22c_in. exact R16. }
      { exact Q18. }
      { rewrite KR by s22c_in. exact R19. }
      { rewrite KR by s22c_in. exact R20. }
      { rewrite KR by s22c_in. exact R21. }
      { rewrite KR by s22c_in. exact R24. }
      { unfold s22_rk. rewrite !KR by s22c_in. tauto. }
    * (* the next byte is the NUL: every byte of the tail is a digit *)
      assert (Hb0 : b = 0).
      { rewrite branch_ne_U, (U_atom _ 32 b), U_lit in Hc by s22c_side.
        apply negb_false_iff, Z.eqb_eq in Hc. exact Hc. }
      clear Hc.
      assert (HtE : (Datatypes.S di + t + 1 = length name)%nat).
      { destruct (Nat.lt_ge_cases (Datatypes.S di + t + 1) (length name)) as [Hlt|Hge]; [|lia].
        exfalso. assert (Hin : In b name) by (unfold b; rewrite app_nth1 by lia; apply nth_In; lia).
        rewrite Hb0 in Hin. exact (Hnf Hin). }
      assert (Hfull : firstn (Datatypes.S t) (skipn (Datatypes.S di) name) = skipn (Datatypes.S di) name)
        by (apply firstn_all2; rewrite length_skipn; lia).
      assert (Hall' : forallb SegModel.isdigit (skipn (Datatypes.S di) name) = true)
        by (rewrite <- Hfull; apply s22c_all_S; [exact Ht | exact Hall | exact Hdig]).
      assert (Hfold : fold_left SegModel.dstep (skipn (Datatypes.S di) name) 0 = SegModel.dstep v d)
        by (rewrite <- Hfull, s22c_fold_S, <- Hv by exact Ht; reflexivity).
      assert (Hmd : SegModel.m_digits (skipn (Datatypes.S di) name) 0 =
                    Some (fold_left SegModel.dstep (skipn (Datatypes.S di) name) 0))
        by (apply s22_digits_some; [exact Hall' | rewrite Hfold; exact Hle]).
      rewrite Hfold in Hmd.
      (* 0x859ac: j 0x859fc; beqz s2 *)
      paj_run_tok RUN HS HJ SHOK VDspan.
      { awr_ok_tac. }
      s22c_mem KA.
      psrr_branch_tok RUN BR HS SHOK VDspan.
      -- (* the value is 0: m_split fails by its vid < 1 test; on to the join *)
         assert (Hz : SegModel.dstep v d = 0).
         { rewrite branch_eq_U, (s22c_U_s2 _ v d), U_lit in Hc by s22c_side. apply Z.eqb_eq in Hc. exact Hc. }
         clear Hc. rewrite Hz in Hmd.
         pose proof (s22c_split_zero name di Hstr Hmd) as Hspl.
         paj_run_to_tok RUNTO HS HJ SHOK VDspan S22_JOIN.
         { awr_ok_tac. }
         s22c_mem KA. pmkst HS.
         lazymatch goal with HS : st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
           exact (s22c_join i cx ly S W regs mem md k acc c m tab mt (ms_regs msf) (ms_mem msf) _ HJN HB0 HFRM HINV
             (s22c_decl cx i Hi Hpos Hspl) HJ
             (s22c_regs_kept Ef ssf msf (w_H W) regs [Z_to_bv 64 b] s22c_kl HS ltac:(s22c_EA EA0)
               ltac:(vm_compute; reflexivity))
             KA R15 R16 R20 R21 R24 Hrk)
         end.
      -- (* the value is in 1 .. 4094: 0x85a00 .. 0x85a14, s4 := a0 - s3 = di, a0 := a0 + s10 = di,
            a1 := a0 + seqz a0 = di, a2 := s6, a0 := s11; on to the parent loop's head at t = 0 *)
         assert (Hv0 : SegModel.dstep v d <> 0).
         { rewrite branch_eq_U, (s22c_U_s2 _ v d), U_lit in Hc by s22c_side. apply Z.eqb_neq in Hc. exact Hc. }
         clear Hc.
         paj_run_to_tok RUNTO HS HJ SHOK VDspan S22_VP.
         { awr_ok_tac. }
         s22c_mem KA. pmkst HS.
         s22c_reg HS (5%bv : bv 5) Q5. s22c_reg HS (10%bv : bv 5) Q10. s22c_reg HS (11%bv : bv 5) Q11.
         s22c_reg HS (12%bv : bv 5) Q12. s22c_reg HS (18%bv : bv 5) Q18. s22c_reg HS (20%bv : bv 5) Q20.
         cbn [sv_denot] in Q5.
         rewrite (s22c_den_off _ 27 (seg_spec.mseg_addr m i) 0) in Q10 by (s22c_ew; exact E27).
         rewrite (s22c_den_off _ 22 (seg_spec.mseg_addr m i) 0) in Q12 by (s22c_ew; exact E22).
         rewrite denot_lit_U, (s22c_U_a1 _ (seg_spec.mseg_addr m i) (Z.of_nat di)) in Q11 by s22c_side.
         rewrite denot_lit_U, (s22c_U_s4 _ (seg_spec.mseg_addr m i) (Z.of_nat di)) in Q20 by s22c_side.
         rewrite denot_lit_U, (s22c_U_s2 _ v d) in Q18 by s22c_side.
         lazymatch goal with HS : st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msf) |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdf |} _ =>
           pose proof (s22c_regs_kept Ef ssf msf (w_H W) regs [Z_to_bv 64 b] s22c_klp HS ltac:(s22c_EA EA0)
             ltac:(vm_compute; reflexivity)) as KR;
           change (SRr SEGS W (cfg_at SEGS (BASE + S22_VP) (ms_regs msf) (ms_mem msf) mdf) (lt_post B MT cx));
           apply (HVP cx ly S W (ms_regs msf) (ms_mem msf) mdf k acc c m tab mt di 0%nat (SegModel.dstep v d))
         end.
         all: try change (SegModel.ms_name (x_seg cx i)) with name.
         { exact HB0. }
         { exact HFRM. }
         { apply s22c_inv_k with (1 := HINV) (2 := HJ); [apply KR; s22c_in .. | exact KA]. }
         { exact Hign. }
         { exact Hstr. }
         { exact Hdi0. }
         { exact Hmd. }
         { pose proof (SegModel.isdigit_range d Hdig). unfold SegModel.dstep in *. lia. }
         { lia. }
         { reflexivity. }
         { exact Q5. }
         { rewrite Q10. reflexivity. }
         { rewrite Q11. unfold w64. f_equal. lia. }
         { rewrite Q12. reflexivity. }
         { rewrite KR by s22c_in. exact R15. }
         { rewrite KR by s22c_in. exact R16. }
         { exact Q18. }
         { rewrite KR by s22c_in. exact R19. }
         { exact Q20. }
         { rewrite KR by s22c_in. exact R21. }
         { rewrite KR by s22c_in. exact R24. }
         { unfold s22_rk. rewrite !KR by s22c_in. tauto. }
Qed.

(* the digit loop, by induction on the bytes left to read *)
Lemma s22c_vd_all : forall i, S22_JOIN_stmt B MT i -> S22_VP_stmt B MT i -> forall n, s22c_vdn i n.
Proof.
intros i HJN HVP n. induction n as [|n IH].
- intros cx ly S W regs mem md k acc c m tab mt di t v Hlen _ _ _ _ _ _ Ht. exfalso. lia.
- exact (s22c_pass i n HJN HVP IH).
Qed.

Lemma s22_p3 : s22_p3_stmt B MT.
Proof.
intros i HJN HVP cx ly S W regs mem md k acc c m tab mt di t v HB0 HFRM HINV Hign Hstr Hdi0 Ht.
exact (s22c_vd_all i HJN HVP (length (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))) - t)
  cx ly S W regs mem md k acc c m tab mt di t v ltac:(lia) HB0 HFRM HINV Hign Hstr Hdi0 Ht).
Qed.

End e.
End f.
End d.
Print Assumptions s22_p3.
