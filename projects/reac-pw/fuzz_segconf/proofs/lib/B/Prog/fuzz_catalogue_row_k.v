(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of rec_shape_of (plugin-hostd/fuzz_command, 0x891ec, 69 instructions),
   in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (the entry state with the GOT word and the shadow cell)
   and A/ACh5.v (the composition of the segments into the contract): the prologue up to the loop head (0x891ec ..
   0x89254), then the loop of lib/A/Prog/rec_shape_of_s.v for the 28 rows, from the image's read-only table g_shapes
   and the literals it points to (lib/A/Prog/CmdRo.v). The per-binary facts are the lemmas of CmdRecFacts' groups in
   lib/A/Prog/CmdRecBase.v, CmdRecRo.v and CmdRecImg.v, under the walk hypotheses
   (with cgif's names). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_shape_of.v, with its module paths and module names changed; 388 of its 485 lines of code are new or changed and 221 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3..., twin 80e82127e8ca...): the walk
   kit of fuzz_catalogue_row (0x8a7d8 = BASE + AF_fuzz_catalogue_row, 200 bytes, 50 instructions, frame 64 bytes, no
   side-stack frame, no UBSan trap branch; catalogue.c:29-35), in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre
   at the entry, SRr of apost_base at the return), against image B's copy lib/B/Prog/fuzz_catalogue_row_c.v of
   fuzz_catalogue_row_contract.
   rule 24 (reuse), RELOCATION: reused lib/A/Prog/fuzz_catalogue_rowA_k.v (the image-A m_file-family lane, commit
   01bfbfa568f9, the image-A walk kit; itself adapted from proofs/reac-pw/fuzz_pin/lib/A/PPgRow.v at
   commit b4e9443a2b9c in the shape of fuzz_command's rec_shape_of walk). Image B's code is
   image A's word for word except the pc-relative words (the ld at 0x8a808 of the .got word 0xa3210, the addi at
   0x8a814 of fuzz_catalogue 0xa20a0, and the three jal targets), which the listing states as the same atoms
   (A_OBJ 0, A_OBJ 77, the strlen / bcmp trampolines and __asan_report_load8 by name). What differs from the A
   file: the Require lines (image B's kit, listing and runtime copies under lib/B, and SegInstB.v for SegInstA.v:
   the same names at image B's values), the table's address in fcr_row_bounds and the segments' HcA (catA =
   0xa20a0), the image's end (kImgEnd = 0x602000 in fcr_tok_low / fcr_rom_view) and these comments.

   THE CODE (the neutral listing of fuzz_catalogue_row in image B):
     0x8a7d8-0x8a7f8  addi sp,sp,-64; ra, s0..s6 saved at sp+56 .. sp+0
     0x8a7fc-0x8a800  s1 = a1 = n, s2 = a0 = p
     0x8a804-0x8a80c  s5 = the shadow base, through the GOT word 0xa3210 (listing object 0) and the cell 0xac7b8
                      (__asan_shadow_memory_dynamic_address, object 12)
     0x8a810-0x8a824  s0 = s3 = fuzz_catalogue 0xa20a0 (object 77), s5 += s0 >> 3, s6 = 11
     0x8a828 lbu a0,0(s5); 0x8a82c bnez a0 -> 0x8a898      the instrumented check of row i's token-pointer word
     0x8a830 ld s4,0(s0); 0x8a834 mv a0,s4; 0x8a838 jal strlen's trampoline 0x43a98
     0x8a83c bne a0,s1 -> 0x8a854                          length <> n: next row
     0x8a840-0x8a848 a0 = s4, a1 = s2, a2 = s1; 0x8a84c jal bcmp's trampoline 0x43ac4
     0x8a850 beqz a0 -> 0x8a86c                            equal: return this row
     0x8a854-0x8a860 s6 -= 1, s3 += 296, s5 += 37, s0 += 296; 0x8a864 bnez s6 -> 0x8a828
     0x8a868 s0 = 0; 0x8a86c a0 = s0; 0x8a870-0x8a890 ra, s0..s6 restored, sp += 64; 0x8a894 ret
     0x8a898 mv a0,s3; 0x8a89c jal the error path 0x5d0f0 (a call of an errpath_* entry), which the walk shows is
     not reached: the token executor decides the check from the shadow entry of the row's first granule.
   The UBSan checks of image B put no compare-and-trap branch in this function (the 50 words above hold no
   `unimp`), so the walk has no trap edge to refute.

   THE STATES. Every loop segment is seeded from concrete registers (fcr_regs_at) by fcr_seed. Atoms: 0..31 the
   registers at the segment's start, 32 the shadow base SB, 33 row i's address row_addr cat i, 34 the rows left
   11 - i, 35..42 the eight words the prologue saved (ra, s0..s6), 43 row i's token pointer. The row index is
   an atom's value, never a literal of the state, so each segment runs once for all 11 rows. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegInstB fuzz_catalogue_row_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------
   Image numbers and program points *)
(* image B's pure numbers are lib/B/Prog/SegInstB.v's (the image-B harness lane, SegInstA's names at image B's values):
   - catA = 0xa20a0: fuzz_catalogue (twin .symtab, nm line 2299, 0xfe0 bytes with its redzone, in .data.rel.ro),
     the listing's object 77 (SegAddr.v seg_objs index 77 = 0xa20a0; the auipc/addi at 0x8a810 is SegList.v
     `PAddHi (8%bv : reg) (10%bv : reg) 121 (A_OBJ 77) 0x0`); fcr_V77 checks it against the listing.
   - STK_fuzz_catalogue_row = 64 + 2 * ESTACK: the 64-byte frame and below it the deepest window of a callee,
     bcmp's 2 * ESTACK (abcmp_realizes, lib/B/YG0d.v:366-385; strlen asks ESTACK, lib/B/Rt/RtString.v:84-89);
     both calls run at sp0 - 64.
   - RLO_A / RHI_A: SegGlob.SEG_RLO / SEG_RHI (image B 0xa1c60 / 0xa3f08); the walk reads only the in_rom
     disjunct of arodata_okP (fcr_rom_view). *)
(* program points, as listing offsets (SegList.v AF_fuzz_catalogue_row = 0x5a18, seg_text = 0x84dc0) *)
Definition FCR_HEAD : Z := AF_fuzz_catalogue_row + 0x50.   (* 0x8a828, the loop head *)
Definition FCR_R1 : Z := AF_fuzz_catalogue_row + 0x64.     (* 0x8a83c, strlen's return *)
Definition FCR_R2 : Z := AF_fuzz_catalogue_row + 0x78.     (* 0x8a850, bcmp's return *)
Definition FCR_NEXT : Z := AF_fuzz_catalogue_row + 0x7c.   (* 0x8a854, the next-row block *)

(* the registers the prologue saves, from the frame's top: ra at sp+56 down to s6 at sp+0 *)
Definition fcr_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22].

(* ------------------------------------------------------------------------------------------------
   The symbolic states *)
Definition FBx : sv := SOff 32 0.
(* s5 at the loop head: the shadow address of row i, in the form the token executor matches (YCbn.v match_x) *)
Definition fshx : sv := SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 33 0) (SLit 3)).
Definition fcr_frame_region : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 64 0 0
(map (fun j => YP09.mkChunk (56 - 8 * Z.of_nat j) (CVal 8 (SOff (35 + j) 0))) (seq 0 8)).
Definition fcr_row_region : YP09.region :=
YP09.mkRegion (Some 33%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 43 0))].
Definition fcr_regions : smem := [fcr_frame_region; fcr_row_region].
Definition fcr_atom_facts : list (nat * afact) :=
[(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF catA (catA + 2960) 0);
 (34%nat, mkAF 1 11 0)].
Definition fcr_facts : facts := mkFacts fcr_atom_facts [] [].
(* the shadow entry of row i's first granule: the token-pointer word the check guards *)
Definition fcr_SH : list shent := [mkSHE 33 0 8].
Definition fcr_sregs : list sv :=
sr_set (sr_set (sr_set (sr_set sr_atoms (8%bv : bv 5) (SOff 33 0)) (19%bv : bv 5) (SOff 33 0)) (21%bv : bv 5) fshx)
(22%bv : bv 5) (SOff 34 0).
Definition ss_fcr (pc : Z) : sstate := mkSS pc fcr_sregs fcr_regions None fcr_facts.
Definition fcr_extra (regs : bvmap 5 word) (i : nat) (tp : Z) : list word :=
[Z_to_bv 64 SB; Z_to_bv 64 (pin_spec.row_addr catA i); Z_to_bv 64 (11 - Z.of_nat i)] ++
map (fun r => getr regs (Z_to_bv 5 r)) fcr_saved ++ [Z_to_bv 64 tp].
(* the entry state: every register its own atom, atom 32 the shadow base; the 64-byte frame below the entry sp,
   the GOT word of the shadow base's cell and the cell (fuzz_command's rec_shape_of.v ss_rso_entry) *)
Definition fcr_entry_facts : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0)] [] [].
Definition ss_fcr_entry : sstate :=
mkSS AF_fuzz_catalogue_row sr_atoms [stack_region 64; got_regionP; bcell_regionP 32] None fcr_entry_facts.

(* ------------------------------------------------------------------------------------------------
   Arithmetic, bytes and the model *)
Lemma fcr_row_bounds : forall i, (i < pin_spec.CAT_N)%nat ->
0xa20a0 <= pin_spec.row_addr catA i <= 0xa20a0 + 2960 /\
pin_spec.row_addr catA i + 8 <= 0xa20a0 + 3256.
Proof. intros i Hi. unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_N, catA in *. lia. Qed.
Lemma fcr_row_next : forall i, pin_spec.row_addr catA (S i) = pin_spec.row_addr catA i + 296.
Proof. intros i. unfold pin_spec.row_addr, pin_spec.CAT_ROW. lia. Qed.
Lemma fcr_div37 : forall a, (a + 296) / 8 = a / 8 + 37.
Proof. intros a. replace (a + 296) with (a + 37 * 8) by lia. apply Z.div_add. lia. Qed.
Lemma U_fshx : forall E v, ew E 32 = Z_to_bv 64 SB -> ew E 33 = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 ->
U E fshx = SB + v / 8.
Proof.
intros E v H32 H33 Hv. unfold fshx.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, H32, H33.
rewrite !unsigned_lit_small by (unfold SB; lia). rewrite !Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound v 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (YP0m.zcanon_small v) by lia. rewrite (YP0m.zcanon_small (v / 8)) by lia. rewrite (YP0m.zcanon_small SB) by (unfold SB; lia).
rewrite YP0m.zcanon_small by (unfold SB; lia). reflexivity.
Qed.
(* the value of an atom plus an offset *)
Lemma U_SOff_v : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff n c) = (v + c) mod 2 ^ 64.
Proof. intros E n v c H Hv. rewrite U_SOff, H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma abytes_some : forall rd a l b, abytes_atR rd a l -> a <= b < a + Z.of_nat (length l) -> rd b <> None.
Proof.
intros rd a l b H Hb. replace b with (a + Z.of_nat (Z.to_nat (b - a))) by lia.
rewrite (H (Z.to_nat (b - a)) ltac:(lia)). discriminate.
Qed.
(* a token as segconf's contracts state it (sa_strz over its values) is a C string in RtDefs.v's form *)
Lemma fcr_astr_of_sa : forall rd a (s : list byte), sa_strz rd a (seg_spec.zs s) -> astr_atR rd a s.
Proof.
intros rd a s [Hz Hn]. split.
- intros k Hk. rewrite length_app in Hk. cbn [length] in Hk.
  assert (Hk' : (k < length (seg_spec.zs s ++ [0%Z]))%nat) by (unfold seg_spec.zs; rewrite length_app, length_map; cbn [length]; lia).
  rewrite (Hz k Hk'). f_equal.
  replace (seg_spec.zs s ++ [0]) with (map bv_unsigned (s ++ [Z_to_bv 8 0])) by (unfold seg_spec.zs; rewrite map_app; reflexivity).
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, length_app; cbn [length]; lia).
  apply map_nth.
- intros Hin. apply Hn. unfold seg_spec.zs. change 0 with (bv_unsigned (Z_to_bv 8 0)). apply in_map. exact Hin.
Qed.
(* two byte strings of one length are equal exactly when the reader gives the same bytes at their addresses *)
Lemma fcr_bytes_eq : forall (rd : reader) x y (l1 l2 : list byte), length l1 = length l2 ->
abytes_atR rd x l1 -> abytes_atR rd y l2 ->
((forall k, 0 <= k < Z.of_nat (length l1) -> rd (x + k) = rd (y + k)) <-> l1 = l2).
Proof.
intros rd x y l1 l2 HL H1 H2. split.
- intros H. apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0); [exact HL|].
  intros k Hk. pose proof (H (Z.of_nat k) ltac:(lia)) as E.
  rewrite (H1 k Hk), (H2 k ltac:(lia)) in E. injection E as E. apply bv_eq. exact E.
- intros <- k Hk. replace k with (Z.of_nat (Z.to_nat k)) by lia.
  rewrite (H1 (Z.to_nat k) ltac:(lia)), (H2 (Z.to_nat k) ltac:(lia)). reflexivity.
Qed.
(* the loop invariant row_of sb = row_from i sb (PPgRow.v rw_row_skip / rw_row_hit) *)
Lemma fcr_row_skip : forall i t, (i < pin_spec.CAT_N)%nat -> pin_spec.tok_bytes i <> t ->
pin_spec.row_from i t = pin_spec.row_from (S i) t.
Proof.
intros i t Hi Hne. rewrite (pin_spec.row_from_step i t Hi).
destruct (pin_spec.bytes_eqb (pin_spec.tok_bytes i) t) eqn:E; [apply pin_spec.bytes_eqb_eq in E; contradiction | reflexivity].
Qed.
Lemma fcr_row_hit : forall i t, (i < pin_spec.CAT_N)%nat -> pin_spec.tok_bytes i = t -> pin_spec.row_from i t = Some i.
Proof. intros i t Hi <-. rewrite (pin_spec.row_from_step i _ Hi), pin_spec.bytes_eqb_refl. reflexivity. Qed.
Lemma fcr_tok_len : forall i, (i < pin_spec.CAT_N)%nat ->
(0 < length (pin_spec.tok_bytes i))%nat /\ (length (pin_spec.tok_bytes i) <= 11)%nat.
Proof.
intros i Hi. unfold pin_spec.CAT_N in Hi.
do 11 (destruct i as [|i];
  [ lazymatch goal with |- context [length (pin_spec.tok_bytes ?k)] =>
      let l := eval vm_compute in (length (pin_spec.tok_bytes k)) in change (length (pin_spec.tok_bytes k)) with l end; lia
  | ]).
lia.
Qed.
(* the callee-saved registers at the return, one equation each (rec_shape_of_k.v rso_pres_ret) *)
Lemma fcr_pres_ret : forall (regs r' : bvmap 5 word),
getr r' 2 = getr regs 2 -> getr r' 3 = getr regs 3 -> getr r' 4 = getr regs 4 -> getr r' 8 = getr regs 8 ->
getr r' 9 = getr regs 9 -> getr r' 18 = getr regs 18 -> getr r' 19 = getr regs 19 -> getr r' 20 = getr regs 20 ->
getr r' 21 = getr regs 21 -> getr r' 22 = getr regs 22 -> getr r' 23 = getr regs 23 -> getr r' 24 = getr regs 24 ->
getr r' 25 = getr regs 25 -> getr r' 26 = getr regs 26 -> getr r' 27 = getr regs 27 ->
aregs_preserved regs r'.
Proof.
intros regs r' H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
repeat (destruct Hc as [-> | Hc]); try subst r;
match goal with H : getr r' ?k = getr regs ?k |- getr r' (Z_to_bv 5 ?n) = _ =>
  replace (Z_to_bv 5 n) with k by (apply bv_eq; reflexivity); exact H end.
Qed.
Lemma fcr_pres_reg : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (HP _ Hr). Qed.
(* a sub-range's shadow hull (rec_shape_of_k.v hull_sub) *)
Lemma fcr_hull_sub : forall (rd : reader) x n m, 0 < n -> n <= m -> 0 <= x ->
shadow_hull_vis rd x m -> shadow_hull_vis rd x n.
Proof.
intros rd x n m Hn Hm Hx HH s Hs. apply HH. split; [lia|].
assert (shadow_addr (x + n - 1) <= shadow_addr (x + m - 1)) by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (shadow_addr (x + n - 1) / 8 * 8 <= shadow_addr (x + m - 1) / 8 * 8) by (apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
lia.
Qed.
Lemma fcr_set_fs_id : forall S, S = set_fs (st_fs S) S.
Proof. intros S. destruct S. reflexivity. Qed.

(* a register's value at a stop, as the denotation of its symbolic value (rec_shape_of_s.v rawreg) *)
Ltac rawreg HS r H :=
lazymatch type of HS with
| st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
  pose proof (st_ok_pi_restrict_reg Hh Ex ss ms r HS) as H;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
  cbn [ms_regs restrict mkst extK] in H
| st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
  pose proof (st_ok_restrict_reg segs Hh Ex ss ms r HS) as H;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
  cbn [ms_regs restrict mkst extK] in H
end.
Ltac csav := unfold acallee_saved;
lazymatch goal with |- context [bv_unsigned ?x] => let z := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with z end; lia.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition fcr_E0 (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 SB]).
Definition fcr_E (regs1 regs : bvmap 5 word) (i : nat) (tp : Z) : env := Eimg (Ereg regs1 (fcr_extra regs i tp)).

(* the frame the prologue writes: register fcr_saved[j] at sp0 - 8 - 8 j *)
Definition fcr_frame (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error fcr_saved j = Some r -> val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Lemma fcr_frame_kept : forall H H' m m' sp0 regs,
fcr_frame (mrestrict H m) sp0 regs -> (forall a, sp0 - 64 <= a < sp0 -> aview SEGS H' m' a = aview SEGS H m a) ->
fcr_frame (mrestrict H' m') sp0 regs.
Proof.
intros H H' m m' sp0 regs HF Hk j r Hj. pose proof (HF j r Hj) as V.
assert (Hj8 : (j < 8)%nat) by (apply (proj1 (nth_error_Some fcr_saved j)); rewrite Hj; discriminate).
intros kk Hkk. rewrite <- (V kk Hkk). apply (mbyte_of_aview SEGS). apply Hk. lia.
Qed.
(* the frame from the stack region of the walk's state after the prologue *)
Lemma fcr_frame_of_region : forall E m sp0 regs lo hi wlo whi cs,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = sp0 ->
(forall j r, nth_error fcr_saved j = Some r -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
(forall r, 0 <= r < 32 -> ew E (Z.to_nat r) = getr regs (Z_to_bv 5 r)) ->
fcr_frame m sp0 regs.
Proof.
intros E m sp0 regs lo hi wlo whi cs HR Hsp HIn HE j r Hj.
assert (Hr : 0 <= r < 32) by (apply nth_error_In in Hj; cbn in Hj; intuition lia).
pose proof (field_of_region_any E m 2 sp0 cs lo hi wlo whi _ 8 _ HR Hsp (HIn j r Hj) ltac:(lia)) as V.
cbn [sv_denot] in V. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE r Hr) in V.
rewrite Z.mod_small in V by (pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as R;
  change (bv_modulus 64) with (2 ^ 64) in R; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia).
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (-8 - 8 * Z.of_nat j)) by lia. exact V.
Qed.
Lemma fcr_E_saved : forall (regs regs1 : bvmap 5 word) i tp j r, nth_error fcr_saved j = Some r ->
ew (fcr_E regs1 regs i tp) (35 + j) = getr regs (Z_to_bv 5 r).
Proof.
intros regs regs1 i tp j r Hj. assert (Hj8 : (j < 8)%nat) by (apply (proj1 (nth_error_Some fcr_saved j)); rewrite Hj; discriminate).
unfold fcr_E. rewrite Eimg_low by (unfold A_TEXT; lia). replace (35 + j)%nat with (32 + (3 + j))%nat by lia. rewrite ew_Ereg_extra.
do 8 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; reflexivity|]). lia.
Qed.
Lemma fcr_E_reg : forall (regs regs1 : bvmap 5 word) i tp n (r : bv 5), Z.of_nat n = bv_unsigned r ->
ew (fcr_E regs1 regs i tp) n = getr regs1 r.
Proof.
intros regs regs1 i tp n r Hn. unfold fcr_E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma fcr_E32 : forall (regs regs1 : bvmap 5 word) i tp, ew (fcr_E regs1 regs i tp) 32 = Z_to_bv 64 SB.
Proof. intros. unfold fcr_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 0). Qed.
Lemma fcr_E33 : forall (regs regs1 : bvmap 5 word) i tp, ew (fcr_E regs1 regs i tp) 33 = Z_to_bv 64 (pin_spec.row_addr catA i).
Proof. intros. unfold fcr_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 1). Qed.
Lemma fcr_E34 : forall (regs regs1 : bvmap 5 word) i tp, ew (fcr_E regs1 regs i tp) 34 = Z_to_bv 64 (11 - Z.of_nat i).
Proof. intros. unfold fcr_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 2). Qed.
Lemma fcr_E43 : forall (regs regs1 : bvmap 5 word) i tp, ew (fcr_E regs1 regs i tp) 43 = Z_to_bv 64 tp.
Proof. intros. unfold fcr_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 11). Qed.

(* the registers at a program point of iteration i: the frame below the entry sp, gp and tp, s0 = s3 = row i,
   s1 = n, s2 = p, s5 = row i's shadow address, s6 = the rows left, s7..s11 as at the entry *)
Definition fcr_regs_at (regs regs1 : bvmap 5 word) (i : nat) : Prop :=
getr regs1 2 = w64 (spZ regs - 64) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
getr regs1 8 = w64 (pin_spec.row_addr catA i) /\ getr regs1 9 = getr regs 11 /\ getr regs1 18 = getr regs 10 /\
getr regs1 19 = w64 (pin_spec.row_addr catA i) /\ getr regs1 21 = w64 (SB + pin_spec.row_addr catA i / 8) /\
getr regs1 22 = w64 (11 - Z.of_nat i) /\ getr regs1 23 = getr regs 23 /\ getr regs1 24 = getr regs 24 /\
getr regs1 25 = getr regs 25 /\ getr regs1 26 = getr regs 26 /\ getr regs1 27 = getr regs 27.

Lemma fcr_regs_ok : forall (regs regs1 : bvmap 5 word) i tp, (i < pin_spec.CAT_N)%nat -> fcr_regs_at regs regs1 i ->
regs_ok (fcr_E regs1 regs i tp) fcr_sregs regs1.
Proof.
intros regs regs1 i tp Hi (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof (fcr_row_bounds i Hi) as [Hr1 Hr2].
pose proof (fcr_E32 regs regs1 i tp) as E32. pose proof (fcr_E33 regs regs1 i tp) as E33. pose proof (fcr_E34 regs regs1 i tp) as E34.
set (E := fcr_E regs1 regs i tp) in *.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; apply fcr_E_reg; exact Hn).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let w := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with w end;
  first
  [ cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; symmetry; apply EE; reflexivity
  | rewrite getr_zero; reflexivity
  | cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; rewrite Z.add_0_r; first [exact R8 | exact R19]
  | cbn [sv_denot]; rewrite E34, unsigned_lit_small by (unfold pin_spec.CAT_N in Hi; lia); rewrite Z.add_0_r; exact R22
  | change (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 33 0) (SLit 3))) with fshx;
    rewrite denot_lit_U, (U_fshx E (pin_spec.row_addr catA i) E32 E33) by lia; exact R21 ]
| ]); try (destruct Hr; fail).
Qed.

Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma fcr_V77 : VAL (A_OBJ 77%nat) = catA.
Proof. rewrite (VOBJS 77%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* the seed of a loop segment at listing offset pc of iteration i *)
Lemma fcr_seed : forall pc (W1 : world SEGS) (regs regs1 : bvmap 5 word) mem1 sp0 i tp,
(i < pin_spec.CAT_N)%nat -> alloc_ceiling <= sp0 - 64 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
fcr_regs_at regs regs1 i -> spZ regs = sp0 ->
fcr_frame (mrestrict (w_H W1) mem1) sp0 regs ->
rdword (rdW W1 mem1) (pin_spec.row_addr catA i) = Some tp -> 0 <= tp < 2 ^ 64 ->
range_addressable (rdW W1 mem1) SHADOW_OFF (pin_spec.row_addr catA i) 8 ->
st_ok_pi SEGS VAL (fcr_E regs1 regs i tp) (ss_fcr pc)
(restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS FBx fcr_SH (fcr_E regs1 regs i tp) (mrestrict (w_H W1) mem1).
Proof.
intros pc W1 regs regs1 mem1 sp0 i tp Hi Hceil H47 Hal HR Hsp0 HFR Hrw Htp HZ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fcr_row_bounds i Hi) as [Hr1 Hr2].
pose proof (fcr_regs_ok regs regs1 i tp Hi HR) as HREG.
pose proof HR as (R2 & _).
rewrite restrict_mkst_fx.
pose proof (fcr_E32 regs regs1 i tp) as E32. pose proof (fcr_E33 regs regs1 i tp) as E33.
pose proof (fcr_E34 regs regs1 i tp) as E34. pose proof (fcr_E43 regs regs1 i tp) as E43.
set (E := fcr_E regs1 regs i tp) in *.
assert (E2 : bv_unsigned (ew E 2) = sp0 - 64).
{ subst E. rewrite (fcr_E_reg regs regs1 i tp 2 2%bv eq_refl), R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (B33 : base_val E (Some 33%nat) = pin_spec.row_addr catA i) by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; lia).
split.
- unfold ss_fcr, fcr_regions. apply pa_entry_st_ok_full.
  + exact HREG.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok.
    * unfold fcr_frame_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      lazymatch goal with |- Forall ?P ?l => let l2 := eval vm_compute in l in change (Forall P l2) end.
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
      let j := eval compute in (n - 35)%nat in let r := eval compute in (nth j fcr_saved 0) in
      apply (chunk_ok_val SEGS E _ (sp0 - 64) off 8 (SOff n 0) (bv_unsigned (ew E n)));
      [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | let HRr := fresh in pose proof (bv_unsigned_in_range 64 (ew E n)) as HRr; clear - HRr; change (bv_modulus 64) with (2 ^ 64) in HRr; exact HRr
      | cbn; lia
      | replace (sp0 - 64 + off) with (sp0 - 8 - 8 * Z.of_nat j) by (cbn; lia);
        let Ej := fresh "Ej" in pose proof (fcr_E_saved regs regs1 i tp j r eq_refl) as Ej; change (35 + j)%nat with n in Ej;
        fold E in Ej; rewrite Ej; exact (HFR j r eq_refl) ] end.
    * unfold fcr_row_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite B33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (pin_spec.row_addr catA i) 0 8 (SOff 43 0) tp);
      [cbn [sv_denot]; rewrite E43, Z.add_0_r, unsigned_lit_small by lia; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W1) mem1 _ _ Hrw).
  + apply pairwise_disjoint_of_extents. unfold fcr_regions, fcr_frame_region, fcr_row_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B33. cbn [base_val]. rewrite E2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [fcr_facts fcr_atom_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E32, E33, E34, !unsigned_lit_small by (unfold SB, pin_spec.CAT_N in *; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hsp16 : (sp0 - 64) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
    unfold SB, catA, pin_spec.CAT_N in *. repeat split; try lia.
- unfold sh_ok, fcr_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W1) mem1 E FBx 33 (pin_spec.row_addr catA i) 8 (pin_spec.row_addr catA i) 0 8 HZ).
  + unfold FBx. rewrite (U_atom E 32 SB E32) by (unfold SB; lia). reflexivity.
  + apply U_atom; [exact E33 | lia].
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* the entry state (rec_shape_of.v rso_entry_seed) *)
Lemma fcr_entry_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem ly S md,
AR SEGS B ly S W mem md -> astk_ok STK_fuzz_catalogue_row ly (spZ regs) ->
(forall a, spZ regs - STK_fuzz_catalogue_row <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (fcr_E0 regs) ss_fcr_entry
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_fuzz_catalogue_row)) mem (seg_rom SEGS)))
/\ sh_ok SEGS FBx [] (fcr_E0 regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem ly S md HAR Hstk Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_fuzz_catalogue_row = 8256) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
unfold kImgEnd in HcellR, HgotR.
set (E := fcr_E0 regs).
assert (E2 : ew E 2 = getr regs 2).
{ subst E. unfold fcr_E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ 2 2%bv eq_refl). }
assert (E32 : ew E 32 = Z_to_bv 64 SB).
{ subst E. unfold fcr_E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold fcr_E0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold fcr_E0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_fcr_entry. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold fcr_E0. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r, SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [fcr_entry_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r. unfold SB.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- unfold sh_ok. apply Forall_nil.
Qed.

(* ------------------------------------------------------------------------------------------------
   The statements of the walk's program points *)
(* the contract's premises (fuzz_catalogue_row_c.v:77-87) at image B's numbers *)
Definition fcr_cx ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (p n : Z) (sb : list byte) : Prop :=
afn_pre SEGS B STK_fuzz_catalogue_row ly S W regs mem md ch /\ arodata_okP SEGS RLO_A RHI_A B (rdW W mem) /\
getr regs 10 = w64 p /\ 0 <= p < 2 ^ 64 /\ getr regs 11 = w64 n /\ 0 <= n < 2 ^ 64 /\ n = Z.of_nat (length sb) /\
sa_bytes (rdW W mem) p sb /\ sa_addr (rdW W mem) p n /\ sa_loc SEGS B ly S p n /\
sa_cat SEGS B (rdW W mem) catA.
(* the contract's post (fuzz_catalogue_row_c.v:88-93) *)
Definition fcr_Q ly S (W : world SEGS) (regs : bvmap 5 word) mem (sb : list byte) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
getr regs' 10 = w64 (seg_spec.cat_ptr catA (SegModel.cat_row (seg_spec.zs sb))) /\
sa_kept SEGS W mem W' mem' regs STK_fuzz_catalogue_row (fun _ => False) /\
sa_noalloc B ly S ly' S'.
Definition fcr_post ly S (W : world SEGS) (regs : bvmap 5 word) mem md (sb : list byte) : world SEGS -> config -> Prop :=
apost_base SEGS B STK_fuzz_catalogue_row [] regs ly S W mem md EV_fuzz_catalogue_row (fcr_Q ly S W regs mem sb).
(* between the entry and the current pc: the journal (no event, no block, footprint empty), every byte outside
   this call's stack window unchanged, and the eight saved registers in the frame *)
Definition fcr_mid ly S (W : world SEGS) (regs : bvmap 5 word) mem md memc mdc : Prop :=
ajournal SEGS B STK_fuzz_catalogue_row (spZ regs) [] ly S W mem md [] ly S W memc mdc 0 /\
kept_out (rdW W mem) (rdW W memc) (spZ regs - STK_fuzz_catalogue_row) (spZ regs) /\
fcr_frame (mrestrict (w_H W) memc) (spZ regs) regs.
Definition fcr_at regs1 memc mdc (pc : Z) ly S (W : world SEGS) (regs : bvmap 5 word) mem md sb : Prop :=
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)) mdc) (fcr_post ly S W regs mem md sb).
(* 0x8a828, the loop head of iteration i: rows 0 .. i - 1 hold no token equal to sb *)
Definition HEAD_stmt (i : nat) : Prop :=
forall ly S W regs mem md ch p n sb regs1 memc mdc,
fcr_cx ly S W regs mem md ch p n sb -> fcr_mid ly S W regs mem md memc mdc -> fcr_regs_at regs regs1 i ->
pin_spec.row_of sb = pin_spec.row_from i sb ->
fcr_at regs1 memc mdc FCR_HEAD ly S W regs mem md sb.
(* 0x8a83c, strlen's return: a0 = the length of row i's token, s4 = its pointer tp, the image's word at row i *)
Definition R1_stmt (i : nat) : Prop :=
forall ly S W regs mem md ch p n sb regs1 memc mdc tp,
fcr_cx ly S W regs mem md ch p n sb -> fcr_mid ly S W regs mem md memc mdc -> fcr_regs_at regs regs1 i ->
rdword (rdW W mem) (pin_spec.row_addr catA i) = Some tp -> getr regs1 20 = w64 tp ->
getr regs1 10 = w64 (Z.of_nat (length (pin_spec.tok_bytes i))) ->
pin_spec.row_of sb = pin_spec.row_from i sb ->
fcr_at regs1 memc mdc FCR_R1 ly S W regs mem md sb.
(* 0x8a850, bcmp's return: a0 = 0 exactly when row i's token is sb *)
Definition R2_stmt (i : nat) : Prop :=
forall ly S W regs mem md ch p n sb regs1 memc mdc tp,
fcr_cx ly S W regs mem md ch p n sb -> fcr_mid ly S W regs mem md memc mdc -> fcr_regs_at regs regs1 i ->
rdword (rdW W mem) (pin_spec.row_addr catA i) = Some tp -> getr regs1 20 = w64 tp ->
(getr regs1 10 = w64 0 <-> pin_spec.tok_bytes i = sb) ->
pin_spec.row_of sb = pin_spec.row_from i sb ->
fcr_at regs1 memc mdc FCR_R2 ly S W regs mem md sb.
(* 0x8a854, the next-row block after row i, which holds no token equal to sb *)
Definition NEXT_stmt (i : nat) : Prop :=
forall ly S W regs mem md ch p n sb regs1 memc mdc,
fcr_cx ly S W regs mem md ch p n sb -> fcr_mid ly S W regs mem md memc mdc -> fcr_regs_at regs regs1 i ->
pin_spec.row_of sb = pin_spec.row_from (Datatypes.S i) sb ->
fcr_at regs1 memc mdc FCR_NEXT ly S W regs mem md sb.

(* ------------------------------------------------------------------------------------------------
   Facts the segments share *)
(* where s lies: below the allocator's ceiling (a live block, a side-stack frame or the image) *)
Lemma fcr_p_low : forall ly S W mem md p n, AR SEGS B ly S W mem md -> sa_loc SEGS B ly S p n -> 0 < n -> 0 <= p ->
p + n <= alloc_ceiling.
Proof.
intros ly S W mem md p n HAR HL Hn Hp. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HL as [(b & m & Hin & H1 & H2) | [(cid & pos & Hin & Hc & H1 & H2) | HI]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & Hk).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hreq]. lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (F1 & F2 & _). lia.
- destruct (HI (p + n - 1) ltac:(lia)) as (Himg & _ & _).
  pose proof (pa_segs_low _ Himg). lia.
Qed.
(* a token of the table: an image object, inside [0x10000, kImgEnd = 0x602000) (PAImg's pa_img_range) *)
Lemma fcr_tok_low : forall tp k, sa_img SEGS B tp (k + 1) -> 0 <= k -> 0x10000 <= tp /\ tp + k + 1 <= 0x602000.
Proof.
intros tp k HI Hk. destruct (HI tp ltac:(lia)) as (I0 & _). destruct (HI (tp + k) ltac:(lia)) as (I1 & _).
pose proof (pa_img_range _ I0). pose proof (pa_img_range _ I1). unfold kImgEnd in *. lia.
Qed.
(* the read-only words the string wrapper reads, from the entry's arodata_okP *)
Lemma fcr_rom_view : forall (W : world SEGS) mem memc lo hi,
arodata_okP SEGS RLO_A RHI_A B (rdW W mem) -> kept_out (rdW W mem) (rdW W memc) lo hi -> 0x602000 <= lo ->
rt_rom_view SEGS B W memc.
Proof.
intros W mem memc lo hi HROD HK Hlo a (sg & Hsg & Hw & Hr) Ho He.
pose proof (pa_img_range a (ex_intro _ sg (conj Hsg Hr))) as Hia. unfold kImgEnd in Hia.
rewrite (HK a) by lia. exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He).
Qed.
(* the frame and the registers after a wrapper call (rec_shape_of_k.v rso_mid_call / rso_regs_at_pres) *)
Lemma fcr_mid_call : forall ly S (W : world SEGS) regs mem md memc mdc mm mem2 md2 lo,
fcr_mid ly S W regs mem md memc mdc ->
(forall a, 0 <= a < 2 ^ 64 -> rdW W mm a = rdW W memc a) ->
ajournal SEGS B STK_fuzz_catalogue_row (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < spZ regs - 64) -> rdW W mem2 a = rdW W mm a) ->
spZ regs - STK_fuzz_catalogue_row <= lo ->
fcr_mid ly S W regs mem md mem2 md2.
Proof.
intros ly S W regs mem md memc mdc mm mem2 md2 lo (HJ & HK & HFR) U1 HJ2 HK2 Hlo.
split; [exact HJ2|]. split.
- intros a Ha Hna. rewrite (HK2 a Ha) by lia. rewrite (U1 a Ha). exact (HK a Ha Hna).
- apply (fcr_frame_kept (w_H W) (w_H W) memc mem2 (spZ regs) regs HFR). intros a Ha.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as R. unfold spZ in *. change (bv_modulus 64) with (2 ^ 64) in R.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & _) & _).
  pose proof asan_consts as (C1 & _). unfold STK_fuzz_catalogue_row, ESTACK in *.
  rewrite (HK2 a) by lia. apply U1. lia.
Qed.
Lemma fcr_regs_at_pres : forall regs regs1 rgT regs2 i,
fcr_regs_at regs regs1 i -> aregs_preserved rgT regs2 ->
getr rgT 2 = getr regs1 2 -> getr rgT 3 = getr regs1 3 -> getr rgT 4 = getr regs1 4 ->
getr rgT 8 = getr regs1 8 -> getr rgT 9 = getr regs1 9 -> getr rgT 18 = getr regs1 18 ->
getr rgT 19 = getr regs1 19 -> getr rgT 21 = getr regs1 21 -> getr rgT 22 = getr regs1 22 ->
getr rgT 23 = getr regs1 23 -> getr rgT 24 = getr regs1 24 -> getr rgT 25 = getr regs1 25 ->
getr rgT 26 = getr regs1 26 -> getr rgT 27 = getr regs1 27 ->
fcr_regs_at regs regs2 i.
Proof.
intros regs regs1 rgT regs2 i (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27) HP
S2 S3 S4 S8 S9 S18 S19 S21 S22 S23 S24 S25 S26 S27.
assert (P : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr rgT r) by (intros r Hr; exact (fcr_pres_reg _ _ r HP Hr)).
repeat split; (rewrite P;
  [ first [ rewrite S2; exact R2 | rewrite S3; exact R3 | rewrite S4; exact R4 | rewrite S8; exact R8 | rewrite S9; exact R9
          | rewrite S18; exact R18 | rewrite S19; exact R19 | rewrite S21; exact R21 | rewrite S22; exact R22
          | rewrite S23; exact R23 | rewrite S24; exact R24 | rewrite S25; exact R25 | rewrite S26; exact R26
          | rewrite S27; exact R27 ]
  | csav ]).
Qed.
End e.
End f.
End d.
