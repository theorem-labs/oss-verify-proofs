(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the trim loop of the inlined words_of in LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x867a4 .. 0x867e4, back to its head or on to 0x8680c), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (a seed, the symbolic engine's runs and their branches) and A/ACfj.v (rt_G_allX: a loop by induction on its counter), over the plain proof's lib/Prog/SlotWordsRun.v sw_trim. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_s43.v, with its module paths and module names changed; 484 of its 560 lines of code are new or changed and 548 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): piece 2 of segment S14 of the walk
   of the test harness's entry function LLVMFuzzerTestOneInput (0x84d34), file group _s22b: from the return of
   the strrchr wrapper (S22_VR, 0x85930) to the continue join (S22_JOIN, 0x859c4) or to the head of the digit loop
   (S22_VD, 0x85974), the statement s22_p2_stmt of LLVMFuzzerTestOneInput_s22k.v.

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep; checker (fresh, read-only): CONFIRM; none: written new)

   THE FORM: plugin-hostd/fuzz_command's lib/A/Prog/LLVMFuzzerTestOneInput_s43.v (origin/ossv/recipes 501c0d516c69):
   a seed with the one byte the code reads (a region at a0), the symbolic engine's runs and their branches, the
   context carried by a kept-memory lemma. The code (dis:769-785, 804-805, 930-932 of the neutral excerpt):
   - 0x85930 beqz a0: strrchr found no '.' -> 0x859bc ld a5,176(s1); 0x859c0 ld a6,168(s1); the join 0x859c4;
   - 0x85934 .. 0x85940: a5 := the shadow base (176(s1)), a7 := -10, t0 := 10, t1 := 128(s1) = 4094;
   - 0x85944 beq a0,s3: the '.' is the name's first byte -> 0x859c0 ld a6,168(s1); the join;
   - 0x85948 .. 0x85958: a1 := a0 + 1 and its 1-byte check (slow block 0x85bb4): the byte lies in the block m;
   - 0x8595c lbu a3,0(a1); 0x85960 ld a6,168(s1); 0x85964 beqz a3: the byte after the '.' is the NUL -> the join;
   - 0x85968 .. 0x85970: s2 := 0, a2 := a1 := a0 + 2: the digit loop's head at t = 0, v = 0.
   Every region of every run is read-only, so the memory after each run reads as before it (p2_frame_ro), and the
   context s22_inv is carried over by p2_inv_kept. The Section header is the file group's canonical one without the two
   call rows (this piece has no call); of its hypotheses the proof uses only IMGS and BSYM (lt_img at the later
   reader), so after the Section closes s22_p2 : forall B MT, s10_img -> AF0m.SegBSyms B -> s22_p2_stmt B MT (fx rc
   SK PI implicit). *)
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

(* ======================= the seeds at 0x85930 (S22_VR) ======================= *)
(* the s1 slots the piece reads: 128(s1) = 4094, 168(s1) = m (atom 33), 176(s1) = the shadow base (atom 32) *)
Definition p2_s1r : YP09.region := YP09.mkRegion (Some 9%nat) 128 184 128 128
  [YP09.mkChunk 128 (CVal 8 (SLit 4094)); YP09.mkChunk 168 (CVal 8 (SOff 33 0)); YP09.mkChunk 176 (CVal 8 (SOff 32 0))].
(* the byte after the '.': a0 + 1, the atom 34 *)
Definition p2_nmr : YP09.region := YP09.mkRegion (Some 10%nat) 1 2 1 1 [YP09.mkChunk 1 (CVal 1 (SOff 34 0))].
Definition p2_factsA : facts := mkFacts [(32%nat, mkAF SB SB 0)] [] [].
Definition p2_factsB : facts :=
  mkFacts [(10%nat, mkAF 4096 0x7fffff800000 0); (32%nat, mkAF SB SB 0); (34%nat, mkAF 0 255 0)] [] [].
(* strrchr found nothing: a0 = 0 *)
Definition ss_p2A : sstate := mkSS S22_VR (sr_set sr_atoms (10%bv : bv 5) (SLit 0)) [p2_s1r] None p2_factsA.
(* strrchr found the '.': a0 = &m->seg[i].name[j] *)
Definition ss_p2B : sstate := mkSS S22_VR sr_atoms [p2_s1r; p2_nmr] None p2_factsB.
Definition p2span : Z * Z := (SB, SB + 2 ^ 44 - 1).

(* the registers every exit keeps *)
Definition p2_shape (sr : list sv) : Prop :=
  sr_get sr (2%bv : bv 5) = SOff 2 0 /\ sr_get sr (3%bv : bv 5) = SOff 3 0 /\ sr_get sr (4%bv : bv 5) = SOff 4 0 /\
  sr_get sr (8%bv : bv 5) = SOff 8 0 /\ sr_get sr (9%bv : bv 5) = SOff 9 0 /\ sr_get sr (19%bv : bv 5) = SOff 19 0 /\
  sr_get sr (20%bv : bv 5) = SOff 20 0 /\ sr_get sr (21%bv : bv 5) = SOff 21 0 /\
  sr_get sr (22%bv : bv 5) = SOff 22 0 /\ sr_get sr (23%bv : bv 5) = SOff 23 0 /\
  sr_get sr (24%bv : bv 5) = SOff 24 0 /\ sr_get sr (25%bv : bv 5) = SOff 25 0 /\
  sr_get sr (26%bv : bv 5) = SOff 26 0 /\ sr_get sr (27%bv : bv 5) = SOff 27 0.
Definition p2_kept (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
  getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 19 = getr regs 19 /\
  getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\
  getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\
  getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.

(* ======================= model facts ======================= *)
Lemma p2_hd0_nth : forall (l : list Z), SegModel.hd0 l = nth 0 l 0.
Proof. intros [|x l]; reflexivity. Qed.

(* the byte after the '.' of the C string name ++ [0] *)
Lemma p2_byte : forall (name : list Z) j, (j < length name)%nat ->
  nth (S j) (name ++ [0]) 0 = SegModel.hd0 (skipn (S j) name).
Proof.
intros name j Hj. rewrite p2_hd0_nth, nth_skipn, Nat.add_0_r.
destruct (Nat.lt_ge_cases (S j) (length name)) as [Hlt|Hge].
- apply app_nth1. exact Hlt.
- rewrite app_nth2 by exact Hge.
  assert (Ho : nth (S j) name 0 = 0) by (apply nth_overflow; exact Hge). rewrite Ho.
  replace (S j - length name)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma p2_len_pos : forall (l : list Z), SegModel.hd0 l <> 0 -> (0 < length l)%nat.
Proof. intros [|x l] H; cbn in *; [exfalso; apply H; reflexivity | lia]. Qed.

(* the three refusals of m_split the join paths meet (SegModel.v:503-513) *)
Lemma p2_split_none_nf : forall name, SegModel.strrchr name 46 = None -> SegModel.m_split name = None.
Proof. intros name Hs. unfold SegModel.m_split. rewrite Hs. reflexivity. Qed.
Lemma p2_split_none_0 : forall name, SegModel.strrchr name 46 = Some 0%nat -> SegModel.m_split name = None.
Proof. intros name Hs. unfold SegModel.m_split. rewrite Hs. reflexivity. Qed.
Lemma p2_split_none_nul : forall name j, SegModel.strrchr name 46 = Some j ->
  SegModel.hd0 (skipn (S j) name) = 0 -> SegModel.m_split name = None.
Proof.
intros name j Hs H0. unfold SegModel.m_split. rewrite Hs. cbv beta iota. rewrite H0, Z.eqb_refl, orb_true_r.
reflexivity.
Qed.

Lemma p2_EV_ewset : forall E k w (regs : bvmap 5 word), (32 <= k)%nat ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) ->
  forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ewset E k w) n = getr regs r.
Proof.
intros E k w regs Hk H n r Hr. pose proof (bv_unsigned_in_range 5 r) as R. change (bv_modulus 5) with 32 in R.
rewrite ew_ewset_other by lia. exact (H n r Hr).
Qed.
Ltac p2_EV EV := repeat (apply p2_EV_ewset; [lia|]); exact EV.
Ltac p2_ew0 := repeat (rewrite ew_ewset_other by lia).

Lemma p2_den_atom : forall E n v off, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n off) = Z_to_bv 64 (v + off).
Proof.
intros E n v off Hn. cbn [sv_denot]. rewrite Hn. apply Z_to_bv64_eq_mod. rewrite Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Ltac p2_awr :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
Ltac p2_mdv name :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (name := d) in *; clearbody name end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ======================= the environment of the seeds ======================= *)
Definition p2_E (regs : bvmap 5 word) (vals : list Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) vals)).
Lemma p2_E_reg : forall regs vals n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (p2_E regs vals) n = getr regs r.
Proof.
intros regs vals n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold p2_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma p2_E_val : forall regs vals j, (j < 100)%nat -> ew (p2_E regs vals) (32 + j) = Z_to_bv 64 (nth j vals 0).
Proof.
intros regs vals j Hj. unfold p2_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
apply map_nth.
Qed.

(* ======================= chunks and regions ======================= *)
Lemma p2_chunk8 : forall E (H : word -> bool) mem base off e v,
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict H mem) base (YP09.mkChunk off (CVal 8 e)).
Proof.
intros E H mem base off e v He Hv Hr.
apply (chunk_ok_val SEGS E _ base off 8 e v He); [cbn; lia | cbn; lia |].
exact (val_mem_of_rdword SEGS H mem _ _ Hr).
Qed.

Lemma p2_chunk1 : forall E (H : word -> bool) mem base off n v,
  ew E n = Z_to_bv 64 v -> aview SEGS H mem (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict H mem) base (YP09.mkChunk off (CVal 1 (SOff n 0))).
Proof.
intros E H mem base off n v En Hv i Hi. cbn in Hi. assert (Hi0 : i = 0) by lia. subst i.
cbn [YP09.c_val YP09.c_off]. rewrite !Z.add_0_r.
destruct (aview_byte SEGS H mem _ _ Hv) as (b & Hm & Hbv & Hr).
exists b. split; [|exact Hm].
cbn [YP09.cbyte]. rewrite (p2_den_atom E n v 0 En), Z.add_0_r. f_equal.
unfold byte_of_word. rewrite unsigned_lit_small by lia. rewrite Z.mul_0_r, Z.shiftr_0_r. subst v.
apply Z_to_bv_bv_unsigned.
Qed.

Lemma p2_s1_ok : forall E (W : world SEGS) mem s1 m,
  ew E 9 = Z_to_bv 64 s1 -> ew E 32 = Z_to_bv 64 SB -> ew E 33 = Z_to_bv 64 m ->
  0 <= s1 -> s1 + 184 <= 2 ^ 64 -> 0 <= m < 2 ^ 64 ->
  rdword (rdW W mem) (s1 + 128) = Some 4094 -> rdword (rdW W mem) (s1 + 168) = Some m ->
  rdword (rdW W mem) (s1 + 176) = Some SHADOW_OFF ->
  YP09.region_ok SEGS E (mrestrict (w_H W) mem) p2_s1r.
Proof.
intros E W mem s1 m E9 E32 E33 H0 H1 Hm R128 R168 R176.
unfold YP09.region_ok, p2_s1r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E9, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- apply (p2_chunk8 E (w_H W) mem s1 128 (SLit 4094) 4094); [reflexivity | lia | exact R128].
- apply (p2_chunk8 E (w_H W) mem s1 168 (SOff 33 0) m); [|lia|exact R168].
  rewrite (p2_den_atom E 33 m 0 E33), Z.add_0_r. reflexivity.
- apply (p2_chunk8 E (w_H W) mem s1 176 (SOff 32 0) SB); [|unfold SB; lia|exact R176].
  rewrite (p2_den_atom E 32 SB 0 E32), Z.add_0_r. reflexivity.
Qed.

Lemma p2_nm_ok : forall E (W : world SEGS) mem r b,
  ew E 10 = Z_to_bv 64 r -> ew E 34 = Z_to_bv 64 b -> 0 <= r -> r + 2 <= 2 ^ 64 ->
  rdW W mem (r + 1) = Some b -> YP09.region_ok SEGS E (mrestrict (w_H W) mem) p2_nmr.
Proof.
intros E W mem r b E10 E34 H0 H1 Hb.
unfold YP09.region_ok, p2_nmr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E10, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. exact (p2_chunk1 E (w_H W) mem r 1 34 b E34 Hb).
Qed.

Lemma p2_seedA : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 m,
  getr regs 9 = w64 s1 -> getr regs 10 = w64 0 -> 0 <= s1 -> s1 + 184 <= 2 ^ 64 -> 0 <= m < 2 ^ 64 ->
  rdword (rdW W mem) (s1 + 128) = Some 4094 -> rdword (rdW W mem) (s1 + 168) = Some m ->
  rdword (rdW W mem) (s1 + 176) = Some SHADOW_OFF ->
  st_ok_pi SEGS VAL (p2_E regs [SB; m; 0]) ss_p2A
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S22_VR)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 m R9 R10 H0 H1 Hm S128 S168 S176.
pose proof (p2_E_reg regs [SB; m; 0]) as EV.
assert (E9 : ew (p2_E regs [SB; m; 0]) 9 = Z_to_bv 64 s1) by (rewrite (EV 9%nat 9%bv eq_refl); exact R9).
assert (E32 : ew (p2_E regs [SB; m; 0]) 32 = Z_to_bv 64 SB) by exact (p2_E_val regs [SB; m; 0] 0 ltac:(lia)).
assert (E33 : ew (p2_E regs [SB; m; 0]) 33 = Z_to_bv 64 m) by exact (p2_E_val regs [SB; m; 0] 1 ltac:(lia)).
unfold ss_p2A. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_rereg; [unfold p2_E; apply regs_ok_Eimg_Ereg | reflexivity | rewrite R10; reflexivity].
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. exact (p2_s1_ok _ W mem s1 m E9 E32 E33 H0 H1 Hm S128 S168 S176).
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. split; exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok p2_factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E32, unsigned_lit_small by (unfold SB; lia). rewrite Z.pow_0_r, Z.mod_1_r. unfold SB. repeat split; lia.
Qed.

Lemma p2_seedB : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 m r b,
  getr regs 9 = w64 s1 -> getr regs 10 = w64 r -> 0 <= s1 -> s1 + 184 <= 2 ^ 64 -> 0 <= m < 2 ^ 64 ->
  4096 <= r <= 0x7fffff800000 -> r + 2 <= s1 + 128 -> 0 <= b < 256 ->
  rdword (rdW W mem) (s1 + 128) = Some 4094 -> rdword (rdW W mem) (s1 + 168) = Some m ->
  rdword (rdW W mem) (s1 + 176) = Some SHADOW_OFF -> rdW W mem (r + 1) = Some b ->
  st_ok_pi SEGS VAL (p2_E regs [SB; m; b]) ss_p2B
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S22_VR)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 m r b R9 R10 H0 H1 Hm Hr Hrs Hb S128 S168 S176 Hrb.
pose proof (p2_E_reg regs [SB; m; b]) as EV.
assert (E9 : ew (p2_E regs [SB; m; b]) 9 = Z_to_bv 64 s1) by (rewrite (EV 9%nat 9%bv eq_refl); exact R9).
assert (E10 : ew (p2_E regs [SB; m; b]) 10 = Z_to_bv 64 r) by (rewrite (EV 10%nat 10%bv eq_refl); exact R10).
assert (E32 : ew (p2_E regs [SB; m; b]) 32 = Z_to_bv 64 SB) by exact (p2_E_val regs [SB; m; b] 0 ltac:(lia)).
assert (E33 : ew (p2_E regs [SB; m; b]) 33 = Z_to_bv 64 m) by exact (p2_E_val regs [SB; m; b] 1 ltac:(lia)).
assert (E34 : ew (p2_E regs [SB; m; b]) 34 = Z_to_bv 64 b) by exact (p2_E_val regs [SB; m; b] 2 ltac:(lia)).
unfold ss_p2B. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold p2_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + exact (p2_s1_ok _ W mem s1 m E9 E32 E33 H0 H1 Hm S128 S168 S176).
  + exact (p2_nm_ok _ W mem r b E10 E34 ltac:(lia) ltac:(lia) Hrb).
- apply pairwise_disjoint_of_extents. unfold p2_s1r, p2_nmr, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint].
  rewrite E9, E10, !unsigned_lit_small by lia. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok p2_factsB]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E10, E32, E34, !unsigned_lit_small by (unfold SB; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB. repeat split; lia.
Qed.

(* ======================= the state after a run ======================= *)
(* a run whose regions are all read-only leaves every byte as it was *)
Lemma p2_frame_ro : forall E rs (H : word -> bool) (m0 m m' : word -> option byte),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a, aview SEGS H m a = aview SEGS H m0 a) -> forall a, aview SEGS H m' a = aview SEGS H m0 a.
Proof.
intros E rs H m0 m m' Hro Hf K a. rewrite <- (K a). unfold aview, mbyte. rewrite (Hf (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & Hr). rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.
Ltac p2_mem KK :=
  lazymatch goal with HFr : frame_of ?E ?rs (mrestrict ?h ?m1) (mrestrict _ ?m2) |- _ =>
    let KK2 := fresh "KK" in
    pose proof (p2_frame_ro E rs h _ m1 m2 ltac:(vm_compute; reflexivity) HFr KK) as KK2;
    clear KK HFr; rename KK2 into KK
  end;
  lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
  lazymatch goal with HG : mem_grows _ _ |- _ => clear HG end.

Lemma p2_reg_keep : forall E ss (ms : machine_state) (H : word -> bool) (regs : bvmap 5 word) n (r : bv 5),
  st_ok_pi SEGS VAL E ss (restrict H ms) -> ew E n = getr regs r -> sr_get (ss_regs ss) r = SOff n 0 ->
  getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms H regs n r HS Hn Hs. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hs.
cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma p2_reg_off : forall E ss (ms : machine_state) (H : word -> bool) n c v (r : bv 5),
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n c -> ew E n = Z_to_bv 64 v ->
  getr (ms_regs ms) r = Z_to_bv 64 (v + c).
Proof.
intros E ss ms H n c v r HS Hs Hn. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hs.
exact (p2_den_atom E n v c Hn).
Qed.
Lemma p2_reg_lit : forall E ss (ms : machine_state) (H : word -> bool) z (r : bv 5),
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> getr (ms_regs ms) r = Z_to_bv 64 z.
Proof. intros E ss ms H z r HS Hs. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hs. reflexivity. Qed.
Lemma p2_keep_of : forall E ss (ms : machine_state) (H : word -> bool) (regs : bvmap 5 word),
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) ->
  p2_shape (ss_regs ss) -> p2_kept regs (ms_regs ms).
Proof.
intros E ss ms H regs HS EV (S2 & S3 & S4 & S8 & S9 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27).
unfold p2_kept.
split; [exact (p2_reg_keep E ss ms H regs 2 2%bv HS (EV 2%nat 2%bv eq_refl) S2)|].
split; [exact (p2_reg_keep E ss ms H regs 3 3%bv HS (EV 3%nat 3%bv eq_refl) S3)|].
split; [exact (p2_reg_keep E ss ms H regs 4 4%bv HS (EV 4%nat 4%bv eq_refl) S4)|].
split; [exact (p2_reg_keep E ss ms H regs 8 8%bv HS (EV 8%nat 8%bv eq_refl) S8)|].
split; [exact (p2_reg_keep E ss ms H regs 9 9%bv HS (EV 9%nat 9%bv eq_refl) S9)|].
split; [exact (p2_reg_keep E ss ms H regs 19 19%bv HS (EV 19%nat 19%bv eq_refl) S19)|].
split; [exact (p2_reg_keep E ss ms H regs 20 20%bv HS (EV 20%nat 20%bv eq_refl) S20)|].
split; [exact (p2_reg_keep E ss ms H regs 21 21%bv HS (EV 21%nat 21%bv eq_refl) S21)|].
split; [exact (p2_reg_keep E ss ms H regs 22 22%bv HS (EV 22%nat 22%bv eq_refl) S22)|].
split; [exact (p2_reg_keep E ss ms H regs 23 23%bv HS (EV 23%nat 23%bv eq_refl) S23)|].
split; [exact (p2_reg_keep E ss ms H regs 24 24%bv HS (EV 24%nat 24%bv eq_refl) S24)|].
split; [exact (p2_reg_keep E ss ms H regs 25 25%bv HS (EV 25%nat 25%bv eq_refl) S25)|].
split; [exact (p2_reg_keep E ss ms H regs 26 26%bv HS (EV 26%nat 26%bv eq_refl) S26)|].
exact (p2_reg_keep E ss ms H regs 27 27%bv HS (EV 27%nat 27%bv eq_refl) S27).
Qed.

(* ======================= the context over a reader that reads as before ======================= *)
Lemma p2_rdword : forall (rd rd' : reader), (forall a, rd' a = rd a) -> forall a, rdword rd' a = rdword rd a.
Proof. intros rd rd' RE a. apply rdword_ext. intros k _. apply RE. Qed.
Lemma p2_bytes : forall (rd rd' : reader) a bs, (forall x, rd' x = rd x) -> sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs RE H i Hi. rewrite RE. exact (H i Hi). Qed.
Lemma p2_zs : forall (rd rd' : reader) a l, (forall x, rd' x = rd x) -> sa_zs rd a l -> sa_zs rd' a l.
Proof. intros rd rd' a l RE H i Hi. rewrite RE. exact (H i Hi). Qed.
Lemma p2_val : forall (rd rd' : reader) a n v, (forall x, rd' x = rd x) -> sa_val rd a n v -> sa_val rd' a n v.
Proof. intros rd rd' a n v RE H i Hi. rewrite RE. exact (H i Hi). Qed.
Lemma p2_addr : forall (rd rd' : reader) q n, (forall x, rd' x = rd x) -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros rd rd' q n RE (H1 & H2 & H3 & H4 & H5).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split.
- intros x Hx. destruct (H4 x Hx) as (s & Hs & Hok). exists s. rewrite RE. split; [exact Hs | exact Hok].
- intros Hn s Hs. rewrite RE. exact (H5 Hn s Hs).
Qed.

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

Lemma p2_hblk : forall ly S (rd rd' : reader) a n, (forall x, rd' x = rd x) ->
  lt_hblk B ly S rd a n -> lt_hblk B ly S rd' a n.
Proof.
intros ly S rd rd' a n RE (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
exact (p2_addr rd rd' a n RE H4).
Qed.

(* s22_inv at a later state whose memory reads as before, whose journal is the run's and whose frame registers
   are kept *)
Lemma p2_inv_kept : forall cx i c m tab mt o L ly S (W : world SEGS) regs mem md k acc regs' mem' md',
  s22_inv B MT cx i c m tab mt o L ly S W regs mem md k acc ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, rdW W mem' a = rdW W mem a) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  s22_inv B MT cx i c m tab mt o L ly S W regs' mem' md' k acc.
Proof.
intros cx i c m tab mt o L ly S W regs mem md k acc regs' mem' md' HI HJ' RE K2 K3 K4 K8 K9.
destruct HI as (Hi & Hpos & (HF & HIMG & HBL & HBUD) & Hc & Hm & Htab & Hmt & HSL & HCM & HTB).
destruct HF as (_ & G2 & G3 & G4 & G8 & G9 & HSV & W0 & W8 & W16 & WFL & W176 & HZS).
unfold s22_inv, lt_core, lt_frame.
split; [exact Hi|]. split; [exact Hpos|].
split; [split; [|split; [|split; [exact HBL | exact HBUD]]]|].
{ split; [exact HJ'|].
  split; [exact (eq_trans K2 G2)|]. split; [exact (eq_trans K3 G3)|]. split; [exact (eq_trans K4 G4)|].
  split; [exact (eq_trans K8 G8)|]. split; [exact (eq_trans K9 G9)|].
  split; [intros i0 r0 Hn; rewrite (p2_rdword _ _ RE); exact (HSV i0 r0 Hn)|].
  rewrite !(p2_rdword _ _ RE).
  split; [exact W0|]. split; [exact W8|]. split; [exact W16|]. split; [exact WFL|]. split; [exact W176|].
  exact (p2_zs _ _ _ _ RE HZS). }
{ exact (s10_lt_img_kept B IMGS BSYM cx W mem' (rdW W mem) (proj1 HJ') (fun a _ _ _ => RE a) HIMG). }
split; [exact (p2_hblk _ _ _ _ _ _ RE Hc)|].
split; [exact (p2_hblk _ _ _ _ _ _ RE Hm)|].
split; [exact (p2_hblk _ _ _ _ _ _ RE Htab)|].
split; [exact (p2_hblk _ _ _ _ _ _ RE Hmt)|].
split; [intros o0 v0 Hin; rewrite (p2_rdword _ _ RE); exact (HSL o0 v0 Hin)|].
split.
{ destruct HCM as [(bs1 & Hb1 & He1) (bs2 & Hb2 & He2)].
  split; [exists bs1; split; [exact (p2_bytes _ _ _ _ RE Hb1) | exact He1]
         |exists bs2; split; [exact (p2_bytes _ _ _ _ RE Hb2) | exact He2]]. }
destruct HTB as (T1 & (bs3 & Hb3 & He3) & Hg & Hv & (bs4 & Hb4 & He4) & T2).
split; [exact T1|]. split; [exists bs3; split; [exact (p2_bytes _ _ _ _ RE Hb3) | exact He3]|].
split; [exact (p2_bytes _ _ _ _ RE Hg)|]. split; [exact (p2_val _ _ _ _ _ RE Hv)|].
split; [exists bs4; split; [exact (p2_bytes _ _ _ _ RE Hb4) | exact He4] | exact T2].
Qed.

(* the continue join, reached with a name m_split refuses: turn i adds nothing *)
Lemma p2_join : forall i cx ly S (W : world SEGS) regs mem md k acc c m tab mt regs' mem' md',
  S22_JOIN_stmt B MT i -> lt_base B MT cx -> sa_frm0 ->
  s22_inv B MT cx i c m tab mt LFO_NV (s22_L cx i c m mt) ly S W regs mem md k acc ->
  SegModel.m_split (SegModel.ms_name (x_seg cx i)) = None ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, rdW W mem' a = rdW W mem a) -> p2_kept regs regs' ->
  getr regs' 15 = w64 SHADOW_OFF -> getr regs' 16 = w64 m ->
  getr regs 20 = w64 4 -> getr regs 21 = w64 (x_sh cx) -> getr regs 24 = w64 tab -> s22_rk m i regs ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + S22_JOIN)) mem' (seg_rom SEGS)) md') (lt_post B MT cx).
Proof.
intros i cx ly S W regs mem md k acc c m tab mt regs' mem' md' HJS HB HFR HI Hsp HJ' RE HK R15 R16 R20 R21 R24 HRK.
pose proof HI as (Hi & Hpos & _).
destruct HK as (K2 & K3 & K4 & K8 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
destruct HRK as (Q22 & Q23 & Q25 & Q26 & Q27).
exact (HJS cx ly S W regs' mem' md' k acc c m tab mt HB HFR
  (s22_decl_step_skip (SegModel.mc_seg (x_mcF cx)) i (x_tab0 cx) (x_cap cx) Hi Hpos (or_intror Hsp))
  (p2_inv_kept cx i c m tab mt LFO_NV (s22_L cx i c m mt) ly S W regs mem md k acc regs' mem' md'
     HI HJ' RE K2 K3 K4 K8 K9)
  R15 R16 (eq_trans K20 R20) (eq_trans K21 R21) (eq_trans K24 R24)
  (conj (eq_trans K22 Q22) (conj (eq_trans K23 Q23) (conj (eq_trans K25 Q25)
    (conj (eq_trans K26 Q26) (eq_trans K27 Q27)))))).
Qed.

(* ======================= the piece ======================= *)
Lemma s22_p2 : s22_p2_stmt B MT.
Proof.
intros i HJOIN HVD cx ly S W regs mem md k acc c m tab mt r HBASE HFRM HINV Hign Hr R10 R19 R20 R21 R24 HRK.
pose proof HINV as (Hi & Hpos & (HF & _ & _ & _) & _ & Hm & _ & _ & HSL & HCM & _).
pose proof HF as (HJ & _ & _ & _ & _ & G9 & _ & _ & _ & _ & _ & W176 & _).
pose proof (proj1 HJ) as HAR.
pose proof HBASE as HB0. unfold lt_base in HB0. destruct HB0 as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
destruct (s10_sp1_facts (spZ (x_regs cx)) Hal16) as (_ & Hs1).
assert (ES1 : x_s1 cx = s10_sp1 (spZ (x_regs cx))) by reflexivity.
pose proof asan_consts as (C1 & _).
pose proof Hm as (Hmin & Hm4096 & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR Hmin) as (_ & _ & Hmceil & _).
assert (HreqM : req_size seg_spec.SEG_M_SIZE = seg_spec.SEG_M_SIZE) by reflexivity.
rewrite HreqM in Hmceil. unfold seg_spec.SEG_M_SIZE in Hmceil.
assert (H32 : (length (SegModel.mc_seg (x_mcF cx)) <= 32)%nat).
{ destruct HCM as [_ Hmc]. destruct Hmc as (bs & _ & Henc). destruct Henc as (_ & Hle & _). exact Hle. }
assert (HMS : seg_spec.mseg_addr m i = m + 256 * Z.of_nat i)
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; reflexivity).
assert (HS1R : 0 <= x_s1 cx /\ x_s1 cx + 184 <= 2 ^ 64) by (rewrite ES1; lia).
assert (HmR : 0 <= m < 2 ^ 64) by lia.
(* the slots: 128(s1) = 4094 (0x85940), 168(s1) = m (0x85960, 0x859c0) *)
assert (S128 : rdword (rdW W mem) (x_s1 cx + 128) = Some 4094).
{ apply (HSL 128 4094). unfold s22_L. apply in_or_app. right. repeat first [left; reflexivity | right]. }
assert (S168 : rdword (rdW W mem) (x_s1 cx + 168) = Some m).
{ apply (HSL 168 m). unfold s22_L. apply in_or_app. left. unfold LT_LV. repeat first [left; reflexivity | right]. }
destruct (s22_name_str cx i c m (rdW W mem) HCM Hi) as (Hstr & Hn16 & Hnul).
assert (KK : forall a, rdW W mem a = rdW W mem a) by (intros a; reflexivity).
unfold cfg_at. change (w64 (BASE + S22_VR)) with (Z_to_bv 64 (BASE + S22_VR)).
destruct Hr as [(-> & Hsn) | (j & Hsj & ->)].
- (* strrchr found no '.': 0x85930 beqz a0 taken; 0x859bc / 0x859c0 reload a5 and a6; the join 0x859c4 *)
  pose proof (p2_split_none_nf _ Hsn) as Hsp.
  pose proof (p2_seedA W regs mem (x_s1 cx) m G9 R10 ltac:(lia) ltac:(lia) HmR S128 S168 W176) as HS.
  pose proof (p2_E_reg regs [SB; m; 0]) as EV.
  assert (E32 : ew (p2_E regs [SB; m; 0]) 32 = Z_to_bv 64 SB) by exact (p2_E_val regs [SB; m; 0] 0 ltac:(lia)).
  assert (E33 : ew (p2_E regs [SB; m; 0]) 33 = Z_to_bv 64 m) by exact (p2_E_val regs [SB; m; 0] 1 ltac:(lia)).
  assert (HEI : img_env VAL A_LIM (p2_E regs [SB; m; 0])) by (unfold p2_E; apply Eimg_env).
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] (p2_E regs [SB; m; 0]) (mrestrict (w_H W) mem))
    by (unfold sh_ok; apply Forall_nil).
  remember (p2_E regs [SB; m; 0]) as E0 eqn:HE0. clear HE0.
  paj_run_to_tok RUNTO HS HJ SHOK p2span S22_JOIN.
  { p2_awr. }
  p2_mdv md1. p2_mem KK.
  pmkst HS.
  lazymatch goal with HSx : st_ok_pi _ _ ?Ex ?ssx (restrict ?Hx ?msx) |- _ =>
    pose proof (p2_keep_of Ex ssx msx Hx regs HSx ltac:(p2_EV EV) ltac:(vm_compute; repeat split)) as HKP;
    pose proof (p2_reg_off Ex ssx msx Hx 32 0 SB (15%bv : bv 5) HSx ltac:(vm_compute; reflexivity)
      ltac:(p2_ew0; exact E32)) as Q15;
    pose proof (p2_reg_off Ex ssx msx Hx 33 0 m (16%bv : bv 5) HSx ltac:(vm_compute; reflexivity)
      ltac:(p2_ew0; exact E33)) as Q16
  end.
  rewrite Z.add_0_r in Q15, Q16.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdd) _ =>
    exact (p2_join i cx ly S W regs mem md k acc c m tab mt rg mm mdd HJOIN HBASE HFRM HINV Hsp HJ KK HKP
      Q15 Q16 R20 R21 R24 HRK) end.
- (* strrchr found the '.' at j: r = &m->seg[i].name[j] *)
  pose proof (SegModel.strrchr_lt _ _ _ Hsj) as Hjl. rewrite (SegModel.cut_nul_id _ Hnul) in Hjl.
  remember (nth (Datatypes.S j) (SegModel.ms_name (x_seg cx i) ++ [0]) 0) as b eqn:Hbd.
  assert (Hb : rdW W mem (seg_spec.mseg_addr m i + Z.of_nat j + 1) = Some b).
  { destruct Hstr as [Hzs _]. rewrite Hbd.
    replace (seg_spec.mseg_addr m i + Z.of_nat j + 1) with (seg_spec.mseg_addr m i + Z.of_nat (Datatypes.S j))
      by lia.
    apply Hzs. rewrite length_app. cbn [length]. lia. }
  destruct (aview_byte SEGS (w_H W) mem _ _ Hb) as (b0 & _ & _ & Hbr).
  assert (Hbh : b = SegModel.hd0 (skipn (Datatypes.S j) (SegModel.ms_name (x_seg cx i))))
    by (rewrite Hbd; apply p2_byte; exact Hjl).
  assert (HR0 : 4096 <= seg_spec.mseg_addr m i + Z.of_nat j <= 0x7fffff800000) by (rewrite HMS; lia).
  assert (HR2 : seg_spec.mseg_addr m i + Z.of_nat j + 2 <= x_s1 cx + 128) by (rewrite HMS, ES1; lia).
  assert (HRm : seg_spec.mseg_addr m i + Z.of_nat j + 2 <= m + 9236) by (rewrite HMS; lia).
  pose proof (p2_seedB W regs mem (x_s1 cx) m (seg_spec.mseg_addr m i + Z.of_nat j) b G9 R10
    ltac:(lia) ltac:(lia) HmR HR0 HR2 Hbr S128 S168 W176 Hb) as HS.
  pose proof (p2_E_reg regs [SB; m; b]) as EV.
  assert (E10 : ew (p2_E regs [SB; m; b]) 10 = Z_to_bv 64 (seg_spec.mseg_addr m i + Z.of_nat j))
    by (rewrite (EV 10%nat 10%bv eq_refl); exact R10).
  assert (E19 : ew (p2_E regs [SB; m; b]) 19 = Z_to_bv 64 (seg_spec.mseg_addr m i))
    by (rewrite (EV 19%nat 19%bv eq_refl); exact R19).
  assert (E32 : ew (p2_E regs [SB; m; b]) 32 = Z_to_bv 64 SB) by exact (p2_E_val regs [SB; m; b] 0 ltac:(lia)).
  assert (E33 : ew (p2_E regs [SB; m; b]) 33 = Z_to_bv 64 m) by exact (p2_E_val regs [SB; m; b] 1 ltac:(lia)).
  assert (E34 : ew (p2_E regs [SB; m; b]) 34 = Z_to_bv 64 b) by exact (p2_E_val regs [SB; m; b] 2 ltac:(lia)).
  assert (HEI : img_env VAL A_LIM (p2_E regs [SB; m; b])) by (unfold p2_E; apply Eimg_env).
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] (p2_E regs [SB; m; b]) (mrestrict (w_H W) mem))
    by (unfold sh_ok; apply Forall_nil).
  remember (p2_E regs [SB; m; b]) as E0 eqn:HE0. clear HE0.
  (* 0x85930 .. 0x85940: beqz a0 decided by a0's fact, a5, a7, t0, t1; stuck at beq a0,s3 *)
  paj_run_tok RUN HS HJ SHOK p2span.
  { p2_awr. }
  p2_mdv md1. p2_mem KK.
  psrr_branch_tok RUN BR HS SHOK p2span.
  + (* 0x85944 beq a0,s3 taken: the '.' is the name's first byte *)
    assert (Hj0 : j = 0%nat).
    { rewrite branch_eq_U in Hc.
      rewrite (U_atom _ 10 (seg_spec.mseg_addr m i + Z.of_nat j)), (U_atom _ 19 (seg_spec.mseg_addr m i)) in Hc
        by first [p2_ew0; assumption | lia].
      apply Z.eqb_eq in Hc. lia. }
    subst j.
    pose proof (p2_split_none_0 _ Hsj) as Hsp.
    (* 0x859c0 ld a6,168(s1); the join *)
    paj_run_to_tok RUNTO HS HJ SHOK p2span S22_JOIN.
    { p2_awr. }
    p2_mdv md2. p2_mem KK.
    pmkst HS.
    lazymatch goal with HSx : st_ok_pi _ _ ?Ex ?ssx (restrict ?Hx ?msx) |- _ =>
      pose proof (p2_keep_of Ex ssx msx Hx regs HSx ltac:(p2_EV EV) ltac:(vm_compute; repeat split)) as HKP;
      pose proof (p2_reg_off Ex ssx msx Hx 32 0 SB (15%bv : bv 5) HSx ltac:(vm_compute; reflexivity)
        ltac:(p2_ew0; exact E32)) as Q15;
      pose proof (p2_reg_off Ex ssx msx Hx 33 0 m (16%bv : bv 5) HSx ltac:(vm_compute; reflexivity)
        ltac:(p2_ew0; exact E33)) as Q16
    end.
    rewrite Z.add_0_r in Q15, Q16.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdd) _ =>
      exact (p2_join i cx ly S W regs mem md k acc c m tab mt rg mm mdd HJOIN HBASE HFRM HINV Hsp HJ KK HKP
        Q15 Q16 R20 R21 R24 HRK) end.
  + (* 0x85944 beq a0,s3 not taken: j <> 0 *)
    assert (Hj0 : j <> 0%nat).
    { rewrite branch_eq_U in Hc.
      rewrite (U_atom _ 10 (seg_spec.mseg_addr m i + Z.of_nat j)), (U_atom _ 19 (seg_spec.mseg_addr m i)) in Hc
        by first [p2_ew0; assumption | lia].
      apply Z.eqb_neq in Hc. lia. }
    clear Hc.
    (* 0x85948 .. 0x85960: a1 := a0 + 1, its 1-byte check (slow block 0x85bb4), lbu a3, ld a6; stuck at beqz a3 *)
    paj_run_tok RUN HS HJ SHOK p2span.
    { (* the check of the byte after the '.': it lies in the block m *)
      apply (obl_of_block SEGS B LAWS ly S W _ _ _ (SOff 32 0) _ 1 m seg_spec.SEG_M_SIZE (proj1 HJ) Hmin).
      - rewrite (U_atom _ 32 SB) by first [p2_ew0; assumption | unfold SB; lia]. reflexivity.
      - rewrite (U_atom_off _ 10 (seg_spec.mseg_addr m i + Z.of_nat j) 1) by first [p2_ew0; assumption | lia].
        lia.
      - rewrite (U_atom_off _ 10 (seg_spec.mseg_addr m i + Z.of_nat j) 1) by first [p2_ew0; assumption | lia].
        rewrite HreqM. unfold seg_spec.SEG_M_SIZE. lia. }
    { p2_awr. }
    p2_mdv md2. p2_mem KK.
    psrr_branch_tok RUN BR HS SHOK p2span.
    * (* 0x85964 beqz a3 taken: the byte after the '.' is the NUL *)
      assert (Hb0 : b = 0).
      { rewrite branch_eq_U, (U_atom _ 34 b), U_lit in Hc by first [p2_ew0; assumption | lia].
        apply Z.eqb_eq in Hc. exact Hc. }
      pose proof (p2_split_none_nul _ _ Hsj (eq_trans (eq_sym Hbh) Hb0)) as Hsp.
      paj_run_to_tok RUNTO HS HJ SHOK p2span S22_JOIN.
      { p2_awr. }
      p2_mdv md3. p2_mem KK.
      pmkst HS.
      lazymatch goal with HSx : st_ok_pi _ _ ?Ex ?ssx (restrict ?Hx ?msx) |- _ =>
        pose proof (p2_keep_of Ex ssx msx Hx regs HSx ltac:(p2_EV EV) ltac:(vm_compute; repeat split)) as HKP;
        pose proof (p2_reg_off Ex ssx msx Hx 32 0 SB (15%bv : bv 5) HSx ltac:(vm_compute; reflexivity)
          ltac:(p2_ew0; exact E32)) as Q15;
        pose proof (p2_reg_off Ex ssx msx Hx 33 0 m (16%bv : bv 5) HSx ltac:(vm_compute; reflexivity)
          ltac:(p2_ew0; exact E33)) as Q16
      end.
      rewrite Z.add_0_r in Q15, Q16.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdd) _ =>
        exact (p2_join i cx ly S W regs mem md k acc c m tab mt rg mm mdd HJOIN HBASE HFRM HINV Hsp HJ KK HKP
          Q15 Q16 R20 R21 R24 HRK) end.
    * (* 0x85964 beqz a3 not taken: 0x85968 .. 0x85970, the digit loop's head at t = 0, v = 0 *)
      assert (Hbn : b <> 0).
      { rewrite branch_eq_U, (U_atom _ 34 b), U_lit in Hc by first [p2_ew0; assumption | lia].
        apply Z.eqb_neq in Hc. exact Hc. }
      clear Hc.
      pose proof (p2_len_pos _ (fun H0 => Hbn (eq_trans Hbh H0))) as Hlen.
      paj_run_to_tok RUNTO HS HJ SHOK p2span S22_VD.
      { p2_awr. }
      p2_mdv md3. p2_mem KK.
      pmkst HS.
      lazymatch goal with HSx : st_ok_pi _ _ ?Ex ?ssx (restrict ?Hx ?msx) |- _ =>
        pose proof (p2_keep_of Ex ssx msx Hx regs HSx ltac:(p2_EV EV) ltac:(vm_compute; repeat split)) as HKP;
        pose proof (p2_reg_off Ex ssx msx Hx 32 0 SB (15%bv : bv 5) HSx ltac:(vm_compute; reflexivity)
          ltac:(p2_ew0; exact E32)) as Q15;
        pose proof (p2_reg_off Ex ssx msx Hx 33 0 m (16%bv : bv 5) HSx ltac:(vm_compute; reflexivity)
          ltac:(p2_ew0; exact E33)) as Q16;
        pose proof (p2_reg_off Ex ssx msx Hx 10 0 (seg_spec.mseg_addr m i + Z.of_nat j) (10%bv : bv 5) HSx
          ltac:(vm_compute; reflexivity) ltac:(p2_ew0; exact E10)) as Q10;
        pose proof (p2_reg_off Ex ssx msx Hx 10 2 (seg_spec.mseg_addr m i + Z.of_nat j) (11%bv : bv 5) HSx
          ltac:(vm_compute; reflexivity) ltac:(p2_ew0; exact E10)) as Q11;
        pose proof (p2_reg_off Ex ssx msx Hx 10 2 (seg_spec.mseg_addr m i + Z.of_nat j) (12%bv : bv 5) HSx
          ltac:(vm_compute; reflexivity) ltac:(p2_ew0; exact E10)) as Q12;
        pose proof (p2_reg_off Ex ssx msx Hx 34 0 b (13%bv : bv 5) HSx
          ltac:(vm_compute; reflexivity) ltac:(p2_ew0; exact E34)) as Q13;
        pose proof (p2_reg_lit Ex ssx msx Hx 10 (5%bv : bv 5) HSx ltac:(vm_compute; reflexivity)) as Q5;
        pose proof (p2_reg_lit Ex ssx msx Hx 4094 (6%bv : bv 5) HSx ltac:(vm_compute; reflexivity)) as Q6;
        pose proof (p2_reg_lit Ex ssx msx Hx 18446744073709551606 (17%bv : bv 5) HSx
          ltac:(vm_compute; reflexivity)) as Q17;
        pose proof (p2_reg_lit Ex ssx msx Hx 0 (18%bv : bv 5) HSx ltac:(vm_compute; reflexivity)) as Q18
      end.
      rewrite Z.add_0_r in Q15, Q16, Q10, Q13.
      destruct HKP as (K2 & K3 & K4 & K8 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdd) _ =>
        assert (V17 : getr rg 17 = w64 (-10)) by (rewrite Q17; unfold w64; apply Z_to_bv64_eq_mod; reflexivity);
        assert (V11 : getr rg 11 = w64 (seg_spec.mseg_addr m i + Z.of_nat (Datatypes.S j) + Z.of_nat 0 + 1))
          by (rewrite Q11; unfold w64; f_equal; lia);
        assert (V12 : getr rg 12 = w64 (seg_spec.mseg_addr m i + Z.of_nat (Datatypes.S j) + Z.of_nat 0 + 1))
          by (rewrite Q12; unfold w64; f_equal; lia);
        assert (V13 : getr rg 13 = w64 (nth 0 (skipn (Datatypes.S j) (SegModel.ms_name (x_seg cx i))) 0))
          by (rewrite Q13, Hbh, p2_hd0_nth; reflexivity);
        assert (VRK : s22_rk m i rg)
          by (destruct HRK as (P22 & P23 & P25 & P26 & P27);
              exact (conj (eq_trans K22 P22) (conj (eq_trans K23 P23) (conj (eq_trans K25 P25)
                (conj (eq_trans K26 P26) (eq_trans K27 P27))))));
        pose proof (eq_trans K19 R19) as V19; pose proof (eq_trans K20 R20) as V20;
        pose proof (eq_trans K21 R21) as V21; pose proof (eq_trans K24 R24) as V24;
        apply (HVD cx ly S W rg mm mdd k acc c m tab mt j 0%nat 0 HBASE HFRM
          (p2_inv_kept cx i c m tab mt LFO_NV (s22_L cx i c m mt) ly S W regs mem md k acc rg mm mdd
             HINV HJ KK K2 K3 K4 K8 K9)
          Hign Hsj Hj0)
      end.
      all: first [ assumption | reflexivity | lia ].
Qed.

End e.
End f.
End d.
Print Assumptions s22_p2.
