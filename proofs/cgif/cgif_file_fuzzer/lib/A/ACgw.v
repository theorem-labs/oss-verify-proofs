(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr ACj3 ACj1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Class af_params := { afp_wfn : Z; afp_hw : Z; afp_ctx : list (list Z) }.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Context {AP : af_params}.
#[local] Notation wfn := (@afp_wfn AP).
#[local] Notation hw := (@afp_hw AP).
#[local] Notation CTX := (@afp_ctx AP).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition AF_RETC : Z := 0x86c.
Definition AF_RET : Z := 0x870.
Definition AF_OK : Z := 0x8b0.
Definition AF_B : Z := 0x918.
Definition AF_LOOP : Z := 0xa2c.
Definition AF_C : Z := 0xb30.
Definition AF_FL : Z := 0xb74.
Definition AF_D : Z := 0xc24.
Definition AF_E : Z := 0xe9c.
Definition AF_SAME : Z := 0x10bc.
Definition AF_EALLOC : Z := 0x1100.
Definition af_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition af_frame (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error af_saved j = Some r -> val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Definition af_extra (regs : bvmap 5 word) (g : Z) (s1 : cgif_st) (cfp : Z) (cf : list Z) (more : list Z) : list word :=
map (Z_to_bv 64) [g; frame_ptr (nth 0 (cg_frames s1) None); frame_ptr (nth 1 (cg_frames s1) None); frame_ptr (nth 2 (cg_frames s1) None);
cg_raw s1; cg_cur s1; SB; cg_pal s1; cg_attr s1; cg_gen s1; cg_W s1; cg_H s1; cg_ngp s1; cg_loops s1; cfp]
++ map (Z_to_bv 64) (firstn 7 (cf ++ repeat 0 7))
++ map (fun r => getr regs (Z_to_bv 5 r)) af_saved
++ map (Z_to_bv 64) more.
Definition A_MORE : nat := 67.
Definition Bxa : sv := SOff 38 0.
Definition RBspanA : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition shq (n : nat) (o : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n o) (SLit 3)) (SOff 38 0).
Definition af_locals (d : Z) (lc : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some 2%nat) d (d + 120) d (d + 120) lc.
Definition af_savedr (d : Z) (sv : bool) : YP09.region :=
YP09.mkRegion (Some 2%nat) (d + 120) (d + 224) (d + 120) (if sv then d + 120 else d + 224)
(if sv then map (fun j => YP09.mkChunk (d + 216 - 8 * Z.of_nat j) (CVal 8 (SOff (54 + j) 0))) (seq 0 13) else []).
Definition af_obj (ih wlo whi : Z) : YP09.region :=
YP09.mkRegion (Some 32%nat) 0 CGIF_SIZE wlo whi
[YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0));
YP09.mkChunk 24 (CVal 8 (SOff 39 0)); YP09.mkChunk 40 (CVal 4 (SOff 40 0)); YP09.mkChunk 44 (CVal 4 (SOff 41 0));
YP09.mkChunk 48 (CVal 2 (SOff 42 0)); YP09.mkChunk 50 (CVal 2 (SOff 43 0)); YP09.mkChunk 52 (CVal 2 (SOff 44 0));
YP09.mkChunk 54 (CVal 2 (SOff 45 0)); YP09.mkChunk 56 (CVal 8 (SLit hw)); YP09.mkChunk 64 (CVal 8 (SLit 0));
YP09.mkChunk 72 (CVal 8 (SOff 36 0)); YP09.mkChunk 80 (CVal 8 (SLit 0)); YP09.mkChunk 88 (CVal 4 (SOff 37 0));
YP09.mkChunk 92 (CVal 4 (SLit ih))].
Definition af_cfr : YP09.region :=
YP09.mkRegion (Some 46%nat) 0 32 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 47 0)); YP09.mkChunk 8 (CVal 8 (SOff 48 0)); YP09.mkChunk 16 (CVal 4 (SOff 49 0));
YP09.mkChunk 20 (CVal 4 (SOff 50 0)); YP09.mkChunk 24 (CVal 2 (SOff 51 0)); YP09.mkChunk 26 (CVal 2 (SOff 52 0));
YP09.mkChunk 28 (CVal 1 (SOff 53 0))].
Definition af_regions (d : Z) (sv : bool) (lc : list YP09.chunk) (ih wlo whi : Z) : smem :=
[af_locals d lc; af_savedr d sv; got_regionP; bcell_regionP 38; af_obj ih wlo whi; af_cfr].
Definition hfactA : afact := mkAF 4096 0x7fffff800000 4.
Definition hfact3 : afact := mkAF 4096 0x7fffff800000 3.
Definition af_facts : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, hfactA); (38%nat, mkAF SB SB 0); (46%nat, hfact3)] [] [].
Definition af_SH : list shent := [mkSHE 32 0 CGIF_SIZE; mkSHE 46 0 32].
Definition ss_af (pc : Z) (sregs : list sv) (d : Z) (sv : bool) (lc : list YP09.chunk) (ih wlo whi : Z) : sstate :=
mkSS pc sregs (af_regions d sv lc ih wlo whi) None af_facts.
Definition FPa (g : Z) (s : cgif_st) (N : Z) : list (Z * Z) := ablocks_fp (cgif_blocks g s N).
Definition af_cx (B : asyms) ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (g cfp : Z) (s : cgif_st) (N : Z)
(lpal lpa img fattr fgen delay nlp tidx : Z) (rest : list (Z * Z)) : Prop :=
afn_pre SEGS B TADDFRAME_STK ly S W regs mem md ch /\
In (raZ regs :: spine ch) CTX /\ Z.of_nat (length (frames S)) <= 7 /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) /\
getr regs 10 = w64 g /\ getr regs 11 = w64 cfp /\
afobj SEGS B ly S W mem cfp 32 /\
obj_at SEGS (mrestrict (w_H W) mem) cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] /\
tcgif_at SEGS wfn hw (mrestrict (w_H W) mem) g s /\ cgif_wf s N /\
Z_to_bv 64 lpa = Z_to_bv 64 lpal /\
Permutation (ablocks B ly S) (cgif_blocks g s N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) /\
st_nev S + EV_ADDFRAME <= EV_MAX /\ blocks_bytes S + LIVE_ADDFRAME <= LIVE_MAX.
Definition af_post (B : asyms) ly S W (regs : bvmap 5 word) mem md (g : Z) (s : cgif_st) (N img fattr lpa nlp : Z) (rest : list (Z * Z)) (kf : Z)
: world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TADDFRAME_STK (spZ regs) (FPa g s N) ly S W mem md [] ly' S' W' mem' md' kf /\
aregs_preserved regs regs' /\
exists s' : cgif_st,
tcgif_at SEGS wfn hw (mrestrict (w_H W') mem') g s' /\ cgif_wf s' N /\
cg_W s' = cg_W s /\ cg_H s' = cg_H s /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\
Permutation (ablocks B ly' S') (cgif_blocks g s' N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) /\
(forall b, In b (cgif_blocks g s' N) ->
aftok (FPa g s N) (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TADDFRAME_STK (spZ regs) (FPa g s N) (ablocks B ly S) blc ly' [] (fst b + i)).
Lemma af_post_mono : forall B ly S W regs mem md g s N img fattr lpa nlp rest kf kf' W' c',
af_post B ly S W regs mem md g s N img fattr lpa nlp rest kf W' c' -> kf <= kf' -> kf' <= EV_ADDFRAME ->
st_nev S + EV_ADDFRAME <= EV_MAX ->
af_post B ly S W regs mem md g s N img fattr lpa nlp rest kf' W' c'.
Proof.
intros B ly S W regs mem md g s N img fattr lpa nlp rest kf kf' W' c' (ly' & S' & regs' & mem' & md' & Hc & HJ & HP & HQ) Hle Hmax Hev.
exists ly', S', regs', mem', md'. split; [exact Hc|]. split; [|split; [exact HP | exact HQ]].
eapply (ajournal_mono_k SEGS B); [exact HJ | lia].
Qed.
Definition af_E (regs : bvmap 5 word) (g : Z) (s : cgif_st) (cfp lpal img fattr fgen delay nlp tidx : Z) (E : env) : Prop :=
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) /\
ew E 32 = Z_to_bv 64 g /\
ew E 33 = Z_to_bv 64 (frame_ptr (nth 0 (cg_frames s) None)) /\ ew E 34 = Z_to_bv 64 (frame_ptr (nth 1 (cg_frames s) None)) /\
ew E 35 = Z_to_bv 64 (frame_ptr (nth 2 (cg_frames s) None)) /\
ew E 36 = Z_to_bv 64 (cg_raw s) /\ ew E 37 = Z_to_bv 64 (cg_cur s) /\ ew E 38 = Z_to_bv 64 SB /\ ew E 39 = Z_to_bv 64 (cg_pal s) /\
ew E 40 = Z_to_bv 64 (cg_attr s) /\ ew E 41 = Z_to_bv 64 (cg_gen s) /\ ew E 42 = Z_to_bv 64 (cg_W s) /\ ew E 43 = Z_to_bv 64 (cg_H s) /\
ew E 44 = Z_to_bv 64 (cg_ngp s) /\ ew E 45 = Z_to_bv 64 (cg_loops s) /\ ew E 46 = Z_to_bv 64 cfp /\
ew E 47 = Z_to_bv 64 lpal /\ ew E 48 = Z_to_bv 64 img /\ ew E 49 = Z_to_bv 64 fattr /\ ew E 50 = Z_to_bv 64 fgen /\
ew E 51 = Z_to_bv 64 delay /\ ew E 52 = Z_to_bv 64 nlp /\ ew E 53 = Z_to_bv 64 tidx /\
img_env VAL A_LIM E    .
Definition af_side (m : word -> option byte) (g : Z) (s1 : cgif_st) : Prop :=
obj_at SEGS m (cg_raw s1) LAY_Raw (traw_vals wfn g s1) /\
(forall f, In (Some f) (cg_frames s1) -> obj_at SEGS m (fr_ptr f) LAY_Frame (frame_vals f)).
Definition af_obj_ok (s s1 : cgif_st) (N : Z) : Prop :=
cgif_wf s1 N /\ cg_W s1 = cg_W s /\ cg_H s1 = cg_H s /\ cg_attr s1 = cg_attr s /\ cg_raw s1 = cg_raw s /\
cg_pal s1 = cg_pal s /\ cg_ngp s1 = cg_ngp s /\ cg_gen s1 = cg_gen s /\ cg_loops s1 = cg_loops s.
Definition af_cblocks (img N fattr lpa nlp : Z) (rest : list (Z * Z)) : list (Z * Z) :=
(img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest.
Definition af_newtok (B : asyms) ly S (regs : bvmap 5 word) (g : Z) (s : cgif_st) (N : Z) (b : Z * Z) : Prop :=
aftok (FPa g s N) (ablocks B ly S) b /\
forall blc lyq ownq i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TADDFRAME_STK (spZ regs) (FPa g s N) (ablocks B ly S) blc lyq ownq (fst b + i).
Definition af_mid (B : asyms) ly S W (regs : bvmap 5 word) mem md (g cfp : Z) (s : cgif_st) (N img fattr lpa nlp : Z) (rest : list (Z * Z))
lyc Sc (Wc : world SEGS) memc mdc (k : Z) (s1 : cgif_st) : Prop :=
ajournal SEGS B TADDFRAME_STK (spZ regs) (FPa g s N) ly S W mem md [] lyc Sc Wc memc mdc k /\ 0 <= k /\
af_frame (mrestrict (w_H Wc) memc) (spZ regs) regs /\
tcgif_at SEGS wfn hw (mrestrict (w_H Wc) memc) g s1 /\ af_obj_ok s s1 N /\
Permutation (ablocks B lyc Sc) (cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest) /\
(forall b, In b (cgif_blocks g s1 N) -> In b (cgif_blocks g s N) \/ af_newtok B ly S regs g s N b).
Definition af_regs_at (B : asyms) (regs regs1 : bvmap 5 word) (g : Z) : Prop :=
getr regs1 2 = w64 (spZ regs - 224) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 18 = w64 g /\ getr regs1 8 = w64 (g + 88) /\ getr regs1 22 = w64 SB.
Definition af_s1_at (regs1 : bvmap 5 word) (g : Z) : Prop := getr regs1 9 = w64 (SB + (g + 88) / 8).
Definition af_regs_ret (B : asyms) (regs regs1 : bvmap 5 word) (g : Z) : Prop :=
getr regs1 2 = w64 (spZ regs - 224) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\ getr regs1 8 = w64 (g + 88).
Definition AF_RET_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1,
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_mid B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= EV_ADDFRAME ->
af_regs_ret B regs regs1 g ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_RET)) memc (seg_rom SEGS)) mdc)
(af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Definition AF_RETC_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (v : Z),
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_mid B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= EV_ADDFRAME ->
af_regs_ret B regs regs1 g -> bv_unsigned (getr regs1 23) mod 2 ^ 32 = v ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_RETC)) memc (seg_rom SEGS)) mdc)
(af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Definition ss_880 (ih : Z) : sstate :=
(mkSS 2004
[SLit 0; SOff 1 0; SOff 2 (-224); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 32 88; SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0); SLit 6; SOff 46 0; SOff 253 0; SOff 13 0; SOff 14 0; SOff 46 0;
SOff 16 0; SOff 17 0; SOff 32 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 38 0; SExt true 32 (SOff 37 0); SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
[{| r_base := Some 2%nat; r_lo := -224; r_hi := -104; r_wlo := -224; r_whi := -104; r_chunks := [] |};
{|
r_base := Some 2%nat;
r_lo := -104;
r_hi := 0;
r_wlo := -104;
r_whi := 0;
r_chunks :=
[{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 38 0) |}] |};
{|
r_base := Some 32%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 88;
r_whi := 92;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 34 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 35 0) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 39 0) |};
{| c_off := 40; YP09.c_val := CVal 4 (SOff 40 0) |}; {| c_off := 44; YP09.c_val := CVal 4 (SOff 41 0) |}; {| c_off := 48; YP09.c_val := CVal 2 (SOff 42 0) |}; {| c_off := 50; YP09.c_val := CVal 2 (SOff 43 0) |};
{| c_off := 52; YP09.c_val := CVal 2 (SOff 44 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 45 0) |}; {| c_off := 56; YP09.c_val := CVal 8 (SLit hw) |}; {| c_off := 64; YP09.c_val := CVal 8 (SLit 0) |};
{| c_off := 72; YP09.c_val := CVal 8 (SOff 36 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 88; YP09.c_val := CVal 4 (SOff 37 0) |};
{| c_off := 92; YP09.c_val := CVal 4 (SLit ih) |}]
|};
{|
r_base := Some 46%nat;
r_lo := 0;
r_hi := 32;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 47 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 48 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 49 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 50 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 51 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 52 0) |}; {| c_off := 28; YP09.c_val := CVal 1 (SOff 53 0) |}]
|}]
None
{|
f_atoms :=
[(2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (38%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(46%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |})];
f_conds := [];
f_alias := []
|}).
Definition af_sites (B : asyms) : list (list Z) :=
[[pc_free_ra0 (as_code B); BASE + 0x10a0]; [pc_free_ra0 (as_code B); BASE + 0x10f0]; [pc_free_ra0 (as_code B); BASE + 0x10f8];
[pc_malloc_ra0 (as_code B); BASE + 0xc2c]; [pc_malloc_ra0 (as_code B); BASE + 0xdd8]; [pc_malloc_ra0 (as_code B); BASE + 0xe58];
[pc_free_ra0 (as_code B); BASE + 0x2ad0]; [pc_free_ra0 (as_code B); BASE + 0x2b08]; [pc_free_ra0 (as_code B); BASE + 0xbbc]].
Definition ss_OK (ih : Z) : sstate :=
(mkSS 2224
[SLit 0; SOff 1 0; SOff 2 (-224); SOff 3 0; SOff 4 0; SOff 32 40; SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 40) (SLit 3)) (SOff 38 0); SOff 7 0; SOff 32 88; SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0); SOff 46 16; SAlu ALU_AND (SExt false 32 (SOff 49 0)) (SLit 4); SAlu ALU_AND (SExt false 32 (SOff 49 0)) (SLit 1); SOff 67 0; SAlu ALU_AND (SExt false 32 (SOff 40 0)) (SLit 4); SOff 46 0; SExt false 32 (SOff 40 0); SAlu ALU_ADD (SAlu ALU_SRL (SOff 46 16) (SLit 3)) (SOff 38 0); SOff 32 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 38 0; SExt true 32 (SOff 37 0); SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
[{|
r_base := Some 2%nat;
r_lo := -224;
r_hi := -104;
r_wlo := -224;
r_whi := -104;
r_chunks := []
|};
{|
r_base := Some 2%nat;
r_lo := -104;
r_hi := 0;
r_wlo := -104;
r_whi := 0;
r_chunks :=
[{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |};
{| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |};
{| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
{| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |};
{| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |};
{| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
{| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |};
{| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |};
{| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
{| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|};
{| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 38 0) |}] |};
{|
r_base := Some 32%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 88;
r_whi := 92;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 33 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 34 0) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 35 0) |};
{| c_off := 24; YP09.c_val := CVal 8 (SOff 39 0) |};
{| c_off := 40; YP09.c_val := CVal 4 (SOff 40 0) |};
{| c_off := 44; YP09.c_val := CVal 4 (SOff 41 0) |};
{| c_off := 48; YP09.c_val := CVal 2 (SOff 42 0) |};
{| c_off := 50; YP09.c_val := CVal 2 (SOff 43 0) |};
{| c_off := 52; YP09.c_val := CVal 2 (SOff 44 0) |};
{| c_off := 54; YP09.c_val := CVal 2 (SOff 45 0) |};
{| c_off := 56; YP09.c_val := CVal 8 (SLit hw) |};
{| c_off := 64; YP09.c_val := CVal 8 (SLit 0) |};
{| c_off := 72; YP09.c_val := CVal 8 (SOff 36 0) |};
{| c_off := 80; YP09.c_val := CVal 8 (SLit 0) |};
{| c_off := 88; YP09.c_val := CVal 4 (SOff 37 0) |};
{|
c_off := 92;
YP09.c_val :=
CVal 4
(SLit
ih)
|}]
|};
{|
r_base := Some 46%nat;
r_lo := 0;
r_hi := 32;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 47 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 48 0) |};
{| c_off := 16; YP09.c_val := CVal 4 (SOff 49 0) |};
{| c_off := 20; YP09.c_val := CVal 4 (SOff 50 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 51 0) |};
{| c_off := 26; YP09.c_val := CVal 2 (SOff 52 0) |};
{| c_off := 28; YP09.c_val := CVal 1 (SOff 53 0) |}]
|}]
None
{|
f_atoms :=
[(2%nat,
{| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |});
(32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(38%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(46%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |})];
f_conds := [];
f_alias := []
|}).
Definition ss_B (ih ho : Z) (hd : nat) : sstate :=
(mkSS 2328
[SLit 0; SOff 1 0; SOff 2 (-224); SOff 3 0; SOff 4 0; SOff 32 40; SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 40) (SLit 3)) (SOff 38 0); SOff 7 0; SOff 32 88; SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0); SOff 46 24;
SAlu ALU_AND (SExt false 32 (SOff 49 0)) (SLit 4); SAlu ALU_AND (SExt false 32 (SOff 49 0)) (SLit 1); SOff hd 0; SOff 512 0; SOff 46 0; SExt false 32 (SOff 40 0); SAlu ALU_ADD (SAlu ALU_SRL (SOff 46 16) (SLit 3)) (SOff 38 0);
SOff 32 0; SOff 19 0; SOff 20 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 ho) (SLit 3)) (SOff 38 0); SOff 38 0; SOff 32 ho; SLit ih; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
[{|
r_base := Some 2%nat;
r_lo := -224;
r_hi := -104;
r_wlo := -224;
r_whi := -104;
r_chunks :=
[{| c_off := -112; YP09.c_val := CVal 8 (SOff hd 0) |}; {| c_off := -120; YP09.c_val := CVal 8 (SOff 46 0) |}; {| c_off := -128; YP09.c_val := CVal 8 (SOff 46 24) |}; {| c_off := -152; YP09.c_val := CVal 8 (SLit ho) |};
{| c_off := -184; YP09.c_val := CVal 8 (SOff 32 92) |}; {| c_off := -192; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 92) (SLit 3)) (SOff 38 0)) |}; {| c_off := -160; YP09.c_val := CVal 8 (SOff 67 0) |};
{| c_off := -136; YP09.c_val := CVal 8 (SOff 46 16) |}; {| c_off := -144; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 46 16) (SLit 3)) (SOff 38 0)) |}; {| c_off := -168; YP09.c_val := CVal 8 (SOff 32 40) |};
{| c_off := -176; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 40) (SLit 3)) (SOff 38 0)) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -104;
r_hi := 0;
r_wlo := -104;
r_whi := 0;
r_chunks :=
[{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 38 0) |}] |};
{|
r_base := Some 32%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 88;
r_whi := 92;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 34 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 35 0) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 39 0) |};
{| c_off := 40; YP09.c_val := CVal 4 (SOff 40 0) |}; {| c_off := 44; YP09.c_val := CVal 4 (SOff 41 0) |}; {| c_off := 48; YP09.c_val := CVal 2 (SOff 42 0) |}; {| c_off := 50; YP09.c_val := CVal 2 (SOff 43 0) |};
{| c_off := 52; YP09.c_val := CVal 2 (SOff 44 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 45 0) |}; {| c_off := 56; YP09.c_val := CVal 8 (SLit hw) |}; {| c_off := 64; YP09.c_val := CVal 8 (SLit 0) |};
{| c_off := 72; YP09.c_val := CVal 8 (SOff 36 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 88; YP09.c_val := CVal 4 (SOff 37 0) |}; {| c_off := 92; YP09.c_val := CVal 4 (SLit ih) |}]
|};
{|
r_base := Some 46%nat;
r_lo := 0;
r_hi := 32;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 47 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 48 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 49 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 50 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 51 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 52 0) |}; {| c_off := 28; YP09.c_val := CVal 1 (SOff 53 0) |}]
|}]
None
{|
f_atoms :=
[(2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (38%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(46%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |})];
f_conds := [];
f_alias := []
|}).
Definition ss_C (ih ho : Z) (hd : nat) : sstate :=
(mkSS 2864
[SLit 0; SOff 644 0; SOff 2 (-224); SOff 3 0; SOff 4 0; SOff 645 0; SOff 646 0; SOff 647 0; SOff 32 88; SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0); SOff 648 0; SOff 649 0; SOff 650 0; SOff 651 0; SOff 652 0; SOff 653 0; SOff 654 0; SOff 655 0; SOff 32 0; SOff 656 0; SOff 657 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 ho) (SLit 3)) (SOff 38 0); SOff 38 0; SOff 32 ho; SLit ih; SOff 658 0; SOff 659 0; SOff 660 0; SOff 661 0; SOff 662 0; SOff 663 0; SOff 664 0]
[{|
r_base := Some 2%nat;
r_lo := -224;
r_hi := -104;
r_wlo := -224;
r_whi := -104;
r_chunks :=
[{| c_off := -112; YP09.c_val := CVal 8 (SOff hd 0) |}; {| c_off := -120; YP09.c_val := CVal 8 (SOff 46 0) |}; {| c_off := -128; YP09.c_val := CVal 8 (SOff 46 24) |}; {| c_off := -152; YP09.c_val := CVal 8 (SLit ho) |};
{| c_off := -184; YP09.c_val := CVal 8 (SOff 32 92) |}; {| c_off := -192; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 92) (SLit 3)) (SOff 38 0)) |}; {| c_off := -160; YP09.c_val := CVal 8 (SOff 67 0) |};
{| c_off := -136; YP09.c_val := CVal 8 (SOff 46 16) |}; {| c_off := -144; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 46 16) (SLit 3)) (SOff 38 0)) |}; {| c_off := -168; YP09.c_val := CVal 8 (SOff 32 40) |};
{| c_off := -176; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 40) (SLit 3)) (SOff 38 0)) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -104;
r_hi := 0;
r_wlo := -104;
r_whi := 0;
r_chunks :=
[{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 38 0) |}] |};
{|
r_base := Some 32%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 88;
r_whi := 92;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 34 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 35 0) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 39 0) |};
{| c_off := 40; YP09.c_val := CVal 4 (SOff 40 0) |}; {| c_off := 44; YP09.c_val := CVal 4 (SOff 41 0) |}; {| c_off := 48; YP09.c_val := CVal 2 (SOff 42 0) |}; {| c_off := 50; YP09.c_val := CVal 2 (SOff 43 0) |};
{| c_off := 52; YP09.c_val := CVal 2 (SOff 44 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 45 0) |}; {| c_off := 56; YP09.c_val := CVal 8 (SLit hw) |}; {| c_off := 64; YP09.c_val := CVal 8 (SLit 0) |};
{| c_off := 72; YP09.c_val := CVal 8 (SOff 36 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 88; YP09.c_val := CVal 4 (SOff 37 0) |}; {| c_off := 92; YP09.c_val := CVal 4 (SLit ih) |}]
|};
{|
r_base := Some 46%nat;
r_lo := 0;
r_hi := 32;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 47 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 48 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 49 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 50 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 51 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 52 0) |}; {| c_off := 28; YP09.c_val := CVal 1 (SOff 53 0) |}]
|}]
None
{|
f_atoms :=
[(2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (38%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(46%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |})];
f_conds := [];
f_alias := []
|}).
Definition af_deads_C : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition af_pre (B : asyms) ly S W (regs : bvmap 5 word) mem md (g cfp : Z) (s : cgif_st) (N fattr : Z) (E : env) (ms1 : machine_state) md1 : Prop :=
ajournal SEGS B TADDFRAME_STK (spZ regs) (FPa g s N) ly S W mem md [] ly S W (ms_mem ms1) md1 0 /\
af_side (mrestrict (w_H W) (ms_mem ms1)) g s /\
(forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte SEGS (mrestrict (w_H W) (ms_mem ms1)) (g + i) = mbyte SEGS (mrestrict (w_H W) mem) (g + i)) /\
(cg_cur s = 0 \/ cg_cur s = R_PENDING) /\
(Z.land fattr 1 <> 0 \/ Z.land (cg_attr s) 4 = 0) /\
ew E 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0) /\
(cg_ihead s = 1 \/ cg_ihead s = 2).
Definition AF_B_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest (E : env) (ms1 : machine_state) md1 (f : frame_st),
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E ->
af_pre B ly S W regs mem md g cfp s N fattr E ms1 md1 ->
nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = Some f ->
st_ok_pi SEGS VAL E (ss_B (cg_ihead s) (8 * cg_ihead s) (33 + Z.to_nat (cg_ihead s))) (restrict (w_H W) ms1) ->
sh_ok SEGS Bxa af_SH E (mrestrict (w_H W) (ms_mem ms1)) ->
SRr SEGS W (mkCfg ms1 md1) (af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Definition AF_C_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest (E : env) (ms1 : machine_state) md1,
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E ->
af_pre B ly S W regs mem md g cfp s N fattr E ms1 md1 ->
st_ok_pi SEGS VAL E (ss_C (cg_ihead s) (8 * cg_ihead s) (33 + Z.to_nat (cg_ihead s))) (restrict (w_H W) ms1) ->
sh_ok SEGS Bxa af_SH E (mrestrict (w_H W) (ms_mem ms1)) ->
SRr SEGS W (mkCfg ms1 md1) (af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Definition af_deads_OK : list (bv 5) := [13]%bv.
Definition af_kill_OK : list (bv 5) := [10; 12]%bv.
Definition AF_OK_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest (E : env) (ms1 : machine_state) md1,
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E ->
af_pre B ly S W regs mem md g cfp s N fattr E ms1 md1 ->
st_ok_pi SEGS VAL E (ss_OK (cg_ihead s)) (restrict (w_H W) ms1) ->
sh_ok SEGS Bxa af_SH E (mrestrict (w_H W) (ms_mem ms1)) ->
SRr SEGS W (mkCfg ms1 md1) (af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Definition af_locs (m : word -> option byte) (sp0 g cfp a4v : Z) : Prop :=
val_mem SEGS m (sp0 - 224 + 104) 8 cfp /\ val_mem SEGS m (sp0 - 224 + 96) 8 (cfp + 24) /\
val_mem SEGS m (sp0 - 224 + 88) 8 (cfp + 16) /\ val_mem SEGS m (sp0 - 224 + 56) 8 (g + 40) /\
val_mem SEGS m (sp0 - 224 + 40) 8 (g + 92) /\ val_mem SEGS m (sp0 - 224 + 32) 8 (SB + (g + 92) / 8) /\
val_mem SEGS m (sp0 - 224 + 48) 8 (SB + (g + 40) / 8) /\ val_mem SEGS m (sp0 - 224 + 64) 8 a4v /\
val_mem SEGS m (sp0 - 224 + 80) 8 (SB + (cfp + 16) / 8).
Definition af_lcD : list YP09.chunk :=
[YP09.mkChunk 104 (CVal 8 (SOff 46 0)); YP09.mkChunk 96 (CVal 8 (SOff 46 24)); YP09.mkChunk 88 (CVal 8 (SOff 46 16));
YP09.mkChunk 56 (CVal 8 (SOff 32 40)); YP09.mkChunk 40 (CVal 8 (SOff 32 92)); YP09.mkChunk 32 (CVal 8 (shq 32 92));
YP09.mkChunk 48 (CVal 8 (shq 32 40)); YP09.mkChunk 64 (CVal 8 (SOff 67 0)); YP09.mkChunk 80 (CVal 8 (shq 46 16))].
Definition af_locsE (m : word -> option byte) (sp0 g cfp a4v : Z) : Prop :=
val_mem SEGS m (sp0 - 224 + 104) 8 cfp /\
val_mem SEGS m (sp0 - 224 + 88) 8 (cfp + 16) /\ val_mem SEGS m (sp0 - 224 + 56) 8 (g + 40) /\
val_mem SEGS m (sp0 - 224 + 40) 8 (g + 92) /\ val_mem SEGS m (sp0 - 224 + 32) 8 (SB + (g + 92) / 8) /\
val_mem SEGS m (sp0 - 224 + 48) 8 (SB + (g + 40) / 8) /\ val_mem SEGS m (sp0 - 224 + 64) 8 a4v /\
val_mem SEGS m (sp0 - 224 + 80) 8 (SB + (cfp + 16) / 8).
Definition af_lcE : list YP09.chunk :=
[YP09.mkChunk 104 (CVal 8 (SOff 46 0)); YP09.mkChunk 88 (CVal 8 (SOff 46 16));
YP09.mkChunk 56 (CVal 8 (SOff 32 40)); YP09.mkChunk 40 (CVal 8 (SOff 32 92)); YP09.mkChunk 32 (CVal 8 (shq 32 92));
YP09.mkChunk 48 (CVal 8 (shq 32 40)); YP09.mkChunk 64 (CVal 8 (SOff 67 0)); YP09.mkChunk 80 (CVal 8 (shq 46 16))].
Definition af_locsD3 (m : word -> option byte) (sp0 g cfp a4v nw : Z) : Prop :=
af_locsE m sp0 g cfp a4v /\
val_mem SEGS m (sp0 - 224 + 8) 8 (SB + (cfp + 0) / 8) /\ val_mem SEGS m (sp0 - 224 + 16) 8 (SB + (nw + 0) / 8) /\
val_mem SEGS m (sp0 - 224 + 24) 8 (SB + (cfp + 26) / 8) /\
val_mem SEGS m (sp0 - 224 + 112) 8 (SB + (nw + 8) / 8).
Definition af_locsD2 (m : word -> option byte) (sp0 g cfp a4v nw : Z) : Prop :=
af_locsD3 m sp0 g cfp a4v nw /\
val_mem SEGS m (sp0 - 224 + 72) 8 (cfp + 26) /\ val_mem SEGS m (sp0 - 224 + 96) 8 (nw + 8).
Definition AF_D_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (i : Z),
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_mid B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= EV_FLUSH + 4 ->
blocks_bytes Sc <= blocks_bytes S ->
af_regs_at B regs regs1 g -> af_s1_at regs1 g -> getr regs1 24 = w64 i ->
af_locs (mrestrict (w_H Wc) memc) (spZ regs) g cfp (if Z.land fattr 4 =? 0 then 1 else 0) ->
(Z.land fattr 1 <> 0 \/ Z.land (cg_attr s) 4 = 0) ->
(i = 1 \/ i = 2) -> nth (Z.to_nat i) (cg_frames s1) None = None -> (i = 2 -> nth 1 (cg_frames s1) None <> None) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_D)) memc (seg_rom SEGS)) mdc)
(af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Definition AF_FL_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (f1 : frame_st),
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_mid B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= 1 ->
blocks_bytes Sc <= blocks_bytes S ->
af_regs_at B regs regs1 g -> af_s1_at regs1 g ->
af_locs (mrestrict (w_H Wc) memc) (spZ regs) g cfp (if Z.land fattr 4 =? 0 then 1 else 0) ->
(Z.land fattr 1 <> 0 \/ Z.land (cg_attr s) 4 = 0) ->
nth 1 (cg_frames s1) None = Some f1 -> nth 2 (cg_frames s1) None <> None ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_FL)) memc (seg_rom SEGS)) mdc)
(af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Definition af_midx (B : asyms) ly S W (regs : bvmap 5 word) mem md (g cfp : Z) (s : cgif_st) (N img fattr lpa nlp : Z) (rest : list (Z * Z))
lyc Sc (Wc : world SEGS) memc mdc (k : Z) (s1 : cgif_st) (X : list (Z * Z)) : Prop :=
ajournal SEGS B TADDFRAME_STK (spZ regs) (FPa g s N) ly S W mem md [] lyc Sc Wc memc mdc k /\ 0 <= k /\
af_frame (mrestrict (w_H Wc) memc) (spZ regs) regs /\
tcgif_at SEGS wfn hw (mrestrict (w_H Wc) memc) g s1 /\ af_obj_ok s s1 N /\
Permutation (ablocks B lyc Sc) (cgif_blocks g s1 N ++ X ++ af_cblocks img N fattr lpa nlp rest) /\
(forall b, In b (cgif_blocks g s1 N) -> In b (cgif_blocks g s N) \/ af_newtok B ly S regs g s N b) /\
(forall b, In b X -> af_newtok B ly S regs g s N b).
Lemma af_midx_nil : forall B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1,
af_mid B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 ->
af_midx B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 [].
Proof. intros * (H1 & H2 & H3 & H4 & H5 & H6 & H7). repeat (split; [assumption|]). intros b []. Qed.
Definition af_locs2 (m : word -> option byte) (sp0 g cfp a4v lpal : Z) : Prop :=
af_locs m sp0 g cfp a4v /\ val_mem SEGS m (sp0 - 224 + 64) 8 lpal.
Definition sx32 (v : Z) : Z := if v <? 2 ^ 31 then v else v - 2 ^ 32 + 2 ^ 64.
Lemma sx32_range : forall v, 0 <= v < 2 ^ 32 -> 0 <= sx32 v < 2 ^ 64.
Proof. intros v Hv. unfold sx32. destruct (Z.ltb_spec v (2 ^ 31)); lia. Qed.
Lemma sx32_low : forall v, 0 <= v < 2 ^ 32 -> sx32 v mod 2 ^ 32 = v.
Proof.
intros v Hv. unfold sx32. destruct (Z.ltb_spec v (2 ^ 31)); [apply Z.mod_small; lia|].
replace (v - 2 ^ 32 + 2 ^ 64) with (v + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma sx32_land : forall v k, 0 <= v < 2 ^ 32 -> 0 <= k < 2 ^ 32 -> Z.land (sx32 v) k = Z.land v k.
Proof.
intros v k Hv Hk. rewrite <- (sx32_low v Hv) at 2. rewrite <- (Z.land_ones (sx32 v) 32) by lia.
rewrite <- Z.land_assoc. f_equal. rewrite Z.land_comm, Z.land_ones by lia. symmetry. apply Z.mod_small. lia.
Qed.
Lemma U_sx32 : forall E a r, U E a = r -> 0 <= r < 2 ^ 32 -> U E (SExt true 32 a) = sx32 r.
Proof.
intros E a r Ha Hr. unfold sx32. rewrite U_SExt, Ha. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small r) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
destruct (Z.ltb_spec r (2 ^ 31)) as [Hl | Hh].
- rewrite (Z.mod_small (r + 2 ^ 31)) by lia. replace (r + 2 ^ 31 - 2 ^ 31) with r by lia. apply zcanon_id. unfold M64. lia.
- replace ((r + 2 ^ 31) mod 2 ^ 32) with (r + 2 ^ 31 - 2 ^ 32).
2:{ replace (r + 2 ^ 31) with ((r + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) at 2 by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
unfold zcanon, M64. replace (r + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with ((r - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma sext32_word : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (sx32 v).
Proof. intros E n v Hn Hv. rewrite denot_lit_U. f_equal. apply (U_sx32 E (SOff n 0) v (U_atom E n v Hn ltac:(lia)) Hv). Qed.
Definition af_locsD (m : word -> option byte) (sp0 g cfp a4v nw : Z) : Prop :=
val_mem SEGS m (sp0 - 224 + 104) 8 (g + 92) /\ val_mem SEGS m (sp0 - 224 + 112) 8 (SB + (g + 92) / 8) /\
val_mem SEGS m (sp0 - 224 + 56) 8 a4v /\
val_mem SEGS m (sp0 - 224 + 8) 8 (SB + (cfp + 0) / 8) /\ val_mem SEGS m (sp0 - 224 + 16) 8 (SB + (nw + 0) / 8) /\
val_mem SEGS m (sp0 - 224 + 24) 8 (SB + (cfp + 26) / 8) /\ val_mem SEGS m (sp0 - 224 + 32) 8 (SB + (g + 50) / 8) /\
val_mem SEGS m (sp0 - 224 + 40) 8 (SB + (g + 48) / 8) /\ val_mem SEGS m (sp0 - 224 + 48) 8 (g + 48) /\
val_mem SEGS m (sp0 - 224 + 64) 8 (SB + (cfp + 8) / 8) /\ val_mem SEGS m (sp0 - 224 + 72) 8 (cfp + 26) /\
val_mem SEGS m (sp0 - 224 + 80) 8 (nw + 8) /\ val_mem SEGS m (sp0 - 224 + 88) 8 (SB + (nw + 8) / 8) /\
val_mem SEGS m (sp0 - 224 + 96) 8 (cfp + 8).
Definition af_lcD2 : list YP09.chunk := af_lcD ++ [YP09.mkChunk 64 (CVal 8 (SOff 47 0))].
Definition AF_D2 : Z := 0xdd4.
Definition AF_D3 : Z := 0xe4c.
Definition af_newcfg (m : word -> option byte) (nw lpal fattr fgen delay nlp tidx : Z) : Prop :=
val_mem SEGS m nw 8 lpal /\ val_mem SEGS m (nw + 16) 4 fattr /\ val_mem SEGS m (nw + 20) 4 fgen /\
val_mem SEGS m (nw + 24) 2 delay /\ val_mem SEGS m (nw + 26) 2 nlp /\
(Z.land fattr 6 <> 0 -> val_mem SEGS m (nw + 28) 1 tidx).
Definition AF_D2_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (i nw : Z),
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_midx B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 [(nw, FRAME_SIZE)] -> k <= EV_FLUSH + 5 ->
blocks_bytes Sc <= blocks_bytes S + FRAME_SIZE ->
af_regs_at B regs regs1 g -> getr regs1 9 = w64 cfp -> getr regs1 24 = w64 i ->
getr regs1 23 = w64 nw -> getr regs1 10 = w64 N -> getr regs1 19 = w64 (cfp + 16) -> getr regs1 25 = w64 (SB + (cfp + 16) / 8) -> getr regs1 27 = w64 (g + 50) ->
af_locsD (mrestrict (w_H Wc) memc) (spZ regs) g cfp (Z.land fattr 4) nw ->
(Z.land fattr 1 <> 0 \/ Z.land (cg_attr s) 4 = 0) ->
(i = 1 \/ i = 2) -> nth (Z.to_nat i) (cg_frames s1) None = None -> (i = 2 -> nth 1 (cg_frames s1) None <> None) ->
In (nw, FRAME_SIZE) (ablocks B lyc Sc) ->
af_newcfg (mrestrict (w_H Wc) memc) nw lpal fattr fgen delay nlp tidx ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_D2)) memc (seg_rom SEGS)) mdc)
(af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Definition AF_D3_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (i nw nimg : Z),
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_midx B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 [(nw, FRAME_SIZE); (nimg, N)] -> k <= EV_FLUSH + 6 ->
blocks_bytes Sc <= blocks_bytes S + FRAME_SIZE + N ->
af_regs_at B regs regs1 g -> getr regs1 9 = w64 cfp -> getr regs1 24 = w64 i -> getr regs1 23 = w64 nw ->
getr regs1 19 = w64 (cfp + 16) -> getr regs1 25 = w64 (SB + (cfp + 16) / 8) -> getr regs1 27 = w64 (cfp + 26) ->
af_locsD (mrestrict (w_H Wc) memc) (spZ regs) g cfp (Z.land fattr 4) nw ->
Z.land fattr 1 <> 0 ->
(i = 1 \/ i = 2) -> nth (Z.to_nat i) (cg_frames s1) None = None -> (i = 2 -> nth 1 (cg_frames s1) None <> None) ->
In (nw, FRAME_SIZE) (ablocks B lyc Sc) -> In (nimg, N) (ablocks B lyc Sc) ->
af_newcfg (mrestrict (w_H Wc) memc) nw lpal fattr fgen delay nlp tidx ->
val_mem SEGS (mrestrict (w_H Wc) memc) (nw + 8) 8 nimg ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_D3)) memc (seg_rom SEGS)) mdc)
(af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Definition af_newblocks (N fattr nlp nw nimg npal : Z) : list (Z * Z) :=
(nw, FRAME_SIZE) :: (nimg, N) :: (if Z.land fattr 1 =? 0 then [] else [(npal, 3 * nlp)]).
Definition AF_E_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (i nw nimg npal : Z),
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_midx B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 (af_newblocks N fattr nlp nw nimg npal) -> k <= EV_FLUSH + 8 ->
af_regs_at B regs regs1 g -> getr regs1 9 = w64 cfp -> getr regs1 24 = w64 i -> getr regs1 23 = w64 nw -> getr regs1 17 = w64 (g + 92) ->
getr regs1 19 = w64 (cfp + 16) -> getr regs1 25 = w64 (SB + (cfp + 16) / 8) ->
af_locsD (mrestrict (w_H Wc) memc) (spZ regs) g cfp (Z.land fattr 4) nw ->
(Z.land fattr 1 <> 0 \/ Z.land (cg_attr s) 4 = 0) ->
(i = 1 \/ i = 2) -> nth (Z.to_nat i) (cg_frames s1) None = None -> (i = 2 -> nth 1 (cg_frames s1) None <> None) ->
In (nw, FRAME_SIZE) (ablocks B lyc Sc) ->
af_newcfg (mrestrict (w_H Wc) memc) nw (if Z.land fattr 1 =? 0 then lpal else npal) fattr fgen delay nlp tidx ->
val_mem SEGS (mrestrict (w_H Wc) memc) (nw + 8) 8 nimg ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_E)) memc (seg_rom SEGS)) mdc)
(af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Lemma af_seed : forall pc sregs d (sv : bool) lc ih wlo whi W1 (regs regs1 : bvmap 5 word) mem1 ly1 S1 md1 lya sp0 g s1 cfp
(lpal img fattr fgen delay nlp tidx : Z) more,
let E := Eimg (Ereg regs1 (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] more)) in
AR SEGS B ly1 S1 W1 mem1 md1 ->
In (g, CGIF_SIZE) (ablocks B ly1 S1) ->
afobj SEGS B ly1 S1 W1 mem1 cfp 32 ->
astk_ok TADDFRAME_STK lya sp0 -> (forall a, sp0 - TADDFRAME_STK <= a < sp0 -> apresent (w_H W1) mem1 a) ->
bv_unsigned (getr regs1 2) = sp0 - 224 - d -> (d = 0 \/ d = -224) -> 0 <= wlo -> whi <= 96 ->
regs_ok E sregs regs1 ->
regions_wf (af_regions d sv lc ih wlo whi) = true ->
Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W1) mem1) (sp0 - 224 - d)) lc ->
(sv = true -> af_frame (mrestrict (w_H W1) mem1) sp0 regs) ->
obj_at SEGS (mrestrict (w_H W1) mem1) g LAY_CGIF (tcgif_vals hw s1) -> cg_ihead s1 = ih ->
obj_at SEGS (mrestrict (w_H W1) mem1) cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
st_ok_pi SEGS VAL E (ss_af pc sregs d sv lc ih wlo whi) (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS Bxa af_SH E (mrestrict (w_H W1) mem1).
Proof.
intros pc sregs d sv lc ih wlo whi W1 regs regs1 mem1 ly1 S1 md1 lya sp0 g s1 cfp lpal img fattr fgen delay nlp tidx more E
HAR Hing HFO Hstk Hpres Hsp Hd Hwlo Hwhi HREG HWF HLC HFR HOBJ Hih HCF.
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & Hgpres & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, Hgpres, Hgh_img.
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds SEGS _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
pose proof (sep_block_frame SEGS _ LAWS ly1 S1 _ _ _ g CGIF_SIZE cid pos HAR Hing Hfin) as HdGC.
unfold zdisjoint in HdGC. cbn [fst snd] in HdGC. change (req_size CGIF_SIZE) with 96 in HdGC.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
assert (FLD : forall j o n v, nth_error LAY_CGIF j = Some (o, n) -> nth_error (tcgif_vals hw s1) j = Some v ->
val_mem SEGS (mrestrict (w_H W1) mem1) (g + o) (N.to_nat n) v /\ 0 <= v < 2 ^ (8 * Z.of_N n)).
{ intros j o n v Hj Hv. exact (obj_at_nth SEGS _ _ _ _ j (o, n) v HOBJ Hj Hv). }
pose proof (FLD 0%nat 0 8%N _ eq_refl eq_refl) as [V0 R0]. pose proof (FLD 1%nat 8 8%N _ eq_refl eq_refl) as [V1 R1].
pose proof (FLD 2%nat 16 8%N _ eq_refl eq_refl) as [V2 R2]. pose proof (FLD 3%nat 24 8%N _ eq_refl eq_refl) as [V3 R3].
pose proof (FLD 5%nat 40 4%N _ eq_refl eq_refl) as [V5 R5]. pose proof (FLD 6%nat 44 4%N _ eq_refl eq_refl) as [V6 R6].
pose proof (FLD 7%nat 48 2%N _ eq_refl eq_refl) as [V7 R7]. pose proof (FLD 8%nat 50 2%N _ eq_refl eq_refl) as [V8 R8].
pose proof (FLD 9%nat 52 2%N _ eq_refl eq_refl) as [V9 R9]. pose proof (FLD 10%nat 54 2%N _ eq_refl eq_refl) as [V10 R10].
pose proof (FLD 11%nat 56 8%N _ eq_refl eq_refl) as [V11 R11]. pose proof (FLD 12%nat 64 8%N _ eq_refl eq_refl) as [V12 _].
pose proof (FLD 13%nat 72 8%N _ eq_refl eq_refl) as [V13 R13]. pose proof (FLD 14%nat 80 8%N _ eq_refl eq_refl) as [V14 _].
pose proof (FLD 15%nat 88 4%N _ eq_refl eq_refl) as [V15 R15]. pose proof (FLD 16%nat 92 4%N _ eq_refl eq_refl) as [V16 R16].
cbn [nth_error tcgif_vals] in V0, R0, V1, R1, V2, R2, V3, R3, V5, R5, V6, R6, V7, R7, V8, R8, V9, R9, V10, R10, V11, V12, V13, R13, V14, V15, R15, V16, R16.
rewrite Hih in V16, R16.
assert (CFD : forall j o n v, nth_error LAY_FrameConfig j = Some (o, n) -> nth_error [lpal; img; fattr; fgen; delay; nlp; tidx] j = Some v ->
val_mem SEGS (mrestrict (w_H W1) mem1) (cfp + o) (N.to_nat n) v /\ 0 <= v < 2 ^ (8 * Z.of_N n)).
{ intros j o n v Hj Hv. exact (obj_at_nth SEGS _ _ _ _ j (o, n) v HCF Hj Hv). }
pose proof (CFD 0%nat 0 8%N _ eq_refl eq_refl) as [U0 Q0]. pose proof (CFD 1%nat 8 8%N _ eq_refl eq_refl) as [U1 Q1].
pose proof (CFD 2%nat 16 4%N _ eq_refl eq_refl) as [U2 Q2]. pose proof (CFD 3%nat 20 4%N _ eq_refl eq_refl) as [U3 Q3].
pose proof (CFD 4%nat 24 2%N _ eq_refl eq_refl) as [U4 Q4]. pose proof (CFD 5%nat 26 2%N _ eq_refl eq_refl) as [U5 Q5].
pose proof (CFD 6%nat 28 1%N _ eq_refl eq_refl) as [U6 Q6].
rewrite restrict_mkst_fx.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] more) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; rewrite Eimg_low by lia; apply ew_Ereg_extra).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 224 - d) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 33%nat ltac:(unfold A_TEXT; lia)) as E33. pose proof (ES 34%nat ltac:(unfold A_TEXT; lia)) as E34.
pose proof (ES 35%nat ltac:(unfold A_TEXT; lia)) as E35. pose proof (ES 36%nat ltac:(unfold A_TEXT; lia)) as E36. pose proof (ES 37%nat ltac:(unfold A_TEXT; lia)) as E37.
pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38. pose proof (ES 39%nat ltac:(unfold A_TEXT; lia)) as E39. pose proof (ES 40%nat ltac:(unfold A_TEXT; lia)) as E40.
pose proof (ES 41%nat ltac:(unfold A_TEXT; lia)) as E41. pose proof (ES 42%nat ltac:(unfold A_TEXT; lia)) as E42. pose proof (ES 43%nat ltac:(unfold A_TEXT; lia)) as E43.
pose proof (ES 44%nat ltac:(unfold A_TEXT; lia)) as E44. pose proof (ES 45%nat ltac:(unfold A_TEXT; lia)) as E45. pose proof (ES 46%nat ltac:(unfold A_TEXT; lia)) as E46.
pose proof (ES 47%nat ltac:(unfold A_TEXT; lia)) as E47. pose proof (ES 48%nat ltac:(unfold A_TEXT; lia)) as E48. pose proof (ES 49%nat ltac:(unfold A_TEXT; lia)) as E49.
pose proof (ES 50%nat ltac:(unfold A_TEXT; lia)) as E50. pose proof (ES 51%nat ltac:(unfold A_TEXT; lia)) as E51. pose proof (ES 52%nat ltac:(unfold A_TEXT; lia)) as E52.
pose proof (ES 53%nat ltac:(unfold A_TEXT; lia)) as E53.
cbn [Nat.sub nth af_extra map app firstn repeat] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49, E50, E51, E52, E53.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof pa_B_ok as HBASE.
assert (Hal2 : (sp0 - 224 - d) mod 16 = 0).
{ destruct Hd as [-> | ->]; [replace (sp0 - 224 - 0) with (sp0 + (-14) * 16) by lia | replace (sp0 - 224 - -224) with (sp0 + 0 * 16) by lia];
rewrite Z_mod_plus_full; exact Hsp0al. }
split.
- unfold ss_af, af_regions. apply pa_entry_st_ok_full; change (Ereg regs1 _) with E.
+ exact HREG.
+ exact HWF.
+ unfold af_locals, af_savedr, got_regionP, bcell_regionP, af_obj, af_cfr.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
*   cbn [base_val]. rewrite E2. split; [lia|]. split; [lia|]. split; [|exact HLC].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
*
cbn [base_val]. rewrite E2. split; [lia|]. split; [destruct sv; lia|]. split.
{ intros o Ho. apply (apresent_writable SEGS). apply Hpres. destruct sv; lia. }
destruct sv; [| constructor].
cbn [map seq Z.of_nat Pos.of_succ_nat Pos.succ Nat.add].
repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
let j := eval compute in (n - 54)%nat in let r := eval compute in (nth j af_saved 0) in
apply (chunk_ok_val SEGS E _ (sp0 - 224 - d) off 8 (SOff n 0) (bv_unsigned (ew E n)));
[ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| let HR := fresh in pose proof (bv_unsigned_in_range 64 (ew E n)) as HR; clear - HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
| cbn; lia
| replace (sp0 - 224 - d + off) with (sp0 - 8 - 8 * Z.of_nat j) by lia;
rewrite (ES n ltac:(unfold A_TEXT; lia)); cbn [Nat.sub nth af_extra map app firstn repeat]; exact (HFR eq_refl j r eq_refl) ] end.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
* rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 Bxa SB);
[cbn [sv_denot Bxa]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
*   rewrite (VB 32%nat g E32) by lia. unfold CGIF_SIZE. split; [lia|]. split; [apply andb_prop in HWF; lia|]. split.
{ intros o Ho. apply (apresent_writable SEGS). apply Hgpres. lia. }
let ck He V := (eapply (chunk_ok_val SEGS E _ g); [cbn [sv_denot]; rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V]) in
constructor; [ck E33 V0|]; constructor; [ck E34 V1|]; constructor; [ck E35 V2|]; constructor; [ck E39 V3|];
constructor; [ck E40 V5|]; constructor; [ck E41 V6|]; constructor; [ck E42 V7|]; constructor; [ck E43 V8|]; constructor; [ck E44 V9|];
constructor; [ck E45 V10|]; constructor; [apply (chunk_ok_val SEGS E _ g 56 8 _ hw); [reflexivity | clear - R11; lia | zside | exact V11]|];
constructor; [apply (chunk_ok_val SEGS E _ g 64 8 _ 0); [reflexivity | zside | zside | exact V12]|];
constructor; [ck E36 V13|]; constructor; [apply (chunk_ok_val SEGS E _ g 80 8 _ 0); [reflexivity | zside | zside | exact V14]|];
constructor; [ck E37 V15|]; constructor; [apply (chunk_ok_val SEGS E _ g 92 4 _ ih); [reflexivity | clear - R16; lia | zside | exact V16]|]; constructor.
*   rewrite (VB 46%nat cfp E46) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
let ck He V := (eapply (chunk_ok_val SEGS E _ cfp); [cbn [sv_denot]; rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V]) in
constructor; [ck E47 U0|]; constructor; [ck E48 U1|]; constructor; [ck E49 U2|]; constructor; [ck E50 U3|];
constructor; [ck E51 U4|]; constructor; [ck E52 U5|]; constructor; [ck E53 U6|]; constructor.
+ apply pairwise_disjoint_of_extents. unfold af_locals, af_savedr, got_regionP, bcell_regionP, af_obj, af_cfr, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 32%nat g E32), (VB 46%nat cfp E46) by lia. rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). cbn [base_val]. rewrite E2.
unfold CGIF_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 C1 C3 HTS Hstk0 HdGC Hflo Hfhi Hf4096 Hfceil Hfhigh Hfhigh_img HcellR HgcD HgotR. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
+ split; [|split; exact I].
cbn [f_atoms atoms_ok af_facts]. unfold afact_ok, hfactA, hfact3. cbn [af_lo af_hi af_al2].
rewrite E2, E32, E38, E46, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hg16 Hsp0al C1 C3 HTS Hstk0 Hd Hal2 Hcal Hflo Hfhi Hf4096 Hfceil Hfhigh Hfhigh_img. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, af_SH. constructor; [|constructor; [|constructor]].
+ apply (shent_ok_of_block SEGS B LAWS ly1 S1 W1 mem1 md1 E Bxa 32 g CGIF_SIZE 0 CGIF_SIZE HAR Hing).
* unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia.
* change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
+ apply (shent_ok_of_range SEGS (w_H W1) mem1 E Bxa 46 cfp 32 cfp 0 32 HRA).
* unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia. * lia. * shent_range_app.
Qed.
End h.
End e.
End c.
