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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChb ACgw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Class af_paramsX := { afx_path : Z; afx_pf : Z }.
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
Context {AX : af_paramsX}.
#[local] Notation path := (@afx_path AX).
#[local] Notation pf := (@afx_pf AX).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition af_objX (ih wlo whi : Z) : YP09.region :=
YP09.mkRegion (Some 32%nat) 0 CGIF_SIZE wlo whi
[YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0));
YP09.mkChunk 24 (CVal 8 (SOff 39 0)); YP09.mkChunk 40 (CVal 4 (SOff 40 0)); YP09.mkChunk 44 (CVal 4 (SOff 41 0));
YP09.mkChunk 48 (CVal 2 (SOff 42 0)); YP09.mkChunk 50 (CVal 2 (SOff 43 0)); YP09.mkChunk 52 (CVal 2 (SOff 44 0));
YP09.mkChunk 54 (CVal 2 (SOff 45 0)); YP09.mkChunk 56 (CVal 8 (SLit hw)); YP09.mkChunk 64 (CVal 8 (SLit 0));
YP09.mkChunk 72 (CVal 8 (SOff 36 0)); YP09.mkChunk 80 (CVal 8 (SLit pf)); YP09.mkChunk 88 (CVal 4 (SOff 37 0));
YP09.mkChunk 92 (CVal 4 (SLit ih))].
Definition af_regionsX (d : Z) (sv : bool) (lc : list YP09.chunk) (ih wlo whi : Z) : smem :=
[af_locals d lc; af_savedr d sv; got_regionP; bcell_regionP 38; af_objX ih wlo whi; af_cfr].
Definition ss_afX (pc : Z) (sregs : list sv) (d : Z) (sv : bool) (lc : list YP09.chunk) (ih wlo whi : Z) : sstate :=
mkSS pc sregs (af_regionsX d sv lc ih wlo whi) None af_facts.
Definition FPn (g : Z) : list (Z * Z) := [(g + 88, g + 92)].
Definition FPb (g : Z) (s : cgif_st) (N : Z) : list (Z * Z) := ablocks_fp (cgif_blocks g s N) ++ asink_fp pf.
Section f.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Definition af_cxS (B : asyms) ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (g cfp : Z) (s : cgif_st) (N : Z)
(lpal lpa img fattr fgen delay nlp tidx : Z) (rest : list (Z * Z)) : Prop :=
afn_pre SEGS B TADDFRAME_STK ly S W regs mem md ch /\
In (raZ regs :: spine ch) CTX /\ Z.of_nat (length (frames S)) <= 7 /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) /\
getr regs 10 = w64 g /\ getr regs 11 = w64 cfp /\
afobj SEGS B ly S W mem cfp 32 /\
obj_at SEGS (mrestrict (w_H W) mem) cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] /\
xcgif_at SEGS wfn path hw pf (mrestrict (w_H W) mem) g s /\ cgif_wf s N /\
Z_to_bv 64 lpa = Z_to_bv 64 lpal /\
Permutation (ablocks B ly S) (cgif_blocks g s N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) /\
st_nev S + EV_ADDFRAME <= EV_MAX /\ blocks_bytes S + LIVE_ADDFRAME <= LIVE_MAX.
Definition af_cxV (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (md : Model) (s : cgif_st) (N img fattr lpa nlp : Z) (rest : list (Z * Z))
(GPAL IMG LPAL : list Z) (gs : YO07.gif_st) : Prop :=
pf <> 0 /\ In (pf, FILE_BLOCK) rest /\
cgif_relA SEGS K (rdW W mem) md s pf N GPAL gs /\
Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N <= SINK_MAX /\
garr8 SEGS (rdW W mem) img IMG /\ Z.of_nat (length IMG) = N /\
(Z.land fattr 1 <> 0 -> garr8 SEGS (rdW W mem) lpa LPAL /\ Z.of_nat (length LPAL) = 3 * nlp) /\
mo_ok MT S (xm_addframe XN N).
Definition af_cxX (B : asyms) ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (g cfp : Z) (s : cgif_st) (N : Z)
(lpal lpa img fattr fgen delay nlp tidx : Z) (rest : list (Z * Z)) (GPAL IMG LPAL : list Z) (gs : YO07.gif_st) : Prop :=
af_cxS B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest /\
af_cxV ly S W mem md s N img fattr lpa nlp rest GPAL IMG LPAL gs.
Definition af_xout (gs gsF : YO07.gif_st) (N : Z) : Prop :=
Z.of_nat (length (concat (YO07.s_out gsF))) <= Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N.
Definition af_postX (B : asyms) ly S W (regs : bvmap 5 word) mem md (g : Z) (s : cgif_st) (N img fattr lpa nlp : Z) (rest : list (Z * Z))
(GPAL : list Z) (gs gsF : YO07.gif_st) (kf : Z) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TADDFRAME_STK (spZ regs) (FPb g s N) ly S W mem md [] ly' S' W' mem' md' kf /\
aregs_preserved regs regs' /\
exists s' : cgif_st,
xcgif_at SEGS wfn path hw pf (mrestrict (w_H W') mem') g s' /\ cgif_wf s' N /\
cg_W s' = cg_W s /\ cg_H s' = cg_H s /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\
cg_gen s' = cg_gen s /\ cg_ngp s' = cg_ngp s /\ cg_pal s' = cg_pal s /\
Permutation (ablocks B ly' S') (cgif_blocks g s' N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) /\
(forall b, In b (cgif_blocks g s' N) ->
aftok (FPb g s N) (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TADDFRAME_STK (spZ regs) (FPb g s N) (ablocks B ly S) blc ly' [] (fst b + i)) /\
cgif_relA SEGS K (rdW W' mem') md' s' pf N GPAL gsF /\
af_xout gs gsF N /\
mo_le MT S S' (xn_addframe XN N).
Lemma af_postX_mono : forall B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF kf kf' W' c',
af_postX B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF kf W' c' -> kf <= kf' ->
af_postX B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF kf' W' c'.
Proof.
intros B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF kf kf' W' c' (ly' & S' & regs' & mem' & md' & Hc & HJ & HP & HQ) Hle.
exists ly', S', regs', mem', md'. split; [exact Hc|]. split; [|split; [exact HP | exact HQ]].
eapply (ajournal_mono_k SEGS B); [exact HJ | lia].
Qed.
Definition af_newtokX (B : asyms) ly S (regs : bvmap 5 word) (g : Z) (s : cgif_st) (N : Z) (b : Z * Z) : Prop :=
aftok (FPb g s N) (ablocks B ly S) b /\
forall blc lyq ownq i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TADDFRAME_STK (spZ regs) (FPb g s N) (ablocks B ly S) blc lyq ownq (fst b + i).
Definition af_midX (B : asyms) ly S W (regs : bvmap 5 word) mem md (g cfp : Z) (s : cgif_st) (N img fattr lpa nlp : Z) (rest : list (Z * Z))
lyc Sc (Wc : world SEGS) memc mdc (k : Z) (s1 : cgif_st) : Prop :=
ajournal SEGS B TADDFRAME_STK (spZ regs) (FPb g s N) ly S W mem md [] lyc Sc Wc memc mdc k /\ 0 <= k /\
af_frame (mrestrict (w_H Wc) memc) (spZ regs) regs /\
xcgif_at SEGS wfn path hw pf (mrestrict (w_H Wc) memc) g s1 /\ af_obj_ok s s1 N /\
Permutation (ablocks B lyc Sc) (cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest) /\
(forall b, In b (cgif_blocks g s1 N) -> In b (cgif_blocks g s N) \/ af_newtokX B ly S regs g s N b).
Definition af_midxX (B : asyms) ly S W (regs : bvmap 5 word) mem md (g cfp : Z) (s : cgif_st) (N img fattr lpa nlp : Z) (rest : list (Z * Z))
lyc Sc (Wc : world SEGS) memc mdc (k : Z) (s1 : cgif_st) (X : list (Z * Z)) : Prop :=
ajournal SEGS B TADDFRAME_STK (spZ regs) (FPb g s N) ly S W mem md [] lyc Sc Wc memc mdc k /\ 0 <= k /\
af_frame (mrestrict (w_H Wc) memc) (spZ regs) regs /\
xcgif_at SEGS wfn path hw pf (mrestrict (w_H Wc) memc) g s1 /\ af_obj_ok s s1 N /\
Permutation (ablocks B lyc Sc) (cgif_blocks g s1 N ++ X ++ af_cblocks img N fattr lpa nlp rest) /\
(forall b, In b (cgif_blocks g s1 N) -> In b (cgif_blocks g s N) \/ af_newtokX B ly S regs g s N b) /\
(forall b, In b X -> af_newtokX B ly S regs g s N b).
Lemma af_midxX_nil : forall B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1,
af_midX B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 ->
af_midxX B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 [].
Proof. intros * (H1 & H2 & H3 & H4 & H5 & H6 & H7). repeat (split; [assumption|]). intros b []. Qed.
Definition af_xmtr (S Sc : astate) (N needM needN : Z) : Prop :=
exists acc, 0 <= acc /\ mo_le MT S Sc acc /\ acc + needM <= xm_addframe XN N /\ acc + needN <= xn_addframe XN N.
Definition af_xret (S Sc : astate) (m : word -> option byte) (md : Model) (s1 : cgif_st) (N : Z) (GPAL : list Z) (gs gsF : YO07.gif_st) : Prop :=
cgif_relA SEGS K m md s1 pf N GPAL gsF /\ af_xout gs gsF N /\ af_xmtr S Sc N 0 0.
Definition af_xretc (S Sc : astate) (m : word -> option byte) (md : Model) (s1 : cgif_st) (N : Z) (GPAL : list Z) (gs gsF : YO07.gif_st) (v : Z) : Prop :=
rc_int v = YO07.s_cur gsF /\ cgif_occ s1 gsF /\ asink_at SEGS K m md pf (concat (YO07.s_out gsF)) /\
(cgif_live gsF -> af_xlive SEGS m s1 N GPAL gsF) /\ af_xout gs gsF N /\ af_xmtr S Sc N 0 0.
Lemma af_xretc_ret : forall S Sc m md s1 N GPAL gs gsF v,
af_xretc S Sc m md s1 N GPAL gs gsF v -> af_xret S Sc m md (cl_set_cur s1 v) N GPAL gs gsF.
Proof.
intros S Sc m md s1 N GPAL gs gsF v (Hv & Hocc & Hsink & Hlive & Hout & Hm). split; [| split; [exact Hout | exact Hm]].
apply (proj2 (cgif_relA_split SEGS K m md (cl_set_cur s1 v) pf N GPAL gsF)).
split; [split; [exact Hv | apply (proj2 (cgif_occ_set_cur s1 v gsF)); exact Hocc]|].
split; [exact Hsink|]. intros Hl. apply (proj2 (af_xlive_set_cur SEGS m s1 N GPAL gsF v)). exact (Hlive Hl).
Qed.
Definition AF_RET_stmtX (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 GPAL IMG LPAL gs gsF,
af_cxX B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_midX B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= EV_ADDFRAME ->
af_regs_ret B regs regs1 g ->
af_xret S Sc (rdW Wc memc) mdc s1 N GPAL gs gsF ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_RET)) memc (seg_rom SEGS)) mdc)
(af_postX B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME).
Definition AF_RETC_stmtX (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (v : Z) GPAL IMG LPAL gs gsF,
af_cxX B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_midX B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= EV_ADDFRAME ->
af_regs_ret B regs regs1 g -> bv_unsigned (getr regs1 23) mod 2 ^ 32 = v ->
af_xretc S Sc (rdW Wc memc) mdc s1 N GPAL gs gsF v ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_RETC)) memc (seg_rom SEGS)) mdc)
(af_postX B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME).
End f.
Definition xs_880 (ih : Z) : sstate :=
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
{| c_off := 72; YP09.c_val := CVal 8 (SOff 36 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SLit pf) |}; {| c_off := 88; YP09.c_val := CVal 4 (SOff 37 0) |};
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
Definition xs_OK (ih : Z) : sstate :=
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
{| c_off := 80; YP09.c_val := CVal 8 (SLit pf) |};
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
Definition xs_B (ih ho : Z) (hd : nat) : sstate :=
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
{| c_off := 72; YP09.c_val := CVal 8 (SOff 36 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SLit pf) |}; {| c_off := 88; YP09.c_val := CVal 4 (SOff 37 0) |}; {| c_off := 92; YP09.c_val := CVal 4 (SLit ih) |}]
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
Definition xs_C (ih ho : Z) (hd : nat) : sstate :=
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
{| c_off := 72; YP09.c_val := CVal 8 (SOff 36 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SLit pf) |}; {| c_off := 88; YP09.c_val := CVal 4 (SOff 37 0) |}; {| c_off := 92; YP09.c_val := CVal 4 (SLit ih) |}]
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
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Lemma af_seedX : forall pc sregs d (sv : bool) lc ih wlo whi W1 (regs regs1 : bvmap 5 word) mem1 ly1 S1 md1 lya sp0 g s1 cfp
(lpal img fattr fgen delay nlp tidx : Z) more,
let E := Eimg (Ereg regs1 (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] more)) in
AR SEGS B ly1 S1 W1 mem1 md1 ->
In (g, CGIF_SIZE) (ablocks B ly1 S1) ->
afobj SEGS B ly1 S1 W1 mem1 cfp 32 ->
astk_ok TADDFRAME_STK lya sp0 -> (forall a, sp0 - TADDFRAME_STK <= a < sp0 -> apresent (w_H W1) mem1 a) ->
bv_unsigned (getr regs1 2) = sp0 - 224 - d -> (d = 0 \/ d = -224) -> 0 <= wlo -> whi <= 96 ->
regs_ok E sregs regs1 ->
regions_wf (af_regionsX d sv lc ih wlo whi) = true ->
Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W1) mem1) (sp0 - 224 - d)) lc ->
(sv = true -> af_frame (mrestrict (w_H W1) mem1) sp0 regs) ->
obj_at SEGS (mrestrict (w_H W1) mem1) g LAY_CGIF (xcgif_vals path hw pf s1) -> cg_ihead s1 = ih ->
obj_at SEGS (mrestrict (w_H W1) mem1) cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
st_ok_pi SEGS VAL E (ss_afX pc sregs d sv lc ih wlo whi) (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS)))
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
assert (FLD : forall j o n v, nth_error LAY_CGIF j = Some (o, n) -> nth_error (xcgif_vals path hw pf s1) j = Some v ->
val_mem SEGS (mrestrict (w_H W1) mem1) (g + o) (N.to_nat n) v /\ 0 <= v < 2 ^ (8 * Z.of_N n)).
{ intros j o n v Hj Hv. exact (obj_at_nth SEGS _ _ _ _ j (o, n) v HOBJ Hj Hv). }
pose proof (FLD 0%nat 0 8%N _ eq_refl eq_refl) as [V0 R0]. pose proof (FLD 1%nat 8 8%N _ eq_refl eq_refl) as [V1 R1].
pose proof (FLD 2%nat 16 8%N _ eq_refl eq_refl) as [V2 R2]. pose proof (FLD 3%nat 24 8%N _ eq_refl eq_refl) as [V3 R3].
pose proof (FLD 5%nat 40 4%N _ eq_refl eq_refl) as [V5 R5]. pose proof (FLD 6%nat 44 4%N _ eq_refl eq_refl) as [V6 R6].
pose proof (FLD 7%nat 48 2%N _ eq_refl eq_refl) as [V7 R7]. pose proof (FLD 8%nat 50 2%N _ eq_refl eq_refl) as [V8 R8].
pose proof (FLD 9%nat 52 2%N _ eq_refl eq_refl) as [V9 R9]. pose proof (FLD 10%nat 54 2%N _ eq_refl eq_refl) as [V10 R10].
pose proof (FLD 11%nat 56 8%N _ eq_refl eq_refl) as [V11 R11]. pose proof (FLD 12%nat 64 8%N _ eq_refl eq_refl) as [V12 _].
pose proof (FLD 13%nat 72 8%N _ eq_refl eq_refl) as [V13 R13]. pose proof (FLD 14%nat 80 8%N _ eq_refl eq_refl) as [V14 R14].
pose proof (FLD 15%nat 88 4%N _ eq_refl eq_refl) as [V15 R15]. pose proof (FLD 16%nat 92 4%N _ eq_refl eq_refl) as [V16 R16].
cbn [nth_error xcgif_vals] in V0, R0, V1, R1, V2, R2, V3, R3, V5, R5, V6, R6, V7, R7, V8, R8, V9, R9, V10, R10, V11, V12, V13, R13, V14, R14, V15, R15, V16, R16.
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
- unfold ss_afX, af_regionsX. apply pa_entry_st_ok_full; change (Ereg regs1 _) with E.
+ exact HREG.
+ exact HWF.
+ unfold af_locals, af_savedr, got_regionP, bcell_regionP, af_objX, af_cfr.
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
constructor; [ck E36 V13|]; constructor; [apply (chunk_ok_val SEGS E _ g 80 8 _ pf); [reflexivity | clear - R14; lia | zside | exact V14]|];
constructor; [ck E37 V15|]; constructor; [apply (chunk_ok_val SEGS E _ g 92 4 _ ih); [reflexivity | clear - R16; lia | zside | exact V16]|]; constructor.
*   rewrite (VB 46%nat cfp E46) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
let ck He V := (eapply (chunk_ok_val SEGS E _ cfp); [cbn [sv_denot]; rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V]) in
constructor; [ck E47 U0|]; constructor; [ck E48 U1|]; constructor; [ck E49 U2|]; constructor; [ck E50 U3|];
constructor; [ck E51 U4|]; constructor; [ck E52 U5|]; constructor; [ck E53 U6|]; constructor.
+ apply pairwise_disjoint_of_extents. unfold af_locals, af_savedr, got_regionP, bcell_regionP, af_objX, af_cfr, extent_of_region.
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
