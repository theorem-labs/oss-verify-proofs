(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import Utf8.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI08 YI0r UI1w UN3b UN3c UI55.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 UI5c YI0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI01 YI6c YI67 UN0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI02 YI03 YI0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI4l YI5a UI2v UI5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section zh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma st_ok_add_regionZ : forall segs E ss ms r,
st_ok segs E ss ms -> region_wf r = true -> region_ok segs E (ms_mem ms) r -> all_disjoint E r (ss_mem ss) ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof using.
intros segs E ss ms r (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hrwf Hr Hd.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [cbn; rewrite Hrwf, Hwf; reflexivity|]. split; [constructor; assumption|]. split; assumption.
Qed.
End zh.
Section zc.
Fixpoint memset_cut (b : option nat) (mlo lo : Z) (rs : smem) : smem :=
match rs with
| [] => []
| r :: rs' =>
if obase_eqb (r_base r) b && (r_lo r <? lo) && (mlo <? r_hi r) then
(if lo <? r_hi r then trim_lo r lo :: memset_cut b mlo lo rs' else memset_cut b mlo lo rs')
else r :: memset_cut b mlo lo rs'
end.
Lemma submem_memset_cut : forall b mlo lo rs, submem (memset_cut b mlo lo rs) rs.
Proof using.
intros b mlo lo rs. induction rs as [|r rs IH]; cbn [memset_cut]; [apply submem_nil|].
destruct (obase_eqb (r_base r) b && (r_lo r <? lo) && (mlo <? r_hi r)); [destruct (lo <? r_hi r)|].
- apply submem_keep; [apply subregion_trim_lo | exact IH].
- apply submem_drop. exact IH.
- apply submem_keep; [apply subregion_refl | exact IH].
Qed.
End zc.
Ltac add_regionZ HS r :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_regionZ segs E1 ss1 ms1 r) in HS;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| vm_compute; reflexivity | | ]
end.
Ltac stretch_cut HS regs2 mem2 newpc b mlo lo HS2 :=
lazymatch type of HS with st_ok ?segs ?Ec ?ssc ?msc =>
lazymatch Ec with havoc _ ?k0 ?l0 =>
let k := eval vm_compute in (k0 + length l0)%nat in
let rs := eval vm_compute in (memset_cut b mlo lo (ss_mem ssc)) in
pose proof (st_ok_after_stretch segs k Ec ssc msc regs2 mem2 rs newpc MEMSET_CLOB HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
(submem_memset_cut b mlo lo (ss_mem ssc))
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ssc rs k MEMSET_CLOB newpc) in
change (ss_after_stretch ssc rs k MEMSET_CLOB newpc) with ss2 in HS2
end end.
Definition rn_frame_chunks : list YP09.chunk := Eval vm_compute in
map (fun i => mkChunk (-104 + Z.of_nat i) (CVal 1 (SLit (nth i (YI0j.hdr13 0 0 0) 0)))) (seq 0 6) ++
[mkChunk (-98) (CVal 1 (SExt false 16 (SOff 36 0))); mkChunk (-97) (CVal 1 (SAlu ALU_SRL (SExt false 16 (SOff 36 0)) (SLit 8)));
mkChunk (-96) (CVal 1 (SExt false 16 (SOff 37 0))); mkChunk (-95) (CVal 1 (SAlu ALU_SRL (SExt false 16 (SOff 37 0)) (SLit 8))); mkChunk (-94) (CZero 3);
mkChunk (-72) (CVal 8 (SOff 23 0)); mkChunk (-64) (CVal 8 (SOff 22 0)); mkChunk (-56) (CVal 8 (SOff 21 0)); mkChunk (-48) (CVal 8 (SOff 20 0));
mkChunk (-40) (CVal 8 (SOff 19 0)); mkChunk (-32) (CVal 8 (SOff 18 0)); mkChunk (-24) (CVal 8 (SOff 9 0)); mkChunk (-16) (CVal 8 (SOff 8 0));
mkChunk (-8) (CVal 8 (SOff 1 0))].
Section rn. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable API : AllocAPI ubs0_msyms.
Definition rn_case (lo hi : Z) : Prop := Eval cbv beta delta [rn_frame_chunks] in
forall (L : layout),
forall (A : astate),
forall (regs : bvmap 5 word),
forall (mem : word → option byte),
forall (md : Model),
forall (cfgp g pgct rattr W H sgct loops : Z),
forall (gvals : list Z),
forall (f pga Npg : Z),
forall (S GCT : list Z),
forall (bq : rbound),
forall (HPRE : fn_pre ubs0_msyms (aa_MR API) RAWNEW_STK L A regs mem md),
forall (Hid : st_init_done A = true),
forall (Ha0 : getr regs 10 = Z_to_bv 64 cfgp),
forall (Hcal : cfgp mod 8 = 0),
forall (Hclo : spZ regs <= cfgp),
forall (Hchi : cfgp + 40 <= 2 ^ 63),
let cvals : list Z := [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] in
forall (Hcfg : obj_at ubs0segs mem cfgp LAY_RawConfig cvals),
forall (Hcrd : ∀ i : Z, 0 <= i < 40 → ∃ b8 : byte, mbyte ubs0segs mem (cfgp + i) = Some b8),
forall (Hobj : obj_at ubs0segs mem g LAY_CGIF gvals),
forall (Hwfn : nth_error gvals CG_wfn = Some 0),
forall (Hfile : nth_error gvals CG_file = Some f),
forall (Hgin : In (g, CGIF_SIZE) (blocks L A)),
forall (Hfin : In (f, FILE_BLOCK) (blocks L A)),
forall (HSK : sink_at ubs0_msyms mem md f S),
forall (Hroom : Z.of_nat (length S) + 1024 <= SINK_MAX),
forall (Hsp47 : spZ regs <= 2 ^ 47),
forall (Hpal : sgct ≠ 0 → In (pga, Npg) (blocks L A) ∧ Z_to_bv 64 pga = Z_to_bv 64 pgct ∧ 3 * sgct <= Npg ∧ (pga, Npg) ≠ (f, FILE_BLOCK) ∧ garr8 ubs0segs mem pga GCT ∧ 3 * sgct <= Z.of_nat (length GCT)),
forall (HRq : res_ok A bq),
forall (HRM : rawnew_room bq),
forall (HH : heap_ok (aa_MR API) L A mem md),
forall (Hra : ret_ok (getr regs 1)),
forall (Hal16 : spZ regs mod 16 = 0),
forall (Hstk0 : 0 <= RAWNEW_STK),
forall (Hceil : alloc_ceiling + RAWNEW_STK <= spZ regs),
forall (H63 : spZ regs < 2 ^ 63),
forall (Hstw : ∀ a : Z, spZ regs - RAWNEW_STK <= a < spZ regs → writable_at (ms_segs ubs0_msyms) mem a),
forall (Htp : getr regs 4 = Z_to_bv 64 (ms_tp ubs0_msyms)),
forall (Herr : errno_ok ubs0_msyms mem),
forall (Hac : 140735332483072 <= alloc_ceiling <= 140737479966720),
forall (HSTKv : RAWNEW_STK = 8304),
forall (HASv : ALLOC_STACK = 8192),
forall (HGSv : CGIF_SIZE = 96),
forall (HRSv : RAW_SIZE = 48),
forall (HDv : RAWNEW_DEPTH = 144),
forall (HFv : RAWNEW_FRAME = 112),
forall (Hg0 : 4096 <= g),
forall (Hg1 : g + CGIF_SIZE <= alloc_ceiling),
forall (Hg16 : g mod 16 = 0),
forall (HFBv : FILE_BLOCK = 1264),
forall (HWSv : WRITECB_STK = 528),
forall (Hf0 : 4096 <= f),
forall (Hf1 : f + FILE_BLOCK <= alloc_ceiling),
forall (Hf16 : f mod 16 = 0),
forall (Hsg_r : 0 <= sgct < 2 ^ (8 * Z.of_N 2)),
forall (Hat_r : 0 <= rattr < 2 ^ (8 * Z.of_N 4)),
forall (Hlp_r : 0 <= loops < 2 ^ (8 * Z.of_N 2)),
let E : env := Ereg regs (map (Z_to_bv 64) cvals ++ map (Z_to_bv 64) gvals ++ []) in
forall (HE : ∀ (n : nat) (r : reg), Z.of_nat n = bv_unsigned r → ew E n = getr regs r),
forall (HX : ∀ (j : nat) (v : Z), nth_error cvals j = Some v → ew E (32 + j) = Z_to_bv 64 v),
forall (HY : ∀ (j : nat) (v : Z), nth_error gvals j = Some v → ew E (40 + j) = Z_to_bv 64 v),
forall (HE2 : ew E 2 = getr regs 2),
forall (HE10 : ew E 10 = Z_to_bv 64 cfgp),
forall (HE33 : ew E 33 = Z_to_bv 64 g),
forall (HE38 : ew E 38 = Z_to_bv 64 sgct),
forall (HE35 : ew E 35 = Z_to_bv 64 rattr),
forall (HE39 : ew E 39 = Z_to_bv 64 loops),
forall (Hspw : bv_unsigned (getr regs 2) = spZ regs),
forall (Hsg : sgct <= 256),
forall (L2 : layout),
forall (A2 : astate),
forall (regs2 : bvmap 5 word),
forall (md2 : Model),
forall (res : Z),
forall (Hid2 : st_init_done A2 = true),
forall (Hres10 : getr regs2 10 = Z_to_bv 64 res),
forall (Hnz : res ≠ 0),
forall (Hres16 : res mod 16 = 0),
forall (b1 b2 : list (Z * Z)),
forall (Hbl2 : blocks L2 A2 = b1 ++ (res, 48) :: b2),
forall (Hblc : blocks L A = b1 ++ b2),
forall (Hwr : ∀ (blc : list (Z * Z)) (i : Z), In (res, 48) blc → 0 <= i < 48 → wr_byte RAWNEW_STK (spZ regs) [] (blocks L A) blc (res + i)),
forall (HRq2 : res_ok A2 (rb_malloc bq 48)),
forall (Hfin2 : In (f, FILE_BLOCK) (blocks L2 A2)),
forall (Hq10 : ew (havoc E 57 (map (getr regs2) CLOB)) 61 = Z_to_bv 64 res),
forall (HE2' : ew (havoc E 57 (map (getr regs2) CLOB)) 2 = getr regs 2),
forall (Hbin2 : In (res, 48) (blocks L2 A2)),
forall (Hb0 : 4096 <= res),
forall (Hb1 : res + 48 <= alloc_ceiling),
forall (Hwr' : ∀ (blc : list (Z * Z)) (i : Z), In (res, 48) blc → 0 <= i < 48 → wr_byte RAWNEW_STK (spZ regs) (sink_fp f) (blocks L A) blc (res + i)),
forall (Hgc : g + CGIF_SIZE <= res ∨ res + 48 <= g),
forall (regs3 : bvmap 5 word),
forall (Hd10 : getr regs3 10 = Z_to_bv 64 res),
forall (Hrf : res + 48 <= f ∨ f + FILE_BLOCK <= res),
forall (Henvblk : ∀ (L1 : layout) (A1 : astate) (m1 : word → option byte) (md1 : Model) (b n a : Z), heap_ok (aa_MR API) L1 A1 m1 md1 → In (b, n) (blocks L1 A1) → env_addr a → ¬ b <= a < b + n),
forall (WR : ∀ (E1 : env) (cs0 cs1 : list YP09.chunk) (lo : Z),
ew E1 61 = Z_to_bv 64 res
→ ew E1 2 = getr regs 2
→ - RAWNEW_STK <= lo
→ wr_ok E1
[{| r_base := Some 61%nat; r_lo := 0; r_hi := 48; r_wlo := 0; r_whi := 48; r_chunks := cs0 |}; {| r_base := Some 2%nat; r_lo := lo; r_hi := 0; r_wlo := lo; r_whi := 0; r_chunks := cs1 |};
{| r_base := Some 10%nat; r_lo := 0; r_hi := 40; r_wlo := 0; r_whi := 0; r_chunks := obj_chunks_gen LAY_RawConfig 32 lits_RawConfig |};
{| r_base := Some 33%nat; r_lo := 0; r_hi := CGIF_SIZE; r_wlo := 0; r_whi := 0; r_chunks := obj_chunks_gen LAY_CGIF 40 lits_CGIF |}]
RAWNEW_STK (spZ regs) (sink_fp f) (blocks L A) (blocks L2 A2)),
forall (Hranges : ∀ (j : nat) (v : Z), nth_error cvals j = Some v → 0 <= v < 2 ^ (8 * Z.of_N (nth j LAY_RawConfig (0, 8%N)).2)),
forall (Hoff : ∀ a : Z, f <= a < f + FILE_BLOCK ∨ env_addr a → 0 <= a < alloc_ceiling ∧ ¬ res <= a < res + 48),
forall (Hgf : g + CGIF_SIZE <= f ∨ f + FILE_BLOCK <= g),
forall (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)),
forall (Hgranges : ∀ (j : nat) (v : Z), nth_error gvals j = Some v → 0 <= v < 2 ^ (8 * Z.of_N (nth j LAY_CGIF (0, 8%N)).2)),
forall (Hglen : length gvals = 17%nat),
forall (HE36 : ew E 36 = Z_to_bv 64 W),
forall (HE37 : ew E 37 = Z_to_bv 64 H),
forall (HWr : 0 <= W < 65536),
forall (HHr : 0 <= H < 65536),
forall (HLr : 0 <= loops < 65536),
forall (HAr : 0 <= rattr < 2 ^ 32),
forall (regs4 : bvmap 5 word),
forall (ms2 : machine_state),
forall (HJ3 : journal ubs0_msyms (aa_MR API) RAWNEW_STK (spZ regs) (sink_fp f) L A mem md L2 A2 (ms_mem ms2) md2),
forall (HSKc : sink_at ubs0_msyms (ms_mem ms2) md2 f S),
forall (HS : st_ok (ms_segs ubs0_msyms)
(havoc (havoc (havoc E 57 (map (getr regs2) CLOB)) 73 (map (getr regs3) (10%bv :: MEMCPY_CLOB))) 85 (map (getr regs4) MEMSET_CLOB))
(mkSS (ubs0_A_cgif_raw_newgif + 272)
[SLit 0; SLit (ubs0_A_cgif_raw_newgif + 132); SOff 2 (-112); SOff 3 0; SOff 4 0; SOff 74 0; SOff 75 0; SOff 76 0; SOff 61 0; SOff 10 0; SOff 38 0;
SAlu ALU_SRL (SExt false 16 (SOff 37 0)) (SLit 8); SLit (-9); SOff 87 0; SOff 88 0; SOff 89 0; SOff 90 0; SOff 83 0;
SExt false 16 (SOff 37 0); SExt false 16 (SOff 36 0); SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
SOff 84 0; SOff 70 0; SOff 71 0; SOff 72 0]
[{| r_base := Some 61%nat; r_lo := 0; r_hi := 48; r_wlo := 0; r_whi := 48;
r_chunks := [mkChunk 0 (CVal 8 (SLit ubs0_A_cgif_writecb)); mkChunk 8 (CVal 8 (SOff 33 0)); mkChunk 16 (CVal 8 (SOff 34 0)); mkChunk 24 (CVal 4 (SOff 35 0));
mkChunk 28 (CVal 2 (SOff 36 0)); mkChunk 30 (CVal 2 (SOff 37 0)); mkChunk 32 (CVal 2 (SOff 38 0)); mkChunk 34 (CVal 2 (SOff 39 0))] |};
{| r_base := Some 2%nat; r_lo := -112; r_hi := 0; r_wlo := -112; r_whi := 0; r_chunks := rn_frame_chunks |};
{| r_base := Some 10%nat; r_lo := 0; r_hi := 40; r_wlo := 0; r_whi := 0; r_chunks := obj_chunks_gen LAY_RawConfig 32 lits_RawConfig |};
{| r_base := Some 33%nat; r_lo := 0; r_hi := CGIF_SIZE; r_wlo := 0; r_whi := 0; r_chunks := obj_chunks_gen LAY_CGIF 40 lits_CGIF |}]
None
(mkFacts [ (61%nat, mkAF 4096 (CEIL_MAX - 48) 4); (2%nat, mkAF (CEIL_MIN + RAWNEW_STK) (2^63) 4);
(10%nat, mkAF (CEIL_MIN + RAWNEW_STK) (2^63 - 40) 3); (33%nat, mkAF 4096 (CEIL_MAX - CGIF_SIZE) 4);
(38%nat, mkAF 0 65535 0); (35%nat, mkAF 0 (2^32-1) 0); (39%nat, mkAF 0 65535 0) ]
[ mkAC BC_GEU (SLit 256) (SOff 38 0) ] []))
ms2),
forall (Hk : lo <= sgct <= hi),
SR (ms_segs ubs0_msyms) {| cfg_ms := ms2; cfg_model := md2 |}
(λ c' : config,
∃ (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word → option byte) (md' : Model) (res0 : Z),
c' = {| cfg_ms := mkst regs' (getr regs 1) mem' (seg_rom ubs0segs); cfg_model := md' |}
∧ journal ubs0_msyms (aa_MR API) RAWNEW_STK (spZ regs) (sink_fp f) L A mem md L' A' mem' md'
∧ regs_preserved regs regs'
∧ st_init_done A' = true
∧ getr regs' 10 = Z_to_bv 64 res0
∧ (res0 = 0 ∧ 256 < sgct ∧ blocks L' A' = blocks L A ∧ sink_at ubs0_msyms mem' md' f S ∧ res_ok A' bq
∨ res0 ≠ 0
∧ sgct <= 256
∧ sink_at ubs0_msyms mem' md' f (S ++ YO07.raw_header W H sgct GCT rattr loops)
∧ (∃ b0 b3 : list (Z * Z), blocks L' A' = b0 ++ (res0, RAW_SIZE) :: b3 ∧ blocks L A = b0 ++ b3)
∧ obj_at ubs0segs mem' res0 LAY_Raw [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops; R_PENDING] ∧ res_ok A' (rawnew_rb bq))).
End rn.
Ltac sink_step HSK HFx Hoff Hq10 HE2 Hspw :=
cbn [ms_mem mkst] in HFx;
lazymatch type of HFx with frame_of _ _ _ ?m1 =>
lazymatch type of HSK with sink_at _ ?m0 ?mdx ?fx ?Sx =>
let Hn := fresh "HSKn" in
assert (Hn : sink_at ubs0_msyms m1 mdx fx Sx);
[ apply (sink_at_frame ubs0_msyms m0 m1 mdx fx Sx); [|exact HSK];
let a := fresh "a" in let Ha := fresh "Ha" in let Ha' := fresh "Ha'" in
intros a Ha; pose proof (Hoff a Ha) as Ha';
apply (mbyte_eq_of ubs0_msyms); apply HFx; rewrite unsigned_lit_small by lia;
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [r_base r_wlo r_whi base_val] in Hr; ew_strip_in Hr; rewrite ?Hq10, ?HE2, ?Hspw, ?unsigned_lit_small in Hr by lia; lia |]);
destruct Hin
| clear HSK; rename Hn into HSK ]
end
end.
Ltac sink_now HS HSK Hoff Hq10 HE2 Hspw :=
lazymatch type of HS with st_ok _ _ _ ?msx =>
match goal with HFx : frame_of _ _ _ (ms_mem msx) |- _ => sink_step HSK HFx Hoff Hq10 HE2 Hspw end end.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section rw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma st_ok_mem_replace : forall segs E ss ms rs,
st_ok segs E ss ms -> mem_ok segs E (ms_mem ms) rs ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof using.
intros segs E ss ms rs (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _ & H9) Hm.
unfold st_ok; cbn. repeat (split; [assumption|]). exact H9.
Qed.
Lemma region_ok_incl : forall segs E m r cs, region_ok segs E m r -> incl cs (r_chunks r) ->
region_ok segs E m (YP09.mkRegion (r_base r) (r_lo r) (r_hi r) (r_wlo r) (r_whi r) cs).
Proof using.
intros segs E m r cs (H1 & H2 & H3 & H4) Hi. unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
apply Forall_forall. intros c Hc. rewrite Forall_forall in H4. apply H4, Hi, Hc.
Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Lemma rn_walk : rn_case API 0 256 -> rawnew_specX API.
Proof using IMG.
intros RCA.
unfold rawnew_specX.
intros L A regs mem md cfgp g pgct rattr W H sgct loops gvals f pga Npg S GCT bq HPRE Hid Ha0 Hcal Hclo Hchi Hcfg Hcrd Hobj Hwfn Hfile Hgin Hfin HSK Hroom Hsp47 Hpal HRq HRM.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : RAWNEW_STK = 8304) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRSv : RAW_SIZE = 48) by reflexivity.
assert (HDv : RAWNEW_DEPTH = 144) by reflexivity. assert (HFv : RAWNEW_FRAME = 112) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md g CGIF_SIZE HH Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
assert (HFBv : FILE_BLOCK = 1264) by reflexivity. assert (HWSv : WRITECB_STK = 528) by reflexivity.
destruct (heap_blocks_range ubs0_msyms MR LAWS L A mem md f FILE_BLOCK HH Hfin ltac:(lia)) as (Hf0 & Hf1 & Hf16).
pose proof (obj_at_nth ubs0segs mem cfgp LAY_RawConfig _ 6 _ _ Hcfg eq_refl eq_refl) as [_ Hsg_r]. cbn [snd] in Hsg_r.
pose proof (obj_at_nth ubs0segs mem cfgp LAY_RawConfig _ 3 _ _ Hcfg eq_refl eq_refl) as [_ Hat_r]. cbn [snd] in Hat_r.
pose proof (obj_at_nth ubs0segs mem cfgp LAY_RawConfig _ 7 _ _ Hcfg eq_refl eq_refl) as [_ Hlp_r]. cbn [snd] in Hlp_r.
set (cvals := [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops]) in *.
set (E := Ereg regs (map (Z_to_bv 64) cvals ++ (map (Z_to_bv 64) gvals ++ []))).
assert (HE : forall n (r : reg), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (HX : forall j v, nth_error cvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HY : forall j v, nth_error gvals j = Some v -> ew E (40 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (40 + j)%nat with (32 + (length cvals + j))%nat by (subst cvals; cbn; lia). apply Ereg_vals2. exact Hj. }
assert (HE2 : ew E 2 = getr regs 2) by (apply (HE 2%nat 2%bv); reflexivity).
assert (HE10 : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (HE 10%nat 10%bv eq_refl); exact Ha0).
assert (HE33 : ew E 33 = Z_to_bv 64 g) by (apply (HX 1%nat); reflexivity).
assert (HE38 : ew E 38 = Z_to_bv 64 sgct) by (apply (HX 6%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 rattr) by (apply (HX 3%nat); reflexivity).
assert (HE39 : ew E 39 = Z_to_bv 64 loops) by (apply (HX 7%nat); reflexivity).
assert (Hspw : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
assert (HS : st_ok ubs0segs E ss_rawnew (mkst regs (Z_to_bv 64 ubs0_A_cgif_raw_newgif) mem (seg_rom ubs0segs))).
{ subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ apply (region_ok_stack ubs0segs _ mem 2 (spZ regs)); [rewrite HE2; reflexivity | lia | lia | intros a Ha; apply Hstw; lia].
+ eapply (region_ok_obj_gen ubs0segs _ mem 10 cfgp); [rewrite HE10; apply unsigned_lit_small; lia | lia | lia | exact Hcfg | reflexivity | | apply lits_RawConfig_ok | intros i Hi; lia].
intros j v Hj. apply (HX j v Hj).
+ eapply (region_ok_obj_gen ubs0segs _ mem 33 g); [rewrite HE33; apply unsigned_lit_small; lia | lia | lia | exact Hobj | reflexivity | | apply (lits_CGIF_ok gvals Hwfn Hfile) | intros i Hi; lia].
intros j v Hj. apply (HY j v Hj).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE10, HE33, !unsigned_lit_small by lia. unfold spZ in *. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE2, HE10, HE33, HE38, HE35, HE39, !unsigned_lit_small by lia. unfold spZ in *.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; lia. }
pose proof (journal_init ubs0_msyms MR RAWNEW_STK (sink_fp f) L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs0_A_cgif_raw_newgif) mem (seg_rom ubs0segs))) in HJ.
jrun LAWS ubs0tbl_ok HS HJ.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
jbranch ubs0tbl HS.
{
rewrite branch_ltu_U, U_lit, (U_atom _ 38 sgct HE38) in Hc by lia.
assert (Hsg : 256 < sgct) by (destruct (Z.ltb_spec 256 sgct); [assumption | discriminate]).
jrun LAWS ubs0tbl_ok HS HJ.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
pose proof (regs_preserved_of_st_ok _ _ _ _ regs _ HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HPR.
jreg HS (10%bv:reg) as Hr10. jreg HS (1%bv:reg) as Hr1. rewrite (HE 1%nat 1%bv eq_refl) in Hr1.
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
lazymatch type of HS with st_ok _ _ _ ?msx => exists L, A, (ms_regs msx), (ms_mem msx), md, 0 end.
rewrite Hr1, Hra. split; [reflexivity|]. split; [exact HJ|]. split; [exact HPR|]. split; [exact Hid|].
split; [exact Hr10|]. left. split; [reflexivity|]. split; [exact Hsg|]. split; [reflexivity|]. split; [|exact HRq].
cbn [ms_mem mkst] in HF, HF0.
apply (sink_at_frame ubs0_msyms mem _ md f S); [|exact HSK].
intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling) by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia]).
transitivity (mbyte ubs0segs (ms_mem ms) a); apply (mbyte_eq_of ubs0_msyms).
- apply (frame_of_win _ _ _ _ _ (spZ regs) _ HF0 eq_refl); [cbn [base_val r_base]; rewrite HE2; exact Hspw | cbn [r_wlo r_whi]; rewrite unsigned_lit_small by lia; lia].
- apply (frame_of_win _ _ _ _ _ (spZ regs) _ HF eq_refl); [cbn [base_val r_base]; rewrite HE2; exact Hspw | cbn [r_wlo r_whi]; rewrite unsigned_lit_small by lia; lia]. }
rewrite branch_ltu_U, U_lit, (U_atom _ 38 sgct HE38) in Hc by lia.
assert (Hsg : sgct <= 256) by (destruct (Z.ltb_spec 256 sgct); [discriminate | lia]). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_malloc.
{ wr_ok_tac. rewrite HE2. exact Hspw. }
jreg HS (10%bv:reg) as Hr10. jreg HS (2%bv:reg) as Hr2. rewrite HE2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hr4. jreg HS (1%bv:reg) as Hr1.
cbn [ms_mem mkst] in HF, HF0.
assert (K1 : forall a, 0 <= a < alloc_ceiling -> mbyte ubs0segs (ms_mem ms0) a = mbyte ubs0segs mem a).
{ intros a Ha'.
transitivity (mbyte ubs0segs (ms_mem ms) a); apply (mbyte_eq_of ubs0_msyms).
- apply (frame_of_win _ _ _ _ _ (spZ regs) _ HF0 eq_refl); [cbn [base_val r_base]; rewrite HE2; exact Hspw | cbn [r_wlo r_whi]; rewrite unsigned_lit_small by lia; lia].
- apply (frame_of_win _ _ _ _ _ (spZ regs) _ HF eq_refl); [cbn [base_val r_base]; rewrite HE2; exact Hspw | cbn [r_wlo r_whi]; rewrite unsigned_lit_small by lia; lia]. }
assert (HSK1 : sink_at ubs0_msyms (ms_mem ms0) md f S).
{ apply (sink_at_frame ubs0_msyms mem _ md f S); [|exact HSK]. intros a Ha. apply K1.
destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); lia]. }
pose proof (journal_restart ubs0_msyms MR _ _ _ _ _ _ _ _ _ _ _ (@nil (Z * Z)) HJ) as HJl.
eapply SR_bind.
{ eapply (jmalloc_at_res API IMG) with (n := 48) (spc := spZ regs - RAWNEW_FRAME);
[ exact HS | reflexivity | reflexivity | exact HJl | exact Hid | exact Hr10 | exact HRq | exact HRM
| rewrite Hr2; unfold spZ; f_equal; lia | lia | rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity | lia | lia | exact Hr4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & HJl2 & Hid2 & HP2 & Hres10 & Hres & Hkeep2 & Hhi2 & HRq2).
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep2, Hhi2.
assert (HJ2 : journal ubs0_msyms MR RAWNEW_STK (spZ regs) (sink_fp f) L A mem md L2 A2 mem2 md2).
{ eapply (journal_sub ubs0_msyms MR); [exact HJ | exact HJl2 | lia | lia |]. intros a (r & [] & _). }
assert (HK2 : sink_at ubs0_msyms mem2 md2 f S /\ In (f, FILE_BLOCK) (blocks L2 A2)).
{ eapply (sink_kept ubs0_msyms MR); [exact HJl2 | | exact Hfin | | exact HSK1].
- intros (r & [] & _).
- intros a _ (r & [] & _). }
destruct HK2 as [HSK2 Hfin2]. clear HJ HJl HJl2.
jafter_call2 HS 57%nat regs2 mem2 HP2 (-112) [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [rewrite HE2; exact Hspw | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 10); [rewrite HE10; apply unsigned_lit_small; lia | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_block_ro ubs0segs _ _ _ 33); [rewrite HE33; apply unsigned_lit_small; lia | exact Hgin | exact Hkeep2 | lia | lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq10. cbn [ms_regs mkst] in Hq10. rewrite Hres10 in Hq10. symmetry in Hq10.
assert (HE2' : ew (havoc E 57 (map (getr regs2) CLOB)) 2 = getr regs 2) by (ew_havoc; exact HE2).
destruct Hres as (Hnz & Hres16 & (b1 & b2 & Hbl2 & Hblc) & Hwr).
assert (Hbin2 : In (res, 48) (blocks L2 A2)) by (rewrite Hbl2; apply in_app_iff; right; left; reflexivity).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 res 48 HH2 Hbin2 ltac:(lia)) as (Hb0 & Hb1 & _).
add_fact HS 61%nat (mkAF 4096 (CEIL_MAX - 48) 4). 2:{ rewrite Hq10, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
assert (Hwr' : forall blc i, In (res, 48) blc -> 0 <= i < 48 -> wr_byte RAWNEW_STK (spZ regs) (sink_fp f) (blocks L A) blc (res + i)).
{ intros blc0 i0 Hw1 Hw2. destruct (Hwr blc0 i0 Hw1 Hw2) as [Hw|[(Hwf & _)|Hw]]; [left; exact Hw | destruct Hwf as (r & [] & _) | right; right; exact Hw]. }
jrun_to LAWS ubs0tbl_ok HS HJ2 ubs0_A_memcpy.
{ wr_ok_tac. rewrite HE2'. exact Hspw. }
jreg HS (10%bv:reg) as M10. rewrite Hq10 in M10.
jreg HS (11%bv:reg) as M11. rewrite HE10 in M11.
jreg HS (12%bv:reg) as M12. jreg HS (1%bv:reg) as M1.
assert (Hgc : g + CGIF_SIZE <= res \/ res + 48 <= g).
{ destruct (heap_sep _ _ LAWS L2 A2 _ md2 b1 (res, 48) b2 (g, CGIF_SIZE) HH2 Hbl2 ltac:(rewrite <- Hblc; exact Hgin)) as [H0|H0]; cbn [fst snd] in H0; lia. }
assert (Hcfg1 : forall i, 0 <= i < 40 -> mbyte ubs0segs (ms_mem ms1) (cfgp + i) = mbyte ubs0segs mem (cfgp + i)).
{ intros i Hi. transitivity (mbyte ubs0segs mem2 (cfgp + i)).
{ unfold mbyte. rewrite (frame_of_win _ _ _ _ _ (spZ regs) (Z_to_bv 64 (cfgp + i)) HF1 eq_refl); [reflexivity | cbn [base_val r_base]; rewrite HE2'; exact Hspw | cbn [r_wlo r_whi]; rewrite unsigned_lit_small by lia; lia]. }
rewrite (proj1 (Hhi2 (cfgp + i) ltac:(lia) ltac:(lia))).
unfold mbyte. cbn [ms_mem] in HF, HF0.
rewrite (frame_of_win _ _ _ _ _ (spZ regs) (Z_to_bv 64 (cfgp + i)) HF0 eq_refl); [| cbn [base_val r_base]; rewrite HE2; exact Hspw | cbn [r_wlo r_whi]; rewrite unsigned_lit_small by lia; lia].
rewrite (frame_of_win _ _ _ _ _ (spZ regs) (Z_to_bv 64 (cfgp + i)) HF eq_refl); [reflexivity | cbn [base_val r_base]; rewrite HE2; exact Hspw | cbn [r_wlo r_whi]; rewrite unsigned_lit_small by lia; lia]. }
eapply SR_bind.
{ eapply (jmemcpy_rd API IMG _ ubs0_memcpy) with (d := res) (src := cfgp) (n := 40);
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact M10 | exact M11 | exact M12 | exact M1
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | lia | ].
- intros i Hi. eapply present_grows; [exact HG1|]. apply (proj1 (heap_blocks _ _ LAWS L2 A2 _ md2 res 48 i HH2 Hbin2 ltac:(lia))).
- intros i Hi. cbn [ms_mem].
destruct (Hcrd i Hi) as [b Hb]. exists b. rewrite <- Hb. apply Hcfg1. exact Hi.
- intros a Ha. replace a with (res + (a - res)) by lia. apply (Hwr' (blocks L2 A2)); [exact Hbin2 | lia]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & Hd10 & Hfr3 & Hout3 & Hgr3 & Hcp3).
assert (Hrf : res + 48 <= f \/ f + FILE_BLOCK <= res).
{ pose proof (heap_sep_in2 ubs0_msyms MR LAWS L2 A2 mem2 md2 (res, 48) (f, FILE_BLOCK) HH2 Hbin2 Hfin2) as Hd.
cbn [fst snd] in Hd. destruct Hd as [Hd|Hd]; [intros E0; injection E0 as E1 E2; lia | lia | lia]. }
assert (Henvblk : forall L1 A1 m1 md1 b n a, heap_ok MR L1 A1 m1 md1 -> In (b, n) (blocks L1 A1) -> env_addr a -> ~ (b <= a < b + n)).
{ intros L1 A1 m1 md1 b n a HH1 Hin1 Hea Hr. apply blocks_In in Hin1 as (q & Hq & Hqin).
destruct (skl_env ubs0_msyms a Hea) as (Himg1 & _). assert (Hrg : 0 <= a - b < n) by lia.
apply (il_blocks IMG L1 A1 m1 md1 q n (a - b) (proj1 HH1) Hqin Hrg). rewrite Hq. replace (b + (a - b)) with a by lia. exact Himg1. }
assert (HSK3 : sink_at ubs0_msyms mem3 md2 f S).
{ cbn [ms_mem mkst] in HF1.
apply (sink_at_frame ubs0_msyms mem2 _ md2 f S); [|exact HSK2].
intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling /\ ~ (res <= a < res + 48)) by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); pose proof (Henvblk L2 A2 mem2 md2 res 48 a HH2 Hbin2 Ha); lia]).
apply (mbyte_eq_of ubs0_msyms). rewrite Hout3 by (rewrite unsigned_lit_small by lia; lia).
apply (frame_of_win _ _ _ _ _ (spZ regs) _ HF1 eq_refl); [cbn [base_val r_base]; rewrite HE2'; exact Hspw | cbn [r_wlo r_whi]; rewrite unsigned_lit_small by lia; lia]. }
jafter_stretch HS 73%nat regs3 mem3 (10%bv :: MEMCPY_CLOB) (ubs0_A_cgif_raw_newgif + 0x6c) HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr3. cbn [reg_in] in Hrr |- *. destruct (bv_eqb rr 10); [discriminate | exact Hrr]. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_outside; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HE2; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HE2; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HE2; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HE10, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HE10, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply region_kept_outside; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HE33, unsigned_lit_small by lia; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HE33, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
assert (Hraw3 : obj_at ubs0segs mem3 res LAY_RawConfig cvals).
{ eapply (obj_at_copy ubs0segs (ms_mem ms1) mem3 cfgp res LAY_RawConfig cvals 40); [| exact (proj1 LAY_RawConfig_ok) | exact Hcp3].
eapply obj_at_transport_range; [exact Hcfg | exact (proj1 LAY_RawConfig_ok) |]. intros i Hi. apply Hcfg1. exact Hi. }
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_region ubs0segs E1 ss1 ms1 (YP09.mkRegion (Some 61%nat) 0 RAW_SIZE 0 RAW_SIZE (obj_chunks_gen LAY_RawConfig 32 lits_RawConfig))) in HS;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| vm_compute; reflexivity
| eapply (region_ok_obj_gen ubs0segs _ mem3 61 res); [ew_havoc; rewrite Hq10; apply unsigned_lit_small; lia | lia | lia | exact Hraw3 | reflexivity | intros j v Hj; assert (Hlj : (j < 8)%nat) by (change 8%nat with (length cvals); apply nth_error_Some; rewrite Hj; discriminate); rewrite !ew_havoc_old by (first [apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); reflexivity | lia]); apply (HX j v Hj) | apply lits_RawConfig_ok | ]
| cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val];
rewrite !(ew_havoc_old _ 73 _ 61), !(ew_havoc_old _ 73 _ 2), !(ew_havoc_old _ 57 _ 2), !(ew_havoc_old _ 73 _ 10), !(ew_havoc_old _ 57 _ 10), !(ew_havoc_old _ 73 _ 33), !(ew_havoc_old _ 57 _ 33) by lia;
rewrite Hq10, HE2, HE10, HE33, Hspw, !unsigned_lit_small by lia; repeat split; lia ] end.
2:{ intros i Hi. apply (present_writable ubs0_msyms). cbn [ms_mem].
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HH3.
apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem3 md2 res 48 i HH3 Hbin2 ltac:(lia))). }
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 (ubs0_A_cgif_raw_newgif + 0x6c)) mem3 (seg_rom ubs0segs))) in HJ3.
assert (WR : forall E1 cs0 cs1 lo,
ew E1 61 = Z_to_bv 64 res -> ew E1 2 = getr regs 2 -> -RAWNEW_STK <= lo ->
wr_ok E1 [ YP09.mkRegion (Some 61%nat) 0 48 0 48 cs0; YP09.mkRegion (Some 2%nat) lo 0 lo 0 cs1;
YP09.mkRegion (Some 10%nat) 0 40 0 0 (obj_chunks_gen LAY_RawConfig 32 lits_RawConfig);
YP09.mkRegion (Some 33%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 40 lits_CGIF) ]
RAWNEW_STK (spZ regs) (sink_fp f) (blocks L A) (blocks L2 A2)).
{ intros E1 cs0 cs1 lo H61 H2' Hlo'.
eapply wr_ok_cons_gen with (k := 61%nat) (b := res); [reflexivity | rewrite H61; apply unsigned_lit_small; lia | cbn [r_wlo r_whi]; intros a Ha; replace a with (res + (a - res)) by lia; apply Hwr'; [exact Hbin2 | lia] |].
eapply wr_ok_cons_win; [reflexivity | rewrite H2'; exact Hspw | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
pose proof (obj_at_range _ _ _ _ _ Hcfg) as Hranges.
assert (Hoff : forall a, f <= a < f + FILE_BLOCK \/ env_addr a -> 0 <= a < alloc_ceiling /\ ~ (res <= a < res + 48)).
{ intros a Ha. destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); pose proof (Henvblk L2 A2 mem2 md2 res 48 a HH2 Hbin2 Ha); lia]. }
assert (Hsegb : segs_below ubs0segs 140735332483072 = true) by (vm_compute; reflexivity).
assert (Hgf : g + CGIF_SIZE <= f \/ f + FILE_BLOCK <= g).
{ pose proof (heap_sep_in2 ubs0_msyms MR LAWS L A mem md (g, CGIF_SIZE) (f, FILE_BLOCK) HH Hgin Hfin) as Hd.
cbn [fst snd] in Hd. destruct Hd as [Hd|Hd]; [intros E0; injection E0 as E1 E2; lia | lia | lia]. }
assert (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (rewrite Hbl2; rewrite Hblc in Hgin; apply in_app_iff in Hgin as [Hg'|Hg']; apply in_app_iff; [left; exact Hg' | right; right; exact Hg']).
pose proof (obj_at_range _ _ _ _ _ Hobj) as Hgranges.
pose proof (obj_at_length _ _ _ _ _ Hobj) as Hglen. cbn [length LAY_CGIF] in Hglen.
rename HSK3 into HSKc.
assert (HE36 : ew E 36 = Z_to_bv 64 W) by (apply (HX 4%nat); reflexivity).
assert (HE37 : ew E 37 = Z_to_bv 64 H) by (apply (HX 5%nat); reflexivity).
assert (HWr : 0 <= W < 65536) by (pose proof (Hranges 4%nat W eq_refl) as Hr; cbn [nth snd LAY_RawConfig] in Hr; change (2 ^ (8 * Z.of_N 2)) with 65536 in Hr; exact Hr).
assert (HHr : 0 <= H < 65536) by (pose proof (Hranges 5%nat H eq_refl) as Hr; cbn [nth snd LAY_RawConfig] in Hr; change (2 ^ (8 * Z.of_N 2)) with 65536 in Hr; exact Hr).
assert (HLr : 0 <= loops < 65536) by (pose proof (Hranges 7%nat loops eq_refl) as Hr; cbn [nth snd LAY_RawConfig] in Hr; change (2 ^ (8 * Z.of_N 2)) with 65536 in Hr; exact Hr).
assert (HAr : 0 <= rattr < 2 ^ 32) by (pose proof (Hranges 3%nat rattr eq_refl) as Hr; cbn [nth snd LAY_RawConfig] in Hr; change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Hr; exact Hr).
jrun_to LAWS ubs0tbl_ok HS HJ3 ubs0_A_memset. { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
jreg HS (10%bv:reg) as Ma0_m. jreg HS (11%bv:reg) as Ma1_m. jreg HS (12%bv:reg) as Ma2_m. jreg HS (1%bv:reg) as Mra_m.
rewrite HE2, Hspw in Ma0_m.
pose proof HJ3 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw_m) & _).
eapply SR_bind.
{ lazymatch type of HS with st_ok _ ?Ec _ _ =>
eapply (jmemset ubs0_msyms MR LAWS IMG ubs0_A_memset ubs0_memset Ec _ _ RAWNEW_STK (spZ regs) (sink_fp f) L A mem md L2 A2 _ (spZ regs + -103) 0 12) end;
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact Ma0_m | exact Ma1_m | exact Ma2_m | exact Mra_m
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw_m; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs4 & mem4 & -> & HJ_m & Hd10_m & Hfr_m & Hout_m & Hgr_m & Hzero_m).
clear HJ3. rename HJ_m into HJ3.
lazymatch type of HSKc with sink_at _ ?m0 ?mdx ?fx ?Sx =>
assert (HSKm : sink_at ubs0_msyms mem4 mdx fx Sx);
[ apply (sink_at_frame ubs0_msyms m0 mem4 mdx fx Sx); [|exact HSKc];
intros a Ha; pose proof (Hoff a Ha) as Ha'; apply (mbyte_eq_of ubs0_msyms); apply Hout_m; rewrite unsigned_lit_small by lia; lia
| clear HSKc; rename HSKm into HSKc ] end.
stretch_cut HS regs4 mem4 (ubs0_A_cgif_raw_newgif + 0x84) (Some 2%nat) (-103) (-91) HS2.
specialize (HS2 Hfr_m).
match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end.
{ repeat (apply Forall_cons;
[ eapply region_kept_out; [exact Hout_m | exact Hgr_m | | | | cbn; lia | cbn; lia];
cbn [r_base r_lo r_hi base_val]; ew_strip; rewrite ?Hq10, ?HE2, ?Hspw, ?HE10, ?HE33, ?unsigned_lit_small by lia;
first [lia | intros a Ha; lia] |]).
apply Forall_nil. }
clear HS. rename HS2 into HS.
pose proof HJ3 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw_r) & _).
lazymatch type of HS with st_ok ?sg ?Ec ?ssc ?msc =>
let rs' := eval vm_compute in (match ss_mem ssc with
| r0 :: f' :: rest => r0 :: YP09.mkRegion (Some 2%nat) (-112) 0 (-112) 0 (mkChunk (-94) (CZero 3) :: r_chunks f') :: rest
| _ => [] end) in
pose proof (st_ok_mem_ok _ _ _ _ HS) as (Hwf0 & Hok0 & Hpd0);
apply (st_ok_mem_replace sg Ec ssc msc rs') in HS;
[ let v2 := eval vm_compute in (mkSS (ss_pc ssc) (ss_regs ssc) rs' (ss_resv ssc) (ss_facts ssc)) in
change (mkSS (ss_pc ssc) (ss_regs ssc) rs' (ss_resv ssc) (ss_facts ssc)) with v2 in HS | ] end.
2:{ split; [vm_compute; reflexivity|]. split.
- cbn [ss_mem] in Hok0. rewrite !Forall_cons_iff in Hok0. destruct Hok0 as (Hr0 & HrF & Hrc & Hrg & _).
rewrite !Forall_cons_iff. split; [exact Hr0|]. split; [|split; [exact Hrc|split; [exact Hrg|constructor]]].
unfold region_ok in HrF |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val ms_mem mkst] in HrF |- *.
destruct HrF as (_ & HbF & _ & HchF). ew_strip_in HbF. ew_strip_in HchF. ew_strip. rewrite ?HE2, ?Hspw in HbF, HchF |- *.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw_r; lia|].
apply Forall_cons; [|exact HchF].
intros i Hi. cbn [c_len cv_len c_off c_val] in Hi |- *. exists (Z_to_bv 8 0). split; [reflexivity|].
replace (spZ regs + -94 + i) with (spZ regs + -103 + (9 + i)) by lia. apply Hzero_m. lia.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_strip.
rewrite ?Hq10, ?HE2, ?Hspw, ?HE10, ?HE33, ?unsigned_lit_small by lia. repeat split; lia. }
clear Hwf0 Hok0 Hpd0.
jrun_to LAWS ubs0tbl_ok HS HJ3 (ubs0_A_cgif_raw_newgif + 0x110). { wr_norm. apply WR; [ew_strip; exact Hq10 | ew_strip; exact HE2 | lia]. }
sink_now HS HSKc Hoff Hq10 HE2 Hspw.
jreg HS (12%bv:reg) as Hx12.
lazymatch type of HS with st_ok _ _ _ ?msc =>
assert (Hx12' : getr (ms_regs msc) 12%bv = Z_to_bv 64 (-9)) by (cbn [ms_regs] in Hx12 |- *; rewrite Hx12; apply bv_eq; vm_compute; reflexivity) end.
pin_reg HS (12%bv:reg) (-9) Hx12'. clear Hx12 Hx12'.
lazymatch type of HS with st_ok ?sg ?Ec ?ssc ?msc =>
let rs' := eval vm_compute in (match ss_mem ssc with
| r0 :: f' :: rest => r0 :: YP09.mkRegion (r_base f') (r_lo f') (r_hi f') (r_wlo f') (r_whi f') rn_frame_chunks :: rest
| _ => [] end) in
pose proof (st_ok_mem_ok _ _ _ _ HS) as (Hwf0 & Hok0 & Hpd0);
apply (st_ok_mem_replace sg Ec ssc msc rs') in HS;
[ let v2 := eval vm_compute in (mkSS (ss_pc ssc) (ss_regs ssc) rs' (ss_resv ssc) (ss_facts ssc)) in
change (mkSS (ss_pc ssc) (ss_regs ssc) rs' (ss_resv ssc) (ss_facts ssc)) with v2 in HS | ] end.
2:{ split; [vm_compute; reflexivity|]. split.
- cbn [ss_mem] in Hok0. rewrite !Forall_cons_iff in Hok0. destruct Hok0 as (Hr0 & HrF & Hrc & Hrg & _).
rewrite !Forall_cons_iff. split; [exact Hr0|]. split; [|split; [exact Hrc|split; [exact Hrg|constructor]]].
refine (region_ok_incl _ _ _ _ _ HrF _).
intros c Hc. cbn [In r_chunks] in Hc |- *.
repeat (destruct Hc as [<- | Hc]; [repeat first [left; reflexivity | right] |]). destruct Hc.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_strip.
rewrite ?Hq10, ?HE2, ?Hspw, ?HE10, ?HE33, ?unsigned_lit_small by lia. repeat split; lia. }
clear Hwf0 Hok0 Hpd0.
refine (RCA L A regs mem md cfgp g pgct rattr W H sgct loops gvals f pga Npg S GCT bq HPRE Hid Ha0 Hcal Hclo Hchi Hcfg Hcrd Hobj Hwfn Hfile Hgin Hfin HSK Hroom Hsp47 Hpal HRq HRM HH Hra Hal16 Hstk0 Hceil H63 Hstw Htp Herr Hac HSTKv HASv HGSv HRSv HDv HFv Hg0 Hg1 Hg16 HFBv HWSv Hf0 Hf1 Hf16 Hsg_r Hat_r Hlp_r HE HX HY HE2 HE10 HE33 HE38 HE35 HE39 Hspw Hsg L2 A2 regs2 md2 res Hid2 Hres10 Hnz Hres16 b1 b2 Hbl2 Hblc Hwr HRq2 Hfin2 Hq10 HE2' Hbin2 Hb0 Hb1 Hwr' Hgc regs3 Hd10 Hrf Henvblk WR Hranges Hoff Hgf Hgin2 Hgranges Hglen HE36 HE37 HWr HHr HLr HAr regs4 _ HJ3 HSKc HS _). lia.
Qed.
End S.
End rw.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
