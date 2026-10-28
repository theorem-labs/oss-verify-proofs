(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YN32 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b UN3c
YI06 UI5b YI09 YI08 YI0t YI0r YI0o YI0s YI6a YI61 UI3n UI3o .
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0u UI30.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac inl' := repeat (first [ left; reflexivity | right ]).
Ltac inl := cbv; inl'.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition TPC_SW2 : Z := ubs0_A_LZW_GenerateStream + 0x504.
Definition tms_facts (map : bool) : list (nat * afact) :=
[ (10%nat, mkAF 0 4095 0); (12%nat, mkAF 4096 CEIL_MAX 0); (13%nat, mkAF 0 4095 0); (14%nat, mkAF 4096 CEIL_MAX 1); (17%nat, mkAF 4096 CEIL_MAX 1);
(22%nat, mkAF 1 99999999 0); (23%nat, mkAF 0 8190 0);
(44%nat, mkAF 4096 CEIL_MAX 1); (45%nat, mkAF 0 255 0); (46%nat, mkAF 0 2046 0); (47%nat, mkAF 0 4095 0); (48%nat, mkAF 4096 CEIL_MAX 0);
(50%nat, mkAF 4096 CEIL_MAX 1) ]
++ (if map then [ (49%nat, mkAF 4096 CEIL_MAX 1) ] else []).
Definition tms_X : sv := SAluw ALU_ADD (SMd M_MUL (SOff 46%nat (-1)) (SOff 20%nat 0)) (SLit 0).
Definition tms_Y : sv := SAluw ALU_ADD (SAlu ALU_ADD tms_X (SOff 45%nat 0)) (SLit 0).
Definition tms_ROW : sv := SMdw M_MUL (SOff 43%nat (-1)) (SOff 20%nat 0).
Definition tms_alias (map : bool) : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 37%nat 0) (SAlu ALU_SLL (SOff 41%nat 0) (SLit 1)), SOff 44%nat 0);
(SAlu ALU_ADD (SOff 34%nat 0) (SOff 13%nat 0), SOff 48%nat 0);
(SAlu ALU_ADD (SOff 35%nat 0) (SOff 23%nat 0), SOff 14%nat 0);
(SAlu ALU_ADD (SAlu ALU_SLL tms_ROW (SLit 1)) (SOff 36%nat 0), SOff 50%nat 0) ]
++ (if map then [ (SAlu ALU_ADD (SOff 36%nat 0) (SAlu ALU_SLL tms_Y (SLit 1)), SOff 49%nat 0) ] else []).
Definition tms_conds_full : list acond :=
[ mkAC BC_GEU (SOff 44%nat 0) (SOff 37%nat 0); mkAC BC_NE (SAlu ALU_SRL (SOff 42%nat 0) (SLit 12)) (SLit 0) ].
Definition tms_conds_map : list acond :=
[ mkAC BC_GEU (SOff 44%nat 0) (SOff 37%nat 0); mkAC BC_EQ (SAlu ALU_SRL (SOff 42%nat 0) (SLit 12)) (SLit 0);
mkAC BC_NE (SOff 46%nat 0) (SLit 0);
mkAC BC_EQ (SMdw M_MUL (SOff 46%nat (-1)) (SOff 20%nat 0)) (SMd M_MUL (SOff 46%nat (-1)) (SOff 20%nat 0));
mkAC BC_EQ (SAluw ALU_ADD tms_X (SOff 45%nat 0)) (SAlu ALU_ADD tms_X (SOff 45%nat 0));
mkAC BC_GEU (SOff 49%nat 0) (SOff 36%nat 0);
mkAC BC_NE (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 49%nat 0) (SOff 36%nat 0)) (SAlu ALU_SLT tms_Y (SLit 0))) (SLit 1)) (SLit 0) ].
Definition tms_conds_first : list acond :=
[ mkAC BC_GEU (SOff 44%nat 0) (SOff 37%nat 0); mkAC BC_EQ (SAlu ALU_SRL (SOff 42%nat 0) (SLit 12)) (SLit 0);
mkAC BC_EQ (SOff 46%nat 0) (SLit 0); mkAC BC_EQ (SOff 47%nat 0) (SLit 0); mkAC BC_GEU (SOff 48%nat 0) (SOff 34%nat 0); mkAC BC_GEU (SOff 14%nat 0) (SOff 35%nat 0) ].
Definition tms_conds_sw : list acond :=
[ mkAC BC_GEU (SOff 44%nat 0) (SOff 37%nat 0); mkAC BC_EQ (SAlu ALU_SRL (SOff 42%nat 0) (SLit 12)) (SLit 0);
mkAC BC_EQ (SOff 46%nat 0) (SLit 0); mkAC BC_NE (SOff 47%nat 0) (SLit 0);
mkAC BC_EQ tms_ROW (SMd M_MUL (SOff 43%nat (-1)) (SOff 20%nat 0));
mkAC BC_GEU (SOff 50%nat 0) (SOff 36%nat 0);
mkAC BC_NE (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 50%nat 0) (SOff 36%nat 0)) (SAlu ALU_SLT tms_ROW (SLit 0))) (SLit 1)) (SLit 0) ].
Definition tms_img1 : YP09.region := YP09.mkRegion (Some 12%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 45%nat 0))].
Definition tms_regions_full : smem := [ regw 44 2 ].
Definition tms_regions_map : smem := [ regw 44 2; tms_img1; reg16 17 46 false; regw 49 2 ].
Definition tms_regions_first : smem := [ regw 44 2; tms_img1; reg16 17 46 false; reg16 14 47 true; regw 48 1 ].
Definition tms_regions_sw : smem := [ regw 44 2; tms_img1; reg16 17 46 false; reg16 14 47 false ].
Definition ss_tms_full : sstate := tlzw_ss TPC_MISS sr_atoms true tms_regions_full (tms_facts false) tms_conds_full (tms_alias false).
Definition ss_tms_map : sstate := tlzw_ss TPC_MISS sr_atoms true tms_regions_map (tms_facts true) tms_conds_map (tms_alias true).
Definition ss_tms_first : sstate := tlzw_ss TPC_MISS sr_atoms true tms_regions_first (tms_facts false) tms_conds_first (tms_alias false).
Definition ss_tms_sw : sstate := tlzw_ss TPC_MISS sr_atoms true tms_regions_sw (tms_facts false) tms_conds_sw (tms_alias false).
Definition tmiss_pre (cx : lzw_tcx) (regs : bvmap 5 word) (s1 q : Z) : Prop :=
getr regs 22 = Z_to_bv 64 s1 /\ getr regs 10 = Z_to_bv 64 q /\ getr regs 17 = Z_to_bv 64 (y_lm cx + 2 * q) /\
getr regs 14 = Z_to_bv 64 (y_li cx + 2 * q) /\ getr regs 12 = Z_to_bv 64 (y_img cx + s1) /\
getr regs 23 = Z_to_bv 64 (2 * q) /\ getr regs 13 = Z_to_bv 64 q.
Definition tsw2_pre (cx : lzw_tcx) (X : lzw_abs) (s1 q c : Z) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
let 'mkLA TI LM LI TM s lp dp mp Cn R := X in
tlzw_regs_fix regs cx /\ gen_at mem cx (lp + 1) dp mp /\
ttables_at mem cx (mkLA TI LM LI (zero_range TM (Z.to_nat ((mp - 1) * y_idl cx)) (Z.to_nat (y_idl cx))) s lp dp mp Cn R) /\
lzw_inv (y_idl cx) (y_nP cx) X /\ dp < 4096 /\
0 <= q < 4096 /\ nth (Z.to_nat q) LI 0 <> 0 /\ nth (Z.to_nat q) LM 0 = 0 /\ 0 <= c < y_idl cx /\ s < s1 <= y_nP cx - 1 /\
getr regs 22 = Z_to_bv 64 s1 /\ getr regs 23 = Z_to_bv 64 (2 * q) /\ getr regs 24 = Z_to_bv 64 dp /\
getr regs 26 = Z_to_bv 64 c /\
getr regs 27 = Z_to_bv 64 ((mp - 1) * y_idl cx) /\ getr regs 25 = Z_to_bv 64 mp.
Lemma talias_ok_app : forall E l1 l2, alias_ok E l1 -> alias_ok E l2 -> alias_ok E (l1 ++ l2).
Proof using. intros E l1 l2 H1 H2. induction l1 as [|[a b] l1 IH]; [exact H2|]. destruct H1 as [Hf H1]. split; [exact Hf | apply IH; exact H1]. Qed.
Inductive tmiss_out := TMO_rst | TMO_tail (X' : lzw_abs) | TMO_sw2.
Definition tmo_pc (o : tmiss_out) : Z := match o with TMO_rst => TPC_RST | TMO_tail _ => TPC_TAIL | TMO_sw2 => TPC_SW2 end.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Definition tmo_val (cx : lzw_tcx) (X : lzw_abs) (V : lzw_v) (PIX : list Z) (s1 q c : Z) (mem' : word -> option byte) (o : tmiss_out) : Prop :=
let vLM := nth (Z.to_nat q) (la_LM X) 0 in let vLI := nth (Z.to_nat q) (la_LI X) 0 in
match o with
| TMO_rst => la_dp X = 4096 /\ vtabs_at mem' cx PIX (mkLV (v_LC V) (v_LD V ++ [q]))
| TMO_tail X' =>
la_dp X < 4096 /\
((vLM <> 0 /\ X' = vx_map (y_idl cx) X vLM c s1 /\ vtabs_at mem' cx PIX (mkLV (v_LC V) (v_LD V ++ [q]))) \/
(vLM = 0 /\ vLI = 0 /\ X' = vx_first X q s1 /\ vtabs_at mem' cx PIX (mkLV (updn (v_LC V) (Z.to_nat q) c) (v_LD V ++ [q]))))
| TMO_sw2 => la_dp X < 4096 /\ vLM = 0 /\ vLI <> 0 /\ vtabs_at mem' cx PIX (mkLV (v_LC V) (v_LD V ++ [q]))
end.
Definition tmo_post (cx : lzw_tcx) (X : lzw_abs) (s1 q c : Z) (regs' : bvmap 5 word) (mem' : word -> option byte) (o : tmiss_out) : Prop :=
match o with
| TMO_rst => trst_pre cx X s1 regs' mem'
| TMO_tail X' => ttail_post cx X regs' mem' X' /\ la_s X' = s1
| TMO_sw2 => tsw2_pre cx X s1 q c regs' mem'
end.
Local Ltac septac HSEP i j :=
let Hs := fresh "Hs" in
pose proof (tcx_sep _ HSEP i j ltac:(lia) ltac:(lia)) as Hs;
cbv [nth app tcx_tabs fst snd zz_disj y_tisz y_tmsz y_cap cap] in Hs.
Local Ltac wr1 n HE W HBt untac :=
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ n); [reflexivity | rewrite HE; apply unsigned_lit_small; lia | |];
[ cbn [r_wlo r_whi gen_region regw reg16]; intros a Ha;
lazymatch type of W with wtok' _ _ _ _ (?d, ?n) => eapply (wr_byte_of_wtok _ _ _ _ _ d n); [exact W | apply HBt; untac; inl' | lia] end |].
Local Ltac wr_tac HE8 HE44 HE14 HE48 HE49 Wg Wld Wli Wlc Wtm HBt :=
wr_norm;
repeat first [ apply wr_ok_nil
| apply wr_ok_cons_ro; [zlit_tac|]
| wr1 8%nat HE8 Wg HBt ltac:(cbv)
| wr1 44%nat HE44 Wld HBt ltac:(cbv [tcx_tabs y_cap cap In]; unfold y_cap, cap)
| wr1 14%nat HE14 Wli HBt ltac:(cbv)
| wr1 48%nat HE48 Wlc HBt ltac:(cbv)
| wr1 49%nat HE49 Wtm HBt ltac:(cbv [tcx_tabs y_tmsz In]; unfold y_tmsz) ].
Local Ltac gfield V Hout Hgout := intros k Hk; rewrite Hout; [apply V; exact Hk | cbn in Hk; lia | apply Hgout; cbn in Hk; lia].
Local Ltac gen_tac HS HE8 HE41 HE42 HE43 HGA Hout Hgout g :=
let HRg := fresh "HRg" in let G8 := fresh "G8" in
lazymatch type of HS with st_ok _ ?E1 _ _ =>
pose proof (tst_ok_region_nth E1 _ _ 0 _ HS eq_refl) as HRg;
assert (G8 : bv_unsigned (ew E1 8) = g) by (rewrite HE8; apply unsigned_lit_small; lia);
let V0 := fresh "V" in let V8 := fresh "V" in let V16 := fresh "V" in let V24 := fresh "V" in let V32 := fresh "V" in
let V40 := fresh "V" in let V48 := fresh "V" in let V56 := fresh "V" in
destruct HGA as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & _);
unfold gen_at; repeat split;
[ gfield V0 Hout Hgout | gfield V8 Hout Hgout | gfield V16 Hout Hgout | gfield V24 Hout Hgout
| gfield V32 Hout Hgout | gfield V40 Hout Hgout | gfield V48 Hout Hgout | gfield V56 Hout Hgout
| change 4%nat with (N.to_nat 4); eapply (tval_mem_of_chunk E1 _ _ 8%nat g 60 4); [exact HRg | reflexivity | inl | exact G8 | | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia];
cbn [sv_denot]; rewrite HE41, unsigned_lit_small by lia; reflexivity
| change 2%nat with (N.to_nat 2); eapply (tval_mem_of_chunk E1 _ _ 8%nat g 64 2); [exact HRg | reflexivity | inl | exact G8 | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia];
cbn [sv_denot]; rewrite HE42, ?Z.add_0_r, unsigned_lit_small by lia; reflexivity
| change 2%nat with (N.to_nat 2); eapply (tval_mem_of_chunk E1 _ _ 8%nat g 66 2); [exact HRg | reflexivity | inl | exact G8 | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia];
cbn [sv_denot]; rewrite HE43, Z.add_0_r, unsigned_lit_small by lia; reflexivity ]
end.
Local Ltac mk_out HF1 ws HE8 HE44 HE14 HE48 HE49 :=
lazymatch type of HF1 with frame_of ?E1 ?rs ?m0 ?m' =>
assert (Hout : forall a, 0 <= a < 2 ^ 64 -> outside ws a -> mbyte ubs0segs m' a = mbyte ubs0segs m0 a)
by (intros a Ha Hws; eapply (tframe_mbyte_list E1 _ _ _ ws a HF1 Ha);
[ repeat (apply Forall2_cons; [first [left; cbn; lia | right; cbn [fst snd r_base r_wlo r_whi regw reg16 tms_img1 gen_region base_val]; rewrite ?HE8, ?HE44, ?HE14, ?HE48, ?HE49, ?unsigned_lit_small by lia; lia]|]); apply Forall2_nil
| exact Hws ]);
cbn [ms_mem] in Hout
end.
Lemma tmiss_fullV : forall cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s1 q c PIX V,
tcx_ok cx -> tcx_ranges cx -> tcx_seps cx -> tcx_blocks cx (blocks Lc Ac) -> tcx_win STK sp0 cx ->
tcx_wtok STK sp0 FP (blocks L A) cx ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
tlzw_regs_fix regs cx -> gen_at memc cx (la_lp X) (la_dp X) (la_mp X) -> ttables_at memc cx X -> lzw_inv (y_idl cx) (y_nP cx) X ->
tmiss_pre cx regs s1 q ->
la_s X < s1 <= y_nP cx - 1 -> 0 <= q < 4096 -> 0 <= c < y_idl cx -> val_mem ubs0segs memc (y_img cx + s1) 1 c ->
la_dp X = 4096 ->
vtabs_at memc cx PIX V -> vinv cx PIX X V ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 TPC_MISS) memc (seg_rom ubs0segs)) mdc)
(fun c' => exists regs' mem' o,
c' = mkCfg (mkst regs' (Z_to_bv 64 (tmo_pc o)) mem' (seg_rom ubs0segs)) mdc /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ tabove_eq cx memc mem' /\
tmo_post cx X s1 q c regs' mem' o /\ tmo_val cx X V PIX s1 q c mem' o).
Proof using IMG LAWS.
intros cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s1 q c PIX V
HCX HRG HSEP HBL HWIN HWT HJ HFX HGA HT HI (H22 & H10 & H17 & H14 & H12 & H23 & H13) Hs1 Hq Hc HC Hfull HVT HVI.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HH.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR1 & HpR2 & HpR3 & HpR8 & Hbi1 & Hbi2 & Hbi3 & Hbi4 & Hgp).
pose proof HRG as ((Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rld1 & Rld2 & Rld3 & Rld4) & (Rg1 & Rg2 & Rg3 & _) & _).
destruct HBL as [HBt HBi]. destruct HWIN as [W1 W2].
unfold y_tisz, y_tmsz, y_cap, cap in *. cbn [fst snd] in Rti1, Rti2, Rti3, Rti4, Rtm1, Rtm2, Rtm3, Rtm4, Rld1, Rld2, Rld3, Rld4.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
assert (HMRle : y_MR cx <= 26055).
{ assert (y_MR cx * 3838 <= y_MR cx * (4094 - y_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (y_idl cx) (y_nP cx) (y_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
pose proof (mp_bound (y_idl cx) (y_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(lia) HI) as Hmpb. cbn [la_mp] in Hmpb.
destruct (LI_read (y_idl cx) (y_nP cx) _ q HI Hq) as [HqLI HvLI]. cbn [la_LI] in HqLI, HvLI.
destruct (LM_read (y_idl cx) (y_nP cx) _ q HI Hq) as [HqLM HvLM]. cbn [la_LM la_mp] in HqLM, HvLM.
set (vLI := nth (Z.to_nat q) LI 0) in *. set (vLM := nth (Z.to_nat q) LM 0) in *.
destruct HT as (ATI & ALM & ALI & ATM).
destruct (arr16_nthZ ubs0segs memc (y_li cx) LI q ALI ltac:(lia) HqLI) as [VLI _].
destruct (arr16_nthZ ubs0segs memc (y_lm cx) LM q ALM ltac:(lia) HqLM) as [VLM _].
fold vLI in VLI. fold vLM in VLM.
assert (DvLI : vLI = nth (Z.to_nat q) LI 0) by reflexivity. assert (DvLM : vLM = nth (Z.to_nat q) LM 0) by reflexivity.
clearbody vLI vLM.
remember ((vLM - 1) * y_idl cx + c) as j eqn:Hj.
assert (Hrow : 0 <= (mp - 1) * y_idl cx <= 2046 * 256).
{ split; [apply Z.mul_nonneg_nonneg; lia | ]. apply (Z.le_trans _ (2046 * y_idl cx)); [apply Z.mul_le_mono_nonneg_r; lia | apply Z.mul_le_mono_nonneg_l; lia]. }
assert (Hrow2 : 2 * ((mp - 1) * y_idl cx) + 2 * y_idl cx <= 4098 * y_idl cx).
{ assert (mp * y_idl cx <= 2047 * y_idl cx) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
assert (Pld : forall i, 0 <= i < 2 -> present memc (y_ld cx + 2 * lp + i)).
{ intros i Hi. replace (y_ld cx + 2 * lp + i) with (y_ld cx + (2 * lp + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_ld cx) (2 * (y_nP cx + 2 + y_MR cx)) (2 * lp + i) HH ltac:(apply HBt; inl) ltac:(lia))). }
assert (Pg : forall i, 0 <= i < 72 -> present memc (y_g cx + i)).
{ intros i Hi. apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_g cx) 72 i HH ltac:(apply HBt; inl) Hi)). }
assert (Plc : forall i, 0 <= i < 1 -> present memc (y_lc cx + q + i)).
{ intros i Hi. replace (y_lc cx + q + i) with (y_lc cx + (q + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_lc cx) 4096 (q + i) HH ltac:(apply HBt; inl) ltac:(lia))). }
assert (Ptm : forall i, 0 <= i < 4098 * y_idl cx -> present memc (y_tm cx + i)).
{ intros i Hi. apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_tm cx) (4098 * y_idl cx) i HH ltac:(apply HBt; inl) Hi)). }
remember [Z_to_bv 64 (y_ld cx + 2 * lp); Z_to_bv 64 c; Z_to_bv 64 vLM; Z_to_bv 64 vLI; Z_to_bv 64 (y_lc cx + q);
Z_to_bv 64 (y_tm cx + 2 * j); Z_to_bv 64 (y_tm cx + 2 * ((mp - 1) * y_idl cx))] as more eqn:Hmore.
remember (Ereg regs (tcx_extra cx lp dp mp ++ more)) as E eqn:HE0.
assert (HE44 : ew E 44 = Z_to_bv 64 (y_ld cx + 2 * lp)) by (rewrite HE0, <- (Nat.add_0_r 44), (TE_more regs _ _ _ _ more 0), Hmore; reflexivity).
assert (HE45 : ew E 45 = Z_to_bv 64 c) by (rewrite HE0; change 45%nat with (44 + 1)%nat; rewrite (TE_more regs _ _ _ _ more 1), Hmore; reflexivity).
assert (HE46 : ew E 46 = Z_to_bv 64 vLM) by (rewrite HE0; change 46%nat with (44 + 2)%nat; rewrite (TE_more regs _ _ _ _ more 2), Hmore; reflexivity).
assert (HE47 : ew E 47 = Z_to_bv 64 vLI) by (rewrite HE0; change 47%nat with (44 + 3)%nat; rewrite (TE_more regs _ _ _ _ more 3), Hmore; reflexivity).
assert (HE48 : ew E 48 = Z_to_bv 64 (y_lc cx + q)) by (rewrite HE0; change 48%nat with (44 + 4)%nat; rewrite (TE_more regs _ _ _ _ more 4), Hmore; reflexivity).
assert (HE49 : ew E 49 = Z_to_bv 64 (y_tm cx + 2 * j)) by (rewrite HE0; change 49%nat with (44 + 5)%nat; rewrite (TE_more regs _ _ _ _ more 5), Hmore; reflexivity).
assert (HE50 : ew E 50 = Z_to_bv 64 (y_tm cx + 2 * ((mp - 1) * y_idl cx))) by (rewrite HE0; change 50%nat with (44 + 6)%nat; rewrite (TE_more regs _ _ _ _ more 6), Hmore; reflexivity).
pose proof (TE_sp regs cx lp dp mp more HFX) as HE2. pose proof (TE_g regs cx lp dp mp more HFX) as HE8.
pose proof (TE_idl regs cx lp dp mp more HFX) as HE20. pose proof (TE_idl2 regs cx lp dp mp more HFX) as HE21.
pose proof (TE_ti regs cx lp dp mp more) as HE32. pose proof (TE_lm regs cx lp dp mp more) as HE33.
pose proof (TE_lc regs cx lp dp mp more) as HE34. pose proof (TE_li regs cx lp dp mp more) as HE35.
pose proof (TE_tm regs cx lp dp mp more) as HE36. pose proof (TE_ld regs cx lp dp mp more) as HE37.
pose proof (TE_img regs cx lp dp mp more) as HE38. pose proof (TE_nP regs cx lp dp mp more) as HE39.
pose proof (TE_lp regs cx lp dp mp more) as HE41. pose proof (TE_dp regs cx lp dp mp more) as HE42. pose proof (TE_mp regs cx lp dp mp more) as HE43.
rewrite <- HE0 in HE2, HE8, HE20, HE21, HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE41, HE42, HE43.
assert (HE22 : ew E 22 = Z_to_bv 64 s1) by (rewrite HE0, (TE_reg regs _ _ _ _ more 22%bv 22) by reflexivity; exact H22).
assert (HE10 : ew E 10 = Z_to_bv 64 q) by (rewrite HE0, (TE_reg regs _ _ _ _ more 10%bv 10) by reflexivity; exact H10).
assert (HE17 : ew E 17 = Z_to_bv 64 (y_lm cx + 2 * q)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 17%bv 17) by reflexivity; exact H17).
assert (HE14 : ew E 14 = Z_to_bv 64 (y_li cx + 2 * q)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 14%bv 14) by reflexivity; exact H14).
assert (HE12 : ew E 12 = Z_to_bv 64 (y_img cx + s1)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 12%bv 12) by reflexivity; exact H12).
assert (HE23 : ew E 23 = Z_to_bv 64 (2 * q)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 23%bv 23) by reflexivity; exact H23).
assert (HE13 : ew E 13 = Z_to_bv 64 q) by (rewrite HE0, (TE_reg regs _ _ _ _ more 13%bv 13) by reflexivity; exact H13).
assert (FACTS0 : atoms_ok E (tms_facts false)).
{ unfold tms_facts. rewrite app_nil_r. cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2].
rewrite HE10, HE12, HE13, HE14, HE17, HE22, HE23, HE44, HE45, HE46, HE47, HE48, HE50, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r. repeat split; try lia.
- apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists q; lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rli3].
- apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists q; lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rlm3].
- apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists lp; lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rld3].
- apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists ((mp - 1) * y_idl cx); lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rtm3]. }
assert (HUROW : U E tms_ROW = (mp - 1) * y_idl cx) by (unfold tms_ROW; apply (U_mulw_row E 43 20 mp (y_idl cx) HE43 HE20); lia).
assert (ALIAS0 : alias_ok E (tms_alias false)).
{ unfold tms_alias. rewrite app_nil_r. cbn [alias_ok]. split; [|split; [|split; [|split; [|exact I]]]].
- apply (alias_b2i' E 37 41 44 (y_ld cx) lp HE37 HE41 HE44); lia.
- apply (alias_add E 34 13 48 (y_lc cx) q HE34 HE13 HE48); lia.
- apply (alias_add E 35 23 14 (y_li cx) (2 * q) HE35 HE23 HE14); lia.
- apply (alias_sll1_base E 36 50 tms_ROW (y_tm cx) ((mp - 1) * y_idl cx) HE36 HUROW HE50); lia. }
assert (CONDLD : acond_ok E (mkAC BC_GEU (SOff 44%nat 0) (SOff 37%nat 0))) by (apply (cond_geu E 44 0 37 0 (y_ld cx + 2 * lp) (y_ld cx) HE44 HE37); lia).
assert (RLD : region_ok ubs0segs E memc (regw 44 2)).
{ apply (region_ok_regw _ E memc 44 2 (y_ld cx + 2 * lp) HE44); [lia | lia | lia |].
intros o Ho. apply (present_writable ubs0_msyms). apply Pld. exact Ho. }
assert (RIMG : region_ok ubs0segs E memc tms_img1).
{ unfold region_ok, tms_img1. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE12, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [| | cbn; lia | rewrite Z.add_0_r; exact HC]; [|change (2 ^ (8 * Z.of_N 1)) with 256; lia].
cbn [sv_denot]. rewrite HE45, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
assert (RLM : region_ok ubs0segs E memc (reg16 17 46 false)).
{ eapply (region_ok_reg16 _ E memc 17 46 false (y_lm cx + 2 * q) vLM HE17 HE46); [lia | lia | lia | exact VLM | intros X0; discriminate X0]. }
pose proof (HWT (y_g cx, 72) ltac:(inl)) as Wg.
pose proof (HWT (y_ld cx, 2 * (y_nP cx + 2 + y_MR cx)) ltac:(cbv [tcx_tabs y_cap cap In]; unfold y_cap, cap; inl')) as Wld.
pose proof (HWT (y_tm cx, 4098 * y_idl cx) ltac:(cbv [tcx_tabs y_tmsz In]; unfold y_tmsz; inl')) as Wtm.
pose proof (HWT (y_li cx, 8192) ltac:(inl)) as Wli.
pose proof (HWT (y_lc cx, 4096) ltac:(inl)) as Wlc.
assert (HS : st_ok ubs0segs E ss_tms_full (mkst regs (Z_to_bv 64 TPC_MISS) memc (seg_rom ubs0segs))).
{ unfold ss_tms_full, tlzw_ss. rewrite HE0.
apply (tlzw_st_ok cx regs lp dp mp more memc TPC_MISS true); rewrite <- ?HE0.
- exact HCX.
- exact HRG.
- exact HFX.
- exact HGA.
- intros _ a Ha. apply (present_writable ubs0_msyms). replace a with (y_g cx + (a - y_g cx)) by lia. apply Pg. lia.
- lia.
- lia.
- lia.
- vm_compute; reflexivity.
- apply Forall_cons; [exact RLD | apply Forall_nil].
- unfold tms_regions_full. cbn [all_disjoint app]; unfold extent_disjoint, regw, gen_region; cbn [r_base r_lo r_hi base_val app].
rewrite HE8, HE44, !unsigned_lit_small by lia. split; [septac HSEP 5%nat 6%nat; lia | exact I].
- unfold tms_regions_full. cbn [pairwise_disjoint all_disjoint app]. split; exact I.
- exact FACTS0.
- unfold tms_conds_full. cbn [conds_ok]. split; [exact CONDLD|]. split; [|exact I].
apply cond_ne_U. rewrite (U_dpfull12 E 42 dp HE42), U_SLit by lia. rewrite (proj2 (Z.eqb_eq dp 4096) Hfull). cbv. discriminate.
- exact ALIAS0. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 TPC_MISS) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ TPC_RST; [wr_tac HE8 HE44 HE14 HE48 HE49 Wg Wld Wli Wlc Wtm HBt|].
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch type of HS with st_ok _ _ _ ?msx => exists (ms_regs msx), (ms_mem msx), TMO_rst end.
split; [reflexivity|]. split; [exact HJ|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs (tcx_extra cx lp dp mp ++ more) TREGS_FIXL HS
ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
lazymatch goal with HF1 : frame_of _ _ _ _ |- _ =>
mk_out HF1 [(y_g cx + 60, y_g cx + 68); (y_ld cx + 2 * lp, y_ld cx + 2 * lp + 2)] HE8 HE44 HE14 HE48 HE49 end.
split; [intros a Ha; apply Hout; [lia | cbn -[Z.add Z.mul Z.sub]; repeat split; lia]|].
assert (Hgout : forall k, y_g cx <= k < y_g cx + 60 -> outside [(y_g cx + 60, y_g cx + 68); (y_ld cx + 2 * lp, y_ld cx + 2 * lp + 2)] k).
{ intros k Hk. cbn -[Z.add Z.mul Z.sub]; split; [lia|]; split; [septac HSEP 5%nat 6%nat; lia|]; exact I. }
split; [| unfold tmo_val; cbn [la_dp]; split; [exact Hfull|];
eapply (vtabs_emit memc _ cx PIX V (mkLA TI LM LI TM s lp dp mp Cn R) (fun a => (y_g cx + 60 <= a < y_g cx + 68) \/ (y_ld cx + 2 * lp <= a < y_ld cx + 2 * lp + 2)) q HVT HVI ltac:(lia));
[ intros a Ha Hna; apply Hout; [exact Ha | cbn -[Z.add Z.mul Z.sub]; tauto]
| cbn [la_lp]; split; [|split]; intros a Ha; (split; [lia|]); intros [Hw | Hw];
[ septac HSEP 2%nat 6%nat; lia | septac HSEP 2%nat 5%nat; lia | septac HSEP 6%nat 7%nat; lia | septac HSEP 5%nat 7%nat; lia | septac HSEP 5%nat 6%nat; lia | lia ]
| rewrite <- (Z.add_0_r (y_ld cx + 2 * la_lp (mkLA TI LM LI TM s lp dp mp Cn R))); cbn [la_lp]; change 2%nat with (N.to_nat 2);
eapply (tval_mem_of_chunk E _ _ 44%nat); [eapply (tst_ok_region_nth _ _ _ 1 _ HS); reflexivity | reflexivity | inl
| rewrite HE44; apply unsigned_lit_small; lia | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia];
cbn [sv_denot]; rewrite HE10, Z.add_0_r, unsigned_lit_small by lia; reflexivity
| lia ] ].
unfold tmo_post, trst_pre. cbv beta iota. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM].
split; [apply (tlzw_regs_fix_kept regs); [exact HFX | intros r Hr; apply HK; exact Hr]|].
split; [gen_tac HS HE8 HE41 HE42 HE43 HGA Hout Hgout (y_g cx)|].
split.
{ eapply (ttables_at_frame _ _ cx (mkLA TI LM LI TM s lp dp mp Cn R)
(fun a => (y_g cx + 60 <= a < y_g cx + 68) \/ (y_ld cx + 2 * lp <= a < y_ld cx + 2 * lp + 2)));
[exact (conj ATI (conj ALM (conj ALI ATM))) | exact HI | lia | exact HRG | intros a Ha Hna; apply Hout; [exact Ha | cbn; tauto] | | | |];
cbn beta; intros a Ha'; unfold y_tisz, y_tmsz in Ha'.
- septac HSEP 0%nat 5%nat. septac HSEP 0%nat 6%nat. lia.
- septac HSEP 1%nat 5%nat. septac HSEP 1%nat 6%nat. lia.
- septac HSEP 3%nat 5%nat. septac HSEP 3%nat 6%nat. lia.
- septac HSEP 4%nat 5%nat. septac HSEP 4%nat 6%nat. lia. }
split; [exact HI|]. split; [exact Hfull|]. split; [treg_val HS (22%bv:reg) | lia].
Qed.
Lemma tmiss_mapV : forall cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s1 q c PIX V,
tcx_ok cx -> tcx_ranges cx -> tcx_seps cx -> tcx_blocks cx (blocks Lc Ac) -> tcx_win STK sp0 cx ->
tcx_wtok STK sp0 FP (blocks L A) cx ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
tlzw_regs_fix regs cx -> gen_at memc cx (la_lp X) (la_dp X) (la_mp X) -> ttables_at memc cx X -> lzw_inv (y_idl cx) (y_nP cx) X ->
tmiss_pre cx regs s1 q ->
la_s X < s1 <= y_nP cx - 1 -> 0 <= q < 4096 -> 0 <= c < y_idl cx -> val_mem ubs0segs memc (y_img cx + s1) 1 c ->
la_dp X < 4096 -> nth (Z.to_nat q) (la_LM X) 0 <> 0 ->
vtabs_at memc cx PIX V -> vinv cx PIX X V ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 TPC_MISS) memc (seg_rom ubs0segs)) mdc)
(fun c' => exists regs' mem' o,
c' = mkCfg (mkst regs' (Z_to_bv 64 (tmo_pc o)) mem' (seg_rom ubs0segs)) mdc /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ tabove_eq cx memc mem' /\
tmo_post cx X s1 q c regs' mem' o /\ tmo_val cx X V PIX s1 q c mem' o).
Proof using IMG LAWS.
intros cx STK sp0 FP L A mem md Lc Ac mdc regs memc X s1 q c PIX V
HCX HRG HSEP HBL HWIN HWT HJ HFX HGA HT HI (H22 & H10 & H17 & H14 & H12 & H23 & H13) Hs1 Hq Hc HC Hdplt HLM1 HVT HVI.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HH.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR1 & HpR2 & HpR3 & HpR8 & Hbi1 & Hbi2 & Hbi3 & Hbi4 & Hgp).
pose proof HRG as ((Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rld1 & Rld2 & Rld3 & Rld4) & (Rg1 & Rg2 & Rg3 & _) & _).
destruct HBL as [HBt HBi]. destruct HWIN as [W1 W2].
unfold y_tisz, y_tmsz, y_cap, cap in *. cbn [fst snd] in Rti1, Rti2, Rti3, Rti4, Rtm1, Rtm2, Rtm3, Rtm4, Rld1, Rld2, Rld3, Rld4.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
assert (HMRle : y_MR cx <= 26055).
{ assert (y_MR cx * 3838 <= y_MR cx * (4094 - y_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (y_idl cx) (y_nP cx) (y_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
pose proof (mp_bound (y_idl cx) (y_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(lia) HI) as Hmpb. cbn [la_mp] in Hmpb.
destruct (LI_read (y_idl cx) (y_nP cx) _ q HI Hq) as [HqLI HvLI]. cbn [la_LI] in HqLI, HvLI.
destruct (LM_read (y_idl cx) (y_nP cx) _ q HI Hq) as [HqLM HvLM]. cbn [la_LM la_mp] in HqLM, HvLM.
set (vLI := nth (Z.to_nat q) LI 0) in *. set (vLM := nth (Z.to_nat q) LM 0) in *.
destruct HT as (ATI & ALM & ALI & ATM).
destruct (arr16_nthZ ubs0segs memc (y_li cx) LI q ALI ltac:(lia) HqLI) as [VLI _].
destruct (arr16_nthZ ubs0segs memc (y_lm cx) LM q ALM ltac:(lia) HqLM) as [VLM _].
fold vLI in VLI. fold vLM in VLM.
assert (DvLI : vLI = nth (Z.to_nat q) LI 0) by reflexivity. assert (DvLM : vLM = nth (Z.to_nat q) LM 0) by reflexivity.
clearbody vLI vLM.
remember ((vLM - 1) * y_idl cx + c) as j eqn:Hj.
assert (Hrow : 0 <= (mp - 1) * y_idl cx <= 2046 * 256).
{ split; [apply Z.mul_nonneg_nonneg; lia | ]. apply (Z.le_trans _ (2046 * y_idl cx)); [apply Z.mul_le_mono_nonneg_r; lia | apply Z.mul_le_mono_nonneg_l; lia]. }
assert (Hrow2 : 2 * ((mp - 1) * y_idl cx) + 2 * y_idl cx <= 4098 * y_idl cx).
{ assert (mp * y_idl cx <= 2047 * y_idl cx) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
assert (Pld : forall i, 0 <= i < 2 -> present memc (y_ld cx + 2 * lp + i)).
{ intros i Hi. replace (y_ld cx + 2 * lp + i) with (y_ld cx + (2 * lp + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_ld cx) (2 * (y_nP cx + 2 + y_MR cx)) (2 * lp + i) HH ltac:(apply HBt; inl) ltac:(lia))). }
assert (Pg : forall i, 0 <= i < 72 -> present memc (y_g cx + i)).
{ intros i Hi. apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_g cx) 72 i HH ltac:(apply HBt; inl) Hi)). }
assert (Plc : forall i, 0 <= i < 1 -> present memc (y_lc cx + q + i)).
{ intros i Hi. replace (y_lc cx + q + i) with (y_lc cx + (q + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_lc cx) 4096 (q + i) HH ltac:(apply HBt; inl) ltac:(lia))). }
assert (Ptm : forall i, 0 <= i < 4098 * y_idl cx -> present memc (y_tm cx + i)).
{ intros i Hi. apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ (y_tm cx) (4098 * y_idl cx) i HH ltac:(apply HBt; inl) Hi)). }
remember [Z_to_bv 64 (y_ld cx + 2 * lp); Z_to_bv 64 c; Z_to_bv 64 vLM; Z_to_bv 64 vLI; Z_to_bv 64 (y_lc cx + q);
Z_to_bv 64 (y_tm cx + 2 * j); Z_to_bv 64 (y_tm cx + 2 * ((mp - 1) * y_idl cx))] as more eqn:Hmore.
remember (Ereg regs (tcx_extra cx lp dp mp ++ more)) as E eqn:HE0.
assert (HE44 : ew E 44 = Z_to_bv 64 (y_ld cx + 2 * lp)) by (rewrite HE0, <- (Nat.add_0_r 44), (TE_more regs _ _ _ _ more 0), Hmore; reflexivity).
assert (HE45 : ew E 45 = Z_to_bv 64 c) by (rewrite HE0; change 45%nat with (44 + 1)%nat; rewrite (TE_more regs _ _ _ _ more 1), Hmore; reflexivity).
assert (HE46 : ew E 46 = Z_to_bv 64 vLM) by (rewrite HE0; change 46%nat with (44 + 2)%nat; rewrite (TE_more regs _ _ _ _ more 2), Hmore; reflexivity).
assert (HE47 : ew E 47 = Z_to_bv 64 vLI) by (rewrite HE0; change 47%nat with (44 + 3)%nat; rewrite (TE_more regs _ _ _ _ more 3), Hmore; reflexivity).
assert (HE48 : ew E 48 = Z_to_bv 64 (y_lc cx + q)) by (rewrite HE0; change 48%nat with (44 + 4)%nat; rewrite (TE_more regs _ _ _ _ more 4), Hmore; reflexivity).
assert (HE49 : ew E 49 = Z_to_bv 64 (y_tm cx + 2 * j)) by (rewrite HE0; change 49%nat with (44 + 5)%nat; rewrite (TE_more regs _ _ _ _ more 5), Hmore; reflexivity).
assert (HE50 : ew E 50 = Z_to_bv 64 (y_tm cx + 2 * ((mp - 1) * y_idl cx))) by (rewrite HE0; change 50%nat with (44 + 6)%nat; rewrite (TE_more regs _ _ _ _ more 6), Hmore; reflexivity).
pose proof (TE_sp regs cx lp dp mp more HFX) as HE2. pose proof (TE_g regs cx lp dp mp more HFX) as HE8.
pose proof (TE_idl regs cx lp dp mp more HFX) as HE20. pose proof (TE_idl2 regs cx lp dp mp more HFX) as HE21.
pose proof (TE_ti regs cx lp dp mp more) as HE32. pose proof (TE_lm regs cx lp dp mp more) as HE33.
pose proof (TE_lc regs cx lp dp mp more) as HE34. pose proof (TE_li regs cx lp dp mp more) as HE35.
pose proof (TE_tm regs cx lp dp mp more) as HE36. pose proof (TE_ld regs cx lp dp mp more) as HE37.
pose proof (TE_img regs cx lp dp mp more) as HE38. pose proof (TE_nP regs cx lp dp mp more) as HE39.
pose proof (TE_lp regs cx lp dp mp more) as HE41. pose proof (TE_dp regs cx lp dp mp more) as HE42. pose proof (TE_mp regs cx lp dp mp more) as HE43.
rewrite <- HE0 in HE2, HE8, HE20, HE21, HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE41, HE42, HE43.
assert (HE22 : ew E 22 = Z_to_bv 64 s1) by (rewrite HE0, (TE_reg regs _ _ _ _ more 22%bv 22) by reflexivity; exact H22).
assert (HE10 : ew E 10 = Z_to_bv 64 q) by (rewrite HE0, (TE_reg regs _ _ _ _ more 10%bv 10) by reflexivity; exact H10).
assert (HE17 : ew E 17 = Z_to_bv 64 (y_lm cx + 2 * q)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 17%bv 17) by reflexivity; exact H17).
assert (HE14 : ew E 14 = Z_to_bv 64 (y_li cx + 2 * q)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 14%bv 14) by reflexivity; exact H14).
assert (HE12 : ew E 12 = Z_to_bv 64 (y_img cx + s1)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 12%bv 12) by reflexivity; exact H12).
assert (HE23 : ew E 23 = Z_to_bv 64 (2 * q)) by (rewrite HE0, (TE_reg regs _ _ _ _ more 23%bv 23) by reflexivity; exact H23).
assert (HE13 : ew E 13 = Z_to_bv 64 q) by (rewrite HE0, (TE_reg regs _ _ _ _ more 13%bv 13) by reflexivity; exact H13).
assert (FACTS0 : atoms_ok E (tms_facts false)).
{ unfold tms_facts. rewrite app_nil_r. cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2].
rewrite HE10, HE12, HE13, HE14, HE17, HE22, HE23, HE44, HE45, HE46, HE47, HE48, HE50, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r. repeat split; try lia.
- apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists q; lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rli3].
- apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists q; lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rlm3].
- apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists lp; lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rld3].
- apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists ((mp - 1) * y_idl cx); lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rtm3]. }
assert (HUROW : U E tms_ROW = (mp - 1) * y_idl cx) by (unfold tms_ROW; apply (U_mulw_row E 43 20 mp (y_idl cx) HE43 HE20); lia).
assert (ALIAS0 : alias_ok E (tms_alias false)).
{ unfold tms_alias. rewrite app_nil_r. cbn [alias_ok]. split; [|split; [|split; [|split; [|exact I]]]].
- apply (alias_b2i' E 37 41 44 (y_ld cx) lp HE37 HE41 HE44); lia.
- apply (alias_add E 34 13 48 (y_lc cx) q HE34 HE13 HE48); lia.
- apply (alias_add E 35 23 14 (y_li cx) (2 * q) HE35 HE23 HE14); lia.
- apply (alias_sll1_base E 36 50 tms_ROW (y_tm cx) ((mp - 1) * y_idl cx) HE36 HUROW HE50); lia. }
assert (CONDLD : acond_ok E (mkAC BC_GEU (SOff 44%nat 0) (SOff 37%nat 0))) by (apply (cond_geu E 44 0 37 0 (y_ld cx + 2 * lp) (y_ld cx) HE44 HE37); lia).
assert (RLD : region_ok ubs0segs E memc (regw 44 2)).
{ apply (region_ok_regw _ E memc 44 2 (y_ld cx + 2 * lp) HE44); [lia | lia | lia |].
intros o Ho. apply (present_writable ubs0_msyms). apply Pld. exact Ho. }
assert (RIMG : region_ok ubs0segs E memc tms_img1).
{ unfold region_ok, tms_img1. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE12, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [| | cbn; lia | rewrite Z.add_0_r; exact HC]; [|change (2 ^ (8 * Z.of_N 1)) with 256; lia].
cbn [sv_denot]. rewrite HE45, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
assert (RLM : region_ok ubs0segs E memc (reg16 17 46 false)).
{ eapply (region_ok_reg16 _ E memc 17 46 false (y_lm cx + 2 * q) vLM HE17 HE46); [lia | lia | lia | exact VLM | intros X0; discriminate X0]. }
pose proof (HWT (y_g cx, 72) ltac:(inl)) as Wg.
pose proof (HWT (y_ld cx, 2 * (y_nP cx + 2 + y_MR cx)) ltac:(cbv [tcx_tabs y_cap cap In]; unfold y_cap, cap; inl')) as Wld.
pose proof (HWT (y_tm cx, 4098 * y_idl cx) ltac:(cbv [tcx_tabs y_tmsz In]; unfold y_tmsz; inl')) as Wtm.
pose proof (HWT (y_li cx, 8192) ltac:(inl)) as Wli.
pose proof (HWT (y_lc cx, 4096) ltac:(inl)) as Wlc.
assert (Hm1 : 1 <= vLM) by lia. clear HLM1.
destruct (TM_read (y_idl cx) (y_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) vLM c ltac:(lia) HI ltac:(cbn; lia) ltac:(lia)) as (T1 & T2 & T3).
cbn [la_TM] in T1, T2. rewrite <- Hj in T1, T2, T3.
assert (Hp0 : 0 <= (vLM - 1) * y_idl cx <= j).
{ assert (0 <= (vLM - 1) * y_idl cx) by (apply Z.mul_nonneg_nonneg; lia). rewrite Hj. lia. }
assert (Hj21 : 2 * j + 2 <= 4098 * y_idl cx /\ j < 2 ^ 20).
{ assert (2049 * y_idl cx <= 2049 * 256) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
assert (HUX : U E tms_X = (vLM - 1) * y_idl cx).
{ unfold tms_X. apply U_sextw_small; [apply (U_mul_row64 E 46 20 vLM (y_idl cx) HE46 HE20); lia | lia]. }
assert (HUY : U E tms_Y = j).
{ unfold tms_Y. apply U_sextw_small; [|lia].
rewrite (U_add_small E tms_X (SOff 45%nat 0) ((vLM - 1) * y_idl cx) c HUX (U_atom E 45 c HE45 ltac:(lia))) by lia. lia. }
assert (Ptmc : forall i, 0 <= i < 2 -> present memc (y_tm cx + 2 * j + i)).
{ intros i Hi. replace (y_tm cx + 2 * j + i) with (y_tm cx + (2 * j + i)) by lia. apply Ptm. lia. }
assert (HS : st_ok ubs0segs E ss_tms_map (mkst regs (Z_to_bv 64 TPC_MISS) memc (seg_rom ubs0segs))).
{ unfold ss_tms_map, tlzw_ss. rewrite HE0.
apply (tlzw_st_ok cx regs lp dp mp more memc TPC_MISS true); rewrite <- ?HE0.
- exact HCX.
- exact HRG.
- exact HFX.
- exact HGA.
- intros _ a Ha. apply (present_writable ubs0_msyms). replace a with (y_g cx + (a - y_g cx)) by lia. apply Pg. lia.
- lia.
- lia.
- lia.
- vm_compute; reflexivity.
- apply Forall_cons; [exact RLD|]. apply Forall_cons; [exact RIMG|]. apply Forall_cons; [exact RLM|]. apply Forall_cons; [|apply Forall_nil].
apply (region_ok_regw _ E memc 49 2 (y_tm cx + 2 * j) HE49); [lia | lia | lia |].
intros o Ho. apply (present_writable ubs0_msyms). apply Ptmc. exact Ho.
- unfold tms_regions_map. cbn [all_disjoint app]; unfold extent_disjoint, regw, reg16, tms_img1, gen_region; cbn [r_base r_lo r_hi base_val app].
rewrite HE8, HE44, HE12, HE17, HE49, !unsigned_lit_small by lia.
split; [septac HSEP 5%nat 6%nat; lia|]. split; [septac HSEP 6%nat 7%nat; lia|]. split; [septac HSEP 1%nat 6%nat; lia|].
split; [septac HSEP 4%nat 6%nat; lia | exact I].
- unfold tms_regions_map. cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint, regw, reg16, tms_img1; cbn [r_base r_lo r_hi base_val].
rewrite HE44, HE12, HE17, HE49, !unsigned_lit_small by lia.
split; [split; [septac HSEP 5%nat 7%nat; lia | split; [septac HSEP 1%nat 5%nat; lia | split; [septac HSEP 4%nat 5%nat; lia | exact I]]]|].
split; [split; [septac HSEP 1%nat 7%nat; lia | split; [septac HSEP 4%nat 7%nat; lia | exact I]]|].
split; [split; [septac HSEP 1%nat 4%nat; lia | exact I]|]. split; exact I.
- unfold tms_facts. apply atoms_ok_app; [exact FACTS0|].
cbn [atoms_ok]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2]. rewrite HE49, !unsigned_lit_small by lia.
change (2 ^ 1) with 2. repeat split; try lia.
apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists j; lia]. apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rtm3].
- unfold tms_conds_map. cbn [conds_ok]. split; [exact CONDLD|]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
+ apply cond_eq_U. rewrite (U_dpfull12 E 42 dp HE42), U_SLit by lia. rewrite (proj2 (Z.eqb_neq dp 4096) ltac:(lia)). reflexivity.
+ apply (cond_ne_lit E 46 vLM 0 HE46); lia.
+ apply cond_eq_U. rewrite (U_mulw_row E 46 20 vLM (y_idl cx) HE46 HE20), (U_mul_row64 E 46 20 vLM (y_idl cx) HE46 HE20) by lia. reflexivity.
+ apply cond_eq_U.
rewrite (U_addw_small E tms_X (SOff 45%nat 0) ((vLM - 1) * y_idl cx) c HUX (U_atom E 45 c HE45 ltac:(lia))) by lia.
rewrite (U_add_small E tms_X (SOff 45%nat 0) ((vLM - 1) * y_idl cx) c HUX (U_atom E 45 c HE45 ltac:(lia))) by lia. reflexivity.
+ apply (cond_geu E 49 0 36 0 (y_tm cx + 2 * j) (y_tm cx) HE49 HE36); lia.
+ apply cond_ne_U. rewrite (U_ptrchk E 49 36 tms_Y (y_tm cx + 2 * j) (y_tm cx) j HE49 HE36 HUY) by lia. rewrite U_lit by lia. lia.
- unfold tms_alias. apply talias_ok_app; [exact ALIAS0|]. cbn [alias_ok]. split; [|exact I].
apply (alias_base_sll1 E 36 49 tms_Y (y_tm cx) j HE36 HUY HE49); lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 TPC_MISS) memc (seg_rom ubs0segs))) in HJ.
clear Ptm.
jrun_to LAWS ubs0tbl_ok HS HJ TPC_TAIL; [wr_tac HE8 HE44 HE14 HE48 HE49 Wg Wld Wli Wlc Wtm HBt|].
rewrite (st_ok_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch type of HS with st_ok _ _ _ ?msx =>
exists (ms_regs msx), (ms_mem msx), (TMO_tail (mkLA TI LM LI (updn TM (Z.to_nat j) dp) s1 (lp + 1) (dp + 1) mp (Cn + 1) R)) end.
split; [reflexivity|]. split; [exact HJ|].
pose proof (regs_kept_of_st_ok _ _ _ _ regs (tcx_extra cx lp dp mp ++ more) TREGS_FIXL HS
ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK.
lazymatch goal with HF1 : frame_of _ _ _ _ |- _ =>
mk_out HF1 [(y_g cx + 60, y_g cx + 68); (y_ld cx + 2 * lp, y_ld cx + 2 * lp + 2); (0, 0); (0, 0); (y_tm cx + 2 * j, y_tm cx + 2 * j + 2)] HE8 HE44 HE14 HE48 HE49 end.
split; [intros a Ha; apply Hout; [lia | cbn -[Z.add Z.mul Z.sub]; repeat split; lia]|].
assert (Hgout : forall k, y_g cx <= k < y_g cx + 60 ->
outside [(y_g cx + 60, y_g cx + 68); (y_ld cx + 2 * lp, y_ld cx + 2 * lp + 2); (0, 0); (0, 0); (y_tm cx + 2 * j, y_tm cx + 2 * j + 2)] k).
{ intros k Hk. cbn -[Z.add Z.mul Z.sub]; split; [lia|]; split; [septac HSEP 5%nat 6%nat; lia|]; split; [lia|]; split; [lia|]; split; [septac HSEP 4%nat 6%nat; lia|]; exact I. }
assert (Vnew : val_mem ubs0segs ltac:(lazymatch type of HS with st_ok _ _ _ ?msx => exact (ms_mem msx) end) (y_tm cx + 2 * j) 2 dp).
{ rewrite <- (Z.add_0_r (y_tm cx + 2 * j)). change 2%nat with (N.to_nat 2).
eapply (tval_mem_of_chunk E _ _ 49%nat); [eapply (tst_ok_region_nth _ _ _ 4 _ HS); reflexivity | reflexivity | inl
| rewrite HE49; apply unsigned_lit_small; lia | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia].
cbn [sv_denot]. rewrite HE42, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
assert (HT' : ttables_at ltac:(lazymatch type of HS with st_ok _ _ _ ?msx => exact (ms_mem msx) end) cx
(mkLA TI LM LI (updn TM (Z.to_nat j) dp) s1 (lp + 1) (dp + 1) mp (Cn + 1) R)).
{ split; [|split; [|split]]; cbn [la_TI la_LM la_LI la_TM].
- eapply arr16_frame; [exact ATI|]. intros a Ha. rewrite LenTI, Z2Nat.id in Ha by lia.
apply Hout; [lia|]. cbn -[Z.add Z.mul Z.sub]; split; [septac HSEP 0%nat 6%nat; lia|]; split; [septac HSEP 0%nat 5%nat; lia|]; split; [lia|]; split; [lia|]; split; [septac HSEP 0%nat 4%nat; lia|]; exact I.
- eapply arr16_frame; [exact ALM|]. intros a Ha. rewrite LenLM in Ha. cbn in Ha.
apply Hout; [lia|]. cbn -[Z.add Z.mul Z.sub]; split; [septac HSEP 1%nat 6%nat; lia|]; split; [septac HSEP 1%nat 5%nat; lia|]; split; [lia|]; split; [lia|]; split; [septac HSEP 1%nat 4%nat; lia|]; exact I.
- eapply arr16_frame; [exact ALI|]. intros a Ha. rewrite LenLI in Ha. cbn in Ha.
apply Hout; [lia|]. cbn -[Z.add Z.mul Z.sub]; split; [septac HSEP 3%nat 6%nat; lia|]; split; [septac HSEP 3%nat 5%nat; lia|]; split; [lia|]; split; [lia|]; split; [septac HSEP 3%nat 4%nat; lia|]; exact I.
- eapply arr16_upd; [exact ATM | lia | exact T1 | lia | exact Vnew |].
intros a Ha Hna. rewrite LenTM, Z2Nat.id in Ha by lia.
apply Hout; [lia|]. cbn -[Z.add Z.mul Z.sub]; split; [septac HSEP 4%nat 6%nat; lia|]; split; [septac HSEP 4%nat 5%nat; lia|]; split; [lia|]; split; [lia|]; split; [lia|]; exact I. }
pose proof (inv_map (y_idl cx) (y_nP cx) Hidl _ vLM c (s1 - 1) HI ltac:(cbn [la_dp]; lia) ltac:(cbn [la_s]; lia) ltac:(cbn [la_mp]; lia) Hc) as HI'.
cbn [st_map] in HI'. rewrite <- Hj in HI'. replace (s1 - 1 + 1) with s1 in HI' by lia.
split; [| unfold tmo_val; cbn [la_dp la_LM la_LI]; rewrite <- DvLM; split; [lia|]; left; split; [lia|]; split; [unfold vx_map; rewrite <- Hj; reflexivity|];
eapply (vtabs_emit memc _ cx PIX V (mkLA TI LM LI TM s lp dp mp Cn R)
(fun a => (y_g cx + 60 <= a < y_g cx + 68) \/ (y_ld cx + 2 * lp <= a < y_ld cx + 2 * lp + 2) \/ (y_tm cx + 2 * j <= a < y_tm cx + 2 * j + 2)) q HVT HVI ltac:(lia));
[ intros a Ha Hna; apply Hout; [exact Ha | cbn -[Z.add Z.mul Z.sub]; repeat split; try lia; tauto]
| cbn [la_lp]; split; [|split]; intros a Ha; (split; [lia|]); intros [Hw | [Hw | Hw]];
[ septac HSEP 2%nat 6%nat; lia | septac HSEP 2%nat 5%nat; lia | septac HSEP 2%nat 4%nat; lia
| septac HSEP 6%nat 7%nat; lia | septac HSEP 5%nat 7%nat; lia | septac HSEP 4%nat 7%nat; lia
| septac HSEP 5%nat 6%nat; lia | lia | septac HSEP 4%nat 5%nat; lia ]
| rewrite <- (Z.add_0_r (y_ld cx + 2 * la_lp (mkLA TI LM LI TM s lp dp mp Cn R))); cbn [la_lp]; change 2%nat with (N.to_nat 2);
eapply (tval_mem_of_chunk E _ _ 44%nat); [eapply (tst_ok_region_nth _ _ _ 1 _ HS); reflexivity | reflexivity | inl
| rewrite HE44; apply unsigned_lit_small; lia | | change (2 ^ (8 * Z.of_N 2)) with 65536; lia | cbn; lia];
cbn [sv_denot]; rewrite HE10, Z.add_0_r, unsigned_lit_small by lia; reflexivity
| lia ] ].
unfold tmo_post, ttail_post. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM].
split; [|reflexivity].
split; [apply (tlzw_regs_fix_kept regs); [exact HFX | intros r Hr; apply HK; exact Hr]|].
split; [gen_tac HS HE8 HE41 HE42 HE43 HGA Hout Hgout (y_g cx)|].
split; [exact HT'|]. split; [exact HI'|]. split; [treg_val HS (22%bv:reg) | lia].
Qed.
End S.
End e.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
