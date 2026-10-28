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
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3a YI06 UI5b YI09 YI08 YI0r
UI1w UI1v UI4l UI21 UI2m UI3t UI5o UI5l YI6b UI5n
UI20 UI1d UI2l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 UI3u UI22 YI5a UI5d YI0f YI2w UI2v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Ltac lia_try := rc_inst; first [ solve [YM03.lf_prune0; YM03.lf_lia_orig] | solve [YM03.lf_prune1; YM03.lf_lia_orig] ].
Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ /\ (_ \/ _) |- _ => clear H | H : (_ \/ _) /\ _ |- _ => clear H end.
Ltac liaND := rc_inst; first [ solve [YM03.lf_prune0; YM03.lf_lia_orig] | solve [clear_disj; YM03.lf_prune1; YM03.lf_lia_orig] | solve [clear_disj; YM03.lf_lia_orig] | lia ].
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ss_flret : sstate :=
mkSS FL_RET sr_atoms [ YP09.mkRegion (Some 2%nat) 0 272 0 0 (fl_stk_saved 32) ] None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4) ] [] []).
Definition FL_CFG : Z := Eval vm_compute in (ubs0_A_flushFrame + 0xa68).
Lemma land1_cases : forall a, 0 <= a -> Z.land a 1 = 0 \/ Z.land a 1 = 1.
Proof using.
intros a Ha. rewrite Z.land_ones with (n := 1) by lia. change (2 ^ 1) with 2.
pose proof (Z.mod_pos_bound a 2 ltac:(lia)). lia.
Qed.
Definition fl_RgM : YP09.region := YP09.mkRegion (Some 80%nat) 0 96 0 0 (obj_chunks_gen LAY_CGIF A_X fl_litsG).
Definition fl_RfM : YP09.region := YP09.mkRegion (Some 81%nat) 0 40 0 0 (obj_chunks_gen LAY_Frame A_F []).
Definition fl_factsM : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4); (80%nat, mkAF 4096 (CEIL_MAX - 96) 4);
(81%nat, mkAF 4096 (CEIL_MAX - 40) 3) ].
Lemma fl_RgM_ok : forall regs1 regs0 s f fb more mem g,
bv_unsigned (ew (fl_E regs1 regs0 s f fb more) 80) = g -> 0 <= g -> g + 96 <= 2 ^ 64 ->
obj_at ubs0segs mem g LAY_CGIF (cgif_vals s) -> region_ok ubs0segs (fl_E regs1 regs0 s f fb more) mem fl_RgM.
Proof using.
intros regs1 regs0 s f fb more mem g H Hlo Hhi Hobj. unfold fl_RgM, fl_litsG, A_X.
eapply (region_ok_obj_gen ubs0segs _ mem 80 g 96 0 0 LAY_CGIF (cgif_vals s) 45 (litsG None None None None));
[exact H | lia | lia | exact Hobj | reflexivity | | apply (litsG_ok s); exact I | intros k Hk; lia].
intros j v Hj. apply (fl_HX regs1 regs0 s f fb more (45 + j) j v eq_refl Hj).
Qed.
Lemma fl_RfM_ok : forall regs1 regs0 s f fb more mem p,
bv_unsigned (ew (fl_E regs1 regs0 s f fb more) 81) = p -> 0 <= p -> p + 40 <= 2 ^ 64 ->
obj_at ubs0segs mem p LAY_Frame (frame_vals f) -> region_ok ubs0segs (fl_E regs1 regs0 s f fb more) mem fl_RfM.
Proof using.
intros regs1 regs0 s f fb more mem p H Hlo Hhi Hobj. unfold fl_RfM, A_F.
eapply (region_ok_obj_gen ubs0segs _ mem 81 p 40 0 0 LAY_Frame (frame_vals f) 62 []);
[exact H | lia | lia | exact Hobj | reflexivity | | intros [|j] z Hz; discriminate Hz | intros k Hk; lia].
intros j v Hj. apply (fl_HF regs1 regs0 s f fb more (62 + j) j v eq_refl Hj).
Qed.
Definition fl_cfg_stk (u : Z) : list YP09.chunk :=
fl_stk_saved 32 ++ [mkChunk 56 (CVal 8 (SLit u)); mkChunk 96 (CVal 8 (SOff 82 0)); mkChunk 112 (CVal 8 (SOff 80 0));
mkChunk 120 (CVal 8 (SOff 81 0)); mkChunk 128 (CVal 8 (SOff 62 0)); mkChunk 136 (CVal 8 (SOff 83 0))].
Definition ss_cfg (u : Z) : sstate :=
mkSS FL_CFG sr_atoms
[ YP09.mkRegion (Some 2%nat) 0 272 0 168 (fl_cfg_stk u) ; fl_RgM ; fl_RfM ] None
(mkFacts (fl_factsM ++ fl_gfacts ++ fl_ffacts ++ [(23%nat, mkAF 1 65535 0); (16%nat, mkAF 1 65535 0); (83%nat, mkAF 4096 CEIL_MAX 0)]) [] []).
Lemma fok_eq : forall segs mem a fd v' v, field_ok segs mem a fd v' -> v' = v -> field_ok segs mem a fd v.
Proof using. intros segs mem a fd v' v H <-. exact H. Qed.
End c.
Ltac stfld HS HU2 OFF N M :=
eapply fok_eq; [ eapply (st_field_low ubs0segs _ _ _ 0 _ 2 _ OFF N _ M HS);
[ reflexivity | reflexivity | cbn [r_chunks]; repeat (first [left; reflexivity | right]) | exact HU2 | cbn; lia | reflexivity ] | ].
Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma chunk_word : forall E mem base off e v,
chunk_ok ubs0segs E mem base (mkChunk off (CVal 8 e)) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
word_mem ubs0segs mem (base + off) v.
Proof using.
intros E mem base off e v Hc He Hv. apply val_mem_word_mem.
eapply (val_of_chunk_ok ubs0segs E mem base off 8%N e); [exact Hc | exact He | cbn; lia | cbn; lia].
Qed.
Definition FL_IMG : Z := Eval vm_compute in (ubs0_A_flushFrame + 0xa44).
Definition fl_raw_stk (r2 : bool) : list YP09.chunk :=
fl_stk_saved 32 ++ [mkChunk 16 (CVal 8 (SOff 86 0)); mkChunk 24 (CVal 8 (SOff 83 0)); mkChunk 32 (CVal 8 (SOff 69 0));
mkChunk 56 (CVal 8 (SOff 87 0)); mkChunk 96 (CVal 8 (SOff 82 0)); mkChunk 112 (CVal 8 (SOff 80 0)); mkChunk 120 (CVal 8 (SOff 81 0))] ++
(if r2 then [mkChunk 40 (CVal 8 (SOff 84 0)); mkChunk 48 (CVal 8 (SOff 85 0))] else []).
Definition ss_raw (pc : Z) (pz r2 : bool) : sstate :=
mkSS pc (if pz then sr_set sr_atoms 8%bv (SLit 0) else sr_atoms)
[ YP09.mkRegion (Some 2%nat) 0 272 0 168 (fl_raw_stk r2) ; fl_RgM ; fl_RfM ] None
(mkFacts (fl_factsM ++ fl_gfacts ++ fl_ffacts ++ (if pz then [] else [(8%nat, mkAF 1 (2^64 - 1) 0)])) [] []).
End l.
Ltac get_HS := match goal with H : st_ok _ _ _ _ |- _ => H end.
Ltac get_HJ := match goal with H : journal _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => H end.
Ltac get_HF := match goal with H : frame_of _ _ _ _ |- _ => H end.
Ltac rgq HS :=
lazymatch goal with |- getr _ ?r = _ =>
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
rewrite (st_ok_reg segs E ss ms r HS);
match goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ assumption | reflexivity | match goal with H : ?x = 0 |- _ = Z_to_bv 64 ?x => rewrite H; reflexivity end ]
end end.
Ltac clear_HG := repeat match goal with H : mem_grows _ _ |- _ => clear H end.
Ltac runW LAWS stop WRT HU2 lo hi :=
let HS := get_HS in let HJ := get_HJ in
jrun_to LAWS ubs0tbl_ok HS HJ stop; [WRT |];
let HF := get_HF in
cbn [ms_mem mkst] in HF; clear_HG;
lazymatch goal with K : forall a, _ -> _ -> mbyte ubs0segs ?m a = mbyte ubs0segs ?m0 a |- _ =>
lazymatch type of HF with frame_of ?E1 ?rs m ?m2 =>
let K2 := fresh "K" in
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> mbyte ubs0segs m2 a = mbyte ubs0segs m0 a);
[ intros a Ha Hna; try rewrite <- (K a Ha Hna);
apply (mbyte_of_frame E1 rs m m2 a HF Ha);
intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; repeat (rewrite ew_havoc_old; [|cbv; lia]); rewrite ?HU2; lia |]); destruct Hr
| clear HF K ]
end
end.
Ltac clear_Hc := match goal with H : branch_taken _ _ _ = _ |- _ => clear H end.
Ltac br_tree RUN LEAF n :=
lazymatch n with
| O => fail "br_tree: out of depth"
| Datatypes.S ?m => RUN; first [ LEAF | let HS := get_HS in jbranch ubs0tbl HS; [ clear_Hc; br_tree RUN LEAF m | clear_Hc; br_tree RUN LEAF m ] ]
end.
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition hidePs (P : Prop) : Prop := P.
Lemma land_shr2_2 : forall Y a : Z, 0 <= Y -> 0 <= a -> Y mod 2 ^ 32 = a mod 2 ^ 32 -> Z.land (Z.shiftr Y 2) 2 = Z.land (Z.shiftr a 2) 2.
Proof using.
intros Y a HY Ha Hm. apply Z.bits_inj'. intros n Hn.
rewrite !Z.land_spec, !Z.shiftr_spec by lia.
destruct (Z.eq_dec n 1) as [-> | Hne].
- change (1 + 2) with 3. rewrite <- (Z.mod_pow2_bits_low Y 32 3), <- (Z.mod_pow2_bits_low a 32 3), Hm by lia. reflexivity.
- replace (Z.testbit 2 n) with false; [rewrite !Bool.andb_false_r; reflexivity|].
symmetry. destruct (Z.eq_dec n 0) as [-> | Hn0]; [reflexivity|].
rewrite (Z.testbit_false 2 n) by lia.
assert (2 < 2 ^ n) by (apply Z.le_lt_trans with (m := n); [lia | apply Z.pow_gt_lin_r; lia]). rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma land_shr2_2_cases : forall a, Z.land (Z.shiftr a 2) 2 = 0 \/ Z.land (Z.shiftr a 2) 2 = 2.
Proof using.
intros a. destruct (Z.testbit (Z.shiftr a 2) 1) eqn:Eb.
- right. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. destruct (Z.eq_dec n 1) as [->|Hne]; [rewrite Eb; reflexivity|].
replace (Z.testbit 2 n) with false; [apply Bool.andb_false_r|]. symmetry. destruct (Z.eq_dec n 0) as [->|Hn0]; [reflexivity|].
rewrite (Z.testbit_false 2 n) by lia. assert (2 < 2 ^ n) by (apply Z.le_lt_trans with (m := n); [lia | apply Z.pow_gt_lin_r; lia]). rewrite Z.div_small by lia. reflexivity.
- left. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0. destruct (Z.eq_dec n 1) as [->|Hne]; [rewrite Eb; reflexivity|].
replace (Z.testbit 2 n) with false; [apply Bool.andb_false_r|]. symmetry. destruct (Z.eq_dec n 0) as [->|Hn0]; [reflexivity|].
rewrite (Z.testbit_false 2 n) by lia. assert (2 < 2 ^ n) by (apply Z.le_lt_trans with (m := n); [lia | apply Z.pow_gt_lin_r; lia]). rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma U_rattr : forall E a t, ew E 64 = Z_to_bv 64 a -> 0 <= a < 2 ^ 32 -> ew E 10 = Z_to_bv 64 t -> (t = 0 \/ t = 1) ->
U E (SAlu ALU_OR (SAlu ALU_AND (SAlu ALU_SRL (SExt true 32 (SOff 64 0)) (SLit 2)) (SLit 2)) (SOff 10 0)) mod 2 ^ 32 = Z.lor (Z.land (Z.shiftr a 2) 2) t.
Proof using.
intros E a t H64 Ha H10 Ht.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SExt. cbn [Z.of_N]. rewrite (U_atom _ 64 a H64) by lia. rewrite (U_atom _ 10 t H10) by lia. rewrite !U_SLit.
change (zcanon 2) with 2. change (Z.land 2 63) with 2. rewrite (Z.mod_small a) by lia.
set (Y := zcanon (bv_swrap 32 a)).
assert (HY : 0 <= Y < 2 ^ 64) by (subst Y; apply zcanon_range).
assert (HYm : Y mod 2 ^ 32 = a mod 2 ^ 32).
{ subst Y. rewrite zcanon_wrap. unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
rewrite (Z.mod_mod_divide _ (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity).
rewrite Zminus_mod, Z.mod_mod, <- Zminus_mod by lia.
replace (a + 2 ^ 31 - 2 ^ 31) with a by lia. reflexivity. }
assert (HM64 : M64 = 2 ^ 64) by reflexivity.
rewrite (zcanon_id (Z.shiftr Y 2)) by (rewrite HM64; split; [apply Z.shiftr_nonneg; lia | rewrite Z.shiftr_div_pow2 by lia; apply Z.div_lt_upper_bound; lia]).
rewrite (land_shr2_2 Y a) by (try lia; rewrite HYm, Z.mod_small by lia; reflexivity).
pose proof (land_shr2_2_cases a) as Hl2.
assert (Hor : 0 <= Z.lor (Z.land (Z.shiftr a 2) 2) t < 4).
{ clear - Hl2 Ht. destruct Hl2 as [E2|E2]; rewrite E2; destruct Ht as [E1|E1]; rewrite E1;
match goal with |- 0 <= ?x < 4 => let v := eval vm_compute in x in change x with v end; lia. }
rewrite (zcanon_id (Z.land (Z.shiftr a 2) 2)) by (rewrite HM64; clear - Hl2; lia).
rewrite zcanon_id by (rewrite HM64; clear - Hor; lia). apply Z.mod_small. clear - Hor; lia.
Qed.
Lemma rattr_model : forall a t, (t = 0 \/ t = 1) ->
Z.lor (Z.land (Z.shiftr a 2) 2) t = t + (if YO07.flag a 8 then 2 else 0).
Proof using.
intros a t Ht. unfold YO07.flag.
assert (H8 : Z.land a 8 = 0 <-> Z.land (Z.shiftr a 2) 2 = 0).
{ split; intros H; apply Z.bits_inj'; intros n Hn; rewrite Z.bits_0, Z.land_spec.
- rewrite Z.shiftr_spec by lia. destruct (Z.eq_dec n 1) as [->|Hne].
+ apply (f_equal (fun z => Z.testbit z 3)) in H. rewrite Z.bits_0, Z.land_spec in H. change (Z.testbit 8 3) with true in H. rewrite Bool.andb_true_r in H.
change (1 + 2) with 3. rewrite H. reflexivity.
+ replace (Z.testbit 2 n) with false; [apply Bool.andb_false_r|]. symmetry. destruct (Z.eq_dec n 0) as [->|Hn0]; [reflexivity|].
rewrite (Z.testbit_false 2 n) by lia. assert (2 < 2 ^ n) by (apply Z.le_lt_trans with (m := n); [lia | apply Z.pow_gt_lin_r; lia]). rewrite Z.div_small by lia. reflexivity.
- destruct (Z.eq_dec n 3) as [->|Hne].
+ apply (f_equal (fun z => Z.testbit z 1)) in H. rewrite Z.bits_0, Z.land_spec, Z.shiftr_spec in H by lia. change (Z.testbit 2 1) with true in H.
rewrite Bool.andb_true_r in H. change (1 + 2) with 3 in H. rewrite H. reflexivity.
+ replace (Z.testbit 8 n) with false; [apply Bool.andb_false_r|]. symmetry.
destruct (Z.lt_ge_cases n 3) as [Hlt|Hge].
* destruct (Z.eq_dec n 0) as [->|H0]; [reflexivity|]. destruct (Z.eq_dec n 1) as [->|H1]; [reflexivity|]. destruct (Z.eq_dec n 2) as [->|H2]; [reflexivity|]. lia.
* rewrite (Z.testbit_false 8 n) by lia. assert (8 < 2 ^ n) by (change 8 with (2 ^ 3); apply Z.pow_lt_mono_r; lia). rewrite Z.div_small by lia. reflexivity. }
pose proof (land_shr2_2_cases a) as [E2|E2]; rewrite E2.
- destruct (Z.eqb_spec (Z.land a 8) 0) as [E8|E8]; [| exfalso; apply E8; apply H8; exact E2]. cbn. destruct Ht as [->| ->]; reflexivity.
- destruct (Z.eqb_spec (Z.land a 8) 0) as [E8|E8]; [exfalso; pose proof (proj1 H8 E8); lia|]. cbn. destruct Ht as [->| ->]; reflexivity.
Qed.
Lemma U_sext16_field : forall E n d, ew E n = Z_to_bv 64 d -> 0 <= d < 2 ^ (8 * 2) -> U E (SExt true 16 (SOff n 0)) mod 2 ^ 16 = d.
Proof using.
intros E n d Hn Hd.
rewrite U_SExt. cbn [Z.of_N]. rewrite (U_atom _ n d Hn) by lia.
rewrite (Z.mod_small d) by lia. rewrite zcanon_wrap.
unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 16) with (2 ^ 16). change (bv_half_modulus 16) with (2 ^ 15).
rewrite (Z.mod_mod_divide _ (2 ^ 64) (2 ^ 16)) by (exists (2 ^ 48); reflexivity).
rewrite Zminus_mod, Z.mod_mod, <- Zminus_mod by lia.
replace (d + 2 ^ 15 - 2 ^ 15) with d by lia. apply Z.mod_small. lia.
Qed.
End p.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (hidePs (A \/ B)) in H end.
Section a0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis RAWADDX : rawadd_specX API.
Lemma fl_ret :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f : frame_st) (rest FP : list (Z * Z))
(S GPAL : list Z) (cur : YO07.frame) (bef : option YO07.frame) (b : rbound) (code : Z) (bytes : list Z),
let sp0 := spZ regs0 in
journal ubs0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 ->
cgif_at memc g (flush_upd s i (fl_gen3 (gcfg_of s GPAL) cur bef) (code mod 2 ^ 32)) -> cgif_wf s N -> nth_error (cg_frames s) i = Some (Some f) ->
Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ rest) ->
fl_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 272) -> fl_untouched regs0 regs1 ->
getr regs1 9 = Z_to_bv 64 code ->
YO07.flush_frame (gcfg_of s GPAL) (rc_int (rw_cur s)) cur bef = (code, bytes) ->
sink_at ubs0_msyms memc mdc (cg_file s) (S ++ bytes) -> Z.of_nat (length bytes) <= FRAME_OUT N ->
res_ok Ac (flush_rb b) ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_RET) memc (seg_rom ubs0segs)) mdc) (fl_post API regs0 g s N i rest FP S GPAL cur bef b L A mem md).
Proof using IMG.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f rest FP S GPAL cur bef b code bytes sp0 HJ Hid Hra0 Hal16 Hat Hwf Hf HB HSV G2 [G3 G4]
G8 HFL HSK HLEN HRq.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (E := Ereg regs1 (map (Z_to_bv 64) (fl_saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HK : forall j v, nth_error (fl_saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HKr : forall n j (r : reg), n = (32 + j)%nat -> nth_error FL_SAVED j = Some r -> ew E n = getr regs0 r).
{ intros n j r -> Hr. rewrite (HK j _ (fl_saved_vals_nth regs0 j r Hr)). apply Z_to_bv_bv_unsigned. }
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HR0 : region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 0 272 0 0 (fl_stk_saved 32))).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply (fl_saved_chunks_ok E memc sp0 regs0 32 HSV HK). }
assert (HFA : atoms_ok E [ (2%nat, mkAF (CEIL_MIN + FLUSH_STK - 272) (2^63 - 272) 4) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2. change (2 ^ 4) with 16.
repeat split; try lia. replace (sp0 - 272) with (sp0 + (-17) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
assert (HS : st_ok ubs0segs E ss_flret (mkst regs1 (Z_to_bv 64 FL_RET) memc (seg_rom ubs0segs))).
{ unfold ss_flret. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | cbn [pairwise_disjoint all_disjoint]; split; exact I | split; [exact HFA | split; exact I]].
constructor; [exact HR0 | constructor]. }
clear HR0 HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_RET) memc (seg_rom ubs0segs))) in HJ.
jrun LAWS ubs0tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
unfold fl_post.
lazymatch type of HS with st_ok _ _ _ ?msf => exists Lc, Ac, (ms_regs msf), (ms_mem msf), mdc, (bv_unsigned (getr regs1 9)), (code mod 2 ^ 32) end.
split. { cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg ubs0segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
rewrite ?Z.add_0_r, (HKr 32%nat 0%nat 1%bv eq_refl eq_refl), Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra0; reflexivity end. }
split. { cbn [ms_mem mkst]. exact HJ. }
split.
{ apply regs_preserved_intro; cbn [ms_regs mkst].
- reg_nowF HS ltac:(rewrite HU2; replace (sp0 - 272 + 272) with sp0 by lia; subst sp0; unfold spZ; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
- reg_nowF HS ltac:(rewrite (HKr 33%nat 1%nat 8%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 34%nat 2%nat 9%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 35%nat 3%nat 18%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 36%nat 4%nat 19%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 37%nat 5%nat 20%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 38%nat 6%nat 21%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 39%nat 7%nat 22%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 40%nat 8%nat 23%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 41%nat 9%nat 24%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 42%nat 10%nat 25%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 43%nat 11%nat 26%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite (HKr 44%nat 12%nat 27%bv eq_refl eq_refl); apply Z_to_bv_bv_unsigned). }
split; [exact Hid|].
split. { cbn [ms_regs mkst]. reg_nowF HS ltac:(rewrite (HE 9%nat 9%bv eq_refl); reflexivity). }
split; [apply u64_range_getr|].
assert (Hlow : forall a, 0 <= a < alloc_ceiling -> mbyte ubs0segs (ms_mem (mkst regs1 (Z_to_bv 64 FL_RET) memc (seg_rom ubs0segs))) a = mbyte ubs0segs memc a).
{ intros a Ha. cbn [ms_mem mkst]. reflexivity. }
split.
{ cbn [ms_mem mkst]. lazymatch goal with |- cgif_at ?m' g ?s' =>
eapply (cgif_at_low0 _ memc m' g s' N Lc Ac memc mdc rest HH0 _ Hat) end.
intros a Ha. cbn [ms_mem mkst] in HF. unfold mbyte.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
split; [exact (cgif_wf_flush_upd s N i _ _ f Hf Hwf) |]. split; [exact HB|].
split; [| exact HRq].
exists code, bytes. split; [exact HFL|]. split; [rewrite Z_to_bv_bv_unsigned; exact G8|]. split; [reflexivity|]. split; [| exact HLEN].
cbn [ms_mem mkst]. cbn [ms_mem mkst] in HF.
apply (sink_at_frame ubs0_msyms memc _ mdc (cg_file s) (S ++ bytes)); [|exact HSK].
intros a Ha. unfold mbyte.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity.
Unshelve. rewrite (cgif_blocks_flush_upd0 g s N i _ _ f Hf). exact HB.
Qed.
Lemma fl_cfg :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f : frame_st)
(rest FP FPw tmp : list (Z * Z)) (pTmp Nt tv img w h : Z)
(S GPAL : list Z) (cur : YO07.frame) (bef : option YO07.frame) (bfr : option frame_st) (b bc : rbound) (top left hastrans : Z),
let sp0 := spZ regs0 in
let G := gcfg_of s GPAL in
let gen1 := fl_gen3 G cur bef in
journal ubs0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
cgif_at memc g (flush_upd s i gen1 (rw_cur s)) -> cgif_wf s N -> (i = 1%nat \/ i = 2%nat) -> nth_error (cg_frames s) i = Some (Some f) ->
fl_fp FP s f ->
Permutation (blocks Lc Ac) (tmp ++ cgif_blocks0 g s N ++ rest) ->
((tmp = [] /\ pTmp = 0 /\ img = fr_img f /\ w * h <= N) \/ (tmp = [(pTmp, Nt)] /\ pTmp <> 0 /\ img = pTmp /\ w * h <= Nt)) ->
(In (pTmp, Nt) (blocks L A) -> forall k, 0 <= k < Nt -> inFP FP (pTmp + k)) ->
1 <= w <= cg_W s -> 1 <= h <= cg_H s -> 0 <= tv < 2 ^ 64 ->
fl_saved_ok memc sp0 regs0 ->
word_mem ubs0segs memc (sp0 - 272 + 112) g -> word_mem ubs0segs memc (sp0 - 272 + 120) (fr_ptr f) ->
word_mem ubs0segs memc (sp0 - 272 + 128) (fr_lpal f) -> word_mem ubs0segs memc (sp0 - 272 + 136) img ->
word_mem ubs0segs memc (sp0 - 272 + 56) (Z.land (fr_attr f) 1) -> word_mem ubs0segs memc (sp0 - 272 + 96) top ->
getr regs1 2 = Z_to_bv 64 (sp0 - 272) -> getr regs1 8 = Z_to_bv 64 pTmp -> getr regs1 9 = Z_to_bv 64 tv ->
getr regs1 23 = Z_to_bv 64 w -> getr regs1 16 = Z_to_bv 64 h ->
fl_untouched regs0 regs1 ->
nth (i - 1) (cg_frames s) None = bfr ->
fl_sink g s N rest FP FPw S L A mem md sp0 ->
fl_vals memc s N f bfr GPAL cur bef ->
getr regs1 22 = Z_to_bv 64 left -> getr regs1 14 = Z_to_bv 64 (fr_disp f) -> getr regs1 10 = Z_to_bv 64 hastrans ->
w = fl_w G cur bef -> h = fl_h G cur bef -> top = fl_top G cur bef -> left = fl_left G cur bef ->
0 <= top -> top + h <= cg_H s -> 0 <= left -> left + w <= cg_W s ->
hastrans = (if (fl_hasAlpha G cur || fl_trans_on G cur bef || fl_hasSet cur)%bool then 1 else 0) ->
tv mod 256 = fl_tidx G cur bef ->
garr8 ubs0segs memc img (fl_img G cur bef) -> Z.of_nat (length (fl_img G cur bef)) = w * h ->
res_ok Ac bc -> rawadd_room bc (w * h) ->
(pTmp = 0 -> rb_le (rawadd_rb bc) (flush_rb b)) -> (pTmp <> 0 -> rb_le (rb_free (rawadd_rb bc) Nt) (flush_rb b)) ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 FL_CFG) memc (seg_rom ubs0segs)) mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur bef b L A mem md).
Proof using IMG RAWADDX.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f rest FP FPw tmp pTmp Nt tv img w h S GPAL cur bef bfr b bc top left hastrans sp0 G gen1
HJ Hid Hra0 Hal16 Htp0 Hat Hwf Hi Hf HFP HB Htmp Htmp_fp Hw Hh Htv HSV Wg Wfr Wlct Wimg Wu Wtop G2 G8 G9 G23 G16 [G3 G4]
Hbfr HSINK HVALS G22 G14 G10 Xw Xh Xtop Xleft Htop0 Htop1 Hleft0 Hleft1 Xhas Xtv XIMG XIMGL HRq HRM HRB0 HRB1.
pose proof HSINK as (HSK0 & HSroom & Hsp47 & HfinLA & Hfrest & HFPtok & HFPav & HFPsub & HFPsink).
pose proof HVALS as (HVg & HVf & HVb & HVra).
pose proof HVf as (XA1 & XA2 & XA3 & XA4 & XA5 & XA6 & XA7 & XVI & XVIl & HVlp). cbn [YO07.f_attr YO07.f_gen] in XA1, XA2.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity. assert (HRSv : RAWADD_STK = 8704) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRWv : RAW_SIZE = 48) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & Hih & Hfwf).
set (s1 := flush_upd s i gen1 (rw_cur s)) in Hat. set (f1 := set_fr_gen f gen1).
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
assert (Hfr1 : cg_frames s1 = list_set (cg_frames s) i (Some f1)) by (subst s1 f1; apply cg_frames_flush_upd; exact Hf).
assert (Hf1in : In (Some f1) (cg_frames s1)) by (rewrite Hfr1; eapply nth_error_In; apply nth_error_list_set_same; exact Hilt).
assert (HBc : Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ (tmp ++ rest))).
{ eapply Permutation_trans; [exact HB|]. apply Permutation_app_swap_app. }
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N _ HH0 HBc) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom f Hfin) as (Hp0 & Hp1 & Hpg).
pose proof (af_raw_frame_sep0 API Lc Ac memc mdc g s N _ f HH0 HBc Hfin) as Hpr.
destruct (fl_img_geom0 API Lc Ac memc mdc g s N _ f HH0 HBc Hfin ltac:(rewrite HN; clear - HW1 HH1; nia)) as [Him0 Him1].
pose proof Hat as (Hobj & Hraw & Hfrs). rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s) : cgif_vals s1 = cgif_vals s) in Hobj.
change (cg_raw s1) with (cg_raw s) in Hraw.
pose proof (Hfrs f1 Hf1in) as Hfobj. change (fr_ptr f1) with (fr_ptr f) in Hfobj.
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (obj_at_range _ _ _ _ _ Hfobj) as Rf.
pose proof (Rf 0%nat (fr_lpal f) eq_refl) as Rlpal. pose proof (Rf 2%nat (fr_attr f) eq_refl) as Rfattr. pose proof (Rf 5%nat (fr_nlp f) eq_refl) as Rnlp.
cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rlpal, Rfattr, Rnlp.
pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. cbn [nth snd LAY_CGIF Z.of_N] in RW, RH.
assert (Himg : 4096 <= img /\ img + w * h <= alloc_ceiling /\ In (img, if pTmp =? 0 then N else Nt) (blocks Lc Ac)).
{ destruct Htmp as [(-> & -> & -> & Hle) | (-> & Hnz & -> & Hle)].
- rewrite Z.eqb_refl. split; [lia|]. split; [clear - Him1 Hle Hw Hh; nia|].
apply (Permutation_in _ (Permutation_sym HBc)). apply in_app_iff. left. apply (frame_blocks_in_cgif0 g s N f); [exact Hfin | right; left; reflexivity].
- destruct (Z.eqb_spec pTmp 0); [lia|].
assert (Hin : In (pTmp, Nt) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); left; reflexivity).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pTmp Nt HH0 Hin) as [T0 T1]. split; [lia|]. split; [clear - T1 Hle Hw Hh; nia | exact Hin]. }
destruct Himg as (Him0' & Him1' & Himgin).
clear Hih Hi.
assert (Ht0 : pTmp = 0 -> tmp = [] /\ img = fr_img f /\ w * h <= N) by (intros H0; destruct Htmp as [(A1 & A2 & A3 & A4)|(A1 & A2 & A3 & A4)]; [auto | lia]).
assert (Ht1 : pTmp <> 0 -> tmp = [(pTmp, Nt)] /\ img = pTmp /\ w * h <= Nt) by (intros H0; destruct Htmp as [(A1 & A2 & A3 & A4)|(A1 & A2 & A3 & A4)]; [lia | auto]).
clear Htmp.
hide_disj.
set (u := Z.land (fr_attr f) 1) in Wu.
assert (Hu01 : 0 <= u <= 1) by (subst u; pose proof (land1_cases (fr_attr f) ltac:(clear - Rfattr; lia)); lia).
set (E := fl_E regs1 regs0 s f1 None [g; fr_ptr f; top; img]).
pose proof (fl_HE regs1 regs0 s f1 None [g; fr_ptr f; top; img] : forall n rr, _ -> ew E n = _) as HE.
pose proof (fl_HK regs1 regs0 s f1 None [g; fr_ptr f; top; img] : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (fl_HKr regs1 regs0 s f1 None [g; fr_ptr f; top; img] : forall n j r, _ -> _ -> ew E n = _) as HKr.
pose proof (fl_HX regs1 regs0 s f1 None [g; fr_ptr f; top; img] : forall n j v, _ -> _ -> ew E n = _) as HX.
pose proof (fl_HF regs1 regs0 s f1 None [g; fr_ptr f; top; img] : forall n j v, _ -> _ -> ew E n = _) as HFf.
pose proof (fl_HM regs1 regs0 s f1 None [g; fr_ptr f; top; img] : forall n j v, _ -> _ -> ew E n = _) as HM.
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HE80 : ew E 80 = Z_to_bv 64 g) by (apply (HM 80%nat 0%nat g eq_refl eq_refl)).
assert (HE81 : ew E 81 = Z_to_bv 64 (fr_ptr f)) by (apply (HM 81%nat 1%nat (fr_ptr f) eq_refl eq_refl)).
assert (HE82 : ew E 82 = Z_to_bv 64 top) by (apply (HM 82%nat 2%nat top eq_refl eq_refl)).
assert (HE83 : ew E 83 = Z_to_bv 64 img) by (apply (HM 83%nat 3%nat img eq_refl eq_refl)).
assert (HU80 : bv_unsigned (ew E 80) = g) by (rewrite HE80; apply unsigned_lit_small; lia).
assert (HU81 : bv_unsigned (ew E 81) = fr_ptr f) by (rewrite HE81; apply unsigned_lit_small; lia).
assert (HE62 : ew E 62 = Z_to_bv 64 (fr_lpal f)) by (apply (HFf 62%nat 0%nat _ eq_refl eq_refl)).
assert (HR0 : region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 0 272 0 168 (fl_cfg_stk u))).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
unfold fl_cfg_stk. apply Forall_app; split; [apply (fl_saved_chunks_ok E memc sp0 regs0 32 HSV); intros j v Hj; exact (HK _ j v eq_refl Hj)|].
constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ u); [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wu].
- eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, HE82, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wtop].
- eapply (chunk_ok_val _ _ _ _ _ _ _ g); [cbn [sv_denot]; rewrite Z.add_0_r, HE80, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wg].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_ptr f)); [cbn [sv_denot]; rewrite Z.add_0_r, HE81, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wfr].
- eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_lpal f)); [cbn [sv_denot]; rewrite Z.add_0_r, HE62, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wlct].
- eapply (chunk_ok_val _ _ _ _ _ _ _ img); [cbn [sv_denot]; rewrite Z.add_0_r, HE83, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wimg]. }
pose proof (fl_RgM_ok regs1 regs0 s f1 None [g; fr_ptr f; top; img] memc g HU80 ltac:(lia) ltac:(lia) Hobj) as HR1.
pose proof (fl_RfM_ok regs1 regs0 s f1 None [g; fr_ptr f; top; img] memc (fr_ptr f) HU81 ltac:(lia) ltac:(lia) Hfobj) as HR2.
assert (HPD : pairwise_disjoint E (ss_mem (ss_cfg u))).
{ cbn [ss_mem ss_cfg]. unfold fl_RgM, fl_RfM. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU80, HU81. clear - Hg1 Hp1 Hpg Hceil HFSv HGSv HFRv Hac; unfold hidePs in *. repeat split; lia. }
assert (HFA : atoms_ok E (fl_factsM ++ fl_gfacts ++ fl_ffacts ++ [(23%nat, mkAF 1 65535 0); (16%nat, mkAF 1 65535 0); (83%nat, mkAF 4096 CEIL_MAX 0)])).
{ apply atoms_ok_app; [| apply atoms_ok_app; [exact (fl_gfacts_ok regs1 regs0 s f1 None [g; fr_ptr f; top; img] memc g N Hobj Hwf ltac:(lia) ltac:(lia))
| apply atoms_ok_app; [exact (fl_ffacts_ok regs1 regs0 s f1 None [g; fr_ptr f; top; img] memc (fr_ptr f) Hfobj Him0 ltac:(change (fr_img f1) with (fr_img f); clear - Him1 HN HW1 HH1; nia)) |]]].
- cbn [atoms_ok fl_factsM]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU80, HU81.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia_try.
 + replace (sp0 - 272) with (sp0 + (-17) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16.
 + pose proof (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr f) FRAME_SIZE HH0 ltac:(apply (Permutation_in _ (Permutation_sym HBc)); apply in_app_iff; left; apply (frame_blocks_in_cgif0 g s N f); [exact Hfin | left; reflexivity]) ltac:(lia)) as (_ & _ & Hp16).
clear - Hp16. apply Z.mod_divide in Hp16; [|lia]. apply Z.mod_divide; [lia|]. destruct Hp16 as [q Hq]. exists (q * 2). lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (HE 23%nat 23%bv eq_refl), (HE 16%nat 16%bv eq_refl), G23, G16, HE83.
rewrite !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. try pose proof (proj1 alloc_ceiling_val) as HacR; clear - HacR Hw Hh RW RH Him0' Him1'. repeat split; try lia; nia. }
assert (HS : st_ok ubs0segs E (ss_cfg u) (mkst regs1 (Z_to_bv 64 FL_CFG) memc (seg_rom ubs0segs))).
{ unfold ss_cfg. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | exact HPD | split; [exact HFA | split; exact I]].
constructor; [exact HR0|]. constructor; [exact HR1|]. constructor; [exact HR2|]. constructor. }
clear HR0 HR1 HR2 HPD HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 FL_CFG) memc (seg_rom ubs0segs))) in HJ.
assert (WR : forall E0 cs, bv_unsigned (ew E0 2) = sp0 - 272 ->
wr_ok E0 [YP09.mkRegion (Some 2%nat) 0 272 0 168 cs; fl_RgM; fl_RfM] FLUSH_STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E0 cs H2. eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HBc)); left; reflexivity).
assert (Hrin : In (cg_raw s, RAW_SIZE) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HBc)); right; left; reflexivity).
assert (Hfr_any : forall x rcur, In (Some x) (cg_frames (flush_upd s i gen1 rcur)) ->
exists y, In (Some y) (cg_frames s) /\ fr_ptr y = fr_ptr x /\ In (Some x) (cg_frames s1)).
{ intros x rcur Hx. assert (Hx1 : In (Some x) (cg_frames s1)) by exact Hx.
destruct (In_frames_flush_upd s i gen1 rcur f x Hf Hx) as [-> | [Hin _]].
- exists f. split; [exact Hfin|]. split; [reflexivity | exact Hx1].
- exists x. split; [exact Hin|]. split; [reflexivity | exact Hx1]. }
assert (CG : forall (m3 : word -> option byte) rcur,
(forall a n k, In (a, n) (cgif_blocks0 g s N) -> 0 <= k < n -> ~ (cg_raw s + 40 <= a + k < cg_raw s + 44) ->
mbyte ubs0segs m3 (a + k) = mbyte ubs0segs memc (a + k)) ->
obj_at ubs0segs m3 (cg_raw s) LAY_Raw [ubs0_A_cgif_writecb; g; rw_gct s; rw_attr s; cg_W s; cg_H s; raw_sgct s; rw_loops s; rcur] ->
cgif_at m3 g (flush_upd s i gen1 rcur)).
{ intros m3 rcur KB Hraw3. split; [| split; [exact Hraw3|]].
- rewrite cgif_vals_flush_upd. eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) |].
intros k Hk. apply (KB g CGIF_SIZE k ltac:(left; reflexivity) ltac:(lia)). clear - Hrg Hk HGSv HRWv; unfold hidePs in *. lia.
- intros x Hx. destruct (Hfr_any x rcur Hx) as (y & Hy & Hyx & Hx1).
destruct (Hfgeom y Hy) as (Y0 & Y1 & Yg). pose proof (af_raw_frame_sep0 API Lc Ac memc mdc g s N _ y HH0 HBc Hy) as Yr.
eapply obj_at_transport_range; [exact (Hfrs x Hx1) | exact (proj1 LAY_Frame_ok) |].
intros k Hk. rewrite <- Hyx. apply (KB (fr_ptr y) FRAME_SIZE k); [| lia | clear - Yr Hk HFRv HRWv; unfold hidePs in *; lia].
apply (frame_blocks_in_cgif0 g s N y); [exact Hy | left; reflexivity]. }
assert (Hu : u = 0 \/ u = 1) by (clear - Hu01; lia). clear Hu01.
destruct Hu as [Hu | Hu]; rewrite Hu in HS, Wu.
all: jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cgif_raw_addframe; [apply WR; exact HU2|].
all: cbn [ms_mem mkst] in HF.
all: assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs memc a)
by (intros a Ha Hna; apply (mbyte_of_frame _ _ _ _ a HF Ha); intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; rewrite ?HU2; lia |]); destruct Hr).
all: clear HF HG.
all: jreg HS (10%bv:reg) as Ha0; rewrite (HX 58%nat 13%nat (cg_raw s) eq_refl eq_refl) in Ha0.
all: jreg HS (11%bv:reg) as Ha1; rewrite HU2 in Ha1.
all: jreg HS (2%bv:reg) as Hsp; rewrite (HE 2%nat 2%bv eq_refl), G2 in Hsp.
all: jreg HS (4%bv:reg) as Htp; rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Htp.
all: jreg HS (1%bv:reg) as Hra.
all: lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hspv : spZ (ms_regs msx) = sp0 - 272) by (unfold spZ; rewrite Hsp; apply unsigned_lit_small; lia) end.
all: assert (HE64 : ew E 64 = Z_to_bv 64 (fr_attr f)) by (apply (HFf 64%nat 2%nat _ eq_refl eq_refl)).
all: assert (HE66 : ew E 66 = Z_to_bv 64 (fr_delay f)) by (apply (HFf 66%nat 4%nat _ eq_refl eq_refl)).
all: assert (HE67 : ew E 67 = Z_to_bv 64 (fr_nlp f)) by (apply (HFf 67%nat 5%nat _ eq_refl eq_refl)).
all: pose proof (Rf 4%nat (fr_delay f) eq_refl) as Rdelay; pose proof (Rf 7%nat (fr_disp f) eq_refl) as Rdisp; cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rdelay, Rdisp.
all: assert (HE10 : ew E 10 = Z_to_bv 64 hastrans) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
all: assert (Hhas01 : hastrans = 0 \/ hastrans = 1) by (rewrite Xhas; destruct (fl_hasAlpha G cur || fl_trans_on G cur bef || fl_hasSet cur)%bool; clear; lia).
all: assert (Hcfg : obj_at ubs0segs (ms_mem ms) (sp0 - 272 + 128) LAY_RawFrameConfig
[fr_lpal f; img; Z.lor (Z.land (Z.shiftr (fr_attr f) 2) 2) hastrans; w; h; top; left; fr_delay f; u * fr_nlp f; fr_disp f; tv mod 256]);
[ apply (proj2 (obj_at_shift ubs0segs (ms_mem ms) (sp0 - 272) 128 LAY_RawFrameConfig _));
apply obj_at_of_fields; [reflexivity|]; intros j fd v Hj Hv;
assert (Hjlt : (j < length (lay_shift 128 LAY_RawFrameConfig))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate);
destruct j as [|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]; [..|cbn in Hjlt; liaND]; cbn in Hj, Hv; injection Hj as <-; injection Hv as <-;
[ stfld HS HU2 128 8%N (2 ^ 64); rewrite (U_atom _ 62 (fr_lpal f) HE62) by liaND; apply Z.mod_small; liaND
| stfld HS HU2 136 8%N (2 ^ 64); rewrite (U_atom _ 83 img HE83) by liaND; apply Z.mod_small; liaND
| stfld HS HU2 144 4%N (2 ^ 32); apply (U_rattr E (fr_attr f) hastrans HE64 ltac:(clear - Rfattr; liaND) HE10 Hhas01)
| stfld HS HU2 148 2%N (2 ^ 16); rewrite (U_atom _ 23 w ltac:(rewrite (HE 23%nat 23%bv eq_refl); exact G23)) by liaND; apply Z.mod_small; liaND
| stfld HS HU2 150 2%N (2 ^ 16); rewrite (U_atom _ 16 h ltac:(rewrite (HE 16%nat 16%bv eq_refl); exact G16)) by liaND; apply Z.mod_small; liaND
| stfld HS HU2 152 2%N (2 ^ 16); rewrite (U_atom _ 82 top HE82) by liaND; apply Z.mod_small; liaND
| stfld HS HU2 154 2%N (2 ^ 16); rewrite (U_atom _ 22 left ltac:(rewrite (HE 22%nat 22%bv eq_refl); exact G22)) by liaND; apply Z.mod_small; liaND
| stfld HS HU2 156 2%N (2 ^ 16); apply (U_sext16_field E 66 (fr_delay f) HE66 Rdelay)
| stfld HS HU2 158 2%N (2 ^ 16); first [ rewrite U_lit by liaND; rewrite Hu; reflexivity
| rewrite (U_atom _ 67 (fr_nlp f) HE67) by liaND; rewrite Hu, Z.mod_small by liaND; liaND ]
| stfld HS HU2 160 1%N (2 ^ 8); rewrite (U_atom _ 14 (fr_disp f) ltac:(rewrite (HE 14%nat 14%bv eq_refl); exact G14)) by liaND; apply Z.mod_small; liaND
| stfld HS HU2 161 1%N (2 ^ 8); rewrite (U_atom _ 9 tv ltac:(rewrite (HE 9%nat 9%bv eq_refl); exact G9)) by liaND; reflexivity ]
| ].
all: assert (Hperm : exists Nimg rest0, Permutation (blocks Lc Ac) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest0) /\
w * h <= Nimg /\ (Z.land (fr_attr f) 1 <> 0 -> In (fr_lpal f, 3 * fr_nlp f) rest0) /\ In (cg_file s, FILE_BLOCK) rest0);
[ destruct (Z.eq_dec pTmp 0) as [Hpz | Hpz];
[ destruct (Ht0 Hpz) as (Htm & Him & Hle); destruct (flush_blocks_img00 g s N rest i f Hf) as (rest0 & HP & HL & HRR);
exists N, rest0; split; [rewrite Him; eapply Permutation_trans; [exact HBc | rewrite Htm; exact HP] | split; [exact Hle | split; [exact HL | apply HRR; exact Hfrest]]]
| destruct (Ht1 Hpz) as (Htm & Him & Hle); destruct (flush_blocks_img10 g s N rest f pTmp Nt Hfin) as (rest0 & HP & HL & HRR);
exists Nt, rest0; split; [rewrite Him; eapply Permutation_trans; [exact HB | rewrite Htm; exact HP] | split; [exact Hle | split; [exact HL | apply HRR; exact Hfrest]]] ]
| ].
all: destruct Hperm as (Nimg & rest0 & Hperm & HleN & Hlct & Hfrest0).
all: assert (HSKc : sink_at ubs0_msyms (ms_mem ms) mdc (cg_file s) S /\ In (cg_file s, FILE_BLOCK) (blocks Lc Ac))
by (eapply (sink_kept ubs0_msyms MR); [exact HJ | exact HFPtok | exact HfinLA | exact HFPav | exact HSK0]).
all: destruct HSKc as [HSKc HfinC].
all: apply (journal_fp_weaken API FLUSH_STK sp0 FP FPw _ _ _ _ _ _ _ _ HFPsub) in HJ.
all: destruct (blocks_range _ _ LAWS Lc Ac memc mdc (cg_file s) FILE_BLOCK HH0 HfinC) as [Hf0 Hf1].
all: eapply SR_bind with (R := fun c' => exists L2 A2 regs2 mem2 md2 (res rcur : Z),
c' = mkCfg (mkst regs2 (Z_to_bv 64 FL_CALLRET) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR FLUSH_STK sp0 FPw L A mem md L2 A2 mem2 md2 /\
regs_preserved (ms_regs ms) regs2 /\ st_init_done A2 = true /\ getr regs2 10 = Z_to_bv 64 res /\
obj_at ubs0segs mem2 (cg_raw s) LAY_Raw [ubs0_A_cgif_writecb; g; rw_gct s; rw_attr s; cg_W s; cg_H s; raw_sgct s; rw_loops s; rcur] /\
Permutation (blocks L2 A2) (blocks Lc Ac) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 272 - RAWADD_STK <= x < sp0 - 272) ->
mbyte ubs0segs mem2 x = mbyte ubs0segs (ms_mem ms) x /\ (writable_at ubs0segs (ms_mem ms) x <-> writable_at ubs0segs mem2 x)) /\
(forall a n k, In (a, n) (blocks Lc Ac) -> 0 <= k < n -> ~ (cg_raw s + 40 <= a + k < cg_raw s + 44) -> ~ (cg_file s <= a + k < cg_file s + FILE_BLOCK) ->
mbyte ubs0segs mem2 (a + k) = mbyte ubs0segs (ms_mem ms) (a + k)) /\
(exists code bytes, YO07.raw_addframe (YO07.flag (rw_attr s) 1) (raw_sgct s) (rc_int (rw_cur s)) (fl_img G cur bef)
(Z.lor (Z.land (Z.shiftr (fr_attr f) 2) 2) hastrans) w h top left (fr_delay f) (u * fr_nlp f) (YO07.f_lpal cur) (fr_disp f) (tv mod 256) = (code, bytes) /\
Z_to_bv 64 res = Z_to_bv 64 code /\ rcur = code mod 2 ^ 32 /\ sink_at ubs0_msyms mem2 md2 (cg_file s) (S ++ bytes) /\ Z.of_nat (length bytes) <= 2 * (w * h) + 2048) /\
res_ok A2 (rawadd_rb bc)).
1,3: eapply SR_mono;
[ eapply (jcall ubs0_msyms MR) with (STK1 := RAWADD_STK) (FP1 := (cg_raw s + 40, cg_raw s + 44) :: sink_fp (cg_file s))
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => exists res rcur : Z,
st_init_done A2 = true /\ getr regs2 10 = Z_to_bv 64 res /\
obj_at ubs0segs mem2 (cg_raw s) LAY_Raw [ubs0_A_cgif_writecb; g; rw_gct s; rw_attr s; cg_W s; cg_H s; raw_sgct s; rw_loops s; rcur] /\
Permutation (blocks L2 A2) (blocks Lc Ac) /\
(exists code bytes, YO07.raw_addframe (YO07.flag (rw_attr s) 1) (raw_sgct s) (rc_int (rw_cur s)) (fl_img G cur bef)
(Z.lor (Z.land (Z.shiftr (fr_attr f) 2) 2) hastrans) w h top left (fr_delay f) (u * fr_nlp f) (YO07.f_lpal cur) (fr_disp f) (tv mod 256) = (code, bytes) /\
Z_to_bv 64 res = Z_to_bv 64 code /\ rcur = code mod 2 ^ 32 /\ sink_at ubs0_msyms mem2 md2 (cg_file s) (S ++ bytes) /\ Z.of_nat (length bytes) <= 2 * (w * h) + 2048) /\
res_ok A2 (rawadd_rb bc));
[ exact HS | reflexivity | exact HJ | exact Hra | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspv; replace (sp0 - 272) with (sp0 + (-17) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16
| clear - HRSv; lia | rewrite Hspv; clear - Hceil HFSv HRSv; lia | rewrite Hspv; lia | exact Htp
| intros a Ha; unfold inFP in Ha; cbn [In fst snd] in Ha; destruct Ha as (r & [<-|[<-|[<-|[]]]] & Hr); cbn [fst snd] in Hr;
[ split; [apply HFPsub; apply (proj1 HFP a); exact Hr | lia]
| split; [apply HFPsink; exists sink_token; split; [left; reflexivity | exact Hr] | unfold sink_token in Hr; cbn [fst snd] in Hr; lia]
| split; [apply HFPsink; exists (cg_file s, cg_file s + FILE_BLOCK); split; [right; left; reflexivity | exact Hr] | lia] ] ];
intros HPRE1; eapply SR_mono;
[ eapply (RAWADDX Lc Ac (ms_regs ms) (ms_mem ms) mdc (cg_raw s) g (sp0 - 272 + 128) (cgif_vals s)
(rw_gct s) (rw_attr s) (cg_W s) (cg_H s) (raw_sgct s) (rw_loops s) (rw_cur s)
(fr_lpal f) img (Z.lor (Z.land (Z.shiftr (fr_attr f) 2) 2) hastrans) w h top left (fr_delay f) (u * fr_nlp f) (fr_disp f) (tv mod 256)
Nimg rest0 (cg_file s) S (fl_img G cur bef) (YO07.f_lpal cur) bc HPRE1 Hid Hfrest0 HSKc);
[ unfold FRAME_OUT in HSroom; clear - HSroom Hw Hh HN HW1 HH1; nia
| rewrite Hspv; eapply Z.le_trans; [| exact Hsp47]; clear; lia
| exact Ha0 | exact Ha1
| clear - Hal16; apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hal16; [|lia]; destruct Hal16 as [q Hq]; exists (q * 2 - 18); lia
| rewrite Hspv; clear; lia | clear - Hsp063; lia | exact Hcfg
| eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) | intros k Hk; apply K1; lia]
| unfold raw_sgct; destruct (Z.eqb_spec (Z.land (cg_attr s) 4) 0); [apply Hngp; assumption | lia]
| eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk; apply K1; lia]
| reflexivity | reflexivity | clear - Hw; lia | clear - Hh; lia | clear - Hw Hh HN HNle; nia | exact HleN | exact Hperm
| intros Hs; assert (Hu1 : u = 1) by (clear - Hs Hu Rnlp; rewrite Hu in Hs |- *; lia);
assert (Ha1' : Z.land (fr_attr f) 1 <> 0) by (change (Z.land (fr_attr f) 1) with u; rewrite Hu1; clear; lia);
destruct (HVlp Ha1') as [HLP HLPl]; pose proof (Hlct Ha1') as Hlin;
assert (Hlin' : In (fr_lpal f, 3 * fr_nlp f) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym Hperm)); right; right; right; exact Hlin);
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 Hlin') as [Hl0 Hl1];
exists (3 * fr_nlp f); rewrite Hu1, Z.mul_1_l; split; [exact Hlin|]; split; [clear; lia|];
split;
[ intros Heq; injection Heq as Hp Hn; clear - Hn; assert (FB : FILE_BLOCK = 1264) by reflexivity; lia
| split; [ eapply garr8_frame; [exact HLP|]; intros a Ha; apply K1; clear - Ha Hl0 Hl1 HLPl Hceil Hsp063 HFSv Hac; lia | rewrite HLPl; clear; lia ] ]
| eapply garr8_frame; [exact XIMG|]; intros a Ha; apply K1; clear - Ha Him0' Him1' Hceil Hsp063 HFSv Hac XIMGL Hw Hh; lia
| exact XIMGL | exact HRq | exact HRM ]
| cbv beta; intros c' (L2 & A2 & regs2 & mem2 & md2 & res & rcur & -> & HJc & HP & Hid2 & Hr10 & Hraw2 & HB2 & HVAL & HRq2);
exists L2, A2, regs2, mem2, md2; split; [rewrite Hra; reflexivity|]; split; [exact HJc|]; split; [exact HP|];
exists res, rcur; split; [exact Hid2|]; split; [exact Hr10|]; split; [exact Hraw2|]; split; [exact HB2|]; split; [exact HVAL | exact HRq2] ]
| cbv beta; intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (res & rcur & Hid2 & Hr10 & Hraw2 & HB2 & HVAL & HRq2));
exists L2, A2, regs2, mem2, md2, res, rcur; split; [reflexivity|]; split; [exact HJ2|]; split; [exact HP2|]; split; [exact Hid2|]; split; [exact Hr10|];
split; [exact Hraw2|]; split; [exact HB2|];
pose proof HJc2 as (_ & _ & Hhi2 & Hblk2 & _); rewrite Hspv in Hhi2; split; [exact Hhi2|]; split; [| split; [exact HVAL | exact HRq2]];
intros a n k Hin Hk Hnot Hnotf; apply (Hblk2 a n k Hin); [apply (Permutation_in _ (Permutation_sym HB2)); exact Hin | exact Hk |];
unfold inFP; cbn [In fst snd]; intros (r & [<-|[<-|[<-|[]]]] & Hr); cbn [fst snd] in Hr; [lia | unfold sink_token in Hr; cbn [fst snd] in Hr | lia];
destruct (blocks_range _ _ LAWS Lc Ac memc mdc a n HH0 Hin) as [Ba0 Ba1]; clear - Ba0 Hr Hk; lia ].
all: cbv beta; intros c' (L2 & A2 & regs2 & mem2 & md2 & res & rcur & -> & HJ2 & HP2 & Hid2 & Hr10 & Hraw2 & HB2 & Hhi2 & Hblk2 & (code & bytes & HRA & Hres & Hrcur & HSK2 & HLEN2) & HRq2); clear HJ.
all: cbn [ms_regs ms_mem mkst] in HP2, Hhi2, HJ2, Hblk2, Hr10, HSK2.
all: pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HH2.
all: jafter_call_keep HS 84%nat regs2 mem2 HP2 [0%nat] HS2.
all: match type of HS2 with ?P -> _ => assert (HKP : P); [|specialize (HS2 HKP); clear HKP] end;
[ constructor; [|constructor]; eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi2 | lia | lia | clear - HRSv; lia | cbn; lia | cbn; lia] |].
all: clear HS; rename HS2 into HS.
all: jrun_to LAWS ubs0tbl_ok HS HJ2 ubs0_A_free; [eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia | apply wr_ok_nil] |].
all: jreg HS (10%bv:reg) as Hf10; rewrite (HE 8%nat 8%bv eq_refl), G8 in Hf10.
all: jreg HS (2%bv:reg) as Hf2; rewrite (HE 2%nat 2%bv eq_refl), G2 in Hf2.
all: jreg HS (4%bv:reg) as Hf4; rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hf4.
all: jreg HS (1%bv:reg) as Hfra.
all: jreg HS (3%bv:reg) as Hf3; rewrite (HE 3%nat 3%bv eq_refl), G3 in Hf3.
all: jreg HS (9%bv:reg) as Hf9.
all: replace 88%nat with (84 + 4)%nat in Hf9 by reflexivity; rewrite (ew_havoc_new _ _ _ 4 (getr regs2 10%bv)) in Hf9 by (cbn; lia); cbn [nth map CLOB] in Hf9; rewrite Hr10 in Hf9.
all: cbn [ms_mem mkst] in HF.
all: assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte ubs0segs (ms_mem ms0) a = mbyte ubs0segs mem2 a)
by (intros a Ha Hna; apply (mbyte_of_frame _ _ _ _ a HF Ha); intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; ew_havocA; rewrite ?HU2; lia |]); destruct Hr).
all: clear HF HG.
all: assert (HFL : YO07.flush_frame G (rc_int (rw_cur s)) cur bef = (code, bytes)).
1,3: rewrite (flush_frame_split G cur bef (rc_int (rw_cur s))), <- HRA, <- Xw, <- Xh, <- Xtop, <- Xleft, <- Xtv;
change G with (gcfg_of s GPAL); rewrite (rattr_model (fr_attr f) hastrans Hhas01), <- raw_sgct_model;
unfold fl_rattr, fl_slct, fl_useLCT; cbn [YO07.g_attr gcfg_of];
unfold G in Xhas; rewrite HVra, flag_raw_attr_of, <- XA1, <- XA3, <- XA4, <- XA6, <- Xhas;
unfold YO07.flag at 3; change (Z.land (fr_attr f) 1) with u; rewrite Hu; cbn [Z.eqb negb]; rewrite ?Z.mul_0_l, ?Z.mul_1_l; reflexivity.
all: assert (HLEN3 : Z.of_nat (length bytes) <= FRAME_OUT N) by (unfold FRAME_OUT; clear - HLEN2 Hw Hh HN HW1 HH1; nia).
all: assert (GO : forall L3 A3 (regs3 : bvmap 5 word) (mem3 : word -> option byte) md3,
journal ubs0_msyms MR FLUSH_STK sp0 FPw L A mem md L3 A3 mem3 md3 -> st_init_done A3 = true ->
Permutation (blocks L3 A3) (cgif_blocks0 g s N ++ rest) ->
(forall b m k, In (b, m) (cgif_blocks0 g s N) -> 0 <= k < m -> mbyte ubs0segs mem3 (b + k) = mbyte ubs0segs (ms_mem ms0) (b + k)) ->
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 272 - ALLOC_STACK <= x < sp0 - 272) -> mbyte ubs0segs mem3 x = mbyte ubs0segs (ms_mem ms0) x) ->
getr regs3 2 = getr (ms_regs ms0) 2 -> getr regs3 3 = getr (ms_regs ms0) 3 -> getr regs3 4 = getr (ms_regs ms0) 4 -> getr regs3 9 = getr (ms_regs ms0) 9 ->
sink_at ubs0_msyms mem3 md3 (cg_file s) (S ++ bytes) -> res_ok A3 (flush_rb b) ->
SR ubs0segs (mkCfg (mkst regs3 (Z_to_bv 64 FL_RET) mem3 (seg_rom ubs0segs)) md3) (fl_post API regs0 g s N i rest FPw S GPAL cur bef b L A mem md)).
1,3: intros L3 A3 regs3 mem3 md3 HJ3 Hid3 HB3 Kb Khi R2 R3 R4 R9 HSK3 HRq3;
assert (ASv : ALLOC_STACK = 8192) by reflexivity;
assert (Kall : forall a n k, In (a, n) (cgif_blocks0 g s N) -> 0 <= k < n -> ~ (cg_raw s + 40 <= a + k < cg_raw s + 44) ->
mbyte ubs0segs mem3 (a + k) = mbyte ubs0segs memc (a + k))
by (intros a n k Hin Hk Hnot;
assert (Hin' : In (a, n) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HBc)); apply in_app_iff; left; exact Hin);
destruct (blocks_range _ _ LAWS Lc Ac memc mdc a n HH0 Hin') as [B0 B1];
assert (Hnf : ~ (cg_file s <= a + k < cg_file s + FILE_BLOCK))
by (pose proof (fl_file_sep API Lc Ac memc mdc g s N tmp rest a n HH0 HB Hfrest Hin) as Xf; clear - Xf Hk; lia);
rewrite (Kb a n k Hin Hk), (K2 (a + k)) by (clear - B0 B1 Hk Hceil HFSv Hac; lia);
rewrite (Hblk2 a n k Hin' Hk Hnot Hnf); apply K1; clear - B0 B1 Hk Hceil HFSv Hac; lia);
eapply (fl_ret L A mem md regs0 regs3 L3 A3 mem3 md3 g N s i f rest FPw S GPAL cur bef b code bytes);
[ exact HJ3 | exact Hid3 | exact Hra0 | exact Hal16
| apply (CG mem3 (code mod 2 ^ 32)); [exact Kall|]; rewrite <- Hrcur;
eapply obj_at_transport_range; [exact Hraw2 | exact (proj1 LAY_Raw_ok) |];
intros k Hk; rewrite (Kb (cg_raw s) RAW_SIZE k ltac:(right; left; reflexivity) ltac:(clear - Hk HRWv; lia));
apply K2; clear - Hk Hr0 Hr1 Hceil HFSv HRWv Hac; lia
| exact Hwf | exact Hf | exact HB3
| apply (fl_saved_ok_kept memc); [exact HSV|]; intros a Ha;
rewrite Khi, K2 by (clear - Ha Hceil Hsp063 HFSv ASv Hac; lia); rewrite (proj1 (Hhi2 a ltac:(clear - Ha Hceil Hsp063 HFSv Hac; lia) ltac:(clear - Ha HRSv; lia)));
apply K1; clear - Ha Hceil Hsp063 HFSv Hac; lia
| rewrite R2; exact Hf2
| split; [rewrite R3; exact Hf3 | rewrite R4, Hf4, Htp0; reflexivity]
| rewrite R9, Hf9; exact Hres
| exact HFL | exact HSK3 | exact HLEN3 | exact HRq3 ].
all: destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)) as (Hh2 & Hl2 & _).
all: assert (ASv : ALLOC_STACK = 8192) by reflexivity.
all: assert (Hspm : (sp0 - 272) mod 16 = 0) by (replace (sp0 - 272) with (sp0 + (-17) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
all: destruct (Z.eq_dec pTmp 0) as [Hpz | Hpz].
1,3: rewrite Hpz in Hf10; eapply SR_bind;
[ eapply (jfree_null _ (aa_free_null API)); [exact HS | reflexivity | reflexivity | exact Hh2 | exact Hl2 | exact Hf10 | exact Hfra | apply ret_ok_even; vm_compute; reflexivity]
| cbv beta; intros c' ->; cbn [ms_regs ms_mem mkst];
destruct (Ht0 Hpz) as (Htm & _ & _);
apply (GO L2 A2 (ms_regs ms0) (ms_mem ms0) md2 HJ2 Hid2);
[ eapply Permutation_trans; [exact HB2 | rewrite <- (app_nil_l (cgif_blocks0 g s N ++ rest)), <- Htm; exact HB]
| intros; reflexivity | intros; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| apply (sink_at_frame ubs0_msyms mem2 _ md2 (cg_file s) (S ++ bytes)); [|exact HSK2]; intros a Ha; apply K2;
[ destruct Ha as [Ha|Ha]; [clear - Ha Hf0 Hf1 Hac; lia | pose proof (ubs0_env_addr_range a Ha); clear - H Hac; lia]
| destruct Ha as [Ha|Ha]; [clear - Ha Hf0 Hf1 Hac Hceil HFSv; lia | pose proof (ubs0_env_addr_range a Ha); clear - H Hac Hceil HFSv; lia] ]
| eapply res_ok_mono; [exact (HRB0 Hpz) | exact HRq2] ] ].
all: destruct (Ht1 Hpz) as (Htm & _ & _).
all: assert (Hpin : In (pTmp, Nt) (blocks L2 A2)) by (apply (Permutation_in _ (Permutation_sym HB2)), (Permutation_in _ (Permutation_sym HB)); rewrite Htm; left; reflexivity).
all: assert (HfinL2 : In (cg_file s, FILE_BLOCK) (blocks L2 A2)) by (apply (Permutation_in _ (Permutation_sym HB2)); exact HfinC).
all: assert (Hsepf : pTmp + Nt <= cg_file s \/ cg_file s + FILE_BLOCK <= pTmp).
1,3: assert (HPc : Permutation (blocks L2 A2) ((pTmp, Nt) :: (cgif_blocks0 g s N ++ rest))) by (eapply Permutation_trans; [exact HB2 | rewrite Htm in HB; exact HB]);
destruct (Permutation_vs_cons_inv HPc) as (l1 & l2 & Hl12);
pose proof (@Permutation_cons_app_inv _ (cgif_blocks0 g s N ++ rest) l1 l2 (pTmp, Nt) ltac:(rewrite <- Hl12; apply Permutation_sym; exact HPc)) as HPl;
destruct (heap_sep _ _ LAWS L2 A2 mem2 md2 l1 (pTmp, Nt) l2 (cg_file s, FILE_BLOCK) HH2 Hl12
ltac:(apply (Permutation_in _ HPl); apply in_app_iff; right; exact Hfrest)) as [Hd|Hd]; cbn [fst snd] in Hd; [left; exact Hd | right; exact Hd].
all: assert (HSK2' : sink_at ubs0_msyms (ms_mem ms0) md2 (cg_file s) (S ++ bytes))
by (apply (sink_at_frame ubs0_msyms mem2 _ md2 (cg_file s) (S ++ bytes)); [|exact HSK2]; intros a Ha; apply K2;
[ destruct Ha as [Ha|Ha]; [clear - Ha Hf0 Hf1 Hac; lia | pose proof (ubs0_env_addr_range a Ha); clear - H Hac; lia]
| destruct Ha as [Ha|Ha]; [clear - Ha Hf0 Hf1 Hac Hceil HFSv; lia | pose proof (ubs0_env_addr_range a Ha); clear - H Hac Hceil HFSv; lia] ]).
all: eapply SR_bind;
[ eapply (jfree_tmp_sinkW_res API IMG) with (a := pTmp) (n := Nt) (spc := sp0 - 272) (b := rawadd_rb bc);
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact Hid2 | exact Hpin
| intros HinLA k Hk; apply HFPsub; exact (Htmp_fp HinLA k Hk)
| exact HfinL2 | exact Hsepf | exact HSK2'
| exact Hf10 | exact Hf2 | clear - Hceil Hsp063 HFSv Hac; lia | exact Hspm | clear - HFSv ASv; lia | lia | exact Hf4 | exact Hfra
| apply ret_ok_even; vm_compute; reflexivity | exact HRq2 ]
| ].
all: cbv beta; intros c' (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & Hid3 & HP3 & Hrm3 & Hkeep3 & Hhi3 & HSK3 & Hfin3 & _ & HR3).
all: change (ms_segs ubs0_msyms) with ubs0segs in Hkeep3, Hhi3; cbn [ms_regs ms_mem mkst] in HP3, Hkeep3, Hhi3, HJ3, HSK3.
all: assert (HB3 : Permutation (blocks L3 A3) (cgif_blocks0 g s N ++ rest))
by (eapply perm_after_rm1; [| exact Hrm3]; eapply Permutation_trans; [exact HB2 | rewrite Htm in HB; exact HB]).
all: apply (GO L3 A3 regs3 mem3 md3 HJ3 Hid3 HB3);
[ intros b0 m k Hin Hk; apply (Hkeep3 b0 m k); [apply (Permutation_in _ (Permutation_sym HB3)); apply in_app_iff; left; exact Hin | exact Hk]
| intros x Hx Hnx; apply (proj1 (Hhi3 x Hx Hnx))
| exact (HP3 2 ltac:(unfold callee_saved; lia)) | exact (HP3 3 ltac:(unfold callee_saved; lia)) | exact (HP3 4 ltac:(unfold callee_saved; lia))
| exact (HP3 9 ltac:(unfold callee_saved; lia))
| exact HSK3 | eapply res_ok_mono; [exact (HRB1 Hpz) | exact HR3] ].
Qed.
Lemma fl_tail :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s : cgif_st) (i : nat) (f : frame_st)
(rest FP FPw tmp : list (Z * Z)) (pTmp Nt tv w h pc : Z)
(S GPAL : list Z) (cur : YO07.frame) (bef : option YO07.frame) (bfr : option frame_st) (b bc : rbound) (top left ha : Z),
let sp0 := spZ regs0 in
let G := gcfg_of s GPAL in
let gen1 := fl_gen3 G cur bef in
journal ubs0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> sp0 mod 16 = 0 -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
cgif_at memc g (flush_upd s i gen1 (rw_cur s)) -> cgif_wf s N -> (i = 1%nat \/ i = 2%nat) -> nth_error (cg_frames s) i = Some (Some f) ->
fl_fp FP s f ->
Permutation (blocks Lc Ac) (tmp ++ cgif_blocks0 g s N ++ rest) ->
((tmp = [] /\ pTmp = 0 /\ w * h <= N) \/ (tmp = [(pTmp, Nt)] /\ pTmp <> 0 /\ w * h <= Nt)) ->
(In (pTmp, Nt) (blocks L A) -> forall k, 0 <= k < Nt -> inFP FP (pTmp + k)) ->
(pc = FL_RAW \/ (pc = FL_RAW2 /\ pTmp <> 0)) ->
1 <= w <= cg_W s -> 1 <= h <= cg_H s -> 0 <= tv < 2 ^ 64 ->
fl_saved_ok memc sp0 regs0 ->
getr regs1 2 = Z_to_bv 64 (sp0 - 272) -> getr regs1 8 = Z_to_bv 64 pTmp -> getr regs1 9 = Z_to_bv 64 tv -> getr regs1 16 = Z_to_bv 64 h ->
word_mem ubs0segs memc (sp0 - 272 + 112) g -> word_mem ubs0segs memc (sp0 - 272 + 120) (fr_ptr f) ->
word_mem ubs0segs memc (sp0 - 272 + 16) (Z.land (fr_attr f) 4) -> word_mem ubs0segs memc (sp0 - 272 + 24) ha ->
word_mem ubs0segs memc (sp0 - 272 + 32) (fr_disp f) -> word_mem ubs0segs memc (sp0 - 272 + 56) (Z.land (fr_attr f) 1) ->
word_mem ubs0segs memc (sp0 - 272 + 96) top ->
(pc = FL_RAW2 -> word_mem ubs0segs memc (sp0 - 272 + 40) w /\ word_mem ubs0segs memc (sp0 - 272 + 48) left) ->
(pc = FL_RAW -> getr regs1 14 = Z_to_bv 64 (fr_disp f) /\ getr regs1 15 = Z_to_bv 64 ha /\ getr regs1 22 = Z_to_bv 64 left /\ getr regs1 23 = Z_to_bv 64 w) ->
fl_untouched regs0 regs1 ->
nth (i - 1) (cg_frames s) None = bfr ->
fl_sink g s N rest FP FPw S L A mem md sp0 ->
fl_vals memc s N f bfr GPAL cur bef ->
ha = (if fl_hasAlpha G cur then 1 else 0) ->
w = fl_w G cur bef -> h = fl_h G cur bef -> top = fl_top G cur bef -> left = fl_left G cur bef ->
0 <= top -> top + h <= cg_H s -> 0 <= left -> left + w <= cg_W s ->
tv mod 256 = fl_tidx G cur bef ->
garr8 ubs0segs memc (if pTmp =? 0 then fr_img f else pTmp) (fl_img G cur bef) -> Z.of_nat (length (fl_img G cur bef)) = w * h ->
res_ok Ac bc -> rawadd_room bc (w * h) ->
(pTmp = 0 -> rb_le (rawadd_rb bc) (flush_rb b)) -> (pTmp <> 0 -> rb_le (rb_free (rawadd_rb bc) Nt) (flush_rb b)) ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 pc) memc (seg_rom ubs0segs)) mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur bef b L A mem md).
Proof using IMG RAWADDX.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s i f rest FP FPw tmp pTmp Nt tv w h pc S GPAL cur bef bfr b bc top left ha sp0 G gen1
HJ Hid Hra0 Hal16 Htp0 Hat Hwf Hi Hf HFP HB Htmp Htmp_fp Hpc Hw Hh Htv HSV G2 G8 G9 G16 Wg Wfr Wa4 Wha Wdisp Wu1 Wtop W2 R1 [G3 G4]
Hbfr HSINK HVALS Xha Xw Xh Xtop Xleft Htop0 Htop1 Hleft0 Hleft1 Xtv XIMG XIMGL HRq HRM HRB0 HRB1.
pose proof HVALS as (_ & HVf & _ & _). pose proof HVf as (XA1 & XA2 & XA3 & XA4 & XA5 & XA6 & XA7 & XVI & XVIl & HVlp).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFSv : FLUSH_STK = 9216) by reflexivity.
assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HRWv : RAW_SIZE = 48) by reflexivity. assert (HFRv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & _ & Hfwf).
set (s1 := flush_upd s i gen1 (rw_cur s)) in Hat. set (f1 := set_fr_gen f gen1).
assert (Hfin : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf).
assert (Hilt : (i < length (cg_frames s))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
assert (Hfr1 : cg_frames s1 = list_set (cg_frames s) i (Some f1)) by (subst s1 f1; apply cg_frames_flush_upd; exact Hf).
assert (Hf1in : In (Some f1) (cg_frames s1)) by (rewrite Hfr1; eapply nth_error_In; apply nth_error_list_set_same; exact Hilt).
assert (HBc : Permutation (blocks Lc Ac) (cgif_blocks0 g s N ++ (tmp ++ rest))) by (eapply Permutation_trans; [exact HB|]; apply Permutation_app_swap_app).
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N _ HH0 HBc) as ((Hr0 & Hr1 & Hrg) & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom f Hfin) as (Hp0 & Hp1 & Hpg).
destruct (fl_img_geom0 API Lc Ac memc mdc g s N _ f HH0 HBc Hfin ltac:(rewrite HN; clear - HW1 HH1; nia)) as [Him0 Him1].
pose proof Hat as (Hobj & Hraw & Hfrs). rewrite (cgif_vals_flush_upd s i gen1 (rw_cur s) : cgif_vals s1 = cgif_vals s) in Hobj.
pose proof (Hfrs f1 Hf1in) as Hfobj. change (fr_ptr f1) with (fr_ptr f) in Hfobj.
pose proof (obj_at_range _ _ _ _ _ Hfobj) as Rf.
pose proof (Rf 0%nat (fr_lpal f) eq_refl) as Rlpal. pose proof (Rf 1%nat (fr_img f) eq_refl) as Rimg. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rlpal, Rimg.
change (fr_img f1) with (fr_img f) in Rimg.
set (mo := [g; fr_ptr f; top; ha; w; left; Z.land (fr_attr f) 4; Z.land (fr_attr f) 1] : list Z).
set (E := fl_E regs1 regs0 s f1 None mo).
pose proof (fl_HE regs1 regs0 s f1 None mo : forall n rr, _ -> ew E n = _) as HE.
pose proof (fl_HK regs1 regs0 s f1 None mo : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (fl_HX regs1 regs0 s f1 None mo : forall n j v, _ -> _ -> ew E n = _) as HX.
pose proof (fl_HF regs1 regs0 s f1 None mo : forall n j v, _ -> _ -> ew E n = _) as HFf.
pose proof (fl_HM regs1 regs0 s f1 None mo : forall n j v, _ -> _ -> ew E n = _) as HM.
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 272) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hceil Hsp063 HFSv Hac; lia).
assert (HE80 : ew E 80 = Z_to_bv 64 g) by (apply (HM 80%nat 0%nat g eq_refl eq_refl)).
assert (HE81 : ew E 81 = Z_to_bv 64 (fr_ptr f)) by (apply (HM 81%nat 1%nat (fr_ptr f) eq_refl eq_refl)).
assert (HE82 : ew E 82 = Z_to_bv 64 top) by (apply (HM 82%nat 2%nat top eq_refl eq_refl)).
assert (HE83 : ew E 83 = Z_to_bv 64 ha) by (apply (HM 83%nat 3%nat ha eq_refl eq_refl)).
assert (HE84 : ew E 84 = Z_to_bv 64 w) by (apply (HM 84%nat 4%nat w eq_refl eq_refl)).
assert (HE85 : ew E 85 = Z_to_bv 64 left) by (apply (HM 85%nat 5%nat left eq_refl eq_refl)).
assert (HE86 : ew E 86 = Z_to_bv 64 (Z.land (fr_attr f) 4)) by (apply (HM 86%nat 6%nat _ eq_refl eq_refl)).
assert (HE87 : ew E 87 = Z_to_bv 64 (Z.land (fr_attr f) 1)) by (apply (HM 87%nat 7%nat _ eq_refl eq_refl)).
assert (HU80 : bv_unsigned (ew E 80) = g) by (rewrite HE80; apply unsigned_lit_small; lia).
assert (HU81 : bv_unsigned (ew E 81) = fr_ptr f) by (rewrite HE81; apply unsigned_lit_small; lia).
assert (HE62 : ew E 62 = Z_to_bv 64 (fr_lpal f)) by (apply (HFf 62%nat 0%nat _ eq_refl eq_refl)).
assert (HE63 : ew E 63 = Z_to_bv 64 (fr_img f)) by (apply (HFf 63%nat 1%nat _ eq_refl eq_refl)).
assert (HE65 : ew E 65 = Z_to_bv 64 gen1) by (apply (HFf 65%nat 3%nat _ eq_refl eq_refl)).
assert (HE69 : ew E 69 = Z_to_bv 64 (fr_disp f)) by (apply (HFf 69%nat 7%nat _ eq_refl eq_refl)).
assert (HE2 : ew E 2 = Z_to_bv 64 (sp0 - 272)) by (rewrite (HE 2%nat 2%bv eq_refl); exact G2).
assert (HE3 : ew E 3 = getr regs0 3) by (rewrite (HE 3%nat 3%bv eq_refl); exact G3).
assert (HE4 : ew E 4 = getr regs0 4) by (rewrite (HE 4%nat 4%bv eq_refl); exact G4).
assert (HE8 : ew E 8 = Z_to_bv 64 pTmp) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (HE9 : ew E 9 = Z_to_bv 64 tv) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE16 : ew E 16 = Z_to_bv 64 h) by (rewrite (HE 16%nat 16%bv eq_refl); exact G16).
assert (Hha01 : ha = 0 \/ ha = 1) by (rewrite Xha; destruct (fl_hasAlpha G cur); clear; lia).
pose proof (Rf 3%nat gen1 eq_refl) as Rgen1. pose proof (Rf 2%nat (fr_attr f) eq_refl) as Rfattr. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rgen1, Rfattr.
pose proof (Z_land_upper (fr_attr f) 4 ltac:(clear; lia)) as Ha4.
assert (Hu1r : 0 <= Z.land (fr_attr f) 1 <= 1) by (pose proof (land1_cases (fr_attr f) ltac:(clear - Rfattr; lia)); lia).
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. cbn [nth snd LAY_CGIF Z.of_N] in RH, RW.
pose proof (Rf 7%nat (fr_disp f) eq_refl) as Rdisp. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rdisp.
assert (Hbfr' : bfr = None \/ exists j, nth_error (cg_frames s) j = Some bfr).
{ destruct bfr as [b'|]; [right | left; reflexivity]. exists (i - 1)%nat. rewrite <- Hbfr. apply nth_error_nth'. rewrite Hlen. clear - Hi; lia. }
assert (GO : forall ss ms' rg0 (isv : sv) (img : Z) (hastrans : Z), st_ok ubs0segs E ss ms' -> ss_pc ss = FL_CFG -> ss_resv ss = None ->
nth_error (ss_mem ss) 0 = Some rg0 -> r_base rg0 = Some 2%nat ->
incl_chunks (fl_stk_saved 32 ++ [mkChunk 56 (CVal 8 (SOff 87 0)); mkChunk 96 (CVal 8 (SOff 82 0)); mkChunk 112 (CVal 8 (SOff 80 0));
mkChunk 120 (CVal 8 (SOff 81 0)); mkChunk 128 (CVal 8 (SOff 62 0)); mkChunk 136 (CVal 8 isv)]) (r_chunks rg0) = true ->
sv_denot E isv = Z_to_bv 64 img -> ((pTmp = 0 /\ img = fr_img f) \/ (pTmp <> 0 /\ img = pTmp)) ->
getr (ms_regs ms') 2 = Z_to_bv 64 (sp0 - 272) -> getr (ms_regs ms') 3 = getr regs0 3 -> getr (ms_regs ms') 4 = getr regs0 4 ->
getr (ms_regs ms') 8 = Z_to_bv 64 pTmp -> getr (ms_regs ms') 9 = Z_to_bv 64 tv -> getr (ms_regs ms') 16 = Z_to_bv 64 h ->
getr (ms_regs ms') 23 = Z_to_bv 64 w -> getr (ms_regs ms') 22 = Z_to_bv 64 left -> getr (ms_regs ms') 14 = Z_to_bv 64 (fr_disp f) ->
getr (ms_regs ms') 10 = Z_to_bv 64 hastrans -> hastrans = (if (fl_hasAlpha G cur || fl_trans_on G cur bef || fl_hasSet cur)%bool then 1 else 0) ->
journal ubs0_msyms MR FLUSH_STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte ubs0segs (ms_mem ms') a = mbyte ubs0segs memc a) ->
SR ubs0segs (mkCfg ms' mdc) (fl_post API regs0 g s N i rest FPw S GPAL cur bef b L A mem md)).
{ intros ss ms' rg0 isv img hastrans HS' Hpc' Hrv Hrg0 Hb0 Hincl Hisv Himg Q2 Q3 Q4 Q8 Q9 Q16 Q23 Q22 Q14 HT10 XHT HJ' K.
rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc'.
pose proof (st_region_chunks ubs0segs E ss ms' 0 rg0 2%nat (sp0 - 272) HS' Hrg0 Hb0 HU2) as Hcs.
pose proof (incl_Forall (incl_chunks_sound _ _ Hincl) Hcs) as Hcs'.
apply Forall_app in Hcs' as [Hsaved Hc3].
pose proof (proj1 (Forall_forall _ _) Hc3 _ ltac:(left; reflexivity)) as C56.
pose proof (proj1 (Forall_forall _ _) Hc3 _ ltac:(right; left; reflexivity)) as C96.
pose proof (proj1 (Forall_forall _ _) Hc3 _ ltac:(right; right; left; reflexivity)) as C112.
pose proof (proj1 (Forall_forall _ _) Hc3 _ ltac:(right; right; right; left; reflexivity)) as C120.
pose proof (proj1 (Forall_forall _ _) Hc3 _ ltac:(right; right; right; right; left; reflexivity)) as C128.
pose proof (proj1 (Forall_forall _ _) Hc3 _ ltac:(right; right; right; right; right; left; reflexivity)) as C136.
assert (Himr : 0 <= img < 2 ^ 64).
{ destruct Himg as [[_ ->] | [Hnz ->]]; [lia|].
destruct Htmp as [(_ & Hz & _) | (Htm & _ & Hle)]; [lia|].
assert (Hin : In (pTmp, Nt) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); rewrite Htm; left; reflexivity).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pTmp Nt HH0 Hin) as [T0 T1]. clear - T0 T1 Hle Hw Hh Hac. nia. }
assert (Kblk : forall a n k, In (a, n) (cgif_blocks0 g s N) -> 0 <= k < n -> mbyte ubs0segs (ms_mem ms') (a + k) = mbyte ubs0segs memc (a + k)).
{ intros a n k Hin Hk. assert (Hin' : In (a, n) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HBc)); apply in_app_iff; left; exact Hin).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc a n HH0 Hin') as [B0 B1]. apply K; clear - B0 B1 Hk Hceil HFSv Hac; lia. }
assert (Himg2 : In (img, if pTmp =? 0 then N else Nt) (blocks Lc Ac) /\ garr8 ubs0segs memc img (fl_img G cur bef)).
{ destruct Himg as [[Hz ->] | [Hnz ->]].
- rewrite Hz, Z.eqb_refl in XIMG |- *; split; [| exact XIMG].
apply (Permutation_in _ (Permutation_sym HBc)); apply in_app_iff; left; apply (frame_blocks_in_cgif0 g s N f); [exact Hfin | right; left; reflexivity].
- destruct (Z.eqb_spec pTmp 0); [exfalso; exact (Hnz ltac:(assumption))|]; split; [| exact XIMG].
destruct Htmp as [(_ & Hz & _) | (Htm & _ & _)]; [exfalso; exact (Hnz Hz)|].
apply (Permutation_in _ (Permutation_sym HB)); rewrite Htm; left; reflexivity. }
destruct Himg2 as [Hin2 X2]. destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 Hin2) as [Bi0 Bi1].
assert (Hwhn : w * h <= (if pTmp =? 0 then N else Nt))
by (destruct Htmp as [(_ & Hz & Hle)|(_ & Hnz & Hle)]; [rewrite Hz, Z.eqb_refl; exact Hle | destruct (Z.eqb_spec pTmp 0); [exfalso; exact (Hnz ltac:(assumption)) | exact Hle]]).
assert (XIMG' : garr8 ubs0segs (ms_mem ms') img (fl_img G cur bef)).
{ eapply garr8_frame; [exact X2|]; intros a Ha. apply K.
- set (nn := if pTmp =? 0 then N else Nt) in *. clear - Ha Bi0 Bi1 Hwhn XIMGL Hac. lia.
- set (nn := if pTmp =? 0 then N else Nt) in *. clear - Ha Bi0 Bi1 Hwhn XIMGL Hac Hceil HFSv. lia. }
eapply (fl_cfg L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s i f rest FP FPw tmp pTmp Nt tv img w h S GPAL cur bef bfr b bc top left hastrans);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hi | exact Hf | exact HFP | exact HB
| destruct Htmp as [(A1 & A2 & A3) | (A1 & A2 & A3)]; destruct Himg as [[B1 B2] | [B1 B2]]; try lia_try; [left | right]; auto
| exact Htmp_fp | exact Hw | exact Hh | exact Htv
| apply (fl_saved_ok_kept memc); [exact HSV | intros a Ha; apply K; lia]
| apply (chunk_word E _ _ _ _ _ C112); [cbn [sv_denot]; rewrite Z.add_0_r, HE80, Z_to_bv_bv_unsigned; reflexivity | lia]
| apply (chunk_word E _ _ _ _ _ C120); [cbn [sv_denot]; rewrite Z.add_0_r, HE81, Z_to_bv_bv_unsigned; reflexivity | lia]
| apply (chunk_word E _ _ _ _ _ C128); [cbn [sv_denot]; rewrite Z.add_0_r, HE62, Z_to_bv_bv_unsigned; reflexivity | lia]
| apply (chunk_word E _ _ _ _ _ C136); [exact Hisv | exact Himr]
| apply (chunk_word E _ _ _ _ _ C56); [cbn [sv_denot]; rewrite Z.add_0_r, HE87, Z_to_bv_bv_unsigned; reflexivity | lia]
| apply (chunk_word E _ _ _ _ _ C96); [cbn [sv_denot]; rewrite Z.add_0_r, HE82, Z_to_bv_bv_unsigned; reflexivity | lia]
| exact Q2 | exact Q8 | exact Q9 | exact Q23 | exact Q16
| split; [exact Q3 | exact Q4]
| exact Hbfr | exact HSINK
| eapply fl_vals_kept; [| exact HVALS]; intros a n k Hin Hk; apply (Kblk a n k); [| exact Hk]; exact (fl_vblocks_sub g s N f bfr i Hf Hbfr' _ Hin)
| exact Q22 | exact Q14 | exact HT10
| exact Xw | exact Xh | exact Xtop | exact Xleft | exact Htop0 | exact Htop1 | exact Hleft0 | exact Hleft1 | exact XHT | exact Xtv
| exact XIMG'
| exact XIMGL | exact HRq | exact HRM | exact HRB0 | exact HRB1 ].
destruct Hat as (_ & _ & _).
split; [| split].
- rewrite (cgif_vals_flush_upd s i (fl_gen3 (gcfg_of s GPAL) cur bef) (rw_cur s)). eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros k Hk; apply K; clear - Hk Hg0 Hg1 Hceil HFSv HGSv Hac; lia].
- change (cg_raw (flush_upd s i (fl_gen3 (gcfg_of s GPAL) cur bef) (rw_cur s))) with (cg_raw s).
eapply obj_at_transport_range; [exact Hraw | exact (proj1 LAY_Raw_ok) | intros k Hk; apply K; clear - Hk Hr0 Hr1 Hceil HFSv HRWv Hac; lia].
- intros x Hx. assert (Hx1 : In (Some x) (cg_frames s1)) by exact Hx.
destruct (In_frames_flush_upd s i (fl_gen3 (gcfg_of s GPAL) cur bef) (rw_cur s) f x Hf Hx) as [-> | [Hin _]].
+ eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply K; change (fr_ptr (set_fr_gen f (fl_gen3 (gcfg_of s GPAL) cur bef))) with (fr_ptr f); clear - Hk Hp0 Hp1 Hceil HFSv HFRv Hac; lia].
+ destruct (Hfgeom x Hin) as (X0 & X1 & _).
eapply obj_at_transport_range; [exact (Hfrs _ Hx1) | exact (proj1 LAY_Frame_ok) | intros k Hk; apply K; clear - Hk X0 X1 Hceil HFSv HFRv Hac; lia]. }
assert (U_orand' : forall g1 a4, ew E 65 = Z_to_bv 64 g1 -> 0 <= g1 < 2 ^ 32 -> ew E 86 = Z_to_bv 64 a4 -> 0 <= a4 < 2 ^ 32 ->
U E (SAlu ALU_OR (SAlu ALU_AND (SOff 65 0) (SLit 1)) (SOff 86 0)) = Z.lor (Z.land g1 1) a4).
{ clear. intros g1 a4 H65 Hg1 H86 Ha4.
rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SAlu; cbn [zalu_raw]. rewrite (U_atom _ 65 g1 H65), (U_atom _ 86 a4 H86), U_SLit by lia. change (zcanon 1) with 1.
pose proof (Z_land_upper g1 1 ltac:(lia)) as H1.
assert (HM64 : M64 = 2 ^ 64) by reflexivity.
rewrite (zcanon_id (Z.land g1 1)) by (rewrite HM64; lia).
pose proof (Z.add_lor_land (Z.land g1 1) a4) as Hll. pose proof (Z.lor_nonneg (Z.land g1 1) a4) as Hnn.
pose proof (Z.land_nonneg (Z.land g1 1) a4) as Hln.
rewrite zcanon_id by (rewrite HM64; lia). reflexivity. }
assert (lor_zero_flags : forall g0 a, (Z.lor (Z.land g0 1) (Z.land a 4) =? 0) = negb (YO07.flag g0 1 || YO07.flag a 4)).
{ clear. intros g0 a. unfold YO07.flag.
destruct (Z.eqb_spec (Z.land g0 1) 0) as [E1|E1]; destruct (Z.eqb_spec (Z.land a 4) 0) as [E4|E4]; cbn [negb orb];
[ rewrite E1, E4; reflexivity
| apply Z.eqb_neq; intros H; apply Z.lor_eq_0_iff in H; lia
| apply Z.eqb_neq; intros H; apply Z.lor_eq_0_iff in H; lia
| apply Z.eqb_neq; intros H; apply Z.lor_eq_0_iff in H; lia ]. }
assert (WR : forall E0 cs, bv_unsigned (ew E0 2) = sp0 - 272 ->
wr_ok E0 [YP09.mkRegion (Some 2%nat) 0 272 0 168 cs; fl_RgM; fl_RfM] FLUSH_STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E0 cs H2. eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (HR0 : forall r2 : bool, (r2 = true -> word_mem ubs0segs memc (sp0 - 272 + 40) w /\ word_mem ubs0segs memc (sp0 - 272 + 48) left) ->
region_ok ubs0segs E memc (YP09.mkRegion (Some 2%nat) 0 272 0 168 (fl_raw_stk r2))).
{ intros r2 Hr2. unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
unfold fl_raw_stk. apply Forall_app; split; [apply (fl_saved_chunks_ok E memc sp0 regs0 32 HSV); intros j v Hj; exact (HK _ j v eq_refl Hj)|].
apply Forall_app; split.
- constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]]].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ (Z.land (fr_attr f) 4)); [cbn [sv_denot]; rewrite Z.add_0_r, HE86, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wa4].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ ha); [cbn [sv_denot]; rewrite Z.add_0_r, HE83, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wha].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_disp f)); [cbn [sv_denot]; rewrite Z.add_0_r, HE69, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wdisp].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ (Z.land (fr_attr f) 1)); [cbn [sv_denot]; rewrite Z.add_0_r, HE87, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wu1].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, HE82, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wtop].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ g); [cbn [sv_denot]; rewrite Z.add_0_r, HE80, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wg].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ (fr_ptr f)); [cbn [sv_denot]; rewrite Z.add_0_r, HE81, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wfr].
- destruct r2; [| constructor]. destruct (Hr2 eq_refl) as [W40 W48].
constructor; [| constructor; [| constructor]].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ w); [cbn [sv_denot]; rewrite Z.add_0_r, HE84, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W40].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ left); [cbn [sv_denot]; rewrite Z.add_0_r, HE85, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W48]. }
pose proof (fl_RgM_ok regs1 regs0 s f1 None mo memc g HU80 ltac:(lia) ltac:(lia) Hobj) as HR1.
pose proof (fl_RfM_ok regs1 regs0 s f1 None mo memc (fr_ptr f) HU81 ltac:(lia) ltac:(lia) Hfobj) as HR2.
assert (HPD : forall (pc' : Z) (pz r2 : bool), pairwise_disjoint E (ss_mem (ss_raw pc' pz r2))).
{ intros pc' pz r2. cbn [ss_mem ss_raw]. unfold fl_RgM, fl_RfM. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU80, HU81. clear - Hg1 Hp1 Hpg Hceil HFSv HGSv HFRv Hac; unfold hidePs in *. repeat split; lia. }
pose proof (fl_gfacts_ok regs1 regs0 s f1 None mo memc g N Hobj Hwf ltac:(lia) ltac:(lia)) as HFAb.
pose proof (fl_ffacts_ok regs1 regs0 s f1 None mo memc (fr_ptr f) Hfobj Him0 ltac:(change (fr_img f1) with (fr_img f); clear - Him1 HN HW1 HH1; nia)) as HFAc.
assert (HFAa : atoms_ok E fl_factsM).
{ cbn [atoms_ok fl_factsM]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU80, HU81.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia_try.
+ replace (sp0 - 272) with (sp0 + (-17) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16.
+ pose proof (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr f) FRAME_SIZE HH0 ltac:(apply (Permutation_in _ (Permutation_sym HBc)); apply in_app_iff; left; apply (frame_blocks_in_cgif0 g s N f); [exact Hfin | left; reflexivity]) ltac:(lia)) as (_ & _ & Hp16).
clear - Hp16. apply Z.mod_divide in Hp16; [|lia]. apply Z.mod_divide; [lia|]. destruct Hp16 as [q Hq]. exists (q * 2). lia. }
assert (HFAd : pTmp <> 0 -> atoms_ok E [(8%nat, mkAF 1 (2^64 - 1) 0)]).
{ intros Hpz. destruct Htmp as [(_ & Hz & _) | (Htm & _ & Hle)]; [lia|].
assert (Hin : In (pTmp, Nt) (blocks Lc Ac)) by (apply (Permutation_in _ (Permutation_sym HB)); rewrite Htm; left; reflexivity).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pTmp Nt HH0 Hin) as [T0 T1].
assert (T2 : pTmp < alloc_ceiling) by (clear - T1 Hle Hw Hh; nia).
cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE8, unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite Z.mod_1_r. clear - T0 T2 Hac. repeat split; lia. }
assert (MK : forall (pc' : Z) (pz r2 : bool), (if pz then pTmp = 0 else pTmp <> 0) ->
(r2 = true -> word_mem ubs0segs memc (sp0 - 272 + 40) w /\ word_mem ubs0segs memc (sp0 - 272 + 48) left) ->
st_ok ubs0segs E (ss_raw pc' pz r2) (mkst regs1 (Z_to_bv 64 pc') memc (seg_rom ubs0segs))).
{ intros pc' pz r2 Hpz Hr2. unfold ss_raw. apply entry_st_ok_full; [| destruct pz, r2; vm_compute; reflexivity | | exact (HPD pc' pz r2) |].
- destruct pz; [| apply regs_ok_Ereg]. apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx |]. rewrite G8, Hpz. reflexivity.
- constructor; [exact (HR0 r2 Hr2)|]. constructor; [exact HR1|]. constructor; [exact HR2|]. constructor.
- split; [| split; exact I]. apply atoms_ok_app; [exact HFAa|]. apply atoms_ok_app; [exact HFAb|]. apply atoms_ok_app; [exact HFAc|].
destruct pz; [exact I | exact (HFAd Hpz)]. }
clear HR0 HR1 HR2 HPD HFAa HFAb HFAc HFAd.
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0 - 272 + 168) -> mbyte ubs0segs memc a = mbyte ubs0segs memc a) by (intros; reflexivity).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 pc) memc (seg_rom ubs0segs))) in HJ.
assert (CASES : (pc = FL_RAW /\ pTmp = 0) \/ (pc = FL_RAW /\ pTmp <> 0) \/ (pc = FL_RAW2 /\ pTmp <> 0))
by (destruct (Z.eq_dec pTmp 0); destruct Hpc as [H1 | [H2 H3]]; [left; auto | exfalso; exact (H3 e) | right; left; auto | right; right; auto]).
clear Hpc.
assert (TG3 : forall g0 cur0 bef0, fl_trans_on g0 cur0 bef0 = YO07.flag (fl_gen3 g0 cur0 bef0) 1).
{ clear. intros g0 cur0 bef0. unfold fl_trans_on, fl_gen3, fl_gen2, fl_gen1. destruct bef0 as [b0|]; [reflexivity|].
assert (C3 : forall v, Z.land (YO07.clr v 3) 1 = 0).
{ intros v. unfold YO07.clr. rewrite <- Z.land_assoc. replace (Z.land (Z.lnot 3) 1) with 0 by reflexivity. apply Z.land_0_r. }
assert (C1 : forall v, Z.land v 1 = 0 -> Z.land (YO07.clr v 1) 1 = 0).
{ intros v Hv. unfold YO07.clr. rewrite <- Z.land_assoc. replace (Z.land (Z.lnot 1) 1) with 0 by reflexivity. apply Z.land_0_r. }
assert (F : forall v, Z.land v 1 = 0 -> YO07.flag v 1 = false) by (intros v Hv; unfold YO07.flag; rewrite Hv; reflexivity).
symmetry. apply F. destruct (fl_npal g0 cur0 =? 256); destruct (fl_hasSet cur0); auto. }
destruct CASES as [[-> Hpz] | [[-> Hpz] | [-> Hpz]]];
[ pose proof (MK FL_RAW true false Hpz ltac:(intros Hx; discriminate Hx)) as HS; destruct (R1 eq_refl) as (G14 & G15 & G22 & G23)
| pose proof (MK FL_RAW false false Hpz ltac:(intros Hx; discriminate Hx)) as HS; destruct (R1 eq_refl) as (G14 & G15 & G22 & G23)
| pose proof (MK FL_RAW2 false true Hpz (fun _ => W2 eq_refl)) as HS ]; clear MK.
all: try (assert (HE14 : ew E 14 = Z_to_bv 64 (fr_disp f)) by (rewrite (HE 14%nat 14%bv eq_refl); exact G14)).
all: try (assert (HE15 : ew E 15 = Z_to_bv 64 ha) by (rewrite (HE 15%nat 15%bv eq_refl); exact G15)).
all: try (assert (HE22 : ew E 22 = Z_to_bv 64 left) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22)).
all: try (assert (HE23 : ew E 23 = Z_to_bv 64 w) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23)).
all: runW LAWS FL_CFG ltac:(apply WR; repeat (rewrite ew_havoc_old; [|cbv; lia]); exact HU2) HU2 (sp0 - 272) (sp0 - 272 + 168).
all: let HS := get_HS in jbranch ubs0tbl HS.
all: first [ rewrite branch_ne_U, U_lit, (U_atom _ 83 ha HE83) in Hc by (clear - Hha01; lia)
| rewrite branch_ne_U, U_lit, (U_atom _ 15 ha HE15) in Hc by (clear - Hha01; lia) ].
1,3,5: runW LAWS FL_CFG ltac:(apply WR; repeat (rewrite ew_havoc_old; [|cbv; lia]); exact HU2) HU2 (sp0 - 272) (sp0 - 272 + 168);
let HS := get_HS in let HJ := get_HJ in
lazymatch goal with K : forall a, _ -> _ -> mbyte ubs0segs _ a = mbyte ubs0segs _ a |- _ =>
first [ eapply (GO _ _ _ (SOff 63 0) (fr_img f) 1 HS);
[ reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
| cbn [sv_denot]; rewrite Z.add_0_r, HE63, Z_to_bv_bv_unsigned; reflexivity | left; split; [assumption | reflexivity]
| rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS
| rewrite (st_ok_reg ubs0segs E _ _ 10%bv HS); reflexivity
| rewrite Xha in Hc; destruct (fl_hasAlpha G cur); [reflexivity | discriminate Hc]
| exact HJ | exact K ]
| eapply (GO _ _ _ (SOff 8 0) pTmp 1 HS);
[ reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
| cbn [sv_denot]; rewrite Z.add_0_r, HE8, Z_to_bv_bv_unsigned; reflexivity | right; split; [assumption | reflexivity]
| rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS
| rewrite (st_ok_reg ubs0segs E _ _ 10%bv HS); reflexivity
| rewrite Xha in Hc; destruct (fl_hasAlpha G cur); [reflexivity | discriminate Hc]
| exact HJ | exact K ] ] end.
all: rename Hc into Hc1; runW LAWS FL_CFG ltac:(apply WR; repeat (rewrite ew_havoc_old; [|cbv; lia]); exact HU2) HU2 (sp0 - 272) (sp0 - 272 + 168).
all: let HS := get_HS in jbranch ubs0tbl HS.
all: rewrite branch_eq_U, (U_orand' gen1 (Z.land (fr_attr f) 4) HE65 ltac:(clear - Rgen1; lia) HE86 ltac:(clear - Ha4; lia)), U_lit, lor_zero_flags in Hc by (clear; lia).
all: assert (HhaF : fl_hasAlpha G cur = false) by (rewrite Xha in Hc1; destruct (fl_hasAlpha G cur); [discriminate Hc1 | reflexivity]).
all: first [ assert (HL0Z : Z.lor (Z.land gen1 1) (Z.land (fr_attr f) 4) = 0) by (apply Z.eqb_eq; rewrite lor_zero_flags; exact Hc);
runW LAWS FL_CFG ltac:(apply WR; repeat (rewrite ew_havoc_old; [|cbv; lia]); exact HU2) HU2 (sp0 - 272) (sp0 - 272 + 168);
let HS := get_HS in let HJ := get_HJ in
lazymatch goal with K : forall a, _ -> _ -> mbyte ubs0segs _ a = mbyte ubs0segs _ a |- _ =>
first [ eapply (GO _ _ _ (SOff 63 0) (fr_img f) 0 HS);
[ reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
| cbn [sv_denot]; rewrite Z.add_0_r, HE63, Z_to_bv_bv_unsigned; reflexivity | left; split; [assumption | reflexivity]
| rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS
| rewrite (st_ok_reg ubs0segs E _ _ 10%bv HS); match goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end;
rewrite denot_lit_U, (U_orand' gen1 (Z.land (fr_attr f) 4) HE65 ltac:(clear - Rgen1; lia) HE86 ltac:(clear - Ha4; lia)), HL0Z; reflexivity
| rewrite HhaF, TG3; unfold fl_hasSet; rewrite <- XA1; change (fl_gen3 G cur bef) with gen1;
destruct (YO07.flag gen1 1); destruct (YO07.flag (fr_attr f) 4); cbn in Hc |- *; try discriminate Hc; reflexivity
| exact HJ | exact K ]
| eapply (GO _ _ _ (SOff 8 0) pTmp 0 HS);
[ reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
| cbn [sv_denot]; rewrite Z.add_0_r, HE8, Z_to_bv_bv_unsigned; reflexivity | right; split; [assumption | reflexivity]
| rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS
| rewrite (st_ok_reg ubs0segs E _ _ 10%bv HS); match goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end;
rewrite denot_lit_U, (U_orand' gen1 (Z.land (fr_attr f) 4) HE65 ltac:(clear - Rgen1; lia) HE86 ltac:(clear - Ha4; lia)), HL0Z; reflexivity
| rewrite HhaF, TG3; unfold fl_hasSet; rewrite <- XA1; change (fl_gen3 G cur bef) with gen1;
destruct (YO07.flag gen1 1); destruct (YO07.flag (fr_attr f) 4); cbn in Hc |- *; try discriminate Hc; reflexivity
| exact HJ | exact K ] ] end
| runW LAWS FL_CFG ltac:(apply WR; repeat (rewrite ew_havoc_old; [|cbv; lia]); exact HU2) HU2 (sp0 - 272) (sp0 - 272 + 168);
let HS := get_HS in let HJ := get_HJ in
lazymatch goal with K : forall a, _ -> _ -> mbyte ubs0segs _ a = mbyte ubs0segs _ a |- _ =>
first [ eapply (GO _ _ _ (SOff 63 0) (fr_img f) 1 HS);
[ reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
| cbn [sv_denot]; rewrite Z.add_0_r, HE63, Z_to_bv_bv_unsigned; reflexivity | left; split; [assumption | reflexivity]
| rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS
| rewrite (st_ok_reg ubs0segs E _ _ 10%bv HS); reflexivity
| rewrite HhaF, TG3; unfold fl_hasSet; rewrite <- XA1; change (fl_gen3 G cur bef) with gen1;
destruct (YO07.flag gen1 1); destruct (YO07.flag (fr_attr f) 4); cbn in Hc |- *; try discriminate Hc; reflexivity
| exact HJ | exact K ]
| eapply (GO _ _ _ (SOff 8 0) pTmp 1 HS);
[ reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
| cbn [sv_denot]; rewrite Z.add_0_r, HE8, Z_to_bv_bv_unsigned; reflexivity | right; split; [assumption | reflexivity]
| rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS | rgq HS
| rewrite (st_ok_reg ubs0segs E _ _ 10%bv HS); reflexivity
| rewrite HhaF, TG3; unfold fl_hasSet; rewrite <- XA1; change (fl_gen3 G cur bef) with gen1;
destruct (YO07.flag gen1 1); destruct (YO07.flag (fr_attr f) 4); cbn in Hc |- *; try discriminate Hc; reflexivity
| exact HJ | exact K ] ] end ].
Qed.
End S.
End a0.
