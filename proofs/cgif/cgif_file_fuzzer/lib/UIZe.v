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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI02 YI03 YI0j UI1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0e YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI4l YI5a UI2v UI5d UI5o UI3w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition PC_NT : Z := ubs0_A_cgif_raw_newgif + 0x240.
Definition PC_NWR : Z := ubs0_A_cgif_raw_newgif + 0x388.
Definition PC_NX : Z := ubs0_A_cgif_raw_newgif + 0x38c.
Definition PC_NM : Z := ubs0_A_cgif_raw_newgif + 0x264.
Definition ss_fin (pz : bool) : sstate :=
mkSS (if pz then PC_NWR else PC_NX)
(if pz then sr_set (sr_set sr_atoms 18%bv (SLit 0)) 10%bv (SLit 0) else sr_set sr_atoms 18%bv (SLit 0))
[ YP09.mkRegion (Some 2%nat) 0 112 0 0 (saved_chunks_at 9 112 32) ;
YP09.mkRegion (Some 8%nat) 0 48 40 44 [] ]
None (mkFacts [ (2%nat, mkAF (CEIL_MIN + 8192) (2^63 - 112) 4); (8%nat, mkAF 4096 (CEIL_MAX - 48) 4) ] [] []).
Lemma rn_obj_at_app : forall segs mem a l1 l2 v1 v2,
obj_at segs mem a l1 v1 -> obj_at segs mem a l2 v2 -> obj_at segs mem a (l1 ++ l2) (v1 ++ v2).
Proof using.
intros segs mem a l1. induction l1 as [|f0 l1 IH]; intros l2 [|v v1] v2 H1 H2; cbn in *; try tauto.
split; [tauto | apply IH; tauto].
Qed.
Lemma rn_fok_eq : forall segs mem a fd v' v, field_ok segs mem a fd v' -> v' = v -> field_ok segs mem a fd v.
Proof using. intros segs mem a fd v' v H <-. exact H. Qed.
Lemma rn_mod16_sub : forall x k, x mod 16 = 0 -> (x - 16 * k) mod 16 = 0.
Proof using. intros x k Hx. replace (x - 16 * k) with (x + (- k) * 16) by lia. rewrite Z.mod_add by lia. exact Hx. Qed.
Lemma rn_hdr_split : forall W H sgct GCT rattr loops,
YO07.raw_header W H sgct GCT rattr loops = YO07.raw_header W H sgct GCT 0 0 ++ (if has_net rattr then net19 loops else []).
Proof using.
intros W H sgct GCT rattr loops. rewrite !raw_header_eq. replace (has_net 0) with false by reflexivity.
rewrite app_nil_r, <- app_assoc. reflexivity.
Qed.
Inductive chunk_bytesZ (E : env) (cs : list YP09.chunk) : Z -> list Z -> Prop :=
| cbz_nil : forall off, chunk_bytesZ E cs off []
| cbz_val : forall off e b bs, In (mkChunk off (CVal 1 e)) cs -> bv_unsigned (sv_denot E e) mod 256 = b ->
chunk_bytesZ E cs (off + 1) bs -> chunk_bytesZ E cs off (b :: bs)
| cbz_zero : forall off co len bs, In (mkChunk co (CZero len)) cs -> co <= off < co + len ->
chunk_bytesZ E cs (off + 1) bs -> chunk_bytesZ E cs off (0 :: bs).
Lemma garr8_of_chunk_bytesZ : forall segs E mem r p a bs off,
region_ok segs E mem r -> r_base r = Some p -> bv_unsigned (ew E p) = a ->
chunk_bytesZ E (r_chunks r) off bs -> garr8 segs mem (a + off) bs.
Proof using.
intros segs E mem r p a bs off HR Hb Hp HC.
induction HC as [off | off e b bs Hin Hbv HC IH | off co len bs Hin Hr HC IH].
- apply garr8_nil.
- intros [|j] Hj.
+ cbn [nth Z.of_nat]. rewrite Z.add_0_r. split.
* exact (vval_mem_of_chunk_mod segs E mem r p a off 1%N e b HR Hb Hin Hp Hbv ltac:(cbn; lia)).
* rewrite <- Hbv. apply Z.mod_pos_bound. lia.
+ cbn [nth]. cbn [length] in Hj. specialize (IH j ltac:(lia)).
replace (a + off + Z.of_nat (Datatypes.S j)) with (a + (off + 1) + Z.of_nat j) by lia. exact IH.
- intros [|j] Hj.
+ cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [|lia].
intros k Hk. assert (Hk0 : k = 0%nat) by lia. subst k.
pose proof HR as (_ & _ & _ & Hcs). pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
rewrite Hb in Hc. cbn [base_val] in Hc. rewrite Hp in Hc.
destruct (Hc (off - co) ltac:(cbn [c_len c_val cv_len]; lia)) as (b0 & Hb1 & Hb2).
cbn [cbyte c_val c_off] in Hb1, Hb2. injection Hb1 as <-.
replace (a + off + Z.of_nat 0) with (a + co + (off - co)) by lia. rewrite Hb2. reflexivity.
+ cbn [nth]. cbn [length] in Hj. specialize (IH j ltac:(lia)).
replace (a + off + Z.of_nat (Datatypes.S j)) with (a + (off + 1) + Z.of_nat j) by lia. exact IH.
Qed.
Lemma byte_atom16 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 16 ->
bv_unsigned (sv_denot E (SOff n 0)) mod 256 = v mod 256.
Proof using.
intros E n v Hn Hv. change (U E (SOff n 0) mod 256 = v mod 256). rewrite (U_atom E n v Hn) by lia. reflexivity.
Qed.
Lemma byte_atom16_hi : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 16 ->
bv_unsigned (sv_denot E (SAlu ALU_SRL (SOff n 0) (SLit 8))) mod 256 = (v / 256) mod 256.
Proof using.
intros E n v Hn Hv. change (U E (SAlu ALU_SRL (SOff n 0) (SLit 8)) mod 256 = (v / 256) mod 256).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 8) 63) with 8. rewrite mod256_zcanon, Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite (U_atom E n v Hn) by lia. reflexivity.
Qed.
Lemma rn_fs_transport : forall regs0 (m m' : word -> option byte) spe,
frame_savedN ubs0_msyms 9 regs0 m spe ->
(forall a, spe - 72 <= a < spe -> mbyte ubs0segs m' a = mbyte ubs0segs m a) ->
frame_savedN ubs0_msyms 9 regs0 m' spe.
Proof using.
intros regs0 m m' spe HF Hk r d Hin k Hk8.
pose proof (SAVEDN_range 9 r d ltac:(lia) Hin) as Hd.
etransitivity; [apply Hk; lia | exact (HF r d Hin k Hk8)].
Qed.
Definition ss_net : sstate :=
mkSS PC_NM sr_atoms
[ YP09.mkRegion (Some 2%nat) 0 112 21 39 [mkChunk 39 (CVal 1 (SLit 0))] ;
YP09.mkRegion (Some 9%nat) 0 40 0 0 (obj_chunks_gen LAY_RawConfig 32 lits_RawConfig) ]
None (mkFacts [ (2%nat, mkAF (CEIL_MIN + 8192) (2^63 - 112) 4); (9%nat, mkAF (CEIL_MIN + 8192) (2^63 - 40) 3) ] [] []).
Definition ss_nt : sstate :=
mkSS PC_NT sr_atoms
[ YP09.mkRegion (Some 2%nat) 0 112 0 0 [] ;
YP09.mkRegion (Some 9%nat) 0 40 0 0 (obj_chunks_gen LAY_RawConfig 32 lits_RawConfig) ]
None (mkFacts [ (2%nat, mkAF (CEIL_MIN + 8192) (2^63 - 112) 4); (9%nat, mkAF (CEIL_MIN + 8192) (2^63 - 40) 3) ] [] []).
Lemma rn_U_zext32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> U E (SExt false 32 (SOff n 0)) = v.
Proof using.
intros E n v Hn Hv. rewrite U_SExt. cbv beta iota. rewrite (U_atom E n v Hn) by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma rn_hdr0_len : forall W H sgct GCT, 0 <= sgct <= 256 ->
(length (YO07.raw_header W H sgct GCT 0 0) <= 781)%nat.
Proof using.
intros W H sgct GCT Hs. rewrite raw_header_eq. replace (has_net 0) with false by reflexivity.
rewrite !length_app. unfold hdr13. cbn [length].
destruct (Z.eqb_spec sgct 0) as [_ | Hs0]; [cbn [length]; lia|].
assert (Hc : forallb (fun n => Nat.leb (Z.to_nat (Z.of_nat n * 3) + length (gct_pad (Z.of_nat n) [])) 768) (seq 1 256) = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in Hc. specialize (Hc (Z.to_nat sgct) ltac:(apply in_seq; lia)).
apply Nat.leb_le in Hc. rewrite Z2Nat.id in Hc by lia.
unfold gct_pad in *. rewrite firstn_nil, app_nil_l in Hc. rewrite length_app.
pose proof (firstn_le_length (Z.to_nat (sgct * 3)) GCT). lia.
Qed.
End h.
Ltac rn_rq HS HX' rr j :=
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
let Q := fresh "Q" in
pose proof (st_ok_reg ubs0segs Ef ssf msf rr HS) as Q; eval_sr_get_in Q; cbn [sv_denot] in Q;
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Q;
let n := eval cbv in (32 + j)%nat in
try rewrite (HX' n j eq_refl ltac:(lia)) in Q; cbn [nth savedN_vals SAVEDN SAVED firstn map fst] in Q;
cbn [ms_regs mkst]; rewrite Q; clear Q
end.
Ltac chunk_bytesZ_step byte_tac :=
lazymatch goal with
| |- chunk_bytesZ _ ?cs ?off _ =>
let o := eval vm_compute in off in
first
[ lazymatch cs with
| context [mkChunk o (CVal 1 ?e)] => eapply (cbz_val _ cs off e); [cbn [In]; tauto | byte_tac | ]
end
| match cs with
| context [mkChunk ?co (CZero ?len)] => eapply (cbz_zero _ cs off co len); [cbn [In]; tauto | lia | ]
end ]
end.
Ltac chunk_bytesZ_tac n byte_tac :=
lazymatch n with
| O => apply cbz_nil
| Datatypes.S ?m => chunk_bytesZ_step byte_tac; chunk_bytesZ_tac m byte_tac
end.
Ltac rn_byte_tac H19c Hlp16 :=
idtac;
lazymatch goal with
| |- (bv_unsigned (sv_denot _ (SLit ?v)) mod 256 = _)%Z => let b := eval vm_compute in (bv_unsigned (Z_to_bv 64 v) mod 256)%Z in exact (eq_refl b)
| |- (bv_unsigned (sv_denot _ (SOff 19 0)) mod 256 = _)%Z => exact (byte_atom16 _ _ _ H19c Hlp16)
| |- (bv_unsigned (sv_denot _ (SAlu ALU_SRL (SOff 19 0) (SLit 8))) mod 256 = _)%Z => exact (byte_atom16_hi _ _ _ H19c Hlp16)
end.
Section S. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis FWRITE : fwrite_spec ubs0_msyms MR ubs0_A_fwrite.
Definition rn_post (regs : bvmap 5 word) L A mem md (g pgct rattr W H sgct loops f : Z) (S GCT : list Z) (b : rbound) : config -> Prop :=
fun c' => exists L' A' regs' mem' md' (res : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR RAWNEW_STK (spZ regs) (sink_fp f) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 res /\
((res = 0 /\ 256 < sgct /\ blocks L' A' = blocks L A /\ sink_at ubs0_msyms mem' md' f S /\ res_ok A' b) \/
(res <> 0 /\ sgct <= 256 /\
sink_at ubs0_msyms mem' md' f (S ++ YO07.raw_header W H sgct GCT rattr loops) /\
(exists b1 b2, blocks L' A' = b1 ++ (res, RAW_SIZE) :: b2 /\ blocks L A = b1 ++ b2) /\
obj_at ubs0segs mem' res LAY_Raw [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops; R_PENDING] /\
res_ok A' (rawnew_rb b))).
Lemma rn_fin :
forall L A mem md (regs0 regs1 : bvmap 5 word) L1 A1 mem1 md1 (g pgct rattr W H sgct loops res f : Z)
(S GCT : list Z) (b : rbound) (b1 b2 : list (Z * Z)) (pz : bool),
journal ubs0_msyms MR RAWNEW_STK (spZ regs0) (sink_fp f) L A mem md L1 A1 mem1 md1 ->
st_init_done A1 = true -> YK0s.ret_ok (getr regs0 1) ->
frame_savedN ubs0_msyms 9 regs0 mem1 (spZ regs0) ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 112) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 24 = getr regs0 24 -> getr regs1 25 = getr regs0 25 -> getr regs1 26 = getr regs0 26 -> getr regs1 27 = getr regs0 27 ->
getr regs1 8 = Z_to_bv 64 res -> getr regs1 18 = Z_to_bv 64 0 -> (pz = true -> getr regs1 10 = Z_to_bv 64 0) ->
obj_at ubs0segs mem1 res LAY_RawConfig [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] ->
blocks L1 A1 = b1 ++ (res, RAW_SIZE) :: b2 -> blocks L A = b1 ++ b2 ->
(forall i, 0 <= i < RAW_SIZE -> wr_byte RAWNEW_STK (spZ regs0) (sink_fp f) (blocks L A) (blocks L1 A1) (res + i)) ->
In (f, FILE_BLOCK) (blocks L A) ->
sink_at ubs0_msyms mem1 md1 f (S ++ YO07.raw_header W H sgct GCT rattr loops) ->
sgct <= 256 -> res_ok A1 (rawnew_rb b) ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 (if pz then PC_NWR else PC_NX)) mem1 (seg_rom ubs0segs)) md1)
(rn_post regs0 L A mem md g pgct rattr W H sgct loops f S GCT b).
Proof using IMG.
intros L A mem md regs0 regs1 L1 A1 mem1 md1 g pgct rattr W H sgct loops res f S GCT b b1 b2 pz
HJ Hid Hra0 HFS G2 G3 G4 G24 G25 G26 G27 G8 G18 G10 Hobj Hbl1 Hbl0 Hwr Hfin HSK Hsg HRq.
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : RAWNEW_STK = 8304) by reflexivity. assert (HRSv : RAW_SIZE = 48) by reflexivity.
assert (HFBv : FILE_BLOCK = 1264) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH1.
assert (Hrin : In (res, RAW_SIZE) (blocks L1 A1)) by (rewrite Hbl1; apply in_app_iff; right; left; reflexivity).
assert (Hfin1 : In (f, FILE_BLOCK) (blocks L1 A1)).
{ rewrite Hbl1. rewrite Hbl0 in Hfin. apply in_app_iff in Hfin as [Hf | Hf]; apply in_app_iff; [left | right; right]; exact Hf. }
destruct (heap_blocks_range _ _ LAWS L1 A1 mem1 md1 res RAW_SIZE HH1 Hrin ltac:(lia)) as (Hr0 & Hr1 & Hr16).
destruct (heap_blocks_range _ _ LAWS L1 A1 mem1 md1 f FILE_BLOCK HH1 Hfin1 ltac:(lia)) as (Hf0 & Hf1 & _).
assert (Hrf : res + 48 <= f \/ f + FILE_BLOCK <= res).
{ pose proof (heap_sep_in2 ubs0_msyms MR LAWS L1 A1 mem1 md1 (res, RAW_SIZE) (f, FILE_BLOCK) HH1 Hrin Hfin1) as Hd.
cbn [fst snd] in Hd. destruct Hd as [Hd|Hd]; [intros E0; injection E0 as E1 E2; lia | lia | lia]. }
assert (Henv : forall a, env_addr a -> ~ (res <= a < res + 48)).
{ intros a Hea Hr. pose proof Hrin as Hrin'. apply blocks_In in Hrin' as (q & Hq & Hqin).
destruct (skl_env ubs0_msyms a Hea) as (Himg1 & _). assert (Hrg : 0 <= a - res < RAW_SIZE) by lia.
apply (il_blocks IMG L1 A1 mem1 md1 q RAW_SIZE (a - res) (proj1 HH1) Hqin Hrg). rewrite Hq. replace (res + (a - res)) with a by lia. exact Himg1. }
set (extra := savedN_vals 9 regs0).
set (E := Ereg regs1 extra).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; apply ew_Ereg_nat; assumption).
assert (HX' : forall n j, (n = 32 + j)%nat -> (j < 9)%nat -> ew E n = nth j (savedN_vals 9 regs0) (Z_to_bv 64 0)).
{ intros n j -> Hj. apply ew_Ereg_extra. }
assert (HE2 : bv_unsigned (ew E 2) = spZ regs0 - 112) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (HE8 : bv_unsigned (ew E 8) = res) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HS : st_ok ubs0segs E (ss_fin pz) (mkst regs1 (Z_to_bv 64 (if pz then PC_NWR else PC_NX)) mem1 (seg_rom ubs0segs))).
{ assert (Hpc : (if pz then PC_NWR else PC_NX) = ss_pc (ss_fin pz)) by (destruct pz; reflexivity).
rewrite Hpc. unfold ss_fin. cbn [ss_pc]. apply entry_st_ok_full; fold E.
- destruct pz.
+ apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx |] | intros Hx; discriminate Hx |].
* exact G18.
* exact (G10 eq_refl).
+ apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx | exact G18].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE2.
split; [unfold spZ in *; lia|]. split; [unfold spZ in *; lia|]. split; [intros o Ho; lia|].
apply (saved_chunks_at_ok ubs0_msyms 9 _ mem1 regs0 (spZ regs0) 112 32 ltac:(lia)); [|exact HFS].
intros j Hj. apply (HX' (32 + j)%nat j eq_refl Hj).
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE8.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (present_writable ubs0_msyms).
apply (proj1 (heap_blocks _ _ LAWS L1 A1 mem1 md1 res RAW_SIZE o HH1 Hrin ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE8. unfold spZ in *. repeat split; lia.
- split; [| split; constructor].
cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE2, HE8.
change (2 ^ 4) with 16. unfold spZ in *.
repeat split; try lia.
all: first [ exact Hr16 | apply (rn_mod16_sub _ 7); exact Hsp0al ]. }
assert (WR : wr_ok E [YP09.mkRegion (Some 2%nat) 0 112 0 0 (saved_chunks_at 9 112 32); YP09.mkRegion (Some 8%nat) 0 48 40 44 []]
RAWNEW_STK (spZ regs0) (sink_fp f) (blocks L A) (blocks L1 A1)).
{ eapply wr_ok_cons_win; [reflexivity | exact HE2 | cbn [r_wlo r_whi]; intros Hx; lia |].
eapply wr_ok_cons_gen; [reflexivity | exact HE8 | | apply wr_ok_nil].
cbn [r_wlo r_whi]. intros a Ha. replace a with (res + (a - res)) by lia. apply Hwr. lia. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 (if pz then PC_NWR else PC_NX)) mem1 (seg_rom ubs0segs))) in HJ.
destruct pz.
all: jrun LAWS ubs0tbl_ok HS HJ; [exact WR|].
all: eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
all: try exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))).
all: try exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))).
all: unfold rn_post.
all: lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?Lf ?Af _ ?mdf =>
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
exists Lf, Af, (ms_regs msf), (ms_mem msf), mdf, res end end.
all: lazymatch type of HS with st_ok _ _ _ ?msf =>
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (res + 40 <= a < res + 44) -> mbyte ubs0segs (ms_mem msf) a = mbyte ubs0segs mem1 a)
by (intros a Ha Hna; lazymatch goal with HF : frame_of _ _ _ _ |- _ => apply (mbyte_of_frame _ _ _ _ a HF Ha) end;
intros r Hr; cbv [In] in Hr; repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; rewrite ?HE2, ?HE8; lia |]); destruct Hr) end.
all: split; [rn_rq HS HX' (1%bv:reg) 0%nat; rewrite Hra0; reflexivity|].
all: split; [exact HJ|].
all: split; [apply regs_preserved_intro_lzw|].
all: try (rn_rq HS HX' (2%bv:reg) 0%nat; rewrite HE2, <- (Z_to_bv_bv_unsigned 64 (getr regs0 2)); f_equal; unfold spZ; lia).
all: try (rn_rq HS HX' (3%bv:reg) 0%nat; rewrite (HE 3%nat 3%bv eq_refl); exact G3).
all: try (rn_rq HS HX' (4%bv:reg) 0%nat; rewrite (HE 4%nat 4%bv eq_refl); exact G4).
all: try (rn_rq HS HX' (8%bv:reg) 1%nat; reflexivity).
all: try (rn_rq HS HX' (9%bv:reg) 2%nat; reflexivity).
all: try (rn_rq HS HX' (18%bv:reg) 3%nat; reflexivity).
all: try (rn_rq HS HX' (19%bv:reg) 4%nat; reflexivity).
all: try (rn_rq HS HX' (20%bv:reg) 5%nat; reflexivity).
all: try (rn_rq HS HX' (21%bv:reg) 6%nat; reflexivity).
all: try (rn_rq HS HX' (22%bv:reg) 7%nat; reflexivity).
all: try (rn_rq HS HX' (23%bv:reg) 8%nat; reflexivity).
all: try (rn_rq HS HX' (24%bv:reg) 0%nat; rewrite (HE 24%nat 24%bv eq_refl); exact G24).
all: try (rn_rq HS HX' (25%bv:reg) 0%nat; rewrite (HE 25%nat 25%bv eq_refl); exact G25).
all: try (rn_rq HS HX' (26%bv:reg) 0%nat; rewrite (HE 26%nat 26%bv eq_refl); exact G26).
all: try (rn_rq HS HX' (27%bv:reg) 0%nat; rewrite (HE 27%nat 27%bv eq_refl); exact G27).
all: split; [exact Hid|].
all: split; [rn_rq HS HX' (10%bv:reg) 0%nat; rewrite (HE 8%nat 8%bv eq_refl), G8; reflexivity|].
all: right; split; [lia|]; split; [exact Hsg|].
all: split.
1,3: apply (sink_at_frame ubs0_msyms mem1 _ md1 f _); [|exact HSK]; intros a Ha;
destruct Ha as [Ha | Ha];
[ apply KM; lia
| pose proof (ubs0_env_addr_range a Ha) as Hea; pose proof (Henv a Ha) as Hna; apply KM; lia ].
all: split; [exists b1, b2; split; [exact Hbl1 | exact Hbl0]|].
all: split; [|exact HRq].
all: change [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops; R_PENDING]
with ([ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] ++ [R_PENDING]).
all: unfold LAY_Raw; apply rn_obj_at_app.
1,3: eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_RawConfig_ok) |];
intros i Hi; apply KM; lia.
all: split; [|exact I].
all: eapply rn_fok_eq;
[ eapply (st_field_low ubs0segs _ _ _ 1 _ 8 _ 40 4%N _ (2 ^ 32) HS);
[ reflexivity | reflexivity | cbn [r_chunks]; repeat (first [left; reflexivity | right]) | exact HE8 | cbn; lia | reflexivity ] | ].
all: cbn [sv_denot]; rewrite ?U_lit by lia; reflexivity.
Qed.
Lemma rn_net :
forall L A mem md (regs0 regs2 : bvmap 5 word) L1 A1 mem2 md1
(cfgp g pgct rattr W H sgct loops res f : Z) gvals (S GCT : list Z) (b : rbound) (b1 b2 : list (Z * Z)),
journal ubs0_msyms MR RAWNEW_STK (spZ regs0) (sink_fp f) L A mem md L1 A1 mem2 md1 ->
st_init_done A1 = true -> YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
spZ regs0 <= 2 ^ 47 ->
frame_savedN ubs0_msyms 9 regs0 mem2 (spZ regs0) ->
getr regs2 2 = Z_to_bv 64 (spZ regs0 - 112) -> getr regs2 3 = getr regs0 3 -> getr regs2 4 = getr regs0 4 ->
getr regs2 24 = getr regs0 24 -> getr regs2 25 = getr regs0 25 -> getr regs2 26 = getr regs0 26 -> getr regs2 27 = getr regs0 27 ->
getr regs2 8 = Z_to_bv 64 res -> getr regs2 9 = Z_to_bv 64 cfgp -> getr regs2 18 = Z_to_bv 64 0 ->
getr regs2 19 = Z_to_bv 64 loops -> has_net rattr = true ->
cfgp mod 8 = 0 -> spZ regs0 <= cfgp -> cfgp + 40 <= 2 ^ 63 ->
obj_at ubs0segs mem2 cfgp LAY_RawConfig [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] ->
obj_at ubs0segs mem2 res LAY_RawConfig [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] ->
obj_at ubs0segs mem2 g LAY_CGIF gvals -> nth_error gvals CG_wfn = Some 0 -> nth_error gvals CG_file = Some f ->
In (g, CGIF_SIZE) (blocks L A) -> In (f, FILE_BLOCK) (blocks L A) ->
blocks L1 A1 = b1 ++ (res, RAW_SIZE) :: b2 -> blocks L A = b1 ++ b2 ->
(forall i, 0 <= i < RAW_SIZE -> wr_byte RAWNEW_STK (spZ regs0) (sink_fp f) (blocks L A) (blocks L1 A1) (res + i)) ->
mbyte ubs0segs mem2 (spZ regs0 - 73) = Some (Z_to_bv 8 0) ->
sink_at ubs0_msyms mem2 md1 f (S ++ YO07.raw_header W H sgct GCT 0 0) ->
Z.of_nat (length S) + 1024 <= SINK_MAX ->
sgct <= 256 -> res_ok A1 (rawnew_rb b) ->
SR ubs0segs (mkCfg (mkst regs2 (Z_to_bv 64 PC_NM) mem2 (seg_rom ubs0segs)) md1)
(rn_post regs0 L A mem md g pgct rattr W H sgct loops f S GCT b).
Proof using IMG FWRITE.
intros L A mem md regs0 regs2 L1 A1 mem2 md1 cfgp g pgct rattr W H sgct loops res f gvals S GCT b b1 b2
HJ Hid Hra0 Htp0 Hsp47 HFS G2 G3 G4 G24 G25 G26 G27 G8 G9 G18 G19 HNET Hcal Hclo Hchi Hcfg Hobj Hgobj Hwfn Hfile
Hgin Hfin Hbl1 Hbl0 Hwr H73 HSK Hroom Hsg HRq.
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : RAWNEW_STK = 8304) by reflexivity. assert (HRSv : RAW_SIZE = 48) by reflexivity.
assert (HFBv : FILE_BLOCK = 1264) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HWSv : WRITECB_STK = 528) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH1.
assert (Hsub : forall x, In x (blocks L A) -> In x (blocks L1 A1)).
{ intros x Hx. rewrite Hbl1. rewrite Hbl0 in Hx. apply in_app_iff in Hx as [Hx | Hx]; apply in_app_iff; [left | right; right]; exact Hx. }
assert (Hrin : In (res, RAW_SIZE) (blocks L1 A1)) by (rewrite Hbl1; apply in_app_iff; right; left; reflexivity).
pose proof (Hsub _ Hfin) as Hfin1. pose proof (Hsub _ Hgin) as Hgin1.
destruct (heap_blocks_range _ _ LAWS L1 A1 mem2 md1 res RAW_SIZE HH1 Hrin ltac:(lia)) as (Hr0 & Hr1 & Hr16).
destruct (heap_blocks_range _ _ LAWS L1 A1 mem2 md1 f FILE_BLOCK HH1 Hfin1 ltac:(lia)) as (Hf0 & Hf1 & Hf16).
destruct (heap_blocks_range _ _ LAWS L1 A1 mem2 md1 g CGIF_SIZE HH1 Hgin1 ltac:(lia)) as (Hg0 & Hg1 & Hg16).
assert (Hrf : res + 48 <= f \/ f + FILE_BLOCK <= res).
{ pose proof (heap_sep_in2 ubs0_msyms MR LAWS L1 A1 mem2 md1 (res, RAW_SIZE) (f, FILE_BLOCK) HH1 Hrin Hfin1) as Hd.
cbn [fst snd] in Hd. destruct Hd as [Hd|Hd]; [intros E0; injection E0 as E1 E2; lia | lia | lia]. }
pose proof (obj_at_range _ _ _ _ _ Hcfg 7%nat loops eq_refl) as Hlp. cbn in Hlp.
pose proof (obj_at_range _ _ _ _ _ Hcfg 6%nat sgct eq_refl) as Hsg0. cbn in Hsg0.
set (cvals := [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops]) in Hcfg, Hobj.
set (E := Ereg regs2 (map (Z_to_bv 64) cvals)).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr) by (intros; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error cvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. pose proof (Ereg_vals2 regs2 [] cvals [] j v Hj) as Q. cbn [map app length] in Q.
rewrite app_nil_r, Nat.add_0_l in Q. exact Q. }
assert (HE2 : bv_unsigned (ew E 2) = spZ regs0 - 112) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (HE9 : bv_unsigned (ew E 9) = cfgp) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; unfold spZ in *; lia).
assert (HS : st_ok ubs0segs E ss_net (mkst regs2 (Z_to_bv 64 PC_NM) mem2 (seg_rom ubs0segs))).
{ unfold ss_net. apply entry_st_ok_full; fold E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE2.
split; [unfold spZ in *; lia|]. split; [unfold spZ in *; lia|]. split; [intros o Ho; apply Hstw; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [reflexivity | cbn; lia | cbn; lia |].
intros kk Hkk. cbn in Hkk. assert (Hkk0 : kk = 0%nat) by lia. subst kk.
replace (spZ regs0 - 112 + 39 + Z.of_nat 0) with (spZ regs0 - 73) by lia. rewrite H73. reflexivity.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE9.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply (obj_chunks_gen_ok ubs0segs E mem2 cfgp LAY_RawConfig cvals 32 lits_RawConfig Hcfg (proj2 LAY_RawConfig_ok) HX).
apply lits_RawConfig_ok.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE9. unfold spZ in *. repeat split; lia.
- split; [| split; constructor].
cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE2, HE9.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. unfold spZ in *.
repeat split; try lia.
all: first [ exact Hcal | apply (rn_mod16_sub _ 7); exact Hsp0al ]. }
assert (WR : wr_ok E [YP09.mkRegion (Some 2%nat) 0 112 21 39 [mkChunk 39 (CVal 1 (SLit 0))];
YP09.mkRegion (Some 9%nat) 0 40 0 0 (obj_chunks_gen LAY_RawConfig 32 lits_RawConfig)]
RAWNEW_STK (spZ regs0) (sink_fp f) (blocks L A) (blocks L1 A1)).
{ eapply wr_ok_cons_win; [reflexivity | exact HE2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HE9 | cbn [r_wlo r_whi]; intros Hx; lia | apply wr_ok_nil]. }
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 PC_NM) mem2 (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cgif_writecb; [exact WR|].
jreg HS (10%bv:reg) as Ha10. jreg HS (11%bv:reg) as Ha11. jreg HS (12%bv:reg) as Ha12.
jreg HS (2%bv:reg) as Ha2. jreg HS (4%bv:reg) as Ha4. jreg HS (1%bv:reg) as Ha1.
rewrite HE2 in Ha11. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Ha4.
assert (Hsp : spZ (ms_regs ms) = spZ regs0 - 112) by (unfold spZ at 1; rewrite Ha2; exact HE2).
assert (Hlp16 : 0 <= loops < 2 ^ 16) by lia.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - 91 <= a < spZ regs0 - 73) -> mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs mem2 a).
{ intros a Ha Hna. lazymatch goal with HF : frame_of _ _ _ _ |- _ => apply (mbyte_of_frame _ _ _ _ a HF Ha) end.
intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; rewrite ?HE2, ?HE9; lia |]). destruct Hr. }
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
assert (H19c : ew Ec 19 = Z_to_bv 64 loops) by (ew_strip; rewrite (HE 19%nat 19%bv eq_refl); exact G19);
let rg := eval vm_compute in (nth 0 (ss_mem ssc) (YP09.mkRegion None 0 0 0 0 [])) in
eassert (HG8 : garr8 ubs0segs (ms_mem msc) (spZ regs0 - 112 + 21) _);
[ eapply (garr8_of_chunk_bytesZ ubs0segs Ec (ms_mem msc) rg 2%nat (spZ regs0 - 112) _ 21);
[ exact (vst_ok_region_nth ubs0segs Ec ssc msc 0%nat rg HS eq_refl) | reflexivity | ew_strip; exact HE2
| cbn [r_chunks]; chunk_bytesZ_tac 19%nat ltac:(rn_byte_tac H19c Hlp16) ]
| ] end.
assert (HobjC : obj_at ubs0segs (ms_mem ms) g LAY_CGIF gvals).
{ apply (obj_at_transport_range ubs0segs mem2 (ms_mem ms) g LAY_CGIF gvals CGIF_SIZE Hgobj); [vm_compute; reflexivity|].
intros i Hi. apply KM; lia. }
assert (HSKc : sink_at ubs0_msyms (ms_mem ms) md1 f (S ++ YO07.raw_header W H sgct GCT 0 0)).
{ apply (sink_at_frame ubs0_msyms mem2 _ md1 f _); [|exact HSK]. intros a Ha.
destruct Ha as [Ha | Ha]; [apply KM; lia | pose proof (ubs0_env_addr_range a Ha) as Hea; apply KM; lia]. }
pose proof (rn_hdr0_len W H sgct GCT ltac:(lia)) as Hhl.
eapply SR_bind.
{ eapply (jwrite ubs0_msyms MR LAWS ubs0_A_cgif_writecb (ubs0_cgif_writecb API IMG FWRITE))
with (g := g) (gvals := gvals) (src := spZ regs0 - 112 + 21) (n := 19) (f := f) (S := S ++ YO07.raw_header W H sgct GCT 0 0);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Ha1 | apply ret_ok_even; vm_compute; reflexivity
| rewrite Ha10; exact (HX 1%nat g eq_refl) | exact Ha11 | exact Ha12
| rewrite Hsp; apply (rn_mod16_sub _ 7); exact Hsp0al | rewrite Hsp; lia | rewrite Hsp; lia | rewrite Hsp; lia
| exact Ha4 | exact HobjC | exact Hwfn | exact Hfile | exact Hgin1 | exact Hfin1 | exact HSKc | exact HG8 | reflexivity
| lia | lia | lia | rewrite Hsp; lia | rewrite length_app; lia | lia | ].
intros a Ha; exact Ha. }
cbv beta. intros c' (regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hr10 & HSK3 & Hhi3 & Hblk3).
rewrite Hsp in Hhi3.
assert (PR : forall (r : reg) (z : Z), bv_unsigned r = z -> callee_saved z -> getr regs3 r = getr (ms_regs ms) r).
{ intros r z <- Hc. pose proof (HP3 (bv_unsigned r) Hc) as Q. rewrite Z_to_bv_bv_unsigned in Q. exact Q. }
assert (Hpc : Z_to_bv 64 (if true then PC_NWR else PC_NX) = getr (ms_regs ms) 1) by (rewrite Ha1; reflexivity).
rewrite <- Ha1, <- Hpc.
apply (rn_fin L A mem md regs0 regs3 L1 A1 mem3 md3 g pgct rattr W H sgct loops res f S GCT b b1 b2 true).
- exact HJ3.
- exact Hid.
- exact Hra0.
- apply (rn_fs_transport regs0 (ms_mem ms)); [apply (rn_fs_transport regs0 mem2); [exact HFS | intros a Ha; apply KM; lia] |].
intros a Ha. apply (proj1 (Hhi3 a ltac:(lia) ltac:(lia))).
- rewrite (PR 2%bv 2 eq_refl ltac:(unfold callee_saved; lia)), Ha2, (HE 2%nat 2%bv eq_refl). exact G2.
- jreg HS (3%bv:reg) as Q3. rewrite (PR 3%bv 3 eq_refl ltac:(unfold callee_saved; lia)), Q3, (HE 3%nat 3%bv eq_refl). exact G3.
- rewrite (PR 4%bv 4 eq_refl ltac:(unfold callee_saved; lia)), Ha4. symmetry. exact Htp0.
- jreg HS (24%bv:reg) as Q24. rewrite (PR 24%bv 24 eq_refl ltac:(unfold callee_saved; lia)), Q24, (HE 24%nat 24%bv eq_refl). exact G24.
- jreg HS (25%bv:reg) as Q25. rewrite (PR 25%bv 25 eq_refl ltac:(unfold callee_saved; lia)), Q25, (HE 25%nat 25%bv eq_refl). exact G25.
- jreg HS (26%bv:reg) as Q26. rewrite (PR 26%bv 26 eq_refl ltac:(unfold callee_saved; lia)), Q26, (HE 26%nat 26%bv eq_refl). exact G26.
- jreg HS (27%bv:reg) as Q27. rewrite (PR 27%bv 27 eq_refl ltac:(unfold callee_saved; lia)), Q27, (HE 27%nat 27%bv eq_refl). exact G27.
- jreg HS (8%bv:reg) as Q8. rewrite (PR 8%bv 8 eq_refl ltac:(unfold callee_saved; lia)), Q8, (HE 8%nat 8%bv eq_refl). exact G8.
- jreg HS (18%bv:reg) as Q18. rewrite (PR 18%bv 18 eq_refl ltac:(unfold callee_saved; lia)), Q18, (HE 18%nat 18%bv eq_refl). exact G18.
- intros _. exact Hr10.
- eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_RawConfig_ok) |].
intros i Hi. etransitivity; [apply (Hblk3 res 48 i Hrin); [lia | intros (r & [<- | [<- | []]] & Hr); cbn [fst snd sink_token] in Hr; lia] | apply KM; lia].
- exact Hbl1.
- exact Hbl0.
- exact Hwr.
- exact Hfin.
- rewrite rn_hdr_split, HNET, app_assoc.
lazymatch type of HSK3 with sink_at _ _ _ _ (_ ++ ?l) => replace (net19 loops) with l by reflexivity end. exact HSK3.
- exact Hsg.
- exact HRq.
Qed.
Lemma rn_tail :
forall L A mem md (regs0 regs1 : bvmap 5 word) L1 A1 mem1 md1
(cfgp g pgct rattr W H sgct loops res f : Z) gvals (S GCT : list Z) (b : rbound) (b1 b2 : list (Z * Z)),
journal ubs0_msyms MR RAWNEW_STK (spZ regs0) (sink_fp f) L A mem md L1 A1 mem1 md1 ->
st_init_done A1 = true -> YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
spZ regs0 <= 2 ^ 47 ->
frame_savedN ubs0_msyms 9 regs0 mem1 (spZ regs0) ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 112) -> getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 24 = getr regs0 24 -> getr regs1 25 = getr regs0 25 -> getr regs1 26 = getr regs0 26 -> getr regs1 27 = getr regs0 27 ->
getr regs1 8 = Z_to_bv 64 res -> getr regs1 9 = Z_to_bv 64 cfgp -> getr regs1 18 = Z_to_bv 64 0 ->
cfgp mod 8 = 0 -> spZ regs0 <= cfgp -> cfgp + 40 <= 2 ^ 63 ->
obj_at ubs0segs mem1 cfgp LAY_RawConfig [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] ->
obj_at ubs0segs mem1 res LAY_RawConfig [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] ->
obj_at ubs0segs mem1 g LAY_CGIF gvals -> nth_error gvals CG_wfn = Some 0 -> nth_error gvals CG_file = Some f ->
In (g, CGIF_SIZE) (blocks L A) -> In (f, FILE_BLOCK) (blocks L A) ->
blocks L1 A1 = b1 ++ (res, RAW_SIZE) :: b2 -> blocks L A = b1 ++ b2 ->
(forall i, 0 <= i < RAW_SIZE -> wr_byte RAWNEW_STK (spZ regs0) (sink_fp f) (blocks L A) (blocks L1 A1) (res + i)) ->
sink_at ubs0_msyms mem1 md1 f (S ++ YO07.raw_header W H sgct GCT 0 0) ->
Z.of_nat (length S) + 1024 <= SINK_MAX ->
sgct <= 256 -> res_ok A1 (rawnew_rb b) ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_NT) mem1 (seg_rom ubs0segs)) md1)
(rn_post regs0 L A mem md g pgct rattr W H sgct loops f S GCT b).
Proof using IMG FWRITE.
intros L A mem md regs0 regs1 L1 A1 mem1 md1 cfgp g pgct rattr W H sgct loops res f gvals S GCT b b1 b2
HJ Hid Hra0 Htp0 Hsp47 HFS G2 G3 G4 G24 G25 G26 G27 G8 G9 G18 Hcal Hclo Hchi Hcfg Hobj Hgobj Hwfn Hfile
Hgin Hfin Hbl1 Hbl0 Hwr HSK Hroom Hsg HRq.
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HSTKv : RAWNEW_STK = 8304) by reflexivity. assert (HRSv : RAW_SIZE = 48) by reflexivity.
assert (HFBv : FILE_BLOCK = 1264) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH1.
assert (Hrin : In (res, RAW_SIZE) (blocks L1 A1)) by (rewrite Hbl1; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS L1 A1 mem1 md1 res RAW_SIZE HH1 Hrin ltac:(lia)) as (Hr0 & Hr1 & Hr16).
assert (Hsub : forall x, In x (blocks L A) -> In x (blocks L1 A1)).
{ intros x Hx. rewrite Hbl1. rewrite Hbl0 in Hx. apply in_app_iff in Hx as [Hx | Hx]; apply in_app_iff; [left | right; right]; exact Hx. }
pose proof (Hsub _ Hfin) as Hfin1. pose proof (Hsub _ Hgin) as Hgin1.
destruct (heap_blocks_range _ _ LAWS L1 A1 mem1 md1 f FILE_BLOCK HH1 Hfin1 ltac:(lia)) as (Hf0 & Hf1 & Hf16).
destruct (heap_blocks_range _ _ LAWS L1 A1 mem1 md1 g CGIF_SIZE HH1 Hgin1 ltac:(lia)) as (Hg0 & Hg1 & Hg16).
pose proof (obj_at_range _ _ _ _ _ Hcfg 3%nat rattr eq_refl) as Hat. cbn in Hat.
pose proof (obj_at_range _ _ _ _ _ Hcfg 7%nat loops eq_refl) as Hlp. cbn in Hlp.
set (cvals := [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops]) in Hcfg, Hobj.
set (E := Ereg regs1 (map (Z_to_bv 64) cvals)).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error cvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. pose proof (Ereg_vals2 regs1 [] cvals [] j v Hj) as Q. cbn [map app length] in Q.
rewrite app_nil_r, Nat.add_0_l in Q. exact Q. }
assert (HE2 : bv_unsigned (ew E 2) = spZ regs0 - 112) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (HE9 : bv_unsigned (ew E 9) = cfgp) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; unfold spZ in *; lia).
assert (HS : st_ok ubs0segs E ss_nt (mkst regs1 (Z_to_bv 64 PC_NT) mem1 (seg_rom ubs0segs))).
{ unfold ss_nt. apply entry_st_ok_full; fold E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE2.
split; [unfold spZ in *; lia|]. split; [unfold spZ in *; lia|]. split; [intros o Ho; lia|]. constructor.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE9.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply (obj_chunks_gen_ok ubs0segs E mem1 cfgp LAY_RawConfig cvals 32 lits_RawConfig Hcfg (proj2 LAY_RawConfig_ok) HX).
apply lits_RawConfig_ok.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HE2, HE9. unfold spZ in *. repeat split; lia.
- split; [| split; constructor].
cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE2, HE9.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. unfold spZ in *.
repeat split; try lia.
all: first [ exact Hcal | apply (rn_mod16_sub _ 7); exact Hsp0al ]. }
assert (WR : wr_ok E [YP09.mkRegion (Some 2%nat) 0 112 0 0 [];
YP09.mkRegion (Some 9%nat) 0 40 0 0 (obj_chunks_gen LAY_RawConfig 32 lits_RawConfig)]
RAWNEW_STK (spZ regs0) (sink_fp f) (blocks L A) (blocks L1 A1)).
{ eapply wr_ok_cons_win; [reflexivity | exact HE2 | cbn [r_wlo r_whi]; intros Hx; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HE9 | cbn [r_wlo r_whi]; intros Hx; lia | apply wr_ok_nil]. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PC_NT) mem1 (seg_rom ubs0segs))) in HJ.
jrun LAWS ubs0tbl_ok HS HJ; [exact WR|].
assert (KM : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem ms) a = mbyte ubs0segs mem1 a).
{ intros a Ha. lazymatch goal with HF : frame_of _ _ _ _ |- _ => apply (mbyte_of_frame _ _ _ _ a HF Ha) end.
intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; lia |]). destruct Hr. }
lazymatch type of HS with st_ok _ ?Ec _ _ => assert (H35 : ew Ec 35 = Z_to_bv 64 rattr) by (ew_strip; exact (HX 3%nat rattr eq_refl)) end.
jbranch ubs0tbl HS.
- rewrite branch_ne_U, U_and_lit, (rn_U_zext32 _ 35 rattr H35), U_lit in Hc by lia.
assert (HNET : has_net rattr = false) by (rewrite has_net_land; destruct (Z.land rattr 3 =? 1); cbn in Hc; first [reflexivity | discriminate Hc]).
jrun_to LAWS ubs0tbl_ok HS HJ PC_NX; [exact WR|].
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msx) a = mbyte ubs0segs mem1 a)
by (intros a Ha; rewrite <- (KM a Ha); lazymatch goal with HF : frame_of _ _ (ms_mem ms) _ |- _ => apply (mbyte_of_frame _ _ _ _ a HF Ha) end;
intros r Hr; cbv [In] in Hr; repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; lia |]); destruct Hr) end.
lazymatch type of HS with st_ok _ ?Ec ?ssx ?msx =>
rewrite (st_ok_mkst _ _ _ _ HS eq_refl);
replace (Z_to_bv 64 (ss_pc ssx)) with (Z_to_bv 64 (if false then PC_NWR else PC_NX)) by (f_equal; vm_compute; reflexivity);
apply (rn_fin L A mem md regs0 (ms_regs msx) L1 A1 (ms_mem msx) md1 g pgct rattr W H sgct loops res f S GCT b b1 b2 false)
end.
+ exact HJ.
+ exact Hid.
+ exact Hra0.
+ apply (rn_fs_transport regs0 mem1); [exact HFS | intros a Ha; apply KM2; lia].
+ jreg HS (2%bv:reg) as Q. rewrite Q, (HE 2%nat 2%bv eq_refl). exact G2.
+ jreg HS (3%bv:reg) as Q. rewrite Q, (HE 3%nat 3%bv eq_refl). exact G3.
+ jreg HS (4%bv:reg) as Q. rewrite Q, (HE 4%nat 4%bv eq_refl). exact G4.
+ jreg HS (24%bv:reg) as Q. rewrite Q, (HE 24%nat 24%bv eq_refl). exact G24.
+ jreg HS (25%bv:reg) as Q. rewrite Q, (HE 25%nat 25%bv eq_refl). exact G25.
+ jreg HS (26%bv:reg) as Q. rewrite Q, (HE 26%nat 26%bv eq_refl). exact G26.
+ jreg HS (27%bv:reg) as Q. rewrite Q, (HE 27%nat 27%bv eq_refl). exact G27.
+ jreg HS (8%bv:reg) as Q. rewrite Q, (HE 8%nat 8%bv eq_refl). exact G8.
+ jreg HS (18%bv:reg) as Q. rewrite Q, (HE 18%nat 18%bv eq_refl). exact G18.
+ intros Hx. discriminate Hx.
+ eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_RawConfig_ok) |]. intros i Hi. apply KM2; lia.
+ exact Hbl1.
+ exact Hbl0.
+ exact Hwr.
+ exact Hfin.
+ rewrite rn_hdr_split, HNET, app_nil_r.
apply (sink_at_frame ubs0_msyms mem1 _ md1 f _); [|exact HSK]. intros a Ha.
destruct Ha as [Ha | Ha]; [apply KM2; lia | pose proof (ubs0_env_addr_range a Ha) as Hea; apply KM2; lia].
+ exact Hsg.
+ exact HRq.
- rewrite branch_ne_U, U_and_lit, (rn_U_zext32 _ 35 rattr H35), U_lit in Hc by lia.
assert (HNET : has_net rattr = true) by (rewrite has_net_land; destruct (Z.land rattr 3 =? 1); cbn in Hc; first [reflexivity | discriminate Hc]).
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_memset; [exact WR|].
jreg HS (10%bv:reg) as Ma0. jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
jreg HS (2%bv:reg) as M2.
rewrite HE2 in Ma0.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs0segs (ms_mem msc) a = mbyte ubs0segs mem1 a)
by (intros a Ha; rewrite <- (KM a Ha); lazymatch goal with HF : frame_of _ _ (ms_mem ms) _ |- _ => apply (mbyte_of_frame _ _ _ _ a HF Ha) end;
intros r Hr; cbv [In] in Hr; repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; lia |]); destruct Hr);
assert (M19 : getr (ms_regs msc) 19 = Z_to_bv 64 loops);
[ pose proof (st_ok_reg ubs0segs Ec ssc msc 19%bv HS) as Q; eval_sr_get_in Q; rewrite Q;
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot _ _)); f_equal;
change (U Ec (SExt false 16 (SOff 39 0)) = loops);
rewrite U_SExt; cbv beta iota; rewrite (U_atom Ec 39 loops) by (first [ew_strip; exact (HX 7%nat loops eq_refl) | lia]);
change (2 ^ Z.of_N 16) with (2 ^ 16); rewrite Z.mod_small by lia; apply zcanon_id; unfold M64; lia
| ];
pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw2) & _);
eapply SR_bind;
[ eapply (jmemset ubs0_msyms MR LAWS IMG ubs0_A_memset ubs0_memset Ec _ _ RAWNEW_STK (spZ regs0) (sink_fp f) L A mem md L1 A1 _ (spZ regs0 - 112 + 22) 0 18);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | unfold spZ in *; lia | unfold spZ in *; lia | lia
| intros i Hi; apply writable_off_img_present; [unfold spZ in *; lia | unfold in_img1; unfold spZ in *; lia | apply Hstw2; lia]
| intros a Ha; left; lia ]
| ];
cbv beta; intros c' (regs_m & mem_m & -> & HJ_m & Hd10_m & Hfr_m & Hout_m & Hgr_m & Hzero_m);
assert (Hpc : Z_to_bv 64 PC_NM = getr (ms_regs msc) 1) by (rewrite Mra; reflexivity);
rewrite <- Mra, <- Hpc;
assert (KMm : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - 90 <= a < spZ regs0 - 72) -> mbyte ubs0segs mem_m a = mbyte ubs0segs mem1 a)
by (intros a Ha Hna; rewrite <- (KM2 a Ha); apply (mbyte_eq_of ubs0_msyms); apply Hout_m; rewrite unsigned_lit_small by lia; lia);
assert (PRm : forall r : reg, reg_in r MEMSET_CLOB = false -> getr regs_m r = getr (ms_regs msc) r) by exact Hfr_m
end.
apply (rn_net L A mem md regs0 regs_m L1 A1 mem_m md1 cfgp g pgct rattr W H sgct loops res f gvals S GCT b b1 b2).
+ exact HJ_m.
+ exact Hid.
+ exact Hra0.
+ exact Htp0.
+ exact Hsp47.
+ apply (rn_fs_transport regs0 mem1); [exact HFS | intros a Ha; apply KMm; lia].
+ rewrite (PRm 2%bv ltac:(vm_compute; reflexivity)), M2, (HE 2%nat 2%bv eq_refl). exact G2.
+ rewrite (PRm 3%bv ltac:(vm_compute; reflexivity)). jreg HS (3%bv:reg) as Q. rewrite Q, (HE 3%nat 3%bv eq_refl). exact G3.
+ rewrite (PRm 4%bv ltac:(vm_compute; reflexivity)). jreg HS (4%bv:reg) as Q. rewrite Q, (HE 4%nat 4%bv eq_refl). exact G4.
+ rewrite (PRm 24%bv ltac:(vm_compute; reflexivity)). jreg HS (24%bv:reg) as Q. rewrite Q, (HE 24%nat 24%bv eq_refl). exact G24.
+ rewrite (PRm 25%bv ltac:(vm_compute; reflexivity)). jreg HS (25%bv:reg) as Q. rewrite Q, (HE 25%nat 25%bv eq_refl). exact G25.
+ rewrite (PRm 26%bv ltac:(vm_compute; reflexivity)). jreg HS (26%bv:reg) as Q. rewrite Q, (HE 26%nat 26%bv eq_refl). exact G26.
+ rewrite (PRm 27%bv ltac:(vm_compute; reflexivity)). jreg HS (27%bv:reg) as Q. rewrite Q, (HE 27%nat 27%bv eq_refl). exact G27.
+ rewrite (PRm 8%bv ltac:(vm_compute; reflexivity)). jreg HS (8%bv:reg) as Q. rewrite Q, (HE 8%nat 8%bv eq_refl). exact G8.
+ rewrite (PRm 9%bv ltac:(vm_compute; reflexivity)). jreg HS (9%bv:reg) as Q. rewrite Q, (HE 9%nat 9%bv eq_refl). exact G9.
+ rewrite (PRm 18%bv ltac:(vm_compute; reflexivity)). jreg HS (18%bv:reg) as Q. rewrite Q, (HE 18%nat 18%bv eq_refl). exact G18.
+ rewrite (PRm 19%bv ltac:(vm_compute; reflexivity)). exact M19.
+ exact HNET.
+ exact Hcal.
+ exact Hclo.
+ exact Hchi.
+ apply (obj_at_transport_range ubs0segs mem1 mem_m cfgp LAY_RawConfig _ 40 Hcfg (proj1 LAY_RawConfig_ok)).
intros i Hi. apply KMm; unfold spZ in *; lia.
+ apply (obj_at_transport_range ubs0segs mem1 mem_m res LAY_RawConfig _ 40 Hobj (proj1 LAY_RawConfig_ok)).
intros i Hi. apply KMm; unfold spZ in *; lia.
+ apply (obj_at_transport_range ubs0segs mem1 mem_m g LAY_CGIF gvals CGIF_SIZE Hgobj); [vm_compute; reflexivity|].
intros i Hi. apply KMm; unfold spZ in *; lia.
+ exact Hwfn.
+ exact Hfile.
+ exact Hgin.
+ exact Hfin.
+ exact Hbl1.
+ exact Hbl0.
+ exact Hwr.
+ replace (spZ regs0 - 73) with (spZ regs0 - 112 + 22 + 17) by lia. apply Hzero_m. lia.
+ apply (sink_at_frame ubs0_msyms mem1 _ md1 f _); [|exact HSK]. intros a Ha.
destruct Ha as [Ha | Ha]; [apply KMm; unfold spZ in *; lia | pose proof (ubs0_env_addr_range a Ha) as Hea; apply KMm; unfold spZ in *; lia].
+ exact Hroom.
+ exact Hsg.
+ exact HRq.
Qed.
End S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
