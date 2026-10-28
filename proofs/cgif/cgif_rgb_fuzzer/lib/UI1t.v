(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3l YI00 YI02 YI01 YI03
UI1e UI1c UI39 UI1i UI59 UI56 YI0x UI57
UI1h UI16 UI1z UI1k UI21 UI22 UI23 UI1j UI1s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma wrap64_nz : forall v, -256 < v < 256 -> v <> 0 -> zcanon (bv_wrap 64 v + 0) <> 0.
Proof. intros v Hv Hnz. unfold zcanon, bv_wrap, M64. cbn [bv_modulus]. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia.
intros Hm. apply (Z.mod_divide v (2 ^ 64)) in Hm; [|lia]. destruct Hm as [q Hq]. assert (q = 0 \/ q <= -1 \/ q >= 1) by lia. nia. Qed.
Lemma cmpPixel_fn_range : forall cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef a b,
-256 < cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef a b < 256.
Proof.
intros. unfold cmpPixel_fn.
repeat (destruct (_ : bool); try lia). apply memcmp_spec_range.
Qed.
Lemma U_xor1_sltu : forall E a b, U E (SAlu ALU_XOR (SAlu ALU_SLTU a b) (SLit 1)) = if U E a <? U E b then 0 else 1.
Proof.
intros E a b. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
destruct (U E a <? U E b); reflexivity.
Qed.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition XaddrW (aw ai ax : nat) : sv :=
SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SMd M_MUL (SAlu ALU_AND (SOff ai 0) (SLit 65535)) (SOff aw 0)) (SAlu ALU_AND (SOff ax 0) (SLit 65535))) (SLit 32)) (SLit 32).
Definition Xaddr (ai ax : nat) : sv := XaddrW 25 ai ax.
Lemma U_XaddrW : forall E aw ai ax i x W, ew E ai = Z_to_bv 64 i -> ew E ax = Z_to_bv 64 x -> ew E aw = Z_to_bv 64 W ->
0 <= i < 65536 -> 0 <= x < 65536 -> 0 <= W < 65536 -> i * W + x < 2 ^ 32 -> U E (XaddrW aw ai ax) = i * W + x.
Proof.
intros E aw ai ax i x W Hi Hx HW Ri Rx RW Hs. unfold XaddrW. rewrite U_zext32_mod.
rewrite (U_add_small E _ _ (i * W) x); [apply Z.mod_small; nia | | | nia | lia | nia].
- apply (U_mul_small' E _ _ i W); [| apply (U_atom _ aw W HW); lia | lia | lia | nia].
rewrite U_and_lit, (U_atom _ ai i Hi) by lia. apply land_ffff. lia.
- rewrite U_and_lit, (U_atom _ ax x Hx) by lia. apply land_ffff. lia.
Qed.
Lemma U_Xaddr : forall E ai ax i x W, ew E ai = Z_to_bv 64 i -> ew E ax = Z_to_bv 64 x -> ew E 25 = Z_to_bv 64 W ->
0 <= i < 65536 -> 0 <= x < 65536 -> 0 <= W < 65536 -> i * W + x < 2 ^ 32 -> U E (Xaddr ai ax) = i * W + x.
Proof. intros E ai ax. exact (U_XaddrW E 25 ai ax). Qed.
Definition s3_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 9 0) (SOff 10 0), SOff 32 0); (SAlu ALU_ADD (SOff 8 0) (SOff 10 0), SOff 33 0) ].
Definition s3_stk : list YQ0b.chunk :=
[mkChunk 96 (CVal 8 (SOff 36 0)); mkChunk 104 (CVal 8 (SOff 37 0)); mkChunk 112 (CVal 8 (SOff 38 0)); mkChunk 120 (CVal 8 (SOff 39 0))].
Definition s3_atoms : list (nat * afact) :=
[ (2%nat, mkAF CEIL_MIN (2^63) 4); (10%nat, mkAF 0 (2^32 - 1) 0);
(21%nat, mkAF (2^64 - 1 - CEIL_MAX) (2^64 - 1 - 4096) 0); (23%nat, mkAF (2^64 - 1 - CEIL_MAX) (2^64 - 1 - 4096) 0);
(32%nat, mkAF 4096 (CEIL_MAX - 1) 0); (33%nat, mkAF 4096 (CEIL_MAX - 1) 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0) ].
Definition ss_s3l : sstate :=
mkSS FL_S3L sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 96 128 96 96 s3_stk ;
YQ0b.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))] ;
YQ0b.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))] ] None
(mkFacts s3_atoms [] s3_alias).
Definition S3L_KEPT : list reg := [2; 3; 4; 8; 9; 18; 21; 23; 24; 27]%bv.
Lemma U_dec16 : forall E a w, U E a = w -> 1 <= w < 2 ^ 16 ->
U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL a (SLit 48)) (SLit (-281474976710656))) (SLit 48)) = w - 1.
Proof.
intros E a w Ha Hw.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite Ha, !U_SLit. change (Z.land (zcanon 48) 63) with 48.
rewrite Z.shiftl_mul_pow2 by lia.
assert (Hin : zcanon (zcanon (w * 2 ^ 48) + zcanon (-281474976710656)) = (w - 1) * 2 ^ 48).
{ unfold zcanon, M64. rewrite <- Zplus_mod.
replace (w * 2 ^ 48 + -281474976710656) with ((w - 1) * 2 ^ 48) by ring. apply Z.mod_small. lia. }
rewrite Hin. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Section e.
Variables (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis HC : dctx mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef.
Let CMP := CMPp mem0 fimg bimg cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef.
Definition s3l_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (top c0 : Z) (c' : config) : Prop :=
exists regs' mem' left,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_S4L) mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall z, mem' z = memc z) /\
0 <= left <= c0 /\ getr regs' 26 = Z_to_bv 64 left /\ getr regs' 25 = Z_to_bv 64 (W - 1) /\
getr regs' 20 = Z_to_bv 64 top /\ getr regs' 19 = Z_to_bv 64 65535 /\ getr regs' 10 = Z_to_bv 64 (top * W + (W - 1)) /\
(forall r : reg, In r S3L_KEPT -> getr regs' r = getr regs r).
Lemma fl_s3l : forall (n : nat) (i x : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top h c0 : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
0 <= top -> 1 <= h -> top + h <= H -> 0 <= c0 < W -> CMP (top * W + c0) <> 0 ->
top <= i < top + h -> 0 <= x -> (x < c0 \/ (x = c0 /\ i = top)) ->
(c0 - x) * h + (top + h - 1 - i) < Z.of_nat n ->
word_mem ubs2segs memc (spv + 96) top ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 8 = Z_to_bv 64 bimg -> getr regs 9 = Z_to_bv 64 fimg -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 21 = Z_to_bv 64 (2 ^ 64 - 1 - fimg) -> getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - bimg) ->
getr regs 22 = Z_to_bv 64 i -> getr regs 26 = Z_to_bv 64 x -> getr regs 10 = Z_to_bv 64 (i * W + x) ->
getr regs 19 = Z_to_bv 64 65535 -> getr regs 24 = Z_to_bv 64 (top + h) -> getr regs 20 = Z_to_bv 64 (top * W) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 FL_S3L) memc (seg_rom ubs2segs)) mdc) (s3l_post STK sp0 FP L A mem md Lc Ac mdc regs memc top c0).
Proof.
intros n. induction n as [|n IH]; intros i x STK sp0 FP L A mem md Lc Ac mdc regs memc top h c0 HJ K0 Hfi Hbi Ht0 Hh Hth Hc0 Hwit Hi Hx0 Hinv Hfuel W96
G2 G8 G9 G18 G21 G23 G22 G26 G10 G19 G24 G20; [exfalso; clear - Hfuel Hinv Hi Hh Hc0 Hx0; nia|].
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
destruct (dctx_objs mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC memc K0)
as (_ & _ & _ & _ & _ & WHm & WWm & WGm & WCm).
assert (Hxc : x <= c0) by (clear - Hinv; lia).
assert (HxW : x < W) by (clear - Hxc Hc0; lia).
assert (Hi1 : i + 1 <= H) by (clear - Hi Hth; lia).
assert (Htp : top + 1 <= H) by (clear - Hh Hth; lia).
assert (Hp : 0 <= i * W + x /\ i * W + x + 1 <= N) by (rewrite HN; clear - Hi Hx0 HxW Hi1 Ht0 HW; nia).
assert (RFA : top * W + (W - 1) < N) by (rewrite HN; clear - Htp Ht0 HW; nia).
set (p := i * W + x) in *. assert (Hpdef : p = i * W + x) by reflexivity. clearbody p.
assert (Hp32 : p < 2 ^ 32) by (clear - Hp HNle; lia). assert (HN32 : N <= 2 ^ 32) by (clear - HNle; lia).
set (bc := byte_at memc (fimg + p)). set (bb := byte_at memc (bimg + p)).
pose proof (byte_at_range memc (fimg + p)) as Rbc. pose proof (byte_at_range memc (bimg + p)) as Rbb. fold bc in Rbc. fold bb in Rbb.
set (E := Ereg regs (map (Z_to_bv 64) [fimg + p; bimg + p; bc; bb; top; W; g; cfp] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HA : forall j v, nth_error [fimg + p; bimg + p; bc; bb; top; W; g; cfp] j = Some v -> ew E (32 + j) = Z_to_bv 64 v)
by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HE32 : ew E 32 = Z_to_bv 64 (fimg + p)) by (apply (HA 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 (bimg + p)) by (apply (HA 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 bc) by (apply (HA 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 bb) by (apply (HA 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 top) by (apply (HA 4%nat); reflexivity).
assert (HE37 : ew E 37 = Z_to_bv 64 W) by (apply (HA 5%nat); reflexivity).
assert (HE38 : ew E 38 = Z_to_bv 64 g) by (apply (HA 6%nat); reflexivity).
assert (HE39 : ew E 39 = Z_to_bv 64 cfp) by (apply (HA 7%nat); reflexivity).
assert (UR : forall (r : reg) (k : nat) v, Z.of_nat k = bv_unsigned r -> getr regs r = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff k 0) = v)
by (intros r k v Hk Hg Hv; apply U_atom; [rewrite (HE k r Hk); exact Hg | exact Hv]).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HU32 : bv_unsigned (ew E 32) = fimg + p) by (rewrite HE32; apply unsigned_lit_small; clear - Hp Hfimg0 Hfimg1 Hac; lia).
assert (HU33 : bv_unsigned (ew E 33) = bimg + p) by (rewrite HE33; apply unsigned_lit_small; clear - Hp Hbimg0 Hbimg1 Hac; lia).
assert (HFA : facts_ok E (mkFacts s3_atoms [] s3_alias)).
{ split; [| split; [exact I|]].
- unfold s3_atoms. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU32, HU33, HE34, HE35, (HE 10%nat 10%bv eq_refl), (HE 21%nat 21%bv eq_refl), (HE 23%nat 23%bv eq_refl), G10, G21, G23.
clear - Hsp0 Hsp1 Hsp16 Hp Hp32 Hfimg0 Hfimg1 Hbimg0 Hbimg1 Rbc Rbb Hac. rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- unfold s3_alias. cbn [f_alias alias_ok].
split; [| split; [| exact I]].
+ rewrite (denot_of_U' E (SOff 32 0) (fimg + p)) by (apply U_atom; [exact HE32 | clear - Hp Hfimg0 Hfimg1 Hac; lia]).
apply denot_of_U'. rewrite (U_add_small E _ _ fimg p); [reflexivity | apply (UR 9%bv); [reflexivity | exact G9 | clear - Hfimg0 Hfimg1 Hp Hac; lia]
| apply (UR 10%bv); [reflexivity | exact G10 | clear - Hp Hp32; lia] | clear - Hfimg0; lia | clear - Hp; lia | clear - Hp Hfimg1 Hac; lia].
+ rewrite (denot_of_U' E (SOff 33 0) (bimg + p)) by (apply U_atom; [exact HE33 | clear - Hp Hbimg0 Hbimg1 Hac; lia]).
apply denot_of_U'. rewrite (U_add_small E _ _ bimg p); [reflexivity | apply (UR 8%bv); [reflexivity | exact G8 | clear - Hbimg0 Hbimg1 Hp Hac; lia]
| apply (UR 10%bv); [reflexivity | exact G10 | clear - Hp Hp32; lia] | clear - Hbimg0; lia | clear - Hp; lia | clear - Hp Hbimg1 Hac; lia]. }
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 96 128 96 96 s3_stk)).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|]. split; [intros o Ho; lia|].
unfold s3_stk. constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, HE36, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Ht0 Hh Hth HH; lia | cbn; lia | apply val_mem_word_mem; exact W96].
- eapply (chunk_ok_val _ _ _ _ _ _ _ W); [cbn [sv_denot]; rewrite Z.add_0_r, HE37, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - HW; lia | cbn; lia | apply val_mem_word_mem; exact WWm].
- eapply (chunk_ok_val _ _ _ _ _ _ _ g); [cbn [sv_denot]; rewrite Z.add_0_r, HE38, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - G0 G1 Hac; unfold CGIF_SIZE in G1; lia | cbn; lia | apply val_mem_word_mem; exact WGm].
- eapply (chunk_ok_val _ _ _ _ _ _ _ cfp); [cbn [sv_denot]; rewrite Z.add_0_r, HE39, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - C0 C1 Hac; lia | cbn; lia | apply val_mem_word_mem; exact WCm]. }
assert (HR1 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 32%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 34 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU32.
split; [lia|]. split; [clear - Hp Hfimg1 Hac; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bc); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc fimg N p HHc Hfi ltac:(clear - Hp; lia))). }
assert (HR2 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 33%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU33.
split; [lia|]. split; [clear - Hp Hbimg1 Hac; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bb); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc bimg N p HHc Hbi ltac:(clear - Hp; lia))). }
assert (HPD : pairwise_disjoint E (ss_mem ss_s3l)).
{ cbn [ss_mem ss_s3l pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU32, HU33.
repeat split; try exact I; clear - Dfb Hp Hsp0 Hfimg0 Hfimg1 Hbimg0 Hbimg1 Hac; lia. }
assert (HS : st_ok ubs2segs E ss_s3l (mkst regs (Z_to_bv 64 FL_S3L) memc (seg_rom ubs2segs))).
{ unfold ss_s3l. subst E. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | exact HPD | exact HFA].
constructor; [exact HR0 | constructor; [exact HR1 | constructor; [exact HR2 | constructor]]]. }
clear HR0 HR1 HR2 HPD HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S3L) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_cmpPixel.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ha0. rewrite HE38 in Ha0.
jreg HS (11%bv:reg) as Ha1. rewrite HE39 in Ha1.
jreg HS (12%bv:reg) as Ha2. rewrite (HE 18%nat 18%bv eq_refl), G18 in Ha2.
jreg HS (13%bv:reg) as Ha3. rewrite HE34 in Ha3. jreg HS (14%bv:reg) as Ha4. rewrite HE35 in Ha4.
jreg HS (1%bv:reg) as Hra.
cbn [ms_mem mkst] in HF.
assert (K1 : forall z, ms_mem ms z = memc z).
{ intros z. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
assert (Hbq : forall a, byte_at (ms_mem ms) a = byte_at memc a) by (intros a; unfold byte_at; rewrite (mbyte_of_eq _ _ _ _ K1); reflexivity).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc ss_s3l].
eapply SR_bind.
{ apply (cmp_callD API IMG mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef HC
STK sp0 FP L A mem md Lc Ac mdc (ms_regs ms) (ms_mem ms) p FL_S3R HJ (KD_eq _ _ _ _ K0 K1) ltac:(clear - Hp; lia) Ha0 Ha1 Ha2).
- rewrite Hbq. exact Ha3.
- rewrite Hbq. exact Ha4.
- rewrite Hra. apply (ret_ok_even (Z_to_bv 64 FL_S3R)). vm_compute. reflexivity. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hmem2 & Hres & Hfr2). clear HJ.
assert (K2 : forall z, mem2 z = memc z) by (intros z; rewrite Hmem2; apply K1).
jafter_stretch_keep HS 40%nat regs2 mem2 CMP_CLOB FL_S3R [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]];
(eapply (region_kept_out ubs2segs _ _ _ _ 0 0); [intros z _; apply Hmem2 | apply mem_grows_of_eq; exact Hmem2
| cbn [r_base r_lo base_val]; rewrite ?HU2, ?HU32, ?HU33; clear - Hsp0 Hp Hfimg0 Hbimg0 Hac; lia
| cbn [r_base r_hi base_val]; rewrite ?HU2, ?HU32, ?HU33; clear - Hsp1 Hp Hfimg1 Hbimg1 Hac; lia
| intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 FL_S3R) mem2 (seg_rom ubs2segs))) in HJ2.
set (E2 := havoc E 40 (map (getr regs2) CMP_CLOB)) in HS.
assert (EA1 : env_agree 32 E E2) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (U19 : U E2 (SOff 19 0) = 65535) by (apply U_atom; [subst E2; ew_havocA; rewrite (HE 19%nat 19%bv eq_refl); exact G19 | lia]).
assert (U20 : U E2 (SOff 20 0) = top * W)
by (apply U_atom; [subst E2; ew_havocA; rewrite (HE 20%nat 20%bv eq_refl); exact G20 | clear - RFA HNle Ht0 HW; nia]).
assert (U21 : U E2 (SOff 21 0) = 2 ^ 64 - 1 - fimg)
by (apply U_atom; [subst E2; ew_havocA; rewrite (HE 21%nat 21%bv eq_refl); exact G21 | clear - Hfimg0 Hfimg1 Hp Hac; lia]).
assert (U22 : U E2 (SOff 22 1) = i + 1)
by (apply U_atom_off; [subst E2; ew_havocA; rewrite (HE 22%nat 22%bv eq_refl); exact G22 | clear - Hi Ht0 Hth HH Hh; lia | clear - Hi Ht0 Hth HH Hh; lia]).
assert (U24 : U E2 (SOff 24 0) = top + h) by (apply U_atom; [subst E2; ew_havocA; rewrite (HE 24%nat 24%bv eq_refl); exact G24 | clear - Ht0 Hth HH Hh; lia]).
assert (U26 : U E2 (SOff 26 0) = x) by (apply U_atom; [subst E2; ew_havocA; rewrite (HE 26%nat 26%bv eq_refl); exact G26 | clear - Hx0 HxW HW; lia]).
assert (U36 : U E2 (SOff 36 0) = top) by (apply U_atom; [subst E2; ew_havocA; exact HE36 | clear - Ht0 Hth HH Hh; lia]).
assert (U37 : U E2 (SOff 37 0) = W) by (apply U_atom; [subst E2; ew_havocA; exact HE37 | clear - HW; lia]).
jbranch ubs2tbl HS.
-
clear Hc.
assert (U37m : U E2 (SOff 37 (-1)) = W - 1).
{ rewrite (U_atom_off E2 37 W (-1)); [clear; lia | subst E2; ew_havocA; exact HE37 | clear - HW; lia | clear - HW; lia]. }
assert (UFA : U E2 (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SOff 20 0) (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 37 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48))) (SLit 32)) (SLit 32))
= top * W + (W - 1)).
{ rewrite U_zext32_mod.
rewrite (U_add_small E2 _ _ (top * W) (W - 1)); [apply Z.mod_small; clear - RFA HN32 Ht0 HW; nia | exact U20 | | clear - Ht0 HW; nia | clear - HW; lia | clear - RFA HN32; lia].
apply U_dec16; [exact U37 | clear - HW; lia]. }
jrun_to LAWS ubs2tbl_ok HS HJ2 FL_S4L.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
assert (K3 : forall z, m2 z = memc z) by (intros z; rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF z); apply K2) end.
clear HF HG.
jbranch ubs2tbl HS; [exfalso; rewrite branch_ltu_U, U21, UFA in Hc; apply Z.ltb_lt in Hc; clear - Hc RFA HN32 Hfimg0 Hfimg1 Hac; lia |].
jrun_to LAWS ubs2tbl_ok HS HJ2 FL_S4L.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
assert (K3b : forall z, m2 z = memc z) by (intros z; rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF z); apply K3) end.
clear HF HG.
apply SR_ret. lazymatch type of HS with st_ok _ _ _ ?msf => exists (ms_regs msf), (ms_mem msf), x end.
split; [rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl); reflexivity|]. split; [exact HJ2|]. split; [exact K3b|]. split; [clear - Hx0 Hxc; lia|].
split; [lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs2segs Ec ssc msc 26%bv HS) end; eval_sr_get; apply denot_of_U'; exact U26|].
split; [lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs2segs Ec ssc msc 25%bv HS) end; eval_sr_get; apply denot_of_U'; exact U37m|].
split; [lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs2segs Ec ssc msc 20%bv HS) end; eval_sr_get; apply denot_of_U'; exact U36|].
split; [reg_nowF HS ltac:(reflexivity)|].
split; [lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs2segs Ec ssc msc 10%bv HS) end; eval_sr_get; apply denot_of_U'; exact UFA|].
intros rr Hrr; subst E E2; lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf => exact (regs_kept_of_st_ok ubs2segs Ef ssf msf regs _ S3L_KEPT HS EA1 ltac:(vm_compute; reflexivity) rr Hrr) end.
-
assert (Hz : CMP p = 0).
{ destruct (Z.eq_dec (CMP p) 0) as [Hz|Hnz]; [exact Hz | exfalso].
rewrite branch_ne_U, U_lit, U_SOff in Hc by (clear; lia). subst E2. change 42%nat with (40 + 2)%nat in Hc.
rewrite (ew_havoc_new E 40 (map (getr regs2) CMP_CLOB) 2 (Z_to_bv 64 0)) in Hc by (cbn; lia). cbn [nth map CMP_CLOB] in Hc. rewrite Hres, Z_to_bv_unsigned in Hc.
pose proof (cmpPixel_fn_range cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef (byte_at mem0 (fimg + p)) (byte_at mem0 (bimg + p))) as Rr.
pose proof (wrap64_nz _ Rr Hnz) as X. destruct (Z.eqb_spec (zcanon (bv_wrap 64 (CMPp mem0 fimg bimg cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef p) + 0)) 0) as [Hq|Hq]; [exact (X Hq) | discriminate Hc]. }
clear Hc.
assert (Hxlt : x < c0) by (destruct Hinv as [Hl | [Hxe Hie]]; [exact Hl | exfalso; apply Hwit; rewrite <- Hxe, <- Hie, <- Hpdef; exact Hz]).
jrun LAWS ubs2tbl_ok HS HJ2.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
assert (K3 : forall z, m2 z = memc z) by (intros z; rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF z); apply K2) end.
clear HF HG.
assert (UAND : forall a v, U E2 a = v -> 0 <= v < 65536 -> U E2 (SAlu ALU_AND a (SOff 19 0)) = v).
{ intros a v Ha Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, U19, land_ffff by exact Hv. apply zcanon_id. unfold M64. lia. }
assert (UA : U E2 (SAlu ALU_AND (SOff 22 1) (SOff 19 0)) = i + 1) by (apply UAND; [exact U22 | clear - Hi Ht0 Hth HH Hh; lia]).
assert (UX : U E2 (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 22 1) (SOff 19 0)) (SOff 24 0)) (SLit 1)) = if i + 1 <? top + h then 0 else 1)
by (rewrite U_xor1_sltu, UA, U24; reflexivity).
assert (UADDR : forall row row' x', U E2 row = row' -> 0 <= row' < 65536 -> forall s, U E2 s = x' -> 0 <= x' < W -> row' * W + x' < 2 ^ 32 ->
U E2 (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SMd M_MUL (SAlu ALU_AND row (SOff 19 0)) (SOff 37 0)) (SAlu ALU_AND s (SOff 19 0))) (SLit 32)) (SLit 32))
= row' * W + x').
{ intros row row' x' Hrow Rrow s Hs Rs Rsum. rewrite U_zext32_mod.
rewrite (U_add_small E2 _ _ (row' * W) x'); [apply Z.mod_small; clear - Rrow Rs Rsum HW; nia | | | clear - Rrow HW; nia | clear - Rs; lia | clear - Rsum Rs; lia].
- apply (U_mul_small' E2 _ _ row' W); [apply UAND; [exact Hrow | exact Rrow] | exact U37 | clear - Rrow; lia | clear - HW; lia | clear - Rrow HW; nia].
- apply UAND; [exact Hs | clear - Rs HW; lia]. }
jbranch ubs2tbl HS.
+
rewrite branch_geu_U, UA, U24 in Hc.
assert (Hwrap : i + 1 = top + h) by (destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [discriminate Hc | clear - Hl Hi; lia]). clear Hc.
assert (US : U E2 (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 22 1) (SOff 19 0)) (SOff 24 0)) (SLit 1))) = x + 1).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U26, UX. destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [clear - Hl Hwrap; lia|].
apply zcanon_id. unfold M64. clear - Hxlt Hc0 Hx0 HW; lia. }
assert (Rsum : top * W + (x + 1) < 2 ^ 32) by (clear - RFA HN32 Hxlt Hc0; nia).
pose proof (UADDR _ _ (x + 1) U36 ltac:(clear - Ht0 Hth HH Hh; lia) _ US ltac:(clear - Hxlt Hc0 Hx0; lia) Rsum) as UAD.
jrun LAWS ubs2tbl_ok HS HJ2.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
assert (K3b : forall z, m2 z = memc z) by (intros z; rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF z); apply K3) end.
clear HF HG.
jbranch ubs2tbl HS; [exfalso; rewrite branch_ltu_U, U21, UAD in Hc; apply Z.ltb_lt in Hc; clear - Hc Rsum Hfimg0 Hfimg1 Hp Hac; lia |].
jrun_to LAWS ubs2tbl_ok HS HJ2 FL_S3L.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
assert (K4 : forall z, m2 z = memc z) by (intros z; rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF z); apply K3b);
assert (W96' : word_mem ubs2segs m2 (spv + 96) top) by (intros k Hk; rewrite (mbyte_of_eq _ _ _ _ K4); exact (W96 k Hk)) end.
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs _ (19%bv :: 20%bv :: S3L_KEPT) HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH top (x + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ2 (KD_eq _ _ _ _ K0 K4) Hfi Hbi Ht0 Hh Hth Hc0 Hwit
ltac:(clear - Hh Ht0; lia) ltac:(clear - Hx0; lia) ltac:(clear - Hxlt; lia) ltac:(clear - Hfuel Hwrap Hxlt Hh; nia) W96').
- rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2.
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- rewrite (HKR 21%bv ltac:(cbv; auto 20)). exact G21.
- rewrite (HKR 23%bv ltac:(cbv; auto 20)). exact G23.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs2segs Ec ssc msc 22%bv HS) end. eval_sr_get.
apply denot_of_U'. exact U36.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs2segs Ec ssc msc 26%bv HS) end. eval_sr_get.
apply denot_of_U'. exact US.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs2segs Ec ssc msc 10%bv HS) end. eval_sr_get.
apply denot_of_U'. exact UAD.
- rewrite (HKR 19%bv ltac:(cbv; auto 20)). exact G19.
- rewrite (HKR 24%bv ltac:(cbv; auto 20)). exact G24.
- rewrite (HKR 20%bv ltac:(cbv; auto 20)). exact G20. }
cbv beta. intros c' (regs' & mem' & left & -> & HJ' & K' & Hl & Q26 & Q25 & Q20 & Q19 & Q10 & HK'). exists regs', mem', left.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K4|]. split; [exact Hl|]. split; [exact Q26|]. split; [exact Q25|].
split; [exact Q20|]. split; [exact Q19|]. split; [exact Q10|].
intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr (or_intror (or_intror Hrr))).
+
rewrite branch_geu_U, UA, U24 in Hc.
assert (Hdown : i + 1 < top + h) by (destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [exact Hl | discriminate Hc]). clear Hc.
assert (US : U E2 (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 22 1) (SOff 19 0)) (SOff 24 0)) (SLit 1))) = x).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U26, UX. destruct (Z.ltb_spec (i + 1) (top + h)) as [Hl|Hl]; [|clear - Hl Hdown; lia].
rewrite Z.add_0_r. apply zcanon_id. unfold M64. clear - Hx0 HxW HW; lia. }
assert (HiH : i + 2 <= H) by (clear - Hdown Hth; lia).
assert (HiN : (i + 1) * W + x < N) by (rewrite HN; clear - HiH HxW Hx0 HW Hi Ht0; nia).
assert (Rsum : (i + 1) * W + x < 2 ^ 32) by (clear - HiN HN32; lia).
pose proof (UADDR _ _ x U22 ltac:(clear - Hi Ht0 Hth HH Hh; lia) _ US ltac:(clear - Hx0 HxW; lia) Rsum) as UAD.
jrun LAWS ubs2tbl_ok HS HJ2.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
assert (K3b : forall z, m2 z = memc z) by (intros z; rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF z); apply K3) end.
clear HF HG.
jbranch ubs2tbl HS; [exfalso; rewrite branch_ltu_U, U21, UAD in Hc; apply Z.ltb_lt in Hc; clear - Hc Rsum Hfimg0 Hfimg1 Hp Hac; lia |].
jrun_to LAWS ubs2tbl_ok HS HJ2 FL_S3L.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
assert (K4 : forall z, m2 z = memc z) by (intros z; rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF z); apply K3b);
assert (W96' : word_mem ubs2segs m2 (spv + 96) top) by (intros k Hk; rewrite (mbyte_of_eq _ _ _ _ K4); exact (W96 k Hk)) end.
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs _ (19%bv :: 20%bv :: S3L_KEPT) HS ltac:(subst E E2; exact EA1) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 1) x STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ2 (KD_eq _ _ _ _ K0 K4) Hfi Hbi Ht0 Hh Hth Hc0 Hwit
ltac:(clear - Hi Hdown; lia) Hx0 ltac:(left; exact Hxlt) ltac:(clear - Hfuel Hdown Hxlt Hh Hi; nia) W96').
- rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2.
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- rewrite (HKR 21%bv ltac:(cbv; auto 20)). exact G21.
- rewrite (HKR 23%bv ltac:(cbv; auto 20)). exact G23.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs2segs Ec ssc msc 22%bv HS) end. eval_sr_get.
apply denot_of_U'. exact U22.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs2segs Ec ssc msc 26%bv HS) end. eval_sr_get.
apply denot_of_U'. exact US.
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => rewrite (st_ok_reg ubs2segs Ec ssc msc 10%bv HS) end. eval_sr_get.
apply denot_of_U'. exact UAD.
- rewrite (HKR 19%bv ltac:(cbv; auto 20)). exact G19.
- rewrite (HKR 24%bv ltac:(cbv; auto 20)). exact G24.
- rewrite (HKR 20%bv ltac:(cbv; auto 20)). exact G20. }
cbv beta. intros c' (regs' & mem' & left & -> & HJ' & K' & Hl & Q26 & Q25 & Q20 & Q19 & Q10 & HK'). exists regs', mem', left.
split; [reflexivity|]. split; [exact HJ'|]. split; [intros z; rewrite K'; apply K4|]. split; [exact Hl|]. split; [exact Q26|]. split; [exact Q25|].
split; [exact Q20|]. split; [exact Q19|]. split; [exact Q10|].
intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr (or_intror (or_intror Hrr))).
Qed.
Definition s3V_alias : list (sv * sv) :=
[ (SAlu ALU_SRL (SAlu ALU_SLL (SMd M_MUL (SOff 13 0) (SOff 12 0)) (SLit 32)) (SLit 32), SOff 32 0) ].
Definition s3V_atoms : list (nat * afact) :=
[ (2%nat, mkAF CEIL_MIN (2^63) 4); (21%nat, mkAF (2^64 - 1 - CEIL_MAX) (2^64 - 1 - 4096) 0); (32%nat, mkAF 0 (2^32 - 1) 0) ].
Definition ss_s3V : sstate :=
mkSS FL_S3 sr_atoms [ YQ0b.mkRegion (Some 2%nat) 64 104 64 72 [mkChunk 96 (CVal 8 (SOff 13 0))] ] None (mkFacts s3V_atoms [] s3V_alias).
Lemma U_addw_small3 : forall E a b, U E a + U E b < 2 ^ 31 -> U E (SAluw ALU_ADD a b) = U E a + U E b.
Proof.
intros E a b Hab. pose proof (U_range E a) as Ha. pose proof (U_range E b) as Hb. unfold M64 in Ha, Hb.
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite !(Z.mod_small _ (2 ^ 32)) by lia.
unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
rewrite (Z.mod_small (U E a + U E b + 2 ^ 31)) by lia. replace (U E a + U E b + 2 ^ 31 - 2 ^ 31) with (U E a + U E b) by lia.
apply Z.mod_small. lia.
Qed.
Lemma U_hgt : forall E a b t r, U E a = t -> U E b = r -> 0 <= t <= r -> r < 2 ^ 64 ->
U E (SAlu ALU_ADD (SMd M_MUL a (SLit (-1))) b) = r - t.
Proof.
intros E a b t r Ha Hb Htr Hr. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite Ha, Hb, U_SLit.
unfold zcanon, M64. rewrite Zplus_mod_idemp_l. replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
replace (t * (2 ^ 64 - 1) + r) with ((r - t) + t * 2 ^ 64) by ring. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma U_hgt48 : forall E a b t r, U E a = t -> U E b = r -> 0 <= t <= r -> r - t < 2 ^ 16 -> r < 2 ^ 16 ->
U E (SAlu ALU_SRL (SAlu ALU_ADD (SMd M_MUL a (SLit 5192296858534827628249021352509440)) (SAlu ALU_SLL b (SLit 48))) (SLit 48)) = r - t.
Proof.
intros E a b t r Ha Hb Htr Hd Hr.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite Ha, Hb, !U_SLit. change (Z.land (zcanon 48) 63) with 48.
rewrite Z.shiftl_mul_pow2 by lia.
assert (Hin : zcanon (zcanon (t * zcanon 5192296858534827628249021352509440) + zcanon (r * 2 ^ 48)) = (r - t) * 2 ^ 48).
{ unfold zcanon, M64. rewrite <- Zplus_mod.
replace (5192296858534827628249021352509440 mod 2 ^ 64) with (2 ^ 64 - 2 ^ 48) by reflexivity.
replace (t * (2 ^ 64 - 2 ^ 48) + r * 2 ^ 48) with ((r - t) * 2 ^ 48 + t * 2 ^ 64) by ring. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
rewrite Hin. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.
Definition S3_KEPT : list reg := [2; 3; 4; 8; 9; 18; 21; 23; 27]%bv.
Definition s3_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (top hrow c0 : Z) (c' : config) : Prop :=
exists regs' mem' left,
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_S4L) mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ KD mem0 spv mem' /\ word_mem ubs2segs mem' (spv + 64) (hrow + 1 - top) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 64 <= a < spv + 72) -> mbyte ubs2segs mem' a = mbyte ubs2segs memc a) /\
word_mem ubs2segs mem' (spv + 96) top /\
0 <= left <= c0 /\ getr regs' 26 = Z_to_bv 64 left /\ getr regs' 25 = Z_to_bv 64 (W - 1) /\
getr regs' 20 = Z_to_bv 64 top /\ getr regs' 19 = Z_to_bv 64 65535 /\ getr regs' 24 = Z_to_bv 64 (hrow + 1) /\
getr regs' 10 = Z_to_bv 64 (top * W + (W - 1)) /\
(forall r : reg, In r S3_KEPT -> getr regs' r = getr regs r).
Lemma fl_s3 : forall STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc (top hrow c0 : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KD mem0 spv memc ->
In (fimg, N) (blocks Lc Ac) -> In (bimg, N) (blocks Lc Ac) ->
spv = sp0 - 272 -> 272 <= STK -> 0 <= top <= hrow -> hrow < H -> 0 <= c0 < W -> CMP (top * W + c0) <> 0 ->
word_mem ubs2segs memc (spv + 96) top ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 8 = Z_to_bv 64 bimg -> getr regs 9 = Z_to_bv 64 fimg -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 21 = Z_to_bv 64 (2 ^ 64 - 1 - fimg) -> getr regs 23 = Z_to_bv 64 (2 ^ 64 - 1 - bimg) ->
getr regs 12 = Z_to_bv 64 W -> getr regs 13 = Z_to_bv 64 top -> getr regs 26 = Z_to_bv 64 (hrow + 1) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 FL_S3) memc (seg_rom ubs2segs)) mdc) (s3_post STK sp0 FP L A mem md Lc Ac mdc regs memc top hrow c0).
Proof.
intros STK sp0 FP L A mem md Lc Ac mdc regs memc top hrow c0 HJ K0 Hfi Hbi Hspv HSTK Htop Hhr Hc0 Hwit W96 G2 G8 G9 G18 G21 G23 G12 G13 G26.
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
set (h := hrow + 1 - top).
assert (Hh : 1 <= h /\ top + h <= H /\ h <= 65535) by (subst h; clear - Htop Hhr HH; lia).
assert (HtW : 0 <= top * W /\ top * W + W <= N) by (rewrite HN; clear - Htop Hhr HW; nia).
assert (HN32 : N <= 2 ^ 32) by (clear - HNle; lia).
set (E := Ereg regs (map (Z_to_bv 64) [top * W] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (top * W)) by (subst E; apply (Ereg_vals regs [top * W] [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (U12 : U E (SOff 12 0) = W) by (apply U_atom; [rewrite (HE 12%nat 12%bv eq_refl); exact G12 | clear - HW; lia]).
assert (U13 : U E (SOff 13 0) = top) by (apply U_atom; [rewrite (HE 13%nat 13%bv eq_refl); exact G13 | clear - Htop Hhr HH; lia]).
assert (U26 : U E (SOff 26 0) = hrow + 1) by (apply U_atom; [rewrite (HE 26%nat 26%bv eq_refl); exact G26 | clear - Htop Hhr HH; lia]).
assert (Hstw : forall a, spv + 64 <= a < spv + 72 -> writable_at ubs2segs memc a).
{ intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hw) & _). apply Hw. clear - Ha Hspv HSTK. lia. }
assert (HR : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 64 104 64 72 [mkChunk 96 (CVal 8 (SOff 13 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [clear - Hsp0 Hac; lia|]. split; [clear - Hsp1; lia|]. split; [intros o Ho; apply Hstw; lia|]. constructor; [|constructor].
eapply (chunk_ok_val _ _ _ _ _ _ _ top); [cbn [sv_denot]; rewrite Z.add_0_r, (HE 13%nat 13%bv eq_refl), G13, Z_to_bv_bv_unsigned; reflexivity | cbn; clear - Htop Hhr HH; lia | cbn; lia | apply val_mem_word_mem; exact W96]. }
assert (HFA : facts_ok E (mkFacts s3V_atoms [] s3V_alias)).
{ split; [| split; [exact I|]].
- unfold s3V_atoms. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HE32, (HE 21%nat 21%bv eq_refl), G21.
clear - Hsp0 Hsp1 Hsp16 HtW HN32 HW Hfimg0 Hfimg1 Hac Hh Htop. rewrite !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- unfold s3V_alias. cbn [f_alias alias_ok]. split; [| exact I].
rewrite (denot_of_U' E (SOff 32 0) (top * W)) by (apply U_atom; [exact HE32 | clear - HtW HN32 HW; lia]).
apply denot_of_U'. rewrite U_zext32_mod, (U_mul_small' E _ _ top W U13 U12) by (clear - HtW HN32 Htop Hhr HW; nia).
apply Z.mod_small. clear - HtW HN32 Htop Hhr HW; nia. }
assert (HS : st_ok ubs2segs E ss_s3V (mkst regs (Z_to_bv 64 FL_S3) memc (seg_rom ubs2segs))).
{ unfold ss_s3V. subst E. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [exact HR | constructor]
| cbn [pairwise_disjoint all_disjoint]; split; exact I | exact HFA]. }
clear HR HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_S3) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ FL_S3L.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; clear - Hspv HSTK; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 64 <= a < spv + 72) -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha Hna. apply (mbyte_of_frame _ _ _ _ a HF Ha). intros r Hr. cbv [In] in Hr.
destruct Hr as [<- | []]; cbn [r_base r_wlo r_whi base_val]; rewrite HU2; clear - Hna; lia. }
assert (K1 : KD mem0 spv (ms_mem ms)) by (apply (KD_frame _ _ _ _ K0); intros a Ha Hna1 Hna2 Hna3 Hna4; apply KF; [exact Ha | clear - Hna3; lia]).
clear HF HG.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (st_region_chunks ubs2segs E ssx msx 0 _ 2%nat spv HS eq_refl eq_refl HU2) as Hcs;
pose proof (regs_kept_of_st_ok ubs2segs E ssx msx regs _ S3_KEPT HS ltac:(subst E; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HKR;
assert (RG : forall (r : reg) nn wv, sr_get (ss_regs ssx) r = SOff nn 0 -> ew E nn = wv -> getr (ms_regs msx) r = wv)
by (intros r nn wv Hr Hvv; rewrite (st_ok_reg ubs2segs E ssx msx r HS), Hr; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hvv);
assert (RGX : forall (r : reg) sv, sr_get (ss_regs ssx) r = sv -> getr (ms_regs msx) r = sv_denot E sv)
by (intros r sv Hr; rewrite (st_ok_reg ubs2segs E ssx msx r HS), Hr; reflexivity) end.
cbn [r_chunks] in Hcs.
assert (W64 : word_mem ubs2segs (ms_mem ms) (spv + 64) h).
{ apply (chunk_word E _ _ 64 _ _ (proj1 (Forall_forall _ _) Hcs (mkChunk 64 (CVal 8 (SAlu ALU_ADD (SMd M_MUL (SOff 13 0) (SLit (-1))) (SOff 26 0)))) ltac:(cbn [In]; tauto)));
[apply denot_of_U'; rewrite (U_hgt E _ _ top (hrow + 1) U13 U26) by (clear - Htop Hhr HH; lia); reflexivity | clear - Hh; lia]. }
assert (W96' : word_mem ubs2segs (ms_mem ms) (spv + 96) top).
{ apply (chunk_word E _ _ 96 _ _ (proj1 (Forall_forall _ _) Hcs (mkChunk 96 (CVal 8 (SOff 13 0))) ltac:(cbn [In]; tauto)));
[cbn [sv_denot]; rewrite Z.add_0_r, (HE 13%nat 13%bv eq_refl), G13, Z_to_bv_bv_unsigned; reflexivity | clear - Htop Hhr HH; lia]. }
clear Hcs.
assert (Q24 : getr (ms_regs ms) 24 = Z_to_bv 64 (top + h)).
{ rewrite (RGX 24%bv _ eq_refl). eval_sr_get. apply denot_of_U'.
rewrite U_addw_small3; rewrite (U_hgt48 E _ _ top (hrow + 1) U13 U26) by (clear - Htop Hhr HH; lia); rewrite U13; subst h; clear - Htop Hhr HH; lia. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (fl_s3l (Datatypes.S (Z.to_nat (c0 * h + h))) top 0 STK sp0 FP L A mem md Lc Ac mdc _ _ top h c0 HJ K1 Hfi Hbi ltac:(clear - Htop; lia) ltac:(clear - Hh; lia) ltac:(clear - Hh; lia) Hc0 Hwit
ltac:(clear - Hh; lia) ltac:(clear; lia) ltac:(clear - Hc0; lia) ltac:(clear - Hc0 Hh; nia) W96').
- rewrite (HKR 2%bv ltac:(cbv; auto 20)). exact G2.
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 20)). exact G18.
- rewrite (HKR 21%bv ltac:(cbv; auto 20)). exact G21.
- rewrite (HKR 23%bv ltac:(cbv; auto 20)). exact G23.
- apply (RG 22%bv 13%nat _ eq_refl). rewrite (HE 13%nat 13%bv eq_refl). exact G13.
- rewrite (RGX 26%bv (SLit 0) eq_refl). reflexivity.
- rewrite Z.add_0_r. apply (RG 10%bv 32%nat _ eq_refl). exact HE32.
- rewrite (RGX 19%bv (SLit 65535) eq_refl). reflexivity.
- exact Q24.
- rewrite (RGX 20%bv _ eq_refl). eval_sr_get. apply denot_of_U'.
apply (U_mul_small' E _ _ top W U13 U12); clear - HtW HN32 Htop Hhr HW; nia. }
cbv beta. intros c' (regs' & mem' & left & -> & HJ' & K' & Hl & Q26 & Q25 & Q20 & Q19 & Q10 & HK'). exists regs', mem', left.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact (KD_eq _ _ _ _ K1 K')|].
split; [intros k Hk; rewrite (mbyte_of_eq _ _ _ _ K'); apply W64; exact Hk|].
split; [intros a Ha Hna; rewrite (mbyte_of_eq _ _ _ _ K'); exact (KF a Ha Hna)|].
split; [intros k Hk; rewrite (mbyte_of_eq _ _ _ _ K'); apply W96'; exact Hk|].
split; [exact Hl|]. split; [exact Q26|]. split; [exact Q25|]. split; [exact Q20|]. split; [exact Q19|].
split; [rewrite (HK' 24%bv ltac:(cbv; auto 20)), Q24; f_equal; subst h; clear; lia|].
split; [exact Q10|].
intros rr Hrr. rewrite (HK' rr ltac:(clear - Hrr; cbv in Hrr; cbv; intuition)). apply (HKR rr Hrr).
Qed.
End e.
End S.
End d.
