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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b
YI06 UI5b YI09 YI08 YI0r YI0o UI1w UI3p UI3m UI3t
UI3w UI4i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 YI02 UI5c UI2z YI0j YI0k YI6c YI01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ssB (lct : bool) : sstate :=
ra_ssW PC_B (sr_set sr_atoms 11%bv (if lct then SOff 9%nat 30 else SOff 8%nat 32)) 46 47 [ch37] false
[(40%nat, mkAF 0 256 0); (19%nat, mkAF 0 (2^32-1) 0)] [] [].
Definition ssIC (fs : list (nat * afact)) : sstate := ra_ssW PC_IC sr_atoms 7 46 [ch37; ch46 69] false fs [] [].
Ltac vne HE46 HE19 HE42 HEne0 cx :=
try (lazymatch goal with H : branch_taken BC_EQ (sv_denot _ (SAlu ALU_AND (SExt false 8 (SOff 46 0)) (SLit 1))) _ = _ |- _ =>
rewrite branch_eq_U, U_and_lit, U_zext, (U_atom _ 46 (c_rattr cx) HE46), U_lit in H by lia;
first [rewrite (test1m_false (c_rattr cx) ltac:(lia) H) | rewrite (test1m_true (c_rattr cx) ltac:(lia) H)] end);
try (lazymatch goal with H : branch_taken BC_EQ (sv_denot _ (SAlu ALU_AND (SOff 19 0) (SLit 1))) _ = _ |- _ =>
rewrite branch_eq_U, U_and_lit, (U_atom _ 19 (c_fattr cx) HE19), U_lit in H by lia;
first [rewrite (test1_false (c_fattr cx) H) | rewrite (test1_true (c_fattr cx) H)] end);
try (lazymatch goal with H : branch_taken BC_LTU (sv_denot _ (SOff 42 0)) _ = _ |- _ =>
rewrite branch_ltu_U, (U_atom _ 42 (c_tidx cx) HE42), (U_atom _ _ _ HEne0) in H by lia;
first [apply Z.ltb_lt in H; rewrite (proj2 (Z.leb_gt _ _) H) | apply Z.ltb_ge in H; rewrite (proj2 (Z.leb_le _ _) H)] end);
cbn [andb]; reflexivity.
Lemma lor_range64 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lor a b < 2 ^ 64.
Proof using.
intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
destruct (Z.eq_dec (Z.lor a b) 0) as [-> | Hnz]; [lia|].
apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg a b); lia|]. rewrite Z.log2_lor by lia.
apply Z.max_lub_lt.
- destruct (Z.eq_dec a 0) as [-> | NE]; [cbn; lia | apply Z.log2_lt_pow2; lia].
- destruct (Z.eq_dec b 0) as [-> | NE]; [cbn; lia | apply Z.log2_lt_pow2; lia].
Qed.
Lemma packed_chunk_byte : forall E cx cur p, fields_ok cx cur -> (c_slct cx <> 0 -> 1 <= p <= 8 /\ p = YO07.pal_pow (c_slct cx)) ->
ew E 12 = Z_to_bv 64 (if c_slct cx =? 0 then 0 else 2 ^ 64 - 128 + (p - 1)) -> ew E 19 = Z_to_bv 64 (c_fattr cx) ->
bv_unsigned (sv_denot E (SAlu ALU_OR (SOff 12 0) (SAlu ALU_SLL (SAlu ALU_AND (SOff 19 0) (SLit 2)) (SLit 5)))) mod 2 ^ (8 * Z.of_N 1) = ra_packed cx.
Proof using.
intros E cx cur p HFO Hpow HE12 HE19. pose proof HFO as (_ & _ & F2 & _ & _ & _ & _ & _ & F8 & _).
change (2 ^ (8 * Z.of_N 1)) with (2 ^ 8). rewrite <- (packed_byte_cx cx cur p HFO Hpow). f_equal.
change (U E (SAlu ALU_OR (SOff 12 0) (SAlu ALU_SLL (SAlu ALU_AND (SOff 19 0) (SLit 2)) (SLit 5))) = Z.lor (if c_slct cx =? 0 then 0 else 2 ^ 64 - 128 + (p - 1)) (Z.shiftl (Z.land (c_fattr cx) 2) 5)).
pose proof (Z_land_upper (c_fattr cx) 2 ltac:(lia)) as HL2.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_and_lit by lia.
rewrite (U_atom _ 12 _ HE12), (U_atom _ 19 _ HE19);
[| lia | destruct (Z.eqb_spec (c_slct cx) 0) as [Hz0|Hnz0]; [lia | pose proof (Hpow Hnz0); lia]].
rewrite ?U_SLit.
change (Z.land (zcanon 5) 63) with 5.
assert (Hsl : 0 <= Z.shiftl (Z.land (c_fattr cx) 2) 5 < 2 ^ 64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
rewrite (zcanon_id (Z.shiftl _ 5)) by (unfold M64; lia).
apply zcanon_id. unfold M64. apply lor_range64; [destruct (Z.eqb_spec (c_slct cx) 0) as [Hz0|Hnz0]; [lia | pose proof (Hpow Hnz0); lia] | exact Hsl].
Qed.
Lemma val2_of_bytes : forall m a v, 0 <= v < 65536 -> val_mem ubs0segs m a 1 (v mod 256) -> val_mem ubs0segs m (a + 1) 1 ((v / 256) mod 256) -> val_mem ubs0segs m a 2 v.
Proof using.
intros m a v Hv H0 H1 kk Hkk. destruct kk as [|[|kk]]; [ | | lia]; cbn [Z.of_nat].
- pose proof (H0 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X. rewrite X. f_equal. unfold le_byte.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 0) with 0. rewrite !Z.shiftr_0_r.
change (2 ^ 8) with 256. change (2 ^ 16) with 65536. rewrite (Z.mod_small v 65536), Zmod_mod by lia. rewrite Zmod_mod. reflexivity.
- pose proof (H1 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X. rewrite Z.add_0_r in X. change (Z.of_nat 1) with 1. rewrite X. f_equal. unfold le_byte.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 0) with 0. rewrite !Z.shiftr_0_r.
change (2 ^ 8) with 256. change (2 ^ 16) with 65536. rewrite (Z.mod_small v 65536), Z.shiftr_div_pow2 by lia. rewrite ?Zmod_mod. reflexivity.
Qed.
Lemma fbC_of_Cregion : forall E m fwlo fwhi xc cxx cur v7,
fields_ok cxx cur -> region_ok ubs0segs E m (YP09.mkRegion (Some 2%nat) (-16) 48 fwlo fwhi xc) -> bv_unsigned (ew E 2) = c_sp cxx ->
ew E 35 = Z_to_bv 64 (c_w cxx) -> ew E 36 = Z_to_bv 64 (c_h cxx) -> ew E 37 = Z_to_bv 64 (c_top cxx) -> ew E 38 = Z_to_bv 64 (c_left cxx) ->
ew E 69 = Z_to_bv 64 (ra_packed cxx) -> 0 <= ra_packed cxx < 256 -> v7 = ra_iclen cxx - 1 -> 0 <= v7 < 256 ->
incl [mkChunk 41 (CVal 1 (SAlu ALU_SRL (SOff 37 0) (SLit 8))); mkChunk 40 (CVal 1 (SOff 37 0));
mkChunk 39 (CVal 1 (SAlu ALU_SRL (SOff 38 0) (SLit 8))); mkChunk 38 (CVal 1 (SOff 38 0));
mkChunk 45 (CVal 1 (SAlu ALU_SRL (SOff 36 0) (SLit 8))); mkChunk 44 (CVal 1 (SOff 36 0));
mkChunk 43 (CVal 1 (SAlu ALU_SRL (SOff 35 0) (SLit 8))); mkChunk 42 (CVal 1 (SOff 35 0));
mkChunk 7 (CVal 1 (SLit v7)); mkChunk 37 (CVal 1 (SLit 44)); mkChunk 46 (CVal 1 (SOff 69 0))] xc ->
fbC m cxx.
Proof using.
intros E0 m fwlo fwhi xc cxx cur v7 HFq HR0 H2 H35 H36 H37 H38 H69 R46 Hv7 R7 Hincl.
pose proof HFq as (_ & _ & _ & Fw & Fh & Ftop & Fleft & _).
assert (B1 : forall off e v, In (mkChunk off (CVal 1 e)) xc -> bv_unsigned (sv_denot E0 e) mod 2 ^ 8 = v -> val_mem ubs0segs m (c_sp cxx + off) 1 v).
{ intros off e v Hin He. eapply (vval_mem_of_chunk_mod ubs0segs E0 m _ 2%nat (c_sp cxx) off 1%N e v HR0); [reflexivity | exact Hin | exact H2 | exact He | cbn; lia]. }
assert (IN : forall c, In c [mkChunk 41 (CVal 1 (SAlu ALU_SRL (SOff 37 0) (SLit 8))); mkChunk 40 (CVal 1 (SOff 37 0));
mkChunk 39 (CVal 1 (SAlu ALU_SRL (SOff 38 0) (SLit 8))); mkChunk 38 (CVal 1 (SOff 38 0));
mkChunk 45 (CVal 1 (SAlu ALU_SRL (SOff 36 0) (SLit 8))); mkChunk 44 (CVal 1 (SOff 36 0));
mkChunk 43 (CVal 1 (SAlu ALU_SRL (SOff 35 0) (SLit 8))); mkChunk 42 (CVal 1 (SOff 35 0));
mkChunk 7 (CVal 1 (SLit v7)); mkChunk 37 (CVal 1 (SLit 44)); mkChunk 46 (CVal 1 (SOff 69 0))] -> In c xc) by (intros c Hc; apply Hincl; exact Hc).
assert (HI16 : forall n v, ew E0 n = Z_to_bv 64 v -> 0 <= v < 65536 -> bv_unsigned (sv_denot E0 (SAlu ALU_SRL (SOff n 0) (SLit 8))) mod 2 ^ 8 = (v / 256) mod 256).
{ intros n v Hn Hv. change (U E0 (SAlu ALU_SRL (SOff n 0) (SLit 8)) mod 2 ^ 8 = (v / 256) mod 256).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E0 n v Hn) by lia. change (Z.land (zcanon 8) 63) with 8.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite zcanon_id by (unfold M64; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). reflexivity. }
unfold fbC, fb7, fb37, fb46. repeat split.
- apply (B1 7 (SLit v7)); [apply IN; cbn; tauto | cbn [sv_denot]; rewrite unsigned_lit_small by lia; rewrite <- Hv7; apply Z.mod_small; lia].
- apply (B1 37 (SLit 44)); [apply IN; cbn; tauto | reflexivity].
- apply val2_of_bytes; [lia | apply (B1 38 (SOff 38 0)); [apply IN; cbn; tauto | change (U E0 (SOff 38 0) mod 2 ^ 8 = c_left cxx mod 256); rewrite (U_atom E0 38 _ H38) by lia; reflexivity]
| replace (c_sp cxx + 38 + 1) with (c_sp cxx + 39) by lia; apply (B1 39 (SAlu ALU_SRL (SOff 38 0) (SLit 8))); [apply IN; cbn; tauto | apply (HI16 38%nat); [exact H38 | lia]]].
- apply val2_of_bytes; [lia | apply (B1 40 (SOff 37 0)); [apply IN; cbn; tauto | change (U E0 (SOff 37 0) mod 2 ^ 8 = c_top cxx mod 256); rewrite (U_atom E0 37 _ H37) by lia; reflexivity]
| replace (c_sp cxx + 40 + 1) with (c_sp cxx + 41) by lia; apply (B1 41 (SAlu ALU_SRL (SOff 37 0) (SLit 8))); [apply IN; cbn; tauto | apply (HI16 37%nat); [exact H37 | lia]]].
- apply val2_of_bytes; [lia | apply (B1 42 (SOff 35 0)); [apply IN; cbn; tauto | change (U E0 (SOff 35 0) mod 2 ^ 8 = c_w cxx mod 256); rewrite (U_atom E0 35 _ H35) by lia; reflexivity]
| replace (c_sp cxx + 42 + 1) with (c_sp cxx + 43) by lia; apply (B1 43 (SAlu ALU_SRL (SOff 35 0) (SLit 8))); [apply IN; cbn; tauto | apply (HI16 35%nat); [exact H35 | lia]]].
- apply val2_of_bytes; [lia | apply (B1 44 (SOff 36 0)); [apply IN; cbn; tauto | change (U E0 (SOff 36 0) mod 2 ^ 8 = c_h cxx mod 256); rewrite (U_atom E0 36 _ H36) by lia; reflexivity]
| replace (c_sp cxx + 44 + 1) with (c_sp cxx + 45) by lia; apply (B1 45 (SAlu ALU_SRL (SOff 36 0) (SLit 8))); [apply IN; cbn; tauto | apply (HI16 36%nat); [exact H36 | lia]]].
- apply (B1 46 (SOff 69 0)); [apply IN; cbn; tauto | change (U E0 (SOff 69 0) mod 2 ^ 8 = ra_packed cxx); rewrite (U_atom E0 69 _ H69) by lia; apply Z.mod_small; lia]. Qed.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Variables (IMGV LCTV : list Z).
Definition at_IC (cx : ra_cx) L A mem md L1 A1 md1 (regs0 : bvmap 5 word) (p : Z) (c' : config) : Prop :=
exists regs1 mem1 (ne : Z),
c' = mkCfg (mkst regs1 (Z_to_bv 64 PC_IC) mem1 (seg_rom ubs0segs)) md1 /\
journal ubs0_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 mem1 md1 /\
ra_regs regs1 cx /\ getr regs1 23 = Z_to_bv 64 (c_slct cx) /\ getr regs1 22 = Z_to_bv 64 (c_cfp cx + 30) /\
getr regs1 10 = Z_to_bv 64 (Z.land (c_fattr cx) 2) /\ getr regs1 24 = Z_to_bv 64 p /\
getr regs1 11 = Z_to_bv 64 ne /\ 0 <= ne <= 256 /\
objs_at mem1 cx (c_rcur cx) /\ frame_savedN ubs0_msyms 12 regs0 mem1 (spZ regs0) /\
ne = ra_ne cx /\ fb37 mem1 cx /\ fb46 mem1 cx.
Definition at_C (cx : ra_cx) L A mem md L1 A1 md1 (regs0 : bvmap 5 word) (p : Z) (c' : config) : Prop :=
exists regs1 mem1 (icl idl : Z),
c' = mkCfg (mkst regs1 (Z_to_bv 64 PC_C) mem1 (seg_rom ubs0segs)) md1 /\
journal ubs0_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 mem1 md1 /\
ra_regs regs1 cx /\ getr regs1 23 = Z_to_bv 64 (c_slct cx) /\ getr regs1 22 = Z_to_bv 64 (c_cfp cx + 30) /\
getr regs1 10 = Z_to_bv 64 (Z.land (c_fattr cx) 2) /\ getr regs1 24 = Z_to_bv 64 p /\
getr regs1 18 = Z_to_bv 64 icl /\ getr regs1 25 = Z_to_bv 64 idl /\ 3 <= icl <= 9 /\ 4 <= idl <= 256 /\
getr regs1 13 = Z_to_bv 64 (c_w cx) /\ getr regs1 14 = Z_to_bv 64 (c_h cx) /\
objs_at mem1 cx (c_rcur cx) /\ frame_savedN ubs0_msyms 12 regs0 mem1 (spZ regs0) /\
icl = ra_iclen cx /\ idl = 2 ^ (icl - 1) /\ fbC mem1 cx.
Lemma ra_neff :
forall cx L A mem md L1 A1 md1 (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte) (p : Z),
rcx_ok cx -> ra_origin cx regs0 ->
journal ubs0_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 mem1 md1 ->
ra_regs regs1 cx -> getr regs1 19 = Z_to_bv 64 (c_fattr cx) -> getr regs1 23 = Z_to_bv 64 (c_slct cx) ->
getr regs1 22 = Z_to_bv 64 (c_cfp cx + 30) -> getr regs1 24 = Z_to_bv 64 p ->
getr regs1 11 = Z_to_bv 64 (if c_slct cx =? 0 then c_raw cx + 32 else c_cfp cx + 30) ->
objs_at mem1 cx (c_rcur cx) -> frame_savedN ubs0_msyms 12 regs0 mem1 (spZ regs0) ->
(c_slct cx <> 0 -> 1 <= p <= 8 /\ p = YO07.pal_pow (c_slct cx)) -> fb37 mem1 cx ->
getr regs1 12 = Z_to_bv 64 (if c_slct cx =? 0 then 0 else 2 ^ 64 - 128 + (p - 1)) ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_B) mem1 (seg_rom ubs0segs)) md1)
(at_IC cx L A mem md L1 A1 md1 regs0 p).
Proof using IMG.
intros cx L A mem md L1 A1 md1 regs0 regs1 mem1 p Hcx HO HJ HR G19 G23 G22 G24 G11 Hobjs HFS Hpow HF37 G12.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof (objs_fields_ok _ _ _ Hobjs) as HFO.
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv & Hf0 & Hf1 & Hfin & Hsp47) & Hslct).
pose proof HFO as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R27).
pose proof (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hstw. cbn beta in Hstw.
pose proof (Z_land_upper (c_fattr cx) 2 ltac:(lia)) as Hil1.
remember (Ereg regs1 (ra_extra cx (c_rcur cx) [])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (E_cv regs1 cx (c_rcur cx) []) as HX. pose proof (E_rv regs1 cx (c_rcur cx) []) as HY. rewrite <- HE0 in HX, HY.
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 (c_raw cx)) by (rewrite (HE 8%nat 8%bv eq_refl); exact R8).
assert (HE9 : ew E 9 = Z_to_bv 64 (c_cfp cx)) by (rewrite (HE 9%nat 9%bv eq_refl); exact R9).
assert (HE19 : ew E 19 = Z_to_bv 64 (c_fattr cx)) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (HE23 : ew E 23 = Z_to_bv 64 (c_slct cx)) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HE22 : ew E 22 = Z_to_bv 64 (c_cfp cx + 30)) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (HE24 : ew E 24 = Z_to_bv 64 p) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (HE40 : ew E 40 = Z_to_bv 64 (c_slct cx)) by (apply (HX 8%nat); reflexivity).
assert (HE42 : ew E 42 = Z_to_bv 64 (c_tidx cx)) by (apply (HX 10%nat); reflexivity).
assert (HE49 : ew E 49 = Z_to_bv 64 (c_sgct cx)) by (apply (HY 6%nat); reflexivity).
assert (HE46 : ew E 46 = Z_to_bv 64 (c_rattr cx)) by (apply (HY 3%nat); reflexivity).
assert (HE12 : ew E 12 = Z_to_bv 64 (if c_slct cx =? 0 then 0 else 2 ^ 64 - 128 + (p - 1))) by (rewrite (HE 12%nat 12%bv eq_refl); exact G12).
assert (Hnes : forall ne0, ne0 = (if c_slct cx =? 0 then c_sgct cx else c_slct cx) ->
ra_ne cx = (if YO07.flag (c_rattr cx) 1 && YO07.flag (c_fattr cx) 1 && (ne0 <=? c_tidx cx) then c_tidx cx + 1 else ne0))
by (intros ne0 Hne0; unfold ra_ne; apply num_eff_spec; exact Hne0).
assert (MKS : forall lct : bool, (if lct then c_slct cx <> 0 else c_slct cx = 0) ->
st_ok ubs0segs E (ssB lct) (mkst regs1 (Z_to_bv 64 PC_B) mem1 (seg_rom ubs0segs))).
{ intros lct Hlct. subst E. unfold ssB.
apply (ra_st_okW cx (c_rcur cx) regs1 [] mem1 PC_B _ 46 47 false [ch37] _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |].
cbn [sv_denot]. rewrite G11. destruct lct; cbn [sv_denot]; [rewrite HE9 | rewrite HE8]; rewrite unsigned_lit_small by lia;
destruct (Z.eqb_spec (c_slct cx) 0); first [reflexivity | lia].
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor; [apply ch37_ok; exact HF37 | constructor].
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE40, HE19, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PC_B) mem1 (seg_rom ubs0segs))) in HJ.
Ltac wr HE2 := eapply ra_wr_okW; [ew_havoc; exact HE2 | lia | lia | intros _; lia | left; cbn; lia].
Ltac finish HS HJ HE HE2 HE8 HE9 HE19 HE22 HE23 HE24 Hobjs HFS Hnes ne netac ne0 HEne0 HE46 HE42 cx HFO Hpow HE12 p :=
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SR_ret;
lazymatch goal with |- at_IC _ _ _ _ _ _ _ _ _ _ (mkCfg ?msx _) => exists (ms_regs msx), (ms_mem msx), ne end;
split; [reflexivity|]; cbn [ms_regs ms_mem mkst]; split; [exact HJ|];
split; [ split; [| split; [| split; [|split; [|split]]]];
[ let Q := fresh "Q" in (jreg HS (2%bv:reg) as Q); rewrite Q, <- (Z_to_bv_bv_unsigned 64 (ew _ 2)), HE2; reflexivity
| let Q := fresh "Q" in (jreg HS (8%bv:reg) as Q); rewrite Q; exact HE8
| let Q := fresh "Q" in (jreg HS (9%bv:reg) as Q); rewrite Q; exact HE9
| let Q := fresh "Q" in (jreg HS (4%bv:reg) as Q); rewrite Q, (HE 4%nat 4%bv eq_refl); assumption
| let Q := fresh "Q" in (jreg HS (3%bv:reg) as Q); rewrite Q, (HE 3%nat 3%bv eq_refl); assumption
| let Q := fresh "Q" in (jreg HS (27%bv:reg) as Q); rewrite Q, (HE 27%nat 27%bv eq_refl); assumption ] |];
split; [let Q := fresh "Q" in (jreg HS (23%bv:reg) as Q); rewrite Q; exact HE23|];
split; [let Q := fresh "Q" in (jreg HS (22%bv:reg) as Q); rewrite Q; exact HE22|];
split; [let Q := fresh "Q" in
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
pose proof (st_ok_reg segs E1 ss1 ms1 (10%bv:reg) HS) as Q; eval_sr_get_in Q;
rewrite denot_lit_U in Q; cbn [ms_regs mkst] in Q; rewrite Q; f_equal;
rewrite U_and_lit by lia; rewrite (U_atom _ 19 _ HE19) by lia; reflexivity end|];
split; [let Q := fresh "Q" in (jreg HS (24%bv:reg) as Q); rewrite Q; exact HE24|];
split; [let Q := fresh "Q" in (jreg HS (11%bv:reg) as Q); rewrite Q; cbn [sv_denot]; netac |];
split; [lia|];
split; [ eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; mbyte_chain ltac:(fun H => rewrite ?HE2 in H)
| split; [ eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]; intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H)
|   split;
[ rewrite (Hnes ne0);
[ vne HE46 HE19 HE42 HEne0 cx
| lazymatch goal with H : c_slct cx = 0 |- _ => rewrite (proj2 (Z.eqb_eq _ _) H) | H : c_slct cx <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) H) end; reflexivity ]
| split;
[ eapply (fb_of_region _ _ _ _ _ _ _ _ 37 1%N (SLit 44) 44 (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) HE2); [cbv; tauto | reflexivity | cbn; lia | cbn; lia]
| unfold fb46; eapply (vval_mem_of_chunk_mod ubs0segs _ _ _ 2%nat (c_sp cx) 46 1%N _ (ra_packed cx) (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl));
[reflexivity | cbv; tauto | exact HE2 | apply (packed_chunk_byte _ cx (c_rcur cx) p HFO Hpow HE12 HE19) | cbn; lia] ] ] ] ].
Ltac tests HS HJ HE HE2 HE8 HE9 HE19 HE22 HE23 HE24 HE42 HE46 Hobjs HFS Hnes cx ne0 HEne0 HFO Hpow HE12 p :=
jrun_to LAWS ubs0tbl_ok HS HJ PC_IC; [wr HE2|];
jbranch ubs0tbl HS;
[ jrun_to LAWS ubs0tbl_ok HS HJ PC_IC; [wr HE2|]; finish HS HJ HE HE2 HE8 HE9 HE19 HE22 HE23 HE24 Hobjs HFS Hnes ne0 ltac:(rewrite HEne0; reflexivity) ne0 HEne0 HE46 HE42 cx HFO Hpow HE12 p
| jrun_to LAWS ubs0tbl_ok HS HJ PC_IC; [wr HE2|];
jbranch ubs0tbl HS;
[ jrun_to LAWS ubs0tbl_ok HS HJ PC_IC; [wr HE2|]; finish HS HJ HE HE2 HE8 HE9 HE19 HE22 HE23 HE24 Hobjs HFS Hnes ne0 ltac:(rewrite HEne0; reflexivity) ne0 HEne0 HE46 HE42 cx HFO Hpow HE12 p
| jrun_to LAWS ubs0tbl_ok HS HJ PC_IC; [wr HE2|];
jbranch ubs0tbl HS;
[ jrun_to LAWS ubs0tbl_ok HS HJ PC_IC; [wr HE2|]; finish HS HJ HE HE2 HE8 HE9 HE19 HE22 HE23 HE24 Hobjs HFS Hnes ne0 ltac:(rewrite HEne0; reflexivity) ne0 HEne0 HE46 HE42 cx HFO Hpow HE12 p
| jrun_to LAWS ubs0tbl_ok HS HJ PC_IC; [wr HE2|];
finish HS HJ HE HE2 HE8 HE9 HE19 HE22 HE23 HE24 Hobjs HFS Hnes (c_tidx cx + 1) ltac:(rewrite HE42, unsigned_lit_small by lia; reflexivity) ne0 HEne0 HE46 HE42 cx HFO Hpow HE12 p ] ] ].
destruct (Z.eq_dec (c_slct cx) 0) as [Hz | Hnz].
- pose proof (MKS false Hz) as HS. clear MKS.
tests HS HJ HE HE2 HE8 HE9 HE19 HE22 HE23 HE24 HE42 HE46 Hobjs HFS Hnes cx (c_sgct cx) HE49 HFO Hpow HE12 p.
- pose proof (MKS true Hnz) as HS. clear MKS.
tests HS HJ HE HE2 HE8 HE9 HE19 HE22 HE23 HE24 HE42 HE46 Hobjs HFS Hnes cx (c_slct cx) HE40 HFO Hpow HE12 p.
Qed.
Lemma ra_icl :
forall cx L A mem md L1 A1 md1 (regs0 regs1 : bvmap 5 word) (mem1 : word -> option byte) (p ne : Z),
rcx_ok cx -> ra_origin cx regs0 ->
journal ubs0_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L1 A1 mem1 md1 ->
ra_regs regs1 cx -> getr regs1 23 = Z_to_bv 64 (c_slct cx) -> getr regs1 22 = Z_to_bv 64 (c_cfp cx + 30) ->
getr regs1 10 = Z_to_bv 64 (Z.land (c_fattr cx) 2) -> getr regs1 24 = Z_to_bv 64 p ->
getr regs1 11 = Z_to_bv 64 ne -> 0 <= ne <= 256 ->
objs_at mem1 cx (c_rcur cx) -> frame_savedN ubs0_msyms 12 regs0 mem1 (spZ regs0) ->
ne = ra_ne cx -> fb37 mem1 cx -> fb46 mem1 cx ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_IC) mem1 (seg_rom ubs0segs)) md1)
(at_C cx L A mem md L1 A1 md1 regs0 p).
Proof using IMG.
intros cx L A mem md L1 A1 md1 regs0 regs1 mem1 p ne Hcx HO HJ HR G23 G22 G10 G24 G11 Hne Hobjs HFS HneV HF37 HF46.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof (objs_fields_ok _ _ _ Hobjs) as HFO.
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv & Hf0 & Hf1 & Hfin & Hsp47) & Hslct).
pose proof HFO as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R27).
pose proof (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hstw. cbn beta in Hstw.
pose proof (Z_land_upper (c_fattr cx) 2 ltac:(lia)) as Hil1.
remember (Ereg regs1 (ra_extra cx (c_rcur cx) [ra_packed cx])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (E_cv regs1 cx (c_rcur cx) [ra_packed cx]) as HX. rewrite <- HE0 in HX.
pose proof (E_morev regs1 cx (c_rcur cx) [ra_packed cx] LG) as HMo. rewrite <- HE0 in HMo.
assert (HE69 : ew E 69 = Z_to_bv 64 (ra_packed cx)) by (apply (HMo 0%nat); reflexivity).
assert (Rpk : 0 <= ra_packed cx < 256).
{ unfold ra_packed. pose proof (YI0j.pal_pow_class) as PPC.
assert (Hpp : c_slct cx <> 0 -> 1 <= YO07.pal_pow (c_slct cx) <= 8).
{ intros Hnz. unfold YO07.pal_pow.
assert (Hc8 : exists k, 0 <= k <= 8 /\ (k = 0 -> c_slct cx <= 1) /\ (0 < k -> 2 ^ (k - 1) < c_slct cx) /\ c_slct cx <= 2 ^ k).
{ assert (Hcases : c_slct cx = 1 \/ c_slct cx = 2 \/ (3 <= c_slct cx <= 4) \/ (5 <= c_slct cx <= 8) \/ (9 <= c_slct cx <= 16) \/
(17 <= c_slct cx <= 32) \/ (33 <= c_slct cx <= 64) \/ (65 <= c_slct cx <= 128) \/ (129 <= c_slct cx <= 256)) by lia.
destruct Hcases as [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | Hk]]]]]]]];
[exists 0 | exists 1 | exists 2 | exists 3 | exists 4 | exists 5 | exists 6 | exists 7 | exists 8]; (split; [lia | split; [intros; lia | split; [intros; cbn; lia | cbn; lia]]]). }
destruct Hc8 as (k & Hk & H0 & Hlo & Hhi). rewrite (YI0j.np2_class k (c_slct cx) ltac:(lia) H0 Hlo Hhi). lia. }
destruct (Z.eqb_spec (c_slct cx) 0); cbn [negb]; destruct (YO07.flag (c_fattr cx) 2); lia. }
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 (c_raw cx)) by (rewrite (HE 8%nat 8%bv eq_refl); exact R8).
assert (HE9 : ew E 9 = Z_to_bv 64 (c_cfp cx)) by (rewrite (HE 9%nat 9%bv eq_refl); exact R9).
assert (HE23 : ew E 23 = Z_to_bv 64 (c_slct cx)) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HE10 : ew E 10 = Z_to_bv 64 (Z.land (c_fattr cx) 2)) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (HE22 : ew E 22 = Z_to_bv 64 (c_cfp cx + 30)) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (HE24 : ew E 24 = Z_to_bv 64 p) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (HE11 : ew E 11 = Z_to_bv 64 ne) by (rewrite (HE 11%nat 11%bv eq_refl); exact G11).
assert (HE35 : ew E 35 = Z_to_bv 64 (c_w cx)) by (apply (HX 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 (c_h cx)) by (apply (HX 4%nat); reflexivity).
assert (HE37 : ew E 37 = Z_to_bv 64 (c_top cx)) by (apply (HX 5%nat); reflexivity).
assert (HE38 : ew E 38 = Z_to_bv 64 (c_left cx)) by (apply (HX 6%nat); reflexivity).
assert (MKS : forall lo hi, lo <= ne <= hi ->
st_ok ubs0segs E (ssIC [(11%nat, mkAF lo hi 0)]) (mkst regs1 (Z_to_bv 64 PC_IC) mem1 (seg_rom ubs0segs))).
{ intros lo hi Hlh. subst E. unfold ssIC.
apply (ra_st_okW cx (c_rcur cx) regs1 [ra_packed cx] mem1 PC_IC sr_atoms 7 46 false [ch37; ch46 69] _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_Ereg.
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor; [apply ch37_ok; exact HF37 | constructor; [apply (ch46_ok _ _ _ 69 HE69 Rpk HF46) | constructor]].
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE11, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 PC_IC) mem1 (seg_rom ubs0segs))) in HJ.
Ltac finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS HneV Hk icl idl k HE37 HE38 HE69 Rpk HFO cx :=
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SR_ret;
lazymatch goal with |- at_C _ _ _ _ _ _ _ _ _ _ (mkCfg ?msx _) => exists (ms_regs msx), (ms_mem msx), icl, idl end;
split; [reflexivity|]; cbn [ms_regs ms_mem mkst]; split; [exact HJ|];
split; [ split; [| split; [| split; [|split; [|split]]]];
[ let Q := fresh "Q" in (jreg HS (2%bv:reg) as Q); rewrite Q, <- (Z_to_bv_bv_unsigned 64 (ew _ 2)), HE2; reflexivity
| let Q := fresh "Q" in (jreg HS (8%bv:reg) as Q); rewrite Q; exact HE8
| let Q := fresh "Q" in (jreg HS (9%bv:reg) as Q); rewrite Q; exact HE9
| let Q := fresh "Q" in (jreg HS (4%bv:reg) as Q); rewrite Q, (HE 4%nat 4%bv eq_refl); assumption
| let Q := fresh "Q" in (jreg HS (3%bv:reg) as Q); rewrite Q, (HE 3%nat 3%bv eq_refl); assumption
| let Q := fresh "Q" in (jreg HS (27%bv:reg) as Q); rewrite Q, (HE 27%nat 27%bv eq_refl); assumption ] |];
split; [let Q := fresh "Q" in (jreg HS (23%bv:reg) as Q); rewrite Q; exact HE23|];
split; [let Q := fresh "Q" in (jreg HS (22%bv:reg) as Q); rewrite Q; exact HE22|];
split; [let Q := fresh "Q" in (jreg HS (10%bv:reg) as Q); rewrite Q; exact HE10|];
split; [let Q := fresh "Q" in (jreg HS (24%bv:reg) as Q); rewrite Q; exact HE24|];
split; [let Q := fresh "Q" in (jreg HS (18%bv:reg) as Q); rewrite Q; reflexivity|];
split; [let Q := fresh "Q" in (jreg HS (25%bv:reg) as Q); rewrite Q; reflexivity|];
split; [lia|]; split; [lia|];
split; [let Q := fresh "Q" in (jreg HS (13%bv:reg) as Q); rewrite Q; exact HE35|];
split; [let Q := fresh "Q" in (jreg HS (14%bv:reg) as Q); rewrite Q; exact HE36|];
split; [ eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; mbyte_chain ltac:(fun H => rewrite ?HE2 in H)
| split; [ eapply (frame_savedN_kept ubs0_msyms 12); [lia | exact HFS|]; intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H)
|
let HIC := fresh "HIC" in let v7 := eval vm_compute in (icl - 1) in
assert (HIC : icl = ra_iclen cx) by (unfold ra_iclen; rewrite <- HneV; rewrite (icl_class k) by lia; reflexivity);
split; [ exact HIC | split; [ reflexivity
| eapply (fbC_of_Cregion _ _ _ _ _ cx (c_rcur cx) v7 HFO (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) HE2 HE35 HE36 HE37 HE38 HE69 Rpk ltac:(rewrite <- HIC; reflexivity) ltac:(lia));
let c := fresh "c" in let Hc := fresh "Hc" in
intros c Hc; repeat (destruct Hc as [<- | Hc]; [cbn; tauto|]); destruct Hc ] ] ] ].
assert (Hcases : (0 <= ne <= 1) \/ ne = 2 \/ (3 <= ne <= 4) \/ (5 <= ne <= 8) \/ (9 <= ne <= 16) \/
(17 <= ne <= 32) \/ (33 <= ne <= 64) \/ (65 <= ne <= 128) \/ (129 <= ne <= 256)) by lia.
destruct Hcases as [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | Hk]]]]]]]].
- pose proof (MKS 0 1 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs0tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS HneV Hk 3 4 0 HE37 HE38 HE69 Rpk HFO cx.
- pose proof (MKS 2 2 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs0tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS HneV Hk 3 4 1 HE37 HE38 HE69 Rpk HFO cx.
- pose proof (MKS 3 4 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs0tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS HneV Hk 3 4 2 HE37 HE38 HE69 Rpk HFO cx.
- pose proof (MKS 5 8 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs0tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS HneV Hk 4 8 3 HE37 HE38 HE69 Rpk HFO cx.
- pose proof (MKS 9 16 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs0tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS HneV Hk 5 16 4 HE37 HE38 HE69 Rpk HFO cx.
- pose proof (MKS 17 32 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs0tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS HneV Hk 6 32 5 HE37 HE38 HE69 Rpk HFO cx.
- pose proof (MKS 33 64 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs0tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS HneV Hk 7 64 6 HE37 HE38 HE69 Rpk HFO cx.
- pose proof (MKS 65 128 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs0tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS HneV Hk 8 128 7 HE37 HE38 HE69 Rpk HFO cx.
- pose proof (MKS 129 256 ltac:(lia)) as HS. clear MKS.
jrun_to LAWS ubs0tbl_ok HS HJ PC_C; [wr HE2|]. finishC HS HJ HE HE2 HE8 HE9 HE10 HE23 HE22 HE24 HE35 HE36 Hobjs HFS HneV Hk 9 256 8 HE37 HE38 HE69 Rpk HFO cx.
Qed.
End S.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
