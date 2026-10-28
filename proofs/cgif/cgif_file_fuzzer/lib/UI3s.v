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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b YI06 UI5b YI09 YI08 YI0r
UI1w UI4l UI21 UI5o UI5l YI6b UN3c UN0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YL01 YN03 YI0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI17 YI14 YI18 YI1a UI5c YI07 YI05 YN00
UI22 YI5a UI23 UI5d UI5f UN38 UN36 YI00 YI01 UI3r.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition NG_TAIL : Z := Eval vm_compute in (ubs0_A_cgif_newgif + 0x11c).
Definition NG_RAWRET : Z := Eval vm_compute in (ubs0_A_cgif_newgif + 0x160).
Definition NG_FCLOSERET : Z := Eval vm_compute in (ubs0_A_cgif_newgif + 0x180).
Definition NG_FREED : Z := Eval vm_compute in (ubs0_A_cgif_newgif + 0x188).
Definition NG_RET0 : Z := Eval vm_compute in (ubs0_A_cgif_newgif + 0x1a8).
End c.
Definition lits_Config : list (option Z) :=
[None; Some ubs0_D_str_tmp_out_gif; None; None; None; None; None; None; Some 0; Some 0].
Definition lits_CGIF0 : list (option Z) :=
[Some 0; Some 0; Some 0; None; Some ubs0_D_str_tmp_out_gif; None; None; None; None; None; None; Some 0; Some 0; Some 0; None; Some 0; Some 1].
Definition cfg_chunks : list YP09.chunk :=
[mkChunk 0 (CVal 8 (SOff 32 0)); mkChunk 8 (CVal 8 (SLit ubs0_D_str_tmp_out_gif)); mkChunk 16 (CVal 4 (SOff 34 0)); mkChunk 20 (CVal 4 (SOff 35 0));
mkChunk 24 (CVal 4 (SOff 42 0)); mkChunk 28 (CVal 2 (SOff 38 0)); mkChunk 30 (CVal 2 (SOff 39 0));
mkChunk 32 (CVal 8 (SLit 0)); mkChunk 40 (CVal 8 (SLit 0))].
Definition ss_ngt : sstate :=
mkSS NG_TAIL sr_atoms
[ YP09.mkRegion (Some 2%nat) 0 80 0 80
[mkChunk 0 (CZero 16); mkChunk 16 (CVal 8 (SOff 32 0)); mkChunk 24 (CZero 16);
mkChunk 72 (CVal 8 (SOff 60 0)); mkChunk 64 (CVal 8 (SOff 61 0)); mkChunk 56 (CVal 8 (SOff 62 0)); mkChunk 48 (CVal 8 (SOff 63 0));
mkChunk 40 (CVal 8 (SOff 64 0))];
YP09.mkRegion (Some 9%nat) 0 48 0 0 cfg_chunks;
YP09.mkRegion (Some 8%nat) 0 CGIF_SIZE 0 CGIF_SIZE (obj_chunks_gen LAY_CGIF 43 lits_CGIF0) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + NEWGIF_STK - 80) (2^47 - 80) 4);
(8%nat, mkAF 4096 (CEIL_MAX - CGIF_SIZE) 4);
(18%nat, mkAF 4096 (CEIL_MAX - FILE_BLOCK) 4);
(9%nat, mkAF CEIL_MIN (2^63 - 48) 3);
(11%nat, mkAF 0 65535 0);
(34%nat, mkAF 0 (2^32 - 1) 0); (36%nat, mkAF 1 65535 0); (37%nat, mkAF 1 65535 0);
(38%nat, mkAF 0 65535 0); (39%nat, mkAF 0 65535 0); (42%nat, mkAF 0 (2^32 - 1) 0) ] [] []).
Definition ss_ngt_c : sstate := Eval vm_compute in ss_ngt.
Lemma lits_Config_ok : forall pal0 attr gen W H ngp loops,
forall j z, nth_error lits_Config j = Some (Some z) ->
nth_error [pal0; ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; loops; 0; 0] j = Some z.
Proof.
intros pal0 attr gen W H ngp loops j z Hj. do 10 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; reflexivity] |]).
destruct j; discriminate Hj.
Qed.
Lemma lits_CGIF0_ok : forall pal' attr gen W H ngp loops f,
forall j z, nth_error lits_CGIF0 j = Some (Some z) ->
nth_error [0; 0; 0; pal'; ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; loops; 0; 0; 0; f; 0; 1] j = Some z.
Proof.
intros pal' attr gen W H ngp loops f j z Hj. do 17 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; reflexivity] |]).
destruct j; discriminate Hj.
Qed.
Ltac lit_range := lazymatch goal with |- (_ <= _ < _)%Z => vm_compute; split; [let HH := fresh in intros HH; discriminate HH | reflexivity] end.
Ltac jafter_stretch_keep HS k regs2 mem2 clob newpc idxs HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
pose proof (st_ok_after_stretch segs k E ss ms regs2 mem2 rs newpc clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob newpc) in
change (ss_after_stretch ss rs k clob newpc) with ss2 in HS2
end.
Ltac add_region HS r :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_region segs E1 ss1 ms1 r) in HS;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| vm_compute; reflexivity | | ]
end.
Ltac ew_havocA :=
repeat match goal with
| |- context [ew (havoc ?E0 ?k ?ws) ?n] => rewrite (ew_havoc_old E0 k ws n) by nat_lt_lit
end.
Ltac ew_havocA_in H :=
repeat match type of H with
| context [ew (havoc ?E0 ?k ?ws) ?n] => rewrite (ew_havoc_old E0 k ws n) in H by nat_lt_lit
end.
Ltac mem_back1 bases slv :=
match goal with
| HF : frame_of ?E ?rs ?m ?m' |- mbyte _ ?m' ?a = _ =>
mb_frame_with HF slv ltac:(ew_havocA; bases; slv)
| Hout : (forall x : word, bv_unsigned x < ?d \/ ?d + ?n <= bv_unsigned x -> ?m' x = ?m x) |- mbyte ?sg ?m' ?a = _ =>
unfold mbyte at 1; rewrite (Hout (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by slv; slv); fold (mbyte sg m a)
| Hhi : (forall x : Z, alloc_ceiling <= x < 2 ^ 64 -> ~ _ -> mbyte _ ?m' x = mbyte _ ?m x /\ _) |- mbyte _ ?m' ?a = _ =>
rewrite (proj1 (Hhi a ltac:(slv) ltac:(slv)))
end.
Ltac mem_back bases slv := cbn [ms_mem mkst] in *; repeat (reflexivity || mem_back1 bases slv).
Ltac frame_wordI HS idx HU2 HE n rr :=
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv + (- dd)) by lia;
eapply (st_chunk_word _ _ _ idx _ 2%nat (- dd) (SOff n 0) spv (bv_unsigned w) HS);
[ reflexivity | reflexivity | cbv; auto 20
| ew_havocA; exact HU2
| cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE n rr eq_refl), Z_to_bv_bv_unsigned; reflexivity
| let Rw := fresh "Rw" in pose proof (bv_unsigned_in_range 64 w) as Rw; change (bv_modulus 64) with (2 ^ 64) in Rw; clear - Rw; lia ]
end.
Ltac cfg_field_atom Hj HX :=
cbn in Hj; injection Hj as <-; cbn [snd nth tl lits_Config nth_error lay_shift map fst Z.of_N];
split; [cbn; lia | ew_havocA; apply HX; reflexivity].
Ltac cfg_field_lit Hj :=
cbn in Hj; injection Hj as <-; cbn [snd nth tl lits_Config nth_error lay_shift map fst Z.of_N];
split; [first [lit_range | cbn; lia] | reflexivity].
Ltac cfg_fields_tac Hj HX :=
let j := lazymatch type of Hj with nth_error _ ?j = _ => j end in
destruct j as [|j]; [cfg_field_lit Hj|];
destruct j as [|j]; [cfg_field_atom Hj HX|];
destruct j as [|j]; [cfg_field_atom Hj HX|];
destruct j as [|j]; [cfg_field_atom Hj HX|];
destruct j as [|j]; [cfg_field_atom Hj HX|];
destruct j as [|j]; [cfg_field_atom Hj HX|];
destruct j as [|j]; [cfg_field_atom Hj HX|];
destruct j as [|j]; [cfg_field_lit Hj|];
destruct j as [|j]; [cfg_field_lit Hj|];
destruct j; discriminate Hj.
Ltac cgif_obj_tac HS Hg palE HpalE HX :=
change LAY_CGIF with ([(0, 8%N); (8, 8%N); (16, 8%N)] ++ [(24, 8%N)] ++
lay_shift 24 [(8, 8%N); (16, 4%N); (20, 4%N); (24, 2%N); (26, 2%N); (28, 2%N); (30, 2%N); (32, 8%N); (40, 8%N)] ++
[(72, 8%N); (80, 8%N); (88, 4%N); (92, 4%N)]);
lazymatch goal with |- obj_at _ _ _ _ [0; 0; 0; ?pal'; 0; ?attr; ?gen; ?W; ?H; ?ngp; ?loops; ?wcb; 0; 0; 0; 0; 1] =>
change [0; 0; 0; pal'; 0; attr; gen; W; H; ngp; loops; wcb; 0; 0; 0; 0; 1]
with ([0; 0; 0] ++ [pal'] ++ [0; attr; gen; W; H; ngp; loops; wcb; 0] ++ [0; 0; 0; 1])
end;
rewrite obj_at_app by reflexivity; split;
[
cbn [obj_at]; unfold field_ok; cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N];
repeat split;
first [ eapply (st_chunk_zero_val _ _ _ _ 0%nat _ 53%nat 0 24 _ _ 8%nat HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hg | lia | cbn; lia]
| lit_range | lia ]
| rewrite obj_at_app by reflexivity; split;
[
cbn [obj_at]; unfold field_ok; cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N];
split; [split; [ eapply (st_chunk_val _ _ _ _ 0%nat _ 53%nat 24 8%N palE _ _ HS);
[reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hg
| cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HpalE, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia ]
| cbn; lia ] | exact I]
| rewrite obj_at_app by reflexivity; split;
[
eapply (st_obj_at _ _ _ _ 0%nat _ 53%nat _ _ _ 33 (tl lits_Config) HS eq_refl eq_refl ltac:(ew_havocA; exact Hg));
[ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity
| let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; cfg_fields_tac Hj HX ]
|
cbn [obj_at]; unfold field_ok; cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N];
split; [split; [ eapply (st_chunk_zero_val _ _ _ _ 1%nat _ 53%nat 72 8 _ _ 8%nat HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hg | lia | cbn; lia] | lit_range ] |];
split; [split; [ eapply (st_chunk_val _ _ _ _ 1%nat _ 53%nat 80 8%N (SLit 0) _ 0 HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hg | reflexivity | lit_range | cbn; lia] | lit_range ] |];
split; [split; [ eapply (st_chunk_zero_val _ _ _ _ 1%nat _ 53%nat 88 4 _ _ 4%nat HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hg | lia | cbn; lia] | lit_range ] |];
split; [split; [ eapply (st_chunk_val _ _ _ _ 1%nat _ 53%nat 92 4%N (SLit 1) _ 1 HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hg | reflexivity | lit_range | cbn; lia] | lit_range ] |];
exact I ] ] ].
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis AX : AllocExtra ubs0_msyms MR.
Hypothesis RAWNEWX : rawnew_specX API.
Lemma newgif_tail_x :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc
(cfgp pal0 pala attr gen W H ngp loops g pal' sgct f : Z) (palblk : list (Z * Z)) (GPAL : list Z) (b : rbound) (TB : TSet),
journal ubs0_msyms MR NEWGIF_STK (spZ regs0) [sink_token] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) -> spZ regs0 mod 16 = 0 -> spZ regs0 <= 2 ^ 47 ->
cfgp mod 8 = 0 -> spZ regs0 <= cfgp -> cfgp + 48 <= 2 ^ 63 ->
obj_at ubs0segs memc cfgp LAY_Config [pal0; ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; loops; 0; 0] ->
1 <= W -> 1 <= H -> W * H <= 100000000 ->
obj_at ubs0segs memc g LAY_CGIF [0; 0; 0; pal'; ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; loops; 0; 0; 0; f; 0; 1] ->
Permutation (blocks Lc Ac) ((g, CGIF_SIZE) :: palblk ++ (f, FILE_BLOCK) :: blocks L A) ->
palblk = (if Z.land attr 4 =? 0 then [(pal', 3 * ngp)] else []) ->
~ In (g, CGIF_SIZE) (blocks L A) -> ~ In (f, FILE_BLOCK) (blocks L A) ->
(forall bb, In bb palblk -> In bb (blocks L A) -> snd bb <= 0) ->
sgct = (if Z.land attr 4 =? 0 then ngp else 0) ->
sink_at ubs0_msyms memc mdc f [] ->
res_ok Ac (ng_b3 b attr ngp) -> newgif_room b ->
Z_to_bv 64 pala = Z_to_bv 64 pal0 ->
(Z.land attr 4 = 0 -> In (pala, 3 * ngp) (blocks L A) /\ YI00.garr8 ubs0segs memc pala GPAL /\ Z.of_nat (length GPAL) = 3 * ngp /\
YI00.garr8 ubs0segs memc pal' GPAL) ->
(forall i, 0 <= i < 40 -> ~ (16 <= i < 24) -> mbyte ubs0segs memc (spZ regs0 - 80 + i) = Some (Z_to_bv 8 0)) ->
word_mem ubs0segs memc (spZ regs0 - 64) pal0 ->
word_mem ubs0segs memc (spZ regs0 - 8) (bv_unsigned (getr regs0 1)) ->
word_mem ubs0segs memc (spZ regs0 - 16) (bv_unsigned (getr regs0 8)) ->
word_mem ubs0segs memc (spZ regs0 - 24) (bv_unsigned (getr regs0 9)) ->
word_mem ubs0segs memc (spZ regs0 - 32) (bv_unsigned (getr regs0 18)) ->
word_mem ubs0segs memc (spZ regs0 - 40) (bv_unsigned (getr regs0 19)) ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 80) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 18 = Z_to_bv 64 f ->
getr regs1 9 = Z_to_bv 64 cfgp -> getr regs1 11 = Z_to_bv 64 sgct -> bv_unsigned (getr regs1 10) mod 2 ^ 32 = attr ->
getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 20 = getr regs0 20 -> getr regs1 21 = getr regs0 21 -> getr regs1 22 = getr regs0 22 ->
getr regs1 23 = getr regs0 23 -> getr regs1 24 = getr regs0 24 -> getr regs1 25 = getr regs0 25 ->
getr regs1 26 = getr regs0 26 -> getr regs1 27 = getr regs0 27 ->
(256 < sgct -> forall c', newgif_postB0 API L A regs0 mem md b c' -> realizes ubs0segs c' TB) ->
(sgct <= 256 -> forall c', newgif_postB1 API L A regs0 mem md b attr gen W H ngp loops GPAL c' -> realizes ubs0segs c' TB) ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 NG_TAIL) memc (seg_rom ubs0segs)) mdc) (fun c1 => realizes ubs0segs c1 TB).
Proof using AX IMG RAWNEWX.
intros L A mem md regs0 regs1 Lc Ac memc mdc cfgp pal0 pala attr gen W H ngp loops g pal' sgct f palblk GPAL b TB
HJ Hid Hra0 Htp0 Hal16 Hsp47 Hcal Hclo Hchi Hcfg HW HH HWH Hobj HB Hpalblk Hgfresh Hffresh Hpalfresh Hsgct
HSK HRES HROOM Hpala HGP Hz Wpal W1 W8 W9 W18 W19
G2 G8 G9 G18 G11 G10 G3 G4 G20 G21 G22 G23 G24 G25 G26 G27 KB0 KB1.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HSTKv : NEWGIF_STK = 9216) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity. assert (HFBv : FILE_BLOCK = 1264) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs0) in *.
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
assert (Hfin : In (f, FILE_BLOCK) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | right; apply in_app_iff; right; left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc g CGIF_SIZE HH0 Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc f FILE_BLOCK HH0 Hfin ltac:(lia)) as (Hf0 & Hf1 & Hf16).
assert (Hsep_fg : f + FILE_BLOCK <= g \/ g + CGIF_SIZE <= f).
{ destruct (heap_sep_perm _ _ LAWS Lc Ac memc mdc (g, CGIF_SIZE) _ (f, FILE_BLOCK) HH0 HB ltac:(apply in_app_iff; right; left; reflexivity)) as [H0|H0]; cbn [fst snd] in H0; lia. }
assert (Henvblk : forall L1 A1 m1 md1 bb n a, heap_ok MR L1 A1 m1 md1 -> In (bb, n) (blocks L1 A1) -> env_addr a -> ~ (bb <= a < bb + n)).
{ intros L1 A1 m1 md1 bb n a HHx Hin1 Hea Hr. apply blocks_In in Hin1 as (q & Hq & Hqin).
destruct (skl_env ubs0_msyms a Hea) as (Himg1 & _). assert (Hrg : 0 <= a - bb < n) by lia.
apply (il_blocks IMG L1 A1 m1 md1 q n (a - bb) (proj1 HHx) Hqin Hrg). rewrite Hq. replace (bb + (a - bb)) with a by lia. exact Himg1. }
pose proof (obj_at_range _ _ _ _ _ Hcfg) as Rcfg. pose proof (obj_at_range _ _ _ _ _ Hobj) as Robj.
pose proof (Rcfg 0%nat pal0 eq_refl) as Rpal0. pose proof (Rcfg 2%nat attr eq_refl) as Rattr. pose proof (Rcfg 3%nat gen eq_refl) as Rgen.
pose proof (Rcfg 4%nat W eq_refl) as RW. pose proof (Rcfg 5%nat H eq_refl) as RH. pose proof (Rcfg 6%nat ngp eq_refl) as Rngp.
pose proof (Rcfg 7%nat loops eq_refl) as Rloops. pose proof (Robj 3%nat pal' eq_refl) as Rpal'.
cbn in Rpal0, Rattr, Rgen, RW, RH, Rngp, Rloops, Rpal'.
assert (Rsgct : 0 <= sgct < 65536) by (rewrite Hsgct; destruct (Z.land attr 4 =? 0); lia).
assert (Hngp3 : 0 <= 3 * ngp <= PALMAX) by (unfold PALMAX; lia).
set (cvals := [pal0; ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; loops; 0; 0]) in *.
set (gvals := [0; 0; 0; pal'; ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; loops; 0; 0; 0; f; 0; 1]) in *.
set (svals := [bv_unsigned (getr regs0 1); bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18);
bv_unsigned (getr regs0 19)]).
set (E := Ereg regs1 (map (Z_to_bv 64) cvals ++ map (Z_to_bv 64) ((W + 65536 * H) :: gvals ++ svals) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error cvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HY : forall j v, nth_error ((W + 65536 * H) :: gvals ++ svals) j = Some v -> ew E (42 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (42 + j)%nat with (32 + (length cvals + j))%nat by (subst cvals; cbn; lia). apply Ereg_vals2. exact Hj. }
assert (HG : forall j v, nth_error gvals j = Some v -> ew E (43 + j) = Z_to_bv 64 v).
{ intros j v Hj. replace (43 + j)%nat with (42 + Datatypes.S j)%nat by lia. apply HY. cbn [nth_error].
rewrite nth_error_app1; [exact Hj|].
destruct (Nat.lt_ge_cases j (length gvals)) as [Hl|Hl]; [exact Hl|]. rewrite (proj2 (nth_error_None gvals j) Hl) in Hj. discriminate. }
assert (HSV : forall j v, nth_error svals j = Some v -> ew E (60 + j) = Z_to_bv 64 v).
{ intros j v Hj. replace (60 + j)%nat with (42 + Datatypes.S (length gvals + j))%nat by (subst gvals; cbn; lia). apply HY. cbn [nth_error].
rewrite nth_error_app2 by lia. replace (length gvals + j - length gvals)%nat with j by lia. exact Hj. }
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 80) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 18) = f) by (rewrite (HE 18%nat 18%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 9) = cfgp) by (rewrite (HE 9%nat 9%bv eq_refl), G18; apply unsigned_lit_small; lia).
assert (HE11 : ew E 11 = Z_to_bv 64 sgct) by (rewrite (HE 11%nat 11%bv eq_refl); exact G11).
assert (HX42 : ew E 42 = Z_to_bv 64 (W + 65536 * H)) by (apply (HY 0%nat); reflexivity).
assert (HX32 : ew E 32 = Z_to_bv 64 pal0) by (apply (HX 0%nat); reflexivity).
assert (HX34 : ew E 34 = Z_to_bv 64 attr) by (apply (HX 2%nat); reflexivity).
assert (HX35 : ew E 35 = Z_to_bv 64 gen) by (apply (HX 3%nat); reflexivity).
assert (HX36 : ew E 36 = Z_to_bv 64 W) by (apply (HX 4%nat); reflexivity).
assert (HX37 : ew E 37 = Z_to_bv 64 H) by (apply (HX 5%nat); reflexivity).
assert (HX38 : ew E 38 = Z_to_bv 64 ngp) by (apply (HX 6%nat); reflexivity).
assert (HX39 : ew E 39 = Z_to_bv 64 loops) by (apply (HX 7%nat); reflexivity).
assert (Rpath : 0 <= ubs0_D_str_tmp_out_gif < 2 ^ 64) by (unfold ubs0_D_str_tmp_out_gif; lia).
assert (HS : st_ok ubs0segs E ss_ngt_c (mkst regs1 (Z_to_bv 64 NG_TAIL) memc (seg_rom ubs0segs))).
{ change ss_ngt_c with ss_ngt. unfold ss_ngt. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_cons. { apply chunk_ok_zero. cbn [c_off]. intros i Hi. replace (sp0 - 80 + 0 + i) with (sp0 - 80 + i) by lia. apply Hz; lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pal0); [cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; replace (sp0 - 80 + 16) with (sp0 - 64) by lia; exact Wpal]. }
apply Forall_cons. { apply chunk_ok_zero. cbn [c_off]. intros i Hi. replace (sp0 - 80 + 24 + i) with (sp0 - 80 + (24 + i)) by lia. apply Hz; lia. }
assert (CK : forall off j (w : Z), nth_error svals j = Some w -> word_mem ubs0segs memc (sp0 - 80 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs0segs (Ereg regs1 (map (Z_to_bv 64) cvals ++ map (Z_to_bv 64) ((W + 65536 * H) :: gvals ++ svals) ++ [])) memc (sp0 - 80) (mkChunk off (CVal 8 (SOff (60 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HSV j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
assert (RU : forall w : word, 0 <= bv_unsigned w < 2 ^ 64).
{ intros w. pose proof (bv_unsigned_in_range 64 w) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw. lia. }
repeat (apply Forall_cons;
[ first [ apply (CK 72 0%nat _ eq_refl); [replace (sp0 - 80 + 72) with (sp0 - 8) by lia; exact W1 | apply RU]
| apply (CK 64 1%nat _ eq_refl); [replace (sp0 - 80 + 64) with (sp0 - 16) by lia; exact W8 | apply RU]
| apply (CK 56 2%nat _ eq_refl); [replace (sp0 - 80 + 56) with (sp0 - 24) by lia; exact W9 | apply RU]
| apply (CK 48 3%nat _ eq_refl); [replace (sp0 - 80 + 48) with (sp0 - 32) by lia; exact W18 | apply RU]
| apply (CK 40 4%nat _ eq_refl); [replace (sp0 - 80 + 40) with (sp0 - 40) by lia; exact W19 | apply RU] ] | ]).
apply Forall_nil.
+
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU18.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
pose proof Hcfg as Hc. cbn [obj_at LAY_Config] in Hc. unfold field_ok in Hc. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N] in Hc.
destruct Hc as ((F0 & _) & (F1 & _) & (F2 & _) & (F3 & _) & (F4 & _) & (F5 & _) & (F6 & _) & (F7 & _) & (F8 & _) & (F9 & _) & _).
unfold cfg_chunks.
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pal0); [cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F0]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ ubs0_D_str_tmp_out_gif); [reflexivity | exact Rpath | cbn; lia | exact F1]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ attr); [cbn [sv_denot]; rewrite Z.add_0_r, HX34, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F2]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ gen); [cbn [sv_denot]; rewrite Z.add_0_r, HX35, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F3]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (W + 65536 * H)); [cbn [sv_denot]; rewrite Z.add_0_r, HX42, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_wh_join; [exact F4 | replace (cfgp + 24 + 2) with (cfgp + 26) by lia; exact F5 | lia | lia]]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ ngp); [cbn [sv_denot]; rewrite Z.add_0_r, HX38, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F6]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ loops); [cbn [sv_denot]; rewrite Z.add_0_r, HX39, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F7]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [reflexivity | cbn; lia | cbn; lia | exact F8]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [reflexivity | cbn; lia | cbn; lia | exact F9]. }
apply Forall_nil.
+
eapply (region_ok_obj_gen ubs0segs _ memc 8 g); [exact HU8 | lia | lia | exact Hobj | reflexivity | | apply lits_CGIF0_ok | ].
* intros j v Hj. apply (HG j v Hj).
* intros i Hi. apply (present_writable ubs0segs). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc g CGIF_SIZE i HH0 Hgin ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU8, HU18. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU8, HU9, HU18, HE11, HX34, HX36, HX37, HX38, HX39, HX42, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert (Hspm : (sp0 - 80) mod 16 = 0) by (replace (sp0 - 80) with (sp0 + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 NG_TAIL) memc (seg_rom ubs0segs))) in HJ.
assert (Hspm : (sp0 - 80) mod 16 = 0) by (replace (sp0 - 80) with (sp0 + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hcf8 : (sp0 - 80) mod 8 = 0).
{ pose proof (proj2 (Z.div_exact sp0 16 ltac:(lia)) Hal16) as E16.
replace (sp0 - 80) with ((2 * (sp0 / 16) - 10) * 8) by lia. apply Z_mod_mult. }
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cgif_raw_newgif.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_tmp; [reflexivity | exact HU8 | exact Hgin | exact Hgfresh | cbn; lia | cbn; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hr10. rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 2)), HU2 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hrawcfg : exists rattr, obj_at ubs0segs (ms_mem msx) (sp0 - 80) LAY_RawConfig [ubs0_A_cgif_writecb; g; pal0; rattr; W; H; sgct; loops]
/\ 0 <= rattr < 2 ^ 32 /\ rattr = raw_attr_of attr)
end.
{ pose proof (st_region_chunks ubs0segs _ _ _ 0%nat _ 2%nat (sp0 - 80) HS eq_refl eq_refl HU2) as HC.
cbn [r_chunks] in HC.
repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC as [?CC HC] end.
lazymatch type of CC2 with chunk_ok _ ?E1 _ _ (mkChunk 24 (CVal 4 ?e)) =>
exists (bv_unsigned (sv_denot E1 e) mod 2 ^ 32) end.
split; [| split; [apply Z.mod_pos_bound; lia |]].
{ cbn [obj_at LAY_RawConfig]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
assert (Vwh : val_mem ubs0segs (ms_mem ms) (sp0 - 80 + 28) 4 (W + 65536 * H)).
{ pose proof (val_mem_low_of_chunk _ _ _ _ _ 4%N _ CC1 ltac:(cbn; lia)) as V.
replace (bv_unsigned (sv_denot _ (SExt true 32 (SOff 42 0))) mod 2 ^ (8 * Z.of_N 4)) with (W + 65536 * H) in V; [exact V|].
change (bv_unsigned (sv_denot E (SExt true 32 (SOff 42 0)))) with (U E (SExt true 32 (SOff 42 0))).
rewrite U_SExt, (U_atom _ 42 (W + 65536 * H) HX42) by lia. change (8 * Z.of_N 4) with 32. symmetry. apply sext32_low. lia. }
destruct (val_mem_wh_split _ _ _ _ _ Vwh ltac:(lia) ltac:(lia)) as [VW VH].
assert (Vlp : val_mem ubs0segs (ms_mem ms) (sp0 - 80 + 34) 2 loops).
{ pose proof (val_mem_low_of_chunk _ _ _ _ _ 2%N _ CC ltac:(cbn; lia)) as V.
replace (bv_unsigned (sv_denot _ (SExt true 16 (SOff 39 0))) mod 2 ^ (8 * Z.of_N 2)) with loops in V; [exact V|].
change (bv_unsigned (sv_denot E (SExt true 16 (SOff 39 0)))) with (U E (SExt true 16 (SOff 39 0))).
rewrite U_SExt, (U_atom _ 39 loops HX39) by lia. change (8 * Z.of_N 2) with 16. symmetry. apply sext16_low. lia. }
split; [split; [| unfold ubs0_A_cgif_writecb; lia] |].
{ eapply (val_of_chunk_ok _ _ _ _ _ 8%N _ _ CC4); [reflexivity | unfold ubs0_A_cgif_writecb; lia | cbn; lia]. }
split; [split; [| lia] |].
{ eapply (val_of_chunk_ok _ _ _ _ _ 8%N _ _ CC3); [cbn [sv_denot]; rewrite Z.add_0_r, HU8; reflexivity | cbn; lia | cbn; lia]. }
split; [split; [| lia] |].
{ eapply (val_of_chunk_ok _ _ _ _ _ 8%N _ _ CC5); [cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
split; [split; [| apply Z.mod_pos_bound; lia] |].
{ apply (val_mem_low_of_chunk _ _ _ _ _ 4%N _ CC2). cbn; lia. }
split; [split; [| lia] |].
{ exact VW. }
split; [split; [| lia] |].
{ replace (sp0 - 80 + 30) with (sp0 - 80 + 28 + 2) by lia. exact VH. }
split; [split; [| lia] |].
{ eapply (val_of_chunk_ok _ _ _ _ _ 2%N _ _ CC0); [cbn [sv_denot]; rewrite Z.add_0_r, HE11, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
split; [split; [| lia] |].
{ exact Vlp. }
exact I. }
set (x := bv_unsigned (getr regs1 10)) in *.
assert (Rx : 0 <= x < 2 ^ 64) by (subst x; pose proof (bv_unsigned_in_range 64 (getr regs1 10)) as Rw; change (bv_modulus 64) with (2 ^ 64) in Rw; lia).
lazymatch goal with |- bv_unsigned (sv_denot ?E1 ?e) mod _ = _ => change (bv_unsigned (sv_denot E1 e)) with (U E1 e) end.
rewrite (raw_attr_exec E 10 x); [| apply U_atom; [rewrite (HE 10%nat 10%bv eq_refl); subst x; symmetry; apply Z_to_bv_bv_unsigned | exact Rx] | exact Rx].
rewrite G10. apply Z.mod_small. unfold raw_attr_of. destruct (YO07.flag attr 2), (YO07.flag attr 16); lia. }
destruct Hrawcfg as (rattr & Hrawcfg & Rrattr & Hrattr).
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hrd : forall i, 0 <= i < 40 -> exists b8, mbyte ubs0segs (ms_mem msx) (sp0 - 80 + i) = Some b8)
end.
{ pose proof (st_region_chunks ubs0segs _ _ _ 0%nat _ 2%nat (sp0 - 80) HS eq_refl eq_refl HU2) as HC.
cbn [r_chunks] in HC.
repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC as [?CC HC] end.
intros i Hi.
destruct (Z_lt_le_dec i 8);  [replace (sp0 - 80 + i) with (sp0 - 80 + 0 + i) by lia; apply (chunk_present _ _ _ _ _ _ CC4); cbn; lia|].
destruct (Z_lt_le_dec i 16); [replace (sp0 - 80 + i) with (sp0 - 80 + 8 + (i - 8)) by lia; apply (chunk_present _ _ _ _ _ _ CC3); cbn; lia|].
destruct (Z_lt_le_dec i 24); [replace (sp0 - 80 + i) with (sp0 - 80 + 16 + (i - 16)) by lia; apply (chunk_present _ _ _ _ _ _ CC5); cbn; lia|].
destruct (Z_lt_le_dec i 28); [replace (sp0 - 80 + i) with (sp0 - 80 + 24 + (i - 24)) by lia; apply (chunk_present _ _ _ _ _ _ CC2); cbn; lia|].
destruct (Z_lt_le_dec i 32); [replace (sp0 - 80 + i) with (sp0 - 80 + 28 + (i - 28)) by lia; apply (chunk_present _ _ _ _ _ _ CC1); cbn; lia|].
destruct (Z_lt_le_dec i 34); [replace (sp0 - 80 + i) with (sp0 - 80 + 32 + (i - 32)) by lia; apply (chunk_present _ _ _ _ _ _ CC0); cbn; lia|].
destruct (Z_lt_le_dec i 36); [replace (sp0 - 80 + i) with (sp0 - 80 + 34 + (i - 34)) by lia; apply (chunk_present _ _ _ _ _ _ CC); cbn; lia|].
replace (sp0 - 80 + i) with (sp0 - 80 + 36 + (i - 36)) by lia; apply (chunk_present _ _ _ _ _ _ CC6); cbn; lia. }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hobj1 : obj_at ubs0segs (ms_mem msx) g LAY_CGIF gvals)
end.
{ eapply (st_obj_at ubs0segs _ _ _ 2%nat _ 8%nat g LAY_CGIF gvals 43 lits_CGIF0 HS eq_refl eq_refl HU8).
- apply incl_chunks_sound. vm_compute. reflexivity.
- reflexivity.
- reflexivity.
- intros j v Hj. split; [exact (Robj j v Hj)|].
assert (Hlj : (j < 17)%nat) by (destruct (Nat.lt_ge_cases j 17) as [Hl|Hl]; [exact Hl|]; rewrite (proj2 (nth_error_None gvals j) Hl) in Hj; discriminate).
do 17 (try (destruct j as [|j]; [cbn [nth_error lits_CGIF0]; first [apply (HG _ _ Hj) | subst gvals; cbn in Hj; congruence] | ])). lia. }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (HSK1 : sink_at ubs0_msyms (ms_mem msx) mdc f [])
end.
{ apply (sink_at_frame ubs0_msyms memc _ mdc f []); [|exact HSK].
intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling /\ ~ (g <= a < g + 96))
by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); pose proof (Henvblk Lc Ac memc mdc g CGIF_SIZE a HH0 Hgin Ha); lia]).
mem_back ltac:(rewrite ?HU2, ?HU8, ?HU18) ltac:(lia). }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (HGP1 : Z.land attr 4 = 0 -> In (pala, 3 * ngp) (blocks L A) /\ YI00.garr8 ubs0segs (ms_mem msx) pala GPAL /\ Z.of_nat (length GPAL) = 3 * ngp /\
YI00.garr8 ubs0segs (ms_mem msx) pal' GPAL)
end.
{ intros Hz4. destruct (HGP Hz4) as (Hpin & HGa & HGn & HGc). rewrite Hz4 in Hpalblk. cbn in Hpalblk.
assert (Hpain : In (pala, 3 * ngp) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | right; apply in_app_iff; right; right; exact Hpin]).
assert (Hpcin : In (pal', 3 * ngp) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | right; rewrite Hpalblk; left; reflexivity]).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pala (3 * ngp) HH0 Hpain) as [Ra0 Ra1].
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pal' (3 * ngp) HH0 Hpcin) as [Rc0 Rc1].
pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (g, CGIF_SIZE) _ (pala, 3 * ngp) HH0 HB ltac:(apply in_app_iff; right; right; exact Hpin)) as Xa. cbn [fst snd] in Xa.
pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (g, CGIF_SIZE) _ (pal', 3 * ngp) HH0 HB ltac:(apply in_app_iff; left; rewrite Hpalblk; left; reflexivity)) as Xc. cbn [fst snd] in Xc.
split; [exact Hpin|]. split; [| split; [exact HGn|]].
- eapply YI00.garr8_frame; [exact HGa|]. intros a Ha. rewrite HGn in Ha. mem_back ltac:(rewrite ?HU2, ?HU8, ?HU18) ltac:(lia).
- eapply YI00.garr8_frame; [exact HGc|]. intros a Ha. rewrite HGn in Ha. mem_back ltac:(rewrite ?HU2, ?HU8, ?HU18) ltac:(lia). }
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := RAWNEW_STK) (FP1 := sink_fp f)
(K := fun L2 A2 (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) => st_init_done A2 = true /\ exists res, getr regs2 10 = Z_to_bv 64 res /\
((res = 0 /\ 256 < sgct /\ blocks L2 A2 = blocks Lc Ac /\ sink_at ubs0_msyms mem2 md2 f [] /\ res_ok A2 (ng_b3 b attr ngp)) \/
(res <> 0 /\ sgct <= 256 /\
sink_at ubs0_msyms mem2 md2 f (YO07.raw_header W H sgct GPAL rattr loops) /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, RAW_SIZE) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
obj_at ubs0segs mem2 res LAY_Raw [ubs0_A_cgif_writecb; g; pal0; rattr; W; H; sgct; loops; R_PENDING] /\
res_ok A2 (rawnew_rb (ng_b3 b attr ngp)))));
[ exact HS | reflexivity | exact HJ | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| unfold spZ; rewrite Hr2, unsigned_lit_small by lia; exact Hspm | unfold RAWNEW_STK, RAWNEW_FRAME; lia
| unfold spZ, RAWNEW_STK, RAWNEW_FRAME; rewrite Hr2, unsigned_lit_small by lia; lia
| unfold spZ; rewrite Hr2, unsigned_lit_small by lia; lia | exact Hr4
| ].
- intros HPRE1. eapply SR_mono.
{ eapply (RAWNEWX _ _ _ _ _ (sp0 - 80) g pal0 rattr W H sgct loops gvals f pala (3 * ngp) [] GPAL (ng_b3 b attr ngp) HPRE1 Hid Hr10);
[ exact Hcf8
| unfold spZ; rewrite Hr2, unsigned_lit_small by lia; lia | lia | exact Hrawcfg | exact Hrd | exact Hobj1 | reflexivity | reflexivity | exact Hgin
| exact Hfin | exact HSK1 | cbn; unfold SINK_MAX; lia | unfold spZ; rewrite Hr2, unsigned_lit_small by lia; lia
| | exact HRES | exact (ng_room4 b attr ngp HROOM Hngp3) ].
intros Hsg. assert (Hz4 : Z.land attr 4 = 0) by (rewrite Hsgct in Hsg; destruct (Z.eqb_spec (Z.land attr 4) 0); [assumption | lia]).
destruct (HGP1 Hz4) as (Hpin & HGa & HGn & _). rewrite Hsgct, Hz4. cbn [Z.eqb].
split; [eapply blocks_perm_in; [exact HB | right; apply in_app_iff; right; right; exact Hpin]|].
split; [exact Hpala|]. split; [lia|]. split; [| split; [exact HGa | lia]].
intros Heq. injection Heq as E1 E2. apply Hffresh. rewrite <- E1, <- E2. exact Hpin. }
cbv beta. intros c' (L4 & A4 & regs4 & mem4 & md4 & res2 & -> & HJc & HP4 & Hid4 & Hq10 & Hres).
exists L4, A4, regs4, mem4, md4. split; [rewrite Hr1; reflexivity|]. split; [exact HJc|]. split; [exact HP4|]. split; [exact Hid4|].
exists res2. split; [exact Hq10|]. cbn [app] in Hres. exact Hres.
-
intros a Ha. unfold sink_fp in Ha. apply inFP_cons in Ha. destruct Ha as [Ha | Ha].
+ left. split; [exists sink_token; split; [left; reflexivity | exact Ha] | unfold sink_token in Ha; cbn in Ha; lia].
+ apply inFP_cons in Ha. destruct Ha as [Ha | Ha]; [| exfalso; exact (inFP_nil a Ha)].
right. exists f, FILE_BLOCK. split; [exact Hfin|]. split; [exact Hffresh | lia]. }
cbv beta. intros c' (L4 & A4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & Hid4 & res2 & Hq10 & Hres). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc, HP4, Hq10.
assert (Hg4 : In (g, CGIF_SIZE) (blocks L4 A4)).
{ destruct Hres as [(_ & _ & Hbl & _) | (_ & _ & _ & (b1 & b2 & Hbl4 & Hblc) & _)]; [rewrite Hbl; exact Hgin|].
rewrite Hbl4. rewrite Hblc in Hgin. apply in_app_iff in Hgin. apply in_app_iff. destruct Hgin as [H0|H0]; [left; exact H0 | right; right; exact H0]. }
assert (Hf4 : In (f, FILE_BLOCK) (blocks L4 A4)).
{ destruct Hres as [(_ & _ & Hbl & _) | (_ & _ & _ & (b1 & b2 & Hbl4 & Hblc) & _)]; [rewrite Hbl; exact Hfin|].
rewrite Hbl4. pose proof Hfin as Hfin'. rewrite Hblc in Hfin'. apply in_app_iff in Hfin'. apply in_app_iff. destruct Hfin' as [H0|H0]; [left; exact H0 | right; right; exact H0]. }
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HH4.
pose proof HJc as (_ & _ & Hhi4 & Hblk4 & _).
assert (HE60 : ew E 60 = getr regs0 1) by (etransitivity; [apply (HSV 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HE61 : ew E 61 = getr regs0 8) by (etransitivity; [apply (HSV 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HE62 : ew E 62 = getr regs0 9) by (etransitivity; [apply (HSV 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HE63 : ew E 63 = getr regs0 18) by (etransitivity; [apply (HSV 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HE64 : ew E 64 = getr regs0 19) by (etransitivity; [apply (HSV 4%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
jafter_call_keep HS 68%nat regs4 mem4 HP4 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [exact HU2 | exact Hhi4 | lia | lia | unfold spZ; rewrite Hr2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 9); [exact HU18 | exact Hhi4 | lia | lia | unfold spZ; rewrite Hr2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; rewrite HU8; intros a Ha.
+ replace a with (g + (a - g)) by lia. apply (Hblk4 g CGIF_SIZE (a - g) Hgin Hg4); [lia |].
unfold sink_fp. intros Hin. apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [unfold sink_token in Hin; cbn in Hin; lia|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [lia | exact (inFP_nil _ Hin)].
+ intros _. apply (present_writable ubs0segs). replace a with (g + (a - g)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L4 A4 mem4 md4 g CGIF_SIZE (a - g) HH4 Hg4 ltac:(lia))). }
clear HS. rename HS2 into HS.
destruct Hres as [(-> & Hsg & Hbl & HSK4 & HR4) | (Hnz & Hsg & HSK4 & (b1 & b2 & Hbl4 & Hblc) & Hraw4 & HR4)].
-
pin_reg HS (10%bv:reg) 0 Hq10.
jrun_to LAWS ubs0tbl_ok HS HJ4 ubs0_A_fclose.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocF; exact HU8 | exact Hg4 | exact Hgfresh | cbn; lia | cbn; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hs10. rewrite (HE 18%nat 18%bv eq_refl), G9 in Hs10.
jreg HS (2%bv:reg) as Hs2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hs2.
jreg HS (4%bv:reg) as Hs4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hs4.
jreg HS (1%bv:reg) as Hs1.
assert (HB4 : Permutation (blocks L4 A4) ((f, FILE_BLOCK) :: (g, CGIF_SIZE) :: palblk ++ blocks L A)).
{ rewrite Hbl. eapply Permutation_trans; [exact HB|]. apply Permutation_sym.
apply (Permutation_middle ((g, CGIF_SIZE) :: palblk) (blocks L A) (f, FILE_BLOCK)). }
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := FCLOSE_STK) (FP1 := sink_fp f)
(K := fun L5 A5 (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) =>
getr regs5 10 = Z_to_bv 64 0 /\ Permutation (blocks L5 A5) ((g, CGIF_SIZE) :: palblk ++ blocks L A) /\
sink_none ubs0_msyms mem5 md5 /\ Fs.fs_lookup (m_fs md5) sink_path = Some (bytes []) /\ res_ok A5 (ng_b3 b attr ngp));
[ exact HS | reflexivity | exact HJ4 | exact Hs1 | | apply ret_ok_even; vm_compute; reflexivity
| unfold spZ; rewrite Hs2, unsigned_lit_small by lia; exact Hspm | unfold FCLOSE_STK; lia
| unfold spZ, FCLOSE_STK; rewrite Hs2, unsigned_lit_small by lia; lia
| unfold spZ; rewrite Hs2, unsigned_lit_small by lia; lia | exact Hs4 | ].
- intros HPRE2. eapply SR_mono.
{ eapply (ubs0_fcloseR API IMG AX L4 A4 _ _ md4 f [] ((g, CGIF_SIZE) :: palblk ++ blocks L A) (ng_b3 b attr ngp) HPRE2 Hid4);
[ unfold spZ; rewrite Hs2, unsigned_lit_small by lia; lia | exact Hs10 | exact HB4 | | exact HR4 ].
apply (sink_at_frame ubs0_msyms mem4 _ md4 f []); [|exact HSK4].
intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling /\ ~ (g <= a < g + 96))
by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); pose proof (Henvblk Lc Ac memc mdc g CGIF_SIZE a HH0 Hgin Ha); lia]).
mem_back ltac:(rewrite ?HU2, ?HU8, ?HU18) ltac:(lia). }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & Hr0 & HB5 & HSN5 & Hkey5 & HR5).
exists L5, A5, regs5, mem5, md5. split; [rewrite Hs1; reflexivity|]. split; [exact HJc5|]. split; [exact HP5|].
split; [exact Hr0|]. split; [exact HB5|]. split; [exact HSN5|]. split; [exact Hkey5 | exact HR5].
- intros a Ha. unfold sink_fp in Ha. apply inFP_cons in Ha. destruct Ha as [Ha | Ha].
+ left. split; [exists sink_token; split; [left; reflexivity | exact Ha] | unfold sink_token in Ha; cbn in Ha; lia].
+ apply inFP_cons in Ha. destruct Ha as [Ha | Ha]; [| exfalso; exact (inFP_nil a Ha)].
right. exists f, FILE_BLOCK. split; [exact Hf4|]. split; [exact Hffresh | lia]. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & Hr0 & HB5 & HSN5 & Hkey5 & HR5). clear HJ4.
cbn [ms_regs ms_mem mkst] in HJc5, HP5, Hr0.
pose proof HJc5 as (_ & _ & Hhi5 & Hblk5 & _).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as HH5.
assert (Hg5 : In (g, CGIF_SIZE) (blocks L5 A5)) by (eapply blocks_perm_in; [exact HB5 | left; reflexivity]).
jafter_call_keep HS 84%nat regs5 mem5 HP5 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocF; exact HU2 | exact Hhi5 | lia | lia | unfold spZ; rewrite Hs2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs0segs _ _ _ 9); [ew_havocF; exact HU18 | exact Hhi5 | lia | lia | unfold spZ; rewrite Hs2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocF; rewrite HU8; intros a Ha.
+ replace a with (g + (a - g)) by lia. apply (Hblk5 g CGIF_SIZE (a - g) Hg4 Hg5); [lia |].
unfold sink_fp. intros Hin. apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [unfold sink_token in Hin; cbn in Hin; lia|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [lia | exact (inFP_nil _ Hin)].
+ intros _. apply (present_writable ubs0segs). replace a with (g + (a - g)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L5 A5 mem5 md5 g CGIF_SIZE (a - g) HH5 Hg5 ltac:(lia))). }
clear HS. rename HS2 into HS.
jrun_to LAWS ubs0tbl_ok HS HJ5 ubs0_A_freeCGIF.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocF; exact HU8 | exact Hg5 | exact Hgfresh | cbn; lia | cbn; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hk10. rewrite (HE 8%nat 8%bv eq_refl), G8 in Hk10.
jreg HS (2%bv:reg) as Hk2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hk2.
jreg HS (4%bv:reg) as Hk4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hk4.
jreg HS (1%bv:reg) as Hk1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hobj2 : obj_at ubs0segs (ms_mem msx) g LAY_CGIF gvals)
end.
{ eapply (st_obj_at ubs0segs _ _ _ 2%nat _ 8%nat g LAY_CGIF gvals 43 lits_CGIF0 HS eq_refl eq_refl ltac:(ew_havocF; exact HU8)).
- apply incl_chunks_sound. vm_compute. reflexivity.
- reflexivity.
- reflexivity.
- intros j v Hj. split; [exact (Robj j v Hj)|].
assert (Hlj : (j < 17)%nat) by (destruct (Nat.lt_ge_cases j 17) as [Hl|Hl]; [exact Hl|]; rewrite (proj2 (nth_error_None gvals j) Hl) in Hj; discriminate).
do 17 (try (destruct j as [|j]; [cbn [nth_error lits_CGIF0]; first [ew_havocF; apply (HG _ _ Hj) | subst gvals; cbn in Hj; congruence] | ])). lia. }
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := FREECGIF_STK) (FP1 := fp_freeCGIF g attr pal' (3 * ngp))
(K := fun L6 A6 (regs6 : bvmap 5 word) (mem6 : word -> option byte) (md6 : Model) =>
Permutation (blocks L6 A6) (blocks L A) /\ st_init_done A6 = true /\ res_ok A6 (ng_b3 b attr ngp));
[ exact HS | reflexivity | exact HJ5 | exact Hk1 | | apply ret_ok_even; vm_compute; reflexivity
| unfold spZ; rewrite Hk2, unsigned_lit_small by lia; exact Hspm | unfold FREECGIF_STK; lia
| unfold spZ, FREECGIF_STK; rewrite Hk2, unsigned_lit_small by lia; lia
| unfold spZ; rewrite Hk2, unsigned_lit_small by lia; lia | exact Hk4 | ].
- intros HPRE3. eapply SR_mono.
{ eapply (ubs0_freeCGIF_res API IMG _ _ _ _ _ g gvals attr pal' (3 * ngp) (blocks L A) (ng_b3 b attr ngp) HPRE3 Hk10 Hobj2 eq_refl eq_refl); [| exact HR5].
unfold gpals_of. rewrite <- Hpalblk. exact HB5. }
cbv beta. intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJc6 & HP6 & HB6 & Hid6 & HR6).
exists L6, A6, regs6, mem6, md6. split; [rewrite Hk1; reflexivity|]. split; [exact HJc6|]. split; [exact HP6|]. split; [exact HB6|]. split; [exact Hid6 | exact HR6].
-
intros a Ha. right. unfold fp_freeCGIF in Ha. apply inFP_cons in Ha. destruct Ha as [Ha | Ha].
+ exists g, CGIF_SIZE. split; [exact Hg5|]. split; [exact Hgfresh | lia].
+ destruct (Z.eqb_spec (Z.land attr 4) 0) as [Hz4|Hz4]; [| exfalso; exact (inFP_nil a Ha)].
apply inFP_cons in Ha. destruct Ha as [Ha | Ha]; [| exfalso; exact (inFP_nil a Ha)].
exists pal', (3 * ngp).
assert (Hpin : In (pal', 3 * ngp) (blocks L5 A5)) by (eapply blocks_perm_in; [exact HB5 | right; rewrite Hpalblk; left; reflexivity]).
split; [exact Hpin|]. split; [| lia].
intros Hin. pose proof (Hpalfresh (pal', 3 * ngp) ltac:(rewrite Hpalblk; left; reflexivity) Hin) as Hle. cbn [snd] in Hle. lia. }
cbv beta. intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJ6 & HJc6 & HP6 & HB6 & Hid6 & HR6). clear HJ5.
cbn [ms_regs ms_mem mkst] in HJc6, HP6.
pose proof HJc6 as (_ & Hos6 & Hhi6 & _).
assert (Hnotok : ~ sink_open_fp (fp_freeCGIF g attr pal' (3 * ngp))).
{ unfold sink_open_fp, fp_freeCGIF. intros Hin. apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [lia|].
destruct (Z.land attr 4 =? 0); [| exact (inFP_nil _ Hin)]. apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [| exact (inFP_nil _ Hin)].
assert (Hpin : In (pal', 3 * ngp) (blocks L5 A5)) by (eapply blocks_perm_in; [exact HB5 | right; rewrite Hpalblk; left; reflexivity]).
destruct (blocks_range _ _ LAWS L5 A5 mem5 md5 pal' (3 * ngp) HH5 Hpin). lia. }
assert (HSN6 : sink_none ubs0_msyms mem6 md6).
{ eapply (sink_none_kept ubs0_msyms MR); [exact HJc6 | exact Hnotok |].
eapply (sink_none_frame ubs0_msyms mem5); [| exact HSN5]. intros a Ha. pose proof (ubs0_env_addr_range a Ha).
pose proof (Henvblk L5 A5 mem5 md5 g CGIF_SIZE a HH5 Hg5 Ha).
mem_back ltac:(rewrite ?HU2, ?HU8, ?HU18) ltac:(lia). }
destruct (os_step_shielded _ md5 md6 Hos6 Hnotok) as (_ & Hfs6 & _).
jafter_call_keep HS 100%nat regs6 mem6 HP6 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocF; exact HU2 | exact Hhi6 | lia | lia | unfold spZ; rewrite Hk2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun LAWS ubs0tbl_ok HS HJ6.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ6))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ6)))). }
apply (KB0 Hsg). unfold newgif_postB0.
lazymatch type of HS with st_ok _ _ _ ?msf => exists L6, A6, (ms_regs msf), (ms_mem msf), md6 end.
split. { cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg ubs0segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
repeat (rewrite ew_havoc_old in Q1; [|nat_lt_lit]); rewrite ?Z.add_0_r, HE60, Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra0; reflexivity end. }
split; [exact HJ6|].
split.
{ apply regs_preserved_intro; cbn [ms_regs mkst].
- reg_nowF HS ltac:(rewrite HU2; replace (sp0 - 80 + 80) with sp0 by lia; subst sp0; unfold spZ; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
- reg_nowF HS ltac:(rewrite HE61; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HE62; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HE63; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HE64; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 20%nat 20%bv eq_refl); exact G20).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27). }
split; [exact Hid6|].
split; [reg_nowF HS ltac:(reflexivity)|].
split; [exact HB6|].
split.
{ eapply (sink_none_frame ubs0_msyms mem6); [| exact HSN6]. intros a Ha. pose proof (ubs0_env_addr_range a Ha).
mem_back ltac:(rewrite ?HU2, ?HU8, ?HU18) ltac:(lia). }
split; [exact Hfs6 || (rewrite Hfs6; exact Hkey5)|].
eapply res_ok_mono; [apply (ng_b3_fin b attr ngp Hngp3) | exact HR6].
-
assert (Hr2in : In (res2, RAW_SIZE) (blocks L4 A4)) by (rewrite Hbl4; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS L4 A4 mem4 md4 res2 RAW_SIZE HH4 Hr2in ltac:(unfold RAW_SIZE; lia)) as (Hq0 & Hq1 & Hq16).
unfold RAW_SIZE in Hq1.
jreg HS (10%bv:reg) as Hq72. cbn [ms_regs mkst] in Hq72. rewrite Hq10 in Hq72. symmetry in Hq72.
add_fact HS 72%nat (mkAF 4096 (CEIL_MAX - 48) 4).
2:{ rewrite Hq72, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
assert (Hsep_gq : g + CGIF_SIZE <= res2 \/ res2 + 48 <= g).
{ destruct (heap_sep _ _ LAWS L4 A4 mem4 md4 b1 (res2, RAW_SIZE) b2 (g, CGIF_SIZE) HH4 Hbl4 ltac:(rewrite <- Hblc; exact Hgin)) as [H0|H0]; cbn [fst snd] in H0; unfold RAW_SIZE in *; lia. }
assert (Hsep_gf : g + CGIF_SIZE <= f \/ f + FILE_BLOCK <= g) by lia.
jrun LAWS ubs0tbl_ok HS HJ4.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocF; exact HU8 | exact Hg4 | exact Hgfresh | cbn; lia | cbn; lia |]. apply wr_ok_nil. }
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ4))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ4)))). }
apply (KB1 Hsg). unfold newgif_postB1.
lazymatch type of HS with st_ok _ _ _ ?msf => exists L4, A4, (ms_regs msf), (ms_mem msf), md4, g end.
exists (mkCgif [None; None; None] pal' attr gen W H ngp loops res2 R_PENDING 1 pal0 rattr loops R_PENDING f).
split. { cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg ubs0segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
repeat (rewrite ew_havoc_old in Q1; [|nat_lt_lit]); rewrite ?Z.add_0_r, HE60, Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra0; reflexivity end. }
split; [exact HJ4|].
split.
{ apply regs_preserved_intro; cbn [ms_regs mkst].
- reg_nowF HS ltac:(rewrite HU2; replace (sp0 - 80 + 80) with sp0 by lia; subst sp0; unfold spZ; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
- reg_nowF HS ltac:(rewrite HE61; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HE62; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HE63; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HE64; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 20%nat 20%bv eq_refl); exact G20).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27). }
split; [exact Hid4|].
split; [reg_nowF HS ltac:(rewrite HU8; reflexivity)|].
split; [lia|].
cbn [cg_frames cg_W cg_H cg_attr cg_cur cg_ihead cg_gen cg_ngp].
split.
{
unfold cgif_at. cbn [cgif_vals raw_vals raw_sgct cg_frames cg_pal cg_attr cg_gen cg_W cg_H cg_ngp cg_loops cg_raw cg_cur cg_ihead rw_gct rw_attr rw_loops rw_cur cg_file nth frame_ptr].
split; [|split].
- unfold cgif_vals. cbn [cg_frames cg_pal cg_attr cg_gen cg_W cg_H cg_ngp cg_loops cg_raw cg_cur cg_ihead cg_file nth frame_ptr].
change LAY_CGIF with ([(0, 8%N); (8, 8%N); (16, 8%N); (24, 8%N); (32, 8%N); (40, 4%N); (44, 4%N); (48, 2%N); (50, 2%N); (52, 2%N); (54, 2%N); (56, 8%N); (64, 8%N)]
++ [(72, 8%N)] ++ [(80, 8%N); (88, 4%N); (92, 4%N)]).
change [0; 0; 0; pal'; ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; loops; 0; 0; res2; f; R_PENDING; 1]
with ([0; 0; 0; pal'; ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; loops; 0; 0] ++ [res2] ++ [f; R_PENDING; 1]).
rewrite obj_at_app by reflexivity. cbn [ms_mem mkst]. split.
+ eapply (st_obj_at ubs0segs _ _ _ 2%nat _ 8%nat g _ _ 43 (firstn 13 lits_CGIF0) HS eq_refl eq_refl ltac:(ew_havocF; exact HU8)).
* apply incl_chunks_sound. vm_compute. reflexivity.
* reflexivity.
* reflexivity.
* intros j v Hj.
assert (Hlj : (j < 13)%nat) by (destruct (Nat.lt_ge_cases j 13) as [Hl|Hl]; [exact Hl|]; rewrite (proj2 (nth_error_None [0; 0; 0; pal'; ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; loops; 0; 0] j) Hl) in Hj; discriminate).
assert (Hj' : nth_error gvals j = Some v) by (subst gvals; do 13 (destruct j as [|j]; [exact Hj|]); lia).
split; [| do 13 (try (destruct j as [|j]; [cbn [nth_error lits_CGIF0 firstn]; first [ew_havocF; apply (HG _ _ Hj') | cbn in Hj; congruence] | ])); lia].
pose proof (Robj j v Hj') as R. do 13 (destruct j as [|j]; [exact R|]). lia.
+ rewrite obj_at_app by reflexivity. split.
* cbn [obj_at]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
split; [split; [ eapply (st_chunk_val _ _ _ _ 2%nat _ 8%nat 72 8%N (SOff 72 0) _ _ HS);
[reflexivity | reflexivity | cbv; auto 40 | ew_havocF; exact HU8
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, Hq72, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia ]
| cbn; lia ] | exact I].
* eapply (st_obj_at ubs0segs _ _ _ 2%nat _ 8%nat g _ _ 57 [None; Some R_PENDING; Some 1] HS eq_refl eq_refl ltac:(ew_havocF; exact HU8)).
-- apply incl_chunks_sound. vm_compute. reflexivity.
-- reflexivity.
-- reflexivity.
-- intros j v Hj. destruct j as [|[|[|j]]]; cbn in Hj; [injection Hj as <- | injection Hj as <- | injection Hj as <- | destruct j; discriminate Hj]; cbn [snd nth nth_error Z.of_N].
++ split; [change (2 ^ (8 * 8)) with (2 ^ 64); lia | rewrite Nat.add_0_r; ew_havocF; apply (HG 14%nat f eq_refl)].
++ split; [lit_range | reflexivity].
++ split; [lit_range | reflexivity].
- unfold raw_vals, raw_sgct. cbn [cg_frames cg_pal cg_attr cg_gen cg_W cg_H cg_ngp cg_loops cg_raw cg_cur cg_ihead rw_gct rw_attr rw_loops rw_cur]. rewrite <- Hsgct. cbn [ms_mem mkst].
eapply obj_at_transport_range; [exact Hraw4 | exact (proj1 LAY_Raw_ok) |].
intros i Hi. unfold RAW_SIZE in Hi. cbn [ms_mem mkst] in HF0. mb_frame_with HF0 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity.
- intros fr Hf. exfalso. destruct Hf as [H0|[H0|[H0|[]]]]; discriminate H0. }
split.
{ unfold cgif_wf. cbn [cg_frames cg_W cg_H cg_attr cg_ngp cg_ihead length].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [lia|].
split; [intros Hz4; rewrite Hsgct in Hsg; rewrite Hz4 in Hsg; cbn [Z.eqb] in Hsg; lia|].
split; [left; reflexivity|].
intros fr Hf. exfalso. destruct Hf as [H0|[H0|[H0|[]]]]; discriminate H0. }
do 8 (split; [reflexivity|]).
split.
{
unfold cgif_blocks, pal_blocks. cbn [cg_raw cg_attr cg_pal cg_ngp cg_frames cg_file frames_blocks flat_map app].
rewrite app_nil_r. rewrite <- Hpalblk. rewrite Hbl4.
eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
cbn [app]. eapply Permutation_trans; [| apply perm_swap]. apply perm_skip. rewrite <- Hblc.
eapply Permutation_trans; [exact HB|]. apply perm_skip.
apply Permutation_sym. apply (Permutation_middle palblk (blocks L A) (f, FILE_BLOCK)). }
split.
{
unfold cgif_rel, cgif_live, gs_new. cbn [cg_cur cg_file rw_cur rw_attr cg_attr cg_ihead cg_pal cg_ngp cg_frames nth
YO07.s_cur YO07.s_out YO07.s_rcur YO07.s_ihead YO07.s_q0 YO07.s_q1 YO07.s_q2 concat oframe_relb].
split; [split; [reflexivity | unfold cgif_occ; cbn [cg_frames nth YO07.s_q0 YO07.s_q1 YO07.s_q2]; tauto]|].
split.
{ rewrite app_nil_r. cbn [ms_mem mkst].
replace (if YO07.flag attr 4 then 0 else ngp) with sgct by (rewrite Hsgct; unfold YO07.flag; destruct (Z.land attr 4 =? 0); reflexivity).
rewrite <- Hrattr.
apply (sink_at_frame ubs0_msyms mem4 _ md4 f _); [|exact HSK4].
intros a Ha. assert (Ha' : 0 <= a < alloc_ceiling /\ ~ (g <= a < g + 96))
by (destruct Ha as [Ha|Ha]; [lia | pose proof (ubs0_env_addr_range a Ha); pose proof (Henvblk Lc Ac memc mdc g CGIF_SIZE a HH0 Hgin Ha); lia]).
cbn [ms_mem mkst] in HF0. mb_frame_with HF0 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity. }
intros _. split; [reflexivity|]. split; [exact Hrattr|]. split; [reflexivity|].
split; [| repeat split; exact I].
intros Hz4. destruct (HGP1 Hz4) as (Hpin & HGa & HGn & HGc). split; [|exact HGn].
assert (Hpcin : In (pal', 3 * ngp) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | right; rewrite Hpalblk, Hz4; left; reflexivity]).
assert (Hpc4 : In (pal', 3 * ngp) (blocks L4 A4)).
{ rewrite Hbl4. rewrite Hblc in Hpcin. apply in_app_iff in Hpcin. apply in_app_iff. destruct Hpcin as [H0|H0]; [left; exact H0 | right; right; exact H0]. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pal' (3 * ngp) HH0 Hpcin) as [Rc0 Rc1].
assert (Hsep_gc : g + CGIF_SIZE <= pal' \/ pal' + 3 * ngp <= g).
{ pose proof (heap_sep_perm _ _ LAWS Lc Ac memc mdc (g, CGIF_SIZE) _ (pal', 3 * ngp) HH0 HB ltac:(apply in_app_iff; left; rewrite Hpalblk, Hz4; left; reflexivity)) as X. cbn [fst snd] in X. lia. }
eapply YI00.garr8_frame; [exact HGc|]. intros a Ha. rewrite HGn in Ha. cbn [ms_mem mkst].
transitivity (mbyte ubs0segs mem4 a).
{ cbn [ms_mem mkst] in HF0. mb_frame_with HF0 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity. }
assert (Hsep_cf : pal' + 3 * ngp <= f \/ f + FILE_BLOCK <= pal').
{ assert (HBp : Permutation (blocks Lc Ac) ((pal', 3 * ngp) :: (g, CGIF_SIZE) :: (f, FILE_BLOCK) :: blocks L A)).
{ eapply Permutation_trans; [exact HB|]. rewrite Hpalblk, Hz4. cbn [Z.eqb app]. apply perm_swap. }
destruct (heap_sep_perm _ _ LAWS Lc Ac memc mdc (pal', 3 * ngp) _ (f, FILE_BLOCK) HH0 HBp ltac:(right; left; reflexivity)) as [X|X]; cbn [fst snd] in X; lia. }
replace a with (pal' + (a - pal')) by lia. apply (Hblk4 pal' (3 * ngp) (a - pal') Hpcin Hpc4); [lia|].
unfold sink_fp. intros Hin. apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [unfold sink_token in Hin; cbn in Hin; lia|].
apply inFP_cons in Hin. destruct Hin as [Hin|Hin]; [lia | exact (inFP_nil _ Hin)]. }
split.
{ unfold gs_new. cbn [YO07.s_out concat]. rewrite app_nil_r. eapply Z.le_trans; [apply raw_header_length|]; [| unfold HDR_OUT; lia].
rewrite Hsgct in Hsg. unfold YO07.flag. destruct (Z.land attr 4 =? 0); cbn [negb]; lia. }
eapply res_ok_mono; [apply (ng_fin_ok b attr ngp Hngp3) | exact HR4].
Qed.
End S.
End h.
