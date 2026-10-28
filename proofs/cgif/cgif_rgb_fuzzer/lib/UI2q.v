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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m YI00 YI02 YI01 YI03
UI1e UI39 UI1i UI59 UI56 YI0x.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac lit_range := lazymatch goal with |- (_ <= _ < _)%Z => vm_compute; split; [let HH := fresh in intros HH; discriminate HH | reflexivity] end.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition NG_TAIL : Z := Eval vm_compute in (ubs2_A_cgif_newgif + 0x11c).
Definition NG_RAWRET : Z := Eval vm_compute in (ubs2_A_cgif_newgif + 0x160).
Definition NG_FREED : Z := Eval vm_compute in (ubs2_A_cgif_newgif + 0x1a8).
Definition lits_Config : list (option Z) :=
[None; Some 0; None; None; None; None; None; None; Some ubs2_A_writecb; Some 0].
Definition lits_CGIF0 : list (option Z) :=
[Some 0; Some 0; Some 0; None; Some 0; None; None; None; None; None; None; Some ubs2_A_writecb; Some 0; Some 0; Some 0; Some 0; Some 1].
Definition cfg_chunks : list YQ0b.chunk :=
[mkChunk 0 (CVal 8 (SOff 32 0)); mkChunk 8 (CVal 8 (SLit 0)); mkChunk 16 (CVal 4 (SOff 34 0)); mkChunk 20 (CVal 4 (SOff 35 0));
mkChunk 24 (CVal 4 (SOff 42 0)); mkChunk 28 (CVal 2 (SOff 38 0)); mkChunk 30 (CVal 2 (SOff 39 0));
mkChunk 32 (CVal 8 (SLit ubs2_A_writecb)); mkChunk 40 (CVal 8 (SLit 0))].
Definition ss_ngt : sstate :=
mkSS NG_TAIL (sr_set sr_atoms 18%bv (SLit 0))
[ YQ0b.mkRegion (Some 2%nat) 0 80 0 80
[mkChunk 0 (CZero 16); mkChunk 16 (CVal 8 (SOff 32 0)); mkChunk 24 (CZero 16);
mkChunk 72 (CVal 8 (SOff 60 0)); mkChunk 64 (CVal 8 (SOff 61 0)); mkChunk 56 (CVal 8 (SOff 62 0)); mkChunk 48 (CVal 8 (SOff 63 0));
mkChunk 40 (CVal 8 (SOff 64 0))];
YQ0b.mkRegion (Some 9%nat) 0 48 0 0 cfg_chunks;
YQ0b.mkRegion (Some 8%nat) 0 CGIF_SIZE 0 CGIF_SIZE (obj_chunks_gen LAY_CGIF 43 lits_CGIF0) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + NEWGIF_STK - 80) (2^63 - 80) 4);
(8%nat, mkAF 4096 (CEIL_MAX - CGIF_SIZE) 4);
(9%nat, mkAF CEIL_MIN (2^63 - 48) 3);
(11%nat, mkAF 0 65535 0);
(34%nat, mkAF 0 (2^32 - 1) 0); (36%nat, mkAF 1 65535 0); (37%nat, mkAF 1 65535 0);
(38%nat, mkAF 0 65535 0); (39%nat, mkAF 0 65535 0); (42%nat, mkAF 0 (2^32 - 1) 0) ] [] []).
Definition ss_ngt_c : sstate := Eval vm_compute in ss_ngt.
Lemma lits_Config_ok : forall pal0 attr gen W H ngp loops,
forall j z, nth_error lits_Config j = Some (Some z) ->
nth_error [pal0; 0; attr; gen; W; H; ngp; loops; ubs2_A_writecb; 0] j = Some z.
Proof.
intros pal0 attr gen W H ngp loops j z Hj. do 10 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; reflexivity] |]).
destruct j; discriminate Hj.
Qed.
Lemma lits_CGIF0_ok : forall pal' attr gen W H ngp loops,
forall j z, nth_error lits_CGIF0 j = Some (Some z) ->
nth_error [0; 0; 0; pal'; 0; attr; gen; W; H; ngp; loops; ubs2_A_writecb; 0; 0; 0; 0; 1] j = Some z.
Proof.
intros pal' attr gen W H ngp loops j z Hj. do 17 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; reflexivity] |]).
destruct j; discriminate Hj.
Qed.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition newgif_post (regs0 : bvmap 5 word) L A mem md (W H attr : Z) (c' : config) : Prop :=
exists L' A' regs' mem' md' (res : Z),
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom ubs2segs)) md' /\
journal ubs2_msyms MR NEWGIF_STK (spZ regs0) [] L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\
getr regs' 10 = Z_to_bv 64 res /\
((res = 0 /\ exists leak, Permutation (blocks L' A') (leak ++ blocks L A)) \/
(res <> 0 /\ exists s,
cgif_at mem' res s /\ cgif_wf s (W * H) /\
cg_frames s = [None; None; None] /\ cg_W s = W /\ cg_H s = H /\ cg_attr s = attr /\
cg_cur s = R_PENDING /\ cg_ihead s = 1 /\
Permutation (blocks L' A') (cgif_blocks res s (W * H) ++ blocks L A))).
Lemma newgif_tail :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc
(cfgp pal0 attr gen W H ngp loops g pal' sgct : Z) (palblk : list (Z * Z)),
journal ubs2_msyms MR NEWGIF_STK (spZ regs0) [] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) -> spZ regs0 mod 16 = 0 ->
cfgp mod 8 = 0 -> spZ regs0 <= cfgp -> cfgp + 48 <= 2 ^ 63 ->
obj_at ubs2segs memc cfgp LAY_Config [pal0; 0; attr; gen; W; H; ngp; loops; ubs2_A_writecb; 0] ->
1 <= W -> 1 <= H -> W * H <= 100000000 ->
obj_at ubs2segs memc g LAY_CGIF [0; 0; 0; pal'; 0; attr; gen; W; H; ngp; loops; ubs2_A_writecb; 0; 0; 0; 0; 1] ->
Permutation (blocks Lc Ac) ((g, CGIF_SIZE) :: palblk ++ blocks L A) ->
palblk = (if Z.land attr 4 =? 0 then [(pal', 3 * ngp)] else []) ->
~ In (g, CGIF_SIZE) (blocks L A) ->
(forall b, In b palblk -> In b (blocks L A) -> snd b <= 0) ->
sgct = (if Z.land attr 4 =? 0 then ngp else 0) ->
(forall i, 0 <= i < 40 -> ~ (16 <= i < 24) -> mbyte ubs2segs memc (spZ regs0 - 80 + i) = Some (Z_to_bv 8 0)) ->
word_mem ubs2segs memc (spZ regs0 - 64) pal0 ->
word_mem ubs2segs memc (spZ regs0 - 8) (bv_unsigned (getr regs0 1)) ->
word_mem ubs2segs memc (spZ regs0 - 16) (bv_unsigned (getr regs0 8)) ->
word_mem ubs2segs memc (spZ regs0 - 24) (bv_unsigned (getr regs0 9)) ->
word_mem ubs2segs memc (spZ regs0 - 32) (bv_unsigned (getr regs0 18)) ->
word_mem ubs2segs memc (spZ regs0 - 40) (bv_unsigned (getr regs0 19)) ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 80) -> getr regs1 8 = Z_to_bv 64 g -> getr regs1 9 = Z_to_bv 64 cfgp ->
getr regs1 18 = Z_to_bv 64 0 -> getr regs1 11 = Z_to_bv 64 sgct ->
getr regs1 3 = getr regs0 3 -> getr regs1 4 = getr regs0 4 ->
getr regs1 20 = getr regs0 20 -> getr regs1 21 = getr regs0 21 -> getr regs1 22 = getr regs0 22 ->
getr regs1 23 = getr regs0 23 -> getr regs1 24 = getr regs0 24 -> getr regs1 25 = getr regs0 25 ->
getr regs1 26 = getr regs0 26 -> getr regs1 27 = getr regs0 27 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 NG_TAIL) memc (seg_rom ubs2segs)) mdc)
(newgif_post regs0 L A mem md W H attr).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc cfgp pal0 attr gen W H ngp loops g pal' sgct palblk
HJ Hid Hra0 Htp0 Hal16 Hcal Hclo Hchi Hcfg HW HH HWH Hobj HB Hpalblk Hgfresh Hpalfresh Hsgct
Hz Wpal W1 W8 W9 W18 W19
G2 G8 G9 G18 G11 G3 G4 G20 G21 G22 G23 G24 G25 G26 G27.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HSTKv : NEWGIF_STK = 9216) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs0) in *.
assert (Hgin : In (g, CGIF_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc g CGIF_SIZE HH0 Hgin ltac:(lia)) as (Hg0 & Hg1 & Hg16).
pose proof (obj_at_range _ _ _ _ _ Hcfg) as Rcfg. pose proof (obj_at_range _ _ _ _ _ Hobj) as Robj.
pose proof (Rcfg 0%nat pal0 eq_refl) as Rpal0. pose proof (Rcfg 2%nat attr eq_refl) as Rattr. pose proof (Rcfg 3%nat gen eq_refl) as Rgen.
pose proof (Rcfg 4%nat W eq_refl) as RW. pose proof (Rcfg 5%nat H eq_refl) as RH. pose proof (Rcfg 6%nat ngp eq_refl) as Rngp.
pose proof (Rcfg 7%nat loops eq_refl) as Rloops. pose proof (Robj 3%nat pal' eq_refl) as Rpal'.
cbn in Rpal0, Rattr, Rgen, RW, RH, Rngp, Rloops, Rpal'.
assert (Rsgct : 0 <= sgct < 65536) by (rewrite Hsgct; destruct (Z.land attr 4 =? 0); lia).
set (cvals := [pal0; 0; attr; gen; W; H; ngp; loops; ubs2_A_writecb; 0]) in *.
set (gvals := [0; 0; 0; pal'; 0; attr; gen; W; H; ngp; loops; ubs2_A_writecb; 0; 0; 0; 0; 1]) in *.
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
assert (HU18 : bv_unsigned (ew E 9) = cfgp) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HE11 : ew E 11 = Z_to_bv 64 sgct) by (rewrite (HE 11%nat 11%bv eq_refl); exact G11).
assert (HX42 : ew E 42 = Z_to_bv 64 (W + 65536 * H)) by (apply (HY 0%nat); reflexivity).
assert (HX32 : ew E 32 = Z_to_bv 64 pal0) by (apply (HX 0%nat); reflexivity).
assert (HX34 : ew E 34 = Z_to_bv 64 attr) by (apply (HX 2%nat); reflexivity).
assert (HX35 : ew E 35 = Z_to_bv 64 gen) by (apply (HX 3%nat); reflexivity).
assert (HX36 : ew E 36 = Z_to_bv 64 W) by (apply (HX 4%nat); reflexivity).
assert (HX37 : ew E 37 = Z_to_bv 64 H) by (apply (HX 5%nat); reflexivity).
assert (HX38 : ew E 38 = Z_to_bv 64 ngp) by (apply (HX 6%nat); reflexivity).
assert (HX39 : ew E 39 = Z_to_bv 64 loops) by (apply (HX 7%nat); reflexivity).
assert (HS : st_ok ubs2segs E ss_ngt_c (mkst regs1 (Z_to_bv 64 NG_TAIL) memc (seg_rom ubs2segs))).
{ change ss_ngt_c with ss_ngt. unfold ss_ngt. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros H0; discriminate H0 |]. cbn [sv_denot]. exact G18.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_cons. { apply chunk_ok_zero. cbn [c_off]. intros i Hi. replace (sp0 - 80 + 0 + i) with (sp0 - 80 + i) by lia. apply Hz; lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pal0); [cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; replace (sp0 - 80 + 16) with (sp0 - 64) by lia; exact Wpal]. }
apply Forall_cons. { apply chunk_ok_zero. cbn [c_off]. intros i Hi. replace (sp0 - 80 + 24 + i) with (sp0 - 80 + (24 + i)) by lia. apply Hz; lia. }
assert (CK : forall off j (w : Z), nth_error svals j = Some w -> word_mem ubs2segs memc (sp0 - 80 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs2segs (Ereg regs1 (map (Z_to_bv 64) cvals ++ map (Z_to_bv 64) ((W + 65536 * H) :: gvals ++ svals) ++ [])) memc (sp0 - 80) (mkChunk off (CVal 8 (SOff (60 + j) 0)))).
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
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [reflexivity | cbn; lia | cbn; lia | exact F1]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ attr); [cbn [sv_denot]; rewrite Z.add_0_r, HX34, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F2]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ gen); [cbn [sv_denot]; rewrite Z.add_0_r, HX35, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F3]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (W + 65536 * H)); [cbn [sv_denot]; rewrite Z.add_0_r, HX42, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_wh_join; [exact F4 | replace (cfgp + 24 + 2) with (cfgp + 26) by lia; exact F5 | lia | lia]]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ ngp); [cbn [sv_denot]; rewrite Z.add_0_r, HX38, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F6]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ loops); [cbn [sv_denot]; rewrite Z.add_0_r, HX39, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F7]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ ubs2_A_writecb); [reflexivity | unfold ubs2_A_writecb; cbn; lia | cbn; lia | exact F8]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [reflexivity | cbn; lia | cbn; lia | exact F9]. }
apply Forall_nil.
+
eapply (region_ok_obj_gen ubs2segs _ memc 8 g); [exact HU8 | lia | lia | exact Hobj | reflexivity | | apply lits_CGIF0_ok | ].
* intros j v Hj. apply (HG j v Hj).
* intros i Hi. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc g CGIF_SIZE i HH0 Hgin ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU8, HU18. repeat split; lia.
- split; [|split; constructor].
cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU8, HU18, HE11, HX34, HX36, HX37, HX38, HX39, HX42,
!unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert (Hspm : (sp0 - 80) mod 16 = 0) by (replace (sp0 - 80) with (sp0 + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hcf8 : (sp0 - 80) mod 8 = 0).
{ pose proof (proj2 (Z.div_exact sp0 16 ltac:(lia)) Hal16) as E16.
replace (sp0 - 80) with ((2 * (sp0 / 16) - 10) * 8) by lia. apply Z_mod_mult. }
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 NG_TAIL) memc (seg_rom ubs2segs))) in HJ.
assert (Hspm : (sp0 - 80) mod 16 = 0) by (replace (sp0 - 80) with (sp0 + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hcf8 : (sp0 - 80) mod 8 = 0).
{ pose proof (proj2 (Z.div_exact sp0 16 ltac:(lia)) Hal16) as E16.
replace (sp0 - 80) with ((2 * (sp0 / 16) - 10) * 8) by lia. apply Z_mod_mult. }
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_cgif_raw_newgif.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_tmp; [reflexivity | exact HU8 | exact Hgin | exact Hgfresh | cbn; lia | cbn; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hr10. rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 2)), HU2 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hrawcfg : exists rattr, obj_at ubs2segs (ms_mem msx) (sp0 - 80) LAY_RawConfig [ubs2_A_cgif_writecb; g; pal0; rattr; W; H; sgct; loops]
/\ 0 <= rattr < 2 ^ 32)
end.
{ pose proof (st_region_chunks ubs2segs _ _ _ 0%nat _ 2%nat (sp0 - 80) HS eq_refl eq_refl HU2) as HC.
cbn [r_chunks] in HC.
repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC as [?CC HC] end.
lazymatch type of CC2 with chunk_ok _ ?E1 _ _ (mkChunk 24 (CVal 4 ?e)) =>
exists (bv_unsigned (sv_denot E1 e) mod 2 ^ 32) end.
split; [| apply Z.mod_pos_bound; lia].
cbn [obj_at LAY_RawConfig]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
assert (Vwh : val_mem ubs2segs (ms_mem ms) (sp0 - 80 + 28) 4 (W + 65536 * H)).
{ pose proof (val_mem_low_of_chunk _ _ _ _ _ 4%N _ CC1 ltac:(cbn; lia)) as V.
replace (bv_unsigned (sv_denot _ (SExt true 32 (SOff 42 0))) mod 2 ^ (8 * Z.of_N 4)) with (W + 65536 * H) in V; [exact V|].
change (bv_unsigned (sv_denot E (SExt true 32 (SOff 42 0)))) with (U E (SExt true 32 (SOff 42 0))).
rewrite U_SExt, (U_atom _ 42 (W + 65536 * H) HX42) by lia. change (8 * Z.of_N 4) with 32. symmetry. apply sext32_low. lia. }
destruct (val_mem_wh_split _ _ _ _ _ Vwh ltac:(lia) ltac:(lia)) as [VW VH].
assert (Vlp : val_mem ubs2segs (ms_mem ms) (sp0 - 80 + 34) 2 loops).
{ pose proof (val_mem_low_of_chunk _ _ _ _ _ 2%N _ CC ltac:(cbn; lia)) as V.
replace (bv_unsigned (sv_denot _ (SExt true 16 (SOff 39 0))) mod 2 ^ (8 * Z.of_N 2)) with loops in V; [exact V|].
change (bv_unsigned (sv_denot E (SExt true 16 (SOff 39 0)))) with (U E (SExt true 16 (SOff 39 0))).
rewrite U_SExt, (U_atom _ 39 loops HX39) by lia. change (8 * Z.of_N 2) with 16. symmetry. apply sext16_low. lia. }
split; [split; [| unfold ubs2_A_cgif_writecb; lia] |].
{ eapply (val_of_chunk_ok _ _ _ _ _ 8%N _ _ CC4); [reflexivity | unfold ubs2_A_cgif_writecb; lia | cbn; lia]. }
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
destruct Hrawcfg as (rattr & Hrawcfg & Rrattr).
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hrd : forall i, 0 <= i < 40 -> exists b, mbyte ubs2segs (ms_mem msx) (sp0 - 80 + i) = Some b)
end.
{ pose proof (st_region_chunks ubs2segs _ _ _ 0%nat _ 2%nat (sp0 - 80) HS eq_refl eq_refl HU2) as HC.
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
assert (Hobj1 : obj_at ubs2segs (ms_mem msx) g LAY_CGIF gvals)
end.
{ eapply (st_obj_at ubs2segs _ _ _ 2%nat _ 8%nat g LAY_CGIF gvals 43 lits_CGIF0 HS eq_refl eq_refl HU8).
- apply incl_chunks_sound. vm_compute. reflexivity.
- reflexivity.
- reflexivity.
- intros j v Hj. split; [exact (Robj j v Hj)|].
assert (Hlj : (j < 17)%nat) by (destruct (Nat.lt_ge_cases j 17) as [Hl|Hl]; [exact Hl|]; rewrite (proj2 (nth_error_None gvals j) Hl) in Hj; discriminate).
do 17 (try (destruct j as [|j]; [cbn [nth_error lits_CGIF0]; first [apply (HG _ _ Hj) | subst gvals; cbn in Hj; congruence] | ])). lia. }
eapply SR_bind.
{ eapply (jcall ubs2_msyms MR) with (STK1 := RAWNEW_STK) (FP1 := [])
(K := fun L2 A2 regs2 mem2 md2 => st_init_done A2 = true /\ exists res, getr regs2 10 = Z_to_bv 64 res /\
((res = 0 /\ blocks L2 A2 = blocks Lc Ac) \/
(res <> 0 /\ sgct <= 256 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, RAW_SIZE) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
obj_at ubs2segs mem2 res LAY_Raw [ubs2_A_cgif_writecb; g; pal0; rattr; W; H; sgct; loops; R_PENDING])));
[ exact HS | reflexivity | exact HJ | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| unfold spZ; rewrite Hr2, unsigned_lit_small by lia; exact Hspm | unfold RAWNEW_STK, RAWNEW_FRAME; lia
| unfold spZ, RAWNEW_STK, RAWNEW_FRAME; rewrite Hr2, unsigned_lit_small by lia; lia
| unfold spZ; rewrite Hr2, unsigned_lit_small by lia; lia | exact Hr4
| intros a Ha; exfalso; exact (inFP_nil a Ha) ].
intros HPRE1. eapply SR_mono.
{ eapply (ubs2_cgif_raw_newgif API IMG _ _ _ _ _ (sp0 - 80) g pal0 rattr W H sgct loops gvals HPRE1 Hid Hr10);
[ exact Hcf8
| unfold spZ; rewrite Hr2, unsigned_lit_small by lia; lia | lia | exact Hrawcfg | exact Hrd | exact Hobj1 | reflexivity | reflexivity | exact Hgin ]. }
cbv beta. intros c' (L4 & A4 & regs4 & mem4 & md4 & res2 & -> & HJc & HP4 & Hid4 & Hq10 & Hres).
exists L4, A4, regs4, mem4, md4. split; [rewrite Hr1; reflexivity|]. split; [exact HJc|]. split; [exact HP4|]. split; [exact Hid4|].
exists res2. split; [exact Hq10|]. exact Hres. }
cbv beta. intros c' (L4 & A4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & Hid4 & res2 & Hq10 & Hres). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc, HP4, Hq10.
assert (Hg4 : In (g, CGIF_SIZE) (blocks L4 A4)).
{ destruct Hres as [[_ Hbl] | (_ & _ & (b1 & b2 & Hbl4 & Hblc) & _)]; [rewrite Hbl; exact Hgin|].
rewrite Hbl4. rewrite Hblc in Hgin. apply in_app_iff in Hgin. apply in_app_iff. destruct Hgin as [H0|H0]; [left; exact H0 | right; right; exact H0]. }
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
- eapply (region_kept_stack ubs2segs _ _ _ 2); [exact HU2 | exact Hhi4 | lia | lia | unfold spZ; rewrite Hr2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 9); [exact HU18 | exact Hhi4 | lia | lia | unfold spZ; rewrite Hr2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia].
- split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; rewrite HU8; intros a Ha.
+ replace a with (g + (a - g)) by lia. apply (Hblk4 g CGIF_SIZE (a - g) Hgin Hg4); [lia | apply inFP_nil].
+ intros _. apply (present_writable ubs2_msyms). replace a with (g + (a - g)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L4 A4 mem4 md4 g CGIF_SIZE (a - g) HH4 Hg4 ltac:(lia))). }
clear HS. rename HS2 into HS.
destruct Hres as [[-> Hbl] | (Hnz & Hsg & (b1 & b2 & Hbl4 & Hblc) & Hraw4)].
-
pin_reg HS (10%bv:reg) 0 Hq10.
jrun_to LAWS ubs2tbl_ok HS HJ4 ubs2_A_freeCGIF.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocF; exact HU8 | exact Hg4 | exact Hgfresh | cbn; lia | cbn; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hs10. rewrite (HE 8%nat 8%bv eq_refl), G8 in Hs10.
jreg HS (2%bv:reg) as Hs2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hs2.
jreg HS (4%bv:reg) as Hs4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hs4.
jreg HS (1%bv:reg) as Hs1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hobj2 : obj_at ubs2segs (ms_mem msx) g LAY_CGIF gvals)
end.
{ eapply (st_obj_at ubs2segs _ _ _ 2%nat _ 8%nat g LAY_CGIF gvals 43 lits_CGIF0 HS eq_refl eq_refl ltac:(ew_havocF; exact HU8)).
- apply incl_chunks_sound. vm_compute. reflexivity.
- reflexivity.
- reflexivity.
- intros j v Hj. split; [exact (Robj j v Hj)|].
assert (Hlj : (j < 17)%nat) by (destruct (Nat.lt_ge_cases j 17) as [Hl|Hl]; [exact Hl|]; rewrite (proj2 (nth_error_None gvals j) Hl) in Hj; discriminate).
do 17 (try (destruct j as [|j]; [cbn [nth_error lits_CGIF0]; first [ew_havocF; apply (HG _ _ Hj) | subst gvals; cbn in Hj; congruence] | ])). lia. }
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := FREECGIF_STK) (FP1 := fp_freeCGIF g attr pal' (3 * ngp))
(K := fun L5 A5 (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) => Permutation (blocks L5 A5) (blocks L A));
[ exact HS | reflexivity | exact HJ4 | exact Hs1 | | apply ret_ok_even; vm_compute; reflexivity
| unfold spZ; rewrite Hs2, unsigned_lit_small by lia; exact Hspm | unfold FREECGIF_STK; lia
| unfold spZ, FREECGIF_STK; rewrite Hs2, unsigned_lit_small by lia; lia
| unfold spZ; rewrite Hs2, unsigned_lit_small by lia; lia | exact Hs4 | ].
- intros HPRE2. eapply SR_mono.
{ eapply (ubs2_freeCGIF API IMG _ _ _ _ _ g gvals attr pal' (3 * ngp) (blocks L A) HPRE2 Hs10 Hobj2 eq_refl eq_refl).
rewrite Hbl. unfold gpals_of. rewrite <- Hpalblk. exact HB. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & HB5).
exists L5, A5, regs5, mem5, md5. split; [rewrite Hs1; reflexivity|]. split; [exact HJc5|]. split; [exact HP5 | exact HB5].
-
intros a Ha. right. unfold fp_freeCGIF in Ha. apply inFP_cons in Ha. destruct Ha as [Ha | Ha].
+ exists g, CGIF_SIZE. split; [exact Hg4|]. split; [exact Hgfresh | lia].
+ destruct (Z.eqb_spec (Z.land attr 4) 0) as [Hz4|Hz4]; [| exfalso; exact (inFP_nil a Ha)].
apply inFP_cons in Ha. destruct Ha as [Ha | Ha]; [| exfalso; exact (inFP_nil a Ha)].
exists pal', (3 * ngp).
assert (Hpin : In (pal', 3 * ngp) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | right; rewrite Hpalblk; left; reflexivity]).
split; [rewrite Hbl; exact Hpin|]. split; [| lia].
intros Hin. pose proof (Hpalfresh (pal', 3 * ngp) ltac:(rewrite Hpalblk; left; reflexivity) Hin) as Hle. cbn [snd] in Hle. lia. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HB5). clear HJ4.
cbn [ms_regs ms_mem mkst] in HJc5, HP5.
pose proof HJc5 as (_ & _ & Hhi5 & _).
jafter_call_keep HS 84%nat regs5 mem5 HP5 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havocF; exact HU2 | exact Hhi5 | lia | lia | unfold spZ; rewrite Hs2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun LAWS ubs2tbl_ok HS HJ5.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ5))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ5)))). }
unfold newgif_post.
lazymatch type of HS with st_ok _ _ _ ?msf => exists L5, A5, (ms_regs msf), (ms_mem msf), md5, 0 end.
split. { cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg ubs2segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
repeat (rewrite ew_havoc_old in Q1; [|nat_lt_lit]); rewrite ?Z.add_0_r, HE60, Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra0; reflexivity end. }
split; [exact HJ5|].
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
split; [reg_nowF HS ltac:(reflexivity)|].
left. split; [reflexivity|]. exists []. exact HB5.
-
assert (Hr2in : In (res2, RAW_SIZE) (blocks L4 A4)) by (rewrite Hbl4; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS L4 A4 mem4 md4 res2 RAW_SIZE HH4 Hr2in ltac:(unfold RAW_SIZE; lia)) as (Hq0 & Hq1 & Hq16).
unfold RAW_SIZE in Hq1.
jreg HS (10%bv:reg) as Hq72. cbn [ms_regs mkst] in Hq72. rewrite Hq10 in Hq72. symmetry in Hq72.
add_fact HS 72%nat (mkAF 4096 (CEIL_MAX - 48) 4).
2:{ rewrite Hq72, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
jrun LAWS ubs2tbl_ok HS HJ4.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocF; exact HU8 | exact Hg4 | exact Hgfresh | cbn; lia | cbn; lia |]. apply wr_ok_nil. }
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ4))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ4)))). }
unfold newgif_post.
lazymatch type of HS with st_ok _ _ _ ?msf => exists L4, A4, (ms_regs msf), (ms_mem msf), md4, g end.
split. { cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg ubs2segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
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
split; [reg_nowF HS ltac:(rewrite HU8; reflexivity)|].
right. split; [lia|].
exists (mkCgif [None; None; None] pal' attr gen W H ngp loops res2 R_PENDING 1 pal0 rattr loops R_PENDING).
cbn [cg_frames cg_W cg_H cg_attr cg_cur cg_ihead].
split.
{
unfold cgif_at. cbn [cgif_vals raw_vals raw_sgct cg_frames cg_pal cg_attr cg_gen cg_W cg_H cg_ngp cg_loops cg_raw cg_cur cg_ihead rw_gct rw_attr rw_loops rw_cur nth frame_ptr].
split; [|split].
- unfold cgif_vals. cbn [cg_frames cg_pal cg_attr cg_gen cg_W cg_H cg_ngp cg_loops cg_raw cg_cur cg_ihead nth frame_ptr].
change LAY_CGIF with ([(0, 8%N); (8, 8%N); (16, 8%N); (24, 8%N); (32, 8%N); (40, 4%N); (44, 4%N); (48, 2%N); (50, 2%N); (52, 2%N); (54, 2%N); (56, 8%N); (64, 8%N)]
++ [(72, 8%N); (80, 8%N); (88, 4%N); (92, 4%N)]).
change [0; 0; 0; pal'; 0; attr; gen; W; H; ngp; loops; ubs2_A_writecb; 0; res2; 0; R_PENDING; 1]
with ([0; 0; 0; pal'; 0; attr; gen; W; H; ngp; loops; ubs2_A_writecb; 0] ++ [res2; 0; R_PENDING; 1]).
rewrite obj_at_app by reflexivity. cbn [ms_mem mkst]. split.
+ eapply (st_obj_at ubs2segs _ _ _ 2%nat _ 8%nat g _ _ 43 (firstn 13 lits_CGIF0) HS eq_refl eq_refl ltac:(ew_havocF; exact HU8)).
* apply incl_chunks_sound. vm_compute. reflexivity.
* reflexivity.
* reflexivity.
* intros j v Hj.
assert (Hlj : (j < 13)%nat) by (destruct (Nat.lt_ge_cases j 13) as [Hl|Hl]; [exact Hl|]; rewrite (proj2 (nth_error_None [0; 0; 0; pal'; 0; attr; gen; W; H; ngp; loops; ubs2_A_writecb; 0] j) Hl) in Hj; discriminate).
assert (Hj' : nth_error gvals j = Some v) by (subst gvals; do 13 (destruct j as [|j]; [exact Hj|]); lia).
split; [| do 13 (try (destruct j as [|j]; [cbn [nth_error lits_CGIF0 firstn]; first [ew_havocF; apply (HG _ _ Hj') | cbn in Hj; congruence] | ])); lia].
pose proof (Robj j v Hj') as R. do 13 (destruct j as [|j]; [exact R|]). lia.
+ eapply (st_obj_at ubs2segs _ _ _ 2%nat _ 8%nat g _ _ 72 [None; Some 0; Some R_PENDING; Some 1] HS eq_refl eq_refl ltac:(ew_havocF; exact HU8)).
* apply incl_chunks_sound. vm_compute. reflexivity.
* reflexivity.
* reflexivity.
* intros j v Hj. destruct j as [|[|[|[|j]]]]; cbn in Hj; [injection Hj as <- | injection Hj as <- | injection Hj as <- | injection Hj as <- | destruct j; discriminate Hj]; cbn [snd nth nth_error Z.of_N].
-- split; [cbn; lia | rewrite Nat.add_0_r; exact Hq72].
-- split; [lit_range | reflexivity].
-- split; [lit_range | reflexivity].
-- split; [lit_range | reflexivity].
- unfold raw_vals, raw_sgct. cbn [cg_frames cg_pal cg_attr cg_gen cg_W cg_H cg_ngp cg_loops cg_raw cg_cur cg_ihead rw_gct rw_attr rw_loops rw_cur]. rewrite <- Hsgct. cbn [ms_mem mkst].
assert (Hgq : g + CGIF_SIZE <= res2 \/ res2 + 48 <= g).
{ destruct (heap_sep _ _ LAWS L4 A4 mem4 md4 b1 (res2, RAW_SIZE) b2 (g, CGIF_SIZE) HH4 Hbl4 ltac:(rewrite <- Hblc; exact Hgin)) as [H0|H0]; cbn [fst snd] in H0; unfold RAW_SIZE in *; lia. }
eapply obj_at_transport_range; [exact Hraw4 | exact (proj1 LAY_Raw_ok) |].
intros i Hi. unfold RAW_SIZE in Hi. cbn [ms_mem mkst] in HF0. mb_frame_with HF0 ltac:(lia) ltac:(rewrite ?HU2, ?HU8; lia). reflexivity.
- intros f Hf. exfalso. destruct Hf as [H0|[H0|[H0|[]]]]; discriminate H0. }
split.
{ unfold cgif_wf. cbn [cg_frames cg_W cg_H cg_attr cg_ngp cg_ihead length].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [lia|].
split; [intros Hz4; rewrite Hsgct in Hsg; destruct (Z.eqb_spec (Z.land attr 4) 0); lia|].
split; [left; reflexivity|].
intros f Hf. exfalso. destruct Hf as [H0|[H0|[H0|[]]]]; discriminate H0. }
do 6 (split; [reflexivity|]).
unfold cgif_blocks, pal_blocks. cbn [cg_raw cg_attr cg_pal cg_ngp cg_frames frames_blocks flat_map app].
rewrite app_nil_r. replace (if Z.land attr 4 =? 0 then [(pal', 3 * ngp)] else (@nil (Z * Z))) with palblk. rewrite Hbl4.
eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
eapply Permutation_trans; [| apply perm_swap]. apply perm_skip. rewrite <- Hblc.
exact HB.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
