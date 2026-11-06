(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8 YCe9 YCfs YCfr YCgw YCfu YCe1.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition CL_IT : Z := 0x88bac.
Definition CL_B : Z := 0x88c0c.
Definition CL_FR : Z := 0x88c74.
Definition CL_RET_FLUSH : Z := 0x88be8. Definition CL_RET_RAWCLOSE : Z := 0x88c28.
Definition CL_RET_FREEFRAME : Z := 0x88c94. Definition CL_RET_FREECGIF : Z := 0x88cb0.
Definition cl_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24].
Definition cl_frame (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error cl_saved j = Some r -> val_mem trbsegs m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Definition cl_extra (regs : bvmap 5 word) (g : Z) (s1 : cgif_st) : list word :=
map (Z_to_bv 64) [g; frame_ptr (nth 0 (cg_frames s1) None); frame_ptr (nth 1 (cg_frames s1) None); frame_ptr (nth 2 (cg_frames s1) None);
cg_raw s1; cg_cur s1; SB; cg_pal s1; cg_attr s1]
++ map (fun r => getr regs (Z_to_bv 5 r)) cl_saved.
Definition Bxc : sv := SOff 38 0.
Definition RBspanC : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition shx (o : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 o) (SLit 3)) (SOff 38 0).
Definition cl_stack (d : Z) (sv : bool) : YQ0b.region :=
YQ0b.mkRegion (Some 2%nat) d (d + 80) d (if sv then d else d + 80)
(if sv then map (fun j => YQ0b.mkChunk (d + 72 - 8 * Z.of_nat j) (CVal 8 (SOff (41 + j) 0))) (seq 0 10) else []).
Definition cl_obj : YQ0b.region :=
YQ0b.mkRegion (Some 32%nat) 0 CGIF_SIZE 88 92
[YQ0b.mkChunk 0 (CVal 8 (SOff 33 0)); YQ0b.mkChunk 8 (CVal 8 (SOff 34 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 35 0));
YQ0b.mkChunk 24 (CVal 8 (SOff 39 0)); YQ0b.mkChunk 40 (CVal 4 (SOff 40 0));
YQ0b.mkChunk 72 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 80 (CVal 8 (SLit 0)); YQ0b.mkChunk 88 (CVal 4 (SOff 37 0))].
Definition cl_regions (d : Z) (sv : bool) : smem := [cl_stack d sv; got_region; bcell_region 38; cl_obj].
Definition hfact : afact := mkAF 4096 0x7fffff800000 4.
Definition cl_facts : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, hfact); (38%nat, mkAF SB SB 0)] [] [].
Definition NOTF : afact := mkAF (2 ^ 64 - 1 - 0x7fffff800000) (2 ^ 64 - 1) 0.
Definition cl_facts_mid : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, hfact); (38%nat, mkAF SB SB 0); (20%nat, NOTF)] [] [].
Definition cl_SH : list shent := [mkSHE 32 0 CGIF_SIZE].
Definition ss_cl (pc : Z) (sregs : list sv) (d : Z) (sv : bool) : sstate :=
mkSS pc sregs (cl_regions d sv) None (if sv then cl_facts_mid else cl_facts).
Definition regsA : list sv := Eval vm_compute in sr_set sr_atoms 10 (SOff 32 0).
Definition regsB : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set sr_atoms 8 (SOff 32 0)) 9 (SOff 32 88)) 19 (shx 88)) 18 (SOff 38 0).
Definition regsIT (i : Z) : list sv := Eval cbv -[Z.mul Z.sub Z.add Z.opp] in
sr_set (sr_set (sr_set (sr_set regsB 21 (SOff 32 (8 * i))) 22 (SLit (8 * i))) 23 (SLit 24)) 10 (SOff 32 (8 * (i - 1))).
Definition regsFR (i : Z) : list sv := Eval cbv -[Z.mul Z.sub Z.add Z.opp] in
sr_set (sr_set regsB 21 (SLit (8 * i))) 22 (SLit 24).
Definition occ (s1 : cgif_st) (i : nat) : bool := match nth i (cg_frames s1) None with Some _ => true | None => false end.
Definition FPc (g : Z) (s : cgif_st) (N : Z) : list (Z * Z) := ablocks_fp (cgif_blocks g s N).
Ltac awr_cl Usp E32u Hing HTS :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
first [ apply awr_ok_cons_ro; [cbn; lia|]
| eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -80); [reflexivity | rewrite Usp; lia | cbn; rewrite HTS; lia | cbn; lia |] ];
apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ =>
eapply awr_ok_cons_block with (n := 32%nat) (m := CGIF_SIZE);
[ reflexivity | exact E32u | exact Hing | cbn [YQ0b.r_wlo]; lia
| cbn [YQ0b.r_whi]; change (req_size CGIF_SIZE) with 96; lia
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; unfold FPc, ablocks_fp, cgif_blocks; cbn [map fst snd app];
lazymatch type of E32u with _ = ?g => exists (g, g + req_size CGIF_SIZE) end;
split; [left; reflexivity | cbn [fst snd]; change (req_size CGIF_SIZE) with 96; lia]
| apply awr_ok_nil ] end.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section h.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Definition cl_cx ly S (W : world trbsegs) (regs : bvmap 5 word) mem md ch (g : Z) (s : cgif_st) (N : Z) (rest : list (Z * Z)) : Prop :=
afn_pre trbsegs B TCLOSE_STK ly S W regs mem md ch /\
In (raZ regs :: spine ch) CTX_cgif_close /\ Z.of_nat (length (frames S)) <= 7 /\
arodata_ok B (aview trbsegs (w_H W) mem) /\
getr regs 10 = w64 g /\
tcgif_at (mrestrict (w_H W) mem) g s /\ cgif_wf s N /\
Permutation (ablocks B ly S) (cgif_blocks g s N ++ rest) /\
vev S + (2 * EV_FLUSH + 16) <= VEV_MAX /\ blocks_bytes S + LIVE_FLUSH <= LIVE_MAX.
Definition cl_post ly S W (regs : bvmap 5 word) mem md (g : Z) (s : cgif_st) (N : Z) (rest : list (Z * Z)) (kf : Z)
: world trbsegs -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B TCLOSE_STK (spZ regs) (FPc g s N) ly S W mem md [] ly' S' W' mem' md' kf /\
aregs_preserved regs regs' /\ Permutation (ablocks B ly' S') rest.
Definition cl_obj_ok (g : Z) (s s1 : cgif_st) (N : Z) : Prop :=
cgif_wf s1 N /\ cg_raw s1 = cg_raw s /\ cg_attr s1 = cg_attr s /\ cg_pal s1 = cg_pal s /\ cg_ngp s1 = cg_ngp s /\
map (option_map (frame_blocks N)) (cg_frames s1) = map (option_map (frame_blocks N)) (cg_frames s).
Definition cl_regs_at (regs regs1 : bvmap 5 word) (g : Z) : Prop :=
getr regs1 2 = w64 (spZ regs - 80) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 g /\ getr regs1 9 = w64 (g + 88) /\ getr regs1 19 = w64 (SB + (g + 88) / 8) /\
getr regs1 18 = w64 SB /\ getr regs1 20 = w64 (2 ^ 64 - 1 - g) /\
(forall r, 25 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))    .
Definition tcgif_at2 (m : word -> option byte) (g : Z) (s1 : cgif_st) : Prop :=
obj_at trbsegs m g LAY_CGIF (tcgif_vals s1) /\
(forall f, In (Some f) (cg_frames s1) -> obj_at trbsegs m (fr_ptr f) LAY_Frame (frame_vals f)).
Definition cl_mid (OBJ : (word -> option byte) -> Z -> cgif_st -> Prop)
ly S W (regs : bvmap 5 word) mem md g s N rest lyc Sc (Wc : world trbsegs) memc mdc (k : Z) (s1 : cgif_st) (bl : list (Z * Z)) : Prop :=
ajournal trbsegs B TCLOSE_STK (spZ regs) (FPc g s N) ly S W mem md [] lyc Sc Wc memc mdc k /\ 0 <= k /\
cl_frame (mrestrict (w_H Wc) memc) (spZ regs) regs /\
OBJ (mrestrict (w_H Wc) memc) g s1 /\ cl_obj_ok g s s1 N /\
Permutation (ablocks B lyc Sc) (bl ++ rest).
Definition CL_B_stmt : Prop :=
forall ly S W regs mem md ch g s N rest lyc Sc Wc regs1 memc mdc k s1,
cl_cx ly S W regs mem md ch g s N rest ->
cl_mid tcgif_at ly S W regs mem md g s N rest lyc Sc Wc memc mdc k s1 (cgif_blocks g s N) -> k <= 2 * EV_FLUSH ->
cl_regs_at regs regs1 g ->
SRr trbsegs Wc (mkCfg (mkst regs1 (Z_to_bv 64 CL_B) memc (seg_rom trbsegs)) mdc) (cl_post ly S W regs mem md g s N rest (k + 16)).
Definition CL_IT_stmt (i : Z) : Prop :=
forall ly S W regs mem md ch g s N rest lyc Sc Wc regs1 memc mdc k s1,
cl_cx ly S W regs mem md ch g s N rest ->
cl_mid tcgif_at ly S W regs mem md g s N rest lyc Sc Wc memc mdc k s1 (cgif_blocks g s N) -> k <= (i - 1) * EV_FLUSH -> cg_cur s1 = 0 ->
cl_regs_at regs regs1 g ->
getr regs1 10 = w64 (g + 8 * (i - 1)) -> getr regs1 21 = w64 (g + 8 * i) -> getr regs1 22 = w64 (8 * i) -> getr regs1 23 = w64 24 ->
SRr trbsegs Wc (mkCfg (mkst regs1 (Z_to_bv 64 CL_IT) memc (seg_rom trbsegs)) mdc) (cl_post ly S W regs mem md g s N rest (k + (3 - i) * EV_FLUSH + 16)).
Definition fr_blocks (g : Z) (s : cgif_st) (N : Z) (i : nat) : list (Z * Z) :=
(g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N (skipn i (cg_frames s)).
Definition tcgif_atI (i : nat) (m : word -> option byte) (g : Z) (s1 : cgif_st) : Prop :=
obj_at trbsegs m g LAY_CGIF (tcgif_vals s1) /\
(forall j f, (i <= j)%nat -> nth_error (cg_frames s1) j = Some (Some f) -> obj_at trbsegs m (fr_ptr f) LAY_Frame (frame_vals f)).
Definition CL_FR_stmt (i : Z) : Prop :=
forall ly S W regs mem md ch g s N rest lyc Sc Wc regs1 memc mdc k s1,
cl_cx ly S W regs mem md ch g s N rest ->
cl_mid (tcgif_atI (Z.to_nat i)) ly S W regs mem md g s N rest lyc Sc Wc memc mdc k s1 (fr_blocks g s N (Z.to_nat i)) -> k <= 2 * EV_FLUSH + 1 + 3 * i ->
cl_regs_at regs regs1 g ->
getr regs1 21 = w64 (8 * i) -> getr regs1 22 = w64 24 ->
SRr trbsegs Wc (mkCfg (mkst regs1 (Z_to_bv 64 CL_FR) memc (seg_rom trbsegs)) mdc) (cl_post ly S W regs mem md g s N rest (k + 3 * (3 - i) + 2)).
Definition CL_AFTER_stmt (i : Z) : Prop :=
forall ly S W regs mem md ch g s N rest lyc Sc Wc regs1 memc mdc k s1,
cl_cx ly S W regs mem md ch g s N rest ->
cl_mid (tcgif_atI (Datatypes.S (Z.to_nat i))) ly S W regs mem md g s N rest lyc Sc Wc memc mdc k s1 (fr_blocks g s N (Datatypes.S (Z.to_nat i))) ->
k <= 2 * EV_FLUSH + 4 + 3 * i ->
cl_regs_at regs regs1 g ->
getr regs1 21 = w64 (8 * i) -> getr regs1 22 = w64 24 ->
SRr trbsegs Wc (mkCfg (mkst regs1 (Z_to_bv 64 CL_RET_FREEFRAME) memc (seg_rom trbsegs)) mdc) (cl_post ly S W regs mem md g s N rest (k + 3 * (2 - i) + 2)).
Lemma cl_seed : forall pc sregs (sv : bool) W1 (regs regs1 : bvmap 5 word) mem1 ly1 S1 md1 lya sp0 g s1,
AR trbsegs B ly1 S1 W1 mem1 md1 ->
In (g, CGIF_SIZE) (ablocks B ly1 S1) ->
astk_ok TCLOSE_STK lya sp0 -> (forall a, sp0 - TCLOSE_STK <= a < sp0 -> apresent (w_H W1) mem1 a) ->
bv_unsigned (getr regs1 2) = sp0 - 80 - (0) ->
regs_ok (Ereg regs1 (cl_extra regs g s1)) sregs regs1 ->
(sv = true -> cl_frame (mrestrict (w_H W1) mem1) sp0 regs) ->
(sv = true -> getr regs1 20 = w64 (2 ^ 64 - 1 - g)) ->
obj_at trbsegs (mrestrict (w_H W1) mem1) g LAY_CGIF (tcgif_vals s1) ->
st_ok trbsegs (Ereg regs1 (cl_extra regs g s1)) (ss_cl pc sregs (0) sv)
(restrict (w_H W1) (mkst regs1 (Z_to_bv 64 pc) mem1 (seg_rom trbsegs)))
/\ sh_ok trbsegs Bxc cl_SH (Ereg regs1 (cl_extra regs g s1)) (mrestrict (w_H W1) mem1).
Proof.
intros pc sregs sv W1 regs regs1 mem1 ly1 S1 md1 lya sp0 g s1 HAR Hing Hstk Hpres Hsp HREG HFR HNOT HOBJ.
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TCLOSE_STK = 17520) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, Hgh_img.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (obj_at_length _ _ _ _ _ HOBJ) as HL. cbn in HL.
assert (FLD : forall j o n v, nth_error LAY_CGIF j = Some (o, n) -> nth_error (tcgif_vals s1) j = Some v ->
val_mem trbsegs (mrestrict (w_H W1) mem1) (g + o) (N.to_nat n) v /\ 0 <= v < 2 ^ (8 * Z.of_N n)).
{ intros j o n v Hj Hv. exact (obj_at_nth trbsegs _ _ _ _ j (o, n) v HOBJ Hj Hv). }
pose proof (FLD 0%nat 0 8%N _ eq_refl eq_refl) as [V0 R0]. pose proof (FLD 1%nat 8 8%N _ eq_refl eq_refl) as [V1 R1].
pose proof (FLD 2%nat 16 8%N _ eq_refl eq_refl) as [V2 R2]. pose proof (FLD 13%nat 72 8%N _ eq_refl eq_refl) as [V13 R13].
pose proof (FLD 14%nat 80 8%N _ eq_refl eq_refl) as [V14 _]. pose proof (FLD 15%nat 88 4%N _ eq_refl eq_refl) as [V15 R15].
pose proof (FLD 3%nat 24 8%N _ eq_refl eq_refl) as [V3 R3]. pose proof (FLD 5%nat 40 4%N _ eq_refl eq_refl) as [V5 R5].
cbn [nth_error tcgif_vals] in V0, R0, V1, R1, V2, R2, V13, R13, V14, V15, R15, V3, R3, V5, R5.
rewrite restrict_mkst_fx.
set (E := Ereg regs1 (cl_extra regs g s1)) in *.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m)%nat -> ew E m = nth (m - 32) (cl_extra regs g s1) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; apply ew_Ereg_extra).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 80 - (0)) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
pose proof (ES 32%nat ltac:(lia)) as E32. pose proof (ES 33%nat ltac:(lia)) as E33. pose proof (ES 34%nat ltac:(lia)) as E34.
pose proof (ES 35%nat ltac:(lia)) as E35. pose proof (ES 36%nat ltac:(lia)) as E36. pose proof (ES 37%nat ltac:(lia)) as E37.
pose proof (ES 38%nat ltac:(lia)) as E38. pose proof (ES 39%nat ltac:(lia)) as E39. pose proof (ES 40%nat ltac:(lia)) as E40.
cbn [Nat.sub nth cl_extra map app] in E32, E33, E34, E35, E36, E37, E38, E39, E40.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_cl, cl_regions. apply (entry_st_ok_full trbsegs); change (Ereg regs1 (cl_extra regs g s1)) with E.
+ exact HREG.
+ destruct sv; vm_compute; reflexivity.
+ unfold cl_stack, got_region, bcell_region, cl_obj.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
*   cbn [base_val]. rewrite E2. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable trbsegs). apply Hpres. destruct sv; lia. }
destruct sv; [| constructor].
lazymatch goal with |- Forall ?P ?l => let l2 := eval vm_compute in l in change (Forall P l2) end.
repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with |- YQ0b.chunk_ok _ _ _ _ (YQ0b.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
let j := eval compute in (n - 41)%nat in let r := eval compute in (nth j cl_saved 0) in
apply (chunk_ok_val trbsegs E _ (sp0 - 80 - (0)) off 8 (SOff n 0) (bv_unsigned (ew E n)));
[ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| let HR := fresh in pose proof (bv_unsigned_in_range 64 (ew E n)) as HR; clear - HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
| cbn; lia
| replace (sp0 - 80 - (0) + off) with (sp0 - 8 - 8 * Z.of_nat j) by lia;
rewrite (ES n ltac:(lia)); cbn [Nat.sub nth cl_extra map app]; exact (HFR eq_refl j r eq_refl) ] end.
* cbn [base_val]. unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 668240) at 1.
apply (chunk_ok_val trbsegs E _ 0 668240 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W1) mem1 _ _ Kgot).
* cbn [base_val]. unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 701048) at 1.
apply (chunk_ok_val trbsegs E _ 0 701048 8 Bxc SB);
[cbn [sv_denot Bxc]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W1) mem1 _ _ Kcell).
*   rewrite (VB 32%nat g E32) by lia. unfold CGIF_SIZE. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable trbsegs). destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (_ & _ & _ & _ & HP & _).
apply HP. change (req_size CGIF_SIZE) with 96. lia. }
constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]]]].
-- apply (chunk_ok_val trbsegs E _ g 0 8 _ (frame_ptr (nth 0 (cg_frames s1) None))); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V0].
-- apply (chunk_ok_val trbsegs E _ g 8 8 _ (frame_ptr (nth 1 (cg_frames s1) None))); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V1].
-- apply (chunk_ok_val trbsegs E _ g 16 8 _ (frame_ptr (nth 2 (cg_frames s1) None))); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V2].
-- apply (chunk_ok_val trbsegs E _ g 24 8 _ (cg_pal s1)); [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V3].
-- apply (chunk_ok_val trbsegs E _ g 40 4 _ (cg_attr s1)); [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V5].
-- apply (chunk_ok_val trbsegs E _ g 72 8 _ (cg_raw s1)); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V13].
-- apply (chunk_ok_val trbsegs E _ g 80 8 _ 0); [reflexivity | zside | zside | exact V14].
-- apply (chunk_ok_val trbsegs E _ g 88 4 _ (cg_cur s1)); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V15].
+ apply pairwise_disjoint_of_extents. unfold cl_stack, got_region, bcell_region, cl_obj, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite (VB 32%nat g E32) by lia. cbn [base_val]. rewrite E2.
unfold A_GOT_shadow, A_shadow_glob, CGIF_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 C1 C3 HTS Hstk0. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
+ assert (A20 : sv = true -> afact_ok E 20 NOTF).
{ intros Hsv. unfold afact_ok, NOTF. cbn [af_lo af_hi af_al2]. rewrite (EE 20%nat 20%bv eq_refl), (HNOT Hsv).
unfold w64. rewrite unsigned_lit_small by (clear - Hgceil Hg4096; ceil; unfold ASAN_CEIL in *; lia). rewrite Z.pow_0_r, Z.mod_1_r.
clear - Hgceil Hg4096. ceil. unfold ASAN_CEIL in *. lia. }
destruct sv; (split; [|split; exact I]);
cbn [f_atoms atoms_ok cl_facts cl_facts_mid]; [split; [|split; [|split; [|split; [exact (A20 eq_refl) | exact I]]]] | split; [|split; [|split; [|exact I]]]];
unfold afact_ok, hfact; cbn [af_lo af_hi af_al2];
rewrite ?E2, ?E32, ?E38, ?unsigned_lit_small by (unfold SB; lia);
change (2 ^ 4) with 16; rewrite ?Z.pow_0_r, ?Z.mod_1_r;
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hg16 Hsp0al C1 C3 HTS Hstk0; clear; unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg; intros;
repeat match goal with |- _ /\ _ => split end; try lia;
replace (sp0 - 80 - (0)) with (sp0 + (-5) * 16) by lia; rewrite Z_mod_plus_full; exact Hsp0al.
- unfold sh_ok, cl_SH. constructor; [|constructor].
apply (shent_ok_of_block trbsegs B LAWS ly1 S1 W1 mem1 md1 E Bxc 32 g CGIF_SIZE 0 CGIF_SIZE HAR Hing).
+ unfold U, Bxc. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
Qed.
Lemma cl_seed_entry : forall pc sregs W1 (regs regs1 : bvmap 5 word) mem1 ly1 S1 md1 lya sp0 g s1,
AR trbsegs B ly1 S1 W1 mem1 md1 ->
In (g, CGIF_SIZE) (ablocks B ly1 S1) ->
astk_ok TCLOSE_STK lya sp0 -> (forall a, sp0 - TCLOSE_STK <= a < sp0 -> apresent (w_H W1) mem1 a) ->
bv_unsigned (getr regs1 2) = sp0 - 80 - (-80) ->
regs_ok (Ereg regs1 (cl_extra regs g s1)) sregs regs1 ->
obj_at trbsegs (mrestrict (w_H W1) mem1) g LAY_CGIF (tcgif_vals s1) ->
st_ok trbsegs (Ereg regs1 (cl_extra regs g s1)) (ss_cl pc sregs (-80) false)
(restrict (w_H W1) (mkst regs1 (Z_to_bv 64 pc) mem1 (seg_rom trbsegs)))
/\ sh_ok trbsegs Bxc cl_SH (Ereg regs1 (cl_extra regs g s1)) (mrestrict (w_H W1) mem1).
Proof.
intros pc sregs W1 regs regs1 mem1 ly1 S1 md1 lya sp0 g s1 HAR Hing Hstk Hpres Hsp HREG HOBJ.
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TCLOSE_STK = 17520) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, Hgh_img.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (obj_at_length _ _ _ _ _ HOBJ) as HL. cbn in HL.
assert (FLD : forall j o n v, nth_error LAY_CGIF j = Some (o, n) -> nth_error (tcgif_vals s1) j = Some v ->
val_mem trbsegs (mrestrict (w_H W1) mem1) (g + o) (N.to_nat n) v /\ 0 <= v < 2 ^ (8 * Z.of_N n)).
{ intros j o n v Hj Hv. exact (obj_at_nth trbsegs _ _ _ _ j (o, n) v HOBJ Hj Hv). }
pose proof (FLD 0%nat 0 8%N _ eq_refl eq_refl) as [V0 R0]. pose proof (FLD 1%nat 8 8%N _ eq_refl eq_refl) as [V1 R1].
pose proof (FLD 2%nat 16 8%N _ eq_refl eq_refl) as [V2 R2]. pose proof (FLD 13%nat 72 8%N _ eq_refl eq_refl) as [V13 R13].
pose proof (FLD 14%nat 80 8%N _ eq_refl eq_refl) as [V14 _]. pose proof (FLD 15%nat 88 4%N _ eq_refl eq_refl) as [V15 R15].
pose proof (FLD 3%nat 24 8%N _ eq_refl eq_refl) as [V3 R3]. pose proof (FLD 5%nat 40 4%N _ eq_refl eq_refl) as [V5 R5].
cbn [nth_error tcgif_vals] in V0, R0, V1, R1, V2, R2, V13, R13, V14, V15, R15, V3, R3, V5, R5.
rewrite restrict_mkst_fx.
set (E := Ereg regs1 (cl_extra regs g s1)) in *.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m)%nat -> ew E m = nth (m - 32) (cl_extra regs g s1) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; apply ew_Ereg_extra).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 80 - (-80)) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
pose proof (ES 32%nat ltac:(lia)) as E32. pose proof (ES 33%nat ltac:(lia)) as E33. pose proof (ES 34%nat ltac:(lia)) as E34.
pose proof (ES 35%nat ltac:(lia)) as E35. pose proof (ES 36%nat ltac:(lia)) as E36. pose proof (ES 37%nat ltac:(lia)) as E37.
pose proof (ES 38%nat ltac:(lia)) as E38. pose proof (ES 39%nat ltac:(lia)) as E39. pose proof (ES 40%nat ltac:(lia)) as E40.
cbn [Nat.sub nth cl_extra map app] in E32, E33, E34, E35, E36, E37, E38, E39, E40.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_cl, cl_regions. apply (entry_st_ok_full trbsegs); change (Ereg regs1 (cl_extra regs g s1)) with E.
+ exact HREG.
+ vm_compute. reflexivity.
+ unfold cl_stack, got_region, bcell_region, cl_obj.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
*   cbn [base_val]. rewrite E2. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable trbsegs). apply Hpres. lia. }
constructor.
* cbn [base_val]. unfold A_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 668240) at 1.
apply (chunk_ok_val trbsegs E _ 0 668240 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W1) mem1 _ _ Kgot).
* cbn [base_val]. unfold A_shadow_glob. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 701048) at 1.
apply (chunk_ok_val trbsegs E _ 0 701048 8 Bxc SB);
[cbn [sv_denot Bxc]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W1) mem1 _ _ Kcell).
*   rewrite (VB 32%nat g E32) by lia. unfold CGIF_SIZE. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable trbsegs). destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (_ & _ & _ & _ & HP & _).
apply HP. change (req_size CGIF_SIZE) with 96. lia. }
constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]]]].
-- apply (chunk_ok_val trbsegs E _ g 0 8 _ (frame_ptr (nth 0 (cg_frames s1) None))); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V0].
-- apply (chunk_ok_val trbsegs E _ g 8 8 _ (frame_ptr (nth 1 (cg_frames s1) None))); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V1].
-- apply (chunk_ok_val trbsegs E _ g 16 8 _ (frame_ptr (nth 2 (cg_frames s1) None))); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V2].
-- apply (chunk_ok_val trbsegs E _ g 24 8 _ (cg_pal s1)); [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V3].
-- apply (chunk_ok_val trbsegs E _ g 40 4 _ (cg_attr s1)); [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V5].
-- apply (chunk_ok_val trbsegs E _ g 72 8 _ (cg_raw s1)); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V13].
-- apply (chunk_ok_val trbsegs E _ g 80 8 _ 0); [reflexivity | zside | zside | exact V14].
-- apply (chunk_ok_val trbsegs E _ g 88 4 _ (cg_cur s1)); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V15].
+ apply pairwise_disjoint_of_extents. unfold cl_stack, got_region, bcell_region, cl_obj, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite (VB 32%nat g E32) by lia. cbn [base_val]. rewrite E2.
unfold A_GOT_shadow, A_shadow_glob, CGIF_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 C1 C3 HTS Hstk0. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
+ split; [|split; exact I].
cbn [f_atoms atoms_ok cl_facts]. unfold afact_ok, hfact. cbn [af_lo af_hi af_al2].
rewrite E2, E32, E38, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hgceil Hgh Hgh_img Hg4096 Hg16 Hsp0al C1 C3 HTS Hstk0. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; try lia.
replace (sp0 - 80 - (-80)) with sp0 by lia. exact Hsp0al.
- unfold sh_ok, cl_SH. constructor; [|constructor].
apply (shent_ok_of_block trbsegs B LAWS ly1 S1 W1 mem1 md1 E Bxc 32 g CGIF_SIZE 0 CGIF_SIZE HAR Hing).
+ unfold U, Bxc. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
Qed.
Lemma obj_at_kept : forall (m m' : word -> option byte) p lay vals sz,
obj_at trbsegs m p lay vals -> lay_inside lay sz = true ->
(forall i, 0 <= i < sz -> mbyte trbsegs m' (p + i) = mbyte trbsegs m (p + i)) -> obj_at trbsegs m' p lay vals.
Proof. intros m m' p lay vals sz H Hl Hk. exact (obj_at_transport_range trbsegs m m' p lay vals sz H Hl Hk). Qed.
Lemma lay_inside_CGIF : lay_inside LAY_CGIF 96 = true. Proof. vm_compute. reflexivity. Qed.
Lemma lay_inside_Frame : lay_inside LAY_Frame 40 = true. Proof. vm_compute. reflexivity. Qed.
Lemma lay_inside_Raw : lay_inside LAY_Raw 48 = true. Proof. vm_compute. reflexivity. Qed.
Definition blk_kept (H H' : word -> bool) (m m' : word -> option byte) (b n : Z) : Prop :=
forall i, 0 <= i < n -> aview trbsegs H' m' (b + i) = aview trbsegs H m (b + i).
Lemma obj_at_blk_kept : forall H H' m m' p lay vals sz,
obj_at trbsegs (mrestrict H m) p lay vals -> lay_inside lay sz = true -> blk_kept H H' m m' p sz ->
obj_at trbsegs (mrestrict H' m') p lay vals.
Proof.
intros H H' m m' p lay vals sz Ho Hl Hk. apply (obj_at_kept _ _ p lay vals sz Ho Hl).
intros i Hi. apply (mbyte_of_aview trbsegs). apply Hk. exact Hi.
Qed.
Lemma tcgif_at2_kept : forall H H' m m' g s1,
tcgif_at2 (mrestrict H m) g s1 -> blk_kept H H' m m' g 96 ->
(forall f, In (Some f) (cg_frames s1) -> blk_kept H H' m m' (fr_ptr f) 40) ->
tcgif_at2 (mrestrict H' m') g s1.
Proof.
intros H H' m m' g s1 [Hg Hf] Kg Kf. split.
- exact (obj_at_blk_kept H H' m m' g LAY_CGIF _ 96 Hg lay_inside_CGIF Kg).
- intros f Hin. exact (obj_at_blk_kept H H' m m' (fr_ptr f) LAY_Frame _ 40 (Hf f Hin) lay_inside_Frame (Kf f Hin)).
Qed.
Lemma tcgif_at_kept : forall H H' m m' g s1,
tcgif_at (mrestrict H m) g s1 -> blk_kept H H' m m' g 96 -> blk_kept H H' m m' (cg_raw s1) 48 ->
(forall f, In (Some f) (cg_frames s1) -> blk_kept H H' m m' (fr_ptr f) 40) ->
tcgif_at (mrestrict H' m') g s1.
Proof.
intros H H' m m' g s1 (Hg & Hr & Hf) Kg Kr Kf. split; [|split].
- exact (obj_at_blk_kept H H' m m' g LAY_CGIF _ 96 Hg lay_inside_CGIF Kg).
- exact (obj_at_blk_kept H H' m m' (cg_raw s1) LAY_Raw _ 48 Hr lay_inside_Raw Kr).
- intros f Hin. exact (obj_at_blk_kept H H' m m' (fr_ptr f) LAY_Frame _ 40 (Hf f Hin) lay_inside_Frame (Kf f Hin)).
Qed.
Lemma tcgif_at_2 : forall m g s1, tcgif_at m g s1 -> tcgif_at2 m g s1.
Proof. intros m g s1 (Hg & _ & Hf). exact (conj Hg Hf). Qed.
Lemma blk_kept_call : forall STK1 sp1 FP1 lyc Sc (W : world trbsegs) memc mdc ly2 S2 W2 mem2 md2 k1 b n,
ajournal trbsegs B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
In (b, n) (ablocks B lyc Sc) -> In (b, n) (ablocks B ly2 S2) -> (forall i, 0 <= i < n -> ~ inFP FP1 (b + i)) ->
blk_kept (w_H W) (w_H W2) memc mem2 b n.
Proof.
intros STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 b n HJ1 Hin Hin2 HnF i Hi.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
destruct (Z_lt_ge_dec n 0) as [Hn|Hn]; [lia|]. pose proof (req_size_pos n ltac:(lia)) as [_ Hr].
apply (G2 b n i Hin Hin2); [lia | apply HnF; exact Hi].
Qed.
Lemma cl_frame_kept : forall H H' m m' sp0 regs,
cl_frame (mrestrict H m) sp0 regs -> (forall a, sp0 - 80 <= a < sp0 -> aview trbsegs H' m' a = aview trbsegs H m a) ->
cl_frame (mrestrict H' m') sp0 regs.
Proof.
intros H H' m m' sp0 regs HF Hk j r Hj. pose proof (HF j r Hj) as V.
assert (Hj9 : (j < 10)%nat) by (apply (proj1 (nth_error_Some cl_saved j)); rewrite Hj; discriminate).
intros kk Hkk. rewrite <- (V kk Hkk). apply (mbyte_of_aview trbsegs). apply Hk. lia.
Qed.
Lemma cl_U_sext32 : forall E a r, U E a = r -> 0 <= r < 2 ^ 32 ->
U E (SExt true 32 a) = (if r <? 2 ^ 31 then r else r - 2 ^ 32 + 2 ^ 64).
Proof.
intros E a r Ha Hr. rewrite U_SExt, Ha. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small r) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
destruct (Z.ltb_spec r (2 ^ 31)) as [Hl | Hh].
- rewrite (Z.mod_small (r + 2 ^ 31)) by lia. replace (r + 2 ^ 31 - 2 ^ 31) with r by lia. apply zcanon_id. unfold M64. lia.
- replace ((r + 2 ^ 31) mod 2 ^ 32) with (r + 2 ^ 31 - 2 ^ 32).
2:{ replace (r + 2 ^ 31) with ((r + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) at 2 by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
unfold zcanon, M64. replace (r + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with ((r - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma achain_data : forall ly rd sp v, (v < alloc_ceiling \/ ly_top ly - 16 <= v) -> achain ly rd sp v [].
Proof. intros ly rd sp v [H|H]; left; (split; [|reflexivity]); [left; exact H | right; left; exact H]. Qed.
Lemma cl_post_mono : forall ly S W regs mem md g s N rest kf kf' W' c',
cl_post ly S W regs mem md g s N rest kf W' c' -> kf <= kf' -> cl_post ly S W regs mem md g s N rest kf' W' c'.
Proof.
intros ly S W regs mem md g s N rest kf kf' W' c' (ly' & S' & regs' & mem' & md' & Hc & HJ & HP & HB) Hle.
exists ly', S', regs', mem', md'. split; [exact Hc|]. split; [exact (ajournal_mono_k trbsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hle)|]. exact (conj HP HB).
Qed.
Lemma tcgif_atI_0 : forall m g s1, tcgif_at m g s1 -> tcgif_atI 0 m g s1.
Proof.
intros m g s1 (Hg & _ & Hf). split; [exact Hg|]. intros j f _ Hj. apply Hf. eapply nth_error_In. exact Hj.
Qed.
Lemma tcgif_atI_le : forall i j m g s1, (i <= j)%nat -> tcgif_atI i m g s1 -> tcgif_atI j m g s1.
Proof. intros i j m g s1 Hij [Hg Hf]. split; [exact Hg|]. intros jj f Hjj. apply Hf. lia. Qed.
Lemma tcgif_atI_kept : forall i H H' m m' g s1,
tcgif_atI i (mrestrict H m) g s1 -> blk_kept H H' m m' g 96 ->
(forall j f, (i <= j)%nat -> nth_error (cg_frames s1) j = Some (Some f) -> blk_kept H H' m m' (fr_ptr f) 40) ->
tcgif_atI i (mrestrict H' m') g s1.
Proof.
intros i H H' m m' g s1 [Hg Hf] Kg Kf. split.
- exact (obj_at_blk_kept H H' m m' g LAY_CGIF _ 96 Hg lay_inside_CGIF Kg).
- intros j f Hij Hj. exact (obj_at_blk_kept H H' m m' (fr_ptr f) LAY_Frame _ 40 (Hf j f Hij Hj) lay_inside_Frame (Kf j f Hij Hj)).
Qed.
Lemma sep_hd_in : forall ly S W mem md x y l,
AR trbsegs B ly S W mem md -> Permutation (ablocks B ly S) (x :: l) -> In y l -> zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W mem md x y l HAR HP Hy. apply in_split in Hy as (l1 & l2 & ->).
apply (sep_blocks_perm trbsegs B LAWS ly S W mem md x y (l1 ++ l2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma obj_at_of_fields : forall m a lay vals,
length vals = length lay ->
(forall j f v, nth_error lay j = Some f -> nth_error vals j = Some v -> field_ok trbsegs m a f v) ->
obj_at trbsegs m a lay vals.
Proof.
intros m a lay. induction lay as [|f lay IH]; intros [|v vals] HL HF; cbn in HL |- *; try discriminate; [exact I|].
split; [exact (HF 0%nat f v eq_refl eq_refl)|]. apply IH; [lia|]. intros j f' v' Hf Hv. exact (HF (S j) f' v' Hf Hv).
Qed.
Lemma obj_cgif_rebuild : forall (m m' : word -> option byte) g vals cur,
obj_at trbsegs m g LAY_CGIF vals ->
(forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte trbsegs m' (g + i) = mbyte trbsegs m (g + i)) ->
nth_error vals 15 = Some cur -> val_mem trbsegs m' (g + 88) 4 cur ->
obj_at trbsegs m' g LAY_CGIF vals.
Proof.
intros m m' g vals cur HO HK Hcur Vcur. pose proof (obj_at_length _ _ _ _ _ HO) as HL.
apply obj_at_of_fields; [exact HL|]. intros j f v Hf Hv.
pose proof (obj_at_nth trbsegs _ _ _ _ j f v HO Hf Hv) as [V R]. split; [|exact R].
destruct (Nat.eq_dec j 15) as [-> | Hne].
- cbn in Hf. injection Hf as <-. rewrite Hcur in Hv. injection Hv as <-. exact Vcur.
- assert (HIN : In f LAY_CGIF) by (eapply nth_error_In; exact Hf).
assert (Hoff : 0 <= fst f /\ fst f + Z.of_N (snd f) <= 96 /\ (fst f + Z.of_N (snd f) <= 88 \/ 92 <= fst f)).
{ assert (Hj : (j < 17)%nat) by (apply (proj1 (nth_error_Some LAY_CGIF j)); rewrite Hf; discriminate).
do 17 (destruct j as [|j]; [cbn in Hf; injection Hf as <-; cbn; lia|]). lia. }
intros kk Hkk. rewrite <- (V kk Hkk). pose proof (N_nat_Z (snd f)).
replace (g + fst f + Z.of_nat kk) with (g + (fst f + Z.of_nat kk)) by lia. apply HK; lia.
Qed.
Lemma cl_frame_of_region : forall E (m : word -> option byte) sp0 (regs : bvmap 5 word),
region_ok trbsegs E m (cl_stack 0 true) -> bv_unsigned (ew E 2) = sp0 - 80 ->
(forall j r, nth_error cl_saved j = Some r -> ew E (41 + j) = getr regs (Z_to_bv 5 r)) ->
cl_frame m sp0 regs.
Proof.
intros E m sp0 regs HR Hsp HE j r Hj.
assert (Hj9 : (j < 10)%nat) by (apply (proj1 (nth_error_Some cl_saved j)); rewrite Hj; discriminate).
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
replace (sp0 - 8 - 8 * Z.of_nat j) with ((sp0 - 80) + (72 - 8 * Z.of_nat j)) by lia. change 8%nat with (N.to_nat 8).
apply (field_of_region E m 2 (sp0 - 80) _ 0 80 0 0 (72 - 8 * Z.of_nat j) 8 (SOff (41 + j) 0) _ HR Hsp).
- unfold cl_stack. cbn [YQ0b.r_chunks].
do 10 (destruct j as [|j]; [cbn; tauto|]). exfalso. lia.
- cbn [sv_denot]. rewrite (HE j r Hj), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- exact HRr.
- cbn. lia.
Qed.
Lemma sep_app : forall ly S W mem md x y l1 l2,
AR trbsegs B ly S W mem md -> Permutation (ablocks B ly S) (l1 ++ l2) -> In x l1 -> In y l2 -> zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W mem md x y l1 l2 HAR HP Hx Hy. apply in_split in Hx as (a1 & a2 & ->). apply in_split in Hy as (b1 & b2 & ->).
assert (P1 : Permutation (a1 ++ x :: a2) (x :: a1 ++ a2)) by (apply Permutation_sym, Permutation_middle).
assert (P2 : Permutation (b1 ++ y :: b2) (y :: b1 ++ b2)) by (apply Permutation_sym, Permutation_middle).
apply (sep_blocks_perm trbsegs B LAWS ly S W mem md x y ((a1 ++ a2) ++ (b1 ++ b2)) HAR).
eapply Permutation_trans; [exact HP|]. eapply Permutation_trans; [apply Permutation_app; [exact P1 | exact P2]|].
cbn [app]. apply perm_skip. apply Permutation_sym. apply (Permutation_middle (a1 ++ a2) (b1 ++ b2) y).
Qed.
Lemma frames3 : forall sx N, cgif_wf sx N -> cg_frames sx = [nth 0 (cg_frames sx) None; nth 1 (cg_frames sx) None; nth 2 (cg_frames sx) None].
Proof. intros sx N HW. pose proof (proj1 HW) as HL. destruct (cg_frames sx) as [|a [|b [|c [|]]]]; cbn in HL; try discriminate. reflexivity. Qed.
Lemma slot_eq : forall g s s1 N i, cl_obj_ok g s s1 N ->
option_map (frame_blocks N) (nth i (cg_frames s) None) = option_map (frame_blocks N) (nth i (cg_frames s1) None).
Proof.
intros g s s1 N i (_ & _ & _ & _ & _ & Hfrm).
rewrite <- (map_nth (option_map (frame_blocks N)) (cg_frames s) None i), <- (map_nth (option_map (frame_blocks N)) (cg_frames s1) None i).
rewrite Hfrm. reflexivity.
Qed.
Lemma frames_blocks_skipn : forall N (fs : list (option frame_st)) i, (i < length fs)%nat ->
frames_blocks N (skipn i fs) = match nth i fs None with Some f => frame_blocks N f | None => [] end ++ frames_blocks N (skipn (Datatypes.S i) fs).
Proof.
intros N fs. induction fs as [|o fs IH]; intros i Hi; cbn in Hi; [lia|].
destruct i as [|i]; [cbn; destruct o; reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.
Lemma frames_blocks_in : forall N (fs : list (option frame_st)) i j f b,
(i <= j)%nat -> nth_error fs j = Some (Some f) -> In b (frame_blocks N f) -> In b (frames_blocks N (skipn i fs)).
Proof.
intros N fs. induction fs as [|o fs IH]; intros i j f b Hij Hj Hb; [destruct j; discriminate|].
destruct i as [|i].
- cbn [skipn]. destruct j as [|j]; cbn in Hj.
+ injection Hj as ->. cbn [frames_blocks flat_map]. apply in_or_app. left. exact Hb.
+ cbn [frames_blocks flat_map]. apply in_or_app. right. change (In b (frames_blocks N (skipn 0 fs))). eapply IH; [| exact Hj | exact Hb]. lia.
- destruct j as [|j]; [lia|]. cbn [skipn]. cbn in Hj. eapply IH; [| exact Hj | exact Hb]. lia.
Qed.
Lemma slot_frame : forall g s s1 N j f, cl_obj_ok g s s1 N -> cgif_wf s N -> nth_error (cg_frames s1) j = Some (Some f) ->
exists f', nth_error (cg_frames s) j = Some (Some f') /\ frame_blocks N f' = frame_blocks N f.
Proof.
intros g s s1 N j f HOK HWF Hj. pose proof (slot_eq g s s1 N j HOK) as SJ.
pose proof HOK as (HWF1 & _). pose proof (proj1 HWF) as HL. pose proof (proj1 HWF1) as HL1.
assert (Hj3 : (j < 3)%nat) by (rewrite <- HL1; apply (proj1 (nth_error_Some _ j)); rewrite Hj; discriminate).
rewrite (nth_error_nth' (cg_frames s1) None) in Hj by lia. injection Hj as Hn. rewrite Hn in SJ. cbn in SJ.
destruct (nth j (cg_frames s) None) as [f'|] eqn:Hn'; [|discriminate]. cbn in SJ.
pose proof (f_equal (fun o : option (list (Z * Z)) => match o with Some l => l | None => [] end) SJ) as SJ'. cbn beta iota in SJ'.
exists f'. split; [|exact SJ']. rewrite (nth_error_nth' (cg_frames s) None) by lia. rewrite Hn'. reflexivity.
Qed.
End h. End e.
