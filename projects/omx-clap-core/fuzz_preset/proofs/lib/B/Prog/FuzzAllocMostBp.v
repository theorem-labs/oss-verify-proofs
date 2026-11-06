(* proves function fuzz_alloc_most (reuse search: proof-index on main@8b3d60a62fb / ossv/recipes@8bece492f26 / ossv/candidates@ee89628c997 / release/pau-projects-recipes@b6a0088adcb + lemma index + live heads, and git grep of 0x85e14 / 0x862e0 on those four refs / `proof-index fuzz_alloc_most 0x85e14 0x862e0`)
   fuzz_preset row AL5, image B' (asan-ubsan, #102 pin): the B' twin of lib/A/Prog/FuzzAllocMostAp.v, the walk of
   fuzz_alloc_most (merged alloc.c :186-189, `g_most = n`; entry B_prog_sigma AS_fuzz_alloc_most of a Theorem Labs lane's listing
   d42e123915ae) against the text tfuzz_alloc_most_specX (lib/A/PRH_FnCheck.v:776, kit of record
   decff67d721f): fuzz_alloc_most_holds_B. The conclusion is SRr (srealizes, YA0n.v).
   Listing (lib/B/Listing_prog.v, slots B_prog_slot AS_fuzz_alloc_most .. + 2):
     fuzz_alloc_most        auipc a1 ; sd a0 -> g_most ; ret                                           (3 words)
   No UBSan check and no instrumented access: the store goes to a static, which is PST.
   The image-generic parts are lib/A/Prog/FuzzAllocMostCore.v (fam_wr_run, the run and frame tactics, the core
   fam_most_core, parametric in the image and in ARx; image-free, so this file does not Require the A' file
   FuzzAllocMostAp.v or S1ImgA); this file holds image B''s byte run and its image facts.
   Opened hypothesis (as the A' file's): PST_unowned (YCbqG's PST_ok, its B half).
   NUMERALS: no ADDRESS literal (g_most is prh_img_B's pi_g_most / pi_gz_most; the entry is B_prog_sigma
   AS_fuzz_alloc_most = pa_sigma of PI_prog_B); 3 LENGTH (the listing's word count); 8 LENGTH (a word's bytes: the
   width bound and the alignment of a static, the stored chunk's width); 1, 10 DERIVED (the ISA's register numbers of
   ra and a0); 64 and 2 ^ 64 WORD (the machine word's width and modulus); 0 WORD (an absolute region's base). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI16 YM05 YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YP08 YL0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG0ncf YG0dcf YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import FuzzAllocMostCore.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ==== image B' (asan-ubsan, #102: PI_prog_B / prh_img_B on the #102 pins): image facts, the byte run, the text ==== *)
(* the core's image facts of prh_img_B's seven statics, by computation over the concrete segments (as the A' file's
   for prh_img_A), over S1ImgCheck.v's pst_allb (:24, :27; Required at :38) *)
Lemma fbm_pst_sep_B : YG0f.pairwise zdisjoint (@prh_pst prh_img_B).
Proof.
unfold prh_pst. cbn [YG0f.pairwise].
repeat match goal with
| |- _ /\ _ => split
| |- True => exact I
| |- Forall _ [] => apply Forall_nil
| |- Forall _ (_ :: _) => apply Forall_cons; [unfold zdisjoint; cbn; lia|]
end.
Qed.
Lemma fbm_pst_al_B : Forall (fun r => fst r mod 8 = 0 /\ 0 <= snd r <= 8) (@prh_pst prh_img_B).
Proof.
unfold prh_pst.
repeat match goal with
| |- Forall _ [] => apply Forall_nil
| |- Forall _ (_ :: _) => apply Forall_cons; [cbn; split; [reflexivity | lia]|]
end.
Qed.
Lemma fbm_pst_rw_b_B : pst_allb (fam_rw_b rsegs) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fbm_pst_rw_B : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  match find_segment rsegs a 1 with Some seg => seg_writable seg = true | None => True end.
Proof.
intros a Ha. pose proof (pst_allb_sound _ _ a fbm_pst_rw_b_B Ha) as H. unfold fam_rw_b in H.
destruct (find_segment rsegs a 1); [exact H | exact I].
Qed.
Lemma fbm_pst_top_B : forallb (fun r => fst r + snd r <=? TASK_SIZE) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.

(* the table: the function's own words read from the image (LENGTH 3: the listing's word count) *)
Definition tbl_bm : ctable := Eval vm_compute in build_table rsegs (B_prog_sigma AS_fuzz_alloc_most) 3 TEmpty.
Lemma tbl_bm_ok : table_ok rsegs tbl_bm.
Proof.
assert (E : tbl_bm = build_table rsegs (B_prog_sigma AS_fuzz_alloc_most) 3 TEmpty) by (vm_cast_no_check (eq_refl tbl_bm)).
rewrite E. apply build_table_ok0. cbv. discriminate.
Qed.

Section Bp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation PA := PI_prog_B.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Abbreviation PIB := prh_img_B.

Lemma fbm_most_run_B : fam_wr_run SEGS (SIGMA AS_fuzz_alloc_most) (@pi_g_most PIB) (@pi_gz_most PIB).
Proof.
intros W regs mem md a0 Q Hra H10 Ha0 HQ. unfold YK0s.ret_ok in Hra.
pose proof (@pa_wx _ _ PA) as Hwx.
assert (Hw : forall x, @pi_g_most PIB <= x < @pi_g_most PIB + Z.of_nat (@pi_gz_most PIB) ->
  writable_at rsegs (mrestrict (w_H W) mem) x)
  by (intros x Hx; apply pst_writable_B; exact (fam_cell_pst (PI := PIB) _ _ x fam_in_most Hx)).
assert (HS : st_ok SEGS (Ereg regs []) (fam_ss (B_prog_sigma AS_fuzz_alloc_most) (@pi_g_most PIB) (@pi_gz_most PIB))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (B_prog_sigma AS_fuzz_alloc_most)) mem (seg_rom SEGS))))
  by exact (fam_entry rsegs regs mem (w_H W) (B_prog_sigma AS_fuzz_alloc_most) (@pi_g_most PIB) (@pi_gz_most PIB)
    ltac:(vm_compute; reflexivity) Hw ltac:(cbn; lia) ltac:(cbn; lia)).
unfold cfg_at. change (w64 (SIGMA AS_fuzz_alloc_most)) with (Z_to_bv 64 (B_prog_sigma AS_fuzz_alloc_most)).
remember (Ereg regs []) as E eqn:HE.
fam_wr_go tbl_bm tbl_bm_ok Hwx HS.
intros ms' mat' HS' HFr Hgr Hhid. clear HS.
refine (SRr_ret_at SEGS tbl_bm tbl_bm_ok Hwx W E _ _ _ _ HS' eq_refl ltac:(vm_compute; reflexivity) _).
intros mat2. rewrite wvb_collapse.
rreg HS' (1%bv : bv 5) R1.
assert (E1 : ew E 1 = getr regs 1) by (rewrite HE; exact (ew_Ereg_nat regs [] 1 1%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 a0) by (rewrite HE; rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10).
rewrite R1, E1, Hra.
(* the stored word: the write cell's one chunk, a0's entry value *)
destruct (st_ok_mem_ok SEGS E _ _ HS') as (_ & HRS & _). cbn [ms_mem restrict] in HRS.
apply Forall_inv in HRS.
unfold region_ok in HRS. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRS.
destruct HRS as (_ & _ & _ & HCk). apply Forall_inv in HCk.
lazymatch type of HCk with context [CVal _ ?e] =>
  assert (Hden : sv_denot E e = Z_to_bv 64 a0)
    by (cbn [sv_denot]; rewrite E10, unsigned_lit_small by lia; f_equal; lia);
  pose proof (val_of_chunk_ok SEGS E _ 0 _ 8 e a0 HCk Hden ltac:(cbn; lia) ltac:(cbn; lia)) as V
end.
assert (AG : env_agree 32 (Ereg regs []) E) by (rewrite HE; apply env_agree_refl).
assert (HPR : aregs_preserved regs (ms_regs ms'))
  by exact (aregs_preserved_of_st_ok SEGS (w_H W) E _ ms' regs [] HS' AG ltac:(vm_compute; reflexivity)).
assert (HFR : forall x : word, ~ (@pi_g_most PIB <= bv_unsigned x < @pi_g_most PIB + Z.of_nat (@pi_gz_most PIB)) ->
  mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) mem x) by (fam_wr_frame HFr).
exact (HQ (ms_regs ms') (ms_mem ms') mat2 HPR HFR Hgr Hhid V).
Qed.
End Bp.

(* ---- the text (lib/A/PRH_FnCheck.v:1706) at image B' (#102): PA := PI_prog_B, PI := prh_img_B, preset's
   CfParams, the kit's room-live instance prh_room_live_a8, and the allocator relation ARcf with the
   error-buffer extents placed. It is FuzzAllocMostCore.v's fam_most_core with image B''s byte run. ---- *)
Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PA := PI_prog_B.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation PIB := prh_img_B.
Variable B : asyms.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* the allocator's laws at ARcf: h-mani-a8's AR_laws_ok_cf (YG0lawscf.v), and AR_laws_x from them (YGcallcf.v) *)
Let LAWS_cf : AR_laws_cf (cp := CP) SEGS B := AR_laws_ok_cf (cp := CP) SEGS B.
Let LAWS : AR_laws_x SEGS B ARcfx (@cf_head CP) := AR_laws_x_xs (cp := CP) SEGS B LAWS_cf.
(* PST_ok's B half: the seven statics are not runtime-owned statics of B (its image half is S1ImgB's pst_in_img_B) *)
Hypothesis PST_unowned : forall a, Exists (in_zr a) (@prh_pst PIB) -> ~ Exists (in_zr a) (as_owned_static B).
Let PST_OK : forall a, Exists (in_zr a) (@prh_pst PIB) -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) :=
  fun a H => conj (pst_in_img_B a H) (PST_unowned a H).

Theorem fuzz_alloc_most_holds_B :
  PRH_FnCheck.tfuzz_alloc_most_specX (cp := CP) (PI := PIB) (RL := prh_room_live_a8 (cp := CP)) (PA := PA) B ARcfx SK.
Proof.
exact (fam_most_core (cp := CP) (PI := PIB) (RL := prh_room_live_a8 (cp := CP)) B ARcfx SK _ LAWS PST_OK
  fbm_pst_sep_B fbm_pst_al_B fbm_pst_rw_B fbm_pst_top_B fbm_most_run_B).
Qed.
End T.
