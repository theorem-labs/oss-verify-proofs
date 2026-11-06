(* proves function fuzz_alloc_most (reuse search: proof-index on main@8b3d60a62fb / ossv/recipes@8bece492f26 / ossv/candidates@ee89628c997 / release/pau-projects-recipes@b6a0088adcb + lemma index + live heads, and git grep of 0x85e14 / 0x862e0 on those four refs / `proof-index fuzz_alloc_most 0x85e14 0x862e0`)
   fuzz_preset row AL5 (rewalk preset-F the internal file FREE-PIECES-102.md Part 5; the internal file AL-ROWS.md), image A' (asan, #102 pin 1be0f53d96cb,
   unstripped twin bff8519bbe3e): the walk of fuzz_alloc_most (merged alloc.c :186-189, `g_most = n`; entry
   A_prog_sigma AS_fuzz_alloc_most of h-verbs-1's listing pins102 d42e123915ae) against K0's text
   tfuzz_alloc_most_specX (lib/A/PRH_FnCheck.v:776, kit of record walkkit-next decff67d721f):
   fuzz_alloc_most_holds. The conclusion is SRr (srealizes, YA0n.v).
   Listing (lib/A/Listing_prog.v, slots A_prog_slot AS_fuzz_alloc_most .. + 2):
     fuzz_alloc_most        auipc a1 ; sd a0 -> g_most ; ret                                           (3 words)
   A LEAF: no call, no frame, no instrumented access (the store goes to a static, which is PST).
   Shape: the accessor walks' (origin/cold/h-w6rep-2-p102-allocsurf f5123281fbe2 lib/A/Prog/PwAllocSurf.v, the
   writers fuzz_alloc_peak_reset / fuzz_alloc_fail), restated for a writer that stores its argument:
   1.-2. (image-free, in lib/A/Prog/FuzzAllocMostCore.v, which both this file and the B' twin Require): fam_wr_run
      states the byte run as machine behaviour over ANY segments (no journal, no ledger); fam_most_core, parametric in
      the image ({PI : PrhImg} {PA : PAImg L}) and in the allocator relation ARx, builds fpostm (YCbqG's
      apost_base_x at PST := prh_pst, with the memnorm keep) from the byte run: the journal by ajournal_x_init then
      ajournal_x_pst_write (the one cell written, g_most, is PST), the ledger by S1Ledger's prh_ledger_iff /
      prh_lblocks_kept from PRH_Base's named projections (ledger_proj; never a positional destruct of prh_ledger):
      the five alloc.c cells and g_own_ran_out kept (prh_pst's cells are pairwise disjoint), g_most := n, Lam / Hp /
      the blocks / the heads kept (a head word is off the written cell, fam_head_off);
   3. image A' (this file): the byte run by the engine (sym_runN over the function's own words read from the image,
      then SRr_ret_at), and the image facts of prh_img_A's statics by computation.
   lib/B/Prog/FuzzAllocMostBp.v is the B' twin; it Requires FuzzAllocMostCore.v, not this file.
   Opened hypothesis (as PwAllocSurf.v's): PST_unowned (YCbqG's PST_ok, its B half: no static is a runtime-owned
   static of B).
   NUMERALS: no ADDRESS literal (g_most is prh_img_A's pi_g_most / pi_gz_most; the entry is A_prog_sigma
   AS_fuzz_alloc_most = pa_sigma of PI_prog_A); 3 LENGTH (the listing's word count); 8 LENGTH (a word's bytes: the
   width bound and the alignment of a static, the stored chunk's width, the head word); 1, 10 DERIVED (the ISA's
   register numbers of ra and a0); 64 and 2 ^ 64 WORD (the machine word's width and modulus); 0 WORD (an absolute
   region's base). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import FuzzAllocMostCore.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ==== 4. image A' (asan, #102: PI_prog_A / prh_img_A on the #102 pins): the byte run, then the text ==== *)
(* the m-form post's and the core's image facts of prh_img_A's seven statics, by computation over the concrete
   segments (PwAllocSurf.v's, over S1ImgA.v's pst_allb) *)
Lemma fam_pst_sep_A : YG0f.pairwise zdisjoint (@prh_pst prh_img_A).
Proof.
unfold prh_pst. cbn [YG0f.pairwise].
repeat match goal with
| |- _ /\ _ => split
| |- True => exact I
| |- Forall _ [] => apply Forall_nil
| |- Forall _ (_ :: _) => apply Forall_cons; [unfold zdisjoint; cbn; lia|]
end.
Qed.
Lemma fam_pst_al_A : Forall (fun r => fst r mod 8 = 0 /\ 0 <= snd r <= 8) (@prh_pst prh_img_A).
Proof.
unfold prh_pst.
repeat match goal with
| |- Forall _ [] => apply Forall_nil
| |- Forall _ (_ :: _) => apply Forall_cons; [cbn; split; [reflexivity | lia]|]
end.
Qed.
Lemma fam_pst_rw_b_A : pst_allb (fam_rw_b rsegs) (@prh_pst prh_img_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fam_pst_rw_A : forall a, Exists (in_zr a) (@prh_pst prh_img_A) ->
  match find_segment rsegs a 1 with Some seg => seg_writable seg = true | None => True end.
Proof.
intros a Ha. pose proof (pst_allb_sound _ _ a fam_pst_rw_b_A Ha) as H. unfold fam_rw_b in H.
destruct (find_segment rsegs a 1); [exact H | exact I].
Qed.
Lemma fam_pst_top_A : forallb (fun r => fst r + snd r <=? TASK_SIZE) (@prh_pst prh_img_A) = true.
Proof. vm_compute. reflexivity. Qed.

(* the table: the function's own words read from the image (LENGTH 3: the listing's word count) *)
Definition tbl_am : ctable := Eval vm_compute in build_table rsegs (A_prog_sigma AS_fuzz_alloc_most) 3 TEmpty.
Lemma tbl_am_ok : table_ok rsegs tbl_am.
Proof.
assert (E : tbl_am = build_table rsegs (A_prog_sigma AS_fuzz_alloc_most) 3 TEmpty) by (vm_cast_no_check (eq_refl tbl_am)).
rewrite E. apply build_table_ok0. cbv. discriminate.
Qed.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation PA := PI_prog_A.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Abbreviation PIA := prh_img_A.

Lemma fam_most_run_A : fam_wr_run SEGS (SIGMA AS_fuzz_alloc_most) (@pi_g_most PIA) (@pi_gz_most PIA).
Proof.
intros W regs mem md a0 Q Hra H10 Ha0 HQ. unfold YK0s.ret_ok in Hra.
pose proof (@pa_wx _ _ PA) as Hwx.
assert (Hw : forall x, @pi_g_most PIA <= x < @pi_g_most PIA + Z.of_nat (@pi_gz_most PIA) ->
  writable_at rsegs (mrestrict (w_H W) mem) x)
  by (intros x Hx; apply pst_writable_A; exact (fam_cell_pst (PI := PIA) _ _ x fam_in_most Hx)).
assert (HS : st_ok SEGS (Ereg regs []) (fam_ss (A_prog_sigma AS_fuzz_alloc_most) (@pi_g_most PIA) (@pi_gz_most PIA))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (A_prog_sigma AS_fuzz_alloc_most)) mem (seg_rom SEGS))))
  by exact (fam_entry rsegs regs mem (w_H W) (A_prog_sigma AS_fuzz_alloc_most) (@pi_g_most PIA) (@pi_gz_most PIA)
    ltac:(vm_compute; reflexivity) Hw ltac:(cbn; lia) ltac:(cbn; lia)).
unfold cfg_at. change (w64 (SIGMA AS_fuzz_alloc_most)) with (Z_to_bv 64 (A_prog_sigma AS_fuzz_alloc_most)).
remember (Ereg regs []) as E eqn:HE.
fam_wr_go tbl_am tbl_am_ok Hwx HS.
intros ms' mat' HS' HFr Hgr Hhid. clear HS.
refine (SRr_ret_at SEGS tbl_am tbl_am_ok Hwx W E _ _ _ _ HS' eq_refl ltac:(vm_compute; reflexivity) _).
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
assert (HFR : forall x : word, ~ (@pi_g_most PIA <= bv_unsigned x < @pi_g_most PIA + Z.of_nat (@pi_gz_most PIA)) ->
  mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) mem x) by (fam_wr_frame HFr).
exact (HQ (ms_regs ms') (ms_mem ms') mat2 HPR HFR Hgr Hhid V).
Qed.
End A.

(* ---- the text (lib/A/PRH_FnCheck.v:776) at image A' (#102): PA := PI_prog_A, PI := prh_img_A, preset's
   CfParams, the kit's room-live instance, a Theorem Labs lane's prh_room_live_a8, and the allocator relation ARcf with the
   error-buffer extents placed (FuzzStrdup.v's, PwAllocSurf.v's). It is the core (section 3) with the byte run of
   section 4. ---- *)
Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PA := PI_prog_A.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation PIA := prh_img_A.
Variable B : asyms.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* the allocator's laws at ARcf: h-mani-a8's AR_laws_ok_cf (YG0lawscf.v), and AR_laws_x from them (YGcallcf.v) *)
Let LAWS_cf : AR_laws_cf (cp := CP) SEGS B := AR_laws_ok_cf (cp := CP) SEGS B.
Let LAWS : AR_laws_x SEGS B ARcfx (@cf_head CP) := AR_laws_x_xs (cp := CP) SEGS B LAWS_cf.
(* PST_ok's B half: the seven statics are not runtime-owned statics of B (its image half is S1ImgA's pst_in_img_A) *)
Hypothesis PST_unowned : forall a, Exists (in_zr a) (@prh_pst PIA) -> ~ Exists (in_zr a) (as_owned_static B).
Let PST_OK : forall a, Exists (in_zr a) (@prh_pst PIA) -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) :=
  fun a H => conj (pst_in_img_A a H) (PST_unowned a H).

Theorem fuzz_alloc_most_holds :
  PRH_FnCheck.tfuzz_alloc_most_specX (cp := CP) (PI := PIA) (RL := prh_room_live_a8 (cp := CP)) (PA := PA) B ARcfx SK.
Proof.
exact (fam_most_core (cp := CP) (PI := PIA) (RL := prh_room_live_a8 (cp := CP)) B ARcfx SK _ LAWS PST_OK
  fam_pst_sep_A fam_pst_al_A fam_pst_rw_A fam_pst_top_A fam_most_run_A).
Qed.
End T.
