(* fuzz_preset image B' (asan-ubsan, #102 pin d663f82d7f48): the walks of alloc.c's seven accessors of the harness
   allocator's statics (alloc.c :129-162) against the texts at the kit of record decff67d721f,
   lib/A/PRH_FnAlloc.v (blob 83fe93bc86e2): tfuzz_alloc_live_specX (:71), tfuzz_alloc_peak_specX (:82),
   tfuzz_alloc_peak_reset_specX (:93), tfuzz_alloc_count_specX (:104), tfuzz_alloc_fail_specX (:115),
   tfuzz_alloc_ran_out_specX (:127) and tfuzz_alloc_ran_out_reset_specX (:138), at the AL rows' instance
   (cp := CfParams_preset) (PI := prh_img_B) (RL := prh_room_live_a8) (L := B_prog_listing) (PA := PI_prog_B)
   B ARcfx SK (OwnB_p102.v's form). Every conclusion is SRr (YA0n.v).
   Each theorem is its image-parametric core (lib/A/Prog/FuzzAllocAcc102.v section 3, Required) with the byte run
   proved here over image B's segments.
   Listings (lib/B/Listing_prog.v, #102, by symbol: B_prog_sigma / B_prog_slot of PAImg_prog.v):
     fuzz_alloc_live           slot 4840: auipc a0 ; ld a0 <- A_OBJ 9 (g_live) ; ret                          (3 words)
     fuzz_alloc_peak           slot 4843: auipc a0 ; ld a0 <- A_OBJ 10 (g_peak) ; ret                         (3 words)
     fuzz_alloc_peak_reset     slot 4846: auipc a0 ; ld a0 <- A_OBJ 9 (g_live) ; auipc a1 ; sd a0 -> g_peak ; ret (5)
     fuzz_alloc_count          slot 4851: auipc a0 ; ld a0 <- A_OBJ 7 (g_count) ; ret                         (3 words)
     fuzz_alloc_fail           slot 4854: auipc a1 ; ld a1 <- A_OBJ 7 (g_count) ; add a0,a1,a0 ; sltu a1,a0,a1 ;
                                          neg a1,a1 ; or a0,a1,a0 ; auipc a1 ; sd a0 -> g_fail_at ; ret        (9 words)
     fuzz_alloc_ran_out        slot 4863: auipc a0 ; lbu a0 <- A_OBJ 11 (g_ran_out, SZ1 unsigned) ; ret        (3 words)
     fuzz_alloc_ran_out_reset  slot 4866: auipc a0 ; sb zero -> g_ran_out ; ret                                (3 words)
   The non-pc-relative words are those of image A' (lib/A/Listing_prog.v slots 4592-4620). The walks read these words
   from the image (build_table over the segments), so a different body fails them. None makes an instrumented access
   or a call: the readers load a static, the writers store into a static, which is PST (PRH_Base.v prh_pst).
   Donors (copied and adapted, not Required): h-w6rep-2's A' relocation origin/cold/h-w6rep-2-p102-allocsurf
   8a019eaaef99, lib/A/Prog/PwAllocSurf.v 428e59506566 (section 4's runs and image checkers, at image B here), and
   its old-pin lib/A/Prog/PwRanOut.v 77105584e9ac / PwRanOutReset.v 5ff92c55a30c (the lbu read, the sb's chunk). The
   released plain / UBSan walks of the same C functions (lib/Prog/fuzz_alloc_*.v, lib/U/Prog) are the rule-24 donors:
   same source, other images; none is Required or cited.
   Opened Section hypothesis: pal_pst_ok, the AL rows' STAND-IN (OwnB_p102.v's text, owner a Theorem Labs lane) for the unit's
   static-placement binding of B; only its first half (PST off as_owned_static B) is used, by the three writers.
   NUMERALS: no ADDRESS literal (the statics are prh_img_B's pi_g_* / pi_gz_*, the entries B_prog_sigma AS_<fn> =
   pa_sigma of PI_prog_B; the listing's objects OBJ_g_* are checked equal to the PrhImg numbers); 3, 5, 9 LENGTH (the
   listings' word counts); 8 LENGTH (a word's bytes: the width bound and the alignment of a static, the stored chunk's
   width); 1 LENGTH (g_ran_out's width, its chunk's width); 32 DERIVED (the symbolic engine's first extra atom, the
   static read); 1, 10 DERIVED (the ISA's register numbers of ra and a0); 64 and 2 ^ 64 WORD (the machine word's width
   and modulus; 2 ^ 64 - 1 is SIZE_MAX); 0, 1 WORD (an absolute region's base, SLit 0, the value stored, the carry). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger FuzzAllocAcc102.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ==== image B' (asan-ubsan, #102: PI_prog_B / prh_img_B on the #102 pins): the seven byte runs, then the texts ==== *)
(* the listing's objects of the seven statics (lib/B/Listing_prog.v's PLdHi operands; PAImg_prog.v B_prog_obj: the
   same object numbers as image A', the OBJ_g_ names of FuzzAllocAcc102.v), each checked equal to prh_img_B's number *)
Lemma acc_objs_B :
  B_prog_val OBJ_g_live = @pi_g_live prh_img_B /\ B_prog_val OBJ_g_peak = @pi_g_peak prh_img_B /\
  B_prog_val OBJ_g_count = @pi_g_count prh_img_B /\ B_prog_val OBJ_g_fail = @pi_g_fail prh_img_B /\
  B_prog_val OBJ_g_ran_out = @pi_g_ran_out prh_img_B /\ B_prog_val OBJ_g_most = @pi_g_most prh_img_B /\
  B_prog_val OBJ_g_own_ran_out = @pi_g_own_ran_out prh_img_B.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* image facts of prh_img_B's seven statics, by computation on the concrete segments *)
Lemma acc_pst_wv_B : acc_pst_allb (acc_wv_b rsegs) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma acc_pst_img_b_B : acc_pst_allb (acc_in_img_b rsegs) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma acc_pst_writable_B : forall (m : word -> option byte) a,
  Exists (in_zr a) (@prh_pst prh_img_B) -> writable_at rsegs m a.
Proof. intros m a Ha. apply acc_writable_of_wv_b. exact (acc_pst_allb_sound _ _ a acc_pst_wv_B Ha). Qed.
Lemma acc_pst_img_B : forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> in_img rsegs a.
Proof. intros a Ha. apply acc_in_img_b_sound. exact (acc_pst_allb_sound _ _ a acc_pst_img_b_B Ha). Qed.
Lemma acc_pst_sep_B : YG0f.pairwise zdisjoint (@prh_pst prh_img_B).
Proof.
unfold prh_pst. cbn [YG0f.pairwise].
repeat match goal with
| |- _ /\ _ => split
| |- True => exact I
| |- Forall _ [] => apply Forall_nil
| |- Forall _ (_ :: _) => apply Forall_cons; [unfold zdisjoint; cbn; lia|]
end.
Qed.
Lemma acc_pst_al_B : Forall (fun r => fst r mod 8 = 0 /\ 0 <= snd r <= 8) (@prh_pst prh_img_B).
Proof.
unfold prh_pst.
repeat match goal with
| |- Forall _ [] => apply Forall_nil
| |- Forall _ (_ :: _) => apply Forall_cons; [cbn; split; [reflexivity | lia]|]
end.
Qed.
Lemma acc_pst_rw_b_B : acc_pst_allb (acc_rw_b rsegs) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma acc_pst_rw_B : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  match find_segment rsegs a 1 with Some seg => seg_writable seg = true | None => True end.
Proof. intros a Ha. exact (acc_rw_of_b rsegs _ a acc_pst_rw_b_B Ha). Qed.
Lemma acc_pst_top_B : forallb (fun r => fst r + snd r <=? TASK_SIZE) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.

(* the tables: the function's own words read from the image (LENGTH 3 / 5 / 9: the listings' word counts) *)
Definition tbl_lv_B : ctable := Eval vm_compute in build_table rsegs (B_prog_sigma AS_fuzz_alloc_live) 3 TEmpty.
Lemma tbl_lv_B_ok : table_ok rsegs tbl_lv_B.
Proof.
assert (E : tbl_lv_B = build_table rsegs (B_prog_sigma AS_fuzz_alloc_live) 3 TEmpty)
  by (vm_cast_no_check (eq_refl tbl_lv_B)).
rewrite E. apply build_table_ok0. cbv. discriminate.
Qed.
Definition tbl_pk_B : ctable := Eval vm_compute in build_table rsegs (B_prog_sigma AS_fuzz_alloc_peak) 3 TEmpty.
Lemma tbl_pk_B_ok : table_ok rsegs tbl_pk_B.
Proof.
assert (E : tbl_pk_B = build_table rsegs (B_prog_sigma AS_fuzz_alloc_peak) 3 TEmpty)
  by (vm_cast_no_check (eq_refl tbl_pk_B)).
rewrite E. apply build_table_ok0. cbv. discriminate.
Qed.
Definition tbl_ct_B : ctable := Eval vm_compute in build_table rsegs (B_prog_sigma AS_fuzz_alloc_count) 3 TEmpty.
Lemma tbl_ct_B_ok : table_ok rsegs tbl_ct_B.
Proof.
assert (E : tbl_ct_B = build_table rsegs (B_prog_sigma AS_fuzz_alloc_count) 3 TEmpty)
  by (vm_cast_no_check (eq_refl tbl_ct_B)).
rewrite E. apply build_table_ok0. cbv. discriminate.
Qed.
Definition tbl_pr_B : ctable := Eval vm_compute in build_table rsegs (B_prog_sigma AS_fuzz_alloc_peak_reset) 5 TEmpty.
Lemma tbl_pr_B_ok : table_ok rsegs tbl_pr_B.
Proof.
assert (E : tbl_pr_B = build_table rsegs (B_prog_sigma AS_fuzz_alloc_peak_reset) 5 TEmpty)
  by (vm_cast_no_check (eq_refl tbl_pr_B)).
rewrite E. apply build_table_ok0. cbv. discriminate.
Qed.
Definition tbl_fl_B : ctable := Eval vm_compute in build_table rsegs (B_prog_sigma AS_fuzz_alloc_fail) 9 TEmpty.
Lemma tbl_fl_B_ok : table_ok rsegs tbl_fl_B.
Proof.
assert (E : tbl_fl_B = build_table rsegs (B_prog_sigma AS_fuzz_alloc_fail) 9 TEmpty)
  by (vm_cast_no_check (eq_refl tbl_fl_B)).
rewrite E. apply build_table_ok0. cbv. discriminate.
Qed.
Definition tbl_ro_B : ctable := Eval vm_compute in build_table rsegs (B_prog_sigma AS_fuzz_alloc_ran_out) 3 TEmpty.
Lemma tbl_ro_B_ok : table_ok rsegs tbl_ro_B.
Proof.
assert (E : tbl_ro_B = build_table rsegs (B_prog_sigma AS_fuzz_alloc_ran_out) 3 TEmpty)
  by (vm_cast_no_check (eq_refl tbl_ro_B)).
rewrite E. apply build_table_ok0. cbv. discriminate.
Qed.
Definition tbl_rr_B : ctable :=
  Eval vm_compute in build_table rsegs (B_prog_sigma AS_fuzz_alloc_ran_out_reset) 3 TEmpty.
Lemma tbl_rr_B_ok : table_ok rsegs tbl_rr_B.
Proof.
assert (E : tbl_rr_B = build_table rsegs (B_prog_sigma AS_fuzz_alloc_ran_out_reset) 3 TEmpty)
  by (vm_cast_no_check (eq_refl tbl_rr_B)).
rewrite E. apply build_table_ok0. cbv. discriminate.
Qed.

(* ---- image B's runs ---- *)
Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation PA := PI_prog_B.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Abbreviation PIB := prh_img_B.

(* the end of a word reader's run: back at ra, a0 = atom 32, memory as it was *)
Ltac acc_rd_ret tbl tblok Hwx Hra HQ HE v :=
  eapply (SRr_ret_at SEGS tbl tblok Hwx _ _); [eassumption | reflexivity | vm_compute; reflexivity |];
  let mat2 := fresh "mat" in intros mat2; rewrite wvb_collapse;
  lazymatch goal with HS : st_ok _ ?E ?ssx (restrict _ ?msx), HF : frame_of _ (ss_mem ?ss0) _ (ms_mem ?msx) |- _ =>
    let Hm := fresh "Hm" in let R1 := fresh "R1" in let R10 := fresh "R10" in
    let E1 := fresh "E1" in let E32 := fresh "E32" in
    assert (Hm : ms_mem msx = _) by exact (frame_of_read_only E (ss_mem ss0) _ _ eq_refl HF);
    rreg HS (1%bv : bv 5) R1; rreg HS (10%bv : bv 5) R10;
    assert (E1 : ew E 1 = getr _ 1) by (rewrite HE; exact (ew_Ereg_nat _ [w64 v] 1 1%bv eq_refl));
    assert (E32 : ew E 32 = w64 v) by (rewrite HE; exact (ew_Ereg_extra _ [w64 v] 0));
    rewrite R1, E1, Hra, Hm;
    apply HQ; [rewrite R10, E32; reflexivity
              | eapply aregs_preserved_of_st_ok; [exact HS | rewrite HE; apply env_agree_refl | vm_compute; reflexivity]]
  end.

Lemma acc_live_run_B : acc_rd_run SEGS (SIGMA AS_fuzz_alloc_live) (@pi_g_live PIB) (@pi_gz_live PIB).
Proof.
intros W regs mem md v Q Hra GV Hv HQ. unfold YK0s.ret_ok in Hra.
pose proof (@pa_wx _ _ PA) as Hwx.
assert (HS : st_ok SEGS (Ereg regs [w64 v]) (acc_ss_rd (B_prog_sigma AS_fuzz_alloc_live) (@pi_g_live PIB) (@pi_gz_live PIB))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (B_prog_sigma AS_fuzz_alloc_live)) mem (seg_rom SEGS))))
  by (apply acc_rd_entry; [vm_compute; reflexivity | exact GV | cbn; lia | cbn; lia | cbn; lia | cbn; lia]).
unfold cfg_at. change (w64 (SIGMA AS_fuzz_alloc_live)) with (Z_to_bv 64 (B_prog_sigma AS_fuzz_alloc_live)).
remember (Ereg regs [w64 v]) as E eqn:HE.
srr_run_with tbl_lv_B_ok HS.
acc_rd_ret tbl_lv_B tbl_lv_B_ok Hwx Hra HQ HE v.
Qed.

Lemma acc_peak_run_B : acc_rd_run SEGS (SIGMA AS_fuzz_alloc_peak) (@pi_g_peak PIB) (@pi_gz_peak PIB).
Proof.
intros W regs mem md v Q Hra GV Hv HQ. unfold YK0s.ret_ok in Hra.
pose proof (@pa_wx _ _ PA) as Hwx.
assert (HS : st_ok SEGS (Ereg regs [w64 v]) (acc_ss_rd (B_prog_sigma AS_fuzz_alloc_peak) (@pi_g_peak PIB) (@pi_gz_peak PIB))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (B_prog_sigma AS_fuzz_alloc_peak)) mem (seg_rom SEGS))))
  by (apply acc_rd_entry; [vm_compute; reflexivity | exact GV | cbn; lia | cbn; lia | cbn; lia | cbn; lia]).
unfold cfg_at. change (w64 (SIGMA AS_fuzz_alloc_peak)) with (Z_to_bv 64 (B_prog_sigma AS_fuzz_alloc_peak)).
remember (Ereg regs [w64 v]) as E eqn:HE.
srr_run_with tbl_pk_B_ok HS.
acc_rd_ret tbl_pk_B tbl_pk_B_ok Hwx Hra HQ HE v.
Qed.

Lemma acc_count_run_B : acc_rd_run SEGS (SIGMA AS_fuzz_alloc_count) (@pi_g_count PIB) (@pi_gz_count PIB).
Proof.
intros W regs mem md v Q Hra GV Hv HQ. unfold YK0s.ret_ok in Hra.
pose proof (@pa_wx _ _ PA) as Hwx.
assert (HS : st_ok SEGS (Ereg regs [w64 v]) (acc_ss_rd (B_prog_sigma AS_fuzz_alloc_count) (@pi_g_count PIB) (@pi_gz_count PIB))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (B_prog_sigma AS_fuzz_alloc_count)) mem (seg_rom SEGS))))
  by (apply acc_rd_entry; [vm_compute; reflexivity | exact GV | cbn; lia | cbn; lia | cbn; lia | cbn; lia]).
unfold cfg_at. change (w64 (SIGMA AS_fuzz_alloc_count)) with (Z_to_bv 64 (B_prog_sigma AS_fuzz_alloc_count)).
remember (Ereg regs [w64 v]) as E eqn:HE.
srr_run_with tbl_ct_B_ok HS.
acc_rd_ret tbl_ct_B tbl_ct_B_ok Hwx Hra HQ HE v.
Qed.

(* fuzz_alloc_ran_out: auipc ; lbu a0 <- g_ran_out ; ret. Back at ra, a0 = the zero-extended byte of atom 32 *)
Lemma acc_ran_out_run_B : acc_rdb_run SEGS (SIGMA AS_fuzz_alloc_ran_out) (@pi_g_ran_out PIB) (@pi_gz_ran_out PIB).
Proof.
intros W regs mem md v Q Hra GV Hv HQ. unfold YK0s.ret_ok in Hra.
pose proof (@pa_wx _ _ PA) as Hwx.
assert (HS : st_ok SEGS (Ereg regs [w64 v])
  (acc_ss_rd (B_prog_sigma AS_fuzz_alloc_ran_out) (@pi_g_ran_out PIB) (@pi_gz_ran_out PIB))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (B_prog_sigma AS_fuzz_alloc_ran_out)) mem (seg_rom SEGS))))
  by (apply acc_rd_entry; [vm_compute; reflexivity | exact GV | cbn; lia | cbn; lia | cbn; lia | cbn; lia]).
unfold cfg_at. change (w64 (SIGMA AS_fuzz_alloc_ran_out)) with (Z_to_bv 64 (B_prog_sigma AS_fuzz_alloc_ran_out)).
remember (Ereg regs [w64 v]) as E eqn:HE.
srr_run_with tbl_ro_B_ok HS.
eapply (SRr_ret_at SEGS tbl_ro_B tbl_ro_B_ok Hwx _ _); [eassumption | reflexivity | vm_compute; reflexivity |].
intros mat2. rewrite wvb_collapse.
lazymatch goal with HS : st_ok _ ?E ?ssx (restrict _ ?msx), HF : frame_of _ (ss_mem ?ss0) _ (ms_mem ?msx) |- _ =>
  assert (Hm : ms_mem msx = _) by exact (frame_of_read_only E (ss_mem ss0) _ _ eq_refl HF);
  rreg HS (1%bv : bv 5) R1; rreg HS (10%bv : bv 5) R10
end.
assert (E1 : ew E 1 = getr regs 1) by (rewrite HE; exact (ew_Ereg_nat regs [w64 v] 1 1%bv eq_refl)).
assert (E32 : ew E 32 = w64 v) by (rewrite HE; exact (ew_Ereg_extra regs [w64 v] 0)).
rewrite R1, E1, Hra, Hm.
apply HQ.
- rewrite R10, E32. unfold w64. apply acc_zext8_small. exact Hv.
- eapply aregs_preserved_of_st_ok; [eassumption | rewrite HE; apply env_agree_refl | vm_compute; reflexivity].
Qed.

(* a writer's run up to its ret, by acc_run_hid *)
Ltac acc_wr_go tbl tblok Hwx HS :=
  lazymatch type of HS with st_ok ?segs ?E0 ?ss (restrict (w_H ?W0) ?ms) =>
    let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
    lazymatch r with (?ss', ?st) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
      apply (acc_run_hid segs tbl tblok Hwx W0 FUEL E0 ss ss' st ms _ _ HS Hrun I)
    end
  end.
(* the frame of a reading writer's run: only the write cell's bytes may change *)
Ltac acc_wr_frame HFr :=
  let x := fresh "x" in let Hx := fresh "Hx" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros x Hx; apply HFr; intros (r & Hin & Hr); apply Hx;
  cbn [ss_mem acc_ss_wr In] in Hin; destruct Hin as [<-|[<-|[]]];
  unfold acc_rcell, acc_wcell, acc_pw_rcell, acc_pw_wcell in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia.

Lemma acc_peak_reset_run_B :
  acc_wr_run SEGS (SIGMA AS_fuzz_alloc_peak_reset) (@pi_g_live PIB) (@pi_gz_live PIB) (@pi_g_peak PIB) (@pi_gz_peak PIB)
    (fun v _ => v).
Proof.
intros W regs mem md v a0 Q Hra _ _ GV Hv HQ. unfold YK0s.ret_ok in Hra.
pose proof (@pa_wx _ _ PA) as Hwx.
assert (HS : st_ok SEGS (Ereg regs [w64 v])
  (acc_ss_wr (B_prog_sigma AS_fuzz_alloc_peak_reset) (@pi_g_live PIB) (@pi_gz_live PIB) (@pi_g_peak PIB) (@pi_gz_peak PIB))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (B_prog_sigma AS_fuzz_alloc_peak_reset)) mem (seg_rom SEGS)))).
{ apply acc_wr_entry; [vm_compute; reflexivity | cbn; lia | exact GV | cbn; lia | cbn; lia | cbn; lia | cbn; lia
    | | cbn; lia | cbn; lia].
  intros x Hx. apply acc_pst_writable_B. exact (acc_cell_pst (PI := PIB) _ _ x acc_in_peak Hx). }
unfold cfg_at. change (w64 (SIGMA AS_fuzz_alloc_peak_reset)) with (Z_to_bv 64 (B_prog_sigma AS_fuzz_alloc_peak_reset)).
remember (Ereg regs [w64 v]) as E eqn:HE.
acc_wr_go tbl_pr_B tbl_pr_B_ok Hwx HS.
intros ms' mat' HS' HFr Hgr Hhid. clear HS.
eapply (SRr_ret_at SEGS tbl_pr_B tbl_pr_B_ok Hwx W E); [exact HS' | reflexivity | vm_compute; reflexivity |].
intros mat2. rewrite wvb_collapse.
rreg HS' (1%bv : bv 5) R1.
assert (E1 : ew E 1 = getr regs 1) by (rewrite HE; exact (ew_Ereg_nat regs [w64 v] 1 1%bv eq_refl)).
assert (E32 : ew E 32 = w64 v) by (rewrite HE; exact (ew_Ereg_extra regs [w64 v] 0)).
rewrite R1, E1, Hra.
destruct (st_ok_mem_ok SEGS E _ _ HS') as (_ & HRS & _). cbn [ms_mem restrict] in HRS.
apply Forall_inv_tail in HRS. apply Forall_inv in HRS.
unfold region_ok in HRS. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRS.
destruct HRS as (_ & _ & _ & HCk). apply Forall_inv in HCk.
assert (Hden : sv_denot E (SOff 32 0) = Z_to_bv 64 v).
{ cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
pose proof (val_of_chunk_ok SEGS E _ 0 _ 8 (SOff 32 0) v HCk Hden ltac:(cbn; lia) ltac:(cbn; lia)) as V.
apply HQ.
- eapply aregs_preserved_of_st_ok; [exact HS' | rewrite HE; apply env_agree_refl | vm_compute; reflexivity].
- acc_wr_frame HFr.
- exact Hgr.
- exact Hhid.
- exact V.
Qed.

Lemma acc_fail_run_B :
  acc_wr_run SEGS (SIGMA AS_fuzz_alloc_fail) (@pi_g_count PIB) (@pi_gz_count PIB) (@pi_g_fail PIB) (@pi_gz_fail PIB)
    (fun c k => if k <? SIZE_MAXZ - c then c + k else SIZE_MAXZ).
Proof.
intros W regs mem md v k Q Hra H10 Hk GV Hv HQ. unfold YK0s.ret_ok in Hra.
pose proof (@pa_wx _ _ PA) as Hwx.
assert (HS : st_ok SEGS (Ereg regs [w64 v])
  (acc_ss_wr (B_prog_sigma AS_fuzz_alloc_fail) (@pi_g_count PIB) (@pi_gz_count PIB) (@pi_g_fail PIB) (@pi_gz_fail PIB))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (B_prog_sigma AS_fuzz_alloc_fail)) mem (seg_rom SEGS)))).
{ apply acc_wr_entry; [vm_compute; reflexivity | cbn; lia | exact GV | cbn; lia | cbn; lia | cbn; lia | cbn; lia
    | | cbn; lia | cbn; lia].
  intros x Hx. apply acc_pst_writable_B. exact (acc_cell_pst (PI := PIB) _ _ x acc_in_fail Hx). }
unfold cfg_at. change (w64 (SIGMA AS_fuzz_alloc_fail)) with (Z_to_bv 64 (B_prog_sigma AS_fuzz_alloc_fail)).
remember (Ereg regs [w64 v]) as E eqn:HE.
acc_wr_go tbl_fl_B tbl_fl_B_ok Hwx HS.
intros ms' mat' HS' HFr Hgr Hhid. clear HS.
eapply (SRr_ret_at SEGS tbl_fl_B tbl_fl_B_ok Hwx W E); [exact HS' | reflexivity | vm_compute; reflexivity |].
intros mat2. rewrite wvb_collapse.
rreg HS' (1%bv : bv 5) R1.
assert (E1 : ew E 1 = getr regs 1) by (rewrite HE; exact (ew_Ereg_nat regs [w64 v] 1 1%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 k) by (rewrite HE; rewrite (ew_Ereg_nat regs [w64 v] 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (rewrite HE; exact (ew_Ereg_extra regs [w64 v] 0)).
rewrite R1, E1, Hra.
destruct (st_ok_mem_ok SEGS E _ _ HS') as (_ & HRS & _). cbn [ms_mem restrict] in HRS.
apply Forall_inv_tail in HRS. apply Forall_inv in HRS.
unfold region_ok in HRS. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRS.
destruct HRS as (_ & _ & _ & HCk). apply Forall_inv in HCk.
set (e := SAlu Instr.ALU_OR (SAlu Instr.ALU_SUB (SLit 0)
    (SAlu Instr.ALU_SLTU (SAlu Instr.ALU_ADD (SOff 10 0) (SOff 32 0)) (SOff 32 0)))
  (SAlu Instr.ALU_ADD (SOff 10 0) (SOff 32 0))) in HCk.
assert (HU : U E e = (if k <? SIZE_MAXZ - v then v + k else SIZE_MAXZ)).
{ subst e. rewrite !U_SAlu, U_SLit, (U_atom E 10 k E10 Hk), (U_atom E 32 v E32 Hv). cbn [zalu_raw].
  exact (acc_sat v k Hv Hk). }
assert (Hden : sv_denot E e = Z_to_bv 64 (if k <? SIZE_MAXZ - v then v + k else SIZE_MAXZ))
  by (rewrite <- HU; unfold U; symmetry; apply Z_to_bv_bv_unsigned).
assert (Hrg : 0 <= (if k <? SIZE_MAXZ - v then v + k else SIZE_MAXZ) < 2 ^ (8 * Z.of_N 8))
  by (destruct (Z.ltb_spec k (SIZE_MAXZ - v)); unfold SIZE_MAXZ in *; cbn; lia).
pose proof (val_of_chunk_ok SEGS E _ 0 _ 8 e _ HCk Hden Hrg ltac:(cbn; lia)) as V.
apply HQ.
- eapply aregs_preserved_of_st_ok; [exact HS' | rewrite HE; apply env_agree_refl | vm_compute; reflexivity].
- acc_wr_frame HFr.
- exact Hgr.
- exact Hhid.
- exact V.
Qed.

(* fuzz_alloc_ran_out_reset: auipc ; sb zero -> g_ran_out ; ret. The one byte written is the write cell's *)
Lemma acc_ran_out_reset_run_B :
  acc_wz_run SEGS (SIGMA AS_fuzz_alloc_ran_out_reset) (@pi_g_ran_out PIB) (@pi_gz_ran_out PIB) 0.
Proof.
intros W regs mem md Q Hra HQ. unfold YK0s.ret_ok in Hra.
pose proof (@pa_wx _ _ PA) as Hwx.
assert (HS : st_ok SEGS (Ereg regs [])
  (acc_ss_wz (B_prog_sigma AS_fuzz_alloc_ran_out_reset) (@pi_g_ran_out PIB) (@pi_gz_ran_out PIB))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (B_prog_sigma AS_fuzz_alloc_ran_out_reset)) mem (seg_rom SEGS)))).
{ apply acc_wz_entry; [vm_compute; reflexivity | | cbn; lia | cbn; lia].
  intros x Hx. apply acc_pst_writable_B. exact (acc_cell_pst (PI := PIB) _ _ x acc_in_ran Hx). }
unfold cfg_at.
change (w64 (SIGMA AS_fuzz_alloc_ran_out_reset)) with (Z_to_bv 64 (B_prog_sigma AS_fuzz_alloc_ran_out_reset)).
remember (Ereg regs []) as E eqn:HE.
acc_wr_go tbl_rr_B tbl_rr_B_ok Hwx HS.
intros ms' mat' HS' HFr Hgr Hhid. clear HS.
eapply (SRr_ret_at SEGS tbl_rr_B tbl_rr_B_ok Hwx W E); [exact HS' | reflexivity | vm_compute; reflexivity |].
intros mat2. rewrite wvb_collapse.
rreg HS' (1%bv : bv 5) R1.
assert (E1 : ew E 1 = getr regs 1) by (rewrite HE; exact (ew_Ereg_nat regs [] 1 1%bv eq_refl)).
rewrite R1, E1, Hra.
(* the byte the store wrote: the write cell's chunk, CVal 1 (SLit 0) at g_ran_out *)
destruct (st_ok_mem_ok SEGS E _ _ HS') as (_ & HRS & _). cbn [ms_mem restrict] in HRS.
apply Forall_inv in HRS.
unfold region_ok in HRS. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRS.
destruct HRS as (_ & _ & _ & HCk). apply Forall_inv in HCk.
pose proof (val_of_chunk_ok SEGS E _ 0 _ 1 (SLit 0) 0 HCk ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
apply HQ.
- eapply aregs_preserved_of_st_ok; [exact HS' | rewrite HE; apply env_agree_refl | vm_compute; reflexivity].
- intros x Hx. apply HFr. intros (r & Hin & Hr). apply Hx.
  cbn [ss_mem acc_ss_wz In] in Hin. destruct Hin as [<-|[]].
  unfold acc_wcell, acc_pw_wcell in Hr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia.
- exact Hgr.
- exact Hhid.
- exact V.
Qed.
End R.

(* ---- the seven TEXTS (a Theorem Labs lane, lib/A/PRH_FnAlloc.v:71-146 at decff67d721f) at image B' (#102), at the AL rows' instance
   (OwnB_p102.v's own_holds_B form): PA := PI_prog_B, PI := prh_img_B, L := B_prog_listing, preset's CfParams,
   a Theorem Labs lane's room-live instance, and the allocator relation ARcfx (ARcf with the error-buffer extents placed). Each
   is its core (FuzzAllocAcc102.v section 3) with the byte run above. ---- *)
Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PA := PI_prog_B.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation PIB := prh_img_B.
#[local] Abbreviation RLa8 := (prh_room_live_a8 (cp := CP)).
Variable B : asyms.
(* the allocator relation (S1KitAlloc's YGcallcf.v ARλ': ARcf and the placed error-buffer extents) *)
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* the allocator's laws at ARcf: h-mani-a8's AR_laws_ok_cf (YG0lawscf.v), and AR_laws_x from them (YGcallcf.v) *)
Let LAWS_cf : AR_laws_cf (cp := CP) SEGS B := AR_laws_ok_cf (cp := CP) SEGS B.
Let LAWS : AR_laws_x SEGS B ARcfx (@cf_head CP) := AR_laws_x_xs (cp := CP) SEGS B LAWS_cf.
(* STAND-IN for the unit's static-placement binding of B (PST off as_owned_static B and off errno) (a Theorem Labs lane): swap by
   citation. OwnB_p102.v's text; the writers use its first half *)
Hypothesis pal_pst_ok : forall a, Exists (in_zr a) (@prh_pst PIB) ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Let PST_OK : forall a, Exists (in_zr a) (@prh_pst PIB) -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) :=
  fun a H => conj (acc_pst_img_B a H) (proj1 (pal_pst_ok a H)).

Theorem fuzz_alloc_live_holds_B :
  tfuzz_alloc_live_specX (cp := CP) (PI := PIB) (RL := RLa8) (L := B_prog_listing) (PA := PA) B ARcfx SK.
Proof. exact (acc_live_core B ARcfx SK _ LAWS acc_live_run_B). Qed.

Theorem fuzz_alloc_peak_holds_B :
  tfuzz_alloc_peak_specX (cp := CP) (PI := PIB) (RL := RLa8) (L := B_prog_listing) (PA := PA) B ARcfx SK.
Proof. exact (acc_peak_core B ARcfx SK _ LAWS acc_peak_run_B). Qed.

Theorem fuzz_alloc_peak_reset_holds_B :
  tfuzz_alloc_peak_reset_specX (cp := CP) (PI := PIB) (RL := RLa8) (L := B_prog_listing) (PA := PA) B ARcfx SK.
Proof.
exact (acc_peak_reset_core B ARcfx SK _ LAWS PST_OK acc_pst_sep_B acc_pst_al_B acc_pst_rw_B acc_pst_top_B
  acc_peak_reset_run_B).
Qed.

Theorem fuzz_alloc_count_holds_B :
  tfuzz_alloc_count_specX (cp := CP) (PI := PIB) (RL := RLa8) (L := B_prog_listing) (PA := PA) B ARcfx SK.
Proof. exact (acc_count_core B ARcfx SK _ LAWS acc_count_run_B). Qed.

Theorem fuzz_alloc_fail_holds_B :
  tfuzz_alloc_fail_specX (cp := CP) (PI := PIB) (RL := RLa8) (L := B_prog_listing) (PA := PA) B ARcfx SK.
Proof.
exact (acc_fail_core B ARcfx SK _ LAWS PST_OK acc_pst_sep_B acc_pst_al_B acc_pst_rw_B acc_pst_top_B acc_fail_run_B).
Qed.

Theorem fuzz_alloc_ran_out_holds_B :
  tfuzz_alloc_ran_out_specX (cp := CP) (PI := PIB) (RL := RLa8) (L := B_prog_listing) (PA := PA) B ARcfx SK.
Proof. exact (acc_ran_out_core B ARcfx SK _ LAWS acc_ran_out_run_B). Qed.

Theorem fuzz_alloc_ran_out_reset_holds_B :
  tfuzz_alloc_ran_out_reset_specX (cp := CP) (PI := PIB) (RL := RLa8) (L := B_prog_listing) (PA := PA) B ARcfx SK.
Proof.
exact (acc_ran_out_reset_core B ARcfx SK _ LAWS PST_OK acc_pst_sep_B acc_pst_al_B acc_pst_rw_B acc_pst_top_B
  acc_ran_out_reset_run_B).
Qed.
End T.
