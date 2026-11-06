(* fuzz_preset lib/A, the #102 re-walk of tx_put on image A': THE INSTANCE WITNESSES of the three image stand-ins
   TxPut102A_Inst.v takes (pal_core, pal_pst_ok, img_shvis), each proved from ONE binding of record of B,
   AF0m.TfibSyms B (lib/A/AF0m.v blob 97f423adf6eb, h-hpreset-7's #102 AF0m: the generated binding of the #102 A'
   image, ELF sha256 bff8519bbe3ea0e4), at PA := PI_prog_A, CfImg_A, CfParams_preset, by vm_compute on the closed
   lists TfibSyms pins.
   rule 24: proves function tx_put (reuse search: the internal file REWALK-102-PLAN.md section T3)
   (kind: instance witnesses of tx_put's image premises; the owner's 16:45Z unit ruling.)
   1. tp_pal_of_tfib : PALibCore from the binding. ts_code pins as_code B = Tfib_code of lib/A/AF0l.v, here RelocA's
      AUDITED A' AF0l, blob dfca6bb1a8d7 (origin/cold/h-rw-pre-4-reloc102-a; owner 17:14Z). The earlier AF0l
      eb3d91d8c440 had every literal 0x94 low and REFUTED PALibCore (the 16:5xZ finding; that refutation is replaced
      by this witness). tpw_code_chk checks every acode field the listing names against PI_prog_A's SIGMA
      (__wrap_free / __wrap_malloc / __interceptor_free / __interceptor_malloc / __asan_memcpy / __asan_memset /
      __wrap_bcmp / __asan_stack_malloc_0, _1, _3) and the two return sites against AF0m's DRV_TRACES singletons, by
      vm_compute (tpw_code_chk_ok); the planted copy with pc_wrap_free + 4 FAILS the same check
      (tpw_code_chk_planted), the negative control. The fields the listing does not name (pc_wrap_memcpy .. strnlen,
      region_is_poisoned, the four spin pcs) were checked against the ELF's own .symtab and words (each at its
      function's +0; each spin pc is `j .` = 0x0000006f; each return site follows a `jal ra`), the commit's table.
      The other parts: tp_cells_of_tfib (as_shadow_cell / as_got_shadow: asyms_ok's aso_const_law puts
      z8 (ANum (as_shadow_cell B)) SHADOW_OFF and z8 (ANum (as_got_shadow B)) (as_shadow_cell B) in as_const B ly =
      Tfib_const ly; the closed list has exactly ONE 8-byte cell holding SHADOW_OFF and exactly ONE holding that
      cell's address, by vm_compute, and they are VAL (A_OBJ 12) / VAL (A_OBJ 0)), tp_got_cell_A,
      tp_rt_below_of_tfib, tp_errno_of_tfib (api_env's first two conjuncts; S1ImgA.v's in_img_b).
   2. tp_pst_of_tfib : no byte of alloc.c's statics (prh_pst, 7 cells) is a runtime-owned static
      (ts_owned: Tfib_owned_static) or errno (ts_errno): a byte-wise check by vm_compute (S1ImgA.v's pst_allb).
   3. tp_shvis_of_tfib : h-mani-a8's img_shadow_vis_cf, AImgShadowVisCf.tfib_img_shadow_vis_cf.
   Every statement passes its instance arguments by name (the owner's 16:49Z rule). No ADDRESS is typed: every
   address is a TfibSyms list's, PI_prog_A's or prh_img_A's. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YM05 YP0b YPsym YC4aP YC1fP YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop YGcfAmx2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img CfImgA CfParamsPreset AF0l AF0m AImgShadowVisCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgCheck.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- the 8-byte constant cells of a list holding a given value: their addresses ---- *)
Definition z8_hit (v : Z) (c : acell) : list Z :=
  match c with
  | ACell (ANum x) w (AV (ANum v')) => if Nat.eqb w 8 && Z.eqb v' v then [x] else []
  | _ => []
  end.
Definition z8_addrs (v : Z) (l : list acell) : list Z := flat_map (z8_hit v) l.

Lemma z8_addrs_in : forall v x l, In (z8 (ANum x) v) l -> In x (z8_addrs v l).
Proof.
intros v x l H. unfold z8_addrs. apply in_flat_map. exists (z8 (ANum x) v). split; [exact H|].
unfold z8_hit, z8, c8. rewrite Z.eqb_refl. cbn. left. reflexivity.
Qed.

(* any layout: Tfib_const ignores it *)
Definition tpw_ly : alayout := ALayout 0 0 0 0 0 0 0 0 0 0 0 0 [] [] 0 [] (0, 0) (fun _ => 0).

(* membership in a list of traces, decided *)
Fixpoint tpw_zl_eqb (u t : list Z) : bool :=
  match u, t with
  | [], [] => true
  | x :: u', y :: t' => Z.eqb x y && tpw_zl_eqb u' t'
  | _, _ => false
  end.
Lemma tpw_zl_eqb_eq : forall u t, tpw_zl_eqb u t = true -> u = t.
Proof.
induction u as [|x u IH]; intros [|y t] H; cbn in H; try discriminate; [reflexivity|].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. exact (IH t H2).
Qed.
Lemma tpw_in_trace : forall (t : list Z) (U : list (list Z)),
  existsb (fun u => tpw_zl_eqb u t) U = true -> In t U.
Proof.
intros t U H. apply existsb_exists in H as (u & Hu & E). apply tpw_zl_eqb_eq in E. subst u. exact Hu.
Qed.

(* the byte-wise disjointness check of the statics from a range list and from errno *)
Definition tpw_off_b (O : list (Z * Z)) (e : Z) (a : Z) : bool :=
  negb (existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) O) && negb ((e <=? a) && (a <? e + 4)).

Lemma tpw_off_b_sound : forall O e a, tpw_off_b O e a = true ->
  ~ Exists (in_zr a) O /\ ~ (e <= a < e + 4).
Proof.
intros O e a H. unfold tpw_off_b in H. apply andb_prop in H as [H1 H2].
apply negb_true_iff in H1. apply negb_true_iff in H2.
split.
- intros Hx. apply Exists_exists in Hx as (r & Hr & Ha). unfold in_zr in Ha.
  assert (E : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) O = true).
  { apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite E in H1. discriminate.
- intros Ha. assert (E : (e <=? a) && (a <? e + 4) = true)
    by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite E in H2. discriminate.
Qed.

Section w. Context {rc : YM05.RunCeil}.
#[local] Abbreviation segsA := (@pa_segs rc A_prog_listing PI_prog_A).
#[local] Abbreviation VALA := (@pa_val rc A_prog_listing PI_prog_A).
#[local] Abbreviation SIGMAA := (@pa_sigma rc A_prog_listing PI_prog_A).

(* ---- 1. PALibCore under the binding ---- *)
(* the shadow cell and the GOT word: the UNIQUE candidates of Tfib_const, the listing's objects *)
Lemma tp_cells_of_tfib : forall B, TfibSyms B ->
  as_shadow_cell B = VALA (A_OBJ 12) /\ as_got_shadow B = VALA (A_OBJ 0).
Proof.
intros B HB. destruct (aso_const_law B (ts_ok B HB) tpw_ly) as (I1 & _ & I3 & _).
rewrite (ts_const B HB tpw_ly) in I1, I3.
apply z8_addrs_in in I1.
assert (E1 : z8_addrs SHADOW_OFF (Tfib_const tpw_ly) = [VALA (A_OBJ 12)]) by (vm_compute; reflexivity).
rewrite E1 in I1. destruct I1 as [C1 | []].
rewrite <- C1 in I3. apply z8_addrs_in in I3.
assert (E2 : z8_addrs (VALA (A_OBJ 12)) (Tfib_const tpw_ly) = [VALA (A_OBJ 0)]) by (vm_compute; reflexivity).
rewrite E2 in I3. destruct I3 as [C2 | []].
split; symmetry; assumption.
Qed.

Lemma tp_got_cell_A : VALA (A_OBJ 0) + 8 <= VALA (A_OBJ 12) \/ VALA (A_OBJ 12) + 8 <= VALA (A_OBJ 0).
Proof. left. vm_compute. discriminate. Qed.

Lemma tp_rt_below_of_tfib : forall B, TfibSyms B ->
  pc_free_ra0 (as_code B) < VALA A_TEXT /\ pc_malloc_ra0 (as_code B) < VALA A_TEXT.
Proof. intros B HB. rewrite (ts_code B HB). split; vm_compute; reflexivity. Qed.

(* errno: below kLowMemEnd, its four bytes image bytes (api_env's first two conjuncts) *)
Lemma tpw_errno_img : pst_allb (in_img_b rsegs) [(TFIB_ERRNO, 4)] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tp_errno_of_tfib : forall B, TfibSyms B ->
  (0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd) /\
  (forall a, as_errno B <= a < as_errno B + 4 -> in_img segsA a).
Proof.
intros B HB. rewrite (ts_errno B HB). split; [unfold TFIB_ERRNO, kLowMemEnd; lia|].
intros a Ha. apply in_img_b_sound. apply (pst_allb_sound (in_img_b rsegs) [(TFIB_ERRNO, 4)] a tpw_errno_img).
apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* the code record against the listing: every acode field the listing names, and the two return sites against
   AF0m's DRV_TRACES singletons *)
Definition tpw_code_chk (c : acode) : bool :=
  (SIGMAA AS___wrap_free =? pc_wrap_free c) && (SIGMAA AS___wrap_malloc =? pc_wrap_malloc c) &&
  (SIGMAA AS___interceptor_free =? pc_free c) && (SIGMAA AS___interceptor_malloc =? pc_malloc c) &&
  (SIGMAA AS___asan_memcpy =? pc_asan_memcpy c) && (SIGMAA AS___asan_memset =? pc_asan_memset c) &&
  (SIGMAA AS___wrap_bcmp =? pc_wrap_bcmp c) &&
  (SIGMAA AS___asan_stack_malloc_0 =? pc_stack_malloc c 0) && (SIGMAA AS___asan_stack_malloc_1 =? pc_stack_malloc c 1) &&
  (SIGMAA AS___asan_stack_malloc_3 =? pc_stack_malloc c 3) &&
  existsb (fun u => tpw_zl_eqb u [pc_malloc_ra0 c]) DRV_TRACES &&
  existsb (fun u => tpw_zl_eqb u [pc_free_ra0 c]) DRV_TRACES.
Lemma tpw_code_chk_ok : tpw_code_chk Tfib_code = true.
Proof. vm_compute. reflexivity. Qed.
(* the NEGATIVE CONTROL: the same record with pc_wrap_free + 4 fails the check *)
Definition tpw_planted : acode :=
  ACode (pc_malloc Tfib_code) (pc_wrap_malloc Tfib_code) (pc_malloc_ra0 Tfib_code) (pc_free Tfib_code)
    (pc_wrap_free Tfib_code + 4) (pc_free_ra0 Tfib_code) (pc_stack_malloc Tfib_code) (pc_asan_memcpy Tfib_code)
    (pc_asan_memset Tfib_code) (pc_wrap_memcpy Tfib_code) (pc_wrap_memset Tfib_code) (pc_wrap_memcmp Tfib_code)
    (pc_wrap_bcmp Tfib_code) (pc_wrap_read Tfib_code) (pc_wrap_fwrite Tfib_code) (pc_wrap_vprintf Tfib_code)
    (pc_wrap_vfprintf Tfib_code) (pc_wrap_fprintf Tfib_code) (pc_wrap_memchr Tfib_code) (pc_wrap_strnlen Tfib_code)
    (pc_region_is_poisoned Tfib_code) (pc_spin_mmapdie Tfib_code) (pc_spin_batch Tfib_code)
    (pc_spin_freearray Tfib_code) (pc_spin_shadow Tfib_code).
Lemma tpw_code_chk_planted : tpw_code_chk tpw_planted = false.
Proof. vm_compute. reflexivity. Qed.

(* THE WITNESS: PALibCore from the binding *)
Lemma tp_pal_of_tfib : forall B, TfibSyms B -> PALibCore (rc := rc) (L := A_prog_listing) (PI := PI_prog_A) B.
Proof.
intros B HB. destruct (tp_cells_of_tfib B HB) as [Hc Hg]. destruct (tp_errno_of_tfib B HB) as [He Hi].
pose proof (tp_rt_below_of_tfib B HB) as Hrt.
constructor.
- exact Hg.
- exact Hc.
- exact tp_got_cell_A.
- split; [exact He|]. split; [exact Hi|]. rewrite (ts_code B HB). split.
  + apply (ts_universe_drv B HB). apply tpw_in_trace. vm_compute. reflexivity.
  + apply (ts_universe_drv B HB). apply tpw_in_trace. vm_compute. reflexivity.
- rewrite (ts_code B HB). vm_compute. reflexivity.
- rewrite (ts_code B HB). vm_compute. reflexivity.
- exact Hrt.
Qed.

(* ---- 2. alloc.c's statics are neither runtime-owned statics nor errno ---- *)
Lemma tpw_pst_check : pst_allb (tpw_off_b Tfib_owned_static TFIB_ERRNO) (@prh_pst prh_img_A) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tp_pst_of_tfib : forall B, TfibSyms B ->
  forall a, Exists (in_zr a) (@prh_pst prh_img_A) ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B HB a Ha. rewrite (ts_owned B HB), (ts_errno B HB).
apply tpw_off_b_sound. exact (pst_allb_sound _ _ a tpw_pst_check Ha).
Qed.

(* ---- 3. the image's shadow is present in every ARcf state (h-mani-a8's AImgShadowVisCf) ---- *)
Lemma tp_shvis_of_tfib : forall B, TfibSyms B ->
  YGcfAmx2.img_shadow_vis_cf (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) segsA B.
Proof. intros B HB. exact (tfib_img_shadow_vis_cf (rc := rc) (cp := CfParams_preset) segsA B HB). Qed.
End w.
