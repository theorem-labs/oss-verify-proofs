(* fuzz_preset lib/B, the #102 re-walk of tx_put on image B' (asan-ubsan pin d663f82d7f488d30): INSTANCE WITNESSES
   of TxPut102B_Base.v's tp_img fields that are facts of the IMAGE BINDING of B (lane TxPutB102, h-rw-pre-7; owner
   ruling 16:45Z / 16:5xZ: reduce them to ONE `TB : TfibSyms B`, the unit's symbol binding, which the top supplies).
   TfibSyms is the B' YF0m of record for building, lib/Reusable/YF0m.v blob f82202ebccdf (origin/cold/h-pre-b3-bp-startup
   f07f899fdd07, generated from the B' pin d663f82d; owner ruling 16:44Z: of record for ACCEPTANCE only after
   h-rw-ide-9's full B' gate). Mirror of the A' lane's TxPut102A_Wit.v route (TxPutA102, 16:5xZ).
   rule 24: proves function tx_put (reuse search: the internal file REWALK-102-PLAN.md section T3)
   - tpw_pst_owned / tpw_pst_errno (tpi_pst_owned / tpi_pst_errno): from ts_owned / ts_errno and a disjointness check
     of prh_pst's cells (prh_img_B) against Tfib_owned_static / TFIB_ERRNO, by vm_compute;
   - tp_shvis_of_tfib_B (tpi_img_shvis): YImgShadowCoverCf.img_shadow_vis_cf_of_cover at CfImg_B's own bounds
     cf_img_lo / cf_img_top (h-mani-a8's per-instance rule, 18:56Z; no YImgTop bound), its cover check of YF0m's
     Tfib_zero_shadow / Tfib_const_shadow by vm_compute, the two inclusions from ts_zsh / ts_const.
   - tp_pal_of_tfib_B (tpi_pal, PALibCore at PI_prog_B): the shadow cell / GOT word as the UNIQUE 8-byte cells of
     Tfib_const holding SHADOW_OFF / that cell's address (asyms_ok's aso_const_law + ts_const), the wrapper entries and
     the two ra0 (below the text, and singletons of DRV_TRACES, in the universe by ts_universe_drv) by ts_code, errno
     by ts_errno, each by vm_compute. ts_code's Tfib_code is h-mani-a4's #102 B' code record, lib/Reusable/YF0l.v
     4a405a3dba65 over YImgCellsB.v f1cc7493a79d (origin/cold/h-mani-a4-b102-cells d54322f67714, of record per the
     owner 17:14Z), checked field by field against the listing's SIGMA (TxPutB102 17:2xZ table: all EQUAL, the planted
     pc_wrap_malloc + 4 control FAILS). A' twin: TxPut102A_Wit.v 85ddc58906d2 (route of tp_cells_of_tfib et al.).
   Numerals: none of its own; every address is YF0m's or PRH_ImgB's. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfAmx2 YImgShadowCover YImgShadowCoverCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbq YP0b YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YF0l YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ---- a list of cells avoids a list of ranges, by a boolean check ---- *)
Definition tpw_disjb (c r : Z * Z) : bool := (fst c + snd c <=? fst r) || (fst r + snd r <=? fst c).
Lemma tpw_disj_check : forall (cs rs : list (Z * Z)),
  forallb (fun c => forallb (tpw_disjb c) rs) cs = true ->
  forall a, Exists (in_zr a) cs -> ~ Exists (in_zr a) rs.
Proof.
intros cs rs H a Hc Hr. apply Exists_exists in Hc as (c & Hcin & Hca). apply Exists_exists in Hr as (r & Hrin & Hra).
rewrite forallb_forall in H. specialize (H c Hcin). rewrite forallb_forall in H. specialize (H r Hrin).
unfold tpw_disjb in H. apply orb_true_iff in H. unfold in_zr in Hca, Hra.
destruct H as [H | H]; apply Z.leb_le in H; lia.
Qed.

#[local] Existing Instance prh_img_B.

(* ---- tpi_pst_owned: no cell of prh_pst is a runtime-owned static ---- *)
Lemma tpw_pst_owned_check :
  forallb (fun c => forallb (tpw_disjb c) Tfib_owned_static) prh_pst = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tpw_pst_owned : forall B, TfibSyms B ->
  forall a, Exists (in_zr a) prh_pst -> ~ Exists (in_zr a) (as_owned_static B).
Proof. intros B TB a Ha. rewrite (ts_owned B TB). exact (tpw_disj_check _ _ tpw_pst_owned_check a Ha). Qed.

(* ---- tpi_pst_errno: no cell of prh_pst meets errno's 4 bytes ---- *)
Lemma tpw_pst_errno_check : forallb (fun c => forallb (tpw_disjb c) [(TFIB_ERRNO, 4)]) prh_pst = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tpw_pst_errno : forall B, TfibSyms B ->
  forall a, Exists (in_zr a) prh_pst -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B TB a Ha He. rewrite (ts_errno B TB) in He.
apply (tpw_disj_check _ _ tpw_pst_errno_check a Ha). apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* ---- tpi_img_shvis: the image's shadow is present in every ARcf state, over CfImg_B's own image bounds
   cf_img_lo / cf_img_top (h-mani-a8's per-instance rule, 18:56Z) ---- *)
Lemma tpw_img_shadow_cover :
  img_shadow_cover Tfib_zero_shadow Tfib_const_shadow (@cf_img_lo CfImg_B) (@cf_img_top CfImg_B) = true.
Proof. vm_compute. reflexivity. Qed.

(* ======================= PALibCore at PI_prog_B under the binding (A' TxPut102A_Wit.v's route) ======================= *)
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
Definition tpw_ly : alayout := ALayout 0 0 0 0 0 0 0 0 0 0 0 0 [] [] 0 [] (0, 0) (fun _ => 0).
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
Lemma tpw_in_trace : forall (t : list Z) (U : list (list Z)), existsb (fun u => tpw_zl_eqb u t) U = true -> In t U.
Proof. intros t U H. apply existsb_exists in H as (u & Hu & E). apply tpw_zl_eqb_eq in E. subst u. exact Hu. Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation segsB := (@pa_segs rc B_prog_listing PI_prog_B).
#[local] Abbreviation VALB := (@pa_val rc B_prog_listing PI_prog_B).
#[local] Abbreviation SIGMAB := (@pa_sigma rc B_prog_listing PI_prog_B).

Lemma tp_cells_of_tfib_B : forall B, TfibSyms B ->
  as_shadow_cell B = VALB (A_OBJ 12) /\ as_got_shadow B = VALB (A_OBJ 0).
Proof.
intros B HB. destruct (aso_const_law B (ts_ok B HB) tpw_ly) as (I1 & _ & I3 & _).
rewrite (ts_const B HB tpw_ly) in I1, I3.
apply z8_addrs_in in I1.
assert (E1 : z8_addrs SHADOW_OFF (Tfib_const tpw_ly) = [VALB (A_OBJ 12)]) by (vm_compute; reflexivity).
rewrite E1 in I1. destruct I1 as [C1 | []].
rewrite <- C1 in I3. apply z8_addrs_in in I3.
assert (E2 : z8_addrs (VALB (A_OBJ 12)) (Tfib_const tpw_ly) = [VALB (A_OBJ 0)]) by (vm_compute; reflexivity).
rewrite E2 in I3. destruct I3 as [C2 | []].
split; symmetry; assumption.
Qed.

Lemma tp_got_cell_B : VALB (A_OBJ 0) + 8 <= VALB (A_OBJ 12) \/ VALB (A_OBJ 12) + 8 <= VALB (A_OBJ 0).
Proof. left. vm_compute. discriminate. Qed.

Lemma tpw_errno_img_B : S1ImgCheck.pst_allb (S1ImgCheck.in_img_b rsegs) [(TFIB_ERRNO, 4)] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tp_pal_of_tfib_B : forall B, TfibSyms B -> PALibCore (rc := rc) (L := B_prog_listing) (PI := PI_prog_B) B.
Proof.
intros B HB. destruct (tp_cells_of_tfib_B B HB) as [Ec Eg].
constructor.
- exact Eg.
- exact Ec.
- exact tp_got_cell_B.
- split; [|split].
  + rewrite (ts_errno B HB). unfold TFIB_ERRNO, kLowMemEnd. lia.
  + intros a Ha. rewrite (ts_errno B HB) in Ha. apply S1ImgCheck.in_img_b_sound.
    apply (S1ImgCheck.pst_allb_sound (S1ImgCheck.in_img_b rsegs) [(TFIB_ERRNO, 4)] a tpw_errno_img_B).
    apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  + rewrite (ts_code B HB). split; apply (ts_universe_drv B HB); apply tpw_in_trace; vm_compute; reflexivity.
- rewrite (ts_code B HB). vm_compute. reflexivity.
- rewrite (ts_code B HB). vm_compute. reflexivity.
- rewrite (ts_code B HB). split; vm_compute; reflexivity.
Qed.

Lemma tp_pst_of_tfib_B : forall B, TfibSyms B ->
  forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof. intros B HB a Ha. exact (conj (tpw_pst_owned B HB a Ha) (tpw_pst_errno B HB a Ha)). Qed.

Lemma tp_shvis_of_tfib_B : forall B, TfibSyms B ->
  YGcfAmx2.img_shadow_vis_cf (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) segsB B.
Proof.
intros B HB. apply (img_shadow_vis_cf_of_cover (ci := CfImg_B) segsB B Tfib_zero_shadow Tfib_const_shadow
  tpw_img_shadow_cover).
- rewrite (ts_zsh B HB). apply incl_refl.
- intros ly. rewrite (ts_const B HB ly). unfold Tfib_const. intros x Hx. apply in_or_app. right. apply in_or_app. right.
  exact Hx.
Qed.
End p.
