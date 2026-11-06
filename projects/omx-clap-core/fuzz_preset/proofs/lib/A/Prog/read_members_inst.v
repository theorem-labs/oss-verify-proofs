(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102: bin/fuzz_preset/fuzz_preset.asan sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44): THE INSTANCE of the parametric read_members walk
   (lib/A/Prog/read_members.v, read_members_holds) at the whole-program listing's image PA := PI_prog_A (lib/A/PAImg_prog.v
   505a51ff7d08, listing lib/A/Listing_prog.v 7ed1529926bd), the A' asyms record B := AD2l.TfibB (lib/A/AD2l.v eb321db7a357
   over lib/A/AF0m.v 97f423adf6eb, AF0l dfca6bb1a8d7, ACej c4a400418590: the A' record files, by path from
   origin/cold/h-rw-man-5-palib102i d00dd1234426) and the allocator instance ARx := ARcf rsegs TfibB at CfParams_preset.
   DISCHARGED HERE: the laws and PALib (lib/A/PALibA.v 88c72c8175cf, palib_laws_A / palib_A, by path from the same branch,
   with lib/Reusable/YStrtodRowX.v 10e84e44e24e); HW by CfParamsPreset.preset_head_wide; RM_IMG (RM_IMG_at_Ap) and the image
   facts of PI_prog_A (the rmA_ lemmas), each by vm_compute over a boolean check whose soundness is proved below (the
   checks and their soundness are RmAsanB's lib/B/Prog/read_members_Bp.v f2eefa03e0b8, at image A's record and listing).
   REMAINING PREMISES of read_members_holds_inst: the two callee texts tpj_get_specX / tpj_get_str_specX at this
   instance. (The former gap premise RM_G3 is gone: the walk takes both its halves from the laws at cf_head, fields 14
   alx_hshadow and 22 alx_hhead of palib_laws_A.) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l AF0m PALibA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnPj PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import read_members.
From Stdlib Require Import List.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======== boolean checks over a segment list and an asyms record, and their soundness (RmAsanB's, image-free) ======== *)
Definition rmA_rng (p n : Z) : list Z := map (fun i => p + Z.of_nat i) (seq 0 (Z.to_nat n)).
Lemma rmA_rng_in : forall p n a, p <= a < p + n -> In a (rmA_rng p n).
Proof.
intros p n a Ha. unfold rmA_rng. apply in_map_iff. exists (Z.to_nat (a - p)). split; [lia|].
apply in_seq. lia.
Qed.
Definition rmA_ro_b (segs : list Segment) (rlo rhi a : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
    segs || ((rlo <=? a) && (a <? rhi)).
Lemma rmA_ro_b_ok : forall segs rlo rhi a, in_roP segs rlo rhi a <-> rmA_ro_b segs rlo rhi a = true.
Proof.
intros segs rlo rhi a. unfold in_roP, rmA_ro_b. rewrite Bool.orb_true_iff, existsb_exists. split.
- intros [(s & Hs & Hw & Hr) | Hr]; [left; exists s; split; [exact Hs|] | right].
  + rewrite Hw. cbn. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  + apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- intros [(s & Hs & Hb) | Hb].
  + left. exists s. apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [Hw H1].
    apply negb_true_iff in Hw. apply Z.leb_le in H1. apply Z.ltb_lt in H2. split; [exact Hs|]. split; [exact Hw | lia].
  + right. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
(* the first const cell z1 (ANum s) v of a list *)
Fixpoint rmA_cfind (s : Z) (l : list acell) : option Z :=
  match l with
  | [] => None
  | ACell (ANum x) 1 (AV (ANum v)) :: r => if x =? s then Some v else rmA_cfind s r
  | _ :: r => rmA_cfind s r
  end.
Lemma rmA_cfind_in : forall s l v, rmA_cfind s l = Some v -> In (z1 (ANum s) v) l.
Proof.
intros s l. induction l as [|c r IH]; intros v H; [discriminate H|].
destruct c as [ca cw cv]. cbn [rmA_cfind] in H.
destruct ca; try (right; exact (IH v H)).
destruct cw as [|[|cw]]; try (right; exact (IH v H)).
destruct cv as [ce|mask w]; [|right; exact (IH v H)].
destruct ce; try (right; exact (IH v H)).
destruct (Z.eqb_spec z s) as [->|_]; [injection H as <-; left; reflexivity | right; exact (IH v H)].
Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {RL : PrhRoomLive} {ci : CfImg}.
Variable SK : YI16.sink_head.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TA := AD2l.TfibB.
#[local] Abbreviation ARI := (YG0ncf.ARcf (cp := CP) rsegs TA).
#[local] Abbreviation PIA := (PI_prog_A (rc := rc)).
#[local] Abbreviation SEGSA := (@pa_segs _ A_prog_listing PIA).
#[local] Abbreviation VALA := (@pa_val _ A_prog_listing PIA).
#[local] Abbreviation PSTA := (@prh_pst prh_img_A).
(* the record's const cells, layout-free (AF0m.v Tfib_const) *)
Definition rmA_const : list acell := AF0m.Tfib_const_sym ++ AF0m.Tfib_const_abs ++ AF0m.Tfib_const_shadow.
Lemma rmA_const_eq : forall ly, as_const TA ly = rmA_const.
Proof. intros ly. reflexivity. Qed.

Definition rmA_zs_b (a n : Z) : bool :=
  existsb (fun r => (fst r <=? a) && (a + n <=? fst r + snd r)) (as_zero_shadow TA).
Lemma rmA_zs_b_ok : forall a n, rmA_zs_b a n = true -> in_zs TA a n.
Proof.
intros a n H. apply existsb_exists in H as ([q m] & Hin & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists q, m. cbn [fst snd] in *. split; [exact Hin | lia].
Qed.
Definition rmA_rsh_b (a : Z) : bool :=
  rmA_zs_b (a - a mod 8) 8 ||
  match rmA_cfind (shadow_addr a) rmA_const with Some v => (v =? 0) || ((a mod 8 <? v) && (v <? 8)) | None => false end.
Lemma rmA_rsh_b_ok : forall a, rmA_rsh_b a = true -> ro_shadow_ok TA a.
Proof.
intros a H. unfold rmA_rsh_b in H. apply Bool.orb_true_iff in H as [H|H]; [left; exact (rmA_zs_b_ok _ _ H)|].
destruct (rmA_cfind (shadow_addr a) rmA_const) as [v|] eqn:Ef; [|discriminate H].
right. exists v. split; [intros ly; rewrite rmA_const_eq; exact (rmA_cfind_in _ _ _ Ef)|].
apply Bool.orb_true_iff in H as [H|H]; [left; apply Z.eqb_eq; exact H|].
right. apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.
Definition rmA_pres_b (a : Z) : bool :=
  rmA_zs_b (a - a mod 8) 8 || match rmA_cfind (shadow_addr a) rmA_const with Some _ => true | None => false end.
Lemma rmA_pres_b_ok : forall a, rmA_pres_b a = true ->
  in_zs TA (a - a mod 8) 8 \/ exists v, forall ly, In (z1 (ANum (shadow_addr a)) v) (as_const TA ly).
Proof.
intros a H. unfold rmA_pres_b in H. apply Bool.orb_true_iff in H as [H|H]; [left; exact (rmA_zs_b_ok _ _ H)|].
destruct (rmA_cfind (shadow_addr a) rmA_const) as [v|] eqn:Ef; [|discriminate H].
right. exists v. intros ly. rewrite rmA_const_eq. exact (rmA_cfind_in _ _ _ Ef).
Qed.
Definition rmA_byte_b (a : Z) : bool :=
  rmA_ro_b SEGSA (@pa_relro_lo _ _ PIA) (@pa_relro_hi _ _ PIA) a &&
  negb (existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) (as_owned_static TA)) &&
  negb ((as_errno TA <=? a) && (a <? as_errno TA + 4)) && rmA_rsh_b a.
Definition rmA_kept_b (p n : Z) : bool :=
  (@pa_lo _ _ PIA + 64 <=? p) && (p + n + 64 <=? @pa_hi _ _ PIA) && forallb rmA_byte_b (rmA_rng p n).
Lemma rmA_kept_b_ok : forall p n, rmA_kept_b p n = true -> kept_img (PA := PIA) TA p n.
Proof.
intros p n H. unfold rmA_kept_b in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. rewrite forallb_forall in H3.
split; [exact H1|]. split; [exact H2|]. intros a Ha. specialize (H3 a (rmA_rng_in p n a Ha)). unfold rmA_byte_b in H3.
apply andb_prop in H3 as [H3 Hs]. apply andb_prop in H3 as [H3 He]. apply andb_prop in H3 as [Hr Ho].
split; [apply rmA_ro_b_ok; exact Hr|]. split; [|split; [|exact (rmA_rsh_b_ok a Hs)]].
- intros HE. apply Exists_exists in HE as ([q m] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
  apply negb_true_iff in Ho.
  assert (Ht : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) (as_owned_static TA) = true).
  { apply existsb_exists. exists (q, m). split; [exact Hin|]. cbn [fst snd].
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  congruence.
- intros Hea. apply negb_true_iff in He.
  assert (Ht : (as_errno TA <=? a) && (a <? as_errno TA + 4) = true)
    by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  congruence.
Qed.

(* ======== RM_IMG at the A' record (h-verbs-1's ruling: discharged at the instance by vm_compute) ======== *)
Definition rmA_keys_b : bool :=
  forallb (fun kn => rmA_kept_b (fst kn) (snd kn + 1) &&
    forallb rmA_pres_b (rmA_rng (fst kn / 64 * 64) ((fst kn + snd kn) / 64 * 64 + 64 - fst kn / 64 * 64)))
    (rm_keys (PA := PIA)).
Lemma rmA_keys_b_true : rmA_keys_b = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rmA_top_b_true : rmA_kept_b (VALA (A_OBJ 3)) 48 = true.
Proof. vm_compute. reflexivity. Qed.
Definition rmA_al_b : bool := forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) (as_zero_shadow TA).
Lemma rmA_al_b_true : rmA_al_b = true.
Proof. vm_compute. reflexivity. Qed.

Lemma RM_IMG_at_Ap : (forall k n, In (k, n) (rm_keys (PA := PIA)) -> kept_img (PA := PIA) TA k (n + 1) /\
    (forall a, k / 64 * 64 <= a < (k + n) / 64 * 64 + 64 ->
       in_zs TA (a - a mod 8) 8 \/ exists v, forall ly, In (z1 (ANum (shadow_addr a)) v) (as_const TA ly))) /\
  kept_img (PA := PIA) TA (VALA (A_OBJ 3)) 48 /\
  Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow TA).
Proof.
split; [|split].
- intros k n Hin. pose proof rmA_keys_b_true as H. unfold rmA_keys_b in H. rewrite forallb_forall in H.
  specialize (H (k, n) Hin). cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
  split; [exact (rmA_kept_b_ok _ _ H1)|]. rewrite forallb_forall in H2.
  intros a Ha. apply rmA_pres_b_ok. apply H2. apply rmA_rng_in. lia.
- exact (rmA_kept_b_ok _ _ rmA_top_b_true).
- pose proof rmA_al_b_true as H. unfold rmA_al_b in H. rewrite forallb_forall in H. apply Forall_forall.
  intros r Hr. specialize (H r Hr). apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
  split; assumption.
Qed.

(* ======== the image facts of PI_prog_A ======== *)
Lemma rmA_ent : @pa_sigma _ _ PIA AS_read_members = VALA A_TEXT + AF_rm.
Proof. vm_compute. reflexivity. Qed.
Definition rmA_obj_b : bool :=
  (0 <=? VALA (A_OBJ 0)) && (VALA (A_OBJ 0) + 8 <=? kLowMemEnd) && (0 <=? VALA (A_OBJ 12)) &&
  (VALA (A_OBJ 12) + 8 <=? kLowMemEnd).
Lemma rmA_obj_b_true : rmA_obj_b = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rmA_obj : forall i, 0 <= i < 8 ->
  0 <= VALA (A_OBJ 0) + i < kLowMemEnd /\ 0 <= VALA (A_OBJ 12) + i < kLowMemEnd.
Proof.
intros i Hi. pose proof rmA_obj_b_true as H. unfold rmA_obj_b in H.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. lia.
Qed.
Lemma rmA_lo : @pa_lo _ _ PIA = IMG_LO.
Proof. reflexivity. Qed.
Lemma rmA_hi : @pa_hi _ _ PIA = IMG_TOP.
Proof. reflexivity. Qed.
(* the thirteen key literals: n non-NUL bytes, the NUL, then image bytes to the end of the granules *)
Definition rmA_lit_b (k n : Z) : bool :=
  forallb (fun j => match rm_rom (PA := PIA) (k + j) with Some c => negb (c =? 0) | None => false end) (rmA_rng 0 n) &&
  match rm_rom (PA := PIA) (k + n) with Some c => c =? 0 | None => false end &&
  forallb (fun j => match rm_rom (PA := PIA) (k + j) with Some _ => true | None => false end) (rmA_rng 0 (n + 8)).
Definition rmA_lits_b : bool := forallb (fun kn => rmA_lit_b (fst kn) (snd kn)) (rm_keys (PA := PIA)).
Lemma rmA_lits_b_true : rmA_lits_b = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rmA_lits : forall k n, In (k, n) (rm_keys (PA := PIA)) ->
  (forall j, 0 <= j < n -> exists c, rm_rom (PA := PIA) (k + j) = Some c /\ c <> 0) /\ rm_rom (PA := PIA) (k + n) = Some 0 /\
  (forall j, 0 <= j < n + 8 -> rm_rom (PA := PIA) (k + j) <> None).
Proof.
intros k n Hin. pose proof rmA_lits_b_true as T. unfold rmA_lits_b in T. rewrite forallb_forall in T.
specialize (T (k, n) Hin). cbn [fst snd] in T. unfold rmA_lit_b in T.
apply andb_prop in T as [T H3]. apply andb_prop in T as [H1 H2]. rewrite forallb_forall in H1, H3.
split; [|split].
- intros j Hj. specialize (H1 j (rmA_rng_in 0 n j ltac:(lia))).
  destruct (rm_rom (PA := PIA) (k + j)) as [c|]; [|discriminate H1].
  exists c. split; [reflexivity|]. apply negb_true_iff, Z.eqb_neq in H1. exact H1.
- destruct (rm_rom (PA := PIA) (k + n)) as [c|]; [|discriminate H2]. apply Z.eqb_eq in H2. subst c. reflexivity.
- intros j Hj. specialize (H3 j (rmA_rng_in 0 (n + 8) j ltac:(lia))).
  destruct (rm_rom (PA := PIA) (k + j)); [discriminate | discriminate H3].
Qed.
(* the static table `top`: its i-th word is the i-th key's address *)
Lemma rmA_top : forall i, (i < 6)%nat ->
  rdword (rm_rom (PA := PIA)) (VALA (A_OBJ 3) + 8 * Z.of_nat i) = Some (fst (nth i (rm_keys (PA := PIA)) (0, 0))).
Proof. intros i Hi. do 6 (destruct i as [|i]; [vm_compute; reflexivity|]). lia. Qed.
(* no program static is a read-only byte *)
Definition rmA_pst_b : bool :=
  forallb (fun r => forallb (fun a => negb (rmA_ro_b SEGSA (@pa_relro_lo _ _ PIA) (@pa_relro_hi _ _ PIA) a))
    (rmA_rng (fst r) (snd r))) PSTA.
Lemma rmA_pst_b_true : rmA_pst_b = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rmA_pst : forall a, in_roP SEGSA (@pa_relro_lo _ _ PIA) (@pa_relro_hi _ _ PIA) a -> ~ Exists (in_zr a) PSTA.
Proof.
intros a Hro HE. apply Exists_exists in HE as ([q m] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
pose proof rmA_pst_b_true as H. unfold rmA_pst_b in H. rewrite forallb_forall in H. specialize (H (q, m) Hin).
rewrite forallb_forall in H. specialize (H a (rmA_rng_in q m a ltac:(lia))).
apply rmA_ro_b_ok in Hro. rewrite Hro in H. discriminate H.
Qed.

(* ======== THE INSTANCE ======== *)
Theorem read_members_holds_inst :
  tpj_get_specX (cp := CP) (PI := prh_img_A) (PA := PIA) TA ARI SK ->
  tpj_get_str_specX (cp := CP) (PI := prh_img_A) (PA := PIA) TA ARI SK ->
  tread_members_specX (cp := CP) (PI := prh_img_A) (PA := PIA) TA ARI SK.
Proof.
intros PJ PJS.
eapply (read_members_holds (fx := fx) (rc := rc) (cp := CP) (RL := RL) (PA := PIA) TA ARI SK).
all: first [ exact (PALibA.palib_laws_A (rc := rc)) | exact (PALibA.palib_A (rc := rc)) | exact PJ | exact PJS
           | exact RM_IMG_at_Ap | exact rmA_ent | exact rmA_obj | exact rmA_lo | exact rmA_hi | exact rmA_lits
           | exact rmA_top | exact rmA_pst | exact CfParamsPreset.preset_head_wide ].
Qed.
End i.

Set Printing Implicit.
Check read_members_holds_inst.
Unset Printing Implicit.
Print Assumptions read_members_holds_inst.
