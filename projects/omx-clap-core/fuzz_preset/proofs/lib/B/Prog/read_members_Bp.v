(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102: pin sha256 d663f82d7f488d30): THE INSTANCE of the
   parametric read_members walk (lib/B/Prog/read_members.v, read_members_holds) at the whole-program listing's image
   PA := PI_prog_B (lib/B/PAImg_prog.v, IMG_TOP_B of lib/Reusable/YImgTop.v d2a97d3111ce), the B' asyms record
   B := YD2l.TfibB (lib/Reusable/YD2l.v 95803a8b9493, over YF0m f82202ebccdf, YF0l 4a405a3dba65, YCej 8a099324acb0,
   YImgCellsB f1cc7493a79d: h-pre-b3's #102 records, by path from origin/cold/h-rw-man-5-palib102bj ed438196d17c)
   and the allocator instance ARx := ARcf rsegs TfibB at CfParams_preset (h-mani-a8's second instance).
   DISCHARGED HERE: the laws and the PALib core (lib/B/PALibB.v 5baa19c890f7, exvi_eh_laws / exvi_eh_palib, by path from
   the same branch); RM_IMG (RM_IMG_at_Bp) and the pure image facts of PI_prog_B (the rmB_ lemmas), each by vm_compute over a
   boolean check whose soundness is proved below.
   REMAINING PREMISES of read_members_holds_Bp: the two callee texts tpj_get_specX / tpj_get_str_specX at this
   instance. (The former gap premise RM_G3 is gone: the walk takes both its halves from the laws at cf_head, fields 14
   alx_hshadow and 22 alx_hhead of exvi_eh_laws.) *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YF0m YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnPj PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import read_members.
From Stdlib Require Import List.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======== boolean checks over a segment list and an asyms record, and their soundness ======== *)
Definition rm_rng (p n : Z) : list Z := map (fun i => p + Z.of_nat i) (seq 0 (Z.to_nat n)).
Lemma rm_rng_in : forall p n a, p <= a < p + n -> In a (rm_rng p n).
Proof.
intros p n a Ha. unfold rm_rng. apply in_map_iff. exists (Z.to_nat (a - p)). split; [lia|].
apply in_seq. lia.
Qed.
Definition rm_img_b (segs : list Segment) (a : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs.
Lemma rm_img_b_ok : forall segs a, rm_img_b segs a = true -> in_img segs a.
Proof.
intros segs a H. apply existsb_exists in H as (s & Hs & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists s. split; [exact Hs | lia].
Qed.
Definition rm_ro_b (segs : list Segment) (rlo rhi a : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
    segs || ((rlo <=? a) && (a <? rhi)).
Lemma rm_ro_b_ok : forall segs rlo rhi a, in_roP segs rlo rhi a <-> rm_ro_b segs rlo rhi a = true.
Proof.
intros segs rlo rhi a. unfold in_roP, rm_ro_b. rewrite Bool.orb_true_iff, existsb_exists. split.
- intros [(s & Hs & Hw & Hr) | Hr]; [left; exists s; split; [exact Hs|] | right].
  + rewrite Hw. cbn. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  + apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- intros [(s & Hs & Hb) | Hb].
  + left. exists s. apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [Hw H1].
    apply negb_true_iff in Hw. apply Z.leb_le in H1. apply Z.ltb_lt in H2. split; [exact Hs|]. split; [exact Hw | lia].
  + right. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Definition rm_rom_eqb (segs : list Segment) (x c : Z) : bool :=
  match seg_rom segs (Z_to_bv 64 x) with Some b => bv_unsigned b =? c | None => false end.
Lemma rm_rom_eqb_ok : forall segs x c, rm_rom_eqb segs x c = true -> seg_rom segs (Z_to_bv 64 x) = Some (Z_to_bv 8 c).
Proof.
intros segs x c H. unfold rm_rom_eqb in H. destruct (seg_rom segs (Z_to_bv 64 x)) as [b|]; [|discriminate].
apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- H. unfold bv_wrap.
symmetry. apply Z.mod_small. exact (bv_unsigned_in_range 8 b).
Qed.
Definition rm_rom_some (segs : list Segment) (x : Z) : bool :=
  match seg_rom segs (Z_to_bv 64 x) with Some _ => true | None => false end.
Lemma rm_rom_some_ok : forall segs x, rm_rom_some segs x = true -> seg_rom segs (Z_to_bv 64 x) <> None.
Proof. intros segs x H. unfold rm_rom_some in H. destruct (seg_rom segs (Z_to_bv 64 x)); [discriminate | discriminate H]. Qed.
(* the first const cell z1 (ANum s) v of a list *)
Fixpoint rm_cfind (s : Z) (l : list acell) : option Z :=
  match l with
  | [] => None
  | ACell (ANum x) 1 (AV (ANum v)) :: r => if x =? s then Some v else rm_cfind s r
  | _ :: r => rm_cfind s r
  end.
Lemma rm_cfind_in : forall s l v, rm_cfind s l = Some v -> In (z1 (ANum s) v) l.
Proof.
intros s l. induction l as [|c r IH]; intros v H; [discriminate H|].
destruct c as [ca cw cv]. cbn [rm_cfind] in H.
destruct ca; try (right; exact (IH v H)).
destruct cw as [|[|cw]]; try (right; exact (IH v H)).
destruct cv as [ce|mask w]; [|right; exact (IH v H)].
destruct ce; try (right; exact (IH v H)).
destruct (Z.eqb_spec z s) as [->|_]; [injection H as <-; left; reflexivity | right; exact (IH v H)].
Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {RL : PrhRoomLive} {ci : CfImg}.
Variable SK : YI16.sink_head.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation ARI := (YG0ncf.ARcf (cp := CP) rsegs TB).
#[local] Abbreviation PIB := (PI_prog_B (rc := rc)).
#[local] Abbreviation SEGSB := (@pa_segs _ B_prog_listing PIB).
#[local] Abbreviation VALB := (@pa_val _ B_prog_listing PIB).
#[local] Abbreviation PSTB := (@prh_pst prh_img_B).
(* the record's const cells, layout-free (YF0m.v Tfib_const) *)
Definition rmB_const : list acell := YF0m.Tfib_const_sym ++ YF0m.Tfib_const_abs ++ YF0m.Tfib_const_shadow.
Lemma rmB_const_eq : forall ly, as_const TB ly = rmB_const.
Proof. intros ly. reflexivity. Qed.

Definition rmB_zs_b (a n : Z) : bool :=
  existsb (fun r => (fst r <=? a) && (a + n <=? fst r + snd r)) (as_zero_shadow TB).
Lemma rmB_zs_b_ok : forall a n, rmB_zs_b a n = true -> in_zs TB a n.
Proof.
intros a n H. apply existsb_exists in H as ([q m] & Hin & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists q, m. cbn [fst snd] in *. split; [exact Hin | lia].
Qed.
Definition rmB_rsh_b (a : Z) : bool :=
  rmB_zs_b (a - a mod 8) 8 ||
  match rm_cfind (shadow_addr a) rmB_const with Some v => (v =? 0) || ((a mod 8 <? v) && (v <? 8)) | None => false end.
Lemma rmB_rsh_b_ok : forall a, rmB_rsh_b a = true -> ro_shadow_ok TB a.
Proof.
intros a H. unfold rmB_rsh_b in H. apply Bool.orb_true_iff in H as [H|H]; [left; exact (rmB_zs_b_ok _ _ H)|].
destruct (rm_cfind (shadow_addr a) rmB_const) as [v|] eqn:Ef; [|discriminate H].
right. exists v. split; [intros ly; rewrite rmB_const_eq; exact (rm_cfind_in _ _ _ Ef)|].
apply Bool.orb_true_iff in H as [H|H]; [left; apply Z.eqb_eq; exact H|].
right. apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.
Definition rmB_pres_b (a : Z) : bool :=
  rmB_zs_b (a - a mod 8) 8 || match rm_cfind (shadow_addr a) rmB_const with Some _ => true | None => false end.
Lemma rmB_pres_b_ok : forall a, rmB_pres_b a = true ->
  in_zs TB (a - a mod 8) 8 \/ exists v, forall ly, In (z1 (ANum (shadow_addr a)) v) (as_const TB ly).
Proof.
intros a H. unfold rmB_pres_b in H. apply Bool.orb_true_iff in H as [H|H]; [left; exact (rmB_zs_b_ok _ _ H)|].
destruct (rm_cfind (shadow_addr a) rmB_const) as [v|] eqn:Ef; [|discriminate H].
right. exists v. intros ly. rewrite rmB_const_eq. exact (rm_cfind_in _ _ _ Ef).
Qed.
Definition rmB_byte_b (a : Z) : bool :=
  rm_ro_b SEGSB (@pa_relro_lo _ _ PIB) (@pa_relro_hi _ _ PIB) a &&
  negb (existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) (as_owned_static TB)) &&
  negb ((as_errno TB <=? a) && (a <? as_errno TB + 4)) && rmB_rsh_b a.
Definition rmB_kept_b (p n : Z) : bool :=
  (@pa_lo _ _ PIB + 64 <=? p) && (p + n + 64 <=? @pa_hi _ _ PIB) && forallb rmB_byte_b (rm_rng p n).
Lemma rmB_kept_b_ok : forall p n, rmB_kept_b p n = true -> kept_img (PA := PIB) TB p n.
Proof.
intros p n H. unfold rmB_kept_b in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. rewrite forallb_forall in H3.
split; [exact H1|]. split; [exact H2|]. intros a Ha. specialize (H3 a (rm_rng_in p n a Ha)). unfold rmB_byte_b in H3.
apply andb_prop in H3 as [H3 Hs]. apply andb_prop in H3 as [H3 He]. apply andb_prop in H3 as [Hr Ho].
split; [apply rm_ro_b_ok; exact Hr|]. split; [|split; [|exact (rmB_rsh_b_ok a Hs)]].
- intros HE. apply Exists_exists in HE as ([q m] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
  apply negb_true_iff in Ho.
  assert (Ht : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) (as_owned_static TB) = true).
  { apply existsb_exists. exists (q, m). split; [exact Hin|]. cbn [fst snd].
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  congruence.
- intros Hea. apply negb_true_iff in He.
  assert (Ht : (as_errno TB <=? a) && (a <? as_errno TB + 4) = true)
    by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  congruence.
Qed.

(* ======== RM_IMG at the B' record (h-verbs-1's ruling: discharged at the instance by vm_compute) ======== *)
Definition rmB_keys_b : bool :=
  forallb (fun kn => rmB_kept_b (fst kn) (snd kn + 1) &&
    forallb rmB_pres_b (rm_rng (fst kn / 64 * 64) ((fst kn + snd kn) / 64 * 64 + 64 - fst kn / 64 * 64)))
    (rm_keys (PA := PIB)).
Lemma rmB_keys_b_true : rmB_keys_b = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rmB_top_b_true : rmB_kept_b (VALB (A_OBJ 3)) 48 = true.
Proof. vm_compute. reflexivity. Qed.
Definition rmB_al_b : bool := forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) (as_zero_shadow TB).
Lemma rmB_al_b_true : rmB_al_b = true.
Proof. vm_compute. reflexivity. Qed.

Lemma RM_IMG_at_Bp : (forall k n, In (k, n) (rm_keys (PA := PIB)) -> kept_img (PA := PIB) TB k (n + 1) /\
    (forall a, k / 64 * 64 <= a < (k + n) / 64 * 64 + 64 ->
       in_zs TB (a - a mod 8) 8 \/ exists v, forall ly, In (z1 (ANum (shadow_addr a)) v) (as_const TB ly))) /\
  kept_img (PA := PIB) TB (VALB (A_OBJ 3)) 48 /\
  Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow TB).
Proof.
split; [|split].
- intros k n Hin. pose proof rmB_keys_b_true as H. unfold rmB_keys_b in H. rewrite forallb_forall in H.
  specialize (H (k, n) Hin). cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
  split; [exact (rmB_kept_b_ok _ _ H1)|]. rewrite forallb_forall in H2.
  intros a Ha. apply rmB_pres_b_ok. apply H2. apply rm_rng_in. lia.
- exact (rmB_kept_b_ok _ _ rmB_top_b_true).
- pose proof rmB_al_b_true as H. unfold rmB_al_b in H. rewrite forallb_forall in H. apply Forall_forall.
  intros r Hr. specialize (H r Hr). apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
  split; assumption.
Qed.

(* ======== the pure image facts of PI_prog_B ======== *)
Lemma rmB_ent : @pa_sigma _ _ PIB AS_read_members = VALB A_TEXT + AF_rmB.
Proof. vm_compute. reflexivity. Qed.
Definition rmB_obj_b : bool :=
  forallb (fun a => rm_img_b SEGSB a) (rm_rng (VALB (A_OBJ 0)) 8 ++ rm_rng (VALB (A_OBJ 12)) 8).
Lemma rmB_obj_b_true : rmB_obj_b = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rmB_obj : forall i, 0 <= i < 8 -> in_img SEGSB (VALB (A_OBJ 0) + i) /\ in_img SEGSB (VALB (A_OBJ 12) + i).
Proof.
intros i Hi. pose proof rmB_obj_b_true as H. unfold rmB_obj_b in H. rewrite forallb_forall in H.
split; apply rm_img_b_ok; apply H; apply in_or_app; [left | right]; apply rm_rng_in; lia.
Qed.
Lemma rmB_lo : @pa_lo _ _ PIB = IMG_LO_B.
Proof. vm_compute. reflexivity. Qed.
Lemma rmB_o2 : VALB (A_OBJ 2) = IMG_LO_B.
Proof. vm_compute. reflexivity. Qed.
Definition rmB_keys_rom_b : bool :=
  forallb (fun on =>
    forallb (fun j => rm_rom_eqb SEGSB (VALB (A_OBJ 2) + fst on + Z.of_nat j) (nth j (snd on ++ [0]) 0))
      (seq 0 (Datatypes.S (length (snd on)))) &&
    forallb (fun j => rm_rom_some SEGSB (VALB (A_OBJ 2) + fst on + Z.of_nat j)) (seq 0 32)) rm_keytab.
Lemma rmB_keys_rom_b_true : rmB_keys_rom_b = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rmB_keys : forall off nm, In (off, nm) rm_keytab ->
  (forall j, (j <= length nm)%nat ->
     seg_rom SEGSB (Z_to_bv 64 (VALB (A_OBJ 2) + off + Z.of_nat j)) = Some (Z_to_bv 8 (nth j (nm ++ [0]) 0))) /\
  (forall j, 0 <= j < 32 -> seg_rom SEGSB (Z_to_bv 64 (VALB (A_OBJ 2) + off + j)) <> None).
Proof.
intros off nm Hin. pose proof rmB_keys_rom_b_true as H. unfold rmB_keys_rom_b in H. rewrite forallb_forall in H.
specialize (H (off, nm) Hin). cbn [fst snd] in H. apply andb_prop in H as [H1 H2]. rewrite forallb_forall in H1, H2.
split.
- intros j Hj. apply rm_rom_eqb_ok. apply H1. apply in_seq. lia.
- intros j Hj. replace j with (Z.of_nat (Z.to_nat j)) by lia. apply rm_rom_some_ok. apply H2. apply in_seq. lia.
Qed.
Definition rmB_top_rom_b : bool :=
  forallb (fun i => forallb (fun j =>
    rm_rom_eqb SEGSB (VALB (A_OBJ 3) + 8 * Z.of_nat i + Z.of_nat j) (rm_byte (VALB (A_OBJ 2) + 0x11020 + 32 * Z.of_nat i) j))
    (seq 0 8)) (seq 0 6).
Lemma rmB_top_rom_b_true : rmB_top_rom_b = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rmB_top : forall i j, (i < 6)%nat -> (j < 8)%nat ->
  seg_rom SEGSB (Z_to_bv 64 (VALB (A_OBJ 3) + 8 * Z.of_nat i + Z.of_nat j)) =
  Some (Z_to_bv 8 (rm_byte (VALB (A_OBJ 2) + 0x11020 + 32 * Z.of_nat i) j)).
Proof.
intros i j Hi Hj. pose proof rmB_top_rom_b_true as H. unfold rmB_top_rom_b in H. rewrite forallb_forall in H.
specialize (H i ltac:(apply in_seq; lia)). rewrite forallb_forall in H.
apply rm_rom_eqb_ok. apply H. apply in_seq. lia.
Qed.
Lemma rmB_top_al : VALB (A_OBJ 3) mod 8 = 0.
Proof. vm_compute. reflexivity. Qed.
Definition rmB_pst_b : bool :=
  forallb (fun r => forallb (fun a => negb (rm_ro_b SEGSB (@pa_relro_lo _ _ PIB) (@pa_relro_hi _ _ PIB) a))
    (rm_rng (fst r) (snd r))) PSTB.
Lemma rmB_pst_b_true : rmB_pst_b = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rmB_pst : forall a, Exists (in_zr a) PSTB -> ~ in_roP SEGSB (@pa_relro_lo _ _ PIB) (@pa_relro_hi _ _ PIB) a.
Proof.
intros a HE Hro. apply Exists_exists in HE as ([q m] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
pose proof rmB_pst_b_true as H. unfold rmB_pst_b in H. rewrite forallb_forall in H. specialize (H (q, m) Hin).
rewrite forallb_forall in H. specialize (H a (rm_rng_in q m a ltac:(lia))).
apply rm_ro_b_ok in Hro. rewrite Hro in H. discriminate H.
Qed.

(* ======== THE INSTANCE ======== *)
Theorem read_members_holds_Bp :
  tpj_get_specX (cp := CP) (PI := prh_img_B) (PA := PIB) TB ARI SK ->
  tpj_get_str_specX (cp := CP) (PI := prh_img_B) (PA := PIB) TB ARI SK ->
  tread_members_specX (cp := CP) (PI := prh_img_B) (PA := PIB) TB ARI SK.
Proof.
intros PJ PJS.
exact (@read_members_holds fx rc RL SK PIB TB ARI
  (PALibB.exvi_eh_laws (rc := rc)) (palib_core (PI := PIB) TB (PALibB.exvi_eh_palib (rc := rc)))
  PJ PJS RM_IMG_at_Bp rmB_ent rmB_obj rmB_lo rmB_o2 rmB_keys rmB_top rmB_top_al rmB_pst).
Qed.
End i.
