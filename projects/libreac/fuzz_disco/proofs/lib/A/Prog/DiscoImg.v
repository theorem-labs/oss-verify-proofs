From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YImgTop.
From OSSVerify.libreac.fuzz_disco.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym DiscoSyms DiscoList DiscoAddr DiscoRoList DiscoPa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition disco_segs : list Segment := Asan.M.loaded_segments.
Definition disco_tbl : ctable :=
Eval vm_compute in (build_table disco_segs disco_text disco_nslots TEmpty).
Lemma disco_tbl_eq : disco_tbl = build_table disco_segs disco_text disco_nslots TEmpty.
Proof. vm_cast_no_check (eq_refl disco_tbl). Qed.
Lemma disco_tbl_ok : table_ok disco_segs disco_tbl.
Proof. rewrite disco_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
Definition disco_val (a : nat) : Z :=
if (a =? A_TEXT)%nat then disco_text else if (a <? A_HI 0)%nat then disco_obj (a - A_OBJ 0) else disco_hi (a - A_HI 0).
Lemma disco_check : pi_check dsym (clookup disco_tbl) disco_val disco_sigma disco_listing = true.
Proof. vm_compute. reflexivity. Qed.
Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.
Lemma disco_val_range : forall a, 0 <= disco_val a < 2 ^ 64.
Proof.
intros a. unfold disco_val. destruct (Nat.eqb a A_TEXT); [zlit|].
destruct (Nat.ltb a (A_HI 0)).
- unfold disco_obj. generalize (a - A_OBJ 0)%nat as m. intros m. do 68 (destruct m as [|m]; [zlit|]). zlit.
- unfold disco_hi. generalize (a - A_HI 0)%nat as m. intros m. do 106 (destruct m as [|m]; [zlit|]). zlit.
Qed.
Lemma disco_wx : wx_segs_nowrap disco_segs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma disco_seg_list : forall b z, In (b, z) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) disco_segs) ->
IMG_LO <= b /\ b + z <= IMG_TOP.
Proof.
intros b z H. vm_compute in H. unfold IMG_LO, IMG_TOP.
repeat (destruct H as [H|H]; [injection H as <- <-; lia|]). destruct H.
Qed.
Lemma disco_img_in : forall a, in_img disco_segs a -> IMG_LO <= a < IMG_TOP.
Proof.
intros a (sg & Hin & Hr).
pose proof (disco_seg_list _ _ (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) disco_segs sg Hin)) as H.
lia.
Qed.
Lemma disco_segs_low : forall a, in_img disco_segs a -> 0 <= a < kLowMemEnd.
Proof. intros a H. pose proof (disco_img_in a H). unfold IMG_LO, IMG_TOP, kLowMemEnd in *. lia. Qed.
Definition disco_relro_lo : Z := 0x9fee0.
Definition disco_relro_hi : Z := 0xa1208.
Lemma disco_relro_img : forall a, disco_relro_lo <= a < disco_relro_hi -> in_img disco_segs a.
Proof.
intros a Ha. unfold disco_relro_lo, disco_relro_hi in Ha. unfold in_img.
assert (E : exists sg, In sg disco_segs /\ Z.of_N (seg_base sg) <= 0x9fee0 /\ 0xa1208 <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg)).
{ unfold disco_segs. remember Asan.M.loaded_segments as l eqn:El.
  assert (B : existsb (fun s : Segment => (Z.of_N (seg_base s) <=? 0x9fee0) && (0xa1208 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) l = true)
    by (subst l; vm_compute; reflexivity).
  apply existsb_exists in B as (sg & Hin & Hb). apply andb_true_iff in Hb as [H1 H2].
  exists sg. split; [exact Hin|]. split; lia. }
destruct E as (sg & Hin & H1 & H2). exists sg. split; [exact Hin | lia].
Qed.
Lemma disco_xcalls_ok : forall s k, In (s, k) disco_xcalls -> disco_sigma s = disco_val A_TEXT + k.
Proof.
intros s k H. cbn [disco_xcalls In] in H.
repeat (destruct H as [H|H]; [injection H as <- <-; vm_compute; reflexivity|]). destruct H.
Qed.
Lemma disco_obj_val : forall i, (i < disco_nobj)%nat -> disco_val (A_OBJ i) = disco_obj i.
Proof.
intros i Hi. unfold disco_val. unfold disco_nobj in Hi.
replace (A_OBJ i =? A_TEXT)%nat with false by (symmetry; apply Nat.eqb_neq; unfold A_OBJ, A_TEXT; lia).
replace (A_OBJ i <? A_HI 0)%nat with true by (symmetry; apply Nat.ltb_lt; unfold A_OBJ, A_HI; lia).
f_equal. unfold A_OBJ. lia.
Qed.
Definition ro_present_b (q sz : Z) : bool :=
forallb (fun i => match seg_rom disco_segs (Z_to_bv 64 (q + Z.of_nat i)) with Some _ => true | None => false end) (seq 0 (Z.to_nat sz)).
Lemma disco_ro_present_b : forallb (fun r => ro_present_b (fst r) (snd r)) disco_ro_all = true.
Proof. vm_compute. reflexivity. Qed.
Lemma disco_ro_present : forall q sz x, In (q, sz) disco_ro_all -> q <= x < q + sz -> seg_rom disco_segs (Z_to_bv 64 x) <> None.
Proof.
intros q sz x Hin Hx. pose proof (proj1 (forallb_forall _ _) disco_ro_present_b (q, sz) Hin) as H. cbn [fst snd] in H.
unfold ro_present_b in H. pose proof (proj1 (forallb_forall _ _) H (Z.to_nat (x - q))) as H1.
assert (Hs : In (Z.to_nat (x - q)) (seq 0 (Z.to_nat sz))) by (apply in_seq; lia).
specialize (H1 Hs). cbv beta in H1. replace (q + Z.of_nat (Z.to_nat (x - q))) with x in H1 by lia.
intro HN. rewrite HN in H1. discriminate H1.
Qed.
Definition rom_range_b (q sz : Z) : bool :=
existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? q) && (q + sz <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) disco_segs.
Lemma disco_rom_extra_b : forallb (fun r => rom_range_b (fst r) (snd r)) (disco_ro_extra ++ disco_glob_tails) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma disco_rom_ok : forall q sz x, In (q, sz) (disco_ro_extra ++ disco_glob_tails) -> q <= x < q + sz -> in_rom disco_segs x.
Proof.
intros q sz x Hin Hx. pose proof (proj1 (forallb_forall _ _) disco_rom_extra_b (q, sz) Hin) as H. cbn [fst snd] in H.
unfold rom_range_b in H. apply existsb_exists in H as (s & Hs & Hb). exists s.
apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [H0 H1].
apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.leb_le in H2. repeat split; auto; lia.
Qed.
Definition ro_range_b (q sz : Z) : bool :=
existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? q) && (q + sz <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) disco_segs
|| ((disco_relro_lo <=? q) && (q + sz <=? disco_relro_hi)).
Lemma disco_ro_ranges_b : forallb (fun r => ro_range_b (fst r) (snd r)) disco_ro_all = true.
Proof. vm_compute. reflexivity. Qed.
Lemma disco_ro_ok : forall q sz x, In (q, sz) disco_ro_all -> q <= x < q + sz ->
(exists s, In s disco_segs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= x < Z.of_N (seg_base s) + Z.of_N (seg_size s)) \/ (disco_relro_lo <= x < disco_relro_hi).
Proof.
intros q sz x Hin Hx. pose proof (proj1 (forallb_forall _ _) disco_ro_ranges_b (q, sz) Hin) as H. cbn [fst snd] in H.
unfold ro_range_b in H. apply orb_true_iff in H as [H|H].
- left. apply existsb_exists in H as (s & Hs & Hb). exists s.
  apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.leb_le in H2. repeat split; auto; lia.
- right. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma disco_img_cover : forall ly S md, ALedger disco_segs ly S md -> fst (ly_img ly) <= IMG_LO /\ IMG_TOP <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S md LG.
assert (Lo : exists sg, In sg disco_segs /\ Z.of_N (seg_base sg) <= IMG_LO).
{ unfold disco_segs. remember Asan.M.loaded_segments as l eqn:El.
  assert (B : existsb (fun s : Segment => Z.of_N (seg_base s) <=? IMG_LO) l = true) by (subst l; vm_compute; reflexivity).
  apply existsb_exists in B as (sg & Hin & Hb). exists sg. split; [exact Hin | lia]. }
assert (Hi : exists sg, In sg disco_segs /\ IMG_TOP <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg)).
{ unfold disco_segs. remember Asan.M.loaded_segments as l eqn:El.
  assert (B : existsb (fun s : Segment => IMG_TOP <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)) l = true) by (subst l; vm_compute; reflexivity).
  apply existsb_exists in B as (sg & Hin & Hb). exists sg. split; [exact Hin | lia]. }
destruct Lo as (s0 & I0 & L0). destruct Hi as (s1 & I1 & L1).
pose proof (al_img _ _ _ _ LG s0 I0) as [A0 _]. pose proof (al_img _ _ _ _ LG s1 I1) as [_ A1].
split; lia.
Qed.
#[global] Instance PB_disco : PAImg disco_listing := {|
pa_segs := disco_segs;
pa_tbl := disco_tbl;
pa_tbl_ok := disco_tbl_ok;
pa_val := disco_val;
pa_sigma := disco_sigma;
pa_cert := disco_check;
pa_B_ok := ltac:(unfold disco_val; cbn; unfold disco_text; lia);
pa_val_range := disco_val_range;
pa_wx := disco_wx;
pa_segs_low := disco_segs_low;
pa_img_range := disco_img_in;
pa_img_cover := disco_img_cover;
pa_obj_img := ltac:(intros i Hi; rewrite (disco_obj_val i Hi); exact (disco_obj_img i Hi));
pa_obj_val := disco_obj_val;
pa_relro_lo := disco_relro_lo;
pa_relro_hi := disco_relro_hi;
pa_relro_img := disco_relro_img;
pa_ro_ok := disco_ro_ok;
pa_rom_ok := disco_rom_ok;
pa_ro_present := disco_ro_present;
pa_xcalls := disco_xcalls_ok |}.
End c.
