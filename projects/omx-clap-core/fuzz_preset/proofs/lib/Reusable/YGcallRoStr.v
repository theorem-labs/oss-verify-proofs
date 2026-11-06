(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-29 (c-omx-alloc, engine owner): A STRING IN THE IMAGE'S READ-ONLY BYTES IS A VALID C STRING AT
   EVERY ARx STATE (h-walk-identity's request: the state half of its S8a stand-in LIT). rule 24: proves no function
   (kind: engine lemma + decision procedure). Image-free: no address, no image number.

   THE LEMMA, ro_cstr_x, generic in segs, B and ARx under LAWS : AR_laws_x. Its conclusion is the cstr_ok
   (lib/A/PRH_Base.v:975-981 at commit decff67d721f) unfolded, conjunct for conjunct, with
   cstr (PRH_Base.v:956-957) unfolded in place and rdW W mem written out as mrestrict (w_H W) mem. The engine does not
   Require the kit, so the kit's names do not appear; the kit states its corollary as below and proves it from ro_cstr_x by destruct and lia (the kit's lane adds it after
   cstr_ok, inside PRH_Base's Section c):
     Lemma cstr_ok_ro {hl : Z} (LAWS : AR_laws_x segs B ARx hl) : forall p l ly S Hp W mem md,
       ARx ly S Hp W mem md -> arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) ->
       YGcallRoStr.ro_str_img segs B p l -> cstr_ok W mem p l.
     Proof. (destruct YGcallRoStr.ro_cstr_x at the premises, then lia: PRH_Base.v:1908-1917.)
   Its two state premises are the two conjuncts of the fpre (PRH_Base.v:578-580): ARx (afn_pre_x's first) and
   arodata_okP at the image's relro range.

   WHERE EACH CONJUNCT COMES FROM.
   - The bytes, the NUL and the tail granule: arodata_okP (lib/Spec/PresetRodata.v:42-44, the one home, REUSED as
     the bytes premise) gives the view at every read-only byte that is neither an owned static nor errno; the image
     premise puts every byte of the string there and says the image holds l ++ [0]. The bytes after the NUL up to the
     end of its granule are in an image segment, so the view is never None there (mbyte falls back to the image).
     AR_laws_x (YCbqG.v:170-189) gives no read-only byte off the cells as_const lists, so the bytes need arodata_okP.
   - The shadow (range_addressable, shadow_hull_vis): FIELD 16 alx_const_cells (YCbqG.v:139-141; every cell of
     as_const B ly holds) and field 12 alx_zshadow (YCbqG.v:105-108; as_zero_shadow B reads 0). The image premise
     names, for every shadow byte the two predicates read, a value the image's const cells or zero-shadow ranges FIX
     (ro_sh_fixed), with saddr_ok for the string's own bytes.
   - The address conjuncts (4096 <= p, the ceiling, the length, amem_range8): numerals of the image premise; the
     ceiling from YM05.alloc_ceiling_value (a string below kLowMemEnd is below CEIL_MIN).
   Numerals: 4096, 8 and 2 ^ 32 are cstr_ok's own (ADDRESS floor, LENGTH slack, LENGTH bound); 8, 7 (DERIVED: 8 - 1)
   and 1 (the NUL) are LENGTH of the 8-byte shadow granule; 4 (LENGTH: errno's width, as arodata_okP); 256 and 2 ^ 8
   (WORD: a byte); 0 (the NUL). No ADDRESS.

   THE IMAGE PREMISE, ro_str_img segs B p l: h-mani-a8 measured that 63 of 91 as_owned_static ranges lie in the
   read-only PT_LOAD 0 of both images, so the premise is per instance. Decide it with ro_str_check (a boolean over
   the image's segments, its const cells, its zero-shadow ranges, its owned statics and errno) and ro_str_check_ok,
   by vm_compute: prove `ro_str_check segs cells zs owned errno p l = true` by `vm_compute; reflexivity`, then apply
   `ro_str_check_ok segs cells zs owned errno B p l` to it and to the instance's ts_owned / ts_errno / ts_zsh
   (AF0m.v / YF0m.v TfibSyms) and a proof that `cells` is in as_const B ly at every ly (from ts_const).

   REUSE (checked, 2026-10-29). c-libc-stdio's ro_clean_check (lib/Reusable/YGcfStrRo.v:53-79, decided per image as
   romA_check, lib/A/PSstrRo.v:43-44 at this file's base, and romB_check, lib/AU/PSstrRo.v) decides the COMPLEMENT:
   every OWNED byte of a read-only segment is a const cell holding its image byte. A string here is off the owned
   statics by premise, so that check gives none of its bytes, and arodata_okP alone gives them; ro_clean_check is not
   needed and not copied.
   No existing check decides the shadow of a string, so ro_str_check decides that, with the string's own image
   facts. Its cell reader rostr_cell_byte reads the same cell shape as YGcfStrRo.cell_cov (an ANum cell with an
   ANum value), but returns the byte the cell fixes rather than comparing with a given one: the shadow conjuncts need
   the value. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI01 YGcfStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRodata.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The image premise (a Prop over the instance's B) and two readers.           *)
Section img.
Variable segs : list Segment.
Variable B : asyms.

(* the image FIXES shadow byte s at v: every reader that satisfies the image's const cells (at any layout) and its
   zero-shadow ranges reads v there. alx_const_cells and alx_zshadow give both at every ARx state. *)
Definition ro_sh_fixed (s v : Z) : Prop :=
  forall ly (rd : reader), Forall (cell_holds B ly rd) (as_const B ly) ->
  Forall (fun r => zero_shadow rd SHADOW_OFF (fst r) (snd r)) (as_zero_shadow B) -> rd s = Some v.

(* the string l at p, NUL-terminated, in the read-only image: addresses, bytes off the owned statics and errno, the
   image bytes, the tail granule present, and the shadow the two shadow conjuncts of cstr_ok read *)
Definition ro_str_img (p : Z) (l : list Z) : Prop :=
  4096 <= p /\ p + Z.of_nat (length l) + 1 + 8 <= kLowMemEnd - 1 /\ Z.of_nat (length l) + 1 < 2 ^ 32 /\
  Forall (fun c => c <> 0) l /\
  (forall a, p <= a <= p + Z.of_nat (length l) ->
     in_rom segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) /\
  (forall j, (j < length (l ++ [0%Z]))%nat ->
     option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 (p + Z.of_nat j))) = Some (nth j (l ++ [0]) 0)) /\
  (forall a, p + Z.of_nat (length l) < a < p + Z.of_nat (length l) - (p + Z.of_nat (length l)) mod 8 + 8 ->
     seg_rom segs (Z_to_bv 64 a) <> None) /\
  (forall x, p <= x <= p + Z.of_nat (length l) -> exists v, ro_sh_fixed (shadow_addr x) v /\ saddr_ok x v) /\
  (forall s, shadow_addr p / 8 * 8 <= s < shadow_addr (p + Z.of_nat (length l)) / 8 * 8 + 8 ->
     exists v, ro_sh_fixed s v).

(* garr8 from the view, byte by byte *)
Lemma rostr_garr8 : forall (H : word -> bool) mem p l,
  (forall j, (j < length l)%nat -> aview segs H mem (p + Z.of_nat j) = Some (nth j l 0)) ->
  garr8 segs (mrestrict H mem) p l.
Proof.
  intros H mem p l Hv j Hj. specialize (Hv j Hj). unfold aview in Hv.
  destruct (mbyte segs (mrestrict H mem) (p + Z.of_nat j)) as [b|] eqn:Eb; [|discriminate Hv].
  cbn [option_map] in Hv. injection Hv as Hv.
  pose proof (bv_unsigned_in_range _ b) as Hr. change (bv_modulus 8) with (2 ^ 8) in Hr.
  rewrite <- Hv. split; [|lia].
  apply YI01.val_mem1_of_mbyte; [lia|]. rewrite Eb. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
End img.

(* ---------------------------------------------------------------------------- *)
(* 2. The lemma: at every ARx state with the read-only view, ro_str_img gives cstr_ok's conjuncts.                  *)
Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx hl.

Lemma ro_sh_fixed_x : forall ly S Hp W mem md s v,
  ARx ly S Hp W mem md -> ro_sh_fixed B s v -> aview segs (w_H W) mem s = Some v.
Proof.
  intros ly S Hp W mem md s v HAR Hf. apply (Hf ly (aview segs (w_H W) mem)).
  - exact (alx_const_cells _ _ _ LAWS ly S Hp W mem md HAR).
  - apply Forall_forall. intros r Hr. apply (alx_zshadow _ _ _ LAWS ly S Hp W mem md r HAR).
    unfold zero_shadow_ranges. right. exact Hr.
Qed.

Lemma ro_cstr_x : forall rlo rhi p l ly S Hp W mem md,
  ARx ly S Hp W mem md ->
  PresetRodata.arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
  ro_str_img segs B p l ->
  (garr8 segs (mrestrict (w_H W) mem) p (l ++ [0]) /\ Forall (fun c => c <> 0) l) /\
  4096 <= p /\ p + Z.of_nat (length l) + 8 <= YM05.alloc_ceiling /\ Z.of_nat (length l) + 1 < 2 ^ 32 /\
  YGcfStr.amem_range8 p (Z.of_nat (length l) + 1) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p (Z.of_nat (length l) + 1) /\
  shadow_hull_vis (aview segs (w_H W) mem) p (Z.of_nat (length l) + 1) /\
  (forall a, p + Z.of_nat (length l) < a < p + Z.of_nat (length l) - (p + Z.of_nat (length l)) mod 8 + 8 ->
     aview segs (w_H W) mem a <> None).
Proof.
  intros rlo rhi p l ly S Hp W mem md HAR HRO HI.
  destruct HI as (H4096 & Hlow & H32 & Hnz & Hrom & Hbytes & Htail & Hsh & Hhull).
  pose proof alloc_ceiling_value as Hceil.
  split; [split; [|exact Hnz]|].
  { apply rostr_garr8. intros j Hj. pose proof (Hbytes j Hj) as Hb.
    rewrite length_app in Hj. cbn [length] in Hj.
    destruct (Hrom (p + Z.of_nat j) ltac:(lia)) as (R1 & R2 & R3).
    rewrite (HRO (p + Z.of_nat j)); [exact Hb | left; exact R1 | exact R2 | exact R3]. }
  split; [exact H4096|]. split; [unfold kLowMemEnd in Hlow; lia|]. split; [exact H32|].
  split; [unfold YGcfStr.amem_range8; left; lia|].
  split.
  { intros x Hx. destruct (Hsh x ltac:(lia)) as (v & Hf & Hok). exists v. split; [|exact Hok].
    exact (ro_sh_fixed_x ly S Hp W mem md _ v HAR Hf). }
  split.
  { intros s Hs. replace (p + (Z.of_nat (length l) + 1) - 1) with (p + Z.of_nat (length l)) in Hs by lia.
    destruct (Hhull s Hs) as (v & Hf). rewrite (ro_sh_fixed_x ly S Hp W mem md s v HAR Hf). discriminate. }
  intros a Ha. pose proof (Htail a Ha) as T. unfold aview, mbyte. revert T.
  destruct (mrestrict (w_H W) mem (Z_to_bv 64 a)) as [b|]; intros T; [cbn [option_map]; discriminate|].
  revert T. destruct (seg_rom segs (Z_to_bv 64 a)) as [b|]; intros T; [cbn [option_map]; discriminate|].
  exfalso. exact (T eq_refl).
Qed.
End x.

(* ---------------------------------------------------------------------------- *)
(* 3. The decision procedure for ro_str_img, over the instance's tables.          *)
Section chk.
Variable segs : list Segment.
Variable cells : list acell.
Variable zs : list (Z * Z).
Variable owned : list (Z * Z).
Variable errno : Z.

Fixpoint rostr_all (f : Z -> bool) (a : Z) (n : nat) : bool :=
  match n with O => true | S n' => f a && rostr_all f (a + 1) n' end.

(* the byte an absolute const cell fixes at s (the cell shape of YGcfStrRo.cell_cov) *)
Definition rostr_cell_byte (s : Z) (c : acell) : option Z :=
  match c_at c, c_val c with
  | ANum z, AV (ANum v) =>
      if (z <=? s) && (s <? z + Z.of_nat (c_w c)) then Some (le_byte v (c_w c) (Z.to_nat (s - z))) else None
  | _, _ => None
  end.
Fixpoint rostr_cells_byte (s : Z) (cs : list acell) : option Z :=
  match cs with
  | [] => None
  | c :: cs' => match rostr_cell_byte s c with Some v => Some v | None => rostr_cells_byte s cs' end
  end.
(* s is a shadow byte of a zero-shadow range (zero_shadow's own span: SHADOW_OFF + q / 8 + i, i < m / 8) *)
Definition rostr_zs_cov (s : Z) : bool :=
  existsb (fun r => (SHADOW_OFF + fst r / 8 <=? s) && (s <? SHADOW_OFF + fst r / 8 + snd r / 8)) zs.
Definition rostr_sh_byte (s : Z) : option Z :=
  match rostr_cells_byte s cells with Some v => Some v | None => if rostr_zs_cov s then Some 0 else None end.

Definition rostr_ro (a : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
    (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs.
Definition rostr_free (a : Z) : bool :=
  negb (existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) owned) && ((a <? errno) || (errno + 4 <=? a)).
Fixpoint rostr_bytes (a : Z) (l : list Z) : bool :=
  match l with
  | [] => true
  | c :: l' =>
      rostr_ro a && rostr_free a &&
      (match option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)) with
       | Some v => v =? c | None => false end) &&
      rostr_bytes (a + 1) l'
  end.
Definition rostr_present (a : Z) : bool := match seg_rom segs (Z_to_bv 64 a) with Some _ => true | None => false end.
Definition rostr_sh_ok (x : Z) : bool :=
  match rostr_sh_byte (shadow_addr x) with Some v => (v =? 0) || ((x mod 8 <? v) && (v <? 8)) | None => false end.
Definition rostr_sh_some (s : Z) : bool := match rostr_sh_byte s with Some _ => true | None => false end.

Definition ro_str_check (p : Z) (l : list Z) : bool :=
  (4096 <=? p) && (p + Z.of_nat (length l) + 1 + 8 <=? kLowMemEnd - 1) && (Z.of_nat (length l) + 1 <? 2 ^ 32) &&
  forallb (fun c => negb (c =? 0)) l &&
  rostr_bytes p (l ++ [0]) &&
  rostr_all rostr_present (p + Z.of_nat (length l) + 1) (Z.to_nat (7 - (p + Z.of_nat (length l)) mod 8)) &&
  rostr_all rostr_sh_ok p (S (length l)) &&
  rostr_all rostr_sh_some (shadow_addr p / 8 * 8)
    (Z.to_nat (shadow_addr (p + Z.of_nat (length l)) / 8 * 8 + 8 - shadow_addr p / 8 * 8)).

Lemma rostr_all_ok : forall f n a, rostr_all f a n = true -> forall x, a <= x < a + Z.of_nat n -> f x = true.
Proof.
  intros f. induction n as [|n IH]; intros a H x Hx; [lia|].
  cbn [rostr_all] in H. apply andb_true_iff in H as [H1 H2].
  destruct (Z.eq_dec x a) as [->|Hne]; [exact H1|].
  apply (IH (a + 1) H2). lia.
Qed.

Lemma rostr_cell_byte_ok : forall B ly rd c s v,
  cell_holds B ly rd c -> rostr_cell_byte s c = Some v -> rd s = Some v.
Proof.
  intros B ly rd [ca cw cv] s v Hh Hc. unfold rostr_cell_byte in Hc. cbn [c_at c_val c_w] in Hc.
  destruct ca as [za| | | | | | | | | | | | | | | | | |]; try discriminate Hc.
  destruct cv as [e|]; try discriminate Hc. destruct e as [ze| | | | | | | | | | | | | | | | | |]; try discriminate Hc.
  destruct ((za <=? s) && (s <? za + Z.of_nat cw)) eqn:Hr; [|discriminate Hc].
  apply andb_true_iff in Hr as [R1 R2]. apply Z.leb_le in R1. apply Z.ltb_lt in R2.
  injection Hc as <-.
  unfold cell_holds in Hh. cbn [c_at c_val c_w aeval] in Hh.
  specialize (Hh (Z.to_nat (s - za)) ltac:(lia)).
  rewrite Z2Nat.id in Hh by lia. replace (za + (s - za)) with s in Hh by lia. exact Hh.
Qed.

Lemma rostr_cells_byte_ok : forall B ly rd cs s v,
  Forall (cell_holds B ly rd) cs -> rostr_cells_byte s cs = Some v -> rd s = Some v.
Proof.
  intros B ly rd cs s v HF.
  induction HF as [|c cs' Hc HF' IH]; cbn [rostr_cells_byte]; [intros E; discriminate E|].
  destruct (rostr_cell_byte s c) as [w|] eqn:E; [|exact IH].
  intros Hw. injection Hw as <-. exact (rostr_cell_byte_ok B ly rd c s w Hc E).
Qed.

Lemma rostr_zs_cov_ok : forall rd s,
  Forall (fun r => zero_shadow rd SHADOW_OFF (fst r) (snd r)) zs -> rostr_zs_cov s = true -> rd s = Some 0.
Proof.
  intros rd s HF Hc. unfold rostr_zs_cov in Hc. apply existsb_exists in Hc as (r & Hr & Hc).
  apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  rewrite Forall_forall in HF. pose proof (HF r Hr) as Hz. unfold zero_shadow, shadow_of_addr in Hz.
  specialize (Hz (s - (SHADOW_OFF + fst r / 8)) ltac:(lia)).
  replace (SHADOW_OFF + fst r / 8 + (s - (SHADOW_OFF + fst r / 8))) with s in Hz by lia. exact Hz.
Qed.

Lemma rostr_sh_byte_ok : forall B s v,
  as_zero_shadow B = zs -> (forall ly, incl cells (as_const B ly)) ->
  rostr_sh_byte s = Some v -> ro_sh_fixed B s v.
Proof.
  intros B s v Ez Ec E ly rd HC HZ. unfold rostr_sh_byte in E.
  destruct (rostr_cells_byte s cells) as [w|] eqn:Ecb.
  - injection E as <-. apply (rostr_cells_byte_ok B ly rd cells s w); [|exact Ecb].
    rewrite Forall_forall in HC |- *. intros c Hin. exact (HC c (Ec ly c Hin)).
  - destruct (rostr_zs_cov s) eqn:Ezc; [|discriminate E]. injection E as <-.
    rewrite Ez in HZ. exact (rostr_zs_cov_ok rd s HZ Ezc).
Qed.

Lemma rostr_bytes_ok : forall l a, rostr_bytes a l = true -> forall j, (j < length l)%nat ->
  rostr_ro (a + Z.of_nat j) = true /\ rostr_free (a + Z.of_nat j) = true /\
  option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 (a + Z.of_nat j))) = Some (nth j l 0).
Proof.
  induction l as [|c l IH]; intros a H j Hj; cbn [length] in Hj; [lia|].
  cbn [rostr_bytes] in H. apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [H H3].
  apply andb_true_iff in H as [H1 H2].
  destruct j as [|j].
  - replace (a + Z.of_nat 0) with a by lia. cbn [nth]. split; [exact H1|]. split; [exact H2|].
    destruct (option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))) as [v|];
      [apply Z.eqb_eq in H3; rewrite H3; reflexivity | discriminate H3].
  - destruct (IH (a + 1) H4 j ltac:(lia)) as (G1 & G2 & G3).
    replace (a + Z.of_nat (S j)) with (a + 1 + Z.of_nat j) by lia. cbn [nth].
    exact (conj G1 (conj G2 G3)).
Qed.

Lemma rostr_ro_ok : forall a, rostr_ro a = true -> in_rom segs a.
Proof.
  intros a H. unfold rostr_ro in H. apply existsb_exists in H as (sg & Hin & H).
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply negb_true_iff in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  exists sg. exact (conj Hin (conj H1 (conj H2 H3))).
Qed.

Lemma rostr_free_ok : forall a, rostr_free a = true -> ~ Exists (in_zr a) owned /\ ~ (errno <= a < errno + 4).
Proof.
  intros a H. unfold rostr_free in H. apply andb_true_iff in H as [H1 H2]. split.
  - intros Hx. apply Exists_exists in Hx as (r & Hr & Hin). apply negb_true_iff in H1.
    assert (Hb : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) owned = true).
    { apply existsb_exists. exists r. split; [exact Hr|]. unfold in_zr in Hin.
      apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    congruence.
  - apply orb_true_iff in H2 as [E|E]; [apply Z.ltb_lt in E | apply Z.leb_le in E]; lia.
Qed.

(* the reflection lemma: the check decides the image premise at any B whose tables are these *)
Lemma ro_str_check_ok : forall B p l, ro_str_check p l = true ->
  as_owned_static B = owned -> as_errno B = errno -> as_zero_shadow B = zs -> (forall ly, incl cells (as_const B ly)) ->
  ro_str_img segs B p l.
Proof.
  intros B p l H Eo Ee Ez Ec. unfold ro_str_check in H.
  apply andb_true_iff in H as [H C8]. apply andb_true_iff in H as [H C7]. apply andb_true_iff in H as [H C6].
  apply andb_true_iff in H as [H C5]. apply andb_true_iff in H as [H C4]. apply andb_true_iff in H as [H C3].
  apply andb_true_iff in H as [C1 C2].
  apply Z.leb_le in C1. apply Z.leb_le in C2. apply Z.ltb_lt in C3.
  pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)) as Hm.
  unfold ro_str_img. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split.
  { apply Forall_forall. intros c Hc. rewrite forallb_forall in C4. specialize (C4 c Hc).
    apply negb_true_iff, Z.eqb_neq in C4. exact C4. }
  split.
  { intros a Ha.
    assert (Hj : (Z.to_nat (a - p) < length (l ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
    pose proof (rostr_bytes_ok (l ++ [0]) p C5 (Z.to_nat (a - p)) Hj) as (B1 & B2 & _).
    rewrite Z2Nat.id in B1, B2 by lia. replace (p + (a - p)) with a in B1, B2 by lia.
    destruct (rostr_free_ok a B2) as [F1 F2]. rewrite Eo, Ee. exact (conj (rostr_ro_ok a B1) (conj F1 F2)). }
  split.
  { intros j Hj. exact (proj2 (proj2 (rostr_bytes_ok (l ++ [0]) p C5 j Hj))). }
  split.
  { intros a Ha. pose proof (rostr_all_ok _ _ _ C6 a ltac:(rewrite Z2Nat.id by lia; lia)) as T.
    unfold rostr_present in T. destruct (seg_rom segs (Z_to_bv 64 a)); [discriminate | discriminate T]. }
  split.
  { intros x Hx. pose proof (rostr_all_ok _ _ _ C7 x ltac:(lia)) as R. unfold rostr_sh_ok in R.
    destruct (rostr_sh_byte (shadow_addr x)) as [v|] eqn:E; [|discriminate R].
    exists v. split; [exact (rostr_sh_byte_ok B _ v Ez Ec E)|]. unfold saddr_ok.
    apply orb_true_iff in R as [R|R]; [left; apply Z.eqb_eq; exact R|].
    right. apply andb_true_iff in R as [R1 R2]. apply Z.ltb_lt in R1. apply Z.ltb_lt in R2. lia. }
  intros s Hs. pose proof (rostr_all_ok _ _ _ C8 s ltac:(rewrite Z2Nat.id by lia; lia)) as R.
  unfold rostr_sh_some in R. destruct (rostr_sh_byte s) as [v|] eqn:E; [|discriminate R].
  exists v. exact (rostr_sh_byte_ok B s v Ez Ec E).
Qed.
End chk.
