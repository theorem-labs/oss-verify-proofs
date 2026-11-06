(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10-29: new file for libreac/fuzz_scene (asan-ubsan). The start-up certificate of
   scene's B: the cells, zero ranges and owned ranges that the memory-checking runtime leaves behind at start-up,
   and the two facts the check_step and reac_ctrl_parse walks take as blanket hypotheses over every AR state,
   `img_shadow_vis` and `globs_marked`, proved here as lemmas of B. *)

(*   Copied by method from a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/Prog/GrantClose.v (a working branch at
   ac3f475adac), sections "computable checks over the image" (:46-92), "generic lemmas over the checks" (:112-170),
   "the checks, by computation" (:172-187) and "6. the shadow of the image and of its registered globals"
   (:378-443, `grant_shadow_cell`, `grant_zs_rd`, `grant_img_shadow_vis`, `grant_globs_marked`, all Qed).
   Every address, range and cell below is scene's, read off the start-up tables of lib/A/AF0m.v; this file copies
   no number from fuzz_grant or from cgif_file_fuzzer.

   One change of method against the donor. `glob_chk` (donor :89-92) demands that a registered global's whole
   granules lie in one zero-shadow range even when it has none: fuzz_grant's .str.4 (0x21020, 7) happens to sit at
   the end of a zero range, scene's .str.4 (0x20e40, 7) does not. The clause gets a `snd g / 8 =? 0` disjunct, which
   `globs_marked`'s proof uses only in the branch `i < sz / 8` that is empty exactly then.

   No Axiom, no admit, no Admitted.

   What this file assumes about B: one Section hypothesis, `HB : TfibSyms B` (lib/AU/YF0m.v:606-630), the
   start-up record of scene's asan-ubsan image. No `asyms` instance of it exists in the tree yet, so it stays a
   hypothesis here; see the note at the end of the file. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YG00 YG0a YG01 YG0f YG0n YG0d YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YF0l YF0m.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import SceneRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- 1. the registered globals of fuzz_scene.asan-ubsan --------------------------------------
   The five entries of the `asan_globals` descriptor array (asan-ubsan 0xa0300..0xa0440), as
   CHECKSTEP-REVIEW.md:92 reads them off the image: beg and size of each registered global.
   `__asan_register_globals` leaves each one's bytes marked usable and its redzone 0xf9. *)
Definition SCENE_GLOBS : list (Z * Z) :=
  [(0x20d80, 12); (0x20da0, 50); (0x20e20, 12); (0x20e40, 7); (0x20e80, 8904)].

(* The redzone tails those five globals own, which `am_const_owned` (YG0n.v:201-204) needs in
   `as_owned_static B`, together with the descriptor array itself. *)
Definition SCENE_RZ_OWNED : list (Z * Z) :=
  [(0x20d8c, 0x14); (0x20dd2, 0x2e); (0x20e2c, 0x14); (0x20e47, 0x19); (0x23148, 0x8b8); (0xa0300, 0x140)].

(* ---- 2. computable checks over the start-up tables (donor GrantClose.v:62-92) ---------- *)
(* The granule (shadow byte) at s is one of the start-up certificate's shadow cells. *)
Definition is_shc (s : Z) (c : acell) : bool :=
  match c with ACell (ANum s') (S O) (AV (ANum _)) => Z.eqb s' s | _ => false end.
Definition is_shv (s v : Z) (c : acell) : bool :=
  match c with ACell (ANum s') (S O) (AV (ANum v')) => (Z.eqb s' s && Z.eqb v' v)%bool | _ => false end.
(* A cell at a literal address, of width w, holding the literal v. *)
Definition is_wv (w : nat) (v : Z) (c : acell) : bool :=
  match c with ACell (ANum _) w' (AV (ANum v')) => (Nat.eqb w' w && Z.eqb v' v)%bool | _ => false end.

(* The end (in granules) of the zero-shadow range that holds granule k, if one does. *)
Fixpoint zfind (k : Z) (zs : list (Z * Z)) : option Z :=
  match zs with
  | [] => None
  | (q, m) :: r => if ((q / 8 <=? k) && (k <? (q + m) / 8))%bool then Some ((q + m) / 8) else zfind k r
  end.

(* Every granule of [k, hi) is in a zero-shadow range or has a certificate cell. *)
Fixpoint vscan (fuel : nat) (k hi : Z) : bool :=
  match fuel with
  | O => false
  | S f =>
      if hi <=? k then true else
      match zfind k Tfib_zero_shadow with
      | Some e => vscan f e hi
      | None => (existsb (is_shc (SHADOW_OFF + k)) Tfib_const_shadow && vscan f (k + 1) hi)%bool
      end
  end.

(* A registered global's full granules lie in one zero-shadow range, and its last partial
   granule has the certificate cell `size mod 8`.
   Against the donor (GrantClose.v:89-92) the zero-range clause gains the `snd g / 8 =? 0`
   disjunct: scene's .str.4 (0x20e40, 7) has no full granule, and its 7 bytes sit in the single
   partial granule 0x7fffc1c8, with no zero-shadow range at 0x20e40. `globs_marked` below uses
   the zero range only where `i < sz / 8`, which is empty exactly when `sz / 8 = 0`. *)
Definition glob_chk (g : Z * Z) : bool :=
  ((fst g mod 8 =? 0) && (0 <=? snd g) &&
   ((snd g / 8 =? 0) ||
    existsb (fun r => (fst r <=? fst g) && (fst g + snd g / 8 * 8 <=? fst r + snd r)) Tfib_zero_shadow) &&
   ((snd g mod 8 =? 0) || existsb (is_shv (SHADOW_OFF + fst g / 8 + snd g / 8) (snd g mod 8)) Tfib_const_shadow))%bool.

(* ---- 3. generic lemmas over the checks (donor GrantClose.v:112-170) -------------------- *)
Lemma le_byte1 : forall v, 0 <= v < 256 -> YG0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256 Hv). exact (Z.mod_small v 256 Hv).
Qed.

Lemma is_shc_eq : forall s c, is_shc s c = true -> exists v, c = z1 (ANum s) v.
Proof.
intros s [ca cw cv] H. destruct ca; try (cbn in H; discriminate H).
destruct cw as [|[|cw]]; try (cbn in H; discriminate H).
destruct cv as [e|m0 v0]; try (cbn in H; discriminate H).
destruct e; try (cbn in H; discriminate H).
cbn in H. apply Z.eqb_eq in H. subst. eexists. reflexivity.
Qed.

Lemma is_shv_eq : forall s v c, is_shv s v c = true -> c = z1 (ANum s) v.
Proof.
intros s v [ca cw cv] H. destruct ca; try (cbn in H; discriminate H).
destruct cw as [|[|cw]]; try (cbn in H; discriminate H).
destruct cv as [e|m0 v0]; try (cbn in H; discriminate H).
destruct e; try (cbn in H; discriminate H).
cbn in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Definition cell_addr (c : acell) : Z := match c_at c with ANum a => a | _ => 0 end.
Lemma is_wv_true8 : forall a v, is_wv 8 v (z8 (ANum a) v) = true.
Proof. intros a v. unfold is_wv, z8, c8. cbn [c_at c_w c_val Nat.eqb andb]. apply Z.eqb_refl. Qed.
Lemma is_wv_true4 : forall a v, is_wv 4 v (z4 (ANum a) v) = true.
Proof. intros a v. unfold is_wv, z4, c4. cbn [c_at c_w c_val Nat.eqb andb]. apply Z.eqb_refl. Qed.

Lemma filter_sing_eq : forall (f : acell -> bool) l x y, List.filter f l = [y] -> In x l -> f x = true -> x = y.
Proof.
intros f l x y Hf Hin Hx.
assert (H : In x (List.filter f l)) by (apply (proj2 (filter_In f x l)); split; assumption).
rewrite Hf in H. destruct H as [H|[]]. symmetry. exact H.
Qed.

Lemma zfind_some : forall k zs e, zfind k zs = Some e ->
  exists q m, In (q, m) zs /\ q / 8 <= k < (q + m) / 8 /\ e = (q + m) / 8.
Proof.
intros k zs. induction zs as [|[q m] r IH]; intros e H; cbn [zfind] in H; [discriminate|].
destruct ((q / 8 <=? k) && (k <? (q + m) / 8))%bool eqn:Hb.
- injection H as <-. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists q, m. split; [left; reflexivity|]. split; [lia | reflexivity].
- destruct (IH e H) as (q' & m' & Hin & Hk & He). exists q', m'. split; [right; exact Hin|]. split; [exact Hk | exact He].
Qed.

Lemma vscan_ok : forall fuel k hi, vscan fuel k hi = true -> forall j, k <= j < hi ->
  (exists q m, In (q, m) Tfib_zero_shadow /\ q / 8 <= j < (q + m) / 8) \/
  existsb (is_shc (SHADOW_OFF + j)) Tfib_const_shadow = true.
Proof.
induction fuel as [|f IH]; intros k hi H j Hj; cbn [vscan] in H; [discriminate|].
destruct (hi <=? k) eqn:E; [apply Z.leb_le in E; exfalso; lia|].
destruct (zfind k Tfib_zero_shadow) as [e|] eqn:Ez.
- destruct (zfind_some _ _ _ Ez) as (q & m & Hin & Hk & ->).
  destruct (Z_lt_le_dec j ((q + m) / 8)) as [Hlt|Hge].
  + left. exists q, m. split; [exact Hin | lia].
  + exact (IH _ _ H j (conj Hge (proj2 Hj))).
- apply andb_prop in H as [Hc H]. destruct (Z.eq_dec j k) as [->|Hne]; [right; exact Hc|].
  apply (IH _ _ H). lia.
Qed.

(* ---- 4. the checks, by computation on fuzz_scene.asan-ubsan ------------------------------- *)
(* The whole image range [IMG_LO, IMG_HI) (SceneRo.v:33-34) is covered, granule by granule, by
   the zero-shadow ranges and the 335 shadow cells of the certificate: 6 range jumps and
   335 single granules, so 4096 is fuel to spare. *)
Lemma scene_vscan : vscan (Pos.to_nat 4096) (IMG_LO / 8) (IMG_HI / 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma scene_globs_chk : forallb glob_chk SCENE_GLOBS = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zs_align_chk :
  forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0) && (0 <=? snd r))%bool Tfib_zero_shadow = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zs_align : forall q m, In (q, m) Tfib_zero_shadow -> q mod 8 = 0 /\ m mod 8 = 0 /\ 0 <= m.
Proof.
intros q m Hin. pose proof (proj1 (forallb_forall _ _) zs_align_chk (q, m) Hin) as Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. auto.
Qed.

(* The four runtime cells of `asyms_ok`'s const law are each the only cell of their width and
   value in the whole start-up table, which is what pins B's four runtime addresses below. *)
Lemma scene_filter_shadow_cell :
  List.filter (is_wv 8 SHADOW_OFF) (Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow)
  = [z8 (ANum 0xa3af8) SHADOW_OFF].
Proof. vm_compute. reflexivity. Qed.
Lemma scene_filter_uar_cell :
  List.filter (is_wv 4 1) (Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow) = [z4 (ANum 0xa3b00) 1].
Proof. vm_compute. reflexivity. Qed.
Lemma scene_filter_got_shadow :
  List.filter (is_wv 8 0xa3af8) (Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow)
  = [z8 (ANum 0x9ba40) 0xa3af8].
Proof. vm_compute. reflexivity. Qed.
Lemma scene_filter_got_uar :
  List.filter (is_wv 8 0xa3b00) (Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow)
  = [z8 (ANum 0x9ba98) 0xa3b00].
Proof. vm_compute. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable B : asyms.
(* The only thing this file assumes: B is scene's start-up record (YF0m.v:606-630). *)
Hypothesis HB : TfibSyms B.

(* ---- 5. B's three start-up tables ------------------------------------------------------ *)
Lemma scene_LAWS : forall segs, AR_laws segs B.
Proof. intro segs. exact (AR_laws_ok segs B). Qed.

Lemma scene_in_const : forall ly c, In c (Tfib_const ly) -> In c (as_const B ly).
Proof. intros ly c H. rewrite (ts_const _ HB ly). exact H. Qed.

Lemma scene_in_zsh : forall r, In r Tfib_zero_shadow -> In r (as_zero_shadow B).
Proof. intros r H. rewrite (ts_zsh _ HB). exact H. Qed.

Lemma scene_in_owned : forall r, In r Tfib_owned_static -> In r (as_owned_static B).
Proof. intros r H. rewrite (ts_owned _ HB). exact H. Qed.

Ltac in_sym n := intro ly; apply scene_in_const; unfold Tfib_const; apply in_or_app; left;
  apply (nth_error_In Tfib_const_sym n); vm_compute; reflexivity.
Ltac in_abs n := intro ly; apply scene_in_const; unfold Tfib_const; apply in_or_app; right;
  apply in_or_app; left; apply (nth_error_In Tfib_const_abs n); vm_compute; reflexivity.
Ltac in_sh n := intro ly; apply scene_in_const; unfold Tfib_const; apply in_or_app; right;
  apply in_or_app; right; apply (nth_error_In Tfib_const_shadow n); vm_compute; reflexivity.
Ltac in_own n := apply scene_in_owned; apply (nth_error_In Tfib_owned_static n); vm_compute; reflexivity.
Ltac in_zr n := apply scene_in_zsh; apply (nth_error_In Tfib_zero_shadow n); vm_compute; reflexivity.

(* ---- 6. B's two symbol fields the TLS chain walks through (Seg A's HC_tp, HC_tsd) ----------- *)
Lemma scene_tp : as_tp B = TFIB_TP.
Proof. exact (ts_tp _ HB). Qed.
Lemma scene_tsd : as_tsd B = TFIB_TSD.
Proof. exact (ts_tsd _ HB). Qed.

(* ---- 7. B's four runtime cell addresses --------------------------------------------------
   `asyms_ok`'s const law (YG0f.v:188-190) puts four cells of B's own addresses in `as_const`;
   each is the only cell of its width and value in the whole table (section 4), so the four
   addresses are determined. They are the values CHECKSTEP-REVIEW.md:66 reads off scene's
   image, and they are NOT cgif's (0xa5ff8 / 0xa6000 / 0x9df98), which a Theorem Labs lane's dry run of
   lib/A/AD2l.v carried; this tree's AU/YD2l.v:49-51 holds scene's. *)
Lemma scene_shadow_cell_addr : forall ly : alayout, as_shadow_cell B = 0xa3af8.
Proof.
intro ly. destruct (aso_const_law _ (ts_ok _ HB) ly) as (I1 & _ & _ & _).
rewrite (ts_const _ HB ly) in I1. unfold Tfib_const in I1.
exact (f_equal cell_addr (filter_sing_eq _ _ _ _ scene_filter_shadow_cell I1 (is_wv_true8 _ _))).
Qed.
Lemma scene_uar_cell_addr : forall ly : alayout, as_uar_cell B = 0xa3b00.
Proof.
intro ly. destruct (aso_const_law _ (ts_ok _ HB) ly) as (_ & I2 & _ & _).
rewrite (ts_const _ HB ly) in I2. unfold Tfib_const in I2.
exact (f_equal cell_addr (filter_sing_eq _ _ _ _ scene_filter_uar_cell I2 (is_wv_true4 _ _))).
Qed.
Lemma scene_got_shadow_addr : forall ly : alayout, as_got_shadow B = 0x9ba40.
Proof.
intro ly. destruct (aso_const_law _ (ts_ok _ HB) ly) as (_ & _ & I3 & _).
rewrite (ts_const _ HB ly) in I3. unfold Tfib_const in I3.
rewrite (scene_shadow_cell_addr ly) in I3.
exact (f_equal cell_addr (filter_sing_eq _ _ _ _ scene_filter_got_shadow I3 (is_wv_true8 _ _))).
Qed.
Lemma scene_got_uar_addr : forall ly : alayout, as_got_uar B = 0x9ba98.
Proof.
intro ly. destruct (aso_const_law _ (ts_ok _ HB) ly) as (_ & _ & _ & I4).
rewrite (ts_const _ HB ly) in I4. unfold Tfib_const in I4.
rewrite (scene_uar_cell_addr ly) in I4.
exact (f_equal cell_addr (filter_sing_eq _ _ _ _ scene_filter_got_uar I4 (is_wv_true8 _ _))).
Qed.

(* ---- 8. the cells of the start-up certificate ------------------------------------------
   Each is `forall ly, In <cell> (as_const B ly)`, the form a Theorem Labs lane's Seg A states them in
   (lib/A/Rt/StackMalloc8SegA.v:310-349, its hypotheses named HC_ ). AR's `am_const`
   (YG0n.v:211) turns one into the byte fact a walk reads. Sources:
   cited-12.md (sha256 6071c8150ae9; internal record) and
   B-CERT-CELLS.md (sha256 d459f8bdaebe; internal record). *)
(* [TP] = F, the thread's fake stack (Seg A's HC_fake_stack; read at malloc_8 entry +0x2c) *)
Lemma scene_c_fake_stack : forall ly, In (c8 (ATp 0) (AF 0)) (as_const B ly).
Proof. in_sym 13%nat. Qed.
(* [TP - 88] = TSD (Seg A's HC_tsd_slot; pthread_getspecific {A}) *)
Lemma scene_c_tsd_slot : forall ly, In (c8 (ATp (-88)) (ATsd 0)) (as_const B ly).
Proof. in_sym 14%nat. Qed.
(* [TP - 8] = the dtv (Seg A's HC_dtv; __tls_get_addr {B}) *)
Lemma scene_c_dtv : forall ly, In (z8 (ATp (-8)) 0x5d6ab8) (as_const B ly).
Proof. in_sym 15%nat. Qed.
(* [TP + 8] = D, DTLS's dtv block (Seg A's HC_dtls; DTLS_on_tls_get_addr {C}) *)
Lemma scene_c_dtls : forall ly, In (c8 (ATp 8) (AD 0)) (as_const B ly).
Proof. in_sym 16%nat. Qed.
(* [D + 24] = TP, dtv entry 1 already recorded (Seg A's HC_dtls_dtv1; {D}) *)
Lemma scene_c_dtls_dtv1 : forall ly, In (c8 (AD 24) (ATp 0)) (as_const B ly).
Proof. in_sym 17%nat. Qed.
(* [TSD] = C, the thread context (Seg A's HC_tsd_main; pthread_getspecific {E}) *)
Lemma scene_c_tsd_main : forall ly, In (c8 (ATsd 0) (AC 0)) (as_const B ly).
Proof. in_sym 12%nat. Qed.
(* [C + 152] = T, the AsanThread (Seg A's HC_ctx_thread; GetCurrentThread {F}) *)
Lemma scene_c_ctx_thread : forall ly, In (c8 (AC 152) (AT 0)) (as_const B ly).
Proof. in_sym 11%nat. Qed.
(* [T + 48], the thread's tls_beg (Seg A's HC_thread_tls_beg; interceptor {G}) *)
Lemma scene_c_thread_tls_beg : forall ly, In (z8 (AT 48) 0x5d71d0) (as_const B ly).
Proof. in_sym 6%nat. Qed.
(* [T + 56], the thread's tls_end (Seg A's HC_thread_tls_end; interceptor {H}) *)
Lemma scene_c_thread_tls_end : forall ly, In (z8 (AT 56) 0x5d72ac) (as_const B ly).
Proof. in_sym 7%nat. Qed.
(* TLS-GD .got pair, module 1 (Seg A's HC_tls_got_mod) *)
Lemma scene_c_tls_got_mod : forall ly, In (z8 (ANum 0x9c728) 0x1) (as_const B ly).
Proof. in_abs 85%nat. Qed.
(* TLS-GD .got pair, offset -0x800 (Seg A's HC_tls_got_off) *)
Lemma scene_c_tls_got_off : forall ly, In (z8 (ANum 0x9c730) 0xfffffffffffff800) (as_const B ly).
Proof. in_abs 86%nat. Qed.
(* real___tls_get_addr = musl __tls_get_addr (Seg A's HC_real_tga) *)
Lemma scene_c_real_tga : forall ly, In (z8 (ANum 0x9d7e8) 0x95964) (as_const B ly).
Proof. in_abs 80%nat. Qed.
(* dtv[1] = TP + 0x800 (Seg A's HC_dtv1) *)
Lemma scene_c_dtv1 : forall ly, In (z8 (ANum 0x5d6ac0) 0x5d7298) (as_const B ly).
Proof. in_abs 105%nat. Qed.
(* asan_inited = 1 (Seg A's HC_asan_inited; B-CERT-CELLS.md:5) *)
Lemma scene_asan_inited_cell : forall ly, In (z1 (ANum 0xa47d8) 0x1) (as_const B ly).
Proof. in_abs 51%nat. Qed.
(* tsd_key_inited = 1 (Seg A's HC_tsd_key_inited) *)
Lemma scene_c_tsd_key_inited : forall ly, In (z1 (ANum 0xa3360) 0x1) (as_const B ly).
Proof. in_abs 58%nat. Qed.
(* tsd_key = 0 (Seg A's HC_tsd_key) *)
Lemma scene_c_tsd_key : forall ly, In (z4 (ANum 0xa3364) 0x0) (as_const B ly).
Proof. in_abs 59%nat. Qed.
(* .got slot of common_flags (Seg A's HC_got_cflags) *)
Lemma scene_c_got_cflags : forall ly, In (z8 (ANum 0x9ba30) 0x135628) (as_const B ly).
Proof. in_abs 142%nat. Qed.
(* common_flags.intercept_tls_get_addr = 1 (Seg A's HC_cflag_tga) *)
Lemma scene_c_cflag_tga : forall ly, In (z1 (ANum 0x1356b1) 0x1) (as_const B ly).
Proof. in_abs 69%nat. Qed.
(* .got slot of current_verbosity (Seg A's HC_got_verb) *)
Lemma scene_c_got_verb : forall ly, In (z8 (ANum 0x9ba90) 0x133598) (as_const B ly).
Proof. in_abs 154%nat. Qed.
(* current_verbosity = 0 (Seg A's HC_verb) *)
Lemma scene_c_verb : forall ly, In (z4 (ANum 0x133598) 0x0) (as_const B ly).
Proof. in_abs 70%nat. Qed.
(* .got slot of DTLS's tp offset (Seg A's HC_got_dtls) *)
Lemma scene_c_got_dtls : forall ly, In (z8 (ANum 0x9c738) 0x8) (as_const B ly).
Proof. in_abs 71%nat. Qed.
(* __asan_option_detect_stack_use_after_return = 1 (B-CERT-CELLS.md:4) *)
Lemma scene_c_uar_flag : forall ly, In (z4 (ANum 0xa3b00) 0x1) (as_const B ly).
Proof. in_abs 50%nat. Qed.
(* can_poison_memory = 1 (B-CERT-CELLS.md:6) *)
Lemma scene_c_can_poison : forall ly, In (z1 (ANum 0xa335c) 0x1) (as_const B ly).
Proof. in_abs 57%nat. Qed.
(* kHighMemEnd (B-CERT-CELLS.md:7) *)
Lemma scene_c_khighmemend : forall ly, In (z8 (ANum 0xa47e0) 0x7fffffffffff) (as_const B ly).
Proof. in_abs 53%nat. Qed.
(* kMidMemBeg = 0 (B-CERT-CELLS.md:8) *)
Lemma scene_c_kmidmembeg : forall ly, In (z8 (ANum 0xa47e8) 0x0) (as_const B ly).
Proof. in_abs 54%nat. Qed.
(* kMidMemEnd = 0 (B-CERT-CELLS.md:9) *)
Lemma scene_c_kmidmemend : forall ly, In (z8 (ANum 0xa47f0) 0x0) (as_const B ly).
Proof. in_abs 55%nat. Qed.
(* __asan_shadow_memory_dynamic_address = SHADOW_OFF (B-CERT-CELLS.md:10) *)
Lemma scene_c_shadow_dyn : forall ly, In (z8 (ANum 0xa3af8) 0x7fff8000) (as_const B ly).
Proof. in_abs 49%nat. Qed.
(* common_flags + 0x20: fast_unwind_on_check 0, _fatal 0, _malloc 1, malloc_context_size 30 (B-CERT-CELLS.md:12-13) *)
Lemma scene_c_cf_unwind : forall ly, In (z8 (ANum 0x135648) 0x1e00010000) (as_const B ly).
Proof. in_abs 4%nat. Qed.
(* common_flags + 0x48: detect_leaks 0 (+0x4a), leak_check_at_exit 1 (+0x4b) (B-CERT-CELLS.md:14) *)
Lemma scene_c_cf_leaks : forall ly, In (z8 (ANum 0x135670) 0x10101000101) (as_const B ly).
Proof. in_abs 9%nat. Qed.
(* common_flags + 0x78 clear_shadow_mmap_threshold = 2^64-1 (B-CERT-CELLS.md:15) *)
Lemma scene_c_cf_clear_thresh : forall ly, In (z8 (ANum 0x1356a0) 18446744073709551615) (as_const B ly).
Proof. in_abs 15%nat. Qed.
(* common_flags + 0x98 hard_rss_limit_mb = 0 (B-CERT-CELLS.md:16) *)
Lemma scene_c_cf_hard_rss : forall ly, In (z8 (ANum 0x1356c0) 0x0) (as_const B ly).
Proof. in_abs 19%nat. Qed.
(* common_flags + 0xa0 soft_rss_limit_mb = 0 (B-CERT-CELLS.md:16) *)
Lemma scene_c_cf_soft_rss : forall ly, In (z8 (ANum 0x1356c8) 0x0) (as_const B ly).
Proof. in_abs 20%nat. Qed.
(* common_flags + 0xb0 heap_profile = 0 (B-CERT-CELLS.md:17) *)
Lemma scene_c_cf_heap_profile : forall ly, In (z8 (ANum 0x1356d8) 0xffffffff00000000) (as_const B ly).
Proof. in_abs 22%nat. Qed.
(* common_flags + 0xf0 compress_stack_depot = 0 (B-CERT-CELLS.md:17) *)
Lemma scene_c_cf_compress_depot : forall ly, In (z8 (ANum 0x135718) 0x101000100000000) (as_const B ly).
Proof. in_abs 30%nat. Qed.
(* asan_flags_dont_use_directly + 24 report_globals = 1 (B-CERT-CELLS.md:20) *)
Lemma scene_c_report_globals : forall ly, In (z8 (ANum 0xa1310) 0x101010000000001) (as_const B ly).
Proof. in_abs 37%nat. Qed.
(* .got GetEnv seal word = 1 (B-CERT-CELLS.md:21) *)
Lemma scene_c_got_getenv_seal : forall ly, In (z8 (ANum 0x9ba80) 0x1) (as_const B ly).
Proof. in_abs 152%nat. Qed.
(* REAL(memset) = musl memset (B-CERT-CELLS.md:22) *)
Lemma scene_c_real_memset : forall ly, In (z8 (ANum 0x9d8b0) 0x95174) (as_const B ly).
Proof. in_abs 66%nat. Qed.
(* .got slot of the shadow-base cell (B-CERT-CELLS.md:10 GOT, item 7 SceneAddr A_OBJ 1) *)
Lemma scene_c_got_shadow : forall ly, In (z8 (ANum 0x9ba40) 0xa3af8) (as_const B ly).
Proof. in_abs 144%nat. Qed.
(* .got slot of the UAR flag (CHECKSTEP-REVIEW.md:66, SceneAddr A_OBJ 0) *)
Lemma scene_c_got_uar : forall ly, In (z8 (ANum 0x9ba98) 0xa3b00) (as_const B ly).
Proof. in_abs 155%nat. Qed.
(* shadow 0x7fffc1b1 = 4: check_step.trailer (0x20d80, 12)'s partial granule *)
Lemma scene_sh_trailer_p : forall ly, In (z1 (ANum 0x7fffc1b1) 0x4) (as_const B ly).
Proof. in_sh 0%nat. Qed.
(* shadow 0x7fffc1b2 = f9: trailer's redzone *)
Lemma scene_sh_trailer_rz0 : forall ly, In (z1 (ANum 0x7fffc1b2) 0xf9) (as_const B ly).
Proof. in_sh 1%nat. Qed.
(* shadow 0x7fffc1b3 = f9: trailer's redzone *)
Lemma scene_sh_trailer_rz1 : forall ly, In (z1 (ANum 0x7fffc1b3) 0xf9) (as_const B ly).
Proof. in_sh 2%nat. Qed.
(* shadow 0x7fffc1ba = 2: __const.check_step.frame (0x20da0, 50)'s partial granule *)
Lemma scene_sh_cframe_p : forall ly, In (z1 (ANum 0x7fffc1ba) 0x2) (as_const B ly).
Proof. in_sh 3%nat. Qed.
(* shadow 0x7fffc1bb = f9 *)
Lemma scene_sh_cframe_rz0 : forall ly, In (z1 (ANum 0x7fffc1bb) 0xf9) (as_const B ly).
Proof. in_sh 4%nat. Qed.
(* shadow 0x7fffc1bc = f9 *)
Lemma scene_sh_cframe_rz1 : forall ly, In (z1 (ANum 0x7fffc1bc) 0xf9) (as_const B ly).
Proof. in_sh 5%nat. Qed.
(* shadow 0x7fffc1bd = f9 *)
Lemma scene_sh_cframe_rz2 : forall ly, In (z1 (ANum 0x7fffc1bd) 0xf9) (as_const B ly).
Proof. in_sh 6%nat. Qed.
(* shadow 0x7fffc1be = f9 *)
Lemma scene_sh_cframe_rz3 : forall ly, In (z1 (ANum 0x7fffc1be) 0xf9) (as_const B ly).
Proof. in_sh 7%nat. Qed.
(* shadow 0x7fffc1bf = f9 *)
Lemma scene_sh_cframe_rz4 : forall ly, In (z1 (ANum 0x7fffc1bf) 0xf9) (as_const B ly).
Proof. in_sh 8%nat. Qed.
(* shadow 0x7fffc1c5 = 4: the (0x20e20, 12) global's partial granule *)
Lemma scene_sh_kl1_p : forall ly, In (z1 (ANum 0x7fffc1c5) 0x4) (as_const B ly).
Proof. in_sh 9%nat. Qed.
(* shadow 0x7fffc1c6 = f9 *)
Lemma scene_sh_kl1_rz0 : forall ly, In (z1 (ANum 0x7fffc1c6) 0xf9) (as_const B ly).
Proof. in_sh 10%nat. Qed.
(* shadow 0x7fffc1c7 = f9 *)
Lemma scene_sh_kl1_rz1 : forall ly, In (z1 (ANum 0x7fffc1c7) 0xf9) (as_const B ly).
Proof. in_sh 11%nat. Qed.
(* shadow 0x7fffc1c8 = 7: .str.4 (0x20e40, 7), parse's bcmp operand *)
Lemma scene_sh_str4_p : forall ly, In (z1 (ANum 0x7fffc1c8) 0x7) (as_const B ly).
Proof. in_sh 12%nat. Qed.
(* shadow 0x7fffc1c9 = f9 *)
Lemma scene_sh_str4_rz0 : forall ly, In (z1 (ANum 0x7fffc1c9) 0xf9) (as_const B ly).
Proof. in_sh 13%nat. Qed.
(* shadow 0x7fffc1ca = f9 *)
Lemma scene_sh_str4_rz1 : forall ly, In (z1 (ANum 0x7fffc1ca) 0xf9) (as_const B ly).
Proof. in_sh 14%nat. Qed.
(* shadow 0x7fffc1cb = f9 *)
Lemma scene_sh_str4_rz2 : forall ly, In (z1 (ANum 0x7fffc1cb) 0xf9) (as_const B ly).
Proof. in_sh 15%nat. Qed.
(* ---- 9. the zero ranges and the owned redzones ---------------------------------------- *)
(* CHECKSTEP-REVIEW.md R2's HB_Z_TR and HB_Z_CF: check_step.trailer's one full granule and
   __const.check_step.frame's six lie in a zero-shadow range of the certificate. *)
Lemma scene_z_trailer : Exists (zr_sub (0x20d80, 8)) (as_zero_shadow B).
Proof.
apply Exists_exists. exists (0x10000, 0x20d88 - 0x10000).
split; [in_zr 0%nat|]. unfold zr_sub. cbn [fst snd]. lia.
Qed.
Lemma scene_z_cframe : Exists (zr_sub (0x20da0, 48)) (as_zero_shadow B).
Proof.
apply Exists_exists. exists (0x20da0, 0x20dd0 - 0x20da0).
split; [in_zr 1%nat|]. unfold zr_sub. cbn [fst snd]. lia.
Qed.
(* The same two, and the 8904-byte placeholder, in the `in_zs` form the walks take
   (SceneRo.v:41-42). The placeholder is whole granules, so all of it is in one range. *)
Lemma scene_zs_trailer : in_zs B 0x20d80 8.
Proof. exists 0x10000, (0x20d88 - 0x10000). split; [in_zr 0%nat | lia]. Qed.
Lemma scene_zs_cframe : in_zs B 0x20da0 48.
Proof. exists 0x20da0, (0x20dd0 - 0x20da0). split; [in_zr 1%nat | lia]. Qed.
Lemma scene_zs_kl1 : in_zs B 0x20e20 8.
Proof. exists 0x20e00, (0x20e28 - 0x20e00). split; [in_zr 2%nat | lia]. Qed.
(* HB_Z_TT in a Theorem Labs lane's frozen entry form (18ba727d44b P_LLVMFuzzerTestOneInput.v:237, AU :245):
   in_zs B (A_TAIL_TRAILER - 0x20) (0x20 + (TAIL_TRAILER_N - TAIL_TRAILER_N mod 8)), with A_TAIL_TRAILER = 0x20e20
   and TAIL_TRAILER_N = 12, i.e. the zero range (0x20e00, 0x28) that also covers the 0x20 bytes below the trailer. *)
Lemma scene_z_tt : in_zs B (0x20e20 - 0x20) (0x20 + (12 - 12 mod 8)).
Proof. exists 0x20e00, (0x20e28 - 0x20e00). split; [in_zr 2%nat | lia]. Qed.
(* HB_C_PL (a Theorem Labs lane 327f73c7513 A/P_LLVMFuzzerTestOneInput.v:247-249, AU :250-253): the eight 0xf9 shadow cells
   starting at shadow_addr (A_reac_scene_placeholder + LLVMF_SCENE_BYTES) = shadow_addr (0x20e80 + 8904) = 0x7fffc629,
   the head of the placeholder's redzone shadow; Tfib_const_shadow entries 16..23. *)
Lemma scene_sh_pl0 : forall ly, In (z1 (ANum 0x7fffc629) 0xf9) (as_const B ly).
Proof. in_sh 16%nat. Qed.
Lemma scene_sh_pl1 : forall ly, In (z1 (ANum 0x7fffc62a) 0xf9) (as_const B ly).
Proof. in_sh 17%nat. Qed.
Lemma scene_sh_pl2 : forall ly, In (z1 (ANum 0x7fffc62b) 0xf9) (as_const B ly).
Proof. in_sh 18%nat. Qed.
Lemma scene_sh_pl3 : forall ly, In (z1 (ANum 0x7fffc62c) 0xf9) (as_const B ly).
Proof. in_sh 19%nat. Qed.
Lemma scene_sh_pl4 : forall ly, In (z1 (ANum 0x7fffc62d) 0xf9) (as_const B ly).
Proof. in_sh 20%nat. Qed.
Lemma scene_sh_pl5 : forall ly, In (z1 (ANum 0x7fffc62e) 0xf9) (as_const B ly).
Proof. in_sh 21%nat. Qed.
Lemma scene_sh_pl6 : forall ly, In (z1 (ANum 0x7fffc62f) 0xf9) (as_const B ly).
Proof. in_sh 22%nat. Qed.
Lemma scene_sh_pl7 : forall ly, In (z1 (ANum 0x7fffc630) 0xf9) (as_const B ly).
Proof. in_sh 23%nat. Qed.
Lemma scene_c_pl : forall ly, Forall (fun c => In c (as_const B ly))
  (map (fun k => z1 (ANum (0x7fffc629 + Z.of_nat k)) 0xf9) (seq 0 8)).
Proof.
intro ly. cbn [map seq].
apply Forall_cons; [exact (scene_sh_pl0 ly)|].
apply Forall_cons; [exact (scene_sh_pl1 ly)|].
apply Forall_cons; [exact (scene_sh_pl2 ly)|].
apply Forall_cons; [exact (scene_sh_pl3 ly)|].
apply Forall_cons; [exact (scene_sh_pl4 ly)|].
apply Forall_cons; [exact (scene_sh_pl5 ly)|].
apply Forall_cons; [exact (scene_sh_pl6 ly)|].
apply Forall_cons; [exact (scene_sh_pl7 ly)|].
apply Forall_nil.
Qed.
Lemma scene_zs_placeholder : in_zs B 0x20e80 8904.
Proof. exists 0x20e60, (0x23148 - 0x20e60). split; [in_zr 3%nat | lia]. Qed.

(* CHECKSTEP-REVIEW.md R2's HB_C_CS, in the exact shape of a Theorem Labs lane's P_check_step.v:136-141
   (at f6b5a0ae3036), with A_CS_TRAILER / A_CS_CFRAME at the values its HB_ADDR fixes. *)
Lemma scene_cs_shadow : forall ly,
  In (z1 (ANum (shadow_addr 0x20d80 + 1)) 4) (as_const B ly) /\
  In (z1 (ANum (shadow_addr 0x20d80 + 2)) 0xf9) (as_const B ly) /\
  In (z1 (ANum (shadow_addr 0x20d80 + 3)) 0xf9) (as_const B ly) /\
  In (z1 (ANum (shadow_addr 0x20da0 + 6)) 2) (as_const B ly) /\
  Forall (fun i => In (z1 (ANum (shadow_addr 0x20da0 + i)) 0xf9) (as_const B ly)) [7; 8; 9; 10; 11].
Proof.
intro ly. split; [exact (scene_sh_trailer_p ly)|]. split; [exact (scene_sh_trailer_rz0 ly)|].
split; [exact (scene_sh_trailer_rz1 ly)|]. split; [exact (scene_sh_cframe_p ly)|].
apply Forall_cons; [exact (scene_sh_cframe_rz0 ly)|]. apply Forall_cons; [exact (scene_sh_cframe_rz1 ly)|].
apply Forall_cons; [exact (scene_sh_cframe_rz2 ly)|]. apply Forall_cons; [exact (scene_sh_cframe_rz3 ly)|].
apply Forall_cons; [exact (scene_sh_cframe_rz4 ly)|]. apply Forall_nil.
Qed.

(* CHECKSTEP-REVIEW.md R2's SCENE_RZ_OWNED: every redzone tail, and the descriptor array. *)
Lemma scene_rz_trailer : In (0x20d8c, 0x14) (as_owned_static B).
Proof. in_own 24%nat. Qed.
Lemma scene_rz_cframe : In (0x20dd2, 0x2e) (as_owned_static B).
Proof. in_own 25%nat. Qed.
Lemma scene_rz_kl1 : In (0x20e2c, 0x14) (as_owned_static B).
Proof. in_own 26%nat. Qed.
Lemma scene_rz_str4 : In (0x20e47, 0x19) (as_owned_static B).
Proof. in_own 27%nat. Qed.
Lemma scene_rz_placeholder : In (0x23148, 0x8b8) (as_owned_static B).
Proof. in_own 28%nat. Qed.
Lemma scene_rz_descriptors : In (0xa0300, 0x140) (as_owned_static B).
Proof. in_own 1%nat. Qed.
Lemma scene_owned_rz : incl SCENE_RZ_OWNED (as_owned_static B).
Proof.
intros r Hr. cbn [SCENE_RZ_OWNED In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
- exact scene_rz_trailer.
- exact scene_rz_cframe.
- exact scene_rz_kl1.
- exact scene_rz_str4.
- exact scene_rz_placeholder.
- exact scene_rz_descriptors.
Qed.

(* ---- 10. the five registered globals, by name ------------------------------------------ *)
Lemma scene_glob_trailer : In (0x20d80, 12) SCENE_GLOBS.
Proof. apply (nth_error_In SCENE_GLOBS 0%nat). vm_compute. reflexivity. Qed.
Lemma scene_glob_cframe : In (0x20da0, 50) SCENE_GLOBS.
Proof. apply (nth_error_In SCENE_GLOBS 1%nat). vm_compute. reflexivity. Qed.
Lemma scene_glob_kl1 : In (0x20e20, 12) SCENE_GLOBS.
Proof. apply (nth_error_In SCENE_GLOBS 2%nat). vm_compute. reflexivity. Qed.
Lemma scene_glob_str4 : In (0x20e40, 7) SCENE_GLOBS.
Proof. apply (nth_error_In SCENE_GLOBS 3%nat). vm_compute. reflexivity. Qed.
Lemma scene_glob_placeholder : In (0x20e80, 8904) SCENE_GLOBS.
Proof. apply (nth_error_In SCENE_GLOBS 4%nat). vm_compute. reflexivity. Qed.

(* ---- 11. the two facts the walks take as hypotheses, proved at scene's B ---------------
   Donor: GrantClose.v:380-443 (grant_shadow_cell, grant_zs_rd, grant_img_shadow_vis,
   grant_globs_marked). They hold for every segment list, because neither `am_const` nor
   `al_zshadow` looks at the segments. *)
(* A shadow cell of the start-up certificate holds its byte in every state. *)
Lemma scene_shadow_cell : forall segs ly S (W : world segs) mem md s v,
  AR segs B ly S W mem md -> In (z1 (ANum s) v) Tfib_const_shadow ->
  aview segs (w_H W) mem s = Some (YG0f.le_byte v 1 0).
Proof.
intros segs ly S W mem md s v HAR Hin.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite Forall_forall in HC.
assert (Hin' : In (z1 (ANum s) v) (as_const B ly)).
{ apply scene_in_const. unfold Tfib_const. apply in_or_app. right. apply in_or_app. right. exact Hin. }
specialize (HC _ Hin'). unfold cell_holds, z1, c1 in HC. cbn [c_at c_val c_w aeval] in HC.
specialize (HC 0%nat ltac:(lia)). cbn [Z.of_nat] in HC. rewrite Z.add_0_r in HC. exact HC.
Qed.

(* A granule of a zero-shadow range of the certificate has shadow byte 0 in every state. *)
Lemma scene_zs_rd : forall segs ly S (W : world segs) mem md q m j,
  AR segs B ly S W mem md -> In (q, m) Tfib_zero_shadow -> q / 8 <= j < (q + m) / 8 ->
  aview segs (w_H W) mem (SHADOW_OFF + j) = Some 0.
Proof.
intros segs ly S W mem md q m j HAR Hin Hj.
pose proof (al_zshadow _ _ (scene_LAWS segs) ly S W mem md (q, m) HAR (or_intror (scene_in_zsh _ Hin))) as Hz.
cbn [fst snd] in Hz.
destruct (zs_align q m Hin) as (Hq & Hm & Hm0).
assert (E : (q + m) / 8 = q / 8 + m / 8).
{ pose proof (Z.div_mod q 8 ltac:(lia)) as Dq.
  replace (q + m) with (m + q / 8 * 8) by lia. rewrite Z.div_add by lia. lia. }
replace (SHADOW_OFF + j) with (shadow_of_addr SHADOW_OFF q + (j - q / 8)) by (unfold shadow_of_addr; lia).
apply Hz. lia.
Qed.

(* HIMGSH: every shadow byte of the image's read range is mapped, in every state. *)
Lemma scene_img_shadow_vis : forall segs, img_shadow_vis segs B.
Proof.
intros segs ly S W mem md a HAR Ha. unfold shadow_addr.
assert (E8 : 8 * (IMG_HI / 8) = IMG_HI) by (vm_compute; reflexivity).
assert (Hj : IMG_LO / 8 <= a / 8 < IMG_HI / 8).
{ split; [apply Z.div_le_mono; lia | apply Z.div_lt_upper_bound; lia]. }
destruct (vscan_ok _ _ _ scene_vscan (a / 8) Hj) as [(q & m & Hin & Hq) | Hc].
- rewrite (scene_zs_rd segs ly S W mem md q m (a / 8) HAR Hin Hq). discriminate.
- apply existsb_exists in Hc as (c & Hin & Hb). destruct (is_shc_eq _ _ Hb) as [v ->].
  rewrite (scene_shadow_cell segs ly S W mem md _ v HAR Hin). discriminate.
Qed.

(* HGM: each registered global's bytes are marked usable, and its partial granule carries
   `size mod 8`, in every state. *)
Lemma scene_globs_marked : forall segs, globs_marked segs B SCENE_GLOBS.
Proof.
intros segs ly S W mem md q sz Hin HAR.
pose proof (proj1 (forallb_forall _ _) scene_globs_chk (q, sz) Hin) as Hb.
unfold glob_chk in Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb Hlast]. apply andb_prop in Hb as [Hb Hfull]. apply andb_prop in Hb as [Hq Hsz].
apply Z.eqb_eq in Hq. apply Z.leb_le in Hsz.
split; [exact Hq|]. split; [exact Hsz|]. intros i Hi.
pose proof (Z.div_mod q 8 ltac:(lia)) as Dq.
pose proof (Z.div_mod sz 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)) as Bs.
pose proof (Z.div_mod (sz + 7) 8 ltac:(lia)) as Ds7. pose proof (Z.mod_pos_bound (sz + 7) 8 ltac:(lia)) as Bs7.
destruct (i <? sz / 8) eqn:Hlt.
- apply Z.ltb_lt in Hlt.
  apply orb_true_iff in Hfull as [H0|H0]; [apply Z.eqb_eq in H0; exfalso; lia|].
  apply existsb_exists in H0 as ([r0 m0] & Hr & Hf). cbn [fst snd] in Hf.
  apply andb_prop in Hf as [Hf1 Hf2]. apply Z.leb_le in Hf1. apply Z.leb_le in Hf2.
  destruct (zs_align r0 m0 Hr) as (Hr8 & Hm8 & Hm0).
  pose proof (Z.div_mod r0 8 ltac:(lia)) as Dr. pose proof (Z.div_mod m0 8 ltac:(lia)) as Dm.
  pose proof (Z.div_mod (r0 + m0) 8 ltac:(lia)) as Drm. pose proof (Z.mod_pos_bound (r0 + m0) 8 ltac:(lia)) as Brm.
  unfold shadow_of_addr.
  replace (SHADOW_OFF + q / 8 + i) with (SHADOW_OFF + (q / 8 + i)) by lia.
  apply (scene_zs_rd segs ly S W mem md r0 m0); [exact HAR | exact Hr | lia].
- apply Z.ltb_ge in Hlt.
  assert (Hi' : i = sz / 8) by lia.
  apply orb_true_iff in Hlast as [H0|H0]; [apply Z.eqb_eq in H0; exfalso; lia|].
  apply existsb_exists in H0 as (c & Hc & Hcb). apply is_shv_eq in Hcb. subst c. subst i.
  unfold shadow_of_addr.
  rewrite (scene_shadow_cell segs ly S W mem md _ _ HAR Hc). rewrite le_byte1 by lia. reflexivity.
Qed.

End c.
End b.

(* ---- 12. what this file does not prove -------------------------------------------------
   One Section hypothesis is left, `HB : TfibSyms B` (section 4 above). It is not discharged
   here: this file is generic in B. The concrete instance is lib/AU/YD2l.v: its TfibB carries
   scene's runtime addresses (as_shadow_cell 0xa3af8, as_uar_cell 0xa3b00, as_got_shadow
   0x9ba40, YD2l.v:49-51; section 7 above), and its `as_universe` field reads `Tfib_universe`
   from lib/AU/YCej.v, fuzz_scene's measured trace universe. TfibB_syms : TfibSyms TfibB is
   proved at YD2l.v:101-113 (Qed), and G_Close.v applies this file's lemmas at B := TfibB,
   HB := TfibB_syms, so every fact above holds of scene's concrete B. The five rows below are
   a separate matter: they have no cell in the start-up tables.

   Five rows of B-CERT-CELLS.md (sha256 d459f8bdaebe; internal record) have no cell in
   YF0m.v's start-up tables, so they are stated nowhere above. Each is listed here with the
   address B-CERT-CELLS.md measures, for the pending YF0m generator fix:
     - __libc.threaded (0x5f6d29, 1 byte, 0), B-CERT-CELLS.md:23;
     - __odr_asan_gen_reac_scene_placeholder (0x5d6180, 1 byte, 1), B-CERT-CELLS.md:25;
     - atexit slot (0x5f6af0, 4 bytes, 1), head (0x5f6af8, 8 bytes), builtin.f[0]
       (0x5f6b08, 8 bytes) and a[0] (0x5f6c08, 8 bytes, __sanitizer_cov_dump 0x71e64), B-CERT-CELLS.md:26. The
       values of head and of builtin.f[0] are not given numerically in any source this lane
       cites, so no cell for them could be stated without inventing a number.
     - the ak_owned sink addresses ofl_head (0x5f7190), ofl_lock (0x5f7188) and __libc + 1
       (0x5f6d29), B-CERT-CELLS.md:27: these are addresses of the sink record, not cells
       of `as_const`.
   One further row is deliberately not stated: oft_in_callback (0x5d6154) is 0 at main but 1
   inside target_run's call window (B-CERT-CELLS.md:24), so it is not constant over every AR
   state and cannot be a cell of `as_const B`. It belongs to the entry/exit composition
   (a Theorem Labs lane's ENTRY-REVIEW.md), not to this certificate. *)
