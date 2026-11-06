(* Theorem Labs, 2026-10: fuzz_preset image A' (#102 pin asan 1be0f53d, unstripped twin bff8519b), lane S7b (WalkS7bR,
   a Theorem Labs lane): INSTANCE WITNESSES of the STATIC image premises the writer walks (PRW_pj_write.v, PRW_put_string_base.v
   / _a / _t / _l / _e, PRW_write_value.v) take as Section hypotheses (unit ruling a Theorem Labs lane 16:45Z: every image
   premise needs a witness closed by vm_compute at the real instance). The instance: PA := PI_prog_A (the cut's
   lib/A/PAImg_prog.v 505a51ff7d08, the whole-program listing of image A') and B := AD2l.TfibB (the cut's lib/A/AD2l.v eb321db7a357, image A''s
   generated asyms record). Each lemma states the premise's text at the instance; each proof unfolds the instance's
   projections (cbn, so the listing table is never evaluated) and closes a closed term by vm_compute. The segments are
   named FULLY QUALIFIED (ASEGS; guard s7bw_segs_A), never by a short name a plain image could capture. Proves nothing
   about the program, and no walk Requires this file.
   The other image premises of the lane are witnessed elsewhere, ONE copy each (cited, not restated here):
     segs_low            : the class field pa_segs_low (at PI_prog_A: PAImg_prog.A_prog_segs_low);
     TL : PALib B        : PALibA.palib_A (blob 88c72c8175cf at the cut);
     errno_low (api_env) : PALibA.palib_errno_A (same file);
     HW (prh_head_wide)  : PALibA.palib_head_A (same file; a8's CfParamsPreset.preset_head_wide);
     ASO (asyms_ok B)    : AD2l.TfibB_ok;
     HPSTRO              : s7bw_pstro_A below (on WalkS7aR's generic S7a_litrd.s7w_pst_clear_b / _sound);
     the literals (pj_write's HLIT; put_string's HLIT17 / HLIT85 / 87 / 89 / 91 / 93; write_value's HLIT):
                           PRW_S7bLitWit.s7bl_pjw_hlit / s7bl_ps_hlit17 / s7bl_ps_hlit85 / 87 / 89 / 91 / 93 /
                           s7bl_wv_hlit (on WalkS7aR's generic S7a_litrd.s7w_lit_rd);
     AMS / AMCPY (the memset / memcpy rows at SIGMA ..): a Theorem Labs lane's PRowSet.prow_asan_memset_xm_A /
                           PRowCpyA.prow_asan_memcpy_xm_A (a working branch 599a4cefc740) at pc_asan_memset /
                           pc_asan_memcpy (as_code TA), glued by s7bw_memset_pc / s7bw_memcpy_pc below.
     SNP (put_string's escape: the engine's snprintf row at its instance): a Theorem Labs lane's snprintf_xrom_A
                           (lib/A/PSnpSnpRoot.v:140, blob 4edc9be9a050 at the cut) at the parameters whose closed side
                           conditions s7bw_snp_row_side below states; its STATIC instance facts SNPI (PRW_put_string_e.v
                           ps_snp_img): s7bw_ps_snp_img below.
   Numerals: none typed except the offsets 0 / 4 / 8 / 25 / 4 * 25 the premises themselves state, the page size 4096
   the image-top fact states, and in s7bw_snp_row_side the numerals of record of snprintf_xrom_A (cited there). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YP08 YL0b YG00 YG0f YG0n YG0d YP0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l.
(* the canary cells' names (Stdlib-only file; AE2p.v:32-33 copies them by Eval vm_compute, with a heavy closure) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AImgCells.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA S7a_litrd.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_pj_write PRW_put_string_base PRW_write_value.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_put_string_e.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_A.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation SEGS := (@pa_segs rc A_prog_listing PI_prog_A).
#[local] Abbreviation VAL := (@pa_val rc A_prog_listing PI_prog_A).
#[local] Abbreviation SIGMA := (@pa_sigma rc A_prog_listing PI_prog_A).
#[local] Abbreviation BASE := (@pa_val rc A_prog_listing PI_prog_A A_TEXT).
#[local] Abbreviation TA := AD2l.TfibB.
#[local] Abbreviation ASEGS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs.

(* the guard: the segments every witness below is stated over are image A''s (the walk's PI_prog_A), not a plain image's *)
Lemma s7bw_segs_A : SEGS = ASEGS.
Proof. reflexivity. Qed.

(* a disjointness of two byte ranges, read off a closed boolean *)
Lemma s7bw_disj_b : forall a n b m, ((a + n <=? b) || (b + m <=? a)) = true -> a + n <= b \/ b + m <= a.
Proof.
intros a n b m H. apply orb_true_iff in H as [H | H]; [left | right]; apply Z.leb_le; exact H.
Qed.

(* f holds at every byte of the ranges of P, read back at one byte (S1ImgA's pst_allb_sound, over any list) *)
Lemma s7bw_allb : forall f P a, pst_allb f P = true -> Exists (in_zr a) P -> f a = true.
Proof. exact pst_allb_sound. Qed.

Lemma s7bw_in_zr_b : forall a (L : list (Z * Z)),
  existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) L = false -> ~ Exists (in_zr a) L.
Proof.
intros a L H Hex. apply Exists_exists in Hex as (r & Hr & Ha). unfold in_zr in Ha.
assert (E : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) L = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite E in H. discriminate.
Qed.

(* ---- pj_write (PRW_pj_write.v Section h) ---- *)

(* Hent : SIGMA AS_pj_write = BASE + AF_pj_write *)
Lemma s7bw_pjw_ent : SIGMA AS_pj_write = BASE + PRW_pj_write.AF_pj_write.
Proof. cbn [pa_sigma pa_val PI_prog_A]. vm_compute. reflexivity. Qed.

(* HRET : nth 0 (pi_ret_sites F_pj_write RT_fuzz_free) 0 = BASE + AF_pj_write + 4 * 25 *)
Lemma s7bw_pjw_ret : nth 0 (pi_ret_sites F_pj_write RT_fuzz_free) 0 = BASE + PRW_pj_write.AF_pj_write + 4 * 25.
Proof. cbn [pa_val PI_prog_A]. vm_compute. reflexivity. Qed.

(* HIMGNL : in_img SEGS PJW_NL *)
Lemma s7bw_pjw_nl_img : in_img SEGS (PRW_pj_write.PJW_NL (PA := PI_prog_A)).
Proof.
unfold PRW_pj_write.PJW_NL. cbn [pa_val pa_segs PI_prog_A].
apply in_img_b_sound. vm_compute. reflexivity.
Qed.

(* ---- put_string (PRW_put_string_base.v Section h; _a / _t / _l / _e repeat it verbatim) ---- *)

(* Hent : SIGMA AS_put_string = BASE + AF_put_string *)
Lemma s7bw_ps_ent : SIGMA AS_put_string = BASE + PRW_put_string_base.AF_put_string.
Proof. cbn [pa_sigma pa_val PI_prog_A]. vm_compute. reflexivity. Qed.

(* Huar : as_got_uar B = VAL (A_OBJ 1) *)
Lemma s7bw_uar : as_got_uar TA = VAL (A_OBJ 1).
Proof. cbn [pa_val PI_prog_A]. vm_compute. reflexivity. Qed.

(* Hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i) /\
          in_img SEGS (VAL (A_OBJ 1) + i) *)
Lemma s7bw_obj : forall i, 0 <= i < 8 ->
  in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i) /\ in_img SEGS (VAL (A_OBJ 1) + i).
Proof.
intros i Hi. cbn [pa_val pa_segs PI_prog_A].
assert (C : pst_allb (in_img_b ASEGS)
              [(A_prog_val (A_OBJ 0), 8); (A_prog_val (A_OBJ 12), 8); (A_prog_val (A_OBJ 1), 8)] = true)
  by (vm_compute; reflexivity).
assert (R : forall k, (k < 3)%nat ->
          in_img ASEGS (fst (nth k [(A_prog_val (A_OBJ 0), 8); (A_prog_val (A_OBJ 12), 8); (A_prog_val (A_OBJ 1), 8)]
                               (0, 0)) + i)).
{ intros k Hk. apply in_img_b_sound. apply (s7bw_allb _ _ _ C). apply Exists_exists.
  exists (nth k [(A_prog_val (A_OBJ 0), 8); (A_prog_val (A_OBJ 12), 8); (A_prog_val (A_OBJ 1), 8)] (0, 0)).
  split; [apply nth_In; cbn [length]; exact Hk|].
  unfold in_zr. destruct k as [|[|[|k]]]; cbn [nth fst snd]; [lia | lia | lia | exfalso; lia]. }
exact (conj (R 0%nat ltac:(lia)) (conj (R 1%nat ltac:(lia)) (R 2%nat ltac:(lia)))).
Qed.

(* HOBJ : ps_objs_disj *)
Lemma s7bw_objs_disj : PRW_put_string_base.ps_objs_disj (PA := PI_prog_A).
Proof. unfold PRW_put_string_base.ps_objs_disj. cbn [pa_val PI_prog_A]. exact A_prog_got_uar_disj. Qed.

(* HUARC : ps_uar_ok B *)
Lemma s7bw_uarc : PRW_put_string_base.ps_uar_ok (PA := PI_prog_A) TA.
Proof.
unfold PRW_put_string_base.ps_uar_ok. cbn [pa_val pa_segs PI_prog_A].
assert (C : pst_allb (in_img_b ASEGS) [(as_uar_cell TA, 4)] = true) by (vm_compute; reflexivity).
split.
- intros i Hi. apply in_img_b_sound. apply (s7bw_allb _ _ _ C). apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- split; [|split]; apply s7bw_disj_b; vm_compute; reflexivity.
Qed.

(* Hsm0 : pc_stack_malloc (as_code B) 0 = SIGMA AS___asan_stack_malloc_0 *)
Lemma s7bw_sm0 : pc_stack_malloc (as_code TA) 0 = SIGMA AS___asan_stack_malloc_0.
Proof. cbn [pa_sigma PI_prog_A]. vm_compute. reflexivity. Qed.

(* PST_ok (put_string's form; pj_write's is its first two conjuncts) *)
Lemma s7bw_pst_ok_ps : forall a, Exists (in_zr a) (@prh_pst prh_img_A) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static TA) /\ ~ (as_errno TA <= a < as_errno TA + 4).
Proof.
intros a Ha. cbn [pa_segs PI_prog_A].
assert (C1 : pst_allb (fun x => negb (existsb (fun r => (fst r <=? x) && (x <? fst r + snd r)) (as_owned_static TA)))
               (@prh_pst prh_img_A) = true) by (vm_compute; reflexivity).
assert (C2 : pst_allb (fun x => negb ((as_errno TA <=? x) && (x <? as_errno TA + 4))) (@prh_pst prh_img_A) = true)
  by (vm_compute; reflexivity).
split; [exact (pst_in_img_A a Ha)|]. split.
- apply s7bw_in_zr_b. pose proof (s7bw_allb _ _ a C1 Ha) as H. cbv beta in H. apply negb_true_iff in H. exact H.
- pose proof (s7bw_allb _ _ a C2 Ha) as H. cbv beta in H. apply negb_true_iff in H. intros (H1 & H2).
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. rewrite H1, H2 in H. discriminate.
Qed.

Lemma s7bw_pst_ok_pjw : forall a, Exists (in_zr a) (@prh_pst prh_img_A) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static TA).
Proof. intros a Ha. destruct (s7bw_pst_ok_ps a Ha) as (H1 & H2 & _). exact (conj H1 H2). Qed.

(* HPSTRO (every walk file) : no static of alloc.c lies in the read-only band; one closed check over prh_pst *)
Lemma s7bw_pst_clear_c : s7w_pst_clear_b ASEGS A_prog_relro_lo A_prog_relro_hi (@prh_pst prh_img_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s7bw_pstro_A : forall a,
  in_roP SEGS (@pa_relro_lo rc A_prog_listing PI_prog_A) (@pa_relro_hi rc A_prog_listing PI_prog_A) a ->
  ~ Exists (in_zr a) (@prh_pst prh_img_A).
Proof. intros a. exact (s7w_pst_clear_sound ASEGS A_prog_relro_lo A_prog_relro_hi _ s7bw_pst_clear_c a). Qed.

(* HPAB (put_string's five segment files) : pa_lo = IMG_LO /\ pa_hi = IMG_TOP *)
Lemma s7bw_hpab : @pa_lo rc A_prog_listing PI_prog_A = IMG_LO /\ @pa_hi rc A_prog_listing PI_prog_A = IMG_TOP.
Proof. split; reflexivity. Qed.

(* the memset / memcpy rows' entries: the listing's symbol is the record's code pointer (AMS / AMCPY glue) *)
Lemma s7bw_memset_pc : SIGMA AS___asan_memset = pc_asan_memset (as_code TA).
Proof. cbn [pa_sigma PI_prog_A]. vm_compute. reflexivity. Qed.
Lemma s7bw_memcpy_pc : SIGMA AS___asan_memcpy = pc_asan_memcpy (as_code TA).
Proof. cbn [pa_sigma PI_prog_A]. vm_compute. reflexivity. Qed.

(* ---- put_string's escape (PRW_put_string_e.v Section fl2): the snprintf row's instance (WalkS7bR.SnpInstR) ---- *)

(* the row's canary cells at A': AImgCells' names (AE2p.v:32-33's A_GOT_canary / A_canary are their Eval vm_compute
   copies; the values of record of snprintf_xrom_A, PSnpI.v:122-123, blob db2a638d5f58 at the cut) *)
#[local] Abbreviation GCAN := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AImgCells.A_GOT_STACK_CHK_GUARD.
#[local] Abbreviation CAN := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AImgCells.A_STACK_CHK_GUARD.

(* an 8-byte constant cell at (ANum p) holding (ANum v), found in a list by a closed boolean *)
Lemma s7bw_cell8_b : forall p v (l : list acell),
  existsb (fun c => match c with
                    | ACell (ANum q) w (AV (ANum u)) => Nat.eqb w 8 && (q =? p) && (u =? v)
                    | _ => false
                    end) l = true ->
  In (z8 (ANum p) v) l.
Proof.
intros p v l H. apply existsb_exists in H as (c & Hc & H).
destruct c as [e w val]. destruct e; cbv beta iota in H; try discriminate H.
destruct val as [e' | m x]; cbv beta iota in H; [|discriminate H].
destruct e'; cbv beta iota in H; try discriminate H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst. exact Hc.
Qed.

(* a constant cell (ANum p, w bytes, value ANum v) that covers the byte a and holds a's image byte there; the image
   byte is read only when the cell covers a *)
Definition s7bw_pin_c (segs : list Segment) (a : Z) (c : acell) : bool :=
  match c with
  | ACell (ANum p) w (AV (ANum v)) =>
      if (p <=? a) && (a <? p + Z.of_nat w) then
        match seg_rom segs (Z_to_bv 64 a) with
        | Some b => bv_unsigned b =? YG0f.le_byte v w (Z.to_nat (a - p))
        | None => false
        end
      else false
  | _ => false
  end.
Lemma s7bw_pin_sound : forall segs a (l : list acell), existsb (s7bw_pin_c segs a) l = true ->
  exists p (w : nat) v, In (ACell (ANum p) w (AV (ANum v))) l /\ p <= a < p + Z.of_nat w /\
    option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)) =
    Some (YG0f.le_byte v w (Z.to_nat (a - p))).
Proof.
intros segs a l H. apply existsb_exists in H as (c & Hc & H). unfold s7bw_pin_c in H.
destruct c as [e w val]. destruct e; cbv beta iota in H; try discriminate H.
destruct val as [e' | m x]; cbv beta iota in H; [|discriminate H].
destruct e'; cbv beta iota in H; try discriminate H.
lazymatch type of H with
| (if ?t then _ else _) = true => revert H; destruct t eqn:Er; intros H; cbv beta iota in H; [|discriminate H]
end.
apply andb_prop in Er as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
revert H. destruct (seg_rom segs (Z_to_bv 64 a)) as [b|]; intros H; cbv beta iota in H; [|discriminate H].
apply Z.eqb_eq in H. do 3 eexists. split; [exact Hc|]. split; [lia|].
cbn [option_map]. rewrite H. reflexivity.
Qed.

(* a byte in one of the ranges L, as a closed boolean *)
Definition s7bw_in_b (L : list (Z * Z)) (a : Z) : bool := existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) L.
Lemma s7bw_in_b_of : forall L a, Exists (in_zr a) L -> s7bw_in_b L a = true.
Proof.
intros L a H. apply Exists_exists in H as (r & Hr & Ha). apply existsb_exists. exists r. split; [exact Hr|].
unfold in_zr in Ha. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* SNPI : ps_snp_img B gcan can (PRW_put_string_e.v), at gcan / can := GCAN / CAN *)
Lemma s7bw_ps_snp_img : PRW_put_string_e.ps_snp_img (PA := PI_prog_A) TA GCAN CAN.
Proof.
unfold PRW_put_string_e.ps_snp_img.
split; [|split; [|split; [|split; [|split; [|split]]]]].
- (* .str.18 "\\%c" with its NUL ends below the GOT cell *)
  apply Z.leb_le. unfold PRW_put_string_base.ps_str, PRW_put_string_base.ps_lit. cbn [pa_val PI_prog_A].
  vm_compute. reflexivity.
- (* .str.22 "\\u%04x" with its NUL ends below the GOT cell *)
  apply Z.leb_le. unfold PRW_put_string_base.ps_str, PRW_put_string_base.ps_lit. cbn [pa_val PI_prog_A].
  vm_compute. reflexivity.
- (* the two cells are image bytes; each byte of the canary cell has an image byte *)
  intros j Hj. cbn [pa_segs PI_prog_A].
  assert (C1 : pst_allb (in_img_b ASEGS) [(GCAN, 8); (CAN, 8)] = true) by (vm_compute; reflexivity).
  assert (C2 : pst_allb (fun x => match seg_rom ASEGS (Z_to_bv 64 x) with Some _ => true | None => false end)
                 [(CAN, 8)] = true) by (vm_compute; reflexivity).
  split; [|split].
  + apply in_img_b_sound. apply (s7bw_allb _ _ _ C1). apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  + apply in_img_b_sound. apply (s7bw_allb _ _ _ C1). apply Exists_cons_tl, Exists_cons_hd. unfold in_zr.
    cbn [fst snd]. lia.
  + pose proof (s7bw_allb _ _ (CAN + j) C2 ltac:(apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia)) as H.
    cbv beta in H. change (seg_rom ASEGS (Z_to_bv 64 (CAN + j)) <> None).
    destruct (seg_rom ASEGS (Z_to_bv 64 (CAN + j))); [discriminate | discriminate H].
- (* the GOT cell is one of TA's constant cells, holding CAN *)
  intros ly. apply s7bw_cell8_b. cbn [as_const AD2l.TfibB]. vm_compute. reflexivity.
- (* every read-only range is nonempty and apart from errno *)
  assert (C : forallb (fun r => (0 <? snd r) && ((fst r + snd r <=? as_errno TA) || (as_errno TA + 4 <=? fst r)))
                (PRW_put_string_e.ps_snp_cr (PA := PI_prog_A)) = true).
  { unfold PRW_put_string_e.ps_snp_cr. cbn [pa_segs PI_prog_A]. vm_compute. reflexivity. }
  apply Forall_forall. intros r Hr. rewrite forallb_forall in C. specialize (C r Hr).
  apply andb_prop in C as [C1 C2]. apply Z.ltb_lt in C1. split; [exact C1|].
  unfold zdisjoint. cbn [fst snd]. apply orb_true_iff in C2 as [C2 | C2]; [left | right]; apply Z.leb_le; exact C2.
- (* an owned static's byte in a read-only range is pinned to its image byte by one of TA's constant cells *)
  intros ly a Hcr Hown.
  assert (C : pst_allb (fun x => if s7bw_in_b (PRW_put_string_e.ps_snp_cr (PA := PI_prog_A)) x
                                 then existsb (s7bw_pin_c ASEGS x) (as_const TA ly) else true)
                (as_owned_static TA) = true).
  { unfold PRW_put_string_e.ps_snp_cr. cbn [pa_segs PI_prog_A as_const as_owned_static AD2l.TfibB].
    vm_compute. reflexivity. }
  pose proof (s7bw_allb _ _ a C Hown) as H. cbv beta in H. rewrite (s7bw_in_b_of _ a Hcr) in H.
  exact (s7bw_pin_sound ASEGS a _ H).
- (* the image's last segment ends in IMG_TOP's page *)
  assert (C : existsb (fun sg => IMG_TOP - 4096 <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) ASEGS = true)
    by (vm_compute; reflexivity).
  apply existsb_exists in C as (sg & Hsg & C). apply Z.ltb_lt in C. exists sg. split; [exact Hsg | exact C].
Qed.

(* the closed side conditions of a Theorem Labs lane's snprintf_xrom_A (lib/A/PSnpSnpRoot.v:140-141, blob 4edc9be9a050 at the cut:
   0x10000 <= lo, got <= AE2p.A_GOT_canary, 8160 <= K, img_lo <= 65536, 0x600000 <= img_hi) at the parameters of
   PRW_put_string_e.v's SNP: lo := IMG_LO, got := gcan := GCAN (AE2p.A_GOT_canary's value, so got <= A_GOT_canary
   holds with equality), K := STK_RT_PRINTF, img_lo := IMG_LO, img_hi := IMG_TOP; GCAN / CAN are the values of record
   (PSnpI.v:122-123 there), and the row's pc PSnpI.PC_snprintf (PSnpI.v:71 there) is SIGMA AS___wrap_snprintf *)
Lemma s7bw_snp_row_side : 0x10000 <= IMG_LO /\ 8160 <= STK_RT_PRINTF /\ IMG_LO <= 65536 /\ 0x600000 <= IMG_TOP /\
  GCAN = 0xa2c98 /\ CAN = 0x5fdf30 /\ SIGMA AS___wrap_snprintf = 0x42d58.
Proof.
rewrite IMG_LO_val, IMG_TOP_val. unfold STK_RT_PRINTF, ESTACK.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
cbn [pa_sigma PI_prog_A]. vm_compute. reflexivity.
Qed.

(* ---- write_value (PRW_write_value.v) ---- *)

(* Hent : SIGMA AS_write_value = BASE + AF_write_value *)
Lemma s7bw_wv_ent : SIGMA AS_write_value = BASE + PRW_write_value.AF_write_value.
Proof. cbn [pa_sigma pa_val PI_prog_A]. vm_compute. reflexivity. Qed.

(* Hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i) *)
Lemma s7bw_wv_obj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
Proof. intros i Hi. destruct (s7bw_obj i Hi) as (H0 & H12 & _). exact (conj H0 H12). Qed.

End w.

Locate Img0.rsegs.
Locate rsegs.
