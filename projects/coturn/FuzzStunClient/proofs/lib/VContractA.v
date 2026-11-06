(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VAbs VStepMem VCert VContract VState2 VStepMem2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Inductive ca_res : Type :=
| CA_ok (l : list (vstate2 * absval))     (* [comment removed for export] *)
| CA_dead
| CA_fail (msg : string).

Definition ca_ok1 (A : vstate2) (v : absval) : ca_res := CA_ok [(A, v)].

Definition lift_cresA (A : vstate2) (r : cres) : ca_res :=
  match r with
  | CROk A1 v => ca_ok1 (with_v1 A A1) v
  | CRDead => CA_dead
  | CRFail m => CA_fail m
  end.

(* [comment removed for export] *)
Definition K_stack_malloc : Z := 208.
Definition K_set_shadow : Z := 0.
Definition K_asan_memset : Z := 2208.
Definition K_asan_memcpy : Z := 2224.
Definition K_i_strlen : Z := 2224.
Definition K_i_strcmp : Z := 2272.   (* [comment removed for export] *)
Definition K_i_strncpy : Z := 4416.
Definition K_i_bcmp : Z := 4560.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition granule_ok (k top : Z) : bool := Z.eqb k 0 || (Z.leb top k && Z.ltb k 8).

(* [comment removed for export] *)
Definition sh_byte (sh : vregion) (g : Z) : option Z :=
  match sh_cover (vr_cells sh) g with
  | Some (_, (_, Some e)) => if lin_is_const e then Some (Z.land (lc e) 255) else None
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint granules_okf (f : Z -> option Z) (g : Z) (k : nat) (alo ahi : Z) : bool :=
  match k with
  | O => true
  | S k' =>
      match f g with
      | Some b => granule_ok b (Z.min ahi (8 * g + 8) - 8 * g) && granules_okf f (g + 1) k' alo ahi
      | None => false
      end
  end.
Definition range_granules_okf (f : Z -> option Z) (alo ahi : Z) : bool :=
  if Z.leb ahi alo then true
  else let g0 := Z.div alo 8 in let g1 := Z.div (ahi - 1) 8 in
       granules_okf f g0 (Z.to_nat (g1 - g0 + 1)) alo ahi.
(* [comment removed for export] *)
Definition granules_ok (sh : vregion) : Z -> nat -> Z -> Z -> bool := granules_okf (sh_byte sh).

Fixpoint sh_drop_ended (m : cellmap) (o : Z) : cellmap :=
  match m with
  | [] => []
  | (k, (w, v)) :: t => if Z.leb (k + w) o then sh_drop_ended t o else m
  end.

Definition sh_cover_f (m : cellmap) (o : Z) : option (Z * (Z * absval)) :=
  find (fun e : Z * cell => match e with (k, (w, _)) => if Z.leb k o then Z.ltb o (k + w) else false end) m.

Lemma sh_cover_f_eq m o : sh_cover_f m o = sh_cover m o.
Proof.
  unfold sh_cover_f, sh_cover. induction m as [|[k [w v]] t IH]; [reflexivity|]. cbn [cm_overlapping find].
  destruct (Z.leb_spec k o) as [H1|H1]; destruct (Z.ltb_spec o (k + w)) as [H2|H2];
    destruct (Z.ltb_spec k (o + 1)) as [H3|H3]; try lia; cbn [andb find].
  all: first [ reflexivity | exact IH | (destruct (Z.leb_spec k o); [|lia]); (destruct (Z.ltb_spec o (k + w)); [|lia]); reflexivity ].
Qed.

Lemma sh_cover_f_drop m o g : o <= g -> sh_cover_f (sh_drop_ended m o) g = sh_cover_f m g.
Proof.
  intros Hog. unfold sh_cover_f. induction m as [|[k [w v]] t IH]; [reflexivity|]. cbn [sh_drop_ended].
  destruct (Z.leb_spec (k + w) o) as [H|H]; [|reflexivity].
  rewrite IH. cbn [find]. destruct (Z.leb k g); [|reflexivity]. destruct (Z.ltb_spec g (k + w)); [lia|reflexivity].
Qed.

Lemma sh_drop_ended_twice m o1 o2 : o1 <= o2 -> sh_drop_ended (sh_drop_ended m o1) o2 = sh_drop_ended m o2.
Proof.
  intros Ho. induction m as [|[k [w v]] t IH]; [reflexivity|]. cbn [sh_drop_ended].
  destruct (Z.leb_spec (k + w) o1) as [H|H]; [rewrite IH; cbn [sh_drop_ended]; destruct (Z.leb_spec (k + w) o2); [reflexivity|lia]|reflexivity].
Qed.

Definition sh_byte_w (cur : cellmap) (g : Z) : option Z :=
  match sh_cover_f cur g with
  | Some (_, (_, Some e)) => if lin_is_const e then Some (Z.land (lc e) 255) else None
  | _ => None
  end.

Fixpoint granules_okw (cur : cellmap) (g : Z) (k : nat) (alo ahi : Z) : bool :=
  match k with
  | O => true
  | S k' =>
      let cur' := sh_drop_ended cur g in
      match sh_byte_w cur' g with
      | Some b => if granule_ok b (Z.min ahi (8 * g + 8) - 8 * g) then granules_okw cur' (g + 1) k' alo ahi else false
      | None => false
      end
  end.

Lemma granules_okw_eq sh : forall k g cur alo ahi,
  (cur = vr_cells sh \/ exists o, o <= g /\ cur = sh_drop_ended (vr_cells sh) o) ->
  granules_okw cur g k alo ahi = granules_okf (sh_byte sh) g k alo ahi.
Proof.
  induction k as [|k IH]; intros g cur alo ahi Hc; [reflexivity|]. cbn [granules_okw granules_okf].
  assert (HB : sh_byte_w (sh_drop_ended cur g) g = sh_byte sh g).
  { unfold sh_byte_w, sh_byte. rewrite sh_cover_f_drop by lia.
    destruct Hc as [->|(o & Ho & ->)]; [|rewrite sh_cover_f_drop by exact Ho]; rewrite sh_cover_f_eq; reflexivity. }
  rewrite HB. destruct (sh_byte sh g) as [b|]; [|reflexivity].
  destruct (granule_ok b (Z.min ahi (8 * g + 8) - 8 * g)); cbn [andb]; [|reflexivity].
  apply IH. right. destruct Hc as [->|(o & Ho & ->)].
  - exists g. split; [lia|reflexivity].
  - exists g. split; [lia|]. apply sh_drop_ended_twice. exact Ho.
Qed.

(* [comment removed for export] *)
Definition zero_run_left (cur : cellmap) (g : Z) : option Z :=
  match cur with
  | (kk, (ww, Some e)) :: _ =>
      if lin_is_const e then
        if Z.eqb (Z.land (lc e) 255) 0 then
          if Z.leb kk g then (let n := kk + ww - g in if Z.ltb 0 n then Some n else None) else None
        else None
      else None
  | _ => None
  end.

Fixpoint granules_okr (cur : cellmap) (g rem : Z) (f : nat) (alo ahi : Z) : bool :=
  match f with
  | O => granules_okw cur g (Z.to_nat rem) alo ahi
  | S f' =>
      if Z.leb rem 0 then true else
      let cur' := sh_drop_ended cur g in
      match zero_run_left cur' g with
      | Some n => if Z.leb rem n then true else granules_okr cur' (g + n) (rem - n) f' alo ahi
      | None =>
          match sh_byte_w cur' g with
          | Some b => if granule_ok b (Z.min ahi (8 * g + 8) - 8 * g) then granules_okr cur' (g + 1) (rem - 1) f' alo ahi else false
          | None => false
          end
      end
  end.

Lemma sh_drop_ended_idem m o : sh_drop_ended (sh_drop_ended m o) o = sh_drop_ended m o.
Proof. apply sh_drop_ended_twice. lia. Qed.

Lemma granules_okw_drop cur g k alo ahi : granules_okw (sh_drop_ended cur g) g k alo ahi = granules_okw cur g k alo ahi.
Proof. destruct k as [|k]; [reflexivity|]. cbn [granules_okw]. rewrite sh_drop_ended_idem. reflexivity. Qed.

Lemma zero_run_skip cur kk ww e t alo ahi :
  cur = (kk, (ww, Some e)) :: t -> lin_is_const e = true -> Z.land (lc e) 255 = 0 ->
  forall (j : nat) g k', kk <= g -> g + Z.of_nat j <= kk + ww ->
  granules_okw cur g (j + k') alo ahi = granules_okw cur (g + Z.of_nat j) k' alo ahi.
Proof.
  intros -> EC EB. induction j as [|j IH]; intros g k' Hk Hj.
  - cbn [Nat.add Z.of_nat]. rewrite Z.add_0_r. reflexivity.
  - cbn [Nat.add granules_okw]. cbn [sh_drop_ended]. destruct (Z.leb_spec (kk + ww) g) as [H|H]; [lia|].
    unfold sh_byte_w, sh_cover_f. cbn [find]. destruct (Z.leb_spec kk g) as [H1|H1]; [|lia].
    destruct (Z.ltb_spec g (kk + ww)) as [H2|H2]; [|lia]. rewrite EC, EB.
    unfold granule_ok. cbn [Z.eqb orb]. rewrite IH by lia. f_equal. lia.
Qed.

Lemma granules_okr_eq : forall f cur g rem alo ahi,
  granules_okr cur g rem f alo ahi = granules_okw cur g (Z.to_nat rem) alo ahi.
Proof.
  induction f as [|f IH]; intros cur g rem alo ahi; cbn [granules_okr]; [reflexivity|].
  destruct (Z.leb_spec rem 0) as [Hr|Hr].
  { replace (Z.to_nat rem) with O by lia. reflexivity. }
  rewrite <- (granules_okw_drop cur g (Z.to_nat rem)).
  assert (IDEM : sh_drop_ended (sh_drop_ended cur g) g = sh_drop_ended cur g) by apply sh_drop_ended_idem.
  remember (sh_drop_ended cur g) as cur' eqn:EC0. clear EC0.
  destruct (zero_run_left cur' g) as [n|] eqn:ZR.
  - unfold zero_run_left in ZR. destruct cur' as [|[kk [ww [e|]]] t]; try discriminate.
    destruct (lin_is_const e) eqn:EC; [|discriminate]. destruct (Z.eqb_spec (Z.land (lc e) 255) 0) as [EB|]; [|discriminate].
    destruct (Z.leb_spec kk g) as [Hk|]; [|discriminate]. cbv zeta in ZR.
    destruct (Z.ltb_spec 0 (kk + ww - g)) as [Hn|]; [|discriminate]. injection ZR as <-.
    destruct (Z.leb_spec rem (kk + ww - g)) as [Hle|Hgt].
    + replace (Z.to_nat rem) with (Z.to_nat rem + 0)%nat by lia.
      pose proof (zero_run_skip ((kk, (ww, Some e)) :: t) kk ww e t alo ahi eq_refl EC EB (Z.to_nat rem) g O Hk ltac:(lia)) as SK.
      symmetry. etransitivity; [exact SK|]. reflexivity.
    + rewrite IH.
      replace (Z.to_nat rem) with (Z.to_nat (kk + ww - g) + Z.to_nat (rem - (kk + ww - g)))%nat by lia.
      pose proof (zero_run_skip ((kk, (ww, Some e)) :: t) kk ww e t alo ahi eq_refl EC EB (Z.to_nat (kk + ww - g)) g
                    (Z.to_nat (rem - (kk + ww - g))) Hk ltac:(lia)) as SK.
      rewrite Z2Nat.id in SK by lia. symmetry. exact SK.
  - replace (Z.to_nat rem) with (S (Z.to_nat (rem - 1))) by lia.
    cbn [granules_okw]. rewrite IDEM.
    destruct (sh_byte_w cur' g) as [b|]; [|reflexivity].
    destruct (granule_ok b (Z.min ahi (8 * g + 8) - 8 * g)); [|reflexivity]. apply IH.
Qed.

Definition range_granules_ok (sh : vregion) (alo ahi : Z) : bool :=
  if Z.leb ahi alo then true
  else let g0 := Z.div alo 8 in let g1 := Z.div (ahi - 1) 8 in
       granules_okr (vr_cells sh) g0 (g1 - g0 + 1) (List.length (vr_cells sh) + List.length (vr_cells sh) + 8) alo ahi.

Lemma range_granules_ok_eq sh alo ahi : range_granules_ok sh alo ahi = range_granules_okf (sh_byte sh) alo ahi.
Proof.
  unfold range_granules_ok, range_granules_okf. destruct (Z.leb ahi alo); [reflexivity|].
  cbv zeta. rewrite granules_okr_eq. apply granules_okw_eq. left; reflexivity.
Qed.

(* [comment removed for export] *)
Definition img_sh_byte (P : vparams2) (g : Z) : option Z :=
  match krun_get (vp_kruns P) (vp_shoff P + g) with Some b => Some (Z.land b 255) | None => None end.
(* [comment removed for export] *)
Definition kruns_cover (P : vparams2) (lo hi : Z) : bool :=
  forallb (fun i => match krun_get (vp_kruns P) (lo + Z.of_nat i) with Some _ => true | None => false end)
          (seq 0 (Z.to_nat (hi - lo))).
Definition LOW_MEM_END : Z := 0x7fff7fff.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition img_addressable (P : vparams2) (alo ahi : Z) : bool :=
  Z.leb 0 alo && Z.ltb alo ahi && Z.leb ahi LOW_MEM_END
  && range_granules_okf (img_sh_byte P) alo ahi
  && kruns_cover P ((vp_shoff P + alo / 8) / 8 * 8) ((vp_shoff P + (ahi - 1) / 8) / 8 * 8 + 8).

(* [comment removed for export] *)
Definition stack_addressable (A : vstate2) (lo hi : Z) : bool :=
  match rgn_shadow_of (vs_rgn A) SP0 with
  | None => false
  | Some sh =>
      match pm_get SP0 (scong (vs_store (v1 A))) with
      | Some (m, r) => negb (Z.eqb m 0) && Z.eqb (m mod 8) 0 && Z.eqb (r mod 8) 0 && range_granules_ok sh lo hi
      | None => false
      end
  end.

(* [comment removed for export] *)
Definition rgn_residue (A : vstate2) (r : vregion) : option Z :=
  match vr_kind r with
  | RK_fake _ _ => Some 0
  | RK_arg => if Z.eqb (vr_disp r) 0 then base_res8 A (vr_base r) else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition rgn_addressable (A : vstate2) (r : vregion) (lo hi : Z) : bool :=
  match rgn_shadow_of (vs_rgn A) (vr_base r), rgn_residue A r with
  | Some sh, Some rB => range_granules_ok sh (lo + rB) (hi + rB)
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zone_ok1d (P : vparams2) (b : sym) (d : Z) (z : fzone) : bool :=
  Pos.eqb (fz_base z) b && Z.eqb (fz_disp z) d && lin_is_const (fz_lo z) && lin_is_const (fz_hi z).
(* [comment removed for export] *)
Fixpoint zone_coverd (P : vparams2) (b : sym) (d : Z) (glo ghi : Z) (fuel : nat) : bool :=
  if Z.leb ghi glo then true else
  match fuel with
  | O => false
  | S f => (fix scan (l : list fzone) : bool :=
              match l with
              | [] => false
              | z :: t => if zone_ok1d P b d z && Z.leb (lc (fz_lo z)) glo && Z.ltb glo (lc (fz_hi z))
                          then (if zone_coverd P b d (lc (fz_hi z)) ghi f then true else scan t)
                          else scan t
              end) (vp_fzones P)
  end.
(* [comment removed for export] *)
Definition zone_hasd (P : vparams2) (b : sym) (d : Z) (lo hi : Z) : bool :=
  zone_coverd P b d lo hi (S (List.length (vp_fzones P))).
(* [comment removed for export] *)
Definition zone_ok1 (P : vparams2) (b : sym) (z : fzone) : bool := zone_ok1d P b (vp_shoff P) z.
Definition zone_cover (P : vparams2) (b : sym) (glo ghi : Z) (fuel : nat) : bool := zone_coverd P b (vp_shoff P) glo ghi fuel.
Definition zone_has (P : vparams2) (b : sym) (glo ghi : Z) : bool := zone_hasd P b (vp_shoff P) glo ghi.
(* [comment removed for export] *)
Definition stack_shadow_words_ok (P : vparams2) (lo hi : Z) : bool :=
  zone_has P SP8 (Z.div lo 8 - 7) (Z.div (hi - 1) 8 + 8).
(* [comment removed for export] *)
Definition FS_FRAMES_G : Z := 4608.        (* [comment removed for export] *)
Definition FS_FRAMES_GLEN : Z := 655360.   (* [comment removed for export] *)
Definition frames_shadow_zone_ok (P : vparams2) : bool := zone_has P FS8 FS_FRAMES_G (FS_FRAMES_G + FS_FRAMES_GLEN).
(* [comment removed for export] *)
Definition FS_FRAMES_SZ : Z := 5242880.    (* [comment removed for export] *)
Definition frames_zone_ok (P : vparams2) : bool := zone_hasd P FSB 0 36864 (36864 + FS_FRAMES_SZ).

(* [comment removed for export] *)
Definition sp_off (A : vstate2) : option Z :=
  match get_reg2 A 2 with
  | Some e => match lt e with
              | [(s, k)] => if Pos.eqb s SP0 && Z.eqb k 1 then Some (lc e) else None
              | _ => None
              end
  | None => None
  end.

(* [comment removed for export] *)
Definition above_sp (A : vstate2) (lo hi : Z) : bool :=
  Z.leb hi lo || match sp_off A with Some spoff => Z.leb spoff lo | None => false end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive rresA : Type :=
| RA_rgn (r : vregion) (lo hi : Z)        (* [comment removed for export] *)
| RA_v1 (rr : rres)                       (* [comment removed for export] *)
| RA_dead
| RA_fail (msg : string).

(* [comment removed for export] *)
Definition range_check (P : vparams2) (A : vstate2) (base n : lin) (store : bool) : rresA :=
  let A1 := v1 A in
  match base_syms A base with
  | [B] =>
      if negb (Z.eqb (lcoef base B) 1) || negb (Z.eqb (lcoef base SP0) 0 && Z.eqb (lcoef base DATA) 0)
      then RA_fail "range: mixed region pointer" else
      match rgn_get (vs_rgn A) B with
      | None => RA_fail "range: internal (base without region)"
      | Some r =>
          match vr_kind r with
          | RK_fake _ _ | RK_arg =>
              let off := laddc (lsub base (lsym B)) (- vr_disp r) in
              let fin := ladd off n in
              if dead_lin A1 off || dead_lin A1 fin then RA_dead else
              match lo_of A1 off, hi_of A1 fin with
              | Some lo, Some hi =>
                  if Z.ltb lo (vr_lo r) || Z.ltb (vr_hi r) hi then RA_fail "range: outside the region's extent"
                  else if store && negb (Z.leb hi lo) && negb (in_ranges (vr_w r) lo (hi - lo)) then RA_fail "range: store range not writable in the region"
                  else if negb (rgn_addressable A r lo hi) then RA_fail "range: region bytes not addressable (shadow)"
                  else if negb (frames_shadow_zone_ok P) then RA_fail "range: FakeStack frames shadow zone (FS8) missing"
                  else RA_rgn r lo hi
              | _, _ => RA_fail "range: unbounded region offsets"
              end
          | _ => RA_fail "range: pointer into a shadow/flag/hint region"
          end
      end
  | [] =>
      if store then
        match stack_range (p1 P) A1 base n true with
        | RR_stack off lo hi => if negb (above_sp A lo hi) then RA_fail "range: stack range not above the callee frame (sp)"
                                else if negb (stack_addressable A lo hi) then RA_fail "range: stack bytes not addressable (shadow)"
                                else if negb (stack_shadow_words_ok P lo hi) then RA_fail "range: stack shadow words not in the SP8 zone"
                                else RA_v1 (RR_stack off lo hi)
        | RR_dead => RA_dead
        | RR_fail m => RA_fail m
        | _ => RA_fail "range: store into Data/image"
        end
      else
        match readable_range (p1 P) A1 base n with
        | RR_stack off lo hi => if negb (above_sp A lo hi) then RA_fail "range: stack range not above the callee frame (sp)"
                                else if negb (stack_addressable A lo hi) then RA_fail "range: stack bytes not addressable (shadow)"
                                else if negb (stack_shadow_words_ok P lo hi) then RA_fail "range: stack shadow words not in the SP8 zone"
                                else RA_v1 (RR_stack off lo hi)
        | RR_data off => RA_v1 (RR_data off)    (* [comment removed for export] *)
        | RR_img lo hi => RA_v1 (RR_img lo hi)    (* [comment removed for export] *)
        | RR_dead => RA_dead
        | RR_fail m => RA_fail m
        end
  | _ => RA_fail "range: two region bases"
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition FS_FRAMES_OFF : Z := 4096 + 32768.
Definition FS_LOG : Z := 20.

(* [comment removed for export] *)
Definition rgn_of_kill (l : list vregion) (b : sym) (lo hi : Z) : list vregion :=
  match rgn_get l b with
  | Some r => rgn_upd l (set_rnul (set_cells r (cm_kill (vr_cells r) lo hi))
                                  (List.filter (fun f : Z * Z => Z.ltb (snd f) lo || Z.leb hi (fst f)) (vr_nul r)))
  | None => l
  end.

Definition ca_stack_malloc (P : vparams2) (tp : Z) (A : vstate2) (spoff cid : Z) : ca_res :=
  let size := Z.shiftl 64 cid in
  if negb (asan_mode P) then CA_fail "stack_malloc: not an ASan image" else
  if negb (Z.leb 0 cid && Z.leb cid 4) then CA_fail "stack_malloc: class not in 0..4" else
  (* [comment removed for export] *)
  if negb (match get_reg2 A 4 with Some e => lin_eqb e (lconst tp) | None => false end) then CA_fail "stack_malloc: x4 is not the thread-pointer constant" else
  match get_reg2 A A0r with
  | Some ea =>
      if negb (lin_is_const ea && Z.ltb 0 (lc ea) && Z.leb (lc ea) size) then CA_fail "stack_malloc: size not a constant in (0, 64<<cid]" else
      match rgn_get (vs_rgn A) FSB with
      | None => CA_fail "stack_malloc: no FakeStack hint region"
      | Some fsr =>
      if negb (match vr_kind fsr with RK_fs => true | _ => false end) then CA_fail "stack_malloc: FSB region is not the hint region" else
      if Z.leb 8 (Z.of_nat (List.length (vs_live A))) then CA_fail "stack_malloc: too many live fake frames" else
      if negb (Z.leb (vp_fdepth P + Z.of_nat (List.length (vs_live A)) + 1) (Z.shiftl 1 (14 - cid)))
      then CA_fail "stack_malloc: live-frame budget exceeded (fdepth)" else
      (* [comment removed for export] *)
      let A1 := v1 A in
      let FF := vs_next A1 in let FL := Pos.succ FF in let F8 := Pos.succ FL in
      let A2 := set_next A1 (Pos.succ F8) in
      let lo_off := FS_FRAMES_OFF + Z.shiftl cid FS_LOG in
      let hi_off := FS_FRAMES_OFF + Z.shiftl (cid + 1) FS_LOG - size in
      let '(ok1, A3) := aassume2 A2 (lsub (laddc (lsym FSB) lo_off) (lsym FF))          (* [comment removed for export] *)
                                    (laddc (lsub (lsym FF) (lsym FSB)) (- hi_off)) in   (* [comment removed for export] *)
      let '(ok2, A4) := ameet_cong A3 FF size 0 in                                        (* [comment removed for export] *)
      let '(ok3, A5) := aassume2 A4 (lsub (laddc (lsym FSB) 4096) (lsym FL))               (* [comment removed for export] *)
                                    (laddc (lsub (lsym FL) (lsym FSB)) (- (4096 + 32768 - 1))) in
      let '(ok4, A6) := aassume2 A5 (lsub (lscale 8 (lsym F8)) (lsym FF))                  (* [comment removed for export] *)
                                    (lsub (lsym FF) (lscale 8 (lsym F8))) in
      if negb (ok1 && ok2 && ok3 && ok4) then CA_fail "stack_malloc: frame facts infeasible" else
      let spc := match get_reg2 A 2 with Some e => [(24, (8, Some e))] | None => [] end in
      let fake := mkVR FF 0 (RK_fake cid FL) 0 size [(0, size)] (spc ++ [(size - 8, (8, Some (lsym FL)))])%list [] (Some F8) in
      let shad := mkVR F8 (vp_shoff P) (RK_shadow FF) 0 (size / 8) [(0, size / 8)] [(0, (size / 8, Some (lconst 0)))] [] None in
      let flag := mkVR FL 0 (RK_flag FF) 0 1 [(0, 1)] [] [] None in
      let rg := flag :: shad :: fake :: rgn_of_kill (vs_rgn A) FSB (8 * cid) (8 * cid + 8) in
      ca_ok1 (mkVS2 A6 rg (FF :: vs_live A) (pm_set F8 (lsym FF, 8) (vs_divdef A)) []) (Some (lsym FF))
      end
  | None => CA_fail "stack_malloc: size Top"
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ca_set_shadow (P : vparams2) (A : vstate2) (b : Z) : ca_res :=
  match get_reg2 A A0r, get_reg2 A A1r with
  | Some ea, Some en =>
      if negb (lin_is_const en && Z.ltb 0 (lc en) && Z.leb (lc en) (2 ^ 18)) then CA_fail "set_shadow: length not a constant in (0, 2^18]" else
      let n := lc en in
      match classify2 A ea n true with
      | Some (C2Rgn r off lo hi) =>
          match vr_kind r with
          | RK_shadow s =>
              if Pos.eqb s DATA then CA_fail "set_shadow: Data shadow" else
              if negb (Z.eqb lo hi) then CA_fail "set_shadow: inexact shadow offset" else
              let r' := set_rnul (set_cells r (sh_write (vr_cells r) lo n (Some (lconst (Z.land b 255))))) [] in
              ca_ok1 (set_rgn A (rgn_upd (vs_rgn A) r')) (Some ea)
          | _ => CA_fail "set_shadow: target is not a shadow region"
          end
      | Some C2Dead => CA_dead
      | Some (C2Fail m) => CA_fail ("set_shadow: " ++ m)
      | None => CA_fail "set_shadow: target is not a region address"
      end
  | _, _ => CA_fail "set_shadow: Top argument"
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint zero_cells8 (m : cellmap) (o : Z) (k : nat) : cellmap :=
  match k with O => m | S k' => zero_cells8 (cm_set m o (8, Some (lconst 0))) (o + 8) k' end.
Fixpoint zero_cells1 (m : cellmap) (o : Z) (k : nat) : cellmap :=
  match k with O => m | S k' => zero_cells1 (cm_set m o (1, Some (lconst 0))) (o + 1) k' end.

(* [comment removed for export] *)
Definition rgn_havoc (r : vregion) (lo hi : Z) (zero ends : bool) : vregion :=
  let m := cm_kill (vr_cells r) lo hi in
  let m' := if zero then
              let k := hi - lo in
              let q := Z.to_nat (k / 8) in let rr := Z.to_nat (k mod 8) in
              zero_cells1 (zero_cells8 m lo q) (lo + 8 * Z.of_nat q) rr
            else m in
  let nul := List.filter (fun f : Z * Z => Z.ltb (snd f) lo || Z.leb hi (fst f)) (vr_nul r) in
  let nul' := if ends then (lo, lo) :: (hi - 1, hi - 1) :: nul else nul in
  set_rnul (set_cells r m') nul'.

(* [comment removed for export] *)
Definition rgn_store_commit (A : vstate2) (r' : vregion) : vstate2 :=
  let l1 := rgn_upd (vs_rgn A) r' in
  set_rgn A (match vr_kind r' with RK_arg => havoc_other_args l1 (vr_base r') | _ => l1 end).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ca_asan_memset (P : vparams2) (A : vstate2) : ca_res :=
  let A1 := v1 A in
  let d := get_reg2 A A0r in let c := get_reg2 A A1r in let n := get_reg2 A A2r in
  match nonneg_len A1 n MAXLEN with
  | NR_dead => CA_dead
  | NR_fail m => CA_fail ("asan_memset n: " ++ m)
  | NR_ok nlo _ =>
  match d with
  | None => CA_fail "asan_memset: dst Top"
  | Some de =>
      let ne := lin_of n in
      match range_check P A de ne true with
      | RA_dead => CA_dead
      | RA_fail m => CA_fail ("asan_memset dst: " ++ m)
      | RA_rgn r lo hi =>
          if negb (is_zero_byte A1 c) then CA_fail "asan_memset: fill value not provably 0" else
          if negb (Z.ltb 0 nlo) then CA_fail "asan_memset: region range possibly empty (n = 0 not excluded) [P]" else
          let ends := lin_is_const ne && Z.ltb 0 (lc ne) && Z.eqb (lo + lc ne) hi in
          let exact := ends && Z.leb (lc ne) MEMSET_TRACK_MAX in
          ca_ok1 (rgn_store_commit A (rgn_havoc r lo hi exact ends)) d
      | RA_v1 _ => lift_cresA A (c_memset (p1 P) A1)
      end
  end end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ca_asan_memcpy (P : vparams2) (A : vstate2) : ca_res :=
  let A1 := v1 A in
  let d := get_reg2 A A0r in let s := get_reg2 A A1r in let n := get_reg2 A A2r in
  match nonneg_len A1 n MAXLEN with
  | NR_dead => CA_dead
  | NR_fail m => CA_fail ("asan_memcpy n: " ++ m)
  | NR_ok nlo _ =>
  match d, s with
  | Some de, Some se =>
      let ne := lin_of n in
      match range_check P A se ne false with
      | RA_dead => CA_dead
      | RA_fail m => CA_fail ("asan_memcpy src: " ++ m)
      | RA_v1 (RR_img _ _) => CA_fail "asan_memcpy: image source (no shadow facts) [P]"
      | sr =>
      match range_check P A de ne true with
      | RA_dead => CA_dead
      | RA_fail m => CA_fail ("asan_memcpy dst: " ++ m)
      | RA_rgn r lo hi =>
          let alias :=
            match sr with
            | RA_rgn r2 _ _ =>
                if Pos.eqb (vr_base r2) (vr_base r) then negb (disjoint_ranges A1 de se ne)
                else match vr_kind r, vr_kind r2 with RK_arg, RK_arg => true | _, _ => false end
            | _ => false
            end in
          if alias then CA_fail "asan_memcpy: source and destination ranges not provably disjoint (same region / two argument regions)" else
          if negb (Z.ltb 0 nlo) then CA_fail "asan_memcpy: region range possibly empty (n = 0 not excluded) [P]"
          else ca_ok1 (rgn_store_commit A (rgn_havoc r lo hi false false)) d
      | RA_v1 (RR_stack _ lo hi) =>
          match sr with
          | RA_v1 (RR_stack _ _ _) =>
              if negb (disjoint_ranges A1 de se ne) then CA_fail "asan_memcpy: stack ranges not provably disjoint"
              else lift_cresA A (c_memcpy (p1 P) A1)
          | RA_v1 _ => lift_cresA A (c_memcpy (p1 P) A1)
          | _ => (* [comment removed for export] *)
              let B1 := set_slots A1 (cm_kill (vs_slots A1) lo hi) in
              let B2 := kill_nul B1 lo (hi - 1) None in
              ca_ok1 (with_v1 A B2) d
          end
      | RA_v1 _ => CA_fail "asan_memcpy dst: unexpected class"
      end end
  | None, _ => CA_fail "asan_memcpy: dst Top"
  | _, None => CA_fail "asan_memcpy: src Top"
  end end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive oc_res : Type := OC_ok | OC_dead | OC_fail (msg : string).
Definition opnd_check (P : vparams2) (A : vstate2) (pe ne : lin) (nhi : Z) : oc_res :=
  match range_check P A pe ne false with
  | RA_dead => OC_dead
  | RA_fail m => OC_fail m
  | RA_rgn _ _ _ => OC_ok
  | RA_v1 (RR_stack _ _ _) => OC_ok
  | RA_v1 (RR_data _) => if Z.leb 8 (vp_datal P) then OC_ok else OC_fail "operand in the Data block but vp_datal < 8"
  | RA_v1 (RR_img _ _) =>
      if Z.eqb nhi 0 then OC_ok
      else if lin_is_const pe && img_addressable P (lc pe) (lc pe + nhi) then OC_ok
      else OC_fail "image operand not addressable (globals shadow runs) or not a constant address"
  | RA_v1 _ => OC_fail "operand: unexpected class"
  end.

(* [comment removed for export] *)
Definition ca_i_bcmp (P : vparams2) (A : vstate2) : ca_res :=
  let A1 := v1 A in
  match nonneg_len A1 (get_reg2 A A2r) MAXLEN, get_reg2 A A0r, get_reg2 A A1r with
  | NR_dead, _, _ => CA_dead
  | NR_fail m, _, _ => CA_fail ("ic_bcmp n: " ++ m)
  | NR_ok _ nhi, Some ae, Some be =>
      let ne := lin_of (get_reg2 A A2r) in
      match opnd_check P A ae ne nhi, opnd_check P A be ne nhi with
      | OC_dead, _ | _, OC_dead => CA_dead
      | OC_fail m, _ => CA_fail ("ic_bcmp a: " ++ m)
      | _, OC_fail m => CA_fail ("ic_bcmp b: " ++ m)
      | OC_ok, OC_ok => let '(v, B1) := afresh A1 (Some (-255), Some 255) in ca_ok1 (with_v1 A B1) v
      end
  | _, _, _ => CA_fail "ic_bcmp: pointer Top"
  end.

(* [comment removed for export] *)
Definition ptr_candidates (A : vstate) (p : lin) : option (list Z) :=
  if lin_is_const p then Some [lc p]
  else match lin_single p with
       | Some (s, k) =>
           if negb (Z.eqb k 1) then None else
           match pm_get s (vs_valset A) with
           | Some vs => if Nat.leb (List.length vs) 64 then Some (map (fun v => lc p + v) vs) else None
           | None => None
           end
       | None => None
       end.

(* [comment removed for export] *)
Fixpoint rodata_cands (P : vparams) (extra : Z) (chk : Z -> Z -> bool) (l : list Z) : option (Z * Z) :=
  match l with
  | [] => None
  | a :: t =>
      match rodata_cstr_len P (Some (lconst a)) with
      | Some k =>
          if negb (in_ranges (vp_segs P) a (k + extra)) || negb (chk a k) then None else
          match t with
          | [] => Some (k, k)
          | _ => match rodata_cands P extra chk t with
                 | Some (lo, hi) => Some (Z.min k lo, Z.max k hi)
                 | None => None
                 end
          end
      | None => None
      end
  end.
(* [comment removed for export] *)
Definition img_str_ok (P : vparams2) (a k : Z) : bool := img_addressable P a (a + k + 1).

(* [comment removed for export] *)
Definition rgn_nul_bound (r : vregion) (phi : Z) : option Z :=
  min_opt (List.map snd (List.filter (fun f : Z * Z => Z.leb phi (fst f)) (vr_nul r))
           ++ slot_zero_bytes (vr_cells r) phi)%list.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ca_i_strlen_cands (P : vparams2) (A : vstate2) (l : list Z) : ca_res :=
  match rodata_cands (p1 P) 8 (img_str_ok P) l with
  | Some (klo, khi) => let '(v, B1) := afresh (v1 A) (Some klo, Some khi) in ca_ok1 (with_v1 A B1) v
  | None => CA_fail "ic_strlen: a candidate is not a readable, addressable rodata string"
  end.
(* [comment removed for export] *)
Definition ca_i_strlen_v1 (P : vparams2) (A : vstate2) (pe : lin) : ca_res :=
  let A1 := v1 A in
  match c_strlen (p1 P) A1 with
  | CRDead => CA_dead
  | CRFail m => CA_fail ("ic_strlen: " ++ m)
  | CROk B v =>
      match rodata_cstr_len (p1 P) (Some pe) with
      | Some k => if img_str_ok P (lc pe) k then ca_ok1 (with_v1 A B) v
                  else CA_fail "ic_strlen: rodata string not addressable (globals shadow runs)"
      | None =>
          let off := lsub pe (lsym SP0) in
          match lo_of A1 off, hi_of A1 off with
          | Some plo, Some phi =>
              match find_nul_bound A1 phi with
              | Some H => if negb (above_sp A plo (H + 1)) then CA_fail "ic_strlen: stack string not above the callee frame (sp)"
                          else if negb (stack_addressable A plo (H + 1)) then CA_fail "ic_strlen: stack string not addressable (shadow)"
                          else if negb (stack_shadow_words_ok P plo (H + 1)) then CA_fail "ic_strlen: stack string shadow words not in the SP8 zone"
                          else ca_ok1 (with_v1 A B) v
              | None => CA_fail "ic_strlen: no NUL bound"
              end
          | _, _ => CA_fail "ic_strlen: unbounded pointer"
          end
      end
  end.
(* [comment removed for export] *)
Definition rk_app (k : rkind) : bool := match k with RK_fake _ _ | RK_arg => true | _ => false end.
(* [comment removed for export] *)
Definition ca_i_strlen_rgn (P : vparams2) (A : vstate2) (pe : lin) (B : sym) : ca_res :=
  let A1 := v1 A in
  if negb (Z.eqb (lcoef pe B) 1) || negb (Z.eqb (lcoef pe SP0) 0 && Z.eqb (lcoef pe DATA) 0) then CA_fail "ic_strlen: mixed region pointer" else
  match rgn_get (vs_rgn A) B with
  | None => CA_fail "ic_strlen: internal"
  | Some r =>
      if negb (rk_app (vr_kind r)) then CA_fail "ic_strlen: pointer into a shadow/flag/hint region" else
      let off := laddc (lsub pe (lsym B)) (- vr_disp r) in
      if dead_lin A1 off then CA_dead else
      match lo_of A1 off, hi_of A1 off with
      | Some plo, Some phi =>
          match rgn_nul_bound r phi with
          | None => CA_fail "ic_strlen: no NUL known in the region at/after the string"
          | Some H =>
              if Z.ltb plo (vr_lo r) || Z.ltb (vr_hi r) (H + 1) then CA_fail "ic_strlen: string range outside the region" else
              if negb (rgn_addressable A r plo (H + 1)) then CA_fail "ic_strlen: region string not addressable (shadow)" else
              if negb (frames_shadow_zone_ok P && frames_zone_ok P) then CA_fail "ic_strlen: FakeStack frames zone (FSB) / frames shadow zone (FS8) missing" else
              let '(s, B1) := fresh_sym A1 in
              let B2 := asetbox B1 s (Some 0, Some (H - plo)) in
              if lin_is_const off then ca_ok1 (with_v1 A B2) (Some (lsym s))
              else match aassume B2 (laddc (ladd (lsym s) off) (- H)) with
                   | (true, B3) => ca_ok1 (with_v1 A B3) (Some (lsym s))
                   | (false, _) => CA_dead
                   end
          end
      | _, _ => CA_fail "ic_strlen: unbounded region pointer"
      end
  end.
Definition ca_i_strlen (P : vparams2) (A : vstate2) : ca_res :=
  match get_reg2 A A0r with
  | None => CA_fail "ic_strlen: pointer Top"
  | Some pe =>
      match base_syms A pe with
      | [] =>
          match ptr_candidates (v1 A) pe with
          | Some (_ :: _ :: _) as cl => match cl with Some l => ca_i_strlen_cands P A l | None => CA_fail "impossible" end
          | _ => ca_i_strlen_v1 P A pe
          end
      | [B] => ca_i_strlen_rgn P A pe B
      | _ => CA_fail "ic_strlen: two region bases"
      end
  end.

(* [comment removed for export] *)
Definition ca_i_strcmp (P : vparams2) (A : vstate2) : ca_res :=
  let A1 := v1 A in
  match get_reg2 A A0r, get_reg2 A A1r with
  | Some ae, Some be =>
      match rodata_cstr_len (p1 P) (Some be) with
      | None => CA_fail "ic_strcmp: second argument is not a rodata constant string"
      | Some kb =>
          if negb (in_ranges (vp_segs (p1 P)) (lc be) (kb + 1)) then CA_fail "ic_strcmp: rodata string not readable" else
          if negb (img_str_ok P (lc be) kb) then CA_fail "ic_strcmp: rodata string not addressable (globals shadow runs)" else
          match range_check P A ae (lconst (kb + 1)) false with
          | RA_dead => CA_dead
          | RA_fail m => CA_fail ("ic_strcmp a: " ++ m)
          | RA_v1 (RR_data _) => CA_fail "ic_strcmp: first argument in the Data block [P]"
          | RA_v1 (RR_img _ _) => CA_fail "ic_strcmp: first argument a rodata constant [P]"
          | _ => let '(v, B1) := afresh A1 (Some (-255), Some 255) in ca_ok1 (with_v1 A B1) v
          end
      end
  | _, _ => CA_fail "ic_strcmp: pointer Top"
  end.

(* [comment removed for export] *)
Definition isn_src_check (P : vparams2) (A : vstate2) (se : lin) (nlo : Z) : option string :=
  let A1 := v1 A in
  match base_syms A se with
  | [] =>
      match ptr_candidates A1 se with
      | Some l =>
          match rodata_cands (p1 P) 8 (fun a k => img_str_ok P a k && Z.leb (k + 8) nlo && Z.ltb 0 a) l with
          | Some _ => None
          | None => Some "ic_strncpy: a source candidate is not an addressable rodata string with NUL index + 8 <= n"%string
          end
      | None =>
          if negb (is_sp_rel se) then Some "ic_strncpy: source neither constant nor stack-relative"%string else
          let off := lsub se (lsym SP0) in
          if dead_lin A1 off then Some "dead"%string else
          match lo_of A1 off, hi_of A1 off with
          | Some plo, Some phi =>
              match find_nul_bound A1 phi with
              | None => Some "ic_strncpy: no NUL known at/after the stack source"%string
              | Some H =>
                  if Z.ltb 0 (H + 8) then Some "ic_strncpy: source scan may reach sp0"%string else
                  if Z.ltb plo (- vp_frame (p1 P)) then Some "ic_strncpy: source below the frame window"%string else
                  if negb (above_sp A plo (H + 1)) then Some "ic_strncpy: stack source not above the callee frame (sp)"%string else
                  if negb (stack_addressable A plo (H + 1)) then Some "ic_strncpy: stack source not addressable (shadow)"%string else
                  if negb (stack_shadow_words_ok P plo (H + 1)) then Some "ic_strncpy: stack source shadow words not in the SP8 zone"%string else
                  if negb (Z.leb (H - plo + 8) nlo) then Some "ic_strncpy: n may be below the source NUL bound + 8"%string else
                  None
              end
          | _, _ => Some "ic_strncpy: unbounded stack source"%string
          end
      end
  | _ => Some "ic_strncpy: region source [P]"%string
  end.

Definition ca_i_strncpy (P : vparams2) (A : vstate2) (spoff : Z) : ca_res :=
  let A1 := v1 A in
  match get_reg2 A A0r, get_reg2 A A1r with
  | Some de, Some se =>
      match nonneg_len A1 (get_reg2 A A2r) MAXLEN with
      | NR_dead => CA_dead
      | NR_fail m => CA_fail ("ic_strncpy n: " ++ m)
      | NR_ok nlo nhi =>
          let ne := lin_of (get_reg2 A A2r) in
          match range_check P A de ne true with
          | RA_dead => CA_dead
          | RA_fail m => CA_fail ("ic_strncpy dst: " ++ m)
          | RA_v1 _ => CA_fail "ic_strncpy: own-stack destination not supported [P]"
          | RA_rgn r lo hi =>
              match isn_src_check P A se nlo with
              | Some m => if String.eqb m "dead" then CA_dead else CA_fail m
              | None => ca_ok1 (rgn_store_commit A (rgn_havoc r lo hi false false)) (Some de)
              end
          end
      end
  | _, _ => CA_fail "ic_strncpy: pointer Top"
  end.
