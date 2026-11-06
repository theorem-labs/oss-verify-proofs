(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMemSound VState2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition FS_SSL : Z := 20.
Definition FS_FLAGS : Z := 4096.                       (* [comment removed for export] *)
Definition FS_FRAMES : Z := 4096 + 32768.              (* [comment removed for export] *)
Definition fs_nframes (cid : Z) : Z := 2 ^ (14 - cid). (* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Fixpoint fs_flags_off_nat (n : nat) : Z :=              (* [comment removed for export] *)
  match n with O => 0 | S k => fs_flags_off_nat k + fs_nframes (Z.of_nat k) end.
Definition fs_flags_off (cid : Z) : Z := fs_flags_off_nat (Z.to_nat cid).
Definition frame_addr (fs cid pos : Z) : Z := fs + FS_FRAMES + cid * 2 ^ FS_SSL + fake_size cid * pos.
Definition flag_addr (fs cid pos : Z) : Z := fs + FS_FLAGS + fs_flags_off cid + pos.
Definition valid_slot (cp : Z * Z) : Prop := 0 <= fst cp <= 4 /\ 0 <= snd cp < fs_nframes (fst cp).
Definition FS_NCLASSES : Z := 5.                        (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Record venv2 := mkEnv2 {
  ev1 : venv ;
  e_fs : Z ;                    (* [comment removed for export] *)
  e_args : list Z ;             (* [comment removed for export] *)
  e_live : list (Z * Z)         (* [comment removed for export] *)
}.

Definition fix_val2 (E : venv2) (s : sym) : option Z :=
  match fix_val (ev1 E) s with
  | Some z => Some z
  | None =>
      if Pos.eqb s SP8 then Some (e_sp0 (ev1 E) / 8)
      else if Pos.eqb s DATA8 then Some (e_data (ev1 E) / 8)
      else if Pos.eqb s FSB then Some (e_fs E)
      else if Pos.eqb s FS8 then Some (e_fs E / 8)
      else if Pos.leb 19 s && Pos.leb s 26 then nth_error (e_args E) (Pos.to_nat s - 19)
      else None
  end.

Definition gamma_fix2 (E : venv2) (nu : val) : Prop := forall s z, fix_val2 E s = Some z -> nu s = z.

Lemma gamma_fix2_fix E nu : gamma_fix2 E nu -> gamma_fix (ev1 E) nu.
Proof. intros H s z Hs. apply H. unfold fix_val2. now rewrite Hs. Qed.

(* [comment removed for export] *)
Definition nuE (E : venv2) : val := fun s => match fix_val2 E s with Some z => z | None => 0 end.

(* [comment removed for export] *)
Definition FZONE_SYMS : list sym := [SP0; DATA; SIZE; TP; GP; SP8; DATA8; FSB; FS8].
Definition fsym_ok (s : sym) : bool := existsb (Pos.eqb s) FZONE_SYMS.
Definition fzone_syms_ok (z : fzone) : bool :=
  fsym_ok (fz_base z) && forallb fsym_ok (lsyms (fz_lo z)) && forallb fsym_ok (lsyms (fz_hi z)).

Lemma nuE_fsym E E' s :
  fsym_ok s = true ->
  e_sp0 (ev1 E) = e_sp0 (ev1 E') -> e_data (ev1 E) = e_data (ev1 E') -> e_size (ev1 E) = e_size (ev1 E') ->
  e_tp (ev1 E) = e_tp (ev1 E') -> e_gp (ev1 E) = e_gp (ev1 E') -> e_fs E = e_fs E' ->
  nuE E s = nuE E' s.
Proof.
  unfold fsym_ok, FZONE_SYMS. cbn [existsb]. rewrite !Bool.orb_true_iff, !Pos.eqb_eq.
  intros Hs H1 H2 H3 H4 H5 H6. unfold nuE, fix_val2, fix_val.
  destruct Hs as [->|[->|[->|[->|[->|[->|[->|[->|[->|F]]]]]]]]]; cbn; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithParams.
  Variable SEGS : list Segment.
  Variable P : vparams2.
  Variable E : venv2.
  Let P1 := p1 P.
  Let E1 := ev1 E.

  Definition zone_lo (z : fzone) : Z := fz_disp z + nuE E (fz_base z) + eval (nuE E) (fz_lo z).
  Definition zone_hi (z : fzone) : Z := fz_disp z + nuE E (fz_base z) + eval (nuE E) (fz_hi z).
  Definition zone_region (z : fzone) : word * Z := (wordZ (zone_lo z), zone_hi z - zone_lo z).

  Definition rw_zones : list fzone := List.filter fz_rw (vp_fzones P).
  Definition zregions : list (word * Z) := map zone_region rw_zones.

  Definition in_zone (a : Z) (z : fzone) : Prop := zone_lo z <= a < zone_hi z.
  Definition in_zoneb (a : Z) (z : fzone) : bool := Z.leb (zone_lo z) a && Z.ltb a (zone_hi z).
  Definition in_rw_zones (a : Z) : bool := existsb (in_zoneb a) rw_zones.

  Definition zpatch (mem0 mem : word -> option byte) : word -> option byte :=
    fun a => if in_rw_zones (bv_unsigned a) then mem a else mem0 a.

  (* [comment removed for export] *)
  Definition footprint2 : list (word * Z) := footprint P1 E1 ++ zregions.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition class_regions (fs cid : Z) (L : list (Z * Z)) : list (word * Z) :=
    flat_map (fun pos : Z =>
                if existsb (fun cp : Z * Z => Z.eqb (fst cp) cid && Z.eqb (snd cp) pos) L then []
                else [(wordZ (frame_addr fs cid pos), fake_size cid);
                      (wordZ (vp_shoff P + frame_addr fs cid pos / 8), fake_size cid / 8)])
             (map Z.of_nat (seq 0 (Z.to_nat (fs_nframes cid)))).
  Fixpoint classes_regions (fs : Z) (n : nat) (L : list (Z * Z)) : list (word * Z) :=
    match n with O => [] | S k => classes_regions fs k L ++ class_regions fs (Z.of_nat k) L end.

  Definition arg_regions : list (word * Z) :=
    map (fun w : Z * (Z * Z) => match w with (i, (lo, hi)) =>
           (wordZ (nth (Z.to_nat i) (e_args E) 0 + lo), hi - lo) end) (vp_wrgn P).

  (* [comment removed for export] *)
  Definition stack_shadow_regions : list (word * Z) :=
    map (fun r : Z * Z => (wordZ (vp_shoff P + (e_sp0 E1 + fst r) / 8), (snd r - fst r) / 8))
        (match vp_wstack P1 with [] => [] | r :: _ => [r] end).

  Definition fs_regions : list (word * Z) :=
    match vp_fs P with
    | None => []
    | Some _ => [(wordZ (e_fs E), 88); (wordZ (e_fs E + FS_FLAGS), 32768)]
                ++ classes_regions (e_fs E) (Z.to_nat FS_NCLASSES) (e_live E)
    end.

  Definition unit_regions2 : list (word * Z) :=
    unit_regions P1 E1 ++ arg_regions ++ (match vp_fs P with None => [] | Some _ => stack_shadow_regions end) ++ fs_regions.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition HIGH_MEM_BEG : Z := 0x10007fff8000.
  Definition HIGH_MEM_END : Z := 2 ^ 47.
  (* [comment removed for export] *)
  Definition LOW_MEM_TOP : Z := 0x7fff7000.
  Definition off_band (x n : Z) : Prop := x + n <= LOW_MEM_TOP \/ HIGH_MEM_BEG <= x.

  (* [comment removed for export] *)
  Definition env_data2 : Prop :=
    e_data E1 mod vp_datal P = 0 /\ 0 < vp_datal P /\ (8 <= vp_datal P -> e_data E1 mod 8 = 0)
    /\ length (e_args E) = 8%nat.

  Definition env_fs : Prop :=
    match vp_fs P with
    | None => e_live E = [] /\ e_fs E = 0
    | Some (len, ssl) =>
        ssl = FS_SSL /\ (0 <= e_fs E /\ off_band (e_fs E) len) /\ e_fs E + len <= HIGH_MEM_END /\ e_fs E mod 4096 = 0
        /\ FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL <= len
        /\ Forall valid_slot (e_live E) /\ NoDup (e_live E)
        (* [comment removed for export] *)
        /\ (e_fs E + len + 4096 <= e_sp0 E1 - vp_frame P1 \/ e_sp0 E1 + 4096 <= e_fs E)
        /\ (e_fs E + len + 4096 <= e_data E1 \/ e_data E1 + e_size E1 <= e_fs E)   (* [comment removed for export] *)
        /\ (e_data E1 + e_size E1 + 4096 <= e_sp0 E1 - vp_frame P1 \/ e_sp0 E1 + 4096 <= e_data E1)
        /\ HIGH_MEM_BEG <= e_sp0 E1 - vp_frame P1
        /\ (0 < e_size E1 -> (off_band (e_data E1) (e_size E1) /\ 16 <= e_data E1) /\ e_data E1 + e_size E1 + 64 <= HIGH_MEM_END)
        (* [comment removed for export] *)
        /\ (8 <= vp_datal P -> 0 < e_size E1 ->
              forall a, vp_shoff P + e_data E1 / 8 - 8 <= a < vp_shoff P + (e_data E1 + e_size E1 - 1) / 8 + 9 ->
                in_rw_zones a = false)
        (* [comment removed for export] *)
        /\ e_sp0 E1 + 16 <= HIGH_MEM_END
        (* [comment removed for export] *)
        /\ Z.of_nat (length (e_live E)) <= vp_fdepth P
        (* [comment removed for export] *)
        /\ vp_imgend P <= e_fs E
    end.

  Definition env_zones : Prop :=
    (forall z, In z (vp_fzones P) -> 0 <= zone_lo z /\ zone_lo z <= zone_hi z /\ zone_hi z <= 2 ^ 64)
    (* [comment removed for export] *)
    /\ (forall z a, In z (vp_fzones P) -> in_zone a z ->
          ~ (e_sp0 E1 - vp_frame P1 <= a < e_sp0 E1)
          /\ (forall c, In c (vp_fcells P1) -> ~ (fst c <= a < fst c + snd c))
          /\ (fz_rw z = true -> ~ (e_data E1 <= a < e_data E1 + e_size E1))
          /\ (forall lo hi, In (lo, hi) (vp_pristine P1) -> ~ (lo <= a < hi))).

  Definition env_kcells : Prop :=
    (* [comment removed for export] *)
    (forall c x, In c (vp_kcells P) -> fst c <= x < fst c + fst (snd c) ->
          in_rw_zones x = false /\ ~ (e_sp0 E1 - vp_frame P1 <= x < e_sp0 E1))
    /\ (forall c x, In c (vp_kruns P) -> fst c <= x < fst (snd c) ->
          0 <= x < 2 ^ 64 /\ in_rw_zones x = false /\ ~ (e_sp0 E1 - vp_frame P1 <= x < e_sp0 E1)).

  Definition env_ok2 : Prop := env_ok P1 E1 /\ env_data2 /\ env_fs /\ env_zones /\ env_kcells.

  (* [comment removed for export] *)
  Definition kcells_hold (mem : word -> option byte) : Prop :=
    forall a w v, In (a, (w, v)) (vp_kcells P) ->
      0 <= a /\ 0 < w /\ a + w <= 2 ^ 64 /\
      exists bs, rdn SEGS mem (wordZ a) (Z.to_nat w) = Some bs /\ bytes_le_to_Z bs = v.

  (* [comment removed for export] *)
  Definition kruns_hold (mem : word -> option byte) : Prop :=
    forall lo hi b, In (lo, (hi, b)) (vp_kruns P) ->
      0 <= lo /\ hi <= 2 ^ 64 /\
      forall a, lo <= a < hi -> exists k : byte, rdn SEGS mem (wordZ a) 1 = Some [k] /\ bv_unsigned k = Z.land b 255.

  (* [comment removed for export] *)
  Definition zones_ok (mem : word -> option byte) : Prop :=
    forall z a, In z (vp_fzones P) -> in_zone a z ->
      (exists b, rdn SEGS mem (wordZ a) 1 = Some [b]) /\ (fz_rw z = true -> store_ok SEGS mem (wordZ a) 1 = true).

  (* [comment removed for export] *)
  Definition shadow_byte (a : Z) : Z := vp_shoff P + a / 8.
  Definition data_shadow_ok (mem : word -> option byte) : Prop :=
    8 <= vp_datal P -> vp_fs P <> None ->
    (forall g, 0 <= 8 * g < e_size E1 ->
       exists k : byte, rdn SEGS mem (wordZ (shadow_byte (e_data E1) + g)) 1 = Some [k]
                  /\ (8 * g + 8 <= e_size E1 -> bv_unsigned k = 0)
                  /\ (e_size E1 < 8 * g + 8 -> bv_unsigned k = e_size E1 - 8 * g))
    /\ (forall a, shadow_byte (e_data E1) - 2 <= a < shadow_byte (e_data E1 + e_size E1 - 1) + 3 ->
       0 < e_size E1 -> exists b, rdn SEGS mem (wordZ a) 1 = Some [b])
    (* [comment removed for export] *)
    /\ (0 < e_size E1 -> forall a, shadow_byte (e_data E1) / 8 * 8 <= a < shadow_byte (e_data E1 + e_size E1 - 1) / 8 * 8 + 8 ->
       exists b, rdn SEGS mem (wordZ a) 1 = Some [b]).

  (* [comment removed for export] *)
  Definition live_flags_ok (mem : word -> option byte) : Prop :=
    forall cp, In cp (e_live E) ->
      exists b, rdn SEGS mem (wordZ (flag_addr (e_fs E) (fst cp) (snd cp))) 1 = Some [b] /\ bv_unsigned b = 1.

  (* [comment removed for export] *)
  Definition rt_apart (a w : Z) : Prop :=
    forall x, a <= x < a + w ->
      in_rw_zones x = false /\ ~ (e_sp0 E1 - vp_frame P1 <= x < e_sp0 E1)
      /\ forall c, In c (vp_fcells P1) -> ~ (fst c <= x < fst c + snd c).
  Definition rt_cell (mem : word -> option byte) (a w v : Z) : Prop :=
    0 <= a /\ 0 < w /\ a + w <= 2 ^ 64 /\ rt_apart a w
    /\ rdn SEGS mem (wordZ a) (Z.to_nat w) = Some (word_to_le_bytes (Z.to_nat w) (wordZ v)).
  Definition rt_readable (mem : word -> option byte) (a w : Z) : Prop :=
    0 <= a /\ a + w <= 2 ^ 64 /\ rt_apart a w
    /\ forall i, 0 <= i < w -> exists b, rdn SEGS mem (wordZ (a + i)) 1 = Some [b].
  (* [comment removed for export] *)
  Definition rtctx_ok (mem : word -> option byte) : Prop :=
    match vp_fs P with
    | None => True
    | Some _ =>
        exists tsd ctx thr db beg,
             rt_cell mem (vp_tp P) 8 (e_fs E)
          /\ rt_cell mem (e_fs E + 88) 8 FS_SSL /\ rt_cell mem (e_fs E + 96) 1 0
          /\ rt_cell mem (vp_tp P - 88) 8 tsd
          /\ rt_cell mem tsd 8 ctx /\ 0 < ctx
          /\ rt_cell mem (ctx + 152) 8 thr /\ 0 < thr
          /\ rt_readable mem (thr + 48) 16
          /\ rt_cell mem (vp_tp P + 8) 8 db /\ 0 < db /\ db <> 2 ^ 64 - 1
          /\ rt_cell mem (db + 24) 8 beg /\ 0 < beg < 2 ^ 64
    end.

  Definition MC2 (mem0 mem : word -> option byte) : Prop :=
    kcells_hold mem /\ zones_ok mem /\ data_shadow_ok mem /\ live_flags_ok mem /\ rtctx_ok mem /\ kruns_hold mem.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition run_holds (mem : word -> option byte) (a w b : Z) : Prop :=
    forall i, 0 <= i < w -> exists k : byte, rdn SEGS mem (wordZ (a + i)) 1 = Some [k] /\ bv_unsigned k = Z.land b 255.

  Definition rcell_holds (shadow : bool) (nu : val) (mem : word -> option byte) (a w : Z) (v : absval) : Prop :=
    match v with
    | None => True
    | Some e =>
        if shadow && lin_is_const e then run_holds mem a w (lc e)
        else cell_holds SEGS nu mem a w v
    end.

  Definition covered (l : list (word * Z)) (a n : Z) : Prop :=
    exists b m, In (b, m) l /\ bv_unsigned b <= a /\ a + n <= bv_unsigned b + m.

  Definition rbase (nu : val) (r : vregion) : Z := vr_disp r + nu (vr_base r).

  Definition kind_ok (nu : val) (A : vstate2) (mem : word -> option byte) (r : vregion) : Prop :=
    let beta := rbase nu r in
    match vr_kind r with
    | RK_fake cid fl =>
        vp_fs P <> None /\ 0 <= cid <= 4 /\ vr_lo r = 0 /\ vr_hi r = fake_size cid /\ (LAST_FIXED2 < vr_base r)%positive /\
        exists pos, 0 <= pos < fs_nframes cid /\ beta = frame_addr (e_fs E) cid pos
               /\ nu fl = flag_addr (e_fs E) cid pos
               /\ (exists b, rdn SEGS mem (wordZ (nu fl)) 1 = Some [b] /\ bv_unsigned b = 1)
               /\ ~ In (cid, pos) (e_live E)
               /\ In (vr_base r) (vs_live A)
    | RK_arg =>
        vp_fs P <> None /\
        (exists cid pos, In (cid, pos) (e_live E)
                        /\ frame_addr (e_fs E) cid pos <= beta + vr_lo r
                        /\ beta + vr_hi r <= frame_addr (e_fs E) cid pos + fake_size cid)
        /\ (exists i, 0 <= i < 8 /\ vr_base r = ASYM2 i /\
              forall lo hi, In (lo, hi) (vr_w r) ->
                exists lo' hi', In (i, (lo', hi')) (vp_wrgn P) /\ lo' <= lo /\ hi <= hi')
    | RK_flag owner =>
        vr_lo r = 0 /\ vr_hi r = 1 /\ vr_disp r = 0 /\ vr_cells r = [] /\
        exists ro cid fl, rgn_get (vs_rgn A) owner = Some ro /\ vr_kind ro = RK_fake cid fl /\ vr_base r = fl
    | RK_shadow s =>
        vp_fs P <> None /\ vr_disp r = vp_shoff P /\
        (s = SP0 -> vr_base r = SP8 /\ - (vp_frame P1 / 8) - 8 <= vr_lo r /\ vr_hi r <= 1) /\
        (s = DATA -> vr_base r = DATA8) /\
        (s <> FSB) /\
        (s <> SP0 -> s <> DATA -> s <> FSB ->
           exists ro, rgn_get (vs_rgn A) s = Some ro /\ vr_b8 ro = Some (vr_base r) /\
             match vr_kind ro with
             | RK_fake cid _ => 8 * nu (vr_base r) = rbase nu ro /\ 0 <= vr_lo r /\ 8 * vr_hi r <= fake_size cid
             | RK_arg => nu (vr_base r) = rbase nu ro / 8 /\ vr_w r = [] /\
                 exists cid pos, In (cid, pos) (e_live E)
                   /\ frame_addr (e_fs E) cid pos <= 8 * (nu (vr_base r) + vr_lo r)
                   /\ 8 * (nu (vr_base r) + vr_hi r) <= frame_addr (e_fs E) cid pos + fake_size cid
             | _ => False
             end)
    | RK_fs => vp_fs P <> None /\ vr_base r = FSB /\ vr_disp r = 0 /\ vr_lo r = 0 /\ vr_hi r = 88
    end.

  Definition is_data_shadow (r : vregion) : bool :=
    match vr_kind r with RK_shadow s => Pos.eqb s DATA | _ => false end.

  Definition in_any_zone (a : Z) : bool := existsb (in_zoneb a) (vp_fzones P).

  (* [comment removed for export] *)
  Definition region_cells_ok (nu : val) (mem : word -> option byte) (r : vregion) : Prop :=
    forall off w v, In (off, (w, v)) (vr_cells r) ->
      vr_lo r <= off /\ 0 < w /\ off + w <= vr_hi r /\ rcell_holds (is_shadow r) nu mem (rbase nu r + off) w v.

  Definition region_perm_ok (nu : val) (mem : word -> option byte) (r : vregion) : Prop :=
    is_data_shadow r = false ->
    (forall off, vr_lo r <= off < vr_hi r ->
        in_any_zone (rbase nu r + off) = true
        /\ exists b, rdn SEGS mem (wordZ (rbase nu r + off)) 1 = Some [b])
    /\ (forall lo hi off, In (lo, hi) (vr_w r) -> lo <= off < hi ->
          vr_lo r <= off < vr_hi r
          /\ in_rw_zones (rbase nu r + off) = true
          /\ store_ok SEGS mem (wordZ (rbase nu r + off)) 1 = true
          /\ covered unit_regions2 (rbase nu r + off) 1).

  Definition region_nul_ok (nu : val) (mem : word -> option byte) (r : vregion) : Prop :=
    forall lo hi, In (lo, hi) (vr_nul r) ->
      exists off b, lo <= off <= hi /\ vr_lo r <= off < vr_hi r /\
                    rdn SEGS mem (wordZ (rbase nu r + off)) 1 = Some [b] /\ bv_unsigned b = 0.

  Definition region_ok (nu : val) (A : vstate2) (mem : word -> option byte) (r : vregion) : Prop :=
    0 <= rbase nu r + vr_lo r /\ rbase nu r + vr_hi r <= 2 ^ 64 /\ vr_lo r <= vr_hi r
    /\ (is_data_shadow r = true -> vr_cells r = [] /\ vr_w r = [] /\ vr_nul r = [])
    /\ region_cells_ok nu mem r
    /\ region_perm_ok nu mem r
    /\ region_nul_ok nu mem r
    /\ kind_ok nu A mem r.

  (* [comment removed for export] *)
  Definition gamma_divdef (nu : val) (A : vstate2) : Prop :=
    forall q x m, pm_get q (vs_divdef A) = Some (x, m) -> 0 < m /\ nu q = Z.div (eval nu x) m.

  (* [comment removed for export] *)
  Definition live_ok (nu : val) (A : vstate2) : Prop :=
    (forall s, In s (vs_live A) <-> exists r, In r (vs_rgn A) /\ vr_base r = s /\
                                              match vr_kind r with RK_fake _ _ => True | _ => False end)
    /\ NoDup (vs_live A)
    /\ (forall r1 r2, In r1 (vs_rgn A) -> In r2 (vs_rgn A) ->
          match vr_kind r1, vr_kind r2 with
          | RK_fake _ _, RK_fake _ _ => vr_base r1 <> vr_base r2 -> rbase nu r1 <> rbase nu r2
          | _, _ => True end)
    /\ List.NoDup (map vr_base (vs_rgn A)).

  (* [comment removed for export] *)
  Definition cells_syms_below (m : cellmap) (b : positive) : Prop :=
    forall k w e, In (k, (w, Some e)) m -> lin_below e b = true.
  Definition state_below2 (A : vstate2) : Prop :=
    (LAST_FIXED2 < vs_next (v1 A))%positive
    /\ (forall r, In r (vs_rgn A) -> (vr_base r < vs_next (v1 A))%positive
                                   /\ cells_syms_below (vr_cells r) (vs_next (v1 A))
                                   /\ match vr_kind r with RK_fake _ fl => (fl < vs_next (v1 A))%positive | _ => True end)
    /\ (forall s, In s (vs_live A) -> (s < vs_next (v1 A))%positive)
    /\ (forall q x m, pm_get q (vs_divdef A) = Some (x, m) ->
          (q < vs_next (v1 A))%positive /\ lin_below x (vs_next (v1 A)) = true)
    /\ (forall a n v, In (a, (n, v)) (vs_memo A) ->
          lin_below a (vs_next (v1 A)) = true /\ lin_below v (vs_next (v1 A)) = true).

  (* [comment removed for export] *)
  Definition memo_ok (nu : val) (mem : word -> option byte) (A : vstate2) : Prop :=
    forall a n v, In (a, (n, v)) (vs_memo A) ->
      0 < n < 8 /\ cell_holds SEGS nu mem (zwrap 64 (eval nu a)) n (Some v).

  (* [comment removed for export] *)
  Definition own_flags (A : vstate2) (nu : val) : list Z :=
    flat_map (fun r => match vr_kind r with RK_fake _ fl => [nu fl] | _ => [] end) (vs_rgn A).
  Definition in_flags_zone (a : Z) : Prop :=
    match vp_fs P with None => False | Some _ => e_fs E + FS_FLAGS <= a < e_fs E + FS_FLAGS + 32768 end.
  Definition flags_step (A A' : vstate2) (nu nu' : val) (mem mem' : word -> option byte) : Prop :=
    forall a, in_flags_zone a ->
         ((In a (own_flags A nu) <-> In a (own_flags A' nu')) /\ mem' (wordZ a) = mem (wordZ a))
      \/ (In a (own_flags A' nu') /\ ~ In a (own_flags A nu) /\ (exists b, mem (wordZ a) = Some b /\ bv_unsigned b = 0))
      \/ (In a (own_flags A nu) /\ ~ In a (own_flags A' nu') /\ (exists b, mem' (wordZ a) = Some b /\ bv_unsigned b = 0)).

  (* [comment removed for export] *)
  Definition flags_inv (A : vstate2) (nu : val) (mem : word -> option byte) : Prop :=
    vp_fs P <> None ->
    forall c p, 0 <= c <= 4 -> 0 <= p < fs_nframes c -> ~ In (c, p) (e_live E) ->
      ~ In (flag_addr (e_fs E) c p) (own_flags A nu) ->
      exists b, mem (wordZ (flag_addr (e_fs E) c p)) = Some b /\ bv_unsigned b = 0.


  (* [comment removed for export] *)
  Definition globs_ok2 (A : vstate2) : Prop :=
    asan_mode P = true ->
    forall a w v, In (a, (w, v)) (vs_globs (v1 A)) ->
      exists f, In f (vp_fcells P1) /\ fst f <= a /\ a + w <= fst f + snd f.

  (* [comment removed for export] *)
  Definition gamma2 (mem0 : word -> option byte) (A : vstate2) (nu : val) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
    gamma SEGS P1 E1 (zpatch mem0 mem) (v1 A) nu regs mem
    /\ env_ok2 /\ MC2 mem0 mem /\ gamma_fix2 E nu
    /\ gamma_divdef nu A
    /\ (forall r, In r (vs_rgn A) -> region_ok nu A mem r)
    /\ live_ok nu A
    /\ state_below2 A
    /\ globs_ok2 A
    /\ flags_inv A nu mem
    /\ memo_ok nu mem A.

  (* [comment removed for export] *)
  Lemma gamma2_v1 mem0 A nu regs mem : gamma2 mem0 A nu regs mem -> gamma SEGS P1 E1 (zpatch mem0 mem) (v1 A) nu regs mem.
  Proof. intros H; exact (proj1 H). Qed.

  Lemma gamma2_fix mem0 A nu regs mem : gamma2 mem0 A nu regs mem -> gamma_fix2 E nu.
  Proof. intros H. exact (proj1 (proj2 (proj2 (proj2 H)))). Qed.

End WithParams.

(* [comment removed for export] *)
Lemma zone_env_indep (E E' : venv2) z :
  fzone_syms_ok z = true ->
  e_sp0 (ev1 E) = e_sp0 (ev1 E') -> e_data (ev1 E) = e_data (ev1 E') -> e_size (ev1 E) = e_size (ev1 E') ->
  e_tp (ev1 E) = e_tp (ev1 E') -> e_gp (ev1 E) = e_gp (ev1 E') -> e_fs E = e_fs E' ->
  zone_lo E z = zone_lo E' z /\ zone_hi E z = zone_hi E' z.
Proof.
  unfold fzone_syms_ok. rewrite !andb_true_iff, !forallb_forall. intros [[Hb Hl] Hh] H1 H2 H3 H4 H5 H6.
  unfold zone_lo, zone_hi.
  rewrite (nuE_fsym E E' (fz_base z) Hb H1 H2 H3 H4 H5 H6).
  rewrite (eval_ext (nuE E) (nuE E') (fz_lo z)) by (intros s Hs; apply nuE_fsym; auto).
  rewrite (eval_ext (nuE E) (nuE E') (fz_hi z)) by (intros s Hs; apply nuE_fsym; auto).
  split; reflexivity.
Qed.

Lemma zpatch_env_indep (P : vparams2) (E E' : venv2) :
  forallb fzone_syms_ok (vp_fzones P) = true ->
  e_sp0 (ev1 E) = e_sp0 (ev1 E') -> e_data (ev1 E) = e_data (ev1 E') -> e_size (ev1 E) = e_size (ev1 E') ->
  e_tp (ev1 E) = e_tp (ev1 E') -> e_gp (ev1 E) = e_gp (ev1 E') -> e_fs E = e_fs E' ->
  (forall a, in_rw_zones P E a = in_rw_zones P E' a)
  /\ zregions P E = zregions P E'
  /\ (forall m0 m a, zpatch P E m0 m a = zpatch P E' m0 m a).
Proof.
  intros HZ H1 H2 H3 H4 H5 H6. rewrite forallb_forall in HZ.
  assert (ZZ : forall z, In z (rw_zones P) -> zone_lo E z = zone_lo E' z /\ zone_hi E z = zone_hi E' z).
  { intros z Hz. unfold rw_zones in Hz. apply filter_In in Hz as [Hz _]. apply zone_env_indep; auto. }
  assert (RW : forall a, in_rw_zones P E a = in_rw_zones P E' a).
  { intros a. unfold in_rw_zones. revert ZZ. generalize (rw_zones P) as l. induction l as [|z t IH]; [reflexivity|].
    intros ZZ. cbn [existsb]. destruct (ZZ z (or_introl eq_refl)) as [L H].
    rewrite IH by (intros y Hy; apply ZZ; right; exact Hy). unfold in_zoneb. rewrite L, H. reflexivity. }
  split; [exact RW|]. split.
  - unfold zregions. revert ZZ. generalize (rw_zones P) as l. induction l as [|z t IH]; [reflexivity|].
    intros ZZ. cbn [map]. destruct (ZZ z (or_introl eq_refl)) as [L H].
    rewrite IH by (intros y Hy; apply ZZ; right; exact Hy). unfold zone_region. rewrite L, H. reflexivity.
  - intros m0 m a. unfold zpatch. rewrite RW. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Iface2.
  Variable SEGS : list Segment.
  Variable P : vparams2.
  Variable E : venv2.
  Variable mem0 : word -> option byte.

  (* [comment removed for export] *)
  Definition params_ok2 : Prop :=
    params_ok SEGS (p1 P)
    /\ 0 <= vp_shoff P /\ vp_frame (p1 P) mod 16 = 0
    /\ (* [comment removed for export] *)
       (forall a w v, In (a, (w, v)) (vp_kcells P) ->
          0 <= a /\ 0 < w /\ a + w <= vp_splo (p1 P) - vp_frame (p1 P)
          /\ (forall c, In c (vp_fcells (p1 P)) -> a + w <= fst c \/ fst c + snd c <= a))
    /\ (forall c, In c (vp_kruns P) ->
          forall f, In f (vp_fcells (p1 P)) -> fst (snd c) <= fst f \/ fst f + snd f <= fst c)
    /\ (forall i lo hi, In (i, (lo, hi)) (vp_wrgn P) -> 0 <= i < 8 /\ lo <= hi)
    /\ (* [comment removed for export] *)
       (vp_fs P <> None -> vp_shoff P = 0x7fff8000 /\ forall c, In c (vp_fcells (p1 P)) -> fst c + snd c <= 0x7fff7000)

    /\ (* [comment removed for export] *)
       (vp_fs P = None -> vp_fzones P = [])
    /\ forallb fzone_syms_ok (vp_fzones P) = true
    /\ (* [comment removed for export] *)
       (vp_fs P <> None -> 0 <= vp_imgend P <= 0x7fff7000
          /\ (forall c, In c (vp_fcells (p1 P)) -> fst c + snd c <= vp_imgend P)
          /\ (forall a w v, In (a, (w, v)) (vp_kcells P) -> a + w <= vp_imgend P \/ 0x7fff8000 <= a)
          /\ (forall lo hi, In (lo, hi) (vp_pristine (p1 P)) -> hi <= vp_imgend P)).

  Definition step_post2 (A : vstate2) (nu : val) (succs : list vstate2)
             (regs : bvmap 5 word) (mem : word -> option byte) (pc : word) (rom : word -> option byte) : Prop :=
    exists regs' pc' mem' A' nu',
      RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst regs' pc' mem' rom)
      /\ In A' succs /\ vs2_pc A' = bv_unsigned pc'
      /\ ext (vs2_next A) nu nu' /\ (vs2_next A <= vs2_next A')%positive
      /\ frame_mod mem mem' (unit_regions2 P E)
      /\ flags_step P E A A' nu nu' mem mem'
      /\ gamma2 SEGS P E mem0 A' nu' regs' mem'.

  (* [comment removed for export] *)
End Iface2.
