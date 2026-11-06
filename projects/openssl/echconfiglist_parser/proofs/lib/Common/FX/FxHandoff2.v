(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxImage FxRn FxHandoff FxHoBuild.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope uint63_scope.

(* [comment removed for export] *)
Definition ho_iseq512 : list int := Eval vm_compute in iseq 512.
Lemma ho_iseq512_eq : ho_iseq512 = iseq 512.
Proof. vm_compute. reflexivity. Qed.
Definition ho_iseq8 : list int := Eval vm_compute in iseq 8.
Lemma ho_iseq8_eq : ho_iseq8 = iseq 8.
Proof. vm_compute. reflexivity. Qed.

Section Check2.
Variable IM : fimage.
Variable facts : list hfact.

(* [comment removed for export] *)
Definition plim (r : rdesc) (pn : int) : int :=
  if (pn << 12) + 4096 <=? rd_len r then 512 else (rd_len r - (pn << 12)) >> 3.

(* [comment removed for export] *)
Definition page_hdr_b2 (r : rdesc) (p : pdesc) : bool :=
  let t := rd_tag r in
  let pn := pd_pn p in
  let L := plim r pn in
  (pn <? b50) && (rd_lo r <=? (pn << 12)) && (rd_len r <=? b62)
  && (if (pn << 12) + 4096 <=? rd_len r then true
      else ((pn << 12) <? rd_len r) && ((rd_len r land 7) =? 0)
           && forallb (fun kv => fst kv <? L) (pd_cells p))
  && (if pd_wr p then (if t =? 0 then seg_wr_page IM pn else wr_cov facts t (pn << 12) (L << 3)) else true)
  && (match pd_kind p with PKImage => t =? 0 | _ => true end).

(* [comment removed for export] *)
Definition cell_chk (r : rdesc) (p : pdesc) (pg : page) (ci : int) : bool :=
  let t := rd_tag r in
  let pn := pd_pn p in
  let off := (pn << 12) + (ci << 3) in
  match iget ci (pg_cells pg) with
  | Some (CV v) => cell_ok IM facts t off v
  | Some CU => true
  | Some (CB sl) => forallb (fun j => slot_ok_b IM facts t (off + j) (sget j sl)) ho_iseq8
  | None => match pd_kind p with
            | PKZero => zero_cov facts t off 8
            | PKUnk => true
            | PKImage => clear_cov facts off 8
            end
  end.

Definition page_cells_b2 (r : rdesc) (p : pdesc) : bool :=
  let pg := page_of p in
  let L := plim r (pd_pn p) in
  forallb (fun ci => if L <=? ci then true else cell_chk r p pg ci) ho_iseq512.

(* [comment removed for export] *)
Definition page_ok_b2 (r : rdesc) (p : pdesc) : bool :=
  if page_hdr_b2 r p then
    match pd_cells p, pd_kind p with
    | [], PKZero =>
        if zero_cov facts (rd_tag r) (pd_pn p << 12) (plim r (pd_pn p) << 3) then true
        else page_cells_b2 r p
    | _, _ => page_cells_b2 r p
    end
  else false.

Definition region_ok_b2 (d : sdesc) (r : rdesc) : bool :=
  region_fact_b facts r
  && forallb (fun r' => (rd_tag r' =? rd_tag r) || disj_fact_b facts r r') (sd_mem d)
  && forallb (page_ok_b2 r) (rd_pages r)
  && (if rd_tag r =? 0 then
        image_pages_ok IM facts r && (match rd_dflt r with None => true | Some _ => false end)
      else
        match rd_dflt r with
        | None => true
        | Some PKUnk => (rd_lo r <=? rd_len r) && wr_cov facts (rd_tag r) (rd_lo r) (rd_len r - rd_lo r)
        | Some PKZero => (rd_lo r <=? rd_len r) && wr_cov facts (rd_tag r) (rd_lo r) (rd_len r - rd_lo r)
                         && zero_cov facts (rd_tag r) (rd_lo r) (rd_len r - rd_lo r)
        | Some PKImage => false
        end).

Definition ho_check2 (d : sdesc) : bool :=
  regs_ok_b facts d && forallb (region_ok_b2 d) (sd_mem d).

(* [comment removed for export] *)
Lemma page_ok_b_imp : forall r p, page_ok_b IM facts r p = true -> page_ok_b2 r p = true.
Proof.
  intros r p H. unfold page_ok_b in H. cbv zeta in H.
  rewrite !andb_true_iff in H. destruct H as [[[[[[Hpn Hlo] Hup] Hlen] Hwr] Hkind] Hcells].
  assert (EL : plim r (pd_pn p) = 512) by (unfold plim; rewrite Hup; reflexivity).
  assert (Hc2 : page_cells_b2 r p = true).
  { unfold page_cells_b2. cbv zeta. rewrite EL, ho_iseq512_eq. rewrite forallb_forall in Hcells |- *.
    intros ci Hci. destruct (512 <=? ci); [reflexivity|].
    specialize (Hcells ci Hci). unfold cell_chk. cbv zeta. rewrite ho_iseq8_eq. exact Hcells. }
  unfold page_ok_b2.
  assert (Eh : page_hdr_b2 r p = true).
  { unfold page_hdr_b2. cbv zeta. rewrite EL, Hpn, Hlo, Hlen, Hup, Hkind. cbn [andb].
    rewrite andb_true_r. change (512 << 3) with 4096. exact Hwr. }
  rewrite Eh. destruct (pd_cells p); [|exact Hc2]. destruct (pd_kind p); try exact Hc2.
  destruct (zero_cov facts (rd_tag r) (pd_pn p << 12) (plim r (pd_pn p) << 3)); [reflexivity | exact Hc2].
Qed.

Lemma ho_check_imp : forall d, ho_check IM facts d = true -> ho_check2 d = true.
Proof.
  intros d H. unfold ho_check in H. unfold ho_check2.
  apply andb_true_iff in H as [H1 H2]. rewrite H1. cbn [andb].
  rewrite forallb_forall in H2 |- *. intros r Hr. specialize (H2 r Hr).
  unfold region_ok_b in H2. unfold region_ok_b2.
  rewrite !andb_true_iff in H2. destruct H2 as [[[Ha Hb] Hc] Hd]. rewrite Ha, Hb, Hd. cbn [andb].
  rewrite andb_true_r. rewrite forallb_forall in Hc |- *. intros p Hp. exact (page_ok_b_imp r p (Hc p Hp)).
Qed.
End Check2.

(* [comment removed for export] *)
Section Build2.
Variable IM : fimage.
Variable facts : list hfact.

(* [comment removed for export] *)
Definition pg_ext (len pn : int) : int :=
  if (pn << 12) + 4096 <=? len then 4096 else len - (pn << 12).

Definition zero_page2 (len t pn : int) : bool := zero_cov facts t (pn << 12) (pg_ext len pn).

Definition cells_of_fact2 (lo len t : int) (f : hfact) : list int :=
  let inside := filter (fun c => (lo <=? c) && (c + 8 <=? len)) in
  match f with
  | HCell t' o n _ => if t' =? t then inside (span_cells o n) else []
  | HVal t' o _ => if t' =? t then inside (span_cells o 8) else []
  | HBytes t' o n _ => if t' =? t then inside (span_cells o n) else []
  | HZero t' o l =>
      if (t' =? t) && (l <=? 1048576)
      then filter (fun c => negb (zero_page2 len t (c >> 12))) (inside (span_cells o l)) else []
  | _ => []
  end.

(* [comment removed for export] *)
Definition zero_pages_of_fact2 (len t : int) (f : hfact) : list int :=
  zero_pages_of_fact t f ++
  match f with
  | HZero t' o l =>
      let pl := len >> 12 in
      if (t' =? t) && (l <=? 1048576) && negb ((len land 4095) =? 0) && zero_page2 len t pl
         && (o <=? (pl << 12)) && (len <=? o + l)
      then [pl] else []
  | _ => []
  end.

Definition page_desc2 (len t pn : int) (cells : list (int * cell)) : pdesc :=
  if t =? 0 then PD pn (seg_wr_page IM pn) PKImage cells
  else PD pn (wr_cov facts t (pn << 12) (pg_ext len pn)) (if zero_page2 len t pn then PKZero else PKUnk) cells.

Definition region_desc2 (shape : int * int * int * int * option pkind) : rdesc :=
  let '(t, lo, len, al, dflt) := shape in
  if t =? 0 then region_desc IM facts shape
  else
  let cells := flat_map (cells_of_fact2 lo len t) facts in
  let grouped := fold_left (add_cell IM facts t) cells iempty in
  let zp := flat_map (zero_pages_of_fact2 len t) facts in
  let grouped := fold_left (fun acc pn => match iget pn acc with Some _ => acc | None => iset pn [] acc end) zp grouped in
  RD t lo len al dflt (map (fun kv => page_desc2 len t (fst kv) (snd kv)) (ielements grouped)).

Definition ho_build2 (pc : int) (shapes : list (int * int * int * int * option pkind)) : sdesc :=
  SD pc (regs_desc facts) (map region_desc2 shapes).
End Build2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound2.
Variable segs : list Segment.
Variable IM : fimage.
Hypothesis HIM : image_ok segs IM.
Hypothesis HWR : image_wr_ok IM.
Open Scope Z_scope.

Lemma i_leb_false (x y : int) : (x <=? y)%uint63 = false -> to_Z y < to_Z x.
Proof. intros H. destruct (lebP x y) as [L|L]; [discriminate | lia]. Qed.

(* [comment removed for export] *)
Lemma plim_spec : forall r pn,
  to_Z pn < 2 ^ 50 -> to_Z (rd_len r) <= 2 ^ 62 ->
  (if ((pn << 12) + 4096 <=? rd_len r)%uint63 then True
   else to_Z pn * 4096 < to_Z (rd_len r) /\ to_Z (rd_len r) mod 8 = 0) ->
  to_Z (plim r pn) = clim (region_of r) pn
  /\ 0 <= to_Z (plim r pn) <= 512
  /\ to_Z pn * 4096 + 8 * to_Z (plim r pn) <= to_Z (rd_len r)
  /\ to_Z pn * 4096 < to_Z (rd_len r)
  /\ (to_Z pn * 4096 + 4096 <= to_Z (rd_len r) \/ to_Z (rd_len r) mod 8 = 0)
  /\ to_Z (plim r pn << 3)%uint63 = 8 * to_Z (plim r pn).
Proof.
  intros r pn Hpn Hlen Hgeo. pose proof (i63_range pn) as Hpn0. pose proof (i63_range (rd_len r)) as Hl0.
  pose proof (ho_toZ_lsl12 pn Hpn) as Epn.
  unfold plim, clim. cbn [region_of rg_len].
  destruct ((pn << 12) + 4096 <=? rd_len r)%uint63 eqn:Eup.
  - apply i_leb_le in Eup.
    rewrite toZ_add_small, Epn in Eup by (rewrite Epn; change (to_Z 4096) with 4096; lia).
    change (to_Z 4096) with 4096 in Eup. change (to_Z 512) with 512. change (to_Z (512 << 3)%uint63) with 4096.
    split; [symmetry; apply Z.min_l; clear - Eup; Z.div_mod_to_equations; lia|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [left; exact Eup | reflexivity].
  - apply i_leb_false in Eup.
    rewrite toZ_add_small, Epn in Eup by (rewrite Epn; change (to_Z 4096) with 4096; lia).
    change (to_Z 4096) with 4096 in Eup. destruct Hgeo as [Hlt Hal].
    assert (Esub : to_Z (rd_len r - (pn << 12))%uint63 = to_Z (rd_len r) - to_Z pn * 4096).
    { rewrite toZ_sub_small; rewrite Epn; lia. }
    assert (EL : to_Z ((rd_len r - (pn << 12)) >> 3)%uint63 = (to_Z (rd_len r) - to_Z pn * 4096) / 8).
    { rewrite lsr_spec, Esub. reflexivity. }
    assert (Hq : 0 <= (to_Z (rd_len r) - to_Z pn * 4096) / 8 < 512
                 /\ 8 * ((to_Z (rd_len r) - to_Z pn * 4096) / 8) <= to_Z (rd_len r) - to_Z pn * 4096).
    { clear - Hlt Eup. Z.div_mod_to_equations. lia. }
    rewrite EL.
    split; [symmetry; apply Z.min_r; lia|].
    split; [lia|]. split; [lia|]. split; [exact Hlt|]. split; [right; exact Hal|].
    rewrite (toZ_lsl_small _ 3 3%uint63); [rewrite EL; change (2 ^ 3) with 8; lia | reflexivity | lia |].
    rewrite EL. change (2 ^ 3) with 8. lia.
Qed.

Section Facts2.
Variable facts : list hfact.
Variable rho : int -> word.
Variable ms : machine_state.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
Hypothesis Hfacts : Forall (hholds segs rho ms) facts.

(* [comment removed for export] *)
Lemma cells_sem : forall r p L,
  to_Z (pd_pn p) < 2 ^ 50 -> L <= 512 ->
  (match pd_kind p with PKImage => (rd_tag r =? 0)%uint63 | _ => true end) = true ->
  (forall ci, 0 <= to_Z ci < L -> cell_chk IM facts r p (page_of p) ci = true) ->
  (forall ci v, 0 <= to_Z ci < L -> cell_at IM (page_of p) (pd_pn p) ci = Some v ->
     forall j, (j < 8)%nat ->
       rview segs (ms_mem ms) (adr rho (rd_tag r) (to_Z (pd_pn p) * 4096 + to_Z ci * 8 + Z.of_nat j))
       = nth_error (wbytes8 (dv rho v)) j)
  /\ (forall ci sl, 0 <= to_Z ci < L -> iget ci (pg_cells (page_of p)) = Some (CB sl) ->
        forall j : int, 0 <= to_Z j < 8 ->
          slot_ok segs rho (ms_mem ms) (adr rho (rd_tag r) (to_Z (pd_pn p) * 4096 + to_Z ci * 8 + to_Z j)) (sget j sl)).
Proof.
  intros r p L Hpn HL Hkind Hall.
  pose proof (i63_range (pd_pn p)) as Hpn0.
  pose proof (ho_toZ_lsl12 _ Hpn) as Epn.
  split.
  - (* [comment removed for export] *)
    intros ci v Hci Hcell j Hj.
    pose proof (Hall ci Hci) as Hcells. unfold cell_chk in Hcells. cbv zeta in Hcells.
    pose proof (ho_toZ_lsl3 ci ltac:(lia)) as Eci.
    assert (Eoff : to_Z ((pd_pn p << 12) + (ci << 3))%uint63 = to_Z (pd_pn p) * 4096 + to_Z ci * 8).
    { rewrite toZ_add_small; rewrite Epn, Eci; [reflexivity | lia]. }
    unfold cell_at in Hcell.
    destruct (iget ci (pg_cells (page_of p))) as [[v0 | | sl0] |] eqn:Eg.
    + inversion Hcell; subst v0.
      pose proof (cell_ok_sound segs IM HIM facts rho ms Hrho0 Hfacts _ _ _ ltac:(rewrite Eoff; lia) Hcells j Hj) as Hv.
      rewrite Eoff in Hv. exact Hv.
    + discriminate Hcell.
    + discriminate Hcell.
    + cbn [page_of pg_kind] in Hcell.
      destruct (pd_kind p) eqn:Ek.
      * inversion Hcell; subst v.
        pose proof (zero_cov_sound segs facts rho ms Hfacts _ _ _ Hcells (Z.of_nat j) ltac:(change (to_Z 8) with 8; lia)) as Hv.
        rewrite Eoff in Hv. rewrite Hv. symmetry. apply (ho_dv_fv0_bytes rho Hrho0). exact Hj.
      * apply ho_eqb_eq in Hkind. rewrite Hkind.
        apply (image_cell_rview segs IM HIM rho ms Hrho0 _ ci v Hpn ltac:(lia) Hcell); [| exact Hj].
        intros x Hx. apply (clear_cov_sound segs facts rho ms Hfacts _ _ Hcells). rewrite Eoff. change (to_Z 8) with 8. lia.
      * discriminate Hcell.
  - (* [comment removed for export] *)
    intros ci sl Hci Hget j Hj.
    pose proof (Hall ci Hci) as Hcells. unfold cell_chk in Hcells. cbv zeta in Hcells.
    rewrite Hget, ho_iseq8_eq in Hcells. rewrite forallb_forall in Hcells.
    specialize (Hcells j (in_iseq 8 j ltac:(change (Z.of_nat 8) with 8; lia))).
    pose proof (ho_toZ_lsl3 ci ltac:(lia)) as Eci.
    assert (Eoff : to_Z ((pd_pn p << 12) + (ci << 3))%uint63 = to_Z (pd_pn p) * 4096 + to_Z ci * 8).
    { rewrite toZ_add_small; rewrite Epn, Eci; [reflexivity | lia]. }
    assert (Ea : to_Z ((pd_pn p << 12) + (ci << 3) + j)%uint63
                 = to_Z (pd_pn p) * 4096 + to_Z ci * 8 + to_Z j).
    { rewrite toZ_add_small; rewrite Eoff; [reflexivity | lia]. }
    unfold slot_ok_b in Hcells. unfold slot_ok.
    destruct (sget j sl) as [b | v j0 |].
    + destruct (byte_known IM facts (rd_tag r) ((pd_pn p << 12) + (ci << 3) + j)%uint63) as [b' |] eqn:Hb;
        [| discriminate Hcells].
      apply ho_eqb_eq in Hcells. subst b'.
      pose proof (byte_known_sound segs IM HIM facts rho ms Hrho0 Hfacts _ _ _ Hb) as Hv. rewrite Ea in Hv. exact Hv.
    + pose proof (sv_cov_sound segs facts rho ms Hfacts _ _ _ _ Hcells) as Hv. rewrite Ea in Hv. exact Hv.
    + exact I.
Qed.

(* [comment removed for export] *)
Lemma page_ok_b2_sound : forall r p,
  page_ok_b2 IM facts r p = true ->
  page_ok segs IM rho (ms_mem ms) (rd_tag r) (pd_pn p) (clim (region_of r) (pd_pn p)) (page_of p)
  /\ to_Z (rd_lo r) <= to_Z (pd_pn p) * 4096
  /\ to_Z (pd_pn p) * 4096 < to_Z (rd_len r)
  /\ (to_Z (pd_pn p) * 4096 + 4096 <= to_Z (rd_len r) \/ to_Z (rd_len r) mod 8 = 0).
Proof.
  intros r p H. unfold page_ok_b2 in H.
  destruct (page_hdr_b2 IM facts r p) eqn:Eh; [|discriminate H].
  unfold page_hdr_b2 in Eh. cbv zeta in Eh. rewrite !andb_true_iff in Eh.
  destruct Eh as [[[[[Hpn Hlo] Hlen] Hgeo] Hwr] Hkind].
  apply i_ltb_lt in Hpn. rewrite ho_b50 in Hpn.
  apply i_leb_le in Hlo, Hlen. rewrite ho_b62 in Hlen.
  pose proof (i63_range (pd_pn p)) as Hpn0.
  pose proof (ho_toZ_lsl12 _ Hpn) as Epn. rewrite Epn in Hlo.
  assert (Hgeo' : if ((pd_pn p << 12) + 4096 <=? rd_len r)%uint63 then True
                  else to_Z (pd_pn p) * 4096 < to_Z (rd_len r) /\ to_Z (rd_len r) mod 8 = 0).
  { destruct ((pd_pn p << 12) + 4096 <=? rd_len r)%uint63; [exact I|].
    rewrite !andb_true_iff in Hgeo. destruct Hgeo as [[Hlt Hal] _].
    apply i_ltb_lt in Hlt. rewrite Epn in Hlt. split; [exact Hlt|].
    apply ho_eqb_eq in Hal. apply (f_equal to_Z) in Hal.
    rewrite (i63_land_ones (rd_len r) 7%uint63 3 eq_refl ltac:(lia)) in Hal. exact Hal. }
  destruct (plim_spec r (pd_pn p) Hpn Hlen Hgeo') as (EL & HL & Hin & Hlt & Hal & EL8).
  split; [| split; [exact Hlo | split; [exact Hlt | exact Hal]]].
  rewrite <- EL.
  assert (Hw : pg_wr (page_of p) = true ->
               forall j, 0 <= j < 8 * to_Z (plim r (pd_pn p)) ->
                 wview segs (ms_mem ms) (adr rho (rd_tag r) (to_Z (pd_pn p) * 4096 + j)) <> None).
  { cbn [page_of pg_wr]. intros Hw j Hj. rewrite Hw in Hwr.
    destruct (rd_tag r =? 0)%uint63 eqn:Et.
    - apply ho_eqb_eq in Et. rewrite Et, (ho_adr0 rho Hrho0).
      unfold seg_wr_page in Hwr.
      destruct (find_seg IM (pd_pn p << 12)%uint63) as [sg |] eqn:Hf; [| discriminate Hwr].
      exact (wview_image_wr segs IM HIM HWR ms _ sg j Hpn Hf Hwr ltac:(lia)).
    - pose proof (wr_cov_sound segs facts rho ms Hfacts _ _ _ Hwr j ltac:(rewrite EL8; exact Hj)) as Hv.
      rewrite Epn in Hv. exact Hv. }
  assert (Hsem : (forall ci, 0 <= to_Z ci < to_Z (plim r (pd_pn p)) ->
                    cell_chk IM facts r p (page_of p) ci = true) ->
                 page_ok segs IM rho (ms_mem ms) (rd_tag r) (pd_pn p) (to_Z (plim r (pd_pn p))) (page_of p)).
  { intros Hall. destruct (cells_sem r p _ Hpn (proj2 HL) Hkind Hall) as [Hc Hs].
    split; [exact Hw | split; [exact Hc | exact Hs]]. }
  assert (Hloop : page_cells_b2 IM facts r p = true ->
                  page_ok segs IM rho (ms_mem ms) (rd_tag r) (pd_pn p) (to_Z (plim r (pd_pn p))) (page_of p)).
  { intros Hc. apply Hsem. intros ci Hci. unfold page_cells_b2 in Hc. cbv zeta in Hc.
    rewrite ho_iseq512_eq, forallb_forall in Hc.
    specialize (Hc ci (in_iseq 512 ci ltac:(change (Z.of_nat 512) with 512; lia))).
    destruct (plim r (pd_pn p) <=? ci)%uint63 eqn:Ele; [apply i_leb_le in Ele; lia | exact Hc]. }
  destruct (pd_cells p) as [|c0 cs] eqn:Ec; [|exact (Hloop H)].
  destruct (pd_kind p) eqn:Ek; try exact (Hloop H).
  destruct (zero_cov facts (rd_tag r) (pd_pn p << 12) (plim r (pd_pn p) << 3)) eqn:Ez; [|exact (Hloop H)].
  (* [comment removed for export] *)
  split; [exact Hw | split].
  - intros ci v Hci Hcell j Hj. unfold cell_at, page_of in Hcell. cbn [pg_cells pg_kind] in Hcell.
    rewrite Ec in Hcell. change (iof_list (@nil (int * cell))) with (@iempty cell) in Hcell.
    rewrite iget_iempty, Ek in Hcell. inversion Hcell; subst v.
    pose proof (zero_cov_sound segs facts rho ms Hfacts _ _ _ Ez (to_Z ci * 8 + Z.of_nat j) ltac:(rewrite EL8; lia)) as Hv.
    rewrite Epn in Hv.
    replace (to_Z (pd_pn p) * 4096 + (to_Z ci * 8 + Z.of_nat j))
      with (to_Z (pd_pn p) * 4096 + to_Z ci * 8 + Z.of_nat j) in Hv by lia.
    rewrite Hv. symmetry. apply (ho_dv_fv0_bytes rho Hrho0). exact Hj.
  - intros ci sl _ Hget. unfold page_of in Hget. cbn [pg_cells] in Hget. rewrite Ec in Hget.
    change (iof_list (@nil (int * cell))) with (@iempty cell) in Hget.
    rewrite iget_iempty in Hget. discriminate Hget.
Qed.

(* [comment removed for export] *)
Lemma region_ok_b2_sound : forall d r,
  region_ok_b2 IM facts d r = true ->
  region_ok rho (rd_tag r) (region_of r)
  /\ forall pn pg, to_Z pn < 2 ^ 50 -> page_at IM (region_of r) (rd_tag r) pn = Some pg ->
       page_ok segs IM rho (ms_mem ms) (rd_tag r) pn (clim (region_of r) pn) pg
       /\ to_Z (rg_lo (region_of r)) <= to_Z pn * 4096
       /\ to_Z pn * 4096 < to_Z (rg_len (region_of r))
       /\ (to_Z pn * 4096 + 4096 <= to_Z (rg_len (region_of r)) \/ to_Z (rg_len (region_of r)) mod 8 = 0).
Proof.
  intros d r H. unfold region_ok_b2 in H. rewrite !andb_true_iff in H.
  destruct H as [[[Hfact _] Hpages] Hrest].
  split; [apply (region_fact_b_sound segs facts rho ms Hrho0 Hfacts); exact Hfact |].
  intros pn pg Hpn Hpa.
  assert (Hwhole : forall pg', page_ok segs IM rho (ms_mem ms) (rd_tag r) pn 512 pg'
            /\ to_Z (rd_lo r) <= to_Z pn * 4096 /\ to_Z pn * 4096 + 4096 <= to_Z (rd_len r) ->
            page_ok segs IM rho (ms_mem ms) (rd_tag r) pn (clim (region_of r) pn) pg'
            /\ to_Z (rd_lo r) <= to_Z pn * 4096 /\ to_Z pn * 4096 < to_Z (rd_len r)
            /\ (to_Z pn * 4096 + 4096 <= to_Z (rd_len r) \/ to_Z (rd_len r) mod 8 = 0)).
  { intros pg' (Hok & Hl & Hu).
    assert (Ec : clim (region_of r) pn = 512).
    { unfold clim. cbn [region_of rg_len]. apply Z.min_l. clear - Hu. Z.div_mod_to_equations. lia. }
    rewrite Ec. split; [exact Hok|]. split; [exact Hl|]. split; [lia | left; exact Hu]. }
  cbn [region_of rg_lo rg_len].
  unfold page_at in Hpa. cbn [region_of rg_pages rg_dflt] in Hpa.
  destruct (iget pn (iof_list (map (fun p => (pd_pn p, page_of p)) (rd_pages r)))) as [pg0 |] eqn:Eg.
  - (* [comment removed for export] *)
    inversion Hpa; subst pg0. clear Hpa.
    destruct (iget_iof_list_map_In pd_pn page_of _ _ _ Eg) as (p & Hp & Hk & ->). subst pn.
    rewrite forallb_forall in Hpages. exact (page_ok_b2_sound r p (Hpages p Hp)).
  - assert (Hexp : explicit_b r pn = false).
    { unfold explicit_b. destruct (existsb (fun p => (pd_pn p =? pn)%uint63) (rd_pages r)) eqn:E; [| reflexivity].
      apply existsb_exists in E as (p & Hp & Hk). apply ho_eqb_eq in Hk.
      exfalso. exact (iget_iof_list_map_None pd_pn page_of _ _ Eg p Hp Hk). }
    destruct (rd_tag r =? 0)%uint63 eqn:Et.
    + apply ho_eqb_eq in Et. apply andb_true_iff in Hrest as [Himg Hdf].
      destruct (find_seg IM (pn << 12)%uint63) as [sg |] eqn:Hf.
      * inversion Hpa; subst pg. apply Hwhole. rewrite Et.
        exact (image_pages_ok_sound segs IM HIM HWR facts rho ms Hrho0 Hfacts r pn sg Himg Hpn Hf Hexp).
      * destruct (rd_dflt r); [discriminate Hdf | discriminate Hpa].
    + destruct (rd_dflt r) as [k |] eqn:Ek; [| discriminate Hpa].
      destruct (page_in_region (region_of r) pn) eqn:Epr; [| discriminate Hpa].
      inversion Hpa; subst pg. clear Hpa.
      apply page_in_region_spec in Epr as (_ & Hlo & Hup & Hal & _). cbn [region_of rg_lo rg_len] in Hlo, Hup, Hal.
      split; [| split; [exact Hlo | split; [exact Hup | exact Hal]]].
      assert (HL : clim (region_of r) pn <= 512 /\ to_Z pn * 4096 + 8 * clim (region_of r) pn <= to_Z (rd_len r)).
      { unfold clim. cbn [region_of rg_len]. clear - Hup. Z.div_mod_to_equations. lia. }
      destruct k.
      * rewrite !andb_true_iff in Hrest. destruct Hrest as [[Hle Hwr] Hz].
        apply (default_page_ok segs IM facts rho ms Hrho0 Hfacts _ (rd_lo r) (rd_len r) pn PKZero Hle Hwr);
          [right; split; [reflexivity | exact Hz] | exact Hpn | exact Hlo | exact (proj1 HL) | exact (proj2 HL)].
      * discriminate Hrest.
      * rewrite !andb_true_iff in Hrest. destruct Hrest as [Hle Hwr].
        apply (default_page_ok segs IM facts rho ms Hrho0 Hfacts _ (rd_lo r) (rd_len r) pn PKUnk Hle Hwr);
          [left; reflexivity | exact Hpn | exact Hlo | exact (proj1 HL) | exact (proj2 HL)].
Qed.
End Facts2.

Theorem handoff_R2 : forall facts d rho ms,
  ho_check2 IM facts d = true ->
  rho 0%uint63 = Z_to_bv 64 0 ->
  Forall (hholds segs rho ms) facts ->
  ms_pc_val ms = Z_to_bv 64 (to_Z (sd_pc d)) ->
  ms_svc_pending ms = None ->
  ms_resv ms = None ->
  R segs IM rho (state_of d) ms.
Proof.
  intros facts d rho ms Hc Hrho0 Hfacts Hpc Hsvc Hresv.
  unfold ho_check2 in Hc. apply andb_true_iff in Hc as [Hregs Hmem].
  rewrite forallb_forall in Hmem.
  constructor.
  - exact Hpc.
  - intros r. exact (regs_ok_b_sound segs facts rho ms Hrho0 Hfacts d r Hregs).
  - exact Hsvc.
  - rewrite Hresv. reflexivity.
  - cbn [state_of f_mem]. split.
    + intros t rg Hget.
      destruct (iget_iof_list_map_In rd_tag region_of _ _ _ Hget) as (r & Hr & Ht & ->). subst t.
      exact (region_ok_b2_sound facts rho ms Hrho0 Hfacts d r (Hmem r Hr)).
    + intros t t' rg rg' Hne Hget Hget'.
      destruct (iget_iof_list_map_In rd_tag region_of _ _ _ Hget) as (r & Hr & Ht & ->).
      destruct (iget_iof_list_map_In rd_tag region_of _ _ _ Hget') as (r' & Hr' & Ht' & ->).
      subst t t'. cbn [region_of rg_len rg_lo].
      pose proof (Hmem r Hr) as Hrb. unfold region_ok_b2 in Hrb. rewrite !andb_true_iff in Hrb.
      destruct Hrb as [[[_ Hdisj] _] _]. rewrite forallb_forall in Hdisj.
      specialize (Hdisj r' Hr'). apply orb_true_iff in Hdisj as [Heq | Hd].
      * apply ho_eqb_eq in Heq. congruence.
      * exact (disj_fact_b_sound segs facts rho ms Hfacts r r' Hd).
Qed.

Theorem handoff_Rn2 : forall facts d n rho ms,
  ho_check2 IM facts d = true ->
  forallb (fact_tags_lt n) facts = true ->
  rho 0%uint63 = Z_to_bv 64 0 ->
  Forall (hholds segs rho ms) facts ->
  ms_pc_val ms = Z_to_bv 64 (to_Z (sd_pc d)) ->
  ms_svc_pending ms = None ->
  ms_resv ms = None ->
  Rn segs IM n rho (state_of d) ms.
Proof.
  intros facts d n rho ms Hc Hlt Hrho Hf Hpc Hsvc Hresv rho' Hag.
  apply (handoff_R2 facts d rho' ms Hc (proj1 Hag)); [|exact Hpc|exact Hsvc|exact Hresv].
  rewrite Forall_forall in *. intros f Hin.
  apply (hholds_agree segs n rho rho' ms f Hag); [|apply Hf; exact Hin].
  rewrite forallb_forall in Hlt. apply Hlt. exact Hin.
Qed.
End Sound2.
