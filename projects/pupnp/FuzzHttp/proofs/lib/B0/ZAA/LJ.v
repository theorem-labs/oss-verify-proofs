(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac ITree Nodes Decode SysStep Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation implA H t Q ms := (ITreeLZ.implL asegs (at_nodeL asegs) hideL H t (epostL Q) ms).

Lemma a0_wx : wx_segs_nowrap asegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Definition mclean (H : word -> bool) (m : word -> option byte) : Prop :=
  (forall x, H x = true -> m x = None) /\ H_off_segments asegs H.

Lemma mclean_some H m x b : mclean H m -> m x = Some b -> H x = false.
Proof. intros [C _] E. destruct (H x) eqn:HX; [| reflexivity]. rewrite (C x HX) in E. discriminate. Qed.

Lemma mclean_unhide H m lo hi : mclean H m -> mclean (unhide_range lo hi H) m.
Proof.
  intros [C O]. split; intros x Hx; unfold unhide_range in Hx; apply andb_prop in Hx as [Hx _]; auto.
Qed.

Definition fixed_eff (addr len : Z) : resp := mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, lenW len)].

Definition resp_eqb (e1 e2 : resp) : bool :=
  match e1, e2 with
  | mkEffectU r1 ws1 zs1 us1 cs1 _, mkEffectU r2 ws2 zs2 us2 cs2 _ =>
      bv_eqb r1 r2 &&
      match ws1, ws2 with [], [] => true | _, _ => false end &&
      match zs1, zs2 with
      | [], [] => true
      | [(a1, n1)], [(a2, n2)] => bv_eqb a1 a2 && bv_eqb n1 n2
      | _, _ => false
      end &&
      match us1, us2 with
      | [], [] => true
      | [(a1, n1)], [(a2, n2)] => bv_eqb a1 a2 && bv_eqb n1 n2
      | _, _ => false
      end &&
      match cs1, cs2 with [], [] => true | _, _ => false end
  end.

Definition dec_fixed (addr len : Z) (rsp : resp) : option unit :=
  if resp_eqb (strip rsp) (fixed_eff addr len) then Some tt else None.

Definition t_commit (addr len : Z) : itree nodeL (exc unit) := enode (LMmapCommit addr len SHADOW_OFF) (dec_fixed addr len).
Definition t_remap (addr len : Z) : itree nodeL (exc unit) := enode (LMmapFixed addr len MAPF_FIXED_NR) (dec_fixed addr len).

Definition madv_eff (addr len : Z) : resp := mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, lenW len)].
Definition dec_madv (addr len : Z) (rsp : resp) : option unit :=
  if resp_eqb (strip rsp) (madv_eff addr len) then Some tt else None.
Definition t_madv (addr len : Z) : itree nodeL (exc unit) := enode (LMadvise addr len) (dec_madv addr len).

Fixpoint avoids_all (a n : Z) (avoid : list (Z * Z)) : bool :=
  match avoid with
  | [] => true
  | (lo, hi) :: rest => ((a + n <=? lo) || (hi <=? a)) && avoids_all a n rest
  end.

Definition app_memb (a n : Z) : bool := (a + n <? 0x7fff8000) || ((0x10007fff8000 <=? a) && (a + n <? 2^47)).

Definition anon_place {HC : HasCeiling} (a n : Z) : Prop :=
  ((0 <= a /\ a + n < 0x7fff8000) \/ 0x10007fff8000 <= a) /\ a + n <= alloc_ceiling.

Lemma anon_place_app_mem {HC : HasCeiling} : forall a n, anon_place a n -> app_mem a n.
Proof. intros a n [L T]. pose proof (@alloc_ceiling_lt47 HC). unfold app_mem. lia. Qed.

Definition dec_anon {HC : HasCeiling} (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option Z :=
  let a := bv_unsigned (eff_ret rsp) in
  if resp_eqb (strip rsp) (mkEffect (eff_ret rsp) [] [(eff_ret rsp, lenW len)])
     && (a mod 4096 =? 0) && (0x609000 <=? a) && app_memb a (lenZ len) && (a + lenZ len <=? alloc_ceiling)
     && avoids_all a (lenZ len) avoid
  then Some a else None.

Definition t_anon {HC : HasCeiling} (len : Z) (avoid : list (Z * Z)) : itree nodeL (exc Z) := enode (LMmapHeap len SHADOW_OFF) (dec_anon len avoid).

Definition dec_unmapu (addr len : Z) (rsp : resp) : option unit :=
  match dec_munmap addr len rsp with Some (RgDone true) => Some tt | _ => None end.

Definition t_unmap (addr len : Z) : itree nodeL (exc unit) := enode (LNode (NMunmap addr len)) (dec_unmapu addr len).

Lemma implA_ret {A} : forall H (Q : A -> (word -> bool) -> machine_state -> Prop) a ms,
  evt asegs (Q a H) ms -> implA H (Ret (Ok a)) Q ms.
Proof. intros. apply implL_ret_ok. assumption. Qed.

Lemma implA_evt {A} : forall H (t : itree nodeL (exc A)) Q P ms,
  evt asegs P ms -> (forall ms', P ms' -> implA H t Q ms') -> implA H t Q ms.
Proof. intros. eapply implL_evt; eauto. Qed.

Lemma implA_ebind {A B} : forall H (t : itree nodeL (exc A)) (f : A -> itree nodeL (exc B)) Q1 Q ms,
  implA H t Q1 ms -> (forall a H' ms', Q1 a H' ms' -> implA H' (f a) Q ms') -> implA H (ebind t f) Q ms.
Proof. intros. eapply implL_ebind; eauto. Qed.

Lemma implA_mono {A} : forall H (t : itree nodeL (exc A)) Q Q' ms,
  implA H t Q ms -> (forall a H' ms', Q a H' ms' -> Q' a H' ms') -> implA H t Q' ms.
Proof. intros. eapply implL_epost_mono; eauto. Qed.

Lemma evt_mclean : forall H P R F pc fc rv m ro,
  mclean H m -> evt asegs P (MS R F pc fc rv m ro) ->
  evt asegs (fun ms' => P ms' /\ mclean H (ms_mem ms')) (MS R F pc fc rv m ro).
Proof.
  intros H P R F pc fc rv m ro [C O] (ms' & HM & HP). exists ms'. split; [exact HM|]. split; [exact HP|].
  split; [| exact O]. intros x Hx.
  exact (msteps_hclean asegs H O a0_wx _ _ (msteps_cat asegs _ _ HM) (fun y Hy => C y Hy) x Hx).
Qed.

Lemma unhide_range_sub lo hi H x : unhide_range lo hi H x = true -> H x = true.
Proof. unfold unhide_range. intros E. apply andb_prop in E as [E _]. exact E. Qed.

Lemma unhide_zb_sub lo hi H x : unhide_zb lo hi H x = true -> H x = true.
Proof. unfold unhide_zb. intros E. apply andb_prop in E as [E _]. exact E. Qed.

Lemma hideL_sub n rsp H x : (forall a l, n <> LMadvise a l) -> hideL n rsp H x = true -> H x = true.
Proof.
  intros NM. destruct n as [n|len off|len|addr len flags|addr len off|addr len]; cbn [hideL].
  - destruct n; try (intros E; exact E); try (destruct (ret_alignedb rsp)); intros E; try exact E;
      eapply unhide_range_sub; exact E.
  - destruct (ret_alignedb rsp); intros E; [| exact E]. apply unhide_zb_sub in E. apply unhide_range_sub in E. exact E.
  - destruct (ret_alignedb rsp); intros E; [| exact E]. apply unhide_range_sub in E. exact E.
  - intros E. apply unhide_range_sub in E. exact E.
  - intros E. apply unhide_zb_sub in E. apply unhide_range_sub in E. exact E.
  - exfalso. exact (NM addr len eq_refl).
Qed.

Lemma mclean_nretL n rsp H ms1 : at_nodeL asegs n ms1 ->
  mclean H (ms_mem ms1) -> mclean (hideL n rsp H) (ms_mem (nretL nodeL hideL n rsp H ms1)).
Proof.
  intros Hat [C O]. split.
  - intros x Hx. unfold nretL. cbn [restrict ms_mem]. unfold mrestrict. rewrite Hx. reflexivity.
  - intros x Hx. destruct n as [n|len off|len|addr len flags|addr len off|addr len].
    6: { cbn [hideL] in Hx. unfold hide_range in Hx. apply orb_prop in Hx as [Hx|Hx]; [exact (O x Hx)|].
         cbn [at_nodeL] in Hat. destruct Hat as (_ & _ & Hpos & Hub & Hoff). apply Hoff.
         unfold in_rangeb in Hx. apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
         assert (EA : addrZ addr = addr) by (unfold addrZ; rewrite unsigned_lit by lia; reflexivity). rewrite EA in *. lia. }
    all: apply O; eapply hideL_sub; [| exact Hx]; intros a l E; discriminate E.
Qed.

Lemma evt_mclean_ms : forall H P ms,
  mclean H (ms_mem ms) -> evt asegs P ms -> evt asegs (fun ms' => P ms' /\ mclean H (ms_mem ms')) ms.
Proof.
  intros H P ms [C O] (ms' & HM & HP). exists ms'. split; [exact HM|]. split; [exact HP|].
  split; [| exact O]. intros x Hx.
  exact (msteps_hclean asegs H O a0_wx _ _ (msteps_cat asegs _ _ HM) (fun y Hy => C y Hy) x Hx).
Qed.

Lemma implA_mclean {A} : forall (t : itree nodeL (exc A)) H Q ms,
  mclean H (ms_mem ms) -> implA H t Q ms -> implA H t (fun a H' ms' => Q a H' ms' /\ mclean H' (ms_mem ms')) ms.
Proof.
  induction t as [r|n k IH]; intros H Q ms C HI; cbn in HI |- *.
  - pose proof (evt_mclean_ms H _ ms C HI) as E. eapply evt_mono; [exact E|]. intros ms' [HQ C']. destruct r; cbn in *; auto.
  - pose proof (evt_mclean_ms H _ ms C HI) as E. eapply evt_mono; [exact E|]. intros ms1 [[Hat Hk] C1].
    split; [exact Hat|]. intros rsp. apply IH; [apply mclean_nretL; [exact Hat| exact C1]| apply Hk].
Qed.

Lemma restrict_MS H R F pc fc rv m ro : restrict H (MS R F pc fc rv m ro) = MS R F pc fc rv (mrestrict H m) ro.
Proof. reflexivity. Qed.
Lemma reveal_MSsvc S R F pc x17 fc rv m ro : reveal S (MSsvc R F pc x17 fc rv m ro) = MSsvc R F pc x17 fc rv (mreveal S m) ro.
Proof. reflexivity. Qed.

Lemma nretL_MSsvc : forall n rsp H R F pc x17 fc rv m ro r ws zs us,
  strip rsp = mkEffectU r ws zs us [] [] ->
  nretL nodeL hideL n rsp H (MSsvc R F pc x17 fc rv m ro)
  = MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4)%bv fc rv
       (mrestrict (hideL n rsp H) (apply_writes (apply_zeros (apply_unmaps (mreveal (unhidden H (hideL n rsp H)) m) us) zs) ws)) ro.
Proof.
  intros n rsp H R F pc x17 fc rv m ro r ws zs us Hs. unfold nretL. rewrite reveal_MSsvc, <- nret_strip, Hs, nret_MSsvc. reflexivity.
Qed.

Definition wreveal (H : word -> bool) (lo hi : Z) (m : word -> option byte) : word -> option byte :=
  fun x => if in_rangeb lo hi x && H x then Some (Z_to_bv 8 0) else m x.

Lemma in_rangeb_in_range lo hi x : in_rangeb lo hi x = in_range lo (hi - lo) x.
Proof. unfold in_rangeb, in_range. f_equal. apply (f_equal (fun z => bv_unsigned x <? z)). lia. Qed.

Lemma unhide_range_false : forall lo hi Hh x, Hh x = false -> unhide_range lo hi Hh x = false.
Proof. intros lo hi Hh x E. unfold unhide_range. rewrite E. reflexivity. Qed.

Lemma unhide_range_in : forall a b Hh x, a <= bv_unsigned x < b -> unhide_range a b Hh x = false.
Proof.
  intros a b Hh x Hx. unfold unhide_range, in_rangeb.
  rewrite (proj2 (Z.leb_le a (bv_unsigned x))) by lia. rewrite (proj2 (Z.ltb_lt (bv_unsigned x) b)) by lia.
  cbn [negb]. apply andb_false_r.
Qed.

Lemma lfixed_mem_eq : forall H m addr len,
  mclean H m -> 0 < addr -> addr + lenZ len <= 2^64 -> 0 < lenZ len ->
  let H' := unhide_range (addrZ addr) (addrZ addr + lenZ len) H in
  mrestrict H' (apply_writes (apply_zeros (apply_unmaps (mreveal (unhidden H H') m) []) [(Z_to_bv 64 addr, lenW len)]) [])
  = apply_zeros m [(Z_to_bv 64 addr, lenW len)].
Proof.
  intros H m addr len C A0 AL L0 H'. apply functional_extensionality. intros x.
  cbn [apply_writes apply_unmaps]. unfold lenW. change (Z_to_bv 64 addr) with (wa addr).
  assert (EA : addrZ addr = addr) by (unfold addrZ; rewrite unsigned_lit by lia; reflexivity).
  unfold mrestrict, mreveal, unhidden. subst H'. unfold unhide_range. rewrite EA.
  rewrite !apply_zeros_spec by lia. rewrite in_rangeb_in_range. replace (addr + lenZ len - addr) with (lenZ len) by lia.
  destruct (in_range addr (lenZ len) x) eqn:IR; cbn [negb andb].
  - rewrite andb_false_r. reflexivity.
  - rewrite andb_true_r. destruct (H x) eqn:HX; cbn; [| reflexivity]. symmetry. apply (proj1 C). exact HX.
Qed.

Lemma lunmap_mem_eq : forall H m addr len,
  mclean H m -> 0 < addr -> addr + lenZ len <= 2^64 -> 0 < lenZ len ->
  let H' := unhide_range (addrZ addr) (addrZ addr + lenZ len) H in
  mrestrict H' (apply_writes (apply_zeros (apply_unmaps (mreveal (unhidden H H') m) [(Z_to_bv 64 addr, lenW len)]) []) [])
  = apply_unmaps m [(Z_to_bv 64 addr, lenW len)].
Proof.
  intros H m addr len C A0 AL L0 H'. apply functional_extensionality. intros x.
  cbn [apply_writes apply_zeros]. unfold lenW. change (Z_to_bv 64 addr) with (wa addr).
  assert (EA : addrZ addr = addr) by (unfold addrZ; rewrite unsigned_lit by lia; reflexivity).
  unfold mrestrict, mreveal, unhidden. subst H'. unfold unhide_range. rewrite EA.
  rewrite !apply_unmaps_spec by lia. rewrite in_rangeb_in_range. replace (addr + lenZ len - addr) with (lenZ len) by lia.
  destruct (in_range addr (lenZ len) x) eqn:IR; cbn [negb andb].
  - rewrite andb_false_r. reflexivity.
  - rewrite andb_true_r. destruct (H x) eqn:HX; cbn; [| reflexivity]. symmetry. apply (proj1 C). exact HX.
Qed.

Lemma lheap_mem_eq : forall H m (a : Z) len wlo whi,
  mclean H m -> 0 < a -> a + lenZ len <= 2^64 -> 0 < lenZ len ->
  let H' := unhide_range wlo whi (unhide_range a (a + lenZ len) H) in
  mrestrict H' (apply_writes (apply_zeros (apply_unmaps (mreveal (unhidden H H') m) []) [(Z_to_bv 64 a, lenW len)]) [])
  = apply_zeros (wreveal H wlo whi m) [(Z_to_bv 64 a, lenW len)].
Proof.
  intros H m a len wlo whi C A0 AL L0. cbv zeta. apply functional_extensionality. intros x.
  cbn [apply_writes apply_unmaps]. unfold lenW. change (Z_to_bv 64 a) with (wa a).
  unfold mrestrict, mreveal, unhidden, wreveal, unhide_range.
  rewrite !apply_zeros_spec by lia. rewrite (in_rangeb_in_range a).
  replace (a + lenZ len - a) with (lenZ len) by lia. rewrite in_rangeb_in_range.
  destruct (in_range a (lenZ len) x) eqn:IR; cbn [negb andb].
  - rewrite !andb_false_r. cbn [andb]. reflexivity.
  - rewrite !andb_true_r. destruct (H x) eqn:HX; cbn [andb negb].
    + destruct (in_range wlo (whi - wlo) x); cbn; [reflexivity|]. symmetry. apply (proj1 C). exact HX.
    + rewrite andb_false_r. reflexivity.
Qed.

Definition A0_IMG_LO : Z := 0x10000.
Definition A0_RO_HI : Z := 0xaa000.
Definition A0_IMG_HI : Z := 0x609000.

Lemma a0_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x609000 <= z) -> find_segment asegs z n = None.
Proof.
  intros z n Hn Hz. unfold asegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_000)) with 0x10000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_000)) with 0x22000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_001)) with 0x32000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_001)) with 0x78000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_002)) with 0xaa000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_002)) with 0x2000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_003)) with 0xac000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_003)) with 0x55d000 by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x22000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x32000 z); destruct (Z.leb_spec0 (z + n) (0x32000 + 0x78000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xaa000 z); destruct (Z.leb_spec0 (z + n) (0xaa000 + 0x2000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xac000 z); destruct (Z.leb_spec0 (z + n) (0xac000 + 0x55d000)); cbn [andb]; try lia.
  all: reflexivity.
Qed.

Lemma a0_ro_addr_false : forall x : word, (bv_unsigned x + 1 <= 0x10000 \/ 0xaa000 <= bv_unsigned x) -> ro_addr asegs x = false.
Proof.
  intros x Hx. unfold ro_addr, asegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_000)) with 0x10000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_000)) with 0x22000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_001)) with 0x32000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_001)) with 0x78000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_002)) with 0xaa000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_002)) with 0x2000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_003)) with 0xac000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_003)) with 0x55d000 by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0x10000 + 0x22000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x32000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0x32000 + 0x78000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xaa000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0xaa000 + 0x2000)); cbn [andb].
  all: try (destruct (Z.leb_spec0 0xac000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0xac000 + 0x55d000)); cbn [andb]).
  all: first [reflexivity | vm_compute; reflexivity].
Qed.

Lemma a0_seg_rom_none : forall x : word, 0x609000 <= bv_unsigned x -> seg_rom asegs x = None.
Proof. intros x Hx. unfold seg_rom, memory_read. rewrite a0_find_segment_none by (cbn; lia). reflexivity. Qed.

Definition mgrow (m m' : word -> option byte) : Prop :=
  forall x, m' x = m x \/ (m x = None /\ seg_rom asegs x = None /\ ro_addr asegs x = false /\ exists b, m' x = Some b).

Section Grow.
Variables (m m' : word -> option byte).
Hypothesis G : mgrow m m'.

#[using="G"] Lemma mrd_grow : forall x b, mrd asegs m x = Some b -> mrd asegs m' x = Some b.
Proof.
  intros x b Hr. unfold mrd in *. destruct (G x) as [E|(E0 & R0 & _ & b' & E')]; [rewrite E; exact Hr|].
  rewrite E0, R0 in Hr. discriminate.
Qed.

#[using="G"] Lemma wview_grow : forall x, wview asegs m x <> None -> wview asegs m' x <> None.
Proof.
  intros x Hw. unfold wview in *. destruct (G x) as [E|(E0 & R0 & _ & b' & E')]; [rewrite E; exact Hw|]. rewrite E'. discriminate.
Qed.

#[using="G"] Lemma bytes_at_grow : forall A bs, bytes_at asegs m A bs -> bytes_at asegs m' A bs.
Proof.
  intros A bs (H0 & H1 & HB). split; [lia|]. split; [lia|]. intros i Hi.
  specialize (HB i Hi). destruct (nth_error bs i) as [b|] eqn:E; [exact (mrd_grow _ _ HB)|].
  exfalso. apply nth_error_None in E. lia.
Qed.

#[using="G"] Lemma wr_at_grow : forall A k, wr_at asegs m A k -> wr_at asegs m' A k.
Proof. intros A k (H0 & H1 & HW). split; [lia|]. split; [lia|]. intros i Hi. apply wview_grow, HW, Hi. Qed.

#[using="G"] Lemma rw_cells_grow : forall A cs, rw_cells asegs m A cs -> rw_cells asegs m' A cs.
Proof. intros A cs [[Hwf HB] HW]. split; [split; [exact Hwf| apply bytes_at_grow; exact HB]| apply wr_at_grow; exact HW]. Qed.

#[using="G"] Lemma ro_cells_grow : forall A cs, ro_cells asegs m A cs -> ro_cells asegs m' A cs.
Proof. intros A cs [Hwf HB]. split; [exact Hwf| apply bytes_at_grow; exact HB]. Qed.

#[using="G"] Lemma u8arr_grow : forall A bs, u8arr asegs m A bs -> u8arr asegs m' A bs.
Proof. intros A bs [HB HW]. split; [apply bytes_at_grow; exact HB| apply wr_at_grow; exact HW]. Qed.
#[using="G"] Lemma u32arr_grow : forall A ws, u32arr asegs m A ws -> u32arr asegs m' A ws.
Proof. intros A ws [HB HW]. split; [apply bytes_at_grow; exact HB| apply wr_at_grow; exact HW]. Qed.
#[using="G"] Lemma u64arr_grow : forall A ws, u64arr asegs m A ws -> u64arr asegs m' A ws.
Proof. intros A ws [HB HW]. split; [apply bytes_at_grow; exact HB| apply wr_at_grow; exact HW]. Qed.

#[using="G"] Lemma stk_grow : forall lo hi, stk asegs m lo hi -> stk asegs m' lo hi.
Proof.
  intros lo hi (H0 & H1 & HS). split; [lia|]. split; [lia|]. intros a Ha. destruct (HS a Ha) as [Hw (b & Hb)].
  split; [apply wview_grow; exact Hw| exists b; apply mrd_grow; exact Hb].
Qed.

#[using="G"] Lemma wmono_grow : forall m0, wmono asegs m0 m -> wmono asegs m0 m'.
Proof. intros m0 WM x Hx. apply wview_grow, WM, Hx. Qed.

#[using="G"] Lemma mem_inv_grow : mem_inv asegs m -> mem_inv asegs m'.
Proof.
  intros MI x b Hx. destruct (G x) as [E|(E0 & R0 & NR & b' & E')]; [| exact NR]. rewrite E in Hx. exact (MI x b Hx).
Qed.
End Grow.

Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma munch_extend : forall W W' m0 m, munch W m0 m -> munch (W ++ W') m0 m.
Proof. intros W W' m0 m MU x Hx. apply outside_app in Hx as [Hx _]. exact (MU x Hx). Qed.

Lemma gmunch_refl : forall W m, gmunch W m m.
Proof. intros W m x _. left. reflexivity. Qed.
Lemma gmunch_of_munch : forall W m m', munch W m m' -> gmunch W m m'.
Proof. intros W m m' MU x Hx. left. exact (MU x Hx). Qed.
Lemma gmunch_of_mgrow : forall W m m', mgrow m m' -> gmunch W m m'.
Proof. intros W m m' G x _. destruct (G x) as [E|(E0 & R0 & NR & _)]; [left; exact E| right; auto]. Qed.
Lemma gmunch_trans : forall W m1 m2 m3, gmunch W m1 m2 -> gmunch W m2 m3 -> gmunch W m1 m3.
Proof.
  intros W m1 m2 m3 G1 G2 x Hx. destruct (G1 x Hx) as [E1|R1]; destruct (G2 x Hx) as [E2|(E0 & R0 & NR)].
  - left. rewrite E2. exact E1.
  - right. rewrite <- E1. auto.
  - destruct R1 as (E0 & R0 & NR). destruct (m3 x) eqn:E3; [| left; rewrite E0; reflexivity]. right. auto.
  - right. exact R1.
Qed.
Lemma gmunch_weaken : forall W W' m m', sub_fp W W' -> gmunch W m m' -> gmunch W' m m'.
Proof. intros W W' m m' Hs G x Hx. apply G. apply Hs. exact Hx. Qed.
Lemma gmunch_extend : forall W W' m0 m, gmunch W m0 m -> gmunch (W ++ W') m0 m.
Proof. intros W W' m0 m G x Hx. apply outside_app in Hx as [Hx _]. exact (G x Hx). Qed.

Lemma gmunch_join : forall W1 W2 m0 m m', gmunch W1 m0 m -> gmunch W2 m m' -> gmunch (W1 ++ W2) m0 m'.
Proof.
  intros W1 W2 m0 m m' G1 G2. eapply gmunch_trans; [eapply gmunch_weaken; [| exact G1] | eapply gmunch_weaken; [| exact G2]];
    intros x Hx; apply outside_app in Hx; tauto.
Qed.
Lemma gmunch_munch : forall W1 W2 m0 m m', gmunch W1 m0 m -> munch W2 m m' -> gmunch (W1 ++ W2) m0 m'.
Proof. intros W1 W2 m0 m m' G MU. eapply gmunch_join; [exact G| apply gmunch_of_munch; exact MU]. Qed.

Lemma gmunch_munch_in : forall W Wc m0 m m', gmunch W m0 m -> munch Wc m m' -> sub_fp Wc W -> gmunch W m0 m'.
Proof. intros W Wc m0 m m' G MU Hs. eapply gmunch_trans; [exact G|]. apply gmunch_of_munch. eapply munch_weaken; eauto. Qed.
Lemma gmunch_write : forall W m0 m a bs,
  gmunch W m0 m -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> inside W a (Z.of_nat (length bs)) ->
  gmunch W m0 (write_to_mem m (wa a) bs).
Proof.
  intros W m0 m a bs G Ha Hl Hin. eapply gmunch_trans; [exact G|]. apply gmunch_of_munch.
  apply munch_write; [apply munch_refl| exact Ha| exact Hl| exact Hin].
Qed.

Section GTransport.
Variables (W : list (Z * Z)) (m m' : word -> option byte).
Hypothesis G : gmunch W m m'.

#[using="G"] Lemma mrd_gkeep : forall x b, outside W (bv_unsigned x) -> mrd asegs m x = Some b -> mrd asegs m' x = Some b.
Proof.
  intros x b Hx Hr. unfold mrd in *. destruct (G x Hx) as [E|(E0 & R0 & _)]; [rewrite E; exact Hr|].
  rewrite E0, R0 in Hr. discriminate.
Qed.

#[using="G"] Lemma bytes_at_gtransport0 : forall A bs, bytes_at asegs m A bs -> disjoint_from W A (Z.of_nat (length bs)) -> bytes_at asegs m' A bs.
Proof.
  intros A bs (Ha & Hl & Hb) Hd. split; [lia|]. split; [lia|]. intros i Hi.
  pose proof (Hb i Hi) as Hr. destruct (nth_error bs i) as [b|] eqn:En; [| exfalso; apply nth_error_None in En; lia].
  apply mrd_gkeep; [| exact Hr]. eapply disjoint_outside; [exact Hd|]. rewrite wa_unsigned by lia. lia.
Qed.
#[using="G"] Lemma rw_cells_gtransport0 : forall A cs, rw_cells asegs m A cs -> wmono asegs m m' -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
Proof.
  intros A cs [[Hwf Hb] Hw] WM Hd. split; [split; [exact Hwf|]|].
  - apply bytes_at_gtransport0; [exact Hb|]. rewrite (cells_bytes_length cs Hwf). exact Hd.
  - eapply wr_at_transport; eauto.
Qed.
#[using="G"] Lemma ro_cells_gtransport0 : forall A cs, ro_cells asegs m A cs -> disjoint_from W A (Z.of_nat (cells_size cs)) -> ro_cells asegs m' A cs.
Proof.
  intros A cs [Hwf Hb] Hd. split; [exact Hwf|]. apply bytes_at_gtransport0; [exact Hb|]. rewrite (cells_bytes_length cs Hwf). exact Hd.
Qed.
#[using="G"] Lemma u8arr_gtransport0 : forall A bs, u8arr asegs m A bs -> wmono asegs m m' -> disjoint_from W A (Z.of_nat (length bs)) -> u8arr asegs m' A bs.
Proof. intros A bs [Hb Hw] WM Hd. split; [apply bytes_at_gtransport0; assumption| eapply wr_at_transport; eauto]. Qed.
#[using="G"] Lemma u32arr_gtransport0 : forall A ws, u32arr asegs m A ws -> wmono asegs m m' -> disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr asegs m' A ws.
Proof.
  intros A ws [Hb Hw] WM Hd. split; [| eapply wr_at_transport; eauto].
  apply bytes_at_gtransport0; [exact Hb|]. rewrite u32s_length, Nat2Z.inj_mul. exact Hd.
Qed.
#[using="G"] Lemma u64arr_gtransport0 : forall A ws, u64arr asegs m A ws -> wmono asegs m m' -> disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
Proof.
  intros A ws [Hb Hw] WM Hd. split; [| eapply wr_at_transport; eauto].
  apply bytes_at_gtransport0; [exact Hb|]. rewrite u64s_length, Nat2Z.inj_mul. exact Hd.
Qed.
#[using="G"] Lemma u8ro_gtransport0 : forall A bs, u8ro asegs m A bs -> disjoint_from W A (Z.of_nat (length bs)) -> u8ro asegs m' A bs.
Proof. intros A bs Hb Hd. apply bytes_at_gtransport0; assumption. Qed.
#[using="G"] Lemma stk_gtransport0 : forall lo hi, stk asegs m lo hi -> wmono asegs m m' -> disjoint_from W lo (hi - lo) -> stk asegs m' lo hi.
Proof.
  intros lo hi (H1 & H2 & Hs) WM Hd. split; [lia|]. split; [lia|]. intros a Ha. destruct (Hs a Ha) as [Hw [b Hb]]. split.
  - apply WM. exact Hw.
  - exists b. apply mrd_gkeep; [| exact Hb]. eapply disjoint_outside; [exact Hd|]. rewrite wa_unsigned by lia. lia.
Qed.
End GTransport.

Lemma bytes_at_gtransport : forall W m m' A bs, bytes_at asegs m A bs -> gmunch W m m' -> disjoint_from W A (Z.of_nat (length bs)) -> bytes_at asegs m' A bs.
Proof. intros. eapply bytes_at_gtransport0; eauto. Qed.
Lemma rw_cells_gtransport : forall W m m' A cs, rw_cells asegs m A cs -> gmunch W m m' -> wmono asegs m m' -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
Proof. intros. eapply rw_cells_gtransport0; eauto. Qed.
Lemma ro_cells_gtransport : forall W m m' A cs, ro_cells asegs m A cs -> gmunch W m m' -> disjoint_from W A (Z.of_nat (cells_size cs)) -> ro_cells asegs m' A cs.
Proof. intros. eapply ro_cells_gtransport0; eauto. Qed.
Lemma u8arr_gtransport : forall W m m' A bs, u8arr asegs m A bs -> gmunch W m m' -> wmono asegs m m' -> disjoint_from W A (Z.of_nat (length bs)) -> u8arr asegs m' A bs.
Proof. intros. eapply u8arr_gtransport0; eauto. Qed.
Lemma u32arr_gtransport : forall W m m' A ws, u32arr asegs m A ws -> gmunch W m m' -> wmono asegs m m' -> disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr asegs m' A ws.
Proof. intros. eapply u32arr_gtransport0; eauto. Qed.
Lemma u64arr_gtransport : forall W m m' A ws, u64arr asegs m A ws -> gmunch W m m' -> wmono asegs m m' -> disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
Proof. intros. eapply u64arr_gtransport0; eauto. Qed.
Lemma u8ro_gtransport : forall W m m' A bs, u8ro asegs m A bs -> gmunch W m m' -> disjoint_from W A (Z.of_nat (length bs)) -> u8ro asegs m' A bs.
Proof. intros. eapply u8ro_gtransport0; eauto. Qed.
Lemma stk_gtransport : forall W m m' lo hi, stk asegs m lo hi -> gmunch W m m' -> wmono asegs m m' -> disjoint_from W lo (hi - lo) -> stk asegs m' lo hi.
Proof. intros. eapply stk_gtransport0; eauto. Qed.

Lemma munch_grow_in : forall W m0 m m' (lo hi : Z),
  munch W m0 m -> (forall x, m' x = m x \/ lo <= bv_unsigned x < hi) -> inside W lo (hi - lo) -> munch W m0 m'.
Proof.
  intros W m0 m m' lo hi MU G IN x Hx. destruct (G x) as [E|R]; [rewrite E; apply MU; exact Hx|].
  exfalso. eapply (inside_not_outside W lo (hi - lo) (bv_unsigned x) IN); [lia| exact Hx].
Qed.

Lemma wreveal_mgrow : forall H lo hi m, mclean H m -> 0x609000 <= lo -> mgrow m (wreveal H lo hi m).
Proof.
  intros H lo hi m C LO x. unfold wreveal.
  destruct (in_rangeb lo hi x) eqn:IR; cbn [andb]; [| left; reflexivity].
  destruct (H x) eqn:HX; [| left; reflexivity]. right.
  unfold in_rangeb in IR. apply andb_prop in IR as [I1 I2]. apply Z.leb_le in I1.
  split; [exact (proj1 C x HX)|]. split; [apply a0_seg_rom_none; lia|]. split; [apply a0_ro_addr_false; lia|]. eexists; reflexivity.
Qed.

Lemma wreveal_changed : forall H lo hi m x, wreveal H lo hi m x = m x \/ lo <= bv_unsigned x < hi.
Proof.
  intros H lo hi m x. unfold wreveal. destruct (in_rangeb lo hi x) eqn:IR; cbn [andb]; [| left; reflexivity].
  unfold in_rangeb in IR. apply andb_prop in IR as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
  destruct (H x); [right; lia| left; reflexivity].
Qed.

Lemma mclean_wreveal : forall H lo hi m a n, mclean H m ->
  mclean (unhide_range lo hi (unhide_range a n H)) (wreveal H lo hi m).
Proof.
  intros H lo hi m a n [C O]. split.
  - intros x Hx. unfold unhide_range in Hx. apply andb_prop in Hx as [Hx NW]. apply andb_prop in Hx as [Hx _].
    unfold wreveal. destruct (in_rangeb lo hi x); cbn [andb negb] in NW |- *; [discriminate| exact (C x Hx)].
  - intros x Hx. apply O. do 2 apply unhide_range_sub in Hx. exact Hx.
Qed.

Ltac transport_grow m m' G :=
  repeat match goal with
  | Hh : bytes_at asegs m ?A ?bs |- _ => apply (bytes_at_grow m m' G A bs) in Hh
  | Hh : wr_at asegs m ?A ?k |- _ => apply (wr_at_grow m m' G A k) in Hh
  | Hh : rw_cells asegs m ?A ?cs |- _ => apply (rw_cells_grow m m' G A cs) in Hh
  | Hh : ro_cells asegs m ?A ?cs |- _ => apply (ro_cells_grow m m' G A cs) in Hh
  | Hh : u8arr asegs m ?A ?xs |- _ => apply (u8arr_grow m m' G A xs) in Hh
  | Hh : u32arr asegs m ?A ?xs |- _ => apply (u32arr_grow m m' G A xs) in Hh
  | Hh : u64arr asegs m ?A ?xs |- _ => apply (u64arr_grow m m' G A xs) in Hh
  | Hh : stk asegs m ?lo ?hi |- _ => apply (stk_grow m m' G lo hi) in Hh
  | Hh : wmono asegs ?m0 m |- _ => apply (wmono_grow m m' G m0) in Hh
  | Hh : mem_inv asegs m |- _ => apply (mem_inv_grow m m' G) in Hh
  | Hh : gmunch ?W ?m0 m |- _ =>
      let Hh' := fresh "GMg" in pose proof (gmunch_trans W m0 m m' Hh (gmunch_of_mgrow W m m' G)) as Hh'; clear Hh; rename Hh' into Hh
  end.

Lemma gmunch_zeros_in : forall W m0 m a n (Ha : 0 <= a < 2^64) (Hn : 0 <= n < 2^64) (Han : a + n <= 2^64),
  gmunch W m0 m -> inside W a n -> gmunch W m0 (apply_zeros m [(wa a, Z_to_bv 64 n)]).
Proof.
  intros W m0 m a n Ha Hn Han G Hin. eapply gmunch_trans; [exact G|]. apply gmunch_of_munch.
  apply (munch_zeros m a n Ha Hn Han W m (munch_refl W m) Hin).
Qed.
Lemma gmunch_unmaps_in : forall W m0 m a n (Ha : 0 <= a < 2^64) (Hn : 0 <= n < 2^64) (Han : a + n <= 2^64),
  gmunch W m0 m -> inside W a n -> gmunch W m0 (apply_unmaps m [(wa a, Z_to_bv 64 n)]).
Proof.
  intros W m0 m a n Ha Hn Han G Hin. eapply gmunch_trans; [exact G|]. apply gmunch_of_munch.
  apply (munch_unmaps m a n Ha Hn Han W m (munch_refl W m) Hin).
Qed.

Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | GM : gmunch ?Wq ?mq m |- _ =>
      first [ apply (gmunch_write Wq mq m a bs) in GM; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared (gmunch) footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

Ltac transport_zeros segs m a n Ha Hn Han ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_zeros_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_zeros segs m a n Ha Hn Han A2 n2) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ => apply (stk_zeros segs m a n Ha Hn Han lo hi) in H
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_zeros m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
            | fail 100 "zero-filled range not inside the declared footprint" ]
  | H : gmunch ?W ?m0 m |- _ =>
      first [ apply (gmunch_zeros_in W m0 m a n Ha Hn Han) in H; [|cbn [inside]; slia]
            | fail 100 "zero-filled range not inside the declared (gmunch) footprint" ]
  | H : wmono segs ?m0 m |- _ => apply (wmono_zeros segs m a n Ha Hn Han m0) in H
  | H : mem_inv segs m |- _ =>
      let H' := fresh "MI" in
      assert (H' : mem_inv segs (apply_zeros m [(wa a, Z_to_bv 64 n)]))
        by (apply (mem_inv_zeros segs m a n Ha Hn Han H); first [assumption | intros; shelve]);
      clear H
  end.

Ltac transport_unmaps segs m a n Ha Hn Han ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_unmaps_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ =>
      first [ apply (wr_at_unmaps_other segs m a n Ha Hn Han A2 n2) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ =>
      first [ apply (stk_unmaps_other segs m a n Ha Hn Han lo hi) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_unmaps m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
            | fail 100 "unmapped range not inside the declared footprint" ]
  | H : gmunch ?W ?m0 m |- _ =>
      first [ apply (gmunch_unmaps_in W m0 m a n Ha Hn Han) in H; [|cbn [inside]; slia]
            | fail 100 "unmapped range not inside the declared (gmunch) footprint" ]
  | H : wmono segs ?m0 m |- _ => idtac "note: dropping wmono (not preserved by an unmap):" H; clear H
  | H : mem_inv segs m |- _ => apply (mem_inv_unmaps segs m a n Ha Hn Han) in H
  end.

Ltac transport_chunk_call segs m m' W MU WM H :=
  lazymatch type of H with
  | bytes_at _ _ ?A2 ?bs2 =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | dj_solve ]
            | lazymatch goal with FK : fkeep ?FI ?Wc ?st m m' |- _ =>
                apply (bytes_at_fkeep FI Wc st m m' A2 bs2) in H; [ | exact FK | solve_in_live | dj_solve ] end
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | wr_at _ _ ?A2 ?n2 => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | rw_cells _ _ ?A2 ?cs2 =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | dj_solve ]
            | lazymatch goal with FK : fkeep ?FI ?Wc ?st m m' |- _ =>
                apply (rw_cells_fkeep FI Wc st m m' A2 cs2) in H; [ | exact FK | exact WM | solve_in_live | dj_solve ] end
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | ro_cells _ _ ?A2 ?cs2 =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | u8arr _ _ ?A2 ?xs =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | u32arr _ _ ?A2 ?xs =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | u64arr _ _ ?A2 ?xs =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | u8ro _ _ ?A2 ?xs =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | stk _ _ ?loq ?hiq =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | dj_solve ]
            | clear H ]
  end.

Ltac transport_chunk_gcall segs m m' W GMc WM H :=
  lazymatch type of H with
  | bytes_at _ _ ?A2 ?bs2 =>
      first [ apply (bytes_at_gtransport W m m' A2 bs2) in H; [ | exact GMc | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | wr_at _ _ ?A2 ?n2 => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | rw_cells _ _ ?A2 ?cs2 =>
      first [ apply (rw_cells_gtransport W m m' A2 cs2) in H; [ | exact GMc | exact WM | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | ro_cells _ _ ?A2 ?cs2 =>
      first [ apply (ro_cells_gtransport W m m' A2 cs2) in H; [ | exact GMc | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | u8arr _ _ ?A2 ?xs =>
      first [ apply (u8arr_gtransport W m m' A2 xs) in H; [ | exact GMc | exact WM | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | u32arr _ _ ?A2 ?xs =>
      first [ apply (u32arr_gtransport W m m' A2 xs) in H; [ | exact GMc | exact WM | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | u64arr _ _ ?A2 ?xs =>
      first [ apply (u64arr_gtransport W m m' A2 xs) in H; [ | exact GMc | exact WM | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | u8ro _ _ ?A2 ?xs =>
      first [ apply (u8ro_gtransport W m m' A2 xs) in H; [ | exact GMc | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | stk _ _ ?loq ?hiq =>
      first [ apply (stk_gtransport W m m' loq hiq) in H; [ | exact GMc | exact WM | dj_solve ]
            | clear H ]
  end.

Ltac sub_fp_app := unfold sub_fp; let xo := fresh "xo" in let Hxo := fresh "Hxo" in intros xo Hxo; apply outside_app in Hxo; tauto.

Ltac transport_footprints_call segs m m' W MU WM :=
  repeat match goal with
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ sub_fp_solve | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : gmunch ?Wq ?mq m |- _ =>
      first [ eapply (gmunch_munch_in Wq W mq m m') in H; [ | exact MU | sub_fp_solve ]
            | apply (gmunch_extend Wq W mq m) in H; eapply (gmunch_munch_in (Wq ++ W) W mq m m') in H;
              [ cbn [List.app] in H | exact MU | sub_fp_app ] ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac transport_after_call_fk segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m _ _ |- _ => transport_chunk_call segs m m' W MU WM H
  | H : wr_at segs m _ _ |- _ => transport_chunk_call segs m m' W MU WM H
  | H : rw_cells segs m _ _ |- _ => transport_chunk_call segs m m' W MU WM H
  | H : ro_cells segs m _ _ |- _ => transport_chunk_call segs m m' W MU WM H
  | H : u8arr segs m _ _ |- _ => transport_chunk_call segs m m' W MU WM H
  | H : u32arr segs m _ _ |- _ => transport_chunk_call segs m m' W MU WM H
  | H : u64arr segs m _ _ |- _ => transport_chunk_call segs m m' W MU WM H
  | H : u8ro segs m _ _ |- _ => transport_chunk_call segs m m' W MU WM H
  | H : stk segs m _ _ |- _ => transport_chunk_call segs m m' W MU WM H
  end;
  transport_footprints_call segs m m' W MU WM.
Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fk segs m m' MU WM.

Ltac transport_after_gcall segs m m' MU GMc WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  let Wg := lazymatch type of GMc with gmunch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m _ _ |- _ => transport_chunk_gcall segs m m' Wg GMc WM H
  | H : wr_at segs m _ _ |- _ => transport_chunk_gcall segs m m' Wg GMc WM H
  | H : rw_cells segs m _ _ |- _ => transport_chunk_gcall segs m m' Wg GMc WM H
  | H : ro_cells segs m _ _ |- _ => transport_chunk_gcall segs m m' Wg GMc WM H
  | H : u8arr segs m _ _ |- _ => transport_chunk_gcall segs m m' Wg GMc WM H
  | H : u32arr segs m _ _ |- _ => transport_chunk_gcall segs m m' Wg GMc WM H
  | H : u64arr segs m _ _ |- _ => transport_chunk_gcall segs m m' Wg GMc WM H
  | H : u8ro segs m _ _ |- _ => transport_chunk_gcall segs m m' Wg GMc WM H
  | H : stk segs m _ _ |- _ => transport_chunk_gcall segs m m' Wg GMc WM H
  end;
  repeat match goal with
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ sub_fp_solve | exact MU ] ]
            | apply (munch_extend Wq W mq m) in H; apply (munch_trans (Wq ++ W) mq m m') in H;
              [ cbn [List.app] in H | eapply (munch_weaken W (Wq ++ W) m m'); [ sub_fp_app | exact MU ] ] ]
  | H : gmunch ?Wq ?mq m |- _ =>
      first [ apply (gmunch_trans Wq mq m m') in H; [ | eapply (gmunch_weaken Wg Wq m m'); [ sub_fp_solve | exact GMc ] ]
            | apply (gmunch_extend Wq Wg mq m) in H; apply (gmunch_trans (Wq ++ Wg) mq m m') in H;
              [ cbn [List.app] in H | eapply (gmunch_weaken Wg (Wq ++ Wg) m m'); [ sub_fp_app | exact GMc ] ] ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Definition swlo (a : Z) : Z := (sh a / 4096) * 4096.
Definition swhi (a n : Z) : Z := ((sh (a + n) + 4095) / 4096) * 4096.

Lemma shw_lo_eq a : shw_lo SHADOW_OFF a = swlo a.
Proof. unfold shw_lo, swlo, sh, page_size. reflexivity. Qed.
Lemma shw_hi_eq a n : shw_hi SHADOW_OFF a n = swhi a n.
Proof. unfold shw_hi, swhi, sh, page_size. reflexivity. Qed.

Lemma sw_bounds : forall a n, 0x609000 <= a -> 0 <= n ->
  swlo a <= sh a /\ sh (a + n) <= swhi a n /\ swlo a mod 4096 = 0 /\ swhi a n mod 4096 = 0
  /\ 0x609000 <= swlo a /\ swhi a n - swlo a <= n / 8 + 2 * 4096.
Proof.
  intros a n A0 N0. unfold swlo, swhi, sh, SHADOW_OFF.
  repeat split; try (Z.div_mod_to_equations; nia).
Qed.

Lemma sw_range : forall a n, 0x609000 <= a -> 0 <= n -> a + n <= 2^47 ->
  0x7fff8000 <= swlo a /\ swhi a n <= 0x10007fff8000.
Proof. intros a n A0 N0 TOP. unfold swlo, swhi, sh, SHADOW_OFF. Z.div_mod_to_equations. nia. Qed.

Definition in_shadow_band (u : Z) : Prop :=
  0x7fff8000 <= u < 0x8fff7000 \/ 0x2008fff7000 <= u < 0x10007fff8000.

Definition shvis (H : word -> bool) (m : word -> option byte) : Prop :=
  forall x, in_shadow_band (bv_unsigned x) -> H x = false -> m x <> None.

Lemma wview_high : forall m x, 0x609000 <= bv_unsigned x -> wview asegs m x = m x.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite a0_find_segment_none by lia. reflexivity.
Qed.

Lemma shvis_wmono : forall H m m', shvis H m -> wmono asegs m m' -> shvis H m'.
Proof.
  intros H m m' S WM x B V. specialize (S x B V). specialize (WM x).
  rewrite !wview_high in WM by (unfold in_shadow_band in B; lia). exact (WM S).
Qed.

Lemma shvis_grow : forall H m m', mgrow m m' -> shvis H m -> shvis H m'.
Proof.
  intros H m m' G S x B V E. specialize (S x B V). destruct (G x) as [E1|(_ & _ & _ & b & E2)]; congruence.
Qed.

Lemma shvis_unhide_zeros : forall H m a n, shvis H m -> 0 < a -> 0 < n -> a + n <= 2^64 ->
  shvis (unhide_range a (a + n) H) (apply_zeros m [(wa a, Z_to_bv 64 n)]).
Proof.
  intros H m a n S A0 N0 AN x B V. rewrite apply_zeros_spec by lia. unfold unhide_range in V. rewrite in_rangeb_in_range in V.
  replace (a + n - a) with n in V by lia. destruct (in_range a n x); [discriminate|].
  rewrite andb_true_r in V. exact (S x B V).
Qed.

Lemma shvis_zeros : forall H m a n, shvis H m -> 0 < a -> 0 < n -> a + n <= 2^64 ->
  shvis H (apply_zeros m [(wa a, Z_to_bv 64 n)]).
Proof.
  intros H m a n S A0 N0 AN x B V. rewrite apply_zeros_spec by lia. destruct (in_range a n x); [discriminate| exact (S x B V)].
Qed.

Lemma shvis_unhide_unmaps : forall H m a n, shvis H m -> 0 < a -> 0 < n -> a + n <= 2^64 -> app_mem a n ->
  shvis (unhide_range a (a + n) H) (apply_unmaps m [(wa a, Z_to_bv 64 n)]).
Proof.
  intros H m a n S A0 N0 AN AM x B V. rewrite apply_unmaps_spec by lia. unfold unhide_range in V. rewrite in_rangeb_in_range in V.
  replace (a + n - a) with n in V by lia. unfold in_range in *.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb negb] in V |- *;
    try (rewrite ?andb_true_r in V; exact (S x B V)).
  exfalso. unfold app_mem, in_shadow_band in *. lia.
Qed.

Lemma sw_in_band : forall a n x, 0x609000 <= a -> 0 <= n -> app_mem a n -> swlo a <= x < swhi a n -> in_shadow_band x.
Proof.
  intros a n x A0 N0 AM W. unfold swlo, swhi, sh, SHADOW_OFF, app_mem, in_shadow_band in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma zb_band : forall x : word, in_shadow_band (bv_unsigned x) -> zb x = true.
Proof.
  intros x B. unfold zb, in_shadow_band in *. apply orb_true_iff.
  destruct B as [B|B]; [left| right]; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt| apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

Lemma unhide_zb_band : forall lo hi (Hh : word -> bool),
  (forall x : word, lo <= bv_unsigned x < hi -> zb x = true) -> unhide_zb lo hi Hh = unhide_range lo hi Hh.
Proof.
  intros lo hi Hh B. apply functional_extensionality. intros x. unfold unhide_zb, unhide_range.
  destruct (in_rangeb lo hi x) eqn:IR; [| reflexivity].
  unfold in_rangeb in IR. apply andb_prop in IR as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
  rewrite (B x ltac:(lia)). reflexivity.
Qed.

Lemma unhide_zb_window : forall a n (Hh : word -> bool), 0x609000 <= a -> 0 <= n -> app_mem a n ->
  unhide_zb (swlo a) (swhi a n) Hh = unhide_range (swlo a) (swhi a n) Hh.
Proof. intros a n Hh A0 N0 AM. apply unhide_zb_band. intros x Hx. apply zb_band. exact (sw_in_band a n _ A0 N0 AM Hx). Qed.

Lemma shvis_wreveal : forall H m a n, shvis H m -> mclean H m -> 0x609000 <= a -> 0 <= n -> app_mem a n ->
  shvis (unhide_range (swlo a) (swhi a n) (unhide_range a (a + n) H)) (wreveal H (swlo a) (swhi a n) m).
Proof.
  intros H m a n S C A0 N0 AM x B V. unfold wreveal, unhide_range in *.
  destruct (in_rangeb (swlo a) (swhi a n) x) eqn:IW; cbn [andb negb] in V |- *.
  - destruct (H x) eqn:HX; [discriminate|]. exact (S x B HX).
  - rewrite andb_true_r in V. destruct (in_rangeb a (a + n) x) eqn:IR; cbn [andb negb] in V.
    + exfalso. unfold in_rangeb in IR. apply andb_prop in IR as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
      unfold app_mem, in_shadow_band in *. lia.
    + rewrite andb_true_r in V. exact (S x B V).
Qed.

Lemma stk_wreveal_window : forall H m a n, shvis H m -> mclean H m -> 0x609000 <= a -> 0 <= n -> app_mem a n ->
  stk asegs (wreveal H (swlo a) (swhi a n) m) (swlo a) (swhi a n).
Proof.
  intros H m a n S C A0 N0 AM. pose proof (sw_bounds a n A0 N0) as (W1 & W2 & W3 & W4 & W5 & W6).
  assert (TOPW : swhi a n <= 0x10007fff8000).
  { pose proof (sw_in_band a n (swhi a n - 1) A0 N0 AM). unfold in_shadow_band in H0.
    destruct (Z_lt_le_dec (swlo a) (swhi a n)); [specialize (H0 ltac:(lia)); lia|].
    unfold swhi, swlo, sh, SHADOW_OFF, app_mem in *. Z.div_mod_to_equations. lia. }
  split; [lia|]. split; [lia|]. intros u Hu.
  pose proof (sw_in_band a n u A0 N0 AM Hu) as B.
  assert (E : exists b, wreveal H (swlo a) (swhi a n) m (wa u) = Some b).
  { unfold wreveal. unfold in_rangeb. rewrite wa_unsigned by lia.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb].
    destruct (H (wa u)) eqn:HX; [eexists; reflexivity|].
    specialize (S (wa u)). rewrite wa_unsigned in S by lia. specialize (S B HX). destruct (m (wa u)); [eexists; reflexivity| congruence]. }
  destruct E as [b E]. split.
  - rewrite wview_high by (rewrite wa_unsigned by lia; unfold in_shadow_band in B; lia). rewrite E. discriminate.
  - exists b. unfold mrd. rewrite E. reflexivity.
Qed.

Definition wmono_but (U : list (Z * Z)) (m m' : word -> option byte) : Prop :=
  forall x, outside U (bv_unsigned x) -> wview asegs m x <> None -> wview asegs m' x <> None.

Lemma wmono_but_of_wmono : forall U m m', wmono asegs m m' -> wmono_but U m m'.
Proof. intros U m m' W x _ Hx. exact (W x Hx). Qed.

Lemma wmono_but_trans : forall U m1 m2 m3, wmono_but U m1 m2 -> wmono_but U m2 m3 -> wmono_but U m1 m3.
Proof. intros U m1 m2 m3 A B x O Hx. exact (B x O (A x O Hx)). Qed.

Lemma wmono_but_unmaps : forall a n m, 0 <= a < 2^64 -> 0 <= n < 2^64 -> a + n <= 2^64 ->
  wmono_but [(a, a + n)] m (apply_unmaps m [(wa a, Z_to_bv 64 n)]).
Proof.
  intros a n m Ha Hn Han x O Hx. cbn in O. unfold wview in *. rewrite apply_unmaps_spec by lia. unfold in_range.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try exact Hx. lia.
Qed.

Lemma lenZ_mmap_len : forall len, 0 <= len < 2^64 -> lenZ len = mmap_len len.
Proof. intros len H. unfold lenZ, mmap_len. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma lenZ_bound : forall len, 0 < len < 2^64 -> len <= lenZ len < len + 4096.
Proof. intros len H. rewrite lenZ_mmap_len by lia. apply mmap_len_bound. lia. Qed.

Lemma addrZ_eq : forall addr, 0 <= addr < 2^64 -> addrZ addr = addr.
Proof. intros. unfold addrZ. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma resp_eqb_sound : forall e r zs us,
  resp_eqb e (mkEffectU r [] zs us [] []) = true -> eff_copyins e = [] ->
  (zs = [] \/ exists p, zs = [p]) -> (us = [] \/ exists p, us = [p]) ->
  e = mkEffectU r [] zs us [] [].
Proof.
  intros [r1 ws1 zs1 us1 cs1 ci1] r zs us E CI HZ HU. cbn in CI. subst ci1. unfold resp_eqb in E.
  repeat (apply andb_prop in E as [E ?X]).
  destruct ws1; [| discriminate]. destruct cs1; [| discriminate]. apply Fs.bv_eqb_eq in E. subst r1.
  assert (EZ : zs1 = zs).
  { destruct zs1 as [|[a1 n1] [|? ?]]; destruct HZ as [->|([a n] & ->)]; try discriminate; [reflexivity|].
    match goal with Hq : bv_eqb a1 a && bv_eqb n1 n = true |- _ => apply andb_prop in Hq as [Q1 Q2]; apply Fs.bv_eqb_eq in Q1; apply Fs.bv_eqb_eq in Q2; subst; reflexivity end. }
  assert (EU : us1 = us).
  { destruct us1 as [|[a1 n1] [|? ?]]; destruct HU as [->|([a n] & ->)]; try discriminate; [reflexivity|].
    match goal with Hq : bv_eqb a1 a && bv_eqb n1 n = true |- _ => apply andb_prop in Hq as [Q1 Q2]; apply Fs.bv_eqb_eq in Q1; apply Fs.bv_eqb_eq in Q2; subst; reflexivity end. }
  subst. reflexivity.
Qed.

Lemma dec_fixed_Some : forall addr len rsp u, dec_fixed addr len rsp = Some u -> strip rsp = fixed_eff addr len.
Proof.
  intros addr len rsp u D. unfold dec_fixed in D. destruct (resp_eqb (strip rsp) (fixed_eff addr len)) eqn:E; [| discriminate].
  unfold fixed_eff in *. apply (resp_eqb_sound (strip rsp)); [exact E| destruct rsp; reflexivity| right; eexists; reflexivity| left; reflexivity].
Qed.

Lemma mclean_zeros : forall H m a n, mclean H m -> 0 < a -> 0 < n -> a + n <= 2^64 ->
  mclean (unhide_range a (a + n) H) (apply_zeros m [(Z_to_bv 64 a, Z_to_bv 64 n)]).
Proof.
  intros H m a n [C O] A0 N0 AN. split.
  - intros x Hx. unfold unhide_range in Hx. apply andb_prop in Hx as [Hx NI].
    change (Z_to_bv 64 a) with (wa a). rewrite apply_zeros_spec by lia. rewrite <- (in_rangeb_in_range a (a + n)) || rewrite in_rangeb_in_range in NI.
    all: replace (a + n - a) with n in * by lia.
    all: destruct (in_range a n x); cbn in NI; [discriminate| exact (C x Hx)].
  - intros x Hx. apply O. eapply unhide_range_sub. exact Hx.
Qed.

Lemma mclean_unmaps : forall H m a n, mclean H m -> 0 < a -> 0 < n -> a + n <= 2^64 ->
  mclean (unhide_range a (a + n) H) (apply_unmaps m [(Z_to_bv 64 a, Z_to_bv 64 n)]).
Proof.
  intros H m a n [C O] A0 N0 AN. split.
  - intros x Hx. unfold unhide_range in Hx. apply andb_prop in Hx as [Hx NI].
    change (Z_to_bv 64 a) with (wa a). rewrite apply_unmaps_spec by lia.
    destruct (in_range a n x); [reflexivity| exact (C x Hx)].
  - intros x Hx. apply O. eapply unhide_range_sub. exact Hx.
Qed.

Lemma implA_fixed {A} : forall flags H (k : unit -> itree nodeL (exc A)) Q R F pc pc4 fc rv m ro addr len w,
  (flags = MAPF_FIXED \/ flags = MAPF_FIXED_NR) ->
  mclean H m ->
  fetch_word asegs (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> pc4 = pc + 4 ->
  reg_get R 17 = Z_to_bv 64 222 ->
  reg_get R 10 = Z_to_bv 64 addr -> reg_get R 11 = Z_to_bv 64 len -> reg_get R 12 = Z_to_bv 64 PROT_RW ->
  reg_get R 13 = Z_to_bv 64 flags -> reg_get R 14 = Z_to_bv 64 (-1) -> reg_get R 15 = Z_to_bv 64 0 ->
  addr mod 4096 = 0 -> 0 < addr -> 0 < len < 2^47 -> addr + lenZ len <= 2^47 ->
  (let H' := unhide_range addr (addr + lenZ len) H in
   let m' := apply_zeros m [(Z_to_bv 64 addr, Z_to_bv 64 (lenZ len))] in
   mclean H' m' -> implA H' (k tt) Q (MS (bvmap_set 10 (Z_to_bv 64 addr) R) F (Z_to_bv 64 pc4) fc rv m' ro)) ->
  implA H (ebind (enode (LMmapFixed addr len flags) (dec_fixed addr len)) k) Q (MS R F (Z_to_bv 64 pc) fc rv m ro).
Proof.
  intros flags H k Q R F pc pc4 fc rv m ro addr len w FL C FW EC -> R17 R10 R11 R12 R13 R14 R15 AL A0 L0 TOP CONT.
  pose proof (lenZ_bound len ltac:(lia)) as LB.
  eapply implA_ebind with (Q1 := fun u H' ms' => H' = unhide_range addr (addr + lenZ len) H /\
      ms' = MS (bvmap_set 10 (Z_to_bv 64 addr) R) F (Z_to_bv 64 (pc + 4)) fc rv (apply_zeros m [(Z_to_bv 64 addr, lenW len)]) ro).
  - apply implL_enode. apply (evt_ecall asegs _ R F pc fc rv m ro w FW EC). split.
    + cbn [at_nodeL]. unfold mmap_regs, areg. cbn [ms_svc_pending ms_regs MSsvc]. rewrite R17, R10, R11, R12, R13, R14, R15.
      rewrite w_is0_lit by lia. rewrite (proj2 (Z.eqb_neq len 0)) by lia.
      repeat split; try reflexivity; try assumption; unfold page_size; lia.
    + intros rsp u D. pose proof (dec_fixed_Some _ _ _ _ D) as Hs. unfold fixed_eff in Hs.
      rewrite (nretL_MSsvc _ rsp H R F (Z_to_bv 64 pc) (reg_get R 17) fc rv m ro _ _ _ _ Hs).
      cbn [hideL]. pose proof (lfixed_mem_eq H m addr len C ltac:(lia) ltac:(lia) ltac:(lia)) as EM. cbv zeta in EM. rewrite EM.
      rewrite addrZ_eq by lia. rewrite lit_add_lit. apply evt_done. split; reflexivity.
  - intros u H' ms' [-> ->]. destruct u. apply CONT. cbv zeta. apply mclean_zeros; try lia. exact C.
Qed.

Lemma lmadv_mem_eq : forall H m addr len,
  mclean H m -> 0 < addr -> addr + lenZ len <= 2^64 -> 0 < lenZ len ->
  let H' := hide_range (addrZ addr) (addrZ addr + lenZ len) H in
  mrestrict H' (apply_writes (apply_zeros (apply_unmaps (mreveal (unhidden H H') m) []) [(Z_to_bv 64 addr, lenW len)]) [])
  = apply_unmaps m [(Z_to_bv 64 addr, lenW len)].
Proof.
  intros H m addr len C A0 AL L0 H'. apply functional_extensionality. intros x.
  cbn [apply_writes]. change (apply_unmaps (mreveal (unhidden H H') m) []) with (mreveal (unhidden H H') m).
  unfold lenW. change (Z_to_bv 64 addr) with (wa addr).
  assert (EA : addrZ addr = addr) by (unfold addrZ; rewrite unsigned_lit by lia; reflexivity).
  unfold mrestrict, mreveal, unhidden. subst H'. unfold hide_range. rewrite EA.
  rewrite apply_zeros_spec, apply_unmaps_spec by lia. rewrite in_rangeb_in_range. replace (addr + lenZ len - addr) with (lenZ len) by lia.
  destruct (in_range addr (lenZ len) x) eqn:IR.
  - rewrite orb_true_r. reflexivity.
  - rewrite orb_false_r. destruct (H x) eqn:HX; cbn [negb andb]; [symmetry; apply (proj1 C); exact HX| reflexivity].
Qed.

Lemma dec_madv_Some : forall addr len rsp u, dec_madv addr len rsp = Some u -> strip rsp = madv_eff addr len.
Proof.
  intros addr len rsp u D. unfold dec_madv in D. destruct (resp_eqb (strip rsp) (madv_eff addr len)) eqn:E; [| discriminate].
  unfold madv_eff in *. apply (resp_eqb_sound (strip rsp)); [exact E| destruct rsp; reflexivity| right; eexists; reflexivity| left; reflexivity].
Qed.

Lemma mclean_zeros_vis : forall H m a n, mclean H m -> 0 < a -> 0 < n -> a + n <= 2^64 ->
  (forall x : word, a <= bv_unsigned x < a + n -> H x = false) ->
  mclean H (apply_zeros m [(Z_to_bv 64 a, Z_to_bv 64 n)]).
Proof.
  intros H m a n [C O] A0 N0 AN VIS. split; [| exact O].
  intros x Hx. change (Z_to_bv 64 a) with (wa a). rewrite apply_zeros_spec by lia.
  destruct (in_range a n x) eqn:IR; [| exact (C x Hx)]. exfalso.
  unfold in_range in IR. apply andb_prop in IR as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
  rewrite (VIS x ltac:(lia)) in Hx. discriminate.
Qed.

Lemma vis_of_mapped : forall H m (a n : Z), mclean H m ->
  (forall x : word, a <= bv_unsigned x < a + n -> m x <> None) ->
  forall x : word, a <= bv_unsigned x < a + n -> H x = false.
Proof.
  intros H m a n C RD x Hx. destruct (m x) as [b|] eqn:E; [exact (mclean_some H m x b C E)| exfalso; exact (RD x Hx E)].
Qed.

Lemma vis_of_rw_cells : forall H m (a : Z) cs, mclean H m -> 0x609000 <= a -> rw_cells asegs m a cs ->
  forall x : word, a <= bv_unsigned x < a + Z.of_nat (cells_size cs) -> H x = false.
Proof.
  intros H m a cs C A0 [_ (W0 & W1 & WR)] x Hx. apply (vis_of_mapped H m a (Z.of_nat (cells_size cs)) C); [| exact Hx].
  intros y Hy. specialize (WR (bv_unsigned y - a) ltac:(lia)). replace (a + (bv_unsigned y - a)) with (bv_unsigned y) in WR by lia.
  rewrite wa_unsigned_id in WR. rewrite wview_high in WR by lia. exact WR.
Qed.

Lemma mclean_rehide : forall H m a n, mclean H m -> 0x609000 <= a -> 0 < n -> a + n <= 2^64 ->
  mclean (hide_range a (a + n) H) (apply_unmaps m [(Z_to_bv 64 a, Z_to_bv 64 n)]).
Proof.
  intros H m a n [C O] A0 N0 AN. split.
  - intros x Hx. change (Z_to_bv 64 a) with (wa a). rewrite apply_unmaps_spec by lia.
    destruct (in_range a n x) eqn:IR; [reflexivity|]. unfold hide_range in Hx. rewrite in_rangeb_in_range in Hx.
    replace (a + n - a) with n in Hx by lia. rewrite IR, orb_false_r in Hx. exact (C x Hx).
  - intros x Hx. unfold hide_range in Hx. apply orb_prop in Hx as [Hx|Hx]; [exact (O x Hx)|].
    unfold in_rangeb in Hx. apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply a0_find_segment_none; lia.
Qed.
Lemma shvis_hide_unmaps : forall H m a n, shvis H m -> 0 < a -> 0 < n -> a + n <= 2^64 ->
  shvis (hide_range a (a + n) H) (apply_unmaps m [(wa a, Z_to_bv 64 n)]).
Proof.
  intros H m a n S A0 N0 AN x B V. rewrite apply_unmaps_spec by lia. unfold hide_range in V. rewrite in_rangeb_in_range in V.
  replace (a + n - a) with n in V by lia. apply orb_false_iff in V as [V1 V2]. rewrite V2. exact (S x B V1).
Qed.

Lemma implA_madv {A} : forall H (k : unit -> itree nodeL (exc A)) Q R F pc pc4 fc rv m ro addr len w,
  mclean H m ->
  fetch_word asegs (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> pc4 = pc + 4 ->
  reg_get R 17 = Z_to_bv 64 233 ->
  reg_get R 10 = Z_to_bv 64 addr -> reg_get R 11 = Z_to_bv 64 len -> reg_get R 12 = Z_to_bv 64 4 ->
  addr mod 4096 = 0 -> 0x609000 <= addr -> 0 < len < 2^47 -> addr + lenZ len <= 2^47 ->
  (let H' := hide_range addr (addr + lenZ len) H in
   let m' := apply_unmaps m [(Z_to_bv 64 addr, Z_to_bv 64 (lenZ len))] in
   mclean H' m' -> implA H' (k tt) Q (MS (bvmap_set 10 (Z_to_bv 64 0) R) F (Z_to_bv 64 pc4) fc rv m' ro)) ->
  implA H (ebind (t_madv addr len) k) Q (MS R F (Z_to_bv 64 pc) fc rv m ro).
Proof.
  intros H k Q R F pc pc4 fc rv m ro addr len w C FW EC -> R17 R10 R11 R12 AL A0 L0 TOP CONT.
  pose proof (lenZ_bound len ltac:(lia)) as LB.
  eapply implA_ebind with (Q1 := fun u H' ms' => H' = hide_range addr (addr + lenZ len) H /\
      ms' = MS (bvmap_set 10 (Z_to_bv 64 0) R) F (Z_to_bv 64 (pc + 4)) fc rv (apply_unmaps m [(Z_to_bv 64 addr, lenW len)]) ro).
  - apply implL_enode. apply (evt_ecall asegs _ R F pc fc rv m ro w FW EC). split.
    + cbn [at_nodeL]. unfold madv_regs, areg. cbn [ms_svc_pending ms_regs MSsvc]. rewrite R17, R10, R11, R12.
      rewrite w_is0_lit by lia. rewrite (proj2 (Z.eqb_neq len 0)) by lia.
      repeat split; try reflexivity; try assumption; unfold page_size; try lia.
      intros a Ha. apply a0_find_segment_none; lia.
    + intros rsp u D. pose proof (dec_madv_Some _ _ _ _ D) as Hs. unfold madv_eff in Hs.
      rewrite (nretL_MSsvc _ rsp H R F (Z_to_bv 64 pc) (reg_get R 17) fc rv m ro _ _ _ _ Hs).
      cbn [hideL]. pose proof (lmadv_mem_eq H m addr len C ltac:(lia) ltac:(lia) ltac:(lia)) as EM. cbv zeta in EM. rewrite EM.
      rewrite addrZ_eq by lia. rewrite lit_add_lit. apply evt_done. split; reflexivity.
  - intros u H' ms' [-> ->]. destruct u. apply CONT. cbv zeta. apply mclean_rehide; try lia. exact C.
Qed.

Lemma dec_unmapu_Some : forall addr len rsp u, dec_unmapu addr len rsp = Some u ->
  strip rsp = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] [].
Proof.
  intros addr len rsp u D. unfold dec_unmapu in D. destruct (dec_munmap addr len rsp) as [[e|[|]]|] eqn:E; try discriminate.
  exact (dec_munmap_Some _ _ _ _ E).
Qed.

Lemma implA_unmap {A} : forall H (k : unit -> itree nodeL (exc A)) Q R F pc pc4 fc rv m ro addr len w,
  mclean H m ->
  fetch_word asegs (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> pc4 = pc + 4 ->
  reg_get R 17 = Z_to_bv 64 215 -> reg_get R 10 = Z_to_bv 64 addr -> reg_get R 11 = Z_to_bv 64 len ->
  addr mod 4096 = 0 -> 0 < addr -> 0 < len < 2^47 -> addr + lenZ len <= 2^47 ->
  (let H' := unhide_range addr (addr + lenZ len) H in
   let m' := apply_unmaps m [(Z_to_bv 64 addr, Z_to_bv 64 (lenZ len))] in
   mclean H' m' -> implA H' (k tt) Q (MS (bvmap_set 10 (Z_to_bv 64 0) R) F (Z_to_bv 64 pc4) fc rv m' ro)) ->
  implA H (ebind (t_unmap addr len) k) Q (MS R F (Z_to_bv 64 pc) fc rv m ro).
Proof.
  intros H k Q R F pc pc4 fc rv m ro addr len w C FW EC -> R17 R10 R11 AL A0 L0 TOP CONT.
  pose proof (lenZ_bound len ltac:(lia)) as LB.
  eapply implA_ebind with (Q1 := fun u H' ms' => H' = unhide_range addr (addr + lenZ len) H /\
      ms' = MS (bvmap_set 10 (Z_to_bv 64 0) R) F (Z_to_bv 64 (pc + 4)) fc rv (apply_unmaps m [(Z_to_bv 64 addr, lenW len)]) ro).
  - apply implL_enode. apply (evt_ecall asegs _ R F pc fc rv m ro w FW EC). split.
    + cbn [at_nodeL at_node]. unfold areg. cbn [ms_svc_pending ms_regs MSsvc]. rewrite R17, R10, R11.
      rewrite w_is0_lit by lia. rewrite (proj2 (Z.eqb_neq len 0)) by lia. rewrite !unsigned_lit by lia. fold (lenZ len).
      repeat split; try reflexivity; unfold page_size; try lia. fold (mmap_len len). rewrite <- lenZ_mmap_len by lia. lia.
    + intros rsp u D. pose proof (dec_unmapu_Some _ _ _ _ D) as Hs. rewrite <- lenZ_mmap_len in Hs by lia. fold (lenW len) in Hs.
      rewrite (nretL_MSsvc _ rsp H R F (Z_to_bv 64 pc) (reg_get R 17) fc rv m ro _ _ _ _ Hs).
      cbn [hideL]. pose proof (lunmap_mem_eq H m addr len C ltac:(lia) ltac:(lia) ltac:(lia)) as EM. cbv zeta in EM. rewrite EM.
      rewrite addrZ_eq by lia. rewrite lit_add_lit. apply evt_done. split; reflexivity.
  - intros u H' ms' [-> ->]. destruct u. apply CONT. cbv zeta. apply mclean_unmaps; try lia. exact C.
Qed.

Lemma avoids_all_Forall : forall a n avoid, avoids_all a n avoid = true -> Forall (fun iv => a + n <= fst iv \/ snd iv <= a) avoid.
Proof.
  induction avoid as [|[lo hi] avoid IH]; intros E; [constructor|]. cbn in E. apply andb_prop in E as [E1 E2].
  constructor; [cbn| apply IH; exact E2]. apply orb_prop in E1 as [E1|E1]; [left; apply Z.leb_le; exact E1| right; apply Z.leb_le; exact E1].
Qed.

Lemma dec_anon_Some {HC : HasCeiling} : forall len avoid rsp a, dec_anon len avoid rsp = Some a ->
  strip rsp = mkEffect (Z_to_bv 64 a) [] [(Z_to_bv 64 a, lenW len)]
  /\ bv_unsigned (eff_ret rsp) = a /\ a mod 4096 = 0 /\ 0x609000 <= a /\ app_mem a (lenZ len) /\ anon_place a (lenZ len)
  /\ Forall (fun iv => a + lenZ len <= fst iv \/ snd iv <= a) avoid.
Proof.
  intros len avoid rsp a D. unfold dec_anon in D.
  match type of D with (if ?c then _ else _) = _ => destruct c eqn:E; [| discriminate] end. injection D as <-.
  apply andb_prop in E as [E X]. apply andb_prop in E as [E XC]. apply Z.leb_le in XC.
  apply andb_prop in E as [E X0]. apply andb_prop in E as [E X1]. apply andb_prop in E as [E X2].
  pose proof (bv_unsigned_in_range 64 (eff_ret rsp)) as AR. unfold bv_modulus in AR. change (2 ^ Z.of_N 64) with (2^64) in AR.
  assert (ES : strip rsp = mkEffect (eff_ret rsp) [] [(eff_ret rsp, lenW len)]).
  { apply (resp_eqb_sound (strip rsp)); [exact E| destruct rsp; reflexivity| right; eexists; reflexivity| left; reflexivity]. }
  rewrite Z_to_bv_bv_unsigned. split; [exact ES|]. split; [reflexivity|].
  apply Z.eqb_eq in X2. apply Z.leb_le in X1. unfold app_memb in X0.
  assert (AM : app_mem (bv_unsigned (eff_ret rsp)) (lenZ len) /\ anon_place (bv_unsigned (eff_ret rsp)) (lenZ len)).
  { unfold app_mem, anon_place. pose proof (@alloc_ceiling_lt47 HC). apply orb_prop in X0 as [X0|X0].
    - apply Z.ltb_lt in X0. split; [left| split; [left|]]; lia.
    - apply andb_prop in X0 as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.ltb_lt in Y2. split; [right| split; [right|]]; lia. }
  destruct AM as [AM TOP]. repeat (split; [assumption|]). apply avoids_all_Forall. exact X.
Qed.

Lemma mclean_apply_zeros : forall Hh m a n, mclean Hh m -> 0 < a -> 0 < n -> a + n <= 2^64 ->
  (forall x, a <= bv_unsigned x < a + n -> Hh x = false) ->
  mclean Hh (apply_zeros m [(wa a, Z_to_bv 64 n)]).
Proof.
  intros Hh m a n [C O] A0 N0 AN HF. split; [| exact O]. intros x Hx.
  rewrite apply_zeros_spec by lia. unfold in_range.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try exact (C x Hx).
  rewrite (HF x) in Hx by lia. discriminate.
Qed.

Lemma implA_anon {HC : HasCeiling} {A} : forall H (k : Z -> itree nodeL (exc A)) Q R F pc pc4 fc rv m ro len avoid w,
  mclean H m -> shvis H m ->
  fetch_word asegs (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> pc4 = pc + 4 ->
  reg_get R 17 = Z_to_bv 64 222 ->
  reg_get R 10 = Z_to_bv 64 0 -> reg_get R 11 = Z_to_bv 64 len -> reg_get R 12 = Z_to_bv 64 PROT_RW ->
  reg_get R 13 = Z_to_bv 64 MAPF_ANON_PRIVATE -> reg_get R 14 = Z_to_bv 64 (-1) -> reg_get R 15 = Z_to_bv 64 0 ->
  0 < len < 2^47 ->
  (forall a, a mod 4096 = 0 -> 0x609000 <= a -> app_mem a (lenZ len) -> anon_place a (lenZ len) ->
     Forall (fun iv => a + lenZ len <= fst iv \/ snd iv <= a) avoid ->
     let H' := unhide_range (swlo a) (swhi a (lenZ len)) (unhide_range a (a + lenZ len) H) in
     let m1 := wreveal H (swlo a) (swhi a (lenZ len)) m in
     let m' := apply_zeros m1 [(Z_to_bv 64 a, Z_to_bv 64 (lenZ len))] in
     mgrow m m1 -> (forall x, m1 x = m x \/ swlo a <= bv_unsigned x < swhi a (lenZ len)) -> mclean H' m' ->
     shvis H' m1 -> stk asegs m1 (swlo a) (swhi a (lenZ len)) ->
     implA H' (k a) Q (MS (bvmap_set 10 (Z_to_bv 64 a) R) F (Z_to_bv 64 pc4) fc rv m' ro)) ->
  implA H (ebind (t_anon len avoid) k) Q (MS R F (Z_to_bv 64 pc) fc rv m ro).
Proof.
  intros H k Q R F pc pc4 fc rv m ro len avoid w C SV FW EC -> R17 R10 R11 R12 R13 R14 R15 L0 CONT.
  pose proof (lenZ_bound len ltac:(lia)) as LB.
  eapply implA_ebind with (Q1 := fun a H' ms' =>
      a mod 4096 = 0 /\ 0x609000 <= a /\ app_mem a (lenZ len) /\ anon_place a (lenZ len) /\
      Forall (fun iv => a + lenZ len <= fst iv \/ snd iv <= a) avoid /\
      H' = unhide_range (swlo a) (swhi a (lenZ len)) (unhide_range a (a + lenZ len) H) /\
      ms' = MS (bvmap_set 10 (Z_to_bv 64 a) R) F (Z_to_bv 64 (pc + 4)) fc rv
              (apply_zeros (wreveal H (swlo a) (swhi a (lenZ len)) m) [(Z_to_bv 64 a, lenW len)]) ro).
  - apply implL_enode. apply (evt_ecall asegs _ R F pc fc rv m ro w FW EC). split.
    + cbn [at_nodeL]. unfold mmap_regs, areg. cbn [ms_svc_pending ms_regs MSsvc]. rewrite R17, R10, R11, R12, R13, R14, R15.
      rewrite w_is0_lit by lia. rewrite (proj2 (Z.eqb_neq len 0)) by lia. unfold SHADOW_OFF.
      repeat split; try reflexivity; lia.
    + intros rsp a D. destruct (dec_anon_Some _ _ _ _ D) as (Hs & EA & AL & IMG & AM & TOP & AV).
      pose proof TOP as [TLOW TCEIL]. pose proof (@alloc_ceiling_lt47 HC) as C47.
      rewrite (nretL_MSsvc _ rsp H R F (Z_to_bv 64 pc) (reg_get R 17) fc rv m ro _ _ _ _ Hs).
      cbn [hideL]. unfold ret_alignedb. rewrite EA. unfold page_size. rewrite (proj2 (Z.eqb_eq _ _) AL). cbv iota.
      rewrite shw_lo_eq, shw_hi_eq.
      rewrite (unhide_zb_window a (lenZ len) _ IMG ltac:(lia) AM).
      pose proof (lheap_mem_eq H m a len (swlo a) (swhi a (lenZ len)) C ltac:(lia) ltac:(lia) ltac:(lia)) as EM. cbv zeta in EM. rewrite EM.
      rewrite lit_add_lit. apply evt_done. repeat (split; [assumption|]). split; reflexivity.
  - intros a H' ms' (AL & IMG & AM & TOP & AV & -> & ->).
    pose proof TOP as [TLOW TCEIL]. pose proof (@alloc_ceiling_lt47 HC) as C47.
    pose proof (sw_bounds a (lenZ len) IMG ltac:(lia)) as (W1 & W2 & W3 & W4 & W5 & W6).
    apply CONT; try assumption.
    + apply wreveal_mgrow; [exact C| exact W5].
    + apply wreveal_changed.
    + cbv zeta. apply mclean_apply_zeros; try lia.
      * exact (mclean_wreveal H (swlo a) (swhi a (lenZ len)) m a (a + lenZ len) C).
      * intros x Hx. apply unhide_range_false. apply unhide_range_in. lia.
    + apply shvis_wreveal; try assumption; lia.
    + apply stk_wreveal_window; try assumption; lia.
Qed.

Lemma implA_commit {A} : forall H (k : unit -> itree nodeL (exc A)) Q R F pc pc4 fc rv m ro addr len w,
  mclean H m -> shvis H m ->
  fetch_word asegs (Z_to_bv 64 pc) = Some w -> is_ecall w = true -> pc4 = pc + 4 ->
  reg_get R 17 = Z_to_bv 64 222 ->
  reg_get R 10 = Z_to_bv 64 addr -> reg_get R 11 = Z_to_bv 64 len -> reg_get R 12 = Z_to_bv 64 PROT_RW ->
  reg_get R 13 = Z_to_bv 64 MAPF_FIXED -> reg_get R 14 = Z_to_bv 64 (-1) -> reg_get R 15 = Z_to_bv 64 0 ->
  addr mod 4096 = 0 -> 0x609000 <= addr -> 0 < len < 2^47 -> addr + lenZ len <= 2^47 -> app_mem addr (lenZ len) ->
  (let H' := unhide_range (swlo addr) (swhi addr (lenZ len)) (unhide_range addr (addr + lenZ len) H) in
   let m1 := wreveal H (swlo addr) (swhi addr (lenZ len)) m in
   let m' := apply_zeros m1 [(Z_to_bv 64 addr, Z_to_bv 64 (lenZ len))] in
   mgrow m m1 -> (forall x, m1 x = m x \/ swlo addr <= bv_unsigned x < swhi addr (lenZ len)) -> mclean H' m' ->
   shvis H' m1 -> stk asegs m1 (swlo addr) (swhi addr (lenZ len)) ->
   implA H' (k tt) Q (MS (bvmap_set 10 (Z_to_bv 64 addr) R) F (Z_to_bv 64 pc4) fc rv m' ro)) ->
  implA H (ebind (t_commit addr len) k) Q (MS R F (Z_to_bv 64 pc) fc rv m ro).
Proof.
  intros H k Q R F pc pc4 fc rv m ro addr len w C SV FW EC -> R17 R10 R11 R12 R13 R14 R15 AL IMG L0 TOP AM CONT.
  pose proof (lenZ_bound len ltac:(lia)) as LB.
  eapply implA_ebind with (Q1 := fun u H' ms' =>
      H' = unhide_range (swlo addr) (swhi addr (lenZ len)) (unhide_range addr (addr + lenZ len) H) /\
      ms' = MS (bvmap_set 10 (Z_to_bv 64 addr) R) F (Z_to_bv 64 (pc + 4)) fc rv
              (apply_zeros (wreveal H (swlo addr) (swhi addr (lenZ len)) m) [(Z_to_bv 64 addr, lenW len)]) ro).
  - apply implL_enode. apply (evt_ecall asegs _ R F pc fc rv m ro w FW EC). split.
    + cbn [at_nodeL]. unfold mmap_regs, areg. cbn [ms_svc_pending ms_regs MSsvc]. rewrite R17, R10, R11, R12, R13, R14, R15.
      rewrite w_is0_lit by lia. rewrite (proj2 (Z.eqb_neq len 0)) by lia. unfold SHADOW_OFF.
      repeat split; try reflexivity; unfold page_size; lia.
    + intros rsp u D. pose proof (dec_fixed_Some _ _ _ _ D) as Hs. unfold fixed_eff in Hs.
      rewrite (nretL_MSsvc _ rsp H R F (Z_to_bv 64 pc) (reg_get R 17) fc rv m ro _ _ _ _ Hs).
      cbn [hideL]. rewrite addrZ_eq by lia. rewrite shw_lo_eq, shw_hi_eq.
      rewrite (unhide_zb_window addr (lenZ len) _ IMG ltac:(lia) AM).
      pose proof (lheap_mem_eq H m addr len (swlo addr) (swhi addr (lenZ len)) C ltac:(lia) ltac:(lia) ltac:(lia)) as EM.
      cbv zeta in EM. rewrite EM.
      rewrite lit_add_lit. apply evt_done. split; reflexivity.
  - intros u H' ms' [-> ->]. destruct u.
    pose proof (sw_bounds addr (lenZ len) IMG ltac:(lia)) as (W1 & W2 & W3 & W4 & W5 & W6).
    apply CONT.
    + apply wreveal_mgrow; [exact C| exact W5].
    + apply wreveal_changed.
    + cbv zeta. apply mclean_apply_zeros; try lia.
      * exact (mclean_wreveal H (swlo addr) (swhi addr (lenZ len)) m addr (addr + lenZ len) C).
      * intros x Hx. apply unhide_range_false. apply unhide_range_in. lia.
    + apply shvis_wreveal; try assumption; lia.
    + apply stk_wreveal_window; try assumption; lia.
Qed.

Definition lzk {A} (H : word -> bool) (t : itree nodeL (exc A)) (Q : A -> (word -> bool) -> machine_state -> Prop)
  : machine_state -> Prop := fun ms1 => mclean H (ms_mem ms1) -> implA H t Q ms1.

Lemma implA_go_clean {A} : forall H (t : itree nodeL (exc A)) Q ms,
  mclean H (ms_mem ms) -> evt asegs (lzk H t Q) ms -> implA H t Q ms.
Proof.
  intros H t Q ms C E. eapply implL_evt; [exact (evt_mclean_ms H _ ms C E)|]. intros ms1 [K C1]. exact (K C1).
Qed.

Lemma implA_evt_clean {A} : forall H (t : itree nodeL (exc A)) Q P ms,
  mclean H (ms_mem ms) -> evt asegs P ms ->
  (forall ms', P ms' -> mclean H (ms_mem ms') -> implA H t Q ms') -> implA H t Q ms.
Proof.
  intros H t Q P ms C E K. eapply implL_evt; [exact (evt_mclean_ms H _ ms C E)|]. intros ms1 [HP C1]. exact (K ms1 HP C1).
Qed.

Ltac find_mclean m := match goal with C : mclean _ m |- _ => C end.

Ltac clean_ms_mem C :=
  cbn [ms_mem] in C;
  try (lazymatch type of C with mclean ?Hh (ms_mem (MS _ _ _ _ _ ?m _)) => change (mclean Hh m) in C end).

Ltac lz_go :=
  lazymatch goal with
  | |- ITreeLZ.implL _ _ _ _ _ _ (MS _ _ _ _ _ ?m _) =>
      let C := find_mclean m in eapply implA_go_clean; [ exact C |]; clear C
  | |- evt _ _ _ => idtac
  end.

Ltac lz_here :=
  lazymatch goal with
  | |- evt _ (lzk _ _ _) _ => apply evt_done; let C := fresh "MC" in intros C; clean_ms_mem C
  | |- evt _ (fun _ => lzk _ _ _ _) _ => apply evt_done; let C := fresh "MC" in intros C; clean_ms_mem C
  | |- ITreeLZ.implL _ _ _ _ _ _ _ => idtac
  end.

Ltac lz_ret := lz_here; apply implA_ret.

Ltac find_shvis H m :=
  match goal with
  | S : shvis H m |- _ => S
  | S : shvis H ?mo, W : wmono asegs ?mo m |- _ => constr:(shvis_wmono H mo m S W)
  end.

Lemma munch_anon_grow : forall W m0 m m1 (a b lo hi : Z),
  munch W m0 m -> (forall x, m1 x = m x \/ lo <= bv_unsigned x < hi) -> munch (W ++ [(a, b); (lo, hi)]) m0 m1.
Proof.
  intros W m0 m m1 a b lo hi MU G x Hx. apply outside_app in Hx as [HW HX]. cbn in HX.
  destruct (G x) as [E|R]; [rewrite E; apply MU; exact HW| lia].
Qed.

Ltac lz_grow m m1 G CH a b :=
  transport_grow m m1 G;
  try match goal with S : shvis _ m |- _ => clear S end;
  repeat match goal with
      | MU : munch ?W ?m0 m |- _ =>
          let MU' := fresh "MUg" in pose proof (munch_anon_grow W m0 m m1 a b _ _ MU CH) as MU'; clear MU; rename MU' into MU; cbn [List.app] in MU
      end;
  repeat match goal with
      | GM : gmunch ?W ?m0 m1 |- _ =>
          lazymatch W with
          | context [(a, b)] => fail
          | _ => apply (gmunch_extend W [(a, b)]) in GM; cbn [List.app] in GM
          end
      end;
  try clear CH; try clear G; try clear m.

Ltac lz_mem_zeros :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (apply_zeros ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
    let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
    change (apply_zeros m [(A, Z_to_bv 64 n)]) with (apply_zeros m [(wa a, Z_to_bv 64 n)]) in *;
    let Ha := fresh "Hza" in let Hn := fresh "Hzn" in let Han := fresh "Hzan" in
    assert (Ha : (0 <= a < 2^64)%Z) by lia;
    assert (Hn : (0 <= n < 2^64)%Z) by lia;
    assert (Han : (a + n <= 2^64)%Z) by lia;
    try match goal with Hm : mem_inv segs m |- _ =>
          apply (mem_inv_zeros segs m a n Ha Hn Han) in Hm;
          [| let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; apply a0_ro_addr_false; lia ] end;
    try match goal with S : shvis ?Hh m |- _ => apply (shvis_zeros Hh m a n) in S; [| lia | lia | lia ] end;
    transport_zeros segs m a n Ha Hn Han;
    let Z' := fresh "ZNEW" in
    pose proof (rw_cells_zeros_new segs m a n Ha Hn Han) as Z';
    let m' := fresh "m" in
    remember (apply_zeros m [(wa a, Z_to_bv 64 n)]) as m' eqn:Heqm in *;
    clear Heqm Ha Hn Han; try clear m
  end.

Ltac lz_mem_unmaps :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (apply_unmaps ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
    let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
    change (apply_unmaps m [(A, Z_to_bv 64 n)]) with (apply_unmaps m [(wa a, Z_to_bv 64 n)]) in *;
    let Ha := fresh "Hua" in let Hn := fresh "Hun" in let Han := fresh "Huan" in
    assert (Ha : (0 <= a < 2^64)%Z) by lia;
    assert (Hn : (0 <= n < 2^64)%Z) by lia;
    assert (Han : (a + n <= 2^64)%Z) by lia;
    let WB := fresh "WMB" in pose proof (wmono_but_unmaps a n m Ha Hn Han) as WB;

    repeat match goal with W : wmono segs ?x m |- _ => apply (wmono_but_of_wmono [(a, a + n)%Z]) in W end;
    repeat match goal with W : wmono_but [(a, a + n)%Z] ?x m |- _ =>
             apply (fun Hw => wmono_but_trans [(a, a + n)%Z] x m _ Hw WB) in W end;
    transport_unmaps segs m a n Ha Hn Han;
    let m' := fresh "m" in
    remember (apply_unmaps m [(wa a, Z_to_bv 64 n)]) as m' eqn:Heqm in *;
    clear Heqm Ha Hn Han; try clear WB; try clear m;

    let WU := fresh "WMu" in pose proof (wmono_refl segs m') as WU
  end.

Ltac expand_avoid :=
  repeat match goal with
  | AV : Forall _ ?avoid, HIN : In _ ?avoid |- _ =>
      let h := fresh "AVS" in pose proof (proj1 (List.Forall_forall _ _) AV _ HIN) as h; cbn [fst snd] in h;
      lazymatch type of HIN with In ?iv ?l => change (id (In iv l)) in HIN end
  end.
Ltac restore_avoid := repeat match goal with HIN : id (In ?iv ?l) |- _ => change (In iv l) in HIN end.

Ltac lz_node_side :=
  lazymatch goal with
  | |- fetch_word _ _ = Some _ => vm_compute; reflexivity
  | |- is_ecall _ = true => vm_compute; reflexivity
  | |- reg_get _ _ = _ => first [ reflexivity | fail 0 "node tactic: a register does not hold the expected value (rewrite it into literal form first)" ]
  | _ => first [ reflexivity | lia | assumption | left; reflexivity | right; reflexivity ]
  end.

Ltac lz_cont MC := eapply implA_go_clean; [ exact MC |]; clear MC.

Ltac node_fixed :=
  lz_here;
  lazymatch goal with
  | |- ITreeLZ.implL ?segs _ _ ?H (ebind (enode (LMmapFixed ?addr ?len ?fl) _) _) _ (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with
      | Some ?w =>
          let C := find_mclean m in let pc4 := eval vm_compute in (pc + 4)%Z in
          eapply (implA_fixed fl H _ _ R F pc pc4 fc rv m ro addr len w);
          [ lz_node_side | exact C | lz_node_side | lz_node_side | reflexivity
          | lz_node_side | lz_node_side | lz_node_side | lz_node_side | lz_node_side | lz_node_side | lz_node_side
          | try lz_node_side | try lz_node_side | try lz_node_side | try lz_node_side
          | cbv zeta; let MC := fresh "MC" in intros MC; try clear C;
            try match goal with S : shvis H m |- _ =>
                  apply (shvis_unhide_zeros H m addr (lenZ len)) in S; [| lia | lia | lia ] end;
            lz_cont MC; lz_mem_zeros ]
      end
  end.

Ltac node_madv :=
  lz_here;
  lazymatch goal with
  | |- ITreeLZ.implL ?segs _ _ ?H (ebind (t_madv ?addr ?len) _) _ (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with
      | Some ?w =>
          let C := find_mclean m in let pc4 := eval vm_compute in (pc + 4)%Z in
          eapply (implA_madv H _ _ R F pc pc4 fc rv m ro addr len w);
          [ exact C | lz_node_side | lz_node_side | reflexivity
          | lz_node_side | lz_node_side | lz_node_side | lz_node_side
          | try lz_node_side | try lz_node_side | try lz_node_side | try lz_node_side
          |
            cbv zeta; let MC := fresh "MC" in intros MC; try clear C;
            try match goal with S : shvis H m |- _ =>
                  first [ apply (shvis_hide_unmaps H m addr (lenZ len)) in S; [| lia | lia | lia ] | clear S ] end;
            lz_cont MC; lz_mem_unmaps ]
      end
  end.

Ltac node_unmap :=
  lz_here;
  lazymatch goal with
  | |- ITreeLZ.implL ?segs _ _ ?H (ebind (t_unmap ?addr ?len) _) _ (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with
      | Some ?w =>
          let C := find_mclean m in let pc4 := eval vm_compute in (pc + 4)%Z in
          eapply (implA_unmap H _ _ R F pc pc4 fc rv m ro addr len w);
          [ exact C | lz_node_side | lz_node_side | reflexivity | lz_node_side | lz_node_side | lz_node_side
          | try lz_node_side | try lz_node_side | try lz_node_side | try lz_node_side
          | cbv zeta; let MC := fresh "MC" in intros MC; try clear C;
            try match goal with S : shvis H m |- _ =>
                  first [ apply (shvis_unhide_unmaps H m addr (lenZ len)) in S; [| lia | lia | lia | first [assumption | unfold app_mem; lia] ]
                        | clear S ] end;
            lz_cont MC; lz_mem_unmaps ]
      end
  end.

Ltac node_anon :=
  lz_here;
  lazymatch goal with
  | |- ITreeLZ.implL ?segs _ _ ?H (ebind (t_anon ?len ?avoid) _) _ (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with
      | Some ?w =>
          let C := find_mclean m in let pc4 := eval vm_compute in (pc + 4)%Z in
          let SV := find_shvis H m in
          eapply (implA_anon H _ _ R F pc pc4 fc rv m ro len avoid w);
          [ exact C | exact SV | lz_node_side | lz_node_side | reflexivity | lz_node_side
          | lz_node_side | lz_node_side | lz_node_side | lz_node_side | lz_node_side | lz_node_side
          | try lz_node_side
          | let a := fresh "a" in let AL := fresh "AL" in let IMG := fresh "IMG" in let AM := fresh "AM" in
            let TOP := fresh "TOP" in let AV := fresh "AV" in let G := fresh "G" in let CH := fresh "CH" in let MC := fresh "MC" in
            let SV' := fresh "SV" in let WIN := fresh "WIN" in
            intros a AL IMG AM TOP AV; cbv zeta; intros G CH MC SV' WIN; try clear C;
            let TLOW := fresh "TLOW" in let TCEIL := fresh "TCEIL" in
            pose proof TOP as [TLOW TCEIL]; pose proof (@alloc_ceiling_lt47 _) as C47;

            expand_avoid; restore_avoid;
            let swr := fresh "SWR" in pose proof (sw_range a (lenZ len) IMG ltac:(lia) ltac:(lia)) as swr;
            let m1 := fresh "mw" in
            set (m1 := wreveal H (swlo a) (swhi a (lenZ len)) m) in *;
            lz_grow m m1 G CH a (a + lenZ len)%Z;
            lz_cont MC; lz_mem_zeros;
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mn _) => pose proof (wmono_refl asegs mn) as WMa end ]
      end
  end.

Ltac node_commit :=
  lz_here;
  lazymatch goal with
  | |- ITreeLZ.implL ?segs _ _ ?H (ebind (t_commit ?addr ?len) _) _ (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with
      | Some ?w =>
          let C := find_mclean m in let pc4 := eval vm_compute in (pc + 4)%Z in
          let SV := find_shvis H m in
          eapply (implA_commit H _ _ R F pc pc4 fc rv m ro addr len w);
          [ exact C | exact SV | lz_node_side | lz_node_side | reflexivity | lz_node_side
          | lz_node_side | lz_node_side | lz_node_side | lz_node_side | lz_node_side | lz_node_side
          | try lz_node_side | try lz_node_side | try lz_node_side | try lz_node_side
          | first [assumption | unfold app_mem; lia | idtac]
          | let G := fresh "G" in let CH := fresh "CH" in let MC := fresh "MC" in
            let SV' := fresh "SV" in let WIN := fresh "WIN" in
            cbv zeta; intros G CH MC SV' WIN; try clear C;
            let m1 := fresh "mw" in
            set (m1 := wreveal H (swlo addr) (swhi addr (lenZ len)) m) in *;
            lz_grow m m1 G CH addr (addr + lenZ len)%Z;
            lz_cont MC; lz_mem_zeros;
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mn _) => pose proof (wmono_refl asegs mn) as WMa end ]
      end
  end.

Ltac absorb_footprint MUc m :=
  lazymatch type of MUc with
  | munch ?Wc m _ =>
      match goal with
      | MUq : munch ?Wq ?mq m |- _ =>
          tryif assert_succeeds (assert (sub_fp Wc Wq) by sub_fp_solve)
          then idtac
          else (apply (munch_extend Wq Wc) in MUq; cbn [List.app] in MUq)
      | _ => idtac
      end
  end.

Ltac post_callA segs m :=
  let a := fresh "r" in let H' := fresh "H'" in let ms' := fresh "ms'" in let PO := fresh "POST" in let MC := fresh "MC" in
  intros a H' ms' [PO MC];
  destruct_exs PO;
  let E := fresh "E" in let EH := fresh "EH" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [EH [MUc [WMc PO]]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms'; subst H'; clean_ms_mem MC;
  try destruct_ands PO;
  expand_avoid; restore_avoid;
  try (lazymatch type of MUc with context [swhi ?wa ?wn] =>
         let h := fresh "SWR" in let h2 := fresh "SWB" in
         pose proof (sw_range wa wn ltac:(lia) ltac:(lia) ltac:(lia)) as h;
         pose proof (sw_bounds wa wn ltac:(lia) ltac:(lia)) as h2 end);
  lazymatch type of MUc with
  | munch _ m ?m' =>
      first [
              lazymatch goal with GMc : gmunch _ m m' |- _ => transport_after_gcall segs m m' MUc GMc WMc; clear GMc end
            | absorb_footprint MUc m; transport_after_call segs m m' MUc WMc ];
      clear MUc WMc;
      try match goal with Hh : mem_inv segs m |- _ => clear Hh end;
      try clear m
  end;
  lz_cont MC;
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
       end).

Tactic Notation "callA" uconstr(SPEC) :=
  lz_here;
  lazymatch goal with
  | |- ITreeLZ.implL ?segs _ _ _ _ _ (MS _ _ _ _ _ ?m _) =>
      let C := find_mclean m in
      eapply implA_ebind; [ eapply implA_mclean; [ exact C | eapply SPEC ] | clear C; post_callA segs m ]
  end.

Lemma bind_ret_r {E R} : forall (t : itree E R), ITree.bind E t (fun r => Ret r) = t.
Proof.
  induction t as [r|n k IH]; cbn; [reflexivity|]. f_equal. apply functional_extensionality. intros x. apply IH.
Qed.
Lemma ebind_ret_r {E A} : forall (t : itree E (exc A)), ebind t (fun a => Ret (Ok a)) = t.
Proof.
  intros t. unfold ebind. rewrite <- (bind_ret_r t) at 2. f_equal. apply functional_extensionality. intros [|a]; reflexivity.
Qed.

Section Leaves.
Context {HC : HasCeiling}.

Definition immap_entry : Z := 0x6a1b4.

Definition immap_fixed_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x5 x6 x7 x11 x12 x13 x14 x15 x16 x28 x29 x30 x31 : word) (H : word -> bool) (addr len : Z) (m : word -> option byte)
  : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H' ms' => exists m',
    ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 addr) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 222) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = unhide_range addr (addr + lenZ len) H
    /\ munch [(addr, addr + lenZ len)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' addr [CB (Z.to_nat (lenZ len)) (repeat (Z_to_bv 8 0) (Z.to_nat (lenZ len)))]
    /\ gmunch [(addr, addr + lenZ len)] m m'.

#[using="Type"] Lemma immap_fixed_spec : forall (ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (H : word -> bool) (addr len flags : Z),
  mem_inv asegs m -> mclean H m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 PROT_RW -> a3 = Z_to_bv 64 flags ->
  a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 -> (flags = MAPF_FIXED \/ flags = MAPF_FIXED_NR) ->
  addr mod 4096 = 0 -> 0x609000 <= addr -> 0 < len < 2^47 -> addr + lenZ len <= 2^47 ->
  implA H (enode (LMmapFixed addr len flags) (dec_fixed addr len))
        (immap_fixed_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x5 x6 x7 a1 a2 a3 a4 a5 a6 x28 x29 x30 x31 H addr len m)
        (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 immap_entry) fc None m (seg_rom asegs)).
Proof.
  intros until flags. intros MI C -> -> -> -> -> -> FL AL IMG L0 TOP. unfold immap_entry.
  pose proof (lenZ_bound len ltac:(lia)) as LB.
  pose proof (munch_refl [(addr, addr + lenZ len)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (gmunch_refl [(addr, addr + lenZ len)] m) as GM.
  rewrite <- (ebind_ret_r (enode _ _)).
  lz_go. step.
  node_fixed.
  step.
  lz_ret. unfold immap_fixed_post. finish. reflexivity.
Qed.

Definition immap_anon_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x5 x6 x7 x11 x12 x13 x14 x15 x16 x28 x29 x30 x31 : word) (H : word -> bool) (len : Z) (avoid : list (Z * Z)) (m : word -> option byte)
  : Z -> (word -> bool) -> machine_state -> Prop :=
  fun a H' ms' => exists m',
    ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 a) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 222) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = unhide_range (swlo a) (swhi a (lenZ len)) (unhide_range a (a + lenZ len) H)
    /\ munch [(a, a + lenZ len); (swlo a, swhi a (lenZ len))] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ a mod 4096 = 0 /\ 0x609000 <= a /\ app_mem a (lenZ len) /\ anon_place a (lenZ len)
    /\ Forall (fun iv => a + lenZ len <= fst iv \/ snd iv <= a) avoid
    /\ rw_cells asegs m' a [CB (Z.to_nat (lenZ len)) (repeat (Z_to_bv 8 0) (Z.to_nat (lenZ len)))]
    /\ stk asegs m' (swlo a) (swhi a (lenZ len)) /\ shvis H' m'
    /\ gmunch [(a, a + lenZ len)] m m'.

#[using="Type"] Lemma immap_anon_spec : forall (ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (H : word -> bool) (len : Z) (avoid : list (Z * Z)),
  mem_inv asegs m -> mclean H m -> shvis H m ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 PROT_RW -> a3 = Z_to_bv 64 MAPF_ANON_PRIVATE ->
  a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 -> 0 < len < 2^47 ->
  implA H (t_anon len avoid)
        (immap_anon_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x5 x6 x7 a1 a2 a3 a4 a5 a6 x28 x29 x30 x31 H len avoid m)
        (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 immap_entry) fc None m (seg_rom asegs)).
Proof.
  intros until avoid. intros MI C SV -> -> -> -> -> -> L0. unfold immap_entry.
  pose proof (lenZ_bound len ltac:(lia)) as LB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM. pose proof (gmunch_refl [] m) as GM.
  rewrite <- (ebind_ret_r (t_anon _ _)).
  lz_go. step.
  node_anon.
  step.
  lz_ret. unfold immap_anon_post. finish. reflexivity.
Qed.

Definition immap_commit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x5 x6 x7 x11 x12 x13 x14 x15 x16 x28 x29 x30 x31 : word) (H : word -> bool) (addr len : Z) (m : word -> option byte)
  : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H' ms' => exists m',
    ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 addr) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 222) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = unhide_range (swlo addr) (swhi addr (lenZ len)) (unhide_range addr (addr + lenZ len) H)
    /\ munch [(addr, addr + lenZ len); (swlo addr, swhi addr (lenZ len))] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' addr [CB (Z.to_nat (lenZ len)) (repeat (Z_to_bv 8 0) (Z.to_nat (lenZ len)))]
    /\ stk asegs m' (swlo addr) (swhi addr (lenZ len)) /\ shvis H' m'
    /\ gmunch [(addr, addr + lenZ len)] m m'.

#[using="Type"] Lemma immap_commit_spec : forall (ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (H : word -> bool) (addr len : Z),
  mem_inv asegs m -> mclean H m -> shvis H m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 PROT_RW -> a3 = Z_to_bv 64 MAPF_FIXED ->
  a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
  addr mod 4096 = 0 -> 0x609000 <= addr -> 0 < len < 2^47 -> addr + lenZ len <= 2^47 -> app_mem addr (lenZ len) ->
  implA H (t_commit addr len)
        (immap_commit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x5 x6 x7 a1 a2 a3 a4 a5 a6 x28 x29 x30 x31 H addr len m)
        (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 immap_entry) fc None m (seg_rom asegs)).
Proof.
  intros until len. intros MI C SV -> -> -> -> -> -> AL IMG L0 TOP AM. unfold immap_entry.
  pose proof (lenZ_bound len ltac:(lia)) as LB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM. pose proof (gmunch_refl [] m) as GM.
  rewrite <- (ebind_ret_r (t_commit _ _)).
  lz_go. step.
  node_commit.
  step.
  lz_ret. unfold immap_commit_post. finish. reflexivity.
Qed.
End Leaves.

Ltac cond_z := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; rewrite ?unsigned_lit by lia; solve_cond_rec.
Ltac if_true_z := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota| symmetry; cond_z] end.
Ltac if_false_z := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota| symmetry; cond_z] end.
