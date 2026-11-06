(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* The allocation edition's mmap and mprotect checkers, copied here as local definitions ([check_mmap_ed],
   [check_mprotect_ed]), and the two transfer lemmas that make them a derived characterisation of the unedited
   model under [ACFG]: an outcome the unedited checker accepts and that is not a spurious refusal is one the
   edited checker accepts ([check_mmap_ed_fwd], outside the MAP_FIXED read-write destructive refusal the edition
   deletes and a forced refusal admits), and an outcome the edited checker accepts is a non-spurious outcome of
   the unedited one ([check_mmap_ed_bwd]). Nothing here assumes the edited model. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Cfg.
Import ListNotations.
Open Scope bv_scope.

Definition w_nilb {A} (l : list A) : bool :=
  match l with [] => true | _ => false end.

Lemma w_nilb_true {A} (l : list A) : w_nilb l = true -> l = [].
Proof. destruct l; [reflexivity|discriminate]. Qed.

Definition check_mmap_ed (addr len prot flags fd off : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (mmap_off_aligned_b off)
  then if mmap_pglen_ok_b len then check_ret_only eff (errno_ret EINVAL) m [] else CheckUnmodeled
  else
  if negb (mmap_anon_b flags) then CheckUnmodeled
  else
  if w_is0 len
  then if mmap_plain_anon_b flags then check_ret_only eff (errno_ret EINVAL) m [] else CheckUnmodeled
  else
  if mmap_modeled_b prot flags off
  then
    match eff with
    | mkEffect r [] zs =>
        if errno_ret_in (mmap_errnos_when (mmap_grant_refusable flags m (page_round_up_Z (bv_unsigned len)))) r
        then if w_nilb zs then CheckOk m [] else CheckReject
        else
          let nZ := page_round_up_Z (bv_unsigned len) in
          let n := Z_to_bv 64 nZ in
          if (bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
             && (bv_unsigned r + nZ <=? alloc_top (m_vmmaps m))%Z
             && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) r n
             && mmap_noreserve_backed_ok flags m nZ && listNN_eqb zs [(r, n)]
          then CheckOk (with_mmap_backing flags r n
                 (with_vmmaps
                    {| vm_reserved := vm_reserved (m_vmmaps m);
                       vm_maps := (r, n) :: vm_maps (m_vmmaps m);
                       vm_noaccess := vm_noaccess (m_vmmaps m);
                       vm_start_brk := vm_start_brk (m_vmmaps m);
                       vm_brk := vm_brk (m_vmmaps m);
                       vm_limit := vm_limit (m_vmmaps m);
                       vm_mmap_base := vm_mmap_base (m_vmmaps m);
                       vm_init_sp := vm_init_sp (m_vmmaps m) |} m)) []
          else CheckReject
    | _ => CheckReject
    end
  else
  if mmap_noaccess_b prot flags off
  then
    match eff with
    | {| eff_ret := r; eff_writes := []; eff_zeros := []; eff_unmaps := us; eff_copies := []; eff_copyins := [] |} =>
        if errno_ret_in (mmap_errnos_when (mmap_reserve_refusable m (page_round_up_Z (bv_unsigned len)))) r
        then if w_nilb us then CheckOk m [] else CheckReject
        else
          let nZ := page_round_up_Z (bv_unsigned len) in
          let n := Z_to_bv 64 nZ in
          if (bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
             && (bv_unsigned r + nZ <=? alloc_top (m_vmmaps m))%Z
             && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) r n
             && listNN_eqb us [(r, n)]
          then CheckOk (with_mmap_backing flags r n
                 (with_vmmaps
                    {| vm_reserved := vm_reserved (m_vmmaps m);
                       vm_maps := (r, n) :: vm_maps (m_vmmaps m);
                       vm_noaccess := (r, n) :: vm_noaccess (m_vmmaps m);
                       vm_start_brk := vm_start_brk (m_vmmaps m);
                       vm_brk := vm_brk (m_vmmaps m);
                       vm_limit := vm_limit (m_vmmaps m);
                       vm_mmap_base := vm_mmap_base (m_vmmaps m);
                       vm_init_sp := vm_init_sp (m_vmmaps m) |} m)) []
          else CheckReject
    | _ => CheckReject
    end
  else
  if mmap_fixed_noaccess_b prot flags off
  then
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z then check_ret_only eff (errno_ret ENOMEM) m []
    else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z then CheckUnmodeled
    else if negb (bv_unsigned addr mod page_size =? 0)%Z then check_ret_only eff (errno_ret EINVAL) m []
    else if negb (0 <? bv_unsigned addr)%Z then CheckUnmodeled
    else
    let n := Z_to_bv 64 nZ in
    if region_free (vm_reserved (m_vmmaps m)) addr n && map_contains (vm_maps (m_vmmaps m)) addr n
    then
      match eff with
      | {| eff_ret := r; eff_writes := []; eff_zeros := []; eff_unmaps := us; eff_copies := []; eff_copyins := [] |} =>
          if errno_ret_in (mmap_errnos_when false) r
          then
            match us with
            | [] => CheckOk m []
            | _ :: _ =>
                if errno_ret_in mmap_destructive_errnos r && listNN_eqb us [(addr, n)]
                then CheckOk (with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) []
                else CheckReject
            end
          else
          if bv_eqb r addr && listNN_eqb us [(addr, n)]
          then CheckOk (with_mmap_replacement flags addr n
                 (with_vmmaps
                    {| vm_reserved := vm_reserved (m_vmmaps m);
                       vm_maps := vm_maps (m_vmmaps m);
                       vm_noaccess := (addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n);
                       vm_start_brk := vm_start_brk (m_vmmaps m);
                       vm_brk := vm_brk (m_vmmaps m);
                       vm_limit := vm_limit (m_vmmaps m);
                       vm_mmap_base := vm_mmap_base (m_vmmaps m);
                       vm_init_sp := vm_init_sp (m_vmmaps m) |} m)) []
          else CheckReject
      | _ => CheckReject
      end
    else
    if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n
    then
      match eff with
      | {| eff_ret := r; eff_writes := []; eff_zeros := []; eff_unmaps := us; eff_copies := []; eff_copyins := [] |} =>
          if errno_ret_in (mmap_errnos_when false) r
          then match us with [] => CheckOk m [] | _ :: _ => CheckReject end
          else
          if bv_eqb r addr && listNN_eqb us [(addr, n)]
          then CheckOk (with_mmap_backing flags addr n
                 (with_vmmaps
                    {| vm_reserved := vm_reserved (m_vmmaps m);
                       vm_maps := (addr, n) :: vm_maps (m_vmmaps m);
                       vm_noaccess := (addr, n) :: vm_noaccess (m_vmmaps m);
                       vm_start_brk := vm_start_brk (m_vmmaps m);
                       vm_brk := vm_brk (m_vmmaps m);
                       vm_limit := vm_limit (m_vmmaps m);
                       vm_mmap_base := vm_mmap_base (m_vmmaps m);
                       vm_init_sp := vm_init_sp (m_vmmaps m) |} m)) []
          else CheckReject
      | _ => CheckReject
      end
    else
    if region_free (vm_reserved (m_vmmaps m)) addr n
    then
      match eff with
      | {| eff_ret := r; eff_writes := []; eff_zeros := []; eff_unmaps := us; eff_copies := []; eff_copyins := [] |} =>
          if errno_ret_in (mmap_errnos_when false) r
          then
            match us with
            | [] => CheckOk m []
            | _ :: _ =>
                if errno_ret_in mmap_destructive_errnos r && listNN_eqb us [(addr, n)]
                then CheckOk (with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) []
                else CheckReject
            end
          else
          if bv_eqb r addr && listNN_eqb us [(addr, n)]
          then CheckOk (with_mmap_replacement flags addr n
                 (with_vmmaps (mmap_fixed_noaccess_span_next (m_vmmaps m) addr n) m)) []
          else CheckReject
      | _ => CheckReject
      end
    else CheckUnmodeled
  else
  if mmap_fixed_rw_b prot flags off
  then
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z then check_ret_only eff (errno_ret ENOMEM) m []
    else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z then CheckUnmodeled
    else if negb (bv_unsigned addr mod page_size =? 0)%Z then check_ret_only eff (errno_ret EINVAL) m []
    else if negb (0 <? bv_unsigned addr)%Z then CheckUnmodeled
    else
    let n := Z_to_bv 64 nZ in
    if region_free (vm_reserved (m_vmmaps m)) addr n && map_contains (vm_maps (m_vmmaps m)) addr n
    then
      match eff with
      | {| eff_ret := r; eff_writes := []; eff_zeros := zs; eff_unmaps := us; eff_copies := []; eff_copyins := [] |} =>
          if errno_ret_in (mmap_errnos_when (mmap_fixed_commit_refusable flags m addr n)) r
          then
            match zs with
            | [] =>
                match us with
                | [] => CheckOk m []
                | _ :: _ =>
                    if errno_ret_in mmap_destructive_errnos r && listNN_eqb us [(addr, n)]
                    then CheckOk (with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) []
                    else CheckReject
                end
            | _ :: _ => CheckReject
            end
          else
            match us with
            | [] =>
                if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_fixed_rw_budget_ok flags m addr n
                then CheckOk (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr n) m)) []
                else CheckReject
            | _ :: _ => CheckReject
            end
      | _ => CheckReject
      end
    else
    if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n
    then
      match eff with
      | mkEffect r [] zs =>
          if errno_ret_in (mmap_errnos_when (mmap_fixed_fresh_refusable flags m nZ)) r
          then if w_nilb zs then CheckOk m [] else CheckReject
          else
            if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags m nZ
            then CheckOk (with_mmap_backing flags addr n
                   (with_vmmaps
                      {| vm_reserved := vm_reserved (m_vmmaps m);
                         vm_maps := (addr, n) :: vm_maps (m_vmmaps m);
                         vm_noaccess := vm_noaccess (m_vmmaps m);
                         vm_start_brk := vm_start_brk (m_vmmaps m);
                         vm_brk := vm_brk (m_vmmaps m);
                         vm_limit := vm_limit (m_vmmaps m);
                         vm_mmap_base := vm_mmap_base (m_vmmaps m);
                         vm_init_sp := vm_init_sp (m_vmmaps m) |} m)) []
            else CheckReject
      | _ => CheckReject
      end
    else
    if region_free (vm_reserved (m_vmmaps m)) addr n
    then
      match eff with
      | {| eff_ret := r; eff_writes := []; eff_zeros := zs; eff_unmaps := us; eff_copies := []; eff_copyins := [] |} =>
          if errno_ret_in (mmap_errnos_when (mmap_fixed_span_refusable flags m addr n)) r
          then
            match zs with
            | [] =>
                match us with
                | [] => CheckOk m []
                | _ :: _ =>
                    if errno_ret_in mmap_destructive_errnos r && listNN_eqb us [(addr, n)]
                    then CheckOk (with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) []
                    else CheckReject
                end
            | _ :: _ => CheckReject
            end
          else
            match us with
            | [] =>
                if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_fixed_rw_span_budget_ok flags m addr n
                then CheckOk (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps m) addr n) m)) []
                else CheckReject
            | _ :: _ => CheckReject
            end
      | _ => CheckReject
      end
    else CheckUnmodeled
  else
  if mmap_noreplace_noaccess_b prot flags off
  then
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z then check_ret_only eff (errno_ret ENOMEM) m []
    else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z then CheckUnmodeled
    else if negb (bv_unsigned addr mod page_size =? 0)%Z then check_ret_only eff (errno_ret EINVAL) m []
    else if negb (0 <? bv_unsigned addr)%Z then CheckUnmodeled
    else
    let n := Z_to_bv 64 nZ in
    if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n
    then
      match eff with
      | {| eff_ret := r; eff_writes := []; eff_zeros := []; eff_unmaps := us; eff_copies := []; eff_copyins := [] |} =>
          if errno_ret_in (mmap_errnos_when false) r
          then match us with [] => CheckOk m [] | _ :: _ => CheckReject end
          else
          if bv_eqb r addr && listNN_eqb us [(addr, n)]
          then CheckOk (with_mmap_backing flags addr n
                 (with_vmmaps
                    {| vm_reserved := vm_reserved (m_vmmaps m);
                       vm_maps := (addr, n) :: vm_maps (m_vmmaps m);
                       vm_noaccess := (addr, n) :: vm_noaccess (m_vmmaps m);
                       vm_start_brk := vm_start_brk (m_vmmaps m);
                       vm_brk := vm_brk (m_vmmaps m);
                       vm_limit := vm_limit (m_vmmaps m);
                       vm_mmap_base := vm_mmap_base (m_vmmaps m);
                       vm_init_sp := vm_init_sp (m_vmmaps m) |} m)) []
          else CheckReject
      | _ => CheckReject
      end
    else
      match eff with
      | mkEffect r [] [] =>
          if errno_ret_in (mmap_errnos_when false) r || bv_eqb r (errno_ret EEXIST) then CheckOk m [] else CheckReject
      | _ => CheckReject
      end
  else
  if mmap_noreplace_rw_b prot flags off
  then
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z then check_ret_only eff (errno_ret ENOMEM) m []
    else if negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m))%Z then CheckUnmodeled
    else if negb (bv_unsigned addr mod page_size =? 0)%Z then check_ret_only eff (errno_ret EINVAL) m []
    else if negb (0 <? bv_unsigned addr)%Z then CheckUnmodeled
    else
    let n := Z_to_bv 64 nZ in
    if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n
    then
      match eff with
      | mkEffect r [] zs =>
          if errno_ret_in (mmap_errnos_when (mmap_fixed_fresh_refusable flags m nZ)) r
          then if w_nilb zs then CheckOk m [] else CheckReject
          else
            if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags m nZ
            then CheckOk (with_mmap_backing flags addr n
                   (with_vmmaps
                      {| vm_reserved := vm_reserved (m_vmmaps m);
                         vm_maps := (addr, n) :: vm_maps (m_vmmaps m);
                         vm_noaccess := vm_noaccess (m_vmmaps m);
                         vm_start_brk := vm_start_brk (m_vmmaps m);
                         vm_brk := vm_brk (m_vmmaps m);
                         vm_limit := vm_limit (m_vmmaps m);
                         vm_mmap_base := vm_mmap_base (m_vmmaps m);
                         vm_init_sp := vm_init_sp (m_vmmaps m) |} m)) []
            else CheckReject
      | _ => CheckReject
      end
    else
      match eff with
      | mkEffect r [] [] =>
          if errno_ret_in (mmap_errnos_when false) r || bv_eqb r (errno_ret EEXIST) then CheckOk m [] else CheckReject
      | _ => CheckReject
      end
  else CheckUnmodeled.

Definition check_mprotect_ed (addr len prot : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if mprotect_grows_conflict_b prot then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (bv_unsigned addr mod page_size =? 0)%Z then check_ret_only eff (errno_ret EINVAL) m []
  else if w_is0 len then check_ret_only eff (Z_to_bv 64 0) m []
  else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z
  then check_ret_only eff (errno_ret ENOMEM) m []
  else if negb (mprotect_modeled_b prot) then CheckUnmodeled
  else
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  if map_contains (vm_noaccess (m_vmmaps m)) addr n && map_contains (vm_maps (m_vmmaps m)) addr n
  then
    match eff with
    | mkEffect r [] zs =>
        if errno_ret_in (mprotect_errnos_when (mprotect_refusable m addr n)) r
        then match zs with [] => CheckOk m [] | _ :: _ => CheckReject end
        else
          if mprotect_budget_ok m addr n && w_is0 r && listNN_eqb zs [(addr, n)]
          then CheckOk (mprotect_model_next m addr n) []
          else CheckReject
    | _ => CheckReject
    end
  else
  if map_contains (vm_maps (m_vmmaps m)) addr n && region_free (vm_noaccess (m_vmmaps m)) addr n
  then
    match eff with
    | mkEffect r [] [] => if w_is0 r then CheckOk m [] else CheckReject
    | _ => CheckReject
    end
  else CheckUnmodeled.

Ltac same := let H := fresh "H" in intros H; exact H.

Lemma errno_ret_in_when_false_of : forall b r,
  errno_ret_in mmap_errnos r = false -> errno_ret_in (mmap_errnos_when b) r = false.
Proof.
  intros b r Free.
  destruct b; [rewrite mmap_errnos_when_true; exact Free | rewrite mmap_errnos_when_false; reflexivity].
Qed.

Lemma errno_ret_in_mprotect_when_false_of : forall b r,
  errno_ret_in mprotect_errnos r = false -> errno_ret_in (mprotect_errnos_when b) r = false.
Proof.
  intros b r Free.
  destruct b; [exact Free | rewrite mprotect_errnos_when_false; reflexivity].
Qed.

Lemma aligned_not_mmap_errno : forall a : word,
  (bv_unsigned a mod page_size = 0)%Z -> errno_ret_in mmap_errnos a = false.
Proof. intros a H. exact (ret_in_errnos_ENOMEM_aligned a H). Qed.

Lemma eexist_not_mmap_errno : errno_ret_in mmap_errnos (errno_ret EEXIST) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma zero_not_mprotect_errno : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false.
Proof. exact ret_in_errnos_ENOMEM_zero. Qed.

Lemma listNN_eqb_refl' : forall l, listNN_eqb l l = true.
Proof. intros l. apply listNN_eqb_eq. reflexivity. Qed.

(** An outcome is forced when, if it is a refusal, every outcome the checker accepts at the same arguments and
    model is one. *)
Definition forced_mmap (addr len prot flags fd off : word) (m : Model) (eff : SyscallEffect) : Prop :=
  errno_ret_in mmap_errnos (eff_ret eff) = true ->
  forall eff2 m2 evs2, check_mmap addr len prot flags fd off eff2 m = CheckOk m2 evs2 ->
  errno_ret_in mmap_errnos (eff_ret eff2) = true.

Definition forced_mprotect (addr len prot : word) (m : Model) (eff : SyscallEffect) : Prop :=
  errno_ret_in mprotect_errnos (eff_ret eff) = true ->
  forall eff2 m2 evs2, check_mprotect addr len prot eff2 m = CheckOk m2 evs2 ->
  errno_ret_in mprotect_errnos (eff_ret eff2) = true.

(** The one outcome the edition deletes and a forced refusal admits: in a MAP_FIXED read-write arm, a refusal that
    destroys the range. Excluded when the outcome destroys nothing, or when the request commits over an existing
    mapping whose budget test passes (then a refusal is never forced). *)
Definition mmap_corner_free (addr len prot flags off : word) (m : Model) (eff : SyscallEffect) : Prop :=
  mmap_fixed_rw_b prot flags off = true ->
  eff_unmaps eff = [] \/
  (region_free (vm_reserved (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
   && map_contains (vm_maps (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true
   /\ mmap_fixed_rw_budget_ok flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true).

Lemma check_mmap_ed_fwd : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  forced_mmap addr len prot flags fd off m eff ->
  mmap_corner_free addr len prot flags off m eff ->
  check_mmap_ed addr len prot flags fd off eff m = CheckOk m' evs.
Proof.
  intros addr len prot flags fd off eff m m' evs Old Frc Crn.
  destruct (errno_ret_in mmap_errnos (eff_ret eff)) eqn:Rfs.
  2:{ (* not a refusal: no gated refusal test fires, and the two bodies agree *)
    destruct eff as [r ws zs us cs ci]. cbn [eff_ret] in Rfs.
    unfold check_mmap_ed. unfold check_mmap in Old.
    rewrite !(errno_ret_in_when_false_of _ r Rfs). rewrite !Rfs in Old. exact Old. }
  (* a refusal: every outcome the unedited checker accepts at these arguments is one too *)
  specialize (Frc Rfs).
  unfold check_mmap_ed. unfold check_mmap in Old, Frc. unfold mmap_corner_free in Crn.
  set (nZ := page_round_up_Z (bv_unsigned len)) in *.
  set (n := Z_to_bv 64 nZ) in *.
  destruct (negb (mmap_off_aligned_b off)); [exact Old|].
  destruct (negb (mmap_anon_b flags)); [exact Old|].
  destruct (w_is0 len); [exact Old|].
  destruct (mmap_modeled_b prot flags off).
  { destruct (mmap_grant_refusable flags m nZ) eqn:Rv.
    - destruct eff as [r ws [|z zs] us cs ci]; exact Old.
    - exfalso.
      destruct (not_refusable_grant_conj flags m nZ Rv) as [Back [a (Aln & Pos & Top & Free)]].
      fold n in Free. pose proof (aligned_not_mmap_errno a Aln) as Plain.
      assert (Bad : errno_ret_in mmap_errnos a = true).
      { eapply (Frc (mkEffectU a [] [(a, n)] [] [] [])). cbv beta iota.
        rewrite Plain, Aln, (proj2 (Z.ltb_lt _ _) Pos), (proj2 (Z.leb_le _ _) Top), Free, Back, listNN_eqb_refl'.
        reflexivity. }
      congruence. }
  destruct (mmap_noaccess_b prot flags off).
  { destruct (mmap_reserve_refusable m nZ) eqn:Rv.
    - destruct eff as [r ws zs [|u us] cs ci]; exact Old.
    - exfalso.
      destruct (not_refusable_reserve_conj m nZ Rv) as [a (Aln & Pos & Top & Free)].
      fold n in Free. pose proof (aligned_not_mmap_errno a Aln) as Plain.
      assert (Bad : errno_ret_in mmap_errnos a = true).
      { eapply (Frc (mkEffectU a [] [] [(a, n)] [] [])). cbv beta iota.
        rewrite Plain, Aln, (proj2 (Z.ltb_lt _ _) Pos), (proj2 (Z.leb_le _ _) Top), Free, listNN_eqb_refl'.
        reflexivity. }
      congruence. }
  destruct (two_pow_64 <=? bv_unsigned addr + nZ)%Z; [exact Old|].
  destruct (negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m)))%Z; [exact Old|].
  destruct (negb (bv_unsigned addr mod page_size =? 0))%Z eqn:Galn; [exact Old|].
  destruct (negb (0 <? bv_unsigned addr))%Z; [exact Old|].
  apply negb_false_iff, Z.eqb_eq in Galn.
  pose proof (aligned_not_mmap_errno addr Galn) as Plain.
  destruct (mmap_fixed_noaccess_b prot flags off).
  { (* three sub-arms accept a grant at [addr] (with unmaps [(addr, n)]), so a refusal is never forced there;
       the fourth returns CheckUnmodeled, which contradicts [Old] *)
    enough (Bad : errno_ret_in mmap_errnos addr = true) by congruence.
    destruct (region_free (vm_reserved (m_vmmaps m)) addr n && map_contains (vm_maps (m_vmmaps m)) addr n).
    2: destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n).
    3: destruct (region_free (vm_reserved (m_vmmaps m)) addr n); [|discriminate Old].
    all: eapply (Frc (mkEffectU addr [] [] [(addr, n)] [] [])); cbv beta iota;
         rewrite Plain, bv_eqb_refl, listNN_eqb_refl'; reflexivity. }
  destruct (mmap_fixed_rw_b prot flags off).
  { specialize (Crn eq_refl).
    destruct (region_free (vm_reserved (m_vmmaps m)) addr n && map_contains (vm_maps (m_vmmaps m)) addr n).
    - destruct (mmap_fixed_commit_refusable flags m addr n) eqn:Rv.
      + destruct eff as [r ws [|z zs] [|u us] cs ci]; try exact Old.
        exfalso. destruct Crn as [Kept | [_ Bud]]; [discriminate Kept|].
        unfold mmap_fixed_commit_refusable in Rv. rewrite Bud in Rv. discriminate Rv.
      + exfalso. unfold mmap_fixed_commit_refusable in Rv.
        destruct (mmap_fixed_rw_budget_ok flags m addr n) eqn:Bud; [|discriminate Rv].
        assert (Bad : errno_ret_in mmap_errnos addr = true).
        { eapply (Frc (mkEffectU addr [] [(addr, n)] [] [] [])). cbv beta iota.
          rewrite Plain, bv_eqb_refl, listNN_eqb_refl'. reflexivity. }
        congruence.
    - destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n).
      + destruct (mmap_fixed_fresh_refusable flags m nZ) eqn:Rv.
        * destruct eff as [r ws [|z zs] us cs ci]; exact Old.
        * exfalso. unfold mmap_fixed_fresh_refusable in Rv.
          destruct (mmap_noreserve_backed_ok flags m nZ) eqn:Back; [|discriminate Rv].
          assert (Bad : errno_ret_in mmap_errnos addr = true).
          { eapply (Frc (mkEffectU addr [] [(addr, n)] [] [] [])). cbv beta iota.
            rewrite Plain, bv_eqb_refl, listNN_eqb_refl'. reflexivity. }
          congruence.
      + destruct (region_free (vm_reserved (m_vmmaps m)) addr n); [|exact Old].
        destruct (mmap_fixed_span_refusable flags m addr n) eqn:Rv.
        * destruct eff as [r ws [|z zs] [|u us] cs ci]; try exact Old.
          exfalso. destruct Crn as [Kept | [Never _]]; [discriminate Kept | discriminate Never].
        * exfalso. unfold mmap_fixed_span_refusable in Rv.
          destruct (mmap_fixed_rw_span_budget_ok flags m addr n) eqn:Bud; [|discriminate Rv].
          assert (Bad : errno_ret_in mmap_errnos addr = true).
          { eapply (Frc (mkEffectU addr [] [(addr, n)] [] [] [])). cbv beta iota.
            rewrite Plain, bv_eqb_refl, listNN_eqb_refl'. reflexivity. }
          congruence. }
  destruct (mmap_noreplace_noaccess_b prot flags off).
  { exfalso. destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n).
    - assert (Bad : errno_ret_in mmap_errnos addr = true).
      { eapply (Frc (mkEffectU addr [] [] [(addr, n)] [] [])). cbv beta iota.
        rewrite Plain, bv_eqb_refl, listNN_eqb_refl'. reflexivity. }
      congruence.
    - assert (Bad : errno_ret_in mmap_errnos (errno_ret EEXIST) = true).
      { eapply (Frc (mkEffectU (errno_ret EEXIST) [] [] [] [] [])). cbv beta iota.
        rewrite bv_eqb_refl, orb_true_r. reflexivity. }
      rewrite eexist_not_mmap_errno in Bad. discriminate Bad. }
  destruct (mmap_noreplace_rw_b prot flags off); [|exact Old].
  destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n).
  - destruct (mmap_fixed_fresh_refusable flags m nZ) eqn:Rv.
    + destruct eff as [r ws [|z zs] us cs ci]; exact Old.
    + exfalso. unfold mmap_fixed_fresh_refusable in Rv.
      destruct (mmap_noreserve_backed_ok flags m nZ) eqn:Back; [|discriminate Rv].
      assert (Bad : errno_ret_in mmap_errnos addr = true).
      { eapply (Frc (mkEffectU addr [] [(addr, n)] [] [] [])). cbv beta iota.
        rewrite Plain, bv_eqb_refl, listNN_eqb_refl'. reflexivity. }
      congruence.
  - exfalso.
    assert (Bad : errno_ret_in mmap_errnos (errno_ret EEXIST) = true).
    { eapply (Frc (mkEffectU (errno_ret EEXIST) [] [] [] [] [])). cbv beta iota.
      rewrite bv_eqb_refl, orb_true_r. reflexivity. }
    rewrite eexist_not_mmap_errno in Bad. discriminate Bad.
Qed.

Lemma check_mprotect_ed_fwd : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs ->
  forced_mprotect addr len prot m eff ->
  check_mprotect_ed addr len prot eff m = CheckOk m' evs.
Proof.
  intros addr len prot eff m m' evs Old Frc.
  destruct (errno_ret_in mprotect_errnos (eff_ret eff)) eqn:Rfs.
  2:{ destruct eff as [r ws zs us cs ci]. cbn [eff_ret] in Rfs.
    unfold check_mprotect_ed. unfold check_mprotect in Old.
    rewrite (errno_ret_in_mprotect_when_false_of _ r Rfs). rewrite Rfs in Old. exact Old. }
  specialize (Frc Rfs).
  unfold check_mprotect_ed. unfold check_mprotect in Old, Frc.
  set (n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) in *.
  destruct (mprotect_grows_conflict_b prot); [exact Old|].
  destruct (negb (bv_unsigned addr mod page_size =? 0))%Z; [exact Old|].
  destruct (w_is0 len); [exact Old|].
  destruct (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z; [exact Old|].
  destruct (negb (mprotect_modeled_b prot)); [exact Old|].
  destruct (map_contains (vm_noaccess (m_vmmaps m)) addr n && map_contains (vm_maps (m_vmmaps m)) addr n);
    [|exact Old].
  destruct (mprotect_refusable m addr n) eqn:Rv.
  - destruct eff as [r ws [|z zs] us cs ci]; exact Old.
  - (* the budget passes, so the zero-returning grant was open *)
    exfalso. apply mprotect_refusable_false_iff in Rv.
    assert (Bad : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = true).
    { eapply (Frc (mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [])). cbv beta iota.
      rewrite zero_not_mprotect_errno, Rv, listNN_eqb_refl'. reflexivity. }
    rewrite zero_not_mprotect_errno in Bad. discriminate Bad.
Qed.

Lemma refusal_neq : forall r a : word,
  errno_ret_in mmap_errnos r = true -> errno_ret_in mmap_errnos a = false -> bv_eqb r a = false.
Proof.
  intros r a Hr Ha. destruct (bv_eqb r a) eqn:Q; [|reflexivity].
  apply bv_eqb_eq in Q. subst a. congruence.
Qed.

Lemma forced_mmap_nonrefusal : forall addr len prot flags fd off m eff,
  errno_ret_in mmap_errnos (eff_ret eff) = false -> forced_mmap addr len prot flags fd off m eff.
Proof. intros addr len prot flags fd off m eff H Hr. congruence. Qed.

Lemma forced_mprotect_nonrefusal : forall addr len prot m eff,
  errno_ret_in mprotect_errnos (eff_ret eff) = false -> forced_mprotect addr len prot m eff.
Proof. intros addr len prot m eff H Hr. congruence. Qed.

(** The condition of an accepting [if] whose else branch rejects. *)
Ltac if_cond Acc Cnd :=
  lazymatch type of Acc with
  | (if ?c then _ else _) = CheckOk _ _ => destruct c eqn:Cnd; [|discriminate Acc]
  end.

Ltac andb_split C :=
  repeat match type of C with
  | (_ && _) = true => let C' := fresh "C" in apply andb_prop in C as [C C']
  end.

Lemma check_mmap_ed_bwd : forall addr len prot flags fd off eff m m' evs,
  check_mmap_ed addr len prot flags fd off eff m = CheckOk m' evs ->
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs
  /\ forced_mmap addr len prot flags fd off m eff.
Proof.
  intros addr len prot flags fd off eff m m' evs New.
  assert (Einval : forall e, check_ret_only e (errno_ret EINVAL) m [] = CheckOk m' evs ->
                             errno_ret_in mmap_errnos (eff_ret e) = false).
  { intros e Acc. apply check_ret_only_ok_iff in Acc as [-> _]. vm_compute. reflexivity. }
  assert (Enomem : forall e m2 evs2, check_ret_only e (errno_ret ENOMEM) m [] = CheckOk m2 evs2 ->
                                     errno_ret_in mmap_errnos (eff_ret e) = true).
  { intros e m2 evs2 Acc. apply check_ret_only_ok_iff in Acc as [-> _].
    exact (errno_ret_in_intro mmap_errnos ENOMEM (or_introl eq_refl)). }
  assert (Taken : (match eff with
                   | mkEffect r [] [] =>
                       if errno_ret_in (mmap_errnos_when false) r || bv_eqb r (errno_ret EEXIST)
                       then CheckOk m [] else CheckReject
                   | _ => CheckReject
                   end = CheckOk m' evs) ->
                  (match eff with
                   | mkEffect r [] [] =>
                       if errno_ret_in mmap_errnos r || bv_eqb r (errno_ret EEXIST) then CheckOk m [] else CheckReject
                   | _ => CheckReject
                   end = CheckOk m' evs) /\
                  errno_ret_in mmap_errnos (eff_ret eff) = false).
  { intros Acc. destruct eff as [r ws zs us cs ci]. destruct ws, zs, us, cs, ci; try discriminate Acc.
    if_cond Acc Pick. change (bv_eqb r (errno_ret EEXIST) = true) in Pick.
    apply bv_eqb_eq in Pick. subst r.
    rewrite bv_eqb_refl, orb_true_r. split; [exact Acc | exact eexist_not_mmap_errno]. }
  unfold check_mmap_ed in New. unfold forced_mmap, check_mmap.
  set (nZ := page_round_up_Z (bv_unsigned len)) in *.
  set (n := Z_to_bv 64 nZ) in *.
  destruct (negb (mmap_off_aligned_b off)).
  { destruct (mmap_pglen_ok_b len); [|discriminate New].
    split; [exact New | intros Rfs; rewrite (Einval eff New) in Rfs; discriminate Rfs]. }
  destruct (negb (mmap_anon_b flags)); [discriminate New|].
  destruct (w_is0 len).
  { destruct (mmap_plain_anon_b flags); [|discriminate New].
    split; [exact New | intros Rfs; rewrite (Einval eff New) in Rfs; discriminate Rfs]. }
  destruct (mmap_modeled_b prot flags off).
  { destruct eff as [r ws zs us cs ci]. destruct ws, us, cs, ci; try discriminate New.
    destruct (errno_ret_in (mmap_errnos_when (mmap_grant_refusable flags m nZ)) r) eqn:Er.
    - destruct (mmap_grant_refusable flags m nZ) eqn:Rv; [|discriminate Er].
      change (errno_ret_in mmap_errnos r = true) in Er.
      destruct zs; [|discriminate New].
      split; [rewrite Er; exact New|].
      intros _ eff2 m2 evs2 Old2. destruct eff2 as [r2 ws2 zs2 us2 cs2 ci2]. cbn [eff_ret].
      destruct (errno_ret_in mmap_errnos r2) eqn:Rfs2; [reflexivity|]. exfalso.
      destruct ws2, us2, cs2, ci2; try discriminate Old2.
      if_cond Old2 Cnd. rewrite !andb_true_iff in Cnd.
      destruct Cnd as (((((Aln & Pos) & Top) & Free) & Back) & _).
      apply Z.eqb_eq in Aln. apply Z.ltb_lt in Pos. apply Z.leb_le in Top.
      rewrite (grant_conj_not_refusable flags m nZ r2 Aln Pos Top Free Back) in Rv. discriminate Rv.
    - if_cond New Cnd. rewrite !andb_true_iff in Cnd.
      destruct Cnd as (((((Aln & _) & _) & _) & _) & _). apply Z.eqb_eq in Aln.
      pose proof (aligned_not_mmap_errno r Aln) as Plain.
      split; [rewrite Plain; exact New | intros Rfs; cbn [eff_ret] in Rfs; congruence]. }
  destruct (mmap_noaccess_b prot flags off).
  { destruct eff as [r ws zs us cs ci]. destruct ws, zs, cs, ci; try discriminate New.
    destruct (errno_ret_in (mmap_errnos_when (mmap_reserve_refusable m nZ)) r) eqn:Er.
    - destruct (mmap_reserve_refusable m nZ) eqn:Rv; [|discriminate Er].
      change (errno_ret_in mmap_errnos r = true) in Er.
      destruct us; [|discriminate New].
      split; [rewrite Er; exact New|].
      intros _ eff2 m2 evs2 Old2. destruct eff2 as [r2 ws2 zs2 us2 cs2 ci2]. cbn [eff_ret].
      destruct (errno_ret_in mmap_errnos r2) eqn:Rfs2; [reflexivity|]. exfalso.
      destruct ws2, zs2, cs2, ci2; try discriminate Old2.
      if_cond Old2 Cnd. rewrite !andb_true_iff in Cnd.
      destruct Cnd as ((((Aln & Pos) & Top) & Free) & _).
      apply Z.eqb_eq in Aln. apply Z.ltb_lt in Pos. apply Z.leb_le in Top.
      rewrite (reserve_conj_not_refusable m nZ r2 Aln Pos Top Free) in Rv. discriminate Rv.
    - if_cond New Cnd. rewrite !andb_true_iff in Cnd.
      destruct Cnd as ((((Aln & _) & _) & _) & _). apply Z.eqb_eq in Aln.
      pose proof (aligned_not_mmap_errno r Aln) as Plain.
      split; [rewrite Plain; exact New | intros Rfs; cbn [eff_ret] in Rfs; congruence]. }
  (* the four MAP_FIXED-family arms share their first four tests *)
  destruct (two_pow_64 <=? bv_unsigned addr + nZ)%Z.
  { destruct (mmap_fixed_noaccess_b prot flags off), (mmap_fixed_rw_b prot flags off),
             (mmap_noreplace_noaccess_b prot flags off), (mmap_noreplace_rw_b prot flags off);
      try discriminate New;
      (split; [exact New | intros _ eff2 m2 evs2 Old2; exact (Enomem eff2 m2 evs2 Old2)]). }
  destruct (negb (bv_unsigned addr + nZ <=? alloc_top (m_vmmaps m)))%Z.
  { destruct (mmap_fixed_noaccess_b prot flags off), (mmap_fixed_rw_b prot flags off),
             (mmap_noreplace_noaccess_b prot flags off), (mmap_noreplace_rw_b prot flags off);
      discriminate New. }
  destruct (negb (bv_unsigned addr mod page_size =? 0))%Z eqn:Galn.
  { destruct (mmap_fixed_noaccess_b prot flags off), (mmap_fixed_rw_b prot flags off),
             (mmap_noreplace_noaccess_b prot flags off), (mmap_noreplace_rw_b prot flags off);
      try discriminate New;
      (split; [exact New | intros Rfs; rewrite (Einval eff New) in Rfs; discriminate Rfs]). }
  destruct (negb (0 <? bv_unsigned addr))%Z.
  { destruct (mmap_fixed_noaccess_b prot flags off), (mmap_fixed_rw_b prot flags off),
             (mmap_noreplace_noaccess_b prot flags off), (mmap_noreplace_rw_b prot flags off);
      discriminate New. }
  apply negb_false_iff, Z.eqb_eq in Galn.
  pose proof (aligned_not_mmap_errno addr Galn) as Plain.
  destruct (mmap_fixed_noaccess_b prot flags off).
  { destruct (region_free (vm_reserved (m_vmmaps m)) addr n && map_contains (vm_maps (m_vmmaps m)) addr n).
    2: destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n).
    3: destruct (region_free (vm_reserved (m_vmmaps m)) addr n); [|discriminate New].
    all: destruct eff as [r ws zs us cs ci]; destruct ws, zs, cs, ci; try discriminate New;
         rewrite mmap_errnos_when_false in New; cbn [errno_ret_in existsb] in New;
         if_cond New Cnd; apply andb_prop in Cnd as [Same _]; apply bv_eqb_eq in Same; subst r;
         split; [rewrite Plain; exact New | intros Rfs; cbn [eff_ret] in Rfs; congruence]. }
  destruct (mmap_fixed_rw_b prot flags off).
  { destruct (region_free (vm_reserved (m_vmmaps m)) addr n && map_contains (vm_maps (m_vmmaps m)) addr n).
    - destruct eff as [r ws zs us cs ci]. destruct ws, cs, ci; try discriminate New.
      destruct (errno_ret_in (mmap_errnos_when (mmap_fixed_commit_refusable flags m addr n)) r) eqn:Er.
      + destruct (mmap_fixed_commit_refusable flags m addr n) eqn:Rv; [|discriminate Er].
        change (errno_ret_in mmap_errnos r = true) in Er.
        destruct zs, us; try discriminate New;
          try (change mmap_destructive_errnos with (@nil Z) in New; cbn [errno_ret_in existsb andb] in New;
               discriminate New).
        split; [rewrite Er; exact New|].
        intros _ eff2 m2 evs2 Old2. destruct eff2 as [r2 ws2 zs2 us2 cs2 ci2]. cbn [eff_ret].
        destruct (errno_ret_in mmap_errnos r2) eqn:Rfs2; [reflexivity|]. exfalso.
        destruct ws2, cs2, ci2, us2; try discriminate Old2.
        if_cond Old2 Cnd. apply andb_prop in Cnd as [_ Bud].
        unfold mmap_fixed_commit_refusable in Rv. rewrite Bud in Rv. discriminate Rv.
      + destruct us; [|discriminate New].
        if_cond New Cnd. apply andb_prop in Cnd as [Cnd _]. apply andb_prop in Cnd as [Same _].
        apply bv_eqb_eq in Same. subst r.
        split; [rewrite Plain; exact New | intros Rfs; cbn [eff_ret] in Rfs; congruence].
    - destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n).
      + destruct eff as [r ws zs us cs ci]. destruct ws, us, cs, ci; try discriminate New.
        destruct (errno_ret_in (mmap_errnos_when (mmap_fixed_fresh_refusable flags m nZ)) r) eqn:Er.
        * destruct (mmap_fixed_fresh_refusable flags m nZ) eqn:Rv; [|discriminate Er].
          change (errno_ret_in mmap_errnos r = true) in Er.
          destruct zs; [|discriminate New].
          split; [rewrite Er; exact New|].
          intros _ eff2 m2 evs2 Old2. destruct eff2 as [r2 ws2 zs2 us2 cs2 ci2]. cbn [eff_ret].
          destruct (errno_ret_in mmap_errnos r2) eqn:Rfs2; [reflexivity|]. exfalso.
          destruct ws2, us2, cs2, ci2; try discriminate Old2.
          if_cond Old2 Cnd. apply andb_prop in Cnd as [_ Back].
          unfold mmap_fixed_fresh_refusable in Rv. rewrite Back in Rv. discriminate Rv.
        * if_cond New Cnd. apply andb_prop in Cnd as [Cnd _]. apply andb_prop in Cnd as [Same _].
          apply bv_eqb_eq in Same. subst r.
          split; [rewrite Plain; exact New | intros Rfs; cbn [eff_ret] in Rfs; congruence].
      + destruct (region_free (vm_reserved (m_vmmaps m)) addr n); [|discriminate New].
        destruct eff as [r ws zs us cs ci]. destruct ws, cs, ci; try discriminate New.
        destruct (errno_ret_in (mmap_errnos_when (mmap_fixed_span_refusable flags m addr n)) r) eqn:Er.
        * destruct (mmap_fixed_span_refusable flags m addr n) eqn:Rv; [|discriminate Er].
          change (errno_ret_in mmap_errnos r = true) in Er.
          destruct zs, us; try discriminate New;
            try (change mmap_destructive_errnos with (@nil Z) in New; cbn [errno_ret_in existsb andb] in New;
                 discriminate New).
          split; [rewrite Er; exact New|].
          intros _ eff2 m2 evs2 Old2. destruct eff2 as [r2 ws2 zs2 us2 cs2 ci2]. cbn [eff_ret].
          destruct (errno_ret_in mmap_errnos r2) eqn:Rfs2; [reflexivity|]. exfalso.
          destruct ws2, cs2, ci2, us2; try discriminate Old2.
          if_cond Old2 Cnd. apply andb_prop in Cnd as [_ Bud].
          unfold mmap_fixed_span_refusable in Rv. rewrite Bud in Rv. discriminate Rv.
        * destruct us; [|discriminate New].
          if_cond New Cnd. apply andb_prop in Cnd as [Cnd _]. apply andb_prop in Cnd as [Same _].
          apply bv_eqb_eq in Same. subst r.
          split; [rewrite Plain; exact New | intros Rfs; cbn [eff_ret] in Rfs; congruence]. }
  destruct (mmap_noreplace_noaccess_b prot flags off).
  { destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n).
    - destruct eff as [r ws zs us cs ci]. destruct ws, zs, cs, ci; try discriminate New.
      rewrite mmap_errnos_when_false in New. cbn [errno_ret_in existsb] in New.
      if_cond New Cnd. apply andb_prop in Cnd as [Same _]. apply bv_eqb_eq in Same. subst r.
      split; [rewrite Plain; exact New | intros Rfs; cbn [eff_ret] in Rfs; congruence].
    - destruct (Taken New) as [Agree Quiet]. split; [exact Agree | intros Rfs; congruence]. }
  destruct (mmap_noreplace_rw_b prot flags off); [|discriminate New].
  destruct (region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n).
  - destruct eff as [r ws zs us cs ci]. destruct ws, us, cs, ci; try discriminate New.
    destruct (errno_ret_in (mmap_errnos_when (mmap_fixed_fresh_refusable flags m nZ)) r) eqn:Er.
    + destruct (mmap_fixed_fresh_refusable flags m nZ) eqn:Rv; [|discriminate Er].
      change (errno_ret_in mmap_errnos r = true) in Er.
      destruct zs; [|discriminate New].
      split; [rewrite Er; exact New|].
      intros _ eff2 m2 evs2 Old2. destruct eff2 as [r2 ws2 zs2 us2 cs2 ci2]. cbn [eff_ret].
      destruct (errno_ret_in mmap_errnos r2) eqn:Rfs2; [reflexivity|]. exfalso.
      destruct ws2, us2, cs2, ci2; try discriminate Old2.
      if_cond Old2 Cnd. apply andb_prop in Cnd as [_ Back].
      unfold mmap_fixed_fresh_refusable in Rv. rewrite Back in Rv. discriminate Rv.
    + if_cond New Cnd. apply andb_prop in Cnd as [Cnd _]. apply andb_prop in Cnd as [Same _].
      apply bv_eqb_eq in Same. subst r.
      split; [rewrite Plain; exact New | intros Rfs; cbn [eff_ret] in Rfs; congruence].
  - destruct (Taken New) as [Agree Quiet]. split; [exact Agree | intros Rfs; congruence].
Qed.

Lemma check_mprotect_ed_bwd : forall addr len prot eff m m' evs,
  check_mprotect_ed addr len prot eff m = CheckOk m' evs ->
  check_mprotect addr len prot eff m = CheckOk m' evs /\ forced_mprotect addr len prot m eff.
Proof.
  intros addr len prot eff m m' evs New.
  assert (Lone : forall e x, errno_ret_in mprotect_errnos x = false ->
                             check_ret_only e x m [] = CheckOk m' evs ->
                             errno_ret_in mprotect_errnos (eff_ret e) = false).
  { intros e x Quiet Acc. apply check_ret_only_ok_iff in Acc as [-> _]. exact Quiet. }
  assert (EinvalQuiet : errno_ret_in mprotect_errnos (errno_ret EINVAL) = false) by (vm_compute; reflexivity).
  unfold check_mprotect_ed in New. unfold forced_mprotect, check_mprotect.
  set (n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) in *.
  destruct (mprotect_grows_conflict_b prot).
  { split; [exact New | intros Rfs; rewrite (Lone eff _ EinvalQuiet New) in Rfs; discriminate Rfs]. }
  destruct (negb (bv_unsigned addr mod page_size =? 0))%Z.
  { split; [exact New | intros Rfs; rewrite (Lone eff _ EinvalQuiet New) in Rfs; discriminate Rfs]. }
  destruct (w_is0 len).
  { split; [exact New | intros Rfs; rewrite (Lone eff _ zero_not_mprotect_errno New) in Rfs; discriminate Rfs]. }
  destruct (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z.
  { split; [exact New|]. intros _ eff2 m2 evs2 Old2.
    apply check_ret_only_ok_iff in Old2 as [-> _].
    exact (errno_ret_in_intro mprotect_errnos ENOMEM (or_introl eq_refl)). }
  destruct (negb (mprotect_modeled_b prot)); [discriminate New|].
  destruct (map_contains (vm_noaccess (m_vmmaps m)) addr n && map_contains (vm_maps (m_vmmaps m)) addr n).
  - destruct eff as [r ws zs us cs ci]. destruct ws, us, cs, ci; try discriminate New.
    destruct (errno_ret_in (mprotect_errnos_when (mprotect_refusable m addr n)) r) eqn:Er.
    + destruct (mprotect_refusable m addr n) eqn:Rv; [|discriminate Er].
      change (errno_ret_in mprotect_errnos r = true) in Er.
      destruct zs; [|discriminate New].
      split; [rewrite Er; exact New|].
      intros _ eff2 m2 evs2 Old2. destruct eff2 as [r2 ws2 zs2 us2 cs2 ci2]. cbn [eff_ret].
      destruct (errno_ret_in mprotect_errnos r2) eqn:Rfs2; [reflexivity|]. exfalso.
      destruct ws2, us2, cs2, ci2; try discriminate Old2.
      if_cond Old2 Cnd. apply andb_prop in Cnd as [Cnd _]. apply andb_prop in Cnd as [Bud _].
      apply mprotect_refusable_false_iff in Bud. congruence.
    + if_cond New Cnd. apply andb_prop in Cnd as [Cnd _]. apply andb_prop in Cnd as [_ Zero].
      unfold w_is0 in Zero. apply bv_eqb_eq in Zero. subst r.
      split; [rewrite zero_not_mprotect_errno; exact New|].
      intros Rfs. cbn [eff_ret] in Rfs. rewrite zero_not_mprotect_errno in Rfs. discriminate Rfs.
  - destruct (map_contains (vm_maps (m_vmmaps m)) addr n && region_free (vm_noaccess (m_vmmaps m)) addr n);
      [|discriminate New].
    destruct eff as [r ws zs us cs ci]. destruct ws, zs, us, cs, ci; try discriminate New.
    if_cond New Zero.
    split; [exact New|].
    unfold w_is0 in Zero. apply bv_eqb_eq in Zero. subst r.
    intros Rfs. cbn [eff_ret] in Rfs. rewrite zero_not_mprotect_errno in Rfs. discriminate Rfs.
Qed.

(** The spurious-refusal filter at an mmap or mprotect input, read at the checker: an outcome is not a spurious
    refusal exactly when it is forced in the sense above. *)
Lemma forced_of_ns_mmap : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  ~ spurious_refusal_cfg ACFG i m eff ->
  forced_mmap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m eff.
Proof.
  intros i m eff Hno Hns Hr eff2 m2 evs2 H2.
  change (errno_ret_in mmap_errnos (eff_ret eff2)) with (ret_in_errnos mmap_errnos (eff_ret eff2)).
  rewrite <- (refusal_b_222 i m (eff_ret eff2) Hno).
  apply (nonspurious_refusal_no_grant ACFG i m eff Hns (acfg_family_off_222 i Hno)) with (m' := m2) (evs' := evs2).
  - rewrite (refusal_b_222 i m (eff_ret eff) Hno). exact Hr.
  - apply check_syscall_ok_iff. rewrite (check_syscall_mmap i eff2 m Hno). exact H2.
Qed.

Lemma ns_of_forced_mmap : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  forced_mmap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m eff ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff Sys Frc [_ [Refused [eff' [m' [evs' [Spec Granted]]]]]].
  rewrite (refusal_b_222 i m (eff_ret eff) Sys) in Refused.
  rewrite (refusal_b_222 i m (eff_ret eff') Sys) in Granted.
  apply check_syscall_ok_iff in Spec. rewrite (check_syscall_mmap i eff' m Sys) in Spec.
  pose proof (Frc Refused eff' m' evs' Spec) as Still.
  change (ret_in_errnos mmap_errnos (eff_ret eff')) with (errno_ret_in mmap_errnos (eff_ret eff')) in Granted.
  congruence.
Qed.

Lemma forced_of_ns_mprotect : forall i m eff,
  bv_unsigned (in_sysno i) = 226%Z ->
  ~ spurious_refusal_cfg ACFG i m eff ->
  forced_mprotect (in_arg i 0) (in_arg i 1) (in_arg i 2) m eff.
Proof.
  intros i m eff Hno Hns Hr eff2 m2 evs2 H2.
  change (errno_ret_in mprotect_errnos (eff_ret eff2)) with (ret_in_errnos mprotect_errnos (eff_ret eff2)).
  rewrite <- (refusal_b_226 i m (eff_ret eff2) Hno).
  apply (nonspurious_refusal_no_grant ACFG i m eff Hns (acfg_family_off_226 i Hno)) with (m' := m2) (evs' := evs2).
  - rewrite (refusal_b_226 i m (eff_ret eff) Hno). exact Hr.
  - apply check_syscall_ok_iff. rewrite (check_syscall_mprotect i eff2 m Hno). exact H2.
Qed.

Lemma ns_of_forced_mprotect : forall i m eff,
  bv_unsigned (in_sysno i) = 226%Z ->
  forced_mprotect (in_arg i 0) (in_arg i 1) (in_arg i 2) m eff ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff Sys Frc [_ [Refused [eff' [m' [evs' [Spec Granted]]]]]].
  rewrite (refusal_b_226 i m (eff_ret eff) Sys) in Refused.
  rewrite (refusal_b_226 i m (eff_ret eff') Sys) in Granted.
  apply check_syscall_ok_iff in Spec. rewrite (check_syscall_mprotect i eff' m Sys) in Spec.
  pose proof (Frc Refused eff' m' evs' Spec) as Still.
  change (ret_in_errnos mprotect_errnos (eff_ret eff')) with (errno_ret_in mprotect_errnos (eff_ret eff')) in Granted.
  congruence.
Qed.

(** The forms the proofs use: an mmap (mprotect) input's checker and filter, as the edited checker. *)
Lemma check_mmap_ed_of_ns : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 222%Z ->
  check_syscall i eff m = CheckOk m' evs ->
  ~ spurious_refusal_cfg ACFG i m eff ->
  mmap_corner_free (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 5) m eff ->
  check_mmap_ed (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m = CheckOk m' evs.
Proof.
  intros i m eff m' evs Hno Hc Hns Hcf. rewrite (check_syscall_mmap i eff m Hno) in Hc.
  apply check_mmap_ed_fwd; [exact Hc| apply forced_of_ns_mmap; assumption| exact Hcf].
Qed.

Lemma ns_of_check_mmap_ed : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 222%Z ->
  check_mmap_ed (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m = CheckOk m' evs ->
  check_syscall i eff m = CheckOk m' evs /\ ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff m' evs Hno H. destruct (check_mmap_ed_bwd _ _ _ _ _ _ _ _ _ _ H) as [Hc Hf].
  split; [rewrite (check_syscall_mmap i eff m Hno); exact Hc| apply ns_of_forced_mmap; assumption].
Qed.

Lemma check_mprotect_ed_of_ns : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 226%Z ->
  check_syscall i eff m = CheckOk m' evs ->
  ~ spurious_refusal_cfg ACFG i m eff ->
  check_mprotect_ed (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m = CheckOk m' evs.
Proof.
  intros i m eff m' evs Hno Hc Hns. rewrite (check_syscall_mprotect i eff m Hno) in Hc.
  apply check_mprotect_ed_fwd; [exact Hc| apply forced_of_ns_mprotect; assumption].
Qed.

Lemma ns_of_check_mprotect_ed : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 226%Z ->
  check_mprotect_ed (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m = CheckOk m' evs ->
  check_syscall i eff m = CheckOk m' evs /\ ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff m' evs Hno H. destruct (check_mprotect_ed_bwd _ _ _ _ _ _ _ H) as [Hc Hf].
  split; [rewrite (check_syscall_mprotect i eff m Hno); exact Hc| apply ns_of_forced_mprotect; assumption].
Qed.

(** A non-refusal and the mmap fixed-read-write arms: the corner premise holds when the arm is not read-write, when
    nothing is destroyed, or when the commit's budget test passes. *)
Lemma mmap_corner_free_not_rw : forall addr len prot flags off m eff,
  mmap_fixed_rw_b prot flags off = false -> mmap_corner_free addr len prot flags off m eff.
Proof. intros addr len prot flags off m eff H H'. congruence. Qed.
