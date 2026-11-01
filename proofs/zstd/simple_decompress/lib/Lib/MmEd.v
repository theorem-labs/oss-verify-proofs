(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Cfg.
Import ListNotations.
Open Scope bv_scope.

Definition w_nilb {A} (l : list A) : bool :=
  match l with [] => true | _ => false end.

Lemma w_nilb_true {A} (l : list A) : w_nilb l = true -> l = [].
Proof. destruct l; [reflexivity|discriminate]. Qed.

Definition check_mmap_ed (addr len prot flags fd off : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (mmap_off_aligned_b off)
  then if mmap_pglen_ok_b len then check_ret_only eff (errno_ret EINVAL) m [] else CheckUnmodeled
  else if negb (mmap_anon_b flags) then CheckUnmodeled
  else if w_is0 len
  then if mmap_plain_anon_b flags then check_ret_only eff (errno_ret EINVAL) m [] else CheckUnmodeled
  else if mmap_modeled_b prot flags off
  then
    match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in (mmap_errnos_when (mmap_grant_refusable flags m (page_round_up_Z (bv_unsigned len)))) r
        then match zs with [] => CheckOk m [] | _ :: _ => CheckReject end
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
  else if mmap_noaccess_b prot flags off
  then
    match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in (mmap_errnos_when (mmap_reserve_refusable m (page_round_up_Z (bv_unsigned len)))) r
        then match us with [] => CheckOk m [] | _ :: _ => CheckReject end
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
  else if mmap_fixed_noaccess_b prot flags off
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
        | mkEffectU r [] [] us [] [] =>
            if errno_ret_in (mmap_errnos_when false) r
            then match us with
                 | [] => CheckOk m []
                 | _ :: _ =>
                     if errno_ret_in mmap_destructive_errnos r && listNN_eqb us [(addr, n)]
                     then CheckOk (with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) []
                     else CheckReject
                 end
            else if bv_eqb r addr && listNN_eqb us [(addr, n)]
            then CheckOk (with_mmap_replacement flags addr n
                   (with_vmmaps
                      {| vm_reserved := vm_reserved (m_vmmaps m);
                         vm_maps := vm_maps (m_vmmaps m);
                         vm_noaccess := (addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m))
                                          (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)%Z;
                         vm_start_brk := vm_start_brk (m_vmmaps m);
                         vm_brk := vm_brk (m_vmmaps m);
                         vm_limit := vm_limit (m_vmmaps m);
                         vm_mmap_base := vm_mmap_base (m_vmmaps m);
                         vm_init_sp := vm_init_sp (m_vmmaps m) |} m)) []
            else CheckReject
        | _ => CheckReject
        end
      else if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] [] us [] [] =>
            if errno_ret_in (mmap_errnos_when false) r
            then match us with [] => CheckOk m [] | _ :: _ => CheckReject end
            else if bv_eqb r addr && listNN_eqb us [(addr, n)]
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
      else if region_free (vm_reserved (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] [] us [] [] =>
            if errno_ret_in (mmap_errnos_when false) r
            then match us with
                 | [] => CheckOk m []
                 | _ :: _ =>
                     if errno_ret_in mmap_destructive_errnos r && listNN_eqb us [(addr, n)]
                     then CheckOk (with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) []
                     else CheckReject
                 end
            else if bv_eqb r addr && listNN_eqb us [(addr, n)]
            then CheckOk (with_mmap_replacement flags addr n
                   (with_vmmaps (mmap_fixed_noaccess_span_next (m_vmmaps m) addr n) m)) []
            else CheckReject
        | _ => CheckReject
        end
      else CheckUnmodeled
  else if mmap_fixed_rw_b prot flags off
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
        | mkEffectU r [] zs us [] [] =>
            if errno_ret_in (mmap_errnos_when (mmap_fixed_commit_refusable flags m addr n)) r
            then match zs with
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
            else match us with
                 | [] =>
                     if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_fixed_rw_budget_ok flags m addr n
                     then CheckOk (with_mmap_replacement flags addr n
                            (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr n) m)) []
                     else CheckReject
                 | _ :: _ => CheckReject
                 end
        | _ => CheckReject
        end
      else if region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] zs [] [] [] =>
            if errno_ret_in (mmap_errnos_when (mmap_fixed_fresh_refusable flags m nZ)) r
            then match zs with [] => CheckOk m [] | _ :: _ => CheckReject end
            else if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags m nZ
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
      else if region_free (vm_reserved (m_vmmaps m)) addr n
      then
        match eff with
        | mkEffectU r [] zs us [] [] =>
            if errno_ret_in (mmap_errnos_when (mmap_fixed_span_refusable flags m addr n)) r
            then match zs with
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
            else match us with
                 | [] =>
                     if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_fixed_rw_span_budget_ok flags m addr n
                     then CheckOk (with_mmap_replacement flags addr n
                            (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps m) addr n) m)) []
                     else CheckReject
                 | _ :: _ => CheckReject
                 end
        | _ => CheckReject
        end
      else CheckUnmodeled
  else if mmap_noreplace_noaccess_b prot flags off
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
        | mkEffectU r [] [] us [] [] =>
            if errno_ret_in (mmap_errnos_when false) r
            then match us with [] => CheckOk m [] | _ :: _ => CheckReject end
            else if bv_eqb r addr && listNN_eqb us [(addr, n)]
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
        | mkEffectU r [] [] [] [] [] =>
            if errno_ret_in (mmap_errnos_when false) r || bv_eqb r (errno_ret EEXIST)
            then CheckOk m [] else CheckReject
        | _ => CheckReject
        end
  else if mmap_noreplace_rw_b prot flags off
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
        | mkEffectU r [] zs [] [] [] =>
            if errno_ret_in (mmap_errnos_when (mmap_fixed_fresh_refusable flags m nZ)) r
            then match zs with [] => CheckOk m [] | _ :: _ => CheckReject end
            else if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags m nZ
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
        | mkEffectU r [] [] [] [] [] =>
            if errno_ret_in (mmap_errnos_when false) r || bv_eqb r (errno_ret EEXIST)
            then CheckOk m [] else CheckReject
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
      | mkEffectU r [] zs [] [] [] =>
          if errno_ret_in (mprotect_errnos_when (mprotect_refusable m addr n)) r
          then match zs with [] => CheckOk m [] | _ :: _ => CheckReject end
          else if mprotect_budget_ok m addr n && w_is0 r && listNN_eqb zs [(addr, n)]
          then CheckOk (mprotect_model_next m addr n) []
          else CheckReject
      | _ => CheckReject
      end
    else if map_contains (vm_maps (m_vmmaps m)) addr n && region_free (vm_noaccess (m_vmmaps m)) addr n
    then
      match eff with
      | mkEffectU r [] [] [] [] [] => if w_is0 r then CheckOk m [] else CheckReject
      | _ => CheckReject
      end
    else CheckUnmodeled.

Ltac same := let H := fresh "H" in intros H; exact H.

Lemma errno_ret_in_when_false_of : forall b r,
  errno_ret_in mmap_errnos r = false -> errno_ret_in (mmap_errnos_when b) r = false.
Proof. intros b r. case b; [same | intros _; reflexivity]. Qed.

Lemma errno_ret_in_mprotect_when_false_of : forall b r,
  errno_ret_in mprotect_errnos r = false -> errno_ret_in (mprotect_errnos_when b) r = false.
Proof.
  intros flag w NoErr. destruct flag as [|];
    [exact NoErr | exact (eq_refl false)].
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

(* [comment removed for export] *)
Definition forced_mmap (addr len prot flags fd off : word) (m : Model) (eff : SyscallEffect) : Prop :=
  errno_ret_in mmap_errnos (eff_ret eff) = true ->
  forall eff2 m2 evs2, check_mmap addr len prot flags fd off eff2 m = CheckOk m2 evs2 ->
  errno_ret_in mmap_errnos (eff_ret eff2) = true.

Definition forced_mprotect (addr len prot : word) (m : Model) (eff : SyscallEffect) : Prop :=
  errno_ret_in mprotect_errnos (eff_ret eff) = true ->
  forall eff2 m2 evs2, check_mprotect addr len prot eff2 m = CheckOk m2 evs2 ->
  errno_ret_in mprotect_errnos (eff_ret eff2) = true.

(* [comment removed for export] *)
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
  intros addr len prot flags fd off eff m m' evs CmOk Forced Corner.
  assert (NoneRefused : forall w : word, errno_ret_in [] w = false) by (intro; reflexivity).
  unfold check_mmap in CmOk. unfold forced_mmap, check_mmap in Forced.
  unfold mmap_corner_free in Corner. unfold check_mmap_ed.
  cbv zeta in CmOk, Forced |- *.
  repeat match type of CmOk with
         | context [if ?b then _ else _] => let Gate := fresh "Gate" in destruct b eqn:Gate; try discriminate CmOk
         end.
  all: try exact CmOk.
  all: destruct eff as [r [|w ws] [|z zs] [|u us] [|c cs] [|t ts]]; try discriminate CmOk.
  all: cbn [eff_ret eff_unmaps] in Forced, Corner.
  all: lazymatch goal with
       | |- context [mmap_errnos_when false] => idtac
       | |- context [mmap_errnos_when ?C] => destruct C eqn:Refusable
       | _ => idtac
       end.
  all: rewrite ?mmap_errnos_when_true, ?mmap_errnos_when_false.
  all: try unfold mmap_destructive_errnos.
  all: rewrite ?NoneRefused; cbn [andb orb].
  all: destruct (errno_ret_in mmap_errnos r) eqn:RetRefused; try exact CmOk.
  all: try (exfalso;
            destruct (Corner eq_refl) as [NoUnmaps | [S1Hit BudgetOk]]; [discriminate NoUnmaps|];
            first [ discriminate S1Hit
                  | unfold mmap_fixed_commit_refusable in Refusable; rewrite BudgetOk in Refusable;
                    discriminate Refusable ]).
  all: exfalso.
  all: try (match goal with
            | Al : negb (bv_unsigned ?a mod page_size =? 0)%Z = false |- _ =>
                pose proof (aligned_not_mmap_errno a (proj1 (Z.eqb_eq _ _) (proj1 (negb_false_iff _) Al))) as AddrFine
            end).
  all: try (unfold mmap_fixed_commit_refusable, mmap_fixed_fresh_refusable, mmap_fixed_span_refusable in Refusable;
            match type of Refusable with
            | context [mmap_fixed_rw_budget_ok ?f ?mm ?a ?k] => destruct (mmap_fixed_rw_budget_ok f mm a k) eqn:BudgetOk
            | context [mmap_noreserve_backed_ok ?f ?mm ?k] => destruct (mmap_noreserve_backed_ok f mm k) eqn:BudgetOk
            | context [mmap_fixed_rw_span_budget_ok ?f ?mm ?a ?k] =>
                destruct (mmap_fixed_rw_span_budget_ok f mm a k) eqn:BudgetOk
            end; try discriminate Refusable).
  all: try (apply not_refusable_grant_conj in Refusable as (BackedOk & base & BaseAl & BasePos & BaseTop & BaseFree)).
  all: try (apply not_refusable_reserve_conj in Refusable as (base & BaseAl & BasePos & BaseTop & BaseFree)).
  all: try (epose proof (Forced eq_refl
                (mkEffectU base [] [(base, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] [] [] []) _ []) as Bad;
            cbn [eff_ret] in Bad; rewrite (aligned_not_mmap_errno base BaseAl) in Bad;
            apply diff_false_true, Bad;
            rewrite (proj2 (Z.eqb_eq _ _) BaseAl), (proj2 (Z.ltb_lt _ _) BasePos), (proj2 (Z.leb_le _ _) BaseTop),
              BaseFree, BackedOk, listNN_eqb_refl';
            reflexivity).
  all: try (epose proof (Forced eq_refl
                (mkEffectU base [] [] [(base, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] [] []) _ []) as Bad;
            cbn [eff_ret] in Bad; rewrite (aligned_not_mmap_errno base BaseAl) in Bad;
            apply diff_false_true, Bad;
            rewrite (proj2 (Z.eqb_eq _ _) BaseAl), (proj2 (Z.ltb_lt _ _) BasePos), (proj2 (Z.leb_le _ _) BaseTop),
              BaseFree, listNN_eqb_refl';
            reflexivity).
  all: try (epose proof (Forced eq_refl
                (mkEffectU addr [] [] [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] [] []) _ []) as Bad;
            cbn [eff_ret] in Bad; rewrite AddrFine in Bad;
            apply diff_false_true, Bad;
            rewrite bv_eqb_refl, listNN_eqb_refl';
            reflexivity).
  all: try (epose proof (Forced eq_refl
                (mkEffectU addr [] [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] [] [] []) _ []) as Bad;
            cbn [eff_ret] in Bad; rewrite AddrFine in Bad;
            apply diff_false_true, Bad;
            rewrite bv_eqb_refl, listNN_eqb_refl';
            reflexivity).
  all: epose proof (Forced eq_refl (mkEffectU (errno_ret EEXIST) [] [] [] [] []) _ []) as Bad;
       cbn [eff_ret] in Bad; rewrite eexist_not_mmap_errno in Bad;
       apply diff_false_true, Bad;
       rewrite bv_eqb_refl;
       reflexivity.
Qed.

Lemma check_mprotect_ed_fwd : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs ->
  forced_mprotect addr len prot m eff ->
  check_mprotect_ed addr len prot eff m = CheckOk m' evs.
Proof.
  intros addr len prot eff m m' evs CmOk Forced.
  unfold check_mprotect in CmOk. unfold forced_mprotect, check_mprotect in Forced. unfold check_mprotect_ed.
  cbv zeta in CmOk, Forced |- *.
  repeat match type of CmOk with
         | context [if ?b then _ else _] => let Gate := fresh "Gate" in destruct b eqn:Gate; try discriminate CmOk
         end.
  all: try exact CmOk.
  destruct eff as [r [|w ws] zs [|u us] [|c cs] [|t ts]]; try discriminate CmOk.
  cbn [eff_ret] in Forced.
  match goal with
  | |- context [mprotect_refusable ?mm ?a ?k] => destruct (mprotect_refusable mm a k) eqn:Refusable
  end.
  { change (mprotect_errnos_when true) with mprotect_errnos. exact CmOk. }
  destruct (errno_ret_in mprotect_errnos r) eqn:RetRefused; [exfalso | exact CmOk].
  apply mprotect_refusable_false_iff in Refusable.
  epose proof (Forced eq_refl
                 (mkEffectU (Z_to_bv 64 0) [] [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] [] [] [])
                 _ []) as ZeroRefused.
  cbn [eff_ret] in ZeroRefused. rewrite zero_not_mprotect_errno in ZeroRefused.
  apply diff_false_true, ZeroRefused.
  rewrite Refusable, listNN_eqb_refl'. reflexivity.
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

(* [comment removed for export] *)
Ltac if_cond Src Tag :=
  match type of Src with
  | context [if ?b then _ else _] => let Cnd := fresh Tag in destruct b eqn:Cnd
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
  intros addr len prot flags fd off eff m m' evs EdOk.
  assert (NoneRefused : forall w : word, errno_ret_in [] w = false) by (intro; reflexivity).
  unfold check_mmap_ed in EdOk. unfold forced_mmap, check_mmap.
  cbv zeta in EdOk |- *.
  repeat (if_cond EdOk Branch; try discriminate EdOk).
  all: try (split; [exact EdOk|];
            intros Refused other m2 evs2 OtherOk;
            apply check_ret_only_ok_iff in EdOk as (-> & _ & _);
            apply check_ret_only_ok_iff in OtherOk as (-> & _ & _);
            exact Refused).
  all: destruct eff as [r [|w ws] [|z zs] [|u us] [|c cs] [|t ts]]; try discriminate EdOk; cbn [eff_ret].
  all: lazymatch type of EdOk with
       | context [mmap_errnos_when false] => idtac
       | context [mmap_errnos_when ?C] => destruct C eqn:Refusable
       | _ => idtac
       end.
  all: rewrite ?mmap_errnos_when_true, ?mmap_errnos_when_false in EdOk.
  all: try unfold mmap_destructive_errnos in EdOk.
  all: rewrite ?NoneRefused in EdOk; cbn [andb orb] in EdOk.
  all: destruct (errno_ret_in mmap_errnos r) eqn:RetRefused; try discriminate EdOk.
  all: try (split; [exact EdOk | intros Absurd; discriminate Absurd]).
  all: try (exfalso;
            match type of EdOk with
            | context [if ?g then CheckOk _ _ else CheckReject] => destruct g eqn:Grant; [|discriminate EdOk]
            end;
            andb_split Grant;
            first
            [ match goal with
              | Al : (bv_unsigned ?x mod page_size =? 0)%Z = true |- _ =>
                  apply Z.eqb_eq, aligned_not_mmap_errno in Al; congruence
              end
            | match goal with
              | Same : bv_eqb ?x _ = true |- _ => apply bv_eqb_eq in Same; subst x
              end;
              first
              [ rewrite eexist_not_mmap_errno in RetRefused; discriminate RetRefused
              | match goal with
                | Al : negb (bv_unsigned ?a mod page_size =? 0)%Z = false |- _ =>
                    apply negb_false_iff, Z.eqb_eq, aligned_not_mmap_errno in Al; congruence
                end ] ]).
  all: split; [exact EdOk|].
  all: intros _ other m2 evs2 OtherOk.
  all: destruct other as [r2 [|? ?] [|? ?] [|? ?] [|? ?] [|? ?]]; try discriminate OtherOk; cbn [eff_ret].
  all: destruct (errno_ret_in mmap_errnos r2) eqn:OtherRefused; [reflexivity | exfalso].
  all: try discriminate OtherOk.
  all: match type of OtherOk with
       | context [if ?g then CheckOk _ _ else CheckReject] => destruct g eqn:Grant; [|discriminate OtherOk]
       end.
  all: andb_split Grant.
  all: try (unfold mmap_fixed_commit_refusable, mmap_fixed_fresh_refusable, mmap_fixed_span_refusable in Refusable;
            match goal with
            | Fits : ?b = true |- _ => rewrite Fits in Refusable; discriminate Refusable
            end).
  all: match goal with
       | Al : (bv_unsigned ?a mod page_size =? 0)%Z = true,
         Ps : (0 <? bv_unsigned ?a)%Z = true,
         Tp : (bv_unsigned ?a + _ <=? alloc_top _)%Z = true,
         Fr : region_free _ ?a _ = true |- _ =>
           apply Z.eqb_eq in Al; apply Z.ltb_lt in Ps; apply Z.leb_le in Tp;
           first [ rewrite (grant_conj_not_refusable _ _ _ a Al Ps Tp Fr) in Refusable by assumption
                 | rewrite (reserve_conj_not_refusable _ _ a Al Ps Tp Fr) in Refusable ];
           discriminate Refusable
       end.
Qed.

Lemma check_mprotect_ed_bwd : forall addr len prot eff m m' evs,
  check_mprotect_ed addr len prot eff m = CheckOk m' evs ->
  check_mprotect addr len prot eff m = CheckOk m' evs /\ forced_mprotect addr len prot m eff.
Proof.
  intros addr len prot eff m m' evs EdOk.
  unfold check_mprotect_ed in EdOk. unfold forced_mprotect, check_mprotect.
  cbv zeta in EdOk |- *.
  repeat (if_cond EdOk Branch; try discriminate EdOk).
  all: try (split; [exact EdOk|];
            intros Refused other m2 evs2 OtherOk;
            apply check_ret_only_ok_iff in EdOk as (-> & _ & _);
            apply check_ret_only_ok_iff in OtherOk as (-> & _ & _);
            exact Refused).
  all: destruct eff as [r [|w ws] [|z zs] [|u us] [|c cs] [|t ts]]; try discriminate EdOk; cbn [eff_ret].
  all: lazymatch type of EdOk with
       | context [mprotect_refusable ?mm ?a ?k] => destruct (mprotect_refusable mm a k) eqn:Refusable
       | _ => idtac
       end.
  all: try change (mprotect_errnos_when true) with mprotect_errnos in EdOk.
  all: destruct (errno_ret_in mprotect_errnos r) eqn:RetRefused; try discriminate EdOk.
  all: try (split; [exact EdOk | intros Absurd; discriminate Absurd]).
  all: try (exfalso;
            match type of EdOk with
            | context [if ?g then CheckOk _ _ else CheckReject] => destruct g eqn:Grant; [|discriminate EdOk]
            end;
            andb_split Grant;
            match goal with
            | RetZero : w_is0 ?x = true |- _ => unfold w_is0 in RetZero; apply bv_eqb_eq in RetZero; subst x
            end;
            rewrite zero_not_mprotect_errno in RetRefused; discriminate RetRefused).
  all: split; [exact EdOk|].
  all: intros _ other m2 evs2 OtherOk.
  all: destruct other as [r2 [|? ?] [|? ?] [|? ?] [|? ?] [|? ?]]; try discriminate OtherOk; cbn [eff_ret].
  all: destruct (errno_ret_in mprotect_errnos r2) eqn:OtherRefused; [reflexivity | exfalso].
  all: match type of OtherOk with
       | context [mprotect_budget_ok ?mm ?a ?k] => destruct (mprotect_budget_ok mm a k) eqn:Budget
       end.
  all: first [ rewrite (proj2 (mprotect_refusable_false_iff _ _ _) Budget) in Refusable; discriminate Refusable
             | discriminate OtherOk ].
Qed.

(* [comment removed for export] *)
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
  intros i m eff Is222 Forced Spurious.
  destruct Spurious as (_ & RefusedB & grant & m_g & evs_g & GrantSpec & GrantKept).
  rewrite (refusal_b_222 i m (eff_ret eff) Is222) in RefusedB.
  rewrite (refusal_b_222 i m (eff_ret grant) Is222) in GrantKept.
  apply check_syscall_ok_iff in GrantSpec.
  rewrite (check_syscall_mmap i grant m Is222) in GrantSpec.
  exact (diff_true_false (eq_trans (eq_sym (Forced RefusedB grant m_g evs_g GrantSpec)) GrantKept)).
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
  intros i m eff Is226 Forced (_ & EffRefused & other & m_o & evs_o & OtherSpec & OtherKept).
  apply check_syscall_ok_iff in OtherSpec.
  rewrite (check_syscall_mprotect i other m Is226) in OtherSpec.
  rewrite refusal_b_226 in EffRefused by exact Is226.
  rewrite refusal_b_226 in OtherKept by exact Is226.
  apply (eq_true_false_abs _ (Forced EffRefused other m_o evs_o OtherSpec)).
  exact OtherKept.
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma mmap_corner_free_not_rw : forall addr len prot flags off m eff,
  mmap_fixed_rw_b prot flags off = false -> mmap_corner_free addr len prot flags off m eff.
Proof. intros addr len prot flags off m eff H H'. congruence. Qed.
