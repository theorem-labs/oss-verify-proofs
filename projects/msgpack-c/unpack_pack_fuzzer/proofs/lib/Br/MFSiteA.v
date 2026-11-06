(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem ITree Nodes NodesM Decode DecodeM.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad MSafe Prog KLink KStep KOwn PgArith.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require MI_Contracts MF_Phi MF_SiteC MF_Evol.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue NodeSound TreeBridge TreeBridgeN KRel MPath Room Grant MMeas MF NoRefuse MFMust.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition cs0 : mstate := ps_m s0.
Local Notation MC := (Malloc.M (mstate * option (aptr * Z))%type).
Definition T0 : MC := malloc_core lay_none cs0 BUF0.

Definition FIN (x : mstate * option (aptr * Z)) : Malloc.M (mstate * option cptr) :=
  let (st1, r) := x in ret (strip st1, match r with Some (g, idx) => Some (slot_of st1 g idx) | None => None end).

Ltac krefl := lazymatch goal with |- ?l = _ => exact_no_check (@eq_refl _ l) end.

Lemma cmalloc_T0 : cmalloc cs0 BUF0 = sbind T0 FIN.
Proof. krefl. Qed.

Definition BL : MC := ret (cs0, @None (aptr * Z)).
Definition KM (st1 : mstate) (idx : Z) : MC :=
  if idx <? 0 then ret (st1, None)
  else match active st1 44 with
       | Some gp => ret (st1, Some (gp, idx))
       | None => SVis (EUndef UBadPtr) (fun _ : Z => BL)
       end.
Definition KS (st2 : mstate) (go : optr) : MC :=
  match go with
  | None => KM st2 (-1)
  | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
              queue (LActive 44) g st3 (fun st4 => KM st4 0) BL
  end.

Definition KAG : mstate -> optr -> MC :=
  let sc := 44 in let req := BUF0 in let lay := lay_none in let k := KS in let bail := BL in
  let size := UNIT * size_class sc in
  (fun st mo =>
  match mo with
  | None => k st None
  | Some m =>
    let usage0 := usage st sc in
    let cnt :=
      if sc <? 9 then small_cnt_pick sc usage0
      else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) usage0) size in
    let cnt := if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt in
    let tail (st : mstate) (p : aptr) (cnt active_idx : Z) : MC := ag_tail lay st sc m p cnt active_idx k in
    if PGSZ / 2 <? size * cnt + UNIT then
      let nosmall := is_bouncing sc st in
      let st1 := step_seq (account_bounce sc st) in
      let usage1 := if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0 in
      let cnt :=
        if (usage1 <? 4 * cnt) && negb nosmall then
          if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
          else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
          else cnt
        else cnt in
      let needed := round_up_pg (size * cnt + UNIT) in
      let '(cnt, needed) :=
        if negb nosmall && (cnt <=? 7) then
          let req := round_up_pg (req + IB + UNIT) in
          if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed)
        else (cnt, needed) in
      SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
        if negb (mmap_answer_ok (live_ranges st1) needed r) then bad_answer bail else
        if is_err r then free_meta m st1 (fun st2 => k st2 None) bail
        else
          let '(st2, rid) := new_region RKGroup r needed st1 in
          let st3 := upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2 in
          let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
          let ai := (4096 - UNIT) / size - 1 in
          let ai := if cnt - 1 <? ai then cnt - 1 else ai in
          let ai := if ai <? 0 then 0 else ai in
          tail st4 (rid, 0) cnt ai)
    else
      let j := size_to_class (UNIT + cnt * size - IB) in
      alloc_slot lay 63%nat st j (UNIT + cnt * size - IB) (fun st1 idx =>
        if idx <? 0 then free_meta m st1 (fun st2 => k st2 None) bail
        else
          match active st1 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g =>
            let p := slot_of st1 g idx in
            let st2 := lh_nest lay st1 g idx j size cnt in
            let st3 := upd_meta m (m_set_maplen 0) st2 in
            tail st3 p cnt (cnt - 1)
          end) bail
  end).

Definition STI : mstate := upd_ctx (fun c => set_init_done 1 (set_secret (s_secret cs0) c)) cs0.
Definition STIv : mstate := Eval vm_compute in STI.
Definition STDv : mstate := Eval vm_compute in (upd_ctx (set_brk BrkDead) STI).
Definition LRDv : list (Z * Z) := Eval vm_compute in (live_ranges STDv).
Definition P0v : aptr := (0%N, 4096).

Definition ST2f (a1 : Z) : mstate :=
  let '(st1, rid) := new_region RKMeta a1 8192 STDv in
  upd_ctx (fun c => set_meta_alloc_shift (c_meta_alloc_shift c + 1)
                      (set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, PGSZ)) c))) st1.
Definition ST2v : Z -> mstate := Eval vm_compute in ST2f.

Definition am_out (st : mstate) : mstate * aptr :=
  match am_carve st P0v (fun s mo => SRet (s, mo)) (SRet (st, @None aptr)) with
  | SRet (s, Some m) => (step_seq (account_bounce 44 s), m)
  | _ => (st, P0v)
  end.
Definition MMv : aptr := Eval vm_compute in (let '(_, m) := am_out (ST2v 0) in m).
Definition ST1v : Z -> mstate := Eval vm_compute in (fun a1 => let '(s, _) := am_out (ST2v a1) in s).
Definition LR1v : Z -> list (Z * Z) := Eval vm_compute in (fun a1 => live_ranges (ST1v a1)).

Definition STG2f (base : Z) : mstate :=
  let '(st1, rid) := new_region RKBrk base (2 * PGSZ) STIv in
  upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, PGSZ)) (set_brk (BrkLive rid (2 * PGSZ)) c))) st1.
Definition STG2v : Z -> mstate := Eval vm_compute in STG2f.
Definition STG1v : Z -> mstate := Eval vm_compute in (fun base => let '(s, _) := am_out (STG2v base) in s).
Definition RESVv : list (Z * Z) := Eval vm_compute in (reservedZ rsegs).
Definition LRG1 (base : Z) : list (Z * Z) := RESVv ++ [(base + PGSZ, 4096)].

Definition nb (b0 : Z) : Z := round_up_pg b0 + 2 * PGSZ.
Definition ENc : Z := TWO64 - 12.
Definition MAPF' : Z := MAP_PRIVATE + MAP_ANON.
Definition MAPFX' : Z := MAP_PRIVATE + MAP_ANON + MAP_FIXED.

Definition LF (st1 : mstate) : MC := free_meta MMv st1 (fun st2 => KS st2 None) BL.
Definition LS (st1 : mstate) (a2 : Z) : MC :=
  let '(st2, rid) := new_region RKGroup a2 69632 st1 in
  let st3 := upd_meta MMv (m_set_maplen (Z.shiftr 69632 12)) st2 in
  let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
  let ai := (4096 - UNIT) / (UNIT * size_class 44) - 1 in
  let ai := if 1 - 1 <? ai then 1 - 1 else ai in
  let ai := if ai <? 0 then 0 else ai in
  ag_tail lay_none st4 44 MMv (rid, 0) 1 ai KS.

Definition KG (lr : list (Z * Z)) (st1 : mstate) : Z -> MC := fun a2 =>
  if negb (mmap_answer_ok lr 69632 a2) then bad_answer BL
  else if is_err a2 then free_meta MMv st1 (fun st2 => KS st2 None) BL
  else let '(st2, rid) := new_region RKGroup a2 69632 st1 in
       let st3 := upd_meta MMv (m_set_maplen (Z.shiftr 69632 12)) st2 in
       let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
       let ai := (4096 - UNIT) / (UNIT * size_class 44) - 1 in
       let ai := if 1 - 1 <? ai then 1 - 1 else ai in
       let ai := if ai <? 0 then 0 else ai in
       ag_tail lay_none st4 44 MMv (rid, 0) 1 ai KS.

Definition KCV (a1 : Z) : MC := SVis (EMmap 0 69632 PROT_RW MAPF') (KG (LR1v a1) (ST1v a1)).
Definition K5 (a1 : Z) : Z -> MC := fun m =>
  if negb (mprotect_answer_ok m) then bad_answer BL
  else if (m =? 0) || (m =? TWO64 - ENOSYS) then KCV a1 else SRet (ST2v a1, None).
Definition K4 : Z -> MC := fun a1 =>
  if negb (mmap_answer_ok LRDv 8192 a1) then bad_answer BL
  else if is_err a1 then SRet (STDv, None)
  else SVis (EMprotect (a1 + PGSZ) PGSZ PROT_RW) (K5 a1).
Definition K3T : MC := SVis (EMmap 0 8192 PROT_NONE MAPF') K4.

Definition KGV (base : Z) : MC := SVis (EMmap 0 69632 PROT_RW MAPF') (KG (LRG1 base) (STG1v base)).
Definition K3G (b0 : Z) : Z -> MC := fun rg =>
  if negb (mmap_fixed_answer_ok (round_up_pg b0) rg) then bad_answer BL else KGV (round_up_pg b0).
Definition K2 (b0 : Z) : Z -> MC := fun r =>
  if negb (brk_answer_ok b0 (nb b0) r) then bad_answer BL
  else if negb (r =? nb b0) then K3T
  else if negb (brk_pages_ok STIv (round_up_pg b0) (2 * PGSZ)) then bad_answer BL
  else SVis (EMmap (round_up_pg b0) PGSZ PROT_NONE MAPFX') (K3G b0).
Definition K1 : Z -> MC := fun b0 =>
  if negb (brk0_answer_ok b0) then bad_answer BL else SVis (EBrk (nb b0)) (K2 b0).
Definition TA : MC := SVis (EBrk 0) K1.

Theorem TA_T0 : TA = T0.
Proof. krefl. Qed.

Lemma cmalloc_TA : cmalloc (ps_m s0) BUF0 = sbind TA FIN.
Proof. rewrite TA_T0. exact cmalloc_T0. Qed.

Definition leaf_res {R} (t : Malloc.M (mstate * R)) : option R := match t with SRet (_, r) => Some r | _ => None end.

Lemma leaf_res_SRet {R} (t : Malloc.M (mstate * R)) r : leaf_res t = Some r -> exists s, t = SRet (s, r).
Proof. destruct t as [[s r']|e k]; cbn; [| discriminate]. intros H. injection H as ->. exists s. reflexivity. Qed.

Lemma LF_refused : forall a1, leaf_res (LF (ST1v a1)) = Some None.
Proof. intros a1. krefl. Qed.
Lemma LS_refused : forall a1 a2, leaf_res (LS (ST1v a1) a2) = Some (Some (MMv, 0)).
Proof. intros a1 a2. krefl. Qed.
Lemma LF_granted : forall b, leaf_res (LF (STG1v b)) = Some None.
Proof. intros b. krefl. Qed.
Lemma LS_granted : forall b a2, leaf_res (LS (STG1v b) a2) = Some (Some (MMv, 0)).
Proof. intros b a2. krefl. Qed.

Lemma KG_eq : forall lr st1 a2,
  KG lr st1 a2 = if negb (mmap_answer_ok lr 69632 a2) then bad_answer BL else if is_err a2 then LF st1 else LS st1 a2.
Proof. intros. krefl. Qed.

Lemma K4_refused : K4 (neg_errno ENOMEM) = SRet (STDv, None).
Proof. krefl. Qed.

Lemma sbind_if {R S} (c : bool) (a b : Malloc.M R) (f : R -> Malloc.M S) :
  sbind (if c then a else b) f = if c then sbind a f else sbind b f.
Proof. destruct c; reflexivity. Qed.

Lemma sbind_bad {R S} (b : Malloc.M R) (f : R -> Malloc.M S) :
  sbind (bad_answer b) f = SVis (EUndef UBadAnswer) (fun _ => sbind b f).
Proof. krefl. Qed.

Lemma FIN_ret : forall x, exists y, FIN x = SRet y.
Proof. intros [st [[g i]|]]; eexists; reflexivity. Qed.

Lemma okpath_ret {R} L (x : R) zs : okpath L (SRet x) zs <-> zs = [].
Proof. destruct zs; cbn; [tauto | split; [tauto | discriminate]]. Qed.

Lemma okpath_vis {R} L e (k : Z -> Malloc.M R) zs :
  okpath L (SVis e k) zs <-> exists z zs', zs = z :: zs' /\ answer_ok L e z = true /\ okpath (event_post L e z) (k z) zs'.
Proof.
  destruct zs as [|z zs']; cbn.
  - split; [tauto|]. intros (z & zs' & H & _). discriminate.
  - split; [intros [A B]; exists z, zs'; auto|]. intros (z0 & zs0 & E & A & B). injection E as <- <-. auto.
Qed.

Lemma okpath_undef {R} L u (k : Z -> Malloc.M R) zs : okpath L (SVis (EUndef u) k) zs -> False.
Proof. destruct zs; cbn; [tauto|]. intros [H _]. discriminate. Qed.

Lemma okpath_bad {R} L (b : Malloc.M R) zs : okpath L (bad_answer b) zs -> False.
Proof. apply okpath_undef. Qed.

Lemma okpath_sbind_FIN : forall (t : MC) L zs, okpath L (sbind t FIN) zs <-> okpath L t zs.
Proof.
  induction t as [x | e k IH]; intros L zs.
  - cbn [sbind]. destruct (FIN_ret x) as [y ->]. rewrite !okpath_ret. tauto.
  - rewrite sbind_vis. rewrite !okpath_vis. split; intros (z & zs' & -> & A & B); exists z, zs'; (split; [reflexivity|]); (split; [exact A|]); apply IH; exact B.
Qed.

Lemma evs_of_sbind_FIN : forall (t : MC) zs, evs_of (sbind t FIN) zs = evs_of t zs.
Proof.
  induction t as [x | e k IH]; intros zs.
  - cbn [sbind]. destruct (FIN_ret x) as [y ->]. destruct zs; reflexivity.
  - rewrite sbind_vis. destruct zs as [|z zs]; [reflexivity|]. cbn [evs_of]. f_equal. apply IH.
Qed.

Lemma mreal_sbind_FIN : forall (t : MC) zs s mo x s' mo' y,
  mreal t zs s mo x s' mo' -> FIN x = SRet y -> mreal (sbind t FIN) zs s mo y s' mo'.
Proof.
  induction t as [x0 | e k IH]; intros zs s mo x s' mo' y H E.
  - destruct zs; cbn in H; [| destruct H]. destruct H as (-> & -> & ->). cbn [sbind]. rewrite E. cbn. auto.
  - destruct zs as [|z zs]; cbn in H; [destruct H|]. destruct H as (s1 & mo1 & H1 & H2).
    rewrite sbind_vis. cbn [mreal]. exists s1, mo1. split; [exact H1|]. eapply IH; eassumption.
Qed.

Lemma esize_vals : esize (EMmap 0 8192 PROT_NONE MAPF') = 8192 /\ esize (EMmap 0 69632 PROT_RW MAPF') = 69632
  /\ (forall a, esize (EMmap a PGSZ PROT_NONE MAPFX') = 4096) /\ (forall a, esize (EBrk a) = 12288)
  /\ (forall a l p, esize (EMprotect a l p) = 0).
Proof. repeat split; intros; reflexivity. Qed.

Lemma KG_events : forall lr st1 L zs, (forall a2, exists r, leaf_res (if is_err a2 then LF st1 else LS st1 a2) = Some r) ->
  okpath L (SVis (EMmap 0 69632 PROT_RW MAPF') (KG lr st1)) zs ->
  exists a2, zs = [a2] .
Proof.
  intros lr st1 L zs Hleaf Hok. apply okpath_vis in Hok as (a2 & zs' & -> & _ & Hok).
  rewrite KG_eq in Hok. destruct (mmap_answer_ok lr 69632 a2); cbn [negb] in Hok; [| exfalso; exact (okpath_bad _ _ _ Hok)].
  destruct (Hleaf a2) as [r Hr]. destruct (leaf_res_SRet _ _ Hr) as [s E]. rewrite E in Hok.
  apply okpath_ret in Hok. subst zs'. exists a2. reflexivity.
Qed.

Theorem siteA_events : forall L zs, okpath L (cmalloc (ps_m s0) BUF0) zs ->
  (length (evs_of (cmalloc (ps_m s0) BUF0) zs) <= 5)%nat /\ esum (evs_of (cmalloc (ps_m s0) BUF0) zs) <= 2 ^ 17.
Proof.
  intros L zs Hok. rewrite cmalloc_TA in *. rewrite okpath_sbind_FIN in Hok. rewrite evs_of_sbind_FIN.
  destruct esize_vals as (E1 & E2 & E3 & E4 & E5).
  unfold TA in *. apply okpath_vis in Hok as (b0 & zs1 & -> & _ & Hok). cbn [evs_of length esum]. rewrite E4.
  unfold K1 in *. destruct (brk0_answer_ok b0); cbn [negb] in Hok |- *; [| exfalso; exact (okpath_bad _ _ _ Hok)].
  apply okpath_vis in Hok as (r & zs2 & -> & _ & Hok). cbn [evs_of length esum]. rewrite E4.
  unfold K2 in *. destruct (brk_answer_ok b0 (nb b0) r); cbn [negb] in Hok |- *; [| exfalso; exact (okpath_bad _ _ _ Hok)].
  destruct (r =? nb b0); cbn [negb] in Hok |- *.
  -
    destruct (brk_pages_ok STIv (round_up_pg b0) (2 * PGSZ)); cbn [negb] in Hok |- *; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    apply okpath_vis in Hok as (rg & zs3 & -> & _ & Hok). cbn [evs_of length esum]. rewrite E3.
    unfold K3G in *. destruct (mmap_fixed_answer_ok (round_up_pg b0) rg); cbn [negb] in Hok |- *; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    unfold KGV in *. destruct (KG_events _ _ _ _ ltac:(intros a2; destruct (is_err a2); eexists; [apply LF_granted | apply LS_granted]) Hok) as [a2 ->].
    cbn [evs_of length esum]. rewrite E2. rewrite KG_eq.
    destruct (negb _); [cbn; lia|]. destruct (is_err a2).
    + destruct (leaf_res_SRet _ _ (LF_granted (round_up_pg b0))) as [s ->]. cbn. lia.
    + destruct (leaf_res_SRet _ _ (LS_granted (round_up_pg b0) a2)) as [s ->]. cbn. lia.
  -
    unfold K3T in *. apply okpath_vis in Hok as (a1 & zs3 & -> & _ & Hok). cbn [evs_of length esum]. rewrite E1.
    unfold K4 in *. destruct (mmap_answer_ok LRDv 8192 a1); cbn [negb] in Hok |- *; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    destruct (is_err a1).
    { apply okpath_ret in Hok. subst zs3. cbn. lia. }
    apply okpath_vis in Hok as (m & zs4 & -> & _ & Hok). cbn [evs_of length esum]. rewrite E5.
    unfold K5 in *. destruct (mprotect_answer_ok m); cbn [negb] in Hok |- *; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    destruct ((m =? 0) || (m =? TWO64 - ENOSYS)).
    + unfold KCV in *. destruct (KG_events _ _ _ _ ltac:(intros a2; destruct (is_err a2); eexists; [apply LF_refused | apply LS_refused]) Hok) as [a2 ->].
      cbn [evs_of length esum]. rewrite E2. rewrite KG_eq.
      destruct (negb _); [cbn; lia|]. destruct (is_err a2).
      * destruct (leaf_res_SRet _ _ (LF_refused a1)) as [s ->]. cbn. lia.
      * destruct (leaf_res_SRet _ _ (LS_refused a1 a2)) as [s ->]. cbn. lia.
    + apply okpath_ret in Hok. subst zs4. cbn. lia.
Qed.

Lemma msteps_snoc : forall k E mo mo1 mo2 e,
  msteps k E mo mo1 -> 0 <= E -> mstep (esize e) mo1 mo2 -> msteps (S k) (E + esize e) mo mo2.
Proof.
  intros k E mo mo1 mo2 e [A1 A2 A3 A4] HE [B1 B2 B3 B4]. pose proof (esize_nonneg e). constructor.
  - lia. - lia.
  - intros B HB H3 Hs. apply B3; [lia|]. apply A3; [lia | exact H3 | exact Hs].
  - congruence.
Qed.

Lemma ev_mmap_none_grant_path : forall len s mo (a : word),
  let h := m_vmmaps mo in let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  0 < len -> nZ < 2^64 -> mo_ok mo ->
  ceil_ok h -> grant_ok mo a nZ ->
  exists mo', tpath nstep (ev_step (EMmap 0 len Malloc.PROT_NONE (Malloc.MAP_PRIVATE + MAP_ANON)) s) mo [] (Ok (bv_unsigned a, s)) mo'
    /\ mo_ok mo' /\ vm_agree mo mo'
    /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) ((a, n) :: vm_noaccess h)
                                   (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
  intros len s mo a h nZ n Hlen HnZ Hmo Hck Hg.
  pose proof Hg as (G1 & G2 & G3 & G4 & G5). fold h in G3, G4, G5 |- *.
  assert (Hnr : mmap_noreserve_b (Z_to_bv 64 (Malloc.MAP_PRIVATE + MAP_ANON)) = false) by reflexivity.
  assert (Hge : len <= nZ) by (unfold nZ, page_round_up_Z, page_size; lia).
  assert (HlenU : bv_unsigned (Z_to_bv 64 len) = len).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul Pos.mul]. lia. }
  assert (Hw : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  unfold ev_step. change (negb (Z.land (Malloc.MAP_PRIVATE + MAP_ANON) MAP_FIXED_Z =? 0)) with false. cbn iota.
  change (Malloc.PROT_NONE =? 0) with true. cbn iota.
  set (mo' := with_mmap_backing (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) a n
                (with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) ((a, n) :: vm_noaccess h)
                               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo)).
  set (eff := mkEffectU a [] [] [(a, n)] [] []).
  assert (Hst : nstep (NMmap 0 len Malloc.PROT_NONE (Malloc.MAP_PRIVATE + MAP_ANON)) mo eff mo' []).
  { apply (proj2 (nstep_mmap_none_inv 0 len mo eff mo' [] Hw)). split; [reflexivity|]. right.
    exists a. rewrite HlenU. fold h nZ n. split; [| split; reflexivity]. repeat split; assumption. }
  destruct (nstep_dec_mmap_none len [] mo eff mo' [] Hlen ltac:(unfold mmap_len; exact HnZ) Hck ltac:(constructor) Hst)
    as (_ & VA & x & Hdec & Hx).
  assert (Hx' : x = MmOk (bv_unsigned a)).
  { unfold eff, dec_mmap_none in Hdec. cbn [eff_copies eff_copyins] in Hdec. rewrite !bv_eqb_refl in Hdec.
    destruct (mmap_addr_ok len [] (bv_unsigned a)); cbn [andb] in Hdec; congruence. }
  subst x.
  exists mo'. split; [| split; [exact (vm_agree_mo_ok _ _ VA Hmo) | split; [exact VA |]]].
  - eapply (tpath_mbind _ _ s mo (MmOk (bv_unsigned a)) s); [eapply tpath_msys; [exact Hst | exact Hdec] | apply tpath_mret].
  - unfold mo'. rewrite with_mmap_backing_noreserve_false by exact Hnr. reflexivity.
Qed.

Lemma ev_mprotect_grant_path : forall (a : Z) s mo,
  let h := m_vmmaps mo in let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 PGSZ in
  0 < a -> a mod 4096 = 0 -> a + PGSZ <= alloc_ceiling -> mo_ok mo ->
  map_contains (vm_noaccess h) aw nw = true -> map_contains (vm_maps h) aw nw = true ->
  vm_live_bytes h <= vm_limit h ->
  tpath nstep (ev_step (EMprotect a PGSZ PROT_RW) s) mo [] (Ok (0, s)) (mprotect_model_next mo aw nw).
Proof.
  intros a s mo h aw nw Ha Hal Hce Hmo Hcn Hcm Hlive. pose proof alloc_ceiling_lt as CL.
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
  set (eff := mkEffect (Z_to_bv 64 0) [] [(aw, nw)]).
  assert (Hbud : mprotect_budget_ok mo aw nw = true).
  { apply mprotect_budget_ok_intro; [exact Hmo | exact Hlive]. }
  assert (Hst : nstep (NMprotect a PGSZ PROT_RW) mo eff (mprotect_model_next mo aw nw) []).
  { apply (proj2 (nstep_mprotect_inv a PGSZ PROT_RW mo eff (mprotect_model_next mo aw nw) []
              ltac:(reflexivity) ltac:(fold aw; rewrite Ua, page_size_eq; exact Hal) ltac:(reflexivity)
              ltac:(fold aw; rewrite Ua; change (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ))) with PGSZ; unfold two_pow_64, PGSZ in *; lia)
              ltac:(reflexivity)
              ltac:(fold aw; change (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ)))) with nw; exact Hcn)
              ltac:(fold aw; change (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ)))) with nw; exact Hcm))).
    split; [reflexivity|]. right. fold aw. change (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ)))) with nw.
    split; [exact Hbud|]. split; reflexivity. }
  assert (Hdec : dec_mprotect_rw a PGSZ eff = Some (RgDone true)).
  { unfold dec_mprotect_rw, dec_mprotect, eff. cbn [eff_copies eff_copyins].
    change (bv_unsigned (Z_to_bv 64 0) =? 0) with true. fold aw. change (Z_to_bv 64 (mmap_len PGSZ)) with nw.
    rewrite !bv_eqb_refl. reflexivity. }
  unfold ev_step.
  eapply (tpath_mbind _ _ s mo (RgDone true) s); [eapply tpath_msys; [exact Hst | exact Hdec] | apply tpath_mret].
Qed.

Lemma KREL0 : forall mo, KREL s0 [] mo -> exists L, MI_Contracts.SIMREL (ps_m s0) L /\ KL L 0 mo.
Proof. intros mo [(L & Hc & HK & _) _]. exists L. split; [exact Hc | exact HK]. Qed.

Lemma ctree_ok_vis {R} L e (k : Z -> stree ev Z R) Post :
  ctree_ok L (SVis e k) Post -> event_pre L e /\ forall z, answer_ok L e z = true -> ctree_ok (event_post L e z) (k z) Post.
Proof. intros H. exact H. Qed.

Lemma ctree_ok_bad {R S} L (b : Malloc.M R) (f : R -> Malloc.M S) Post : ctree_ok L (sbind (bad_answer b) f) Post -> False.
Proof. rewrite sbind_bad. cbn. tauto. Qed.

Section BRK.
Variables (mo : Model) (L : mled).
Hypothesis Hc : MI_Contracts.SIMREL (ps_m s0) L.
Hypothesis HK : KL L 0 mo.
Hypothesis Hmo : mo_ok mo.

Let b := vm_brk (m_vmmaps mo).
Let b0 := bv_unsigned b.
Let s1 := set_brk_ps b0 s0.
Let mo1 := with_brk_next mo (Z_to_bv 64 0) b.
Let L1 := set_brkph (BPQueried b0) L.
Let mo2 := with_brk_next mo1 (Z_to_bv 64 (nb b0)) (vm_brk (m_vmmaps mo1)).
Let L2 := set_brkph BPDead L1.
Let Post := fun (L' : mled) (r : mstate * option cptr) => match snd r with Some c => ~ In c (ld_live L') | None => True end.
Let s2 := set_brk_ps (nb b0) s1.
Let mo2g := with_brk_next mo1 (Z_to_bv 64 (nb b0)) (Z_to_bv 64 (nb b0)).

Lemma brk_steps : brk_grow_ok mo1 (Z_to_bv 64 (nb b0)) (Z_to_bv 64 (nb b0)) = false ->
  tpath nstep (ev_step (EBrk 0) s0) mo [] (Ok (b0, s1)) mo1
  /\ tpath nstep (ev_step (EBrk (nb b0)) s1) mo1 [] (Ok (b0, s1)) mo2
  /\ brk0_answer_ok b0 = true /\ nb b0 = b0 + 2 * PGSZ /\ 0 < b0 /\ b0 + 4 * PGSZ <= alloc_ceiling
  /\ KL L2 b0 mo2 /\ mo_ok mo1 /\ mo_ok mo2 /\ msteps 2 (2 * 12288) mo mo2
  /\ ctree_ok L2 (sbind K3T FIN) Post.
Proof.
  intros Hng.
  pose proof (MI_Contracts.cmalloc_contract_sim _ _ BUF0 Hc ltac:(unfold BUF0; lia)) as CT.
  rewrite cmalloc_TA in CT. unfold TA in CT. rewrite sbind_vis in CT. apply ctree_ok_vis in CT as [Hpre1 CT1].
  pose proof (ev_brk0_path s0 mo) as E1. cbv zeta in E1. fold b b0 s1 mo1 in E1.
  destruct (kev_measure L (EBrk 0) s0 mo b0 s1 mo1 Hpre1 HK Hmo E1) as (Hok1 & HK1 & _ & _ & _ & Hmo1 & Hva1 & M1).
  cbn [answer_ok Z.eqb] in Hok1. cbn [event_post Z.eqb ps_brk s1 set_brk_ps] in HK1. fold L1 in HK1.
  pose proof (kl_phase _ _ _ HK1) as PH. cbn [ld_brk L1 set_brkph] in PH. destruct PH as (Eb0 & Ebrk1 & _ & _).
  pose proof (kl_start _ _ _ HK1) as (S1 & S2 & S3 & S4). rewrite <- Eb0 in S1, S2, S4.
  assert (Enb : nb b0 = b0 + 2 * PGSZ) by (unfold nb; rewrite round_up_pg_aligned by (unfold PGSZ in S2; exact S2); reflexivity).
  pose proof alloc_ceiling_lt as CL.
  specialize (CT1 b0 Hok1). cbn [event_post Z.eqb] in CT1. fold L1 in CT1.
  unfold K1 in CT1. rewrite Hok1 in CT1. cbn [negb] in CT1. rewrite sbind_vis in CT1. apply ctree_ok_vis in CT1 as [Hpre2 CT2].
  assert (Honly : forall r, brk_r_ok mo1 (Z_to_bv 64 (nb b0)) r = true -> r = vm_brk (m_vmmaps mo1)).
  { apply brk_only_old; [rewrite w_is0_lit by (unfold PGSZ in *; lia); apply Z.eqb_neq; unfold PGSZ in *; lia
                         | unfold min_brk; rewrite unsigned_lit by (unfold PGSZ in *; lia); lia
                         | rewrite unsigned_lit by (unfold PGSZ in *; lia); lia | exact Hng]. }
  pose proof (ev_brk_refuse_path (nb b0) s1 mo1 ltac:(unfold PGSZ in *; lia) ltac:(cbn [ps_brk s1 set_brk_ps]; symmetry; exact Ebrk1) Honly) as E2.
  cbv zeta in E2. cbn [ps_brk s1 set_brk_ps] in E2. fold mo2 in E2.
  destruct (kev_measure L1 (EBrk (nb b0)) s1 mo1 b0 s1 mo2 Hpre2 HK1 Hmo1 E2) as (Hok2 & HK2 & _ & _ & _ & Hmo2 & Hva2 & M2).
  assert (Enz : (nb b0 =? 0) = false) by (apply Z.eqb_neq; unfold PGSZ in *; lia).
  assert (Ene : (b0 =? nb b0) = false) by (apply Z.eqb_neq; unfold PGSZ in *; lia).
  cbn [event_post] in HK2. rewrite Enz, Ene in HK2. cbn [ps_brk s1 set_brk_ps] in HK2. fold L2 in HK2.
  specialize (CT2 b0 Hok2). cbn [event_post] in CT2. rewrite Enz, Ene in CT2. fold L2 in CT2.
  unfold K2 in CT2. replace (brk_answer_ok b0 (nb b0) b0) with true in CT2 by (unfold brk_answer_ok; rewrite Z.eqb_refl, orb_true_r; reflexivity).
  rewrite Ene in CT2. cbn [negb] in CT2.
  split; [exact E1|]. split; [exact E2|]. split; [exact Hok1|]. split; [exact Enb|]. split; [lia|]. split; [exact S4|].
  split; [exact HK2|]. split; [exact Hmo1|]. split; [exact Hmo2|].
  split. { replace (2 * 12288) with ((0 + esize (EBrk 0)) + esize (EBrk (nb b0))) by reflexivity.
           eapply msteps_snoc; [eapply msteps_snoc; [apply msteps_refl | lia | exact M1] | cbn; lia | exact M2]. }
  exact CT2.
Qed.

Lemma succ_grow : room mo 0 -> brk_grow_ok mo1 (Z_to_bv 64 (nb b0)) (Z_to_bv 64 (nb b0)) = true ->
  malloc_can_succeed s0 mo BUF0.
Proof.
  intros Hroom Hg.
  pose proof (MI_Contracts.cmalloc_contract_sim _ _ BUF0 Hc ltac:(unfold BUF0; lia)) as CT.
  rewrite cmalloc_TA in CT. unfold TA in CT. rewrite sbind_vis in CT. apply ctree_ok_vis in CT as [Hpre1 CT1].
  pose proof (ev_brk0_path s0 mo) as E1. cbv zeta in E1. fold b b0 s1 mo1 in E1.
  destruct (kev_measure L (EBrk 0) s0 mo b0 s1 mo1 Hpre1 HK Hmo E1) as (Hok1 & HK1 & _ & _ & _ & Hmo1 & Hva1 & M1).
  cbn [answer_ok Z.eqb] in Hok1. cbn [event_post Z.eqb ps_brk s1 set_brk_ps] in HK1. fold L1 in HK1.
  pose proof (kl_phase _ _ _ HK1) as PH. cbn [ld_brk L1 set_brkph] in PH. destruct PH as (Eb0 & Ebrk1 & _ & _).
  pose proof (kl_start _ _ _ HK1) as (S1 & S2 & S3 & S4). rewrite <- Eb0 in S1, S2, S4.
  assert (Enb : nb b0 = b0 + 2 * PGSZ) by (unfold nb; rewrite round_up_pg_aligned by (unfold PGSZ in S2; exact S2); reflexivity).
  assert (Ea : round_up_pg b0 = b0) by (apply round_up_pg_aligned; unfold PGSZ in S2; exact S2).
  pose proof alloc_ceiling_lt as CL.
  specialize (CT1 b0 Hok1). cbn [event_post Z.eqb] in CT1. fold L1 in CT1.
  unfold K1 in CT1. rewrite Hok1 in CT1. cbn [negb] in CT1. rewrite sbind_vis in CT1. apply ctree_ok_vis in CT1 as [Hpre2 CT2].
  pose proof (ev_brk_grow_path (nb b0) s1 mo1 ltac:(lia) ltac:(lia) ltac:(unfold PGSZ in *; lia)
                ltac:(cbn [ps_brk s1 set_brk_ps]; symmetry; exact Ebrk1) Hg) as E2.
  fold s2 mo2g in E2.
  destruct (kev_measure L1 (EBrk (nb b0)) s1 mo1 (nb b0) s2 mo2g Hpre2 HK1 Hmo1 E2) as (Hok2 & HK2 & _ & _ & _ & Hmo2 & Hva2 & M2).
  assert (Enz : (nb b0 =? 0) = false) by (apply Z.eqb_neq; unfold PGSZ in *; lia).
  specialize (CT2 (nb b0) Hok2).
  cbn [answer_ok] in Hok2. rewrite Enz in Hok2. cbn [ld_brk L1 set_brkph] in Hok2. apply andb_prop in Hok2 as [HBA _].
  cbn [event_post] in HK2, CT2. rewrite Enz, Z.eqb_refl in HK2, CT2. cbn [ld_brk L1 set_brkph ps_brk s2 set_brk_ps] in HK2, CT2.
  unfold K2 in CT2. rewrite HBA, Z.eqb_refl in CT2. cbn [negb] in CT2.
  destruct (brk_pages_ok STIv (round_up_pg b0) (2 * PGSZ)) eqn:BP; cbn [negb] in CT2; [| exfalso; exact (ctree_ok_bad _ _ _ _ CT2)].
  rewrite sbind_vis in CT2. apply ctree_ok_vis in CT2 as [Hpre3 CT3].
  pose proof (kl_phase _ _ _ HK2) as PH2. cbn [ld_brk set_brkph] in PH2.
  destruct PH2 as (Ecur & _ & _ & _ & _ & (e0 & He0 & He0l & He0h) & _ & _).
  assert (Ua : bv_unsigned (Z_to_bv 64 (round_up_pg b0)) = b0) by (rewrite Ea; apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Hrf : region_free (vm_reserved (m_vmmaps mo2g)) (Z_to_bv 64 (round_up_pg b0)) (Z_to_bv 64 PGSZ) = true).
  { apply region_free_above. intros e He. rewrite Ua, Ecur. apply (kl_resv_top _ _ _ HK2). exact He. }
  assert (Hmc : map_contains (vm_maps (m_vmmaps mo2g)) (Z_to_bv 64 (round_up_pg b0)) (Z_to_bv 64 PGSZ) = true).
  { unfold map_contains. apply existsb_exists. exists e0. split; [exact He0|].
    rewrite Ua, (unsigned_lit PGSZ) by (unfold PGSZ; lia). unfold elo, ehi in *.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity. }
  destruct (ev_mmap_fixed_guard_path (round_up_pg b0) s2 mo2g ltac:(rewrite Ea; lia) ltac:(rewrite Ea; unfold PGSZ in *; lia)
              ltac:(rewrite Ea; unfold PGSZ in S2; exact S2) (kl_ceil _ _ _ HK2) Hrf Hmc) as (mo3 & E3).
  destruct (kev_measure _ (EMmap (round_up_pg b0) PGSZ PROT_NONE MAPFX') s2 mo2g (round_up_pg b0) s2 mo3 Hpre3 HK2 Hmo2 E3)
    as (Hok3 & HK3 & _ & _ & _ & Hmo3 & _ & M3).
  specialize (CT3 _ Hok3). unfold K3G in CT3.
  destruct (mmap_fixed_answer_ok (round_up_pg b0) (round_up_pg b0)) eqn:FA; cbn [negb] in CT3; [| exfalso; exact (ctree_ok_bad _ _ _ _ CT3)].
  unfold KGV in CT3. rewrite sbind_vis in CT3. apply ctree_ok_vis in CT3 as [Hpre4 CT4].
  pose proof esize_vals as (EV1 & EV2 & EV3 & EV4 & EV5).
  assert (MS3 : msteps 3 (12288 + 12288 + 4096) mo mo3).
  { replace (12288 + 12288 + 4096) with (0 + esize (EBrk 0) + esize (EBrk (nb b0)) + esize (EMmap (round_up_pg b0) PGSZ PROT_NONE MAPFX'))
      by (rewrite EV3, !EV4; reflexivity).
    eapply msteps_snoc; [eapply msteps_snoc; [eapply msteps_snoc; [apply msteps_refl | lia | exact M1] | rewrite EV4; lia | exact M2]
                        | rewrite !EV4; lia | exact M3]. }
  pose proof (room_step mo mo3 0 3 _ Hroom ltac:(lia) MS3 ltac:(lia) ltac:(lia)) as R3.
  destruct (room_grant mo3 (0 + 1) 69632 R3 ltac:(lia) Hmo3 (kl_ceil _ _ _ HK3) ltac:(lia)) as [a' Hga'].
  destruct (ev_mmap_grant_path 69632 PROT_RW s2 mo3 a' ltac:(lia) ltac:(change (page_round_up_Z 69632) with 69632; lia) (or_introl eq_refl)
              Hmo3 (kl_ceil _ _ _ HK3) Hga') as (mo4 & E4 & Hmo4 & _ & _ & _ & _).
  set (a2 := bv_unsigned a') in *.
  assert (Herr2 : is_err a2 = false).
  { pose proof Hga' as (_ & _ & G3' & _). pose proof (kl_ceil _ _ _ HK3) as Hck. unfold ceil_ok in Hck. pose_ceil.
    unfold is_err, TWO64. apply Z.ltb_ge. lia. }
  destruct (kev_measure _ (EMmap 0 69632 PROT_RW MAPF') s2 mo3 a2 s2 mo4 Hpre4 HK3 Hmo3 E4) as (Hok4 & _).
  specialize (CT4 a2 Hok4).
  rewrite KG_eq in CT4. destruct (mmap_answer_ok (LRG1 (round_up_pg b0)) 69632 a2) eqn:C6; cbn [negb] in CT4; [| exfalso; exact (ctree_ok_bad _ _ _ _ CT4)].
  destruct (leaf_res_SRet _ _ (LS_granted (round_up_pg b0) a2)) as [sS ES].
  eexists _, (set_m (strip sS) s2), mo4.
  apply (mpath_raw_malloc BUF0 s0 mo [b0; nb b0; round_up_pg b0; a2] (strip sS) (Some (slot_of sS MMv 0)) s2 mo4).
  rewrite cmalloc_TA. apply (mreal_sbind_FIN TA _ _ _ (sS, Some (MMv, 0))); [| reflexivity].
  unfold TA. cbn [mreal]. exists s1, mo1. split; [exact E1|].
  unfold K1. rewrite Hok1. cbn [negb mreal]. exists s2, mo2g. split; [exact E2|].
  unfold K2. rewrite HBA, Z.eqb_refl, BP. cbn [negb mreal]. exists s2, mo3. split; [exact E3|].
  unfold K3G. rewrite FA. cbn [negb]. unfold KGV. cbn [mreal]. exists s2, mo4. split; [exact E4|].
  rewrite KG_eq, C6, Herr2. cbn [negb]. rewrite ES. cbn. repeat split; reflexivity.
Qed.
End BRK.

Theorem MF3_A : MF3_A_stmt.
Proof.
  intros mo j r s' mo' HK Hmo Hroom Hj Hp.
  destruct (raw_malloc_measure BUF0 s0 [] mo r s' mo' 5 (2 ^ 17) HK Hmo ltac:(unfold BUF0; lia)) as (k' & E' & Hk & HE & MS).
  - intros L zs Hc Hok. exact (siteA_events L zs Hok).
  - exact Hp.
  - eapply room_step; [exact Hroom | exact Hj | exact MS | lia | lia].
Qed.

Lemma noref_sbind_FIN : forall (t : MC) zs, noref (sbind t FIN) zs <-> noref t zs.
Proof.
  induction t as [x | e k IH]; intros zs.
  - cbn [sbind]. destruct (FIN_ret x) as [y ->]. cbn [noref]. tauto.
  - rewrite sbind_vis. destruct zs as [|z zs]; [cbn [noref]; tauto|]. cbn [noref]. rewrite IH. tauto.
Qed.

Lemma follow_sbind_FIN : forall (t : MC) zs y, follow (sbind t FIN) zs = Some y -> exists x, follow t zs = Some x /\ FIN x = SRet y.
Proof.
  induction t as [x | e k IH]; intros zs y H.
  - cbn [sbind] in H. destruct (FIN_ret x) as [y' E]. rewrite E in H. cbn [follow] in H. injection H as <-.
    exists x. split; [reflexivity | exact E].
  - rewrite sbind_vis in H. destruct e; destruct zs as [|z zs]; cbn [follow] in H |- *; try discriminate; apply IH; exact H.
Qed.

Lemma FIN_some : forall st g i y, FIN (st, Some (g, i)) = SRet y -> snd y <> None.
Proof. intros st g i y H. cbn [FIN] in H. injection H as <-. cbn [snd]. discriminate. Qed.

Theorem siteA_must : forall L zs st' p,
  okpath L (cmalloc (ps_m s0) BUF0) zs -> noref (cmalloc (ps_m s0) BUF0) zs ->
  follow (cmalloc (ps_m s0) BUF0) zs = Some (st', p) -> p <> None.
Proof.
  intros L zs st' p Hok Hnr Hf. rewrite cmalloc_TA in Hok, Hnr, Hf. rewrite okpath_sbind_FIN in Hok. rewrite noref_sbind_FIN in Hnr.
  apply follow_sbind_FIN in Hf as (x & Hf & HF).
  unfold TA in Hok, Hnr, Hf. apply okpath_vis in Hok as (b0 & zs1 & -> & _ & Hok). cbn [noref follow] in Hnr, Hf. destruct Hnr as [_ Hnr].
  unfold K1 in Hok, Hnr, Hf. destruct (brk0_answer_ok b0); cbn [negb] in Hok, Hnr, Hf; [| exfalso; exact (okpath_bad _ _ _ Hok)].
  apply okpath_vis in Hok as (r & zs2 & -> & _ & Hok). cbn [noref follow] in Hnr, Hf. destruct Hnr as [_ Hnr].
  unfold K2 in Hok, Hnr, Hf. destruct (brk_answer_ok b0 (nb b0) r); cbn [negb] in Hok, Hnr, Hf; [| exfalso; exact (okpath_bad _ _ _ Hok)].
  destruct (r =? nb b0); cbn [negb] in Hok, Hnr, Hf.
  -
    destruct (brk_pages_ok STIv (round_up_pg b0) (2 * PGSZ)); cbn [negb] in Hok, Hnr, Hf; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    apply okpath_vis in Hok as (rg & zs3 & -> & _ & Hok). cbn [noref follow] in Hnr, Hf. destruct Hnr as [_ Hnr].
    unfold K3G in Hok, Hnr, Hf. destruct (mmap_fixed_answer_ok (round_up_pg b0) rg); cbn [negb] in Hok, Hnr, Hf; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    unfold KGV in Hok, Hnr, Hf. apply okpath_vis in Hok as (a2 & zs4 & -> & _ & Hok). cbn [noref follow] in Hnr, Hf.
    destruct Hnr as [Hn2 _]. specialize (Hn2 eq_refl).
    rewrite KG_eq in Hok, Hf. destruct (mmap_answer_ok (LRG1 (round_up_pg b0)) 69632 a2); cbn [negb] in Hok, Hf; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    rewrite Hn2 in Hf. destruct (leaf_res_SRet _ _ (LS_granted (round_up_pg b0) a2)) as [sS ES]. rewrite ES in Hf. cbn [follow] in Hf.
    injection Hf as <-. exact (FIN_some _ _ _ _ HF).
  -
    unfold K3T in Hok, Hnr, Hf. apply okpath_vis in Hok as (a1 & zs3 & -> & _ & Hok). cbn [noref follow] in Hnr, Hf.
    destruct Hnr as [Hn1 Hnr]. specialize (Hn1 eq_refl).
    unfold K4 in Hok, Hnr, Hf. destruct (mmap_answer_ok LRDv 8192 a1); cbn [negb] in Hok, Hnr, Hf; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    rewrite Hn1 in Hok, Hnr, Hf.
    apply okpath_vis in Hok as (m & zs4 & -> & _ & Hok). cbn [noref follow] in Hnr, Hf. destruct Hnr as [-> Hnr].
    unfold K5 in Hok, Hnr, Hf. change (mprotect_answer_ok 0) with true in Hok, Hnr, Hf.
    change ((0 =? 0) || (0 =? TWO64 - ENOSYS)) with true in Hok, Hnr, Hf. cbn [negb] in Hok, Hnr, Hf.
    unfold KCV in Hok, Hnr, Hf. apply okpath_vis in Hok as (a2 & zs5 & -> & _ & Hok). cbn [noref follow] in Hnr, Hf.
    destruct Hnr as [Hn2 _]. specialize (Hn2 eq_refl).
    rewrite KG_eq in Hok, Hf. destruct (mmap_answer_ok (LR1v a1) 69632 a2); cbn [negb] in Hok, Hf; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    rewrite Hn2 in Hf. destruct (leaf_res_SRet _ _ (LS_refused a1 a2)) as [sS ES]. rewrite ES in Hf. cbn [follow] in Hf.
    injection Hf as <-. exact (FIN_some _ _ _ _ HF).
Qed.

Theorem MF_A_must : MF_A_must_stmt.
Proof.
  intros mo HK Hmo Hroom r s' mo' Hp.
  destruct (raw_malloc_noref BUF0 s0 [] mo r s' mo' 0 HK Hmo ltac:(unfold BUF0; lia) Hroom ltac:(lia)) with (2 := Hp)
    as (L & zs & st' & p & Hc & Hf & Hok & Hnr & ->).
  { intros L zs Hc Hok. destruct (siteA_events L zs Hok) as [B1 B2]. split; lia. }
  pose proof (siteA_must L zs st' p Hok Hnr Hf) as NN. destruct p; [discriminate | congruence].
Qed.

Lemma is_err_grant : forall mo a nZ, 0 <= nZ -> ceil_ok (m_vmmaps mo) -> grant_ok mo a nZ -> is_err (bv_unsigned a) = false.
Proof.
  intros mo a nZ HnZ Hck Hg. pose proof Hg as (_ & _ & G3 & _). unfold ceil_ok in Hck. pose_ceil.
  unfold is_err, TWO64. apply Z.ltb_ge. lia.
Qed.

Theorem MF_A_succ : MF_A_succ_stmt.
Proof.
  intros mo HKR Hmo Hroom. destruct (KREL0 mo HKR) as (L & Hc & HK).
  destruct (brk_grow_ok (with_brk_next mo (Z_to_bv 64 0) (vm_brk (m_vmmaps mo)))
              (Z_to_bv 64 (nb (bv_unsigned (vm_brk (m_vmmaps mo))))) (Z_to_bv 64 (nb (bv_unsigned (vm_brk (m_vmmaps mo)))))) eqn:Hg.
  { exact (succ_grow mo L Hc HK Hmo Hroom Hg). }
  destruct (brk_steps mo L Hc HK Hmo Hg) as (E1 & E2 & Hb0 & Enb & Hpos & Hce & HK2 & Hmo1 & Hmo2 & MS2 & CT2).
  set (b0 := bv_unsigned (vm_brk (m_vmmaps mo))) in *.
  set (s1 := set_brk_ps b0 s0) in *.
  set (mo1 := with_brk_next mo (Z_to_bv 64 0) (vm_brk (m_vmmaps mo))) in *.
  set (mo2 := with_brk_next mo1 (Z_to_bv 64 (nb b0)) (vm_brk (m_vmmaps mo1))) in *.
  set (L2 := set_brkph BPDead (set_brkph (BPQueried b0) L)) in *.
  assert (Ene : (b0 =? nb b0) = false) by (apply Z.eqb_neq; unfold PGSZ in Enb; lia).
  pose proof alloc_ceiling_lt as CL.

  pose proof (room_step mo mo2 0 2 (2 * 12288) Hroom ltac:(lia) MS2 ltac:(lia) ltac:(lia)) as R2.

  unfold K3T in CT2. rewrite sbind_vis in CT2. apply ctree_ok_vis in CT2 as [Hpre3 CT3].
  destruct (room_grant mo2 (0 + 1) 8192 R2 ltac:(lia) Hmo2 (kl_ceil _ _ _ HK2) ltac:(lia)) as [a Hga].
  destruct (ev_mmap_none_grant_path 8192 s1 mo2 a ltac:(lia) ltac:(change (page_round_up_Z 8192) with 8192; lia) Hmo2 (kl_ceil _ _ _ HK2) Hga) as (mo3 & E3 & Hmo3 & Hva3 & Hvm3).
  change (page_round_up_Z 8192) with 8192 in Hvm3.
  set (a1 := bv_unsigned a) in *.
  pose proof Hga as (G1 & G2 & G3 & _). rewrite page_size_eq in G1. fold a1 in G1, G2, G3.
  pose proof (kl_ceil _ _ _ HK2) as CK2. unfold ceil_ok in CK2. pose_ceil.
  assert (G3' : a1 + 8192 <= alloc_ceiling).
  { apply (ceil_page_le (m_vmmaps mo2)); [exact (kl_ceil _ _ _ HK2) | rewrite page_size_eq, Z.add_mod, G1 by lia; reflexivity | exact G3]. }
  pose proof (is_err_grant mo2 a 8192 ltac:(lia) (kl_ceil _ _ _ HK2) Hga) as Herr1. fold a1 in Herr1.
  destruct (kev_measure L2 (EMmap 0 8192 PROT_NONE MAPF') s1 mo2 a1 s1 mo3 Hpre3 HK2 Hmo2 E3) as (Hok3 & HK3 & _ & _ & _ & _ & _ & M3).
  specialize (CT3 a1 Hok3). set (L3 := event_post L2 (EMmap 0 8192 PROT_NONE MAPF') a1) in *.
  unfold K4 in CT3. destruct (mmap_answer_ok LRDv 8192 a1) eqn:C4; cbn [negb] in CT3; [| exfalso; exact (ctree_ok_bad _ _ _ _ CT3)].
  rewrite Herr1 in CT3. rewrite sbind_vis in CT3. apply ctree_ok_vis in CT3 as [Hpre4 CT4].
  pose proof (msteps_snoc _ _ _ _ _ (EMmap 0 8192 PROT_NONE MAPF') MS2 ltac:(lia) M3) as MS3.
  change (esize (EMmap 0 8192 PROT_NONE MAPF')) with 8192 in MS3.
  pose proof (room_step mo mo3 0 3 _ Hroom ltac:(lia) MS3 ltac:(lia) ltac:(lia)) as R3.

  assert (Hcn : map_contains (vm_noaccess (m_vmmaps mo3)) (Z_to_bv 64 (a1 + PGSZ)) (Z_to_bv 64 PGSZ) = true).
  { rewrite Hvm3. unfold map_contains. cbn [vm_noaccess existsb fst snd]. apply orb_true_iff. left.
    unfold PGSZ. rewrite !unsigned_lit by (pose_ceil; lia). fold a1.
    apply andb_true_iff. split; apply Z.leb_le; lia. }
  assert (Hcm : map_contains (vm_maps (m_vmmaps mo3)) (Z_to_bv 64 (a1 + PGSZ)) (Z_to_bv 64 PGSZ) = true).
  { rewrite Hvm3. unfold map_contains. cbn [vm_maps existsb fst snd]. apply orb_true_iff. left.
    unfold PGSZ. rewrite !unsigned_lit by (pose_ceil; lia). fold a1.
    apply andb_true_iff. split; apply Z.leb_le; lia. }
  assert (Hlive : vm_live_bytes (m_vmmaps mo3) <= vm_limit (m_vmmaps mo3)).
  { destruct R3 as [_ _ RL RM]. lia. }
  pose proof (ev_mprotect_grant_path (a1 + PGSZ) s1 mo3 ltac:(unfold PGSZ; lia)
                ltac:(unfold PGSZ; rewrite Z.add_mod, G1 by lia; reflexivity)
                ltac:(unfold PGSZ in *; lia) Hmo3 Hcn Hcm Hlive) as E4.
  cbv zeta in E4. set (mo4 := mprotect_model_next mo3 (Z_to_bv 64 (a1 + PGSZ)) (Z_to_bv 64 PGSZ)) in *.
  destruct (kev_measure L3 (EMprotect (a1 + PGSZ) PGSZ PROT_RW) s1 mo3 0 s1 mo4 Hpre4 HK3 Hmo3 E4) as (Hok4 & HK4 & _ & _ & _ & Hmo4 & _ & M4).
  specialize (CT4 0 Hok4). set (L4 := event_post L3 (EMprotect (a1 + PGSZ) PGSZ PROT_RW) 0) in *.
  unfold K5 in CT4. change (mprotect_answer_ok 0) with true in CT4. change ((0 =? 0) || (0 =? TWO64 - ENOSYS)) with true in CT4.
  cbn [negb] in CT4. unfold KCV in CT4. rewrite sbind_vis in CT4. apply ctree_ok_vis in CT4 as [Hpre5 CT5].
  pose proof (msteps_snoc _ _ _ _ _ (EMprotect (a1 + PGSZ) PGSZ PROT_RW) MS3 ltac:(lia) M4) as MS4.
  change (esize (EMprotect (a1 + PGSZ) PGSZ PROT_RW)) with 0 in MS4.
  pose proof (room_step mo mo4 0 4 _ Hroom ltac:(lia) MS4 ltac:(lia) ltac:(lia)) as R4.

  destruct (room_grant mo4 (0 + 1) 69632 R4 ltac:(lia) Hmo4 (kl_ceil _ _ _ HK4) ltac:(lia)) as [a' Hga'].
  destruct (ev_mmap_grant_path 69632 PROT_RW s1 mo4 a' ltac:(lia) ltac:(change (page_round_up_Z 69632) with 69632; lia) (or_introl eq_refl) Hmo4 (kl_ceil _ _ _ HK4) Hga') as (mo5 & E5 & Hmo5 & _ & _ & _ & _).
  set (a2 := bv_unsigned a') in *.
  pose proof (is_err_grant mo4 a' 69632 ltac:(lia) (kl_ceil _ _ _ HK4) Hga') as Herr2. fold a2 in Herr2.
  destruct (kev_measure L4 (EMmap 0 69632 PROT_RW MAPF') s1 mo4 a2 s1 mo5 Hpre5 HK4 Hmo4 E5) as (Hok5 & _).
  specialize (CT5 a2 Hok5).
  rewrite KG_eq in CT5. destruct (mmap_answer_ok (LR1v a1) 69632 a2) eqn:C6; cbn [negb] in CT5; [| exfalso; exact (ctree_ok_bad _ _ _ _ CT5)].
  destruct (leaf_res_SRet _ _ (LS_refused a1 a2)) as [sS ES].

  eexists _, (set_m (strip sS) s1), mo5.
  apply (mpath_raw_malloc BUF0 s0 mo [b0; b0; a1; 0; a2] (strip sS) (Some (slot_of sS MMv 0)) s1 mo5).
  rewrite cmalloc_TA. apply (mreal_sbind_FIN TA _ _ _ (sS, Some (MMv, 0))); [| reflexivity].
  unfold TA. cbn [mreal]. exists s1, mo1. split; [exact E1|].
  unfold K1. rewrite Hb0. cbn [negb mreal]. exists s1, mo2. split; [exact E2|].
  unfold K2. replace (brk_answer_ok b0 (nb b0) b0) with true by (unfold brk_answer_ok; rewrite Z.eqb_refl, orb_true_r; reflexivity).
  rewrite Ene. cbn [negb]. unfold K3T. cbn [mreal]. exists s1, mo3. split; [exact E3|].
  unfold K4. rewrite C4, Herr1. cbn [negb mreal]. exists s1, mo4. split; [exact E4|].
  unfold K5. change (mprotect_answer_ok 0) with true. change ((0 =? 0) || (0 =? TWO64 - ENOSYS)) with true. cbn [negb].
  unfold KCV. cbn [mreal]. exists s1, mo5. split; [exact E5|].
  rewrite KG_eq, C6, Herr2. cbn [negb]. rewrite ES. cbn. repeat split; reflexivity.
Qed.

Lemma LS_fg : forall st1 a2,
  (forall sc, active st1 sc = None) -> s_metas st1 !! MMv = Some meta0 ->
  LS st1 a2 = SRet (MF_Evol.fg_final st1 MMv a2, Some (MMv, 0)).
Proof.
  intros st1 a2 HA HM.
  change (LS st1 a2) with (ag_tail lay_none (MF_Evol.fg_st4 st1 MMv a2) 44 MMv (s_next_rid st1, 0) 1 0
     (fun st2 go => match go with
                    | None => KM st2 (-1)
                    | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                                queue (LActive 44) g st3 (fun st4 => KM st4 0) BL
                    end)).
  rewrite (MF_Evol.first_group_leaf st1 MMv a2 HA HM KM BL).
  unfold KM. change (0 <? 0) with false. cbv iota.
  unfold MF_Evol.fg_final. rewrite MF_SiteC.fin_active, Z.eqb_refl. reflexivity.
Qed.

Lemma PHI_strip : forall st, MF_Phi.PHI st -> MF_Phi.PHI (strip st).
Proof. intros st H. exact H. Qed.

Lemma ST1v_facts : forall a1, let st1 := ST1v a1 in
  c_init_done (s_ctx st1) = 1 /\ 50 <= c_avail_meta_count (s_ctx st1) /\ c_free_meta_head (s_ctx st1) = None
  /\ (forall sc, active st1 sc = None) /\ s_groups st1 = ∅ /\ s_metas st1 !! MMv = Some meta0.
Proof.
  intros a1. cbv zeta. split; [reflexivity|]. split; [vm_compute; discriminate|]. split; [reflexivity|].
  split; [intros sc; reflexivity|]. split; [reflexivity|]. vm_compute. reflexivity.
Qed.
Lemma STG1v_facts : forall b, let st1 := STG1v b in
  c_init_done (s_ctx st1) = 1 /\ 50 <= c_avail_meta_count (s_ctx st1) /\ c_free_meta_head (s_ctx st1) = None
  /\ (forall sc, active st1 sc = None) /\ s_groups st1 = ∅ /\ s_metas st1 !! MMv = Some meta0.
Proof.
  intros b. cbv zeta. split; [reflexivity|]. split; [vm_compute; discriminate|]. split; [reflexivity|].
  split; [intros sc; reflexivity|]. split; [reflexivity|]. vm_compute. reflexivity.
Qed.

Local Ltac bad CP := rewrite sbind_bad in CP; exact (False_ind _ (MF_EvolA.cpath_undef_inv _ _ _ _ _ CP)).
Local Ltac leafN CP E := rewrite E, sbind_ret_l in CP; cbn [FIN] in CP; apply MF_EvolA.cpath_ret_inv in CP as [_ CP]; discriminate.

Theorem T2_A : forall L L1 cs1 c,
  MI_Contracts.SIMREL (ps_m s0) L -> cpath L (cmalloc (ps_m s0) BUF0) L1 (cs1, Some c) -> MF_Phi.PHI cs1.
Proof.
  intros L L1 cs1 c Hc CP. rewrite cmalloc_TA in CP. unfold TA in CP.
  rewrite sbind_vis in CP. apply MF_EvolA.cpath_vis_inv in CP as (b0 & _ & CP). unfold K1 in CP.
  destruct (brk0_answer_ok b0); cbn [negb] in CP; [| bad CP].
  rewrite sbind_vis in CP. apply MF_EvolA.cpath_vis_inv in CP as (r & _ & CP). unfold K2 in CP.
  destruct (brk_answer_ok b0 (nb b0) r); cbn [negb] in CP; [| bad CP].
  destruct (r =? nb b0); cbn [negb] in CP.
  -
    destruct (brk_pages_ok STIv (round_up_pg b0) (2 * PGSZ)); cbn [negb] in CP; [| bad CP].
    rewrite sbind_vis in CP. apply MF_EvolA.cpath_vis_inv in CP as (rg & _ & CP). unfold K3G in CP.
    destruct (mmap_fixed_answer_ok (round_up_pg b0) rg); cbn [negb] in CP; [| bad CP].
    unfold KGV in CP. rewrite sbind_vis in CP. apply MF_EvolA.cpath_vis_inv in CP as (a2 & _ & CP). rewrite KG_eq in CP.
    destruct (mmap_answer_ok (LRG1 (round_up_pg b0)) 69632 a2); cbn [negb] in CP; [| bad CP].
    destruct (STG1v_facts (round_up_pg b0)) as (HI & HC & HF & HA & HG & HM).
    destruct (is_err a2).
    + destruct (leaf_res_SRet _ _ (LF_granted (round_up_pg b0))) as [s E]. leafN CP E.
    + rewrite (LS_fg _ a2 HA HM), sbind_ret_l in CP. cbn [FIN] in CP. apply MF_EvolA.cpath_ret_inv in CP as [_ CP].
      injection CP as E1 E2. rewrite E1. apply PHI_strip. apply MF_Evol.PHI_first_group; assumption.
  -
    unfold K3T in CP. rewrite sbind_vis in CP. apply MF_EvolA.cpath_vis_inv in CP as (a1 & _ & CP). unfold K4 in CP.
    destruct (mmap_answer_ok LRDv 8192 a1); cbn [negb] in CP; [| bad CP].
    destruct (is_err a1).
    { rewrite sbind_ret_l in CP. cbn [FIN] in CP. apply MF_EvolA.cpath_ret_inv in CP as [_ CP]. discriminate. }
    rewrite sbind_vis in CP. apply MF_EvolA.cpath_vis_inv in CP as (m & _ & CP). unfold K5 in CP.
    destruct (mprotect_answer_ok m); cbn [negb] in CP; [| bad CP].
    destruct ((m =? 0) || (m =? TWO64 - ENOSYS)).
    2:{ rewrite sbind_ret_l in CP. cbn [FIN] in CP. apply MF_EvolA.cpath_ret_inv in CP as [_ CP]. discriminate. }
    unfold KCV in CP. rewrite sbind_vis in CP. apply MF_EvolA.cpath_vis_inv in CP as (a2 & _ & CP). rewrite KG_eq in CP.
    destruct (mmap_answer_ok (LR1v a1) 69632 a2); cbn [negb] in CP; [| bad CP].
    destruct (ST1v_facts a1) as (HI & HC & HF & HA & HG & HM).
    destruct (is_err a2).
    + destruct (leaf_res_SRet _ _ (LF_refused a1)) as [s E]. leafN CP E.
    + rewrite (LS_fg _ a2 HA HM), sbind_ret_l in CP. cbn [FIN] in CP. apply MF_EvolA.cpath_ret_inv in CP as [_ CP].
      injection CP as E1 E2. rewrite E1. apply PHI_strip. apply MF_Evol.PHI_first_group; assumption.
Qed.

End CEIL.

Ltac krefl := lazymatch goal with |- ?l = _ => exact_no_check (@eq_refl _ l) end.
Local Ltac bad CP := rewrite sbind_bad in CP; exact (False_ind _ (MF_EvolA.cpath_undef_inv _ _ _ _ _ CP)).
Local Ltac leafN CP E := rewrite E, sbind_ret_l in CP; cbn [FIN] in CP; apply MF_EvolA.cpath_ret_inv in CP as [_ CP]; discriminate.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.NodesM OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.DecodeM.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Prelim OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.KInv.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.MSafe OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KLink OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KOwn OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.PgArith.
Import F_syscalls.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.StateGlue OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.NodeSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.TreeBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.TreeBridgeN OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.KRel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MPath OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.Room OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.Grant OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MMeas OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.NoRefuse OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MFMust.
Import MF.TwinB.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition cs0 : mstate := ps_m s0.
Local Notation MC := (Malloc.M (mstate * option (aptr * Z))%type).
Definition T0 : MC := malloc_core lay_none cs0 BUF0.

Definition FIN (x : mstate * option (aptr * Z)) : Malloc.M (mstate * option cptr) :=
  let (st1, r) := x in ret (strip st1, match r with Some (g, idx) => Some (slot_of st1 g idx) | None => None end).

Ltac krefl := lazymatch goal with |- ?l = _ => exact_no_check (@eq_refl _ l) end.

Lemma cmalloc_T0 : cmalloc cs0 BUF0 = sbind T0 FIN.
Proof. krefl. Qed.

Definition BL : MC := ret (cs0, @None (aptr * Z)).
Definition KM (st1 : mstate) (idx : Z) : MC :=
  if idx <? 0 then ret (st1, None)
  else match active st1 44 with
       | Some gp => ret (st1, Some (gp, idx))
       | None => SVis (EUndef UBadPtr) (fun _ : Z => BL)
       end.
Definition KS (st2 : mstate) (go : optr) : MC :=
  match go with
  | None => KM st2 (-1)
  | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
              queue (LActive 44) g st3 (fun st4 => KM st4 0) BL
  end.

Definition KAG : mstate -> optr -> MC :=
  let sc := 44 in let req := BUF0 in let lay := lay_none in let k := KS in let bail := BL in
  let size := UNIT * size_class sc in
  (fun st mo =>
  match mo with
  | None => k st None
  | Some m =>
    let usage0 := usage st sc in
    let cnt :=
      if sc <? 9 then small_cnt_pick sc usage0
      else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) usage0) size in
    let cnt := if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt in
    let tail (st : mstate) (p : aptr) (cnt active_idx : Z) : MC := ag_tail lay st sc m p cnt active_idx k in
    if PGSZ / 2 <? size * cnt + UNIT then
      let nosmall := is_bouncing sc st in
      let st1 := step_seq (account_bounce sc st) in
      let usage1 := if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0 in
      let cnt :=
        if (usage1 <? 4 * cnt) && negb nosmall then
          if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
          else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
          else cnt
        else cnt in
      let needed := round_up_pg (size * cnt + UNIT) in
      let '(cnt, needed) :=
        if negb nosmall && (cnt <=? 7) then
          let req := round_up_pg (req + IB + UNIT) in
          if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed)
        else (cnt, needed) in
      SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
        if negb (mmap_answer_ok (live_ranges st1) needed r) then bad_answer bail else
        if is_err r then free_meta m st1 (fun st2 => k st2 None) bail
        else
          let '(st2, rid) := new_region RKGroup r needed st1 in
          let st3 := upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2 in
          let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
          let ai := (4096 - UNIT) / size - 1 in
          let ai := if cnt - 1 <? ai then cnt - 1 else ai in
          let ai := if ai <? 0 then 0 else ai in
          tail st4 (rid, 0) cnt ai)
    else
      let j := size_to_class (UNIT + cnt * size - IB) in
      alloc_slot lay 63%nat st j (UNIT + cnt * size - IB) (fun st1 idx =>
        if idx <? 0 then free_meta m st1 (fun st2 => k st2 None) bail
        else
          match active st1 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g =>
            let p := slot_of st1 g idx in
            let st2 := lh_nest lay st1 g idx j size cnt in
            let st3 := upd_meta m (m_set_maplen 0) st2 in
            tail st3 p cnt (cnt - 1)
          end) bail
  end).

Definition STI : mstate := upd_ctx (fun c => set_init_done 1 (set_secret (s_secret cs0) c)) cs0.
Definition STIv : mstate := Eval vm_compute in STI.
Definition STDv : mstate := Eval vm_compute in (upd_ctx (set_brk BrkDead) STI).
Definition LRDv : list (Z * Z) := Eval vm_compute in (live_ranges STDv).
Definition P0v : aptr := (0%N, 4096).

Definition ST2f (a1 : Z) : mstate :=
  let '(st1, rid) := new_region RKMeta a1 8192 STDv in
  upd_ctx (fun c => set_meta_alloc_shift (c_meta_alloc_shift c + 1)
                      (set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, PGSZ)) c))) st1.
Definition ST2v : Z -> mstate := Eval vm_compute in ST2f.

Definition am_out (st : mstate) : mstate * aptr :=
  match am_carve st P0v (fun s mo => SRet (s, mo)) (SRet (st, @None aptr)) with
  | SRet (s, Some m) => (step_seq (account_bounce 44 s), m)
  | _ => (st, P0v)
  end.
Definition MMv : aptr := Eval vm_compute in (let '(_, m) := am_out (ST2v 0) in m).
Definition ST1v : Z -> mstate := Eval vm_compute in (fun a1 => let '(s, _) := am_out (ST2v a1) in s).
Definition LR1v : Z -> list (Z * Z) := Eval vm_compute in (fun a1 => live_ranges (ST1v a1)).

Definition STG2f (base : Z) : mstate :=
  let '(st1, rid) := new_region RKBrk base (2 * PGSZ) STIv in
  upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, PGSZ)) (set_brk (BrkLive rid (2 * PGSZ)) c))) st1.
Definition STG2v : Z -> mstate := Eval vm_compute in STG2f.
Definition STG1v : Z -> mstate := Eval vm_compute in (fun base => let '(s, _) := am_out (STG2v base) in s).
Definition RESVv : list (Z * Z) := Eval vm_compute in (reservedZ rsegs).
Definition LRG1 (base : Z) : list (Z * Z) := RESVv ++ [(base + PGSZ, 4096)].

Definition nb (b0 : Z) : Z := round_up_pg b0 + 2 * PGSZ.
Definition ENc : Z := TWO64 - 12.
Definition MAPF' : Z := MAP_PRIVATE + MAP_ANON.
Definition MAPFX' : Z := MAP_PRIVATE + MAP_ANON + MAP_FIXED.

Definition LF (st1 : mstate) : MC := free_meta MMv st1 (fun st2 => KS st2 None) BL.
Definition LS (st1 : mstate) (a2 : Z) : MC :=
  let '(st2, rid) := new_region RKGroup a2 69632 st1 in
  let st3 := upd_meta MMv (m_set_maplen (Z.shiftr 69632 12)) st2 in
  let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
  let ai := (4096 - UNIT) / (UNIT * size_class 44) - 1 in
  let ai := if 1 - 1 <? ai then 1 - 1 else ai in
  let ai := if ai <? 0 then 0 else ai in
  ag_tail lay_none st4 44 MMv (rid, 0) 1 ai KS.

Definition KG (lr : list (Z * Z)) (st1 : mstate) : Z -> MC := fun a2 =>
  if negb (mmap_answer_ok lr 69632 a2) then bad_answer BL
  else if is_err a2 then free_meta MMv st1 (fun st2 => KS st2 None) BL
  else let '(st2, rid) := new_region RKGroup a2 69632 st1 in
       let st3 := upd_meta MMv (m_set_maplen (Z.shiftr 69632 12)) st2 in
       let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
       let ai := (4096 - UNIT) / (UNIT * size_class 44) - 1 in
       let ai := if 1 - 1 <? ai then 1 - 1 else ai in
       let ai := if ai <? 0 then 0 else ai in
       ag_tail lay_none st4 44 MMv (rid, 0) 1 ai KS.

Definition KCV (a1 : Z) : MC := SVis (EMmap 0 69632 PROT_RW MAPF') (KG (LR1v a1) (ST1v a1)).
Definition K5 (a1 : Z) : Z -> MC := fun m =>
  if negb (mprotect_answer_ok m) then bad_answer BL
  else if (m =? 0) || (m =? TWO64 - ENOSYS) then KCV a1 else SRet (ST2v a1, None).
Definition K4 : Z -> MC := fun a1 =>
  if negb (mmap_answer_ok LRDv 8192 a1) then bad_answer BL
  else if is_err a1 then SRet (STDv, None)
  else SVis (EMprotect (a1 + PGSZ) PGSZ PROT_RW) (K5 a1).
Definition K3T : MC := SVis (EMmap 0 8192 PROT_NONE MAPF') K4.

Definition KGV (base : Z) : MC := SVis (EMmap 0 69632 PROT_RW MAPF') (KG (LRG1 base) (STG1v base)).
Definition K3G (b0 : Z) : Z -> MC := fun rg =>
  if negb (mmap_fixed_answer_ok (round_up_pg b0) rg) then bad_answer BL else KGV (round_up_pg b0).
Definition K2 (b0 : Z) : Z -> MC := fun r =>
  if negb (brk_answer_ok b0 (nb b0) r) then bad_answer BL
  else if negb (r =? nb b0) then K3T
  else if negb (brk_pages_ok STIv (round_up_pg b0) (2 * PGSZ)) then bad_answer BL
  else SVis (EMmap (round_up_pg b0) PGSZ PROT_NONE MAPFX') (K3G b0).
Definition K1 : Z -> MC := fun b0 =>
  if negb (brk0_answer_ok b0) then bad_answer BL else SVis (EBrk (nb b0)) (K2 b0).
Definition TA : MC := SVis (EBrk 0) K1.

Theorem TA_T0 : TA = T0.
Proof. krefl. Qed.

Lemma cmalloc_TA : cmalloc (ps_m s0) BUF0 = sbind TA FIN.
Proof. rewrite TA_T0. exact cmalloc_T0. Qed.

Definition leaf_res {R} (t : Malloc.M (mstate * R)) : option R := match t with SRet (_, r) => Some r | _ => None end.

Lemma leaf_res_SRet {R} (t : Malloc.M (mstate * R)) r : leaf_res t = Some r -> exists s, t = SRet (s, r).
Proof. destruct t as [[s r']|e k]; cbn; [| discriminate]. intros H. injection H as ->. exists s. reflexivity. Qed.

Lemma LF_refused : forall a1, leaf_res (LF (ST1v a1)) = Some None.
Proof. intros a1. krefl. Qed.
Lemma LS_refused : forall a1 a2, leaf_res (LS (ST1v a1) a2) = Some (Some (MMv, 0)).
Proof. intros a1 a2. krefl. Qed.
Lemma LF_granted : forall b, leaf_res (LF (STG1v b)) = Some None.
Proof. intros b. krefl. Qed.
Lemma LS_granted : forall b a2, leaf_res (LS (STG1v b) a2) = Some (Some (MMv, 0)).
Proof. intros b a2. krefl. Qed.

Lemma KG_eq : forall lr st1 a2,
  KG lr st1 a2 = if negb (mmap_answer_ok lr 69632 a2) then bad_answer BL else if is_err a2 then LF st1 else LS st1 a2.
Proof. intros. krefl. Qed.

Lemma K4_refused : K4 (neg_errno ENOMEM) = SRet (STDv, None).
Proof. krefl. Qed.

Lemma sbind_if {R S} (c : bool) (a b : Malloc.M R) (f : R -> Malloc.M S) :
  sbind (if c then a else b) f = if c then sbind a f else sbind b f.
Proof. destruct c; reflexivity. Qed.

Lemma sbind_bad {R S} (b : Malloc.M R) (f : R -> Malloc.M S) :
  sbind (bad_answer b) f = SVis (EUndef UBadAnswer) (fun _ => sbind b f).
Proof. krefl. Qed.

Lemma FIN_ret : forall x, exists y, FIN x = SRet y.
Proof. intros [st [[g i]|]]; eexists; reflexivity. Qed.

Lemma okpath_ret {R} L (x : R) zs : okpath L (SRet x) zs <-> zs = [].
Proof. destruct zs; cbn; [tauto | split; [tauto | discriminate]]. Qed.

Lemma okpath_vis {R} L e (k : Z -> Malloc.M R) zs :
  okpath L (SVis e k) zs <-> exists z zs', zs = z :: zs' /\ answer_ok L e z = true /\ okpath (event_post L e z) (k z) zs'.
Proof.
  destruct zs as [|z zs']; cbn.
  - split; [tauto|]. intros (z & zs' & H & _). discriminate.
  - split; [intros [A B]; exists z, zs'; auto|]. intros (z0 & zs0 & E & A & B). injection E as <- <-. auto.
Qed.

Lemma okpath_undef {R} L u (k : Z -> Malloc.M R) zs : okpath L (SVis (EUndef u) k) zs -> False.
Proof. destruct zs; cbn; [tauto|]. intros [H _]. discriminate. Qed.

Lemma okpath_bad {R} L (b : Malloc.M R) zs : okpath L (bad_answer b) zs -> False.
Proof. apply okpath_undef. Qed.

Lemma okpath_sbind_FIN : forall (t : MC) L zs, okpath L (sbind t FIN) zs <-> okpath L t zs.
Proof.
  induction t as [x | e k IH]; intros L zs.
  - cbn [sbind]. destruct (FIN_ret x) as [y ->]. rewrite !okpath_ret. tauto.
  - rewrite sbind_vis. rewrite !okpath_vis. split; intros (z & zs' & -> & A & B); exists z, zs'; (split; [reflexivity|]); (split; [exact A|]); apply IH; exact B.
Qed.

Lemma evs_of_sbind_FIN : forall (t : MC) zs, evs_of (sbind t FIN) zs = evs_of t zs.
Proof.
  induction t as [x | e k IH]; intros zs.
  - cbn [sbind]. destruct (FIN_ret x) as [y ->]. destruct zs; reflexivity.
  - rewrite sbind_vis. destruct zs as [|z zs]; [reflexivity|]. cbn [evs_of]. f_equal. apply IH.
Qed.

Lemma mreal_sbind_FIN : forall (t : MC) zs s mo x s' mo' y,
  mreal t zs s mo x s' mo' -> FIN x = SRet y -> mreal (sbind t FIN) zs s mo y s' mo'.
Proof.
  induction t as [x0 | e k IH]; intros zs s mo x s' mo' y H E.
  - destruct zs; cbn in H; [| destruct H]. destruct H as (-> & -> & ->). cbn [sbind]. rewrite E. cbn. auto.
  - destruct zs as [|z zs]; cbn in H; [destruct H|]. destruct H as (s1 & mo1 & H1 & H2).
    rewrite sbind_vis. cbn [mreal]. exists s1, mo1. split; [exact H1|]. eapply IH; eassumption.
Qed.

Lemma esize_vals : esize (EMmap 0 8192 PROT_NONE MAPF') = 8192 /\ esize (EMmap 0 69632 PROT_RW MAPF') = 69632
  /\ (forall a, esize (EMmap a PGSZ PROT_NONE MAPFX') = 4096) /\ (forall a, esize (EBrk a) = 12288)
  /\ (forall a l p, esize (EMprotect a l p) = 0).
Proof. repeat split; intros; reflexivity. Qed.

Lemma KG_events : forall lr st1 L zs, (forall a2, exists r, leaf_res (if is_err a2 then LF st1 else LS st1 a2) = Some r) ->
  okpath L (SVis (EMmap 0 69632 PROT_RW MAPF') (KG lr st1)) zs ->
  exists a2, zs = [a2] .
Proof.
  intros lr st1 L zs Hleaf Hok. apply okpath_vis in Hok as (a2 & zs' & -> & _ & Hok).
  rewrite KG_eq in Hok. destruct (mmap_answer_ok lr 69632 a2); cbn [negb] in Hok; [| exfalso; exact (okpath_bad _ _ _ Hok)].
  destruct (Hleaf a2) as [r Hr]. destruct (leaf_res_SRet _ _ Hr) as [s E]. rewrite E in Hok.
  apply okpath_ret in Hok. subst zs'. exists a2. reflexivity.
Qed.

Theorem siteA_events : forall L zs, okpath L (cmalloc (ps_m s0) BUF0) zs ->
  (length (evs_of (cmalloc (ps_m s0) BUF0) zs) <= 5)%nat /\ esum (evs_of (cmalloc (ps_m s0) BUF0) zs) <= 2 ^ 17.
Proof.
  intros L zs Hok. rewrite cmalloc_TA in *. rewrite okpath_sbind_FIN in Hok. rewrite evs_of_sbind_FIN.
  destruct esize_vals as (E1 & E2 & E3 & E4 & E5).
  unfold TA in *. apply okpath_vis in Hok as (b0 & zs1 & -> & _ & Hok). cbn [evs_of length esum]. rewrite E4.
  unfold K1 in *. destruct (brk0_answer_ok b0); cbn [negb] in Hok |- *; [| exfalso; exact (okpath_bad _ _ _ Hok)].
  apply okpath_vis in Hok as (r & zs2 & -> & _ & Hok). cbn [evs_of length esum]. rewrite E4.
  unfold K2 in *. destruct (brk_answer_ok b0 (nb b0) r); cbn [negb] in Hok |- *; [| exfalso; exact (okpath_bad _ _ _ Hok)].
  destruct (r =? nb b0); cbn [negb] in Hok |- *.
  -
    destruct (brk_pages_ok STIv (round_up_pg b0) (2 * PGSZ)); cbn [negb] in Hok |- *; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    apply okpath_vis in Hok as (rg & zs3 & -> & _ & Hok). cbn [evs_of length esum]. rewrite E3.
    unfold K3G in *. destruct (mmap_fixed_answer_ok (round_up_pg b0) rg); cbn [negb] in Hok |- *; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    unfold KGV in *. destruct (KG_events _ _ _ _ ltac:(intros a2; destruct (is_err a2); eexists; [apply LF_granted | apply LS_granted]) Hok) as [a2 ->].
    cbn [evs_of length esum]. rewrite E2. rewrite KG_eq.
    destruct (negb _); [cbn; lia|]. destruct (is_err a2).
    + destruct (leaf_res_SRet _ _ (LF_granted (round_up_pg b0))) as [s ->]. cbn. lia.
    + destruct (leaf_res_SRet _ _ (LS_granted (round_up_pg b0) a2)) as [s ->]. cbn. lia.
  -
    unfold K3T in *. apply okpath_vis in Hok as (a1 & zs3 & -> & _ & Hok). cbn [evs_of length esum]. rewrite E1.
    unfold K4 in *. destruct (mmap_answer_ok LRDv 8192 a1); cbn [negb] in Hok |- *; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    destruct (is_err a1).
    { apply okpath_ret in Hok. subst zs3. cbn. lia. }
    apply okpath_vis in Hok as (m & zs4 & -> & _ & Hok). cbn [evs_of length esum]. rewrite E5.
    unfold K5 in *. destruct (mprotect_answer_ok m); cbn [negb] in Hok |- *; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    destruct ((m =? 0) || (m =? TWO64 - ENOSYS)).
    + unfold KCV in *. destruct (KG_events _ _ _ _ ltac:(intros a2; destruct (is_err a2); eexists; [apply LF_refused | apply LS_refused]) Hok) as [a2 ->].
      cbn [evs_of length esum]. rewrite E2. rewrite KG_eq.
      destruct (negb _); [cbn; lia|]. destruct (is_err a2).
      * destruct (leaf_res_SRet _ _ (LF_refused a1)) as [s ->]. cbn. lia.
      * destruct (leaf_res_SRet _ _ (LS_refused a1 a2)) as [s ->]. cbn. lia.
    + apply okpath_ret in Hok. subst zs4. cbn. lia.
Qed.

Lemma msteps_snoc : forall k E mo mo1 mo2 e,
  msteps k E mo mo1 -> 0 <= E -> mstep (esize e) mo1 mo2 -> msteps (S k) (E + esize e) mo mo2.
Proof.
  intros k E mo mo1 mo2 e [A1 A2 A3 A4] HE [B1 B2 B3 B4]. pose proof (esize_nonneg e). constructor.
  - lia. - lia.
  - intros B HB H3 Hs. apply B3; [lia|]. apply A3; [lia | exact H3 | exact Hs].
  - congruence.
Qed.

Lemma ev_mmap_none_grant_path : forall len s mo (a : word),
  let h := m_vmmaps mo in let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  0 < len -> nZ < 2^64 -> mo_ok mo ->
  ceil_ok h -> grant_ok mo a nZ ->
  exists mo', tpath nstep (ev_step (EMmap 0 len Malloc.PROT_NONE (Malloc.MAP_PRIVATE + MAP_ANON)) s) mo [] (Ok (bv_unsigned a, s)) mo'
    /\ mo_ok mo' /\ vm_agree mo mo'
    /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) ((a, n) :: vm_noaccess h)
                                   (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
  intros len s mo a h nZ n Hlen HnZ Hmo Hck Hg.
  pose proof Hg as (G1 & G2 & G3 & G4 & G5). fold h in G3, G4, G5 |- *.
  assert (Hnr : mmap_noreserve_b (Z_to_bv 64 (Malloc.MAP_PRIVATE + MAP_ANON)) = false) by reflexivity.
  assert (Hge : len <= nZ) by (unfold nZ, page_round_up_Z, page_size; lia).
  assert (HlenU : bv_unsigned (Z_to_bv 64 len) = len).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul Pos.mul]. lia. }
  assert (Hw : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  unfold ev_step. change (negb (Z.land (Malloc.MAP_PRIVATE + MAP_ANON) MAP_FIXED_Z =? 0)) with false. cbn iota.
  change (Malloc.PROT_NONE =? 0) with true. cbn iota.
  set (mo' := with_mmap_backing (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) a n
                (with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) ((a, n) :: vm_noaccess h)
                               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo)).
  set (eff := mkEffectU a [] [] [(a, n)] [] []).
  assert (Hst : nstep (NMmap 0 len Malloc.PROT_NONE (Malloc.MAP_PRIVATE + MAP_ANON)) mo eff mo' []).
  { apply (proj2 (nstep_mmap_none_inv 0 len mo eff mo' [] Hw)). split; [reflexivity|]. right.
    exists a. rewrite HlenU. fold h nZ n. split; [| split; reflexivity]. repeat split; assumption. }
  destruct (nstep_dec_mmap_none len [] mo eff mo' [] Hlen ltac:(unfold mmap_len; exact HnZ) Hck ltac:(constructor) Hst)
    as (_ & VA & x & Hdec & Hx).
  assert (Hx' : x = MmOk (bv_unsigned a)).
  { unfold eff, dec_mmap_none in Hdec. cbn [eff_copies eff_copyins] in Hdec. rewrite !bv_eqb_refl in Hdec.
    destruct (mmap_addr_ok len [] (bv_unsigned a)); cbn [andb] in Hdec; congruence. }
  subst x.
  exists mo'. split; [| split; [exact (vm_agree_mo_ok _ _ VA Hmo) | split; [exact VA |]]].
  - eapply (tpath_mbind _ _ s mo (MmOk (bv_unsigned a)) s); [eapply tpath_msys; [exact Hst | exact Hdec] | apply tpath_mret].
  - unfold mo'. rewrite with_mmap_backing_noreserve_false by exact Hnr. reflexivity.
Qed.

Lemma ev_mprotect_grant_path : forall (a : Z) s mo,
  let h := m_vmmaps mo in let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 PGSZ in
  0 < a -> a mod 4096 = 0 -> a + PGSZ <= alloc_ceiling -> mo_ok mo ->
  map_contains (vm_noaccess h) aw nw = true -> map_contains (vm_maps h) aw nw = true ->
  vm_live_bytes h <= vm_limit h ->
  tpath nstep (ev_step (EMprotect a PGSZ PROT_RW) s) mo [] (Ok (0, s)) (mprotect_model_next mo aw nw).
Proof.
  intros a s mo h aw nw Ha Hal Hce Hmo Hcn Hcm Hlive. pose proof alloc_ceiling_lt as CL.
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
  set (eff := mkEffect (Z_to_bv 64 0) [] [(aw, nw)]).
  assert (Hbud : mprotect_budget_ok mo aw nw = true).
  { apply mprotect_budget_ok_intro; [exact Hmo | exact Hlive]. }
  assert (Hst : nstep (NMprotect a PGSZ PROT_RW) mo eff (mprotect_model_next mo aw nw) []).
  { apply (proj2 (nstep_mprotect_inv a PGSZ PROT_RW mo eff (mprotect_model_next mo aw nw) []
              ltac:(reflexivity) ltac:(fold aw; rewrite Ua, page_size_eq; exact Hal) ltac:(reflexivity)
              ltac:(fold aw; rewrite Ua; change (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ))) with PGSZ; unfold two_pow_64, PGSZ in *; lia)
              ltac:(reflexivity)
              ltac:(fold aw; change (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ)))) with nw; exact Hcn)
              ltac:(fold aw; change (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ)))) with nw; exact Hcm))).
    split; [reflexivity|]. right. fold aw. change (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ)))) with nw.
    split; [exact Hbud|]. split; reflexivity. }
  assert (Hdec : dec_mprotect_rw a PGSZ eff = Some (RgDone true)).
  { unfold dec_mprotect_rw, dec_mprotect, eff. cbn [eff_copies eff_copyins].
    change (bv_unsigned (Z_to_bv 64 0) =? 0) with true. fold aw. change (Z_to_bv 64 (mmap_len PGSZ)) with nw.
    rewrite !bv_eqb_refl. reflexivity. }
  unfold ev_step.
  eapply (tpath_mbind _ _ s mo (RgDone true) s); [eapply tpath_msys; [exact Hst | exact Hdec] | apply tpath_mret].
Qed.

Lemma KREL0 : forall mo, KREL s0 [] mo -> exists L, MI_Contracts.SIMREL (ps_m s0) L /\ KL L 0 mo.
Proof. intros mo [(L & Hc & HK & _) _]. exists L. split; [exact Hc | exact HK]. Qed.

Lemma ctree_ok_vis {R} L e (k : Z -> stree ev Z R) Post :
  ctree_ok L (SVis e k) Post -> event_pre L e /\ forall z, answer_ok L e z = true -> ctree_ok (event_post L e z) (k z) Post.
Proof. intros H. exact H. Qed.

Lemma ctree_ok_bad {R S} L (b : Malloc.M R) (f : R -> Malloc.M S) Post : ctree_ok L (sbind (bad_answer b) f) Post -> False.
Proof. rewrite sbind_bad. cbn. tauto. Qed.

Section BRK.
Variables (mo : Model) (L : mled).
Hypothesis Hc : MI_Contracts.SIMREL (ps_m s0) L.
Hypothesis HK : KL L 0 mo.
Hypothesis Hmo : mo_ok mo.

Let b := vm_brk (m_vmmaps mo).
Let b0 := bv_unsigned b.
Let s1 := set_brk_ps b0 s0.
Let mo1 := with_brk_next mo (Z_to_bv 64 0) b.
Let L1 := set_brkph (BPQueried b0) L.
Let mo2 := with_brk_next mo1 (Z_to_bv 64 (nb b0)) (vm_brk (m_vmmaps mo1)).
Let L2 := set_brkph BPDead L1.
Let Post := fun (L' : mled) (r : mstate * option cptr) => match snd r with Some c => ~ In c (ld_live L') | None => True end.
Let s2 := set_brk_ps (nb b0) s1.
Let mo2g := with_brk_next mo1 (Z_to_bv 64 (nb b0)) (Z_to_bv 64 (nb b0)).

Lemma brk_steps : brk_grow_ok mo1 (Z_to_bv 64 (nb b0)) (Z_to_bv 64 (nb b0)) = false ->
  tpath nstep (ev_step (EBrk 0) s0) mo [] (Ok (b0, s1)) mo1
  /\ tpath nstep (ev_step (EBrk (nb b0)) s1) mo1 [] (Ok (b0, s1)) mo2
  /\ brk0_answer_ok b0 = true /\ nb b0 = b0 + 2 * PGSZ /\ 0 < b0 /\ b0 + 4 * PGSZ <= alloc_ceiling
  /\ KL L2 b0 mo2 /\ mo_ok mo1 /\ mo_ok mo2 /\ msteps 2 (2 * 12288) mo mo2
  /\ ctree_ok L2 (sbind K3T FIN) Post.
Proof.
  intros Hng.
  pose proof (MI_Contracts.cmalloc_contract_sim _ _ BUF0 Hc ltac:(unfold BUF0; lia)) as CT.
  rewrite cmalloc_TA in CT. unfold TA in CT. rewrite sbind_vis in CT. apply ctree_ok_vis in CT as [Hpre1 CT1].
  pose proof (ev_brk0_path s0 mo) as E1. cbv zeta in E1. fold b b0 s1 mo1 in E1.
  destruct (kev_measure L (EBrk 0) s0 mo b0 s1 mo1 Hpre1 HK Hmo E1) as (Hok1 & HK1 & _ & _ & _ & Hmo1 & Hva1 & M1).
  cbn [answer_ok Z.eqb] in Hok1. cbn [event_post Z.eqb ps_brk s1 set_brk_ps] in HK1. fold L1 in HK1.
  pose proof (kl_phase _ _ _ HK1) as PH. cbn [ld_brk L1 set_brkph] in PH. destruct PH as (Eb0 & Ebrk1 & _ & _).
  pose proof (kl_start _ _ _ HK1) as (S1 & S2 & S3 & S4). rewrite <- Eb0 in S1, S2, S4.
  assert (Enb : nb b0 = b0 + 2 * PGSZ) by (unfold nb; rewrite round_up_pg_aligned by (unfold PGSZ in S2; exact S2); reflexivity).
  pose proof alloc_ceiling_lt as CL.
  specialize (CT1 b0 Hok1). cbn [event_post Z.eqb] in CT1. fold L1 in CT1.
  unfold K1 in CT1. rewrite Hok1 in CT1. cbn [negb] in CT1. rewrite sbind_vis in CT1. apply ctree_ok_vis in CT1 as [Hpre2 CT2].
  assert (Honly : forall r, brk_r_ok mo1 (Z_to_bv 64 (nb b0)) r = true -> r = vm_brk (m_vmmaps mo1)).
  { apply brk_only_old; [rewrite w_is0_lit by (unfold PGSZ in *; lia); apply Z.eqb_neq; unfold PGSZ in *; lia
                         | unfold min_brk; rewrite unsigned_lit by (unfold PGSZ in *; lia); lia
                         | rewrite unsigned_lit by (unfold PGSZ in *; lia); lia | exact Hng]. }
  pose proof (ev_brk_refuse_path (nb b0) s1 mo1 ltac:(unfold PGSZ in *; lia) ltac:(cbn [ps_brk s1 set_brk_ps]; symmetry; exact Ebrk1) Honly) as E2.
  cbv zeta in E2. cbn [ps_brk s1 set_brk_ps] in E2. fold mo2 in E2.
  destruct (kev_measure L1 (EBrk (nb b0)) s1 mo1 b0 s1 mo2 Hpre2 HK1 Hmo1 E2) as (Hok2 & HK2 & _ & _ & _ & Hmo2 & Hva2 & M2).
  assert (Enz : (nb b0 =? 0) = false) by (apply Z.eqb_neq; unfold PGSZ in *; lia).
  assert (Ene : (b0 =? nb b0) = false) by (apply Z.eqb_neq; unfold PGSZ in *; lia).
  cbn [event_post] in HK2. rewrite Enz, Ene in HK2. cbn [ps_brk s1 set_brk_ps] in HK2. fold L2 in HK2.
  specialize (CT2 b0 Hok2). cbn [event_post] in CT2. rewrite Enz, Ene in CT2. fold L2 in CT2.
  unfold K2 in CT2. replace (brk_answer_ok b0 (nb b0) b0) with true in CT2 by (unfold brk_answer_ok; rewrite Z.eqb_refl, orb_true_r; reflexivity).
  rewrite Ene in CT2. cbn [negb] in CT2.
  split; [exact E1|]. split; [exact E2|]. split; [exact Hok1|]. split; [exact Enb|]. split; [lia|]. split; [exact S4|].
  split; [exact HK2|]. split; [exact Hmo1|]. split; [exact Hmo2|].
  split. { replace (2 * 12288) with ((0 + esize (EBrk 0)) + esize (EBrk (nb b0))) by reflexivity.
           eapply msteps_snoc; [eapply msteps_snoc; [apply msteps_refl | lia | exact M1] | cbn; lia | exact M2]. }
  exact CT2.
Qed.

Lemma succ_grow : room mo 0 -> brk_grow_ok mo1 (Z_to_bv 64 (nb b0)) (Z_to_bv 64 (nb b0)) = true ->
  malloc_can_succeed s0 mo BUF0.
Proof.
  intros Hroom Hg.
  pose proof (MI_Contracts.cmalloc_contract_sim _ _ BUF0 Hc ltac:(unfold BUF0; lia)) as CT.
  rewrite cmalloc_TA in CT. unfold TA in CT. rewrite sbind_vis in CT. apply ctree_ok_vis in CT as [Hpre1 CT1].
  pose proof (ev_brk0_path s0 mo) as E1. cbv zeta in E1. fold b b0 s1 mo1 in E1.
  destruct (kev_measure L (EBrk 0) s0 mo b0 s1 mo1 Hpre1 HK Hmo E1) as (Hok1 & HK1 & _ & _ & _ & Hmo1 & Hva1 & M1).
  cbn [answer_ok Z.eqb] in Hok1. cbn [event_post Z.eqb ps_brk s1 set_brk_ps] in HK1. fold L1 in HK1.
  pose proof (kl_phase _ _ _ HK1) as PH. cbn [ld_brk L1 set_brkph] in PH. destruct PH as (Eb0 & Ebrk1 & _ & _).
  pose proof (kl_start _ _ _ HK1) as (S1 & S2 & S3 & S4). rewrite <- Eb0 in S1, S2, S4.
  assert (Enb : nb b0 = b0 + 2 * PGSZ) by (unfold nb; rewrite round_up_pg_aligned by (unfold PGSZ in S2; exact S2); reflexivity).
  assert (Ea : round_up_pg b0 = b0) by (apply round_up_pg_aligned; unfold PGSZ in S2; exact S2).
  pose proof alloc_ceiling_lt as CL.
  specialize (CT1 b0 Hok1). cbn [event_post Z.eqb] in CT1. fold L1 in CT1.
  unfold K1 in CT1. rewrite Hok1 in CT1. cbn [negb] in CT1. rewrite sbind_vis in CT1. apply ctree_ok_vis in CT1 as [Hpre2 CT2].
  pose proof (ev_brk_grow_path (nb b0) s1 mo1 ltac:(lia) ltac:(lia) ltac:(unfold PGSZ in *; lia)
                ltac:(cbn [ps_brk s1 set_brk_ps]; symmetry; exact Ebrk1) Hg) as E2.
  fold s2 mo2g in E2.
  destruct (kev_measure L1 (EBrk (nb b0)) s1 mo1 (nb b0) s2 mo2g Hpre2 HK1 Hmo1 E2) as (Hok2 & HK2 & _ & _ & _ & Hmo2 & Hva2 & M2).
  assert (Enz : (nb b0 =? 0) = false) by (apply Z.eqb_neq; unfold PGSZ in *; lia).
  specialize (CT2 (nb b0) Hok2).
  cbn [answer_ok] in Hok2. rewrite Enz in Hok2. cbn [ld_brk L1 set_brkph] in Hok2. apply andb_prop in Hok2 as [HBA _].
  cbn [event_post] in HK2, CT2. rewrite Enz, Z.eqb_refl in HK2, CT2. cbn [ld_brk L1 set_brkph ps_brk s2 set_brk_ps] in HK2, CT2.
  unfold K2 in CT2. rewrite HBA, Z.eqb_refl in CT2. cbn [negb] in CT2.
  destruct (brk_pages_ok STIv (round_up_pg b0) (2 * PGSZ)) eqn:BP; cbn [negb] in CT2; [| exfalso; exact (ctree_ok_bad _ _ _ _ CT2)].
  rewrite sbind_vis in CT2. apply ctree_ok_vis in CT2 as [Hpre3 CT3].
  pose proof (kl_phase _ _ _ HK2) as PH2. cbn [ld_brk set_brkph] in PH2.
  destruct PH2 as (Ecur & _ & _ & _ & _ & (e0 & He0 & He0l & He0h) & _ & _).
  assert (Ua : bv_unsigned (Z_to_bv 64 (round_up_pg b0)) = b0) by (rewrite Ea; apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Hrf : region_free (vm_reserved (m_vmmaps mo2g)) (Z_to_bv 64 (round_up_pg b0)) (Z_to_bv 64 PGSZ) = true).
  { apply region_free_above. intros e He. rewrite Ua, Ecur. apply (kl_resv_top _ _ _ HK2). exact He. }
  assert (Hmc : map_contains (vm_maps (m_vmmaps mo2g)) (Z_to_bv 64 (round_up_pg b0)) (Z_to_bv 64 PGSZ) = true).
  { unfold map_contains. apply existsb_exists. exists e0. split; [exact He0|].
    rewrite Ua, (unsigned_lit PGSZ) by (unfold PGSZ; lia). unfold elo, ehi in *.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity. }
  destruct (ev_mmap_fixed_guard_path (round_up_pg b0) s2 mo2g ltac:(rewrite Ea; lia) ltac:(rewrite Ea; unfold PGSZ in *; lia)
              ltac:(rewrite Ea; unfold PGSZ in S2; exact S2) (kl_ceil _ _ _ HK2) Hrf Hmc) as (mo3 & E3).
  destruct (kev_measure _ (EMmap (round_up_pg b0) PGSZ PROT_NONE MAPFX') s2 mo2g (round_up_pg b0) s2 mo3 Hpre3 HK2 Hmo2 E3)
    as (Hok3 & HK3 & _ & _ & _ & Hmo3 & _ & M3).
  specialize (CT3 _ Hok3). unfold K3G in CT3.
  destruct (mmap_fixed_answer_ok (round_up_pg b0) (round_up_pg b0)) eqn:FA; cbn [negb] in CT3; [| exfalso; exact (ctree_ok_bad _ _ _ _ CT3)].
  unfold KGV in CT3. rewrite sbind_vis in CT3. apply ctree_ok_vis in CT3 as [Hpre4 CT4].
  pose proof esize_vals as (EV1 & EV2 & EV3 & EV4 & EV5).
  assert (MS3 : msteps 3 (12288 + 12288 + 4096) mo mo3).
  { replace (12288 + 12288 + 4096) with (0 + esize (EBrk 0) + esize (EBrk (nb b0)) + esize (EMmap (round_up_pg b0) PGSZ PROT_NONE MAPFX'))
      by (rewrite EV3, !EV4; reflexivity).
    eapply msteps_snoc; [eapply msteps_snoc; [eapply msteps_snoc; [apply msteps_refl | lia | exact M1] | rewrite EV4; lia | exact M2]
                        | rewrite !EV4; lia | exact M3]. }
  pose proof (room_step mo mo3 0 3 _ Hroom ltac:(lia) MS3 ltac:(lia) ltac:(lia)) as R3.
  destruct (room_grant mo3 (0 + 1) 69632 R3 ltac:(lia) Hmo3 (kl_ceil _ _ _ HK3) ltac:(lia)) as [a' Hga'].
  destruct (ev_mmap_grant_path 69632 PROT_RW s2 mo3 a' ltac:(lia) ltac:(change (page_round_up_Z 69632) with 69632; lia) (or_introl eq_refl)
              Hmo3 (kl_ceil _ _ _ HK3) Hga') as (mo4 & E4 & Hmo4 & _ & _ & _ & _).
  set (a2 := bv_unsigned a') in *.
  assert (Herr2 : is_err a2 = false).
  { pose proof Hga' as (_ & _ & G3' & _). pose proof (kl_ceil _ _ _ HK3) as Hck. unfold ceil_ok in Hck. pose_ceil.
    unfold is_err, TWO64. apply Z.ltb_ge. lia. }
  destruct (kev_measure _ (EMmap 0 69632 PROT_RW MAPF') s2 mo3 a2 s2 mo4 Hpre4 HK3 Hmo3 E4) as (Hok4 & _).
  specialize (CT4 a2 Hok4).
  rewrite KG_eq in CT4. destruct (mmap_answer_ok (LRG1 (round_up_pg b0)) 69632 a2) eqn:C6; cbn [negb] in CT4; [| exfalso; exact (ctree_ok_bad _ _ _ _ CT4)].
  destruct (leaf_res_SRet _ _ (LS_granted (round_up_pg b0) a2)) as [sS ES].
  eexists _, (set_m (strip sS) s2), mo4.
  apply (mpath_raw_malloc BUF0 s0 mo [b0; nb b0; round_up_pg b0; a2] (strip sS) (Some (slot_of sS MMv 0)) s2 mo4).
  rewrite cmalloc_TA. apply (mreal_sbind_FIN TA _ _ _ (sS, Some (MMv, 0))); [| reflexivity].
  unfold TA. cbn [mreal]. exists s1, mo1. split; [exact E1|].
  unfold K1. rewrite Hok1. cbn [negb mreal]. exists s2, mo2g. split; [exact E2|].
  unfold K2. rewrite HBA, Z.eqb_refl, BP. cbn [negb mreal]. exists s2, mo3. split; [exact E3|].
  unfold K3G. rewrite FA. cbn [negb]. unfold KGV. cbn [mreal]. exists s2, mo4. split; [exact E4|].
  rewrite KG_eq, C6, Herr2. cbn [negb]. rewrite ES. cbn. repeat split; reflexivity.
Qed.
End BRK.

Theorem MF3_A : MF3_A_stmt.
Proof.
  intros mo j r s' mo' HK Hmo Hroom Hj Hp.
  destruct (raw_malloc_measure BUF0 s0 [] mo r s' mo' 5 (2 ^ 17) HK Hmo ltac:(unfold BUF0; lia)) as (k' & E' & Hk & HE & MS).
  - intros L zs Hc Hok. exact (siteA_events L zs Hok).
  - exact Hp.
  - eapply room_step; [exact Hroom | exact Hj | exact MS | lia | lia].
Qed.

Lemma noref_sbind_FIN : forall (t : MC) zs, noref (sbind t FIN) zs <-> noref t zs.
Proof.
  induction t as [x | e k IH]; intros zs.
  - cbn [sbind]. destruct (FIN_ret x) as [y ->]. cbn [noref]. tauto.
  - rewrite sbind_vis. destruct zs as [|z zs]; [cbn [noref]; tauto|]. cbn [noref]. rewrite IH. tauto.
Qed.

Lemma follow_sbind_FIN : forall (t : MC) zs y, follow (sbind t FIN) zs = Some y -> exists x, follow t zs = Some x /\ FIN x = SRet y.
Proof.
  induction t as [x | e k IH]; intros zs y H.
  - cbn [sbind] in H. destruct (FIN_ret x) as [y' E]. rewrite E in H. cbn [follow] in H. injection H as <-.
    exists x. split; [reflexivity | exact E].
  - rewrite sbind_vis in H. destruct e; destruct zs as [|z zs]; cbn [follow] in H |- *; try discriminate; apply IH; exact H.
Qed.

Lemma FIN_some : forall st g i y, FIN (st, Some (g, i)) = SRet y -> snd y <> None.
Proof. intros st g i y H. cbn [FIN] in H. injection H as <-. cbn [snd]. discriminate. Qed.

Theorem siteA_must : forall L zs st' p,
  okpath L (cmalloc (ps_m s0) BUF0) zs -> noref (cmalloc (ps_m s0) BUF0) zs ->
  follow (cmalloc (ps_m s0) BUF0) zs = Some (st', p) -> p <> None.
Proof.
  intros L zs st' p Hok Hnr Hf. rewrite cmalloc_TA in Hok, Hnr, Hf. rewrite okpath_sbind_FIN in Hok. rewrite noref_sbind_FIN in Hnr.
  apply follow_sbind_FIN in Hf as (x & Hf & HF).
  unfold TA in Hok, Hnr, Hf. apply okpath_vis in Hok as (b0 & zs1 & -> & _ & Hok). cbn [noref follow] in Hnr, Hf. destruct Hnr as [_ Hnr].
  unfold K1 in Hok, Hnr, Hf. destruct (brk0_answer_ok b0); cbn [negb] in Hok, Hnr, Hf; [| exfalso; exact (okpath_bad _ _ _ Hok)].
  apply okpath_vis in Hok as (r & zs2 & -> & _ & Hok). cbn [noref follow] in Hnr, Hf. destruct Hnr as [_ Hnr].
  unfold K2 in Hok, Hnr, Hf. destruct (brk_answer_ok b0 (nb b0) r); cbn [negb] in Hok, Hnr, Hf; [| exfalso; exact (okpath_bad _ _ _ Hok)].
  destruct (r =? nb b0); cbn [negb] in Hok, Hnr, Hf.
  -
    destruct (brk_pages_ok STIv (round_up_pg b0) (2 * PGSZ)); cbn [negb] in Hok, Hnr, Hf; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    apply okpath_vis in Hok as (rg & zs3 & -> & _ & Hok). cbn [noref follow] in Hnr, Hf. destruct Hnr as [_ Hnr].
    unfold K3G in Hok, Hnr, Hf. destruct (mmap_fixed_answer_ok (round_up_pg b0) rg); cbn [negb] in Hok, Hnr, Hf; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    unfold KGV in Hok, Hnr, Hf. apply okpath_vis in Hok as (a2 & zs4 & -> & _ & Hok). cbn [noref follow] in Hnr, Hf.
    destruct Hnr as [Hn2 _]. specialize (Hn2 eq_refl).
    rewrite KG_eq in Hok, Hf. destruct (mmap_answer_ok (LRG1 (round_up_pg b0)) 69632 a2); cbn [negb] in Hok, Hf; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    rewrite Hn2 in Hf. destruct (leaf_res_SRet _ _ (LS_granted (round_up_pg b0) a2)) as [sS ES]. rewrite ES in Hf. cbn [follow] in Hf.
    injection Hf as <-. exact (FIN_some _ _ _ _ HF).
  -
    unfold K3T in Hok, Hnr, Hf. apply okpath_vis in Hok as (a1 & zs3 & -> & _ & Hok). cbn [noref follow] in Hnr, Hf.
    destruct Hnr as [Hn1 Hnr]. specialize (Hn1 eq_refl).
    unfold K4 in Hok, Hnr, Hf. destruct (mmap_answer_ok LRDv 8192 a1); cbn [negb] in Hok, Hnr, Hf; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    rewrite Hn1 in Hok, Hnr, Hf.
    apply okpath_vis in Hok as (m & zs4 & -> & _ & Hok). cbn [noref follow] in Hnr, Hf. destruct Hnr as [-> Hnr].
    unfold K5 in Hok, Hnr, Hf. change (mprotect_answer_ok 0) with true in Hok, Hnr, Hf.
    change ((0 =? 0) || (0 =? TWO64 - ENOSYS)) with true in Hok, Hnr, Hf. cbn [negb] in Hok, Hnr, Hf.
    unfold KCV in Hok, Hnr, Hf. apply okpath_vis in Hok as (a2 & zs5 & -> & _ & Hok). cbn [noref follow] in Hnr, Hf.
    destruct Hnr as [Hn2 _]. specialize (Hn2 eq_refl).
    rewrite KG_eq in Hok, Hf. destruct (mmap_answer_ok (LR1v a1) 69632 a2); cbn [negb] in Hok, Hf; [| exfalso; exact (okpath_bad _ _ _ Hok)].
    rewrite Hn2 in Hf. destruct (leaf_res_SRet _ _ (LS_refused a1 a2)) as [sS ES]. rewrite ES in Hf. cbn [follow] in Hf.
    injection Hf as <-. exact (FIN_some _ _ _ _ HF).
Qed.

Theorem MF_A_must : MF_A_must_stmt.
Proof.
  intros mo HK Hmo Hroom r s' mo' Hp.
  destruct (raw_malloc_noref BUF0 s0 [] mo r s' mo' 0 HK Hmo ltac:(unfold BUF0; lia) Hroom ltac:(lia)) with (2 := Hp)
    as (L & zs & st' & p & Hc & Hf & Hok & Hnr & ->).
  { intros L zs Hc Hok. destruct (siteA_events L zs Hok) as [B1 B2]. split; lia. }
  pose proof (siteA_must L zs st' p Hok Hnr Hf) as NN. destruct p; [discriminate | congruence].
Qed.

Lemma is_err_grant : forall mo a nZ, 0 <= nZ -> ceil_ok (m_vmmaps mo) -> grant_ok mo a nZ -> is_err (bv_unsigned a) = false.
Proof.
  intros mo a nZ HnZ Hck Hg. pose proof Hg as (_ & _ & G3 & _). unfold ceil_ok in Hck. pose_ceil.
  unfold is_err, TWO64. apply Z.ltb_ge. lia.
Qed.

Theorem MF_A_succ : MF_A_succ_stmt.
Proof.
  intros mo HKR Hmo Hroom. destruct (KREL0 mo HKR) as (L & Hc & HK).
  destruct (brk_grow_ok (with_brk_next mo (Z_to_bv 64 0) (vm_brk (m_vmmaps mo)))
              (Z_to_bv 64 (nb (bv_unsigned (vm_brk (m_vmmaps mo))))) (Z_to_bv 64 (nb (bv_unsigned (vm_brk (m_vmmaps mo)))))) eqn:Hg.
  { exact (succ_grow mo L Hc HK Hmo Hroom Hg). }
  destruct (brk_steps mo L Hc HK Hmo Hg) as (E1 & E2 & Hb0 & Enb & Hpos & Hce & HK2 & Hmo1 & Hmo2 & MS2 & CT2).
  set (b0 := bv_unsigned (vm_brk (m_vmmaps mo))) in *.
  set (s1 := set_brk_ps b0 s0) in *.
  set (mo1 := with_brk_next mo (Z_to_bv 64 0) (vm_brk (m_vmmaps mo))) in *.
  set (mo2 := with_brk_next mo1 (Z_to_bv 64 (nb b0)) (vm_brk (m_vmmaps mo1))) in *.
  set (L2 := set_brkph BPDead (set_brkph (BPQueried b0) L)) in *.
  assert (Ene : (b0 =? nb b0) = false) by (apply Z.eqb_neq; unfold PGSZ in Enb; lia).
  pose proof alloc_ceiling_lt as CL.

  pose proof (room_step mo mo2 0 2 (2 * 12288) Hroom ltac:(lia) MS2 ltac:(lia) ltac:(lia)) as R2.

  unfold K3T in CT2. rewrite sbind_vis in CT2. apply ctree_ok_vis in CT2 as [Hpre3 CT3].
  destruct (room_grant mo2 (0 + 1) 8192 R2 ltac:(lia) Hmo2 (kl_ceil _ _ _ HK2) ltac:(lia)) as [a Hga].
  destruct (ev_mmap_none_grant_path 8192 s1 mo2 a ltac:(lia) ltac:(change (page_round_up_Z 8192) with 8192; lia) Hmo2 (kl_ceil _ _ _ HK2) Hga) as (mo3 & E3 & Hmo3 & Hva3 & Hvm3).
  change (page_round_up_Z 8192) with 8192 in Hvm3.
  set (a1 := bv_unsigned a) in *.
  pose proof Hga as (G1 & G2 & G3 & _). rewrite page_size_eq in G1. fold a1 in G1, G2, G3.
  pose proof (kl_ceil _ _ _ HK2) as CK2. unfold ceil_ok in CK2. pose_ceil.
  assert (G3' : a1 + 8192 <= alloc_ceiling).
  { apply (ceil_page_le (m_vmmaps mo2)); [exact (kl_ceil _ _ _ HK2) | rewrite page_size_eq, Z.add_mod, G1 by lia; reflexivity | exact G3]. }
  pose proof (is_err_grant mo2 a 8192 ltac:(lia) (kl_ceil _ _ _ HK2) Hga) as Herr1. fold a1 in Herr1.
  destruct (kev_measure L2 (EMmap 0 8192 PROT_NONE MAPF') s1 mo2 a1 s1 mo3 Hpre3 HK2 Hmo2 E3) as (Hok3 & HK3 & _ & _ & _ & _ & _ & M3).
  specialize (CT3 a1 Hok3). set (L3 := event_post L2 (EMmap 0 8192 PROT_NONE MAPF') a1) in *.
  unfold K4 in CT3. destruct (mmap_answer_ok LRDv 8192 a1) eqn:C4; cbn [negb] in CT3; [| exfalso; exact (ctree_ok_bad _ _ _ _ CT3)].
  rewrite Herr1 in CT3. rewrite sbind_vis in CT3. apply ctree_ok_vis in CT3 as [Hpre4 CT4].
  pose proof (msteps_snoc _ _ _ _ _ (EMmap 0 8192 PROT_NONE MAPF') MS2 ltac:(lia) M3) as MS3.
  change (esize (EMmap 0 8192 PROT_NONE MAPF')) with 8192 in MS3.
  pose proof (room_step mo mo3 0 3 _ Hroom ltac:(lia) MS3 ltac:(lia) ltac:(lia)) as R3.

  assert (Hcn : map_contains (vm_noaccess (m_vmmaps mo3)) (Z_to_bv 64 (a1 + PGSZ)) (Z_to_bv 64 PGSZ) = true).
  { rewrite Hvm3. unfold map_contains. cbn [vm_noaccess existsb fst snd]. apply orb_true_iff. left.
    unfold PGSZ. rewrite !unsigned_lit by (pose_ceil; lia). fold a1.
    apply andb_true_iff. split; apply Z.leb_le; lia. }
  assert (Hcm : map_contains (vm_maps (m_vmmaps mo3)) (Z_to_bv 64 (a1 + PGSZ)) (Z_to_bv 64 PGSZ) = true).
  { rewrite Hvm3. unfold map_contains. cbn [vm_maps existsb fst snd]. apply orb_true_iff. left.
    unfold PGSZ. rewrite !unsigned_lit by (pose_ceil; lia). fold a1.
    apply andb_true_iff. split; apply Z.leb_le; lia. }
  assert (Hlive : vm_live_bytes (m_vmmaps mo3) <= vm_limit (m_vmmaps mo3)).
  { destruct R3 as [_ _ RL RM]. lia. }
  pose proof (ev_mprotect_grant_path (a1 + PGSZ) s1 mo3 ltac:(unfold PGSZ; lia)
                ltac:(unfold PGSZ; rewrite Z.add_mod, G1 by lia; reflexivity)
                ltac:(unfold PGSZ in *; lia) Hmo3 Hcn Hcm Hlive) as E4.
  cbv zeta in E4. set (mo4 := mprotect_model_next mo3 (Z_to_bv 64 (a1 + PGSZ)) (Z_to_bv 64 PGSZ)) in *.
  destruct (kev_measure L3 (EMprotect (a1 + PGSZ) PGSZ PROT_RW) s1 mo3 0 s1 mo4 Hpre4 HK3 Hmo3 E4) as (Hok4 & HK4 & _ & _ & _ & Hmo4 & _ & M4).
  specialize (CT4 0 Hok4). set (L4 := event_post L3 (EMprotect (a1 + PGSZ) PGSZ PROT_RW) 0) in *.
  unfold K5 in CT4. change (mprotect_answer_ok 0) with true in CT4. change ((0 =? 0) || (0 =? TWO64 - ENOSYS)) with true in CT4.
  cbn [negb] in CT4. unfold KCV in CT4. rewrite sbind_vis in CT4. apply ctree_ok_vis in CT4 as [Hpre5 CT5].
  pose proof (msteps_snoc _ _ _ _ _ (EMprotect (a1 + PGSZ) PGSZ PROT_RW) MS3 ltac:(lia) M4) as MS4.
  change (esize (EMprotect (a1 + PGSZ) PGSZ PROT_RW)) with 0 in MS4.
  pose proof (room_step mo mo4 0 4 _ Hroom ltac:(lia) MS4 ltac:(lia) ltac:(lia)) as R4.

  destruct (room_grant mo4 (0 + 1) 69632 R4 ltac:(lia) Hmo4 (kl_ceil _ _ _ HK4) ltac:(lia)) as [a' Hga'].
  destruct (ev_mmap_grant_path 69632 PROT_RW s1 mo4 a' ltac:(lia) ltac:(change (page_round_up_Z 69632) with 69632; lia) (or_introl eq_refl) Hmo4 (kl_ceil _ _ _ HK4) Hga') as (mo5 & E5 & Hmo5 & _ & _ & _ & _).
  set (a2 := bv_unsigned a') in *.
  pose proof (is_err_grant mo4 a' 69632 ltac:(lia) (kl_ceil _ _ _ HK4) Hga') as Herr2. fold a2 in Herr2.
  destruct (kev_measure L4 (EMmap 0 69632 PROT_RW MAPF') s1 mo4 a2 s1 mo5 Hpre5 HK4 Hmo4 E5) as (Hok5 & _).
  specialize (CT5 a2 Hok5).
  rewrite KG_eq in CT5. destruct (mmap_answer_ok (LR1v a1) 69632 a2) eqn:C6; cbn [negb] in CT5; [| exfalso; exact (ctree_ok_bad _ _ _ _ CT5)].
  destruct (leaf_res_SRet _ _ (LS_refused a1 a2)) as [sS ES].

  eexists _, (set_m (strip sS) s1), mo5.
  apply (mpath_raw_malloc BUF0 s0 mo [b0; b0; a1; 0; a2] (strip sS) (Some (slot_of sS MMv 0)) s1 mo5).
  rewrite cmalloc_TA. apply (mreal_sbind_FIN TA _ _ _ (sS, Some (MMv, 0))); [| reflexivity].
  unfold TA. cbn [mreal]. exists s1, mo1. split; [exact E1|].
  unfold K1. rewrite Hb0. cbn [negb mreal]. exists s1, mo2. split; [exact E2|].
  unfold K2. replace (brk_answer_ok b0 (nb b0) b0) with true by (unfold brk_answer_ok; rewrite Z.eqb_refl, orb_true_r; reflexivity).
  rewrite Ene. cbn [negb]. unfold K3T. cbn [mreal]. exists s1, mo3. split; [exact E3|].
  unfold K4. rewrite C4, Herr1. cbn [negb mreal]. exists s1, mo4. split; [exact E4|].
  unfold K5. change (mprotect_answer_ok 0) with true. change ((0 =? 0) || (0 =? TWO64 - ENOSYS)) with true. cbn [negb].
  unfold KCV. cbn [mreal]. exists s1, mo5. split; [exact E5|].
  rewrite KG_eq, C6, Herr2. cbn [negb]. rewrite ES. cbn. repeat split; reflexivity.
Qed.

Lemma LS_fg : forall st1 a2,
  (forall sc, active st1 sc = None) -> s_metas st1 !! MMv = Some meta0 ->
  LS st1 a2 = SRet (MF_Evol.fg_final st1 MMv a2, Some (MMv, 0)).
Proof.
  intros st1 a2 HA HM.
  change (LS st1 a2) with (ag_tail lay_none (MF_Evol.fg_st4 st1 MMv a2) 44 MMv (s_next_rid st1, 0) 1 0
     (fun st2 go => match go with
                    | None => KM st2 (-1)
                    | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                                queue (LActive 44) g st3 (fun st4 => KM st4 0) BL
                    end)).
  rewrite (MF_Evol.first_group_leaf st1 MMv a2 HA HM KM BL).
  unfold KM. change (0 <? 0) with false. cbv iota.
  unfold MF_Evol.fg_final. rewrite MF_SiteC.fin_active, Z.eqb_refl. reflexivity.
Qed.

Lemma PHI_strip : forall st, MF_Phi.PHI st -> MF_Phi.PHI (strip st).
Proof. intros st H. exact H. Qed.

Lemma ST1v_facts : forall a1, let st1 := ST1v a1 in
  c_init_done (s_ctx st1) = 1 /\ 50 <= c_avail_meta_count (s_ctx st1) /\ c_free_meta_head (s_ctx st1) = None
  /\ (forall sc, active st1 sc = None) /\ s_groups st1 = ∅ /\ s_metas st1 !! MMv = Some meta0.
Proof.
  intros a1. cbv zeta. split; [reflexivity|]. split; [vm_compute; discriminate|]. split; [reflexivity|].
  split; [intros sc; reflexivity|]. split; [reflexivity|]. vm_compute. reflexivity.
Qed.
Lemma STG1v_facts : forall b, let st1 := STG1v b in
  c_init_done (s_ctx st1) = 1 /\ 50 <= c_avail_meta_count (s_ctx st1) /\ c_free_meta_head (s_ctx st1) = None
  /\ (forall sc, active st1 sc = None) /\ s_groups st1 = ∅ /\ s_metas st1 !! MMv = Some meta0.
Proof.
  intros b. cbv zeta. split; [reflexivity|]. split; [vm_compute; discriminate|]. split; [reflexivity|].
  split; [intros sc; reflexivity|]. split; [reflexivity|]. vm_compute. reflexivity.
Qed.

Local Ltac bad CP := rewrite sbind_bad in CP; exact (False_ind _ (MF_EvolA.cpath_undef_inv _ _ _ _ _ CP)).
Local Ltac leafN CP E := rewrite E, sbind_ret_l in CP; cbn [FIN] in CP; apply MF_EvolA.cpath_ret_inv in CP as [_ CP]; discriminate.

Theorem T2_A : forall L L1 cs1 c,
  MI_Contracts.SIMREL (ps_m s0) L -> cpath L (cmalloc (ps_m s0) BUF0) L1 (cs1, Some c) -> MF_Phi.PHI cs1.
Proof.
  intros L L1 cs1 c Hc CP. rewrite cmalloc_TA in CP. unfold TA in CP.
  rewrite sbind_vis in CP. apply MF_EvolA.cpath_vis_inv in CP as (b0 & _ & CP). unfold K1 in CP.
  destruct (brk0_answer_ok b0); cbn [negb] in CP; [| bad CP].
  rewrite sbind_vis in CP. apply MF_EvolA.cpath_vis_inv in CP as (r & _ & CP). unfold K2 in CP.
  destruct (brk_answer_ok b0 (nb b0) r); cbn [negb] in CP; [| bad CP].
  destruct (r =? nb b0); cbn [negb] in CP.
  -
    destruct (brk_pages_ok STIv (round_up_pg b0) (2 * PGSZ)); cbn [negb] in CP; [| bad CP].
    rewrite sbind_vis in CP. apply MF_EvolA.cpath_vis_inv in CP as (rg & _ & CP). unfold K3G in CP.
    destruct (mmap_fixed_answer_ok (round_up_pg b0) rg); cbn [negb] in CP; [| bad CP].
    unfold KGV in CP. rewrite sbind_vis in CP. apply MF_EvolA.cpath_vis_inv in CP as (a2 & _ & CP). rewrite KG_eq in CP.
    destruct (mmap_answer_ok (LRG1 (round_up_pg b0)) 69632 a2); cbn [negb] in CP; [| bad CP].
    destruct (STG1v_facts (round_up_pg b0)) as (HI & HC & HF & HA & HG & HM).
    destruct (is_err a2).
    + destruct (leaf_res_SRet _ _ (LF_granted (round_up_pg b0))) as [s E]. leafN CP E.
    + rewrite (LS_fg _ a2 HA HM), sbind_ret_l in CP. cbn [FIN] in CP. apply MF_EvolA.cpath_ret_inv in CP as [_ CP].
      injection CP as E1 E2. rewrite E1. apply PHI_strip. apply MF_Evol.PHI_first_group; assumption.
  -
    unfold K3T in CP. rewrite sbind_vis in CP. apply MF_EvolA.cpath_vis_inv in CP as (a1 & _ & CP). unfold K4 in CP.
    destruct (mmap_answer_ok LRDv 8192 a1); cbn [negb] in CP; [| bad CP].
    destruct (is_err a1).
    { rewrite sbind_ret_l in CP. cbn [FIN] in CP. apply MF_EvolA.cpath_ret_inv in CP as [_ CP]. discriminate. }
    rewrite sbind_vis in CP. apply MF_EvolA.cpath_vis_inv in CP as (m & _ & CP). unfold K5 in CP.
    destruct (mprotect_answer_ok m); cbn [negb] in CP; [| bad CP].
    destruct ((m =? 0) || (m =? TWO64 - ENOSYS)).
    2:{ rewrite sbind_ret_l in CP. cbn [FIN] in CP. apply MF_EvolA.cpath_ret_inv in CP as [_ CP]. discriminate. }
    unfold KCV in CP. rewrite sbind_vis in CP. apply MF_EvolA.cpath_vis_inv in CP as (a2 & _ & CP). rewrite KG_eq in CP.
    destruct (mmap_answer_ok (LR1v a1) 69632 a2); cbn [negb] in CP; [| bad CP].
    destruct (ST1v_facts a1) as (HI & HC & HF & HA & HG & HM).
    destruct (is_err a2).
    + destruct (leaf_res_SRet _ _ (LF_refused a1)) as [s E]. leafN CP E.
    + rewrite (LS_fg _ a2 HA HM), sbind_ret_l in CP. cbn [FIN] in CP. apply MF_EvolA.cpath_ret_inv in CP as [_ CP].
      injection CP as E1 E2. rewrite E1. apply PHI_strip. apply MF_Evol.PHI_first_group; assumption.
Qed.

End CEIL.

Ltac krefl := lazymatch goal with |- ?l = _ => exact_no_check (@eq_refl _ l) end.
Local Ltac bad CP := rewrite sbind_bad in CP; exact (False_ind _ (MF_EvolA.cpath_undef_inv _ _ _ _ _ CP)).
Local Ltac leafN CP E := rewrite E, sbind_ret_l in CP; cbn [FIN] in CP; apply MF_EvolA.cpath_ret_inv in CP as [_ CP]; discriminate.
End TwinB.
