(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the run instance [KHr] the ASan+UBSan library is closed
   at (the ASan+UBSan copy of As/AsSRRun.v, over this binary's [asegs] and [KHp]).
   [AS_InstDefs.KHp] reaches its targets over the binary's own segments ([as_SR (KHp p)] is
   [AsSR.SR] = [sreach asegs]); a run that calls time() executes in the vDSO pair, so the
   library that calls it is instantiated at [KHr]: the reach is over the run's list
   [asegs ++ tail] from the state with that list's read-only backing (as Ref/HeapSRRun.v's
   [sr_run]); the kernel relation adds [vcm2 vlo vb vhi], [PairCleanAll.vcm_cfg] of each of the
   pair's two reserved entries, the vvar pages [vlo, vb) and the text [vb, vhi) (the overlay holds
   no byte of the entry, the entry is one of the launch's reserved pair, and no map meets it; one
   invariant per entry, as Ref/HeapSRRun.v's [pair_inv]), and [pw_ok vb] of the state: the shadow
   byte [sh vb] of the text's first bytes (the marker) is visible, the 32 shadow bytes
   [sh vb + 72, sh vb + 104) that cover the text's string table, which time()'s first call reads
   (the window), are hidden, and 4096 bytes of the allocator's budget, from which time() opens the
   window, are held back: [as_AL] is the state's budget less those 4096.  Every other field is
   [KHp p]'s.
     - [khr_SR_laws]: the straight-line law is [KHp]'s lazy one ([AS_InstLaws1.inst_SR_laws],
       i.e. [AsSR.ASR_lift_at]) run from the state with the run's backing, [vcm2] carried through
       the reach by [PairCleanAll.sreach_keep_vcm] once per entry (no segment of the binary meets
       either: [as_nw_win_at]), the reach lifted by [RunTail.sreach_app_tail]; the continuation
       is entered at the state with the caller's backing; the state, so [pw_ok], is the caller's.
     - [khr_rt_hyps_x]: [AsIfaceX.asan_rt_hyps_x] of [KHr] from that of [KHp p].  malloc, free,
       free(NULL) and realloc are the theorems at [AS_InstX.KHX p XR] ([XR]: [vcm2] and the
       marker and window of [pw_ok], [pw_core]), lifted by [RunTail.sreach_lift_tail] with [vcm2]
       carried ([lift_p]).  [xkeep_r] is why a heap call keeps [XR]: it changes the writable view
       only inside its write set [AG_WriteSet.awrit], which holds neither the marker nor the
       window ([pw_not_awrit]: they are high-shadow bytes, where no object of the allocator lies,
       and the application bytes they cover are text bytes, which no map holds), so the marker
       keeps its byte and stays visible and the window keeps having none and stays hidden
       ([AllocRepX.awin_vis]: every visible byte has one; [AllocRepX.akernel]: both are lazily
       reserved, so a hidden byte has none); [pw_ok]'s budget conjunct is the call's budget
       bound.  Every other conjunct is [KHp p]'s, by conversion.  [khr_memalign_stmt] is
       posix_memalign ([AInstFacts.ainst_facts]' second conjunct) the same way.
     - [khr_driver_laws]: the run's driver-law record [AsDriverLaws.asan_driver_laws_run] (the walk
       over the run's list, [vcm2] in the kernel relation, the pair above the image with the vvar
       entry first) for [KHr], from [AS_InstLaws1.inst_driver_laws].
   [vcm2], the record and the facts that no segment of the binary reaches the image's top or is
   the vDSO text ([asegs_find_none], [vdso_image_asegs]) are Both/As/AsDriverLaws.v's.
   The time call's statement is not proved here. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil Scfg SReach ShapeAlg LazyRestrict LazySR.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require AsanAllocModel VdsoClean.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Exec MState TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomBase RunTail.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require PairCleanAll.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsIface AsIfaceX AsIfaceMemalign AsDriverLaws
  AllocRep AllocRepX AsDepotInv AG_WriteSet AS_InstDefs AS_InstX AS_InstLaws1.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As Require AG_Malloc2 AS_InstHeap AS_InstFree AS_InstRealloc AS_InstMemalign.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** * Windows above the binary's image (no segment of the binary there: [asegs_find_none]) *)

(* no segment of the binary holds a byte of a window above its image ([PairCleanAll]'s [Hnw]) *)
Lemma as_nw_win_at : forall wlo whi : Z, AIMG_TOP <= wlo -> forall (x : word) s,
  wlo <= bv_unsigned x < whi -> find_segment asegs (bv_unsigned x) 1 = Some s -> seg_writable s = false.
Proof. intros wlo whi HT x s Hx Hf. rewrite (asegs_find_none (bv_unsigned x)) in Hf by lia. discriminate Hf. Qed.

(* [vcm_cfg] of a window above the image is carried through every reach over [asegs] *)
Lemma keep_vcm_w : forall wlo whi : Z, AIMG_TOP <= wlo -> forall (Q : config -> Prop) c,
  sreach asegs Q c -> PairCleanAll.vcm_cfg wlo whi c ->
  sreach asegs (fun c' => Q c' /\ PairCleanAll.vcm_cfg wlo whi c') c.
Proof.
  intros wlo whi HT Q c S V.
  eapply PairCleanAll.sreach_keep_vcm; first [exact S | exact V | exact (as_nw_win_at wlo whi HT)].
Qed.

(* the writable view of a byte above the image is the overlay's *)
Lemma wview_noseg : forall (mm : mem) (a : word), AIMG_TOP <= bv_unsigned a -> wview asegs mm a = mm a.
Proof.
  intros mm a Ha. unfold wview. destruct (mm a) as [b|]; [reflexivity|].
  rewrite (asegs_find_none (bv_unsigned a) Ha). reflexivity.
Qed.

(* a byte of a window that no map meets is in no map *)
Lemma maps_off_in : forall (wlo whi : Z) (l : list (word * word)) (x : word),
  Forall (VdsoClean.range_off wlo whi) l -> wlo <= bv_unsigned x < whi -> in_rangesb x l = false.
Proof.
  intros wlo whi l x HF Hx. apply (proj2 (in_rangesb_false x l)). intros lo sz Hin Hr.
  rewrite Forall_forall in HF. specialize (HF (lo, sz) Hin). unfold VdsoClean.range_off in HF. cbn [fst snd] in HF. lia.
Qed.

Lemma in_maps_off : forall (wlo whi : Z) (l : list (word * word)) (a n : word) (z : Z),
  Forall (VdsoClean.range_off wlo whi) l -> In (a, n) l ->
  bv_unsigned a <= z < bv_unsigned a + bv_unsigned n -> wlo <= z < whi -> False.
Proof.
  intros wlo whi l a n z HF Hin Hz Hw. rewrite Forall_forall in HF. specialize (HF (a, n) Hin).
  unfold VdsoClean.range_off in HF. cbn [fst snd] in HF. lia.
Qed.

(** * The marker and the window (the pair's two entries: [AsDriverLaws.vcm2]) *)

(* the window: the 32 shadow bytes of the text's bytes [vb + 576, vb + 832), which hold the string
   table [vb + 624, vb + 805) time()'s first call reads ([AsStrcmp.astrcmp_shz]) *)
Definition pw_win (vb : Z) : word * word := (Z_to_bv 64 (sh vb + 72), Z_to_bv 64 32).
(* the marker: the shadow byte of the text's first 8 bytes, on the window's page *)
Definition pw_mark (vb : Z) : word * word := (Z_to_bv 64 (sh vb), Z_to_bv 64 1).

(* the last of the 8 application bytes a shadow byte [q] covers *)
Definition pw_app (q : Z) : Z := 8 * (q - ASHADOW_BASE) + 7.

Section PwOk.
  Context {HCEIL : HeapCeil}.

  (* the marker visible, the window hidden, 4096 bytes of budget held back *)
  Definition pw_ok (vb : Z) (x : ist) : Prop :=
       in_rangesb (Z_to_bv 64 (sh vb)) (a_S (i_s x)) = true
    /\ (forall y : word, sh vb + 72 <= bv_unsigned y < sh vb + 104 -> in_rangesb y (a_S (i_s x)) = false)
    /\ 4096 <= a_AL (i_s x).
End PwOk.

Section RunAs.
  Context {HCEIL : HeapCeil}.
  Variable p : iparams.
  Variable tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  (* the pair: the vvar entry [vlo, vb) and the text entry [vb, vhi) *)
  Variables vlo vb vhi : Z.
  (* the pair lies above the binary's image *)
  Hypothesis Hvtop : AIMG_TOP <= vlo.
  Hypothesis Hvord : vlo <= vb.
  (* the text base is 8-aligned, in the application's high range, and the bytes [vb, vb + 832)
     the marker and the window cover are below the heap ceiling and inside the text entry *)
  Hypothesis Hvb : vb mod 8 = 0 /\ AHI_LO <= vb /\ vb + 832 <= aceil /\ vb + 832 <= vhi.
  (* the bound on the binary's trace list that the heap calls' theorems take *)
  Hypothesis TRLEN : (length (ip_TR p) <= 4000)%nat.

  Local Notation rV := (OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.seg_rom (asegs ++ tail)) (only parsing).
  Local Notation VC2 := (vcm2 vlo vb vhi) (only parsing).

  (** reaching [Q] over the run's list, from the state with the run's backing *)
  Definition sr_run (Q : config -> Prop) (c : config) : Prop :=
    sreach (asegs ++ tail) (fun c' => exists c0, c' = cwrom c0 rV /\ Q c0) (cwrom c rV).

  Definition KHr : asr :=
    {| as_St := as_St (KHp p);
       as_SR := sr_run;
       as_VIS := as_VIS (KHp p);
       as_AKREL := fun s c => as_AKREL (KHp p) s c /\ vcm2 vlo vb vhi c /\ pw_ok vb s;
       as_MPRES := as_MPRES (KHp p);
       as_RHEAP := as_RHEAP (KHp p);
       as_RFS := as_RFS (KHp p);
       as_rauxv_ok := as_rauxv_ok (KHp p);
       as_lb_remove := as_lb_remove (KHp p);
       as_alloc_ok := as_alloc_ok (KHp p);
       as_LIVE_MAX := as_LIVE_MAX (KHp p); as_LIVE_CNT_MAX := as_LIVE_CNT_MAX (KHp p);
       as_AL := fun x : ist => a_AL (i_s x) - 4096;
       as_Cm := as_Cm (KHp p); as_Cf := as_Cf (KHp p);
       as_chain := as_chain (KHp p);
       as_TR := as_TR (KHp p);
       as_FSB := as_FSB (KHp p) |}.

  (** * The pair and the binary's segments *)

  Lemma vbtop : AIMG_TOP <= vb.
  Proof. pose proof Hvtop. pose proof Hvord. lia. Qed.

  (* both entries' invariants are carried through every reach over [asegs] *)
  Lemma keep_vcm2 : forall (Q : config -> Prop) c, sreach asegs Q c -> VC2 c ->
    sreach asegs (fun c' => Q c' /\ VC2 c') c.
  Proof.
    intros Q c S [V1 V2].
    pose proof (keep_vcm_w vlo vb Hvtop Q c S V1) as S1.
    pose proof (keep_vcm_w vb vhi vbtop _ c S1 V2) as S2.
    apply (sreach_mono asegs _ _ c S2). intros c' [[HQ W1] W2]. split; [exact HQ | split; [exact W1 | exact W2]].
  Qed.

  (** * The view, the kernel relation and the read-only backing *)

  Lemma sr_p_sreach : forall (Q : config -> Prop) c, as_SR (KHp p) Q c -> sreach asegs Q c.
  Proof. intros Q c S. exact S. Qed.

  Lemma vis_rom_p : forall (s : as_St (KHp p)) msF, ms_rom (as_VIS (KHp p) s msF) = ms_rom msF.
  Proof. intros s msF. destruct msF; reflexivity. Qed.

  Lemma vis_rom_eq : forall (s : as_St KHr) msF ms, as_VIS KHr s msF = ms -> ms_rom msF = ms_rom ms.
  Proof. intros s msF ms <-. destruct msF; reflexivity. Qed.

  Lemma vis_wrom_p : forall (s : as_St (KHp p)) msF r,
    as_VIS (KHp p) s (wrom msF r) = wrom (as_VIS (KHp p) s msF) r.
  Proof. intros s msF r. destruct msF; reflexivity. Qed.

  (* [lzok] and [IK] read no byte of the read-only backing *)
  Lemma akrel_wrom : forall (s : as_St (KHp p)) msF mo r,
    as_AKREL (KHp p) s (mkCfg msF mo) -> as_AKREL (KHp p) s (mkCfg (wrom msF r) mo).
  Proof.
    intros s msF mo r [[HL Hinv Hh HZ HSZ HZL HLM] K].
    split; [constructor | exact K].
    - exact HL.
    - exact Hinv.
    - exact Hh.
    - exact HZ.
    - exact HSZ.
    - exact HZL.
    - exact HLM.
  Qed.

  (* [vcm_cfg] reads the overlay and the model, not the read-only backing *)
  Lemma vcm2_wrom : forall msF mo r, VC2 (mkCfg msF mo) -> VC2 (mkCfg (wrom msF r) mo).
  Proof. intros msF mo r V. exact V. Qed.

  (** * [SR_laws] *)

  Lemma srr_done : forall (Q : config -> Prop) c, Q c -> sr_run Q c.
  Proof. intros Q c HQ. unfold sr_run. apply sr_done. exists c. split; [reflexivity | exact HQ]. Qed.

  Lemma srr_mono : forall (Q Q' : config -> Prop) c, sr_run Q c -> (forall c', Q c' -> Q' c') -> sr_run Q' c.
  Proof.
    intros Q Q' c HQ Himp. unfold sr_run in *. eapply sreach_mono; [exact HQ|].
    intros c' (c0 & -> & H0). exists c0. split; [reflexivity | exact (Himp c0 H0)].
  Qed.

  Lemma srr_seq : forall (Q1 Q2 : config -> Prop) c,
    sr_run Q1 c -> (forall c', Q1 c' -> sr_run Q2 c') -> sr_run Q2 c.
  Proof.
    intros Q1 Q2 c H1 H2. unfold sr_run in *. eapply sreach_seq; [exact H1|].
    intros c' (c0 & -> & H0). exact (H2 c0 H0).
  Qed.

  (* [KHp]'s lazy straight-line law from the state with the run's backing [rV]: the walk the
     premise gives is one from that state ([RunTail.exec_msteps_wrom]); [vcm2] is carried
     through the reach over [asegs], which is lifted to the run's list; at its end the state
     with the caller's backing [ms_rom y] is the continuation's, and its walk is from the reach's
     end, whose backing is [rV]; the state is the caller's, so [pw_ok] is its. *)
  Lemma srr_evt : forall (P : machine_state -> Prop) (Q : config -> Prop) (s : as_St KHr) msF ms mo,
    as_AKREL KHr s (mkCfg msF mo) -> as_VIS KHr s msF = ms -> Exec.evt asegs P ms ->
    (forall msF' mo', as_AKREL KHr s (mkCfg msF' mo') -> as_MPRES KHr mo mo' -> P (as_VIS KHr s msF') ->
                      as_SR KHr Q (mkCfg msF' mo')) ->
    as_SR KHr Q (mkCfg msF mo).
  Proof.
    intros P Q s msF ms mo [HA [HV PW]] HVIS HE HK. subst ms.
    destruct (inst_SR_laws p) as (D0 & _ & _ & EV).
    assert (S1 : as_SR (KHp p)
                   (fun c' => as_AKREL (KHp p) s c' /\ as_MPRES (KHp p) mo (cfg_model c')
                              /\ (exists y, as_VIS (KHp p) s (cfg_ms c') = wrom y rV /\ P y))
                   (mkCfg (wrom msF rV) mo)).
    { apply (EV (fun x => exists y, x = wrom y rV /\ P y) _ s (wrom msF rV) (wrom (as_VIS (KHp p) s msF) rV) mo).
      - exact (akrel_wrom s msF mo rV HA).
      - exact (vis_wrom_p s msF rV).
      - destruct HE as (ms1 & Hms & HP). exists (wrom ms1 rV). split.
        + exact (exec_msteps_wrom asegs _ ms1 rV Hms).
        + exists ms1. split; [reflexivity | exact HP].
      - intros msF' mo' HA' HM HP'. apply D0.
        split; [exact HA'|]. split; [exact HM | exact HP']. }
    pose proof (keep_vcm2 _ _ (sr_p_sreach _ _ S1) (vcm2_wrom msF mo rV HV)) as S2.
    change (sr_run Q (mkCfg msF mo)). unfold sr_run.
    change (cwrom (mkCfg msF mo) rV) with (mkCfg (wrom msF rV) mo).
    eapply sreach_seq.
    { first [ exact (sreach_app_tail asegs tail Hnx Hnw vdso_image_asegs _ _ S2)
            | eapply sreach_app_tail; first [exact S2 | exact Hnx | exact Hnw | exact vdso_image_asegs] ]. }
    intros [msF' mo'] ((HA' & HM & y & Ey & Py) & V').
    cbn [cfg_ms cfg_model] in HM, Ey.
    assert (Er : ms_rom msF' = rV).
    { rewrite <- (vis_rom_p s msF'), Ey. reflexivity. }
    assert (HPk : P (as_VIS KHr s (wrom msF' (ms_rom y)))).
    { change (P (as_VIS (KHp p) s (wrom msF' (ms_rom y)))).
      rewrite (vis_wrom_p s msF' (ms_rom y)), Ey.
      change (P (wrom y (ms_rom y))). rewrite wrom_eta. exact Py. }
    pose proof (HK (wrom msF' (ms_rom y)) mo'
                   (conj (akrel_wrom s msF' mo' (ms_rom y) HA') (conj (vcm2_wrom msF' mo' (ms_rom y) V') PW)) HM HPk) as SK.
    change (sreach (asegs ++ tail) (fun c' => exists c0, c' = cwrom c0 rV /\ Q c0)
              (mkCfg (wrom (wrom msF' (ms_rom y)) rV) mo')) in SK.
    assert (E2 : wrom (wrom msF' (ms_rom y)) rV = msF').
    { rewrite <- Er. exact (wrom_eta msF'). }
    rewrite E2 in SK. exact SK.
  Qed.

  Theorem khr_SR_laws : SR_laws KHr.
  Proof.
    split; [exact srr_done|]. split; [exact srr_mono|]. split; [exact srr_seq | exact srr_evt].
  Qed.

  Theorem khr_AKREL_laws : AKREL_laws KHr.
  Proof.
    destruct (inst_AKREL_laws p) as [A1 A2]. split.
    - intros s c [HA _]. exact (A1 s c HA).
    - exact A2.
  Qed.

  Theorem khr_MPRES_laws : MPRES_laws KHr.
  Proof. exact (inst_MPRES_laws p). Qed.

  (** * The marker and the window across a heap call *)

  (* [pw_ok] but for its budget conjunct *)
  Definition pw_core (x : ist) : Prop :=
       in_rangesb (Z_to_bv 64 (sh vb)) (a_S (i_s x)) = true
    /\ (forall y : word, sh vb + 72 <= bv_unsigned y < sh vb + 104 -> in_rangesb y (a_S (i_s x)) = false).

  (* what [KHr]'s kernel relation adds to [KHp p]'s, but for the budget: what the heap calls keep *)
  Definition XR : ist -> config -> Prop := fun x c => VC2 c /\ pw_core x.

  Lemma pw_core_of : forall x, pw_ok vb x -> pw_core x.
  Proof. intros x (A & B & _). split; [exact A | exact B]. Qed.

  Lemma pw_ok_of : forall x, pw_core x -> 4096 <= a_AL (i_s x) -> pw_ok vb x.
  Proof. intros x [A B] C. split; [exact A|]. split; [exact B | exact C]. Qed.

  Lemma ikeep_r : ikeep VC2.
  Proof. intros Q c S V. exact (keep_vcm2 Q c S V). Qed.

  Lemma xr_vcm : forall x c, XR x c -> VC2 c.
  Proof. intros x c [V _]. exact V. Qed.

  (* where the marker and the window lie: high-shadow bytes, below [AHI_LO] and above the image,
     whose application bytes are text bytes *)
  Lemma pw_geo : forall Y, sh vb <= Y < sh vb + 104 ->
       sh AHI_LO <= Y < sh aceil /\ ALOWSH_LO <= Y < AHI_LO /\ AIMG_TOP <= Y /\ Y < aceil
    /\ vb <= pw_app Y < vhi /\ 0 <= pw_app Y < 2 ^ 64 /\ 0 <= Y < 2 ^ 64.
  Proof.
    intros Y HY. pose proof Hvb as (V8 & V1 & V2 & V3).
    pose proof aceil_facts as ACF. pose proof sh_ceiling_lt_AHI_LO as SC.
    unfold pw_app, sh, ASHADOW_BASE, AHI_LO, ALOWSH_LO, AIMG_TOP in *.
    Z.div_mod_to_equations. lia.
  Qed.

  (* a heap call writes neither the marker nor the window: they are high-shadow bytes, where no
     object of the allocator, of its depot or of the binary lies, and the application bytes they
     cover are text bytes, which no map holds, so they are no shadow byte of the primary space or
     of a secondary chunk of either state *)
  Lemma pw_not_awrit : forall (s s' : ast) (d : depot) msF mo msF' mo' (lo SP : Z) (y : word),
    placed_ok s -> placed_ok s' -> AG_Malloc2.depot_placed s d -> aceil <= lo ->
    akernel s mo -> akernel s' mo' ->
    PairCleanAll.vcm_cfg vb vhi (mkCfg msF mo) -> PairCleanAll.vcm_cfg vb vhi (mkCfg msF' mo') ->
    sh vb <= bv_unsigned y < sh vb + 104 ->
    ~ awrit s s' d lo SP (bv_unsigned y).
  Proof.
    intros s s' d msF mo msF' mo' lo SP y PL PL' DPL CEIL AK AK' V V' Hy.
    destruct (pw_geo (bv_unsigned y) Hy) as (HS & LAND & TOP & ACE & Z1 & Z2 & _).
    assert (MO : Forall (VdsoClean.range_off vb vhi) (vm_maps (m_vmmaps mo))) by (destruct V as [_ [MO _]]; exact MO).
    assert (MO' : Forall (VdsoClean.range_off vb vhi) (vm_maps (m_vmmaps mo'))) by (destruct V' as [_ [MO' _]]; exact MO').
    pose proof PL as (_ & S2 & _ & _ & P2 & _ & _ & T2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
    pose proof PL' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC' & _).
    pose proof DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _ & G12 & _).
    unfold awrit. intros W.
    destruct W as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
    - (* the stack, above the ceiling *)
      lia.
    - (* the thread page: an object of the low range or of the application's *)
      destruct T2 as [T2|T2].
      + unfold alow1, AIMG_LO in T2. unfold ALOWSH_LO in LAND. lia.
      + destruct (aapp_not_shadowland _ _ T2); lia.
    - (* the primary space, at or above [AHI_LO] *)
      lia.
    - (* the primary space's shadow: the byte would cover a primary byte, which is mapped, but the
         bytes it covers are text bytes, which no map holds *)
      assert (Hz : a_sb s <= pw_app (bv_unsigned y) < a_sb s + AsanAllocModel.kSpaceSize + AsanAllocModel.kPageSize).
      { clear - C. unfold pw_app. unfold sh in C. Z.div_mod_to_equations. lia. }
      assert (IN : in_rangesb (Z_to_bv 64 (pw_app (bv_unsigned y))) (vm_maps (m_vmmaps mo)) = true).
      { apply (ak_sbmaps s mo AK). rewrite MState.unsigned_lit by exact Z2. exact Hz. }
      assert (OUT : in_rangesb (Z_to_bv 64 (pw_app (bv_unsigned y))) (vm_maps (m_vmmaps mo)) = false).
      { apply (maps_off_in vb vhi); [exact MO | rewrite MState.unsigned_lit by exact Z2; exact Z1]. }
      congruence.
    - (* the pointer array *)
      destruct (aapp_not_shadowland _ _ P2); lia.
    - (* a secondary chunk of either state: its bytes are application bytes, and a shadow byte of
         it would cover a byte of the chunk, which is mapped *)
      destruct C as (sc & INs & R).
      assert (AP : aapp (AsanAllocModel.sc_map_beg sc) (AsanAllocModel.sc_map_size sc)
                   /\ AsanAllocModel.sc_map_beg sc + AsanAllocModel.sc_map_size sc <= aceil
                   /\ 2 * AsanAllocModel.kPageSize <= AsanAllocModel.sc_map_size sc).
      { destruct INs as [Is|Is];
          [ pose proof (SEC sc Is) as (_ & A1 & A2 & A3 & _) | pose proof (SEC' sc Is) as (_ & A1 & A2 & A3 & _) ];
          exact (conj A1 (conj A2 A3)). }
      destruct AP as (AP & CE & SZ). unfold AsanAllocModel.kPageSize in SZ.
      destruct R as [R|R].
      + destruct (aapp_not_shadowland _ _ AP); lia.
      + assert (Hz : AsanAllocModel.sc_map_beg sc <= pw_app (bv_unsigned y)
                       < AsanAllocModel.sc_map_beg sc + AsanAllocModel.sc_map_size sc).
        { clear - R. unfold pw_app. unfold sh in R. Z.div_mod_to_equations. lia. }
        pose proof (aapp_bounds _ _ AP ltac:(lia)) as (B1 & B2 & B3 & B4 & _).
        assert (EB : bv_unsigned (TacX.wz (AsanAllocModel.sc_map_beg sc)) = AsanAllocModel.sc_map_beg sc)
          by (apply TacX.wz_unsigned; unfold AAPP_HI in B3; lia).
        assert (ES : bv_unsigned (TacX.wz (AsanAllocModel.sc_map_size sc)) = AsanAllocModel.sc_map_size sc)
          by (apply TacX.wz_unsigned; unfold AAPP_HI in B3; lia).
        destruct INs as [Is|Is].
        * apply (in_maps_off vb vhi _ (TacX.wz (AsanAllocModel.sc_map_beg sc)) (TacX.wz (AsanAllocModel.sc_map_size sc)) (pw_app (bv_unsigned y))
                   MO (ak_secmaps s mo AK sc Is)); [rewrite EB, ES; exact Hz | exact Z1].
        * apply (in_maps_off vb vhi _ (TacX.wz (AsanAllocModel.sc_map_beg sc)) (TacX.wz (AsanAllocModel.sc_map_size sc)) (pw_app (bv_unsigned y))
                   MO' (ak_secmaps s' mo' AK' sc Is)); [rewrite EB, ES; exact Hz | exact Z1].
    - (* the binary's static cells, in its image *)
      unfold astatw, AINST, AIAINIT, AIAINST in C. unfold ALOWSH_LO in LAND. lia.
    - (* the depot's two blocks *)
      destruct (aapp_not_shadowland _ _ G10); lia.
    - destruct (aapp_not_shadowland _ _ G12); lia.
  Qed.

  (* a heap call keeps [XR]: the marker keeps the byte the caller's view has there, so it stays
     visible; the window keeps having none, so it stays hidden *)
  Lemma xkeep_r : XKEEP VC2 XR.
  Proof.
    unfold XKEEP, XR. cbv beta.
    intros s s' d d' msF mo msF' mo' m m' lo SP [V PC] V' AMX AWV PL DPL Em AMX' AWV' PL' Em' KEEP CEIL.
    split; [exact V'|].
    pose proof (proj2 AMX) as AK. pose proof (proj2 AMX') as AK'.
    unfold pw_core in PC |- *. cbn [i_s] in PC |- *. destruct PC as [MK WN].
    assert (NW : forall y : word, sh vb <= bv_unsigned y < sh vb + 104 -> ~ awrit s s' d lo SP (bv_unsigned y)).
    { intros y Hy. exact (pw_not_awrit s s' d msF mo msF' mo' lo SP y PL PL' DPL CEIL AK AK' (proj2 V) (proj2 V') Hy). }
    assert (LS : forall y : word, sh vb <= bv_unsigned y < sh vb + 104 ->
                   in_rangesb y (a_L s) = true /\ in_rangesb y (a_L s') = true).
    { intros y Hy. destruct (pw_geo _ Hy) as (HS & _).
      split; [exact (ak_lsh s mo AK y HS) | exact (ak_lsh s' mo' AK' y HS)]. }
    assert (NS : forall (mm : mem) (y : word), sh vb <= bv_unsigned y < sh vb + 104 -> wview asegs mm y = mm y).
    { intros mm y Hy. destruct (pw_geo _ Hy) as (_ & _ & HT & _). exact (wview_noseg mm y HT). }
    split.
    - (* the marker: visible before, so the caller's view has its byte, which the call keeps;
         were it hidden after, the callee's view would have none *)
      destruct (pw_geo (sh vb) ltac:(lia)) as (_ & _ & _ & _ & _ & _ & R0).
      assert (HX : sh vb <= bv_unsigned (Z_to_bv 64 (sh vb)) < sh vb + 104)
        by (rewrite MState.unsigned_lit by exact R0; lia).
      destruct (in_rangesb (Z_to_bv 64 (sh vb)) (a_S s')) eqn:E'; [reflexivity | exfalso].
      pose proof (proj2 (KEEP _ (NW _ HX)) (AWV _ MK)) as W1.
      rewrite (NS m' _ HX) in W1. apply W1.
      rewrite <- Em', ms_mem_restrict. apply restrict_mem_hidden.
      apply (proj2 (hiddenb_true_iff _ _ _)). split; [exact (proj2 (LS _ HX)) | exact E'].
    - (* the window: hidden before, so the caller's view has no byte there, nor does the callee's;
         were it visible after, the callee's view would have one *)
      intros y Hy.
      assert (HY : sh vb <= bv_unsigned y < sh vb + 104) by lia.
      destruct (in_rangesb y (a_S s')) eqn:E'; [exfalso | reflexivity].
      assert (W0 : wview asegs m y = None).
      { rewrite (NS m y HY), <- Em, ms_mem_restrict. apply restrict_mem_hidden.
        apply (proj2 (hiddenb_true_iff _ _ _)). split; [exact (proj1 (LS _ HY)) | exact (WN y Hy)]. }
      exact (AWV' _ E' (proj1 (KEEP _ (NW _ HY)) W0)).
  Qed.

  (** * The budget *)

  Lemma al_kr : forall s : as_St KHr, as_AL KHr s = as_AL (KHp p) s - 4096.
  Proof. intros s. reflexivity. Qed.
  Lemma al_kp : forall s : as_St (KHp p), as_AL (KHp p) s = a_AL (i_s s).
  Proof. intros s. reflexivity. Qed.
  Lemma cm_kr : forall n, as_Cm KHr n = as_Cm (KHp p) n.
  Proof. intros n. reflexivity. Qed.
  Lemma cf_kr : forall n, as_Cf KHr n = as_Cf (KHp p) n.
  Proof. intros n. reflexivity. Qed.

  (** * The heap calls' reaches *)

  (* a reach of [KHp p] from a state with the binary's backing and the pair's invariant is a
     reach of [KHr], the invariant holding where it arrives *)
  Lemma lift_p : forall (Q Q' : config -> Prop) msF mo,
    as_SR (KHp p) Q (mkCfg msF mo) ->
    VC2 (mkCfg msF mo) ->
    ms_rom msF = OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.seg_rom asegs ->
    (forall c, Q c -> VC2 c -> Q' c) ->
    as_SR KHr Q' (mkCfg msF mo).
  Proof.
    intros Q Q' msF mo S V Hr K.
    change (sr_run Q' (mkCfg msF mo)). unfold sr_run.
    eapply sreach_mono;
      [exact (sreach_lift_tail asegs tail Hnx Hnw vdso_image_asegs _ (mkCfg msF mo)
                (keep_vcm2 Q _ (sr_p_sreach _ _ S) V) Hr) |].
    intros c' (c0 & E & HQ & HV0). exists c0. split; [exact E | exact (K c0 HQ HV0)].
  Qed.

  (* the posts at [KHX p XR] are those at [KHr]: the kernel relation's [XR] and the budget bound
     give [pw_ok], and the bound restates with the 4096 held back on both sides *)
  Lemma malloc_post_r : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (s : as_St (KHp p)) LB n lo B m mo c,
    as_Cm (KHp p) n <= as_AL (KHp p) s - 4096 ->
    malloc_post (KHX p XR) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo c ->
    malloc_post KHr ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo c.
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo c HC HP.
    unfold malloc_post in HP |- *.
    destruct HP as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & A & junk & q & s'
                    & E & (K & V & PC) & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & AL).
    assert (AL' : as_AL (KHp p) s' >= as_AL (KHp p) s - as_Cm (KHp p) n) by exact AL.
    pose proof (pw_ok_of s' PC ltac:(pose proof (al_kp s'); lia)) as PW.
    assert (AL'' : as_AL KHr s' >= as_AL KHr s - as_Cm KHr n)
      by (pose proof (al_kr s'); pose proof (al_kr s); pose proof (cm_kr n); lia).
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', errv', A, junk, q, s'.
    exact (conj E (conj (conj K (conj V PW))
             (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 (conj R8 (conj R9 (conj R10 (conj R11 AL''))))))))))))).
  Qed.

  Lemma free_post_r : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (s : as_St (KHp p)) LB q n lo B errv m mo c,
    as_Cf (KHp p) n <= as_AL (KHp p) s - 4096 ->
    free_post (KHX p XR) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB q n lo B errv m mo c ->
    free_post KHr ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB q n lo B errv m mo c.
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB q n lo B errv m mo c HC HP.
    unfold free_post in HP |- *.
    destruct HP as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & s'
                    & E & (K & V & PC) & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & AL).
    assert (AL' : as_AL (KHp p) s' >= as_AL (KHp p) s - as_Cf (KHp p) n) by exact AL.
    pose proof (pw_ok_of s' PC ltac:(pose proof (al_kp s'); lia)) as PW.
    assert (AL'' : as_AL KHr s' >= as_AL KHr s - as_Cf KHr n)
      by (pose proof (al_kr s'); pose proof (al_kr s); pose proof (cf_kr n); lia).
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', s'.
    exact (conj E (conj (conj K (conj V PW))
             (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 (conj R8 AL'')))))))))).
  Qed.

  Lemma free_null_post_r : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (s : as_St (KHp p)) LB lo B errv m mo c,
    as_Cf (KHp p) 0 <= as_AL (KHp p) s - 4096 ->
    free_null_post (KHX p XR) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B errv m mo c ->
    free_null_post KHr ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B errv m mo c.
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B errv m mo c HC HP.
    unfold free_null_post in HP |- *.
    destruct HP as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & s'
                    & E & (K & V & PC) & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & AL).
    assert (AL' : as_AL (KHp p) s' >= as_AL (KHp p) s - as_Cf (KHp p) 0) by exact AL.
    pose proof (pw_ok_of s' PC ltac:(pose proof (al_kp s'); lia)) as PW.
    assert (AL'' : as_AL KHr s' >= as_AL KHr s - as_Cf KHr 0)
      by (pose proof (al_kr s'); pose proof (al_kr s); pose proof (cf_kr 0); lia).
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', s'.
    exact (conj E (conj (conj K (conj V PW))
             (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 (conj R8 AL'')))))))))).
  Qed.

  Lemma realloc_post_r : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (s : as_St (KHp p)) LB q old n lo B bs m mo c,
    as_Cm (KHp p) n + as_Cf (KHp p) old <= as_AL (KHp p) s - 4096 ->
    realloc_post (KHX p XR) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB q old n lo B bs m mo c ->
    realloc_post KHr ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB q old n lo B bs m mo c.
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB q old n lo B bs m mo c HC HP.
    unfold realloc_post in HP |- *.
    destruct HP as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & A' & junk & q' & s'
                    & E & (K & V & PC) & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & AL).
    assert (AL' : as_AL (KHp p) s' >= as_AL (KHp p) s - as_Cm (KHp p) n - as_Cf (KHp p) old) by exact AL.
    pose proof (pw_ok_of s' PC ltac:(pose proof (al_kp s'); lia)) as PW.
    assert (AL'' : as_AL KHr s' >= as_AL KHr s - as_Cm KHr n - as_Cf KHr old)
      by (pose proof (al_kr s'); pose proof (al_kr s); pose proof (cm_kr n); pose proof (cf_kr old); lia).
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', errv', A', junk, q', s'.
    exact (conj E (conj (conj K (conj V PW))
             (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 (conj R8 (conj R9 (conj R10 (conj R11 AL''))))))))))))).
  Qed.

  Lemma memalign_post_r : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (s : as_St (KHp p)) LB P al n lo B m mo c,
    as_Cm (KHp p) (n + al) <= as_AL (KHp p) s - 4096 ->
    memalign_post (KHX p XR) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB P al n lo B m mo c ->
    memalign_post KHr ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB P al n lo B m mo c.
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB P al n lo B m mo c HC HP.
    unfold memalign_post in HP |- *.
    destruct HP as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & Ab & junk & q & s'
                    & E & (K & V & PC) & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & AL).
    assert (AL' : as_AL (KHp p) s' >= as_AL (KHp p) s - as_Cm (KHp p) (n + al)) by exact AL.
    pose proof (pw_ok_of s' PC ltac:(pose proof (al_kp s'); lia)) as PW.
    assert (AL'' : as_AL KHr s' >= as_AL KHr s - as_Cm KHr (n + al))
      by (pose proof (al_kr s'); pose proof (al_kr s); pose proof (cm_kr (n + al)); lia).
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', errv', Ab, junk, q, s'.
    exact (conj E (conj (conj K (conj V PW))
             (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 (conj R8 (conj R9 (conj R10
               (conj R11 (conj R12 (conj R13 AL''))))))))))))))).
  Qed.

  (* each heap call at [KHr]: the theorem at [KHX p XR] from the caller's state with [XR], the
     budget bound with the 4096 held back given, lifted to the run's list *)
  Lemma khr_malloc : malloc_stmt KHr.
  Proof.
    unfold malloc_stmt, malloc_stmt_at.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m s LB n lo B errv mo CH
           HV HR HK0 HAO HCm HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH HTR Ha0 HN.
    destruct HK0 as (HK & VC & PW).
    assert (HC : as_Cm (KHp p) n <= as_AL (KHp p) s - 4096) by (pose proof (al_kr s); pose proof (cm_kr n); lia).
    assert (HC' : as_Cm (KHp p) n <= as_AL (KHp p) s) by lia.
    pose proof (AS_InstHeap.inst_malloc_stmt_X p TRLEN VC2 XR ikeep_r xr_vcm xkeep_r
                  ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m s LB n lo B errv mo CH
                  HV HR (conj HK (conj VC (pw_core_of s PW))) HAO HC' HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH HTR Ha0 HN) as S0.
    apply (lift_p _ _ msF mo (srx_p p XR _ _ S0) VC (vis_rom_eq _ _ _ HV)).
    intros c HP _.
    exact (malloc_post_r ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo c HC HP).
  Qed.

  Lemma khr_free : free_stmt KHr.
  Proof.
    unfold free_stmt, free_stmt_at.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m s LB q A n lo B errv mo CH bs sbs
           HV HR HK0 HIN HCf HRW HSH HLS HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH HTR Ha0.
    destruct HK0 as (HK & VC & PW).
    assert (HC : as_Cf (KHp p) n <= as_AL (KHp p) s - 4096) by (pose proof (al_kr s); pose proof (cf_kr n); lia).
    assert (HC' : as_Cf (KHp p) n <= as_AL (KHp p) s) by lia.
    pose proof (AS_InstFree.inst_free_stmt_X p TRLEN VC2 XR ikeep_r xr_vcm xkeep_r
                  ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m s LB q A n lo B errv mo CH bs sbs
                  HV HR (conj HK (conj VC (pw_core_of s PW))) HIN HC' HRW HSH HLS HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH HTR Ha0) as S0.
    apply (lift_p _ _ msF mo (srx_p p XR _ _ S0) VC (vis_rom_eq _ _ _ HV)).
    intros c HP _.
    exact (free_post_r ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB q n lo B errv m mo c HC HP).
  Qed.

  Lemma khr_free_null : free_null_stmt_at KHr AFREE_STUB.
  Proof.
    unfold free_null_stmt_at.
    intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m s LB lo B errv mo CH
           HV HR HK0 HCf HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH.
    destruct HK0 as (HK & VC & PW).
    assert (HC : as_Cf (KHp p) 0 <= as_AL (KHp p) s - 4096) by (pose proof (al_kr s); pose proof (cf_kr 0); lia).
    assert (HC' : as_Cf (KHp p) 0 <= as_AL (KHp p) s) by lia.
    pose proof (AS_InstFree.inst_free_null_stmt_X p VC2 XR ikeep_r xr_vcm xkeep_r
                  ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m s LB lo B errv mo CH
                  HV HR (conj HK (conj VC (pw_core_of s PW))) HC' HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH) as S0.
    apply (lift_p _ _ msF mo (srx_p p XR _ _ S0) VC (vis_rom_eq _ _ _ HV)).
    intros c HP _.
    exact (free_null_post_r ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B errv m mo c HC HP).
  Qed.

  Lemma khr_realloc : realloc_stmt KHr.
  Proof.
    unfold realloc_stmt, realloc_stmt_at.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m s LB q A old n lo B errv mo CH bs sbs
           HV HR HK0 HIN HAO HCm HRW HSH HLS HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH HTR Ha0 Ha1 HN HOLD.
    destruct HK0 as (HK & VC & PW).
    assert (HC : as_Cm (KHp p) n + as_Cf (KHp p) old <= as_AL (KHp p) s - 4096)
      by (pose proof (al_kr s); pose proof (cm_kr n); pose proof (cf_kr old); lia).
    assert (HC' : as_Cm (KHp p) n + as_Cf (KHp p) old <= as_AL (KHp p) s) by lia.
    pose proof (AS_InstRealloc.inst_realloc_stmt_X p TRLEN VC2 XR ikeep_r xr_vcm xkeep_r
                  ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m s LB q A old n lo B errv mo CH bs sbs
                  HV HR (conj HK (conj VC (pw_core_of s PW))) HIN HAO HC' HRW HSH HLS HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH HTR Ha0 Ha1 HN HOLD) as S0.
    apply (lift_p _ _ msF mo (srx_p p XR _ _ S0) VC (vis_rom_eq _ _ _ HV)).
    intros c HP _.
    exact (realloc_post_r ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB q old n lo B bs m mo c HC HP).
  Qed.

  (* posix_memalign, which [AInstFacts.ainst_facts] takes besides time() *)
  Lemma khr_memalign_stmt : memalign_stmt KHr APOSIX_MEMALIGN_STUB APC0_POSIX_MEMALIGN.
  Proof.
    unfold memalign_stmt.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc msF m s LB P al n lo B errv mo CH pjunk
           HV HR HK0 HAO HCm HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH HTR Ha0 HP8 HPW HCW HACW HPOFF Ha1 HAL Ha2 HN.
    destruct HK0 as (HK & VC & PW).
    assert (HC : as_Cm (KHp p) (n + al) <= as_AL (KHp p) s - 4096)
      by (pose proof (al_kr s); pose proof (cm_kr (n + al)); lia).
    assert (HC' : as_Cm (KHp p) (n + al) <= as_AL (KHp p) s) by lia.
    pose proof (AS_InstMemalign.inst_memalign_stmt_X p TRLEN VC2 XR ikeep_r xr_vcm xkeep_r
                  ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc msF m s LB P al n lo B errv mo CH pjunk
                  HV HR (conj HK (conj VC (pw_core_of s PW))) HAO HC' HAU HB HST HL1 HL2 HER HMI HTP HSP HAC HCH HTR Ha0 HP8 HPW HCW HACW HPOFF Ha1 HAL Ha2 HN) as S0.
    apply (lift_p _ _ msF mo (srx_p p XR _ _ S0) VC (vis_rom_eq _ _ _ HV)).
    intros c HPost _.
    exact (memalign_post_r ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB P al n lo B m mo c HC HPost).
  Qed.

  (** * [asan_rt_hyps_x]: the four heap calls at [KHX p XR], every other conjunct [KHp p]'s *)

  Theorem khr_rt_hyps_x : asan_rt_hyps_x (KHp p) -> asan_rt_hyps_x KHr.
  Proof.
    intros (HH & _ & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
    destruct HH as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & L17
                    & L18 & L19 & L20 & L21 & L22 & _ & _ & _ & S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
    split; [|split; [exact khr_realloc|]].
    - split; [exact khr_SR_laws|]. split; [exact khr_AKREL_laws|]. split; [exact L3|]. split; [exact L4|].
      split; [exact L5|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8|]. split; [exact L9|].
      split; [exact L10|]. split; [exact L11|]. split; [exact L12|]. split; [exact L13|]. split; [exact L14|].
      split; [exact L15|]. split; [exact L16|]. split; [exact L17|]. split; [exact L18|]. split; [exact L19|].
      split; [exact L20|]. split; [exact L21|]. split; [exact L22|].
      split; [exact khr_malloc|]. split; [exact khr_free|]. split; [exact khr_free_null|].
      split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|].
      split; [exact S6|]. split; [exact S7|]. split; [exact S8 | exact S9].
    - split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
      split; [exact X6|]. split; [exact X7|]. split; [exact X8|]. split; [exact X9 | exact X10].
  Qed.

  (** * The driver laws over the run's list *)

  Theorem khr_driver_laws : asan_driver_laws_run tail vlo vb vhi KHr.
  Proof.
    pose proof (inst_driver_laws p) as DL.
    constructor.
    - intros Q c T S K. change (sr_run Q c) in S. unfold sr_run in S.
      eapply sreach_realizes; [exact S|].
      intros c' (c0 & -> & HQ). exact (K c0 HQ).
    - intros s. destruct (adl_lazy (KHp p) DL s) as (L & S & Zr & HV & HL & HT).
      exists L, S, Zr. split; [|split].
      + exact HV.
      + intros c [HA _]. exact (HL c HA).
      + intros ms mo ms' mo' [HA [_ PW]] LZ E1 E2 V. split; [exact (HT ms mo ms' mo' HA LZ E1 E2) | exact (conj V PW)].
    - intros s c [_ [V _]]. exact V.
    - exact (adl_mpres (KHp p) DL).
    - exact (adl_sb (KHp p) DL).
    - exact (adl_rdr (KHp p) DL).
    - exact (adl_live (KHp p) DL).
    - exact Hvtop.
    - exact Hvord.
  Qed.
End RunAs.
