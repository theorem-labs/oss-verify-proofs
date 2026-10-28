(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  RefNodes HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface LibIfaceAB DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition IMG_LIB_A : list (Z * Z) :=
  [(0x10000, 0x139000); (0x13bbe0, 0x13c580); (0x662290, 0x6722c0); (0x672308, 0x672530); (0x6733f0, 0x673ca8);
   (0x673cb0, 0x673cf8); (0x673d14, 0x673d28); (0x673d30, 0x693d50); (0x693f70, 0x6951b8); (0x6951c0, 0x696000)].      (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LIB_HOLES : list (Z * Z) := [(0x6722c0, 0x672308); (0x672530, 0x6733f0); (0x693d50, 0x693f70)].
Definition keep_libA (so sc : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so sc bls vbnd [] IMG_LIB_A IMG_RW_A kn.
Lemma img_lib_sub : forall lo hi, In (lo, hi) IMG_LIB_A ->
  (exists lo' hi', In (lo', hi') IMG_CLIENT_A /\ lo' <= lo /\ hi <= hi') /\ 0x10000 <= lo /\ hi <= 0x696000 /\ lo <= hi
  /\ forall hl hh, In (hl, hh) LIB_HOLES -> hi <= hl \/ hh <= lo.
Proof.
  intros lo hi Hin. unfold IMG_LIB_A in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-;
    (split; [first [ (exists 0x10000, 0x139000; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
                   | (exists 0x13bbe0, 0x13c580; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
                   | (exists 0x662290, 0x673ca8; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
                   | (exists 0x673cb0, 0x673cf8; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
                   | (exists 0x673d14, 0x673d28; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
                   | (exists 0x673d30, 0x6951b8; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia])
                   | (exists 0x6951c0, 0x696000; split; [unfold IMG_CLIENT_A; cbn [In]; tauto | lia]) ] |]);
    (split; [lia|]); (split; [lia|]); (split; [lia|]);
    intros hl hh Hh; unfold LIB_HOLES in Hh; cbn [In] in Hh; repeat (destruct Hh as [Hh|Hh]; [injection Hh as <- <-; lia|]); destruct Hh |]).
  destruct Hin.
Qed.

(* [comment removed for export] *)
Record drv_lib_layoutA (Lay : lib_layoutA) (L : asan_layout) : Prop := DRV_LIB_LAYOUTA {
  dlla_L : lla_L Lay = L;
  dlla_entry : lla_entry Lay = 0xa7fa4;
  dlla_gp : lla_gp Lay = 0x10800;
  dlla_stack : 4096 <= lla_stack Lay <= 2 ^ 20 /\ lla_stack Lay mod 8 = 0;      (* [comment removed for export] *)
  dlla_empty : lla_empty Lay = 0x6722a0;                                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  dlla_foot : forall iv, In iv (lla_foot Lay) -> exists hl hh, In (hl, hh) LIB_HOLES /\ hl <= fst iv /\ snd iv <= hh;
  (* [comment removed for export] *)
  dlla_junk : forall iv, In iv (lla_junk Lay) -> exists hl hh, In (hl, hh) LIB_HOLES /\ hl <= fst iv /\ snd iv <= hh;
  dlla_credit_pos : forall n, 0 <= n -> 0 <= fst (lla_credit Lay n) /\ 0 <= snd (lla_credit Lay n);
  (* [comment removed for export] *)
  dlla_frames : forall k, In k [0; 1; 2; 3; 4; 5] -> 0 <= lla_leak Lay k /\ 4 * lla_leak Lay k + lla_frames Lay k <= ff_cap k
}.

(* [comment removed for export] *)
Lemma regs_ok_upd_sameA : forall E sr R (rd : reg) e,
  regs_ok E sr R -> rd <> 0%bv -> edenot E e = getr R rd -> regs_ok E (sr_upd sr (ridx rd) e) R.
Proof.
  intros E sr R rd e HR Hrd He r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - specialize (HR r). unfold sr_get in HR. rewrite Hr0 in HR. exact HR.
  - rewrite nth_sr_upd. destruct (Nat.eqb (ridx r) (ridx rd)) eqn:Hi.
    + apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r. symmetry. exact He.
    + specialize (HR r). unfold sr_get in HR. rewrite Hr0 in HR. exact HR.
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section LibSite.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Variable M0 : word -> option byte.
  Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
  Variable Lay : lib_layoutA.
  Variable LSt : lib_statics.
  Hypothesis DLL : drv_lib_layoutA Lay L.
  Hypothesis LIok : lib_call_okA Lay ar scfg HI LSt.

  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation LV := (lib_view Lay ar).

  #[using="L sp0 Hsp DLL"] Lemma not_foot_of_hole : forall a, (forall hl hh, In (hl, hh) LIB_HOLES -> ~ (hl <= a < hh)) -> ~ in_foot LV a.
  Proof.
    intros a Hn (iv & Hin & Hr). cbn [lib_view ll_foot] in Hin. destruct (dlla_foot Lay L DLL iv Hin) as (hl & hh & Hh & H1 & H2).
    apply (Hn hl hh Hh). lia.
  Qed.
  #[using="L sp0 Hsp DLL"] Lemma not_foot_off_image : forall a, ~ (0x662290 <= a < 0x696000) -> ~ in_foot LV a.
  Proof.
    intros a Ha. apply not_foot_of_hole. intros hl hh Hh. unfold LIB_HOLES in Hh. cbn [In] in Hh.
    repeat (destruct Hh as [Hh|Hh]; [injection Hh as <- <-; lia|]). destruct Hh.
  Qed.
  (* [comment removed for export] *)
  #[using="L sp0 Hsp DLL"] Lemma not_junk_of_hole : forall a, (forall hl hh, In (hl, hh) LIB_HOLES -> ~ (hl <= a < hh)) -> ~ in_junk Lay a.
  Proof.
    intros a Hn (iv & Hin & Hr). destruct (dlla_junk Lay L DLL iv Hin) as (hl & hh & Hh & H1 & H2).
    apply (Hn hl hh Hh). lia.
  Qed.
  #[using="L sp0 Hsp DLL"] Lemma not_junk_off_image : forall a, ~ (0x662290 <= a < 0x696000) -> ~ in_junk Lay a.
  Proof.
    intros a Ha. apply not_junk_of_hole. intros hl hh Hh. unfold LIB_HOLES in Hh. cbn [In] in Hh.
    repeat (destruct Hh as [Hh|Hh]; [injection Hh as <- <-; lia|]). destruct Hh.
  Qed.

  (* [comment removed for export] *)
  Definition CPl (LBc : list (Z * Z)) (sp scr : Z) (H H' : word -> bool) (a : Z) : Prop :=
    (aclient L ar LBc [] sp scr a /\ ~ in_foot LV a /\ ~ in_junk Lay a) /\ H (Z_to_bv 64 a) = false /\ H' (Z_to_bv 64 a) = false.

  #[using="scfg C IL HIok Hsp DL DLL"] Lemma regions_callL : forall vals ebs so scr bls vbnd LB LK LK' cr cr' A A' M M' model model',
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    - 2 ^ 22 <= so <= 0 -> 0 <= scr <= 2 ^ 21 ->
    ri_inv HI LB [] LK cr A M (vml_of model) -> ri_inv HI LB [] LK' cr' A' M' (vml_of model') ->
    (forall i nb, find_nz i bls = Some nb -> sub_blockA L ar LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> bv_unsigned (vals_ev vals v) <= b) ->
    regions_ok ASEGS 0 so scr bls vbnd [] IMG_LIB_A IMG_RW_A E
               (CPl LB (bv_unsigned sp0 + so) scr (ahid A model) (ahid A' model')) (SCa (bv_unsigned sp0 + so) scr).
  Proof.
    intros vals ebs so scr bls vbnd LB LK LK' cr cr' A A' M M' model model' E P0 Hso Hscr HH HH' Hbl Hvb.
    pose proof Hsp as Hsp'.
    assert (VIS : forall a, 0 <= a < 2 ^ 64 -> (a < 0x696000 \/ bv_unsigned sp0 - 8388608 <= a \/ in_block LB a) ->
                  ahid A model (Z_to_bv 64 a) = false /\ ahid A' model' (Z_to_bv 64 a) = false).
    { intros a Ha Hc. split.
      - apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a HH Ha). destruct Hc as [Hc|[Hc|Hc]]; auto.
      - apply (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a HH' Ha). destruct Hc as [Hc|[Hc|Hc]]; auto. }
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CPl. split; [split|apply VIS; lia].
      + unfold aclient. right. left. rewrite (dla_sptop L ar IL sp0 DL). lia.
      + split; [apply not_foot_off_image | apply not_junk_off_image]; lia.
    - intros z Hz. right. unfold SCa. lia.
    - intros i nb Hf. pose proof (sub_blockA_hz L ar IL sp0 DL _ _ _ (Hbl i nb Hf)) as (Z1 & Z2 & Z3).
      destruct (Hbl i nb Hf) as (cap & Hnb & Hin & HB). pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HB) as (Y1 & Y2 & Y3).
      split; [lia|]. intros z Hz.
      assert (IB : in_block LB (bv_unsigned (vals_ev vals i) + z)).
      { exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin|]. cbn [fst snd]. lia. }
      unfold CPl. split; [split; [left; exact IB | split; [apply not_foot_off_image | apply not_junk_off_image]; lia] | apply VIS; [lia | right; right; exact IB]].
    - exact Hvb.
    - intros i [].
    - intros lo hi Hin. destruct (img_lib_sub lo hi Hin) as ((lo' & hi' & Hin' & S1 & S2) & I1 & I2 & I3 & HOLE).
      split; [lia|]. split; [lia|]. intros a Ha. unfold CPl. split; [split|apply VIS; lia].
      + unfold aclient. right. right. left. rewrite (dla_img_lo L ar IL sp0 DL), (dla_img_hi L ar IL sp0 DL). split; [lia|].
        apply (dla_client L ar IL sp0 DL lo' hi' a Hin'). lia.
      + split; [apply not_foot_of_hole | apply not_junk_of_hole]; intros hl hh Hh; destruct (HOLE hl hh Hh); lia.
    - intros lo hi Hin. unfold IMG_RW_A in Hin. destruct Hin as [E1|[]]. injection E1 as <- <-. split; [lia|]. split; [lia|].
      intros Mx d m Hd Hm.
      apply (store_ok_window ASEGS Mx (Z_to_bv 64 0x662290) (Z_to_bv 64 d) 65536%nat m 0x662290 0x672290);
        first [exact (wseg_stage) | reflexivity | lia | (rewrite u_small by lia; lia)].
  Qed.

  (* [comment removed for export] *)
  #[using="C IL HIok Hsp Hal DL M0_def DLL LIok"] Lemma alib_site : forall vals ebs sr kn R M (model : Model) LB LK cr A g so stk bls vbnd (ptr ra : Z) (payload : list byte) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok ASEGS E (mrestrict (ahid A model) M) kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 21 <= so <= 0 -> so mod 16 = 0 -> lla_stack Lay <= stk <= 2 ^ 21 ->
    getr R 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 47 -> ra mod 2 = 0 ->
    getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x673d00 ->
    getr R 10 = Z_to_bv 64 ptr -> getr R 11 = Z_to_bv 64 (Z.of_nat (length payload)) -> Z.of_nat (length payload) < 2 ^ 26 ->
    ((length payload = 0%nat /\ ptr = lla_empty Lay) \/ (0 < Z.of_nat (length payload) /\ In (ptr, Z.of_nat (length payload)) LB)) ->
    rdn ASEGS M (Z_to_bv 64 ptr) (length payload) = Some payload ->
    credit_le (lla_credit Lay (Z.of_nat (length payload))) cr ->
    (forall k, In k [0; 1; 2; 3; 4; 5] -> Z.of_nat (ff_count k LK) + lla_frames Lay k <= ff_cap k) ->
    ls_ok LSt g M ->
    dinvA LB LK cr A M model ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_blockA L ar LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    K [] ->
    (forall (fx' : PropExec.FPState) R' M' (model' : Model) g' cr' LK' A',
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       regs_ok E' (sr_upd (sr_after_call_j sr (map ridx c_kept) (length vals)) (ridx 10) (ELit 0)) R' ->
       know_ok ASEGS E' (mrestrict (ahid A' model') M') (keep_libA so stk bls vbnd kn) ->
       dinvA LB LK' cr' A' M' model' -> model_rt model model' -> incl A A' ->
       (forall k, In k [0; 1; 2; 3; 4; 5] -> Z.of_nat (ff_count k LK') <= Z.of_nat (ff_count k LK) + lla_leak Lay k) ->
       ls_ok LSt g' M' ->
       credit_le (credit_sub cr (lla_credit Lay (Z.of_nat (length payload)))) cr' ->
       (forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall lo hi a, In (lo, hi) IMG_LIB_A -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 ra) M' (seg_rom ASEGS)) model') K) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xa7fa4) M (seg_rom ASEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB LK cr A g so stk bls vbnd ptr ra payload K E HR HK Hsv Hkv HL1 P0 Hiw
           R2 Hso Hsoal Hstk R1 Hra Hra2 R3 R4 R10 R11 Hlen Hptr Hpay Hcr Hroom Hls DI Hbl Hvb HK0 CONT.
    pose proof (di_inv _ _ _ _ _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ _ _ _ _ DI) as HMI.
    pose proof (dinv_stack_defined scfg L ar C HI HIok sp0 Hsp M0 M0_def _ _ _ _ _ _ DI) as Hdef.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'. destruct (dlla_stack Lay L DLL) as ((ST1 & ST2) & ST3).
    set (sp := bv_unsigned sp0 + so) in *.
    assert (WDEF : forall a, bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0 -> M (Z_to_bv 64 a) <> None)
      by (exact (window_defined sp0 Hsp vals ebs (ahid A model) M kn HK Hiw P0)).
    destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & (B4096 & TOPEQ & _ & _) & TOP47 & _).
    pose proof (LIok fx g LB [] LK cr A sp ptr ra payload R M model K) as MS.
    unfold lib_cfgA in MS. rewrite (dlla_L Lay L DLL), (dla_segs L ar IL sp0 DL), (dlla_entry Lay L DLL) in MS.
    apply MS; clear MS; try assumption.
    - (* [comment removed for export] *)
      constructor; rewrite ?(dlla_L Lay L DLL), ?(dla_segs L ar IL sp0 DL), ?(dla_tp L ar IL sp0 DL), ?(dlla_gp Lay L DLL); try assumption.
      + split; [exact Hra | exact Hra2].
      + (* [comment removed for export] *)
        rewrite (dla_sptop L ar IL sp0 DL). unfold sp.
        split; [rewrite Z.add_mod, Hal', Hsoal by lia; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
        * intros i Hi. apply WDEF. lia.
        * intros i Hi. destruct (Z_lt_le_dec (bv_unsigned sp0 + so + i) (bv_unsigned sp0)) as [Hlo|Hhi].
          -- apply WDEF. lia.
          -- replace (bv_unsigned sp0 + so + i) with (bv_unsigned sp0 + (so + i)) by ring. apply Hdef. lia.
      + intros f [].
      + (* [comment removed for export] *)
        intros j Hj. apply (di_stksh _ _ _ _ _ _ _ _ _ _ DI). unfold STKTOP, in_shadow_of, S, SB. rewrite (dla_sptop L ar IL sp0 DL) in *.
        set (mx := Z.max (bv_unsigned sp0) (ar_stack_top ar)) in *.
        replace (bv_unsigned sp0 - 8388608 + (mx - (bv_unsigned sp0 - 8388608)) - 1) with (mx - 1) by ring.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        unfold sp in *. lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - (* [comment removed for export] *)
      intros fx' g' R' M' model' cr' LK' A' POST HRT HINC Hh' HMI' HLEAK HH'.
      destruct POST as [Qa0 Qregs Qcr Qframe Qscr Qgrows Qstk Qls].
      rewrite ?(dlla_L Lay L DLL) in *.
      assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
      assert (FR : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB [] sp stk a -> ~ in_foot LV a /\ ~ in_junk Lay a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha Hc [Hf Hj]. apply Qframe; [exact Ha | | exact Hf | exact Hj]. apply (aclient_scr_mono L ar sp0 Hsp LB [] sp stk (lla_stack Lay) a); [lia | exact Hc]. }
      assert (ABOVE : forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha. apply FR; [lia | | split; [apply not_foot_off_image | apply not_junk_off_image]; lia]. unfold aclient. right. left. rewrite (dla_sptop L ar IL sp0 DL). unfold sp. lia. }
      apply (CONT fx' R' M' model' g' cr' LK' A' HL'); try assumption.
      + (* [comment removed for export] *)
        apply regs_ok_upd_sameA; [| discriminate | cbn [edenot]; symmetry; exact Qa0].
        apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA sp0 Hsp R R' Qregs) c_kept_no0A).
      + (* [comment removed for export] *)
        unfold keep_libA.
        pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
        refine (know_keep_sound ASEGS 0 so stk bls vbnd [] IMG_LIB_A IMG_RW_A
                  (Env (vals_ev (vals ++ junk_vals R')) ebs)
                  (CPl LB sp stk (ahid A model) (ahid A' model')) (SCa sp stk)
                  _ (mrestrict (ahid A model) M) (mrestrict (ahid A' model') M') _ _ kn HK1).
        * eapply (regions_callL (vals ++ junk_vals R') ebs so stk bls vbnd LB LK LK' cr cr' A A' M M' model model');
            [exact P0' | lia | lia | exact HH | exact HH' | | ].
          -- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
          -- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
        * intros a Ha ((HC & HF) & V1 & V2). unfold mrestrict. rewrite V1, V2. apply FR; assumption.
        * intros a HS. unfold SCa in HS. unfold mrestrict.
          rewrite (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a HH') by (unfold sp in *; lia).
          destruct (Z_lt_le_dec a (sp - lla_stack Lay)) as [Hlo|Hhi].
          -- rewrite Qframe; [apply WDEF; unfold sp in *; lia | unfold sp in *; lia | | apply not_foot_off_image; unfold sp in *; lia | apply not_junk_off_image; unfold sp in *; lia].
             unfold aclient. right. left. rewrite (dla_sptop L ar IL sp0 DL). unfold sp in *. lia.
          -- replace a with (sp - lla_stack Lay + (a - (sp - lla_stack Lay))) by ring. apply Qscr. lia.
      + (* [comment removed for export] *)
        apply DINV; [exact HH' | exact HMI' | exact Hh' | | |].
        * intros a Ha. rewrite (ABOVE a Ha). exact (di_above _ _ _ _ _ _ _ _ _ _ DI a Ha).
        * intros x Hx. destruct (stksh_rng scfg L ar C IL HI HIok sp0 Hsp DL _ _ _ _ _ _ _ x HH Hx) as (XR & XC).
          unfold STKTOP, in_shadow_of, S, SB in Hx. rewrite (dla_sptop L ar IL sp0 DL) in Hx.
          set (mx := Z.max (bv_unsigned sp0) (ar_stack_top ar)) in *.
          replace (bv_unsigned sp0 - 8388608 + (mx - (bv_unsigned sp0 - 8388608)) - 1) with (mx - 1) in Hx by ring.
          destruct (Z_lt_le_dec x (S (sp - lla_stack Lay))) as [Hlo|Hhi].
          -- unfold byte_at. rewrite FR; [exact (di_stksh _ _ _ _ _ _ _ _ _ _ DI x ltac:(unfold STKTOP, in_shadow_of, S, SB; rewrite (dla_sptop L ar IL sp0 DL); fold mx;
                   replace (bv_unsigned sp0 - 8388608 + (mx - (bv_unsigned sp0 - 8388608)) - 1) with (mx - 1) by ring; exact Hx)) | lia | | split; [apply not_foot_off_image | apply not_junk_off_image]; lia].
             unfold aclient. right. right. right. right. left. exact XC.
          -- replace x with (S (sp - lla_stack Lay) + (x - S (sp - lla_stack Lay))) by ring. apply Qstk.
             rewrite (dla_sptop L ar IL sp0 DL). fold mx. unfold S, SB in *.
             Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
             unfold sp in *. lia.
             Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        * intros x Hx. pose proof (hish_rng L ar IL sp0 Hsp DL x Hx) as XR. unfold byte_at.
          rewrite FR; [exact (di_hish _ _ _ _ _ _ _ _ _ _ DI x Hx) | lia | unfold aclient; right; right; right; right; left; exact Hx | split; [apply not_foot_off_image | apply not_junk_off_image]; lia].
      + intros a Ha Hb. apply FR; [exact Ha | left; exact Hb |].
        destruct Hb as (b & Hb & Hr). destruct (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _). destruct (WF b Hb) as (HBR & _).
        pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR) as (Y1 & Y2 & Y3). split; [apply not_foot_off_image | apply not_junk_off_image]; lia.
      + intros lo hi a Hin Ha. destruct (img_lib_sub lo hi Hin) as ((lo' & hi' & Hin' & S1 & S2) & I1 & I2 & I3 & HOLE).
        apply FR; [lia | | split; [apply not_foot_of_hole | apply not_junk_of_hole]; intros hl hh Hhol; destruct (HOLE hl hh Hhol); lia].
        unfold aclient. right. right. left. rewrite (dla_img_lo L ar IL sp0 DL), (dla_img_hi L ar IL sp0 DL). split; [lia|].
        apply (dla_client L ar IL sp0 DL lo' hi' a Hin'). lia.
  Qed.
End LibSite.
End FPX_1.
