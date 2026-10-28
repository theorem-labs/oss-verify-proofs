(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RunEnv
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg ShapeLaws SpinAlg SpinAlgX
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Hoare AsanAcct
  HeapIface LibIface LibIfaceFp DrvKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6Drv_defs_u5 Pm6DrvLib_u5 Pm6DrvD_defs_u5 Pm6ExitAx_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Lib Require Import LibContractU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Drv Require Import LibStaticsU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Record drv_lib_layout (Lay : lib_layout) (L : heap_layout) : Prop := DRV_LIB_LAYOUT {
  dll_heap : ll_heap Lay = L;
  dll_entry : ll_entry Lay = 0x3a610;
  dll_gp : ll_gp Lay = 0x10800;
  dll_empty : ll_empty Lay = 0xdb5a0;
  dll_stack : ll_stack Lay = 65536;
  dll_rw_lo : ll_rw_lo Lay <= 0xcb428;
  dll_foot : forall iv, In iv (ll_foot Lay) -> (0xdb5b0 <= fst iv /\ snd iv <= 0xdc788) \/ (0xdcf38 <= fst iv /\ snd iv <= 0xdcf40)
                                            \/ (0xfd058 <= fst iv /\ snd iv <= 0xfd278);
  dll_initc : forall iv, In iv (ll_initc Lay) ->
      (0xdcf48 <= fst iv /\ snd iv <= 0xdd010) \/ (0xfd280 <= fst iv /\ snd iv <= 0xfd288) \/ (0xfd2a8 <= fst iv /\ snd iv <= 0xfd2b0)
      \/ (0xfd2d8 <= fst iv /\ snd iv <= 0xfd308)
      \/ (0xfd2a3 <= fst iv /\ snd iv <= 0xfd2a4) \/ (0xfd378 <= fst iv /\ snd iv <= 0xfd37c);   (* [comment removed for export] *)
  dll_credit_pos : forall n, 0 <= n -> 0 <= fst (ll_credit Lay n) /\ 0 <= snd (ll_credit Lay n);
  dll_init_img : ll_init_img Lay = [(0x10000, 0xcb538); (0xdb591, 0xdb594); (0xdb595, 0xdcf40); (0xfd018, 0xfd038);
                                    (0xfd058, 0xfd060); (0xfd064, 0xfd068); (0xfd070, 0xfd078); (0xfd080, 0xfd178); (0xfd180, 0xfd278);
                                    (0xfd2a3, 0xfd2a4); (0xfd378, 0xfd37c)];
      (* [comment removed for export] *)
  dll_init_cells : ll_init_cells Lay = [(0xfd060, 4%nat, 1); (0xfd068, 8%nat, 0xfd070); (0xfd078, 8%nat, 0xad8c0); (0xfd178, 8%nat, 0x3a598)];
      (* [comment removed for export] *)
  dll_td_self : ll_td_self Lay = 0xdcf48;
  dll_td_tid : ll_td_tid Lay = 0xdcf68;
  dll_td_locale : ll_td_locale Lay = 0xdcfe0;
  dll_locale : ll_locale Lay = 0xfd2d8;
  dll_td_canary : ll_td_canary Lay = 0xdd000;
  dll_guard : ll_guard Lay = 0xfd280;
  dll_auxvp : ll_auxvp Lay = 0xfd2a8;
  dll_phdr : ll_phdr Lay = 0x10040;
  dll_phent : ll_phent Lay = 56;
  dll_phnum : ll_phnum Lay = 10
}.

(* [comment removed for export] *)
Definition DRV_ATEXIT : Z * Z := (0xad8c0, 0x3a598).
(* [comment removed for export] *)
Definition AEF_IN_CALLBACK : Z := 0xdb594.
Definition XInv (m : word -> option byte) : Prop := rdn RSEGS m (Z_to_bv 64 AEF_IN_CALLBACK) 1%nat = Some [Z_to_bv 8 0].
Definition lib_exit_ok (LSt : lib_statics) : Prop :=
  forall (g : ls_state LSt) (M : word -> option byte), ls_ok LSt g M ->
    exists hs : list (Z * Z), Z.of_nat (length hs) <= 31
      /\ (forall fx : PropExec.FPState, Forall (fun h => @handler_ok fx (fun _ => True) (fst h) (snd h)) hs)
      /\ atexit_state M (DRV_ATEXIT :: hs).

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)
Lemma regs_ok_upd_same : forall E sr R (rd : reg) e,
  regs_ok E sr R -> rd <> 0%bv -> edenot E e = getr R rd -> regs_ok E (sr_upd sr (ridx rd) e) R.
Proof.
  intros E sr R rd e HR Hrd He r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - specialize (HR r). unfold sr_get in HR. rewrite Hr0 in HR. exact HR.
  - rewrite nth_sr_upd. destruct (Nat.eqb (ridx r) (ridx rd)) eqn:Hi.
    + apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r. symmetry. exact He.
    + specialize (HR r). unfold sr_get in HR. rewrite Hr0 in HR. exact HR.
Qed.

Lemma segs_below : segs_below_b RSEGS 0xfe000 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma window_defined : forall M (a : Z),
  0xfe000 <= a -> a < 2 ^ 64 -> store_ok RSEGS M (Z_to_bv 64 a) 1 = true -> M (Z_to_bv 64 a) <> None.
Proof.
  intros M a Ha Ha2 Hst.
  pose proof (store_ok_all RSEGS M 1%nat (Z_to_bv 64 a) ltac:(rewrite u_small by lia; cbn; lia) Hst (Z_to_bv 64 a)
                ltac:(rewrite u_small by lia; cbn; lia)) as W.
  unfold wview in W. destruct (M (Z_to_bv 64 a)) as [b|] eqn:E; [congruence|].
  rewrite (find_segment1_none_above RSEGS 0xfe000 (bv_unsigned (Z_to_bv 64 a)) segs_below) in W by (rewrite u_small by lia; lia).
  exact W.
Qed.

Section DrvLibLayout.
  Variable L : heap_layout.
  Variable HI : heap_iface.
  Hypothesis HIok : heap_iface_ok L scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layout L sp0.
  Variable Lay : lib_layout.
  Variable LSt : lib_statics.
  Hypothesis DLL : drv_lib_layout Lay L.
  Hypothesis LIok : lib_iface_ok_u Lay scfg HI LSt.

  (* [comment removed for export] *)
  Definition CPl (LB : list (Z * Z)) (sp : Z) (a : Z) : Prop :=
    client_addr L LB sp 65536 a /\ ~ in_foot Lay a /\ ~ in_errno L a.
  Definition SCl (sp : Z) (a : Z) : Prop := sp - 65536 <= a < sp.

  Lemma not_foot : forall a, (a < 0xdb5b0 \/ (0xdc788 <= a < 0xdcf38) \/ (0xdcf40 <= a < 0xfd058) \/ 0xfd278 <= a) -> ~ in_foot Lay a.
  Proof.
    intros a Ha (iv & Hin & Hr). apply (dll_foot Lay L DLL) in Hin. lia.
  Qed.

  Lemma regions_lib : forall vals ebs so bls vbnd LB,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    - 2 ^ 22 <= so <= 0 ->
    (forall i nb, find_nz i bls = Some nb -> sub_block L LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> bv_unsigned (vals_ev vals v) <= b) ->
    (forall i, In i [3%nat; 4%nat] -> bv_unsigned sp0 <= bv_unsigned (vals_ev vals i) /\ bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64) ->
    regions_ok RSEGS 0 so 65536 bls vbnd [3%nat; 4%nat] IMG_LIB IMG_RW E
               (CPl LB (bv_unsigned sp0 + so)) (SCl (bv_unsigned sp0 + so)).
  Proof.
    intros vals ebs so bls vbnd LB E P0 Hso Hbl Hvb Hhi.
    pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH. pose proof (dl_errno L sp0 DL) as ER.
    pose proof (dl_sptop L sp0 DL) as TOP.
    assert (NE : forall a, 0xdcf70 <= a \/ a < 0xdcf6c -> ~ in_errno L a) by (intros a Ha; unfold in_errno; rewrite ER; lia).
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CPl, client_addr. split; [right; left; rewrite TOP; lia |]. split; [apply not_foot; lia | apply NE; lia].
    - intros z Hz. destruct (Z.lt_ge_cases (bv_unsigned sp0 + z) (bv_unsigned sp0 + so - 65536)) as [A|A].
      + left. unfold CPl, client_addr. split; [right; left; rewrite TOP; lia |]. split; [apply not_foot; lia | apply NE; lia].
      + right. unfold SCl. lia.
    - intros i nb Hf. pose proof (sub_block_hz L sp0 DL _ _ _ (Hbl i nb Hf)) as (Z1 & Z2 & Z3).
      destruct (Hbl i nb Hf) as (cap & Hnb & Hin & HB). pose proof (hz_of_block_range L sp0 DL _ _ HB) as (Y1 & Y2 & Y3).
      split; [lia|].
      intros z Hz. unfold CPl, client_addr.
      split; [left; exists (bv_unsigned (vals_ev vals i), cap); split; [exact Hin|]; cbn [fst snd]; lia |].
      split; [apply not_foot; lia | apply NE; lia].
    - exact Hvb.
    - intros i Hi. destruct (Hhi i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|].
      intros z Hz. unfold CPl, client_addr. split; [right; left; rewrite TOP; lia |]. split; [apply not_foot; lia | apply NE; lia].
    - intros lo hi Hin. unfold IMG_LIB in Hin.
      destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]);
        intros a Ha; unfold CPl, client_addr; (split; [| split; [apply not_foot; lia | apply NE; lia]]); right; right; rewrite IL, IH; (split; [lia|]);
        intros Hs; apply (dl_static L sp0 DL) in Hs; lia.
    - intros lo hi Hin. unfold IMG_RW in Hin.
      destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros Mx d m Hd Hm.
      + eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xc4000) _ 28672%nat m 0xc4000 0xcb000);
          [reflexivity | reflexivity | lia | apply wseg_c0000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
      + eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xcb000) _ 208896%nat m 0xcb000 0xfe000);
          [reflexivity | reflexivity | lia | apply wseg_c7000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
  Qed.

  (* [comment removed for export] *)
  Definition credit_scale (k : Z) (c : credit) : credit := (k * fst c, k * snd c).

  Lemma credit_le_step : forall k c cr cr',
    1 <= k -> 0 <= fst c -> 0 <= snd c ->
    credit_le (credit_scale k c) cr -> credit_le (credit_sub cr c) cr' -> credit_le (credit_scale (k - 1) c) cr'.
  Proof.
    intros k c cr cr' Hk H1 H2 [A B] [C D]. unfold credit_scale, credit_sub, credit_le in *. cbn [fst snd] in *. nia.
  Qed.

  Lemma credit_le_head : forall k c cr, 1 <= k -> 0 <= fst c -> 0 <= snd c ->
    credit_le (credit_scale k c) cr -> credit_le c cr.
  Proof. intros k c cr Hk H1 H2 [A B]. unfold credit_scale, credit_le in *. cbn [fst snd] in *. nia. Qed.

  (* [comment removed for export] *)
  Lemma lib_site : forall vals ebs sr kn R M (model : Model) LB cr g so bls vbnd (ptr ra : Z) (payload : list byte) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok RSEGS E M kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (5 <= length vals)%nat ->
    vals_ev vals 0 = sp0 ->
    (forall i, In i [3%nat; 4%nat] -> bv_unsigned sp0 <= bv_unsigned (vals_ev vals i) /\ bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64) ->
    has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    getr R 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 47 -> ra mod 2 = 0 ->
    getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0xdd010 ->
    getr R 10 = Z_to_bv 64 ptr -> getr R 11 = Z_to_bv 64 (Z.of_nat (length payload)) -> Z.of_nat (length payload) < 2 ^ 26 ->
    ((length payload = 0%nat /\ ptr = 0xdb5a0) \/ (0 < Z.of_nat (length payload) /\ In (ptr, Z.of_nat (length payload)) LB)) ->
    rdn RSEGS M (Z_to_bv 64 ptr) (length payload) = Some payload ->
    credit_le (ll_credit Lay (Z.of_nat (length payload))) cr ->
    ls_ok LSt g M ->
    fp_ok fx ->
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_block L LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    K [] ->
    lsu_phi Lay scfg HI LSt LIok payload ->
    (forall (fx' : PropExec.FPState) R' M' (model' : Model) g' cr',
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       regs_ok E' (sr_upd (sr_after_call_j sr (map ridx c_kept) (length vals)) (ridx 10) (ELit 0)) R' ->
       know_ok RSEGS E' M' (keep_lib so bls vbnd kn) ->
       hi_heap HI LB cr' M' (m_vmmaps model') ->
       model_but_vm model model' ->
       ls_ok LSt g' M' ->
       fp_ok fx' ->
       credit_le (credit_sub cr (ll_credit Lay (Z.of_nat (length payload)))) cr' ->
       (forall x : word, bv_unsigned sp0 <= bv_unsigned x -> M' x = M x) ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall a, 0x10000 <= a < 0xfe000 -> ~ (0xfd418 <= a < 0xfd7c0) -> ~ (0xdcf6c <= a < 0xdcf70) ->
                  (a < 0xdb5b0 \/ (0xdc788 <= a < 0xdcf38) \/ (0xdcf40 <= a < 0xfd058) \/ 0xfd278 <= a) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes RSEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 ra) M' (seg_rom RSEGS)) model') K) ->
    srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x3a610) M (seg_rom RSEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB cr g so bls vbnd ptr ra payload K E HR HK Hsv Hkv HL5 P0 Hhi Hiw
           R2 Hso Hsoal R1 Hra Hra2 R3 R4 R10 R11 Hlen Hptr Hpay Hcr Hls HFP HH Hh Hlz Hmt Hbl Hvb HK0 HPHI CONT.
    pose proof (LCU.liou_call Lay scfg HI LSt (lsu_phi Lay scfg HI LSt LIok) (lsu_ok Lay scfg HI LSt LIok)
                  fx g LB cr (bv_unsigned sp0 + so) ptr ra payload R M model K) as MS.
    unfold lib_cfg in MS. rewrite (dll_heap Lay L DLL), (dl_segs L sp0 DL), (dll_entry Lay L DLL) in MS.
    pose proof (dl_stack L sp0 DL) as ST.
    apply MS; clear MS; try assumption.
    - (* [comment removed for export] *)
      constructor; rewrite ?(dll_heap Lay L DLL), ?(dl_segs L sp0 DL), ?(dl_tp L sp0 DL), ?(dll_empty Lay L DLL), ?(dll_stack Lay L DLL),
                           ?(dll_gp Lay L DLL), ?(dl_sptop L sp0 DL); try assumption.
      + lia.
      + (* [comment removed for export] *)
        destruct (has_window_nth kn Hiw) as [i Hn].
        split; [rewrite Z.add_mod, Hal, Hsoal by lia; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
        * intros d m Hd Hm.
          pose proof (kwr_store_ok RSEGS E M kn i (EVar 0) (-8388608) 8388608 (so - 65536 + d) m HK Hn ltac:(lia) ltac:(lia)) as W.
          unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite P0 in W. unfold v_addi in W.
          replace (bv_unsigned sp0 + so - 65536 + d) with (bv_unsigned sp0 + (so - 65536 + d)) by lia. exact W.
        * intros a Ha.
          pose proof (kwr_store_ok RSEGS E M kn i (EVar 0) (-8388608) 8388608 (a - bv_unsigned sp0) 1%nat HK Hn ltac:(lia) ltac:(cbn; lia)) as W.
          unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite P0 in W. unfold v_addi in W.
          replace (bv_unsigned sp0 + (a - bv_unsigned sp0)) with a in W by lia.
          apply (window_defined M a); [lia | lia | exact W].
    - (* [comment removed for export] *)
      intros fx' g' R' M' model' cr' HFP' HPOST HH' HBUT.
      destruct HPOST as [Qa0 Qregs Qcr Qframe Qscr Qls].
      rewrite (dll_stack Lay L DLL) in Qframe, Qscr. rewrite (dll_heap Lay L DLL) in Qframe.
      assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
      apply (CONT fx' R' M' model' g' cr' HL').
      + (* [comment removed for export] *)
        apply regs_ok_upd_same; [| discriminate | cbn [edenot]; symmetry; exact Qa0].
        apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_kept sp0 Hsp R R' Qregs) c_kept_no0).
      + (* [comment removed for export] *)
        unfold keep_lib.
        pose proof (env_app_know RSEGS vals (junk_vals R') ebs M kn Hkv HK) as HK1.
        eapply (know_keep_sound RSEGS 0 so 65536 bls vbnd [3%nat; 4%nat] IMG_LIB IMG_RW
                  (Env (vals_ev (vals ++ junk_vals R')) ebs) (CPl LB (bv_unsigned sp0 + so)) (SCl (bv_unsigned sp0 + so))).
        * apply regions_lib; try assumption.
          -- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
          -- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
          -- intros i Hi. rewrite vals_ev_app_l; [apply Hhi; exact Hi|]. destruct Hi as [<-|[<-|[]]]; lia.
        * intros a Ha (HC & HF & HE). apply Qframe; assumption.
        * intros a HS. apply Qscr. exact HS.
        * exact HK1.
      + exact HH'.
      + exact HBUT.
      + exact Qls.
      + exact HFP'.
      + exact Qcr.
      + intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Qframe.
        * pose proof (u64_range x). lia.
        * unfold client_addr. right. left. rewrite (dl_sptop L sp0 DL). pose proof (u64_range x). lia.
        * apply not_foot. lia.
        * unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
      + intros a Ha Hb. apply Qframe; [exact Ha | left; exact Hb | |].
        * destruct Hb as (b & Hin & Hr). destruct (hio_wf L scfg HI HIok LB cr M (m_vmmaps model) HH) as [WF _].
          destruct (WF b Hin) as (BR & _). pose proof (hz_of_block_range L sp0 DL _ _ BR) as (Y1 & Y2 & Y3). apply not_foot. lia.
        * destruct Hb as (b & Hin & Hr). destruct (hio_wf L scfg HI HIok LB cr M (m_vmmaps model) HH) as [WF _].
          destruct (WF b Hin) as (BR & _). pose proof (hz_of_block_range L sp0 DL _ _ BR) as (Y1 & Y2 & Y3).
          unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
      + intros a Ha Hs He Hf. apply Qframe; [lia | | apply not_foot; exact Hf |].
        * unfold client_addr. right. right. rewrite (dl_img_lo L sp0 DL), (dl_img_hi L sp0 DL). split; [lia|].
          intros Hst. apply (dl_static L sp0 DL) in Hst. lia.
        * unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
  Qed.
End DrvLibLayout.
End FPX_1.
