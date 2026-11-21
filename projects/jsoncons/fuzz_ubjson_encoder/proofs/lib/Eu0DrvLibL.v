(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the BMode context; addresses and numbers; imports; unused lemmas removed; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Ub0DrvLibL.v, 99 lines within its lines 60-264. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import RunEnv
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg ShapeLaws SpinAlg SpinAlgX
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Hoare AsanAcct
  HeapIface LibIface DrvKit Eu0MainEntry Eu0Drv_defs Eu0DrvLib Eu0DrvD_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import LibIfaceE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Record drv_lib_layout (Lay : lib_layout) (L : heap_layout) : Prop := DRV_LIB_LAYOUT {
  dll_heap : ll_heap Lay = L;
  dll_entry : ll_entry Lay = 0x34eec;
  dll_gp : ll_gp Lay = 0x10800;
  dll_empty : ll_empty Lay = 0xcb1a0;
  dll_stack : ll_stack Lay = 65536;
  dll_rw_lo : ll_rw_lo Lay <= 0xbb028;
  dll_foot : forall iv, In iv (ll_foot Lay) -> (0xcb1b0 <= fst iv /\ snd iv <= 0xcc338) \/ (0xccae8 <= fst iv /\ snd iv <= 0xccaf0)
    \/ (0xecc08 <= fst iv /\ snd iv <= 0xece28);   (* [comment removed for export] *)
  dll_initc : forall iv, In iv (ll_initc Lay) ->
      (0xccaf8 <= fst iv /\ snd iv <= 0xccbc0) \/ (0xece30 <= fst iv /\ snd iv <= 0xece38) \/ (0xece58 <= fst iv /\ snd iv <= 0xece60)
      \/ (0xece88 <= fst iv /\ snd iv <= 0xeceb8)
      \/ (0xece53 <= fst iv /\ snd iv <= 0xece54) \/ (0xecf28 <= fst iv /\ snd iv <= 0xecf2c);   (* [comment removed for export] *)
  dll_credit_pos : forall n, 0 <= n -> 0 <= fst (ll_credit Lay n) /\ 0 <= snd (ll_credit Lay n);
  (* [comment removed for export] *)
  dll_init_img : ll_init_img Lay = [(0x10000, 0xbb140); (0xcb191, 0xcb194); (0xcb195, 0xccaf0); (0xecbc8, 0xecbe8);
                                   (0xecc00, 0xecc10); (0xecc14, 0xecc18); (0xecc20, 0xecc28); (0xecc30, 0xecd28); (0xecd30, 0xece28);
                                   (0xece53, 0xece54); (0xecf28, 0xecf2c)];
  dll_init_cells : ll_init_cells Lay = [(0xecc10, 4, 1); (0xecc18, 8, 0xecc20); (0xecc28, 8, 0x9d920); (0xecd28, 8, 0x34e74)];   (* [comment removed for export] *)
  dll_td_self : ll_td_self Lay = 0xccaf8;
  dll_td_tid : ll_td_tid Lay = 0xccb18;
  dll_td_locale : ll_td_locale Lay = 0xccb90;
  dll_locale : ll_locale Lay = 0xece88;
  dll_td_canary : ll_td_canary Lay = 0xccbb0;
  dll_guard : ll_guard Lay = 0xece30;
  dll_auxvp : ll_auxvp Lay = 0xece58;
  dll_phdr : ll_phdr Lay = 0x10040;
  dll_phent : ll_phent Lay = 56;
  dll_phnum : ll_phnum Lay = 10
}.

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.
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

Lemma segs_below : segs_below_b RSEGS 0xee000 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma window_defined : forall M (a : Z),
  0xee000 <= a -> a < 2 ^ 64 -> store_ok RSEGS M (Z_to_bv 64 a) 1 = true -> M (Z_to_bv 64 a) <> None.
Proof.
  intros M a Ha Ha2 Hst.
  pose proof (store_ok_all RSEGS M 1%nat (Z_to_bv 64 a) ltac:(rewrite u_small by lia; cbn; lia) Hst (Z_to_bv 64 a)
                ltac:(rewrite u_small by lia; cbn; lia)) as W.
  unfold wview in W. destruct (M (Z_to_bv 64 a)) as [b|] eqn:E; [congruence|].
  rewrite (find_segment1_none_above RSEGS 0xee000 (bv_unsigned (Z_to_bv 64 a)) segs_below) in W by (rewrite u_small by lia; lia).
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
  Variables PayOk PayExport : list byte -> Prop.
  Hypothesis LIokX : lib_iface_ok_x Lay scfg HI LSt PayOk PayExport.

  (* [comment removed for export] *)
  Definition CPl (LB : list (Z * Z)) (sp : Z) (a : Z) : Prop :=
    client_addr L LB sp 65536 a /\ ~ in_foot Lay a /\ ~ in_errno L a.
  Definition SCl (sp : Z) (a : Z) : Prop := sp - 65536 <= a < sp.

  Lemma not_foot : forall a, (a < 0xcb1b0 \/ (0xcc338 <= a < 0xccae8) \/ (0xccaf0 <= a < 0xecc08) \/ 0xece28 <= a) -> ~ in_foot Lay a.
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
    assert (NE : forall a, 0xccb20 <= a \/ a < 0xccb1c -> ~ in_errno L a) by (intros a Ha; unfold in_errno; rewrite ER; lia).
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
      + eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xb4000) _ 24576%nat m 0xb4000 0xba000);
          [reflexivity | reflexivity | lia | apply wseg_b0570 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
      + eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xba000) _ 212992%nat m 0xba000 0xee000);
          [reflexivity | reflexivity | lia | apply wseg_62ef4 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
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
    getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0xccbc0 ->
    getr R 10 = Z_to_bv 64 ptr -> getr R 11 = Z_to_bv 64 (Z.of_nat (length payload)) -> Z.of_nat (length payload) < 2 ^ 26 ->
    ((length payload = 0%nat /\ ptr = 0xcb1a0) \/ (0 < Z.of_nat (length payload) /\ In (ptr, Z.of_nat (length payload)) LB)) ->
    rdn RSEGS M (Z_to_bv 64 ptr) (length payload) = Some payload ->
    credit_le (ll_credit Lay (Z.of_nat (length payload))) cr ->
    ls_ok LSt g M ->
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_block L LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    PayOk payload ->      (* [comment removed for export] *)
    K [] ->
    (forall (fx' : PropExec.FPState) R' M' (model' : Model) g' cr',
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       regs_ok E' (sr_upd (sr_after_call_j sr (map ridx c_kept) (length vals)) (ridx 10) (ELit 0)) R' ->
       know_ok RSEGS E' M' (keep_lib so bls vbnd kn) ->
       hi_heap HI LB cr' M' (m_vmmaps model') ->
       model_but_vm model model' ->
       ls_ok LSt g' M' ->
       credit_le (credit_sub cr (ll_credit Lay (Z.of_nat (length payload)))) cr' ->
       (forall x : word, bv_unsigned sp0 <= bv_unsigned x -> M' x = M x) ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall a, 0x10000 <= a < 0xee000 -> ~ (0xecfc8 <= a < 0xed370) -> ~ (0xccb1c <= a < 0xccb20) ->
                  (a < 0xcb1b0 \/ (0xcc338 <= a < 0xccae8) \/ (0xccaf0 <= a < 0xecc08) \/ 0xece28 <= a) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       PayExport payload ->      (* [comment removed for export] *)
       srealizes RSEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 ra) M' (seg_rom RSEGS)) model') K) ->
    srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x34eec) M (seg_rom RSEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB cr g so bls vbnd ptr ra payload K E HR HK Hsv Hkv HL5 P0 Hhi Hiw
           R2 Hso Hsoal R1 Hra Hra2 R3 R4 R10 R11 Hlen Hptr Hpay Hcr Hls HH Hh Hlz Hmt Hbl Hvb HPok HK0 CONT.
    pose proof (liox_call Lay scfg HI LSt PayOk PayExport LIokX fx g LB cr (bv_unsigned sp0 + so) ptr ra payload R M model K) as MS.
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
          (* old: [... (EVar 0) (-8388608) 8388608 ...]; [so - 65536 + d >= - 2 ^ 22 - 65536 = -4259840 >= - DRV_ZWIN] *)
          pose proof (kwr_store_ok RSEGS E M kn i (EVar 0) (- DRV_ZWIN) DRV_ZWIN (so - 65536 + d) m HK Hn ltac:(lia) ltac:(lia)) as W.
          unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite P0 in W. unfold v_addi in W.
          replace (bv_unsigned sp0 + so - 65536 + d) with (bv_unsigned sp0 + (so - 65536 + d)) by lia. exact W.
        * intros a Ha.
          (* old: [... (EVar 0) (-8388608) 8388608 ...]; [a >= bv_unsigned sp0 + so - 65536 >= bv_unsigned sp0 - DRV_ZWIN] *)
          pose proof (kwr_store_ok RSEGS E M kn i (EVar 0) (- DRV_ZWIN) DRV_ZWIN (a - bv_unsigned sp0) 1%nat HK Hn ltac:(lia) ltac:(cbn; lia)) as W.
          unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite P0 in W. unfold v_addi in W.
          replace (bv_unsigned sp0 + (a - bv_unsigned sp0)) with a in W by lia.
          apply (window_defined M a); [lia | lia | exact W].
    - (* [comment removed for export] *)
      intros fx' g' R' M' model' cr' HPOST HPX HH' HBUT.
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
      + exact HPX.
  Qed.
End DrvLibLayout.
End FPX_1.
