(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
  HeapIface LibIface LibIfaceFp LibIfaceFpW DrvKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6Drv_defs_u5 Pm6DrvLib_u5 Pm6DrvD_defs_u5 Pm6ExitAx_u5 Pm6DrvLibL_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Lib Require Import LibContractU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvLibLayoutW.
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
  Variable PHI : list byte -> Prop.
  Hypothesis LIokW : LCU.lib_iface_okU Lay scfg HI LSt PHI.

  Lemma lib_sitew : forall vals ebs sr kn R M (model : Model) LB cr g so bls vbnd (ptr ra : Z) (payload : list byte) K,
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
    PHI payload ->
    (forall (fx' : PropExec.FPState) R' M' (model' : Model) g' cr',
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       PHI payload ->
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
           R2 Hso Hsoal R1 Hra Hra2 R3 R4 R10 R11 Hlen Hptr Hpay Hcr Hls HFP HH Hh Hlz Hmt Hbl Hvb HK0 HPHI0 CONT.
    pose proof (LCU.liou_call Lay scfg HI LSt PHI LIokW fx g LB cr (bv_unsigned sp0 + so) ptr ra payload R M model K) as MS.
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
      apply (CONT fx' R' M' model' g' cr' HL' HPHI0).
      + (* [comment removed for export] *)
        apply regs_ok_upd_same; [| discriminate | cbn [edenot]; symmetry; exact Qa0].
        apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_kept sp0 Hsp R R' Qregs) c_kept_no0).
      + (* [comment removed for export] *)
        unfold keep_lib.
        pose proof (env_app_know RSEGS vals (junk_vals R') ebs M kn Hkv HK) as HK1.
        eapply (know_keep_sound RSEGS 0 so 65536 bls vbnd [3%nat; 4%nat] IMG_LIB IMG_RW
                  (Env (vals_ev (vals ++ junk_vals R')) ebs) (CPl L Lay LB (bv_unsigned sp0 + so)) (SCl (bv_unsigned sp0 + so))).
        * apply (regions_lib L sp0 Hsp DL Lay DLL); try assumption.
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
        * apply (not_foot L sp0 Hsp Lay DLL). lia.
        * unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
      + intros a Ha Hb. apply Qframe; [exact Ha | left; exact Hb | |].
        * destruct Hb as (b & Hin & Hr). destruct (hio_wf L scfg HI HIok LB cr M (m_vmmaps model) HH) as [WF _].
          destruct (WF b Hin) as (BR & _). pose proof (hz_of_block_range L sp0 DL _ _ BR) as (Y1 & Y2 & Y3). apply (not_foot L sp0 Hsp Lay DLL). lia.
        * destruct Hb as (b & Hin & Hr). destruct (hio_wf L scfg HI HIok LB cr M (m_vmmaps model) HH) as [WF _].
          destruct (WF b Hin) as (BR & _). pose proof (hz_of_block_range L sp0 DL _ _ BR) as (Y1 & Y2 & Y3).
          unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
      + intros a Ha Hs He Hf. apply Qframe; [lia | | apply (not_foot L sp0 Hsp Lay DLL); exact Hf |].
        * unfold client_addr. right. right. rewrite (dl_img_lo L sp0 DL), (dl_img_hi L sp0 DL). split; [lia|].
          intros Hst. apply (dl_static L sp0 DL) in Hst. lia.
        * unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
  Qed.
End DrvLibLayoutW.
End FPX_1.
