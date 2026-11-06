(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame ITree Nodes InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanCtrlProps AsanEmbed AsanInv AsanBudget AsanTotalCore AsanNodeSem AsanTotal AsanFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ALayout AMalloc_iface AMalloc_iface2 AArenaLaw ATsafeCore ATsafeEv ATsafeAlloc ATsafeOps.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AEmbRep AEmbFrame APristLaw AFake_iface AInstanceU2 ARepAtMain ARepAtMain2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainExport MainFactsAsan MainEntry AsanPlanCore.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Adeq Acct.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainExport.
Module MF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainFactsAsan.
Module MA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntry.

Definition wE (b n : Z) : word * word := (wa b, wa n).

Section Root.
Context {rc : runConstT}.
Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (sp : word) (fs : Fs.Fs) (mo : Model).
Hypothesis HV : forall n, 0 <= V n < 2 ^ 64.
Hypothesis HPF : Forall (ME.pfact_ok V) MF.asan_pure_facts.
Hypothesis HUSP : usp_pin V.
Hypothesis HU : univ_ok U.
Hypothesis AMO : MA.amodel V sp fs mo.
Hypothesis USP : bv_unsigned sp = ATOP + 8388608.

Lemma LZSUB : forall z, ME.in_ivs z (m_vm_lazy mo) -> ME.in_ivs z (vm_maps (m_vmmaps mo)).
Proof. exact (MA.am_lazy_sub V sp fs mo AMO). Qed.
Lemma NANZ : Forall (fun e => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mo)).
Proof. exact (MA.am_noaccess_nz V sp fs mo AMO). Qed.
Lemma FKEAGER : forall a, 4096 * V 377%nat <= a < 4096 * V 377%nat + 11571200 -> page_in_ranges (page_base_of a) (m_vm_lazy mo) = false.
Proof. exact (MA.am_fake_eager V sp fs mo AMO). Qed.

Variable SHFIX : word -> Prop.
Variable KSH : Z.
Hypothesis SHFIX_fin : abud SHFIX KSH.
Hypothesis KSH0 : 0 <= KSH.

Variable NMAX : nat.
Hypothesis HNMAX : 59854610 + KSH <= Z.of_nat NMAX.

Local Notation L := (L0 V w U).
Local Notation sta := (st0 V w U).
Local Notation HP := (hp V HPF).
Tactic Notation "hpf" constr(k) ident(H) := pose proof (HP k _ eq_refl) as H; cbn [ME.pfact_ok ME.zv] in H.
Local Notation ALO := (alayout_ok_main V w U HV HPF HUSP HU).
Local Notation maps := (vm_maps (m_vmmaps mo)).

Definition KNOWN_hi : list (word * word) := [wE (4096 * V 471%nat) 4096; wE (4096 * V 454%nat) 8388608; wE (4096 * V 453%nat) 1048576].
Definition KNOWN_lo : list (word * word) :=
  [wE (4096 * V 377%nat) 11571200; wE (4096 * V 310%nat) 4096; wE (4096 * V 245%nat) 4096; wE (4096 * V 228%nat) 65536;
   wE (4096 * V 227%nat) 4096; wE (4096 * V 226%nat) 8388608; wE (4096 * V 208%nat) 137439023104; wE (4096 * V 207%nat) 3727360;
   wE (4096 * V 78%nat) 65536; wE 2201439137792 15392894357504; wE 2415882240 2199023255552; wE 2147446784 268435456].

Lemma maps_shape : exists fog : list (word * word),
  (length fog <= 2)%nat /\ Forall (fun iv => bv_unsigned (snd iv) <= 8192) fog
  /\ maps = KNOWN_hi ++ fog ++ KNOWN_lo.
Proof.
  pose proof (MA.am_maps V sp fs mo AMO) as LD. unfold MF.asan_ledger in LD. cbn [ME.ledger_den ME.zv] in LD.
  destruct LD as (m1 & E1 & m2 & E2 & m3 & E3 & LD).
  assert (TAILS : forall mx, ME.ledger_den V (skipn 5 MF.asan_ledger) mx -> mx = KNOWN_lo).
  { intros mx H. unfold MF.asan_ledger in H. cbn [skipn ME.ledger_den ME.zv] in H.
    destruct H as (n1 & -> & n2 & -> & n3 & -> & n4 & -> & n5 & -> & n6 & -> & n7 & -> & n8 & -> & n9 & -> & n10 & -> & n11 & -> & n12 & -> & ->).
    reflexivity. }
  destruct LD as [LD|(iv1 & m4 & E4 & S1 & LD)]; (destruct LD as [LD|(iv2 & m5 & E5 & S2 & LD)]).
  - exists []. split; [cbn; lia|]. split; [constructor|]. rewrite E1, E2, E3. rewrite (TAILS _ LD). reflexivity.
  - exists [iv2]. split; [cbn; lia|]. split; [constructor; [exact S2| constructor]|]. rewrite E1, E2, E3, E5. rewrite (TAILS _ LD). reflexivity.
  - exists [iv1]. split; [cbn; lia|]. split; [constructor; [exact S1| constructor]|]. rewrite E1, E2, E3, E4. rewrite (TAILS _ LD). reflexivity.
  - exists [iv1; iv2]. split; [cbn; lia|]. split; [constructor; [exact S1| constructor; [exact S2| constructor]]|]. rewrite E1, E2, E3, E4, E5. rewrite (TAILS _ LD). reflexivity.
Qed.

Lemma live_chunks_st0 : live_chunks sta = [].
Proof. unfold live_chunks. cbn [st0 ainit a_live]. rewrite map_to_list_empty. reflexivity. Qed.
Lemma qbatches_st0 : qbatches [] sta = [].
Proof. reflexivity. Qed.
Lemma all_chunks_st0 : all_chunks [] [] sta = [].
Proof. unfold all_chunks. rewrite live_chunks_st0. reflexivity. Qed.
Lemma CHX_st0 : CHX [] [] sta = [].
Proof. unfold CHX, CH. rewrite all_chunks_st0. reflexivity. Qed.

Lemma AINV_main : AINV ATOP [] [] sta.
Proof.
  unfold AINV. rewrite all_chunks_st0, qbatches_st0. pose proof (ao_space_al L ALO) as SAL. pose proof (ao_ptr L ALO) as (P1 & P2 & _).
  pose proof (ARepAtMain2.space_facts V w U HV HPF HUSP HU) as (S1 & _).
  split.
  { intros c Hc. unfold cls_inv. rewrite get_cls_st0, max_count_st0, all_chunks_st0, qbatches_st0.
    cbn [c_allocated_user c_mapped_user c_mapped_free_array c_num_freed c_count aclass0 cntP List.filter zlen length Z.of_nat].
    unfold nbatch, cntP, zlen, K_FREEARR_OFF, K_USER_MAP, K_FREEARR_MAX, K_FREEARR_MAP. cbn [List.filter length Z.of_nat].
    repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia. destruct (c =? K_BATCH_CLASS); cbn [length Z.of_nat]; lia. }
  split; [constructor|]. split; [constructor|]. split; [reflexivity|]. split; [reflexivity|]. split; [unfold CH; rewrite all_chunks_st0; reflexivity|].
  split; [exists 0; cbn [st0 ainit a_nres]; lia|].
  split. { intros id ch H. cbn [st0 ainit a_live] in H. rewrite lookup_empty in H. discriminate H. }
  split; [| split; [| split; [| split; [| split]]]].
  - cbn [st0 ainit a_space_beg]. exact SAL.
  - cbn [st0 ainit a_space_beg]. lia.
  - cbn [st0 ainit a_ptr_array]. exact P1.
  - cbn [st0 ainit a_ptr_array]. lia.
  - unfold live_budget. rewrite live_chunks_st0. unfold cntP, zlen, secs, secbytes. cbn [List.filter flat_map length Z.of_nat]. rewrite Z.mul_0_r. unfold L24MAX, SMAX, LSBYTES. lia.
  - unfold emb_ok. cbn [st0 ainit a_emb]. left. split; reflexivity.
Qed.

Definition RESV0 : list (Z * Z) :=
  [(0x10000, 0x3b000); (0x3b000, 0xcd000); (0xcd000, 0xd3000); (0xd3000, 0x62f000);
   (LS_LO, LS_LO + LS_SZ); (GAP_LO, GAP_LO + GAP_SZ); (HS_LO, HS_LO + HS_SZ);
   (4096 * V 208%nat, 4096 * V 208%nat + 137439023104); (4096 * V 226%nat, 4096 * V 226%nat + 8388608);
   (4096 * V 227%nat, 4096 * V 227%nat + 4096); (4096 * V 228%nat, 4096 * V 228%nat + 65536);
   (4096 * V 453%nat, 4096 * V 453%nat + 1048576); (4096 * V 454%nat, 4096 * V 454%nat + 8388608);
   (4096 * V 377%nat, 4096 * V 377%nat + 11571200); (4096 * V 310%nat, 4096 * V 310%nat + 4096);
   (4096 * V 78%nat, 4096 * V 78%nat + 65536); (4096 * V 207%nat, 4096 * V 207%nat + 3727360);
   (4096 * V 245%nat, 4096 * V 245%nat + 4096); (4096 * V 471%nat, 4096 * V 471%nat + 4096)].

Lemma pcov1 : forall lo hi, In (lo, hi) RESV0 -> pcov RESV0 lo hi.
Proof. intros lo hi Hin x Hx. exists (lo, hi). split; [exact Hin| exact Hx]. Qed.

Lemma aresv_ok_main : aresv_ok L RESV0.
Proof.
  unfold aresv_ok. unfold al_ptr_array, al_t, al_ctx, al_nodes, al_store, al_fake, al_dtls. cbn [al_V L0 VL]. unfold AIMG_HI.
  assert (I4 : pcov RESV0 0x10000 0x62f000).
  { intros x Hx. destruct (Z_lt_ge_dec x 0x3b000); [exists (0x10000, 0x3b000); split; [cbn; tauto| cbn; lia]|].
    destruct (Z_lt_ge_dec x 0xcd000); [exists (0x3b000, 0xcd000); split; [cbn; tauto| cbn; lia]|].
    destruct (Z_lt_ge_dec x 0xd3000); [exists (0xcd000, 0xd3000); split; [cbn; tauto| cbn; lia]|].
    exists (0xd3000, 0x62f000); split; [cbn; tauto| cbn; lia]. }
  assert (SH : pcov RESV0 0x7fff7000 0x10007fff8000).
  { intros x Hx. unfold RESV0, LS_LO, LS_SZ, GAP_LO, GAP_SZ, HS_LO, HS_SZ.
    destruct (Z_lt_ge_dec x 0x8fff7000); [eexists; split; [do 4 right; left; reflexivity| cbn; lia]|].
    destruct (Z_lt_ge_dec x 0x2008fff7000); [eexists; split; [do 5 right; left; reflexivity| cbn; lia]|].
    eexists; split; [do 6 right; left; reflexivity| cbn; lia]. }
  split; [exact I4|]. split; [exact SH|].
  repeat match goal with |- _ /\ _ => split end; apply pcov1; unfold RESV0; cbn [In]; tauto.
Qed.

Lemma maps_In_known : forall e, In e (KNOWN_hi ++ KNOWN_lo) -> In e maps.
Proof.
  intros e He. destruct maps_shape as (fog & _ & _ & EQ). rewrite EQ. apply in_app_or in He as [He|He]; apply in_or_app; [left; exact He| right; apply in_or_app; right; exact He].
Qed.

Lemma seps_of_ivs_sep : forall l, ME.ivs_sep l -> seps l.
Proof.
  induction l as [|p l IH]; intros H; [constructor|].
  constructor.
  - apply Forall_forall. intros q Hq. apply In_nth_error in Hq as [j Hj]. unfold wsep. exact (H 0%nat (Datatypes.S j) p q ltac:(lia) eq_refl Hj).
  - apply IH. intros i j a b Hij Hi Hj. exact (H (Datatypes.S i) (Datatypes.S j) a b ltac:(lia) Hi Hj).
Qed.

Lemma ivs_wf_of_bound : forall l (R : Z), Forall (fun iv => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= R) l -> R <= 2 ^ 64 -> ivs_wf l.
Proof. intros l R HF HR q Hq. unfold iv_wf, B, S. pose proof (proj1 (Forall_forall _ _) HF q Hq) as X. cbn in X. lia. Qed.

Lemma shadow_not_noaccess : forall a : word,
  (LS_LO <= bv_unsigned a < LS_LO + LS_SZ \/ HS_LO <= bv_unsigned a < HS_LO + HS_SZ) -> ~ ME.in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps mo)).
Proof.
  intros a Ha. pose proof (MA.am_kinds V sp fs mo AMO) as K. unfold MF.asan_ledger in K.
  pose proof (proj1 (Forall_forall _ _) K (ME.LMap (ME.ZLit 2147446784) 268435456 AsanPlanCore.APC.KRWLAZY) ltac:(cbn; tauto)) as KL.
  pose proof (proj1 (Forall_forall _ _) K (ME.LMap (ME.ZLit 2201439137792) 15392894357504 AsanPlanCore.APC.KRWLAZY) ltac:(cbn; tauto)) as KH.
  cbn [ME.lentry_kind_ok ME.zv] in KL, KH. unfold LS_LO, LS_SZ, HS_LO, HS_SZ in Ha.
  destruct Ha as [Ha|Ha]; [exact (proj1 (KL a Ha))| exact (proj1 (KH a Ha))].
Qed.

Lemma noacc_sep_main : noacc_sep (vm_noaccess (m_vmmaps mo)).
Proof.
  unfold noacc_sep. apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) NANZ e He) as NZ. cbn in NZ.
  pose proof (MA.am_noaccess_sub V sp fs mo AMO) as SUB.
  assert (IN : forall x, bv_unsigned (fst e) <= x < bv_unsigned (fst e) + bv_unsigned (snd e) -> ME.in_ivs x (vm_noaccess (m_vmmaps mo))).
  { intros x Hx. exists e. split; [exact He| exact Hx]. }
  pose proof (bv_unsigned_in_range _ (fst e)) as R1. pose proof (bv_unsigned_in_range _ (snd e)) as R2.
  unfold sepz, LS_LO, LS_SZ, HS_LO, HS_SZ. split.
  - destruct (Z_le_gt_dec (bv_unsigned (fst e) + bv_unsigned (snd e)) 2147446784) as [|G1]; [left; lia|].
    destruct (Z_le_gt_dec (2147446784 + 268435456) (bv_unsigned (fst e))) as [|G2]; [right; lia|]. exfalso.
    set (x := Z.max (bv_unsigned (fst e)) 2147446784).
    apply (shadow_not_noaccess (wa x)); rewrite wa_unsigned by lia; [left; unfold LS_LO, LS_SZ; lia| apply IN; lia].
  - destruct (Z_le_gt_dec (bv_unsigned (fst e) + bv_unsigned (snd e)) 2201439137792) as [|G1]; [left; lia|].
    destruct (Z_le_gt_dec (2201439137792 + 15392894357504) (bv_unsigned (fst e))) as [|G2]; [right; lia|]. exfalso.
    set (x := Z.max (bv_unsigned (fst e)) 2201439137792).
    apply (shadow_not_noaccess (wa x)); rewrite wa_unsigned by lia; [right; unfold HS_LO, HS_SZ; lia| apply IN; lia].
Qed.

Lemma csum_st0 : forall f, f aclass0 = 0 -> csum f sta = 0.
Proof.
  intros f Hf. unfold csum. generalize CLASSES as l. induction l as [|c l IH]; cbn [fold_right]; [reflexivity|]. rewrite get_cls_st0, Hf, IH. reflexivity.
Qed.
Lemma commit_bytes_st0 : commit_bytes sta = 0.
Proof. unfold commit_bytes. rewrite csum_st0 by reflexivity. reflexivity. Qed.

Lemma sum_count_Pm : forall mx, m_vmmaps mx = m_vmmaps mo -> m_vm_lazy mx = m_vm_lazy mo ->
  sum_count (Pm mx) maps = nonlazy_bytes mo.
Proof.
  intros mx EM EL. unfold nonlazy_bytes, vm_backed_maps. rewrite <- maps_subtract_all_app_cuts.
  assert (WF : ivs_wf maps).
  { apply (ivs_wf_of_bound maps (bv_unsigned sp - 8388608)); [| pose proof (bv_unsigned_in_range _ sp); lia].
    eapply Forall_impl; [| exact (MA.am_bounds V sp fs mo AMO)]. cbn. intros iv (_ & _ & _ & _ & _ & X). exact X. }
  destruct (live_msa (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) maps WF) as [E _]. rewrite E.
  apply sum_count_ext. intros x. unfold Pm. rewrite EM, EL. reflexivity.
Qed.

Lemma START_main : START RESV0 ATOP maps (vm_reserved (m_vmmaps mo)) sta.
Proof.
  unfold START. cbn [st0 ainit a_space_beg a_ptr_array]. pose proof (ao_space L ALO) as SP. pose proof (ao_res_hi L ALO) as RH. pose proof (ao_res L ALO) as (_ & _ & R3 & _).
  pose proof (ao_ptr L ALO) as (P1 & P2 & P3 & P4 & P5). revert SP RH R3. rewrite al_res_eq. intros SP RH R3.
  unfold al_ptr_array in *. cbn [al_V L0 VL] in *. pose proof atop_range as AR.
  split. { exists (4096 * V 208%nat). unfold PRIM_SZ, KHIGH. split; [apply maps_In_known; cbn; tauto| lia]. }
  split; [apply maps_In_known; cbn; tauto|]. split; [unfold PTR_SZ; lia|].
  split. { rewrite (MA.am_reserved V sp fs mo AMO), segments_reserved_asan. unfold PTR_SZ.
           apply (region_free_above _ _ _ 0x62f000); [| unfold iclr, AIMG_LO, AIMG_HI in P5; lia| lia| lia| lia].
           repeat (apply Forall_cons; [cbn [fst snd]; rewrite !unsigned_lit by lia; lia|]). apply Forall_nil. }
  split; [apply maps_In_known; cbn; tauto|]. split; [apply maps_In_known; cbn; tauto|]. split; [apply maps_In_known; cbn; tauto|].
  destruct maps_shape as (fog & FL & FS & EQ).
  split. { rewrite EQ. unfold zlen, LEN0. rewrite !length_app. cbn [length KNOWN_hi KNOWN_lo]. lia. }
  split. { pose proof (MA.am_totsz V sp fs mo AMO) as T. unfold MF.asan_totsz in T. unfold TOT0.
           assert (LE : forall l1 l2, live_bytes l2 <= ME.ivs_sum (l1 ++ l2)).
           { intros l1 l2. induction l1 as [|iv l1 IH]; cbn.
             - induction l2 as [|[a b] l2 IH2]; cbn; [lia|]. lia.
             - pose proof (bv_unsigned_in_range _ (snd iv)). lia. }
           pose proof (LE (vm_reserved (m_vmmaps mo)) maps). lia. }
  unfold RESV0. unfold LS_LO, LS_SZ, GAP_LO, GAP_SZ, HS_LO, HS_SZ.
  rewrite (MA.am_reserved V sp fs mo AMO), segments_reserved_asan.
  hpf 12%nat B78. hpf 13%nat B207. hpf 14%nat B208. hpf 16%nat B226. hpf 17%nat B227. hpf 18%nat B228.
  hpf 19%nat B245. hpf 20%nat B310. hpf 24%nat B377. hpf 32%nat B453. hpf 33%nat B454. hpf 34%nat B471.
  set (R4 := [(Z_to_bv 64 65536, Z_to_bv 64 176128); (Z_to_bv 64 241664, Z_to_bv 64 598016); (Z_to_bv 64 839680, Z_to_bv 64 24576); (Z_to_bv 64 864256, Z_to_bv 64 5619712)]).
  assert (KB : forall b n lo hi, In (wE b n) maps -> 0 <= b -> 0 <= n -> b + n < 2 ^ 64 -> b <= lo -> hi <= b + n -> rcov (R4 ++ maps) (lo, hi)).
  { intros b n lo hi Hin Hb Hn Hbn H1 H2. exists (wE b n). split; [apply in_or_app; right; exact Hin|]. unfold wE. cbn [fst snd]. rewrite !wa_unsigned by lia. lia. }
  assert (KR : forall b n lo hi, In (Z_to_bv 64 b, Z_to_bv 64 n) R4 -> 0 <= b < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> b <= lo -> hi <= b + n -> rcov (R4 ++ maps) (lo, hi)).
  { intros b n lo hi Hin Hb Hn H1 H2. exists (Z_to_bv 64 b, Z_to_bv 64 n). split; [apply in_or_app; left; exact Hin|]. cbn [fst snd]. rewrite !unsigned_lit by lia. lia. }

  apply Forall_cons; [apply (KR 65536 176128); [unfold R4; cbn; tauto| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KR 241664 598016); [unfold R4; cbn; tauto| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KR 839680 24576); [unfold R4; cbn; tauto| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KR 864256 5619712); [unfold R4; cbn; tauto| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB 2147446784 268435456); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB 2415882240 2199023255552); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB 2201439137792 15392894357504); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 208%nat) 137439023104); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 226%nat) 8388608); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 227%nat) 4096); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 228%nat) 65536); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 453%nat) 1048576); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 454%nat) 8388608); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 377%nat) 11571200); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 310%nat) 4096); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 78%nat) 65536); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 207%nat) 3727360); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 245%nat) 4096); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 471%nat) 4096); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_nil.
Qed.

Lemma covered_in_ivs : forall l x, covered l x = true <-> ME.in_ivs x l.
Proof.
  intros l x. unfold covered, ME.in_ivs. rewrite existsb_exists. unfold in_iv, in_rng, B, S. split.
  - intros (iv & Hin & H). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists iv. split; [exact Hin| lia].
  - intros (iv & Hin & H). exists iv. split; [exact Hin|]. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

Lemma AMI_main : AMI RESV0 ATOP [] sta (canon mo).
Proof.
  unfold AMI, canon. rewrite !m_vmmaps_MX, !m_vm_lazy_MX, m_vm_materialized_MX. pose proof atop_range as AR. pose proof (bv_unsigned_in_range _ sp) as SPR.
  split; [reflexivity|].
  split; [rewrite (MA.am_limit V sp fs mo AMO); reflexivity|].
  split. { rewrite (MA.am_reserved V sp fs mo AMO), segments_reserved_asan. unfold RES_HI. repeat (apply Forall_cons; [cbn [fst snd]; rewrite !unsigned_lit by lia; lia|]). apply Forall_nil. }
  split. { rewrite (MA.am_reserved V sp fs mo AMO), segments_reserved_asan. unfold zlen, LEN0. cbn [length Z.of_nat]. lia. }
  split. { rewrite (MA.am_reserved V sp fs mo AMO), segments_reserved_asan. unfold RTOT0. cbn [live_bytes]. rewrite !unsigned_lit by lia. lia. }
  split. { eapply Forall_impl; [| exact (MA.am_bounds V sp fs mo AMO)]. cbn. intros iv (B1 & B2 & B3 & B4 & B5 & B6). unfold entry_ok. rewrite USP in B6. lia. }
  split. { split; [| exact noacc_sep_main]. apply (ivs_wf_of_bound _ (2 ^ 64)); [exact (MA.am_noaccess_wf V sp fs mo AMO)| lia]. }
  split. { apply (ivs_wf_of_bound _ (bv_unsigned sp - 8388608)); [| lia]. eapply Forall_impl; [| exact (MA.am_lazy_bounds V sp fs mo AMO)]. cbn. intros iv [_ X]. exact X. }
  split. { split; [apply seps_of_ivs_sep; exact (MA.am_sep V sp fs mo AMO)|].
           unfold rsep. eapply Forall_impl; [| exact (MA.am_bounds V sp fs mo AMO)]. cbn. intros iv (B1 & B2 & B3 & B4 & B5 & B6).
           rewrite (MA.am_reserved V sp fs mo AMO), segments_reserved_asan. unfold MA.AIMG_LO, MA.AIMG_HI in B5.
           repeat (apply Forall_cons; [cbn [fst snd]; rewrite !unsigned_lit by lia; lia|]). apply Forall_nil. }
  split. { split; [unfold atop_ok, ACEIL, AsanInv.ATOP_MAX; lia|]. unfold alloc_top. rewrite (MA.am_top V sp fs mo AMO). unfold stack_max_size. lia. }
  exists maps. split; [rewrite app_nil_r; apply Permutation_refl|]. split; [exact START_main|].
  split. { rewrite commit_bytes_st0, (sum_count_Pm (MX mo [])) by reflexivity. pose proof (MA.am_nonlazy V sp fs mo AMO) as NL. unfold MF.asan_eager in NL. unfold EAGER0. lia. }
  intros x Hx. split.
  - apply (proj2 (covered_in_ivs _ _)). apply LZSUB. apply (proj1 (covered_in_ivs _ _)). exact Hx.
  - intros (c & Hc & R). rewrite get_cls_st0 in R. cbn [c_mapped_user aclass0] in R. lia.
Qed.

Theorem INV_main : INV RESV0 ATOP [] [] sta (canon mo).
Proof. split; [exact AINV_main|]. rewrite CHX_st0. exact AMI_main. Qed.

Lemma pagedown_spec : forall z, ME.pagedown z <= z < ME.pagedown z + 4096 /\ ME.pagedown z mod 4096 = 0.
Proof. intros z. unfold ME.pagedown. Z.div_mod_to_equations. lia. Qed.
Lemma pageup_spec : forall z, z <= ME.pageup z < z + 4096 /\ ME.pageup z mod 4096 = 0.
Proof. intros z. unfold ME.pageup. Z.div_mod_to_equations. lia. Qed.
Lemma page_base_of_val : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (page_base_of z) = ME.pagedown z.
Proof.
  intros z Hz. unfold page_base_of, page_size, ME.pagedown. pose proof (pagedown_spec z) as [P _]. unfold ME.pagedown in P.
  rewrite unsigned_lit by lia. reflexivity.
Qed.

Definition appz_e (e : word * word) : bool := (B e + S e <=? LS_LO) || (KHIGH <=? B e).
Definition shiv (e : word * word) : Z * Z := (ME.pagedown (shad (B e)), ME.pageup (shad (B e + S e))).
Definition ALV : list (Z * Z) := ME.allow_of MA.ASHOFF V MF.asan_vis.
Definition ALC : list (Z * Z) := map shiv (List.filter appz_e maps).
Definition AL0 : list (Z * Z) := ALV ++ ALC.
Definition A0 : alw := fun p => (bv_unsigned p mod 4096 = 0 /\ ME.aallowed AL0 p) \/ SHFIX p.
Definition RNG0 : footprint := fp_ok (m_vm_lazy mo) A0.

Lemma aallowed_app_l : forall l1 l2 p, ME.aallowed l1 p -> ME.aallowed (l1 ++ l2) p.
Proof. intros l1 l2 p (iv & Hin & H). exists iv. split; [apply in_or_app; left; exact Hin| exact H]. Qed.
Lemma aallowed_app_r : forall l1 l2 p, ME.aallowed l2 p -> ME.aallowed (l1 ++ l2) p.
Proof. intros l1 l2 p (iv & Hin & H). exists iv. split; [apply in_or_app; right; exact Hin| exact H]. Qed.

Lemma maps_sep2 : forall p q, In p maps -> In q maps -> p = q \/ wsep p q.
Proof.
  intros p q Hp Hq. apply In_nth_error in Hp as [i Hi]. apply In_nth_error in Hq as [j Hj].
  pose proof (MA.am_sep V sp fs mo AMO) as SEP.
  destruct (lt_eq_lt_dec i j) as [[LT|EQ]|GT].
  - right. exact (SEP i j p q LT Hi Hj).
  - left. subst j. rewrite Hi in Hj. injection Hj as E. exact E.
  - right. pose proof (SEP j i q p GT Hj Hi) as X. unfold wsep in *. lia.
Qed.

Lemma appz_entry : forall e x, In e maps -> B e <= x < B e + S e -> appz x -> appz_e e = true.
Proof.
  intros e x He Hx AP. unfold appz_e. unfold appz in AP. apply orb_true_intro.
  assert (INLS : In (wE LS_LO LS_SZ) maps) by (apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE, LS_LO, LS_SZ; cbn [In app]; tauto).
  assert (INHS : In (wE HS_LO HS_SZ) maps) by (apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE, HS_LO, HS_SZ; cbn [In app]; tauto).
  unfold LS_LO, LS_SZ, HS_LO, HS_SZ, KHIGH in *. unfold B, S in *.
  destruct AP as [AP|AP].
  - left. apply Z.leb_le. destruct (maps_sep2 e _ He INLS) as [->|W].
    + exfalso. unfold wE in Hx. cbn [fst snd] in Hx. rewrite !wa_unsigned in Hx by lia. lia.
    + unfold wsep, wE in W. cbn [fst snd] in W. rewrite !wa_unsigned in W by lia. lia.
  - right. apply Z.leb_le. destruct (maps_sep2 e _ He INHS) as [->|W].
    + exfalso. unfold wE in Hx. cbn [fst snd] in Hx. rewrite !wa_unsigned in Hx by lia. lia.
    + unfold wsep, wE in W. cbn [fst snd] in W. rewrite !wa_unsigned in W by lia. lia.
Qed.

Lemma ALC_page : forall e z', In e maps -> appz_e e = true -> shad (B e) <= z' < shad (B e + S e) -> 0 <= z' < 2 ^ 64 -> A0 (page_base_of z').
Proof.
  intros e z' He AE Hz R. left. rewrite page_base_of_val by exact R. pose proof (pagedown_spec z') as [P1 P2]. split; [exact P2|].
  apply aallowed_app_r. exists (shiv e). split; [apply in_map_iff; exists e; split; [reflexivity| apply filter_In; split; [exact He| exact AE]]|].
  unfold shiv. cbn [fst snd]. rewrite page_base_of_val by exact R. pose proof (pagedown_spec (shad (B e))) as [Q1 _]. pose proof (pageup_spec (shad (B e + S e))) as [Q2 _].
  unfold ME.pagedown, ME.pageup in *. clear -Hz Q1 Q2 P1. Z.div_mod_to_equations. lia.
Qed.

Lemma A0_base : alw_le (Abase_x SHFIX (al_space_beg L) (al_ptr_array L)) A0.
Proof.
  intros p [AB|AF]; [| right; exact AF]. destruct AB as (z' & Hz & ->).
  pose proof (ao_space L ALO) as SP. pose proof (ao_res_hi L ALO) as RH. pose proof (ao_res L ALO) as (_ & _ & R3 & R4 & _). pose proof (ao_ptr L ALO) as (P1 & P2 & P3 & P4 & P5).
  revert SP RH R3 R4. rewrite al_res_eq. intros SP RH R3 R4. unfold al_ptr_array in *. cbn [al_V L0 VL] in *. pose proof atop_range as AR.
  unfold K_SPACE_SIZE, K_PTRARR_RESERVE in Hz. rewrite !shad_div in Hz. unfold ASHOFF in Hz.
  destruct Hz as [Hz|Hz].
  - apply (ALC_page (wE (4096 * V 208%nat) 137439023104)).
    + apply maps_In_known; unfold KNOWN_hi, KNOWN_lo; cbn [In app]; tauto.
    + unfold appz_e, B, S, wE. cbn [fst snd]. rewrite !wa_unsigned by lia. apply orb_true_intro. right. apply Z.leb_le. unfold KHIGH. lia.
    + unfold B, S, wE. cbn [fst snd]. rewrite !wa_unsigned by lia. rewrite !shad_div. unfold ASHOFF. clear -Hz SP. Z.div_mod_to_equations. lia.
    + clear -Hz SP RH R3 AR. Z.div_mod_to_equations. lia.
  - apply (ALC_page (wE (4096 * V 226%nat) 8388608)).
    + apply maps_In_known; unfold KNOWN_hi, KNOWN_lo; cbn [In app]; tauto.
    + unfold appz_e, B, S, wE. cbn [fst snd]. rewrite !wa_unsigned by lia. unfold sclr in P4. unfold LS_LO, KHIGH, KLS in *.
      apply orb_true_intro. destruct P4 as [P4|P4]; [left| right]; apply Z.leb_le; lia.
    + unfold B, S, wE. cbn [fst snd]. rewrite !wa_unsigned by lia. rewrite !shad_div. unfold ASHOFF. clear -Hz. Z.div_mod_to_equations. lia.
    + clear -Hz P2 P3 AR. Z.div_mod_to_equations. lia.
Qed.

Lemma A0_covp : forall p, COVP (canon mo) p -> A0 p.
Proof.
  intros p (e & x & He & Hx & AP & ->). unfold canon in He. rewrite m_vmmaps_MX in He.
  pose proof (proj1 (Forall_forall _ _) (MA.am_bounds V sp fs mo AMO) e He) as (B1 & B2 & B3 & B4 & B5 & B6).
  assert (SPR : 0 <= bv_unsigned sp < 2 ^ 64) by exact (bv_unsigned_in_range 64 sp).
  apply (ALC_page e); [exact He| exact (appz_entry e x He Hx AP)| |]; unfold B, S in *; rewrite !shad_div; unfold ASHOFF; clear -Hx B2 B3 B4 B6 SPR; Z.div_mod_to_equations; lia.
Qed.

Lemma A0_mat : forall p, In p (m_vm_materialized mo) -> A0 p.
Proof.
  intros p Hp. destruct (MA.am_mat V sp fs mo AMO p Hp) as (M1 & _ & M3). left. split; [exact M1|]. apply aallowed_app_l. exact M3.
Qed.

Lemma ALC_wf : ME.ivz_wf ALC.
Proof.
  unfold ME.ivz_wf, ALC. apply Forall_forall. intros iv Hin. apply in_map_iff in Hin as (e & <- & He). unfold shiv. cbn [fst snd].
  pose proof (pagedown_spec (shad (B e))) as [P1 P2]. pose proof (pageup_spec (shad (B e + S e))) as [Q1 Q2].
  split; [| split; [exact P2| exact Q2]]. pose proof (S_range e). rewrite !shad_div in *. Z.div_mod_to_equations. lia.
Qed.
Lemma AL0_wf : ME.ivz_wf AL0.
Proof. unfold AL0, ME.ivz_wf. apply Forall_app. split; [exact (MA.am_allow_wf V sp fs mo AMO)| exact ALC_wf]. Qed.

Definition shc (e : word * word) : Z := S e / 8 + 8192.
Fixpoint sum_shc (l : list (word * word)) : Z := match l with [] => 0 | e :: l' => shc e + sum_shc l' end.
Lemma shc_nonneg : forall e, 0 <= shc e. Proof. intros e. unfold shc. pose proof (S_range e). Z.div_mod_to_equations. lia. Qed.
Lemma sum_shc_app : forall l1 l2, sum_shc (l1 ++ l2) = sum_shc l1 + sum_shc l2.
Proof. induction l1 as [|e l1 IH]; intros l2; cbn; [lia| rewrite IH; lia]. Qed.
Lemma sum_shc_filter : forall f l, sum_shc (List.filter f l) <= sum_shc l.
Proof. induction l as [|e l IH]; cbn; [lia|]. pose proof (shc_nonneg e). destruct (f e); cbn; lia. Qed.
Lemma ivz_shiv : forall l, ME.ivz_bytes (map shiv l) <= sum_shc l.
Proof.
  induction l as [|e l IH]; [cbn; lia|].
  change (ME.ivz_bytes (map shiv (e :: l))) with ((ME.pageup (shad (B e + S e)) - ME.pagedown (shad (B e))) + ME.ivz_bytes (map shiv l)).
  cbn [sum_shc]. unfold shc at 1.
  pose proof (pagedown_spec (shad (B e))) as [P1 _]. pose proof (pageup_spec (shad (B e + S e))) as [Q1 _].
  pose proof (S_range e) as SR. pose proof (B_range e) as BR. rewrite !shad_div in *. unfold ASHOFF in *.
  assert ((B e + S e) / 8 - B e / 8 <= S e / 8 + 1) by (clear -SR BR; Z.div_mod_to_equations; lia). lia.
Qed.
Lemma filter_app' : forall {X} (f : X -> bool) l1 l2, List.filter f (l1 ++ l2) = List.filter f l1 ++ List.filter f l2.
Proof. intros X f l1 l2. induction l1 as [|x l1 IH]; cbn; [reflexivity|]. rewrite IH. destruct (f x); reflexivity. Qed.

Lemma ALC_bytes : ME.ivz_bytes ALC <= 17184153600.
Proof.
  unfold ALC. pose proof (ivz_shiv (List.filter appz_e maps)) as IV. eapply Z.le_trans; [exact IV|].
  destruct maps_shape as (fog & FL & FS & EQ). rewrite EQ. rewrite !filter_app', !sum_shc_app.
  hpf 14%nat B208. hpf 16%nat B226. hpf 17%nat B227. hpf 18%nat B228. hpf 32%nat B453. hpf 33%nat B454.
  hpf 24%nat B377. hpf 20%nat B310. hpf 12%nat B78. hpf 13%nat B207. hpf 19%nat B245. hpf 34%nat B471.
  assert (F1 : sum_shc (List.filter appz_e KNOWN_hi) <= 1204736).
  { eapply Z.le_trans; [apply sum_shc_filter|]. unfold KNOWN_hi. cbn [sum_shc]. unfold shc, S, wE. cbn [snd]. rewrite !wa_unsigned by lia.
    apply Z.leb_le. vm_compute. reflexivity. }
  assert (F2 : sum_shc (List.filter appz_e fog) <= 18432).
  { eapply Z.le_trans; [apply sum_shc_filter|]. destruct fog as [|f1 [|f2 [|f3 fog]]]; cbn [length] in FL; [cbn; lia| | | lia].
    - pose proof (Forall_inv FS) as S1. cbn [sum_shc]. unfold shc, S in *. clear -S1. Z.div_mod_to_equations. lia.
    - pose proof (Forall_inv FS) as S1. pose proof (Forall_inv (Forall_inv_tail FS)) as S2. cbn [sum_shc]. unfold shc, S in *. clear -S1 S2. Z.div_mod_to_equations. lia. }
  assert (F3 : sum_shc (List.filter appz_e KNOWN_lo) <= 17182930432).
  { unfold KNOWN_lo.
    change ([wE (4096 * V 377%nat) 11571200; wE (4096 * V 310%nat) 4096; wE (4096 * V 245%nat) 4096; wE (4096 * V 228%nat) 65536;
             wE (4096 * V 227%nat) 4096; wE (4096 * V 226%nat) 8388608; wE (4096 * V 208%nat) 137439023104; wE (4096 * V 207%nat) 3727360;
             wE (4096 * V 78%nat) 65536; wE 2201439137792 15392894357504; wE 2415882240 2199023255552; wE 2147446784 268435456])
      with ([wE (4096 * V 377%nat) 11571200; wE (4096 * V 310%nat) 4096; wE (4096 * V 245%nat) 4096; wE (4096 * V 228%nat) 65536;
             wE (4096 * V 227%nat) 4096; wE (4096 * V 226%nat) 8388608; wE (4096 * V 208%nat) 137439023104; wE (4096 * V 207%nat) 3727360;
             wE (4096 * V 78%nat) 65536] ++ [wE 2201439137792 15392894357504; wE 2415882240 2199023255552; wE 2147446784 268435456]).
    rewrite filter_app', sum_shc_app.
    replace (List.filter appz_e [wE 2201439137792 15392894357504; wE 2415882240 2199023255552; wE 2147446784 268435456]) with (@nil (word * word)) by (vm_compute; reflexivity).
    cbn [sum_shc]. eapply Z.le_trans; [apply Z.add_le_mono_r; apply sum_shc_filter|]. cbn [sum_shc]. unfold shc, S, wE. cbn [snd]. rewrite !wa_unsigned by lia.
    apply Z.leb_le. vm_compute. reflexivity. }
  lia.
Qed.

Lemma A0_bud : abud A0 (4796178 + KSH).
Proof.
  destruct (ME.aallowed_fin AL0 AL0_wf) as (L1 & N1 & LEN1 & IN1). destruct SHFIX_fin as (L2 & N2 & LEN2 & IN2).
  destruct (nodup_extend L1 L2 N1) as (L3 & N3 & LEN3 & IN3).
  exists L3. split; [exact N3|]. split.
  - assert (BY : ME.ivz_bytes AL0 <= 2460986368 + 17184153600).
    { unfold AL0. assert (E : forall a b, ME.ivz_bytes (a ++ b) = ME.ivz_bytes a + ME.ivz_bytes b) by (intros a b; induction a as [|iv a IH]; cbn; [lia| rewrite IH; lia]).
      rewrite E. pose proof (MA.am_abytes V sp fs mo AMO) as AB. unfold MF.asan_abytes in AB. fold ALV in AB. pose proof ALC_bytes. unfold ALV in *. lia. }
    assert (ME.ivz_bytes AL0 / 4096 <= 4796178) by (Z.div_mod_to_equations; lia). lia.
  - intros p [[M A]|F]; apply IN3; [left; exact (IN1 p M A)| right; exact (IN2 p F)].
Qed.

Lemma lazy_above : forall z, ATOP <= z -> 0 <= z < 2 ^ 64 -> page_in_ranges (page_base_of z) (m_vm_lazy mo) = false.
Proof.
  intros z Hz R. pose proof (MA.am_lazy_bounds V sp fs mo AMO) as LB.
  destruct (page_in_ranges (page_base_of z) (m_vm_lazy mo)) eqn:E; [| reflexivity]. exfalso.
  unfold page_in_ranges in E. apply existsb_exists in E as (iv & Hin & T). apply andb_prop in T as [T1 T2]. apply Z.leb_le in T1. apply Z.leb_le in T2.
  rewrite page_base_of_val in T1, T2 by exact R. pose proof (pagedown_spec z) as [P _]. unfold page_size in T2.
  pose proof (proj1 (Forall_forall _ _) LB iv Hin) as [_ X]. cbn in X. rewrite USP in X. lia.
Qed.
Lemma lazy_image : forall z, 0x10000 <= z < 0x62f000 -> page_in_ranges (page_base_of z) (m_vm_lazy mo) = false.
Proof.
  intros z Hz. pose proof (MA.am_lazy_bounds V sp fs mo AMO) as LB.
  destruct (page_in_ranges (page_base_of z) (m_vm_lazy mo)) eqn:E; [| reflexivity]. exfalso.
  unfold page_in_ranges in E. apply existsb_exists in E as (iv & Hin & T). apply andb_prop in T as [T1 T2]. apply Z.leb_le in T1. apply Z.leb_le in T2.
  rewrite page_base_of_val in T1, T2 by lia. pose proof (pagedown_spec z) as [P PM]. unfold page_size in T2.
  pose proof (proj1 (Forall_forall _ _) LB iv Hin) as [X _]. cbn in X. unfold MA.AIMG_LO, MA.AIMG_HI in X. unfold ME.pagedown in *.
  clear -Hz T1 T2 P PM X. Z.div_mod_to_equations. lia.
Qed.

Lemma ALV_page : forall bn z, In bn MF.asan_vis ->
  (ME.pagedown (ME.zv V (fst bn)) <= z < ME.pageup (ME.zv V (fst bn) + ME.zv V (snd bn))
   \/ ME.pagedown (MA.ASHOFF + ME.zv V (fst bn) / 8) <= z < ME.pageup (MA.ASHOFF + (ME.zv V (fst bn) + ME.zv V (snd bn)) / 8)) ->
  0 <= z < 2 ^ 64 -> A0 (page_base_of z).
Proof.
  intros bn z Hin Hz R. left. rewrite page_base_of_val by exact R. pose proof (pagedown_spec z) as [P1 P2]. split; [exact P2|].
  apply aallowed_app_l. unfold ALV, ME.allow_of. set (b := ME.zv V (fst bn)) in *. set (n := ME.zv V (snd bn)) in *.
  destruct Hz as [Hz|Hz].
  - exists (ME.pagedown b, ME.pageup (b + n)). split.
    + apply in_flat_map. exists bn. split; [exact Hin|]. cbn. left. reflexivity.
    + cbn [fst snd]. rewrite page_base_of_val by exact R. pose proof (pagedown_spec b) as [Q1 Q1m]. pose proof (pageup_spec (b + n)) as [Q2 Q2m].
      set (u := ME.pagedown b) in *. set (v := ME.pageup (b + n)) in *. clearbody u v. unfold ME.pagedown in *.
      clear -Hz P1 Q1m Q2m. Z.div_mod_to_equations. lia.
  - exists (ME.pagedown (MA.ASHOFF + b / 8), ME.pageup (MA.ASHOFF + (b + n) / 8)). split.
    + apply in_flat_map. exists bn. split; [exact Hin|]. cbn. right. left. reflexivity.
    + cbn [fst snd]. rewrite page_base_of_val by exact R. pose proof (pagedown_spec (MA.ASHOFF + b / 8)) as [Q1 Q1m]. pose proof (pageup_spec (MA.ASHOFF + (b + n) / 8)) as [Q2 Q2m].
      set (u := ME.pagedown (MA.ASHOFF + b / 8)) in *. set (v := ME.pageup (MA.ASHOFF + (b + n) / 8)) in *. clearbody u v. unfold ME.pagedown in *.
      clear -Hz P1 Q1m Q2m. Z.div_mod_to_equations. lia.
Qed.

Lemma vis_in : forall bn, In bn MF.asan_vis_app -> In bn MF.asan_vis.
Proof. intros bn H. unfold MF.asan_vis. apply in_or_app. left. exact H. Qed.
Local Ltac visk k := apply vis_in; unfold MF.asan_vis_app; apply (nth_error_In _ k); reflexivity.

Lemma rng0_of : forall lo n, 0 <= lo -> lo + n <= 2 ^ 64 -> (forall z, lo <= z < lo + n -> page_ok (m_vm_lazy mo) A0 (page_base_of z)) -> rng RNG0 lo n.
Proof. intros lo n H1 H2 H3. unfold RNG0. apply rng_fp_ok; assumption. Qed.

Lemma rng0_visp : forall k bn lo n, nth_error MF.asan_vis_app k = Some bn ->
  ((ME.pagedown (ME.zv V (fst bn)) <= lo /\ lo + n <= ME.pageup (ME.zv V (fst bn) + ME.zv V (snd bn)))
   \/ (ME.pagedown (MA.ASHOFF + ME.zv V (fst bn) / 8) <= lo /\ lo + n <= ME.pageup (MA.ASHOFF + (ME.zv V (fst bn) + ME.zv V (snd bn)) / 8))) ->
  0 <= lo -> lo + n <= 2 ^ 64 -> rng RNG0 lo n.
Proof.
  intros k bn lo n Hk Hr H1 H2. apply rng0_of; [exact H1| exact H2|]. intros z Hz. right.
  apply (ALV_page bn); [apply vis_in; exact (nth_error_In _ k Hk)| | lia]. destruct Hr as [[A1 A2]|[A1 A2]]; [left| right]; lia.
Qed.
Lemma rng0_vis : forall k bn lo n, nth_error MF.asan_vis_app k = Some bn ->
  ((ME.zv V (fst bn) <= lo /\ lo + n <= ME.zv V (fst bn) + ME.zv V (snd bn)) \/ (MA.ASHOFF + ME.zv V (fst bn) / 8 <= lo /\ lo + n <= MA.ASHOFF + (ME.zv V (fst bn) + ME.zv V (snd bn)) / 8)) ->
  0 <= lo -> lo + n <= 2 ^ 64 -> rng RNG0 lo n.
Proof.
  intros k bn lo n Hk Hr H1 H2. apply (rng0_visp k bn lo n Hk); [| exact H1| exact H2].
  pose proof (pagedown_spec (ME.zv V (fst bn))) as [P1 _]. pose proof (pageup_spec (ME.zv V (fst bn) + ME.zv V (snd bn))) as [P2 _].
  pose proof (pagedown_spec (MA.ASHOFF + ME.zv V (fst bn) / 8)) as [P3 _]. pose proof (pageup_spec (MA.ASHOFF + (ME.zv V (fst bn) + ME.zv V (snd bn)) / 8)) as [P4 _].
  destruct Hr as [[A1 A2]|[A1 A2]]; [left| right]; lia.
Qed.

Theorem FPX_main : FPX L RNG0.
Proof.
  unfold FPX. pose proof atop_range as AR. pose proof (ao_fake L ALO) as (F1 & F2 & F3 & _). pose proof (ao_dtls L ALO) as (D1 & D2 & D3 & _).
  revert F1 F2 F3 D1 D2 D3. rewrite al_fake_eq. unfold al_dtls. cbn [al_V L0 VL]. intros F1 F2 F3 D1 D2 D3.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 10%nat) as B10. pose proof (HV 6%nat) as B6.
  split. { apply rng0_of; [lia| lia|]. intros z Hz. left. apply lazy_above; lia. }
  split. { apply rng0_of; [lia| lia|]. intros z Hz. left. apply lazy_image; lia. }
  split. { apply (rng0_visp 11 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [right; split; apply Z.leb_le; vm_compute; reflexivity| lia| lia]. }
  split. { rewrite shad_div. unfold ASHOFF, Shadow.KHIGH. apply (rng0_vis 12 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [right| |]; clear -AR HU0 B0 B10 B6; Z.div_mod_to_equations; lia. }
  unfold afake_rng. rewrite al_fake_eq. unfold al_dtls, FAKESZ, shlen. cbn [al_V L0 VL]. rewrite shad_div, Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2 ^ 3) with 8.
  split. { apply (rng0_vis 3 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia]. }
  split. { apply (rng0_vis 3 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [right| |]; clear -F1 F2 F3 AR; Z.div_mod_to_equations; lia. }
  apply (rng0_vis 4 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia].
Qed.

Theorem arng0_main : arng0 L RNG0.
Proof.
  unfold arng0. pose proof atop_range as AR.
  pose proof (ao_t L ALO) as (T1 & T2 & T3 & _). pose proof (ao_ctx L ALO) as (C1 & C2 & C3 & _). pose proof (ao_nodes L ALO) as (N1 & N2 & N3 & _).
  pose proof (ao_store L ALO) as (ST1 & ST2 & ST3 & _). pose proof (ao_fake L ALO) as (F1 & F2 & F3 & _). pose proof (ao_dtls L ALO) as (D1 & D2 & D3 & _).
  pose proof (ao_space L ALO) as SP. pose proof (ao_res_hi L ALO) as RH. pose proof (ao_res L ALO) as (_ & _ & R3 & _).
  revert T1 T2 T3 C1 C2 C3 N1 N2 N3 ST1 ST2 ST3 F1 F2 F3 D1 D2 D3 SP RH R3.
  rewrite al_t_eq, al_ctx_eq, al_nodes_eq, al_store_eq, al_fake_eq, al_res_eq, al_space_beg_eq. unfold al_dtls. cbn [al_V L0 VL]. intros.
  unfold K_SPACE_SIZE, K_SPACE_EXTRA, shlen. rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2 ^ 3) with 8. change (2 ^ 37) with 137438953472.
  split. { apply rng0_of; [lia| lia|]. intros z Hz. left. apply lazy_image; lia. }
  split. { apply (rng0_vis 7 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia]. }
  split. { apply (rng0_vis 6 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia]. }
  split. { apply (rng0_vis 2 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia]. }
  split. { apply (rng0_vis 1 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia]. }
  split. { apply (rng0_vis 8 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia]. }
  split. { apply (rng0_vis 3 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia]. }
  split. { apply (rng0_vis 3 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [right| |]; clear -F1 F2 F3 AR; Z.div_mod_to_equations; lia. }
  split. { apply (rng0_vis 4 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia]. }

  apply rng0_of; [clear -SP RH; Z.div_mod_to_equations; lia| clear -SP RH R3 AR; Z.div_mod_to_equations; lia|].
  intros z Hz. right. apply A0_base. left. exists z. split; [| reflexivity]. left.
  rewrite al_space_beg_eq. unfold al_ptr_array, K_SPACE_SIZE. rewrite !shad_div. unfold ASHOFF. change (2 ^ 37) with 137438953472.
  clear -Hz SP RH. Z.div_mod_to_equations. lia.
Qed.

Theorem lazy_shape_main : forall z, (0x10000 <= z < ABase.AIMG_HI \/ ATOP <= z < 2 ^ 64) -> page_in_ranges (page_base_of z) (m_vm_lazy mo) = false.
Proof.
  intros z [Hz|Hz]; [apply lazy_image; unfold ABase.AIMG_HI in Hz; lia| apply lazy_above; [lia| pose proof atop_range; lia]].
Qed.

Theorem FIXZ_main : FIXZ L (canon mo).
Proof.
  unfold FIXZ, canon. rewrite m_vmmaps_MX, m_vm_lazy_MX, m_halted_MX. split; [| split; [| split]].
  - rewrite (MA.am_reserved V sp fs mo AMO), segments_reserved_asan. unfold ABase.AIMG_HI.
    repeat (apply Forall_cons; [cbn [fst snd]; rewrite !unsigned_lit by lia; lia|]). apply Forall_nil.
  - intros z Hz. apply FKEAGER. rewrite al_fake_eq in Hz. exact Hz.
  - exact (MA.am_halted V sp fs mo AMO).
  - intros z Hz. rewrite m_vm_lazy_MX. apply lazy_shape_main. unfold C0A in Hz. exact Hz.
Qed.

Theorem ACCT_root : forall aw, bv_unsigned aw <= CRED0 -> ACCT NMAX SHFIX aw L RNG0 sta [] mo.
Proof.
  intros aw Haw. pose proof (bv_unsigned_in_range _ aw) as AWR.
  exists RESV0, A0. split; [exact aresv_ok_main|].
  split.
  { unfold ACCTc. split; [exact INV_main|]. cbn [st0 ainit a_qloc_bytes a_qglob_bytes]. unfold Q_CACHE, Q_MAX.
    split; [lia|]. split; [lia|]. split; [unfold RNG0, canon; rewrite m_vm_lazy_MX; reflexivity|]. split; [lia|].
    split. { rewrite live_chunks_st0. unfold emb_sz. cbn [secbytes st0 ainit a_emb snd]. unfold C_EXH. lia. }
    exists (4796178 + KSH). split; [exact A0_base|]. split; [exact A0_covp|]. split; [exact A0_bud|]. split; [lia|].
    unfold GP, emb_cap, PEMB, pcost, EMB_MAX. cbn [st0 ainit a_emb fst snd]. unfold CRED0 in Haw.
    change (2 ^ 23 / 4096 + 2 ^ 23 / 32768 + 4) with 2308. change ((2 ^ 23 - 0) / 4096) with 2048. lia. }
  split; [exact (MA.am_mat_nodup V sp fs mo AMO)|]. split; [exact A0_mat|]. split; [exact FPX_main|]. split; [exact FIXZ_main|].
  intros id ch H. cbn [st0 ainit a_live] in H. rewrite lookup_empty in H. discriminate H.
Qed.

End Root.

Theorem h0_at_main {rc : runConstT} :
  forall (UNIV : list (list Z)) (SHFIX : word -> Prop) (KSH : Z) (NMAX : nat) (en : ExecEntry) (inp : ProcInput) (ms : machine_state) (mo : Model) (aw : word),
  univ_ok UNIV -> abud SHFIX KSH -> 0 <= KSH -> 59854610 + KSH <= Z.of_nat NMAX ->
  MA.amain_at en inp ms mo -> bv_unsigned (en_sp en) = ATOP + 8388608 ->
  bv_unsigned aw <= CRED0 ->
  exists (Lm : alayout) (RNG : footprint) (sta : astate),
       AInstanceU2.AHEAPu2 Lm RNG sta [] (ms_mem ms)
    /\ ACCT NMAX SHFIX aw Lm RNG sta [] mo
    /\ incl UNIV (al_U Lm)
    /\ (forall z, (0x10000 <= z < ABase.AIMG_HI \/ ATOP <= z < 2 ^ 64) -> page_in_ranges (page_base_of z) (m_vm_lazy mo) = false)
    /\ APristLaw.aprist sta.
Proof.
  intros UNIV SHFIX KSH NMAX en inp ms mo aw HU HSH HK HN HM USP Haw.
  destruct HM as (w & V & m & Hms & HV & PIN & HMFall & HPFall & MINV & STK & HID & SH0 & AMO).
  destruct PIN as (_ & _ & _ & P3 & _).
  apply Forall_app in HMFall as [HMF HMFw]. apply Forall_app in HPFall as [HPF _].
  assert (HUSP : usp_pin V) by (unfold usp_pin; lia).
  pose proof (ACCT_root V w UNIV (en_sp en) (in_fs inp) mo HV HPF HUSP HU AMO USP SHFIX KSH HSH HK NMAX HN aw Haw) as AC.
  eexists (L0 V w UNIV), _, (st0 V w UNIV).
  split; [| split; [exact AC|]].
  - rewrite Hms. cbn [ms_mem]. unfold RNG0. eapply (aheapu2_main V w UNIV m); try eassumption.
    eapply (arng0_main V w UNIV (en_sp en) (in_fs inp) mo); eassumption.
  - split; [intros u Hu; exact Hu|].
    split; [| exact (aprist_main V w UNIV)].
    intros z Hz. eapply (lazy_shape_main V); eassumption.
Qed.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainFactsBoth MainEntryBoth.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ModelX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.MmXfer OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrlProps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanInv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanBudget OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanTotalCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanNodeSem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanTotal OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanFree.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.BackingAlgebra.
Import AProto.TwinB ABase.TwinB ALayout.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB AArenaLaw.TwinB ATsafeCore.TwinB ATsafeEv.TwinB ATsafeAlloc.TwinB ATsafeOps.TwinB.
Import AEmbRep.TwinB AEmbFrame.TwinB APristLaw.TwinB AFake_iface.TwinB AInstanceU2.TwinB ARepAtMain.TwinB ARepAtMain2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import Adeq.TwinB Acct.TwinB.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainExport.
Module MF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainFactsBoth.
Module MA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntryBoth.

Definition wE (b n : Z) : word * word := (wa b, wa n).

Section Root.
Context {rc : runConstT}.
Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (sp : word) (fs : Fs.Fs) (mo : Model).
Hypothesis HV : forall n, 0 <= V n < 2 ^ 64.
Hypothesis HPF : Forall (ME.pfact_ok V) MF.both_pure_facts.
Hypothesis HUSP : usp_pin V.
Hypothesis HU : univ_ok U.
Hypothesis AMO : MA.bmodel V sp fs mo.
Hypothesis USP : bv_unsigned sp = ATOP + 8388608.

Lemma LZSUB : forall z, ME.in_ivs z (m_vm_lazy mo) -> ME.in_ivs z (vm_maps (m_vmmaps mo)).
Proof. exact (MA.bm_lazy_sub V sp fs mo AMO). Qed.
Lemma NANZ : Forall (fun e => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mo)).
Proof. exact (MA.bm_noaccess_nz V sp fs mo AMO). Qed.
Lemma FKEAGER : forall a, 4096 * V 377%nat <= a < 4096 * V 377%nat + 11571200 -> page_in_ranges (page_base_of a) (m_vm_lazy mo) = false.
Proof. exact (MA.bm_fake_eager V sp fs mo AMO). Qed.

Variable SHFIX : word -> Prop.
Variable KSH : Z.
Hypothesis SHFIX_fin : abud SHFIX KSH.
Hypothesis KSH0 : 0 <= KSH.

Variable NMAX : nat.
Hypothesis HNMAX : 59854612 + KSH <= Z.of_nat NMAX.

Local Notation L := (L0 V w U).
Local Notation sta := (st0 V w U).
Local Notation HP := (hp V HPF).
Tactic Notation "hpf" constr(k) ident(H) := pose proof (HP k _ eq_refl) as H; cbn [ME.pfact_ok ME.zv] in H.
Local Notation ALO := (alayout_ok_main V w U HV HPF HUSP HU).
Local Notation maps := (vm_maps (m_vmmaps mo)).

Definition KNOWN_hi : list (word * word) := [wE (4096 * V 471%nat) 4096; wE (4096 * V 454%nat) 8388608; wE (4096 * V 453%nat) 1048576].
Definition KNOWN_lo : list (word * word) :=
  [wE (4096 * V 377%nat) 11571200; wE (4096 * V 310%nat) 4096; wE (4096 * V 245%nat) 4096; wE (4096 * V 228%nat) 65536;
   wE (4096 * V 227%nat) 4096; wE (4096 * V 226%nat) 8388608; wE (4096 * V 208%nat) 137439023104; wE (4096 * V 207%nat) 3727360;
   wE (4096 * V 78%nat) 65536; wE 2201439137792 15392894357504; wE 2415882240 2199023255552; wE 2147446784 268435456].

Lemma maps_shape : exists fog : list (word * word),
  (length fog <= 2)%nat /\ Forall (fun iv => bv_unsigned (snd iv) <= 8192) fog
  /\ maps = KNOWN_hi ++ fog ++ KNOWN_lo.
Proof.
  pose proof (MA.bm_maps V sp fs mo AMO) as LD. unfold MF.both_ledger in LD. cbn [ME.ledger_den ME.zv] in LD.
  destruct LD as (m1 & E1 & m2 & E2 & m3 & E3 & LD).
  assert (TAILS : forall mx, ME.ledger_den V (skipn 5 MF.both_ledger) mx -> mx = KNOWN_lo).
  { intros mx H. unfold MF.both_ledger in H. cbn [skipn ME.ledger_den ME.zv] in H.
    destruct H as (n1 & -> & n2 & -> & n3 & -> & n4 & -> & n5 & -> & n6 & -> & n7 & -> & n8 & -> & n9 & -> & n10 & -> & n11 & -> & n12 & -> & ->).
    reflexivity. }
  destruct LD as [LD|(iv1 & m4 & E4 & S1 & LD)]; (destruct LD as [LD|(iv2 & m5 & E5 & S2 & LD)]).
  - exists []. split; [cbn; lia|]. split; [constructor|]. rewrite E1, E2, E3. rewrite (TAILS _ LD). reflexivity.
  - exists [iv2]. split; [cbn; lia|]. split; [constructor; [exact S2| constructor]|]. rewrite E1, E2, E3, E5. rewrite (TAILS _ LD). reflexivity.
  - exists [iv1]. split; [cbn; lia|]. split; [constructor; [exact S1| constructor]|]. rewrite E1, E2, E3, E4. rewrite (TAILS _ LD). reflexivity.
  - exists [iv1; iv2]. split; [cbn; lia|]. split; [constructor; [exact S1| constructor; [exact S2| constructor]]|]. rewrite E1, E2, E3, E4, E5. rewrite (TAILS _ LD). reflexivity.
Qed.

Lemma live_chunks_st0 : live_chunks sta = [].
Proof. unfold live_chunks. cbn [st0 ainit a_live]. rewrite map_to_list_empty. reflexivity. Qed.
Lemma qbatches_st0 : qbatches [] sta = [].
Proof. reflexivity. Qed.
Lemma all_chunks_st0 : all_chunks [] [] sta = [].
Proof. unfold all_chunks. rewrite live_chunks_st0. reflexivity. Qed.
Lemma CHX_st0 : CHX [] [] sta = [].
Proof. unfold CHX, CH. rewrite all_chunks_st0. reflexivity. Qed.

Lemma AINV_main : AINV ATOP [] [] sta.
Proof.
  unfold AINV. rewrite all_chunks_st0, qbatches_st0. pose proof (ao_space_al L ALO) as SAL. pose proof (ao_ptr L ALO) as (P1 & P2 & _).
  pose proof (ARepAtMain2.TwinB.space_facts V w U HV HPF HUSP HU) as (S1 & _).
  split.
  { intros c Hc. unfold cls_inv. rewrite get_cls_st0, max_count_st0, all_chunks_st0, qbatches_st0.
    cbn [c_allocated_user c_mapped_user c_mapped_free_array c_num_freed c_count aclass0 cntP List.filter zlen length Z.of_nat].
    unfold nbatch, cntP, zlen, K_FREEARR_OFF, K_USER_MAP, K_FREEARR_MAX, K_FREEARR_MAP. cbn [List.filter length Z.of_nat].
    repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia. destruct (c =? K_BATCH_CLASS); cbn [length Z.of_nat]; lia. }
  split; [constructor|]. split; [constructor|]. split; [reflexivity|]. split; [reflexivity|]. split; [unfold CH; rewrite all_chunks_st0; reflexivity|].
  split; [exists 0; cbn [st0 ainit a_nres]; lia|].
  split. { intros id ch H. cbn [st0 ainit a_live] in H. rewrite lookup_empty in H. discriminate H. }
  split; [| split; [| split; [| split; [| split]]]].
  - cbn [st0 ainit a_space_beg]. exact SAL.
  - cbn [st0 ainit a_space_beg]. lia.
  - cbn [st0 ainit a_ptr_array]. exact P1.
  - cbn [st0 ainit a_ptr_array]. lia.
  - unfold live_budget. rewrite live_chunks_st0. unfold cntP, zlen, secs, secbytes. cbn [List.filter flat_map length Z.of_nat]. rewrite Z.mul_0_r. unfold L24MAX, SMAX, LSBYTES. lia.
  - unfold emb_ok. cbn [st0 ainit a_emb]. left. split; reflexivity.
Qed.

Definition RESV0 : list (Z * Z) :=
  [(0x10000, 0x3c000); (0x3c000, 0xcf000); (0xcf000, 0xd5000); (0xd5000, 0x631000);
   (LS_LO, LS_LO + LS_SZ); (GAP_LO, GAP_LO + GAP_SZ); (HS_LO, HS_LO + HS_SZ);
   (4096 * V 208%nat, 4096 * V 208%nat + 137439023104); (4096 * V 226%nat, 4096 * V 226%nat + 8388608);
   (4096 * V 227%nat, 4096 * V 227%nat + 4096); (4096 * V 228%nat, 4096 * V 228%nat + 65536);
   (4096 * V 453%nat, 4096 * V 453%nat + 1048576); (4096 * V 454%nat, 4096 * V 454%nat + 8388608);
   (4096 * V 377%nat, 4096 * V 377%nat + 11571200); (4096 * V 310%nat, 4096 * V 310%nat + 4096);
   (4096 * V 78%nat, 4096 * V 78%nat + 65536); (4096 * V 207%nat, 4096 * V 207%nat + 3727360);
   (4096 * V 245%nat, 4096 * V 245%nat + 4096); (4096 * V 471%nat, 4096 * V 471%nat + 4096)].

Lemma pcov1 : forall lo hi, In (lo, hi) RESV0 -> pcov RESV0 lo hi.
Proof. intros lo hi Hin x Hx. exists (lo, hi). split; [exact Hin| exact Hx]. Qed.

Lemma aresv_ok_main : aresv_ok L RESV0.
Proof.
  unfold aresv_ok. unfold al_ptr_array, al_t, al_ctx, al_nodes, al_store, al_fake, al_dtls. cbn [al_V L0 VL]. unfold AIMG_HI.
  assert (I4 : pcov RESV0 0x10000 0x631000).
  { intros x Hx. destruct (Z_lt_ge_dec x 0x3c000); [exists (0x10000, 0x3c000); split; [cbn; tauto| cbn; lia]|].
    destruct (Z_lt_ge_dec x 0xcf000); [exists (0x3c000, 0xcf000); split; [cbn; tauto| cbn; lia]|].
    destruct (Z_lt_ge_dec x 0xd5000); [exists (0xcf000, 0xd5000); split; [cbn; tauto| cbn; lia]|].
    exists (0xd5000, 0x631000); split; [cbn; tauto| cbn; lia]. }
  assert (SH : pcov RESV0 0x7fff7000 0x10007fff8000).
  { intros x Hx. unfold RESV0, LS_LO, LS_SZ, GAP_LO, GAP_SZ, HS_LO, HS_SZ.
    destruct (Z_lt_ge_dec x 0x8fff7000); [eexists; split; [do 4 right; left; reflexivity| cbn; lia]|].
    destruct (Z_lt_ge_dec x 0x2008fff7000); [eexists; split; [do 5 right; left; reflexivity| cbn; lia]|].
    eexists; split; [do 6 right; left; reflexivity| cbn; lia]. }
  split; [exact I4|]. split; [exact SH|].
  repeat match goal with |- _ /\ _ => split end; apply pcov1; unfold RESV0; cbn [In]; tauto.
Qed.

Lemma maps_In_known : forall e, In e (KNOWN_hi ++ KNOWN_lo) -> In e maps.
Proof.
  intros e He. destruct maps_shape as (fog & _ & _ & EQ). rewrite EQ. apply in_app_or in He as [He|He]; apply in_or_app; [left; exact He| right; apply in_or_app; right; exact He].
Qed.

Lemma seps_of_ivs_sep : forall l, ME.ivs_sep l -> seps l.
Proof.
  induction l as [|p l IH]; intros H; [constructor|].
  constructor.
  - apply Forall_forall. intros q Hq. apply In_nth_error in Hq as [j Hj]. unfold wsep. exact (H 0%nat (Datatypes.S j) p q ltac:(lia) eq_refl Hj).
  - apply IH. intros i j a b Hij Hi Hj. exact (H (Datatypes.S i) (Datatypes.S j) a b ltac:(lia) Hi Hj).
Qed.

Lemma ivs_wf_of_bound : forall l (R : Z), Forall (fun iv => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= R) l -> R <= 2 ^ 64 -> ivs_wf l.
Proof. intros l R HF HR q Hq. unfold iv_wf, B, S. pose proof (proj1 (Forall_forall _ _) HF q Hq) as X. cbn in X. lia. Qed.

Lemma shadow_not_noaccess : forall a : word,
  (LS_LO <= bv_unsigned a < LS_LO + LS_SZ \/ HS_LO <= bv_unsigned a < HS_LO + HS_SZ) -> ~ ME.in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps mo)).
Proof.
  intros a Ha. pose proof (MA.bm_kinds V sp fs mo AMO) as K. unfold MF.both_ledger in K.
  pose proof (proj1 (Forall_forall _ _) K (ME.LMap (ME.ZLit 2147446784) 268435456 AsanPlanCore.APC.KRWLAZY) ltac:(cbn; tauto)) as KL.
  pose proof (proj1 (Forall_forall _ _) K (ME.LMap (ME.ZLit 2201439137792) 15392894357504 AsanPlanCore.APC.KRWLAZY) ltac:(cbn; tauto)) as KH.
  cbn [ME.lentry_kind_ok ME.zv] in KL, KH. unfold LS_LO, LS_SZ, HS_LO, HS_SZ in Ha.
  destruct Ha as [Ha|Ha]; [exact (proj1 (KL a Ha))| exact (proj1 (KH a Ha))].
Qed.

Lemma noacc_sep_main : noacc_sep (vm_noaccess (m_vmmaps mo)).
Proof.
  unfold noacc_sep. apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) NANZ e He) as NZ. cbn in NZ.
  pose proof (MA.bm_noaccess_sub V sp fs mo AMO) as SUB.
  assert (IN : forall x, bv_unsigned (fst e) <= x < bv_unsigned (fst e) + bv_unsigned (snd e) -> ME.in_ivs x (vm_noaccess (m_vmmaps mo))).
  { intros x Hx. exists e. split; [exact He| exact Hx]. }
  pose proof (bv_unsigned_in_range _ (fst e)) as R1. pose proof (bv_unsigned_in_range _ (snd e)) as R2.
  unfold sepz, LS_LO, LS_SZ, HS_LO, HS_SZ. split.
  - destruct (Z_le_gt_dec (bv_unsigned (fst e) + bv_unsigned (snd e)) 2147446784) as [|G1]; [left; lia|].
    destruct (Z_le_gt_dec (2147446784 + 268435456) (bv_unsigned (fst e))) as [|G2]; [right; lia|]. exfalso.
    set (x := Z.max (bv_unsigned (fst e)) 2147446784).
    apply (shadow_not_noaccess (wa x)); rewrite wa_unsigned by lia; [left; unfold LS_LO, LS_SZ; lia| apply IN; lia].
  - destruct (Z_le_gt_dec (bv_unsigned (fst e) + bv_unsigned (snd e)) 2201439137792) as [|G1]; [left; lia|].
    destruct (Z_le_gt_dec (2201439137792 + 15392894357504) (bv_unsigned (fst e))) as [|G2]; [right; lia|]. exfalso.
    set (x := Z.max (bv_unsigned (fst e)) 2201439137792).
    apply (shadow_not_noaccess (wa x)); rewrite wa_unsigned by lia; [right; unfold HS_LO, HS_SZ; lia| apply IN; lia].
Qed.

Lemma csum_st0 : forall f, f aclass0 = 0 -> csum f sta = 0.
Proof.
  intros f Hf. unfold csum. generalize CLASSES as l. induction l as [|c l IH]; cbn [fold_right]; [reflexivity|]. rewrite get_cls_st0, Hf, IH. reflexivity.
Qed.
Lemma commit_bytes_st0 : commit_bytes sta = 0.
Proof. unfold commit_bytes. rewrite csum_st0 by reflexivity. reflexivity. Qed.

Lemma sum_count_Pm : forall mx, m_vmmaps mx = m_vmmaps mo -> m_vm_lazy mx = m_vm_lazy mo ->
  sum_count (Pm mx) maps = nonlazy_bytes mo.
Proof.
  intros mx EM EL. unfold nonlazy_bytes, vm_backed_maps. rewrite <- maps_subtract_all_app_cuts.
  assert (WF : ivs_wf maps).
  { apply (ivs_wf_of_bound maps (bv_unsigned sp - 8388608)); [| pose proof (bv_unsigned_in_range _ sp); lia].
    eapply Forall_impl; [| exact (MA.bm_bounds V sp fs mo AMO)]. cbn. intros iv (_ & _ & _ & _ & _ & X). exact X. }
  destruct (live_msa (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) maps WF) as [E _]. rewrite E.
  apply sum_count_ext. intros x. unfold Pm. rewrite EM, EL. reflexivity.
Qed.

Lemma START_main : START RESV0 ATOP maps (vm_reserved (m_vmmaps mo)) sta.
Proof.
  unfold START. cbn [st0 ainit a_space_beg a_ptr_array]. pose proof (ao_space L ALO) as SP. pose proof (ao_res_hi L ALO) as RH. pose proof (ao_res L ALO) as (_ & _ & R3 & _).
  pose proof (ao_ptr L ALO) as (P1 & P2 & P3 & P4 & P5). revert SP RH R3. rewrite al_res_eq. intros SP RH R3.
  unfold al_ptr_array in *. cbn [al_V L0 VL] in *. pose proof atop_range as AR.
  split. { exists (4096 * V 208%nat). unfold PRIM_SZ, KHIGH. split; [apply maps_In_known; cbn; tauto| lia]. }
  split; [apply maps_In_known; cbn; tauto|]. split; [unfold PTR_SZ; lia|].
  split. { rewrite (MA.bm_reserved V sp fs mo AMO), segments_reserved_asan. unfold PTR_SZ.
           apply (region_free_above _ _ _ 0x631000); [| unfold iclr, AIMG_LO, AIMG_HI in P5; lia| lia| lia| lia].
           repeat (apply Forall_cons; [cbn [fst snd]; rewrite !unsigned_lit by lia; lia|]). apply Forall_nil. }
  split; [apply maps_In_known; cbn; tauto|]. split; [apply maps_In_known; cbn; tauto|]. split; [apply maps_In_known; cbn; tauto|].
  destruct maps_shape as (fog & FL & FS & EQ).
  split. { rewrite EQ. unfold zlen, LEN0. rewrite !length_app. cbn [length KNOWN_hi KNOWN_lo]. lia. }
  split. { pose proof (MA.bm_totsz V sp fs mo AMO) as T. unfold MF.both_totsz in T. unfold TOT0.
           assert (LE : forall l1 l2, live_bytes l2 <= ME.ivs_sum (l1 ++ l2)).
           { intros l1 l2. induction l1 as [|iv l1 IH]; cbn.
             - induction l2 as [|[a b] l2 IH2]; cbn; [lia|]. lia.
             - pose proof (bv_unsigned_in_range _ (snd iv)). lia. }
           pose proof (LE (vm_reserved (m_vmmaps mo)) maps). lia. }
  unfold RESV0. unfold LS_LO, LS_SZ, GAP_LO, GAP_SZ, HS_LO, HS_SZ.
  rewrite (MA.bm_reserved V sp fs mo AMO), segments_reserved_asan.
  hpf 12%nat B78. hpf 13%nat B207. hpf 14%nat B208. hpf 16%nat B226. hpf 17%nat B227. hpf 18%nat B228.
  hpf 19%nat B245. hpf 20%nat B310. hpf 24%nat B377. hpf 32%nat B453. hpf 33%nat B454. hpf 34%nat B471.
  set (R4 := [(Z_to_bv 64 65536, Z_to_bv 64 180224); (Z_to_bv 64 245760, Z_to_bv 64 602112); (Z_to_bv 64 847872, Z_to_bv 64 24576); (Z_to_bv 64 872448, Z_to_bv 64 5619712)]).
  assert (KB : forall b n lo hi, In (wE b n) maps -> 0 <= b -> 0 <= n -> b + n < 2 ^ 64 -> b <= lo -> hi <= b + n -> rcov (R4 ++ maps) (lo, hi)).
  { intros b n lo hi Hin Hb Hn Hbn H1 H2. exists (wE b n). split; [apply in_or_app; right; exact Hin|]. unfold wE. cbn [fst snd]. rewrite !wa_unsigned by lia. lia. }
  assert (KR : forall b n lo hi, In (Z_to_bv 64 b, Z_to_bv 64 n) R4 -> 0 <= b < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> b <= lo -> hi <= b + n -> rcov (R4 ++ maps) (lo, hi)).
  { intros b n lo hi Hin Hb Hn H1 H2. exists (Z_to_bv 64 b, Z_to_bv 64 n). split; [apply in_or_app; left; exact Hin|]. cbn [fst snd]. rewrite !unsigned_lit by lia. lia. }

  apply Forall_cons; [apply (KR 65536 180224); [unfold R4; cbn; tauto| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KR 245760 602112); [unfold R4; cbn; tauto| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KR 847872 24576); [unfold R4; cbn; tauto| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KR 872448 5619712); [unfold R4; cbn; tauto| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB 2147446784 268435456); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB 2415882240 2199023255552); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB 2201439137792 15392894357504); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 208%nat) 137439023104); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 226%nat) 8388608); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 227%nat) 4096); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 228%nat) 65536); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 453%nat) 1048576); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 454%nat) 8388608); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 377%nat) 11571200); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 310%nat) 4096); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 78%nat) 65536); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 207%nat) 3727360); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 245%nat) 4096); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_cons; [apply (KB (4096 * V 471%nat) 4096); [apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE; cbn [In app]; tauto| lia| lia| lia| lia| lia]|].
  apply Forall_nil.
Qed.

Lemma covered_in_ivs : forall l x, covered l x = true <-> ME.in_ivs x l.
Proof.
  intros l x. unfold covered, ME.in_ivs. rewrite existsb_exists. unfold in_iv, in_rng, B, S. split.
  - intros (iv & Hin & H). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists iv. split; [exact Hin| lia].
  - intros (iv & Hin & H). exists iv. split; [exact Hin|]. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

Lemma AMI_main : AMI RESV0 ATOP [] sta (canon mo).
Proof.
  unfold AMI, canon. rewrite !m_vmmaps_MX, !m_vm_lazy_MX, m_vm_materialized_MX. pose proof atop_range as AR. pose proof (bv_unsigned_in_range _ sp) as SPR.
  split; [reflexivity|].
  split; [rewrite (MA.bm_limit V sp fs mo AMO); reflexivity|].
  split. { rewrite (MA.bm_reserved V sp fs mo AMO), segments_reserved_asan. unfold RES_HI. repeat (apply Forall_cons; [cbn [fst snd]; rewrite !unsigned_lit by lia; lia|]). apply Forall_nil. }
  split. { rewrite (MA.bm_reserved V sp fs mo AMO), segments_reserved_asan. unfold zlen, LEN0. cbn [length Z.of_nat]. lia. }
  split. { rewrite (MA.bm_reserved V sp fs mo AMO), segments_reserved_asan. unfold RTOT0. cbn [live_bytes]. rewrite !unsigned_lit by lia. lia. }
  split. { eapply Forall_impl; [| exact (MA.bm_bounds V sp fs mo AMO)]. cbn. intros iv (B1 & B2 & B3 & B4 & B5 & B6). unfold entry_ok. rewrite USP in B6. lia. }
  split. { split; [| exact noacc_sep_main]. apply (ivs_wf_of_bound _ (2 ^ 64)); [exact (MA.bm_noaccess_wf V sp fs mo AMO)| lia]. }
  split. { apply (ivs_wf_of_bound _ (bv_unsigned sp - 8388608)); [| lia]. eapply Forall_impl; [| exact (MA.bm_lazy_bounds V sp fs mo AMO)]. cbn. intros iv [_ X]. exact X. }
  split. { split; [apply seps_of_ivs_sep; exact (MA.bm_sep V sp fs mo AMO)|].
           unfold rsep. eapply Forall_impl; [| exact (MA.bm_bounds V sp fs mo AMO)]. cbn. intros iv (B1 & B2 & B3 & B4 & B5 & B6).
           rewrite (MA.bm_reserved V sp fs mo AMO), segments_reserved_asan. unfold MA.BIMG_LO, MA.BIMG_HI in B5.
           repeat (apply Forall_cons; [cbn [fst snd]; rewrite !unsigned_lit by lia; lia|]). apply Forall_nil. }
  split. { split; [unfold atop_ok, ACEIL, AsanInv.ATOP_MAX; lia|]. unfold alloc_top. rewrite (MA.bm_top V sp fs mo AMO). unfold stack_max_size. lia. }
  exists maps. split; [rewrite app_nil_r; apply Permutation_refl|]. split; [exact START_main|].
  split. { rewrite commit_bytes_st0, (sum_count_Pm (MX mo [])) by reflexivity. pose proof (MA.bm_nonlazy V sp fs mo AMO) as NL. unfold MF.both_eager in NL. unfold EAGER0. lia. }
  intros x Hx. split.
  - apply (proj2 (covered_in_ivs _ _)). apply LZSUB. apply (proj1 (covered_in_ivs _ _)). exact Hx.
  - intros (c & Hc & R). rewrite get_cls_st0 in R. cbn [c_mapped_user aclass0] in R. lia.
Qed.

Theorem INV_main : INV RESV0 ATOP [] [] sta (canon mo).
Proof. split; [exact AINV_main|]. rewrite CHX_st0. exact AMI_main. Qed.

Lemma pagedown_spec : forall z, ME.pagedown z <= z < ME.pagedown z + 4096 /\ ME.pagedown z mod 4096 = 0.
Proof. intros z. unfold ME.pagedown. Z.div_mod_to_equations. lia. Qed.
Lemma pageup_spec : forall z, z <= ME.pageup z < z + 4096 /\ ME.pageup z mod 4096 = 0.
Proof. intros z. unfold ME.pageup. Z.div_mod_to_equations. lia. Qed.
Lemma page_base_of_val : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (page_base_of z) = ME.pagedown z.
Proof.
  intros z Hz. unfold page_base_of, page_size, ME.pagedown. pose proof (pagedown_spec z) as [P _]. unfold ME.pagedown in P.
  rewrite unsigned_lit by lia. reflexivity.
Qed.

Definition appz_e (e : word * word) : bool := (B e + S e <=? LS_LO) || (KHIGH <=? B e).
Definition shiv (e : word * word) : Z * Z := (ME.pagedown (shad (B e)), ME.pageup (shad (B e + S e))).
Definition ALV : list (Z * Z) := ME.allow_of MA.ASHOFF V MF.both_vis.
Definition ALC : list (Z * Z) := map shiv (List.filter appz_e maps).
Definition AL0 : list (Z * Z) := ALV ++ ALC.
Definition A0 : alw := fun p => (bv_unsigned p mod 4096 = 0 /\ ME.aallowed AL0 p) \/ SHFIX p.
Definition RNG0 : footprint := fp_ok (m_vm_lazy mo) A0.

Lemma aallowed_app_l : forall l1 l2 p, ME.aallowed l1 p -> ME.aallowed (l1 ++ l2) p.
Proof. intros l1 l2 p (iv & Hin & H). exists iv. split; [apply in_or_app; left; exact Hin| exact H]. Qed.
Lemma aallowed_app_r : forall l1 l2 p, ME.aallowed l2 p -> ME.aallowed (l1 ++ l2) p.
Proof. intros l1 l2 p (iv & Hin & H). exists iv. split; [apply in_or_app; right; exact Hin| exact H]. Qed.

Lemma maps_sep2 : forall p q, In p maps -> In q maps -> p = q \/ wsep p q.
Proof.
  intros p q Hp Hq. apply In_nth_error in Hp as [i Hi]. apply In_nth_error in Hq as [j Hj].
  pose proof (MA.bm_sep V sp fs mo AMO) as SEP.
  destruct (lt_eq_lt_dec i j) as [[LT|EQ]|GT].
  - right. exact (SEP i j p q LT Hi Hj).
  - left. subst j. rewrite Hi in Hj. injection Hj as E. exact E.
  - right. pose proof (SEP j i q p GT Hj Hi) as X. unfold wsep in *. lia.
Qed.

Lemma appz_entry : forall e x, In e maps -> B e <= x < B e + S e -> appz x -> appz_e e = true.
Proof.
  intros e x He Hx AP. unfold appz_e. unfold appz in AP. apply orb_true_intro.
  assert (INLS : In (wE LS_LO LS_SZ) maps) by (apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE, LS_LO, LS_SZ; cbn [In app]; tauto).
  assert (INHS : In (wE HS_LO HS_SZ) maps) by (apply maps_In_known; unfold KNOWN_hi, KNOWN_lo, wE, HS_LO, HS_SZ; cbn [In app]; tauto).
  unfold LS_LO, LS_SZ, HS_LO, HS_SZ, KHIGH in *. unfold B, S in *.
  destruct AP as [AP|AP].
  - left. apply Z.leb_le. destruct (maps_sep2 e _ He INLS) as [->|W].
    + exfalso. unfold wE in Hx. cbn [fst snd] in Hx. rewrite !wa_unsigned in Hx by lia. lia.
    + unfold wsep, wE in W. cbn [fst snd] in W. rewrite !wa_unsigned in W by lia. lia.
  - right. apply Z.leb_le. destruct (maps_sep2 e _ He INHS) as [->|W].
    + exfalso. unfold wE in Hx. cbn [fst snd] in Hx. rewrite !wa_unsigned in Hx by lia. lia.
    + unfold wsep, wE in W. cbn [fst snd] in W. rewrite !wa_unsigned in W by lia. lia.
Qed.

Lemma ALC_page : forall e z', In e maps -> appz_e e = true -> shad (B e) <= z' < shad (B e + S e) -> 0 <= z' < 2 ^ 64 -> A0 (page_base_of z').
Proof.
  intros e z' He AE Hz R. left. rewrite page_base_of_val by exact R. pose proof (pagedown_spec z') as [P1 P2]. split; [exact P2|].
  apply aallowed_app_r. exists (shiv e). split; [apply in_map_iff; exists e; split; [reflexivity| apply filter_In; split; [exact He| exact AE]]|].
  unfold shiv. cbn [fst snd]. rewrite page_base_of_val by exact R. pose proof (pagedown_spec (shad (B e))) as [Q1 _]. pose proof (pageup_spec (shad (B e + S e))) as [Q2 _].
  unfold ME.pagedown, ME.pageup in *. clear -Hz Q1 Q2 P1. Z.div_mod_to_equations. lia.
Qed.

Lemma A0_base : alw_le (Abase_x SHFIX (al_space_beg L) (al_ptr_array L)) A0.
Proof.
  intros p [AB|AF]; [| right; exact AF]. destruct AB as (z' & Hz & ->).
  pose proof (ao_space L ALO) as SP. pose proof (ao_res_hi L ALO) as RH. pose proof (ao_res L ALO) as (_ & _ & R3 & R4 & _). pose proof (ao_ptr L ALO) as (P1 & P2 & P3 & P4 & P5).
  revert SP RH R3 R4. rewrite al_res_eq. intros SP RH R3 R4. unfold al_ptr_array in *. cbn [al_V L0 VL] in *. pose proof atop_range as AR.
  unfold K_SPACE_SIZE, K_PTRARR_RESERVE in Hz. rewrite !shad_div in Hz. unfold ASHOFF in Hz.
  destruct Hz as [Hz|Hz].
  - apply (ALC_page (wE (4096 * V 208%nat) 137439023104)).
    + apply maps_In_known; unfold KNOWN_hi, KNOWN_lo; cbn [In app]; tauto.
    + unfold appz_e, B, S, wE. cbn [fst snd]. rewrite !wa_unsigned by lia. apply orb_true_intro. right. apply Z.leb_le. unfold KHIGH. lia.
    + unfold B, S, wE. cbn [fst snd]. rewrite !wa_unsigned by lia. rewrite !shad_div. unfold ASHOFF. clear -Hz SP. Z.div_mod_to_equations. lia.
    + clear -Hz SP RH R3 AR. Z.div_mod_to_equations. lia.
  - apply (ALC_page (wE (4096 * V 226%nat) 8388608)).
    + apply maps_In_known; unfold KNOWN_hi, KNOWN_lo; cbn [In app]; tauto.
    + unfold appz_e, B, S, wE. cbn [fst snd]. rewrite !wa_unsigned by lia. unfold sclr in P4. unfold LS_LO, KHIGH, KLS in *.
      apply orb_true_intro. destruct P4 as [P4|P4]; [left| right]; apply Z.leb_le; lia.
    + unfold B, S, wE. cbn [fst snd]. rewrite !wa_unsigned by lia. rewrite !shad_div. unfold ASHOFF. clear -Hz. Z.div_mod_to_equations. lia.
    + clear -Hz P2 P3 AR. Z.div_mod_to_equations. lia.
Qed.

Lemma A0_covp : forall p, COVP (canon mo) p -> A0 p.
Proof.
  intros p (e & x & He & Hx & AP & ->). unfold canon in He. rewrite m_vmmaps_MX in He.
  pose proof (proj1 (Forall_forall _ _) (MA.bm_bounds V sp fs mo AMO) e He) as (B1 & B2 & B3 & B4 & B5 & B6).
  assert (SPR : 0 <= bv_unsigned sp < 2 ^ 64) by exact (bv_unsigned_in_range 64 sp).
  apply (ALC_page e); [exact He| exact (appz_entry e x He Hx AP)| |]; unfold B, S in *; rewrite !shad_div; unfold ASHOFF; clear -Hx B2 B3 B4 B6 SPR; Z.div_mod_to_equations; lia.
Qed.

Lemma A0_mat : forall p, In p (m_vm_materialized mo) -> A0 p.
Proof.
  intros p Hp. destruct (MA.bm_mat V sp fs mo AMO p Hp) as (M1 & _ & M3). left. split; [exact M1|]. apply aallowed_app_l. exact M3.
Qed.

Lemma ALC_wf : ME.ivz_wf ALC.
Proof.
  unfold ME.ivz_wf, ALC. apply Forall_forall. intros iv Hin. apply in_map_iff in Hin as (e & <- & He). unfold shiv. cbn [fst snd].
  pose proof (pagedown_spec (shad (B e))) as [P1 P2]. pose proof (pageup_spec (shad (B e + S e))) as [Q1 Q2].
  split; [| split; [exact P2| exact Q2]]. pose proof (S_range e). rewrite !shad_div in *. Z.div_mod_to_equations. lia.
Qed.
Lemma AL0_wf : ME.ivz_wf AL0.
Proof. unfold AL0, ME.ivz_wf. apply Forall_app. split; [exact (MA.bm_allow_wf V sp fs mo AMO)| exact ALC_wf]. Qed.

Definition shc (e : word * word) : Z := S e / 8 + 8192.
Fixpoint sum_shc (l : list (word * word)) : Z := match l with [] => 0 | e :: l' => shc e + sum_shc l' end.
Lemma shc_nonneg : forall e, 0 <= shc e. Proof. intros e. unfold shc. pose proof (S_range e). Z.div_mod_to_equations. lia. Qed.
Lemma sum_shc_app : forall l1 l2, sum_shc (l1 ++ l2) = sum_shc l1 + sum_shc l2.
Proof. induction l1 as [|e l1 IH]; intros l2; cbn; [lia| rewrite IH; lia]. Qed.
Lemma sum_shc_filter : forall f l, sum_shc (List.filter f l) <= sum_shc l.
Proof. induction l as [|e l IH]; cbn; [lia|]. pose proof (shc_nonneg e). destruct (f e); cbn; lia. Qed.
Lemma ivz_shiv : forall l, ME.ivz_bytes (map shiv l) <= sum_shc l.
Proof.
  induction l as [|e l IH]; [cbn; lia|].
  change (ME.ivz_bytes (map shiv (e :: l))) with ((ME.pageup (shad (B e + S e)) - ME.pagedown (shad (B e))) + ME.ivz_bytes (map shiv l)).
  cbn [sum_shc]. unfold shc at 1.
  pose proof (pagedown_spec (shad (B e))) as [P1 _]. pose proof (pageup_spec (shad (B e + S e))) as [Q1 _].
  pose proof (S_range e) as SR. pose proof (B_range e) as BR. rewrite !shad_div in *. unfold ASHOFF in *.
  assert ((B e + S e) / 8 - B e / 8 <= S e / 8 + 1) by (clear -SR BR; Z.div_mod_to_equations; lia). lia.
Qed.
Lemma filter_app' : forall {X} (f : X -> bool) l1 l2, List.filter f (l1 ++ l2) = List.filter f l1 ++ List.filter f l2.
Proof. intros X f l1 l2. induction l1 as [|x l1 IH]; cbn; [reflexivity|]. rewrite IH. destruct (f x); reflexivity. Qed.

Lemma ALC_bytes : ME.ivz_bytes ALC <= 17184153600.
Proof.
  unfold ALC. pose proof (ivz_shiv (List.filter appz_e maps)) as IV. eapply Z.le_trans; [exact IV|].
  destruct maps_shape as (fog & FL & FS & EQ). rewrite EQ. rewrite !filter_app', !sum_shc_app.
  hpf 14%nat B208. hpf 16%nat B226. hpf 17%nat B227. hpf 18%nat B228. hpf 32%nat B453. hpf 33%nat B454.
  hpf 24%nat B377. hpf 20%nat B310. hpf 12%nat B78. hpf 13%nat B207. hpf 19%nat B245. hpf 34%nat B471.
  assert (F1 : sum_shc (List.filter appz_e KNOWN_hi) <= 1204736).
  { eapply Z.le_trans; [apply sum_shc_filter|]. unfold KNOWN_hi. cbn [sum_shc]. unfold shc, S, wE. cbn [snd]. rewrite !wa_unsigned by lia.
    apply Z.leb_le. vm_compute. reflexivity. }
  assert (F2 : sum_shc (List.filter appz_e fog) <= 18432).
  { eapply Z.le_trans; [apply sum_shc_filter|]. destruct fog as [|f1 [|f2 [|f3 fog]]]; cbn [length] in FL; [cbn; lia| | | lia].
    - pose proof (Forall_inv FS) as S1. cbn [sum_shc]. unfold shc, S in *. clear -S1. Z.div_mod_to_equations. lia.
    - pose proof (Forall_inv FS) as S1. pose proof (Forall_inv (Forall_inv_tail FS)) as S2. cbn [sum_shc]. unfold shc, S in *. clear -S1 S2. Z.div_mod_to_equations. lia. }
  assert (F3 : sum_shc (List.filter appz_e KNOWN_lo) <= 17182930432).
  { unfold KNOWN_lo.
    change ([wE (4096 * V 377%nat) 11571200; wE (4096 * V 310%nat) 4096; wE (4096 * V 245%nat) 4096; wE (4096 * V 228%nat) 65536;
             wE (4096 * V 227%nat) 4096; wE (4096 * V 226%nat) 8388608; wE (4096 * V 208%nat) 137439023104; wE (4096 * V 207%nat) 3727360;
             wE (4096 * V 78%nat) 65536; wE 2201439137792 15392894357504; wE 2415882240 2199023255552; wE 2147446784 268435456])
      with ([wE (4096 * V 377%nat) 11571200; wE (4096 * V 310%nat) 4096; wE (4096 * V 245%nat) 4096; wE (4096 * V 228%nat) 65536;
             wE (4096 * V 227%nat) 4096; wE (4096 * V 226%nat) 8388608; wE (4096 * V 208%nat) 137439023104; wE (4096 * V 207%nat) 3727360;
             wE (4096 * V 78%nat) 65536] ++ [wE 2201439137792 15392894357504; wE 2415882240 2199023255552; wE 2147446784 268435456]).
    rewrite filter_app', sum_shc_app.
    replace (List.filter appz_e [wE 2201439137792 15392894357504; wE 2415882240 2199023255552; wE 2147446784 268435456]) with (@nil (word * word)) by (vm_compute; reflexivity).
    cbn [sum_shc]. eapply Z.le_trans; [apply Z.add_le_mono_r; apply sum_shc_filter|]. cbn [sum_shc]. unfold shc, S, wE. cbn [snd]. rewrite !wa_unsigned by lia.
    apply Z.leb_le. vm_compute. reflexivity. }
  lia.
Qed.

Lemma A0_bud : abud A0 (4796180 + KSH).
Proof.
  destruct (ME.aallowed_fin AL0 AL0_wf) as (L1 & N1 & LEN1 & IN1). destruct SHFIX_fin as (L2 & N2 & LEN2 & IN2).
  destruct (nodup_extend L1 L2 N1) as (L3 & N3 & LEN3 & IN3).
  exists L3. split; [exact N3|]. split.
  - assert (BY : ME.ivz_bytes AL0 <= 2460995584 + 17184153600).
    { unfold AL0. assert (E : forall a b, ME.ivz_bytes (a ++ b) = ME.ivz_bytes a + ME.ivz_bytes b) by (intros a b; induction a as [|iv a IH]; cbn; [lia| rewrite IH; lia]).
      rewrite E. pose proof (MA.bm_abytes V sp fs mo AMO) as AB. unfold MF.both_abytes in AB. fold ALV in AB. pose proof ALC_bytes. unfold ALV in *. lia. }
    assert (ME.ivz_bytes AL0 / 4096 <= 4796180) by (Z.div_mod_to_equations; lia). lia.
  - intros p [[M A]|F]; apply IN3; [left; exact (IN1 p M A)| right; exact (IN2 p F)].
Qed.

Lemma lazy_above : forall z, ATOP <= z -> 0 <= z < 2 ^ 64 -> page_in_ranges (page_base_of z) (m_vm_lazy mo) = false.
Proof.
  intros z Hz R. pose proof (MA.bm_lazy_bounds V sp fs mo AMO) as LB.
  destruct (page_in_ranges (page_base_of z) (m_vm_lazy mo)) eqn:E; [| reflexivity]. exfalso.
  unfold page_in_ranges in E. apply existsb_exists in E as (iv & Hin & T). apply andb_prop in T as [T1 T2]. apply Z.leb_le in T1. apply Z.leb_le in T2.
  rewrite page_base_of_val in T1, T2 by exact R. pose proof (pagedown_spec z) as [P _]. unfold page_size in T2.
  pose proof (proj1 (Forall_forall _ _) LB iv Hin) as [_ X]. cbn in X. rewrite USP in X. lia.
Qed.
Lemma lazy_image : forall z, 0x10000 <= z < 0x631000 -> page_in_ranges (page_base_of z) (m_vm_lazy mo) = false.
Proof.
  intros z Hz. pose proof (MA.bm_lazy_bounds V sp fs mo AMO) as LB.
  destruct (page_in_ranges (page_base_of z) (m_vm_lazy mo)) eqn:E; [| reflexivity]. exfalso.
  unfold page_in_ranges in E. apply existsb_exists in E as (iv & Hin & T). apply andb_prop in T as [T1 T2]. apply Z.leb_le in T1. apply Z.leb_le in T2.
  rewrite page_base_of_val in T1, T2 by lia. pose proof (pagedown_spec z) as [P PM]. unfold page_size in T2.
  pose proof (proj1 (Forall_forall _ _) LB iv Hin) as [X _]. cbn in X. unfold MA.BIMG_LO, MA.BIMG_HI in X. unfold ME.pagedown in *.
  clear -Hz T1 T2 P PM X. Z.div_mod_to_equations. lia.
Qed.

Lemma ALV_page : forall bn z, In bn MF.both_vis ->
  (ME.pagedown (ME.zv V (fst bn)) <= z < ME.pageup (ME.zv V (fst bn) + ME.zv V (snd bn))
   \/ ME.pagedown (MA.ASHOFF + ME.zv V (fst bn) / 8) <= z < ME.pageup (MA.ASHOFF + (ME.zv V (fst bn) + ME.zv V (snd bn)) / 8)) ->
  0 <= z < 2 ^ 64 -> A0 (page_base_of z).
Proof.
  intros bn z Hin Hz R. left. rewrite page_base_of_val by exact R. pose proof (pagedown_spec z) as [P1 P2]. split; [exact P2|].
  apply aallowed_app_l. unfold ALV, ME.allow_of. set (b := ME.zv V (fst bn)) in *. set (n := ME.zv V (snd bn)) in *.
  destruct Hz as [Hz|Hz].
  - exists (ME.pagedown b, ME.pageup (b + n)). split.
    + apply in_flat_map. exists bn. split; [exact Hin|]. cbn. left. reflexivity.
    + cbn [fst snd]. rewrite page_base_of_val by exact R. pose proof (pagedown_spec b) as [Q1 Q1m]. pose proof (pageup_spec (b + n)) as [Q2 Q2m].
      set (u := ME.pagedown b) in *. set (v := ME.pageup (b + n)) in *. clearbody u v. unfold ME.pagedown in *.
      clear -Hz P1 Q1m Q2m. Z.div_mod_to_equations. lia.
  - exists (ME.pagedown (MA.ASHOFF + b / 8), ME.pageup (MA.ASHOFF + (b + n) / 8)). split.
    + apply in_flat_map. exists bn. split; [exact Hin|]. cbn. right. left. reflexivity.
    + cbn [fst snd]. rewrite page_base_of_val by exact R. pose proof (pagedown_spec (MA.ASHOFF + b / 8)) as [Q1 Q1m]. pose proof (pageup_spec (MA.ASHOFF + (b + n) / 8)) as [Q2 Q2m].
      set (u := ME.pagedown (MA.ASHOFF + b / 8)) in *. set (v := ME.pageup (MA.ASHOFF + (b + n) / 8)) in *. clearbody u v. unfold ME.pagedown in *.
      clear -Hz P1 Q1m Q2m. Z.div_mod_to_equations. lia.
Qed.

Lemma vis_in : forall bn, In bn MF.both_vis_app -> In bn MF.both_vis.
Proof. intros bn H. unfold MF.both_vis. apply in_or_app. left. exact H. Qed.
Local Ltac visk k := apply vis_in; unfold MF.both_vis_app; apply (nth_error_In _ k); reflexivity.

Lemma rng0_of : forall lo n, 0 <= lo -> lo + n <= 2 ^ 64 -> (forall z, lo <= z < lo + n -> page_ok (m_vm_lazy mo) A0 (page_base_of z)) -> rng RNG0 lo n.
Proof. intros lo n H1 H2 H3. unfold RNG0. apply rng_fp_ok; assumption. Qed.

Lemma rng0_visp : forall k bn lo n, nth_error MF.both_vis_app k = Some bn ->
  ((ME.pagedown (ME.zv V (fst bn)) <= lo /\ lo + n <= ME.pageup (ME.zv V (fst bn) + ME.zv V (snd bn)))
   \/ (ME.pagedown (MA.ASHOFF + ME.zv V (fst bn) / 8) <= lo /\ lo + n <= ME.pageup (MA.ASHOFF + (ME.zv V (fst bn) + ME.zv V (snd bn)) / 8))) ->
  0 <= lo -> lo + n <= 2 ^ 64 -> rng RNG0 lo n.
Proof.
  intros k bn lo n Hk Hr H1 H2. apply rng0_of; [exact H1| exact H2|]. intros z Hz. right.
  apply (ALV_page bn); [apply vis_in; exact (nth_error_In _ k Hk)| | lia]. destruct Hr as [[A1 A2]|[A1 A2]]; [left| right]; lia.
Qed.
Lemma rng0_vis : forall k bn lo n, nth_error MF.both_vis_app k = Some bn ->
  ((ME.zv V (fst bn) <= lo /\ lo + n <= ME.zv V (fst bn) + ME.zv V (snd bn)) \/ (MA.ASHOFF + ME.zv V (fst bn) / 8 <= lo /\ lo + n <= MA.ASHOFF + (ME.zv V (fst bn) + ME.zv V (snd bn)) / 8)) ->
  0 <= lo -> lo + n <= 2 ^ 64 -> rng RNG0 lo n.
Proof.
  intros k bn lo n Hk Hr H1 H2. apply (rng0_visp k bn lo n Hk); [| exact H1| exact H2].
  pose proof (pagedown_spec (ME.zv V (fst bn))) as [P1 _]. pose proof (pageup_spec (ME.zv V (fst bn) + ME.zv V (snd bn))) as [P2 _].
  pose proof (pagedown_spec (MA.ASHOFF + ME.zv V (fst bn) / 8)) as [P3 _]. pose proof (pageup_spec (MA.ASHOFF + (ME.zv V (fst bn) + ME.zv V (snd bn)) / 8)) as [P4 _].
  destruct Hr as [[A1 A2]|[A1 A2]]; [left| right]; lia.
Qed.

Theorem FPX_main : FPX L RNG0.
Proof.
  unfold FPX. pose proof atop_range as AR. pose proof (ao_fake L ALO) as (F1 & F2 & F3 & _). pose proof (ao_dtls L ALO) as (D1 & D2 & D3 & _).
  revert F1 F2 F3 D1 D2 D3. rewrite al_fake_eq. unfold al_dtls. cbn [al_V L0 VL]. intros F1 F2 F3 D1 D2 D3.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 10%nat) as B10. pose proof (HV 6%nat) as B6.
  split. { apply rng0_of; [lia| lia|]. intros z Hz. left. apply lazy_above; lia. }
  split. { apply rng0_of; [lia| lia|]. intros z Hz. left. apply lazy_image; lia. }
  split. { apply (rng0_visp 11 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [right; split; apply Z.leb_le; vm_compute; reflexivity| lia| lia]. }
  split. { rewrite shad_div. unfold ASHOFF, Shadow.KHIGH. apply (rng0_vis 12 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [right| |]; clear -AR HU0 B0 B10 B6; Z.div_mod_to_equations; lia. }
  unfold afake_rng. rewrite al_fake_eq. unfold al_dtls, FAKESZ, shlen. cbn [al_V L0 VL]. rewrite shad_div, Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2 ^ 3) with 8.
  split. { apply (rng0_vis 3 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia]. }
  split. { apply (rng0_vis 3 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [right| |]; clear -F1 F2 F3 AR; Z.div_mod_to_equations; lia. }
  apply (rng0_vis 4 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia].
Qed.

Theorem arng0_main : arng0 L RNG0.
Proof.
  unfold arng0. pose proof atop_range as AR.
  pose proof (ao_t L ALO) as (T1 & T2 & T3 & _). pose proof (ao_ctx L ALO) as (C1 & C2 & C3 & _). pose proof (ao_nodes L ALO) as (N1 & N2 & N3 & _).
  pose proof (ao_store L ALO) as (ST1 & ST2 & ST3 & _). pose proof (ao_fake L ALO) as (F1 & F2 & F3 & _). pose proof (ao_dtls L ALO) as (D1 & D2 & D3 & _).
  pose proof (ao_space L ALO) as SP. pose proof (ao_res_hi L ALO) as RH. pose proof (ao_res L ALO) as (_ & _ & R3 & _).
  revert T1 T2 T3 C1 C2 C3 N1 N2 N3 ST1 ST2 ST3 F1 F2 F3 D1 D2 D3 SP RH R3.
  rewrite al_t_eq, al_ctx_eq, al_nodes_eq, al_store_eq, al_fake_eq, al_res_eq, al_space_beg_eq. unfold al_dtls. cbn [al_V L0 VL]. intros.
  unfold K_SPACE_SIZE, K_SPACE_EXTRA, shlen. rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2 ^ 3) with 8. change (2 ^ 37) with 137438953472.
  split. { apply rng0_of; [lia| lia|]. intros z Hz. left. apply lazy_image; lia. }
  split. { apply (rng0_vis 7 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia]. }
  split. { apply (rng0_vis 6 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia]. }
  split. { apply (rng0_vis 2 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia]. }
  split. { apply (rng0_vis 1 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia]. }
  split. { apply (rng0_vis 8 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia]. }
  split. { apply (rng0_vis 3 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia]. }
  split. { apply (rng0_vis 3 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [right| |]; clear -F1 F2 F3 AR; Z.div_mod_to_equations; lia. }
  split. { apply (rng0_vis 4 _ _ _ eq_refl); cbn [fst snd ME.zv]; unfold MA.ASHOFF; [left; lia| lia| lia]. }

  apply rng0_of; [clear -SP RH; Z.div_mod_to_equations; lia| clear -SP RH R3 AR; Z.div_mod_to_equations; lia|].
  intros z Hz. right. apply A0_base. left. exists z. split; [| reflexivity]. left.
  rewrite al_space_beg_eq. unfold al_ptr_array, K_SPACE_SIZE. rewrite !shad_div. unfold ASHOFF. change (2 ^ 37) with 137438953472.
  clear -Hz SP RH. Z.div_mod_to_equations. lia.
Qed.

Theorem lazy_shape_main : forall z, (0x10000 <= z < ABase.TwinB.AIMG_HI \/ ATOP <= z < 2 ^ 64) -> page_in_ranges (page_base_of z) (m_vm_lazy mo) = false.
Proof.
  intros z [Hz|Hz]; [apply lazy_image; unfold ABase.TwinB.AIMG_HI in Hz; lia| apply lazy_above; [lia| pose proof atop_range; lia]].
Qed.

Theorem FIXZ_main : FIXZ L (canon mo).
Proof.
  unfold FIXZ, canon. rewrite m_vmmaps_MX, m_vm_lazy_MX, m_halted_MX. split; [| split; [| split]].
  - rewrite (MA.bm_reserved V sp fs mo AMO), segments_reserved_asan. unfold ABase.TwinB.AIMG_HI.
    repeat (apply Forall_cons; [cbn [fst snd]; rewrite !unsigned_lit by lia; lia|]). apply Forall_nil.
  - intros z Hz. apply FKEAGER. rewrite al_fake_eq in Hz. exact Hz.
  - exact (MA.bm_halted V sp fs mo AMO).
  - intros z Hz. rewrite m_vm_lazy_MX. apply lazy_shape_main. unfold C0A in Hz. exact Hz.
Qed.

Theorem ACCT_root : forall aw, bv_unsigned aw <= CRED0 -> ACCT NMAX SHFIX aw L RNG0 sta [] mo.
Proof.
  intros aw Haw. pose proof (bv_unsigned_in_range _ aw) as AWR.
  exists RESV0, A0. split; [exact aresv_ok_main|].
  split.
  { unfold ACCTc. split; [exact INV_main|]. cbn [st0 ainit a_qloc_bytes a_qglob_bytes]. unfold Q_CACHE, Q_MAX.
    split; [lia|]. split; [lia|]. split; [unfold RNG0, canon; rewrite m_vm_lazy_MX; reflexivity|]. split; [lia|].
    split. { rewrite live_chunks_st0. unfold emb_sz. cbn [secbytes st0 ainit a_emb snd]. unfold C_EXH. lia. }
    exists (4796180 + KSH). split; [exact A0_base|]. split; [exact A0_covp|]. split; [exact A0_bud|]. split; [lia|].
    unfold GP, emb_cap, PEMB, pcost, EMB_MAX. cbn [st0 ainit a_emb fst snd]. unfold CRED0 in Haw.
    change (2 ^ 23 / 4096 + 2 ^ 23 / 32768 + 4) with 2308. change ((2 ^ 23 - 0) / 4096) with 2048. lia. }
  split; [exact (MA.bm_mat_nodup V sp fs mo AMO)|]. split; [exact A0_mat|]. split; [exact FPX_main|]. split; [exact FIXZ_main|].
  intros id ch H. cbn [st0 ainit a_live] in H. rewrite lookup_empty in H. discriminate H.
Qed.

End Root.

Theorem h0_at_main {rc : runConstT} :
  forall (UNIV : list (list Z)) (SHFIX : word -> Prop) (KSH : Z) (NMAX : nat) (en : ExecEntry) (inp : ProcInput) (ms : machine_state) (mo : Model) (aw : word),
  univ_ok UNIV -> abud SHFIX KSH -> 0 <= KSH -> 59854612 + KSH <= Z.of_nat NMAX ->
  MA.bmain_at en inp ms mo -> bv_unsigned (en_sp en) = ATOP + 8388608 ->
  bv_unsigned aw <= CRED0 ->
  exists (Lm : alayout) (RNG : footprint) (sta : astate),
       AInstanceU2.TwinB.AHEAPu2 Lm RNG sta [] (ms_mem ms)
    /\ ACCT NMAX SHFIX aw Lm RNG sta [] mo
    /\ incl UNIV (al_U Lm)
    /\ (forall z, (0x10000 <= z < ABase.TwinB.AIMG_HI \/ ATOP <= z < 2 ^ 64) -> page_in_ranges (page_base_of z) (m_vm_lazy mo) = false)
    /\ APristLaw.TwinB.aprist sta.
Proof.
  intros UNIV SHFIX KSH NMAX en inp ms mo aw HU HSH HK HN HM USP Haw.
  destruct HM as (w & V & m & Hms & HV & PIN & HMFall & HPFall & MINV & STK & HID & SH0 & AMO).
  destruct PIN as (_ & _ & _ & P3 & _).
  apply Forall_app in HMFall as [HMF HMFw]. apply Forall_app in HPFall as [HPF _].
  assert (HUSP : usp_pin V) by (unfold usp_pin; lia).
  pose proof (ACCT_root V w UNIV (en_sp en) (in_fs inp) mo HV HPF HUSP HU AMO USP SHFIX KSH HSH HK NMAX HN aw Haw) as AC.
  eexists (L0 V w UNIV), _, (st0 V w UNIV).
  split; [| split; [exact AC|]].
  - rewrite Hms. cbn [ms_mem]. unfold RNG0. eapply (aheapu2_main V w UNIV m); try eassumption.
    eapply (arng0_main V w UNIV (en_sp en) (in_fs inp) mo); eassumption.
  - split; [intros u Hu; exact Hu|].
    split; [| exact (aprist_main V w UNIV)].
    intros z Hz. eapply (lazy_shape_main V); eassumption.
Qed.
End TwinB.
