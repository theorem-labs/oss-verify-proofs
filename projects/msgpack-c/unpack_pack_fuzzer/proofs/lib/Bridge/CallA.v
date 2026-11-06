(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.PropExec ALib.MState ALib.Frame ALib.Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Instr Mem State Step Plan ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import GlueA Actr.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP CtrLib CtrFX ActrA.
Open Scope Z_scope.
Unset Lia Cache.

Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require KnownT.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require KnownA.
Unset Nia Cache. Unset Nra Cache.
Module AMem := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.

Section CallA.
Variable segs : list Segment.
Variable OPS : optable.

Lemma stack_sound_g : forall E st ms mo need,
  st_ok segs OPS E st ms mo -> to_Z need < 2 ^ 32 -> stack_room_g st need = true ->
  exists k off r ksp, getr st X2 = VP k off /\ IMap.find k (s_regs st) = Some r /\ PrimInt63.eqb k 0%uint63 = false
    /\ okey off = Some ksp /\ keyZ ksp mod 16 = 0
    /\ bv_unsigned (ev E k) mod 16 = 0
    /\ bv_unsigned (den E (getr st X2)) = bv_unsigned (ev E k) + keyZ ksp
    /\ 0 <= bv_unsigned (ev E k) + keyZ ksp - to_Z need
    /\ bv_unsigned (ev E k) + keyZ ksp < 2 ^ 64
    /\ AF.stk segs (ms_mem ms) (bv_unsigned (ev E k) + loZ r) (bv_unsigned (ev E k) + keyZ ksp)
    /\ sp_region st = Some (k, off, r) /\ loZ r <= keyZ ksp - to_Z need /\ 0 <= bv_unsigned (ev E k) + loZ r.
Proof.
  intros E st ms mo need HS Hneed H. unfold stack_room_g, sp_region in H.
  destruct (getr st X2) as [|k off| | | | | | | | |] eqn:HX2; try discriminate.
  destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate].
  match type of H with match (if ?c then _ else _) with _ => _ end = _ => destruct c eqn:CK; [|discriminate] end.
  do 4 (apply andb_prop in CK as [CK ?]). rename H0 into BGN, H1 into ALN, H2 into AL16, H3 into HW. apply negb_true_iff in CK.
  destruct (okey (wsub off (wlit need))) as [klo|] eqn:Hklo; [|discriminate].
  destruct (okey off) as [ksp|] eqn:Hksp; [|discriminate].
  destruct (rg_hi r) as [h| | | | | | | | | |] eqn:Hhi; try discriminate.
  destruct (okey h) as [kh|] eqn:Hkh; [|discriminate].
  do 2 (apply andb_prop in H as [H ?]). rename H into L1, H0 into L2, H1 into L3.
  rewrite kleb_keyZ in L1, L2, L3. apply Z.leb_le in L1. apply Z.leb_le in L2. apply Z.leb_le in L3.
  destruct (okey_sound _ _ Hksp) as [Eksp Rksp]. destruct (okey_sound _ _ Hklo) as [Eklo Rklo]. destruct (okey_sound _ _ Hkh) as [Ekh Rkh].
  rewrite !half63 in Rksp, Rklo, Rkh.
  assert (Eneed : w2Zs (wlit need) = to_Z need) by (rewrite w2Zs_eq, wlit_ok; cbn [wt wlit]; lia).
  pose proof (int_range need) as Rn. rewrite two63_eq in Rn.
  assert (Eklo' : keyZ klo = keyZ ksp - to_Z need).
  { rewrite Eklo, (GlueA.w2Zs_wsub_small); [rewrite Eneed, Eksp; reflexivity|]. rewrite Eneed, <- Eksp. unfold two63 in *. lia. }
  pose proof (so_reg _ _ _ _ _ _ HS _ _ Hr) as RO.
  pose proof (ro_range _ _ _ _ _ _ RO CK) as [RLO RHI]. unfold two64 in RHI.
  assert (Ehi : keyZ kh <= hiZ E r).
  { unfold hiZ. rewrite Hhi, unsigned_VL, Ekh, w2Zs_eq. unfold two64. destruct (wt h); lia. }
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  assert (A16 : bv_unsigned (ev E k) mod 16 = 0).
  { pose proof (find_align_le E (s_facts st) HF k 4%uint63 ALN) as X. change (2 ^ to_Z 4%uint63) with 16 in X. exact X. }
  assert (K16 : keyZ ksp mod 16 = 0).
  { apply Uint63.eqb_correct in AL16.
    assert (WL : wl off = ksp). { unfold okey in Hksp. destruct (wt off); [destruct (PrimInt63.leb bit62i (wl off))| destruct (PrimInt63.ltb (wl off) bit62i)]; congruence. }
    rewrite WL in AL16.
    pose proof (land_mk ksp 4%uint63 ltac:(change (to_Z 4%uint63) with 4; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 4) 1)%uint63 with 15%uint63 in LM. rewrite AL16 in LM.
    change (to_Z 0%uint63) with 0 in LM. change (2 ^ to_Z 4%uint63) with 16 in LM.
    destruct (keyZ_cases ksp) as [[_ ->]|[_ ->]]; [lia|].
    replace (to_Z ksp - 2 ^ 63) with (to_Z ksp + (- 2 ^ 59) * 16) by lia. rewrite Z.mod_add by lia. lia. }
  assert (Esp : bv_unsigned (den E (VP k off)) = bv_unsigned (ev E k) + keyZ ksp).
  { rewrite den_VP, <- Eksp. unfold loZ in *. apply Z.mod_small. unfold two64. lia. }
  exists k, off, r, ksp. split; [reflexivity|]. split; [exact Hr|]. split; [exact CK|]. split; [exact Hksp|]. split; [exact K16|].
  split; [exact A16|]. split; [exact Esp|]. unfold loZ in *. split; [lia|]. split; [lia|].
  split.
  { unfold AF.stk. split; [lia|]. split; [lia|]. intros a Ha.
    destruct (ro_valid _ _ _ _ _ _ RO CK a ltac:(unfold loZ; lia)) as (V1 & V2 & _).
    split; [apply (GlueA.wb_wviewA segs); apply V2; exact HW|]. rewrite (GlueA.rb_mrdA segs) in V1.
    destruct (AMem.mrd segs (ms_mem ms) (AMem.wa a)); [eexists; reflexivity| congruence]. }
  split; [| split; [lia| lia]].
  unfold sp_region. rewrite HX2, Hr. rewrite CK. cbn [negb andb]. rewrite HW, AL16, ALN, BGN. reflexivity.
Qed.

Lemma sp_region_inv : forall st k off r, sp_region st = Some (k, off, r) ->
  getr st X2 = VP k off /\ IMap.find k (s_regs st) = Some r /\ PrimInt63.eqb k 0%uint63 = false /\ rg_w r = true /\ rg_bg r = BGNone.
Proof.
  intros st k off r H. unfold sp_region in H.
  destruct (getr st X2) as [|k0 off0| | | | | | | | |]; try discriminate. destruct (IMap.find k0 (s_regs st)) as [r0|] eqn:F; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end. injection H as -> -> ->.
  do 4 (apply andb_prop in CK as [CK ?]). apply negb_true_iff in CK.
  repeat (split; [reflexivity || assumption|]). destruct (rg_bg r); try discriminate. reflexivity.
Qed.

Lemma reg_of_X8 : reg_of_r5 X8 = 8%bv. Proof. apply bv_eq. reflexivity. Qed.

Lemma amalloc_regs : forall E st ms mo r tp cred,
  st_ok segs OPS E st ms mo ->
  call_pre st = Some r -> getr st X4 = VL tp -> weqb tp (wlit ATPi) = true ->
  KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) (getr st X10) = true -> KnownT.KnownT.known_leu_t (s_facts st) (getr st X10) (VL AREQMAXw) = true ->
  cred_pre (s_facts st) (getr st X10) cred = true ->
  let R := ms_regs ms in
  s_resv st = RNone
  /\ AP.getr R 1 = Z_to_bv 64 (to_Z r) /\ 0 <= to_Z r < 2 ^ 62
  /\ AP.getr R 4 = Z_to_bv 64 (to_Z ATPi)
  /\ 0 < bv_unsigned (AP.getr R 10) <= 0xFFF00000
  /\ (1048576 <= bv_unsigned (den E cred)
      /\ (prim_decided (s_facts st) (getr st X10) = true \/ bv_unsigned (AP.getr R 10) <= bv_unsigned (den E cred))).
Proof.
  intros E st ms mo r tp cred HS CP TP TPE N0 N1 NC R.
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  pose proof (getr_RA segs OPS E st ms mo HS) as GR.
  destruct (HeapCtr.call_pre_inv st r CP) as (_ & (ra & Hra & WT & LT & ->)).
  split; [exact (HeapCtr.call_pre_resv st _ CP)|].
  assert (ERA : ra = wlit (wl ra)) by (destruct ra as [t l]; cbn in WT |- *; subst t; reflexivity).
  split. { subst R. rewrite <- HeapCtr.reg_of_X1, (GR X1), Hra, ERA, HeapCtr.den_wlit. reflexivity. }
  split. { apply Uint63.ltb_spec in LT. rewrite to_Z_bit62i in LT. pose proof (int_range (wl ra)) as RR. split; [apply RR| exact LT]. }
  split. { subst R. rewrite <- HeapCtr.reg_of_X4, (GR X4), TP. apply (proj1 (weqb_ok _ _)) in TPE. subst tp. rewrite HeapCtr.den_wlit. reflexivity. }
  pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF N0) as L0. pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF N1) as L1.
  unfold cred_pre in NC. apply andb_prop in NC as [NCX NC].
  pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF NCX) as LX. replace (bv_unsigned (den E (VL C_EXHw))) with 1048576 in LX by (vm_compute; reflexivity).
  cbn [den] in L0, L1. rewrite wbv_unsigned in L0, L1. rewrite wzero_ok in L0.
  subst R. rewrite <- HeapCtr.reg_of_X10, (GR X10).
  split. { split; [exact L0|]. replace 0xFFF00000 with (w2Z AREQMAXw) by (vm_compute; reflexivity). exact L1. }
  split; [exact LX|]. apply orb_prop in NC as [NC|NC]; [left; exact NC| right; exact (KnownA.KnownA.known_leu_sound E _ _ _ HF NC)].
Qed.

Lemma acall_regs : forall E st ms mo r tp,
  st_ok segs OPS E st ms mo -> call_pre st = Some r -> getr st X4 = VL tp -> weqb tp (wlit ATPi) = true ->
  let R := ms_regs ms in
  s_resv st = RNone /\ AP.getr R 1 = Z_to_bv 64 (to_Z r) /\ 0 <= to_Z r < 2 ^ 62 /\ AP.getr R 4 = Z_to_bv 64 (to_Z ATPi).
Proof.
  intros E st ms mo r tp HS CP TP TPE R.
  pose proof (getr_RA segs OPS E st ms mo HS) as GR.
  destruct (HeapCtr.call_pre_inv st r CP) as (_ & (ra & Hra & WT & LT & ->)).
  split; [exact (HeapCtr.call_pre_resv st _ CP)|].
  assert (ERA : ra = wlit (wl ra)) by (destruct ra as [t l]; cbn in WT |- *; subst t; reflexivity).
  split. { subst R. rewrite <- HeapCtr.reg_of_X1, (GR X1), Hra, ERA, HeapCtr.den_wlit. reflexivity. }
  split. { apply Uint63.ltb_spec in LT. rewrite to_Z_bit62i in LT. pose proof (int_range (wl ra)) as RR. split; [apply RR| exact LT]. }
  subst R. rewrite <- HeapCtr.reg_of_X4, (GR X4), TP. apply (proj1 (weqb_ok _ _)) in TPE. subst tp. rewrite HeapCtr.den_wlit. reflexivity.
Qed.
Lemma unw_stop_sound : forall E st ms mo, st_ok segs OPS E st ms mo -> unw_stop st = true ->
  bv_unsigned (AP.getr (ms_regs ms) 8) <= bv_unsigned (AP.getr (ms_regs ms) 2).
Proof.
  intros E st ms mo HS UNW. pose proof (so_facts _ _ _ _ _ _ HS) as HF. pose proof (getr_RA segs OPS E st ms mo HS) as GR.
  unfold unw_stop in UNW. pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF UNW) as L3.
  rewrite <- reg_of_X8, <- HeapCtr.reg_of_X2, (GR X8), (GR X2). exact L3.
Qed.

Lemma block_of_twin_sound : forall E fs sh k, facts_hold E fs -> block_of_twin fs sh = Some k ->
  bv_unsigned (ev E sh) = (bv_unsigned (ev E k) / 8 + 0x7fff8000) mod 2 ^ 64.
Proof.
  intros E fs sh k HF. unfold block_of_twin. induction fs as [|f fs IH]; intros H; [discriminate|].
  inversion HF as [|f' l Hf HF']; subst.
  assert (STEP : (fix go (l : list fact) : option int :=
                    match l with
                    | FEq (VP sh' o) (VAlu ALU_ADD (VAlu ALU_SRL (VP k o') (VL c3)) (VL sb)) :: l' =>
                        if PrimInt63.eqb sh sh' && weqb o wzero && weqb o' wzero && weqb c3 (wlit 3%uint63) && weqb sb SBw then Some k else go l'
                    | _ :: l' => go l'
                    | [] => None
                    end) fs = Some k -> bv_unsigned (ev E sh) = (bv_unsigned (ev E k) / 8 + 0x7fff8000) mod 2 ^ 64) by exact (IH HF').
  destruct f as [| | | |x y| | |]; try (apply STEP; exact H).
  destruct x as [|sh0 z| | | | | | | | |]; try (apply STEP; exact H).
  destruct y as [| |op y1 y2| | | | | | | |]; try (apply STEP; exact H). destruct op; try (apply STEP; exact H).
  destruct y1 as [| |op1 u1 u2| | | | | | | |]; try (apply STEP; exact H). destruct op1; try (apply STEP; exact H).
  destruct u1 as [|k' z'| | | | | | | | |]; try (apply STEP; exact H). destruct u2 as [c| | | | | | | | | |]; try (apply STEP; exact H).
  destruct y2 as [s'| | | | | | | | | |]; try (apply STEP; exact H).
  destruct (PrimInt63.eqb sh sh0 && weqb z wzero && weqb z' wzero && weqb c (wlit 3%uint63) && weqb s' SBw) eqn:C; [|apply STEP; exact H].
  injection H as ->. apply andb_prop in C as [C S']. apply andb_prop in C as [C C3]. apply andb_prop in C as [C Z']. apply andb_prop in C as [K' Z0].
  apply weqb_eq in Z0. apply weqb_eq in Z'. apply weqb_eq in S'. apply weqb_eq in C3. apply Uint63.eqb_correct in K'. subst z z' s' c sh0.
  cbn [fact_holds] in Hf. rewrite HeapCtr.den_VPz in Hf. rewrite Hf.
  change (den E (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw)))
    with (alu64 ALU_ADD (alu64 ALU_SRL (den E (VP k wzero)) (wbv (wlit 3%uint63))) (wbv SBw)).
  rewrite HeapCtr.den_VPz.
  unfold alu64, alu. rewrite bv_add_unsigned, bv_shiftr_unsigned, bv_and_unsigned.
  replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
  replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  replace (bv_unsigned (wbv SBw)) with 0x7fff8000 by (vm_compute; reflexivity).
  unfold bv_wrap, bv_modulus. reflexivity.
Qed.

Lemma twin_arm_old_inv : forall fs R wl0 sh len, twin_arm_old fs R wl0 sh len = true ->
  exists k r n, block_of_twin fs sh = Some k /\ IMap.find sh R = Some r /\ CtrA.win_lookup wl0 k = Some (n, CtrLib.K_BLOCK)
    /\ len_is_twin fs len n = true /\ (prim_decided fs n = true \/ (is_twin_region r n = true /\ size_shape_ok fs n = true)
                             \/ (is_twin_main r n = true /\ exists s2, tail_scan fs R sh n = Some s2)).
Proof.
  intros fs R wl0 sh len H1. unfold twin_arm_old in H1.
  destruct (block_of_twin fs sh) as [k|] eqn:BT; [|discriminate]. destruct (IMap.find sh R) as [r|] eqn:FR; [|discriminate].
  destruct (CtrA.win_lookup wl0 k) as [[n kdb]|] eqn:WL; [|discriminate].
  apply andb_prop in H1 as [H1 ALT]. apply andb_prop in H1 as [KB LEN]. apply weqb_eq in KB. subst kdb.
  exists k, r, n. repeat (split; [reflexivity || assumption|]).

  apply orb_prop in ALT as [ALT|PD]; [| left; exact PD].
  apply orb_prop in ALT as [CAN|PAIR]; [right; left; apply andb_prop in CAN; exact CAN|].
  right. right. apply andb_prop in PAIR as [TM TS]. split; [exact TM|]. destruct (tail_scan fs R sh n) as [s2|]; [exists s2; reflexivity| discriminate TS].
Qed.

Lemma twin_arm_ev_inv : forall fs R wl0 cv sh len kx, twin_arm_ev fs R wl0 cv sh len kx = true ->
  exists lw kb,
    len = VL lw /\ block_of_twin fs sh = Some kb /\ wt lw = false /\ to_Z (wl lw) <= 8064 /\ PrimInt63.leb 3%uint63 (find_align fs kb) = true
    /\ (In kb cv
        \/ exists ks lens kd r o2 o1,
             In (ks, lens, kd) wl0 /\ ks <> kx /\ kd <> CtrLib.K_BLOCK /\ weqb kd K_TWIN = false
             /\ IMap.find ks R = Some r /\ rg_w r = true /\ rg_lo r = 0%uint63 /\ KnownT.KnownT.known_ltu_t fs (VL wzero) (rg_hi r) = true
             /\ GTwinSub.GTwinSub.find_lb fs ks kb = Some o2 /\ find_ub_g fs ks = Some (kb, o1) /\ wt o2 = false /\ wt o1 = false
             /\ nowrap_kb fs kb o2 = true /\ to_Z (wl o1) + 8 <= 8 * to_Z (wl lw)).
Proof.
  intros fs R wl0 cv sh len kx H. unfold twin_arm_ev in H. destruct len as [lw| | | | | | | | | |]; try discriminate H.
  destruct (block_of_twin fs sh) as [kb|] eqn:BT; [|discriminate H].
  apply andb_prop in H as [H EX]. apply andb_prop in H as [H AL]. apply andb_prop in H as [WT LE].
  apply negb_true_iff in WT. apply Uint63.leb_spec in LE. change (to_Z 8064%uint63) with 8064 in LE.
  exists lw, kb. repeat (split; [reflexivity || assumption|]).
  apply orb_prop in EX as [CV|EX].
  { left. apply existsb_exists in CV as (x & Hx & Q). apply Uint63.eqb_correct in Q. subst x. exact Hx. }
  right.
  apply existsb_exists in EX as ([[ks lens] kd] & Hin & EV). unfold own_ev1 in EV.
  apply andb_prop in EV as [EV M]. apply andb_prop in EV as [EV NT]. apply andb_prop in EV as [NX NB].
  apply negb_true_iff in NX. apply Uint63.eqb_false_spec in NX. apply negb_true_iff in NT.
  assert (NKB : kd <> CtrLib.K_BLOCK). { intros ->. apply negb_true_iff in NB. rewrite weqb_refl in NB. discriminate NB. }
  destruct (IMap.find ks R) as [r|] eqn:FR; [|discriminate M].
  apply andb_prop in M as [M F]. apply andb_prop in M as [M POS]. apply andb_prop in M as [RW L0]. apply Uint63.eqb_correct in L0.
  destruct (GTwinSub.GTwinSub.find_lb fs ks kb) as [o2|] eqn:LB; [|discriminate F]. destruct (find_ub_g fs ks) as [[kb' o1]|] eqn:UB; [|discriminate F].
  apply andb_prop in F as [F LE8]. apply andb_prop in F as [F O1S]. apply andb_prop in F as [F NW]. apply andb_prop in F as [F WT1]. apply andb_prop in F as [EKB WT2].
  apply Uint63.eqb_correct in EKB. subst kb'. apply negb_true_iff in WT1. apply negb_true_iff in WT2.
  apply Uint63.leb_spec in LE8. apply Uint63.leb_spec in O1S. change (to_Z 64512%uint63) with 64512 in O1S.
  rewrite Uint63.add_spec, lsl_spec in LE8. change (to_Z 8%uint63) with 8 in LE8. change (to_Z 3%uint63) with 3 in LE8. change (2 ^ 3) with 8 in LE8.
  pose proof (int_range (wl o1)) as R1. pose proof (int_range (wl lw)) as R2. change wB with (2 ^ 63) in *.
  rewrite !Z.mod_small in LE8 by lia.
  exists ks, lens, kd, r, o2, o1. repeat (split; [reflexivity || assumption|]). lia.
Qed.

Lemma carg_vecs_spec : forall st md A nw rest kb, find_op HEAP_ID (s_ops st) = Some (VL md :: A :: VL nw :: rest) -> In kb (carg_vecs st) ->
  exists i, In i (VECS (w2Z md)) /\ nth_error (skipn (3 * Z.to_nat (to_Z (wl nw))) rest) i = Some (VP kb wzero).
Proof.
  intros st md A nw rest kb Hf H. unfold carg_vecs in H. rewrite Hf in H. apply in_flat_map in H as (i & Hi & Hk). exists i. split; [exact Hi|].
  unfold carg_anchor in Hk. destruct (nth_error (skipn (3 * Z.to_nat (to_Z (wl nw))) rest) i) as [v|]; [| destruct Hk].
  destruct v as [|k o| | | | | | | | |]; try (destruct Hk). destruct (weqb o wzero) eqn:Q; [| destruct Hk]. apply weqb_eq in Q. subst o.
  destruct Hk as [->|[]]. reflexivity.
Qed.
Lemma twin_lit_inv : forall len, twin_lit len = true -> exists lw, len = VL lw /\ wt lw = false /\ to_Z (wl lw) <= 8064.
Proof.
  intros len H. unfold twin_lit in H. destruct len as [lw| | | | | | | | | |]; try discriminate H. apply andb_prop in H as [WT LE].
  apply negb_true_iff in WT. apply Uint63.leb_spec in LE. change (to_Z 8064%uint63) with 8064 in LE. exists lw. auto.
Qed.

Lemma srl3_den_raw : forall E xs, bv_unsigned (den E (VAlu ALU_SRL xs (VL (wlit 3%uint63)))) = bv_unsigned (den E xs) / 8.
Proof.
  intros E xs. cbn [den]. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned.
  replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
  replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma and7_den_raw : forall E xs, bv_unsigned (den E (VAlu ALU_AND xs (VL (wlit 7%uint63)))) = bv_unsigned (den E xs) mod 8.
Proof.
  intros E xs. cbn [den]. unfold alu64, alu. rewrite bv_and_unsigned, wbv_unsigned, wlit_ok.
  change (to_Z 7%uint63) with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma tie_of_holds : forall E fs len xs, facts_hold E fs -> tie_of fs len = Some xs -> bv_unsigned (den E len) = bv_unsigned (den E xs) / 8.
Proof.
  intros E fs len xs HF. induction fs as [|f fs IH]; intros H; [discriminate H|].
  pose proof (Forall_inv HF) as Hf. pose proof (Forall_inv_tail HF) as HF'.
  assert (STEP : tie_of fs len = Some xs -> bv_unsigned (den E len) = bv_unsigned (den E xs) / 8) by (intros X; exact (IH HF' X)).
  cbn [tie_of] in H. destruct f as [| | | |a b| | |]; try (apply STEP; exact H).
  destruct b as [| |op u1 u2| | | | | | | |]; try (apply STEP; exact H). destruct op; try (apply STEP; exact H).
  destruct u2 as [c3| | | | | | | | | |]; try (apply STEP; exact H).
  destruct (sv_eqb a len && weqb c3 (wlit 3%uint63)) eqn:C; [| apply STEP; exact H].
  injection H as ->. apply andb_prop in C as [C1 C3]. apply ValP.sv_eqb_eq in C1. apply weqb_eq in C3. subst a c3.
  cbn [fact_holds] in Hf. rewrite Hf. exact (srl3_den_raw E xs).
Qed.
Lemma find_ub_sym_holds : forall E fs ks oU kb xs, facts_hold E fs -> find_ub_sym fs ks = Some (oU, kb, xs) ->
  wt oU = false /\ bv_unsigned (den E (VP ks oU)) <= bv_unsigned (den E (VAlu ALU_ADD (VP kb wzero) xs)).
Proof.
  intros E fs ks oU kb xs HF. induction fs as [|f fs IH]; intros H; [discriminate H|].
  pose proof (Forall_inv HF) as Hf. pose proof (Forall_inv_tail HF) as HF'.
  assert (STEP : find_ub_sym fs ks = Some (oU, kb, xs) -> wt oU = false /\ bv_unsigned (den E (VP ks oU)) <= bv_unsigned (den E (VAlu ALU_ADD (VP kb wzero) xs)))
    by (intros X; exact (IH HF' X)).
  cbn [find_ub_sym] in H. destruct f as [| | |a b| | | |]; try (apply STEP; exact H).
  destruct a as [|k o| | | | | | | | |]; try (apply STEP; exact H).
  destruct b as [| |op u1 u2| | | | | | | |]; try (apply STEP; exact H). destruct op; try (apply STEP; exact H).
  destruct u1 as [|kb' z| | | | | | | | |]; try (apply STEP; exact H).
  destruct (PrimInt63.eqb k ks && weqb z wzero && negb (wt o)) eqn:C; [| apply STEP; exact H].
  injection H as -> -> ->. apply andb_prop in C as [C WT]. apply andb_prop in C as [K Z0]. apply Uint63.eqb_correct in K. apply weqb_eq in Z0. subst k z.
  apply negb_true_iff in WT. split; [exact WT|]. exact Hf.
Qed.
Lemma twin_small_sound : forall E fs len, facts_hold E fs -> twin_small fs len = true -> bv_unsigned (den E len) <= 8064.
Proof.
  intros E fs len HF H. unfold twin_small in H. apply orb_prop in H as [H|H].
  - destruct (twin_lit_inv _ H) as (lw & -> & WT & LW). cbn [den]. rewrite wbv_unsigned. unfold w2Z. rewrite WT. exact LW.
  - pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF H) as LE. replace (bv_unsigned (den E (VL (wlit 8064%uint63)))) with 8064 in LE by (vm_compute; reflexivity). exact LE.
Qed.
Lemma twins_scan_sound : forall fs R wl0 wl sh len kd, twins_scan fs R wl0 wl = true -> In (sh, len, kd) wl -> weqb kd K_TWIN = true ->
  twin_arm_old fs R wl0 sh len = true \/ twin_small fs len = true.
Proof.
  intros fs R wl0 wl. induction wl as [|[[sh0 len0] kd0] wl IH]; intros sh len kd H Hin KD; [destruct Hin|].
  cbn [twins_scan] in H. apply andb_prop in H as [H1 H2].
  destruct Hin as [Hin|Hin]; [| exact (IH sh len kd H2 Hin KD)].
  injection Hin as -> -> ->. rewrite KD in H1. apply orb_prop in H1. destruct H1 as [X|X]; [| right; exact X].
  apply orb_prop in X. destruct X as [X|X]; [right; unfold twin_small; rewrite X; reflexivity| left; exact X].
Qed.
Lemma twins_apart_inv : forall fs R wl cv kf sh k len kd, twins_apart fs R wl cv kf sh = true -> In (k, len, kd) wl -> weqb kd K_TWIN = true -> k <> sh ->
  twin_arm_old fs R wl k len = true \/ twin_arm_evx fs R wl cv k len kf = true.
Proof.
  intros fs R wl cv kf sh k len kd H Hin KD NS. unfold twins_apart in H. pose proof (proj1 (forallb_forall _ _) H _ Hin) as C. cbv beta iota in C.
  rewrite KD in C. cbn [negb orb] in C. replace (PrimInt63.eqb k sh) with false in C by (symmetry; apply Uint63.eqb_false_spec; exact NS).
  cbn [orb] in C. apply orb_prop in C. exact C.
Qed.

Lemma twin_canon_inv : forall st wl kf sh, twin_canon st wl kf sh = true ->
  exists r n kdn lent kdt, IMap.find sh (s_regs st) = Some r /\ CtrA.win_lookup wl kf = Some (n, kdn) /\ CtrA.win_lookup wl sh = Some (lent, kdt)
    /\ is_twin_region r n = true /\ size_shape_ok (s_facts st) n = true /\ len_is_twin (s_facts st) lent n = true
    /\ twins_apart (s_facts st) (s_regs st) wl (carg_vecs st) kf sh = true
    /\ no_tail_at (s_facts st) (s_regs st) sh n = true.
Proof.
  intros st wl kf sh H. unfold twin_canon in H. destruct (IMap.find sh (s_regs st)) as [r|]; [|discriminate].
  destruct (CtrA.win_lookup wl kf) as [[n kdn]|]; [|discriminate]. destruct (CtrA.win_lookup wl sh) as [[lent kdt]|]; [|discriminate].
  apply andb_prop in H as [H NT]. apply andb_prop in H as [H TA]. apply andb_prop in H as [H LEN]. apply andb_prop in H as [TR SS].
  exists r, n, kdn, lent, kdt. repeat (split; [reflexivity || assumption|]). exact NT.
Qed.

Lemma prim_decided_sound : forall E fs n, facts_hold E fs -> prim_decided fs n = true -> bv_unsigned (den E n) <= 64512.
Proof.
  intros E fs n HF H. unfold prim_decided in H. pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF H) as LE.
  replace (bv_unsigned (den E (VL PRIM_MAXw))) with 64512 in LE by (vm_compute; reflexivity). exact LE.
Qed.

Lemma sz_and7_den : forall E n, bv_unsigned (den E (sz_and7 n)) = bv_unsigned (den E n) mod 8.
Proof.
  intros E n. unfold sz_and7. rewrite ValP.den_sv_alu. cbn [den]. unfold alu64, alu. rewrite bv_and_unsigned, wbv_unsigned, wlit_ok.
  change (to_Z 7%uint63) with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma sz_last_den : forall E n, 1 <= bv_unsigned (den E n) -> bv_unsigned (den E (sz_last n)) = (bv_unsigned (den E n) - 1) / 8.
Proof.
  intros E n N1. unfold sz_last. rewrite !ValP.den_sv_alu. cbn [den]. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned.
  replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
  replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite bv_add_unsigned. replace (bv_unsigned (wbv wones)) with (2 ^ 64 - 1) by (vm_compute; reflexivity).
  pose proof (bv_unsigned_in_range 64 (den E n)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (bv_unsigned (den E n) + (2 ^ 64 - 1)) with (bv_unsigned (den E n) - 1 + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma twin_len_den : forall E n, bv_unsigned (den E n) + 7 < 2 ^ 62 ->
  bv_unsigned (den E (twin_len n)) = (bv_unsigned (den E n) + 7) / 8.
Proof.
  intros E n B.
  assert (GEN : bv_unsigned (den E (sv_alu ALU_SRL (sv_alu ALU_ADD n (VL (wlit 7%uint63))) (VL (wlit 3%uint63)))) = (bv_unsigned (den E n) + 7) / 8).
  { rewrite !ValP.den_sv_alu. cbn [den]. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned, bv_add_unsigned.
    replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
    replace (bv_unsigned (wbv (wlit 7%uint63))) with 7 by (vm_compute; reflexivity).
    replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
    change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold bv_wrap, bv_modulus. pose proof (bv_unsigned_in_range 64 (den E n)) as R. rewrite Z.mod_small by (change (2 ^ Z.of_N 64) with (2^64); lia).
    reflexivity. }
  destruct n as [w| | | | | | | | | |]; try exact GEN.
  cbn [twin_len]. rewrite !unsigned_VL in *. rewrite wlit_ok.
  assert (WT : wt w = false). { rewrite w2Z_wt. apply Z.leb_gt. unfold two63. lia. }
  rewrite (w2Z_nowt w WT) in *. rewrite lsr_spec, Uint63.add_spec. change (to_Z 3%uint63) with 3. change (to_Z 7%uint63) with 7. change (2 ^ 3) with 8.
  rewrite Z.mod_small; [reflexivity|]. pose proof (int_range (wl w)). change wB with (2 ^ 63). lia.
Qed.

Lemma al8_spec : forall o, al8 o = true -> wt o = false /\ w2Zs o = to_Z (wl o) /\ to_Z (wl o) mod 8 = 0.
Proof.
  intros o H. unfold al8 in H. apply andb_prop in H as [T L]. apply negb_true_iff in T. apply Uint63.eqb_correct in L.
  split; [exact T|]. split; [rewrite w2Zs_eq; unfold w2Z; rewrite T; lia|].
  pose proof (ValP.land_mk (wl o) 3%uint63 ltac:(change (to_Z 3%uint63) with 3; lia)) as LM.
  change (PrimInt63.sub (PrimInt63.lsl 1 3) 1)%uint63 with 7%uint63 in LM. rewrite L in LM. change (to_Z 0%uint63) with 0 in LM.
  change (2 ^ to_Z 3%uint63) with 8 in LM. lia.
Qed.

Lemma mod64_mod8 : forall x, (x mod 2 ^ 64) mod 8 = x mod 8.
Proof. intros x. symmetry. apply Znumtheory.Zmod_div_mod; [reflexivity| reflexivity| exists (2 ^ 61); reflexivity]. Qed.

Lemma has_fact_holds : forall E f fs, facts_hold E fs -> has_fact f fs = true -> fact_holds E f.
Proof.
  intros E f fs HF. induction fs as [|g fs IH]; intros H; [discriminate H|]. cbn [has_fact] in H.
  apply Forall_cons_iff in HF as [Hg HF]. destruct (fact_eqb f g) eqn:Q; [| exact (IH HF H)].
  apply ValP.fact_eqb_eq in Q. subst g. exact Hg.
Qed.

Lemma div8_holds : forall E fs xs, facts_hold E fs -> div8 fs xs = true -> bv_unsigned (den E xs) mod 8 = 0.
Proof.
  intros E fs xs HF H. unfold div8 in H. pose proof (has_fact_holds E _ _ HF H) as FH. cbn [fact_holds] in FH.
  pose proof (f_equal bv_unsigned FH) as Q. rewrite and7_den_raw in Q. rewrite Q. vm_compute. reflexivity.
Qed.

Lemma alk_lit_spec : forall k o, to_Z k <= 63 -> alk_lit k o = true -> wt o = false /\ w2Zs o = to_Z (wl o) /\ to_Z (wl o) mod 2 ^ (to_Z k) = 0.
Proof.
  intros k o Hk H. unfold alk_lit in H. apply andb_prop in H as [T L]. apply negb_true_iff in T. apply Uint63.eqb_correct in L.
  split; [exact T|]. split; [rewrite w2Zs_eq; unfold w2Z; rewrite T; lia|].
  pose proof (ValP.land_mk (wl o) k Hk) as LM. rewrite L in LM. change (to_Z 0%uint63) with 0 in LM. lia.
Qed.
Lemma mod64_mod2k : forall x k, 0 <= k <= 64 -> (x mod 2 ^ 64) mod 2 ^ k = x mod 2 ^ k.
Proof.
  intros x k Hk. symmetry. apply Znumtheory.Zmod_div_mod; [apply Z.pow_pos_nonneg; lia| apply Z.pow_pos_nonneg; lia|].
  exists (2 ^ (64 - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma mod8_mod2k : forall x k, 0 <= k <= 3 -> x mod 8 = 0 -> x mod 2 ^ k = 0.
Proof.
  intros x k Hk H. apply Znumtheory.Zmod_divide in H; [|lia]. apply Znumtheory.Zdivide_mod. destruct H as [q ->].
  exists (q * 2 ^ (3 - k)). rewrite <- Z.mul_assoc. f_equal. change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma alk_sv_sound : forall E fs v, facts_hold E fs -> forall kk, to_Z kk <= 3 -> alk_sv kk fs v = true -> bv_unsigned (den E v) mod 2 ^ (to_Z kk) = 0.
Proof.
  intros E fs v HF. induction v as [c|n o|op a IHa b IHb| |mo a IHa b IHb| | | | | |]; intros kk Hk H; cbn [alk_sv] in H; fold alk_sv in H;
    pose proof (int_range kk) as KR;
    (destruct (PrimInt63.eqb kk 0%uint63) eqn:K0; [apply Uint63.eqb_correct in K0; subst kk; change (2 ^ to_Z 0%uint63) with 1; apply Z.mod_1_r|]);
    (destruct (div8 fs _) eqn:D8; [apply mod8_mod2k; [lia| exact (div8_holds E fs _ HF D8)]|]); try discriminate H.
  - destruct (alk_lit_spec kk c ltac:(lia) H) as (T & _ & M). destruct c as [t l]. cbn [wt wl] in T, M. subst t.
    change (W64 false l) with (wlit l). rewrite HeapCtr.den_wlit. unfold ALib.Mem.wa. rewrite Z_to_bv_small; [exact M|].
    pose proof (int_range l) as R. rewrite two63_eq in R. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). unfold two64. lia.
  - apply andb_prop in H as [A8 AL]. destruct (alk_lit_spec kk o ltac:(lia) A8) as (T & ZS & M).
    assert (AN : bv_unsigned (ev E n) mod 2 ^ (to_Z kk) = 0).
    { destruct (PrimInt63.leb kk (find_align fs n)) eqn:FA; [exact (ValP.find_align_le E fs HF n kk FA)|].
      pose proof (div8_holds E fs _ HF AL) as X. rewrite HeapCtr.den_VPz in X. apply mod8_mod2k; [lia| exact X]. }
    rewrite (ValP.den_VP E n o), ZS. unfold two64. rewrite mod64_mod2k by lia.
    rewrite Z.add_mod, AN, M by (apply Z.pow_nonzero; lia). cbn [Z.add]. apply Z.mod_0_l. apply Z.pow_nonzero; lia.
  - destruct op; try discriminate H.
    + destruct (alk_sv kk fs a) eqn:HA; [|discriminate H]. specialize (IHa kk Hk HA). specialize (IHb kk Hk H).
      cbn [den]. unfold alu64, alu. rewrite bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
      rewrite mod64_mod2k by lia. rewrite Z.add_mod, IHa, IHb by (apply Z.pow_nonzero; lia). cbn [Z.add]. apply Z.mod_0_l. apply Z.pow_nonzero; lia.
    +
      destruct b as [s| | | | | | | | | |]; try discriminate H.
      pose proof (shamt6_range s) as SR.
      cbn [den]. unfold alu64, alu. rewrite bv_shiftl_unsigned, shamt6_bv. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
      rewrite mod64_mod2k by lia. rewrite Z.shiftl_mul_pow2 by lia.
      destruct (PrimInt63.leb kk (shamt6 s)) eqn:KS.
      * apply leb_spec in KS. apply Znumtheory.Zdivide_mod. exists (bv_unsigned (den E a) * 2 ^ (to_Z (shamt6 s) - to_Z kk)).
        rewrite <- Z.mul_assoc. f_equal. rewrite <- Z.pow_add_r by lia. f_equal. lia.
      * assert (LT : to_Z (shamt6 s) < to_Z kk) by (destruct (Z_lt_le_dec (to_Z (shamt6 s)) (to_Z kk)) as [X|X]; [exact X| exfalso; rewrite (proj2 (leb_spec _ _) X) in KS; discriminate KS]).
        assert (EK : to_Z (PrimInt63.sub kk (shamt6 s)) = to_Z kk - to_Z (shamt6 s)) by (rewrite Uint63.sub_spec, wB_two63, two63_eq, Z.mod_small; [reflexivity| lia]).
        specialize (IHa (PrimInt63.sub kk (shamt6 s)) ltac:(rewrite EK; lia) H). rewrite EK in IHa.
        apply Znumtheory.Zmod_divide in IHa; [| apply Z.pow_nonzero; lia]. destruct IHa as [q Hq]. apply Znumtheory.Zdivide_mod.
        exists q. rewrite Hq, <- Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. lia.
  -
    destruct mo; try discriminate H. destruct b as [c| | | | | | | | | |]; try discriminate H.
    cbn [den]. unfold mul_div. rewrite bv_mul_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite mod64_mod2k by lia.
    destruct (alk_lit kk c) eqn:AL.
    + destruct (alk_lit_spec kk c ltac:(lia) AL) as (T & _ & M). destruct c as [t l]. cbn [wt wl] in T, M. subst t.
      rewrite wbv_unsigned. unfold w2Z. cbn [wt wl]. rewrite Z.add_0_l.
      rewrite Z.mul_mod, M, Z.mul_0_r by (apply Z.pow_nonzero; lia). apply Z.mod_0_l. apply Z.pow_nonzero; lia.
    + specialize (IHa kk Hk H). rewrite Z.mul_mod, IHa, Z.mul_0_l by (apply Z.pow_nonzero; lia). apply Z.mod_0_l. apply Z.pow_nonzero; lia.
Qed.
Lemma al8_sv_sound : forall E fs v, facts_hold E fs -> al8_sv fs v = true -> bv_unsigned (den E v) mod 8 = 0.
Proof. intros E fs v HF H. exact (alk_sv_sound E fs v HF 3%uint63 ltac:(change (to_Z 3%uint63) with 3; lia) H). Qed.
Lemma div8x_holds : forall E fs xs, facts_hold E fs -> div8x fs xs = true -> bv_unsigned (den E xs) mod 8 = 0.
Proof. intros E fs xs HF H. unfold div8x in H. destruct (div8 fs xs) eqn:D; [exact (div8_holds E fs xs HF D)| exact (al8_sv_sound E fs xs HF H)]. Qed.

Lemma tier1_tiers : forall {A} fs vs (q : list fact -> option A) r, tier1 fs vs q = Some r -> KnownT.KnownT.tiers fs vs q = Some r.
Proof. intros A fs vs q r H. unfold tier1 in H. unfold KnownT.KnownT.tiers. rewrite H. reflexivity. Qed.
Lemma tiers12_tiers : forall {A} fs vs (q : list fact -> option A) r, tiers12 fs vs q = Some r -> KnownT.KnownT.tiers fs vs q = Some r.
Proof.
  intros A fs vs q r H. unfold tiers12 in H. unfold KnownT.KnownT.tiers.
  destruct (q (rel_facts vs fs)) as [r1|]; [exact H|]. rewrite H. reflexivity.
Qed.
Lemma known_ltu_t1_t : forall fs a b, known_ltu_t1 fs a b = true -> KnownT.KnownT.known_ltu_t fs a b = true.
Proof.
  intros fs a b H. unfold known_ltu_t1, Step.dec_true in H. unfold KnownT.KnownT.known_ltu_t, KnownT.KnownT.decide_ltu_tt, KnownT.KnownT.dec_true.
  destruct (tier1 fs _ _) as [[|]|] eqn:T; try discriminate H. rewrite (tier1_tiers _ _ _ _ T). reflexivity.
Qed.
Lemma known_leu_t1_t : forall fs a b, known_leu_t1 fs a b = true -> KnownT.KnownT.known_leu_t fs a b = true.
Proof.
  intros fs a b H. unfold known_leu_t1, Step.dec_false in H. unfold KnownT.KnownT.known_leu_t, KnownT.KnownT.decide_ltu_tt, KnownT.KnownT.dec_false.
  destruct (tier1 fs _ _) as [[|]|] eqn:T; try discriminate H. rewrite (tier1_tiers _ _ _ _ T). reflexivity.
Qed.
Lemma known_leu_t12_t : forall fs a b, known_leu_t12 fs a b = true -> KnownT.KnownT.known_leu_t fs a b = true.
Proof.
  intros fs a b H. unfold known_leu_t12, Step.dec_false in H. unfold KnownT.KnownT.known_leu_t, KnownT.KnownT.decide_ltu_tt, KnownT.KnownT.dec_false.
  destruct (tiers12 fs _ _) as [[|]|] eqn:T; try discriminate H. rewrite (tiers12_tiers _ _ _ _ T). reflexivity.
Qed.
Lemma reqmax_ok_eq : forall fs n, reqmax_ok fs n = reqmax_ok_spec fs n.
Proof.
  intros fs n. unfold reqmax_ok, reqmax_ok_spec.
  destruct (reqmax_x4_t1 fs n) eqn:X1.
  - unfold reqmax_x4_t1 in X1. destruct (known_ltu_t1 fs n (VL B61w)) eqn:A; [|discriminate X1].
    unfold reqmax_x4. rewrite (known_ltu_t1_t _ _ _ A), (known_leu_t1_t _ _ _ X1). destruct (KnownT.KnownT.known_leu_t fs n (VL AREQMAXw)); reflexivity.
  - destruct (known_leu_t12 fs n (VL AREQMAXw)) eqn:A12.
    + rewrite (known_leu_t12_t _ _ _ A12). reflexivity.
    + destruct (reqmax_x4 fs n), (KnownT.KnownT.known_leu_t fs n (VL AREQMAXw)); reflexivity.
Qed.
Lemma reqmax_ok_sound : forall E fs n, facts_hold E fs -> reqmax_ok fs n = true -> bv_unsigned (den E n) <= 0xFFF00000.
Proof.
  intros E fs n HF H. rewrite reqmax_ok_eq in H. unfold reqmax_ok_spec, reqmax_x4 in H.
  destruct (KnownT.KnownT.known_leu_t fs n (VL AREQMAXw)) eqn:D.
  - pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF D) as L. cbn [den] in L. rewrite wbv_unsigned in L. exact L.
  - destruct (KnownT.KnownT.known_ltu_t fs n (VL B61w)) eqn:B; [|discriminate H].
    pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF B) as LB. cbn [den] in LB. rewrite wbv_unsigned in LB.
    replace (w2Z B61w) with (2 ^ 61) in LB by (vm_compute; reflexivity).
    pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF H) as L4.
    replace (bv_unsigned (den E (VL AREQMAX4w))) with 0x3FFC00000 in L4 by (vm_compute; reflexivity).
    cbn [den] in L4. unfold alu64, alu in L4. rewrite bv_shiftl_unsigned, shamt6_bv in L4.
    unfold bv_wrap, bv_modulus in L4. change (2 ^ Z.of_N 64) with (2 ^ 64) in L4.
    replace (to_Z (shamt6 (wlit 2%uint63))) with 2 in L4 by (vm_compute; reflexivity).
    rewrite Z.shiftl_mul_pow2 in L4 by lia. rewrite Z.mod_small in L4; [lia|].
    pose proof (bv_unsigned_in_range _ (den E n)) as R. lia.
Qed.

Lemma size_shape_sound : forall E fs n, facts_hold E fs -> size_shape_ok fs n = true ->
  match n with VL _ => True | _ => bv_unsigned (den E n) mod 8 = 0 end.
Proof.
  intros E fs n HF H.
  assert (GEN : al8_sv fs n || (KnownT.KnownT.known_eq_t fs (VAlu ALU_AND n (VL (wlit 7%uint63))) (VL wzero) || KnownT.KnownT.known_eq_t fs (sz_and7 n) (VL wzero)
                || KnownT.KnownT.known_leu_t fs (sz_and7 n) (VL wzero)) = true -> bv_unsigned (den E n) mod 8 = 0).
  { intros K. apply orb_prop in K as [K|K]; [exact (al8_sv_sound E fs n HF K)|].
    apply orb_prop in K as [K|K]; [apply orb_prop in K as [K|K]|].
    - pose proof (KnownA.KnownA.known_eq_sound E _ _ _ HF K) as EQ. cbn [den] in EQ. unfold alu64, alu in EQ.
      apply (f_equal bv_unsigned) in EQ. rewrite bv_and_unsigned, !wbv_unsigned, wlit_ok, wzero_ok in EQ. change (to_Z 7%uint63) with (Z.ones 3) in EQ.
      rewrite Z.land_ones in EQ by lia. exact EQ.
    - pose proof (KnownA.KnownA.known_eq_sound E _ _ _ HF K) as EQ. apply (f_equal bv_unsigned) in EQ. rewrite sz_and7_den in EQ.
      cbn [den] in EQ. rewrite wbv_unsigned, wzero_ok in EQ. exact EQ.
    - pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF K) as LE. rewrite sz_and7_den in LE. cbn [den] in LE. rewrite wbv_unsigned, wzero_ok in LE.
      pose proof (Z.mod_pos_bound (bv_unsigned (den E n)) 8 ltac:(lia)). lia. }
  destruct n; try exact I; apply GEN; cbn [size_shape_ok] in H;
    (destruct (al8_sv fs _); [reflexivity|]); cbn [orb];
    repeat match type of H with (if ?c then true else _) = true => destruct c; [rewrite ?orb_true_r; reflexivity|] end; rewrite ?orb_false_l; exact H.
Qed.

Lemma size_tail_sound : forall E fs n, facts_hold E fs -> size_tail_ok fs n = true ->
  1 <= bv_unsigned (den E n) /\ (forall w, n <> VL w).
Proof.
  intros E fs n HF H.
  assert (GEN : KnownT.KnownT.known_ltu_t fs (VL wzero) n = true -> 1 <= bv_unsigned (den E n)).
  { intros K. pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF K) as LT. cbn [den] in LT. rewrite wbv_unsigned, wzero_ok in LT. lia. }
  destruct n; cbn [size_tail_ok] in H; try discriminate H; (split; [apply GEN; exact H| intros w X; discriminate X]).
Qed.

Lemma no_tail_at_sound : forall fs (R : IMap.t region) sh n k0 rg, IMap.bst R -> no_tail_at fs R sh n = true ->
  IMap.find k0 R = Some rg -> tail_named (tail_rhs sh n) k0 fs = true -> False.
Proof.
  intros fs R sh n k0 rg B NT F TN. unfold no_tail_at in NT.
  pose proof (proj1 (IMap.forallb_spec _ _ B) NT k0 rg F) as C. cbv beta in C. rewrite TN in C. discriminate C.
Qed.

Lemma aheap_windows_inv : forall st hargs wnl, aheap_windows st = Some (hargs, wnl) ->
  find_op HEAP_ID (s_ops st) = Some hargs /\ CtrA.count_op HEAP_ID (s_ops st) = 1%nat
  /\ exists r1 n md A nw rest, IMap.find STACK_ID (s_regs st) = Some r1 /\ heap_nwin hargs = Some n /\ hargs = VL md :: A :: VL nw :: rest
     /\ wt nw = false /\ n = Z.to_nat (to_Z (wl nw)) /\ (3 * n <= length rest)%nat /\ (n <= 255)%nat
     /\ stack_window_ok_g n rest (rg_lo r1) = true /\ CtrA.nonstack_windows n rest = Some wnl
     /\ CtrA.windows_anchored (s_regs st) wnl = true /\ aregions_justified st wnl = true
     /\ twins_scan (s_facts st) (s_regs st) wnl wnl = true.
Proof.
  intros st hargs wnl H. unfold aheap_windows in H.
  destruct (find_op HEAP_ID (s_ops st)) as [h|] eqn:Hf; [|discriminate].
  destruct (CtrA.count_op HEAP_ID (s_ops st)) as [|[|c]] eqn:Hc; try discriminate.
  destruct (IMap.find STACK_ID (s_regs st)) as [r1|] eqn:Hr1; [|discriminate].
  destruct (heap_nwin h) as [n|] eqn:Hn; [|discriminate].
  destruct (heap_nwin_shape h n Hn) as (md & A & nw & rest & Eh & T & N & L). rewrite Eh in H.
  destruct (Nat.leb n 255 && stack_window_ok_g n rest (rg_lo r1)) eqn:C1; [|discriminate].
  apply andb_prop in C1 as [N255 SW]. apply Nat.leb_le in N255.
  destruct (CtrA.nonstack_windows n rest) as [wl'|] eqn:NW; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:AJ; [|discriminate] end.
  injection H as <- <-. apply andb_prop in AJ as [AJ A2]. apply andb_prop in AJ as [A1 TS]. subst h.
  split; [reflexivity|]. split; [reflexivity|].
  exists r1, n, md, A, nw, rest. repeat (split; [assumption || reflexivity|]). exact TS.
Qed.

Lemma stack_window_g_In : forall E n rest klo,
  stack_window_ok_g n rest klo = true ->
  exists wlo kw len, okey wlo = Some kw /\ keyZ kw <= keyZ klo
    /\ In (HeapOp.Win (bv_unsigned (den E (VP STACK_ID wlo))) len HeapOp.K_STACK) (wins_of E n rest).
Proof.
  intros E n. induction n as [|n IH]; intros rest klo H; [cbn in H; destruct rest; discriminate|].
  destruct rest as [|lo rest1]; [cbn in H; discriminate|].
  destruct rest1 as [|len rest2]; [destruct lo; cbn in H; discriminate|].
  destruct rest2 as [|kd rest']; [destruct lo; cbn in H; discriminate|].
  cbn [stack_window_ok_g] in H.
  assert (STEP : stack_window_ok_g n rest' klo = true ->
            exists wlo kw len0, okey wlo = Some kw /\ keyZ kw <= keyZ klo
              /\ In (HeapOp.Win (bv_unsigned (den E (VP STACK_ID wlo))) len0 HeapOp.K_STACK) (wins_of E (S n) (lo :: len :: kd :: rest'))).
  { intros H'. destruct (IH rest' klo H') as (wlo & kw & len0 & K1 & K2 & K3). exists wlo, kw, len0. split; [exact K1|]. split; [exact K2|].
    rewrite wins_of_cons. right. exact K3. }
  destruct lo as [|k wlo| | | | | | | | |]; cbn in H; try (apply STEP; exact H).
  destruct kd as [kdw| | | | | | | | | |]; cbn in H; try (apply STEP; exact H).
  apply orb_prop in H as [H|H]; [| apply STEP; exact H].
  apply andb_prop in H as [H HK]. apply andb_prop in H as [H1 H2].
  apply Uint63.eqb_correct in H1. subst k. destruct (okey wlo) as [kw|] eqn:Hkw; [|discriminate].
  rewrite kleb_keyZ in HK. apply Z.leb_le in HK.
  exists wlo, kw, (bv_unsigned (den E len)). split; [exact Hkw|]. split; [exact HK|]. rewrite wins_of_cons. left.
  unfold HeapOp.K_STACK. rewrite (unsigned_VL E kdw), (HeapCtr.weqb_wzero_unsigned' kdw H2). reflexivity.
Qed.

Lemma den_key2w : forall E k o, bv_unsigned (den E (VP k (key2w o))) = (bv_unsigned (ev E k) + keyZ o) mod two64.
Proof. intros E k o. rewrite den_VP. unfold key2w. rewrite w2Zs_key. reflexivity. Qed.

Lemma den_add_vp0 : forall E k hi, bv_unsigned (den E (VAlu ALU_ADD (VP k wzero) hi)) = (bv_unsigned (ev E k) + bv_unsigned (den E hi)) mod two64.
Proof.
  intros E k hi. change (den E (VAlu ALU_ADD (VP k wzero) hi)) with (alu64 ALU_ADD (den E (VP k wzero)) (den E hi)).
  rewrite HeapCtr.den_VPz. unfold alu64, alu. rewrite bv_add_unsigned. reflexivity.
Qed.

Lemma below_top_sound : forall E st ms mo k r, st_ok segs OPS E st ms mo -> IMap.find k (s_regs st) = Some r -> k <> 0%uint63 ->
  below_top (s_facts st) k r = true -> bv_unsigned (ev E k) + hiZ E r <= 2 ^ 47.
Proof.
  intros E st ms mo k r HS Hk K0 BT. pose proof (so_facts _ _ _ _ _ _ HS) as HF. pose proof (so_reg _ _ _ _ _ _ HS k r Hk) as RO.
  assert (KZ : PrimInt63.eqb k 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  destruct (ro_range _ _ _ _ _ _ RO KZ) as [RLO RHI].
  unfold below_top in BT. apply orb_prop in BT as [FAST|BT].
  {
    unfold below_top_fast in FAST. destruct (rg_hi r) as [h| | | | | | | | | |] eqn:EH; try discriminate FAST.
    destruct (find_range (s_facts st) k) as [[lo0 hi0]|] eqn:FR; [|discriminate FAST].
    apply andb_prop in FAST as [FAST L3]. apply andb_prop in FAST as [FAST L2]. apply andb_prop in FAST as [FAST L1]. apply andb_prop in FAST as [T1 T2].
    apply negb_true_iff in T1. apply negb_true_iff in T2. apply Uint63.leb_spec in L1. apply Uint63.leb_spec in L2. apply Uint63.leb_spec in L3.
    change (to_Z TOP47i) with (2 ^ 47) in L1, L2, L3.
    pose proof (ValP.find_range_sound E _ HF k lo0 hi0 FR) as [_ RK].
    assert (WH : w2Z hi0 = to_Z (wl hi0)) by (unfold w2Z; rewrite T1; lia).
    assert (HZ : hiZ E r = to_Z (wl h)) by (unfold hiZ; rewrite EH; cbn [den]; rewrite wbv_unsigned; unfold w2Z; rewrite T2; lia).
    pose proof (int_range (wl hi0)) as R1. pose proof (int_range (wl h)) as R2.
    rewrite Uint63.add_spec, Z.mod_small in L3 by (rewrite wB_two63, two63_eq; lia). rewrite HZ. lia. }
  pose proof (KnownA.KnownA.known_leu_q_sound E _ _ _ HF BT) as X.
  replace (bv_unsigned (den E (VL (wlit 140737488355328%uint63)))) with (2 ^ 47) in X by (vm_compute; reflexivity).
  assert (EQ : bv_unsigned (den E (match rg_hi r with VL h => VP k h | hi => VAlu ALU_ADD (VP k wzero) hi end)) = bv_unsigned (ev E k) + hiZ E r).
  { unfold hiZ in *. pose proof (bv_unsigned_in_range 64 (ev E k)) as REK. pose proof (bv_unsigned_in_range 64 (den E (rg_hi r))) as RHH.
    change (bv_modulus 64) with (2 ^ 64) in *. unfold two64 in *.
    destruct (rg_hi r) as [h| | | | | | | | | |]; try (rewrite den_add_vp0; apply Z.mod_small; unfold two64; lia).
    cbn [den] in *. rewrite bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. lia. }
  rewrite EQ in X. exact X.
Qed.

Lemma known_leu_s_sound : forall fs a b, known_leu_s fs a b = true -> known_leu fs a b = true.
Proof.
  intros fs a b H. unfold known_leu_s in H. unfold known_leu, decide_ltu. destruct (decide_ltu_s fs b a) as [x|]; [exact H| discriminate H].
Qed.

Lemma annot_end_ok_sound : forall E fs k len x11, facts_hold E fs -> annot_end_ok fs k len x11 = true ->
  bv_unsigned (ev E k) mod 8 = 0 -> bv_unsigned (den E x11) mod 8 = 0 -> bv_unsigned (den E len) <= 8064 -> bv_unsigned (ev E k) < 2 ^ 47 ->
  bv_unsigned (den E x11) <= bv_unsigned (ev E k) + 8 * bv_unsigned (den E len).
Proof.
  intros E fs k len x11 HF H K8 E8 WMAX K47. unfold annot_end_ok in H.
  pose proof (bv_unsigned_in_range 64 (ev E k)) as RK. unfold bv_modulus in RK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RK.
  assert (SYM : match tie_of fs len with
                | Some xs => (sv_eqb x11 (VAlu ALU_ADD (VP k wzero) xs) ||| has_fact (FULe x11 (VAlu ALU_ADD (VP k wzero) xs)) fs)
                             &&& KnownT.KnownT.known_leu_t fs xs (VL SYMCAPw) &&& nowrap_kb fs k SYMCAPw
                | None => false
                end = true -> bv_unsigned (den E x11) <= bv_unsigned (ev E k) + 8 * bv_unsigned (den E len)).
  { clear H. intros H. destruct (tie_of fs len) as [xs|] eqn:TIE; [|discriminate H].
    apply andb_prop in H as [H NWK]. apply andb_prop in H as [HFA XS].
    assert (U : bv_unsigned (den E x11) <= bv_unsigned (den E (VAlu ALU_ADD (VP k wzero) xs))).
    { apply orb_prop in HFA as [EQ|HFA]; [apply sv_eqb_eq in EQ; rewrite EQ; lia|]. pose proof (has_fact_holds E _ _ HF HFA) as U0. cbn [fact_holds] in U0. exact U0. }
    rewrite den_add_vp0 in U.
    pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF XS) as X8. replace (bv_unsigned (den E (VL SYMCAPw))) with 65536 in X8 by (vm_compute; reflexivity).
    pose proof (bv_unsigned_in_range 64 (den E xs)) as RX. unfold bv_modulus in RX. change (2 ^ Z.of_N 64) with (2 ^ 64) in RX.
    unfold two64 in U. rewrite Z.mod_small in U by lia.
    rewrite (tie_of_holds E fs len xs HF TIE). clear - U K8 E8. Z.div_mod_to_equations. lia. }
  destruct len as [wlen| | | | | | | | | |]; try (exact (SYM H)). clear SYM.
  apply andb_prop in H as [WT LE]. apply negb_true_iff in WT.
  pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF LE) as EI.
  assert (WLE : bv_unsigned (den E (VL wlen)) = to_Z (wl wlen)) by (cbn [den]; rewrite wbv_unsigned; unfold w2Z; rewrite WT; reflexivity).
  rewrite WLE in *. pose proof (int_range (wl wlen)) as RW.
  assert (LS : to_Z (PrimInt63.lsl (wl wlen) 3%uint63) = 8 * to_Z (wl wlen)).
  { rewrite lsl_spec. change (to_Z 3%uint63) with 3. change (2 ^ 3) with 8. rewrite Z.mod_small; [lia|]. rewrite wB_two63, two63_eq. lia. }
  assert (ZS : w2Zs (wlit (PrimInt63.lsl (wl wlen) 3%uint63)) = 8 * to_Z (wl wlen)).
  { rewrite w2Zs_eq. unfold w2Z, wlit. cbn [wt wl]. rewrite LS. lia. }
  rewrite (ValP.den_VP E k _), ZS in EI. unfold two64 in EI. rewrite Z.mod_small in EI by lia. exact EI.
Qed.
Lemma stack_side_just_sound : forall E st ms mo ks k r, st_ok segs OPS E st ms mo -> IMap.find k (s_regs st) = Some r -> k <> 0%uint63 ->
  stack_side_just (s_facts st) (getr st X2) (sp_below_anchor_t (s_facts st) (getr st X2)) ks k r = true ->
  (k = ks \/ bv_unsigned (den E (getr st X2)) <= bv_unsigned (ev E k) + loZ r) /\ bv_unsigned (ev E k) + hiZ E r <= 2 ^ 47.
Proof.
  intros E st ms mo ks k r HS Hk K0 J. pose proof (so_facts _ _ _ _ _ _ HS) as HF. pose proof (so_reg _ _ _ _ _ _ HS k r Hk) as RO.
  assert (KZ : PrimInt63.eqb k 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  destruct (ro_range _ _ _ _ _ _ RO KZ) as [RLO RHI].
  unfold stack_side_just in J. destruct (PrimInt63.eqb k ks) eqn:KS.
  { apply Uint63.eqb_correct in KS. split; [left; exact KS| exact (below_top_sound E st ms mo k r HS Hk K0 J)]. }
  apply andb_prop in J as [AB BT]. split; [right| exact (below_top_sound E st ms mo k r HS Hk K0 BT)].
  assert (DIRECT : bv_unsigned (den E (getr st X2)) <= bv_unsigned (den E (VP k (key2w (rg_lo r)))) ->
            bv_unsigned (den E (getr st X2)) <= bv_unsigned (ev E k) + loZ r).
  { intros X. rewrite den_key2w in X. unfold loZ in *.
    pose proof (Z.mod_le (bv_unsigned (ev E k) + keyZ (rg_lo r)) two64 ltac:(lia) ltac:(unfold two64; lia)). lia. }
  apply orb_prop in AB as [AB1|AB].
  { apply orb_prop in AB1 as [DS|PAD]; [exact (DIRECT (HeapCtr.known_leu_sound E _ _ _ HF (known_leu_s_sound _ _ _ DS)))|].

    unfold pad_side in PAD. destruct (getr st X2) as [|n o| | | | | | | | |] eqn:SPE; try discriminate PAD.
    apply andb_prop in PAD as [PAD NW]. apply andb_prop in PAD as [PAD HFa]. apply andb_prop in PAD as [L0 WT]. apply Uint63.eqb_correct in L0.
    pose proof (has_fact_holds E _ _ HF HFa) as FH. cbn [fact_holds] in FH. rewrite !HeapCtr.den_VPz in FH.
    destruct (ValP.nowrap_kb_sound E _ HF n o NW) as [RR D]. rewrite D. rewrite ValP.w2Zs_eq, WT in *.
    pose proof (w2Z_range o) as ROo. unfold loZ. rewrite L0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. unfold two64 in *. lia. }
  apply orb_prop in AB as [AB|AB]; [| exact (DIRECT (KnownA.KnownA.known_leu_sound E _ _ _ HF AB))].
  apply andb_prop in AB as [AB SS]. apply andb_prop in AB as [L0 _]. apply Uint63.eqb_correct in L0.
  pose proof (KnownA.KnownA.stack_side_sound E _ _ _ HF SS) as X. unfold loZ. rewrite L0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. lia.
Qed.

Lemma find_lb_to_holds : forall E fs n k o, Forall (fact_holds E) fs -> find_lb_to fs n k = Some o ->
  bv_unsigned (den E (VP k o)) <= bv_unsigned (ev E n).
Proof.
  intros E fs. induction fs as [|f fs IH]; intros n k o HF H; cbn [find_lb_to] in H; [discriminate|].
  inversion HF as [|f' l Hf HF']; subst.
  destruct f as [| | |x y|x y| | |]; try exact (IH n k o HF' H).
  - destruct x as [|k' o'| | | | | | | | |]; try exact (IH n k o HF' H). destruct y as [|n' z| | | | | | | | |]; try exact (IH n k o HF' H).
    destruct (PrimInt63.eqb n' n && PrimInt63.eqb k' k && weqb z wzero) eqn:C; [| exact (IH n k o HF' H)]. injection H as <-.
    apply andb_prop in C as [C Z0]. apply andb_prop in C as [EN EK]. apply Uint63.eqb_correct in EN. apply Uint63.eqb_correct in EK. apply weqb_eq in Z0. subst n' k' z.
    cbn [fact_holds] in Hf. rewrite HeapCtr.den_VPz in Hf. exact Hf.
  - destruct x as [|n' z| | | | | | | | |]; try exact (IH n k o HF' H). destruct y as [|k' o'| | | | | | | | |]; try exact (IH n k o HF' H).
    destruct (PrimInt63.eqb n' n && PrimInt63.eqb k' k && weqb z wzero) eqn:C; [| exact (IH n k o HF' H)]. injection H as <-.
    apply andb_prop in C as [C Z0]. apply andb_prop in C as [EN EK]. apply Uint63.eqb_correct in EN. apply Uint63.eqb_correct in EK. apply weqb_eq in Z0. subst n' k' z.
    cbn [fact_holds] in Hf. rewrite HeapCtr.den_VPz in Hf. rewrite <- Hf. lia.
Qed.
Lemma find_ub_to_holds : forall E fs n oA k c, Forall (fact_holds E) fs -> find_ub_to fs n oA k = Some c ->
  bv_unsigned (den E (VP n oA)) <= bv_unsigned (den E (VP k c)).
Proof.
  intros E fs. induction fs as [|f fs IH]; intros n oA k c HF H; cbn [find_ub_to] in H; [discriminate|].
  inversion HF as [|f' l Hf HF']; subst.
  destruct f as [| | |x y|x y| | |]; try exact (IH n oA k c HF' H).
  destruct x as [|n' o'| | | | | | | | |]; try exact (IH n oA k c HF' H). destruct y as [|k' c'| | | | | | | | |]; try exact (IH n oA k c HF' H).
  destruct (PrimInt63.eqb n' n && weqb o' oA && PrimInt63.eqb k' k) eqn:C; [| exact (IH n oA k c HF' H)]. injection H as <-.
  apply andb_prop in C as [C EK]. apply andb_prop in C as [EN EO]. apply Uint63.eqb_correct in EN. apply Uint63.eqb_correct in EK. apply weqb_eq in EO. subst n' k' o'.
  exact Hf.
Qed.
Lemma vec_hi_in_sound : forall E fs h len, Forall (fact_holds E) fs -> vec_hi_in fs h len = true ->
  bv_unsigned (den E h) <= bv_unsigned (den E len).
Proof.
  intros E fs h len HF H. unfold vec_hi_in in H.
  destruct h as [| |op x c3v| | | | | | | |]; try discriminate H. destruct op; try discriminate H.
  destruct x as [| |op2 a b| | | | | | | |]; try discriminate H. destruct op2; try discriminate H.
  destruct a as [|n oA| | | | | | | | |]; try discriminate H. destruct b as [|k z| | | | | | | | |]; try discriminate H.
  destruct c3v as [c3| | | | | | | | | |]; try discriminate H.
  assert (SYMARM : (weqb z wzero && weqb c3 (wlit 3%uint63)
      && match tie_of fs len, find_lb_to fs n k with
         | Some xs, Some o2 =>
             has_fact (FULe (VP n oA) (VAlu ALU_ADD (VP k wzero) xs)) fs
             && KnownT.KnownT.known_leu_t fs xs (VL SYMCAPw) && nowrap_kb fs k SYMCAPw && negb (wt oA) && negb (wt o2)
             && nowrap_kb fs n oA && nowrap_kb fs k o2
         | _, _ => false
         end = true) ->
      bv_unsigned (den E (VAlu ALU_SRL (VAlu ALU_SUB (VP n oA) (VP k z)) (VL c3))) <= bv_unsigned (den E len)).
  { clear H. intros H. apply andb_prop in H as [H M]. apply andb_prop in H as [Z0 C3]. apply weqb_eq in Z0. apply weqb_eq in C3. subst z c3.
    destruct (tie_of fs len) as [xs|] eqn:TIE; [|discriminate M]. destruct (find_lb_to fs n k) as [o2|] eqn:LB; [|discriminate M].
    apply andb_prop in M as [M NW2]. apply andb_prop in M as [M NWA]. apply andb_prop in M as [M WT2]. apply andb_prop in M as [M WTA].
    apply andb_prop in M as [M NWK]. apply andb_prop in M as [HFA XS].
    apply negb_true_iff in WT2. apply negb_true_iff in WTA.
    destruct (nowrap_kb_sound E _ HF n oA NWA) as [RA DA]. destruct (nowrap_kb_sound E _ HF k _ NWK) as [RK8 _]. destruct (nowrap_kb_sound E _ HF k o2 NW2) as [R2 D2].
    pose proof (find_lb_to_holds E fs n k o2 HF LB) as L. rewrite D2 in L.
    pose proof (has_fact_holds E _ _ HF HFA) as U. cbn [fact_holds] in U. rewrite DA, den_add_vp0 in U.
    pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF XS) as X8. replace (bv_unsigned (den E (VL SYMCAPw))) with 65536 in X8 by (vm_compute; reflexivity).
    replace (w2Zs SYMCAPw) with 65536 in RK8 by (vm_compute; reflexivity).
    pose proof (tie_of_holds E fs len xs HF TIE) as TL.
    assert (ZA : w2Zs oA = w2Z oA) by (rewrite w2Zs_eq; rewrite WTA; lia).
    assert (Z2 : w2Zs o2 = w2Z o2) by (rewrite w2Zs_eq; rewrite WT2; lia).
    rewrite ZA in U, RA, DA. rewrite Z2 in L.
    pose proof (w2Z_range oA) as ROA. pose proof (w2Z_range o2) as RO2.
    pose proof (bv_unsigned_in_range 64 (den E xs)) as RX. unfold bv_modulus in RX. change (2 ^ Z.of_N 64) with (2 ^ 64) in RX.
    pose proof (bv_unsigned_in_range 64 (ev E n)) as RN. pose proof (bv_unsigned_in_range 64 (ev E k)) as RKK. unfold bv_modulus in RN, RKK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RN, RKK.
    unfold two64 in *. rewrite Z.mod_small in U by lia.
    rewrite TL. cbn [den]. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned, bv_sub_unsigned.
    replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
    replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
    change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    change (bv_add (ev E n) (wbv oA)) with (den E (VP n oA)). rewrite DA.
    change (bv_add (ev E k) (wbv wzero)) with (den E (VP k wzero)). rewrite (HeapCtr.den_VPz E k).
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Z.mod_small by lia. clear - U L RO2. Z.div_mod_to_equations. lia. }
  destruct len as [wlen| | | | | | | | | |]; try (exact (SYMARM H)). clear SYMARM.
  apply andb_prop in H as [H M]. apply andb_prop in H as [H W58]. apply andb_prop in H as [H WTL]. apply andb_prop in H as [Z0 C3].
  apply weqb_eq in Z0. apply weqb_eq in C3. subst z c3. apply negb_true_iff in WTL. apply Uint63.ltb_spec in W58.
  destruct (find_lb_to fs n k) as [o2|] eqn:LB; [|discriminate M]. destruct (find_ub_to fs n oA k) as [cU|] eqn:UB; [|discriminate M].
  apply andb_prop in M as [M NW2]. apply andb_prop in M as [M NWC]. apply andb_prop in M as [M NWA]. apply andb_prop in M as [M WT2].
  apply andb_prop in M as [M WTA]. apply andb_prop in M as [WTC LEC].
  apply negb_true_iff in WT2. apply negb_true_iff in WTA. apply negb_true_iff in WTC. apply Uint63.leb_spec in LEC.
  destruct (nowrap_kb_sound E _ HF n oA NWA) as [RA DA]. destruct (nowrap_kb_sound E _ HF k cU NWC) as [RC DC]. destruct (nowrap_kb_sound E _ HF k o2 NW2) as [R2 D2].
  pose proof (find_lb_to_holds E fs n k o2 HF LB) as L. pose proof (find_ub_to_holds E fs n oA k cU HF UB) as U.
  rewrite D2 in L. rewrite DA, DC in U.
  assert (ZA : w2Zs oA = w2Z oA) by (rewrite w2Zs_eq; rewrite WTA; lia).
  assert (ZC : w2Zs cU = w2Z cU) by (rewrite w2Zs_eq; rewrite WTC; lia).
  assert (Z2 : w2Zs o2 = w2Z o2) by (rewrite w2Zs_eq; rewrite WT2; lia).
  rewrite ZA, ZC in U. rewrite Z2 in L. rewrite ZA in RA, DA.
  pose proof (w2Z_range oA) as ROA. pose proof (w2Z_range o2) as RO2. pose proof (w2Z_range cU) as ROC.
  assert (WC : w2Z cU = to_Z (wl cU)) by (unfold w2Z; rewrite WTC; lia).
  assert (WL : w2Z wlen = to_Z (wl wlen)) by (unfold w2Z; rewrite WTL; lia).
  rewrite lsl_spec in LEC. change (to_Z 3%uint63) with 3 in LEC. change (to_Z 288230376151711744%uint63) with (2 ^ 58) in W58.
  rewrite Z.mod_small in LEC by (pose proof (int_range (wl wlen)); change wB with (2 ^ 63); change (2 ^ 3) with 8; lia). change (2 ^ 3) with 8 in LEC.
  pose proof (bv_unsigned_in_range 64 (ev E n)) as RN. pose proof (bv_unsigned_in_range 64 (ev E k)) as RK. unfold bv_modulus in RN, RK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RN, RK.
  unfold two64 in *.
  cbn [den]. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned, bv_sub_unsigned.
  replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
  replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  change (bv_add (ev E n) (wbv oA)) with (den E (VP n oA)). rewrite DA.
  change (bv_add (ev E k) (wbv wzero)) with (den E (VP k wzero)). rewrite (HeapCtr.den_VPz E k).
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. rewrite wbv_unsigned, WL. clear - U L LEC WC RO2. Z.div_mod_to_equations. lia.
Qed.

Definition sliver_sem (E : env) (st : sstate) (ks : int) (rss : region) (k : int) (r : region) : Prop :=
  rg_cells r = IMap.Leaf /\ rg_bg r = BGNone /\ rg_w r = true /\ loZ r = 0
  /\ exists wlo, stack_wlo st = Some wlo /\ bv_unsigned (ev E k) = bv_unsigned (den E (VP STACK_ID wlo))
       /\ bv_unsigned (ev E k) + hiZ E r = bv_unsigned (ev E ks) + loZ rss.

Lemma sliver_floor_sound : forall E st ms mo ks offs rss wlo,
  st_ok segs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) -> sliver_floor st = true -> stack_wlo st = Some wlo ->
  0 <= bv_unsigned (ev E ks) + loZ rss ->
  bv_unsigned (den E (VP STACK_ID wlo)) = bv_unsigned (ev E STACK_ID) + w2Zs wlo
  /\ bv_unsigned (den E (VP STACK_ID wlo)) <= bv_unsigned (ev E ks) + loZ rss.
Proof.
  intros E st ms mo ks offs rss wlo HS SR FL SW LO0. unfold sliver_floor in FL. unfold stack_wlo in SW.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|]; [|discriminate].
  unfold sp_floor_ok in FL. destruct (heap_nwin hargs) as [n|]; [|discriminate].
  destruct hargs as [|h0 [|h1 [|h2 rest]]]; try discriminate. rewrite SR in FL.
  destruct (stack_window_key n rest) as [w|] eqn:SK; [|discriminate].
  destruct (nowrap_kb (s_facts st) STACK_ID w) eqn:NWw; [|discriminate]. injection SW as ->.
  destruct (okey wlo) as [kw|] eqn:KW; [|discriminate].
  apply andb_prop in FL as [NW H].
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  destruct (nowrap_kb_sound E _ HF STACK_ID wlo NWw) as [R1 D1].
  destruct (okey_sound _ _ KW) as [EKW _].
  split; [exact D1|]. rewrite D1, <- EKW.
  destruct (PrimInt63.eqb ks STACK_ID) eqn:K1.
  - apply Uint63.eqb_correct in K1. subst ks. rewrite kleb_keyZ in H. apply Z.leb_le in H. unfold loZ. lia.
  - destruct (GTwinSub.GTwinSub.find_lb (s_facts st) ks STACK_ID) as [o2|] eqn:FLB; [|discriminate].
    apply andb_prop in H as [NW2 LE]. apply Z.leb_le in LE.
    destruct (nowrap_kb_sound E _ HF STACK_ID o2 NW2) as [R2 D2].
    pose proof (GTwinSub.GTwinSub.find_lb_holds E _ ks STACK_ID o2 HF FLB) as LB. rewrite D2, HeapCtr.den_VPz in LB. unfold loZ. lia.
Qed.

Lemma sliver_just_sound : forall E st ms mo ks offs rss k r,
  st_ok segs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) -> IMap.find k (s_regs st) = Some r -> k <> 0%uint63 ->
  sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k r = true ->
  sliver_sem E st ks rss k r.
Proof.
  intros E st ms mo ks offs rss k r HS SR Hk K0 J. unfold sliver_just in J.
  destruct (stack_wlo st) as [wlo|] eqn:SW; [|discriminate].
  destruct (sp_region_inv st ks offs rss SR) as (_ & Hrs & KZs & _). rewrite Hrs in J.
  apply andb_prop in J as [J Q]. apply andb_prop in J as [J Q0]. apply andb_prop in J as [J Q1]. apply andb_prop in J as [J Q2].
  apply andb_prop in J as [J Q3]. apply andb_prop in J as [J Q4]. apply andb_prop in J as [J Q5].
  pose proof (so_facts _ _ _ _ _ _ HS) as HF. pose proof (so_zero _ _ _ _ _ _ HS) as HZ.
  destruct (rg_cells r) eqn:RC; [|discriminate Q2]. destruct (rg_bg r) eqn:RB; try discriminate Q1.
  apply Uint63.eqb_correct in Q3. apply sv_eqb_eq in Q0.
  assert (KNEG : keyZ (rg_lo rss) < 0).
  { apply negb_true_iff in Q5. destruct (keyZ_cases (rg_lo rss)) as [[B _]|[_ ->]].
    - exfalso. destruct (ltbP (rg_lo rss) bit62i) as [L|L]; [discriminate Q5|]. rewrite to_Z_bit62i in L. lia.
    - pose proof (int_range (rg_lo rss)) as R. rewrite two63_eq in R. lia. }
  pose proof (has_fact_holds E _ _ HF Q) as FE. cbn [fact_holds] in FE.
  pose proof (ro_range _ _ _ _ _ _ (so_reg _ _ _ _ _ _ HS ks rss Hrs) KZs) as [RS0 RS1].
  destruct (sliver_floor_sound E st ms mo ks offs rss wlo HS SR J SW RS0) as [D1 FLO].
  unfold sliver_sem. split; [exact RC|]. split; [exact RB|]. split; [exact Q4|]. split; [unfold loZ; rewrite Q3; reflexivity|].
  exists wlo. split; [exact SW|].
  assert (EK : bv_unsigned (ev E k) = bv_unsigned (den E (VP STACK_ID wlo))) by (rewrite <- FE, HeapCtr.den_VPz; reflexivity).
  split; [exact EK|].
  unfold hiZ. rewrite Q0. cbn [den]. unfold alu64, alu. rewrite bv_sub_unsigned.
  change (bv_add (ev E ks) (wbv (key2w (rg_lo rss)))) with (den E (VP ks (key2w (rg_lo rss)))).
  change (bv_add (ev E STACK_ID) (wbv wlo)) with (den E (VP STACK_ID wlo)).
  pose proof (bv_unsigned_in_range 64 (ev E ks)) as RKS. unfold bv_modulus in RKS.
  rewrite den_key2w. unfold loZ in *. rewrite (Z.mod_small (bv_unsigned (ev E ks) + keyZ (rg_lo rss))) by (unfold two64 in *; lia).
  pose proof (bv_unsigned_in_range 64 (den E (VP STACK_ID wlo))) as RW. unfold bv_modulus in RW.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). unfold two64 in *. rewrite Z.mod_small by lia. lia.
Qed.

Lemma sliver_neg : forall st ks offs rss k r, sp_region st = Some (ks, offs, rss) ->
  sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k r = true -> loZ rss < 0.
Proof.
  intros st ks offs rss k r SR J. unfold sliver_just in J. destruct (stack_wlo st) as [wlo|]; [|discriminate].
  destruct (sp_region_inv st ks offs rss SR) as (_ & Hrs & _). rewrite Hrs in J.
  apply andb_prop in J as [J _]. apply andb_prop in J as [J _]. apply andb_prop in J as [J _]. apply andb_prop in J as [J _].
  apply andb_prop in J as [J _]. apply andb_prop in J as [J _]. apply andb_prop in J as [_ Q5].
  apply negb_true_iff in Q5. unfold loZ. destruct (keyZ_cases (rg_lo rss)) as [[B _]|[_ ->]].
  - exfalso. destruct (ltbP (rg_lo rss) bit62i) as [L|L]; [discriminate Q5|]. rewrite to_Z_bit62i in L. lia.
  - pose proof (int_range (rg_lo rss)) as R. rewrite two63_eq in R. lia.
Qed.

Lemma sliver_range : forall E st ms mo ks offs rss k r a,
  st_ok segs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) -> sliver_sem E st ks rss k r ->
  bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r ->
  exists wlo, stack_wlo st = Some wlo /\ bv_unsigned (den E (VP STACK_ID wlo)) <= a < bv_unsigned (ev E ks) + loZ rss.
Proof.
  intros E st ms mo ks offs rss k r a HS SR (_ & _ & _ & L0 & wlo & SW & EK & EH) Ha. exists wlo. split; [exact SW|]. rewrite L0 in Ha. lia.
Qed.

Lemma pair_main_in_sound : forall E fs wl k h len, facts_hold E fs -> pair_main_in fs wl k h len = true -> bv_unsigned (den E h) <= bv_unsigned (den E len).
Proof.
  intros E fs wl k h len HF H. unfold pair_main_in in H.
  destruct (block_of_twin fs k) as [kb|]; [|discriminate H]. destruct (CtrA.win_lookup wl kb) as [[n kdb]|]; [|discriminate H].
  apply andb_prop in H as [H NMAX]. apply andb_prop in H as [H ST]. apply andb_prop in H as [H EL]. apply andb_prop in H as [_ EH].
  apply sv_eqb_eq in EH, EL. subst h len.
  destruct (size_tail_sound E fs n HF ST) as [N1 _].
  pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF NMAX) as NM. replace (bv_unsigned (den E (VL AREQMAXw))) with 4293918720 in NM by (vm_compute; reflexivity).
  rewrite (sz_last_den E n N1), (twin_len_den E n) by lia. clear - N1. Z.div_mod_to_equations. lia.
Qed.

Lemma twin_full_in_sound : forall E fs h len, facts_hold E fs -> twin_full_in fs h len = true -> bv_unsigned (den E h) <= bv_unsigned (den E len).
Proof.
  intros E fs h len HF H. unfold twin_full_in in H. destruct (tie_of fs len) as [xs|] eqn:TIE; [|discriminate H].
  apply andb_prop in H as [H X8]. apply andb_prop in H as [EH D8]. apply sv_eqb_eq in EH. subst h.
  pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF X8) as B. replace (bv_unsigned (den E (VL SYMCAPw))) with 65536 in B by (vm_compute; reflexivity).
  rewrite (twin_len_den E xs) by lia. rewrite (tie_of_holds E fs len xs HF TIE). pose proof (div8x_holds E fs xs HF D8) as M. clear - M. Z.div_mod_to_equations. lia.
Qed.
Lemma aregion_just_sound : forall E st ms mo wnl ks offs rss k r,
  st_ok segs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) -> aregions_justified st wnl = true ->
  IMap.find k (s_regs st) = Some r -> k <> 0%uint63 ->
  (k = ks /\ bv_unsigned (ev E k) + hiZ E r <= 2 ^ 47)
  \/ (k <> ks /\
      ((exists len kd, CtrA.win_lookup wnl k = Some (len, kd) /\ loZ r = 0 /\ hiZ E r <= bv_unsigned (den E len))
       \/ (bv_unsigned (den E (getr st X2)) <= bv_unsigned (ev E k) + loZ r /\ bv_unsigned (ev E k) + hiZ E r <= 2 ^ 47)
       \/ (view_just (s_facts st) (s_regs st) (getr st X2) (sp_below_anchor_t (s_facts st) (getr st X2)) wnl ks (stack_wlo st) k r = true
           \/ sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k r = true))).
Proof.
  intros E st ms mo wnl ks offs rss k r HS SR J Hk K0. unfold aregions_justified in J. rewrite SR in J. cbv zeta in J.
  pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) J k r Hk) as Jk. clear J.
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  assert (KZ : PrimInt63.eqb k 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  unfold aregion_just in Jk. rewrite KZ in Jk.
  destruct (PrimInt63.eqb k ks) eqn:KS.
  { left. apply Uint63.eqb_correct in KS. split; [exact KS|]. exact (below_top_sound E st ms mo k r HS Hk K0 Jk). }
  assert (NKS : k <> ks) by (apply Uint63.eqb_false_spec; exact KS).
  right. split; [exact NKS|].

  set (SJ := stack_side_just (s_facts st) (getr st X2) (sp_below_anchor_t (s_facts st) (getr st X2)) ks k r) in *.
  set (VJ := view_just (s_facts st) (s_regs st) (getr st X2) (sp_below_anchor_t (s_facts st) (getr st X2)) wnl ks (stack_wlo st) k r) in *.
  set (SL := sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k r) in *.
  assert (REST : (if rg_w r then (if (if SL then true else SJ) then true else VJ) else (if (if VJ then true else SJ) then true else SL)) = true ->
            (bv_unsigned (den E (getr st X2)) <= bv_unsigned (ev E k) + loZ r /\ bv_unsigned (ev E k) + hiZ E r <= 2 ^ 47)
            \/ (VJ = true \/ SL = true)).
  { intros H. destruct SJ eqn:SJE.
    - left. destruct (stack_side_just_sound E st ms mo ks k r HS Hk K0 SJE) as [[X|X] TOP]; [contradiction| split; assumption].
    - right. destruct (rg_w r), VJ, SL; cbn in H; try discriminate H; auto. }
  destruct (CtrA.win_lookup wnl k) as [[len kd]|] eqn:WL.
  - match type of Jk with (if ?c then _ else _) = _ => destruct c eqn:INW end.
    + left. apply andb_prop in INW as [L0 LE]. apply Uint63.eqb_correct in L0. exists len, kd. split; [reflexivity|].
      split; [unfold loZ; rewrite L0; reflexivity|].
      apply orb_prop in LE as [LE|LE]; [apply orb_prop in LE as [LE|LE]; [apply orb_prop in LE as [LE|LE]; [apply orb_prop in LE as [LE|LE]|]|]|].
      * apply sv_eqb_eq in LE. unfold hiZ. rewrite LE. lia.
      * unfold hiZ. exact (vec_hi_in_sound E _ _ _ HF LE).
      * unfold hiZ. exact (pair_main_in_sound E _ _ _ _ _ HF LE).
      * unfold hiZ. exact (twin_full_in_sound E _ _ _ HF LE).
      * exact (KnownA.KnownA.known_leu_q_sound E _ _ _ HF LE).
    + right. exact (REST Jk).
  - right. exact (REST Jk).
Qed.

Lemma stack_window_key_In : forall E n rest wlo, stack_window_key n rest = Some wlo ->
  exists len, In (HeapOp.Win (bv_unsigned (den E (VP STACK_ID wlo))) len HeapOp.K_STACK) (wins_of E n rest).
Proof.
  intros E n. induction n as [|n IH]; intros rest wlo H; [cbn in H; destruct rest; discriminate|].
  destruct rest as [|lo rest1]; [cbn in H; discriminate|].
  destruct rest1 as [|len rest2]; [destruct lo; cbn in H; discriminate|].
  destruct rest2 as [|kd rest']; [destruct lo; cbn in H; discriminate|].
  cbn [stack_window_key] in H.
  assert (STEP : stack_window_key n rest' = Some wlo ->
            exists len0, In (HeapOp.Win (bv_unsigned (den E (VP STACK_ID wlo))) len0 HeapOp.K_STACK) (wins_of E (S n) (lo :: len :: kd :: rest'))).
  { intros H'. destruct (IH rest' wlo H') as (len0 & K3). exists len0. rewrite wins_of_cons. right. exact K3. }
  destruct lo as [|k wlo0| | | | | | | | |]; cbn in H; try (apply STEP; exact H).
  destruct kd as [kdw| | | | | | | | | |]; cbn in H; try (apply STEP; exact H).
  destruct (PrimInt63.eqb k STACK_ID && weqb kdw wzero) eqn:C; [| apply STEP; exact H].
  injection H as ->. apply andb_prop in C as [H1 H2]. apply Uint63.eqb_correct in H1. subst k.
  exists (bv_unsigned (den E len)). rewrite wins_of_cons. left.
  unfold HeapOp.K_STACK. rewrite (unsigned_VL E kdw), (HeapCtr.weqb_wzero_unsigned' kdw H2). reflexivity.
Qed.

Lemma sp_floor_sound : forall E st ms mo hargs n md A nw rest k off r,
  st_ok segs OPS E st ms mo -> sp_floor_ok st hargs = true ->
  heap_nwin hargs = Some n -> hargs = VL md :: A :: VL nw :: rest -> sp_region st = Some (k, off, r) ->
  0 <= bv_unsigned (ev E k) + loZ r ->
  exists wlo len, In (HeapOp.Win (bv_unsigned (den E (VP STACK_ID wlo))) len HeapOp.K_STACK) (wins_of E n rest)
    /\ bv_unsigned (den E (VP STACK_ID wlo)) <= bv_unsigned (ev E k) + loZ r.
Proof.
  intros E st ms mo hargs n md A nw rest k off r HS H Hn Eh SR LO0. unfold sp_floor_ok in H. rewrite Hn, Eh, SR in H.
  destruct (stack_window_key n rest) as [wlo|] eqn:SK; [|discriminate].
  destruct (okey wlo) as [kw|] eqn:KW; [|discriminate].
  apply andb_prop in H as [NW H].
  pose proof (so_facts _ _ _ _ _ _ HS) as HF. pose proof (so_zero _ _ _ _ _ _ HS) as HZ.
  destruct (nowrap_kb_sound E _ HF STACK_ID wlo NW) as [R1 D1].
  destruct (okey_sound _ _ KW) as [EKW _].
  destruct (stack_window_key_In E n rest wlo SK) as (len & IN).
  exists wlo, len. split; [exact IN|]. rewrite D1, <- EKW.
  destruct (PrimInt63.eqb k STACK_ID) eqn:K1.
  - apply Uint63.eqb_correct in K1. subst k. rewrite kleb_keyZ in H. apply Z.leb_le in H. unfold loZ. lia.
  - destruct (GTwinSub.GTwinSub.find_lb (s_facts st) k STACK_ID) as [o2|] eqn:FL; [|discriminate].
    apply andb_prop in H as [NW2 LE]. apply Z.leb_le in LE.
    destruct (nowrap_kb_sound E _ HF STACK_ID o2 NW2) as [R2 D2].
    pose proof (GTwinSub.GTwinSub.find_lb_holds E _ k STACK_ID o2 HF FL) as LB. rewrite D2, HeapCtr.den_VPz in LB. unfold loZ. lia.
Qed.

Lemma sp_altop_sound : forall E st ms mo hargs n md A nw rest,
  st_ok segs OPS E st ms mo -> sp_altop_ok st hargs = true ->
  heap_nwin hargs = Some n -> hargs = VL md :: A :: VL nw :: rest ->
  exists wlo len, stack_window_key n rest = Some wlo
    /\ In (HeapOp.Win (bv_unsigned (den E (VP STACK_ID wlo))) len HeapOp.K_STACK) (wins_of E n rest)
    /\ bv_unsigned (den E (getr st X2)) - bv_unsigned (den E (VP STACK_ID wlo)) <= SPALT.
Proof.
  intros E st ms mo hargs n md A nw rest HS H Hn Eh. unfold sp_altop_ok in H. rewrite Hn, Eh in H.
  destruct (getr st X2) as [|k off| | | | | | | | |] eqn:GX; try discriminate.
  destruct (stack_window_key n rest) as [wlo|] eqn:SK; [|discriminate].
  apply andb_prop in H as [H ARM]. apply andb_prop in H as [NW1 NW2].
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  destruct (nowrap_kb_sound E _ HF STACK_ID wlo NW1) as [R1 D1]. destruct (nowrap_kb_sound E _ HF k off NW2) as [R2 D2].
  destruct (stack_window_key_In E n rest wlo SK) as (len & IN). exists wlo, len. split; [reflexivity|]. split; [exact IN|]. rewrite D1, D2.
  destruct (PrimInt63.eqb k STACK_ID) eqn:K1.
  - apply Uint63.eqb_correct in K1. subst k. apply Z.leb_le in ARM. lia.
  - destruct (GTwinSub.GTwinSub.find_ub (s_facts st) k) as [[kb o1]|] eqn:UB; [|discriminate].
    apply andb_prop in ARM as [ARM LE]. apply andb_prop in ARM as [KB NW3]. apply Uint63.eqb_correct in KB. subst kb. apply Z.leb_le in LE.
    destruct (nowrap_kb_sound E _ HF STACK_ID o1 NW3) as [R3 D3].
    pose proof (GTwinSub.GTwinSub.find_ub_holds E _ k STACK_ID o1 HF UB) as U. rewrite D3, HeapCtr.den_VPz in U. lia.
Qed.

Lemma sp_floor_key : forall E st ms mo hargs n md A nw rest k off r wlo,
  st_ok segs OPS E st ms mo -> sp_floor_ok st hargs = true ->
  heap_nwin hargs = Some n -> hargs = VL md :: A :: VL nw :: rest -> sp_region st = Some (k, off, r) ->
  stack_window_key n rest = Some wlo ->
  bv_unsigned (den E (VP STACK_ID wlo)) <= bv_unsigned (ev E k) + loZ r.
Proof.
  intros E st ms mo hargs n md A nw rest k off r wlo HS H Hn Eh SR SK. unfold sp_floor_ok in H. rewrite Hn, Eh, SR, SK in H.
  destruct (okey wlo) as [kw|] eqn:KW; [|discriminate].
  apply andb_prop in H as [NW H].
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  destruct (nowrap_kb_sound E _ HF STACK_ID wlo NW) as [R1 D1].
  destruct (okey_sound _ _ KW) as [EKW _]. rewrite D1, <- EKW.
  destruct (PrimInt63.eqb k STACK_ID) eqn:K1.
  - apply Uint63.eqb_correct in K1. subst k. rewrite kleb_keyZ in H. apply Z.leb_le in H. unfold loZ. lia.
  - destruct (GTwinSub.GTwinSub.find_lb (s_facts st) k STACK_ID) as [o2|] eqn:FL; [|discriminate].
    apply andb_prop in H as [NW2 LE]. apply Z.leb_le in LE.
    destruct (nowrap_kb_sound E _ HF STACK_ID o2 NW2) as [R2 D2].
    pose proof (GTwinSub.GTwinSub.find_lb_holds E _ k STACK_ID o2 HF FL) as LB. rewrite D2, HeapCtr.den_VPz in LB. unfold loZ. lia.
Qed.

Lemma cell_eqb_eq : forall a b, cell_eqb a b = true -> a = b.
Proof.
  intros [i w v] [i' w' v'] H. unfold cell_eqb in H. cbn [c_idx c_w c_v] in H. apply andb_prop in H as [H V]. apply andb_prop in H as [I W].
  apply Uint63.eqb_correct in I. apply Uint63.eqb_correct in W. apply sv_eqb_eq in V. subst. reflexivity.
Qed.
Lemma slot_eqb_eq : forall a b, slot_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply cell_eqb_eq in H1. subst y. f_equal. exact (IH b H2).
Qed.
Lemma grans_eqb_eq : forall a b, grans_eqb a b = true -> a = b.
Proof.
  induction a as [|[k g] a IH]; intros [|[k' g'] b] H; cbn [grans_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Uint63.eqb_correct in H1. subst k'.
  unfold gran_eqb in H2. apply andb_prop in H2 as [D C]. apply Bool.eqb_prop in D. apply slot_eqb_eq in C.
  destruct g as [d c], g' as [d' c']. cbn [g_dirty g_cells] in D, C. subst. f_equal. exact (IH b H3).
Qed.

Lemma in_granule_1 : forall o, in_granule o 1%uint63 = true.
Proof.
  intros o. unfold in_granule. apply Uint63.leb_spec. destruct (gidx_ok o) as [_ R].
  rewrite Uint63.add_spec. change (to_Z 1%uint63) with 1. change (to_Z 8%uint63) with 8.
  rewrite Z.mod_small; [lia|]. pose proof wB_pos. change wB with (2 ^ 63) in *. lia.
Qed.

Lemma twin_region_cells : forall n,
  rg_cells (twin_region n) = IMap.empty
  \/ exists w, n = VL w /\ PrimInt63.eqb (PrimInt63.land (wl w) 7%uint63) 0%uint63 = false
       /\ rg_cells (twin_region n) = IMap.add (granule (PrimInt63.lsr (wl w) 3%uint63))
                                        (Gran false [Cell (gidx (PrimInt63.lsr (wl w) 3%uint63)) 1%uint63 (VL (wlit (PrimInt63.land (wl w) 7%uint63)))]) IMap.empty.
Proof.
  intros n. destruct n as [w| | | | | | | | | |]; try (left; reflexivity).
  unfold twin_region. cbv zeta. destruct (PrimInt63.eqb (PrimInt63.land (wl w) 7%uint63) 0%uint63) eqn:T0; [left; reflexivity|].
  right. exists w. split; [reflexivity|]. split; [exact T0|].
  unfold region_store. rewrite in_granule_1. unfold region_store1. cbn [rg_cells IMap.find IMap.empty]. reflexivity.
Qed.
Lemma twin_region_hi : forall n, rg_hi (twin_region n) = twin_len n.
Proof.
  intros n. destruct n as [w| | | | | | | | | |]; try reflexivity.
  unfold twin_region. cbv zeta. destruct (PrimInt63.eqb (PrimInt63.land (wl w) 7%uint63) 0%uint63); [reflexivity|].
  unfold region_store. rewrite in_granule_1. unfold region_store1. cbn [rg_cells IMap.find IMap.empty]. reflexivity.
Qed.

Lemma len_is_twin_refl : forall fs n, len_is_twin fs (twin_len n) n = true.
Proof. intros fs n. unfold len_is_twin. rewrite ValP.sv_eqb_refl. reflexivity. Qed.
Lemma len_is_twin_sound : forall E fs len n, facts_hold E fs -> len_is_twin fs len n = true -> bv_unsigned (den E n) + 7 < 2 ^ 62 ->
  bv_unsigned (den E len) = (bv_unsigned (den E n) + 7) / 8.
Proof.
  intros E fs len n HF H B. unfold len_is_twin in H. apply orb_prop in H as [H|H].
  - apply sv_eqb_eq in H. subst len. apply twin_len_den. exact B.
  - destruct (tie_of fs len) as [xs|] eqn:TIE; [|discriminate H]. apply andb_prop in H as [EQ D8]. apply sv_eqb_eq in EQ. subst xs.
    rewrite (tie_of_holds E fs len n HF TIE). pose proof (div8x_holds E fs n HF D8) as M. clear - M. Z.div_mod_to_equations. lia.
Qed.

Lemma is_twin_region_sound : forall priv E m sh r n,
  region_ok segs priv E m sh r -> PrimInt63.eqb sh 0%uint63 = false ->
  is_twin_region r n = true ->
  bv_unsigned (den E n) + 7 < 2 ^ 62 ->
  match n with VL _ => True | _ => bv_unsigned (den E n) mod 8 = 0 end ->
  forall g, 0 <= g -> 8 * g < bv_unsigned (den E n) ->
    rb segs m (bv_unsigned (ev E sh) + g)
    = Some (Z_to_bv 8 (if 8 * g + 8 <=? bv_unsigned (den E n) then 0 else bv_unsigned (den E n) - 8 * g)).
Proof.
  intros priv E m sh r n RO NZ H B SHAPE g G0 G1. set (N := bv_unsigned (den E n)) in *.
  unfold is_twin_region in H. cbv zeta in H. do 4 (apply andb_prop in H as [H ?]).
  rename H into LO, H3 into HI, H2 into WR, H1 into BG, H0 into CE.
  apply Uint63.eqb_correct in LO. apply sv_eqb_eq in HI. rewrite twin_region_hi in HI.
  destruct (rg_bg r) eqn:BGE; try discriminate BG. clear BG.
  apply grans_eqb_eq in CE.
  assert (HIZ : hiZ E r = (N + 7) / 8) by (unfold hiZ; rewrite HI; apply twin_len_den; exact B).
  assert (LOZ : loZ r = 0) by (unfold loZ; rewrite LO; reflexivity).
  assert (GIN : loZ r <= g < hiZ E r) by (rewrite LOZ, HIZ; clear - G0 G1; Z.div_mod_to_equations; lia).

  assert (BT : IMap.bst (rg_cells (twin_region n))).
  { destruct (twin_region_cells n) as [->|(w & _ & _ & ->)]; [apply IMap.bst_empty| apply IMap.bst_add; apply IMap.bst_empty]. }
  assert (FE : forall gk, IMap.find gk (rg_cells r) = IMap.find gk (rg_cells (twin_region n))).
  { intros gk. apply IMap.option_ext. intros gr. rewrite <- (IMap.elements_spec gk gr _ (ro_bst _ _ _ _ _ _ RO)), <- (IMap.elements_spec gk gr _ BT), CE. reflexivity. }
  destruct (twin_region_cells n) as [EMP|(w & -> & T0 & CELLS)].
  -
    assert (UNC : uncovered r g). { intros gk gr _ F. rewrite FE, EMP, IMap.find_empty in F. discriminate. }
    pose proof (ro_bg _ _ _ _ _ _ RO g (fun _ => GIN) ltac:(intros X; rewrite X in NZ; discriminate) UNC) as BGB.
    unfold bg_byte in BGB. rewrite BGE in BGB. rewrite BGB. do 2 f_equal.
    destruct (Z.leb_spec (8 * g + 8) N) as [|GT]; [reflexivity| exfalso].
    destruct n as [w| | | | | | | | | |]; try (clear - SHAPE G1 GT; Z.div_mod_to_equations; lia).

    unfold twin_region in EMP. cbv zeta in EMP.
    destruct (PrimInt63.eqb (PrimInt63.land (wl w) 7%uint63) 0%uint63) eqn:T0.
    + apply Uint63.eqb_correct in T0. pose proof (gidx_ok (wl w)) as [GI _]. unfold gidx in GI. rewrite T0 in GI. change (to_Z 0%uint63) with 0 in GI.
      subst N. rewrite unsigned_VL in *. assert (WT : wt w = false) by (rewrite w2Z_wt; apply Z.leb_gt; unfold two63; lia).
      rewrite (w2Z_nowt w WT) in *. clear - GI G1 GT. Z.div_mod_to_equations. lia.
    + unfold region_store in EMP. rewrite in_granule_1 in EMP. unfold region_store1 in EMP. cbn [rg_cells IMap.find IMap.empty] in EMP.
      exfalso. clear - EMP. unfold IMap.add, IMap.empty in EMP. cbn in EMP. discriminate EMP.
  -
    subst N. rewrite unsigned_VL in *. assert (WT : wt w = false) by (rewrite w2Z_wt; apply Z.leb_gt; unfold two63; lia).
    rewrite (w2Z_nowt w WT) in *. set (N := to_Z (wl w)) in *. set (o := PrimInt63.lsr (wl w) 3%uint63) in *.
    assert (EO : to_Z o = N / 8) by (unfold o; rewrite lsr_spec; reflexivity).
    assert (KO : keyZ o = N / 8).
    { destruct (keyZ_cases o) as [[_ ->]|[X _]]; [exact EO|]. exfalso. rewrite EO in X. clear - X B. Z.div_mod_to_equations. lia. }
    assert (N0 : 0 <= N) by (pose proof (int_range (wl w)); unfold N; lia).
    destruct (granule_gidx o ltac:(rewrite KO; unfold two63; clear - B N0; Z.div_mod_to_equations; lia)) as [GG GR].
    assert (T0Z : to_Z (PrimInt63.land (wl w) 7%uint63) = N mod 8) by (pose proof (gidx_ok (wl w)) as [GI _]; exact GI).
    assert (T0NZ : N mod 8 <> 0).
    { intros X. rewrite <- T0Z in X. apply Uint63.eqb_false_spec in T0. apply T0. apply to_Z_inj. rewrite X. reflexivity. }
    destruct (Z.eq_dec g (N / 8)) as [GE|GNE].
    +
      pose proof (ro_cells _ _ _ _ _ _ RO (granule o) _ ltac:(rewrite FE, CELLS; apply IMap.find_add_same; apply IMap.bst_empty)) as [_ FC].
      cbn [g_cells] in FC. apply Forall_inv in FC. destruct FC as (_ & _ & _ & CB). cbn [c_idx c_w c_v] in CB.
      specialize (CB 0 ltac:(change (to_Z 1%uint63) with 1; lia)).
      replace (bv_unsigned (ev E sh) + 8 * keyZ (granule o) + to_Z (gidx o) + 0) with (bv_unsigned (ev E sh) + g) in CB by (rewrite GE, <- KO, GG; lia).
      rewrite CB. do 2 f_equal. unfold byte_of. rewrite den_VL, wbv_unsigned, wlit_ok, T0Z. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
      destruct (Z.leb_spec (8 * g + 8) N) as [LE|GT]; [exfalso; clear - LE GE; Z.div_mod_to_equations; lia|].
      cbv iota. f_equal. clear - GE. Z.div_mod_to_equations. lia.
    +
      assert (UNC : uncovered r g).
      { intros gk gr KG F. rewrite FE, CELLS in F.
        destruct (Uint63.eqb (granule o) gk) eqn:Q.
        - apply Uint63.eqb_correct in Q. subst gk. rewrite IMap.find_add_same in F by apply IMap.bst_empty. injection F as <-.
          cbn [g_dirty g_cells]. split; [reflexivity|]. constructor; [|constructor]. unfold covers. cbn [c_idx c_w]. change (to_Z 1%uint63) with 1.
          intros CV. apply GNE. rewrite <- KO, GG, KG. clear - CV. Z.div_mod_to_equations. lia.
        - rewrite IMap.find_add_other_eqb in F by (apply IMap.bst_empty || exact Q). rewrite IMap.find_empty in F. discriminate. }
      pose proof (ro_bg _ _ _ _ _ _ RO g (fun _ => GIN) ltac:(intros X; rewrite X in NZ; discriminate) UNC) as BGB.
      unfold bg_byte in BGB. rewrite BGE in BGB. rewrite BGB. do 2 f_equal.
      destruct (Z.leb_spec (8 * g + 8) N) as [|GT]; [reflexivity| exfalso]. clear - GNE G1 GT. Z.div_mod_to_equations. lia.
Qed.

Lemma twin_region_fields : forall n,
  rg_lo (twin_region n) = 0%uint63 /\ rg_w (twin_region n) = false /\ rg_bg (twin_region n) = BGZero.
Proof.
  intros n. destruct n as [w| | | | | | | | | |]; try (repeat split; reflexivity).
  unfold twin_region. cbv zeta. destruct (PrimInt63.eqb (PrimInt63.land (wl w) 7%uint63) 0%uint63); [repeat split; reflexivity|].
  unfold region_store. rewrite in_granule_1. unfold region_store1. cbn [rg_cells IMap.find IMap.empty]. repeat split; reflexivity.
Qed.

Lemma twin_region_ok : forall priv E m sh n,
  PrimInt63.eqb sh 0%uint63 = false ->
  1 <= bv_unsigned (den E n) -> bv_unsigned (den E n) + 7 < 2 ^ 62 ->
  match n with VL _ => True | _ => bv_unsigned (den E n) mod 8 = 0 end ->
  bv_unsigned (ev E sh) + (bv_unsigned (den E n) + 7) / 8 < two64 ->
  (forall g, 0 <= g -> 8 * g < bv_unsigned (den E n) ->
      rb segs m (bv_unsigned (ev E sh) + g) = Some (Z_to_bv 8 (if 8 * g + 8 <=? bv_unsigned (den E n) then 0 else bv_unsigned (den E n) - 8 * g))
      /\ find_segment segs (bv_unsigned (ev E sh) + g) 1 = None) ->
  region_ok segs priv E m sh (twin_region n).
Proof.
  intros priv E m sh n NZ N1 B SHAPE HI64 PAT. set (N := bv_unsigned (den E n)) in *.
  destruct (twin_region_fields n) as (LO & WR & BG).
  assert (HIZ : hiZ E (twin_region n) = (N + 7) / 8) by (unfold hiZ; rewrite twin_region_hi; apply twin_len_den; exact B).
  assert (LOZ : loZ (twin_region n) = 0) by (unfold loZ; rewrite LO; reflexivity).
  assert (BT : IMap.bst (rg_cells (twin_region n))).
  { destruct (twin_region_cells n) as [->|(w & _ & _ & ->)]; [apply IMap.bst_empty| apply IMap.bst_add; apply IMap.bst_empty]. }
  assert (GR : forall o, 0 <= o < (N + 7) / 8 -> 0 <= o /\ 8 * o < N) by (intros o Ho; split; [lia|]; clear - Ho; Z.div_mod_to_equations; lia).
  pose proof (bv_unsigned_in_range 64 (ev E sh)) as RSH.
  constructor.
  - exact BT.
  - intros _. rewrite LOZ, HIZ. lia.
  - intros _ a Ha. rewrite LOZ, HIZ in Ha. destruct (GR (a - bv_unsigned (ev E sh)) ltac:(lia)) as [G0 G1].
    destruct (PAT _ G0 G1) as [P1 P2]. replace (bv_unsigned (ev E sh) + (a - bv_unsigned (ev E sh))) with a in P1, P2 by lia.
    split; [rewrite P1; discriminate|]. split; [rewrite WR; discriminate| exact P2].
  -
    intros g gr F. destruct (twin_region_cells n) as [EMP|(w & -> & T0 & CELLS)]; [rewrite EMP, IMap.find_empty in F; discriminate|].
    rewrite CELLS in F. subst N. rewrite unsigned_VL in *.
    assert (WT : wt w = false) by (rewrite w2Z_wt; apply Z.leb_gt; unfold two63; lia). rewrite (w2Z_nowt w WT) in *.
    set (N := to_Z (wl w)) in *. set (o := PrimInt63.lsr (wl w) 3%uint63) in *.
    destruct (Uint63.eqb (granule o) g) eqn:Q; [| rewrite IMap.find_add_other_eqb in F by (apply IMap.bst_empty || exact Q); rewrite IMap.find_empty in F; discriminate].
    apply Uint63.eqb_correct in Q. subst g. rewrite IMap.find_add_same in F by apply IMap.bst_empty. injection F as <-. cbn [g_cells].
    assert (EO : to_Z o = N / 8) by (unfold o; rewrite lsr_spec; reflexivity).
    assert (KO : keyZ o = N / 8).
    { destruct (keyZ_cases o) as [[_ ->]|[X _]]; [exact EO|]. exfalso. rewrite EO in X. clear - X B. Z.div_mod_to_equations. lia. }
    destruct (granule_gidx o ltac:(rewrite KO; unfold two63; clear - B N1; Z.div_mod_to_equations; lia)) as [GG GRR].
    assert (T0Z : to_Z (PrimInt63.land (wl w) 7%uint63) = N mod 8) by (pose proof (gidx_ok (wl w)) as [GI _]; exact GI).
    assert (T0NZ : N mod 8 <> 0).
    { intros X. rewrite <- T0Z in X. apply Uint63.eqb_false_spec in T0. apply T0. apply to_Z_inj. rewrite X. reflexivity. }
    split; [cbn; auto|]. constructor; [|constructor]. unfold cell_ok. cbn [c_idx c_w c_v]. change (to_Z 1%uint63) with 1.
    split; [lia|]. split; [lia|]. split; [lia|]. intros i Hi. assert (i = 0) by lia. subst i.
    destruct (PAT (N / 8) ltac:(clear - N1; Z.div_mod_to_equations; lia) ltac:(clear - T0NZ; Z.div_mod_to_equations; lia)) as [P1 _].
    replace (bv_unsigned (ev E sh) + 8 * keyZ (granule o) + to_Z (gidx o) + 0) with (bv_unsigned (ev E sh) + N / 8) by (rewrite <- KO, GG; lia).
    rewrite P1. do 2 f_equal. unfold byte_of. rewrite den_VL, wbv_unsigned, wlit_ok, T0Z. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
    destruct (Z.leb_spec (8 * (N / 8) + 8) N) as [LE|GT]; [exfalso; clear - LE; Z.div_mod_to_equations; lia|].
    cbv iota. f_equal. clear - N1. Z.div_mod_to_equations. lia.
  -
    intros g gr c i F Hc Hi. cbv zeta. split; [| intros X; rewrite X in NZ; discriminate]. intros _.
    destruct (twin_region_cells n) as [EMP|(w & -> & T0 & CELLS)]; [rewrite EMP, IMap.find_empty in F; discriminate|].
    rewrite CELLS in F. subst N. rewrite unsigned_VL in *.
    assert (WT : wt w = false) by (rewrite w2Z_wt; apply Z.leb_gt; unfold two63; lia). rewrite (w2Z_nowt w WT) in *.
    set (N := to_Z (wl w)) in *. set (o := PrimInt63.lsr (wl w) 3%uint63) in *.
    destruct (Uint63.eqb (granule o) g) eqn:Q; [| rewrite IMap.find_add_other_eqb in F by (apply IMap.bst_empty || exact Q); rewrite IMap.find_empty in F; discriminate].
    apply Uint63.eqb_correct in Q. subst g. rewrite IMap.find_add_same in F by apply IMap.bst_empty. injection F as <-. cbn [g_cells] in Hc.
    destruct Hc as [<-|[]]. cbn [c_idx c_w] in *. change (to_Z 1%uint63) with 1 in Hi. assert (i = 0) by lia. subst i.
    assert (EO : to_Z o = N / 8) by (unfold o; rewrite lsr_spec; reflexivity).
    assert (KO : keyZ o = N / 8).
    { destruct (keyZ_cases o) as [[_ ->]|[X _]]; [exact EO|]. exfalso. rewrite EO in X. clear - X B. Z.div_mod_to_equations. lia. }
    destruct (granule_gidx o ltac:(rewrite KO; unfold two63; clear - B N1; Z.div_mod_to_equations; lia)) as [GG GRR].
    assert (T0Z : to_Z (PrimInt63.land (wl w) 7%uint63) = N mod 8) by (pose proof (gidx_ok (wl w)) as [GI _]; exact GI).
    assert (T0NZ : N mod 8 <> 0).
    { intros X. rewrite <- T0Z in X. apply Uint63.eqb_false_spec in T0. apply T0. apply to_Z_inj. rewrite X. reflexivity. }
    rewrite LOZ, HIZ. replace (8 * keyZ (granule o) + to_Z (gidx o) + 0) with (N / 8) by (rewrite <- KO, GG; lia).
    clear - T0NZ N1. Z.div_mod_to_equations. lia.
  -
    intros o R1 _ UNC. specialize (R1 NZ). rewrite LOZ, HIZ in R1. unfold bg_byte. rewrite BG.
    destruct (GR o R1) as [G0 G1]. destruct (PAT o G0 G1) as [P1 _]. rewrite P1. do 2 f_equal.
    destruct (Z.leb_spec (8 * o + 8) N) as [|GT]; [reflexivity| exfalso].
    destruct (twin_region_cells n) as [EMP|(w & -> & T0 & CELLS)].
    + destruct n as [w| | | | | | | | | |]; try (clear - SHAPE G1 GT; Z.div_mod_to_equations; lia).
      unfold twin_region in EMP. cbv zeta in EMP.
      destruct (PrimInt63.eqb (PrimInt63.land (wl w) 7%uint63) 0%uint63) eqn:T0.
      * apply Uint63.eqb_correct in T0. pose proof (gidx_ok (wl w)) as [GI _]. unfold gidx in GI. rewrite T0 in GI. change (to_Z 0%uint63) with 0 in GI.
        subst N. rewrite unsigned_VL in *. assert (WT : wt w = false) by (rewrite w2Z_wt; apply Z.leb_gt; unfold two63; lia).
        rewrite (w2Z_nowt w WT) in *. clear - GI G1 GT. Z.div_mod_to_equations. lia.
      * unfold region_store in EMP. rewrite in_granule_1 in EMP. unfold region_store1 in EMP. cbn [rg_cells IMap.find IMap.empty] in EMP.
        clear - EMP. unfold IMap.add, IMap.empty in EMP. cbn in EMP. discriminate EMP.
    +
      subst N. rewrite unsigned_VL in *. assert (WT : wt w = false) by (rewrite w2Z_wt; apply Z.leb_gt; unfold two63; lia).
      rewrite (w2Z_nowt w WT) in *. set (N := to_Z (wl w)) in *. set (o0 := PrimInt63.lsr (wl w) 3%uint63) in *.
      assert (EO : to_Z o0 = N / 8) by (unfold o0; rewrite lsr_spec; reflexivity).
      assert (KO : keyZ o0 = N / 8).
      { destruct (keyZ_cases o0) as [[_ ->]|[X _]]; [exact EO|]. exfalso. rewrite EO in X. clear - X B. Z.div_mod_to_equations. lia. }
      destruct (granule_gidx o0 ltac:(rewrite KO; unfold two63; clear - B N1; Z.div_mod_to_equations; lia)) as [GG GRR].
      assert (OE : o = N / 8) by (clear - G1 GT; Z.div_mod_to_equations; lia).
      destruct (UNC (granule o0) _ ltac:(rewrite OE, <- KO, GG; clear - GRR; Z.div_mod_to_equations; lia)
                    ltac:(rewrite CELLS; apply IMap.find_add_same; apply IMap.bst_empty)) as [_ FC].
      cbn [g_cells] in FC. apply Forall_inv in FC. apply FC. unfold covers. cbn [c_idx c_w]. change (to_Z 1%uint63) with 1.
      rewrite OE, <- KO, GG. clear - GRR. Z.div_mod_to_equations. lia.
Qed.

Lemma tail_region_fields : forall n,
  rg_lo (tail_region n) = 0%uint63 /\ rg_hi (tail_region n) = VL wone /\ rg_w (tail_region n) = false /\ rg_bg (tail_region n) = BGZero
  /\ rg_cells (tail_region n) = IMap.add (granule 0%uint63) (Gran false [Cell (gidx 0%uint63) 1%uint63 (sz_and7 n)]) IMap.empty.
Proof.
  intros n. unfold tail_region, region_store. rewrite in_granule_1. unfold region_store1. cbn [rg_cells IMap.find IMap.empty rg_lo rg_hi rg_w rg_bg].
  repeat split; reflexivity.
Qed.
Lemma region_is_inv : forall r t, region_is r t = true ->
  rg_lo r = rg_lo t /\ rg_hi r = rg_hi t /\ rg_w r = rg_w t /\ rg_bg r = BGZero /\ rg_bg t = BGZero
  /\ IMap.elements (rg_cells r) = IMap.elements (rg_cells t).
Proof.
  intros r t H. unfold region_is in H. do 4 (apply andb_prop in H as [H ?]).
  apply Uint63.eqb_correct in H. apply sv_eqb_eq in H3. apply Bool.eqb_prop in H2. apply grans_eqb_eq in H0.
  destruct (rg_bg r), (rg_bg t); try discriminate H1. repeat split; assumption.
Qed.
Lemma find_tail_sound : forall E fs sh n s2, facts_hold E fs -> find_tail fs sh n = Some s2 -> ev E s2 = den E (tail_rhs sh n).
Proof.
  intros E fs sh n s2 HF H. unfold find_tail in H. induction fs as [|f fs IH]; [discriminate H|].
  apply Forall_cons_iff in HF as [Hf HF].
  destruct f as [| | | |a b| | |]; try (apply IH; assumption).
  destruct a as [|s z| | | | | | | | |]; try (apply IH; assumption).
  destruct (weqb z wzero && sv_eqb b (tail_rhs sh n)) eqn:Q; [| apply IH; assumption].
  injection H as <-. apply andb_prop in Q as [Z0 B0]. apply weqb_eq in Z0. apply sv_eqb_eq in B0. subst z b.
  cbn [fact_holds] in Hf. rewrite HeapCtr.den_VPz in Hf. exact Hf.
Qed.
Lemma tail_rhs_den : forall E sh n, 1 <= bv_unsigned (den E n) -> bv_unsigned (ev E sh) + (bv_unsigned (den E n) - 1) / 8 < 2 ^ 64 ->
  bv_unsigned (den E (tail_rhs sh n)) = bv_unsigned (ev E sh) + (bv_unsigned (den E n) - 1) / 8.
Proof.
  intros E sh n N1 B. unfold tail_rhs. rewrite ValP.den_sv_alu. unfold alu64, alu. rewrite bv_add_unsigned, HeapCtr.den_VPz, (sz_last_den E n N1).
  apply bv_wrap_small. pose proof (bv_unsigned_in_range 64 (ev E sh)). pose proof (bv_unsigned_in_range 64 (den E n)).
  change (bv_modulus 64) with (2 ^ 64) in *. split; [| exact B]. assert (0 <= (bv_unsigned (den E n) - 1) / 8) by (apply Z.div_pos; lia). lia.
Qed.
Lemma tail_scan_inv : forall fs R sh n s2, tail_scan fs R sh n = Some s2 ->
  find_tail fs sh n = Some s2 /\ s2 <> 0%uint63 /\ s2 <> sh /\ exists r2, IMap.find s2 R = Some r2 /\ is_tail_region r2 n = true.
Proof.
  intros fs R sh n s2 H. unfold tail_scan in H. destruct (find_tail fs sh n) as [s|] eqn:FT; [|discriminate H].
  destruct (IMap.find s R) as [r2|] eqn:F2; [|discriminate H].
  destruct (is_tail_region r2 n && negb (PrimInt63.eqb s 0%uint63) && negb (PrimInt63.eqb s sh)) eqn:Q; [|discriminate H].
  injection H as <-. apply andb_prop in Q as [Q NS]. apply andb_prop in Q as [TR N0]. apply negb_true_iff in NS, N0.
  apply Uint63.eqb_false_spec in NS, N0. split; [reflexivity|]. split; [exact N0|]. split; [exact NS|]. exists r2. split; [exact F2| exact TR].
Qed.

Lemma tail_region_byte : forall priv E m s2 r2 n, region_ok segs priv E m s2 r2 -> is_tail_region r2 n = true ->
  rb segs m (bv_unsigned (ev E s2)) = Some (Z_to_bv 8 (bv_unsigned (den E n) mod 8)).
Proof.
  intros priv E m s2 r2 n RO TR. destruct (region_is_inv _ _ TR) as (_ & _ & _ & _ & _ & CE).
  destruct (tail_region_fields n) as (_ & _ & _ & _ & CELLS).
  assert (BT : IMap.bst (rg_cells (tail_region n))) by (rewrite CELLS; apply IMap.bst_add; apply IMap.bst_empty).
  assert (FE : forall gk, IMap.find gk (rg_cells r2) = IMap.find gk (rg_cells (tail_region n))).
  { intros gk. apply IMap.option_ext. intros gr. rewrite <- (IMap.elements_spec gk gr _ (ro_bst _ _ _ _ _ _ RO)), <- (IMap.elements_spec gk gr _ BT), CE. reflexivity. }
  pose proof (ro_cells _ _ _ _ _ _ RO (granule 0%uint63) _ ltac:(rewrite FE, CELLS; apply IMap.find_add_same; apply IMap.bst_empty)) as [_ FC].
  cbn [g_cells] in FC. apply Forall_inv in FC. destruct FC as (_ & _ & _ & CB). cbn [c_idx c_w c_v] in CB.
  specialize (CB 0 ltac:(change (to_Z 1%uint63) with 1; lia)).
  replace (bv_unsigned (ev E s2) + 8 * keyZ (granule 0%uint63) + to_Z (gidx 0%uint63) + 0) with (bv_unsigned (ev E s2)) in CB by (vm_compute (keyZ (granule 0%uint63)); vm_compute (to_Z (gidx 0%uint63)); lia).
  rewrite CB. do 2 f_equal. unfold byte_of. rewrite sz_and7_den. change (8 * 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
Qed.

Lemma twin_main_ok : forall priv E m sh n,
  PrimInt63.eqb sh 0%uint63 = false ->
  1 <= bv_unsigned (den E n) ->
  bv_unsigned (ev E sh) + (bv_unsigned (den E n) - 1) / 8 < two64 ->
  (forall g, 0 <= g < (bv_unsigned (den E n) - 1) / 8 ->
      rb segs m (bv_unsigned (ev E sh) + g) = Some (Z_to_bv 8 0) /\ find_segment segs (bv_unsigned (ev E sh) + g) 1 = None) ->
  region_ok segs priv E m sh (twin_main n).
Proof.
  intros priv E m sh n NZ N1 HI64 PAT. set (N := bv_unsigned (den E n)) in *.
  assert (HIZ : hiZ E (twin_main n) = (N - 1) / 8) by (unfold hiZ, twin_main; cbn [rg_hi]; apply sz_last_den; exact N1).
  assert (HIP : 0 <= (N - 1) / 8) by (apply Z.div_pos; lia).
  assert (LOZ : loZ (twin_main n) = 0) by reflexivity.
  pose proof (bv_unsigned_in_range 64 (ev E sh)) as RSH.
  constructor.
  - cbn [twin_main rg_cells]. apply IMap.bst_empty.
  - intros _. rewrite LOZ, HIZ. lia.
  - intros _ a Ha. rewrite LOZ, HIZ in Ha. destruct (PAT (a - bv_unsigned (ev E sh)) ltac:(lia)) as [P1 P2].
    replace (bv_unsigned (ev E sh) + (a - bv_unsigned (ev E sh))) with a in P1, P2 by lia.
    split; [rewrite P1; discriminate|]. split; [cbn [twin_main rg_w]; discriminate| exact P2].
  - intros g gr F. cbn [twin_main rg_cells] in F. rewrite IMap.find_empty in F. discriminate.
  - intros g gr c i F. cbn [twin_main rg_cells] in F. rewrite IMap.find_empty in F. discriminate.
  - intros o R1 _ UNC. specialize (R1 NZ). rewrite LOZ, HIZ in R1. unfold bg_byte. cbn [twin_main rg_bg]. destruct (PAT o R1) as [P1 _]. exact P1.
Qed.
Lemma tail_region_ok : forall priv E m s2 n,
  PrimInt63.eqb s2 0%uint63 = false ->
  bv_unsigned (ev E s2) + 1 < two64 ->
  rb segs m (bv_unsigned (ev E s2)) = Some (Z_to_bv 8 (bv_unsigned (den E n) mod 8)) ->
  find_segment segs (bv_unsigned (ev E s2)) 1 = None ->
  region_ok segs priv E m s2 (tail_region n).
Proof.
  intros priv E m s2 n NZ HI64 BYTE SEG. destruct (tail_region_fields n) as (LO & HI & WR & BG & CELLS).
  assert (HIZ : hiZ E (tail_region n) = 1) by (unfold hiZ; rewrite HI; cbn [den]; rewrite wbv_unsigned; reflexivity).
  assert (LOZ : loZ (tail_region n) = 0) by (unfold loZ; rewrite LO; reflexivity).
  pose proof (bv_unsigned_in_range 64 (ev E s2)) as RSH.
  assert (G0 : keyZ (granule 0%uint63) = 0) by (vm_compute; reflexivity).
  assert (I0 : to_Z (gidx 0%uint63) = 0) by (vm_compute; reflexivity).
  constructor.
  - rewrite CELLS. apply IMap.bst_add. apply IMap.bst_empty.
  - intros _. rewrite LOZ, HIZ. lia.
  - intros _ a Ha. rewrite LOZ, HIZ in Ha. assert (a = bv_unsigned (ev E s2)) by lia. subst a.
    split; [rewrite BYTE; discriminate|]. split; [rewrite WR; discriminate| exact SEG].
  - intros g gr F. rewrite CELLS in F.
    destruct (Uint63.eqb (granule 0%uint63) g) eqn:Q; [| rewrite IMap.find_add_other_eqb in F by (apply IMap.bst_empty || exact Q); rewrite IMap.find_empty in F; discriminate].
    apply Uint63.eqb_correct in Q. subst g. rewrite IMap.find_add_same in F by apply IMap.bst_empty. injection F as <-. cbn [g_cells].
    split; [cbn; auto|]. constructor; [|constructor]. unfold cell_ok. cbn [c_idx c_w c_v]. change (to_Z 1%uint63) with 1.
    split; [lia|]. split; [lia|]. split; [lia|]. intros i Hi. assert (i = 0) by lia. subst i.
    replace (bv_unsigned (ev E s2) + 8 * keyZ (granule 0%uint63) + to_Z (gidx 0%uint63) + 0) with (bv_unsigned (ev E s2)) by lia.
    rewrite BYTE. do 2 f_equal. unfold byte_of. rewrite sz_and7_den. change (8 * 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - intros g gr c i F Hc Hi. cbv zeta. split; [| intros X; rewrite X in NZ; discriminate]. intros _. rewrite CELLS in F.
    destruct (Uint63.eqb (granule 0%uint63) g) eqn:Q; [| rewrite IMap.find_add_other_eqb in F by (apply IMap.bst_empty || exact Q); rewrite IMap.find_empty in F; discriminate].
    apply Uint63.eqb_correct in Q. subst g. rewrite IMap.find_add_same in F by apply IMap.bst_empty. injection F as <-. cbn [g_cells] in Hc.
    destruct Hc as [<-|[]]. cbn [c_idx c_w] in *. change (to_Z 1%uint63) with 1 in Hi. rewrite LOZ, HIZ. lia.
  - intros o R1 _ UNC. specialize (R1 NZ). rewrite LOZ, HIZ in R1. assert (o = 0) by lia. subst o. exfalso.
    destruct (UNC (granule 0%uint63) _ ltac:(lia) ltac:(rewrite CELLS; apply IMap.find_add_same; apply IMap.bst_empty)) as [_ FC].
    cbn [g_cells] in FC. apply Forall_inv in FC. apply FC. unfold covers. cbn [c_idx c_w]. change (to_Z 1%uint63) with 1. lia.
Qed.

Lemma twin_pair_sound : forall priv E m fs (R : IMap.t region) sh r n s2,
  facts_hold E fs -> (forall k rg, IMap.find k R = Some rg -> region_ok segs priv E m k rg) ->
  IMap.find sh R = Some r -> PrimInt63.eqb sh 0%uint63 = false ->
  is_twin_main r n = true -> tail_scan fs R sh n = Some s2 ->
  1 <= bv_unsigned (den E n) ->
  bv_unsigned (ev E sh) + (bv_unsigned (den E n) - 1) / 8 < 2 ^ 64 ->
  forall g, 0 <= g -> 8 * g < bv_unsigned (den E n) ->
    rb segs m (bv_unsigned (ev E sh) + g)
    = Some (Z_to_bv 8 (if 8 * g + 8 <=? bv_unsigned (den E n) then 0 else bv_unsigned (den E n) - 8 * g)).
Proof.
  intros priv E m fs R sh r n s2 HF ROK FR NZ TM TS N1 B g G0 G1. set (N := bv_unsigned (den E n)) in *.
  pose proof (ROK _ _ FR) as RO.
  destruct (region_is_inv _ _ TM) as (LO & HI & WR & BGE & _ & CE). cbn [twin_main rg_lo rg_hi rg_w rg_cells] in LO, HI, WR, CE.
  assert (HIZ : hiZ E r = (N - 1) / 8) by (unfold hiZ; rewrite HI; apply sz_last_den; exact N1).
  assert (LOZ : loZ r = 0) by (unfold loZ; rewrite LO; reflexivity).
  destruct (Z_lt_le_dec g ((N - 1) / 8)) as [BELOW|LAST].
  -
    assert (GIN : loZ r <= g < hiZ E r) by (rewrite LOZ, HIZ; lia).
    assert (UNC : uncovered r g).
    { intros gk gr _ F. rewrite <- (IMap.elements_spec gk gr _ (ro_bst _ _ _ _ _ _ RO)), CE in F. cbn in F. contradiction. }
    pose proof (ro_bg _ _ _ _ _ _ RO g (fun _ => GIN) ltac:(intros X; rewrite X in NZ; discriminate) UNC) as BGB.
    unfold bg_byte in BGB. rewrite BGE in BGB.
    replace (8 * g + 8 <=? N) with true by (symmetry; apply Z.leb_le; clear - BELOW; Z.div_mod_to_equations; lia). exact BGB.
  -
    destruct (tail_scan_inv _ _ _ _ _ TS) as (FT & S0 & SNE & r2 & F2 & TR).
    pose proof (find_tail_sound E fs sh n s2 HF FT) as EV. apply (f_equal bv_unsigned) in EV. rewrite (tail_rhs_den E sh n N1 B) in EV. fold N in EV.
    assert (GE : g = (N - 1) / 8) by (clear - G1 LAST G0; Z.div_mod_to_equations; lia).
    pose proof (tail_region_byte priv E m s2 r2 n (ROK _ _ F2) TR) as TB. fold N in TB. rewrite EV in TB. rewrite GE. rewrite TB.
    do 2 f_equal. destruct (Z.leb_spec (8 * ((N - 1) / 8) + 8) N) as [FL|PT]; [clear - N1 FL| clear - N1 PT]; Z.div_mod_to_equations; lia.
Qed.

Lemma fold_filter_inv : forall (P : int -> bool) (l : list (int * gran)) (acc : IMap.t gran), IMap.bst acc ->
  let acc' := List.fold_left (fun a kv => if P (fst kv) then a else IMap.add (fst kv) (snd kv) a) l acc in
  IMap.bst acc' /\ forall g gr, IMap.find g acc' = Some gr -> IMap.find g acc = Some gr \/ (In (g, gr) l /\ P g = false).
Proof.
  intros P l. induction l as [|[k x] l IH]; intros acc B; cbn [fold_left fst snd].
  - split; [exact B| intros g gr H; left; exact H].
  - destruct (P k) eqn:PK.
    + destruct (IH acc B) as [B' H']. split; [exact B'|]. intros g gr H. destruct (H' g gr H) as [X|[X Y]]; [left; exact X| right; split; [right; exact X| exact Y]].
    + destruct (IH (IMap.add k x acc) (IMap.bst_add k x acc B)) as [B' H']. split; [exact B'|]. intros g gr H.
      destruct (H' g gr H) as [X|[X Y]]; [| right; split; [right; exact X| exact Y]].
      destruct (Uint63.eqb k g) eqn:Q.
      * apply Uint63.eqb_correct in Q. subst g. rewrite IMap.find_add_same in X by exact B. injection X as <-. right. split; [left; reflexivity| exact PK].
      * rewrite IMap.find_add_other_eqb in X by (exact B || exact Q). left. exact X.
Qed.

Lemma region_forget_below_cells : forall r ksp, IMap.bst (rg_cells r) ->
  IMap.bst (rg_cells (region_forget_below r ksp))
  /\ forall g gr, IMap.find g (rg_cells (region_forget_below r ksp)) = Some gr ->
       IMap.find g (rg_cells r) = Some gr /\ kltb g (granule ksp) = false.
Proof.
  intros r ksp B. unfold region_forget_below. cbn [rg_cells]. rewrite IMap.fold_spec.
  destruct (fold_filter_inv (fun g => kltb g (granule ksp)) (IMap.elements (rg_cells r)) IMap.empty IMap.bst_empty) as [B' H'].
  split; [exact B'|]. intros g gr H. destruct (H' g gr H) as [X|[X Y]]; [rewrite IMap.find_empty in X; discriminate|].
  split; [apply (IMap.elements_spec g gr _ B); exact X| exact Y].
Qed.

Lemma key_range_half : forall i, - two63 / 2 <= keyZ i < two63 / 2.
Proof. intros i. pose proof (keyZ_range i). change (- two63 / 2) with (- (2 ^ 62)). rewrite half63. lia. Qed.

Lemma region_forget_below_ok : forall priv E m m' k r ksp,
  ev E 0%uint63 = Z_to_bv 64 0 ->
  region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false -> rg_bg r = BGNone ->
  keyZ ksp mod 16 = 0 ->
  let base := bv_unsigned (ev E k) in let sp := base + keyZ ksp in
  (forall a, sp <= a < base + hiZ E r -> rb segs m' a = rb segs m a /\ (wb segs m a = true -> wb segs m' a = true)) ->
  (forall a, base + loZ r <= a < sp -> rb segs m' a <> None /\ wb segs m' a = true) ->
  region_ok segs priv E m' k (region_forget_below r ksp).
Proof.
  intros priv E m m' k r ksp Hz RO KZ HBG K16. cbv zeta. intros AG BELOW.
  destruct (region_forget_below_cells r ksp (ro_bst _ _ _ _ _ _ RO)) as [B' CE].
  assert (RO' : region_ok segs priv E m k (region_forget_below r ksp)).
  { destruct RO as [Rbst Rrange Rvalid Rcells Rin Rbg]. constructor.
    - exact B'.
    - exact Rrange.
    - exact Rvalid.
    - intros g gr F. destruct (CE g gr F) as [F0 _]. exact (Rcells g gr F0).
    - intros g gr c i F. destruct (CE g gr F) as [F0 _]. exact (Rin g gr c i F0).
    - intros o _ _ _. unfold bg_byte. cbn [rg_bg region_forget_below]. rewrite HBG. exact I. }
  apply (region_ok_fine_frame segs priv E m m' k _ Hz RO').
  - intros o R1 _ CL. specialize (R1 KZ). change (loZ (region_forget_below r ksp)) with (loZ r) in R1. change (hiZ E (region_forget_below r ksp)) with (hiZ E r) in R1.
    destruct CL as [(g & gr & c & Hg & Hc & Eg & COV) | [U BG]].
    + destruct (CE g gr Hg) as [_ NLT].
      assert (LE : keyZ ksp <= o).
      { destruct (granule_gidx ksp (key_range_half _)) as [Gk Ik]. destruct (gidx_ok ksp) as [Gm _].
        assert (G0 : to_Z (gidx ksp) = 0).
        { rewrite Gm. destruct (keyZ_cases ksp) as [[_ EK]|[_ EK]]; rewrite EK in K16.
          - apply Z.mod_divide in K16; [|lia]. apply Z.mod_divide; [lia|]. destruct K16 as [q Qq]. exists (2 * q). lia.
          - replace (to_Z ksp - 2 ^ 63) with (to_Z ksp + (- 2 ^ 59) * 16) in K16 by lia. rewrite Z.mod_add in K16 by lia.
            apply Z.mod_divide in K16; [|lia]. apply Z.mod_divide; [lia|]. destruct K16 as [q Qq]. exists (2 * q). lia. }
        rewrite kltb_keyZ in NLT. apply Z.ltb_ge in NLT.
        pose proof (Z.div_mod o 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound o 8 ltac:(lia)) as MB. lia. }
      exact (proj1 (AG (bv_unsigned (ev E k) + o) ltac:(lia))).
    + exfalso. apply BG. unfold bg_byte. cbn [rg_bg region_forget_below]. rewrite HBG. reflexivity.
  - intros _ a Ha. change (loZ (region_forget_below r ksp)) with (loZ r) in Ha. change (hiZ E (region_forget_below r ksp)) with (hiZ E r) in Ha.
    destruct (Z_lt_le_dec a (bv_unsigned (ev E k) + keyZ ksp)) as [LT|GE].
    + destruct (BELOW a ltac:(lia)) as [V1 V2]. split; [exact V1|]. intros _. exact V2.
    + destruct (ro_valid _ _ _ _ _ _ RO KZ a Ha) as (V1 & V2 & _).
      destruct (AG a ltac:(lia)) as [E2 W2].
      split; [rewrite E2; exact V1|]. intros Wr. apply W2. apply V2. exact Wr.
Qed.

Lemma sec_decided_sound : forall E fs n, facts_hold E fs -> sec_decided fs n = true -> 64512 < bv_unsigned (den E n).
Proof.
  intros E fs n HF H. unfold sec_decided in H. pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF H) as LT.
  replace (bv_unsigned (den E (VL PRIM_MAXw))) with 64512 in LT by (vm_compute; reflexivity). exact LT.
Qed.
Lemma win_not_prist_sound : forall E fs l sz kd, facts_hold E fs -> win_not_prist fs l sz kd = true ->
  HeapOp.Win (bv_unsigned (den E l)) (bv_unsigned (den E sz)) (bv_unsigned (den E kd)) <> HeapOp.Win (2^47 + 2^46) 0 HeapOp.K_STACK.
Proof.
  intros E fs l sz kd HF H X. injection X as X1 X2 X3. unfold win_not_prist in H.
  destruct kd as [k0| | | | | | | | | |]; try discriminate H.
  rewrite unsigned_VL in X3. change HeapOp.K_STACK with (w2Z wzero) in X3.
  assert (KW : weqb k0 wzero = true) by (rewrite weqb_eqb; apply Z.eqb_eq; exact X3). rewrite KW in H.
  destruct sz as [z| | | | | | | | | |]; try discriminate H.
  rewrite unsigned_VL in X2. change 0 with (w2Z wzero) in X2.
  assert (ZW : weqb z wzero = true) by (rewrite weqb_eqb; apply Z.eqb_eq; exact X2). rewrite ZW in H.
  assert (SYM : KnownT.KnownT.known_ltu_t fs l (VL PRIST_BASEw) || KnownT.KnownT.known_ltu_t fs (VL PRIST_BASEw) l = true -> False).
  { intros O. apply orb_prop in O as [O|O]; pose proof (KnownA.KnownA.known_ltu_sound E fs _ _ HF O) as Q; rewrite unsigned_VL in Q;
      change (w2Z PRIST_BASEw) with (2^47 + 2^46) in Q; lia. }
  destruct l as [a| | | | | | | | | |]; try exact (SYM H).
  rewrite unsigned_VL in X1. apply negb_true_iff in H. rewrite weqb_eqb in H. apply Z.eqb_neq in H. apply H.
  change (w2Z PRIST_BASEw) with (2^47 + 2^46). exact X1.
Qed.
Lemma wins_not_prist_sound : forall E fs, facts_hold E fs -> forall n ws, wins_not_prist fs n ws = true ->
  ~ In (HeapOp.Win (2^47 + 2^46) 0 HeapOp.K_STACK) (wins_of E n ws).
Proof.
  intros E fs HF n. induction n as [|n IH]; intros ws H Hw; [destruct ws; cbn in Hw; contradiction|].
  destruct ws as [|wlo [|ln [|kdv ws0]]]; try (cbn in H; discriminate). cbn [wins_not_prist] in H. apply andb_prop in H as [H1 H2].
  rewrite wins_of_cons in Hw. destruct Hw as [Hw|Hw]; [| exact (IH ws0 H2 Hw)].
  exact (win_not_prist_sound E fs wlo ln kdv HF H1 Hw).
Qed.

End CallA.

Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.
Import GlueA.TwinB Actr.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP CtrLib CtrFX ActrA.
Open Scope Z_scope.
Unset Lia Cache.

Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.

Unset Nia Cache. Unset Nra Cache.
Module AMem := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.

Section CallA.
Variable segs : list Segment.
Variable OPS : optable.

Lemma stack_sound_g : forall E st ms mo need,
  st_ok segs OPS E st ms mo -> to_Z need < 2 ^ 32 -> stack_room_g st need = true ->
  exists k off r ksp, getr st X2 = VP k off /\ IMap.find k (s_regs st) = Some r /\ PrimInt63.eqb k 0%uint63 = false
    /\ okey off = Some ksp /\ keyZ ksp mod 16 = 0
    /\ bv_unsigned (ev E k) mod 16 = 0
    /\ bv_unsigned (den E (getr st X2)) = bv_unsigned (ev E k) + keyZ ksp
    /\ 0 <= bv_unsigned (ev E k) + keyZ ksp - to_Z need
    /\ bv_unsigned (ev E k) + keyZ ksp < 2 ^ 64
    /\ AF.stk segs (ms_mem ms) (bv_unsigned (ev E k) + loZ r) (bv_unsigned (ev E k) + keyZ ksp)
    /\ sp_region st = Some (k, off, r) /\ loZ r <= keyZ ksp - to_Z need /\ 0 <= bv_unsigned (ev E k) + loZ r.
Proof.
  intros E st ms mo need HS Hneed H. unfold stack_room_g, sp_region in H.
  destruct (getr st X2) as [|k off| | | | | | | | |] eqn:HX2; try discriminate.
  destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate].
  match type of H with match (if ?c then _ else _) with _ => _ end = _ => destruct c eqn:CK; [|discriminate] end.
  do 4 (apply andb_prop in CK as [CK ?]). rename H0 into BGN, H1 into ALN, H2 into AL16, H3 into HW. apply negb_true_iff in CK.
  destruct (okey (wsub off (wlit need))) as [klo|] eqn:Hklo; [|discriminate].
  destruct (okey off) as [ksp|] eqn:Hksp; [|discriminate].
  destruct (rg_hi r) as [h| | | | | | | | | |] eqn:Hhi; try discriminate.
  destruct (okey h) as [kh|] eqn:Hkh; [|discriminate].
  do 2 (apply andb_prop in H as [H ?]). rename H into L1, H0 into L2, H1 into L3.
  rewrite kleb_keyZ in L1, L2, L3. apply Z.leb_le in L1. apply Z.leb_le in L2. apply Z.leb_le in L3.
  destruct (okey_sound _ _ Hksp) as [Eksp Rksp]. destruct (okey_sound _ _ Hklo) as [Eklo Rklo]. destruct (okey_sound _ _ Hkh) as [Ekh Rkh].
  rewrite !half63 in Rksp, Rklo, Rkh.
  assert (Eneed : w2Zs (wlit need) = to_Z need) by (rewrite w2Zs_eq, wlit_ok; cbn [wt wlit]; lia).
  pose proof (int_range need) as Rn. rewrite two63_eq in Rn.
  assert (Eklo' : keyZ klo = keyZ ksp - to_Z need).
  { rewrite Eklo, (GlueA.TwinB.w2Zs_wsub_small); [rewrite Eneed, Eksp; reflexivity|]. rewrite Eneed, <- Eksp. unfold two63 in *. lia. }
  pose proof (so_reg _ _ _ _ _ _ HS _ _ Hr) as RO.
  pose proof (ro_range _ _ _ _ _ _ RO CK) as [RLO RHI]. unfold two64 in RHI.
  assert (Ehi : keyZ kh <= hiZ E r).
  { unfold hiZ. rewrite Hhi, unsigned_VL, Ekh, w2Zs_eq. unfold two64. destruct (wt h); lia. }
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  assert (A16 : bv_unsigned (ev E k) mod 16 = 0).
  { pose proof (find_align_le E (s_facts st) HF k 4%uint63 ALN) as X. change (2 ^ to_Z 4%uint63) with 16 in X. exact X. }
  assert (K16 : keyZ ksp mod 16 = 0).
  { apply Uint63.eqb_correct in AL16.
    assert (WL : wl off = ksp). { unfold okey in Hksp. destruct (wt off); [destruct (PrimInt63.leb bit62i (wl off))| destruct (PrimInt63.ltb (wl off) bit62i)]; congruence. }
    rewrite WL in AL16.
    pose proof (land_mk ksp 4%uint63 ltac:(change (to_Z 4%uint63) with 4; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 4) 1)%uint63 with 15%uint63 in LM. rewrite AL16 in LM.
    change (to_Z 0%uint63) with 0 in LM. change (2 ^ to_Z 4%uint63) with 16 in LM.
    destruct (keyZ_cases ksp) as [[_ ->]|[_ ->]]; [lia|].
    replace (to_Z ksp - 2 ^ 63) with (to_Z ksp + (- 2 ^ 59) * 16) by lia. rewrite Z.mod_add by lia. lia. }
  assert (Esp : bv_unsigned (den E (VP k off)) = bv_unsigned (ev E k) + keyZ ksp).
  { rewrite den_VP, <- Eksp. unfold loZ in *. apply Z.mod_small. unfold two64. lia. }
  exists k, off, r, ksp. split; [reflexivity|]. split; [exact Hr|]. split; [exact CK|]. split; [exact Hksp|]. split; [exact K16|].
  split; [exact A16|]. split; [exact Esp|]. unfold loZ in *. split; [lia|]. split; [lia|].
  split.
  { unfold AF.stk. split; [lia|]. split; [lia|]. intros a Ha.
    destruct (ro_valid _ _ _ _ _ _ RO CK a ltac:(unfold loZ; lia)) as (V1 & V2 & _).
    split; [apply (GlueA.TwinB.wb_wviewA segs); apply V2; exact HW|]. rewrite (GlueA.TwinB.rb_mrdA segs) in V1.
    destruct (AMem.mrd segs (ms_mem ms) (AMem.wa a)); [eexists; reflexivity| congruence]. }
  split; [| split; [lia| lia]].
  unfold sp_region. rewrite HX2, Hr. rewrite CK. cbn [negb andb]. rewrite HW, AL16, ALN, BGN. reflexivity.
Qed.

Lemma sp_region_inv : forall st k off r, sp_region st = Some (k, off, r) ->
  getr st X2 = VP k off /\ IMap.find k (s_regs st) = Some r /\ PrimInt63.eqb k 0%uint63 = false /\ rg_w r = true /\ rg_bg r = BGNone.
Proof.
  intros st k off r H. unfold sp_region in H.
  destruct (getr st X2) as [|k0 off0| | | | | | | | |]; try discriminate. destruct (IMap.find k0 (s_regs st)) as [r0|] eqn:F; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end. injection H as -> -> ->.
  do 4 (apply andb_prop in CK as [CK ?]). apply negb_true_iff in CK.
  repeat (split; [reflexivity || assumption|]). destruct (rg_bg r); try discriminate. reflexivity.
Qed.

Lemma reg_of_X8 : reg_of_r5 X8 = 8%bv. Proof. apply bv_eq. reflexivity. Qed.

Lemma amalloc_regs : forall E st ms mo r tp cred,
  st_ok segs OPS E st ms mo ->
  call_pre st = Some r -> getr st X4 = VL tp -> weqb tp (wlit ATPi) = true ->
  KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) (getr st X10) = true -> KnownT.KnownT.known_leu_t (s_facts st) (getr st X10) (VL AREQMAXw) = true ->
  cred_pre (s_facts st) (getr st X10) cred = true ->
  let R := ms_regs ms in
  s_resv st = RNone
  /\ AP.getr R 1 = Z_to_bv 64 (to_Z r) /\ 0 <= to_Z r < 2 ^ 62
  /\ AP.getr R 4 = Z_to_bv 64 (to_Z ATPi)
  /\ 0 < bv_unsigned (AP.getr R 10) <= 0xFFF00000
  /\ (1048576 <= bv_unsigned (den E cred)
      /\ (prim_decided (s_facts st) (getr st X10) = true \/ bv_unsigned (AP.getr R 10) <= bv_unsigned (den E cred))).
Proof.
  intros E st ms mo r tp cred HS CP TP TPE N0 N1 NC R.
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  pose proof (getr_RA segs OPS E st ms mo HS) as GR.
  destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (_ & (ra & Hra & WT & LT & ->)).
  split; [exact (HeapCtr.TwinB.call_pre_resv st _ CP)|].
  assert (ERA : ra = wlit (wl ra)) by (destruct ra as [t l]; cbn in WT |- *; subst t; reflexivity).
  split. { subst R. rewrite <- HeapCtr.TwinB.reg_of_X1, (GR X1), Hra, ERA, HeapCtr.TwinB.den_wlit. reflexivity. }
  split. { apply Uint63.ltb_spec in LT. rewrite to_Z_bit62i in LT. pose proof (int_range (wl ra)) as RR. split; [apply RR| exact LT]. }
  split. { subst R. rewrite <- HeapCtr.TwinB.reg_of_X4, (GR X4), TP. apply (proj1 (weqb_ok _ _)) in TPE. subst tp. rewrite HeapCtr.TwinB.den_wlit. reflexivity. }
  pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF N0) as L0. pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF N1) as L1.
  unfold cred_pre in NC. apply andb_prop in NC as [NCX NC].
  pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF NCX) as LX. replace (bv_unsigned (den E (VL C_EXHw))) with 1048576 in LX by (vm_compute; reflexivity).
  cbn [den] in L0, L1. rewrite wbv_unsigned in L0, L1. rewrite wzero_ok in L0.
  subst R. rewrite <- HeapCtr.TwinB.reg_of_X10, (GR X10).
  split. { split; [exact L0|]. replace 0xFFF00000 with (w2Z AREQMAXw) by (vm_compute; reflexivity). exact L1. }
  split; [exact LX|]. apply orb_prop in NC as [NC|NC]; [left; exact NC| right; exact (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF NC)].
Qed.

Lemma acall_regs : forall E st ms mo r tp,
  st_ok segs OPS E st ms mo -> call_pre st = Some r -> getr st X4 = VL tp -> weqb tp (wlit ATPi) = true ->
  let R := ms_regs ms in
  s_resv st = RNone /\ AP.getr R 1 = Z_to_bv 64 (to_Z r) /\ 0 <= to_Z r < 2 ^ 62 /\ AP.getr R 4 = Z_to_bv 64 (to_Z ATPi).
Proof.
  intros E st ms mo r tp HS CP TP TPE R.
  pose proof (getr_RA segs OPS E st ms mo HS) as GR.
  destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (_ & (ra & Hra & WT & LT & ->)).
  split; [exact (HeapCtr.TwinB.call_pre_resv st _ CP)|].
  assert (ERA : ra = wlit (wl ra)) by (destruct ra as [t l]; cbn in WT |- *; subst t; reflexivity).
  split. { subst R. rewrite <- HeapCtr.TwinB.reg_of_X1, (GR X1), Hra, ERA, HeapCtr.TwinB.den_wlit. reflexivity. }
  split. { apply Uint63.ltb_spec in LT. rewrite to_Z_bit62i in LT. pose proof (int_range (wl ra)) as RR. split; [apply RR| exact LT]. }
  subst R. rewrite <- HeapCtr.TwinB.reg_of_X4, (GR X4), TP. apply (proj1 (weqb_ok _ _)) in TPE. subst tp. rewrite HeapCtr.TwinB.den_wlit. reflexivity.
Qed.
Lemma unw_stop_sound : forall E st ms mo, st_ok segs OPS E st ms mo -> unw_stop st = true ->
  bv_unsigned (AP.getr (ms_regs ms) 8) <= bv_unsigned (AP.getr (ms_regs ms) 2).
Proof.
  intros E st ms mo HS UNW. pose proof (so_facts _ _ _ _ _ _ HS) as HF. pose proof (getr_RA segs OPS E st ms mo HS) as GR.
  unfold unw_stop in UNW. pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF UNW) as L3.
  rewrite <- reg_of_X8, <- HeapCtr.TwinB.reg_of_X2, (GR X8), (GR X2). exact L3.
Qed.

Lemma block_of_twin_sound : forall E fs sh k, facts_hold E fs -> block_of_twin fs sh = Some k ->
  bv_unsigned (ev E sh) = (bv_unsigned (ev E k) / 8 + 0x7fff8000) mod 2 ^ 64.
Proof.
  intros E fs sh k HF. unfold block_of_twin. induction fs as [|f fs IH]; intros H; [discriminate|].
  inversion HF as [|f' l Hf HF']; subst.
  assert (STEP : (fix go (l : list fact) : option int :=
                    match l with
                    | FEq (VP sh' o) (VAlu ALU_ADD (VAlu ALU_SRL (VP k o') (VL c3)) (VL sb)) :: l' =>
                        if PrimInt63.eqb sh sh' && weqb o wzero && weqb o' wzero && weqb c3 (wlit 3%uint63) && weqb sb SBw then Some k else go l'
                    | _ :: l' => go l'
                    | [] => None
                    end) fs = Some k -> bv_unsigned (ev E sh) = (bv_unsigned (ev E k) / 8 + 0x7fff8000) mod 2 ^ 64) by exact (IH HF').
  destruct f as [| | | |x y| | |]; try (apply STEP; exact H).
  destruct x as [|sh0 z| | | | | | | | |]; try (apply STEP; exact H).
  destruct y as [| |op y1 y2| | | | | | | |]; try (apply STEP; exact H). destruct op; try (apply STEP; exact H).
  destruct y1 as [| |op1 u1 u2| | | | | | | |]; try (apply STEP; exact H). destruct op1; try (apply STEP; exact H).
  destruct u1 as [|k' z'| | | | | | | | |]; try (apply STEP; exact H). destruct u2 as [c| | | | | | | | | |]; try (apply STEP; exact H).
  destruct y2 as [s'| | | | | | | | | |]; try (apply STEP; exact H).
  destruct (PrimInt63.eqb sh sh0 && weqb z wzero && weqb z' wzero && weqb c (wlit 3%uint63) && weqb s' SBw) eqn:C; [|apply STEP; exact H].
  injection H as ->. apply andb_prop in C as [C S']. apply andb_prop in C as [C C3]. apply andb_prop in C as [C Z']. apply andb_prop in C as [K' Z0].
  apply weqb_eq in Z0. apply weqb_eq in Z'. apply weqb_eq in S'. apply weqb_eq in C3. apply Uint63.eqb_correct in K'. subst z z' s' c sh0.
  cbn [fact_holds] in Hf. rewrite HeapCtr.TwinB.den_VPz in Hf. rewrite Hf.
  change (den E (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw)))
    with (alu64 ALU_ADD (alu64 ALU_SRL (den E (VP k wzero)) (wbv (wlit 3%uint63))) (wbv SBw)).
  rewrite HeapCtr.TwinB.den_VPz.
  unfold alu64, alu. rewrite bv_add_unsigned, bv_shiftr_unsigned, bv_and_unsigned.
  replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
  replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  replace (bv_unsigned (wbv SBw)) with 0x7fff8000 by (vm_compute; reflexivity).
  unfold bv_wrap, bv_modulus. reflexivity.
Qed.

Lemma twin_arm_old_inv : forall fs R wl0 sh len, twin_arm_old fs R wl0 sh len = true ->
  exists k r n, block_of_twin fs sh = Some k /\ IMap.find sh R = Some r /\ CtrA.win_lookup wl0 k = Some (n, CtrLib.K_BLOCK)
    /\ len_is_twin fs len n = true /\ (prim_decided fs n = true \/ (is_twin_region r n = true /\ size_shape_ok fs n = true)
                             \/ (is_twin_main r n = true /\ exists s2, tail_scan fs R sh n = Some s2)).
Proof.
  intros fs R wl0 sh len H1. unfold twin_arm_old in H1.
  destruct (block_of_twin fs sh) as [k|] eqn:BT; [|discriminate]. destruct (IMap.find sh R) as [r|] eqn:FR; [|discriminate].
  destruct (CtrA.win_lookup wl0 k) as [[n kdb]|] eqn:WL; [|discriminate].
  apply andb_prop in H1 as [H1 ALT]. apply andb_prop in H1 as [KB LEN]. apply weqb_eq in KB. subst kdb.
  exists k, r, n. repeat (split; [reflexivity || assumption|]).

  apply orb_prop in ALT as [ALT|PD]; [| left; exact PD].
  apply orb_prop in ALT as [CAN|PAIR]; [right; left; apply andb_prop in CAN; exact CAN|].
  right. right. apply andb_prop in PAIR as [TM TS]. split; [exact TM|]. destruct (tail_scan fs R sh n) as [s2|]; [exists s2; reflexivity| discriminate TS].
Qed.

Lemma twin_arm_ev_inv : forall fs R wl0 cv sh len kx, twin_arm_ev fs R wl0 cv sh len kx = true ->
  exists lw kb,
    len = VL lw /\ block_of_twin fs sh = Some kb /\ wt lw = false /\ to_Z (wl lw) <= 8064 /\ PrimInt63.leb 3%uint63 (find_align fs kb) = true
    /\ (In kb cv
        \/ exists ks lens kd r o2 o1,
             In (ks, lens, kd) wl0 /\ ks <> kx /\ kd <> CtrLib.K_BLOCK /\ weqb kd K_TWIN = false
             /\ IMap.find ks R = Some r /\ rg_w r = true /\ rg_lo r = 0%uint63 /\ KnownT.KnownT.known_ltu_t fs (VL wzero) (rg_hi r) = true
             /\ GTwinSub.GTwinSub.find_lb fs ks kb = Some o2 /\ find_ub_g fs ks = Some (kb, o1) /\ wt o2 = false /\ wt o1 = false
             /\ nowrap_kb fs kb o2 = true /\ to_Z (wl o1) + 8 <= 8 * to_Z (wl lw)).
Proof.
  intros fs R wl0 cv sh len kx H. unfold twin_arm_ev in H. destruct len as [lw| | | | | | | | | |]; try discriminate H.
  destruct (block_of_twin fs sh) as [kb|] eqn:BT; [|discriminate H].
  apply andb_prop in H as [H EX]. apply andb_prop in H as [H AL]. apply andb_prop in H as [WT LE].
  apply negb_true_iff in WT. apply Uint63.leb_spec in LE. change (to_Z 8064%uint63) with 8064 in LE.
  exists lw, kb. repeat (split; [reflexivity || assumption|]).
  apply orb_prop in EX as [CV|EX].
  { left. apply existsb_exists in CV as (x & Hx & Q). apply Uint63.eqb_correct in Q. subst x. exact Hx. }
  right.
  apply existsb_exists in EX as ([[ks lens] kd] & Hin & EV). unfold own_ev1 in EV.
  apply andb_prop in EV as [EV M]. apply andb_prop in EV as [EV NT]. apply andb_prop in EV as [NX NB].
  apply negb_true_iff in NX. apply Uint63.eqb_false_spec in NX. apply negb_true_iff in NT.
  assert (NKB : kd <> CtrLib.K_BLOCK). { intros ->. apply negb_true_iff in NB. rewrite weqb_refl in NB. discriminate NB. }
  destruct (IMap.find ks R) as [r|] eqn:FR; [|discriminate M].
  apply andb_prop in M as [M F]. apply andb_prop in M as [M POS]. apply andb_prop in M as [RW L0]. apply Uint63.eqb_correct in L0.
  destruct (GTwinSub.GTwinSub.find_lb fs ks kb) as [o2|] eqn:LB; [|discriminate F]. destruct (find_ub_g fs ks) as [[kb' o1]|] eqn:UB; [|discriminate F].
  apply andb_prop in F as [F LE8]. apply andb_prop in F as [F O1S]. apply andb_prop in F as [F NW]. apply andb_prop in F as [F WT1]. apply andb_prop in F as [EKB WT2].
  apply Uint63.eqb_correct in EKB. subst kb'. apply negb_true_iff in WT1. apply negb_true_iff in WT2.
  apply Uint63.leb_spec in LE8. apply Uint63.leb_spec in O1S. change (to_Z 64512%uint63) with 64512 in O1S.
  rewrite Uint63.add_spec, lsl_spec in LE8. change (to_Z 8%uint63) with 8 in LE8. change (to_Z 3%uint63) with 3 in LE8. change (2 ^ 3) with 8 in LE8.
  pose proof (int_range (wl o1)) as R1. pose proof (int_range (wl lw)) as R2. change wB with (2 ^ 63) in *.
  rewrite !Z.mod_small in LE8 by lia.
  exists ks, lens, kd, r, o2, o1. repeat (split; [reflexivity || assumption|]). lia.
Qed.

Lemma carg_vecs_spec : forall st md A nw rest kb, find_op HEAP_ID (s_ops st) = Some (VL md :: A :: VL nw :: rest) -> In kb (carg_vecs st) ->
  exists i, In i (VECS (w2Z md)) /\ nth_error (skipn (3 * Z.to_nat (to_Z (wl nw))) rest) i = Some (VP kb wzero).
Proof.
  intros st md A nw rest kb Hf H. unfold carg_vecs in H. rewrite Hf in H. apply in_flat_map in H as (i & Hi & Hk). exists i. split; [exact Hi|].
  unfold carg_anchor in Hk. destruct (nth_error (skipn (3 * Z.to_nat (to_Z (wl nw))) rest) i) as [v|]; [| destruct Hk].
  destruct v as [|k o| | | | | | | | |]; try (destruct Hk). destruct (weqb o wzero) eqn:Q; [| destruct Hk]. apply weqb_eq in Q. subst o.
  destruct Hk as [->|[]]. reflexivity.
Qed.
Lemma twin_lit_inv : forall len, twin_lit len = true -> exists lw, len = VL lw /\ wt lw = false /\ to_Z (wl lw) <= 8064.
Proof.
  intros len H. unfold twin_lit in H. destruct len as [lw| | | | | | | | | |]; try discriminate H. apply andb_prop in H as [WT LE].
  apply negb_true_iff in WT. apply Uint63.leb_spec in LE. change (to_Z 8064%uint63) with 8064 in LE. exists lw. auto.
Qed.

Lemma srl3_den_raw : forall E xs, bv_unsigned (den E (VAlu ALU_SRL xs (VL (wlit 3%uint63)))) = bv_unsigned (den E xs) / 8.
Proof.
  intros E xs. cbn [den]. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned.
  replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
  replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma and7_den_raw : forall E xs, bv_unsigned (den E (VAlu ALU_AND xs (VL (wlit 7%uint63)))) = bv_unsigned (den E xs) mod 8.
Proof.
  intros E xs. cbn [den]. unfold alu64, alu. rewrite bv_and_unsigned, wbv_unsigned, wlit_ok.
  change (to_Z 7%uint63) with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma tie_of_holds : forall E fs len xs, facts_hold E fs -> tie_of fs len = Some xs -> bv_unsigned (den E len) = bv_unsigned (den E xs) / 8.
Proof.
  intros E fs len xs HF. induction fs as [|f fs IH]; intros H; [discriminate H|].
  pose proof (Forall_inv HF) as Hf. pose proof (Forall_inv_tail HF) as HF'.
  assert (STEP : tie_of fs len = Some xs -> bv_unsigned (den E len) = bv_unsigned (den E xs) / 8) by (intros X; exact (IH HF' X)).
  cbn [tie_of] in H. destruct f as [| | | |a b| | |]; try (apply STEP; exact H).
  destruct b as [| |op u1 u2| | | | | | | |]; try (apply STEP; exact H). destruct op; try (apply STEP; exact H).
  destruct u2 as [c3| | | | | | | | | |]; try (apply STEP; exact H).
  destruct (sv_eqb a len && weqb c3 (wlit 3%uint63)) eqn:C; [| apply STEP; exact H].
  injection H as ->. apply andb_prop in C as [C1 C3]. apply ValP.sv_eqb_eq in C1. apply weqb_eq in C3. subst a c3.
  cbn [fact_holds] in Hf. rewrite Hf. exact (srl3_den_raw E xs).
Qed.
Lemma find_ub_sym_holds : forall E fs ks oU kb xs, facts_hold E fs -> find_ub_sym fs ks = Some (oU, kb, xs) ->
  wt oU = false /\ bv_unsigned (den E (VP ks oU)) <= bv_unsigned (den E (VAlu ALU_ADD (VP kb wzero) xs)).
Proof.
  intros E fs ks oU kb xs HF. induction fs as [|f fs IH]; intros H; [discriminate H|].
  pose proof (Forall_inv HF) as Hf. pose proof (Forall_inv_tail HF) as HF'.
  assert (STEP : find_ub_sym fs ks = Some (oU, kb, xs) -> wt oU = false /\ bv_unsigned (den E (VP ks oU)) <= bv_unsigned (den E (VAlu ALU_ADD (VP kb wzero) xs)))
    by (intros X; exact (IH HF' X)).
  cbn [find_ub_sym] in H. destruct f as [| | |a b| | | |]; try (apply STEP; exact H).
  destruct a as [|k o| | | | | | | | |]; try (apply STEP; exact H).
  destruct b as [| |op u1 u2| | | | | | | |]; try (apply STEP; exact H). destruct op; try (apply STEP; exact H).
  destruct u1 as [|kb' z| | | | | | | | |]; try (apply STEP; exact H).
  destruct (PrimInt63.eqb k ks && weqb z wzero && negb (wt o)) eqn:C; [| apply STEP; exact H].
  injection H as -> -> ->. apply andb_prop in C as [C WT]. apply andb_prop in C as [K Z0]. apply Uint63.eqb_correct in K. apply weqb_eq in Z0. subst k z.
  apply negb_true_iff in WT. split; [exact WT|]. exact Hf.
Qed.
Lemma twin_small_sound : forall E fs len, facts_hold E fs -> twin_small fs len = true -> bv_unsigned (den E len) <= 8064.
Proof.
  intros E fs len HF H. unfold twin_small in H. apply orb_prop in H as [H|H].
  - destruct (twin_lit_inv _ H) as (lw & -> & WT & LW). cbn [den]. rewrite wbv_unsigned. unfold w2Z. rewrite WT. exact LW.
  - pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF H) as LE. replace (bv_unsigned (den E (VL (wlit 8064%uint63)))) with 8064 in LE by (vm_compute; reflexivity). exact LE.
Qed.
Lemma twins_scan_sound : forall fs R wl0 wl sh len kd, twins_scan fs R wl0 wl = true -> In (sh, len, kd) wl -> weqb kd K_TWIN = true ->
  twin_arm_old fs R wl0 sh len = true \/ twin_small fs len = true.
Proof.
  intros fs R wl0 wl. induction wl as [|[[sh0 len0] kd0] wl IH]; intros sh len kd H Hin KD; [destruct Hin|].
  cbn [twins_scan] in H. apply andb_prop in H as [H1 H2].
  destruct Hin as [Hin|Hin]; [| exact (IH sh len kd H2 Hin KD)].
  injection Hin as -> -> ->. rewrite KD in H1. apply orb_prop in H1. destruct H1 as [X|X]; [| right; exact X].
  apply orb_prop in X. destruct X as [X|X]; [right; unfold twin_small; rewrite X; reflexivity| left; exact X].
Qed.
Lemma twins_apart_inv : forall fs R wl cv kf sh k len kd, twins_apart fs R wl cv kf sh = true -> In (k, len, kd) wl -> weqb kd K_TWIN = true -> k <> sh ->
  twin_arm_old fs R wl k len = true \/ twin_arm_evx fs R wl cv k len kf = true.
Proof.
  intros fs R wl cv kf sh k len kd H Hin KD NS. unfold twins_apart in H. pose proof (proj1 (forallb_forall _ _) H _ Hin) as C. cbv beta iota in C.
  rewrite KD in C. cbn [negb orb] in C. replace (PrimInt63.eqb k sh) with false in C by (symmetry; apply Uint63.eqb_false_spec; exact NS).
  cbn [orb] in C. apply orb_prop in C. exact C.
Qed.

Lemma twin_canon_inv : forall st wl kf sh, twin_canon st wl kf sh = true ->
  exists r n kdn lent kdt, IMap.find sh (s_regs st) = Some r /\ CtrA.win_lookup wl kf = Some (n, kdn) /\ CtrA.win_lookup wl sh = Some (lent, kdt)
    /\ is_twin_region r n = true /\ size_shape_ok (s_facts st) n = true /\ len_is_twin (s_facts st) lent n = true
    /\ twins_apart (s_facts st) (s_regs st) wl (carg_vecs st) kf sh = true
    /\ no_tail_at (s_facts st) (s_regs st) sh n = true.
Proof.
  intros st wl kf sh H. unfold twin_canon in H. destruct (IMap.find sh (s_regs st)) as [r|]; [|discriminate].
  destruct (CtrA.win_lookup wl kf) as [[n kdn]|]; [|discriminate]. destruct (CtrA.win_lookup wl sh) as [[lent kdt]|]; [|discriminate].
  apply andb_prop in H as [H NT]. apply andb_prop in H as [H TA]. apply andb_prop in H as [H LEN]. apply andb_prop in H as [TR SS].
  exists r, n, kdn, lent, kdt. repeat (split; [reflexivity || assumption|]). exact NT.
Qed.

Lemma prim_decided_sound : forall E fs n, facts_hold E fs -> prim_decided fs n = true -> bv_unsigned (den E n) <= 64512.
Proof.
  intros E fs n HF H. unfold prim_decided in H. pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF H) as LE.
  replace (bv_unsigned (den E (VL PRIM_MAXw))) with 64512 in LE by (vm_compute; reflexivity). exact LE.
Qed.

Lemma sz_and7_den : forall E n, bv_unsigned (den E (sz_and7 n)) = bv_unsigned (den E n) mod 8.
Proof.
  intros E n. unfold sz_and7. rewrite ValP.den_sv_alu. cbn [den]. unfold alu64, alu. rewrite bv_and_unsigned, wbv_unsigned, wlit_ok.
  change (to_Z 7%uint63) with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma sz_last_den : forall E n, 1 <= bv_unsigned (den E n) -> bv_unsigned (den E (sz_last n)) = (bv_unsigned (den E n) - 1) / 8.
Proof.
  intros E n N1. unfold sz_last. rewrite !ValP.den_sv_alu. cbn [den]. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned.
  replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
  replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite bv_add_unsigned. replace (bv_unsigned (wbv wones)) with (2 ^ 64 - 1) by (vm_compute; reflexivity).
  pose proof (bv_unsigned_in_range 64 (den E n)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (bv_unsigned (den E n) + (2 ^ 64 - 1)) with (bv_unsigned (den E n) - 1 + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma twin_len_den : forall E n, bv_unsigned (den E n) + 7 < 2 ^ 62 ->
  bv_unsigned (den E (twin_len n)) = (bv_unsigned (den E n) + 7) / 8.
Proof.
  intros E n B.
  assert (GEN : bv_unsigned (den E (sv_alu ALU_SRL (sv_alu ALU_ADD n (VL (wlit 7%uint63))) (VL (wlit 3%uint63)))) = (bv_unsigned (den E n) + 7) / 8).
  { rewrite !ValP.den_sv_alu. cbn [den]. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned, bv_add_unsigned.
    replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
    replace (bv_unsigned (wbv (wlit 7%uint63))) with 7 by (vm_compute; reflexivity).
    replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
    change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold bv_wrap, bv_modulus. pose proof (bv_unsigned_in_range 64 (den E n)) as R. rewrite Z.mod_small by (change (2 ^ Z.of_N 64) with (2^64); lia).
    reflexivity. }
  destruct n as [w| | | | | | | | | |]; try exact GEN.
  cbn [twin_len]. rewrite !unsigned_VL in *. rewrite wlit_ok.
  assert (WT : wt w = false). { rewrite w2Z_wt. apply Z.leb_gt. unfold two63. lia. }
  rewrite (w2Z_nowt w WT) in *. rewrite lsr_spec, Uint63.add_spec. change (to_Z 3%uint63) with 3. change (to_Z 7%uint63) with 7. change (2 ^ 3) with 8.
  rewrite Z.mod_small; [reflexivity|]. pose proof (int_range (wl w)). change wB with (2 ^ 63). lia.
Qed.

Lemma al8_spec : forall o, al8 o = true -> wt o = false /\ w2Zs o = to_Z (wl o) /\ to_Z (wl o) mod 8 = 0.
Proof.
  intros o H. unfold al8 in H. apply andb_prop in H as [T L]. apply negb_true_iff in T. apply Uint63.eqb_correct in L.
  split; [exact T|]. split; [rewrite w2Zs_eq; unfold w2Z; rewrite T; lia|].
  pose proof (ValP.land_mk (wl o) 3%uint63 ltac:(change (to_Z 3%uint63) with 3; lia)) as LM.
  change (PrimInt63.sub (PrimInt63.lsl 1 3) 1)%uint63 with 7%uint63 in LM. rewrite L in LM. change (to_Z 0%uint63) with 0 in LM.
  change (2 ^ to_Z 3%uint63) with 8 in LM. lia.
Qed.

Lemma mod64_mod8 : forall x, (x mod 2 ^ 64) mod 8 = x mod 8.
Proof. intros x. symmetry. apply Znumtheory.Zmod_div_mod; [reflexivity| reflexivity| exists (2 ^ 61); reflexivity]. Qed.

Lemma has_fact_holds : forall E f fs, facts_hold E fs -> has_fact f fs = true -> fact_holds E f.
Proof.
  intros E f fs HF. induction fs as [|g fs IH]; intros H; [discriminate H|]. cbn [has_fact] in H.
  apply Forall_cons_iff in HF as [Hg HF]. destruct (fact_eqb f g) eqn:Q; [| exact (IH HF H)].
  apply ValP.fact_eqb_eq in Q. subst g. exact Hg.
Qed.

Lemma div8_holds : forall E fs xs, facts_hold E fs -> div8 fs xs = true -> bv_unsigned (den E xs) mod 8 = 0.
Proof.
  intros E fs xs HF H. unfold div8 in H. pose proof (has_fact_holds E _ _ HF H) as FH. cbn [fact_holds] in FH.
  pose proof (f_equal bv_unsigned FH) as Q. rewrite and7_den_raw in Q. rewrite Q. vm_compute. reflexivity.
Qed.

Lemma alk_lit_spec : forall k o, to_Z k <= 63 -> alk_lit k o = true -> wt o = false /\ w2Zs o = to_Z (wl o) /\ to_Z (wl o) mod 2 ^ (to_Z k) = 0.
Proof.
  intros k o Hk H. unfold alk_lit in H. apply andb_prop in H as [T L]. apply negb_true_iff in T. apply Uint63.eqb_correct in L.
  split; [exact T|]. split; [rewrite w2Zs_eq; unfold w2Z; rewrite T; lia|].
  pose proof (ValP.land_mk (wl o) k Hk) as LM. rewrite L in LM. change (to_Z 0%uint63) with 0 in LM. lia.
Qed.
Lemma mod64_mod2k : forall x k, 0 <= k <= 64 -> (x mod 2 ^ 64) mod 2 ^ k = x mod 2 ^ k.
Proof.
  intros x k Hk. symmetry. apply Znumtheory.Zmod_div_mod; [apply Z.pow_pos_nonneg; lia| apply Z.pow_pos_nonneg; lia|].
  exists (2 ^ (64 - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma mod8_mod2k : forall x k, 0 <= k <= 3 -> x mod 8 = 0 -> x mod 2 ^ k = 0.
Proof.
  intros x k Hk H. apply Znumtheory.Zmod_divide in H; [|lia]. apply Znumtheory.Zdivide_mod. destruct H as [q ->].
  exists (q * 2 ^ (3 - k)). rewrite <- Z.mul_assoc. f_equal. change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma alk_sv_sound : forall E fs v, facts_hold E fs -> forall kk, to_Z kk <= 3 -> alk_sv kk fs v = true -> bv_unsigned (den E v) mod 2 ^ (to_Z kk) = 0.
Proof.
  intros E fs v HF. induction v as [c|n o|op a IHa b IHb| |mo a IHa b IHb| | | | | |]; intros kk Hk H; cbn [alk_sv] in H; fold alk_sv in H;
    pose proof (int_range kk) as KR;
    (destruct (PrimInt63.eqb kk 0%uint63) eqn:K0; [apply Uint63.eqb_correct in K0; subst kk; change (2 ^ to_Z 0%uint63) with 1; apply Z.mod_1_r|]);
    (destruct (div8 fs _) eqn:D8; [apply mod8_mod2k; [lia| exact (div8_holds E fs _ HF D8)]|]); try discriminate H.
  - destruct (alk_lit_spec kk c ltac:(lia) H) as (T & _ & M). destruct c as [t l]. cbn [wt wl] in T, M. subst t.
    change (W64 false l) with (wlit l). rewrite HeapCtr.TwinB.den_wlit. unfold ALib.Mem.wa. rewrite Z_to_bv_small; [exact M|].
    pose proof (int_range l) as R. rewrite two63_eq in R. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). unfold two64. lia.
  - apply andb_prop in H as [A8 AL]. destruct (alk_lit_spec kk o ltac:(lia) A8) as (T & ZS & M).
    assert (AN : bv_unsigned (ev E n) mod 2 ^ (to_Z kk) = 0).
    { destruct (PrimInt63.leb kk (find_align fs n)) eqn:FA; [exact (ValP.find_align_le E fs HF n kk FA)|].
      pose proof (div8_holds E fs _ HF AL) as X. rewrite HeapCtr.TwinB.den_VPz in X. apply mod8_mod2k; [lia| exact X]. }
    rewrite (ValP.den_VP E n o), ZS. unfold two64. rewrite mod64_mod2k by lia.
    rewrite Z.add_mod, AN, M by (apply Z.pow_nonzero; lia). cbn [Z.add]. apply Z.mod_0_l. apply Z.pow_nonzero; lia.
  - destruct op; try discriminate H.
    + destruct (alk_sv kk fs a) eqn:HA; [|discriminate H]. specialize (IHa kk Hk HA). specialize (IHb kk Hk H).
      cbn [den]. unfold alu64, alu. rewrite bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
      rewrite mod64_mod2k by lia. rewrite Z.add_mod, IHa, IHb by (apply Z.pow_nonzero; lia). cbn [Z.add]. apply Z.mod_0_l. apply Z.pow_nonzero; lia.
    +
      destruct b as [s| | | | | | | | | |]; try discriminate H.
      pose proof (shamt6_range s) as SR.
      cbn [den]. unfold alu64, alu. rewrite bv_shiftl_unsigned, shamt6_bv. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
      rewrite mod64_mod2k by lia. rewrite Z.shiftl_mul_pow2 by lia.
      destruct (PrimInt63.leb kk (shamt6 s)) eqn:KS.
      * apply leb_spec in KS. apply Znumtheory.Zdivide_mod. exists (bv_unsigned (den E a) * 2 ^ (to_Z (shamt6 s) - to_Z kk)).
        rewrite <- Z.mul_assoc. f_equal. rewrite <- Z.pow_add_r by lia. f_equal. lia.
      * assert (LT : to_Z (shamt6 s) < to_Z kk) by (destruct (Z_lt_le_dec (to_Z (shamt6 s)) (to_Z kk)) as [X|X]; [exact X| exfalso; rewrite (proj2 (leb_spec _ _) X) in KS; discriminate KS]).
        assert (EK : to_Z (PrimInt63.sub kk (shamt6 s)) = to_Z kk - to_Z (shamt6 s)) by (rewrite Uint63.sub_spec, wB_two63, two63_eq, Z.mod_small; [reflexivity| lia]).
        specialize (IHa (PrimInt63.sub kk (shamt6 s)) ltac:(rewrite EK; lia) H). rewrite EK in IHa.
        apply Znumtheory.Zmod_divide in IHa; [| apply Z.pow_nonzero; lia]. destruct IHa as [q Hq]. apply Znumtheory.Zdivide_mod.
        exists q. rewrite Hq, <- Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. lia.
  -
    destruct mo; try discriminate H. destruct b as [c| | | | | | | | | |]; try discriminate H.
    cbn [den]. unfold mul_div. rewrite bv_mul_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite mod64_mod2k by lia.
    destruct (alk_lit kk c) eqn:AL.
    + destruct (alk_lit_spec kk c ltac:(lia) AL) as (T & _ & M). destruct c as [t l]. cbn [wt wl] in T, M. subst t.
      rewrite wbv_unsigned. unfold w2Z. cbn [wt wl]. rewrite Z.add_0_l.
      rewrite Z.mul_mod, M, Z.mul_0_r by (apply Z.pow_nonzero; lia). apply Z.mod_0_l. apply Z.pow_nonzero; lia.
    + specialize (IHa kk Hk H). rewrite Z.mul_mod, IHa, Z.mul_0_l by (apply Z.pow_nonzero; lia). apply Z.mod_0_l. apply Z.pow_nonzero; lia.
Qed.
Lemma al8_sv_sound : forall E fs v, facts_hold E fs -> al8_sv fs v = true -> bv_unsigned (den E v) mod 8 = 0.
Proof. intros E fs v HF H. exact (alk_sv_sound E fs v HF 3%uint63 ltac:(change (to_Z 3%uint63) with 3; lia) H). Qed.
Lemma div8x_holds : forall E fs xs, facts_hold E fs -> div8x fs xs = true -> bv_unsigned (den E xs) mod 8 = 0.
Proof. intros E fs xs HF H. unfold div8x in H. destruct (div8 fs xs) eqn:D; [exact (div8_holds E fs xs HF D)| exact (al8_sv_sound E fs xs HF H)]. Qed.

Lemma tier1_tiers : forall {A} fs vs (q : list fact -> option A) r, tier1 fs vs q = Some r -> KnownT.KnownT.tiers fs vs q = Some r.
Proof. intros A fs vs q r H. unfold tier1 in H. unfold KnownT.KnownT.tiers. rewrite H. reflexivity. Qed.
Lemma tiers12_tiers : forall {A} fs vs (q : list fact -> option A) r, tiers12 fs vs q = Some r -> KnownT.KnownT.tiers fs vs q = Some r.
Proof.
  intros A fs vs q r H. unfold tiers12 in H. unfold KnownT.KnownT.tiers.
  destruct (q (rel_facts vs fs)) as [r1|]; [exact H|]. rewrite H. reflexivity.
Qed.
Lemma known_ltu_t1_t : forall fs a b, known_ltu_t1 fs a b = true -> KnownT.KnownT.known_ltu_t fs a b = true.
Proof.
  intros fs a b H. unfold known_ltu_t1, Step.dec_true in H. unfold KnownT.KnownT.known_ltu_t, KnownT.KnownT.decide_ltu_tt, KnownT.KnownT.dec_true.
  destruct (tier1 fs _ _) as [[|]|] eqn:T; try discriminate H. rewrite (tier1_tiers _ _ _ _ T). reflexivity.
Qed.
Lemma known_leu_t1_t : forall fs a b, known_leu_t1 fs a b = true -> KnownT.KnownT.known_leu_t fs a b = true.
Proof.
  intros fs a b H. unfold known_leu_t1, Step.dec_false in H. unfold KnownT.KnownT.known_leu_t, KnownT.KnownT.decide_ltu_tt, KnownT.KnownT.dec_false.
  destruct (tier1 fs _ _) as [[|]|] eqn:T; try discriminate H. rewrite (tier1_tiers _ _ _ _ T). reflexivity.
Qed.
Lemma known_leu_t12_t : forall fs a b, known_leu_t12 fs a b = true -> KnownT.KnownT.known_leu_t fs a b = true.
Proof.
  intros fs a b H. unfold known_leu_t12, Step.dec_false in H. unfold KnownT.KnownT.known_leu_t, KnownT.KnownT.decide_ltu_tt, KnownT.KnownT.dec_false.
  destruct (tiers12 fs _ _) as [[|]|] eqn:T; try discriminate H. rewrite (tiers12_tiers _ _ _ _ T). reflexivity.
Qed.
Lemma reqmax_ok_eq : forall fs n, reqmax_ok fs n = reqmax_ok_spec fs n.
Proof.
  intros fs n. unfold reqmax_ok, reqmax_ok_spec.
  destruct (reqmax_x4_t1 fs n) eqn:X1.
  - unfold reqmax_x4_t1 in X1. destruct (known_ltu_t1 fs n (VL B61w)) eqn:A; [|discriminate X1].
    unfold reqmax_x4. rewrite (known_ltu_t1_t _ _ _ A), (known_leu_t1_t _ _ _ X1). destruct (KnownT.KnownT.known_leu_t fs n (VL AREQMAXw)); reflexivity.
  - destruct (known_leu_t12 fs n (VL AREQMAXw)) eqn:A12.
    + rewrite (known_leu_t12_t _ _ _ A12). reflexivity.
    + destruct (reqmax_x4 fs n), (KnownT.KnownT.known_leu_t fs n (VL AREQMAXw)); reflexivity.
Qed.
Lemma reqmax_ok_sound : forall E fs n, facts_hold E fs -> reqmax_ok fs n = true -> bv_unsigned (den E n) <= 0xFFF00000.
Proof.
  intros E fs n HF H. rewrite reqmax_ok_eq in H. unfold reqmax_ok_spec, reqmax_x4 in H.
  destruct (KnownT.KnownT.known_leu_t fs n (VL AREQMAXw)) eqn:D.
  - pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF D) as L. cbn [den] in L. rewrite wbv_unsigned in L. exact L.
  - destruct (KnownT.KnownT.known_ltu_t fs n (VL B61w)) eqn:B; [|discriminate H].
    pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF B) as LB. cbn [den] in LB. rewrite wbv_unsigned in LB.
    replace (w2Z B61w) with (2 ^ 61) in LB by (vm_compute; reflexivity).
    pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF H) as L4.
    replace (bv_unsigned (den E (VL AREQMAX4w))) with 0x3FFC00000 in L4 by (vm_compute; reflexivity).
    cbn [den] in L4. unfold alu64, alu in L4. rewrite bv_shiftl_unsigned, shamt6_bv in L4.
    unfold bv_wrap, bv_modulus in L4. change (2 ^ Z.of_N 64) with (2 ^ 64) in L4.
    replace (to_Z (shamt6 (wlit 2%uint63))) with 2 in L4 by (vm_compute; reflexivity).
    rewrite Z.shiftl_mul_pow2 in L4 by lia. rewrite Z.mod_small in L4; [lia|].
    pose proof (bv_unsigned_in_range _ (den E n)) as R. lia.
Qed.

Lemma size_shape_sound : forall E fs n, facts_hold E fs -> size_shape_ok fs n = true ->
  match n with VL _ => True | _ => bv_unsigned (den E n) mod 8 = 0 end.
Proof.
  intros E fs n HF H.
  assert (GEN : al8_sv fs n || (KnownT.KnownT.known_eq_t fs (VAlu ALU_AND n (VL (wlit 7%uint63))) (VL wzero) || KnownT.KnownT.known_eq_t fs (sz_and7 n) (VL wzero)
                || KnownT.KnownT.known_leu_t fs (sz_and7 n) (VL wzero)) = true -> bv_unsigned (den E n) mod 8 = 0).
  { intros K. apply orb_prop in K as [K|K]; [exact (al8_sv_sound E fs n HF K)|].
    apply orb_prop in K as [K|K]; [apply orb_prop in K as [K|K]|].
    - pose proof (KnownA.TwinB.KnownA.known_eq_sound E _ _ _ HF K) as EQ. cbn [den] in EQ. unfold alu64, alu in EQ.
      apply (f_equal bv_unsigned) in EQ. rewrite bv_and_unsigned, !wbv_unsigned, wlit_ok, wzero_ok in EQ. change (to_Z 7%uint63) with (Z.ones 3) in EQ.
      rewrite Z.land_ones in EQ by lia. exact EQ.
    - pose proof (KnownA.TwinB.KnownA.known_eq_sound E _ _ _ HF K) as EQ. apply (f_equal bv_unsigned) in EQ. rewrite sz_and7_den in EQ.
      cbn [den] in EQ. rewrite wbv_unsigned, wzero_ok in EQ. exact EQ.
    - pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF K) as LE. rewrite sz_and7_den in LE. cbn [den] in LE. rewrite wbv_unsigned, wzero_ok in LE.
      pose proof (Z.mod_pos_bound (bv_unsigned (den E n)) 8 ltac:(lia)). lia. }
  destruct n; try exact I; apply GEN; cbn [size_shape_ok] in H;
    (destruct (al8_sv fs _); [reflexivity|]); cbn [orb];
    repeat match type of H with (if ?c then true else _) = true => destruct c; [rewrite ?orb_true_r; reflexivity|] end; rewrite ?orb_false_l; exact H.
Qed.

Lemma size_tail_sound : forall E fs n, facts_hold E fs -> size_tail_ok fs n = true ->
  1 <= bv_unsigned (den E n) /\ (forall w, n <> VL w).
Proof.
  intros E fs n HF H.
  assert (GEN : KnownT.KnownT.known_ltu_t fs (VL wzero) n = true -> 1 <= bv_unsigned (den E n)).
  { intros K. pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF K) as LT. cbn [den] in LT. rewrite wbv_unsigned, wzero_ok in LT. lia. }
  destruct n; cbn [size_tail_ok] in H; try discriminate H; (split; [apply GEN; exact H| intros w X; discriminate X]).
Qed.

Lemma no_tail_at_sound : forall fs (R : IMap.t region) sh n k0 rg, IMap.bst R -> no_tail_at fs R sh n = true ->
  IMap.find k0 R = Some rg -> tail_named (tail_rhs sh n) k0 fs = true -> False.
Proof.
  intros fs R sh n k0 rg B NT F TN. unfold no_tail_at in NT.
  pose proof (proj1 (IMap.forallb_spec _ _ B) NT k0 rg F) as C. cbv beta in C. rewrite TN in C. discriminate C.
Qed.

Lemma aheap_windows_inv : forall st hargs wnl, aheap_windows st = Some (hargs, wnl) ->
  find_op HEAP_ID (s_ops st) = Some hargs /\ CtrA.count_op HEAP_ID (s_ops st) = 1%nat
  /\ exists r1 n md A nw rest, IMap.find STACK_ID (s_regs st) = Some r1 /\ heap_nwin hargs = Some n /\ hargs = VL md :: A :: VL nw :: rest
     /\ wt nw = false /\ n = Z.to_nat (to_Z (wl nw)) /\ (3 * n <= length rest)%nat /\ (n <= 255)%nat
     /\ stack_window_ok_g n rest (rg_lo r1) = true /\ CtrA.nonstack_windows n rest = Some wnl
     /\ CtrA.windows_anchored (s_regs st) wnl = true /\ aregions_justified st wnl = true
     /\ twins_scan (s_facts st) (s_regs st) wnl wnl = true.
Proof.
  intros st hargs wnl H. unfold aheap_windows in H.
  destruct (find_op HEAP_ID (s_ops st)) as [h|] eqn:Hf; [|discriminate].
  destruct (CtrA.count_op HEAP_ID (s_ops st)) as [|[|c]] eqn:Hc; try discriminate.
  destruct (IMap.find STACK_ID (s_regs st)) as [r1|] eqn:Hr1; [|discriminate].
  destruct (heap_nwin h) as [n|] eqn:Hn; [|discriminate].
  destruct (heap_nwin_shape h n Hn) as (md & A & nw & rest & Eh & T & N & L). rewrite Eh in H.
  destruct (Nat.leb n 255 && stack_window_ok_g n rest (rg_lo r1)) eqn:C1; [|discriminate].
  apply andb_prop in C1 as [N255 SW]. apply Nat.leb_le in N255.
  destruct (CtrA.nonstack_windows n rest) as [wl'|] eqn:NW; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:AJ; [|discriminate] end.
  injection H as <- <-. apply andb_prop in AJ as [AJ A2]. apply andb_prop in AJ as [A1 TS]. subst h.
  split; [reflexivity|]. split; [reflexivity|].
  exists r1, n, md, A, nw, rest. repeat (split; [assumption || reflexivity|]). exact TS.
Qed.

Lemma stack_window_g_In : forall E n rest klo,
  stack_window_ok_g n rest klo = true ->
  exists wlo kw len, okey wlo = Some kw /\ keyZ kw <= keyZ klo
    /\ In (HeapOp.Win (bv_unsigned (den E (VP STACK_ID wlo))) len HeapOp.K_STACK) (wins_of E n rest).
Proof.
  intros E n. induction n as [|n IH]; intros rest klo H; [cbn in H; destruct rest; discriminate|].
  destruct rest as [|lo rest1]; [cbn in H; discriminate|].
  destruct rest1 as [|len rest2]; [destruct lo; cbn in H; discriminate|].
  destruct rest2 as [|kd rest']; [destruct lo; cbn in H; discriminate|].
  cbn [stack_window_ok_g] in H.
  assert (STEP : stack_window_ok_g n rest' klo = true ->
            exists wlo kw len0, okey wlo = Some kw /\ keyZ kw <= keyZ klo
              /\ In (HeapOp.Win (bv_unsigned (den E (VP STACK_ID wlo))) len0 HeapOp.K_STACK) (wins_of E (S n) (lo :: len :: kd :: rest'))).
  { intros H'. destruct (IH rest' klo H') as (wlo & kw & len0 & K1 & K2 & K3). exists wlo, kw, len0. split; [exact K1|]. split; [exact K2|].
    rewrite wins_of_cons. right. exact K3. }
  destruct lo as [|k wlo| | | | | | | | |]; cbn in H; try (apply STEP; exact H).
  destruct kd as [kdw| | | | | | | | | |]; cbn in H; try (apply STEP; exact H).
  apply orb_prop in H as [H|H]; [| apply STEP; exact H].
  apply andb_prop in H as [H HK]. apply andb_prop in H as [H1 H2].
  apply Uint63.eqb_correct in H1. subst k. destruct (okey wlo) as [kw|] eqn:Hkw; [|discriminate].
  rewrite kleb_keyZ in HK. apply Z.leb_le in HK.
  exists wlo, kw, (bv_unsigned (den E len)). split; [exact Hkw|]. split; [exact HK|]. rewrite wins_of_cons. left.
  unfold HeapOp.K_STACK. rewrite (unsigned_VL E kdw), (HeapCtr.TwinB.weqb_wzero_unsigned' kdw H2). reflexivity.
Qed.

Lemma den_key2w : forall E k o, bv_unsigned (den E (VP k (key2w o))) = (bv_unsigned (ev E k) + keyZ o) mod two64.
Proof. intros E k o. rewrite den_VP. unfold key2w. rewrite w2Zs_key. reflexivity. Qed.

Lemma den_add_vp0 : forall E k hi, bv_unsigned (den E (VAlu ALU_ADD (VP k wzero) hi)) = (bv_unsigned (ev E k) + bv_unsigned (den E hi)) mod two64.
Proof.
  intros E k hi. change (den E (VAlu ALU_ADD (VP k wzero) hi)) with (alu64 ALU_ADD (den E (VP k wzero)) (den E hi)).
  rewrite HeapCtr.TwinB.den_VPz. unfold alu64, alu. rewrite bv_add_unsigned. reflexivity.
Qed.

Lemma below_top_sound : forall E st ms mo k r, st_ok segs OPS E st ms mo -> IMap.find k (s_regs st) = Some r -> k <> 0%uint63 ->
  below_top (s_facts st) k r = true -> bv_unsigned (ev E k) + hiZ E r <= 2 ^ 47.
Proof.
  intros E st ms mo k r HS Hk K0 BT. pose proof (so_facts _ _ _ _ _ _ HS) as HF. pose proof (so_reg _ _ _ _ _ _ HS k r Hk) as RO.
  assert (KZ : PrimInt63.eqb k 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  destruct (ro_range _ _ _ _ _ _ RO KZ) as [RLO RHI].
  unfold below_top in BT. apply orb_prop in BT as [FAST|BT].
  {
    unfold below_top_fast in FAST. destruct (rg_hi r) as [h| | | | | | | | | |] eqn:EH; try discriminate FAST.
    destruct (find_range (s_facts st) k) as [[lo0 hi0]|] eqn:FR; [|discriminate FAST].
    apply andb_prop in FAST as [FAST L3]. apply andb_prop in FAST as [FAST L2]. apply andb_prop in FAST as [FAST L1]. apply andb_prop in FAST as [T1 T2].
    apply negb_true_iff in T1. apply negb_true_iff in T2. apply Uint63.leb_spec in L1. apply Uint63.leb_spec in L2. apply Uint63.leb_spec in L3.
    change (to_Z TOP47i) with (2 ^ 47) in L1, L2, L3.
    pose proof (ValP.find_range_sound E _ HF k lo0 hi0 FR) as [_ RK].
    assert (WH : w2Z hi0 = to_Z (wl hi0)) by (unfold w2Z; rewrite T1; lia).
    assert (HZ : hiZ E r = to_Z (wl h)) by (unfold hiZ; rewrite EH; cbn [den]; rewrite wbv_unsigned; unfold w2Z; rewrite T2; lia).
    pose proof (int_range (wl hi0)) as R1. pose proof (int_range (wl h)) as R2.
    rewrite Uint63.add_spec, Z.mod_small in L3 by (rewrite wB_two63, two63_eq; lia). rewrite HZ. lia. }
  pose proof (KnownA.TwinB.KnownA.known_leu_q_sound E _ _ _ HF BT) as X.
  replace (bv_unsigned (den E (VL (wlit 140737488355328%uint63)))) with (2 ^ 47) in X by (vm_compute; reflexivity).
  assert (EQ : bv_unsigned (den E (match rg_hi r with VL h => VP k h | hi => VAlu ALU_ADD (VP k wzero) hi end)) = bv_unsigned (ev E k) + hiZ E r).
  { unfold hiZ in *. pose proof (bv_unsigned_in_range 64 (ev E k)) as REK. pose proof (bv_unsigned_in_range 64 (den E (rg_hi r))) as RHH.
    change (bv_modulus 64) with (2 ^ 64) in *. unfold two64 in *.
    destruct (rg_hi r) as [h| | | | | | | | | |]; try (rewrite den_add_vp0; apply Z.mod_small; unfold two64; lia).
    cbn [den] in *. rewrite bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. lia. }
  rewrite EQ in X. exact X.
Qed.

Lemma known_leu_s_sound : forall fs a b, known_leu_s fs a b = true -> known_leu fs a b = true.
Proof.
  intros fs a b H. unfold known_leu_s in H. unfold known_leu, decide_ltu. destruct (decide_ltu_s fs b a) as [x|]; [exact H| discriminate H].
Qed.

Lemma annot_end_ok_sound : forall E fs k len x11, facts_hold E fs -> annot_end_ok fs k len x11 = true ->
  bv_unsigned (ev E k) mod 8 = 0 -> bv_unsigned (den E x11) mod 8 = 0 -> bv_unsigned (den E len) <= 8064 -> bv_unsigned (ev E k) < 2 ^ 47 ->
  bv_unsigned (den E x11) <= bv_unsigned (ev E k) + 8 * bv_unsigned (den E len).
Proof.
  intros E fs k len x11 HF H K8 E8 WMAX K47. unfold annot_end_ok in H.
  pose proof (bv_unsigned_in_range 64 (ev E k)) as RK. unfold bv_modulus in RK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RK.
  assert (SYM : match tie_of fs len with
                | Some xs => (sv_eqb x11 (VAlu ALU_ADD (VP k wzero) xs) ||| has_fact (FULe x11 (VAlu ALU_ADD (VP k wzero) xs)) fs)
                             &&& KnownT.KnownT.known_leu_t fs xs (VL SYMCAPw) &&& nowrap_kb fs k SYMCAPw
                | None => false
                end = true -> bv_unsigned (den E x11) <= bv_unsigned (ev E k) + 8 * bv_unsigned (den E len)).
  { clear H. intros H. destruct (tie_of fs len) as [xs|] eqn:TIE; [|discriminate H].
    apply andb_prop in H as [H NWK]. apply andb_prop in H as [HFA XS].
    assert (U : bv_unsigned (den E x11) <= bv_unsigned (den E (VAlu ALU_ADD (VP k wzero) xs))).
    { apply orb_prop in HFA as [EQ|HFA]; [apply sv_eqb_eq in EQ; rewrite EQ; lia|]. pose proof (has_fact_holds E _ _ HF HFA) as U0. cbn [fact_holds] in U0. exact U0. }
    rewrite den_add_vp0 in U.
    pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF XS) as X8. replace (bv_unsigned (den E (VL SYMCAPw))) with 65536 in X8 by (vm_compute; reflexivity).
    pose proof (bv_unsigned_in_range 64 (den E xs)) as RX. unfold bv_modulus in RX. change (2 ^ Z.of_N 64) with (2 ^ 64) in RX.
    unfold two64 in U. rewrite Z.mod_small in U by lia.
    rewrite (tie_of_holds E fs len xs HF TIE). clear - U K8 E8. Z.div_mod_to_equations. lia. }
  destruct len as [wlen| | | | | | | | | |]; try (exact (SYM H)). clear SYM.
  apply andb_prop in H as [WT LE]. apply negb_true_iff in WT.
  pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF LE) as EI.
  assert (WLE : bv_unsigned (den E (VL wlen)) = to_Z (wl wlen)) by (cbn [den]; rewrite wbv_unsigned; unfold w2Z; rewrite WT; reflexivity).
  rewrite WLE in *. pose proof (int_range (wl wlen)) as RW.
  assert (LS : to_Z (PrimInt63.lsl (wl wlen) 3%uint63) = 8 * to_Z (wl wlen)).
  { rewrite lsl_spec. change (to_Z 3%uint63) with 3. change (2 ^ 3) with 8. rewrite Z.mod_small; [lia|]. rewrite wB_two63, two63_eq. lia. }
  assert (ZS : w2Zs (wlit (PrimInt63.lsl (wl wlen) 3%uint63)) = 8 * to_Z (wl wlen)).
  { rewrite w2Zs_eq. unfold w2Z, wlit. cbn [wt wl]. rewrite LS. lia. }
  rewrite (ValP.den_VP E k _), ZS in EI. unfold two64 in EI. rewrite Z.mod_small in EI by lia. exact EI.
Qed.
Lemma stack_side_just_sound : forall E st ms mo ks k r, st_ok segs OPS E st ms mo -> IMap.find k (s_regs st) = Some r -> k <> 0%uint63 ->
  stack_side_just (s_facts st) (getr st X2) (sp_below_anchor_t (s_facts st) (getr st X2)) ks k r = true ->
  (k = ks \/ bv_unsigned (den E (getr st X2)) <= bv_unsigned (ev E k) + loZ r) /\ bv_unsigned (ev E k) + hiZ E r <= 2 ^ 47.
Proof.
  intros E st ms mo ks k r HS Hk K0 J. pose proof (so_facts _ _ _ _ _ _ HS) as HF. pose proof (so_reg _ _ _ _ _ _ HS k r Hk) as RO.
  assert (KZ : PrimInt63.eqb k 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  destruct (ro_range _ _ _ _ _ _ RO KZ) as [RLO RHI].
  unfold stack_side_just in J. destruct (PrimInt63.eqb k ks) eqn:KS.
  { apply Uint63.eqb_correct in KS. split; [left; exact KS| exact (below_top_sound E st ms mo k r HS Hk K0 J)]. }
  apply andb_prop in J as [AB BT]. split; [right| exact (below_top_sound E st ms mo k r HS Hk K0 BT)].
  assert (DIRECT : bv_unsigned (den E (getr st X2)) <= bv_unsigned (den E (VP k (key2w (rg_lo r)))) ->
            bv_unsigned (den E (getr st X2)) <= bv_unsigned (ev E k) + loZ r).
  { intros X. rewrite den_key2w in X. unfold loZ in *.
    pose proof (Z.mod_le (bv_unsigned (ev E k) + keyZ (rg_lo r)) two64 ltac:(lia) ltac:(unfold two64; lia)). lia. }
  apply orb_prop in AB as [AB1|AB].
  { apply orb_prop in AB1 as [DS|PAD]; [exact (DIRECT (HeapCtr.TwinB.known_leu_sound E _ _ _ HF (known_leu_s_sound _ _ _ DS)))|].

    unfold pad_side in PAD. destruct (getr st X2) as [|n o| | | | | | | | |] eqn:SPE; try discriminate PAD.
    apply andb_prop in PAD as [PAD NW]. apply andb_prop in PAD as [PAD HFa]. apply andb_prop in PAD as [L0 WT]. apply Uint63.eqb_correct in L0.
    pose proof (has_fact_holds E _ _ HF HFa) as FH. cbn [fact_holds] in FH. rewrite !HeapCtr.TwinB.den_VPz in FH.
    destruct (ValP.nowrap_kb_sound E _ HF n o NW) as [RR D]. rewrite D. rewrite ValP.w2Zs_eq, WT in *.
    pose proof (w2Z_range o) as ROo. unfold loZ. rewrite L0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. unfold two64 in *. lia. }
  apply orb_prop in AB as [AB|AB]; [| exact (DIRECT (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF AB))].
  apply andb_prop in AB as [AB SS]. apply andb_prop in AB as [L0 _]. apply Uint63.eqb_correct in L0.
  pose proof (KnownA.TwinB.KnownA.stack_side_sound E _ _ _ HF SS) as X. unfold loZ. rewrite L0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. lia.
Qed.

Lemma find_lb_to_holds : forall E fs n k o, Forall (fact_holds E) fs -> find_lb_to fs n k = Some o ->
  bv_unsigned (den E (VP k o)) <= bv_unsigned (ev E n).
Proof.
  intros E fs. induction fs as [|f fs IH]; intros n k o HF H; cbn [find_lb_to] in H; [discriminate|].
  inversion HF as [|f' l Hf HF']; subst.
  destruct f as [| | |x y|x y| | |]; try exact (IH n k o HF' H).
  - destruct x as [|k' o'| | | | | | | | |]; try exact (IH n k o HF' H). destruct y as [|n' z| | | | | | | | |]; try exact (IH n k o HF' H).
    destruct (PrimInt63.eqb n' n && PrimInt63.eqb k' k && weqb z wzero) eqn:C; [| exact (IH n k o HF' H)]. injection H as <-.
    apply andb_prop in C as [C Z0]. apply andb_prop in C as [EN EK]. apply Uint63.eqb_correct in EN. apply Uint63.eqb_correct in EK. apply weqb_eq in Z0. subst n' k' z.
    cbn [fact_holds] in Hf. rewrite HeapCtr.TwinB.den_VPz in Hf. exact Hf.
  - destruct x as [|n' z| | | | | | | | |]; try exact (IH n k o HF' H). destruct y as [|k' o'| | | | | | | | |]; try exact (IH n k o HF' H).
    destruct (PrimInt63.eqb n' n && PrimInt63.eqb k' k && weqb z wzero) eqn:C; [| exact (IH n k o HF' H)]. injection H as <-.
    apply andb_prop in C as [C Z0]. apply andb_prop in C as [EN EK]. apply Uint63.eqb_correct in EN. apply Uint63.eqb_correct in EK. apply weqb_eq in Z0. subst n' k' z.
    cbn [fact_holds] in Hf. rewrite HeapCtr.TwinB.den_VPz in Hf. rewrite <- Hf. lia.
Qed.
Lemma find_ub_to_holds : forall E fs n oA k c, Forall (fact_holds E) fs -> find_ub_to fs n oA k = Some c ->
  bv_unsigned (den E (VP n oA)) <= bv_unsigned (den E (VP k c)).
Proof.
  intros E fs. induction fs as [|f fs IH]; intros n oA k c HF H; cbn [find_ub_to] in H; [discriminate|].
  inversion HF as [|f' l Hf HF']; subst.
  destruct f as [| | |x y|x y| | |]; try exact (IH n oA k c HF' H).
  destruct x as [|n' o'| | | | | | | | |]; try exact (IH n oA k c HF' H). destruct y as [|k' c'| | | | | | | | |]; try exact (IH n oA k c HF' H).
  destruct (PrimInt63.eqb n' n && weqb o' oA && PrimInt63.eqb k' k) eqn:C; [| exact (IH n oA k c HF' H)]. injection H as <-.
  apply andb_prop in C as [C EK]. apply andb_prop in C as [EN EO]. apply Uint63.eqb_correct in EN. apply Uint63.eqb_correct in EK. apply weqb_eq in EO. subst n' k' o'.
  exact Hf.
Qed.
Lemma vec_hi_in_sound : forall E fs h len, Forall (fact_holds E) fs -> vec_hi_in fs h len = true ->
  bv_unsigned (den E h) <= bv_unsigned (den E len).
Proof.
  intros E fs h len HF H. unfold vec_hi_in in H.
  destruct h as [| |op x c3v| | | | | | | |]; try discriminate H. destruct op; try discriminate H.
  destruct x as [| |op2 a b| | | | | | | |]; try discriminate H. destruct op2; try discriminate H.
  destruct a as [|n oA| | | | | | | | |]; try discriminate H. destruct b as [|k z| | | | | | | | |]; try discriminate H.
  destruct c3v as [c3| | | | | | | | | |]; try discriminate H.
  assert (SYMARM : (weqb z wzero && weqb c3 (wlit 3%uint63)
      && match tie_of fs len, find_lb_to fs n k with
         | Some xs, Some o2 =>
             has_fact (FULe (VP n oA) (VAlu ALU_ADD (VP k wzero) xs)) fs
             && KnownT.KnownT.known_leu_t fs xs (VL SYMCAPw) && nowrap_kb fs k SYMCAPw && negb (wt oA) && negb (wt o2)
             && nowrap_kb fs n oA && nowrap_kb fs k o2
         | _, _ => false
         end = true) ->
      bv_unsigned (den E (VAlu ALU_SRL (VAlu ALU_SUB (VP n oA) (VP k z)) (VL c3))) <= bv_unsigned (den E len)).
  { clear H. intros H. apply andb_prop in H as [H M]. apply andb_prop in H as [Z0 C3]. apply weqb_eq in Z0. apply weqb_eq in C3. subst z c3.
    destruct (tie_of fs len) as [xs|] eqn:TIE; [|discriminate M]. destruct (find_lb_to fs n k) as [o2|] eqn:LB; [|discriminate M].
    apply andb_prop in M as [M NW2]. apply andb_prop in M as [M NWA]. apply andb_prop in M as [M WT2]. apply andb_prop in M as [M WTA].
    apply andb_prop in M as [M NWK]. apply andb_prop in M as [HFA XS].
    apply negb_true_iff in WT2. apply negb_true_iff in WTA.
    destruct (nowrap_kb_sound E _ HF n oA NWA) as [RA DA]. destruct (nowrap_kb_sound E _ HF k _ NWK) as [RK8 _]. destruct (nowrap_kb_sound E _ HF k o2 NW2) as [R2 D2].
    pose proof (find_lb_to_holds E fs n k o2 HF LB) as L. rewrite D2 in L.
    pose proof (has_fact_holds E _ _ HF HFA) as U. cbn [fact_holds] in U. rewrite DA, den_add_vp0 in U.
    pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF XS) as X8. replace (bv_unsigned (den E (VL SYMCAPw))) with 65536 in X8 by (vm_compute; reflexivity).
    replace (w2Zs SYMCAPw) with 65536 in RK8 by (vm_compute; reflexivity).
    pose proof (tie_of_holds E fs len xs HF TIE) as TL.
    assert (ZA : w2Zs oA = w2Z oA) by (rewrite w2Zs_eq; rewrite WTA; lia).
    assert (Z2 : w2Zs o2 = w2Z o2) by (rewrite w2Zs_eq; rewrite WT2; lia).
    rewrite ZA in U, RA, DA. rewrite Z2 in L.
    pose proof (w2Z_range oA) as ROA. pose proof (w2Z_range o2) as RO2.
    pose proof (bv_unsigned_in_range 64 (den E xs)) as RX. unfold bv_modulus in RX. change (2 ^ Z.of_N 64) with (2 ^ 64) in RX.
    pose proof (bv_unsigned_in_range 64 (ev E n)) as RN. pose proof (bv_unsigned_in_range 64 (ev E k)) as RKK. unfold bv_modulus in RN, RKK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RN, RKK.
    unfold two64 in *. rewrite Z.mod_small in U by lia.
    rewrite TL. cbn [den]. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned, bv_sub_unsigned.
    replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
    replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
    change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    change (bv_add (ev E n) (wbv oA)) with (den E (VP n oA)). rewrite DA.
    change (bv_add (ev E k) (wbv wzero)) with (den E (VP k wzero)). rewrite (HeapCtr.TwinB.den_VPz E k).
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Z.mod_small by lia. clear - U L RO2. Z.div_mod_to_equations. lia. }
  destruct len as [wlen| | | | | | | | | |]; try (exact (SYMARM H)). clear SYMARM.
  apply andb_prop in H as [H M]. apply andb_prop in H as [H W58]. apply andb_prop in H as [H WTL]. apply andb_prop in H as [Z0 C3].
  apply weqb_eq in Z0. apply weqb_eq in C3. subst z c3. apply negb_true_iff in WTL. apply Uint63.ltb_spec in W58.
  destruct (find_lb_to fs n k) as [o2|] eqn:LB; [|discriminate M]. destruct (find_ub_to fs n oA k) as [cU|] eqn:UB; [|discriminate M].
  apply andb_prop in M as [M NW2]. apply andb_prop in M as [M NWC]. apply andb_prop in M as [M NWA]. apply andb_prop in M as [M WT2].
  apply andb_prop in M as [M WTA]. apply andb_prop in M as [WTC LEC].
  apply negb_true_iff in WT2. apply negb_true_iff in WTA. apply negb_true_iff in WTC. apply Uint63.leb_spec in LEC.
  destruct (nowrap_kb_sound E _ HF n oA NWA) as [RA DA]. destruct (nowrap_kb_sound E _ HF k cU NWC) as [RC DC]. destruct (nowrap_kb_sound E _ HF k o2 NW2) as [R2 D2].
  pose proof (find_lb_to_holds E fs n k o2 HF LB) as L. pose proof (find_ub_to_holds E fs n oA k cU HF UB) as U.
  rewrite D2 in L. rewrite DA, DC in U.
  assert (ZA : w2Zs oA = w2Z oA) by (rewrite w2Zs_eq; rewrite WTA; lia).
  assert (ZC : w2Zs cU = w2Z cU) by (rewrite w2Zs_eq; rewrite WTC; lia).
  assert (Z2 : w2Zs o2 = w2Z o2) by (rewrite w2Zs_eq; rewrite WT2; lia).
  rewrite ZA, ZC in U. rewrite Z2 in L. rewrite ZA in RA, DA.
  pose proof (w2Z_range oA) as ROA. pose proof (w2Z_range o2) as RO2. pose proof (w2Z_range cU) as ROC.
  assert (WC : w2Z cU = to_Z (wl cU)) by (unfold w2Z; rewrite WTC; lia).
  assert (WL : w2Z wlen = to_Z (wl wlen)) by (unfold w2Z; rewrite WTL; lia).
  rewrite lsl_spec in LEC. change (to_Z 3%uint63) with 3 in LEC. change (to_Z 288230376151711744%uint63) with (2 ^ 58) in W58.
  rewrite Z.mod_small in LEC by (pose proof (int_range (wl wlen)); change wB with (2 ^ 63); change (2 ^ 3) with 8; lia). change (2 ^ 3) with 8 in LEC.
  pose proof (bv_unsigned_in_range 64 (ev E n)) as RN. pose proof (bv_unsigned_in_range 64 (ev E k)) as RK. unfold bv_modulus in RN, RK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RN, RK.
  unfold two64 in *.
  cbn [den]. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned, bv_sub_unsigned.
  replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
  replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  change (bv_add (ev E n) (wbv oA)) with (den E (VP n oA)). rewrite DA.
  change (bv_add (ev E k) (wbv wzero)) with (den E (VP k wzero)). rewrite (HeapCtr.TwinB.den_VPz E k).
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. rewrite wbv_unsigned, WL. clear - U L LEC WC RO2. Z.div_mod_to_equations. lia.
Qed.

Definition sliver_sem (E : env) (st : sstate) (ks : int) (rss : region) (k : int) (r : region) : Prop :=
  rg_cells r = IMap.Leaf /\ rg_bg r = BGNone /\ rg_w r = true /\ loZ r = 0
  /\ exists wlo, stack_wlo st = Some wlo /\ bv_unsigned (ev E k) = bv_unsigned (den E (VP STACK_ID wlo))
       /\ bv_unsigned (ev E k) + hiZ E r = bv_unsigned (ev E ks) + loZ rss.

Lemma sliver_floor_sound : forall E st ms mo ks offs rss wlo,
  st_ok segs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) -> sliver_floor st = true -> stack_wlo st = Some wlo ->
  0 <= bv_unsigned (ev E ks) + loZ rss ->
  bv_unsigned (den E (VP STACK_ID wlo)) = bv_unsigned (ev E STACK_ID) + w2Zs wlo
  /\ bv_unsigned (den E (VP STACK_ID wlo)) <= bv_unsigned (ev E ks) + loZ rss.
Proof.
  intros E st ms mo ks offs rss wlo HS SR FL SW LO0. unfold sliver_floor in FL. unfold stack_wlo in SW.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|]; [|discriminate].
  unfold sp_floor_ok in FL. destruct (heap_nwin hargs) as [n|]; [|discriminate].
  destruct hargs as [|h0 [|h1 [|h2 rest]]]; try discriminate. rewrite SR in FL.
  destruct (stack_window_key n rest) as [w|] eqn:SK; [|discriminate].
  destruct (nowrap_kb (s_facts st) STACK_ID w) eqn:NWw; [|discriminate]. injection SW as ->.
  destruct (okey wlo) as [kw|] eqn:KW; [|discriminate].
  apply andb_prop in FL as [NW H].
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  destruct (nowrap_kb_sound E _ HF STACK_ID wlo NWw) as [R1 D1].
  destruct (okey_sound _ _ KW) as [EKW _].
  split; [exact D1|]. rewrite D1, <- EKW.
  destruct (PrimInt63.eqb ks STACK_ID) eqn:K1.
  - apply Uint63.eqb_correct in K1. subst ks. rewrite kleb_keyZ in H. apply Z.leb_le in H. unfold loZ. lia.
  - destruct (GTwinSub.GTwinSub.find_lb (s_facts st) ks STACK_ID) as [o2|] eqn:FLB; [|discriminate].
    apply andb_prop in H as [NW2 LE]. apply Z.leb_le in LE.
    destruct (nowrap_kb_sound E _ HF STACK_ID o2 NW2) as [R2 D2].
    pose proof (GTwinSub.GTwinSub.find_lb_holds E _ ks STACK_ID o2 HF FLB) as LB. rewrite D2, HeapCtr.TwinB.den_VPz in LB. unfold loZ. lia.
Qed.

Lemma sliver_just_sound : forall E st ms mo ks offs rss k r,
  st_ok segs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) -> IMap.find k (s_regs st) = Some r -> k <> 0%uint63 ->
  sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k r = true ->
  sliver_sem E st ks rss k r.
Proof.
  intros E st ms mo ks offs rss k r HS SR Hk K0 J. unfold sliver_just in J.
  destruct (stack_wlo st) as [wlo|] eqn:SW; [|discriminate].
  destruct (sp_region_inv st ks offs rss SR) as (_ & Hrs & KZs & _). rewrite Hrs in J.
  apply andb_prop in J as [J Q]. apply andb_prop in J as [J Q0]. apply andb_prop in J as [J Q1]. apply andb_prop in J as [J Q2].
  apply andb_prop in J as [J Q3]. apply andb_prop in J as [J Q4]. apply andb_prop in J as [J Q5].
  pose proof (so_facts _ _ _ _ _ _ HS) as HF. pose proof (so_zero _ _ _ _ _ _ HS) as HZ.
  destruct (rg_cells r) eqn:RC; [|discriminate Q2]. destruct (rg_bg r) eqn:RB; try discriminate Q1.
  apply Uint63.eqb_correct in Q3. apply sv_eqb_eq in Q0.
  assert (KNEG : keyZ (rg_lo rss) < 0).
  { apply negb_true_iff in Q5. destruct (keyZ_cases (rg_lo rss)) as [[B _]|[_ ->]].
    - exfalso. destruct (ltbP (rg_lo rss) bit62i) as [L|L]; [discriminate Q5|]. rewrite to_Z_bit62i in L. lia.
    - pose proof (int_range (rg_lo rss)) as R. rewrite two63_eq in R. lia. }
  pose proof (has_fact_holds E _ _ HF Q) as FE. cbn [fact_holds] in FE.
  pose proof (ro_range _ _ _ _ _ _ (so_reg _ _ _ _ _ _ HS ks rss Hrs) KZs) as [RS0 RS1].
  destruct (sliver_floor_sound E st ms mo ks offs rss wlo HS SR J SW RS0) as [D1 FLO].
  unfold sliver_sem. split; [exact RC|]. split; [exact RB|]. split; [exact Q4|]. split; [unfold loZ; rewrite Q3; reflexivity|].
  exists wlo. split; [exact SW|].
  assert (EK : bv_unsigned (ev E k) = bv_unsigned (den E (VP STACK_ID wlo))) by (rewrite <- FE, HeapCtr.TwinB.den_VPz; reflexivity).
  split; [exact EK|].
  unfold hiZ. rewrite Q0. cbn [den]. unfold alu64, alu. rewrite bv_sub_unsigned.
  change (bv_add (ev E ks) (wbv (key2w (rg_lo rss)))) with (den E (VP ks (key2w (rg_lo rss)))).
  change (bv_add (ev E STACK_ID) (wbv wlo)) with (den E (VP STACK_ID wlo)).
  pose proof (bv_unsigned_in_range 64 (ev E ks)) as RKS. unfold bv_modulus in RKS.
  rewrite den_key2w. unfold loZ in *. rewrite (Z.mod_small (bv_unsigned (ev E ks) + keyZ (rg_lo rss))) by (unfold two64 in *; lia).
  pose proof (bv_unsigned_in_range 64 (den E (VP STACK_ID wlo))) as RW. unfold bv_modulus in RW.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). unfold two64 in *. rewrite Z.mod_small by lia. lia.
Qed.

Lemma sliver_neg : forall st ks offs rss k r, sp_region st = Some (ks, offs, rss) ->
  sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k r = true -> loZ rss < 0.
Proof.
  intros st ks offs rss k r SR J. unfold sliver_just in J. destruct (stack_wlo st) as [wlo|]; [|discriminate].
  destruct (sp_region_inv st ks offs rss SR) as (_ & Hrs & _). rewrite Hrs in J.
  apply andb_prop in J as [J _]. apply andb_prop in J as [J _]. apply andb_prop in J as [J _]. apply andb_prop in J as [J _].
  apply andb_prop in J as [J _]. apply andb_prop in J as [J _]. apply andb_prop in J as [_ Q5].
  apply negb_true_iff in Q5. unfold loZ. destruct (keyZ_cases (rg_lo rss)) as [[B _]|[_ ->]].
  - exfalso. destruct (ltbP (rg_lo rss) bit62i) as [L|L]; [discriminate Q5|]. rewrite to_Z_bit62i in L. lia.
  - pose proof (int_range (rg_lo rss)) as R. rewrite two63_eq in R. lia.
Qed.

Lemma sliver_range : forall E st ms mo ks offs rss k r a,
  st_ok segs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) -> sliver_sem E st ks rss k r ->
  bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r ->
  exists wlo, stack_wlo st = Some wlo /\ bv_unsigned (den E (VP STACK_ID wlo)) <= a < bv_unsigned (ev E ks) + loZ rss.
Proof.
  intros E st ms mo ks offs rss k r a HS SR (_ & _ & _ & L0 & wlo & SW & EK & EH) Ha. exists wlo. split; [exact SW|]. rewrite L0 in Ha. lia.
Qed.

Lemma pair_main_in_sound : forall E fs wl k h len, facts_hold E fs -> pair_main_in fs wl k h len = true -> bv_unsigned (den E h) <= bv_unsigned (den E len).
Proof.
  intros E fs wl k h len HF H. unfold pair_main_in in H.
  destruct (block_of_twin fs k) as [kb|]; [|discriminate H]. destruct (CtrA.win_lookup wl kb) as [[n kdb]|]; [|discriminate H].
  apply andb_prop in H as [H NMAX]. apply andb_prop in H as [H ST]. apply andb_prop in H as [H EL]. apply andb_prop in H as [_ EH].
  apply sv_eqb_eq in EH, EL. subst h len.
  destruct (size_tail_sound E fs n HF ST) as [N1 _].
  pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF NMAX) as NM. replace (bv_unsigned (den E (VL AREQMAXw))) with 4293918720 in NM by (vm_compute; reflexivity).
  rewrite (sz_last_den E n N1), (twin_len_den E n) by lia. clear - N1. Z.div_mod_to_equations. lia.
Qed.

Lemma twin_full_in_sound : forall E fs h len, facts_hold E fs -> twin_full_in fs h len = true -> bv_unsigned (den E h) <= bv_unsigned (den E len).
Proof.
  intros E fs h len HF H. unfold twin_full_in in H. destruct (tie_of fs len) as [xs|] eqn:TIE; [|discriminate H].
  apply andb_prop in H as [H X8]. apply andb_prop in H as [EH D8]. apply sv_eqb_eq in EH. subst h.
  pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF X8) as B. replace (bv_unsigned (den E (VL SYMCAPw))) with 65536 in B by (vm_compute; reflexivity).
  rewrite (twin_len_den E xs) by lia. rewrite (tie_of_holds E fs len xs HF TIE). pose proof (div8x_holds E fs xs HF D8) as M. clear - M. Z.div_mod_to_equations. lia.
Qed.
Lemma aregion_just_sound : forall E st ms mo wnl ks offs rss k r,
  st_ok segs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) -> aregions_justified st wnl = true ->
  IMap.find k (s_regs st) = Some r -> k <> 0%uint63 ->
  (k = ks /\ bv_unsigned (ev E k) + hiZ E r <= 2 ^ 47)
  \/ (k <> ks /\
      ((exists len kd, CtrA.win_lookup wnl k = Some (len, kd) /\ loZ r = 0 /\ hiZ E r <= bv_unsigned (den E len))
       \/ (bv_unsigned (den E (getr st X2)) <= bv_unsigned (ev E k) + loZ r /\ bv_unsigned (ev E k) + hiZ E r <= 2 ^ 47)
       \/ (view_just (s_facts st) (s_regs st) (getr st X2) (sp_below_anchor_t (s_facts st) (getr st X2)) wnl ks (stack_wlo st) k r = true
           \/ sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k r = true))).
Proof.
  intros E st ms mo wnl ks offs rss k r HS SR J Hk K0. unfold aregions_justified in J. rewrite SR in J. cbv zeta in J.
  pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) J k r Hk) as Jk. clear J.
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  assert (KZ : PrimInt63.eqb k 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  unfold aregion_just in Jk. rewrite KZ in Jk.
  destruct (PrimInt63.eqb k ks) eqn:KS.
  { left. apply Uint63.eqb_correct in KS. split; [exact KS|]. exact (below_top_sound E st ms mo k r HS Hk K0 Jk). }
  assert (NKS : k <> ks) by (apply Uint63.eqb_false_spec; exact KS).
  right. split; [exact NKS|].

  set (SJ := stack_side_just (s_facts st) (getr st X2) (sp_below_anchor_t (s_facts st) (getr st X2)) ks k r) in *.
  set (VJ := view_just (s_facts st) (s_regs st) (getr st X2) (sp_below_anchor_t (s_facts st) (getr st X2)) wnl ks (stack_wlo st) k r) in *.
  set (SL := sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k r) in *.
  assert (REST : (if rg_w r then (if (if SL then true else SJ) then true else VJ) else (if (if VJ then true else SJ) then true else SL)) = true ->
            (bv_unsigned (den E (getr st X2)) <= bv_unsigned (ev E k) + loZ r /\ bv_unsigned (ev E k) + hiZ E r <= 2 ^ 47)
            \/ (VJ = true \/ SL = true)).
  { intros H. destruct SJ eqn:SJE.
    - left. destruct (stack_side_just_sound E st ms mo ks k r HS Hk K0 SJE) as [[X|X] TOP]; [contradiction| split; assumption].
    - right. destruct (rg_w r), VJ, SL; cbn in H; try discriminate H; auto. }
  destruct (CtrA.win_lookup wnl k) as [[len kd]|] eqn:WL.
  - match type of Jk with (if ?c then _ else _) = _ => destruct c eqn:INW end.
    + left. apply andb_prop in INW as [L0 LE]. apply Uint63.eqb_correct in L0. exists len, kd. split; [reflexivity|].
      split; [unfold loZ; rewrite L0; reflexivity|].
      apply orb_prop in LE as [LE|LE]; [apply orb_prop in LE as [LE|LE]; [apply orb_prop in LE as [LE|LE]; [apply orb_prop in LE as [LE|LE]|]|]|].
      * apply sv_eqb_eq in LE. unfold hiZ. rewrite LE. lia.
      * unfold hiZ. exact (vec_hi_in_sound E _ _ _ HF LE).
      * unfold hiZ. exact (pair_main_in_sound E _ _ _ _ _ HF LE).
      * unfold hiZ. exact (twin_full_in_sound E _ _ _ HF LE).
      * exact (KnownA.TwinB.KnownA.known_leu_q_sound E _ _ _ HF LE).
    + right. exact (REST Jk).
  - right. exact (REST Jk).
Qed.

Lemma stack_window_key_In : forall E n rest wlo, stack_window_key n rest = Some wlo ->
  exists len, In (HeapOp.Win (bv_unsigned (den E (VP STACK_ID wlo))) len HeapOp.K_STACK) (wins_of E n rest).
Proof.
  intros E n. induction n as [|n IH]; intros rest wlo H; [cbn in H; destruct rest; discriminate|].
  destruct rest as [|lo rest1]; [cbn in H; discriminate|].
  destruct rest1 as [|len rest2]; [destruct lo; cbn in H; discriminate|].
  destruct rest2 as [|kd rest']; [destruct lo; cbn in H; discriminate|].
  cbn [stack_window_key] in H.
  assert (STEP : stack_window_key n rest' = Some wlo ->
            exists len0, In (HeapOp.Win (bv_unsigned (den E (VP STACK_ID wlo))) len0 HeapOp.K_STACK) (wins_of E (S n) (lo :: len :: kd :: rest'))).
  { intros H'. destruct (IH rest' wlo H') as (len0 & K3). exists len0. rewrite wins_of_cons. right. exact K3. }
  destruct lo as [|k wlo0| | | | | | | | |]; cbn in H; try (apply STEP; exact H).
  destruct kd as [kdw| | | | | | | | | |]; cbn in H; try (apply STEP; exact H).
  destruct (PrimInt63.eqb k STACK_ID && weqb kdw wzero) eqn:C; [| apply STEP; exact H].
  injection H as ->. apply andb_prop in C as [H1 H2]. apply Uint63.eqb_correct in H1. subst k.
  exists (bv_unsigned (den E len)). rewrite wins_of_cons. left.
  unfold HeapOp.K_STACK. rewrite (unsigned_VL E kdw), (HeapCtr.TwinB.weqb_wzero_unsigned' kdw H2). reflexivity.
Qed.

Lemma sp_floor_sound : forall E st ms mo hargs n md A nw rest k off r,
  st_ok segs OPS E st ms mo -> sp_floor_ok st hargs = true ->
  heap_nwin hargs = Some n -> hargs = VL md :: A :: VL nw :: rest -> sp_region st = Some (k, off, r) ->
  0 <= bv_unsigned (ev E k) + loZ r ->
  exists wlo len, In (HeapOp.Win (bv_unsigned (den E (VP STACK_ID wlo))) len HeapOp.K_STACK) (wins_of E n rest)
    /\ bv_unsigned (den E (VP STACK_ID wlo)) <= bv_unsigned (ev E k) + loZ r.
Proof.
  intros E st ms mo hargs n md A nw rest k off r HS H Hn Eh SR LO0. unfold sp_floor_ok in H. rewrite Hn, Eh, SR in H.
  destruct (stack_window_key n rest) as [wlo|] eqn:SK; [|discriminate].
  destruct (okey wlo) as [kw|] eqn:KW; [|discriminate].
  apply andb_prop in H as [NW H].
  pose proof (so_facts _ _ _ _ _ _ HS) as HF. pose proof (so_zero _ _ _ _ _ _ HS) as HZ.
  destruct (nowrap_kb_sound E _ HF STACK_ID wlo NW) as [R1 D1].
  destruct (okey_sound _ _ KW) as [EKW _].
  destruct (stack_window_key_In E n rest wlo SK) as (len & IN).
  exists wlo, len. split; [exact IN|]. rewrite D1, <- EKW.
  destruct (PrimInt63.eqb k STACK_ID) eqn:K1.
  - apply Uint63.eqb_correct in K1. subst k. rewrite kleb_keyZ in H. apply Z.leb_le in H. unfold loZ. lia.
  - destruct (GTwinSub.GTwinSub.find_lb (s_facts st) k STACK_ID) as [o2|] eqn:FL; [|discriminate].
    apply andb_prop in H as [NW2 LE]. apply Z.leb_le in LE.
    destruct (nowrap_kb_sound E _ HF STACK_ID o2 NW2) as [R2 D2].
    pose proof (GTwinSub.GTwinSub.find_lb_holds E _ k STACK_ID o2 HF FL) as LB. rewrite D2, HeapCtr.TwinB.den_VPz in LB. unfold loZ. lia.
Qed.

Lemma sp_altop_sound : forall E st ms mo hargs n md A nw rest,
  st_ok segs OPS E st ms mo -> sp_altop_ok st hargs = true ->
  heap_nwin hargs = Some n -> hargs = VL md :: A :: VL nw :: rest ->
  exists wlo len, stack_window_key n rest = Some wlo
    /\ In (HeapOp.Win (bv_unsigned (den E (VP STACK_ID wlo))) len HeapOp.K_STACK) (wins_of E n rest)
    /\ bv_unsigned (den E (getr st X2)) - bv_unsigned (den E (VP STACK_ID wlo)) <= SPALT.
Proof.
  intros E st ms mo hargs n md A nw rest HS H Hn Eh. unfold sp_altop_ok in H. rewrite Hn, Eh in H.
  destruct (getr st X2) as [|k off| | | | | | | | |] eqn:GX; try discriminate.
  destruct (stack_window_key n rest) as [wlo|] eqn:SK; [|discriminate].
  apply andb_prop in H as [H ARM]. apply andb_prop in H as [NW1 NW2].
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  destruct (nowrap_kb_sound E _ HF STACK_ID wlo NW1) as [R1 D1]. destruct (nowrap_kb_sound E _ HF k off NW2) as [R2 D2].
  destruct (stack_window_key_In E n rest wlo SK) as (len & IN). exists wlo, len. split; [reflexivity|]. split; [exact IN|]. rewrite D1, D2.
  destruct (PrimInt63.eqb k STACK_ID) eqn:K1.
  - apply Uint63.eqb_correct in K1. subst k. apply Z.leb_le in ARM. lia.
  - destruct (GTwinSub.GTwinSub.find_ub (s_facts st) k) as [[kb o1]|] eqn:UB; [|discriminate].
    apply andb_prop in ARM as [ARM LE]. apply andb_prop in ARM as [KB NW3]. apply Uint63.eqb_correct in KB. subst kb. apply Z.leb_le in LE.
    destruct (nowrap_kb_sound E _ HF STACK_ID o1 NW3) as [R3 D3].
    pose proof (GTwinSub.GTwinSub.find_ub_holds E _ k STACK_ID o1 HF UB) as U. rewrite D3, HeapCtr.TwinB.den_VPz in U. lia.
Qed.

Lemma sp_floor_key : forall E st ms mo hargs n md A nw rest k off r wlo,
  st_ok segs OPS E st ms mo -> sp_floor_ok st hargs = true ->
  heap_nwin hargs = Some n -> hargs = VL md :: A :: VL nw :: rest -> sp_region st = Some (k, off, r) ->
  stack_window_key n rest = Some wlo ->
  bv_unsigned (den E (VP STACK_ID wlo)) <= bv_unsigned (ev E k) + loZ r.
Proof.
  intros E st ms mo hargs n md A nw rest k off r wlo HS H Hn Eh SR SK. unfold sp_floor_ok in H. rewrite Hn, Eh, SR, SK in H.
  destruct (okey wlo) as [kw|] eqn:KW; [|discriminate].
  apply andb_prop in H as [NW H].
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  destruct (nowrap_kb_sound E _ HF STACK_ID wlo NW) as [R1 D1].
  destruct (okey_sound _ _ KW) as [EKW _]. rewrite D1, <- EKW.
  destruct (PrimInt63.eqb k STACK_ID) eqn:K1.
  - apply Uint63.eqb_correct in K1. subst k. rewrite kleb_keyZ in H. apply Z.leb_le in H. unfold loZ. lia.
  - destruct (GTwinSub.GTwinSub.find_lb (s_facts st) k STACK_ID) as [o2|] eqn:FL; [|discriminate].
    apply andb_prop in H as [NW2 LE]. apply Z.leb_le in LE.
    destruct (nowrap_kb_sound E _ HF STACK_ID o2 NW2) as [R2 D2].
    pose proof (GTwinSub.GTwinSub.find_lb_holds E _ k STACK_ID o2 HF FL) as LB. rewrite D2, HeapCtr.TwinB.den_VPz in LB. unfold loZ. lia.
Qed.

Lemma cell_eqb_eq : forall a b, cell_eqb a b = true -> a = b.
Proof.
  intros [i w v] [i' w' v'] H. unfold cell_eqb in H. cbn [c_idx c_w c_v] in H. apply andb_prop in H as [H V]. apply andb_prop in H as [I W].
  apply Uint63.eqb_correct in I. apply Uint63.eqb_correct in W. apply sv_eqb_eq in V. subst. reflexivity.
Qed.
Lemma slot_eqb_eq : forall a b, slot_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply cell_eqb_eq in H1. subst y. f_equal. exact (IH b H2).
Qed.
Lemma grans_eqb_eq : forall a b, grans_eqb a b = true -> a = b.
Proof.
  induction a as [|[k g] a IH]; intros [|[k' g'] b] H; cbn [grans_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Uint63.eqb_correct in H1. subst k'.
  unfold gran_eqb in H2. apply andb_prop in H2 as [D C]. apply Bool.eqb_prop in D. apply slot_eqb_eq in C.
  destruct g as [d c], g' as [d' c']. cbn [g_dirty g_cells] in D, C. subst. f_equal. exact (IH b H3).
Qed.

Lemma in_granule_1 : forall o, in_granule o 1%uint63 = true.
Proof.
  intros o. unfold in_granule. apply Uint63.leb_spec. destruct (gidx_ok o) as [_ R].
  rewrite Uint63.add_spec. change (to_Z 1%uint63) with 1. change (to_Z 8%uint63) with 8.
  rewrite Z.mod_small; [lia|]. pose proof wB_pos. change wB with (2 ^ 63) in *. lia.
Qed.

Lemma twin_region_cells : forall n,
  rg_cells (twin_region n) = IMap.empty
  \/ exists w, n = VL w /\ PrimInt63.eqb (PrimInt63.land (wl w) 7%uint63) 0%uint63 = false
       /\ rg_cells (twin_region n) = IMap.add (granule (PrimInt63.lsr (wl w) 3%uint63))
                                        (Gran false [Cell (gidx (PrimInt63.lsr (wl w) 3%uint63)) 1%uint63 (VL (wlit (PrimInt63.land (wl w) 7%uint63)))]) IMap.empty.
Proof.
  intros n. destruct n as [w| | | | | | | | | |]; try (left; reflexivity).
  unfold twin_region. cbv zeta. destruct (PrimInt63.eqb (PrimInt63.land (wl w) 7%uint63) 0%uint63) eqn:T0; [left; reflexivity|].
  right. exists w. split; [reflexivity|]. split; [exact T0|].
  unfold region_store. rewrite in_granule_1. unfold region_store1. cbn [rg_cells IMap.find IMap.empty]. reflexivity.
Qed.
Lemma twin_region_hi : forall n, rg_hi (twin_region n) = twin_len n.
Proof.
  intros n. destruct n as [w| | | | | | | | | |]; try reflexivity.
  unfold twin_region. cbv zeta. destruct (PrimInt63.eqb (PrimInt63.land (wl w) 7%uint63) 0%uint63); [reflexivity|].
  unfold region_store. rewrite in_granule_1. unfold region_store1. cbn [rg_cells IMap.find IMap.empty]. reflexivity.
Qed.

Lemma len_is_twin_refl : forall fs n, len_is_twin fs (twin_len n) n = true.
Proof. intros fs n. unfold len_is_twin. rewrite ValP.sv_eqb_refl. reflexivity. Qed.
Lemma len_is_twin_sound : forall E fs len n, facts_hold E fs -> len_is_twin fs len n = true -> bv_unsigned (den E n) + 7 < 2 ^ 62 ->
  bv_unsigned (den E len) = (bv_unsigned (den E n) + 7) / 8.
Proof.
  intros E fs len n HF H B. unfold len_is_twin in H. apply orb_prop in H as [H|H].
  - apply sv_eqb_eq in H. subst len. apply twin_len_den. exact B.
  - destruct (tie_of fs len) as [xs|] eqn:TIE; [|discriminate H]. apply andb_prop in H as [EQ D8]. apply sv_eqb_eq in EQ. subst xs.
    rewrite (tie_of_holds E fs len n HF TIE). pose proof (div8x_holds E fs n HF D8) as M. clear - M. Z.div_mod_to_equations. lia.
Qed.

Lemma is_twin_region_sound : forall priv E m sh r n,
  region_ok segs priv E m sh r -> PrimInt63.eqb sh 0%uint63 = false ->
  is_twin_region r n = true ->
  bv_unsigned (den E n) + 7 < 2 ^ 62 ->
  match n with VL _ => True | _ => bv_unsigned (den E n) mod 8 = 0 end ->
  forall g, 0 <= g -> 8 * g < bv_unsigned (den E n) ->
    rb segs m (bv_unsigned (ev E sh) + g)
    = Some (Z_to_bv 8 (if 8 * g + 8 <=? bv_unsigned (den E n) then 0 else bv_unsigned (den E n) - 8 * g)).
Proof.
  intros priv E m sh r n RO NZ H B SHAPE g G0 G1. set (N := bv_unsigned (den E n)) in *.
  unfold is_twin_region in H. cbv zeta in H. do 4 (apply andb_prop in H as [H ?]).
  rename H into LO, H3 into HI, H2 into WR, H1 into BG, H0 into CE.
  apply Uint63.eqb_correct in LO. apply sv_eqb_eq in HI. rewrite twin_region_hi in HI.
  destruct (rg_bg r) eqn:BGE; try discriminate BG. clear BG.
  apply grans_eqb_eq in CE.
  assert (HIZ : hiZ E r = (N + 7) / 8) by (unfold hiZ; rewrite HI; apply twin_len_den; exact B).
  assert (LOZ : loZ r = 0) by (unfold loZ; rewrite LO; reflexivity).
  assert (GIN : loZ r <= g < hiZ E r) by (rewrite LOZ, HIZ; clear - G0 G1; Z.div_mod_to_equations; lia).

  assert (BT : IMap.bst (rg_cells (twin_region n))).
  { destruct (twin_region_cells n) as [->|(w & _ & _ & ->)]; [apply IMap.bst_empty| apply IMap.bst_add; apply IMap.bst_empty]. }
  assert (FE : forall gk, IMap.find gk (rg_cells r) = IMap.find gk (rg_cells (twin_region n))).
  { intros gk. apply IMap.option_ext. intros gr. rewrite <- (IMap.elements_spec gk gr _ (ro_bst _ _ _ _ _ _ RO)), <- (IMap.elements_spec gk gr _ BT), CE. reflexivity. }
  destruct (twin_region_cells n) as [EMP|(w & -> & T0 & CELLS)].
  -
    assert (UNC : uncovered r g). { intros gk gr _ F. rewrite FE, EMP, IMap.find_empty in F. discriminate. }
    pose proof (ro_bg _ _ _ _ _ _ RO g (fun _ => GIN) ltac:(intros X; rewrite X in NZ; discriminate) UNC) as BGB.
    unfold bg_byte in BGB. rewrite BGE in BGB. rewrite BGB. do 2 f_equal.
    destruct (Z.leb_spec (8 * g + 8) N) as [|GT]; [reflexivity| exfalso].
    destruct n as [w| | | | | | | | | |]; try (clear - SHAPE G1 GT; Z.div_mod_to_equations; lia).

    unfold twin_region in EMP. cbv zeta in EMP.
    destruct (PrimInt63.eqb (PrimInt63.land (wl w) 7%uint63) 0%uint63) eqn:T0.
    + apply Uint63.eqb_correct in T0. pose proof (gidx_ok (wl w)) as [GI _]. unfold gidx in GI. rewrite T0 in GI. change (to_Z 0%uint63) with 0 in GI.
      subst N. rewrite unsigned_VL in *. assert (WT : wt w = false) by (rewrite w2Z_wt; apply Z.leb_gt; unfold two63; lia).
      rewrite (w2Z_nowt w WT) in *. clear - GI G1 GT. Z.div_mod_to_equations. lia.
    + unfold region_store in EMP. rewrite in_granule_1 in EMP. unfold region_store1 in EMP. cbn [rg_cells IMap.find IMap.empty] in EMP.
      exfalso. clear - EMP. unfold IMap.add, IMap.empty in EMP. cbn in EMP. discriminate EMP.
  -
    subst N. rewrite unsigned_VL in *. assert (WT : wt w = false) by (rewrite w2Z_wt; apply Z.leb_gt; unfold two63; lia).
    rewrite (w2Z_nowt w WT) in *. set (N := to_Z (wl w)) in *. set (o := PrimInt63.lsr (wl w) 3%uint63) in *.
    assert (EO : to_Z o = N / 8) by (unfold o; rewrite lsr_spec; reflexivity).
    assert (KO : keyZ o = N / 8).
    { destruct (keyZ_cases o) as [[_ ->]|[X _]]; [exact EO|]. exfalso. rewrite EO in X. clear - X B. Z.div_mod_to_equations. lia. }
    assert (N0 : 0 <= N) by (pose proof (int_range (wl w)); unfold N; lia).
    destruct (granule_gidx o ltac:(rewrite KO; unfold two63; clear - B N0; Z.div_mod_to_equations; lia)) as [GG GR].
    assert (T0Z : to_Z (PrimInt63.land (wl w) 7%uint63) = N mod 8) by (pose proof (gidx_ok (wl w)) as [GI _]; exact GI).
    assert (T0NZ : N mod 8 <> 0).
    { intros X. rewrite <- T0Z in X. apply Uint63.eqb_false_spec in T0. apply T0. apply to_Z_inj. rewrite X. reflexivity. }
    destruct (Z.eq_dec g (N / 8)) as [GE|GNE].
    +
      pose proof (ro_cells _ _ _ _ _ _ RO (granule o) _ ltac:(rewrite FE, CELLS; apply IMap.find_add_same; apply IMap.bst_empty)) as [_ FC].
      cbn [g_cells] in FC. apply Forall_inv in FC. destruct FC as (_ & _ & _ & CB). cbn [c_idx c_w c_v] in CB.
      specialize (CB 0 ltac:(change (to_Z 1%uint63) with 1; lia)).
      replace (bv_unsigned (ev E sh) + 8 * keyZ (granule o) + to_Z (gidx o) + 0) with (bv_unsigned (ev E sh) + g) in CB by (rewrite GE, <- KO, GG; lia).
      rewrite CB. do 2 f_equal. unfold byte_of. rewrite den_VL, wbv_unsigned, wlit_ok, T0Z. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
      destruct (Z.leb_spec (8 * g + 8) N) as [LE|GT]; [exfalso; clear - LE GE; Z.div_mod_to_equations; lia|].
      cbv iota. f_equal. clear - GE. Z.div_mod_to_equations. lia.
    +
      assert (UNC : uncovered r g).
      { intros gk gr KG F. rewrite FE, CELLS in F.
        destruct (Uint63.eqb (granule o) gk) eqn:Q.
        - apply Uint63.eqb_correct in Q. subst gk. rewrite IMap.find_add_same in F by apply IMap.bst_empty. injection F as <-.
          cbn [g_dirty g_cells]. split; [reflexivity|]. constructor; [|constructor]. unfold covers. cbn [c_idx c_w]. change (to_Z 1%uint63) with 1.
          intros CV. apply GNE. rewrite <- KO, GG, KG. clear - CV. Z.div_mod_to_equations. lia.
        - rewrite IMap.find_add_other_eqb in F by (apply IMap.bst_empty || exact Q). rewrite IMap.find_empty in F. discriminate. }
      pose proof (ro_bg _ _ _ _ _ _ RO g (fun _ => GIN) ltac:(intros X; rewrite X in NZ; discriminate) UNC) as BGB.
      unfold bg_byte in BGB. rewrite BGE in BGB. rewrite BGB. do 2 f_equal.
      destruct (Z.leb_spec (8 * g + 8) N) as [|GT]; [reflexivity| exfalso]. clear - GNE G1 GT. Z.div_mod_to_equations. lia.
Qed.

Lemma twin_region_fields : forall n,
  rg_lo (twin_region n) = 0%uint63 /\ rg_w (twin_region n) = false /\ rg_bg (twin_region n) = BGZero.
Proof.
  intros n. destruct n as [w| | | | | | | | | |]; try (repeat split; reflexivity).
  unfold twin_region. cbv zeta. destruct (PrimInt63.eqb (PrimInt63.land (wl w) 7%uint63) 0%uint63); [repeat split; reflexivity|].
  unfold region_store. rewrite in_granule_1. unfold region_store1. cbn [rg_cells IMap.find IMap.empty]. repeat split; reflexivity.
Qed.

Lemma twin_region_ok : forall priv E m sh n,
  PrimInt63.eqb sh 0%uint63 = false ->
  1 <= bv_unsigned (den E n) -> bv_unsigned (den E n) + 7 < 2 ^ 62 ->
  match n with VL _ => True | _ => bv_unsigned (den E n) mod 8 = 0 end ->
  bv_unsigned (ev E sh) + (bv_unsigned (den E n) + 7) / 8 < two64 ->
  (forall g, 0 <= g -> 8 * g < bv_unsigned (den E n) ->
      rb segs m (bv_unsigned (ev E sh) + g) = Some (Z_to_bv 8 (if 8 * g + 8 <=? bv_unsigned (den E n) then 0 else bv_unsigned (den E n) - 8 * g))
      /\ find_segment segs (bv_unsigned (ev E sh) + g) 1 = None) ->
  region_ok segs priv E m sh (twin_region n).
Proof.
  intros priv E m sh n NZ N1 B SHAPE HI64 PAT. set (N := bv_unsigned (den E n)) in *.
  destruct (twin_region_fields n) as (LO & WR & BG).
  assert (HIZ : hiZ E (twin_region n) = (N + 7) / 8) by (unfold hiZ; rewrite twin_region_hi; apply twin_len_den; exact B).
  assert (LOZ : loZ (twin_region n) = 0) by (unfold loZ; rewrite LO; reflexivity).
  assert (BT : IMap.bst (rg_cells (twin_region n))).
  { destruct (twin_region_cells n) as [->|(w & _ & _ & ->)]; [apply IMap.bst_empty| apply IMap.bst_add; apply IMap.bst_empty]. }
  assert (GR : forall o, 0 <= o < (N + 7) / 8 -> 0 <= o /\ 8 * o < N) by (intros o Ho; split; [lia|]; clear - Ho; Z.div_mod_to_equations; lia).
  pose proof (bv_unsigned_in_range 64 (ev E sh)) as RSH.
  constructor.
  - exact BT.
  - intros _. rewrite LOZ, HIZ. lia.
  - intros _ a Ha. rewrite LOZ, HIZ in Ha. destruct (GR (a - bv_unsigned (ev E sh)) ltac:(lia)) as [G0 G1].
    destruct (PAT _ G0 G1) as [P1 P2]. replace (bv_unsigned (ev E sh) + (a - bv_unsigned (ev E sh))) with a in P1, P2 by lia.
    split; [rewrite P1; discriminate|]. split; [rewrite WR; discriminate| exact P2].
  -
    intros g gr F. destruct (twin_region_cells n) as [EMP|(w & -> & T0 & CELLS)]; [rewrite EMP, IMap.find_empty in F; discriminate|].
    rewrite CELLS in F. subst N. rewrite unsigned_VL in *.
    assert (WT : wt w = false) by (rewrite w2Z_wt; apply Z.leb_gt; unfold two63; lia). rewrite (w2Z_nowt w WT) in *.
    set (N := to_Z (wl w)) in *. set (o := PrimInt63.lsr (wl w) 3%uint63) in *.
    destruct (Uint63.eqb (granule o) g) eqn:Q; [| rewrite IMap.find_add_other_eqb in F by (apply IMap.bst_empty || exact Q); rewrite IMap.find_empty in F; discriminate].
    apply Uint63.eqb_correct in Q. subst g. rewrite IMap.find_add_same in F by apply IMap.bst_empty. injection F as <-. cbn [g_cells].
    assert (EO : to_Z o = N / 8) by (unfold o; rewrite lsr_spec; reflexivity).
    assert (KO : keyZ o = N / 8).
    { destruct (keyZ_cases o) as [[_ ->]|[X _]]; [exact EO|]. exfalso. rewrite EO in X. clear - X B. Z.div_mod_to_equations. lia. }
    destruct (granule_gidx o ltac:(rewrite KO; unfold two63; clear - B N1; Z.div_mod_to_equations; lia)) as [GG GRR].
    assert (T0Z : to_Z (PrimInt63.land (wl w) 7%uint63) = N mod 8) by (pose proof (gidx_ok (wl w)) as [GI _]; exact GI).
    assert (T0NZ : N mod 8 <> 0).
    { intros X. rewrite <- T0Z in X. apply Uint63.eqb_false_spec in T0. apply T0. apply to_Z_inj. rewrite X. reflexivity. }
    split; [cbn; auto|]. constructor; [|constructor]. unfold cell_ok. cbn [c_idx c_w c_v]. change (to_Z 1%uint63) with 1.
    split; [lia|]. split; [lia|]. split; [lia|]. intros i Hi. assert (i = 0) by lia. subst i.
    destruct (PAT (N / 8) ltac:(clear - N1; Z.div_mod_to_equations; lia) ltac:(clear - T0NZ; Z.div_mod_to_equations; lia)) as [P1 _].
    replace (bv_unsigned (ev E sh) + 8 * keyZ (granule o) + to_Z (gidx o) + 0) with (bv_unsigned (ev E sh) + N / 8) by (rewrite <- KO, GG; lia).
    rewrite P1. do 2 f_equal. unfold byte_of. rewrite den_VL, wbv_unsigned, wlit_ok, T0Z. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
    destruct (Z.leb_spec (8 * (N / 8) + 8) N) as [LE|GT]; [exfalso; clear - LE; Z.div_mod_to_equations; lia|].
    cbv iota. f_equal. clear - N1. Z.div_mod_to_equations. lia.
  -
    intros g gr c i F Hc Hi. cbv zeta. split; [| intros X; rewrite X in NZ; discriminate]. intros _.
    destruct (twin_region_cells n) as [EMP|(w & -> & T0 & CELLS)]; [rewrite EMP, IMap.find_empty in F; discriminate|].
    rewrite CELLS in F. subst N. rewrite unsigned_VL in *.
    assert (WT : wt w = false) by (rewrite w2Z_wt; apply Z.leb_gt; unfold two63; lia). rewrite (w2Z_nowt w WT) in *.
    set (N := to_Z (wl w)) in *. set (o := PrimInt63.lsr (wl w) 3%uint63) in *.
    destruct (Uint63.eqb (granule o) g) eqn:Q; [| rewrite IMap.find_add_other_eqb in F by (apply IMap.bst_empty || exact Q); rewrite IMap.find_empty in F; discriminate].
    apply Uint63.eqb_correct in Q. subst g. rewrite IMap.find_add_same in F by apply IMap.bst_empty. injection F as <-. cbn [g_cells] in Hc.
    destruct Hc as [<-|[]]. cbn [c_idx c_w] in *. change (to_Z 1%uint63) with 1 in Hi. assert (i = 0) by lia. subst i.
    assert (EO : to_Z o = N / 8) by (unfold o; rewrite lsr_spec; reflexivity).
    assert (KO : keyZ o = N / 8).
    { destruct (keyZ_cases o) as [[_ ->]|[X _]]; [exact EO|]. exfalso. rewrite EO in X. clear - X B. Z.div_mod_to_equations. lia. }
    destruct (granule_gidx o ltac:(rewrite KO; unfold two63; clear - B N1; Z.div_mod_to_equations; lia)) as [GG GRR].
    assert (T0Z : to_Z (PrimInt63.land (wl w) 7%uint63) = N mod 8) by (pose proof (gidx_ok (wl w)) as [GI _]; exact GI).
    assert (T0NZ : N mod 8 <> 0).
    { intros X. rewrite <- T0Z in X. apply Uint63.eqb_false_spec in T0. apply T0. apply to_Z_inj. rewrite X. reflexivity. }
    rewrite LOZ, HIZ. replace (8 * keyZ (granule o) + to_Z (gidx o) + 0) with (N / 8) by (rewrite <- KO, GG; lia).
    clear - T0NZ N1. Z.div_mod_to_equations. lia.
  -
    intros o R1 _ UNC. specialize (R1 NZ). rewrite LOZ, HIZ in R1. unfold bg_byte. rewrite BG.
    destruct (GR o R1) as [G0 G1]. destruct (PAT o G0 G1) as [P1 _]. rewrite P1. do 2 f_equal.
    destruct (Z.leb_spec (8 * o + 8) N) as [|GT]; [reflexivity| exfalso].
    destruct (twin_region_cells n) as [EMP|(w & -> & T0 & CELLS)].
    + destruct n as [w| | | | | | | | | |]; try (clear - SHAPE G1 GT; Z.div_mod_to_equations; lia).
      unfold twin_region in EMP. cbv zeta in EMP.
      destruct (PrimInt63.eqb (PrimInt63.land (wl w) 7%uint63) 0%uint63) eqn:T0.
      * apply Uint63.eqb_correct in T0. pose proof (gidx_ok (wl w)) as [GI _]. unfold gidx in GI. rewrite T0 in GI. change (to_Z 0%uint63) with 0 in GI.
        subst N. rewrite unsigned_VL in *. assert (WT : wt w = false) by (rewrite w2Z_wt; apply Z.leb_gt; unfold two63; lia).
        rewrite (w2Z_nowt w WT) in *. clear - GI G1 GT. Z.div_mod_to_equations. lia.
      * unfold region_store in EMP. rewrite in_granule_1 in EMP. unfold region_store1 in EMP. cbn [rg_cells IMap.find IMap.empty] in EMP.
        clear - EMP. unfold IMap.add, IMap.empty in EMP. cbn in EMP. discriminate EMP.
    +
      subst N. rewrite unsigned_VL in *. assert (WT : wt w = false) by (rewrite w2Z_wt; apply Z.leb_gt; unfold two63; lia).
      rewrite (w2Z_nowt w WT) in *. set (N := to_Z (wl w)) in *. set (o0 := PrimInt63.lsr (wl w) 3%uint63) in *.
      assert (EO : to_Z o0 = N / 8) by (unfold o0; rewrite lsr_spec; reflexivity).
      assert (KO : keyZ o0 = N / 8).
      { destruct (keyZ_cases o0) as [[_ ->]|[X _]]; [exact EO|]. exfalso. rewrite EO in X. clear - X B. Z.div_mod_to_equations. lia. }
      destruct (granule_gidx o0 ltac:(rewrite KO; unfold two63; clear - B N1; Z.div_mod_to_equations; lia)) as [GG GRR].
      assert (OE : o = N / 8) by (clear - G1 GT; Z.div_mod_to_equations; lia).
      destruct (UNC (granule o0) _ ltac:(rewrite OE, <- KO, GG; clear - GRR; Z.div_mod_to_equations; lia)
                    ltac:(rewrite CELLS; apply IMap.find_add_same; apply IMap.bst_empty)) as [_ FC].
      cbn [g_cells] in FC. apply Forall_inv in FC. apply FC. unfold covers. cbn [c_idx c_w]. change (to_Z 1%uint63) with 1.
      rewrite OE, <- KO, GG. clear - GRR. Z.div_mod_to_equations. lia.
Qed.

Lemma tail_region_fields : forall n,
  rg_lo (tail_region n) = 0%uint63 /\ rg_hi (tail_region n) = VL wone /\ rg_w (tail_region n) = false /\ rg_bg (tail_region n) = BGZero
  /\ rg_cells (tail_region n) = IMap.add (granule 0%uint63) (Gran false [Cell (gidx 0%uint63) 1%uint63 (sz_and7 n)]) IMap.empty.
Proof.
  intros n. unfold tail_region, region_store. rewrite in_granule_1. unfold region_store1. cbn [rg_cells IMap.find IMap.empty rg_lo rg_hi rg_w rg_bg].
  repeat split; reflexivity.
Qed.
Lemma region_is_inv : forall r t, region_is r t = true ->
  rg_lo r = rg_lo t /\ rg_hi r = rg_hi t /\ rg_w r = rg_w t /\ rg_bg r = BGZero /\ rg_bg t = BGZero
  /\ IMap.elements (rg_cells r) = IMap.elements (rg_cells t).
Proof.
  intros r t H. unfold region_is in H. do 4 (apply andb_prop in H as [H ?]).
  apply Uint63.eqb_correct in H. apply sv_eqb_eq in H3. apply Bool.eqb_prop in H2. apply grans_eqb_eq in H0.
  destruct (rg_bg r), (rg_bg t); try discriminate H1. repeat split; assumption.
Qed.
Lemma find_tail_sound : forall E fs sh n s2, facts_hold E fs -> find_tail fs sh n = Some s2 -> ev E s2 = den E (tail_rhs sh n).
Proof.
  intros E fs sh n s2 HF H. unfold find_tail in H. induction fs as [|f fs IH]; [discriminate H|].
  apply Forall_cons_iff in HF as [Hf HF].
  destruct f as [| | | |a b| | |]; try (apply IH; assumption).
  destruct a as [|s z| | | | | | | | |]; try (apply IH; assumption).
  destruct (weqb z wzero && sv_eqb b (tail_rhs sh n)) eqn:Q; [| apply IH; assumption].
  injection H as <-. apply andb_prop in Q as [Z0 B0]. apply weqb_eq in Z0. apply sv_eqb_eq in B0. subst z b.
  cbn [fact_holds] in Hf. rewrite HeapCtr.TwinB.den_VPz in Hf. exact Hf.
Qed.
Lemma tail_rhs_den : forall E sh n, 1 <= bv_unsigned (den E n) -> bv_unsigned (ev E sh) + (bv_unsigned (den E n) - 1) / 8 < 2 ^ 64 ->
  bv_unsigned (den E (tail_rhs sh n)) = bv_unsigned (ev E sh) + (bv_unsigned (den E n) - 1) / 8.
Proof.
  intros E sh n N1 B. unfold tail_rhs. rewrite ValP.den_sv_alu. unfold alu64, alu. rewrite bv_add_unsigned, HeapCtr.TwinB.den_VPz, (sz_last_den E n N1).
  apply bv_wrap_small. pose proof (bv_unsigned_in_range 64 (ev E sh)). pose proof (bv_unsigned_in_range 64 (den E n)).
  change (bv_modulus 64) with (2 ^ 64) in *. split; [| exact B]. assert (0 <= (bv_unsigned (den E n) - 1) / 8) by (apply Z.div_pos; lia). lia.
Qed.
Lemma tail_scan_inv : forall fs R sh n s2, tail_scan fs R sh n = Some s2 ->
  find_tail fs sh n = Some s2 /\ s2 <> 0%uint63 /\ s2 <> sh /\ exists r2, IMap.find s2 R = Some r2 /\ is_tail_region r2 n = true.
Proof.
  intros fs R sh n s2 H. unfold tail_scan in H. destruct (find_tail fs sh n) as [s|] eqn:FT; [|discriminate H].
  destruct (IMap.find s R) as [r2|] eqn:F2; [|discriminate H].
  destruct (is_tail_region r2 n && negb (PrimInt63.eqb s 0%uint63) && negb (PrimInt63.eqb s sh)) eqn:Q; [|discriminate H].
  injection H as <-. apply andb_prop in Q as [Q NS]. apply andb_prop in Q as [TR N0]. apply negb_true_iff in NS, N0.
  apply Uint63.eqb_false_spec in NS, N0. split; [reflexivity|]. split; [exact N0|]. split; [exact NS|]. exists r2. split; [exact F2| exact TR].
Qed.

Lemma tail_region_byte : forall priv E m s2 r2 n, region_ok segs priv E m s2 r2 -> is_tail_region r2 n = true ->
  rb segs m (bv_unsigned (ev E s2)) = Some (Z_to_bv 8 (bv_unsigned (den E n) mod 8)).
Proof.
  intros priv E m s2 r2 n RO TR. destruct (region_is_inv _ _ TR) as (_ & _ & _ & _ & _ & CE).
  destruct (tail_region_fields n) as (_ & _ & _ & _ & CELLS).
  assert (BT : IMap.bst (rg_cells (tail_region n))) by (rewrite CELLS; apply IMap.bst_add; apply IMap.bst_empty).
  assert (FE : forall gk, IMap.find gk (rg_cells r2) = IMap.find gk (rg_cells (tail_region n))).
  { intros gk. apply IMap.option_ext. intros gr. rewrite <- (IMap.elements_spec gk gr _ (ro_bst _ _ _ _ _ _ RO)), <- (IMap.elements_spec gk gr _ BT), CE. reflexivity. }
  pose proof (ro_cells _ _ _ _ _ _ RO (granule 0%uint63) _ ltac:(rewrite FE, CELLS; apply IMap.find_add_same; apply IMap.bst_empty)) as [_ FC].
  cbn [g_cells] in FC. apply Forall_inv in FC. destruct FC as (_ & _ & _ & CB). cbn [c_idx c_w c_v] in CB.
  specialize (CB 0 ltac:(change (to_Z 1%uint63) with 1; lia)).
  replace (bv_unsigned (ev E s2) + 8 * keyZ (granule 0%uint63) + to_Z (gidx 0%uint63) + 0) with (bv_unsigned (ev E s2)) in CB by (vm_compute (keyZ (granule 0%uint63)); vm_compute (to_Z (gidx 0%uint63)); lia).
  rewrite CB. do 2 f_equal. unfold byte_of. rewrite sz_and7_den. change (8 * 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
Qed.

Lemma twin_main_ok : forall priv E m sh n,
  PrimInt63.eqb sh 0%uint63 = false ->
  1 <= bv_unsigned (den E n) ->
  bv_unsigned (ev E sh) + (bv_unsigned (den E n) - 1) / 8 < two64 ->
  (forall g, 0 <= g < (bv_unsigned (den E n) - 1) / 8 ->
      rb segs m (bv_unsigned (ev E sh) + g) = Some (Z_to_bv 8 0) /\ find_segment segs (bv_unsigned (ev E sh) + g) 1 = None) ->
  region_ok segs priv E m sh (twin_main n).
Proof.
  intros priv E m sh n NZ N1 HI64 PAT. set (N := bv_unsigned (den E n)) in *.
  assert (HIZ : hiZ E (twin_main n) = (N - 1) / 8) by (unfold hiZ, twin_main; cbn [rg_hi]; apply sz_last_den; exact N1).
  assert (HIP : 0 <= (N - 1) / 8) by (apply Z.div_pos; lia).
  assert (LOZ : loZ (twin_main n) = 0) by reflexivity.
  pose proof (bv_unsigned_in_range 64 (ev E sh)) as RSH.
  constructor.
  - cbn [twin_main rg_cells]. apply IMap.bst_empty.
  - intros _. rewrite LOZ, HIZ. lia.
  - intros _ a Ha. rewrite LOZ, HIZ in Ha. destruct (PAT (a - bv_unsigned (ev E sh)) ltac:(lia)) as [P1 P2].
    replace (bv_unsigned (ev E sh) + (a - bv_unsigned (ev E sh))) with a in P1, P2 by lia.
    split; [rewrite P1; discriminate|]. split; [cbn [twin_main rg_w]; discriminate| exact P2].
  - intros g gr F. cbn [twin_main rg_cells] in F. rewrite IMap.find_empty in F. discriminate.
  - intros g gr c i F. cbn [twin_main rg_cells] in F. rewrite IMap.find_empty in F. discriminate.
  - intros o R1 _ UNC. specialize (R1 NZ). rewrite LOZ, HIZ in R1. unfold bg_byte. cbn [twin_main rg_bg]. destruct (PAT o R1) as [P1 _]. exact P1.
Qed.
Lemma tail_region_ok : forall priv E m s2 n,
  PrimInt63.eqb s2 0%uint63 = false ->
  bv_unsigned (ev E s2) + 1 < two64 ->
  rb segs m (bv_unsigned (ev E s2)) = Some (Z_to_bv 8 (bv_unsigned (den E n) mod 8)) ->
  find_segment segs (bv_unsigned (ev E s2)) 1 = None ->
  region_ok segs priv E m s2 (tail_region n).
Proof.
  intros priv E m s2 n NZ HI64 BYTE SEG. destruct (tail_region_fields n) as (LO & HI & WR & BG & CELLS).
  assert (HIZ : hiZ E (tail_region n) = 1) by (unfold hiZ; rewrite HI; cbn [den]; rewrite wbv_unsigned; reflexivity).
  assert (LOZ : loZ (tail_region n) = 0) by (unfold loZ; rewrite LO; reflexivity).
  pose proof (bv_unsigned_in_range 64 (ev E s2)) as RSH.
  assert (G0 : keyZ (granule 0%uint63) = 0) by (vm_compute; reflexivity).
  assert (I0 : to_Z (gidx 0%uint63) = 0) by (vm_compute; reflexivity).
  constructor.
  - rewrite CELLS. apply IMap.bst_add. apply IMap.bst_empty.
  - intros _. rewrite LOZ, HIZ. lia.
  - intros _ a Ha. rewrite LOZ, HIZ in Ha. assert (a = bv_unsigned (ev E s2)) by lia. subst a.
    split; [rewrite BYTE; discriminate|]. split; [rewrite WR; discriminate| exact SEG].
  - intros g gr F. rewrite CELLS in F.
    destruct (Uint63.eqb (granule 0%uint63) g) eqn:Q; [| rewrite IMap.find_add_other_eqb in F by (apply IMap.bst_empty || exact Q); rewrite IMap.find_empty in F; discriminate].
    apply Uint63.eqb_correct in Q. subst g. rewrite IMap.find_add_same in F by apply IMap.bst_empty. injection F as <-. cbn [g_cells].
    split; [cbn; auto|]. constructor; [|constructor]. unfold cell_ok. cbn [c_idx c_w c_v]. change (to_Z 1%uint63) with 1.
    split; [lia|]. split; [lia|]. split; [lia|]. intros i Hi. assert (i = 0) by lia. subst i.
    replace (bv_unsigned (ev E s2) + 8 * keyZ (granule 0%uint63) + to_Z (gidx 0%uint63) + 0) with (bv_unsigned (ev E s2)) by lia.
    rewrite BYTE. do 2 f_equal. unfold byte_of. rewrite sz_and7_den. change (8 * 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - intros g gr c i F Hc Hi. cbv zeta. split; [| intros X; rewrite X in NZ; discriminate]. intros _. rewrite CELLS in F.
    destruct (Uint63.eqb (granule 0%uint63) g) eqn:Q; [| rewrite IMap.find_add_other_eqb in F by (apply IMap.bst_empty || exact Q); rewrite IMap.find_empty in F; discriminate].
    apply Uint63.eqb_correct in Q. subst g. rewrite IMap.find_add_same in F by apply IMap.bst_empty. injection F as <-. cbn [g_cells] in Hc.
    destruct Hc as [<-|[]]. cbn [c_idx c_w] in *. change (to_Z 1%uint63) with 1 in Hi. rewrite LOZ, HIZ. lia.
  - intros o R1 _ UNC. specialize (R1 NZ). rewrite LOZ, HIZ in R1. assert (o = 0) by lia. subst o. exfalso.
    destruct (UNC (granule 0%uint63) _ ltac:(lia) ltac:(rewrite CELLS; apply IMap.find_add_same; apply IMap.bst_empty)) as [_ FC].
    cbn [g_cells] in FC. apply Forall_inv in FC. apply FC. unfold covers. cbn [c_idx c_w]. change (to_Z 1%uint63) with 1. lia.
Qed.

Lemma twin_pair_sound : forall priv E m fs (R : IMap.t region) sh r n s2,
  facts_hold E fs -> (forall k rg, IMap.find k R = Some rg -> region_ok segs priv E m k rg) ->
  IMap.find sh R = Some r -> PrimInt63.eqb sh 0%uint63 = false ->
  is_twin_main r n = true -> tail_scan fs R sh n = Some s2 ->
  1 <= bv_unsigned (den E n) ->
  bv_unsigned (ev E sh) + (bv_unsigned (den E n) - 1) / 8 < 2 ^ 64 ->
  forall g, 0 <= g -> 8 * g < bv_unsigned (den E n) ->
    rb segs m (bv_unsigned (ev E sh) + g)
    = Some (Z_to_bv 8 (if 8 * g + 8 <=? bv_unsigned (den E n) then 0 else bv_unsigned (den E n) - 8 * g)).
Proof.
  intros priv E m fs R sh r n s2 HF ROK FR NZ TM TS N1 B g G0 G1. set (N := bv_unsigned (den E n)) in *.
  pose proof (ROK _ _ FR) as RO.
  destruct (region_is_inv _ _ TM) as (LO & HI & WR & BGE & _ & CE). cbn [twin_main rg_lo rg_hi rg_w rg_cells] in LO, HI, WR, CE.
  assert (HIZ : hiZ E r = (N - 1) / 8) by (unfold hiZ; rewrite HI; apply sz_last_den; exact N1).
  assert (LOZ : loZ r = 0) by (unfold loZ; rewrite LO; reflexivity).
  destruct (Z_lt_le_dec g ((N - 1) / 8)) as [BELOW|LAST].
  -
    assert (GIN : loZ r <= g < hiZ E r) by (rewrite LOZ, HIZ; lia).
    assert (UNC : uncovered r g).
    { intros gk gr _ F. rewrite <- (IMap.elements_spec gk gr _ (ro_bst _ _ _ _ _ _ RO)), CE in F. cbn in F. contradiction. }
    pose proof (ro_bg _ _ _ _ _ _ RO g (fun _ => GIN) ltac:(intros X; rewrite X in NZ; discriminate) UNC) as BGB.
    unfold bg_byte in BGB. rewrite BGE in BGB.
    replace (8 * g + 8 <=? N) with true by (symmetry; apply Z.leb_le; clear - BELOW; Z.div_mod_to_equations; lia). exact BGB.
  -
    destruct (tail_scan_inv _ _ _ _ _ TS) as (FT & S0 & SNE & r2 & F2 & TR).
    pose proof (find_tail_sound E fs sh n s2 HF FT) as EV. apply (f_equal bv_unsigned) in EV. rewrite (tail_rhs_den E sh n N1 B) in EV. fold N in EV.
    assert (GE : g = (N - 1) / 8) by (clear - G1 LAST G0; Z.div_mod_to_equations; lia).
    pose proof (tail_region_byte priv E m s2 r2 n (ROK _ _ F2) TR) as TB. fold N in TB. rewrite EV in TB. rewrite GE. rewrite TB.
    do 2 f_equal. destruct (Z.leb_spec (8 * ((N - 1) / 8) + 8) N) as [FL|PT]; [clear - N1 FL| clear - N1 PT]; Z.div_mod_to_equations; lia.
Qed.

Lemma fold_filter_inv : forall (P : int -> bool) (l : list (int * gran)) (acc : IMap.t gran), IMap.bst acc ->
  let acc' := List.fold_left (fun a kv => if P (fst kv) then a else IMap.add (fst kv) (snd kv) a) l acc in
  IMap.bst acc' /\ forall g gr, IMap.find g acc' = Some gr -> IMap.find g acc = Some gr \/ (In (g, gr) l /\ P g = false).
Proof.
  intros P l. induction l as [|[k x] l IH]; intros acc B; cbn [fold_left fst snd].
  - split; [exact B| intros g gr H; left; exact H].
  - destruct (P k) eqn:PK.
    + destruct (IH acc B) as [B' H']. split; [exact B'|]. intros g gr H. destruct (H' g gr H) as [X|[X Y]]; [left; exact X| right; split; [right; exact X| exact Y]].
    + destruct (IH (IMap.add k x acc) (IMap.bst_add k x acc B)) as [B' H']. split; [exact B'|]. intros g gr H.
      destruct (H' g gr H) as [X|[X Y]]; [| right; split; [right; exact X| exact Y]].
      destruct (Uint63.eqb k g) eqn:Q.
      * apply Uint63.eqb_correct in Q. subst g. rewrite IMap.find_add_same in X by exact B. injection X as <-. right. split; [left; reflexivity| exact PK].
      * rewrite IMap.find_add_other_eqb in X by (exact B || exact Q). left. exact X.
Qed.

Lemma region_forget_below_cells : forall r ksp, IMap.bst (rg_cells r) ->
  IMap.bst (rg_cells (region_forget_below r ksp))
  /\ forall g gr, IMap.find g (rg_cells (region_forget_below r ksp)) = Some gr ->
       IMap.find g (rg_cells r) = Some gr /\ kltb g (granule ksp) = false.
Proof.
  intros r ksp B. unfold region_forget_below. cbn [rg_cells]. rewrite IMap.fold_spec.
  destruct (fold_filter_inv (fun g => kltb g (granule ksp)) (IMap.elements (rg_cells r)) IMap.empty IMap.bst_empty) as [B' H'].
  split; [exact B'|]. intros g gr H. destruct (H' g gr H) as [X|[X Y]]; [rewrite IMap.find_empty in X; discriminate|].
  split; [apply (IMap.elements_spec g gr _ B); exact X| exact Y].
Qed.

Lemma key_range_half : forall i, - two63 / 2 <= keyZ i < two63 / 2.
Proof. intros i. pose proof (keyZ_range i). change (- two63 / 2) with (- (2 ^ 62)). rewrite half63. lia. Qed.

Lemma region_forget_below_ok : forall priv E m m' k r ksp,
  ev E 0%uint63 = Z_to_bv 64 0 ->
  region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false -> rg_bg r = BGNone ->
  keyZ ksp mod 16 = 0 ->
  let base := bv_unsigned (ev E k) in let sp := base + keyZ ksp in
  (forall a, sp <= a < base + hiZ E r -> rb segs m' a = rb segs m a /\ (wb segs m a = true -> wb segs m' a = true)) ->
  (forall a, base + loZ r <= a < sp -> rb segs m' a <> None /\ wb segs m' a = true) ->
  region_ok segs priv E m' k (region_forget_below r ksp).
Proof.
  intros priv E m m' k r ksp Hz RO KZ HBG K16. cbv zeta. intros AG BELOW.
  destruct (region_forget_below_cells r ksp (ro_bst _ _ _ _ _ _ RO)) as [B' CE].
  assert (RO' : region_ok segs priv E m k (region_forget_below r ksp)).
  { destruct RO as [Rbst Rrange Rvalid Rcells Rin Rbg]. constructor.
    - exact B'.
    - exact Rrange.
    - exact Rvalid.
    - intros g gr F. destruct (CE g gr F) as [F0 _]. exact (Rcells g gr F0).
    - intros g gr c i F. destruct (CE g gr F) as [F0 _]. exact (Rin g gr c i F0).
    - intros o _ _ _. unfold bg_byte. cbn [rg_bg region_forget_below]. rewrite HBG. exact I. }
  apply (region_ok_fine_frame segs priv E m m' k _ Hz RO').
  - intros o R1 _ CL. specialize (R1 KZ). change (loZ (region_forget_below r ksp)) with (loZ r) in R1. change (hiZ E (region_forget_below r ksp)) with (hiZ E r) in R1.
    destruct CL as [(g & gr & c & Hg & Hc & Eg & COV) | [U BG]].
    + destruct (CE g gr Hg) as [_ NLT].
      assert (LE : keyZ ksp <= o).
      { destruct (granule_gidx ksp (key_range_half _)) as [Gk Ik]. destruct (gidx_ok ksp) as [Gm _].
        assert (G0 : to_Z (gidx ksp) = 0).
        { rewrite Gm. destruct (keyZ_cases ksp) as [[_ EK]|[_ EK]]; rewrite EK in K16.
          - apply Z.mod_divide in K16; [|lia]. apply Z.mod_divide; [lia|]. destruct K16 as [q Qq]. exists (2 * q). lia.
          - replace (to_Z ksp - 2 ^ 63) with (to_Z ksp + (- 2 ^ 59) * 16) in K16 by lia. rewrite Z.mod_add in K16 by lia.
            apply Z.mod_divide in K16; [|lia]. apply Z.mod_divide; [lia|]. destruct K16 as [q Qq]. exists (2 * q). lia. }
        rewrite kltb_keyZ in NLT. apply Z.ltb_ge in NLT.
        pose proof (Z.div_mod o 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound o 8 ltac:(lia)) as MB. lia. }
      exact (proj1 (AG (bv_unsigned (ev E k) + o) ltac:(lia))).
    + exfalso. apply BG. unfold bg_byte. cbn [rg_bg region_forget_below]. rewrite HBG. reflexivity.
  - intros _ a Ha. change (loZ (region_forget_below r ksp)) with (loZ r) in Ha. change (hiZ E (region_forget_below r ksp)) with (hiZ E r) in Ha.
    destruct (Z_lt_le_dec a (bv_unsigned (ev E k) + keyZ ksp)) as [LT|GE].
    + destruct (BELOW a ltac:(lia)) as [V1 V2]. split; [exact V1|]. intros _. exact V2.
    + destruct (ro_valid _ _ _ _ _ _ RO KZ a Ha) as (V1 & V2 & _).
      destruct (AG a ltac:(lia)) as [E2 W2].
      split; [rewrite E2; exact V1|]. intros Wr. apply W2. apply V2. exact Wr.
Qed.

Lemma sec_decided_sound : forall E fs n, facts_hold E fs -> sec_decided fs n = true -> 64512 < bv_unsigned (den E n).
Proof.
  intros E fs n HF H. unfold sec_decided in H. pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF H) as LT.
  replace (bv_unsigned (den E (VL PRIM_MAXw))) with 64512 in LT by (vm_compute; reflexivity). exact LT.
Qed.
Lemma win_not_prist_sound : forall E fs l sz kd, facts_hold E fs -> win_not_prist fs l sz kd = true ->
  HeapOp.Win (bv_unsigned (den E l)) (bv_unsigned (den E sz)) (bv_unsigned (den E kd)) <> HeapOp.Win (2^47 + 2^46) 0 HeapOp.K_STACK.
Proof.
  intros E fs l sz kd HF H X. injection X as X1 X2 X3. unfold win_not_prist in H.
  destruct kd as [k0| | | | | | | | | |]; try discriminate H.
  rewrite unsigned_VL in X3. change HeapOp.K_STACK with (w2Z wzero) in X3.
  assert (KW : weqb k0 wzero = true) by (rewrite weqb_eqb; apply Z.eqb_eq; exact X3). rewrite KW in H.
  destruct sz as [z| | | | | | | | | |]; try discriminate H.
  rewrite unsigned_VL in X2. change 0 with (w2Z wzero) in X2.
  assert (ZW : weqb z wzero = true) by (rewrite weqb_eqb; apply Z.eqb_eq; exact X2). rewrite ZW in H.
  assert (SYM : KnownT.KnownT.known_ltu_t fs l (VL PRIST_BASEw) || KnownT.KnownT.known_ltu_t fs (VL PRIST_BASEw) l = true -> False).
  { intros O. apply orb_prop in O as [O|O]; pose proof (KnownA.TwinB.KnownA.known_ltu_sound E fs _ _ HF O) as Q; rewrite unsigned_VL in Q;
      change (w2Z PRIST_BASEw) with (2^47 + 2^46) in Q; lia. }
  destruct l as [a| | | | | | | | | |]; try exact (SYM H).
  rewrite unsigned_VL in X1. apply negb_true_iff in H. rewrite weqb_eqb in H. apply Z.eqb_neq in H. apply H.
  change (w2Z PRIST_BASEw) with (2^47 + 2^46). exact X1.
Qed.
Lemma wins_not_prist_sound : forall E fs, facts_hold E fs -> forall n ws, wins_not_prist fs n ws = true ->
  ~ In (HeapOp.Win (2^47 + 2^46) 0 HeapOp.K_STACK) (wins_of E n ws).
Proof.
  intros E fs HF n. induction n as [|n IH]; intros ws H Hw; [destruct ws; cbn in Hw; contradiction|].
  destruct ws as [|wlo [|ln [|kdv ws0]]]; try (cbn in H; discriminate). cbn [wins_not_prist] in H. apply andb_prop in H as [H1 H2].
  rewrite wins_of_cons in Hw. destruct Hw as [Hw|Hw]; [| exact (IH ws0 H2 Hw)].
  exact (win_not_prist_sound E fs wlo ln kdv HF H1 Hw).
Qed.

End CallA.
End TwinB.
