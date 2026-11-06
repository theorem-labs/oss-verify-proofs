(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Frame Step Omono.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Instr Plan ValProofs MemProofs StepSoundBase StepSoundMem StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree PkOps PkLib GLib PkPeek PkStep PkBody.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem State Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM LdPart.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue RegsEqv RMallocG MemcpyG CtrFX MemFX CopyFX HeapCtr MemcpyCtr LdPartSound.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St Step Plan ValP MemP StepB StepM StepS PlanS CtrLib CtrA CtrFX HeapOp UB UG TR PK PKL.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Section OPS.
Variable IMGX : list iv.
Variable AW : alloc_world rsegs IMGX.
Variable CW : client_world.
Variable OPS : St.optable.

Hypothesis OPS_plain : St.plain_table OPS.
Hypothesis HOPS : heap_ops rsegs IMGX AW CW OPS.
Hypothesis CW3 : forall ca LB ws m, cw_holds CW 3 ca LB ws m -> PK.cw_pk_holds rsegs ca LB ws m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Ltac unfT := unfold T_NIL, T_BOOLEAN, T_POSINT, T_NEGINT, T_FLOAT64, T_STR, T_BIN, T_ARRAY, T_MAP, T_EXT, T_FLOAT32 in *.

Lemma nth_map_seq : forall {A} (f : nat -> A) n j d, (j < n)%nat -> nth j (map f (seq 0 n)) d = f j.
Proof.
  intros A f n j d Hj. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hj).
  rewrite map_nth, seq_nth by exact Hj. reflexivity.
Qed.

Lemma body_of_focus : forall bm z fo t (p n : Z),
  tree_wf bm z fo -> obj_type fo = t -> (t = T_STR \/ t = T_BIN \/ t = T_EXT) -> obj_ptr fo = p -> (PK.obj_via fo = n \/ obj_cnt fo = n) ->
  let N := (if t =? T_EXT then n + 1 else n) in
  0 <= n /\ N <= LIMIT /\ (p = 0 -> N = 0) /\ (p <> 0 -> in_zone z p N /\ readable bm p (Z.to_nat N)).
Proof.
  intros bm z fo t p n TW TY HT HP HN. cbv zeta.
  destruct fo; cbn [obj_type] in TY; subst t; unfT; try (exfalso; lia); cbn [obj_ptr PK.obj_via obj_cnt] in HP, HN;
    (assert (HN' : n0 = n) by (destruct HN; assumption)); clear HN; subst;
    cbn [tree_wf] in TW; cbn [Z.eqb Pos.eqb].
  - destruct TW as (A & B & C). unfold LIMIT in *. split; [lia|]. split; [lia|]. split; [exact B| exact C].
  - destruct TW as (A & B & C). unfold LIMIT in *. split; [lia|]. split; [lia|]. split; [exact B| exact C].
  - destruct TW as (A & B & C & D & E). unfold LIMIT in *. split; [lia|]. split; [lia|].
    split; [intros P0; exfalso; exact (C P0)| intros _; split; assumption].
Qed.

Lemma w2Zs_wadd_small : forall a b, - two63 <= w2Zs a + w2Z b < two63 -> w2Zs (wadd a b) = w2Zs a + w2Z b.
Proof.
  intros a b H. rewrite (w2Zs_eq (wadd a b)), w2Z_wt, wadd_ok.
  rewrite (w2Zs_eq a), (w2Z_wt a) in H |- *.
  pose proof (w2Z_range a) as Ra. pose proof (w2Z_range b) as Rb. unfold two63, two64 in *.
  destruct (Z.leb_spec 9223372036854775808 (w2Z a));
  destruct (Z_lt_le_dec (w2Z a + w2Z b) 18446744073709551616);
  try (rewrite (Z.mod_small (w2Z a + w2Z b)) by lia; destruct (Z.leb_spec 9223372036854775808 (w2Z a + w2Z b)); lia);
  try (replace (w2Z a + w2Z b) with ((w2Z a + w2Z b - 18446744073709551616) + 1 * 18446744073709551616) by lia;
       rewrite Z.mod_add, Z.mod_small by lia;
       destruct (Z.leb_spec 9223372036854775808 (w2Z a + w2Z b - 18446744073709551616)); lia).
Qed.

Lemma cell_apart_sound : forall E fs OFF n g c,
  facts_hold E fs -> PkBody.cell_apart fs OFF n g c = true ->
  0 <= to_Z (Mem.c_idx c) -> to_Z (Mem.c_idx c) + to_Z (Mem.c_w c) <= 8 -> 0 < to_Z (Mem.c_w c) ->
  bv_unsigned (den E OFF) + bv_unsigned (den E n) < two64 ->
  keyZ g = to_Z g /\
  (8 * to_Z g + to_Z (Mem.c_idx c) + to_Z (Mem.c_w c) <= bv_unsigned (den E OFF)
   \/ bv_unsigned (den E OFF) + bv_unsigned (den E n) <= 8 * to_Z g + to_Z (Mem.c_idx c)).
Proof.
  intros E fs OFF n g c Hfs H Hi Hiw Hw NW. unfold PkBody.cell_apart in H.
  apply andb_prop in H as [GM H]. apply Uint63.ltb_spec in GM. change (to_Z PkBody.G_MAX) with (2 ^ 59) in GM.
  pose proof (int_range g) as Rg. pose proof (int_range (Mem.c_idx c)) as Ri. pose proof (int_range (Mem.c_w c)) as Rw. rewrite two63_eq in Rg, Ri, Rw.
  assert (KG : keyZ g = to_Z g) by (destruct (keyZ_cases g) as [[_ ->]|[R _]]; [reflexivity| lia]).
  assert (E8 : to_Z (PrimInt63.lsl g 3) = 8 * to_Z g).
  { rewrite lsl_spec, wB_two63, two63_eq. change (2 ^ to_Z 3%uint63) with 8. rewrite Z.mod_small by lia. lia. }
  assert (EO : to_Z (PrimInt63.add (PrimInt63.lsl g 3) (Mem.c_idx c)) = 8 * to_Z g + to_Z (Mem.c_idx c)).
  { rewrite add_spec, E8, wB_two63, two63_eq. rewrite Z.mod_small by lia. reflexivity. }
  assert (EE : to_Z (PrimInt63.add (PrimInt63.add (PrimInt63.lsl g 3) (Mem.c_idx c)) (Mem.c_w c)) = 8 * to_Z g + to_Z (Mem.c_idx c) + to_Z (Mem.c_w c)).
  { rewrite add_spec, EO, wB_two63, two63_eq. rewrite Z.mod_small by lia. reflexivity. }
  split; [exact KG|].
  apply orb_prop in H as [H|H]; apply (known_leu_sound E _ _ _ Hfs) in H.
  - left. rewrite unsigned_VL, wlit_ok, EE in H. exact H.
  - right. rewrite unsigned_VL, wlit_ok, EO, den_sv_alu in H. cbn [alu64 alu] in H. rewrite bv_add_unsigned in H.
    unfold bv_wrap in H. pose proof (bv_unsigned_in_range 64 (den E OFF)) as X1. pose proof (bv_unsigned_in_range 64 (den E n)) as X2. rewrite bv_modulus_64 in X1, X2.
    rewrite bv_modulus_64 in H. unfold W64.two64 in H, NW. rewrite Z.mod_small in H by lia.
    exact H.
Qed.

Lemma to_Z_3 : to_Z 3%uint63 = 3. Proof. reflexivity. Qed.

Lemma den_unsextw : forall E fs v, facts_hold E fs -> den E (PkBody.unsextw fs v) = den E v.
Proof.
  intros E fs v Hfs. unfold PkBody.unsextw.
  destruct v as [| | |opw x y| | | | | | |]; try reflexivity. destruct opw; try reflexivity.
  destruct y as [z| | | | | | | | | |]; try reflexivity.
  destruct (weqb z wzero && wltu (snd (sv_bounds fs x)) (wlit 2147483648%uint63)) eqn:C; [| reflexivity].
  apply andb_prop in C as [Z0 LT]. apply weqb_eq in Z0. subst z.
  pose proof (ValP.sv_bounds_sound E fs Hfs x) as B. unfold ValP.inb in B.
  rewrite wltu_w2Z in LT. apply Z.ltb_lt in LT. rewrite wlit_ok in LT. change (to_Z 2147483648%uint63) with (2 ^ 31) in LT.
  cbn [den alu32 alu]. apply bv_eq. rewrite sext32_unsigned, bv_add_unsigned, !low32_ext.
  rewrite wbv_unsigned. change (w2Z wzero) with 0. rewrite (Z.mod_0_l (2 ^ 32)) by lia. rewrite Z.add_0_r.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  pose proof (bv_unsigned_in_range 64 (den E x)) as R.
  rewrite (Z.mod_small (bv_unsigned (den E x) mod 2 ^ 32) (2 ^ 32)) by (apply Z.mod_pos_bound; lia).
  rewrite (Z.mod_small (bv_unsigned (den E x)) (2 ^ 32)) by lia.
  unfold sx32Z. destruct (Z.leb_spec (2 ^ 31) (bv_unsigned (den E x))); [lia| reflexivity].
Qed.

Theorem pkmemcpy_sound : forall pc, to_Z pc = RMEMCPY_SYM ->
  contract_sound rsegs OPS MP PB (PkBody.pkmemcpy_c rsegs ERRNO pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply PkBody.pkmemcpy_c] in Happ. unfold PkBody.pkmemcpy_apply in Happ.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (CtrA.sym_offset (s_regs st) (getr st X10)) as [[kS OFF]|] eqn:DOFF; [|discriminate].
  destruct (PrimInt63.eqb kS 0%uint63 || PrimInt63.eqb kS STACK_ID) eqn:KS01; [discriminate|].
  apply orb_false_iff in KS01 as [KS0 KS1].
  destruct (IMap.find kS (s_regs st)) as [rS|] eqn:HkS; [|discriminate].
  cbv zeta in Happ.
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  set (rS' := PkBody.dst_region (s_facts st) OFF (getr st X12) rS) in Happ.
  set (st1 := setregs st (IMap.add kS rS' (s_regs st))) in Happ.
  destruct (havoc_errno rsegs ERRNO (clobber st1)) as [st2|] eqn:HE; [|discriminate].
  apply Some_inj in Happ. subst sts.
  apply andb_prop in C2 as [C2 SRC]. apply andb_prop in C2 as [C2 LE2]. apply andb_prop in C2 as [C2 LE1].
  apply andb_prop in C2 as [C2 Ws]. apply andb_prop in C2 as [BGs LOs]. apply Uint63.eqb_correct in LOs.

  destruct (call_sound OPS E st ms mo r HS CP) as [RV SVB POS B62 RA1 RA2 GR MI].
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  pose proof (Preg kS rS HkS) as ROs.

  set (BS := bv_unsigned (ev E kS)) in *. set (offZ := bv_unsigned (den E OFF)). set (N := bv_unsigned (den E (getr st X12))).
  assert (EN0 : N = bv_unsigned (den E (getr st X12))) by reflexivity.
  assert (A2 : PropExec.getr (ms_regs ms) 12%bv = Z_to_bv 64 N) by (rewrite <- reg_of_X12, GR; subst N; symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range 64 (den E OFF)) as OR. rewrite bv_modulus_64 in OR. fold offZ in OR.
  pose proof (bv_unsigned_in_range 64 (den E (getr st X12))) as NR. rewrite bv_modulus_64, <- EN0 in NR.
  clearbody N.
  apply (known_leu_sound E _ _ _ Pfacts) in LE1. apply (known_leu_sound E _ _ _ Pfacts) in LE2.
  fold offZ (hiZ E rS) in LE1. rewrite <- EN0 in LE2. rewrite den_sv_alu in LE2. cbn [alu64 alu] in LE2. rewrite bv_sub_unsigned in LE2. fold offZ (hiZ E rS) in LE2.
  pose proof (ro_range _ _ _ _ _ _ ROs KS0) as [RLs RHs]. fold BS in RLs, RHs. unfold W64.two64 in RHs.
  assert (LZs : loZ rS = 0) by (unfold loZ; rewrite LOs; reflexivity). rewrite LZs in RLs.
  pose proof (bv_unsigned_in_range 64 (den E (Mem.rg_hi rS))) as HSR. rewrite bv_modulus_64 in HSR. fold (hiZ E rS) in HSR.
  assert (SUM : offZ + N <= hiZ E rS).
  { unfold bv_wrap in LE2. rewrite bv_modulus_64 in LE2. rewrite Z.mod_small in LE2; unfold W64.two64 in *; lia. }
  set (D := BS + offZ).
  assert (DA : den E (getr st X10) = Z_to_bv 64 D).
  { rewrite (sym_offset_sound E (s_regs st) _ kS OFF DOFF). apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. subst D BS offZ. reflexivity. }
  destruct (MemFX.based_rw_cells rsegs (s_priv st) E (ms_mem ms) kS rS offZ (Z.to_nat N) ROs KS0 Ws ltac:(lia) ltac:(lia)) as (junk & LJ & DST).
  fold BS in DST. fold D in DST.
  pose proof two64_eq as T64.

  assert (SRCX : exists S src, PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 S /\ 0 <= S < 2 ^ 64 /\ S + N <= 2 ^ 64 /\
                 length src = Z.to_nat N /\ bytes_at rsegs (ms_mem ms) S src /\ (S + N <= D \/ D + N <= S)).
  { apply orb_prop in SRC as [SRC|SRC]; [apply orb_prop in SRC as [SRC|SRC]|].
    -
      unfold PkBody.stack_src_ok in SRC.
      destruct (getr st X11) as [|k1 o| | | | | | | | |] eqn:HX11; try discriminate.
      destruct (getr st X12) as [nw| | | | | | | | | |] eqn:HX12; try discriminate.
      destruct (getr st X2) as [|k2 osp| | | | | | | | |] eqn:HX2; try discriminate.
      destruct (IMap.find STACK_ID (s_regs st)) as [r1|] eqn:Hr1; [|discriminate].
      apply andb_prop in SRC as [SRC KEYS]. apply andb_prop in SRC as [SRC NWM]. apply andb_prop in SRC as [SRC NWT]. apply andb_prop in SRC as [K1 K2].
      apply Uint63.eqb_correct in K1. apply Uint63.eqb_correct in K2. subst k1 k2. apply negb_true_iff in NWT. apply Uint63.leb_spec in NWM.
      assert (NW4 : w2Z nw = to_Z (wl nw)) by (unfold w2Z; rewrite NWT; lia).
      change (to_Z PkBody.STK_MAX) with 4096 in NWM.
      destruct (Mem.okey o) as [i|] eqn:Hi; [|discriminate]. destruct (Mem.okey (wadd o nw)) as [ie|] eqn:Hie; [|discriminate].
      destruct (Mem.okey osp) as [ksp|] eqn:Hksp; [|discriminate].
      destruct (Mem.rg_hi r1) as [h| | | | | | | | | |] eqn:Hh; try discriminate.
      destruct (Mem.okey h) as [kh|] eqn:Hkh; [|discriminate].
      apply andb_prop in KEYS as [KEYS L4]. apply andb_prop in KEYS as [KEYS L3]. apply andb_prop in KEYS as [L1 L2].
      rewrite kleb_keyZ in L1, L2, L3, L4. apply Z.leb_le in L1. apply Z.leb_le in L2. apply Z.leb_le in L3. apply Z.leb_le in L4.
      destruct (okey_sound _ _ Hi) as [Ei Ri]. destruct (okey_sound _ _ Hie) as [Eie Rie]. destruct (okey_sound _ _ Hkh) as [Ekh Rkh].
      rewrite ?half63 in Ri, Rie, Rkh. unfold W64.two63 in Ri, Rie, Rkh.
      pose proof (so_reg _ _ _ _ _ _ HS _ _ Hr1) as RO1.
      pose proof (ro_range _ _ _ _ _ _ RO1 eq_refl) as [RLO1 RHI1]. unfold W64.two64 in RHI1.
      set (B1 := bv_unsigned (ev E STACK_ID)) in *.
      assert (Ehi : keyZ kh <= hiZ E r1).
      { unfold hiZ. rewrite Hh, unsigned_VL, Ekh, w2Zs_eq. unfold W64.two64. destruct (wt h); lia. }
      assert (NWZ : N = w2Z nw) by (rewrite EN0, ?HX12, unsigned_VL; reflexivity).
      pose proof (w2Z_range nw) as Rnw. pose proof (int_range (wl nw)) as Rnw'. rewrite two63_eq in Rnw'.
      assert (Eie' : keyZ ie = keyZ i + N).
      { rewrite Eie, NWZ, w2Zs_wadd_small; [rewrite Ei; reflexivity|]. rewrite <- Ei. unfold W64.two63 in *. lia. }
      unfold loZ in RLO1.
      set (S := B1 + keyZ i).
      assert (ES : den E (VP STACK_ID o) = Z_to_bv 64 S).
      { apply bv_eq. rewrite Z_to_bv_unsigned, den_VP, <- Ei. fold B1. subst S. unfold bv_wrap. rewrite bv_modulus_64. reflexivity || (apply Z.mod_small; unfold W64.two64; lia) || (symmetry; apply Z.mod_small; unfold W64.two64; lia). }
      destruct (MemFX.based_bytes rsegs (s_priv st) E (ms_mem ms) STACK_ID r1 (keyZ i) (Z.to_nat N) RO1 eq_refl ltac:(unfold loZ; lia) ltac:(lia)) as (src & LEN & SRCB).
      fold B1 in SRCB. fold S in SRCB.
      exists S, src. split; [rewrite <- reg_of_X11, GR, ?HX11; exact ES|]. split; [subst S; lia|]. split; [subst S; lia|].
      split; [exact LEN|]. split; [exact SRCB|].
      destruct (Z.eq_dec N 0) as [->|N0]; [lia|].
      apply (CopyFX.sep_of_pointwise S D N ltac:(lia)). intros j j' Hj Hj' EQ.
      apply (Pdisj STACK_ID r1 kS rS Hr1 HkS ltac:(intros X; rewrite <- X in KS1; discriminate KS1) eq_refl KS0 (or_intror Ws) (S + j)).
      fold B1 BS. rewrite LZs. split; [unfold loZ; subst S; lia| subst D; lia].
    -
      unfold PkBody.based_src_ok in SRC.
      destruct (CtrA.sym_offset (s_regs st) (getr st X11)) as [[kd OFFs]|] eqn:SOFF; [|discriminate].
      destruct (IMap.find kd (s_regs st)) as [rd|] eqn:Hkd; [|discriminate].
      apply andb_prop in SRC as [SRC LE4]. apply andb_prop in SRC as [SRC LE3]. apply andb_prop in SRC as [SRC LOd].
      apply andb_prop in SRC as [Kd0 KdS]. apply negb_true_iff in Kd0. apply negb_true_iff in KdS. apply Uint63.eqb_correct in LOd.
      pose proof (Preg kd rd Hkd) as ROd.
      set (Bd := bv_unsigned (ev E kd)) in *. set (offS := bv_unsigned (den E OFFs)).
      pose proof (bv_unsigned_in_range 64 (den E OFFs)) as OSR. rewrite bv_modulus_64 in OSR. fold offS in OSR.
      apply (known_leu_sound E _ _ _ Pfacts) in LE3. apply (known_leu_sound E _ _ _ Pfacts) in LE4.
      fold offS (hiZ E rd) in LE3. rewrite <- EN0 in LE4. rewrite den_sv_alu in LE4. cbn [alu64 alu] in LE4. rewrite bv_sub_unsigned in LE4. fold offS (hiZ E rd) in LE4.
      pose proof (ro_range _ _ _ _ _ _ ROd Kd0) as [RLd RHd]. fold Bd in RLd, RHd. unfold W64.two64 in RHd.
      assert (LZd : loZ rd = 0) by (unfold loZ; rewrite LOd; reflexivity). rewrite LZd in RLd.
      pose proof (bv_unsigned_in_range 64 (den E (Mem.rg_hi rd))) as HDR. rewrite bv_modulus_64 in HDR. fold (hiZ E rd) in HDR.
      assert (SUMd : offS + N <= hiZ E rd).
      { unfold bv_wrap in LE4. rewrite bv_modulus_64 in LE4. rewrite Z.mod_small in LE4; unfold W64.two64 in *; lia. }
      set (S := Bd + offS).
      assert (SA : den E (getr st X11) = Z_to_bv 64 S).
      { rewrite (sym_offset_sound E (s_regs st) _ kd OFFs SOFF). apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. subst S Bd offS. reflexivity. }
      destruct (MemFX.based_bytes rsegs (s_priv st) E (ms_mem ms) kd rd offS (Z.to_nat N) ROd Kd0 ltac:(lia) ltac:(lia)) as (src & LEN & SRCB).
      fold Bd in SRCB. fold S in SRCB.
      exists S, src. split; [rewrite <- reg_of_X11, GR; exact SA|]. split; [subst S; lia|]. split; [subst S; lia|].
      split; [exact LEN|]. split; [exact SRCB|].
      destruct (Z.eq_dec N 0) as [->|N0]; [lia|].
      apply (CopyFX.sep_of_pointwise S D N ltac:(lia)). intros j j' Hj Hj' EQ.
      apply (Pdisj kd rd kS rS Hkd HkS ltac:(apply Uint63.eqb_false_spec; exact KdS) Kd0 KS0 (or_intror Ws) (S + j)).
      fold D Bd BS. rewrite LZd, LZs. split; [subst S; lia| lia].
    -
      unfold PkBody.body_src_ok in SRC.
      destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
      apply andb_prop in SRC as [MD SRC]. apply Uint63.eqb_correct in MD. subst mdi.
      destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
        try discriminate.
      destruct (PkBody.body_src (s_facts st) eb rootT n1 P1 cf fT fN fP) as [[[fTv fNv] fPv]|] eqn:SRCB; [|discriminate].
      destruct fTv as [t| | | | | | | | | |]; try discriminate.
      apply andb_prop in SRC as [SRC DEQN]. apply andb_prop in SRC as [TY DEQP].

      destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
      pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
      destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
      rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
      apply CW3 in HC. unfold PK.cw_pk_holds in HC. cbn [map PK.decode_pk] in HC.
      destruct HC as (g & ls & L & P & O & Wk & M & GH).
      pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
      cbn [PK.a_root PK.a_rootT PK.a_n1 PK.a_P1 PK.a_c0 PK.a_eb PK.a_ee PK.a_ecap PK.a_tptr PK.a_trest PK.a_tmap PK.a_tkey PK.a_cf PK.a_fT PK.a_fN PK.a_fP] in LCF.
      pose proof P as (LV & EL & SZ & VE & CE & ZV).
      pose proof M as (TW & KA & [IC IB] & CH & PE).
      assert (FO : exists fo, tree_wf (bmem_of rsegs (ms_mem ms)) (PK.k_zone g) fo /\ obj_type fo = bv_unsigned (den E (VL t))
                /\ obj_ptr fo = bv_unsigned (den E fPv) /\ (PK.obj_via fo = bv_unsigned (den E fNv) \/ obj_cnt fo = bv_unsigned (den E fNv))).
      { unfold PkBody.body_src in SRCB. destruct (sv_eqb eb (VL wzero)) eqn:EB0.
        - apply sv_eqb_eq in EB0. subst eb. injection SRCB as <- <- <-.
          cbn [PK.a_root PK.a_rootT PK.a_n1 PK.a_P1 PK.a_c0 PK.a_eb] in LT, LN, LP, Leb.
          assert (VB0 : v_begin (PK.k_evec g) = 0) by (rewrite Leb; cbn [den]; rewrite wbv_unsigned; reflexivity).
          destruct VE as [(_ & _ & ->)|[(_ & _ & VNZ & _) _]]; [| exfalso; exact (VNZ VB0)].
          exists (PK.k_tree g). split; [exact TW|]. split; [exact LT|]. split; [exact LP|]. right. exact LN.
        - unfold dec_false in SRCB. destruct (decide_eq0 (s_facts st) cf) as [[|]|] eqn:DZ; try discriminate. injection SRCB as <- <- <-.
          pose proof (decide_eq0_sound E (s_facts st) Pfacts _ _ DZ) as CNZ. apply (proj1 (eqb_iff _ _ false)) in CNZ.
          assert (CF0 : bv_unsigned (den E cf) <> 0) by (intros X; apply CNZ; apply bv_eq; rewrite X; reflexivity).
          destruct (LCF CF0) as (LSNE & CFA & fo & FN & FT & FVIA & FPTR).
          pose proof (last_opt_spec ls) as LS. unfold PK.focus_node in FN.
          destruct (last_opt ls) as [l|] eqn:LAST; [| contradiction]. destruct LS as [ls0 ELS].
          assert (HLV : PK.levels_ok (PK.k_tree g) (ls0 ++ [l])) by (rewrite <- ELS; exact LV).
          exists fo. split; [exact (focus_tree_wf _ _ _ _ _ _ TW HLV FN)|]. auto. }
      clear LCF SRCB. destruct FO as (fo & TWF & FT & FPTR & FVIA).
      assert (HT : w2Z t = T_STR \/ w2Z t = T_BIN \/ w2Z t = T_EXT).
      { unfold PkBody.T_STRw, PkBody.T_BINw, PkBody.T_EXTw in TY. unfT.
        apply orb_prop in TY as [TY|TY]; [apply orb_prop in TY as [TY|TY]|]; apply (proj1 (weqb_ok _ _)) in TY; subst t;
          rewrite ?w2Z_wlit || idtac; cbn; auto. }
      assert (FT' : obj_type fo = w2Z t) by (rewrite FT; cbn [den]; rewrite wbv_unsigned; reflexivity).
      set (p := obj_ptr fo) in *. set (n := bv_unsigned (den E fNv)) in *.
      pose proof (body_of_focus (bmem_of rsegs (ms_mem ms)) (PK.k_zone g) fo (w2Z t) p n TWF FT' HT eq_refl FVIA) as BODY. cbv zeta in BODY.
      set (N' := if w2Z t =? T_EXT then n + 1 else n) in *.
      destruct BODY as (N0 & NL & PZ & PNZ).
      unfold dec_true in DEQP.
      destruct (decide_eq (s_facts st) (getr st X11) (if weqb t PkBody.T_EXTw then sv_alu ALU_ADD fPv (VL wone) else fPv)) as [[|]|] eqn:DQP; try discriminate.
      pose proof (decide_eq_sound E (s_facts st) Pfacts _ _ _ DQP) as EQP. apply (proj1 (eqb_iff _ _ true)) in EQP.
      unfold dec_true in DEQN.
      destruct (decide_eq (s_facts st) (getr st X12) (PkBody.unsextw (s_facts st) (narrow_f (s_facts st) fNv))) as [[|]|] eqn:DQN; try discriminate.
      pose proof (eq_trans (den_unsextw E (s_facts st) _ Pfacts) (ValP.den_narrow_f E (s_facts st) Pfacts fNv)) as DNF.
      pose proof (decide_eq_sound E (s_facts st) Pfacts _ _ _ DQN) as EQN. apply (proj1 (eqb_iff _ _ true)) in EQN.
      assert (NN : N = n) by (rewrite EN0, EQN, DNF; reflexivity).
      assert (EN : N' = (if w2Z t =? T_EXT then n + 1 else n)) by reflexivity. clearbody N'. unfT.

      assert (T9 : weqb t (wlit 9%uint63) = (w2Z t =? 9)).
      { destruct (weqb t (wlit 9%uint63)) eqn:T9.
        - apply (proj1 (weqb_ok _ _)) in T9. subst t. reflexivity.
        - symmetry. apply Z.eqb_neq. intros X. destruct t as [tt tl]. unfold w2Z in X. cbn [wt wl] in X.
          unfold weqb, wlit in T9. cbn [wt wl] in T9. destruct tt; [pose proof (Uint63.to_Z_bounded tl); unfold W64.two63 in X; lia|].
          cbn [Bool.eqb andb] in T9. apply Uint63.eqb_false_spec in T9. apply T9. apply Uint63.to_Z_inj. change (to_Z 9%uint63) with 9. lia. }
      unfold PkBody.T_EXTw in EQP. rewrite T9 in EQP.
      set (isx := if w2Z t =? 9 then 1 else 0).
      assert (ENI : N' = n + isx /\ 0 <= isx <= 1) by (subst isx; rewrite EN; destruct (w2Z t =? 9); lia).
      clear EN. destruct ENI as [EN IR].
      pose proof (bv_unsigned_in_range 64 (den E fPv)) as PR. rewrite bv_modulus_64, <- FPTR in PR.
      assert (SP : bv_unsigned (den E (getr st X11)) = (p + isx) mod 2 ^ 64).
      { rewrite EQP. unfold isx. destruct (w2Z t =? 9).
        - rewrite den_sv_alu. cbn [alu64 alu]. rewrite bv_add_unsigned, <- FPTR, unsigned_VL. change (w2Z wone) with 1.
          unfold bv_wrap. rewrite bv_modulus_64. reflexivity.
        - rewrite <- FPTR, Z.add_0_r, Z.mod_small by lia. reflexivity. }
      clearbody isx.
      set (S := bv_unsigned (den E (getr st X11))) in *.
      pose proof (bv_unsigned_in_range 64 (den E (getr st X11))) as SR. rewrite bv_modulus_64 in SR. fold S in SR.

      assert (SRCX : N = 0 \/ (N <> 0 /\ p <> 0 /\ S = p + isx /\ p + N' <= 2 ^ 64 /\
                     (exists src, length src = Z.to_nat N /\ bytes_at rsegs (ms_mem ms) S src) /\
                     (exists c, In c (z_chunks (PK.k_zone g)) /\ in_chunk c p N'))).
      { destruct (Z.eq_dec N 0) as [Z0|NZ0]; [left; exact Z0| right].
        assert (PN0 : p <> 0) by (intros P0; pose proof (PZ P0); lia).
        destruct (PNZ PN0) as [IZ [v RD]].
        pose proof IZ as (c & Hc & ICc).
        destruct (aw_blocks_ok rsegs IMGX AW _ LB _ (ms_mem ms) mo (chunk_block c) HA
                    (proj1 O _ ltac:(unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc))) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
        unfold chunk_block in Bc1, Bc2, Bc3. cbn [fst snd] in Bc1, Bc2, Bc3.
        assert (PB8 : 0 <= p /\ p + N' <= 2 ^ 64) by (unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in ICc; unfold CHUNK_HDR in *; lia).
        assert (ES : S = p + isx) by (rewrite SP; apply Z.mod_small; lia).
        split; [exact NZ0|]. split; [exact PN0|]. split; [exact ES|]. split; [lia|]. split; [| exists c; auto].
        exists (map (fun i => Z_to_bv 8 (zbyte v (Z.of_nat i + isx))) (seq 0 (Z.to_nat N))).
        assert (LENs : length (map (fun i => Z_to_bv 8 (zbyte v (Z.of_nat i + isx))) (seq 0 (Z.to_nat N))) = Z.to_nat N) by (rewrite length_map, length_seq; reflexivity).
        split; [exact LENs|].
        apply CopyFX.bytes_at_of_rb; [lia| rewrite LENs; lia|]. rewrite LENs. intros j Hj.
        pose proof (rdZ_bytes _ _ _ _ (bmem_of_bytes_range rsegs (ms_mem ms)) RD (j + isx) ltac:(lia)) as X. unfold bmem_of in X.
        replace ((0 <=? p + (j + isx)) && (p + (j + isx) <? two64)) with true in X by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
        rewrite ES. replace (p + isx + j) with (p + (j + isx)) by lia.
        destruct (rb rsegs (ms_mem ms) (p + (j + isx))) as [b|]; [|discriminate X]. cbn [option_map] in X. injection X as X.
        f_equal. rewrite nth_map_seq by lia. cbn beta.
        apply bv_eq. rewrite X, Z2Nat.id by lia. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
        pose proof (zbyte_range v (j + isx)). change (bv_modulus 8) with 256. lia. }
      assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 S) by (rewrite <- reg_of_X11, GR; subst S; symmetry; apply Z_to_bv_bv_unsigned).
      destruct SRCX as [Z0|(NZ0 & PN0 & ES & PB8 & (src & LENS & SRC') & (c & Hc & ICc))].
      {
        exists S, []. split; [exact A1|]. split; [lia|]. split; [lia|]. split; [rewrite Z0; reflexivity|].
        split; [| lia]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. }
      exists S, src. split; [exact A1|]. split; [lia|]. split; [lia|]. split; [exact LENS|]. split; [exact SRC'|].

      assert (INLB : In (chunk_block c) LB) by (apply (proj1 O); unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc).
      destruct (aw_blocks_ok rsegs IMGX AW _ LB _ (ms_mem ms) mo (chunk_block c) HA INLB) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
      unfold chunk_block in Bc1, Bc2, Bc3, Bc5. cbn [fst snd] in Bc1, Bc2, Bc3, Bc5.
      apply (CopyFX.sep_of_pointwise S D N ltac:(lia)). intros j j' Hj Hj' EQ.
      assert (INB : in_iv (fst c, CHUNK_HDR + snd c) (S + j)) by (unfold in_iv, in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in *; cbn [fst snd]; lia).
      assert (FP : Exists (fun q => fst q <= S + j < snd q) (St.op_fp OPS (op_id o) (map (den E) (op_args o)))).
      { rewrite OID, (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ _ _ _ _ (S + j) (DECf E))).
        split; [lia|]. split; [exact (Bc5 _ INB)|].
        intros IW. apply in_ws_map_iff in IW as (w & Hw & INW).
        pose proof (proj1 (Forall_forall _ _) WF (wden E w) (in_map _ _ _ Hw)) as (_ & _ & _ & [[KSk CEk]|OTHERk]).
        - unfold in_iv, w_iv in INW. unfold in_iv in INB. cbn [fst snd] in INW, INB. lia.
        - assert (NK : w_kind (wden E w) <> K_STACK) by (destruct OTHERk as [[-> _]|[KS _]]; [discriminate| unfold K_SUB, K_STACK in *; lia]).
          destruct (proj1 (Forall_forall _ _) Wk (wden E w) (in_map _ _ _ Hw) NK) as [[_ DISJ]|[_ ET]].
          + apply (DISJ (chunk_block c) ltac:(unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc) (S + j) INW). exact INB.
          + exact (PK.safe_zone g ls LB (map (wden E) ws) P O p N' (S + j) ltac:(lia) (ex_intro _ c (conj Hc ICc)) ltac:(lia) (wden E w) (in_map _ _ _ Hw) ET INW). }
      destruct (proj1 (Forall_forall _ _) Papart o (op_in_In st o OPS1) (S + j) FP) as [NB _].
      apply NB. exists kS, rS. split; [exact HkS|]. split; [exact KS0|]. fold BS. rewrite LZs. rewrite EQ. subst D. lia. }
  destruct SRCX as (S & src & A1 & S0 & SN & LEN & SRC' & SEP).

  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 D) by (rewrite <- reg_of_X10, GR; exact DA).
  pose proof (ms_shape OPS E st ms mo HS RV) as MSE. rewrite Hspc in MSE. cbn [c_pc PkBody.pkmemcpy_c] in MSE. rewrite Hpc in MSE.
  rewrite MSE.
  apply (memcpy_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo D S N src junk K A0 A1 A2
           ltac:(lia) ltac:(lia) ltac:(lia) RA1 SRC' LEN DST SEP MI (mf_halted _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS))) (mf_lazy _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS)))).
  intros R' M' KEPT A0' MU WM MI' RW BA OM.

  assert (RO' : St.region_ok rsegs (s_priv st) E M' kS rS').
  { destruct RW as [[CWF BY] (_ & _ & WR)]. cbn [cells_size csize cells_bytes cbytes Nat.add] in BY, WR. rewrite app_nil_r in BY. rewrite Nat.add_0_r in WR.
    destruct BY as (_ & _ & BY). rewrite LEN in BY.
    destruct ROs as [Abst Arange Avalid Acells Ain Abg].
    assert (VALID : forall a, BS + loZ rS <= a < BS + hiZ E rS -> rb rsegs M' a <> None /\ (Mem.rg_w rS = true -> wb rsegs M' a = true) /\ find_segment rsegs a 1 = None).
    { intros a Ha. destruct (Avalid KS0 a Ha) as (V1 & V2 & V3). rewrite LZs in Ha.
      destruct (Z_lt_le_dec a D) as [L0|G0]; [| destruct (Z_lt_le_dec a (D + N)) as [L2|G2]].
      + assert (EQM : M' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) by (apply (memcpy_frame _ _ D N MU a); unfold W64.two64 in *; lia).
        split; [| split; [| exact V3]]; [unfold rb in V1 |- *; rewrite EQM; exact V1|].
        intros W. apply (proj2 (MemFX.wb_wview rsegs _ _)). apply WM. apply (proj1 (MemFX.wb_wview rsegs _ _)). exact (V2 W).
      + split; [| split; [| exact V3]].
        * rewrite MemFX.rb_mrd. replace a with (D + Z.of_nat (Z.to_nat (a - D))) by lia. rewrite BY by lia.
          destruct (nth_error src (Z.to_nat (a - D))) eqn:X; [congruence|]. apply nth_error_None in X. lia.
        * intros _. apply (proj2 (MemFX.wb_wview rsegs _ _)). replace a with (D + (a - D)) by lia. apply WR. lia.
      + assert (EQM : M' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) by (apply (memcpy_frame _ _ D N MU a); unfold W64.two64 in *; lia).
        split; [| split; [| exact V3]]; [unfold rb in V1 |- *; rewrite EQM; exact V1|].
        intros W. apply (proj2 (MemFX.wb_wview rsegs _ _)). apply WM. apply (proj1 (MemFX.wb_wview rsegs _ _)). exact (V2 W). }
    unfold rS', PkBody.dst_region.
    destruct (PkBody.cells_apart (s_facts st) OFF (getr st X12) (Mem.rg_cells rS)) eqn:APART.
    -
      constructor; cbn [Mem.rg_lo Mem.rg_hi Mem.rg_w Mem.rg_bg Mem.rg_cells].
      + exact Abst.
      + exact Arange.
      + intros K0 a Ha. exact (VALID a Ha).
      + intros gg gr Hg. destruct (Acells gg gr Hg) as [SS FA]. split; [exact SS|].
        apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) FA c Hc) as (C1 & C2 & C3 & C4).
        split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. intros i Hi.
        unfold PkBody.cells_apart in APART.
        pose proof (proj1 (IMap.forallb_spec _ _ Abst) APART gg gr Hg) as FB. cbn beta in FB.
        pose proof (proj1 (forallb_forall _ _) FB c Hc) as CA.
        destruct (cell_apart_sound E (s_facts st) OFF (getr st X12) gg c Pfacts CA C1 C3 C2 ltac:(fold offZ; rewrite <- EN0; unfold W64.two64; lia)) as [KG APT].
        fold offZ in APT. rewrite <- EN0 in APT.
        pose proof (Ain gg gr c i Hg Hc Hi) as AIN. cbv zeta in AIN. destruct AIN as [P1 _]. specialize (P1 KS0). rewrite LZs in P1.
        rewrite <- (C4 i Hi). unfold rb. fold BS.
        rewrite (memcpy_frame _ _ D N MU (BS + 8 * keyZ gg + to_Z (Mem.c_idx c) + i)); [reflexivity| unfold W64.two64; lia|]. subst D. rewrite KG in P1. rewrite KG. lia.
      + exact Ain.
      + intros oo H1 H2 U. exact I.
    -
      constructor; cbn [Mem.rg_lo Mem.rg_hi Mem.rg_w Mem.rg_bg Mem.rg_cells].
      + exact I.
      + exact Arange.
      + intros K0 a Ha. exact (VALID a Ha).
      + intros gg gr Hg. cbn in Hg. discriminate Hg.
      + intros gg gr c i Hg. cbn in Hg. discriminate Hg.
      + intros oo H1 H2 U. exact I. }
  pose proof (MemFX.st_ok_based_write rsegs OPS E st (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None (ms_mem ms) M' (seg_rom rsegs) mo kS rS rS'
                ltac:(rewrite <- MSE; exact HS) HkS KS0 Ws
                ltac:(intros a Ha NI; apply (memcpy_frame _ _ D N MU a Ha); fold BS in NI; rewrite LZs in NI; lia)
                OM (minv_of_mem_inv M' MI') RO' ltac:(unfold loZ, rS', PkBody.dst_region; cbn [Mem.rg_lo]; lia)
                ltac:(unfold hiZ, rS', PkBody.dst_region; cbn [Mem.rg_hi]; lia)) as HS1.
  assert (SVB1 : st_vars_below (s_next st) st1 = true).
  { apply (MemFX.st_vars_below_setregs (s_next st) st kS rS rS' Pbst SVB HkS).
    destruct (MemFX.st_vars_below_parts (s_next st) st SVB) as (P1 & P2 & P3 & P4 & P5 & P6).
    pose proof (proj1 (IMap.forallb_spec _ _ Pbst) P4 kS rS HkS) as RVB. cbn beta in RVB.
    apply andb_prop in RVB as [_ RVB].
    unfold region_vars_below in RVB |- *. unfold rS', PkBody.dst_region. cbn [Mem.rg_hi Mem.rg_cells].
    apply andb_prop in RVB as [RH RC]. rewrite RH.
    destruct (PkBody.cells_apart (s_facts st) OFF (getr st X12) (Mem.rg_cells rS)); [exact RC| reflexivity]. }
  assert (HKR : forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr (ms_regs ms) (reg_of_r5 x)).
  { intros x N0' CPx. destruct (r5_eqb x X10) eqn:Q.
    - apply r5_eqb_spec in Q. subst x. rewrite reg_of_X10, A0', A0. reflexivity.
    - apply KEPT. apply kept_or_clobbered; [exact N0'| intros ->; rewrite r5_eqb_refl in Q; discriminate| exact CPx]. }
  destruct (MemFX.ccall_frame rsegs OPS E st1 ERRNO r st2 (ms_regs ms) R' (ms_fregs ms)
              (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) M' (seg_rom rsegs) mo HS1 RV SVB1 POS B62 HKR HE) as (ST & NX & _).
  rewrite <- RA2 in ST.
  exact (HK _ (or_introl eq_refl) _ _ _ (MemFX.cenv_ext _ E _ R' M' ERRNO) HMP ST).
Qed.

Lemma dec_true_inv : forall x, dec_true x = true -> x = Some true.
Proof. intros [[|]|]; cbn; congruence. Qed.

Lemma st_ok_facts_next : forall E st ms mo fs' nx,
  St.st_ok rsegs OPS E st ms mo -> Forall (fact_holds E) fs' ->
  St.st_ok rsegs OPS E (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (fs' ++ s_facts st) (s_ops st) (s_priv st) nx) ms mo.
Proof.
  intros E st ms mo fs' nx HS HF.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  apply Forall_app. split; [exact HF| exact Pfacts].
Qed.

Theorem pkextb_sound : forall pc, contract_sound rsegs OPS MP PB (PkBody.pkextb_c rsegs pc).
Proof.
  intros pc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply PkBody.pkextb_c] in Happ. unfold PkBody.pkextb_apply in Happ.
  destruct (LdPart.load_at rsegs (s_pc st)) as [[[[[sz sx] rd] rs] off]|] eqn:LA; [|discriminate].
  destruct sz; try discriminate. destruct sx; [|discriminate].
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 3) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi. cbn [negb] in Happ.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  destruct (PkBody.body_src (s_facts st) eb rootT n1 P1 cf fT fN fP) as [[[fTv fNv] fPv]|] eqn:SRCB; [|discriminate].
  destruct fTv as [t| | | | | | | | | |]; try discriminate.
  cbv zeta in Happ.
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  apply Some_inj in Happ. subst sts.
  apply andb_prop in C2 as [C2 PCB]. apply andb_prop in C2 as [C2 NLT]. apply andb_prop in C2 as [C2 NPOS].
  apply andb_prop in C2 as [C2 VB]. apply andb_prop in C2 as [C2 RD0]. apply andb_prop in C2 as [TY DEQP].
  apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS. apply Uint63.ltb_spec in NLT.
  set (n := s_next st) in *.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].

  destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
  apply CW3 in HC. unfold PK.cw_pk_holds in HC. cbn [map PK.decode_pk] in HC.
  destruct HC as (g & ls & L & P & O & Wk & M & GH).
  pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
  cbn [PK.a_root PK.a_rootT PK.a_n1 PK.a_P1 PK.a_c0 PK.a_eb PK.a_ee PK.a_ecap PK.a_tptr PK.a_trest PK.a_tmap PK.a_tkey PK.a_cf PK.a_fT PK.a_fN PK.a_fP] in LCF.
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  pose proof M as (TW & KA & [IC IB] & CH & PE).
  assert (FO : exists fo, tree_wf (bmem_of rsegs (ms_mem ms)) (PK.k_zone g) fo /\ obj_type fo = bv_unsigned (den E (VL t))
            /\ obj_ptr fo = bv_unsigned (den E fPv) /\ (PK.obj_via fo = bv_unsigned (den E fNv) \/ obj_cnt fo = bv_unsigned (den E fNv))).
  { unfold PkBody.body_src in SRCB. destruct (sv_eqb eb (VL wzero)) eqn:EB0.
    - apply sv_eqb_eq in EB0. subst eb. injection SRCB as <- <- <-.
      cbn [PK.a_root PK.a_rootT PK.a_n1 PK.a_P1 PK.a_c0 PK.a_eb] in LT, LN, LP, Leb.
      assert (VB0 : v_begin (PK.k_evec g) = 0) by (rewrite Leb; cbn [den]; rewrite wbv_unsigned; reflexivity).
      destruct VE as [(_ & _ & ->)|[(_ & _ & VNZ & _) _]]; [| exfalso; exact (VNZ VB0)].
      exists (PK.k_tree g). split; [exact TW|]. split; [exact LT|]. split; [exact LP|]. right. exact LN.
    - unfold dec_false in SRCB. destruct (decide_eq0 (s_facts st) cf) as [[|]|] eqn:DZ; try discriminate. injection SRCB as <- <- <-.
      pose proof (decide_eq0_sound E (s_facts st) Pfacts _ _ DZ) as CNZ. apply (proj1 (eqb_iff _ _ false)) in CNZ.
      assert (CF0 : bv_unsigned (den E cf) <> 0) by (intros X; apply CNZ; apply bv_eq; rewrite X; reflexivity).
      destruct (LCF CF0) as (LSNE & CFA & fo & FN & FT & FVIA & FPTR).
      pose proof (last_opt_spec ls) as LS. unfold PK.focus_node in FN.
      destruct (last_opt ls) as [l|] eqn:LAST; [| contradiction]. destruct LS as [ls0 ELS].
      assert (HLV : PK.levels_ok (PK.k_tree g) (ls0 ++ [l])) by (rewrite <- ELS; exact LV).
      exists fo. split; [exact (focus_tree_wf _ _ _ _ _ _ TW HLV FN)|]. auto. }
  clear LCF SRCB. destruct FO as (fo & TWF & FT & FPTR & FVIA).
  unfold PkBody.T_EXTw in TY. apply (proj1 (weqb_ok _ _)) in TY. subst t.
  assert (FT' : obj_type fo = T_EXT) by (rewrite FT; cbn [den]; rewrite wbv_unsigned; reflexivity).
  set (p := obj_ptr fo) in *. set (nb := bv_unsigned (den E fNv)) in *.
  pose proof (body_of_focus (bmem_of rsegs (ms_mem ms)) (PK.k_zone g) fo T_EXT p nb TWF FT' ltac:(unfT; lia) eq_refl FVIA) as BODY.
  cbv zeta in BODY. unfT. replace (9 =? 9) with true in BODY by reflexivity.
  destruct BODY as (N0 & NL & PZ & PNZ).
  assert (PN0 : p <> 0) by (intros P0; pose proof (PZ P0); lia).
  destruct (PNZ PN0) as [IZ [v RD]].
  pose proof IZ as (c & Hc & ICc).
  destruct (aw_blocks_ok rsegs IMGX AW _ LB _ (ms_mem ms) mo (chunk_block c) HA
              (proj1 O _ ltac:(unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc))) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
  unfold chunk_block in Bc1, Bc2, Bc3. cbn [fst snd] in Bc1, Bc2, Bc3.
  pose proof two64_eq as T64.
  assert (PB8 : 0 <= p /\ p + (nb + 1) <= 2 ^ 64) by (unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in ICc; unfold CHUNK_HDR in *; lia).

  pose proof (rdZ_bytes _ _ _ _ (bmem_of_bytes_range rsegs (ms_mem ms)) RD 0 ltac:(lia)) as X0. rewrite Z.add_0_r in X0.
  assert (RD1 : rdZ (bmem_of rsegs (ms_mem ms)) p (Z.to_nat (to_Z (msize_bytes SZ1))) = Some (zbyte v 0)).
  { change (Z.to_nat (to_Z (msize_bytes SZ1))) with 1%nat. cbn [rdZ]. rewrite X0. cbn [rdZ]. f_equal. pose proof (zbyte_range v 0). lia. }
  pose proof (zbyte_range v 0) as ZB. change (bv_modulus 8) with 256 in ZB.
  set (z := zbyte v 0) in *.

  pose proof (dec_true_inv _ DEQP) as DQP.
  pose proof (decide_eq_sound E (s_facts st) Pfacts _ _ _ DQP) as EQP. apply (proj1 (eqb_iff _ _ true)) in EQP.

  set (W := Z_to_bv 64 z).
  set (E' := env_upd E n W).
  assert (HX : env_ext n E E') by (subst E'; apply env_upd_ext).
  assert (EVn : ev E' n = W) by (subst E'; apply env_upd_same).
  assert (HS' : St.st_ok rsegs OPS E' st ms mo) by exact (st_ok_reval rsegs OPS n E E' HX st ms mo NPOS VB HS).
  set (rv := VExt true 0%uint63 1%uint63 (VP n wzero)).
  assert (Dv : den E' rv = ext_word true 0 (to_Z (msize_bytes SZ1)) (Z_to_bv 64 z)).
  { subst rv. cbn [den]. rewrite EVn. subst W. change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1.
    change (to_Z (msize_bytes SZ1)) with 1. f_equal. apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned. change (w2Z wzero) with 0.
    rewrite Z.add_0_r. apply bv_wrap_bv_unsigned. }
  set (st1 := SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (FRange n wzero (wlit 255%uint63) :: s_facts st)
                 (s_ops st) (s_priv st) (PrimInt63.add n 1%uint63)).
  assert (HS1 : St.st_ok rsegs OPS E' st1 ms mo).
  { apply (st_ok_facts_next E' st ms mo [FRange n wzero (wlit 255%uint63)] (PrimInt63.add n 1%uint63) HS').
    constructor; [| constructor]. cbn [fact_holds]. rewrite EVn. subst W. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; lia).
    rewrite wlit_ok || rewrite w2Z_wlit. change (w2Z wzero) with 0. change (to_Z 255%uint63) with 255. lia. }

  destruct (LdPartSound.load_at_spec rsegs _ _ _ _ _ _ LA) as (wi & ins & Hf & He & Hd & Hof).
  assert (Hf' : fetch_word rsegs (ms_pc_val ms) = Some wi) by (rewrite (so_pc _ _ _ _ _ _ HS); exact Hf).
  assert (VBa : sv_vars_below n (sv_alu ALU_ADD (getr st rs) (VL off)) = true).
  { destruct (MemFX.st_vars_below_parts n st VB) as (P1r & _). apply (MemFX.sv_vars_below_alu n ALU_ADD _ (VL off) (or_introl eq_refl) (rf_allb_get _ _ _ P1r rs)). reflexivity. }
  assert (DA : den E' (sv_alu ALU_ADD (getr st1 rs) (VL off)) = Z_to_bv 64 p).
  { change (getr st1 rs) with (getr st rs). rewrite (den_reval n E E' HX _ VBa), EQP. apply bv_eq. rewrite Z_to_bv_unsigned, <- FPTR.
    symmetry. apply bv_wrap_small. rewrite bv_modulus_64. pose proof (bv_unsigned_in_range 64 (den E fPv)). rewrite bv_modulus_64 in H. lia. }
  destruct (PkStep.oracle_ILoad rsegs OPS E' st1 ms mo wi ins SZ1 true rd rs off p z rv HS1 PCB Hf' He Hd Hof DA ltac:(lia)
              ltac:(change (to_Z (msize_bytes SZ1)) with 1; unfold W64.two64; lia) RD1 Dv) as (ms' & STEP & MEM & HS2).
  apply (rz_step rsegs ms mo ms' K (mf_halted _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS))) (mf_lazy _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS))) (so_svc _ _ _ _ _ _ HS) STEP).
  exact (HK _ (or_introl eq_refl) E' ms' mo HX HMP HS2).
Qed.

End OPS.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.base stdpp.decidable stdpp.list stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Omono.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import F_syscalls.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Model OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Layout OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Steps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.OpsBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Tree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkOps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkPeek OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkBody.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsM OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.LdPart.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.StateGlue OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.RegsEqv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MemFX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CopyFX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.LdPartSound.
Import RMallocG.TwinB MemcpyG.TwinB HeapCtr.TwinB MemcpyCtr.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St Step Plan ValP MemP StepB StepM StepS PlanS CtrLib CtrA CtrFX HeapOp UB UG TR PK PKL.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Section OPS.
Variable IMGX : list iv.
Variable AW : alloc_world rsegs IMGX.
Variable CW : client_world.
Variable OPS : St.optable.

Hypothesis OPS_plain : St.plain_table OPS.
Hypothesis HOPS : heap_ops rsegs IMGX AW CW OPS.
Hypothesis CW3 : forall ca LB ws m, cw_holds CW 3 ca LB ws m -> PK.cw_pk_holds rsegs ca LB ws m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Ltac unfT := unfold T_NIL, T_BOOLEAN, T_POSINT, T_NEGINT, T_FLOAT64, T_STR, T_BIN, T_ARRAY, T_MAP, T_EXT, T_FLOAT32 in *.

Lemma nth_map_seq : forall {A} (f : nat -> A) n j d, (j < n)%nat -> nth j (map f (seq 0 n)) d = f j.
Proof.
  intros A f n j d Hj. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hj).
  rewrite map_nth, seq_nth by exact Hj. reflexivity.
Qed.

Lemma body_of_focus : forall bm z fo t (p n : Z),
  tree_wf bm z fo -> obj_type fo = t -> (t = T_STR \/ t = T_BIN \/ t = T_EXT) -> obj_ptr fo = p -> (PK.obj_via fo = n \/ obj_cnt fo = n) ->
  let N := (if t =? T_EXT then n + 1 else n) in
  0 <= n /\ N <= LIMIT /\ (p = 0 -> N = 0) /\ (p <> 0 -> in_zone z p N /\ readable bm p (Z.to_nat N)).
Proof.
  intros bm z fo t p n TW TY HT HP HN. cbv zeta.
  destruct fo; cbn [obj_type] in TY; subst t; unfT; try (exfalso; lia); cbn [obj_ptr PK.obj_via obj_cnt] in HP, HN;
    (assert (HN' : n0 = n) by (destruct HN; assumption)); clear HN; subst;
    cbn [tree_wf] in TW; cbn [Z.eqb Pos.eqb].
  - destruct TW as (A & B & C). unfold LIMIT in *. split; [lia|]. split; [lia|]. split; [exact B| exact C].
  - destruct TW as (A & B & C). unfold LIMIT in *. split; [lia|]. split; [lia|]. split; [exact B| exact C].
  - destruct TW as (A & B & C & D & E). unfold LIMIT in *. split; [lia|]. split; [lia|].
    split; [intros P0; exfalso; exact (C P0)| intros _; split; assumption].
Qed.

Lemma w2Zs_wadd_small : forall a b, - two63 <= w2Zs a + w2Z b < two63 -> w2Zs (wadd a b) = w2Zs a + w2Z b.
Proof.
  intros a b H. rewrite (w2Zs_eq (wadd a b)), w2Z_wt, wadd_ok.
  rewrite (w2Zs_eq a), (w2Z_wt a) in H |- *.
  pose proof (w2Z_range a) as Ra. pose proof (w2Z_range b) as Rb. unfold two63, two64 in *.
  destruct (Z.leb_spec 9223372036854775808 (w2Z a));
  destruct (Z_lt_le_dec (w2Z a + w2Z b) 18446744073709551616);
  try (rewrite (Z.mod_small (w2Z a + w2Z b)) by lia; destruct (Z.leb_spec 9223372036854775808 (w2Z a + w2Z b)); lia);
  try (replace (w2Z a + w2Z b) with ((w2Z a + w2Z b - 18446744073709551616) + 1 * 18446744073709551616) by lia;
       rewrite Z.mod_add, Z.mod_small by lia;
       destruct (Z.leb_spec 9223372036854775808 (w2Z a + w2Z b - 18446744073709551616)); lia).
Qed.

Lemma cell_apart_sound : forall E fs OFF n g c,
  facts_hold E fs -> PkBody.cell_apart fs OFF n g c = true ->
  0 <= to_Z (Mem.c_idx c) -> to_Z (Mem.c_idx c) + to_Z (Mem.c_w c) <= 8 -> 0 < to_Z (Mem.c_w c) ->
  bv_unsigned (den E OFF) + bv_unsigned (den E n) < two64 ->
  keyZ g = to_Z g /\
  (8 * to_Z g + to_Z (Mem.c_idx c) + to_Z (Mem.c_w c) <= bv_unsigned (den E OFF)
   \/ bv_unsigned (den E OFF) + bv_unsigned (den E n) <= 8 * to_Z g + to_Z (Mem.c_idx c)).
Proof.
  intros E fs OFF n g c Hfs H Hi Hiw Hw NW. unfold PkBody.cell_apart in H.
  apply andb_prop in H as [GM H]. apply Uint63.ltb_spec in GM. change (to_Z PkBody.G_MAX) with (2 ^ 59) in GM.
  pose proof (int_range g) as Rg. pose proof (int_range (Mem.c_idx c)) as Ri. pose proof (int_range (Mem.c_w c)) as Rw. rewrite two63_eq in Rg, Ri, Rw.
  assert (KG : keyZ g = to_Z g) by (destruct (keyZ_cases g) as [[_ ->]|[R _]]; [reflexivity| lia]).
  assert (E8 : to_Z (PrimInt63.lsl g 3) = 8 * to_Z g).
  { rewrite lsl_spec, wB_two63, two63_eq. change (2 ^ to_Z 3%uint63) with 8. rewrite Z.mod_small by lia. lia. }
  assert (EO : to_Z (PrimInt63.add (PrimInt63.lsl g 3) (Mem.c_idx c)) = 8 * to_Z g + to_Z (Mem.c_idx c)).
  { rewrite add_spec, E8, wB_two63, two63_eq. rewrite Z.mod_small by lia. reflexivity. }
  assert (EE : to_Z (PrimInt63.add (PrimInt63.add (PrimInt63.lsl g 3) (Mem.c_idx c)) (Mem.c_w c)) = 8 * to_Z g + to_Z (Mem.c_idx c) + to_Z (Mem.c_w c)).
  { rewrite add_spec, EO, wB_two63, two63_eq. rewrite Z.mod_small by lia. reflexivity. }
  split; [exact KG|].
  apply orb_prop in H as [H|H]; apply (known_leu_sound E _ _ _ Hfs) in H.
  - left. rewrite unsigned_VL, wlit_ok, EE in H. exact H.
  - right. rewrite unsigned_VL, wlit_ok, EO, den_sv_alu in H. cbn [alu64 alu] in H. rewrite bv_add_unsigned in H.
    unfold bv_wrap in H. pose proof (bv_unsigned_in_range 64 (den E OFF)) as X1. pose proof (bv_unsigned_in_range 64 (den E n)) as X2. rewrite bv_modulus_64 in X1, X2.
    rewrite bv_modulus_64 in H. unfold W64.two64 in H, NW. rewrite Z.mod_small in H by lia.
    exact H.
Qed.

Lemma to_Z_3 : to_Z 3%uint63 = 3. Proof. reflexivity. Qed.

Lemma den_unsextw : forall E fs v, facts_hold E fs -> den E (PkBody.unsextw fs v) = den E v.
Proof.
  intros E fs v Hfs. unfold PkBody.unsextw.
  destruct v as [| | |opw x y| | | | | | |]; try reflexivity. destruct opw; try reflexivity.
  destruct y as [z| | | | | | | | | |]; try reflexivity.
  destruct (weqb z wzero && wltu (snd (sv_bounds fs x)) (wlit 2147483648%uint63)) eqn:C; [| reflexivity].
  apply andb_prop in C as [Z0 LT]. apply weqb_eq in Z0. subst z.
  pose proof (ValP.sv_bounds_sound E fs Hfs x) as B. unfold ValP.inb in B.
  rewrite wltu_w2Z in LT. apply Z.ltb_lt in LT. rewrite wlit_ok in LT. change (to_Z 2147483648%uint63) with (2 ^ 31) in LT.
  cbn [den alu32 alu]. apply bv_eq. rewrite sext32_unsigned, bv_add_unsigned, !low32_ext.
  rewrite wbv_unsigned. change (w2Z wzero) with 0. rewrite (Z.mod_0_l (2 ^ 32)) by lia. rewrite Z.add_0_r.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  pose proof (bv_unsigned_in_range 64 (den E x)) as R.
  rewrite (Z.mod_small (bv_unsigned (den E x) mod 2 ^ 32) (2 ^ 32)) by (apply Z.mod_pos_bound; lia).
  rewrite (Z.mod_small (bv_unsigned (den E x)) (2 ^ 32)) by lia.
  unfold sx32Z. destruct (Z.leb_spec (2 ^ 31) (bv_unsigned (den E x))); [lia| reflexivity].
Qed.

Theorem pkmemcpy_sound : forall pc, to_Z pc = RMEMCPY_SYM ->
  contract_sound rsegs OPS MP PB (PkBody.pkmemcpy_c rsegs ERRNO pc).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply PkBody.pkmemcpy_c] in Happ. unfold PkBody.pkmemcpy_apply in Happ.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (CtrA.sym_offset (s_regs st) (getr st X10)) as [[kS OFF]|] eqn:DOFF; [|discriminate].
  destruct (PrimInt63.eqb kS 0%uint63 || PrimInt63.eqb kS STACK_ID) eqn:KS01; [discriminate|].
  apply orb_false_iff in KS01 as [KS0 KS1].
  destruct (IMap.find kS (s_regs st)) as [rS|] eqn:HkS; [|discriminate].
  cbv zeta in Happ.
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  set (rS' := PkBody.dst_region (s_facts st) OFF (getr st X12) rS) in Happ.
  set (st1 := setregs st (IMap.add kS rS' (s_regs st))) in Happ.
  destruct (havoc_errno rsegs ERRNO (clobber st1)) as [st2|] eqn:HE; [|discriminate].
  apply Some_inj in Happ. subst sts.
  apply andb_prop in C2 as [C2 SRC]. apply andb_prop in C2 as [C2 LE2]. apply andb_prop in C2 as [C2 LE1].
  apply andb_prop in C2 as [C2 Ws]. apply andb_prop in C2 as [BGs LOs]. apply Uint63.eqb_correct in LOs.

  destruct (call_sound OPS E st ms mo r HS CP) as [RV SVB POS B62 RA1 RA2 GR MI].
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  pose proof (Preg kS rS HkS) as ROs.

  set (BS := bv_unsigned (ev E kS)) in *. set (offZ := bv_unsigned (den E OFF)). set (N := bv_unsigned (den E (getr st X12))).
  assert (EN0 : N = bv_unsigned (den E (getr st X12))) by reflexivity.
  assert (A2 : PropExec.getr (ms_regs ms) 12%bv = Z_to_bv 64 N) by (rewrite <- reg_of_X12, GR; subst N; symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range 64 (den E OFF)) as OR. rewrite bv_modulus_64 in OR. fold offZ in OR.
  pose proof (bv_unsigned_in_range 64 (den E (getr st X12))) as NR. rewrite bv_modulus_64, <- EN0 in NR.
  clearbody N.
  apply (known_leu_sound E _ _ _ Pfacts) in LE1. apply (known_leu_sound E _ _ _ Pfacts) in LE2.
  fold offZ (hiZ E rS) in LE1. rewrite <- EN0 in LE2. rewrite den_sv_alu in LE2. cbn [alu64 alu] in LE2. rewrite bv_sub_unsigned in LE2. fold offZ (hiZ E rS) in LE2.
  pose proof (ro_range _ _ _ _ _ _ ROs KS0) as [RLs RHs]. fold BS in RLs, RHs. unfold W64.two64 in RHs.
  assert (LZs : loZ rS = 0) by (unfold loZ; rewrite LOs; reflexivity). rewrite LZs in RLs.
  pose proof (bv_unsigned_in_range 64 (den E (Mem.rg_hi rS))) as HSR. rewrite bv_modulus_64 in HSR. fold (hiZ E rS) in HSR.
  assert (SUM : offZ + N <= hiZ E rS).
  { unfold bv_wrap in LE2. rewrite bv_modulus_64 in LE2. rewrite Z.mod_small in LE2; unfold W64.two64 in *; lia. }
  set (D := BS + offZ).
  assert (DA : den E (getr st X10) = Z_to_bv 64 D).
  { rewrite (sym_offset_sound E (s_regs st) _ kS OFF DOFF). apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. subst D BS offZ. reflexivity. }
  destruct (MemFX.based_rw_cells rsegs (s_priv st) E (ms_mem ms) kS rS offZ (Z.to_nat N) ROs KS0 Ws ltac:(lia) ltac:(lia)) as (junk & LJ & DST).
  fold BS in DST. fold D in DST.
  pose proof two64_eq as T64.

  assert (SRCX : exists S src, PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 S /\ 0 <= S < 2 ^ 64 /\ S + N <= 2 ^ 64 /\
                 length src = Z.to_nat N /\ bytes_at rsegs (ms_mem ms) S src /\ (S + N <= D \/ D + N <= S)).
  { apply orb_prop in SRC as [SRC|SRC]; [apply orb_prop in SRC as [SRC|SRC]|].
    -
      unfold PkBody.stack_src_ok in SRC.
      destruct (getr st X11) as [|k1 o| | | | | | | | |] eqn:HX11; try discriminate.
      destruct (getr st X12) as [nw| | | | | | | | | |] eqn:HX12; try discriminate.
      destruct (getr st X2) as [|k2 osp| | | | | | | | |] eqn:HX2; try discriminate.
      destruct (IMap.find STACK_ID (s_regs st)) as [r1|] eqn:Hr1; [|discriminate].
      apply andb_prop in SRC as [SRC KEYS]. apply andb_prop in SRC as [SRC NWM]. apply andb_prop in SRC as [SRC NWT]. apply andb_prop in SRC as [K1 K2].
      apply Uint63.eqb_correct in K1. apply Uint63.eqb_correct in K2. subst k1 k2. apply negb_true_iff in NWT. apply Uint63.leb_spec in NWM.
      assert (NW4 : w2Z nw = to_Z (wl nw)) by (unfold w2Z; rewrite NWT; lia).
      change (to_Z PkBody.STK_MAX) with 4096 in NWM.
      destruct (Mem.okey o) as [i|] eqn:Hi; [|discriminate]. destruct (Mem.okey (wadd o nw)) as [ie|] eqn:Hie; [|discriminate].
      destruct (Mem.okey osp) as [ksp|] eqn:Hksp; [|discriminate].
      destruct (Mem.rg_hi r1) as [h| | | | | | | | | |] eqn:Hh; try discriminate.
      destruct (Mem.okey h) as [kh|] eqn:Hkh; [|discriminate].
      apply andb_prop in KEYS as [KEYS L4]. apply andb_prop in KEYS as [KEYS L3]. apply andb_prop in KEYS as [L1 L2].
      rewrite kleb_keyZ in L1, L2, L3, L4. apply Z.leb_le in L1. apply Z.leb_le in L2. apply Z.leb_le in L3. apply Z.leb_le in L4.
      destruct (okey_sound _ _ Hi) as [Ei Ri]. destruct (okey_sound _ _ Hie) as [Eie Rie]. destruct (okey_sound _ _ Hkh) as [Ekh Rkh].
      rewrite ?half63 in Ri, Rie, Rkh. unfold W64.two63 in Ri, Rie, Rkh.
      pose proof (so_reg _ _ _ _ _ _ HS _ _ Hr1) as RO1.
      pose proof (ro_range _ _ _ _ _ _ RO1 eq_refl) as [RLO1 RHI1]. unfold W64.two64 in RHI1.
      set (B1 := bv_unsigned (ev E STACK_ID)) in *.
      assert (Ehi : keyZ kh <= hiZ E r1).
      { unfold hiZ. rewrite Hh, unsigned_VL, Ekh, w2Zs_eq. unfold W64.two64. destruct (wt h); lia. }
      assert (NWZ : N = w2Z nw) by (rewrite EN0, ?HX12, unsigned_VL; reflexivity).
      pose proof (w2Z_range nw) as Rnw. pose proof (int_range (wl nw)) as Rnw'. rewrite two63_eq in Rnw'.
      assert (Eie' : keyZ ie = keyZ i + N).
      { rewrite Eie, NWZ, w2Zs_wadd_small; [rewrite Ei; reflexivity|]. rewrite <- Ei. unfold W64.two63 in *. lia. }
      unfold loZ in RLO1.
      set (S := B1 + keyZ i).
      assert (ES : den E (VP STACK_ID o) = Z_to_bv 64 S).
      { apply bv_eq. rewrite Z_to_bv_unsigned, den_VP, <- Ei. fold B1. subst S. unfold bv_wrap. rewrite bv_modulus_64. reflexivity || (apply Z.mod_small; unfold W64.two64; lia) || (symmetry; apply Z.mod_small; unfold W64.two64; lia). }
      destruct (MemFX.based_bytes rsegs (s_priv st) E (ms_mem ms) STACK_ID r1 (keyZ i) (Z.to_nat N) RO1 eq_refl ltac:(unfold loZ; lia) ltac:(lia)) as (src & LEN & SRCB).
      fold B1 in SRCB. fold S in SRCB.
      exists S, src. split; [rewrite <- reg_of_X11, GR, ?HX11; exact ES|]. split; [subst S; lia|]. split; [subst S; lia|].
      split; [exact LEN|]. split; [exact SRCB|].
      destruct (Z.eq_dec N 0) as [->|N0]; [lia|].
      apply (CopyFX.sep_of_pointwise S D N ltac:(lia)). intros j j' Hj Hj' EQ.
      apply (Pdisj STACK_ID r1 kS rS Hr1 HkS ltac:(intros X; rewrite <- X in KS1; discriminate KS1) eq_refl KS0 (or_intror Ws) (S + j)).
      fold B1 BS. rewrite LZs. split; [unfold loZ; subst S; lia| subst D; lia].
    -
      unfold PkBody.based_src_ok in SRC.
      destruct (CtrA.sym_offset (s_regs st) (getr st X11)) as [[kd OFFs]|] eqn:SOFF; [|discriminate].
      destruct (IMap.find kd (s_regs st)) as [rd|] eqn:Hkd; [|discriminate].
      apply andb_prop in SRC as [SRC LE4]. apply andb_prop in SRC as [SRC LE3]. apply andb_prop in SRC as [SRC LOd].
      apply andb_prop in SRC as [Kd0 KdS]. apply negb_true_iff in Kd0. apply negb_true_iff in KdS. apply Uint63.eqb_correct in LOd.
      pose proof (Preg kd rd Hkd) as ROd.
      set (Bd := bv_unsigned (ev E kd)) in *. set (offS := bv_unsigned (den E OFFs)).
      pose proof (bv_unsigned_in_range 64 (den E OFFs)) as OSR. rewrite bv_modulus_64 in OSR. fold offS in OSR.
      apply (known_leu_sound E _ _ _ Pfacts) in LE3. apply (known_leu_sound E _ _ _ Pfacts) in LE4.
      fold offS (hiZ E rd) in LE3. rewrite <- EN0 in LE4. rewrite den_sv_alu in LE4. cbn [alu64 alu] in LE4. rewrite bv_sub_unsigned in LE4. fold offS (hiZ E rd) in LE4.
      pose proof (ro_range _ _ _ _ _ _ ROd Kd0) as [RLd RHd]. fold Bd in RLd, RHd. unfold W64.two64 in RHd.
      assert (LZd : loZ rd = 0) by (unfold loZ; rewrite LOd; reflexivity). rewrite LZd in RLd.
      pose proof (bv_unsigned_in_range 64 (den E (Mem.rg_hi rd))) as HDR. rewrite bv_modulus_64 in HDR. fold (hiZ E rd) in HDR.
      assert (SUMd : offS + N <= hiZ E rd).
      { unfold bv_wrap in LE4. rewrite bv_modulus_64 in LE4. rewrite Z.mod_small in LE4; unfold W64.two64 in *; lia. }
      set (S := Bd + offS).
      assert (SA : den E (getr st X11) = Z_to_bv 64 S).
      { rewrite (sym_offset_sound E (s_regs st) _ kd OFFs SOFF). apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. subst S Bd offS. reflexivity. }
      destruct (MemFX.based_bytes rsegs (s_priv st) E (ms_mem ms) kd rd offS (Z.to_nat N) ROd Kd0 ltac:(lia) ltac:(lia)) as (src & LEN & SRCB).
      fold Bd in SRCB. fold S in SRCB.
      exists S, src. split; [rewrite <- reg_of_X11, GR; exact SA|]. split; [subst S; lia|]. split; [subst S; lia|].
      split; [exact LEN|]. split; [exact SRCB|].
      destruct (Z.eq_dec N 0) as [->|N0]; [lia|].
      apply (CopyFX.sep_of_pointwise S D N ltac:(lia)). intros j j' Hj Hj' EQ.
      apply (Pdisj kd rd kS rS Hkd HkS ltac:(apply Uint63.eqb_false_spec; exact KdS) Kd0 KS0 (or_intror Ws) (S + j)).
      fold D Bd BS. rewrite LZd, LZs. split; [subst S; lia| lia].
    -
      unfold PkBody.body_src_ok in SRC.
      destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
      apply andb_prop in SRC as [MD SRC]. apply Uint63.eqb_correct in MD. subst mdi.
      destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
        try discriminate.
      destruct (PkBody.body_src (s_facts st) eb rootT n1 P1 cf fT fN fP) as [[[fTv fNv] fPv]|] eqn:SRCB; [|discriminate].
      destruct fTv as [t| | | | | | | | | |]; try discriminate.
      apply andb_prop in SRC as [SRC DEQN]. apply andb_prop in SRC as [TY DEQP].

      destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
      pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
      destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
      rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
      apply CW3 in HC. unfold PK.cw_pk_holds in HC. cbn [map PK.decode_pk] in HC.
      destruct HC as (g & ls & L & P & O & Wk & M & GH).
      pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
      cbn [PK.a_root PK.a_rootT PK.a_n1 PK.a_P1 PK.a_c0 PK.a_eb PK.a_ee PK.a_ecap PK.a_tptr PK.a_trest PK.a_tmap PK.a_tkey PK.a_cf PK.a_fT PK.a_fN PK.a_fP] in LCF.
      pose proof P as (LV & EL & SZ & VE & CE & ZV).
      pose proof M as (TW & KA & [IC IB] & CH & PE).
      assert (FO : exists fo, tree_wf (bmem_of rsegs (ms_mem ms)) (PK.k_zone g) fo /\ obj_type fo = bv_unsigned (den E (VL t))
                /\ obj_ptr fo = bv_unsigned (den E fPv) /\ (PK.obj_via fo = bv_unsigned (den E fNv) \/ obj_cnt fo = bv_unsigned (den E fNv))).
      { unfold PkBody.body_src in SRCB. destruct (sv_eqb eb (VL wzero)) eqn:EB0.
        - apply sv_eqb_eq in EB0. subst eb. injection SRCB as <- <- <-.
          cbn [PK.a_root PK.a_rootT PK.a_n1 PK.a_P1 PK.a_c0 PK.a_eb] in LT, LN, LP, Leb.
          assert (VB0 : v_begin (PK.k_evec g) = 0) by (rewrite Leb; cbn [den]; rewrite wbv_unsigned; reflexivity).
          destruct VE as [(_ & _ & ->)|[(_ & _ & VNZ & _) _]]; [| exfalso; exact (VNZ VB0)].
          exists (PK.k_tree g). split; [exact TW|]. split; [exact LT|]. split; [exact LP|]. right. exact LN.
        - unfold dec_false in SRCB. destruct (decide_eq0 (s_facts st) cf) as [[|]|] eqn:DZ; try discriminate. injection SRCB as <- <- <-.
          pose proof (decide_eq0_sound E (s_facts st) Pfacts _ _ DZ) as CNZ. apply (proj1 (eqb_iff _ _ false)) in CNZ.
          assert (CF0 : bv_unsigned (den E cf) <> 0) by (intros X; apply CNZ; apply bv_eq; rewrite X; reflexivity).
          destruct (LCF CF0) as (LSNE & CFA & fo & FN & FT & FVIA & FPTR).
          pose proof (last_opt_spec ls) as LS. unfold PK.focus_node in FN.
          destruct (last_opt ls) as [l|] eqn:LAST; [| contradiction]. destruct LS as [ls0 ELS].
          assert (HLV : PK.levels_ok (PK.k_tree g) (ls0 ++ [l])) by (rewrite <- ELS; exact LV).
          exists fo. split; [exact (focus_tree_wf _ _ _ _ _ _ TW HLV FN)|]. auto. }
      clear LCF SRCB. destruct FO as (fo & TWF & FT & FPTR & FVIA).
      assert (HT : w2Z t = T_STR \/ w2Z t = T_BIN \/ w2Z t = T_EXT).
      { unfold PkBody.T_STRw, PkBody.T_BINw, PkBody.T_EXTw in TY. unfT.
        apply orb_prop in TY as [TY|TY]; [apply orb_prop in TY as [TY|TY]|]; apply (proj1 (weqb_ok _ _)) in TY; subst t;
          rewrite ?w2Z_wlit || idtac; cbn; auto. }
      assert (FT' : obj_type fo = w2Z t) by (rewrite FT; cbn [den]; rewrite wbv_unsigned; reflexivity).
      set (p := obj_ptr fo) in *. set (n := bv_unsigned (den E fNv)) in *.
      pose proof (body_of_focus (bmem_of rsegs (ms_mem ms)) (PK.k_zone g) fo (w2Z t) p n TWF FT' HT eq_refl FVIA) as BODY. cbv zeta in BODY.
      set (N' := if w2Z t =? T_EXT then n + 1 else n) in *.
      destruct BODY as (N0 & NL & PZ & PNZ).
      unfold dec_true in DEQP.
      destruct (decide_eq (s_facts st) (getr st X11) (if weqb t PkBody.T_EXTw then sv_alu ALU_ADD fPv (VL wone) else fPv)) as [[|]|] eqn:DQP; try discriminate.
      pose proof (decide_eq_sound E (s_facts st) Pfacts _ _ _ DQP) as EQP. apply (proj1 (eqb_iff _ _ true)) in EQP.
      unfold dec_true in DEQN.
      destruct (decide_eq (s_facts st) (getr st X12) (PkBody.unsextw (s_facts st) (narrow_f (s_facts st) fNv))) as [[|]|] eqn:DQN; try discriminate.
      pose proof (eq_trans (den_unsextw E (s_facts st) _ Pfacts) (ValP.den_narrow_f E (s_facts st) Pfacts fNv)) as DNF.
      pose proof (decide_eq_sound E (s_facts st) Pfacts _ _ _ DQN) as EQN. apply (proj1 (eqb_iff _ _ true)) in EQN.
      assert (NN : N = n) by (rewrite EN0, EQN, DNF; reflexivity).
      assert (EN : N' = (if w2Z t =? T_EXT then n + 1 else n)) by reflexivity. clearbody N'. unfT.

      assert (T9 : weqb t (wlit 9%uint63) = (w2Z t =? 9)).
      { destruct (weqb t (wlit 9%uint63)) eqn:T9.
        - apply (proj1 (weqb_ok _ _)) in T9. subst t. reflexivity.
        - symmetry. apply Z.eqb_neq. intros X. destruct t as [tt tl]. unfold w2Z in X. cbn [wt wl] in X.
          unfold weqb, wlit in T9. cbn [wt wl] in T9. destruct tt; [pose proof (Uint63.to_Z_bounded tl); unfold W64.two63 in X; lia|].
          cbn [Bool.eqb andb] in T9. apply Uint63.eqb_false_spec in T9. apply T9. apply Uint63.to_Z_inj. change (to_Z 9%uint63) with 9. lia. }
      unfold PkBody.T_EXTw in EQP. rewrite T9 in EQP.
      set (isx := if w2Z t =? 9 then 1 else 0).
      assert (ENI : N' = n + isx /\ 0 <= isx <= 1) by (subst isx; rewrite EN; destruct (w2Z t =? 9); lia).
      clear EN. destruct ENI as [EN IR].
      pose proof (bv_unsigned_in_range 64 (den E fPv)) as PR. rewrite bv_modulus_64, <- FPTR in PR.
      assert (SP : bv_unsigned (den E (getr st X11)) = (p + isx) mod 2 ^ 64).
      { rewrite EQP. unfold isx. destruct (w2Z t =? 9).
        - rewrite den_sv_alu. cbn [alu64 alu]. rewrite bv_add_unsigned, <- FPTR, unsigned_VL. change (w2Z wone) with 1.
          unfold bv_wrap. rewrite bv_modulus_64. reflexivity.
        - rewrite <- FPTR, Z.add_0_r, Z.mod_small by lia. reflexivity. }
      clearbody isx.
      set (S := bv_unsigned (den E (getr st X11))) in *.
      pose proof (bv_unsigned_in_range 64 (den E (getr st X11))) as SR. rewrite bv_modulus_64 in SR. fold S in SR.

      assert (SRCX : N = 0 \/ (N <> 0 /\ p <> 0 /\ S = p + isx /\ p + N' <= 2 ^ 64 /\
                     (exists src, length src = Z.to_nat N /\ bytes_at rsegs (ms_mem ms) S src) /\
                     (exists c, In c (z_chunks (PK.k_zone g)) /\ in_chunk c p N'))).
      { destruct (Z.eq_dec N 0) as [Z0|NZ0]; [left; exact Z0| right].
        assert (PN0 : p <> 0) by (intros P0; pose proof (PZ P0); lia).
        destruct (PNZ PN0) as [IZ [v RD]].
        pose proof IZ as (c & Hc & ICc).
        destruct (aw_blocks_ok rsegs IMGX AW _ LB _ (ms_mem ms) mo (chunk_block c) HA
                    (proj1 O _ ltac:(unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc))) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
        unfold chunk_block in Bc1, Bc2, Bc3. cbn [fst snd] in Bc1, Bc2, Bc3.
        assert (PB8 : 0 <= p /\ p + N' <= 2 ^ 64) by (unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in ICc; unfold CHUNK_HDR in *; lia).
        assert (ES : S = p + isx) by (rewrite SP; apply Z.mod_small; lia).
        split; [exact NZ0|]. split; [exact PN0|]. split; [exact ES|]. split; [lia|]. split; [| exists c; auto].
        exists (map (fun i => Z_to_bv 8 (zbyte v (Z.of_nat i + isx))) (seq 0 (Z.to_nat N))).
        assert (LENs : length (map (fun i => Z_to_bv 8 (zbyte v (Z.of_nat i + isx))) (seq 0 (Z.to_nat N))) = Z.to_nat N) by (rewrite length_map, length_seq; reflexivity).
        split; [exact LENs|].
        apply CopyFX.bytes_at_of_rb; [lia| rewrite LENs; lia|]. rewrite LENs. intros j Hj.
        pose proof (rdZ_bytes _ _ _ _ (bmem_of_bytes_range rsegs (ms_mem ms)) RD (j + isx) ltac:(lia)) as X. unfold bmem_of in X.
        replace ((0 <=? p + (j + isx)) && (p + (j + isx) <? two64)) with true in X by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
        rewrite ES. replace (p + isx + j) with (p + (j + isx)) by lia.
        destruct (rb rsegs (ms_mem ms) (p + (j + isx))) as [b|]; [|discriminate X]. cbn [option_map] in X. injection X as X.
        f_equal. rewrite nth_map_seq by lia. cbn beta.
        apply bv_eq. rewrite X, Z2Nat.id by lia. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
        pose proof (zbyte_range v (j + isx)). change (bv_modulus 8) with 256. lia. }
      assert (A1 : PropExec.getr (ms_regs ms) 11%bv = Z_to_bv 64 S) by (rewrite <- reg_of_X11, GR; subst S; symmetry; apply Z_to_bv_bv_unsigned).
      destruct SRCX as [Z0|(NZ0 & PN0 & ES & PB8 & (src & LENS & SRC') & (c & Hc & ICc))].
      {
        exists S, []. split; [exact A1|]. split; [lia|]. split; [lia|]. split; [rewrite Z0; reflexivity|].
        split; [| lia]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. }
      exists S, src. split; [exact A1|]. split; [lia|]. split; [lia|]. split; [exact LENS|]. split; [exact SRC'|].

      assert (INLB : In (chunk_block c) LB) by (apply (proj1 O); unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc).
      destruct (aw_blocks_ok rsegs IMGX AW _ LB _ (ms_mem ms) mo (chunk_block c) HA INLB) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
      unfold chunk_block in Bc1, Bc2, Bc3, Bc5. cbn [fst snd] in Bc1, Bc2, Bc3, Bc5.
      apply (CopyFX.sep_of_pointwise S D N ltac:(lia)). intros j j' Hj Hj' EQ.
      assert (INB : in_iv (fst c, CHUNK_HDR + snd c) (S + j)) by (unfold in_iv, in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in *; cbn [fst snd]; lia).
      assert (FP : Exists (fun q => fst q <= S + j < snd q) (St.op_fp OPS (op_id o) (map (den E) (op_args o)))).
      { rewrite OID, (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ _ _ _ _ (S + j) (DECf E))).
        split; [lia|]. split; [exact (Bc5 _ INB)|].
        intros IW. apply in_ws_map_iff in IW as (w & Hw & INW).
        pose proof (proj1 (Forall_forall _ _) WF (wden E w) (in_map _ _ _ Hw)) as (_ & _ & _ & [[KSk CEk]|OTHERk]).
        - unfold in_iv, w_iv in INW. unfold in_iv in INB. cbn [fst snd] in INW, INB. lia.
        - assert (NK : w_kind (wden E w) <> K_STACK) by (destruct OTHERk as [[-> _]|[KS _]]; [discriminate| unfold K_SUB, K_STACK in *; lia]).
          destruct (proj1 (Forall_forall _ _) Wk (wden E w) (in_map _ _ _ Hw) NK) as [[_ DISJ]|[_ ET]].
          + apply (DISJ (chunk_block c) ltac:(unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc) (S + j) INW). exact INB.
          + exact (PK.safe_zone g ls LB (map (wden E) ws) P O p N' (S + j) ltac:(lia) (ex_intro _ c (conj Hc ICc)) ltac:(lia) (wden E w) (in_map _ _ _ Hw) ET INW). }
      destruct (proj1 (Forall_forall _ _) Papart o (op_in_In st o OPS1) (S + j) FP) as [NB _].
      apply NB. exists kS, rS. split; [exact HkS|]. split; [exact KS0|]. fold BS. rewrite LZs. rewrite EQ. subst D. lia. }
  destruct SRCX as (S & src & A1 & S0 & SN & LEN & SRC' & SEP).

  assert (A0 : PropExec.getr (ms_regs ms) 10%bv = Z_to_bv 64 D) by (rewrite <- reg_of_X10, GR; exact DA).
  pose proof (ms_shape OPS E st ms mo HS RV) as MSE. rewrite Hspc in MSE. cbn [c_pc PkBody.pkmemcpy_c] in MSE. rewrite Hpc in MSE.
  rewrite MSE.
  apply (memcpy_G (ms_regs ms) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) mo D S N src junk K A0 A1 A2
           ltac:(lia) ltac:(lia) ltac:(lia) RA1 SRC' LEN DST SEP MI (mf_halted _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS))) (mf_lazy _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS)))).
  intros R' M' KEPT A0' MU WM MI' RW BA OM.

  assert (RO' : St.region_ok rsegs (s_priv st) E M' kS rS').
  { destruct RW as [[CWF BY] (_ & _ & WR)]. cbn [cells_size csize cells_bytes cbytes Nat.add] in BY, WR. rewrite app_nil_r in BY. rewrite Nat.add_0_r in WR.
    destruct BY as (_ & _ & BY). rewrite LEN in BY.
    destruct ROs as [Abst Arange Avalid Acells Ain Abg].
    assert (VALID : forall a, BS + loZ rS <= a < BS + hiZ E rS -> rb rsegs M' a <> None /\ (Mem.rg_w rS = true -> wb rsegs M' a = true) /\ find_segment rsegs a 1 = None).
    { intros a Ha. destruct (Avalid KS0 a Ha) as (V1 & V2 & V3). rewrite LZs in Ha.
      destruct (Z_lt_le_dec a D) as [L0|G0]; [| destruct (Z_lt_le_dec a (D + N)) as [L2|G2]].
      + assert (EQM : M' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) by (apply (memcpy_frame _ _ D N MU a); unfold W64.two64 in *; lia).
        split; [| split; [| exact V3]]; [unfold rb in V1 |- *; rewrite EQM; exact V1|].
        intros W. apply (proj2 (MemFX.wb_wview rsegs _ _)). apply WM. apply (proj1 (MemFX.wb_wview rsegs _ _)). exact (V2 W).
      + split; [| split; [| exact V3]].
        * rewrite MemFX.rb_mrd. replace a with (D + Z.of_nat (Z.to_nat (a - D))) by lia. rewrite BY by lia.
          destruct (nth_error src (Z.to_nat (a - D))) eqn:X; [congruence|]. apply nth_error_None in X. lia.
        * intros _. apply (proj2 (MemFX.wb_wview rsegs _ _)). replace a with (D + (a - D)) by lia. apply WR. lia.
      + assert (EQM : M' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) by (apply (memcpy_frame _ _ D N MU a); unfold W64.two64 in *; lia).
        split; [| split; [| exact V3]]; [unfold rb in V1 |- *; rewrite EQM; exact V1|].
        intros W. apply (proj2 (MemFX.wb_wview rsegs _ _)). apply WM. apply (proj1 (MemFX.wb_wview rsegs _ _)). exact (V2 W). }
    unfold rS', PkBody.dst_region.
    destruct (PkBody.cells_apart (s_facts st) OFF (getr st X12) (Mem.rg_cells rS)) eqn:APART.
    -
      constructor; cbn [Mem.rg_lo Mem.rg_hi Mem.rg_w Mem.rg_bg Mem.rg_cells].
      + exact Abst.
      + exact Arange.
      + intros K0 a Ha. exact (VALID a Ha).
      + intros gg gr Hg. destruct (Acells gg gr Hg) as [SS FA]. split; [exact SS|].
        apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) FA c Hc) as (C1 & C2 & C3 & C4).
        split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. intros i Hi.
        unfold PkBody.cells_apart in APART.
        pose proof (proj1 (IMap.forallb_spec _ _ Abst) APART gg gr Hg) as FB. cbn beta in FB.
        pose proof (proj1 (forallb_forall _ _) FB c Hc) as CA.
        destruct (cell_apart_sound E (s_facts st) OFF (getr st X12) gg c Pfacts CA C1 C3 C2 ltac:(fold offZ; rewrite <- EN0; unfold W64.two64; lia)) as [KG APT].
        fold offZ in APT. rewrite <- EN0 in APT.
        pose proof (Ain gg gr c i Hg Hc Hi) as AIN. cbv zeta in AIN. destruct AIN as [P1 _]. specialize (P1 KS0). rewrite LZs in P1.
        rewrite <- (C4 i Hi). unfold rb. fold BS.
        rewrite (memcpy_frame _ _ D N MU (BS + 8 * keyZ gg + to_Z (Mem.c_idx c) + i)); [reflexivity| unfold W64.two64; lia|]. subst D. rewrite KG in P1. rewrite KG. lia.
      + exact Ain.
      + intros oo H1 H2 U. exact I.
    -
      constructor; cbn [Mem.rg_lo Mem.rg_hi Mem.rg_w Mem.rg_bg Mem.rg_cells].
      + exact I.
      + exact Arange.
      + intros K0 a Ha. exact (VALID a Ha).
      + intros gg gr Hg. cbn in Hg. discriminate Hg.
      + intros gg gr c i Hg. cbn in Hg. discriminate Hg.
      + intros oo H1 H2 U. exact I. }
  pose proof (MemFX.st_ok_based_write rsegs OPS E st (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) None (ms_mem ms) M' (seg_rom rsegs) mo kS rS rS'
                ltac:(rewrite <- MSE; exact HS) HkS KS0 Ws
                ltac:(intros a Ha NI; apply (memcpy_frame _ _ D N MU a Ha); fold BS in NI; rewrite LZs in NI; lia)
                OM (minv_of_mem_inv M' MI') RO' ltac:(unfold loZ, rS', PkBody.dst_region; cbn [Mem.rg_lo]; lia)
                ltac:(unfold hiZ, rS', PkBody.dst_region; cbn [Mem.rg_hi]; lia)) as HS1.
  assert (SVB1 : st_vars_below (s_next st) st1 = true).
  { apply (MemFX.st_vars_below_setregs (s_next st) st kS rS rS' Pbst SVB HkS).
    destruct (MemFX.st_vars_below_parts (s_next st) st SVB) as (P1 & P2 & P3 & P4 & P5 & P6).
    pose proof (proj1 (IMap.forallb_spec _ _ Pbst) P4 kS rS HkS) as RVB. cbn beta in RVB.
    apply andb_prop in RVB as [_ RVB].
    unfold region_vars_below in RVB |- *. unfold rS', PkBody.dst_region. cbn [Mem.rg_hi Mem.rg_cells].
    apply andb_prop in RVB as [RH RC]. rewrite RH.
    destruct (PkBody.cells_apart (s_facts st) OFF (getr st X12) (Mem.rg_cells rS)); [exact RC| reflexivity]. }
  assert (HKR : forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr (ms_regs ms) (reg_of_r5 x)).
  { intros x N0' CPx. destruct (r5_eqb x X10) eqn:Q.
    - apply r5_eqb_spec in Q. subst x. rewrite reg_of_X10, A0', A0. reflexivity.
    - apply KEPT. apply kept_or_clobbered; [exact N0'| intros ->; rewrite r5_eqb_refl in Q; discriminate| exact CPx]. }
  destruct (MemFX.ccall_frame rsegs OPS E st1 ERRNO r st2 (ms_regs ms) R' (ms_fregs ms)
              (Z_to_bv 64 RMEMCPY_SYM) (ms_fcsr ms) M' (seg_rom rsegs) mo HS1 RV SVB1 POS B62 HKR HE) as (ST & NX & _).
  rewrite <- RA2 in ST.
  exact (HK _ (or_introl eq_refl) _ _ _ (MemFX.cenv_ext _ E _ R' M' ERRNO) HMP ST).
Qed.

Lemma dec_true_inv : forall x, dec_true x = true -> x = Some true.
Proof. intros [[|]|]; cbn; congruence. Qed.

Lemma st_ok_facts_next : forall E st ms mo fs' nx,
  St.st_ok rsegs OPS E st ms mo -> Forall (fact_holds E) fs' ->
  St.st_ok rsegs OPS E (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (fs' ++ s_facts st) (s_ops st) (s_priv st) nx) ms mo.
Proof.
  intros E st ms mo fs' nx HS HF.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  apply Forall_app. split; [exact HF| exact Pfacts].
Qed.

Theorem pkextb_sound : forall pc, contract_sound rsegs OPS MP PB (PkBody.pkextb_c rsegs pc).
Proof.
  intros pc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply PkBody.pkextb_c] in Happ. unfold PkBody.pkextb_apply in Happ.
  destruct (LdPart.load_at rsegs (s_pc st)) as [[[[[sz sx] rd] rs] off]|] eqn:LA; [|discriminate].
  destruct sz; try discriminate. destruct sx; [|discriminate].
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 3) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi. cbn [negb] in Happ.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  destruct (PkBody.body_src (s_facts st) eb rootT n1 P1 cf fT fN fP) as [[[fTv fNv] fPv]|] eqn:SRCB; [|discriminate].
  destruct fTv as [t| | | | | | | | | |]; try discriminate.
  cbv zeta in Happ.
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  apply Some_inj in Happ. subst sts.
  apply andb_prop in C2 as [C2 PCB]. apply andb_prop in C2 as [C2 NLT]. apply andb_prop in C2 as [C2 NPOS].
  apply andb_prop in C2 as [C2 VB]. apply andb_prop in C2 as [C2 RD0]. apply andb_prop in C2 as [TY DEQP].
  apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS. apply Uint63.ltb_spec in NLT.
  set (n := s_next st) in *.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].

  destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
  apply CW3 in HC. unfold PK.cw_pk_holds in HC. cbn [map PK.decode_pk] in HC.
  destruct HC as (g & ls & L & P & O & Wk & M & GH).
  pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
  cbn [PK.a_root PK.a_rootT PK.a_n1 PK.a_P1 PK.a_c0 PK.a_eb PK.a_ee PK.a_ecap PK.a_tptr PK.a_trest PK.a_tmap PK.a_tkey PK.a_cf PK.a_fT PK.a_fN PK.a_fP] in LCF.
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  pose proof M as (TW & KA & [IC IB] & CH & PE).
  assert (FO : exists fo, tree_wf (bmem_of rsegs (ms_mem ms)) (PK.k_zone g) fo /\ obj_type fo = bv_unsigned (den E (VL t))
            /\ obj_ptr fo = bv_unsigned (den E fPv) /\ (PK.obj_via fo = bv_unsigned (den E fNv) \/ obj_cnt fo = bv_unsigned (den E fNv))).
  { unfold PkBody.body_src in SRCB. destruct (sv_eqb eb (VL wzero)) eqn:EB0.
    - apply sv_eqb_eq in EB0. subst eb. injection SRCB as <- <- <-.
      cbn [PK.a_root PK.a_rootT PK.a_n1 PK.a_P1 PK.a_c0 PK.a_eb] in LT, LN, LP, Leb.
      assert (VB0 : v_begin (PK.k_evec g) = 0) by (rewrite Leb; cbn [den]; rewrite wbv_unsigned; reflexivity).
      destruct VE as [(_ & _ & ->)|[(_ & _ & VNZ & _) _]]; [| exfalso; exact (VNZ VB0)].
      exists (PK.k_tree g). split; [exact TW|]. split; [exact LT|]. split; [exact LP|]. right. exact LN.
    - unfold dec_false in SRCB. destruct (decide_eq0 (s_facts st) cf) as [[|]|] eqn:DZ; try discriminate. injection SRCB as <- <- <-.
      pose proof (decide_eq0_sound E (s_facts st) Pfacts _ _ DZ) as CNZ. apply (proj1 (eqb_iff _ _ false)) in CNZ.
      assert (CF0 : bv_unsigned (den E cf) <> 0) by (intros X; apply CNZ; apply bv_eq; rewrite X; reflexivity).
      destruct (LCF CF0) as (LSNE & CFA & fo & FN & FT & FVIA & FPTR).
      pose proof (last_opt_spec ls) as LS. unfold PK.focus_node in FN.
      destruct (last_opt ls) as [l|] eqn:LAST; [| contradiction]. destruct LS as [ls0 ELS].
      assert (HLV : PK.levels_ok (PK.k_tree g) (ls0 ++ [l])) by (rewrite <- ELS; exact LV).
      exists fo. split; [exact (focus_tree_wf _ _ _ _ _ _ TW HLV FN)|]. auto. }
  clear LCF SRCB. destruct FO as (fo & TWF & FT & FPTR & FVIA).
  unfold PkBody.T_EXTw in TY. apply (proj1 (weqb_ok _ _)) in TY. subst t.
  assert (FT' : obj_type fo = T_EXT) by (rewrite FT; cbn [den]; rewrite wbv_unsigned; reflexivity).
  set (p := obj_ptr fo) in *. set (nb := bv_unsigned (den E fNv)) in *.
  pose proof (body_of_focus (bmem_of rsegs (ms_mem ms)) (PK.k_zone g) fo T_EXT p nb TWF FT' ltac:(unfT; lia) eq_refl FVIA) as BODY.
  cbv zeta in BODY. unfT. replace (9 =? 9) with true in BODY by reflexivity.
  destruct BODY as (N0 & NL & PZ & PNZ).
  assert (PN0 : p <> 0) by (intros P0; pose proof (PZ P0); lia).
  destruct (PNZ PN0) as [IZ [v RD]].
  pose proof IZ as (c & Hc & ICc).
  destruct (aw_blocks_ok rsegs IMGX AW _ LB _ (ms_mem ms) mo (chunk_block c) HA
              (proj1 O _ ltac:(unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc))) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
  unfold chunk_block in Bc1, Bc2, Bc3. cbn [fst snd] in Bc1, Bc2, Bc3.
  pose proof two64_eq as T64.
  assert (PB8 : 0 <= p /\ p + (nb + 1) <= 2 ^ 64) by (unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in ICc; unfold CHUNK_HDR in *; lia).

  pose proof (rdZ_bytes _ _ _ _ (bmem_of_bytes_range rsegs (ms_mem ms)) RD 0 ltac:(lia)) as X0. rewrite Z.add_0_r in X0.
  assert (RD1 : rdZ (bmem_of rsegs (ms_mem ms)) p (Z.to_nat (to_Z (msize_bytes SZ1))) = Some (zbyte v 0)).
  { change (Z.to_nat (to_Z (msize_bytes SZ1))) with 1%nat. cbn [rdZ]. rewrite X0. cbn [rdZ]. f_equal. pose proof (zbyte_range v 0). lia. }
  pose proof (zbyte_range v 0) as ZB. change (bv_modulus 8) with 256 in ZB.
  set (z := zbyte v 0) in *.

  pose proof (dec_true_inv _ DEQP) as DQP.
  pose proof (decide_eq_sound E (s_facts st) Pfacts _ _ _ DQP) as EQP. apply (proj1 (eqb_iff _ _ true)) in EQP.

  set (W := Z_to_bv 64 z).
  set (E' := env_upd E n W).
  assert (HX : env_ext n E E') by (subst E'; apply env_upd_ext).
  assert (EVn : ev E' n = W) by (subst E'; apply env_upd_same).
  assert (HS' : St.st_ok rsegs OPS E' st ms mo) by exact (st_ok_reval rsegs OPS n E E' HX st ms mo NPOS VB HS).
  set (rv := VExt true 0%uint63 1%uint63 (VP n wzero)).
  assert (Dv : den E' rv = ext_word true 0 (to_Z (msize_bytes SZ1)) (Z_to_bv 64 z)).
  { subst rv. cbn [den]. rewrite EVn. subst W. change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1.
    change (to_Z (msize_bytes SZ1)) with 1. f_equal. apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned. change (w2Z wzero) with 0.
    rewrite Z.add_0_r. apply bv_wrap_bv_unsigned. }
  set (st1 := SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (FRange n wzero (wlit 255%uint63) :: s_facts st)
                 (s_ops st) (s_priv st) (PrimInt63.add n 1%uint63)).
  assert (HS1 : St.st_ok rsegs OPS E' st1 ms mo).
  { apply (st_ok_facts_next E' st ms mo [FRange n wzero (wlit 255%uint63)] (PrimInt63.add n 1%uint63) HS').
    constructor; [| constructor]. cbn [fact_holds]. rewrite EVn. subst W. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; lia).
    rewrite wlit_ok || rewrite w2Z_wlit. change (w2Z wzero) with 0. change (to_Z 255%uint63) with 255. lia. }

  destruct (LdPartSound.load_at_spec rsegs _ _ _ _ _ _ LA) as (wi & ins & Hf & He & Hd & Hof).
  assert (Hf' : fetch_word rsegs (ms_pc_val ms) = Some wi) by (rewrite (so_pc _ _ _ _ _ _ HS); exact Hf).
  assert (VBa : sv_vars_below n (sv_alu ALU_ADD (getr st rs) (VL off)) = true).
  { destruct (MemFX.st_vars_below_parts n st VB) as (P1r & _). apply (MemFX.sv_vars_below_alu n ALU_ADD _ (VL off) (or_introl eq_refl) (rf_allb_get _ _ _ P1r rs)). reflexivity. }
  assert (DA : den E' (sv_alu ALU_ADD (getr st1 rs) (VL off)) = Z_to_bv 64 p).
  { change (getr st1 rs) with (getr st rs). rewrite (den_reval n E E' HX _ VBa), EQP. apply bv_eq. rewrite Z_to_bv_unsigned, <- FPTR.
    symmetry. apply bv_wrap_small. rewrite bv_modulus_64. pose proof (bv_unsigned_in_range 64 (den E fPv)). rewrite bv_modulus_64 in H. lia. }
  destruct (PkStep.oracle_ILoad rsegs OPS E' st1 ms mo wi ins SZ1 true rd rs off p z rv HS1 PCB Hf' He Hd Hof DA ltac:(lia)
              ltac:(change (to_Z (msize_bytes SZ1)) with 1; unfold W64.two64; lia) RD1 Dv) as (ms' & STEP & MEM & HS2).
  apply (rz_step rsegs ms mo ms' K (mf_halted _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS))) (mf_lazy _ (St.plain_mf _ _ OPS_plain (so_mf _ _ _ _ _ _ HS))) (so_svc _ _ _ _ _ _ HS) STEP).
  exact (HK _ (or_introl eq_refl) E' ms' mo HX HMP HS2).
Qed.

End OPS.
End TwinB.
