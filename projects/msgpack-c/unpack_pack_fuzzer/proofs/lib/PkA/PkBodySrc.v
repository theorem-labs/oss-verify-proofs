(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Instr Plan ValProofs MemProofs StepSoundBase StepSoundMem StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree PkOps PkLib GLib PkPeek PkStep PkBody.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem State Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA LdPart.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM StepS PlanS CtrLib CtrA HeapOp UB UG TR PK PKL.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module PkBodySrc.
Section WithSegs.
Variable segs : list Segment.

Ltac unfT := unfold T_NIL, T_BOOLEAN, T_POSINT, T_NEGINT, T_FLOAT64, T_STR, T_BIN, T_ARRAY, T_MAP, T_EXT, T_FLOAT32 in *.

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

Lemma body_src_facts : forall E st aw ws ca LB wsZ (m : word -> option byte),
  facts_hold E (s_facts st) -> the_op st = Some (3%uint63, aw, ws, ca) -> PkBody.body_src_ok st (getr st X12) = true ->
  PK.cw_pk_holds segs (map (den E) ca) LB wsZ m -> (forall b, In b LB -> fst b + snd b <= 2 ^ 64) ->
  let S := bv_unsigned (den E (getr st X11)) in let N := bv_unsigned (den E (getr st X12)) in
  N = 0 \/ (N <> 0 /\ exists g ls c, PK.pure_pk g ls /\ PK.own_pk g LB /\ PK.wins_pk g wsZ /\ PK.ghost_pk g wsZ /\
            In c (z_chunks (PK.k_zone g)) /\ chunk_lo c <= S /\ S + N <= chunk_hi c).
Proof.
  intros E st aw ws ca LB wsZ m Pfacts TO SRC HC BND. cbv zeta.
  set (N := bv_unsigned (den E (getr st X12))).
  assert (EN0 : N = bv_unsigned (den E (getr st X12))) by reflexivity.
  pose proof two64_eq as T64.
  unfold PkBody.body_src_ok in SRC. rewrite TO in SRC.
  apply andb_prop in SRC as [_ SRC].
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  destruct (PkBody.body_src (s_facts st) eb rootT n1 P1 cf fT fN fP) as [[[fTv fNv] fPv]|] eqn:SRCB; [|discriminate].
  destruct fTv as [t| | | | | | | | | |]; try discriminate.
      apply andb_prop in SRC as [SRC DEQN]. apply andb_prop in SRC as [TY DEQP].
      unfold PK.cw_pk_holds in HC. cbn [map PK.decode_pk] in HC.
      destruct HC as (g & ls & L & P & O & Wk & M & GH).
      pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
      cbn [PK.a_root PK.a_rootT PK.a_n1 PK.a_P1 PK.a_c0 PK.a_eb PK.a_ee PK.a_ecap PK.a_tptr PK.a_trest PK.a_tmap PK.a_tkey PK.a_cf PK.a_fT PK.a_fN PK.a_fP] in LCF.
      pose proof P as (LV & EL & SZ & VE & CE & ZV).
      pose proof M as (TW & KA & [IC IB] & CH & PE).
      assert (FO : exists fo, tree_wf (bmem_of segs m) (PK.k_zone g) fo /\ obj_type fo = bv_unsigned (den E (VL t))
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
      pose proof (body_of_focus (bmem_of segs m) (PK.k_zone g) fo (w2Z t) p n TWF FT' HT eq_refl FVIA) as BODY. cbv zeta in BODY.
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
        - rewrite den_sv_alu. cbn [alu64 alu]. rewrite bv_add_unsigned, <- FPTR. cbn [den]. rewrite wbv_unsigned. change (w2Z wone) with 1.
          unfold bv_wrap. rewrite bv_modulus_64. reflexivity.
        - rewrite <- FPTR, Z.add_0_r, Z.mod_small by lia. reflexivity. }
      clearbody isx.
      set (S := bv_unsigned (den E (getr st X11))) in *.
      pose proof (bv_unsigned_in_range 64 (den E (getr st X11))) as SR. rewrite bv_modulus_64 in SR. fold S in SR.
      destruct (Z.eq_dec N 0) as [Z0|NZ0]; [left; exact Z0| right]. split; [exact NZ0|].
      assert (PN0 : p <> 0) by (intros P0; pose proof (PZ P0); lia).
      destruct (PNZ PN0) as [IZ _].
      pose proof IZ as (c & Hc & ICc).
      pose proof (PK.owned_pos g ls P (chunk_block c) ltac:(unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc)) as POSc.
      destruct GH as [GH1 _].
      exists g, ls, c. split; [exact P|]. split; [exact O|]. split; [exact Wk|]. split; [exact GH1|]. split; [exact Hc|].
      pose proof (BND _ (proj1 O _ ltac:(unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc))) as BC.
      unfold chunk_block in BC. cbn [fst snd] in BC.
      unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in *.
      assert (ES : S = p + isx) by (rewrite SP; apply Z.mod_small; lia).
      lia.
Qed.
End WithSegs.
End PkBodySrc.

Module TwinB.
Import stdpp.base stdpp.decidable stdpp.list stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Model OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Layout OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Steps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.OpsBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Tree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkOps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkPeek OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkBody.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.LdPart.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM StepS PlanS CtrLib CtrA HeapOp UB UG TR PK PKL.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module PkBodySrc.
Section WithSegs.
Variable segs : list Segment.

Ltac unfT := unfold T_NIL, T_BOOLEAN, T_POSINT, T_NEGINT, T_FLOAT64, T_STR, T_BIN, T_ARRAY, T_MAP, T_EXT, T_FLOAT32 in *.

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

Lemma body_src_facts : forall E st aw ws ca LB wsZ (m : word -> option byte),
  facts_hold E (s_facts st) -> the_op st = Some (3%uint63, aw, ws, ca) -> PkBody.body_src_ok st (getr st X12) = true ->
  PK.cw_pk_holds segs (map (den E) ca) LB wsZ m -> (forall b, In b LB -> fst b + snd b <= 2 ^ 64) ->
  let S := bv_unsigned (den E (getr st X11)) in let N := bv_unsigned (den E (getr st X12)) in
  N = 0 \/ (N <> 0 /\ exists g ls c, PK.pure_pk g ls /\ PK.own_pk g LB /\ PK.wins_pk g wsZ /\ PK.ghost_pk g wsZ /\
            In c (z_chunks (PK.k_zone g)) /\ chunk_lo c <= S /\ S + N <= chunk_hi c).
Proof.
  intros E st aw ws ca LB wsZ m Pfacts TO SRC HC BND. cbv zeta.
  set (N := bv_unsigned (den E (getr st X12))).
  assert (EN0 : N = bv_unsigned (den E (getr st X12))) by reflexivity.
  pose proof two64_eq as T64.
  unfold PkBody.body_src_ok in SRC. rewrite TO in SRC.
  apply andb_prop in SRC as [_ SRC].
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  destruct (PkBody.body_src (s_facts st) eb rootT n1 P1 cf fT fN fP) as [[[fTv fNv] fPv]|] eqn:SRCB; [|discriminate].
  destruct fTv as [t| | | | | | | | | |]; try discriminate.
      apply andb_prop in SRC as [SRC DEQN]. apply andb_prop in SRC as [TY DEQP].
      unfold PK.cw_pk_holds in HC. cbn [map PK.decode_pk] in HC.
      destruct HC as (g & ls & L & P & O & Wk & M & GH).
      pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
      cbn [PK.a_root PK.a_rootT PK.a_n1 PK.a_P1 PK.a_c0 PK.a_eb PK.a_ee PK.a_ecap PK.a_tptr PK.a_trest PK.a_tmap PK.a_tkey PK.a_cf PK.a_fT PK.a_fN PK.a_fP] in LCF.
      pose proof P as (LV & EL & SZ & VE & CE & ZV).
      pose proof M as (TW & KA & [IC IB] & CH & PE).
      assert (FO : exists fo, tree_wf (bmem_of segs m) (PK.k_zone g) fo /\ obj_type fo = bv_unsigned (den E (VL t))
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
      pose proof (body_of_focus (bmem_of segs m) (PK.k_zone g) fo (w2Z t) p n TWF FT' HT eq_refl FVIA) as BODY. cbv zeta in BODY.
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
        - rewrite den_sv_alu. cbn [alu64 alu]. rewrite bv_add_unsigned, <- FPTR. cbn [den]. rewrite wbv_unsigned. change (w2Z wone) with 1.
          unfold bv_wrap. rewrite bv_modulus_64. reflexivity.
        - rewrite <- FPTR, Z.add_0_r, Z.mod_small by lia. reflexivity. }
      clearbody isx.
      set (S := bv_unsigned (den E (getr st X11))) in *.
      pose proof (bv_unsigned_in_range 64 (den E (getr st X11))) as SR. rewrite bv_modulus_64 in SR. fold S in SR.
      destruct (Z.eq_dec N 0) as [Z0|NZ0]; [left; exact Z0| right]. split; [exact NZ0|].
      assert (PN0 : p <> 0) by (intros P0; pose proof (PZ P0); lia).
      destruct (PNZ PN0) as [IZ _].
      pose proof IZ as (c & Hc & ICc).
      pose proof (PK.owned_pos g ls P (chunk_block c) ltac:(unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc)) as POSc.
      destruct GH as [GH1 _].
      exists g, ls, c. split; [exact P|]. split; [exact O|]. split; [exact Wk|]. split; [exact GH1|]. split; [exact Hc|].
      pose proof (BND _ (proj1 O _ ltac:(unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc))) as BC.
      unfold chunk_block in BC. cbn [fst snd] in BC.
      unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in *.
      assert (ES : S = p + isx) by (rewrite SP; apply Z.mod_small; lia).
      lia.
Qed.
End WithSegs.
End PkBodySrc.
End TwinB.
