(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9L5DefsA PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutHeap2 CutL5 CutL5A CutHeapA CutBridgeA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import TopSpecsCB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RDKC.
Definition mem := (word -> option byte).

Section Agree.
Variable segs : list Segment.
Variable IC : PMLA.consts.
Variables (M M' : mem) (S : Z -> Prop).
Hypothesis AG : forall a, S a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Abbreviation out := (PTA.out S).

Definition pax (Mx : mem) (P : Z) (ps : PML.pstate) : Prop :=
  PMLA.u64 segs Mx P (PMLA.VT_PARSER IC) /\ PMLA.u32 segs Mx (P + 8) 1024 /\
  PMLA.u8 segs Mx (P + 12) 0 /\ PMLA.u8 segs Mx (P + 13) 1 /\ PMLA.u8 segs Mx (P + 14) 0 /\ PMLA.u8 segs Mx (P + 15) 1 /\ PMLA.u8 segs Mx (P + 16) 0 /\ PMLA.u8 segs Mx (P + 17) 0 /\ PMLA.u8 segs Mx (P + 18) 0 /\
  L5.lstr_short segs Mx (P + 24) [] /\ L5.lstr_short segs Mx (P + 48) [] /\ L5.lstr_short segs Mx (P + 72) [] /\
  PMLA.u64 segs Mx (P + 96) (PMLA.VT_FUNC IC) /\ PMLA.u64 segs Mx (P + 128) (P + 96) /\
  PMLA.u32 segs Mx (P + 144) (PML.ps_level ps) /\
  PMLA.u8 segs Mx (P + 208) (PML.ps_st ps) /\ PMLA.u8 segs Mx (P + 209) (PML.ps_sst ps) /\ PMLA.u8 segs Mx (P + 210) (PML.ps_nst ps) /\
  PMLA.u8 segs Mx (P + 211) (PMLA.b2z (PML.ps_more ps)) /\ PMLA.u8 segs Mx (P + 212) (PMLA.b2z (PML.ps_done ps)) /\ PMLA.u8 segs Mx (P + 213) 1 /\ PMLA.u32 segs Mx (P + 216) 0 /\
  PMLA.str_at segs Mx (P + 224) (PML.SLong (PML.ps_bcap ps) (PML.ps_bptr ps) (PML.ps_buf ps)) /\ 264 <= PML.ps_bcap ps /\
  PMLA.u64 segs Mx (P + 248) (PML.ps_sb ps) /\ PMLA.u64 segs Mx (P + 256) (PML.ps_sb ps + Z.of_nat (length (PML.ps_stack ps))) /\ PMLA.u64 segs Mx (P + 264) (PML.ps_sb ps + PML.ps_scap ps) /\
  L5.bytes_at segs Mx (PML.ps_sb ps) (PML.ps_stack ps) /\ Z.of_nat (length (PML.ps_stack ps)) <= PML.ps_scap ps /\
  L5.defined Mx P 272.

Definition win (Mx : mem) (P : Z) (w : option (Z * Z)) : Prop :=
  match w with None => PMLA.u64 segs Mx (P + 192) 0 /\ PMLA.u64 segs Mx (P + 200) 0 | Some (p, e) => PMLA.u64 segs Mx (P + 200) p /\ PMLA.u64 segs Mx (P + 192) e /\ p <= e end.

Lemma pax_of : forall Mx P ps, PMLA.parser_at segs IC Mx P ps -> pax Mx P ps /\ win Mx P (PML.ps_win ps).
Proof.
  intros Mx P ps H. unfold PMLA.parser_at in H. unfold pax, win.
  destruct H as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30).
  split; [|exact A15]. repeat (split; [assumption|]). exact A30.
Qed.
Lemma pax_to : forall Mx P ps w, pax Mx P ps -> win Mx P w -> PMLA.parser_at segs IC Mx P (PML.ps_set_win ps w).
Proof.
  intros Mx P ps w H HW. unfold pax in H. unfold PMLA.parser_at. destruct ps; cbn in *.
  destruct H as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30).
  repeat (split; [assumption|]). exact A30.
Qed.
Lemma ps_set_win_id : forall ps, PML.ps_set_win ps (PML.ps_win ps) = ps.
Proof. intros ps. destruct ps; reflexivity. Qed.
Lemma pax_set_win : forall Mx P ps w, pax Mx P (PML.ps_set_win ps w) <-> pax Mx P ps.
Proof. intros Mx P ps w. destruct ps; cbn. split; intros H; exact H. Qed.

Lemma pax_ag : forall P ps,
  (forall k n, 0 <= k -> k + n <= 272 -> (k + n <= 192 \/ 208 <= k) -> out (P + k) n) -> out (PML.ps_bptr ps) (PML.ps_bcap ps) -> out (PML.ps_sb ps) (PML.ps_scap ps) ->
  (forall i, 192 <= i < 208 -> M' (Z_to_bv 64 (P + i)) <> None) ->
  pax M P ps -> pax M' P ps.
Proof.
  intros P ps OO OB OS DW H. unfold pax, PMLA.u64, PMLA.u32, PMLA.u8 in *.
  destruct H as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30).
  split; [replace P with (P + 0) by lia; apply (PTA.u64_ag segs M M' S AG); [apply OO; lia | rewrite Z.add_0_r; exact A0]|].
  split; [apply (PTA.u32_ag segs M M' S AG); [apply OO; lia | exact A1]|].
  split; [apply (PTA.u8_ag segs M M' S AG); [apply OO; lia | exact A2]|]. split; [apply (PTA.u8_ag segs M M' S AG); [apply OO; lia | exact A3]|].
  split; [apply (PTA.u8_ag segs M M' S AG); [apply OO; lia | exact A4]|]. split; [apply (PTA.u8_ag segs M M' S AG); [apply OO; lia | exact A5]|].
  split; [apply (PTA.u8_ag segs M M' S AG); [apply OO; lia | exact A6]|]. split; [apply (PTA.u8_ag segs M M' S AG); [apply OO; lia | exact A7]|].
  split; [apply (PTA.u8_ag segs M M' S AG); [apply OO; lia | exact A8]|].
  split; [apply (PTA.lstr_short_nil_ag segs M M' S AG); [apply OO; lia | exact A9]|]. split; [apply (PTA.lstr_short_nil_ag segs M M' S AG); [apply OO; lia | exact A10]|].
  split; [apply (PTA.lstr_short_nil_ag segs M M' S AG); [apply OO; lia | exact A11]|].
  split; [apply (PTA.u64_ag segs M M' S AG); [apply OO; lia | exact A12]|]. split; [apply (PTA.u64_ag segs M M' S AG); [apply OO; lia | exact A13]|].
  split; [apply (PTA.u32_ag segs M M' S AG); [apply OO; lia | exact A14]|].
  split; [apply (PTA.u8_ag segs M M' S AG); [apply OO; lia | exact A16]|]. split; [apply (PTA.u8_ag segs M M' S AG); [apply OO; lia | exact A17]|].
  split; [apply (PTA.u8_ag segs M M' S AG); [apply OO; lia | exact A18]|]. split; [apply (PTA.u8_ag segs M M' S AG); [apply OO; lia | exact A19]|].
  split; [apply (PTA.u8_ag segs M M' S AG); [apply OO; lia | exact A20]|]. split; [apply (PTA.u8_ag segs M M' S AG); [apply OO; lia | exact A21]|].
  split; [apply (PTA.u32_ag segs M M' S AG); [apply OO; lia | exact A22]|].
  split; [apply (PTA.str_long_ag segs M M' S AG); [apply OO; lia | exact OB | exact A23]|]. split; [exact A24|].
  split; [apply (PTA.u64_ag segs M M' S AG); [apply OO; lia | exact A25]|]. split; [apply (PTA.u64_ag segs M M' S AG); [apply OO; lia | exact A26]|].
  split; [apply (PTA.u64_ag segs M M' S AG); [apply OO; lia | exact A27]|].
  split; [apply (PTA.bytes_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ OS); lia | exact A28]|]. split; [exact A29|].
  intros i Hi. destruct (Z_lt_dec i 192) as [L1|L1]; [|destruct (Z_le_dec 208 i) as [L2|L2]].
  - destruct (OO 0 192 ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & O3). rewrite (AG (P + i) (O3 (P + i) ltac:(lia))). exact (A30 i Hi).
  - destruct (OO 208 64 ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & O3). rewrite (AG (P + i) (O3 (P + i) ltac:(lia))). exact (A30 i Hi).
  - apply DW. lia.
Qed.

Definition text_out (IS : Z) (rep : PML.srep) : Prop := match rep with PML.SShort _ => True | PML.SLong cap p _ => out p cap end.
Lemma isrc_ag : forall IS rep gp rd, out IS 272 -> text_out IS rep -> Z.of_nat (length (PML.srep_chars rep)) < 2 ^ 26 ->
  PMLA.isrc_at segs IC M IS rep gp rd -> PMLA.isrc_at segs IC M' IS rep gp rd.
Proof.
  intros IS rep gp rd OI OT LEN H. unfold PMLA.isrc_at, PMLA.u64, PMLA.u32, PMLA.u8 in *. cbv zeta in *.
  destruct H as (I0 & I16 & I24 & I32 & I40 & I48 & GR & I56 & I64 & I72 & STR & I104 & I112 & I120 & IOSB & RD & IDEF).
  assert (U64T : forall k v, 0 <= k -> k + 8 <= 272 -> L5.u64_at segs M (IS + k) v -> L5.u64_at segs M' (IS + k) v) by (intros k v K0 K1 Hv; apply (PTA.u64_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ OI); lia | exact Hv]).
  assert (U32T : forall k v, 0 <= k -> k + 4 <= 272 -> L5.u32_at segs M (IS + k) v -> L5.u32_at segs M' (IS + k) v) by (intros k v K0 K1 Hv; apply (PTA.u32_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ OI); lia | exact Hv]).
  split; [replace IS with (IS + 0) by lia; apply (U64T 0); [lia | lia | rewrite Z.add_0_r; exact I0]|].
  split; [exact (U64T 16 _ ltac:(lia) ltac:(lia) I16)|]. split; [exact (U64T 24 _ ltac:(lia) ltac:(lia) I24)|]. split; [exact (U64T 32 _ ltac:(lia) ltac:(lia) I32)|].
  split; [exact (U64T 40 _ ltac:(lia) ltac:(lia) I40)|]. split; [exact (U64T 48 _ ltac:(lia) ltac:(lia) I48)|]. split; [exact GR|].
  split; [exact (U64T 56 _ ltac:(lia) ltac:(lia) I56)|]. split; [exact (U64T 64 _ ltac:(lia) ltac:(lia) I64)|]. split; [exact (U64T 72 _ ltac:(lia) ltac:(lia) I72)|].
  split.
  { destruct rep as [s|cap p s]; cbn [PML.srep_chars PML.srep_data] in *.
    - destruct STR as (SL & SH0 & SBY & SNUL). unfold PMLA.str_at. split; [exact SL|].
      split; [apply (PTA.u8_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ OI); lia | exact SH0]|].
      split; [apply (PTA.bytes_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ OI); lia | exact SBY]|].
      apply (PTA.u8_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ OI); lia | exact SNUL].
    - apply (PTA.str_long_ag segs M M' S AG (IS + 80) cap p s); [apply (PTA.out_sub _ _ _ _ _ OI); lia | exact OT | exact STR]. }
  split; [exact (U64T 104 _ ltac:(lia) ltac:(lia) I104)|]. split; [exact (U32T 112 _ ltac:(lia) ltac:(lia) I112)|]. split; [exact (U64T 120 _ ltac:(lia) ltac:(lia) I120)|].
  split.
  { destruct IOSB as (J32 & J36 & J40 & J48 & JZ & JDEF). unfold PMLA.iosb_at, PMLA.u64, PMLA.u32.
    split; [replace (IS + 120 + 32) with (IS + 152) in * by lia; exact (U32T 152 _ ltac:(lia) ltac:(lia) J32)|].
    split; [replace (IS + 120 + 36) with (IS + 156) in * by lia; exact (U32T 156 _ ltac:(lia) ltac:(lia) J36)|].
    split; [replace (IS + 120 + 40) with (IS + 160) in * by lia; exact (U64T 160 _ ltac:(lia) ltac:(lia) J40)|].
    split; [replace (IS + 120 + 48) with (IS + 168) in * by lia; exact (U64T 168 _ ltac:(lia) ltac:(lia) J48)|].
    split; [intros k Hk; replace (IS + 120 + 56 + 8 * k) with (IS + (176 + 8 * k)) by lia; apply (U64T (176 + 8 * k)); [lia | lia | replace (IS + (176 + 8 * k)) with (IS + 120 + 56 + 8 * k) by lia; exact (JZ k Hk)]|].
    replace (IS + 120) with (IS + 120) by lia. apply (PTA.def_ag M M' S AG); [apply (PTA.out_sub _ _ _ _ _ OI); lia | exact JDEF]. }
  split; [exact RD|]. apply (PTA.def_ag M M' S AG); [exact OI | exact IDEF].
Qed.
Lemma srep_sh_ag : forall (rep : PML.srep), (match rep with PML.SShort _ => True | PML.SLong cap p _ => 0 <= cap /\ p mod 8 = 0 /\ forall a, in_shadow_of p cap a -> S a end) ->
  PMLA.srep_sh M rep -> PMLA.srep_sh M' rep.
Proof.
  intros rep H HS. unfold PMLA.srep_sh in *. destruct rep as [s|cap p s]; [exact I|]. destruct H as (H0 & H8 & HA).
  exact (PTA.shadow_blk_ag M M' S AG p cap H0 HA H8 HS).
Qed.

Lemma rdr_ag : forall L Rr IS V ch bof, out Rr 320 -> TPSA.rdr_atA L IC M Rr IS V ch bof -> segs = hl_segs L -> TPSA.rdr_atA L IC M' Rr IS V ch bof.
Proof.
  intros L Rr IS V ch bof OR H HS. unfold TPSA.rdr_atA, PMLA.u64, PMLA.u8 in *. rewrite <- HS in *.
  destruct H as (Q240 & Q248 & Q264 & Q272 & (de & Q280 & DER) & Q288 & Q296 & Q304 & Q312 & QIOSB & Q32 & RDEF).
  assert (U64T : forall k v, 0 <= k -> k + 8 <= 320 -> L5.u64_at segs M (Rr + k) v -> L5.u64_at segs M' (Rr + k) v) by (intros k v K0 K1 Hv; apply (PTA.u64_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ OR); lia | exact Hv]).
  assert (U32T : forall k v, 0 <= k -> k + 4 <= 320 -> L5.u32_at segs M (Rr + k) v -> L5.u32_at segs M' (Rr + k) v) by (intros k v K0 K1 Hv; apply (PTA.u32_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ OR); lia | exact Hv]).
  split; [exact (U64T 240 _ ltac:(lia) ltac:(lia) Q240)|]. split; [exact (U64T 248 _ ltac:(lia) ltac:(lia) Q248)|]. split; [exact (U64T 264 _ ltac:(lia) ltac:(lia) Q264)|].
  split; [exact (U64T 272 _ ltac:(lia) ltac:(lia) Q272)|]. split; [exists de; split; [exact (U64T 280 _ ltac:(lia) ltac:(lia) Q280) | exact DER]|].
  split; [exact (U64T 288 _ ltac:(lia) ltac:(lia) Q288)|]. split; [apply (PTA.u8_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ OR); lia | exact Q296]|].
  split; [exact (U64T 304 _ ltac:(lia) ltac:(lia) Q304)|]. split; [exact (U64T 312 _ ltac:(lia) ltac:(lia) Q312)|].
  split.
  { destruct QIOSB as (st0 & K32 & K36 & K40 & K48 & KZ & KDEF). exists st0. unfold PMLA.iosb_at, PMLA.u64, PMLA.u32.
    split; [replace (Rr + 88 + 32) with (Rr + 120) in * by lia; exact (U32T 120 _ ltac:(lia) ltac:(lia) K32)|].
    split; [replace (Rr + 88 + 36) with (Rr + 124) in * by lia; exact (U32T 124 _ ltac:(lia) ltac:(lia) K36)|].
    split; [replace (Rr + 88 + 40) with (Rr + 128) in * by lia; exact (U64T 128 _ ltac:(lia) ltac:(lia) K40)|].
    split; [replace (Rr + 88 + 48) with (Rr + 136) in * by lia; exact (U64T 136 _ ltac:(lia) ltac:(lia) K48)|].
    split; [intros k Hk; replace (Rr + 88 + 56 + 8 * k) with (Rr + (144 + 8 * k)) by lia; apply (U64T (144 + 8 * k)); [lia | lia | replace (Rr + (144 + 8 * k)) with (Rr + 88 + 56 + 8 * k) by lia; exact (KZ k Hk)]|].
    apply (PTA.def_ag M M' S AG); [apply (PTA.out_sub _ _ _ _ _ OR); lia | exact KDEF]. }
  split; [exact (U64T 32 _ ltac:(lia) ltac:(lia) Q32)|]. apply (PTA.def_ag M M' S AG); [exact OR | exact RDEF].
Qed.
End Agree.

Lemma source_of_rdr : forall L IC M Rr IS V ch bof, TPSA.rdr_atA L IC M Rr IS V ch bof -> PMLA.source_at (hl_segs L) IC M Rr ch.
Proof.
  intros L IC M Rr IS V ch bof (Q240 & Q248 & Q264 & Q272 & _ & Q288 & Q296 & Q304 & Q312 & QIOSB & Q32 & RDEF).
  split; [exact Q264|]. split; [exact Q272|]. split; [exact QIOSB|]. split; [exact Q32 | exact RDEF].
Qed.

Lemma lb_remove_cons_neq : forall ch b n LB, b <> ch -> lb_remove ch ((b, n) :: LB) = (b, n) :: lb_remove ch LB.
Proof. intros ch b n LB H. cbn [lb_remove fst]. destruct (Z.eqb_spec b ch); [lia|]. reflexivity. Qed.
Lemma lb_remove_cons_eq : forall ch n LB, lb_remove ch ((ch, n) :: LB) = LB.
Proof. intros ch n LB. cbn [lb_remove fst]. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma win_okA_front : forall M LBo ch ps, In (ch, 16384) LBo -> PMLA.win_okA M LBo ps -> PMLA.win_okA M ((ch, 16384) :: lb_remove ch LBo) ps.
Proof.
  intros M LBo ch ps Hin H. unfold PMLA.win_okA in *. destruct (PML.ps_win ps) as [[p e]|]; [|exact I]. destruct H as (c & A & B). exists c. split; [|exact B].
  destruct (Z.eq_dec c ch) as [->|ne]; [left; reflexivity | right; exact (L5C.in_lb_remove_neq ch c 16384 LBo A ne)].
Qed.
Lemma win_okA_back : forall M LBo ch ps, In (ch, 16384) LBo -> PMLA.win_okA M ((ch, 16384) :: lb_remove ch LBo) ps -> PMLA.win_okA M LBo ps.
Proof.
  intros M LBo ch ps Hin H. unfold PMLA.win_okA in *. destruct (PML.ps_win ps) as [[p e]|]; [|exact I]. destruct H as (c & A & B). exists c. split; [|exact B].
  destruct A as [E|A]; [injection E as <-; exact Hin | exact (L5C.in_lb_remove ch _ LBo A)].
Qed.

Lemma win_okA_agx : forall (M M' : mem) LBo ch ps,
  (forall c a, In (c, 16384) LBo -> c <> ch -> (c <= a < c + 16384 \/ in_shadow_of c 16384 a) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall c, In (c, 16384) LBo -> 0 <= c /\ c + 16384 <= 2 ^ 64 /\ c mod 8 = 0) ->
  shadow_blk M' ch 16384 -> L5.defined M' ch 16384 -> PMLA.win_okA M LBo ps -> PMLA.win_okA M' LBo ps.
Proof.
  intros M M' LBo ch ps AG RG CSH CDEF H. unfold PMLA.win_okA in *. destruct (PML.ps_win ps) as [[p e]|]; [|exact I].
  destruct H as (c & Hin & C1 & C2 & D & SH). exists c. split; [exact Hin|]. split; [exact C1|]. split; [exact C2|].
  destruct (Z.eq_dec c ch) as [->|ne].
  - split; [intros q Hq; replace (p + q) with (ch + (p - ch + q)) by lia; apply CDEF; lia | exact CSH].
  - destruct (RG c Hin) as (R0 & R1 & R8). split.
    + apply (PTA.def_ag M M' (fun a => c <= a < c + 16384 \/ in_shadow_of c 16384 a) (fun a Ha => AG c a Hin ne Ha)); [|exact D]. split; [lia|]. split; [lia|]. intros i Hi. left. lia.
    + apply (PTA.shadow_blk_ag M M' (fun a => c <= a < c + 16384 \/ in_shadow_of c 16384 a) (fun a Ha => AG c a Hin ne Ha) c 16384 ltac:(lia)); [intros a Ha; right; exact Ha | exact R8 | exact SH].
Qed.

Section Perm.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.

Lemma chunk3_front : forall b1 b2 LBo FF LK cr A M V ch n, ri_inv HI (b1 :: b2 :: LBo) FF LK cr A M V -> In (ch, n) LBo ->
  ri_inv HI (b1 :: b2 :: (ch, n) :: lb_remove ch LBo) FF LK cr A M V.
Proof.
  intros b1 b2 LBo FF LK cr A M V ch n HH Hin. destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)) as [ND1 ND2].
  assert (NDo : base.NoDup (map fst LBo)) by (cbn [map] in ND1; apply list_relations.list.NoDup_cons in ND1 as [_ ND1]; apply list_relations.list.NoDup_cons in ND1 as [_ ND1]; exact ND1).
  apply (PmHeapIfaceA.aio_perm _ _ _ _ _ HIok _ _ FF FF LK cr A M V HH).
  - intros x. cbn [In]. split.
    + intros [H|[H|H]]; [left; exact H | right; left; exact H | right; right].
      destruct (Z.eq_dec (fst x) ch) as [e|ne].
      * left. symmetry. apply (CH2.nodup_fst_eq LBo x (ch, n) NDo H Hin). exact e.
      * right. destruct x as [B m]. exact (L5C.in_lb_remove_neq ch B m LBo H ne).
    + intros [H|[H|[<-|H]]]; [left; exact H | right; left; exact H | right; right; exact Hin | right; right; exact (L5C.in_lb_remove ch x LBo H)].
  - cbn [map fst]. cbn [map] in ND1. apply list_relations.list.NoDup_cons in ND1 as [N1 ND1]. apply list_relations.list.NoDup_cons in ND1 as [N2 _].
    apply list_relations.list.NoDup_cons. split.
    { intros Hx. apply N1. cbn [In map fst] in Hx |- *. apply list_elem_of_In in Hx. apply list_elem_of_In. cbn [In] in Hx |- *.
      destruct Hx as [Hx|[Hx|Hx]]; [left; exact Hx | right; rewrite <- Hx; apply in_map_iff; exists (ch, n); split; [reflexivity | exact Hin] | right].
      apply in_map_iff in Hx as ([u m] & Hu & Hx). cbn [fst] in Hu. subst u. apply in_map_iff. exists (fst b1, m). split; [reflexivity | exact (L5C.in_lb_remove ch _ LBo Hx)]. }
    apply list_relations.list.NoDup_cons. split.
    { intros Hx. apply N2. cbn [In map fst] in Hx |- *. apply list_elem_of_In in Hx. apply list_elem_of_In. cbn [In] in Hx |- *.
      destruct Hx as [Hx|Hx]; [rewrite <- Hx; apply in_map_iff; exists (ch, n); split; [reflexivity | exact Hin] |].
      apply in_map_iff in Hx as ([u m] & Hu & Hx). cbn [fst] in Hu. subst u. apply in_map_iff. exists (fst b2, m). split; [reflexivity | exact (L5C.in_lb_remove ch _ LBo Hx)]. }
    apply list_relations.list.NoDup_cons. split; [|exact (CH2.lb_remove_nodup ch LBo NDo)].
    intros H. apply list_elem_of_In in H. exact (CH2.lb_remove_fst_notin ch LBo NDo H).
  - intros f. split; intros X; exact X.
  - exact (CBA.nodup_ff FF LK ND2).
Qed.
Lemma chunk3_back : forall b1 b2 LBo FF LK cr A M V ch n, ri_inv HI (b1 :: b2 :: (ch, n) :: lb_remove ch LBo) FF LK cr A M V -> In (ch, n) LBo -> base.NoDup (map fst LBo) ->
  ri_inv HI (b1 :: b2 :: LBo) FF LK cr A M V.
Proof.
  intros b1 b2 LBo FF LK cr A M V ch n HH Hin NDo. destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)) as [ND1 ND2].
  apply (PmHeapIfaceA.aio_perm _ _ _ _ _ HIok _ _ FF FF LK cr A M V HH).
  - intros x. cbn [In]. split.
    + intros [H|[H|[<-|H]]]; [left; exact H | right; left; exact H | right; right; exact Hin | right; right; exact (L5C.in_lb_remove ch x LBo H)].
    + intros [H|[H|H]]; [left; exact H | right; left; exact H | right; right].
      destruct (Z.eq_dec (fst x) ch) as [e|ne].
      * left. symmetry. apply (CH2.nodup_fst_eq LBo x (ch, n) NDo H Hin). exact e.
      * right. destruct x as [B m]. exact (L5C.in_lb_remove_neq ch B m LBo H ne).
  - cbn [map fst]. cbn [map] in ND1. apply list_relations.list.NoDup_cons in ND1 as [N1 ND1]. apply list_relations.list.NoDup_cons in ND1 as [N2 ND1]. apply list_relations.list.NoDup_cons in ND1 as [N3 ND1].
    apply list_relations.list.NoDup_cons. split.
    { intros Hx. apply N1. apply list_elem_of_In in Hx. apply list_elem_of_In. cbn [In] in Hx |- *.
      destruct Hx as [Hx|Hx]; [left; exact Hx | right]. apply in_map_iff in Hx as ([u m] & Hu & Hx). cbn [fst] in Hu. subst u.
      destruct (Z.eq_dec (fst b1) ch) as [->|ne]; [left; reflexivity | right]. apply in_map_iff. exists (fst b1, m). split; [reflexivity | exact (L5C.in_lb_remove_neq ch _ m LBo Hx ne)]. }
    apply list_relations.list.NoDup_cons. split; [|exact NDo].
    intros Hx. apply N2. apply list_elem_of_In in Hx. apply list_elem_of_In. cbn [In] in Hx |- *.
    apply in_map_iff in Hx as ([u m] & Hu & Hx). cbn [fst] in Hu. subst u.
    destruct (Z.eq_dec (fst b2) ch) as [->|ne]; [left; reflexivity | right]. apply in_map_iff. exists (fst b2, m). split; [reflexivity | exact (L5C.in_lb_remove_neq ch _ m LBo Hx ne)].
  - intros f. split; intros X; exact X.
  - exact (CBA.nodup_ff FF LK ND2).
Qed.
End Perm.
End RDKC.
