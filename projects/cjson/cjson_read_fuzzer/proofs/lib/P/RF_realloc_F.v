(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_enframe.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require SspGuard.
From Stdlib Require Zify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Module RMallocKit_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.


Lemma rmrep_wr32 : forall st m p v r,
  rmrep st m -> ticks_ok st ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup -> 0 <= snd p -> snd p + 4 <= round_up_pg (r_len r) ->
  (forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> snd p + 4 <= snd b \/ snd b + 9 <= snd p) ->
  0 <= v < 2^32 ->
  rmrep (wr32 p v st) (write_to_mem m (wa (r_base r + snd p)) (le4 (wz v)))
  /\ ticks_ok (wr32 p v st).
Proof using .
  intros st m p v r MR TK Hr Hk H0 H4 Hg Hv.
  rewrite le4_bytes by lia.
  change (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256); b8 ((v / 256) mod 256); b8 ((v / 65536) mod 256); b8 (v / 16777216)])
    with (write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)])
            (wa (r_base r + snd p) + 1) [b8 ((v / 256) mod 256)]) (wa (r_base r + snd p) + 1 + 1) [b8 ((v / 65536) mod 256)])
            (wa (r_base r + snd p) + 1 + 1 + 1) [b8 (v / 16777216)]).
  rewrite !wa_succ.
  unfold wr32.
  assert (E1 : forall q w stx, wr8 q w stx = wr8 q (w mod 256) stx) by (intros; apply wr8_mod).
  rewrite (E1 p v), (E1 (aadd p 1) (Z.shiftr v 8)), (E1 (aadd p 2) (Z.shiftr v 16)), (E1 (aadd p 3) (Z.shiftr v 24)).
  rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216.
  rewrite (Z.mod_small (v / 16777216) 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (B0 : 0 <= v mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (B1 : 0 <= (v / 256) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (B2 : 0 <= (v / 65536) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (B3 : 0 <= v / 16777216 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (S1 : rmrep (wr8 p (v mod 256) st) (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) /\ ticks_ok (wr8 p (v mod 256) st)).
  { split; [|apply ticks_ok_wr8; exact TK]. apply (rmrep_wr8 st m p _ r MR TK Hr Hk); [lia| |lia].
    intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
  destruct S1 as [M1 T1].
  assert (S2 : rmrep (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)) (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p + 1)) [b8 ((v / 256) mod 256)])
               /\ ticks_ok (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st))).
  { split; [|apply ticks_ok_wr8; exact T1].
    replace (r_base r + snd p + 1) with (r_base r + snd (aadd p 1)) by (cbn; lia).
    apply (rmrep_wr8 _ _ (aadd p 1) _ r M1 T1); cbn; [exact Hr| exact Hk| lia| |lia].
    intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
  destruct S2 as [M2 T2].
  assert (S3 : rmrep (wr8 (aadd p 2) ((v / 65536) mod 256) (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)))
                    (write_to_mem (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p + 1)) [b8 ((v / 256) mod 256)]) (wa (r_base r + snd p + 1 + 1)) [b8 ((v / 65536) mod 256)])
               /\ ticks_ok (wr8 (aadd p 2) ((v / 65536) mod 256) (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)))).
  { split; [|apply ticks_ok_wr8; exact T2].
    replace (r_base r + snd p + 1 + 1) with (r_base r + snd (aadd p 2)) by (cbn; lia).
    apply (rmrep_wr8 _ _ (aadd p 2) _ r M2 T2); cbn; [exact Hr| exact Hk| lia| |lia].
    intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
  destruct S3 as [M3 T3].
  split; [|apply ticks_ok_wr8; exact T3].
  replace (r_base r + snd p + 1 + 1 + 1) with (r_base r + snd (aadd p 3)) by (cbn; lia).
  apply (rmrep_wr8 _ _ (aadd p 3) _ r M3 T3); cbn; [exact Hr| exact Hk| lia| |lia].
  intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rrdv_mem : forall st stx m (q : aptr) r (x : byte),
  rmrep st m -> get_shadow stx (fst q) = get_shadow st (fst q) -> (forall q', conc stx q' = conc st q') ->
  (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  bytes_at psegs m (r_base r + snd q) [x] ->
  rdv pans_mem m stx q = bv_unsigned x.
Proof using .
  intros st stx m q r x MR Hsh Hconc Hr Hk Ho Hb.
  unfold rdv. rewrite Hsh. destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - destruct (rmrep_shadow_read st m (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
    pose proof (bytes_at_read psegs m _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
    rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
  - unfold pans_mem. rewrite Hconc, (conc_region' st q r Hr).
    destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
    unfold mrd in HB |- *.
    destruct (m (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
    exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). unfold alloc_ceiling in RBC.
    pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
    rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rauxv_ok_pres : forall C m m' B,
  rauxv_ok m B -> rpres_except C m m' ->
  (forall a, B <= a -> ~ C a) -> (forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> ~ C a) ->
  rauxv_ok m' B.
Proof using .
  intros C m m' B (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C1 & A1 & A2 & H) HP HB HC.
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rpres_except_rw_cells; [exact HP| exact C1|]. cbn. intros a Ha. apply HC. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A1|]. intros a Ha. apply HB. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A2|]. intros a Ha. apply HB. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rpres_write : forall (C : Z -> Prop) m0 m a bs,
  rpres_except C m0 m -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> C x) ->
  rpres_except C m0 (write_to_mem m (wa a) bs).
Proof using .
  intros C m0 m a bs HP Ha Hl HC x Hx HCx.
  destruct (HP x Hx HCx) as [E W].
  assert (NE : write_to_mem m (wa a) bs (wa x) = m (wa x)).
  { rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
    destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
    exfalso. apply HCx, HC. lia. }
  split.
  - rewrite NE. exact E.
  - intros Hw. apply wview_write_mono. apply W, Hw.
Qed.

Lemma rpres_except_munch_frame : forall C m0 m m' W,
  rpres_except C m0 m -> munch W m m' -> wmono psegs m m' ->
  (forall x, 0 <= x < 2^64 -> ~ C x -> outside W x) -> rpres_except C m0 m'.
Proof.
  intros C m0 m m' W HP MU WM HW. eapply rpres_except_trans; [exact HP|]. eapply rpres_except_of_munch; eauto.
Qed.


End CeilWrap.
End RMallocKit_A.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Export PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocRep MallocTree MallocBlocks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocFacts_A MallocFacts_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import Malloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Prog KInv MI_Inv MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Ext.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree.
Import RMallocKit_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RMallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv MallocFacts_inv2 MallocFacts_inv3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation RAREACH := (AREACH_from ref_reserved).

(* [comment removed for export] *)
Record rrF (st : mstate) (m : mem) (LB0 : list block) (p : bptr) (A k : Z) (g b : aptr) (r : region) (i off : Z) : Prop := mkRRF {
  rf_C : CINV st LB0;
  rf_slot : s_slots st !! (fst p) = Some (g, i);
  rf_hosts : exists ai, s_groups st !! b = Some (mkGhdr (Some g) ai);
  rf_mem : m_mem (MR st g) = Some b;
  rf_gok : gmeta_ok st g b;
  rf_reg : s_regions st !! (fst b) = Some r;
  rf_kind : r_kind r = RKGroup;
  rf_c : fst p = (fst b, snd b + UNIT + get_stride (MR st g) * i);
  rf_i : 0 <= i <= m_last_idx (MR st g);
  rf_nfree : Z.testbit (m_avail (MR st g)) i = false /\ Z.testbit (m_freed (MR st g)) i = false;
  rf_off : 0 <= off <= 255;
  rf_k : 0 <= k;
  rf_fit : UNIT * off + k <= get_stride (MR st g) - IB;
  rf_A : A = conc st (fst p) + UNIT * off;
  rf_conc : conc st (fst p) = r_base r + snd (fst p) /\ conc st b = r_base r + snd b;
  rf_span : snd b + UNIT + get_stride (MR st g) * (m_last_idx (MR st g) + 1) <= round_up_pg (r_len r);
  rf_regwf : 0 < r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
             /\ ranges_free ref_reserved (r_base r) (round_up_pg (r_len r)) = true
             /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x55000 <= r_base r);
  rf_s20 : m_sizeclass (MR st g) < 48 -> get_stride (MR st g) * (m_last_idx (MR st g) + 1) < 2^20;
  rf_sc28 : m_sizeclass (MR st g) < 48 -> get_stride (MR st g) <= UNIT * size_class (m_sizeclass (MR st g)) \/ 28 <= m_sizeclass (MR st g);
  rf_b : 0 <= snd b /\ snd b mod 16 = 0;
  (* [comment removed for export] *)
  rf_bytes :
    let P0 := conc st (fst p) in let E := P0 + get_stride (MR st g) - IB in let res := E - A - k in
    let q := (snd (fst p) + UNIT * off - snd b - UNIT) / UNIT in
    bytes_at psegs m (A - 4) [b8 0] /\ bytes_at psegs m (A - 3) [b8 (i + 32 * Z.min res 5)]
    /\ bytes_at psegs m (A - 2) (le2 (wz q)) /\ 0 <= q < 2^16 /\ 16 * q = A - conc st b - 16
    /\ (5 <= res -> bytes_at psegs m (E - 4) (le4 (wz res)) /\ bytes_at psegs m (E - 5) [b8 0] /\ res < 2^32)
    /\ (0 < res -> bytes_at psegs m (E - res) [b8 0])
    /\ bytes_at psegs m E [b8 0];
  rf_grphdr : bytes_at psegs m (conc st b) (le8 (wz (conc st g)));
  rf_meta : rw_cells psegs m (conc st g) (meta_cells st (MR st g)) /\ meta_slot st g;
  rf_acheck : exists secret, 0 <= secret < 2^64 /\ bytes_at psegs m (conc st g - conc st g mod 4096) (le8 (wz secret))
              /\ bytes_at psegs m RCTX (le8 (wz secret));
  rf_G : 0 < conc st g /\ conc st g + 40 <= alloc_ceiling /\ 24 <= conc st g mod 4096;
  rf_nogrp : forall b' gh, s_groups st !! b' = Some gh -> fst b' = fst b ->
             snd b' + 16 <= snd (fst p) \/ snd (fst p) + get_stride (MR st g) <= snd b';
  rf_others : forall blk', In blk' LB0 -> blk_slot blk' <> fst p -> fst (blk_slot blk') = fst b ->
             blk_addr blk' + blk_size blk' + IB <= conc st (fst p) \/ conc st (fst p) + get_stride (MR st g) <= blk_addr blk';
  rf_INV : exists L LS BL, INVL x0 st L BL LS /\ ld_live L = map bslot BL /\ ld_resv L = ref_reserved /\ s_secret st = 0
           /\ MallocFacts_inv.CORR st LB0 BL /\ In ((fst p, off), k) BL
}.

(* [comment removed for export] *)
Lemma q_bytes q : 0 <= q < 2^16 -> q = byte_of q 0 + 256 * byte_of q 1 /\ 0 <= byte_of q 0 < 256 /\ 0 <= byte_of q 1 < 256.
Proof using .
  intros Hq. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r, Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. change (2^8) with 256.
  pose proof (Z.mod_pos_bound q 256 ltac:(lia)). pose proof (Z.mod_pos_bound (q / 256) 256 ltac:(lia)).
  rewrite (Z.mod_small (q / 256)) by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia.
Qed.

Lemma res_bytes res : 0 <= res < 2^32 ->
  byte_of res 0 = res mod 256 /\ byte_of res 1 = (res / 256) mod 256 /\ byte_of res 2 = (res / 65536) mod 256 /\ byte_of res 3 = res / 16777216.
Proof using .
  intros Hr. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r. replace (8 * 2) with 16 by lia. replace (8 * 3) with 24 by lia.
  rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216.
  change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. change (2^8) with 256.
  repeat split; try reflexivity. apply Z.mod_small. Z.div_mod_to_equations. lia.
Qed.

Lemma area_page_base ca k : ca mod 4096 = 0 -> 0 <= k < 101 -> (ca + (24 + 40 * k)) - (ca + (24 + 40 * k)) mod 4096 = ca.
Proof using . intros Hm Hk. Z.div_mod_to_equations. nia. Qed.

Lemma slot_after_hdr (s e bo : Z) : s mod 16 = 0 -> bo mod 16 = 0 -> e <= bo + 4 -> s <= e -> e = s + (e - s) -> (e - s) mod 16 = 0 -> e <= bo.
Proof using . intros. Z.div_mod_to_equations. lia. Qed.

Section INTRO.
Variables (st : mstate) (m : mem) (LB0 : list block) (p : bptr) (A k : Z).
Hypothesis AR : RAREACH st LB0.
Hypothesis MRP : rmrep st m.
Hypothesis Hin0 : In (p, A, k) LB0.

Theorem rrF_intro : exists g b r i off, rrF st m LB0 p A k g b r i off.
Proof using AR Hin0 MRP.
  destruct (MallocFacts_inv.areach_inv _ st LB0 AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
  pose proof (MallocFacts_inv3.areach_cinv_proof st LB0 AR) as C.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof MRP as (WF & CX & GL & ARr & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  (* [comment removed for export] *)
  destruct (MallocFacts_inv.Forall2_In_l _ _ _ _ CR Hin0) as (kb & Hkb & (C1 & C2 & C3)).
  destruct kb as [[c off] k']. cbn [blk_slot blk_size blk_addr bslot bsize boff fst snd] in C1, C2, C3. subst k'.
  assert (Ec : fst p = c) by exact C1.
  destruct (is_blocks _ _ _ IS _ Hkb) as (g & i & Hs & Ho & Hk & Hfit). cbn [bslot boff bsize fst snd] in Hs, Ho, Hk, Hfit.
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hi & Es).
  destruct (hosts_ok _ _ _ IG _ _ Hb) as (ai & Hgb & GO).
  pose proof (hosts_mem _ _ _ IM _ _ Hb) as Hmem.
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb) in Es.
  destruct (ig_region _ _ _ IG _ _ Hgb) as (r & Hr & Kr).
  exists g, b, r, i, off.
  (* [comment removed for export] *)
  pose proof (ci_gmetas _ _ C b g Hb) as GOK.
  destruct (go_region _ _ _ GOK) as (r' & Hr' & _ & B0 & B16 & SPAN & TOP). rewrite Hr in Hr'. injection Hr' as <-.
  unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN.
  destruct (WR _ _ Hr) as (R0 & RAL & RL0 & RC & RF).
  pose proof (ir_shape _ _ _ IR _ _ Hr) as (_ & _ & RLpos & _).
  pose proof (rreserved_disjoint1 _ _ RF ltac:(pose proof (round_up_pg_ge (r_len r)); lia)) as RI.
  (* [comment removed for export] *)
  assert (NF : Z.testbit (m_avail (MR st g)) i = false /\ Z.testbit (m_freed (MR st g)) i = false).
  { pose proof (is_part _ _ _ IS b g ai i Hgb Hi) as P5. cbv zeta in P5. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb), <- Es in P5.
    assert (INc : In c (map bslot BL)) by (rewrite <- Ec; change (fst p) with (bslot ((fst p, off), k)); rewrite Ec; apply in_map_iff; exists ((c, off), k); split; [reflexivity| exact Hkb]).
    destruct P5 as (_ & _ & AC & _ & _ & BC & _).
    unfold tbit in AC, BC. split.
    - destruct (Z.testbit (m_avail (MR st g)) i) eqn:E; [exfalso; apply AC; auto| reflexivity].
    - destruct (Z.testbit (m_freed (MR st g)) i) eqn:E; [exfalso; apply BC; auto| reflexivity]. }
  (* [comment removed for export] *)
  pose proof (stride_ge _ _ _ IG _ _ Hb) as [S16 SM].
  assert (Cc : conc st c = r_base r + snd c) by (apply conc_region'; rewrite Es; exact Hr).
  assert (Cb : conc st b = r_base r + snd b) by (apply conc_region'; exact Hr).
  assert (SC : snd c = snd b + UNIT + get_stride (MR st g) * i) by (rewrite Es; unfold sstart; rewrite (hosts_gbase _ _ _ IM _ _ Hb); reflexivity).
  assert (SK : 0 <= get_stride (MR st g) * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SKL : get_stride (MR st g) * i + get_stride (MR st g) <= get_stride (MR st g) * (m_last_idx (MR st g) + 1)).
  { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
  (* [comment removed for export] *)
  destruct (ish_blk _ _ ISH ((c, off), k) g i Hkb Hs) as (K4 & K3 & K2 & K1 & HQ & KF & KC & KU). cbn [bslot boff bsize fst snd] in K4, K3, K2, K1, HQ, KF, KC, KU.
  rewrite (hosts_gbase _ _ _ IM _ _ Hb) in K2, K1, HQ.
  pose proof (ish_hdr0 _ _ ISH b g (i + 1) Hb ltac:(unfold cnt_of; lia)) as KE.
  assert (EE : sstart (MR st g) (i + 1) - IB = snd c + get_stride (MR st g) - IB) by (rewrite SC; unfold sstart; rewrite (hosts_gbase _ _ _ IM _ _ Hb); lia).
  rewrite EE in KE.
  change (get_meta_rec st g) with (MR st g) in SPAN, TOP.
  set (stride := get_stride (MR st g)) in *.
  set (res := stride - IB - UNIT * off - k).
  replace (snd c + stride - IB - (snd c + UNIT * off) - k) with res in K3, KF, KC by lia.
  assert (Efc : fst c = fst b) by (rewrite Es; reflexivity).
  (* [comment removed for export] *)
  assert (KB : forall o v, known st (fst b, o) v -> 0 <= o < round_up_pg (r_len r) -> bytes_at psegs m (r_base r + o) [b8 v] /\ 0 <= v < 256).
  { intros o v Kn Hoo. destruct (SH (fst b) r Hr Kr) as [_ HB]. apply (HB o v Hoo). exact Kn. }
  rewrite Efc in K4, K3, K2, K1, KC, KF, KU.
  assert (RNG : 0 <= snd c + UNIT * off - 4 /\ snd c + stride - IB + 1 <= round_up_pg (r_len r)) by (unfold UNIT, IB in *; lia).
  (* [comment removed for export] *)
  set (q := (snd c + UNIT * off - snd b - UNIT) / UNIT) in *.
  assert (EQ16 : 16 * q = snd c + UNIT * off - snd b - 16).
  { subst q. rewrite SC. unfold UNIT in *. pose proof (Z_div_exact_full_2 stride 16 ltac:(lia) SM) as ES.
    set (s16 := stride / 16) in *. clearbody s16. subst stride. rewrite ES.
    replace (snd b + 16 + 16 * s16 * i + 16 * off - snd b - 16) with ((s16 * i + off) * 16) by lia.
    rewrite Z.div_mul by lia. lia. }
  pose proof (rmeta_slot_bounds st m g MRP (go_slot _ _ _ GOK)) as (G0 & G40 & GI & G4 & G24).
  constructor.
  - exact C.
  - rewrite Ec. exact Hs.
  - exists ai. exact Hgb.
  - exact Hmem.
  - exact GOK.
  - exact Hr.
  - exact Kr.
  - rewrite Ec, Es. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hb). reflexivity.
  - exact Hi.
  - exact NF.
  - exact Ho.
  - exact Hk.
  - exact Hfit.
  - rewrite Ec. exact C3.
  - rewrite Ec. auto.
  - exact SPAN.
  - unfold alloc_ceiling. split; [exact R0|]. split; [exact RAL|]. split; [exact RC|]. split; [exact RF| exact RI].
  - intros Hsc. pose proof (MallocFacts_inv2.areach_facts_proof st LB0 AR) as MF.
    pose proof (mf_gmeta _ _ MF g b ltac:(rewrite get_meta_rec_strip; exact Hmem)) as GF. cbv zeta in GF. rewrite !get_meta_rec_strip in GF.
    change (get_meta_rec st g) with (MR st g) in GF. fold stride in GF.
    destruct GF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X). apply X. exact Hsc.
  - intros Hsc. exact (proj1 (g_stride _ _ _ _ _ _ GO Hsc)).
  - auto.
  - (* [comment removed for export] *)
    cbv zeta. rewrite Ec, C3, Cc, Cb. fold stride. fold q.
    replace (r_base r + snd c + stride - IB - (r_base r + snd c + UNIT * off) - k) with res by lia.
    split. { replace (r_base r + snd c + UNIT * off - 4) with (r_base r + (snd c + UNIT * off - 4)) by lia. apply (KB _ _ K4). unfold UNIT, IB in *; lia. }
    split. { replace (r_base r + snd c + UNIT * off - 3) with (r_base r + (snd c + UNIT * off - 3)) by lia. apply (KB _ _ K3). unfold UNIT, IB in *; lia. }
    split. { destruct (KB _ _ K2 ltac:(unfold UNIT, IB in *; lia)) as [B2 V2]. destruct (KB _ _ K1 ltac:(unfold UNIT, IB in *; lia)) as [B1 V1].
             destruct (q_bytes q HQ) as (EQQ & QB0 & QB1). rewrite EQQ at 1.
             rewrite (le2_lohi (byte_of q 0) (byte_of q 1)) by assumption.
             change [b8 (byte_of q 0); b8 (byte_of q 1)] with ([b8 (byte_of q 0)] ++ [b8 (byte_of q 1)]). apply bytes_at_app. cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat].
             split; [replace (r_base r + snd c + UNIT * off - 2) with (r_base r + (snd c + UNIT * off - 2)) by lia; exact B2|].
             replace (r_base r + snd c + UNIT * off - 2 + 1) with (r_base r + (snd c + UNIT * off - 1)) by lia. exact B1. }
    split; [exact HQ|]. split; [lia|].
    split. { intros R5. destruct (KF R5) as (F0 & F1 & F2 & F3 & F5 & R32).
             destruct (KB _ _ F0 ltac:(unfold UNIT, IB in *; lia)) as [B0' V0]. destruct (KB _ _ F1 ltac:(unfold UNIT, IB in *; lia)) as [B1' V1].
             destruct (KB _ _ F2 ltac:(unfold UNIT, IB in *; lia)) as [B2' V2]. destruct (KB _ _ F3 ltac:(unfold UNIT, IB in *; lia)) as [B3' V3].
             split; [| split; [replace (r_base r + snd c + stride - IB - 5) with (r_base r + (snd c + stride - IB - 5)) by lia; apply (KB _ _ F5); unfold UNIT, IB in *; lia| exact R32]].
             rewrite le4_bytes by lia.
             destruct (res_bytes res ltac:(lia)) as (E0 & E1 & E2 & E3).
             rewrite <- E0, <- E1, <- E2, <- E3.
             change [b8 (byte_of res 0); b8 (byte_of res 1); b8 (byte_of res 2); b8 (byte_of res 3)] with ([b8 (byte_of res 0)] ++ ([b8 (byte_of res 1)] ++ ([b8 (byte_of res 2)] ++ [b8 (byte_of res 3)]))).
             repeat (apply bytes_at_app; cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat]; split);
               first [ replace (r_base r + snd c + stride - IB - 4) with (r_base r + (snd c + stride - IB - 4)) by lia; exact B0'
                     | replace (r_base r + snd c + stride - IB - 4 + 1) with (r_base r + (snd c + stride - IB - 3)) by lia; exact B1'
                     | replace (r_base r + snd c + stride - IB - 4 + 1 + 1) with (r_base r + (snd c + stride - IB - 2)) by lia; exact B2'
                     | replace (r_base r + snd c + stride - IB - 4 + 1 + 1 + 1) with (r_base r + (snd c + stride - IB - 1)) by lia; exact B3' ]. }
    split. { intros RP. replace (r_base r + snd c + stride - IB - res) with (r_base r + (snd c + stride - IB - res)) by lia. apply (KB _ _ (KC RP)). unfold UNIT, IB in *; lia. }
    replace (r_base r + snd c + stride - IB) with (r_base r + (snd c + stride - IB)) by lia. apply (KB _ _ KE). unfold UNIT, IB in *; lia.
  - (* [comment removed for export] *)
    destruct (GR b _ Hgb) as (w8 & RW & _). pose proof (rw_cells_bytes_at psegs m _ _ RW) as BA. cbn [cells_bytes cbytes app g_meta] in BA.
    change (le8 (pw st (Some g)) ++ [w8]) with (le8 (wz (conc st g)) ++ [w8]) in BA. apply bytes_at_app in BA as [BA _]. exact BA.
  - split; [apply rmrep_meta_chunk; [exact MRP| exact (go_slot _ _ _ GOK)]| exact (go_slot _ _ _ GOK)].
  - (* [comment removed for export] *)
    destruct (go_slot _ _ _ GOK) as (a & ar & ka & Ha & Hka & Eg).
    destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & Ra0 & RaAL & RaC).
    destruct (ia_areas _ IA a ar Ha) as (_ & CHK & _ & _).
    pose proof (ia_secret _ IA) as [SR SI]. pose proof (ia_ctx _ IA) as _.
    (* [comment removed for export] *)
    assert (WS : wz (bv_unsigned malloc_secret_val) = malloc_secret_val) by (unfold wz; apply Z_to_bv_bv_unsigned).
    exists (bv_unsigned malloc_secret_val).
    assert (GE : conc st g = conc st a + (AREA_HDR + META_SIZE * ka)) by (rewrite Eg, conc_aadd by (rewrite Hra; eexists; reflexivity); reflexivity).
    assert (PG : conc st g - conc st g mod 4096 = conc st a).
    { rewrite GE. unfold AREA_HDR, META_SIZE, NSLOTS in *. apply area_page_base; [| exact Hka]. rewrite Ca. rewrite Z.add_mod, RaAL, SaL by lia. reflexivity. }
    rewrite PG. split; [| split].
    + pose proof (bv_unsigned_in_range _ (@malloc_secret_val AGRD)) as S5. change (bv_modulus 64) with (2^64) in S5. exact S5.
    + destruct (ARr a ar Ha) as (HD & _ & _). pose proof (rw_cells_bytes_at psegs m _ _ HD) as BA. cbn [cells_bytes cbytes app] in BA.
      rewrite WS. apply bytes_at_app in BA as [BA _]. exact BA.
    + destruct CX as (HD & _). pose proof (rw_cells_bytes_at psegs m _ _ HD) as BA. unfold rctx_head_cells in BA.
      rewrite (rsec_area st a ar Ha) in BA. cbn [cells_bytes cbytes app] in BA.
      rewrite WS. apply bytes_at_app in BA as [BA _]. exact BA.
  - unfold alloc_ceiling. split; [lia|]. split; [lia| lia].
  - (* [comment removed for export] *)
    intros b' gh Hb' Efb. rewrite Ec, Es. cbn [snd]. fold stride.
    assert (Hh : hosts st b' (default g (g_meta gh))).
    { destruct (ci_grps _ _ C b' gh Hb') as (g' & Eg' & _). exists (g_active_idx gh). rewrite Hb'. destruct gh as [gm gai]; cbn in Eg' |- *. subst gm. reflexivity. }
    assert (NH : s_groups st !! (fst b, sstart (MR st g) i) = None).
    { rewrite <- Es, <- Ec. exact (bk_nogroup _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, k) Hin0)). }
    destruct (sep_ghdr _ _ _ _ IM IG IS g b i Hb Hi NH _ b' Hh Efb) as [X|X]; [left; exact X| right].
    rewrite sstart_succ in X. fold stride in X.
    destruct (hosts_ok _ _ _ IG _ _ Hh) as (ai' & _ & GO'). pose proof (g_align _ _ _ _ _ _ GO') as [_ AL'].
    assert (SM0 : sstart (MR st g) i mod 16 = 0).
    { unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hb). unfold UNIT in *.
      rewrite Z.add_mod, (Z.add_mod (snd b) 16), B16, Z.mul_mod, SM by lia. reflexivity. }
    unfold UNIT in *. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    intros blk' Hb' NE Efb.
    destruct (MallocFacts_inv2.LB_geo _ st L BL LS INV LB0 CR blk' Hb') as (c' & off' & n' & m' & bm' & i' & r'' & Hk' & C1' & C2' & Hm' & Hi' & Ec' & NH' & Hr'' & Kr'' & Ea' & Ho' & Hn' & Fit').
    rewrite C1' in NE, Efb. rewrite Ec in NE. rewrite Ec, Cc.
    assert (Efb' : fst bm' = fst b) by (rewrite Ec' in Efb; exact Efb).
    rewrite Efb', Hr in Hr''. injection Hr'' as <-.
    assert (NH : s_groups st !! (fst b, sstart (MR st g) i) = None).
    { rewrite <- Es, <- Ec. exact (bk_nogroup _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, k) Hin0)). }
    assert (NE' : m' <> g \/ i' <> i).
    { destruct (aptr_eq_dec m' g) as [->|]; [right| now left]. intros ->. apply NE. rewrite Ec', Es, Efb'. reflexivity. }
    rewrite Ec' in NH'.
    assert (ESC : sstart (MR st g) i = snd c) by (rewrite Es; reflexivity).
    pose proof (sstart_succ st m' i') as SS'.
    destruct (sep_ext _ _ _ _ IM IG IS g b i Hb Hi NH m' bm' i' Hm' Efb' Hi' NE' NH') as [X|X]; rewrite sstart_succ in X; rewrite ESC in X.
    + left. fold stride in X. unfold UNIT, IB in *. lia.
    + right. fold stride in X. unfold UNIT, IB in *. lia.
  - exists L, LS, BL. rewrite Ec. auto 10.
Qed.
End INTRO.


End CeilWrap.
(* [comment removed for export] *)
Notation RAREACH := (AREACH_from ref_reserved).
