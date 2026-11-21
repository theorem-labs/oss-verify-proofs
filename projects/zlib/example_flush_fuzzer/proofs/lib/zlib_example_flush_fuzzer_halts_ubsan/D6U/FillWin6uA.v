(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux MemFill DSLayout ZSLayout FillWinMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState DeflateLz ZChkAdl LmatchModel AdlerModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u DS6u Callee6u.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

End FXG.
Notation zstR := (zst s6u_segs 180992 181024 181056) (only parsing).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Definition FR : Z := 272.
(* 1.4 UBSan: fill_window 96 + read_buf 48 + adler32_z 128 = 272 bytes of stack (1.3.1: 80 + 48 + 128 = 256) *)

Lemma bs_check_ok : forall bs ws, - 2 ^ 62 <= bs < 2 ^ 62 -> 0 < ws < 2 ^ 16 ->
  szwrap 64 (bs mod 2 ^ 64 - ws) = bs - ws /\ szwrap 64 (bs mod 2 ^ 64) = bs.
Proof.
  intros bs ws Hbs Hws. split.
  - rewrite <- (szwrap_mod 64 (bs mod 2 ^ 64 - ws)) by lia.
    rewrite Zminus_mod_idemp_l. rewrite szwrap_mod by lia. apply szwrap_small; lia.
  - rewrite szwrap_mod by lia. apply szwrap_small; lia.
Qed.

Lemma even_plus_shl1 : forall p i, p mod 2 = 0 -> 0 <= p -> 0 <= i -> (p + i * 2 ^ 1) mod 2 ^ 1 = 0.
Proof.
  intros p i Hp H0 Hi. change (2 ^ 1) with 2.
  rewrite Z.add_mod, Hp, Z.mod_mul by lia. reflexivity.
Qed.

Definition BSI (s : deflate_state) : Prop := ds_strstart s - 2 ^ 62 <= ds_block_start s < 2 ^ 62.

Record ub_pre (S : Z) (p : ds_ptrs) (zp : zs_ptrs) : Prop := UBPRE {
  ub_S8 : S mod 8 = 0;
  ub_S1 : 0 < S;
  ub_strm1 : 0 < p_strm p;
  ub_strm8 : p_strm p mod 8 = 0;
  ub_hd2 : p_head p mod 2 = 0;
  ub_pv2 : p_prev p mod 2 = 0;
  ub_inp : 0 < zp_in zp }.

End FXG.
Ltac open_ub HUB :=
  pose proof (ub_S8 _ _ _ HUB) as US8; pose proof (ub_S1 _ _ _ HUB) as US1;
  pose proof (ub_strm1 _ _ _ HUB) as UST1; pose proof (ub_strm8 _ _ _ HUB) as UST8;
  pose proof (ub_hd2 _ _ _ HUB) as UHD2; pose proof (ub_pv2 _ _ _ HUB) as UPV2;
  pose proof (ub_inp _ _ _ HUB) as UINP.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Section Walk.
Variable mem : word -> option byte.
Variables (S sp : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) (ra : word).
Variable regs0 : bvmap 5 word.
Variable ROM : (word -> option byte) -> Prop.
Hypothesis Hret : ret_ok ra.
Hypothesis HFW : fw_pre s6u_segs 180992 181024 181056 272 mem S sp p zp ds.
Hypothesis Hwrap1 : ds_wrap ds = 1.
Hypothesis HD2 : 2 <= p_head p.
Hypothesis PV2 : 2 <= p_prev p.
Hypothesis HROM : ROM mem.
Hypothesis ROM_local : rom_local6u ROM.
Hypothesis MEMCPY : memcpy_run6u.
Hypothesis MEMSET : memset_run6u.
Hypothesis ADLER : adler32_run6u ROM.
Hypothesis HUB : ub_pre S p zp.

Local Abbreviation W := (p_window p).
Local Abbreviation PV := (p_prev p).
Local Abbreviation HD := (p_head p).
Local Abbreviation strm := (p_strm p).
Local Abbreviation INP := (zp_in zp).
Local Abbreviation ws := (ds_w_size ds).
Local Abbreviation hs := (ds_hash_size ds).
Local Abbreviation ILEN := (arr_len (cs_input (ds_strm ds))).

Definition LF : franges :=
  [(sp - 272, 272); (S + 128, 4); (S + 152, 8); (S + 172, 12); (S + 5932, 4); (S + 5952, 12);
   (W, 2 * ws); (PV, 2 * ws); (HD, 2 * hs); (strm, 24); (strm + 96, 8)].
(* 1.4: (S + 5952, 12) = high_water (8 bytes at 5952) and slid (4 bytes at 5960,
   set to 1 by `sw s9,28(s2)` at 0x16b00); 1.3.1 had high_water at (S + 5944, 8) *)

Hypothesis HLFimg : forall x, in_franges LF x -> IMG6U_LO <= x < IMG6U_HI -> False.

Definition fr_layout : list (Z * nat) :=
  [(8, 8%nat); (16, 8%nat); (24, 8%nat); (32, 8%nat); (40, 8%nat); (48, 8%nat);
   (56, 8%nat); (64, 8%nat); (72, 8%nat); (80, 8%nat); (88, 8%nat)].
Definition fr_vals : list Z :=
  [bv_unsigned (getr regs0 25); bv_unsigned (getr regs0 24); bv_unsigned (getr regs0 23); bv_unsigned (getr regs0 22);
   bv_unsigned (getr regs0 21); bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 19);
   bv_unsigned (getr regs0 18); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 8); bv_unsigned ra].
(* 1.4 UBSan: a 96-byte frame, s9 saved at 8(sp), word 0 unused (1.3.1: 80 bytes, s8 at 0(sp)) *)
Definition FRM (m : word -> option byte) : Prop := fields s6u_segs m (sp - 96) fr_layout fr_vals.

Definition CSTL (s : deflate_state) : Prop :=
  arr_len (ds_window s) = 2 * ws /\ arr_len (ds_prev s) = ws /\ arr_len (ds_head s) = hs
  /\ cs_input (ds_strm s) = cs_input (ds_strm ds) /\ ds_wrap s = ds_wrap ds
  /\ ds_w_size s = ws /\ ds_hash_size s = hs.

Definition RI (m : word -> option byte) (s : deflate_state) : Prop :=
  zstR m S p zp s /\ FRM m
  /\ mapped m (sp - 272) 272 /\ mapped m S dsl_SIZE /\ mapped m W (2 * ws)
  /\ mapped m PV (2 * ws) /\ mapped m HD (2 * hs) /\ mapped m strm zsl_SIZE
  /\ agree_out LF mem m /\ (forall x, mem x <> None -> m x <> None) /\ ROM m.

Local Ltac open_fw := open_fwpre HFW.
Local Ltac apart i j := apart_of HFW i j.


Lemma fr_layout_within : layout_within fr_layout 96 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma RI_transport : forall m m' s s' (G : franges),
  RI m s -> CSTL s ->
  agree_out G m m' -> (forall x, in_franges G x -> in_franges LF x) ->
  (forall x, m x <> None -> m' x <> None) ->
  (disj_franges G S dsl_SIZE -> ds_window s' = ds_window s /\ ds_prev s' = ds_prev s /\ ds_head s' = ds_head s ->
     dsl_scalars s6u_segs 180992 181024 181056 m S p s' -> True) ->
  dsl_scalars s6u_segs 180992 181024 181056 m' S p s' ->
  dsl_windowA s6u_segs m' p s' -> dsl_prevA s6u_segs m' p s' -> dsl_headA s6u_segs m' p s' ->
  zsl_scalars s6u_segs m' strm zp S (ds_strm s') -> zsl_input s6u_segs m' zp (ds_strm s') ->
  disj_franges G (sp - 96) 96 ->
  RI m' s'.
Proof.
  intros m m' s s' G (Hz & Hfr & M1 & M2 & M3 & M4 & M5 & M6 & Hag & Hgr & Hrom) HC HagG HGLF Hgr' _
         Hsc' Hw' Hp' Hh' Hzs' Hin' HdF. open_fw.
  unfold RI. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
  - unfold zst. split; [exact Hsc'|]. split; [exact Hw'|]. split; [exact Hp'|]. split; [exact Hh'|]. split; [exact Hzs'|exact Hin'].
  - unfold FRM in *. eapply (fields_agree_out s6u_segs G); [exact Hfr | exact fr_layout_within | exact HagG | exact HdF | lia | lia].
  - intros x Hx. apply Hgr'. exact (M1 x Hx).
  - intros x Hx. apply Hgr'. exact (M2 x Hx).
  - intros x Hx. apply Hgr'. exact (M3 x Hx).
  - intros x Hx. apply Hgr'. exact (M4 x Hx).
  - intros x Hx. apply Hgr'. exact (M5 x Hx).
  - intros x Hx. apply Hgr'. exact (M6 x Hx).
  - intros x Hx. rewrite (HagG x) by (intros HG; exact (Hx (HGLF _ HG))). exact (Hag x Hx).
  - intros x Hx. apply Hgr'. exact (Hgr x Hx).
  - apply (ROM_local m m' Hrom). intros x Hx. apply HagG. intros HG. exact (HLFimg _ (HGLF _ HG) Hx).
Qed.

Lemma zst_keep_S : forall m m' s G, RI m s -> agree_out G m m' -> disj_franges G S dsl_SIZE ->
  dsl_scalars s6u_segs 180992 181024 181056 m' S p s.
Proof.
  intros m m' s G (Hz & _) Hag Hd. open_fw.
  eapply (dsl_scalars_agree s6u_segs _ _ _ G); [exact (proj1 Hz) | exact Hag | exact Hd | lia | unfold dsl_SIZE; lia].
Qed.

Lemma zst_keep_W : forall m m' s G, RI m s -> CSTL s -> agree_out G m m' -> disj_franges G W (2 * ws) ->
  dsl_windowA s6u_segs m' p s.
Proof.
  intros m m' s G (Hz & _) (Hl & _) Hag Hd. open_fw.
  destruct Hz as (_ & Hw & _). unfold dsl_windowA in *. rewrite Hl in Hw |- *.
  eapply (cells_agree_out s6u_segs G); [exact Hag | | cbn; lia | lia | lia | exact Hw].
  replace (1 * (2 * ws)) with (2 * ws) by lia. exact Hd.
Qed.

Lemma zst_keep_PV : forall m m' s G, RI m s -> CSTL s -> agree_out G m m' -> disj_franges G PV (2 * ws) ->
  dsl_prevA s6u_segs m' p s.
Proof.
  intros m m' s G (Hz & _) (_ & Hl & _) Hag Hd. open_fw.
  destruct Hz as (_ & _ & Hpv & _). unfold dsl_prevA in *. rewrite Hl in Hpv |- *.
  eapply (cells_agree_out s6u_segs G); [exact Hag | exact Hd | cbn; lia | lia | lia | exact Hpv].
Qed.

Lemma zst_keep_HD : forall m m' s G, RI m s -> CSTL s -> agree_out G m m' -> disj_franges G HD (2 * hs) ->
  dsl_headA s6u_segs m' p s.
Proof.
  intros m m' s G (Hz & _) (_ & _ & Hl & _) Hag Hd. open_fw.
  destruct Hz as (_ & _ & _ & Hh & _). unfold dsl_headA in *. rewrite Hl in Hh |- *.
  eapply (cells_agree_out s6u_segs G); [exact Hag | exact Hd | cbn; lia | lia | lia | exact Hh].
Qed.

Lemma zst_keep_Z : forall m m' s G, RI m s -> agree_out G m m' -> disj_franges G strm zsl_SIZE ->
  zsl_scalars s6u_segs m' strm zp S (ds_strm s).
Proof.
  intros m m' s G (Hz & _) Hag Hd. open_fw. destruct Hz as (_ & _ & _ & _ & Hzs & _).
  eapply (zsl_scalars_agree s6u_segs G); [exact Hzs | exact Hag | exact Hd | lia | unfold zsl_SIZE; lia].
Qed.

Lemma zst_keep_IN : forall m m' s G, RI m s -> CSTL s -> agree_out G m m' -> disj_franges G INP ILEN ->
  zsl_input s6u_segs m' zp (ds_strm s).
Proof.
  intros m m' s G (Hz & _) (_ & _ & _ & Hinp & _) Hag Hd. open_fw. destruct Hz as (_ & _ & _ & _ & _ & Hin).
  unfold zsl_input in *. rewrite Hinp in Hin |- *.
  eapply (cells_agree_out s6u_segs G); [exact Hag | | cbn; lia | lia | lia | exact Hin].
  replace (1 * ILEN) with ILEN by lia. exact Hd.
Qed.

Lemma RI_updS : forall m s (off : Z) (w : nat) v s',
  RI m s -> CSTL s ->
  dsl_scalars s6u_segs 180992 181024 181056 (wbytes m (zw (S + off)) (Z_to_le_bytes w v)) S p s' ->
  ds_window s' = ds_window s -> ds_prev s' = ds_prev s -> ds_head s' = ds_head s -> ds_strm s' = ds_strm s ->
  sub_franges LF (S + off) (Z.of_nat w) -> 0 <= off -> off + Z.of_nat w <= dsl_SIZE ->
  RI (wbytes m (zw (S + off)) (Z_to_le_bytes w v)) s'.
Proof.
  intros m s off w v s' HRI HC Hsc' Ew Ep Eh Est Hsub Ho1 Ho2. open_fw.
  assert (Hag : agree_out [(S + off, Z.of_nat w)] m (wbytes m (zw (S + off)) (Z_to_le_bytes w v))).
  { apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try lia; [apply agree_out_refl|].
    apply sub_franges_here; lia. }
  assert (Hgr : forall x, m x <> None -> wbytes m (zw (S + off)) (Z_to_le_bytes w v) x <> None).
  { intros x Hx. apply wbytes_grows. exact Hx. }
  apart 0%nat 1%nat. apart 1%nat 2%nat. apart 1%nat 3%nat. apart 1%nat 4%nat. apart 1%nat 5%nat. apart 1%nat 6%nat.
  eapply (RI_transport m _ s s' [(S + off, Z.of_nat w)] HRI HC Hag); try assumption.
  - intros x Hx. apply Hsub. cbn in Hx. lia.
  - intros; exact I.
  - unfold dsl_windowA. rewrite Ew. apply (zst_keep_W m _ s _ HRI HC Hag).
    apply disj_franges_cons; [lia | apply disj_franges_nil].
  - unfold dsl_prevA. rewrite Ep. apply (zst_keep_PV m _ s _ HRI HC Hag).
    apply disj_franges_cons; [lia | apply disj_franges_nil].
  - unfold dsl_headA. rewrite Eh. apply (zst_keep_HD m _ s _ HRI HC Hag).
    apply disj_franges_cons; [lia | apply disj_franges_nil].
  - rewrite Est. apply (zst_keep_Z m _ s _ HRI Hag). apply disj_franges_cons; [unfold zsl_SIZE; lia | apply disj_franges_nil].
  - rewrite Est. apply (zst_keep_IN m _ s _ HRI HC Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply disj_franges_cons; [lia | apply disj_franges_nil].
Qed.

Lemma RI_updZ : forall m s (off : Z) (w : nat) v st',
  RI m s -> CSTL s ->
  zsl_scalars s6u_segs (wbytes m (zw (strm + off)) (Z_to_le_bytes w v)) strm zp S st' ->
  cs_input st' = cs_input (ds_strm s) ->
  sub_franges LF (strm + off) (Z.of_nat w) -> 0 <= off -> off + Z.of_nat w <= zsl_SIZE ->
  RI (wbytes m (zw (strm + off)) (Z_to_le_bytes w v)) (set_strm s st').
Proof.
  intros m s off w v st' HRI HC Hzs' Ein Hsub Ho1 Ho2. open_fw.
  assert (Hag : agree_out [(strm + off, Z.of_nat w)] m (wbytes m (zw (strm + off)) (Z_to_le_bytes w v))).
  { apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try lia; [apply agree_out_refl|].
    apply sub_franges_here; lia. }
  assert (Hgr : forall x, m x <> None -> wbytes m (zw (strm + off)) (Z_to_le_bytes w v) x <> None).
  { intros x Hx. apply wbytes_grows. exact Hx. }
  apart 0%nat 5%nat. apart 1%nat 5%nat. apart 2%nat 5%nat. apart 3%nat 5%nat. apart 4%nat 5%nat. apart 5%nat 6%nat.
  eapply (RI_transport m _ s (set_strm s st') [(strm + off, Z.of_nat w)] HRI HC Hag); try assumption.
  - intros x Hx. apply Hsub. cbn in Hx. lia.
  - intros; exact I.
  - apply (zst_keep_S m _ s _ HRI Hag). apply disj_franges_cons; [unfold dsl_SIZE; lia | apply disj_franges_nil].
  - apply (zst_keep_W m _ s _ HRI HC Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply (zst_keep_PV m _ s _ HRI HC Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply (zst_keep_HD m _ s _ HRI HC Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - unfold zsl_input. cbn [ds_strm set_strm]. rewrite Ein.
    pose proof (zst_keep_IN m _ s _ HRI HC Hag) as K. unfold zsl_input in K. apply K.
    apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply disj_franges_cons; [lia | apply disj_franges_nil].
Qed.

Lemma RI_updW : forall m m' s w' lo hi,
  RI m s -> CSTL s ->
  agree_out [(W + lo, hi - lo)] m m' -> (forall x, m x <> None -> m' x <> None) ->
  0 <= lo -> lo <= hi -> hi <= 2 * ws ->
  arr_len w' = 2 * ws -> cells s6u_segs m' W 1 1 (2 * ws) (arr_get w') ->
  RI m' (set_window s w').
Proof.
  intros m m' s w' lo hi HRI HC Hag Hgr Hlo Hlh Hhi Hlen Hc. open_fw.
  apart 0%nat 2%nat. apart 1%nat 2%nat. apart 2%nat 3%nat. apart 2%nat 4%nat. apart 2%nat 5%nat. apart 2%nat 6%nat.
  eapply (RI_transport m m' s (set_window s w') [(W + lo, hi - lo)] HRI HC Hag); try assumption.
  - intros x Hx. cbn in Hx. unfold LF. cbn [in_franges]. do 6 right. left. lia.
  - intros; exact I.
  - apply (zst_keep_S m _ s _ HRI Hag). apply disj_franges_cons; [unfold dsl_SIZE; lia | apply disj_franges_nil].
  - unfold dsl_windowA. cbn [ds_window set_window]. rewrite Hlen. exact Hc.
  - apply (zst_keep_PV m _ s _ HRI HC Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply (zst_keep_HD m _ s _ HRI HC Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply (zst_keep_Z m _ s _ HRI Hag). apply disj_franges_cons; [unfold zsl_SIZE; lia | apply disj_franges_nil].
  - apply (zst_keep_IN m _ s _ HRI HC Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply disj_franges_cons; [lia | apply disj_franges_nil].
Qed.

Lemma RI_updHD : forall m m' s h',
  RI m s -> CSTL s ->
  agree_out [(HD, 2 * hs)] m m' -> (forall x, m x <> None -> m' x <> None) ->
  arr_len h' = hs -> cells s6u_segs m' HD 2 2 hs (arr_get h') ->
  RI m' (set_head s h').
Proof.
  intros m m' s h' HRI HC Hag Hgr Hlen Hc. open_fw.
  apart 0%nat 4%nat. apart 1%nat 4%nat. apart 2%nat 4%nat. apart 3%nat 4%nat. apart 4%nat 5%nat. apart 4%nat 6%nat.
  eapply (RI_transport m m' s (set_head s h') [(HD, 2 * hs)] HRI HC Hag); try assumption.
  - intros x Hx. cbn in Hx. unfold LF. cbn [in_franges]. do 8 right. left. lia.
  - intros; exact I.
  - apply (zst_keep_S m _ s _ HRI Hag). apply disj_franges_cons; [unfold dsl_SIZE; lia | apply disj_franges_nil].
  - apply (zst_keep_W m _ s _ HRI HC Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply (zst_keep_PV m _ s _ HRI HC Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - unfold dsl_headA. cbn [ds_head set_head]. rewrite Hlen. exact Hc.
  - apply (zst_keep_Z m _ s _ HRI Hag). apply disj_franges_cons; [unfold zsl_SIZE; lia | apply disj_franges_nil].
  - apply (zst_keep_IN m _ s _ HRI HC Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply disj_franges_cons; [lia | apply disj_franges_nil].
Qed.

Lemma RI_updPV : forall m m' s pv',
  RI m s -> CSTL s ->
  agree_out [(PV, 2 * ws)] m m' -> (forall x, m x <> None -> m' x <> None) ->
  arr_len pv' = ws -> cells s6u_segs m' PV 2 2 ws (arr_get pv') ->
  RI m' (set_prev s pv').
Proof.
  intros m m' s pv' HRI HC Hag Hgr Hlen Hc. open_fw.
  apart 0%nat 3%nat. apart 1%nat 3%nat. apart 2%nat 3%nat. apart 3%nat 4%nat. apart 3%nat 5%nat. apart 3%nat 6%nat.
  eapply (RI_transport m m' s (set_prev s pv') [(PV, 2 * ws)] HRI HC Hag); try assumption.
  - intros x Hx. cbn in Hx. unfold LF. cbn [in_franges]. do 7 right. left. lia.
  - intros; exact I.
  - apply (zst_keep_S m _ s _ HRI Hag). apply disj_franges_cons; [unfold dsl_SIZE; lia | apply disj_franges_nil].
  - apply (zst_keep_W m _ s _ HRI HC Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - unfold dsl_prevA. cbn [ds_prev set_prev]. rewrite Hlen. exact Hc.
  - apply (zst_keep_HD m _ s _ HRI HC Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply (zst_keep_Z m _ s _ HRI Hag). apply disj_franges_cons; [unfold zsl_SIZE; lia | apply disj_franges_nil].
  - apply (zst_keep_IN m _ s _ HRI HC Hag). apply disj_franges_cons; [lia | apply disj_franges_nil].
  - apply disj_franges_cons; [lia | apply disj_franges_nil].
Qed.


Definition fwC : cfg :=
  CFG [(0%nat, 256); (1%nat, 65536); (2%nat, 65536); (3%nat, 256)] [] [EVar 1%nat]
      [0x16a20; 0x16a70; 0x16adc; 0x16b08; 0x16b34; 0x16b60; 0x16b68; 0x16b80; 0x19458; 0x194b8; 0x194ec;
       0x16bc4; 0x16c4c; 0x16d00; 0x16d1c; 0x16dc0; 0x2a824; 0x1af3c; 0x1b6c4; 0x2ac28;
       0x16df8; 0x16df4; 0x19548] [].

Local Ltac sc_close :=
  cbn [fam] in *; change (2 ^ 1) with 2 in *; zmod_bounds;
  first [ assumption
        | rewrite ?szwrap64_32_small by lia; rewrite ?szwrap32_small by lia; repeat (rewrite Z.mod_small by lia); lia
        | zcond_close
        | fam_bounds
        | symex_read_auto | symex_sok_auto | symex_store_auto ].

Definition shv (m : Z) : Z := if m <? ws then 0 else m - ws.

Lemma slide_val_eq : forall mv, 0 <= mv < 65536 -> 512 <= ws <= 32768 ->
  Z.land ((if mv <? (szwrap 32 (mv - ws)) mod 2 ^ 64 then 1 else 0) + -1) (szwrap 32 (mv - ws)) = shv mv.
Proof.
  intros mv Hm Hws. unfold shv. rewrite (szwrap32_small (mv - ws)) by lia.
  destruct (Z.ltb_spec mv ws) as [C|C].
  - rewrite zmod64_neg by lia. destruct (Z.ltb_spec mv (mv - ws + 2 ^ 64)); [|lia]. apply Z.land_0_l.
  - rewrite (Z.mod_small (mv - ws)) by lia. destruct (Z.ltb_spec mv (mv - ws)); [lia|]. apply Z.land_m1_l.
Qed.

Lemma shv_shm : forall mv, 0 <= mv < 65536 -> shv mv = shm ws mv.
Proof.
  intros mv Hm. open_fw. unfold shv. rewrite shm_small by lia.
  destruct (Z.ltb_spec mv ws), (Z.leb_spec ws mv); lia.
Qed.

Lemma shv_range : forall mv, 0 <= mv < 65536 -> 0 <= shv mv < 65536.
Proof. intros mv Hm. open_fw. unfold shv. destruct (Z.ltb_spec mv ws); lia. Qed.


Definition hlPC (hd : bool) : word := if hd then (0x16adc%bv : word) else (0x16b34%bv : word).
Definition hlPCX (hd : bool) : word := if hd then (0x16b08%bv : word) else (0x16b60%bv : word).
(* 1.4: the prev loop exits at the slid store `sw s9,28(s2)` (0x16b00), walked by hx *)
Definition hlRP (hd : bool) : reg := if hd then (13%bv : reg) else (12%bv : reg).
Definition hlRN (hd : bool) : reg := if hd then (12%bv : reg) else (13%bv : reg).

Section SlideLoop.
Variable B : Z.
Hypothesis HB : 2 <= B /\ B < 2 ^ 63.

Local Ltac hl_run pc dirs k a F pins :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let A := fresh "A" in
  lazymatch goal with |- context [mkst ?regs _ ?m s6u_rom] =>
  symex s6u_segs fwC 14%nat dirs [RVal (EApp1 F (EVar 33))]
    pins
    [(32%nat, 2 ^ 63); (33%nat, 2 ^ 31); (34%nat, 2 ^ 16)] NoRegions
    [B; k - 1; ws] NoVals (fam (ds_window ds) a a (cs_input (ds_strm ds))) F0'
    (mkst regs pc m s6u_rom) R HR Hfr Hms;
  first
    [ sc_close
    | exists R; split;
      [ exact Hms
      | split; [ symex_reg HR (13%bv : reg) as A; rewrite A; change (2 ^ 1) with 2; rewrite ?szwrap32_small by lia; f_equal; lia
      | split; [ symex_reg HR (12%bv : reg) as A; rewrite A; change (2 ^ 1) with 2; rewrite ?szwrap32_small by lia; f_equal; lia
      | fr_weak Hfr ] ] ] ]
  end.

Lemma hl_step : forall (hd : bool) regs m (g : Z -> Z) k n,
  cells s6u_segs m B 2 2 n g -> (forall i, 0 <= i < n -> 0 <= g i < 65536) -> n < 2 ^ 31 ->
  mapped m B (2 * n) ->
  getr regs (hlRP hd) = zw (B + 2 * k) -> getr regs (hlRN hd) = zw k -> getr regs 10 = zw ws -> getr regs 20 = zw 3 ->
  1 <= k <= n ->
  exists R, msteps s6u_segs (mkst regs (hlPC hd) m s6u_rom)
              (mkst R (if k - 1 =? 0 then hlPCX hd else hlPC hd)
                    (wbytes m (zw (B + k * 2 + -2)) (Z_to_le_bytes 2 (shv (g (k - 1))))) s6u_rom)
    /\ getr R 13 = zw (if hd then B + 2 * (k - 1) else k - 1)
    /\ getr R 12 = zw (if hd then k - 1 else B + 2 * (k - 1))
    /\ (forall r : reg, reg_in r [12; 13; 14; 15]%bv = false -> getr R r = getr regs r).
Proof.
  intros hd regs m g k n Hc Hg Hn Hmap HP HN H10 H20 Hk. open_fw.
  clear MEMCPY MEMSET ADLER HROM.
  pose proof (Hg (k - 1) ltac:(lia)) as Hgk.
  assert (HF : pb (arr_init n g) (k - 1) = g (k - 1)).
  { unfold pb. rewrite arr_get_init. apply Z.mod_small. lia. }
  assert (Hrd : exists bs, rdn s6u_segs m (zw (B + (k - 1) * 2 ^ 1)) 2 = Some bs
                           /\ bytes_le_to_Z bs = pb (arr_init n g) (k - 1)).
  { eapply cell_read_at; [ replace (B + (k - 1) * 2 ^ 1) with (B + 2 * (k - 1)) by lia; exact (Hc (k - 1) ltac:(lia)) |].
    rewrite HF. change (2 ^ (8 * Z.of_nat 2)) with 65536. rewrite Z.mod_small by lia. reflexivity. }
  replace (B + 2 * k) with (B + (k - 1) * 2 ^ 1 + 2) in HP by lia.
  replace k with (k - 1 + 1) in HN at 1 by lia.
  replace (B + k * 2 + -2) with (B + (k - 1) * 2 ^ 1) by lia.
  rewrite <- (slide_val_eq (g (k - 1))) by lia.
  rewrite <- HF in Hgk |- *. unfold mapped in Hmap.
  destruct hd; cbn [hlPC hlPCX hlRP hlRN] in *; destruct (Z.eqb_spec (k - 1) 0) as [Kz|Knz].
  - hl_run (0x16adc%bv : word) [false; false] k (arr_init n g) 1%nat
      [(13, EAdd (EAdd (EVar 32) (EShl (EVar 33) 1)) (ELit 2)); (12, EAdd (EVar 33) (ELit 1)); (10, EVar 34); (20, ELit 3)].
  - hl_run (0x16adc%bv : word) [false; true] k (arr_init n g) 1%nat
      [(13, EAdd (EAdd (EVar 32) (EShl (EVar 33) 1)) (ELit 2)); (12, EAdd (EVar 33) (ELit 1)); (10, EVar 34); (20, ELit 3)].
  - hl_run (0x16b34%bv : word) [false; false] k (arr_init n g) 1%nat
      [(12, EAdd (EAdd (EVar 32) (EShl (EVar 33) 1)) (ELit 2)); (13, EAdd (EVar 33) (ELit 1)); (10, EVar 34); (20, ELit 3)].
  - hl_run (0x16b34%bv : word) [false; true] k (arr_init n g) 1%nat
      [(12, EAdd (EAdd (EVar 32) (EShl (EVar 33) 1)) (ELit 2)); (13, EAdd (EVar 33) (ELit 1)); (10, EVar 34); (20, ELit 3)].
Qed.

Lemma hl_loop : forall (hd : bool) cnt regs m (g : Z -> Z) k n,
  k = Z.of_nat cnt -> 1 <= k <= n -> n < 2 ^ 31 ->
  cells s6u_segs m B 2 2 n g -> (forall i, 0 <= i < n -> 0 <= g i < 65536) ->
  mapped m B (2 * n) ->
  getr regs (hlRP hd) = zw (B + 2 * k) -> getr regs (hlRN hd) = zw k -> getr regs 10 = zw ws -> getr regs 20 = zw 3 ->
  exists R m', msteps s6u_segs (mkst regs (hlPC hd) m s6u_rom) (mkst R (hlPCX hd) m' s6u_rom)
    /\ cells s6u_segs m' B 2 2 n (fun i => if i <? k then shv (g i) else g i)
    /\ agree_out [(B, 2 * n)] m m'
    /\ (forall x, m x <> None -> m' x <> None)
    /\ (forall r : reg, reg_in r [12; 13; 14; 15]%bv = false -> getr R r = getr regs r).
Proof.
  intros hd. induction cnt as [|cnt IH]; intros regs m g k n Hk Hkr Hn Hc Hg Hmap HP HN H10 H20; [lia|]. open_fw.
  destruct (hl_step hd regs m g k n Hc Hg Hn Hmap HP HN H10 H20 Hkr) as (R1 & Hms1 & A13 & A12 & Hfr1).
  pose proof (shv_range (g (k - 1)) (Hg (k - 1) ltac:(lia))) as Hsr.
  assert (Hc1 : cells s6u_segs (wbytes m (zw (B + k * 2 + -2)) (Z_to_le_bytes 2 (shv (g (k - 1))))) B 2 2 n
                  (fun i => if i =? k - 1 then shv (g (k - 1)) else g i)).
  { replace (B + k * 2 + -2) with (B + 2 * (k - 1)) by lia. apply cells_write_cell; try lia. exact Hc. }
  assert (Hg1 : forall i, 0 <= i < n -> 0 <= (fun i => if i =? k - 1 then shv (g (k - 1)) else g i) i < 65536).
  { intros i Hi. cbn beta. destruct (i =? k - 1); [lia | apply Hg; lia]. }
  assert (Hag1 : agree_out [(B, 2 * n)] m (wbytes m (zw (B + k * 2 + -2)) (Z_to_le_bytes 2 (shv (g (k - 1)))))).
  { apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try lia; [apply agree_out_refl|].
    apply sub_franges_here; cbn; lia. }
  destruct (Z.eqb_spec (k - 1) 0) as [Kz|Knz].
  - exists R1, (wbytes m (zw (B + k * 2 + -2)) (Z_to_le_bytes 2 (shv (g (k - 1))))).
    split; [exact Hms1|]. split.
    { refine (cells_ext _ _ _ _ _ _ _ _ _ Hc1). intros i Hi. cbn beta.
      destruct (Z.eqb_spec i (k - 1)), (Z.ltb_spec i k); subst; try reflexivity; try lia;
      replace i with (k - 1) by lia; reflexivity. }
    split; [exact Hag1|]. split; [intros x Hx; apply wbytes_grows; exact Hx | exact Hfr1].
  - assert (HP1 : getr R1 (hlRP hd) = zw (B + 2 * (k - 1))) by (destruct hd; cbn [hlRP]; [exact A13 | exact A12]).
    assert (HN1 : getr R1 (hlRN hd) = zw (k - 1)) by (destruct hd; cbn [hlRN]; [exact A12 | exact A13]).
    destruct (IH R1 _ _ (k - 1) n ltac:(lia) ltac:(lia) Hn Hc1 Hg1
                 ltac:(apply mapped_wbytes; exact Hmap)
                 HP1 HN1
                 ltac:(rewrite (Hfr1 10%bv eq_refl); exact H10)
                 ltac:(rewrite (Hfr1 20%bv eq_refl); exact H20))
      as (R2 & m' & Hms2 & Hc2 & Hag2 & Hgr2 & Hfr2).
    exists R2, m'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split.
    { refine (cells_ext _ _ _ _ _ _ _ _ _ Hc2). intros i Hi. cbn beta.
      destruct (Z.ltb_spec i (k - 1)), (Z.eqb_spec i (k - 1)), (Z.ltb_spec i k); subst; try reflexivity; try lia. }
    split; [eapply agree_out_trans; [exact Hag1 | exact Hag2]|].
    split; [intros x Hx; apply Hgr2; apply wbytes_grows; exact Hx|].
    intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.
End SlideLoop.


Definition LREGS (regs : bvmap 5 word) : Prop :=
  getr regs 8 = zw S /\ getr regs 2 = zw (sp - 96) /\ getr regs 18 = zw (S + 5932) /\ getr regs 19 = zw ws
  /\ getr regs 20 = zw 3 /\ getr regs 21 = zw 32 /\ getr regs 22 = zw 2 /\ getr regs 23 = zw 261
  /\ getr regs 24 = zw (ws + -262) /\ getr regs 25 = zw 1.
(* 1.4 UBSan: s7 = 261, s8 = w_size - 262, s9 = 1 (1.3.1: s7 = w_size - 262, s8 = 261, no s9) *)

Lemma LREGS_via : forall regs R (l : list reg),
  LREGS regs -> (forall r : reg, reg_in r l = false -> getr R r = getr regs r) ->
  forallb (fun r : reg => negb (reg_in r l)) [8; 2; 18; 19; 20; 21; 22; 23; 24; 25]%bv = true ->
  LREGS R.
Proof.
  intros regs R l (A8 & A2 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25) Hfr Hl.
  cbn [forallb] in Hl. rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in Hl.
  destruct Hl as (X8 & X2 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & _).
  unfold LREGS. rewrite !Hfr by assumption.
  split; [exact A8|]. split; [exact A2|]. split; [exact A18|]. split; [exact A19|].
  split; [exact A20|]. split; [exact A21|]. split; [exact A22|]. split; [exact A23|]. split; [exact A24|exact A25].
Qed.

Definition LP : list (Z * expr) :=
  [(8, EVar 32); (2, EVar 33); (18, EAdd (EVar 32) (ELit 5932)); (19, EVar 39); (20, ELit 3);
   (21, ELit 32); (22, ELit 2); (23, ELit 261); (24, EAdd (EVar 39) (ELit (-262))); (25, ELit 1)].
Definition LB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 63); (36%nat, 2 ^ 63);
   (37%nat, 2 ^ 63); (38%nat, 2 ^ 63); (39%nat, 32769); (40%nat, 65537)].

Local Ltac run fuel dirs rds pinsx vbx pvx F1 :=
  let pins := eval vm_compute in (LP ++ pinsx) in
  let vb := eval vm_compute in (LB ++ vbx) in
  let pv := constr:(S :: (sp - 96) :: W :: PV :: HD :: strm :: INP :: ws :: hs :: pvx) in
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  unfold mapped, dsl_SIZE, zsl_SIZE in *;
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs fwC fuel dirs rds pins vb NoRegions pv NoVals F1 F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => try sc_close
  end.

Local Ltac open_lregs H :=
  let H' := fresh "HL'" in pose proof H as H';
  destruct H' as (P8 & P2 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25).

Local Ltac trim := clear MEMCPY MEMSET ADLER HROM.


Definition moreof (s : deflate_state) : Z := 2 * ws - ds_strstart s - ds_lookahead s.

Lemma h_noslide : forall regs m s,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  getr regs 10 = zw (ds_lookahead s) ->
  ds_strstart s < ws + (ws - 262) ->
  exists R, msteps s6u_segs (mkst regs (0x16a20 : word) m s6u_rom) (mkst R (0x16b68 : word) m s6u_rom)
    /\ LREGS R /\ getr R 9 = zw (moreof s) /\ getr R 11 = zw (ds_strstart s)
    /\ (forall r : reg, reg_in r [9; 10; 11; 12; 13]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m s HRI HW HK HL H10 Hns. open_fw. open_wf HW. open_lregs HL.
  destruct HRI as (Hz & _). trim.
  cellS Hz dsl_strstart C172. cellS Hz dsl_window_size C104. rewrite Vwsz in C104.
  cellS Hz dsl_w_size C80. rewrite Vws in C80.
  run 30%nat [true] [RVal (EVar 42); RVal (EVar 39); RVal (EAdd (EVar 39) (EVar 39))]
      [(10, EVar 41)] [(41%nat, 65537); (42%nat, 65537)]
      [ds_lookahead s; ds_strstart s] (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
  exists R. split; [exact Hms|].
  split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
  symex_reg HR (9%bv : reg) as A9. symex_reg HR (11%bv : reg) as A11.
  unfold moreof. rewrite szwrap32_small in A9 by lia.
  split; [rewrite A9; f_equal; lia|]. split; [exact A11|]. fr_weak Hfr.
Qed.

Lemma h_slide : forall regs m s,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  getr regs 10 = zw (ds_lookahead s) ->
  ws + (ws - 262) <= ds_strstart s ->
  exists R, msteps s6u_segs (mkst regs (0x16a20 : word) m s6u_rom) (mkst R (0x2a824 : word) m s6u_rom)
    /\ LREGS R /\ getr R 1 = zw 0x16a70
    /\ getr R 10 = zw W /\ getr R 11 = zw (W + ws) /\ getr R 12 = zw (ds_strstart s + ds_lookahead s - ws)
    /\ getr R 9 = zw (moreof s)
    /\ (forall r : reg, reg_in r [1; 9; 10; 11; 12; 13]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m s HRI HW HK HL H10 Hsl. open_fw. open_wf HW. open_lregs HL.
  destruct HRI as (Hz & _). trim.
  cellS Hz dsl_strstart C172. cellS Hz dsl_window_size C104. rewrite Vwsz in C104.
  cellS Hz dsl_w_size C80. rewrite Vws in C80. cellS Hz dsl_window C96.
  run 30%nat [false; false; false] [RVal (EVar 42); RVal (EVar 39); RVal (EAdd (EVar 39) (EVar 39)); RVal (EVar 34)]
      [(10, EVar 41)] [(41%nat, 65537); (42%nat, 65537)]
      [ds_lookahead s; ds_strstart s] (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
  exists R. split; [exact Hms|].
  split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
  symex_reg HR (1%bv : reg) as A1. symex_reg HR (10%bv : reg) as A10. symex_reg HR (11%bv : reg) as A11.
  symex_reg HR (12%bv : reg) as A12. symex_reg HR (9%bv : reg) as A9.
  split; [exact A1|]. split; [exact A10|]. split; [exact A11|].
  unfold moreof. rewrite ?szwrap32_small in A12 by lia. rewrite ?szwrap32_small in A9 by lia.
  split; [rewrite A12; rewrite ?Z.mod_small by lia; f_equal; lia|].
  split; [rewrite A9; f_equal; lia|]. fr_weak Hfr.
Qed.

Lemma ret_ok_zw : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> ret_ok (zw z).
Proof. intros z Hz H2. apply ret_ok_even. rewrite u_zw_small by lia. exact H2. Qed.


Lemma CSTL_set_window : forall s w', CSTL s -> arr_len w' = 2 * ws -> CSTL (set_window s w').
Proof. intros s w' HK Hl. unfold CSTL in *. dsred. rewrite Hl. tauto. Qed.

Lemma slide_copy : forall regs m s n,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs ->
  getr regs 1 = zw 0x16a70 -> getr regs 10 = zw W -> getr regs 11 = zw (W + ws) -> getr regs 12 = zw n ->
  0 <= n <= ws ->
  let w' := arr_blit (ds_window s) 0 (ds_window s) ws n in
  exists R m', msteps s6u_segs (mkst regs (0x2a824 : word) m s6u_rom) (mkst R (0x16a70 : word) m' s6u_rom)
    /\ RI m' (set_window s w') /\ CSTL (set_window s w') /\ LREGS R
    /\ (forall r : reg, reg_in r memcpy_clob = false -> getr R r = getr regs r).
Proof.
  intros regs m s n HRI HW HK HL H1 H10 H11 H12 Hn w'. open_fw. open_wf HW.
  destruct HK as (Kwl & Kpl & Khl & Kin & Kwr & Kws & Khs).
  pose proof HRI as (Hz & _ & _ & _ & MW & _). destruct Hz as (_ & Hwin & _).
  unfold dsl_windowA in Hwin. rewrite Kwl in Hwin.
  set (bs := fbytes (arr_get (ds_window s)) ws (Z.to_nat n)).
  assert (Hrd : rdn s6u_segs m (zw (W + ws)) (Z.to_nat n) = Some bs).
  { subst bs. apply (cells_rdn s6u_segs m W (2 * ws)); try lia. exact Hwin. }
  assert (Hlen : length bs = Z.to_nat n) by (subst bs; apply fbytes_length).
  destruct (MEMCPY m regs W (W + ws) (Z.to_nat n) bs (zw 0x16a70) Hrd
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(eapply mapped_sub; [exact MW | lia | lia])
              ltac:(apply ret_ok_zw; [lia | reflexivity])
              H1 H10 H11 ltac:(rewrite Z2Nat.id by lia; exact H12))
    as (R & Hms & A10 & Hfr).
  symex_pc_lit_in Hms.
  exists R, (wbytes m (zw W) bs). split; [exact Hms|].
  assert (Hl' : arr_len w' = 2 * ws) by (subst w'; rewrite arr_len_blit; exact Kwl).
  split; [|split; [apply CSTL_set_window; [unfold CSTL; tauto | exact Hl']
         |split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity] | exact Hfr]]].
  eapply (RI_updW m _ s w' 0 n HRI ltac:(unfold CSTL; tauto)).
  - replace (W + 0) with W by lia. replace (n - 0) with (Z.of_nat (length bs)) by lia.
    apply memcpy_agree_out; lia.
  - intros x Hx. apply wbytes_grows. exact Hx.
  - lia. - lia. - lia.
  - exact Hl'.
  - pose proof (cells_wbytes_bytes s6u_segs m W (2 * ws) (arr_get (ds_window s)) 0 bs Hwin
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hc.
    replace (W + 0) with W in Hc by lia.
    refine (cells_ext _ _ _ _ _ _ _ _ _ Hc). intros i Hi. cbn beta. subst w'.
    rewrite arr_get_blit. unfold arr_inb. rewrite Kwl, Hlen.
    destruct (Z.leb_spec 0 i), (Z.ltb_spec i (0 + Z.of_nat (Z.to_nat n))), (Z.ltb_spec i (0 + Z.max 0 n)),
      (Z.ltb_spec i (2 * ws)); cbn [andb]; try reflexivity; try lia.
    subst bs. rewrite fbytes_nth; [f_equal; lia | lia |].
    intros j Hj. apply (wf_wb _ _ _ HW). lia.
Qed.


Definition slide_fields (s1 : deflate_state) : deflate_state :=
  let s2 := set_match_start s1 (wrap32 (ds_match_start s1 - ws)) in
  let s3 := set_strstart s2 (ds_strstart s1 - ws) in
  let s4 := set_block_start s3 (ds_block_start s1 - ws) in
  if ds_strstart s1 - ws <? ds_insert s1 then set_insert s4 (ds_strstart s1 - ws) else s4.

Local Ltac in_LF := unfold LF; repeat first [ apply sub_franges_here; cbn; lia | apply sub_franges_later ].

Local Ltac ri_field upd :=
  intros m s v HRI HK; pose proof HRI as (Hz & _); open_fw;
  eapply RI_updS; [ exact HRI | exact HK
    | apply upd; [exact (proj1 Hz) | lia | unfold dsl_SIZE; lia]
    | reflexivity | reflexivity | reflexivity | reflexivity
    | in_LF | lia | unfold dsl_SIZE; cbn; lia ].

Lemma RI_match_start : forall m s v, RI m s -> CSTL s ->
  RI (wbytes m (zw (S + 176)) (Z_to_le_bytes 4 v)) (set_match_start s v).
Proof. ri_field (dsl_upd_match_start s6u_segs 180992 181024 181056). Qed.
Lemma RI_strstart : forall m s v, RI m s -> CSTL s ->
  RI (wbytes m (zw (S + 172)) (Z_to_le_bytes 4 v)) (set_strstart s v).
Proof. ri_field (dsl_upd_strstart s6u_segs 180992 181024 181056). Qed.
Lemma RI_lookahead : forall m s v, RI m s -> CSTL s ->
  RI (wbytes m (zw (S + 180)) (Z_to_le_bytes 4 v)) (set_lookahead s v).
Proof. ri_field (dsl_upd_lookahead s6u_segs 180992 181024 181056). Qed.
Lemma RI_block_start : forall m s v, RI m s -> CSTL s ->
  RI (wbytes m (zw (S + 152)) (Z_to_le_bytes 8 v)) (set_block_start s v).
Proof. ri_field (dsl_upd_block_start s6u_segs 180992 181024 181056). Qed.
Lemma RI_ins_h : forall m s v, RI m s -> CSTL s ->
  RI (wbytes m (zw (S + 128)) (Z_to_le_bytes 4 v)) (set_ins_h s v).
Proof. ri_field (dsl_upd_ins_h s6u_segs 180992 181024 181056). Qed.
Lemma RI_insert : forall m s v, RI m s -> CSTL s ->
  RI (wbytes m (zw (S + 5932)) (Z_to_le_bytes 4 v)) (set_insert s v).
Proof. ri_field (dsl_upd_insert s6u_segs 180992 181024 181056). Qed.
Lemma RI_high_water : forall m s v, RI m s -> CSTL s ->
  RI (wbytes m (zw (S + 5952)) (Z_to_le_bytes 8 v)) (set_high_water s v).
Proof. ri_field (dsl_upd_high_water s6u_segs 180992 181024 181056). Qed.
(* 1.4: slid is a junk byte range of the layout, so the store keeps the model state (as the plain port) *)
Lemma RI_slid : forall m s v, RI m s -> CSTL s ->
  RI (wbytes m (zw (S + 5960)) (Z_to_le_bytes 4 v)) s.
Proof. ri_field (dsl_upd_slid s6u_segs 180992 181024 181056). Qed.

Local Ltac cstl := intros; unfold CSTL in *; dsred; assumption.
Lemma CSTL_match_start : forall s v, CSTL s -> CSTL (set_match_start s v). Proof. cstl. Qed.
Lemma CSTL_strstart : forall s v, CSTL s -> CSTL (set_strstart s v). Proof. cstl. Qed.
Lemma CSTL_lookahead : forall s v, CSTL s -> CSTL (set_lookahead s v). Proof. cstl. Qed.
Lemma CSTL_block_start : forall s v, CSTL s -> CSTL (set_block_start s v). Proof. cstl. Qed.
Lemma CSTL_ins_h : forall s v, CSTL s -> CSTL (set_ins_h s v). Proof. cstl. Qed.
Lemma CSTL_insert : forall s v, CSTL s -> CSTL (set_insert s v). Proof. cstl. Qed.

Lemma CSTL_set_head : forall s h', CSTL s -> arr_len h' = hs -> CSTL (set_head s h').
Proof. intros s h' HK Hl. unfold CSTL in *. dsred. rewrite Hl. tauto. Qed.
Lemma CSTL_set_prev : forall s pv', CSTL s -> arr_len pv' = ws -> CSTL (set_prev s pv').
Proof. intros s pv' HK Hl. unfold CSTL in *. dsred. rewrite Hl. tauto. Qed.



Lemma sl2 : forall regs m s1,
  RI m s1 -> CSTL s1 -> LREGS regs -> BSI s1 ->
  0 <= ds_match_start s1 < 2 ^ 32 -> ws <= ds_strstart s1 <= 2 * ws -> 0 <= ds_insert s1 <= ds_strstart s1 ->
  exists R m', msteps s6u_segs (mkst regs (0x16a70 : word) m s6u_rom) (mkst R (0x16adc : word) m' s6u_rom)
    /\ RI m' (slide_fields s1) /\ CSTL (slide_fields s1) /\ LREGS R
    /\ getr R 13 = zw (HD + 2 * hs) /\ getr R 12 = zw hs /\ getr R 10 = zw ws
    /\ getr R 11 = zw (ds_strstart s1 - ws)
    /\ (forall r : reg, reg_in r [10; 11; 12; 13; 14; 15]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m s1 HRI HK HL HBS Hmsr Hstr Hins. open_fw. open_lregs HL. open_ub HUB.
  pose proof HK as (Kwl & Kpl & Khl & Kin & Kwr & Kws & Khs).
  pose proof HRI as (Hz & _ & _ & MS & _).
  cellS Hz dsl_match_start C176. cellS Hz dsl_block_start C152. cellS Hz dsl_strstart C172.
  cellS Hz dsl_insert C5932. cellS Hz dsl_hash_size C132. cellS Hz dsl_head C120. cellS Hz dsl_w_size C80.
  rewrite Khs in C132. rewrite Kws in C80.
  unfold BSI in HBS.
  pose proof (bs_check_ok (ds_block_start s1) ws ltac:(lia) ltac:(lia)) as (BC1 & BC2).
  pose proof (Z.mod_pos_bound (ds_block_start s1) (2 ^ 64) ltac:(lia)) as BR.
  unfold slide_fields.
  set (s2 := set_match_start s1 (wrap32 (ds_match_start s1 - ws))).
  set (s3 := set_strstart s2 (ds_strstart s1 - ws)).
  set (s4 := set_block_start s3 (ds_block_start s1 - ws)).
  assert (E1 : Z_to_le_bytes 4 (szwrap 32 (ds_match_start s1 - ws)) = Z_to_le_bytes 4 (wrap32 (ds_match_start s1 - ws))).
  { apply Z_to_le_bytes_eqm. rewrite wrap32_mod. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
    rewrite szwrap_eqm, Z.mod_mod by lia. reflexivity. }
  assert (E2 : Z_to_le_bytes 8 (ds_block_start s1 mod 2 ^ 64 - ws) = Z_to_le_bytes 8 (ds_block_start s1 - ws)).
  { apply Z_to_le_bytes_eqm. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Zminus_mod_idemp_l. reflexivity. }
  pose proof (RI_strstart m s1 (ds_strstart s1 - ws) HRI HK) as Ra.
  pose proof (CSTL_strstart s1 (ds_strstart s1 - ws) HK) as Ka.
  pose proof (RI_match_start _ _ (wrap32 (ds_match_start s1 - ws)) Ra Ka) as Rb.
  pose proof (CSTL_match_start _ (wrap32 (ds_match_start s1 - ws)) Ka) as Kb.
  pose proof (RI_block_start _ _ (ds_block_start s1 - ws) Rb Kb) as R4.
  pose proof (CSTL_block_start _ (ds_block_start s1 - ws) Kb) as K4.
  assert (E4 : set_block_start (set_match_start (set_strstart s1 (ds_strstart s1 - ws)) (wrap32 (ds_match_start s1 - ws)))
                 (ds_block_start s1 - ws) = s4) by reflexivity.
  rewrite E4 in R4, K4. clear Ra Ka Rb Kb E4.
  trim.
  destruct (Z.ltb_spec (ds_strstart s1 - ws) (ds_insert s1)) as [Lt|Ge].
  - pose proof (RI_insert _ s4 (ds_strstart s1 - ws) R4 K4) as R5.
    pose proof (CSTL_insert s4 (ds_strstart s1 - ws) K4) as K5.
    run 40%nat [false; false; false; false; false]
      [RVal (EVar 43); RVal (EVar 42); RVal (EVar 44); RVal (EVar 45); RVal (EVar 40); RVal (EVar 36); RVal (EVar 39)]
      NoPins [(41%nat, 1); (42%nat, 65537); (43%nat, 2 ^ 32); (44%nat, 2 ^ 64); (45%nat, 65537)]
      [0; ds_strstart s1; ds_match_start s1; ds_block_start s1 mod 2 ^ 64; ds_insert s1]
      (fam (ds_window s1) (ds_head s1) (ds_prev s1) (cs_input (ds_strm s1))).
    all: try solve [rewrite BC1, BC2; zcond_close].
    rewrite E1, E2, (szwrap32_small (ds_strstart s1 - ws)) in Hms by lia.
    eexists R, _. split; [exact Hms|].
    split; [exact R5|]. split; [exact K5|].
    split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
    symex_reg HR (12%bv : reg) as A12. symex_reg HR (13%bv : reg) as A13. symex_reg HR (10%bv : reg) as A10.
    symex_reg HR (11%bv : reg) as A11.
    split; [rewrite A13; change (2 ^ 1) with 2; f_equal; lia|]. split; [rewrite A12; rewrite ?Z.mod_small by lia; f_equal; lia|]. split; [exact A10|].
    split; [rewrite A11, szwrap32_small by lia; reflexivity|]. fr_weak Hfr.
  - run 40%nat [false; true; false; false; false]
      [RVal (EVar 43); RVal (EVar 42); RVal (EVar 44); RVal (EVar 45); RVal (EVar 40); RVal (EVar 36); RVal (EVar 39)]
      NoPins [(41%nat, 1); (42%nat, 65537); (43%nat, 2 ^ 32); (44%nat, 2 ^ 64); (45%nat, 65537)]
      [0; ds_strstart s1; ds_match_start s1; ds_block_start s1 mod 2 ^ 64; ds_insert s1]
      (fam (ds_window s1) (ds_head s1) (ds_prev s1) (cs_input (ds_strm s1))).
    all: try solve [rewrite BC1, BC2; zcond_close].
    rewrite E1, E2, (szwrap32_small (ds_strstart s1 - ws)) in Hms by lia.
    eexists R, _. split; [exact Hms|].
    split; [exact R4|]. split; [exact K4|].
    split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
    symex_reg HR (12%bv : reg) as A12. symex_reg HR (13%bv : reg) as A13. symex_reg HR (10%bv : reg) as A10.
    symex_reg HR (11%bv : reg) as A11.
    split; [rewrite A13; change (2 ^ 1) with 2; f_equal; lia|]. split; [rewrite A12; rewrite ?Z.mod_small by lia; f_equal; lia|]. split; [exact A10|].
    split; [rewrite A11, szwrap32_small by lia; reflexivity|]. fr_weak Hfr.
Qed.



Lemma sl3 : forall regs m s,
  RI m s -> CSTL s -> LREGS regs -> getr regs 10 = zw ws ->
  exists R, msteps s6u_segs (mkst regs (0x16b08 : word) m s6u_rom) (mkst R (0x16b34 : word) m s6u_rom)
    /\ LREGS R /\ getr R 12 = zw (PV + 2 * ws) /\ getr R 13 = zw ws /\ getr R 10 = zw ws
    /\ (forall r : reg, reg_in r [12; 13; 14; 15]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m s HRI HK HL H10. open_fw. open_lregs HL. open_ub HUB.
  pose proof HRI as (Hz & _). cellS Hz dsl_prev C112. trim.
  run 20%nat [false; false; false] [RVal (EVar 35)] [(10, EVar 39)] NoBounds (@nil Z)
      (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
  exists R. split; [exact Hms|].
  split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
  symex_reg HR (12%bv : reg) as A12. symex_reg HR (13%bv : reg) as A13. symex_reg HR (10%bv : reg) as A10.
  split; [rewrite A12; change (2 ^ 1) with 2; f_equal; lia|].
  split; [exact A13|]. split; [exact A10|]. fr_weak Hfr.
Qed.


Lemma hx : forall regs m (s : deflate_state) more,
  RI m s -> CSTL s ->
  LREGS regs -> getr regs 9 = zw more -> 0 <= more <= 2 * ws ->
  exists R m', msteps s6u_segs (mkst regs (0x16b60 : word) m s6u_rom) (mkst R (0x16b68 : word) m' s6u_rom)
    /\ RI m' s /\ LREGS R /\ getr R 9 = zw (ws + more)
    /\ (forall r : reg, reg_in r [9]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m s more HRI HK HL H9 Hm. open_fw. open_lregs HL.
  pose proof HRI as (Hz & _ & _ & MS & _).
  pose proof (RI_slid m s 1 HRI HK) as Rs.
  trim.
  run 5%nat NoDirs NoReads [(9, EVar 41)] [(41%nat, 2 ^ 17)] [more]
      (fam (ds_window s) (ds_head s) (ds_prev s) (cs_input (ds_strm s))).
  eexists R, _. split; [exact Hms|]. split; [exact Rs|].
  split; [eapply LREGS_via; [exact HL | exact Hfr | reflexivity]|].
  symex_reg HR (9%bv : reg) as A9. rewrite ?szwrap32_small in A9 by lia.
  split; [rewrite A9; f_equal; lia|]. fr_weak Hfr.
Qed.


Definition slide_clob : list reg := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.


Lemma slide_run : forall regs m s,
  RI m s -> fw_wf ws hs s -> CSTL s -> LREGS regs -> BSI s ->
  getr regs 10 = zw (ds_lookahead s) ->
  ws + (ws - 262) <= ds_strstart s ->
  let n := ds_strstart s + ds_lookahead s - ws in
  let s5 := slide_fields (set_window s (arr_blit (ds_window s) 0 (ds_window s) ws n)) in
  exists R m', msteps s6u_segs (mkst regs (0x16a20 : word) m s6u_rom) (mkst R (0x16b68 : word) m' s6u_rom)
    /\ RI m' (slide_hash s5) /\ CSTL (slide_hash s5) /\ LREGS R
    /\ getr R 9 = zw (ws + moreof s) /\ getr R 11 = zw (ds_strstart (slide_hash s5))
    /\ (forall r : reg, reg_in r slide_clob = false -> getr R r = getr regs r).
Proof.
  intros regs m s HRI HW HK HL HBS H10 Hsl n s5. open_fw. open_wf HW.
  pose proof HK as (Kwl & Kpl & Khl & Kin & Kwr & Kws & Khs).
  destruct (h_slide regs m s HRI HW HK HL H10 Hsl) as (R1 & Hms1 & HL1 & A1 & A10 & A11 & A12 & A9 & Hfr1).
  destruct (slide_copy R1 m s n HRI HW HK HL1 A1 A10 A11 A12 ltac:(lia))
    as (R2 & m2 & Hms2 & HRI2 & HK2 & HL2 & Hfr2).
  set (s1 := set_window s (arr_blit (ds_window s) 0 (ds_window s) ws n)) in *.
  destruct (sl2 R2 m2 s1 HRI2 HK2 HL2 ltac:(subst s1; unfold BSI in *; dsred; lia)
              ltac:(subst s1; dsred; lia) ltac:(subst s1; dsred; lia) ltac:(subst s1; dsred; lia))
    as (R3 & m3 & Hms3 & HRI3 & HK3 & HL3 & B13 & B12 & B10 & B11 & Hfr3).
  fold s5 in HRI3, HK3.
  pose proof HRI3 as (Hz3 & _ & _ & _ & _ & _ & MH3 & _).
  destruct Hz3 as (_ & _ & _ & Hh3 & _). unfold dsl_headA in Hh3.
  pose proof HK3 as (_ & _ & Khl3 & _). rewrite Khl3 in Hh3.
  assert (Hhb : forall i, 0 <= i < hs -> 0 <= arr_get (ds_head s5) i < 65536).
  { intros i Hi. replace (ds_head s5) with (ds_head s). apply (wf_hb _ _ _ HW). exact Hi.
    subst s5 s1. unfold slide_fields. destruct (_ <? _); reflexivity. }
  pose proof HL3 as (_ & _ & _ & _ & Q20 & _).
  destruct (hl_loop HD ltac:(lia) true
              (Z.to_nat hs) R3 m3 (arr_get (ds_head s5)) hs hs ltac:(lia) ltac:(lia) ltac:(lia) Hh3 Hhb MH3 B13 B12 B10 Q20)
    as (R4 & m4 & Hms4 & Hc4 & Hag4 & Hgr4 & Hfr4).
  cbn [hlPC hlPCX] in Hms4.
  set (h' := slide_hash_loop (Z.to_nat hs) (ds_head s5) hs ws).
  assert (Hlh' : arr_len h' = hs) by (subst h'; rewrite slide_hash_loop_len; exact Khl3).
  assert (HRI4 : RI m4 (set_head s5 h')).
  { eapply (RI_updHD m3 m4 s5 h' HRI3 HK3 Hag4 Hgr4 Hlh').
    refine (cells_ext _ _ _ _ _ _ _ _ _ Hc4). intros i Hi. cbn beta. subst h'.
    rewrite (slide_hash_loop_get (Z.to_nat hs) (ds_head s5) ws i hs) by lia.
    destruct (Z.leb_spec 0 i), (Z.ltb_spec i hs); cbn [andb]; try lia.
    apply shv_shm. apply Hhb. lia. }
  pose proof (CSTL_set_head s5 h' HK3 Hlh') as HK4.
  pose proof (LREGS_via _ _ _ HL3 Hfr4 eq_refl) as HL4.
  destruct (sl3 R4 m4 (set_head s5 h') HRI4 HK4 HL4 ltac:(rewrite (Hfr4 10%bv eq_refl); exact B10))
    as (R5 & Hms5 & HL5 & C12 & C13 & C10 & Hfr5).
  pose proof HRI4 as (Hz4 & _ & _ & _ & _ & MP4 & _).
  destruct Hz4 as (_ & _ & Hp4 & _). unfold dsl_prevA in Hp4. cbn [ds_prev set_head] in Hp4.
  pose proof HK3 as (_ & Kpl3 & _). rewrite Kpl3 in Hp4.
  assert (Hpb : forall i, 0 <= i < ws -> 0 <= arr_get (ds_prev s5) i < 65536).
  { intros i Hi. replace (ds_prev s5) with (ds_prev s). apply (wf_pb _ _ _ HW). exact Hi.
    subst s5 s1. unfold slide_fields. destruct (_ <? _); reflexivity. }
  pose proof HL5 as (_ & _ & _ & _ & Q20' & _).
  destruct (hl_loop PV ltac:(lia) false
              (Z.to_nat ws) R5 m4 (arr_get (ds_prev s5)) ws ws ltac:(lia) ltac:(lia) ltac:(lia) Hp4 Hpb MP4 C12 C13 C10 Q20')
    as (R6 & m6 & Hms6 & Hc6 & Hag6 & Hgr6 & Hfr6).
  cbn [hlPC hlPCX] in Hms6.
  set (pv' := slide_hash_loop (Z.to_nat ws) (ds_prev s5) ws ws).
  assert (Hlp' : arr_len pv' = ws) by (subst pv'; rewrite slide_hash_loop_len; exact Kpl3).
  assert (HRI6 : RI m6 (set_prev (set_head s5 h') pv')).
  { eapply (RI_updPV m4 m6 (set_head s5 h') pv' HRI4 HK4 Hag6 Hgr6 Hlp').
    refine (cells_ext _ _ _ _ _ _ _ _ _ Hc6). intros i Hi. cbn beta. subst pv'.
    rewrite (slide_hash_loop_get (Z.to_nat ws) (ds_prev s5) ws i ws) by lia.
    destruct (Z.leb_spec 0 i), (Z.ltb_spec i ws); cbn [andb]; try lia.
    apply shv_shm. apply Hpb. lia. }
  pose proof (LREGS_via _ _ _ HL5 Hfr6 eq_refl) as HL6.
  pose proof (CSTL_set_prev (set_head s5 h') pv' HK4 Hlp') as HK6.
  destruct (hx R6 m6 (set_prev (set_head s5 h') pv') (moreof s) HRI6 HK6 HL6
              ltac:(rewrite (Hfr6 9%bv eq_refl), (Hfr5 9%bv eq_refl), (Hfr4 9%bv eq_refl), (Hfr3 9%bv eq_refl), (Hfr2 9%bv eq_refl); exact A9)
              ltac:(unfold moreof; lia))
    as (R7 & m7 & Hms7 & HRI7 & HL7 & D9 & Hfr7).
  exists R7, m7.
  split.
  { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
    eapply msteps_trans; [exact Hms4|]. eapply msteps_trans; [exact Hms5|]. eapply msteps_trans; [exact Hms6 | exact Hms7]. }
  assert (Es : slide_hash s5 = set_prev (set_head s5 h') pv').
  { unfold slide_hash. subst h' pv'.
    replace (ds_w_size s5) with ws by (symmetry; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HK3))))))).
    replace (ds_hash_size s5) with hs by (symmetry; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HK3))))))).
    reflexivity. }
  rewrite Es. split; [exact HRI7|]. split; [apply CSTL_set_prev; [exact HK4 | exact Hlp']|].
  split; [exact HL7|].
  split; [exact D9|].
  split.
  { rewrite (Hfr7 11%bv eq_refl), (Hfr6 11%bv eq_refl), (Hfr5 11%bv eq_refl), (Hfr4 11%bv eq_refl), B11. f_equal.
    subst s5 s1. unfold slide_fields. dsred. destruct (_ <? _); dsred; reflexivity. }
  intros r Hr.
  rewrite (Hfr7 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr6 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr5 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr4 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr3 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr2 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  apply Hfr1. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.

End Walk.
End FXG.
