(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptRoom LeptExec LeptExecW LeptExecT LeptExecFP LeptExecB LeptRecs LeptSel.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptDilW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptCselsA.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section CselsA.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma cs_frame_sess : forall C A Ar m0 m md E log (rb : expr) (s F k1 k2 : Z) (blks : list (expr * Z * Z)),
  Cok C -> W C A m md -> log_flat E log ->
  ex_in_regions ((rb, - F, -48) :: (rb, k1, k1 + 8) :: (rb, k2, k2 + 8) :: map exW_blk_region blks) log = true ->
  edenot E rb = Z_to_bv 64 s -> 0 <= s < 2 ^ 64 -> c_top C - LSTK + F <= s -> s <= c_top C -> (48 <=? F) = true ->
  Forall (exW_blk_ok C A Ar E) blks -> forallb (fun b => 0 <? snd b) blks = true ->
  O23LeptCselsA.cs_fra s k1 k2 m0 m -> O23LeptCselsA.cs_fra s k1 k2 m0 (mem_denot E m log).
Proof.
  intros C A Ar m0 m md E log rb s F k1 k2 blks CK HW LF IR Erb Hs Hlo Hhi HF HB _ Hfr a Ha Hk1 Hk2.
  apply Z.leb_le in HF.
  rewrite <- (Hfr a Ha Hk1 Hk2).
  destruct (omem_eq_dec (mem_denot E m log a) (m a)) as [EQ|NE]; [exact EQ|exfalso].
  pose proof (ex_changed E m log _ LF IR a NE) as EX.
  apply Exists_cons in EX as [EX|EX]; [cbv beta iota in EX; rewrite Erb, u_Z2bv in EX by lia; lia|].
  apply Exists_cons in EX as [EX|EX]; [cbv beta iota in EX; rewrite Erb, u_Z2bv in EX by lia; apply Hk1; lia|].
  apply Exists_cons in EX as [EX|EX]; [cbv beta iota in EX; rewrite Erb, u_Z2bv in EX by lia; apply Hk2; lia|].
  apply Exists_exists in EX as (r & Hin & Hr).
  apply in_map_iff in Hin as (b & <- & Hb).
  rewrite Forall_forall in HB. specialize (HB b Hb).
  destruct b as [[pb p] n]. unfold exW_blk_ok in HB. unfold exW_blk_region in Hr. cbv beta iota in HB, Hr.
  destruct HB as (Ep & Hp & Lp & _ & _).
  rewrite Ep, u_Z2bv in Hr by lia.
  assert (Hu : u (Z_to_bv 64 p) <= u a < u (Z_to_bv 64 p) + n) by (rewrite u_Z2bv by lia; lia).
  destruct (blk_byte C A m md (Z_to_bv 64 p) n a CK HW Lp Hu) as (_ & _ & _ & NW & _).
  apply NW. unfold win. lia.
Qed.

(* [comment removed for export] *)
Lemma cs_frame_hop : forall C (s F off k1 k2 : Z) (m0 M M' : word -> option byte),
  Cok C -> FRM C (s + off) M M' -> c_top C - LSTK + F <= s -> (- F <=? off) = true -> (off <=? -48) = true ->
  O23LeptCselsA.cs_fra s k1 k2 m0 M -> O23LeptCselsA.cs_fra s k1 k2 m0 M'.
Proof.
  intros C s F off k1 k2 m0 M M' CK HF Hs Hlo Hhi Hfr a Ha Hk1 Hk2.
  apply Z.leb_le in Hlo, Hhi.
  rewrite <- (Hfr a Ha Hk1 Hk2).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  apply HF.
  - apply above_not_gap. lia.
  - intros G. apply pin_glob in G. unfold inZ in G. lia.
  - intros G. apply pin_errno in G. unfold inZ in G. lia.
  - unfold hcell. lia.
  - unfold scratch. lia.
Qed.

End CselsA.

Section CselsW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition cs_cell (m : word -> option byte) (c : Z * nat * Z) : Prop :=
  rdn SEGS m (Z_to_bv 64 (fst (fst c))) (snd (fst c)) = Some (Z_to_le_bytes (snd (fst c)) (snd c)).
Definition cs_sel_facts (C : lctx) (A A' : AS) (m' : word -> option byte) (sel arr sy sx cy cx : Z) (rows : list Z) (tab : list (list Z)) : Prop :=
  Forall (O23LeptCselsA.cs_blk C A A') ((sel, 32) :: (arr, 8 * sy) :: map (fun r => (r, 4 * sx)) rows) /\
  Forall (cs_cell m') [(sel + 0, 4%nat, sy); (sel + 4, 4%nat, sx); (sel + 8, 4%nat, cy); (sel + 12, 4%nat, cx); (sel + 16, 8%nat, arr); (sel + 24, 8%nat, 0)] /\
  Forall (cs_cell m') (O23LeptCselsA.cs_mk arr 8 8%nat 0 rows) /\
  Forall2 (fun r vals => Forall (cs_cell m') (O23LeptCselsA.cs_mk r 4 4%nat 0 vals)) rows tab.

Lemma cs_mk_nth : forall m base stride n vals i0 (k : nat), Forall (cs_cell m) (O23LeptCselsA.cs_mk base stride n i0 vals) -> (k < length vals)%nat ->
  cs_cell m (base + stride * (i0 + Z.of_nat k), n, nth k vals 0).
Proof.
  intros m base stride n vals. induction vals as [|v t IH]; intros i0 k H Hk.
  - cbn [length] in Hk. lia.
  - cbn [O23LeptCselsA.cs_mk] in H. apply Forall_cons_iff in H as [H0 H1].
    destruct k as [|k].
    + cbn [nth]. replace (i0 + Z.of_nat 0) with i0 by lia. exact H0.
    + cbn [nth]. cbn [length] in Hk.
      replace (i0 + Z.of_nat (S k)) with (i0 + 1 + Z.of_nat k) by lia.
      apply IH; [exact H1 | lia].
Qed.

Lemma cs_f2_len : forall (X Y : Type) (P : X -> Y -> Prop) (l1 : list X) (l2 : list Y), Forall2 P l1 l2 -> length l1 = length l2.
Proof.
  intros X Y P l1 l2 H. induction H as [|x y t1 t2 _ _ IH]; cbn [length]; lia.
Qed.

Lemma cs_f2_nth : forall (X Y : Type) (P : X -> Y -> Prop) (l1 : list X) (l2 : list Y) (dx : X) (dy : Y) (k : nat),
  Forall2 P l1 l2 -> (k < length l1)%nat -> P (nth k l1 dx) (nth k l2 dy).
Proof.
  intros X Y P l1 l2 dx dy k H. revert k. induction H as [|x y t1 t2 Hxy _ IH]; intros k Hk.
  - cbn [length] in Hk. lia.
  - destruct k as [|k]; cbn [nth length] in Hk |- *; [exact Hxy|]. apply IH. lia.
Qed.

Lemma cs_blk_ok : forall C A m md (p n : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some n -> 0 <= p < 2 ^ 64 -> 0 < n ->
  bok (alloc_top (c_vm C)) p n /\ p + n < 2 ^ 47 /\ (forall i, 0 <= i < n -> m (Z_to_bv 64 (p + i)) <> None).
Proof.
  intros C A m md p n HC HW HL Hp Hn.
  destruct (blk_range C A m md (Z_to_bv 64 p) n HC HW HL Hn) as [Hlo Hhi].
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) HL) as (Hn0 & Hal & _ & Hb).
  rewrite u_Z2bv in Hlo, Hhi, Hal by lia.
  pose proof HC as [Ht Hs0 Hs1 _ _].
  rewrite LSTK_val in Ht.
  split; [unfold bok; lia|]. split; [lia|].
  intros i Hi.
  assert (Hi' : 0 <= i < round16 n) by (pose proof (round16_ge n Hn0); lia).
  destruct (Hb i Hi') as (_ & Hd & _).
  unfold at_ in Hd. rewrite u_Z2bv in Hd by lia. exact Hd.
Qed.

Lemma cs_bytes : forall m (a : Z) (k : nat) (v : Z), 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> m (Z_to_bv 64 (a + i)) <> None) ->
  rdn SEGS m (Z_to_bv 64 a) k = Some (Z_to_le_bytes k v) -> bytes_at m a (Z_to_le_bytes k v).
Proof.
  intros m a k v Ha Hk Hd Hr.
  apply (rdn_bytes_at SEGS); rewrite ?length_Z_to_le_bytes; assumption.
Qed.

Lemma cs_rec : forall m (sel sy sx cy cx data name : Z), 0 <= sel -> sel + 32 < 2 ^ 64 ->
  (forall i, 0 <= i < 32 -> m (Z_to_bv 64 (sel + i)) <> None) ->
  0 <= sy < 2 ^ 32 -> 0 <= sx < 2 ^ 32 -> 0 <= cy < 2 ^ 32 -> 0 <= cx < 2 ^ 32 -> 0 <= data < 2 ^ 64 -> 0 <= name < 2 ^ 64 ->
  rdn SEGS m (Z_to_bv 64 (sel + 0)) 4 = Some (Z_to_le_bytes 4 sy) -> rdn SEGS m (Z_to_bv 64 (sel + 4)) 4 = Some (Z_to_le_bytes 4 sx) ->
  rdn SEGS m (Z_to_bv 64 (sel + 8)) 4 = Some (Z_to_le_bytes 4 cy) -> rdn SEGS m (Z_to_bv 64 (sel + 12)) 4 = Some (Z_to_le_bytes 4 cx) ->
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 data) -> rdn SEGS m (Z_to_bv 64 (sel + 24)) 8 = Some (Z_to_le_bytes 8 name) ->
  RECat m sel (sel_flds sy sx cy cx data name).
Proof.
  intros m sel sy sx cy cx data name H0 H32 Hd Hsy Hsx Hcy Hcx Hdt Hnm R0 R4 R8 R12 R16 R24.
  unfold RECat, sel_flds. cbn [flds_len flds_wf flds_bytes].
  split; [lia|]. split; [lia|]. split.
  - change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
    repeat split; lia.
  - rewrite !bytes_at_app, !length_Z_to_le_bytes.
    repeat split;
      match goal with
      | |- bytes_at m _ [] => intros i Hi; cbn [length Z.of_nat] in Hi; lia
      | |- bytes_at m ?a (Z_to_le_bytes ?k ?v) =>
          apply cs_bytes;
          [ lia | lia
          | intros i Hi; replace (a + i) with (sel + (a - sel + i)) by lia; apply Hd; lia
          | match goal with H : rdn SEGS m (Z_to_bv 64 ?b) k = Some (Z_to_le_bytes k v) |- _ => replace a with b by lia; exact H end ]
      end.
Qed.

Lemma cs_sel_of : forall C A A' m' md' (sel arr sy sx cy cx : Z) (rows : list Z) (tab : list (list Z)),
  Cok C -> W C A' m' md' ->
  cs_sel_facts C A A' m' sel arr sy sx cy cx rows tab ->
  List.NoDup (O23LeptCselsA.cs_words sel arr rows) ->
  Z.of_nat (length rows) = sy -> 1 <= sy <= 10000 -> 1 <= sx <= 10000 -> 0 <= cy < 2 ^ 32 -> 0 <= cx < 2 ^ 32 ->
  O23LeptCselsA.cs_tab_ok sx tab = true ->
  sel_at (alloc_top (c_vm C)) A' m' sel (O23LeptCselsA.cs_sv sy sx cy cx arr rows) /\ sel_cont m' (O23LeptCselsA.cs_sv sy sx cy cx arr rows) (O23LeptCselsA.cs_tab tab) /\
  (forall p, sel_blk sel (O23LeptCselsA.cs_sv sy sx cy cx arr rows) p ->
     In (Z_to_bv 64 p) (O23LeptCselsA.cs_words sel arr rows) /\ live A (Z_to_bv 64 p) = None /\ live (c_A0 C) (Z_to_bv 64 p) = None) /\
  (forall q, In q (O23LeptCselsA.cs_words sel arr rows) -> exists p, sel_blk sel (O23LeptCselsA.cs_sv sy sx cy cx arr rows) p /\ q = Z_to_bv 64 p).
Proof.
  intros C A A' m' md' sel arr sy sx cy cx rows tab HC HW HF ND Hlen Hsy Hsx Hcy Hcx Htab.
  destruct HF as (FB & FS & FA & FR).
  apply Forall_cons_iff in FB as [Bs FB]. apply Forall_cons_iff in FB as [Ba FBr].
  rewrite Forall_forall in FBr.
  assert (Brow : forall r, In r rows -> live A' (Z_to_bv 64 r) = Some (4 * sx) /\ live A (Z_to_bv 64 r) = None /\
                                       live (c_A0 C) (Z_to_bv 64 r) = None /\ 0 <= r < 2 ^ 64).
  { intros r Hr. exact (FBr (r, 4 * sx) (in_map (fun r0 => (r0, 4 * sx)) rows r Hr)). }
  unfold O23LeptCselsA.cs_blk in Bs, Ba. cbn [fst snd] in Bs, Ba.
  destruct Bs as (Ls & Lsa & Lsc & Rs). destruct Ba as (La & Laa & Lac & Ra).
  apply Forall_cons_iff in FS as [Fsy FS]. apply Forall_cons_iff in FS as [Fsx FS].
  apply Forall_cons_iff in FS as [Fcy FS]. apply Forall_cons_iff in FS as [Fcx FS].
  apply Forall_cons_iff in FS as [Fdt FS]. apply Forall_cons_iff in FS as [Fnm _].
  unfold cs_cell in Fsy, Fsx, Fcy, Fcx, Fdt, Fnm. cbn [fst snd] in Fsy, Fsx, Fcy, Fcx, Fdt, Fnm.
  pose proof ND as ND'.
  unfold O23LeptCselsA.cs_words in ND'. cbn [map] in ND'.
  apply NoDup_cons_iff in ND' as [NDs ND']. apply NoDup_cons_iff in ND' as [NDa NDr].
  apply NoDup_map_inv in NDr.
  pose proof (cs_f2_len _ _ _ _ _ FR) as Ltab.
  destruct (cs_blk_ok C A' m' md' sel 32 HC HW Ls Rs ltac:(lia)) as (Bks & Ts & Ds).
  destruct (cs_blk_ok C A' m' md' arr (8 * sy) HC HW La Ra ltac:(lia)) as (Bka & Ta & Da).
  assert (Hsa : arr <> sel) by (intros Es; apply NDs; rewrite Es; left; reflexivity).
  assert (Hrow : forall i, 0 <= i < sy ->
     (Z.to_nat i < length rows)%nat /\ In (O23LeptCselsA.cs_rows rows i) rows /\
     O23LeptCselsA.cs_rows rows i <> sel /\ O23LeptCselsA.cs_rows rows i <> arr).
  { intros i Hi. assert (Hk : (Z.to_nat i < length rows)%nat) by lia.
    assert (Hin : In (O23LeptCselsA.cs_rows rows i) rows) by (unfold O23LeptCselsA.cs_rows; apply nth_In; exact Hk).
    split; [exact Hk|]. split; [exact Hin|]. split; intros Es.
    - apply NDs. right. rewrite <- Es. apply in_map. exact Hin.
    - apply NDa. rewrite <- Es. apply in_map. exact Hin. }
  split; [|split; [|split]].
  - unfold sel_at, O23LeptCselsA.cs_sv. cbn [v_sy v_sx v_cy v_cx v_data v_name v_rows].
    split; [lia|]. split; [lia|]. split; [exact Bks|]. split; [exact Ls|].
    split; [apply cs_rec; try lia; assumption|].
    split; [exact Bka|]. split; [exact La|]. split; [exact Hsa|]. split.
    + intros i Hi. destruct (Hrow i Hi) as (Hk & Hin & N1 & N2).
      destruct (Brow _ Hin) as (Lr & _ & _ & Rr).
      destruct (cs_blk_ok C A' m' md' _ (4 * sx) HC HW Lr Rr ltac:(lia)) as (Bkr & _ & _).
      split; [exact Bkr|]. split; [exact Lr|]. split; [exact N2|]. split; [exact N1|].
      pose proof (cs_mk_nth m' arr 8 8%nat rows 0 (Z.to_nat i) FA Hk) as Ci. unfold cs_cell in Ci. cbn [fst snd] in Ci.
      replace (arr + 8 * (0 + Z.of_nat (Z.to_nat i))) with (arr + 8 * i) in Ci by lia.
      apply cs_bytes; [lia | change (Z.of_nat 8) with 8; lia | | exact Ci].
      intros t Ht. change (Z.of_nat 8) with 8 in Ht.
      replace (arr + 8 * i + t) with (arr + (8 * i + t)) by lia. apply Da. lia.
    + intros i j Hi Hj Hij Es.
      destruct (Hrow i Hi) as (Hki & _). destruct (Hrow j Hj) as (Hkj & _).
      unfold O23LeptCselsA.cs_rows in Es.
      pose proof (proj1 (NoDup_nth rows 0) NDr (Z.to_nat i) (Z.to_nat j) Hki Hkj Es). lia.
  - unfold sel_cont, O23LeptCselsA.cs_sv. cbn [v_sy v_sx v_rows]. intros i j Hi Hj.
    destruct (Hrow i Hi) as (Hk & _).
    assert (Hint : In (nth (Z.to_nat i) tab []) tab) by (apply nth_In; lia).
    unfold O23LeptCselsA.cs_tab_ok in Htab. rewrite forallb_forall in Htab.
    pose proof (Htab _ Hint) as Hv. cbv beta in Hv. apply andb_prop in Hv as [Hvl Hvv]. apply Z.eqb_eq in Hvl.
    rewrite forallb_forall in Hvv.
    assert (Hl : (Z.to_nat j < length (nth (Z.to_nat i) tab []))%nat) by lia.
    assert (Hinv : In (nth (Z.to_nat j) (nth (Z.to_nat i) tab []) 0) (nth (Z.to_nat i) tab [])) by (apply nth_In; exact Hl).
    pose proof (Hvv _ Hinv) as Hr. cbv beta in Hr. apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.ltb_lt in Hr2.
    pose proof (cs_f2_nth _ _ _ rows tab 0 [] (Z.to_nat i) FR Hk) as Frow. cbv beta in Frow.
    pose proof (cs_mk_nth m' _ 4 4%nat _ 0 (Z.to_nat j) Frow Hl) as Cj. unfold cs_cell in Cj. cbn [fst snd] in Cj.
    replace (0 + Z.of_nat (Z.to_nat j)) with j in Cj by lia.
    unfold O23LeptCselsA.cs_tab, O23LeptCselsA.cs_rows. split; [lia | exact Cj].
  - unfold sel_blk, O23LeptCselsA.cs_sv. cbn [v_data v_sy v_rows].
    intros p [-> | [-> | (i & Hi & ->)]].
    + split; [unfold O23LeptCselsA.cs_words; cbn [map]; left; reflexivity|]. split; assumption.
    + split; [unfold O23LeptCselsA.cs_words; cbn [map]; right; left; reflexivity|]. split; assumption.
    + destruct (Hrow i Hi) as (_ & Hin & _ & _). destruct (Brow _ Hin) as (_ & Lra & Lrc & _).
      split; [unfold O23LeptCselsA.cs_words; cbn [map]; right; right; apply in_map; exact Hin|]. split; assumption.
  - intros q Hq. unfold O23LeptCselsA.cs_words in Hq. apply in_map_iff in Hq as (x & <- & Hx).
    unfold sel_blk, O23LeptCselsA.cs_sv. cbn [v_data v_sy v_rows].
    destruct Hx as [<- | [<- | Hx]].
    + exists sel. split; [left; reflexivity | reflexivity].
    + exists arr. split; [right; left; reflexivity | reflexivity].
    + apply In_nth with (d := 0) in Hx as (k & Hk & <-).
      exists (nth k rows 0). split; [|reflexivity].
      right; right. exists (Z.of_nat k). split; [lia|].
      unfold O23LeptCselsA.cs_rows. rewrite Nat2Z.id. reflexivity.
Qed.

End CselsW.
