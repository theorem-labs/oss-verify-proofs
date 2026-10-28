(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptRecs LeptSel LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptTextSelW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptTextSelC.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition tsel_text (K : nat) : Z := match K with 1%nat => 0x1e73b | 2%nat => 0x10c18 | 3%nat => 0x1304c | _ => 0x17281 end%Z.

Definition PC_selstr : Z := 0xa5894.

(* [comment removed for export] *)
Definition sel_cells (m : word -> option byte) (sv : selv) (c : Z -> Z -> Z) : Prop :=
  forall i j, (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z ->
    rdn SEGS m (Z_to_bv 64 (v_rows sv i + 4 * j)) 4 = Some (Z_to_le_bytes 4 (c i j)).

Section TextSel.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.

(* [comment removed for export] *)
Lemma sel_cells_keep : forall (A : AS) m m' sv c,
  (forall i, (0 <= i < v_sy sv)%Z -> live A (Z_to_bv 64 (v_rows sv i)) = Some (4 * v_sx sv)%Z /\ (0 <= v_rows sv i)%Z /\ (v_rows sv i + 4 * v_sx sv < 2 ^ 64)%Z) ->
  LIVK A m m' -> sel_cells m sv c -> sel_cells m' sv c.
Proof.
  intros A m m' sv c Hrows HL Hc i j Hi Hj.
  destruct (Hrows i Hi) as (Lr & Hr0 & Hr1).
  rewrite <- (Hc i j Hi Hj).
  apply rdn_ext.
  - rewrite u_Z2bv by lia. lia.
  - intros x Hx. rewrite u_Z2bv in Hx by lia.
    pose proof (HL (Z_to_bv 64 (v_rows sv i)) (4 * v_sx sv)%Z (bv_unsigned x - v_rows sv i)%Z Lr ltac:(lia)) as E.
    unfold at_ in E. rewrite u_Z2bv in E by lia.
    replace (v_rows sv i + (bv_unsigned x - v_rows sv i))%Z with (bv_unsigned x) in E by lia.
    rewrite zbv_self in E. exact E.
Qed.

(* [comment removed for export] *)
Lemma tsw_blk : forall C A m md (p n : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some n -> (0 <= p < 2 ^ 64)%Z -> (0 < n)%Z ->
  bok (alloc_top (c_vm C)) p n /\ (p + n < 2 ^ 47)%Z /\ (forall i, (0 <= i < n)%Z -> m (Z_to_bv 64 (p + i)) <> None).
Proof.
  intros C A m md p n HC HW HL Hp Hn.
  destruct (blk_range C A m md (Z_to_bv 64 p) n HC HW HL Hn) as [Hlo Hhi].
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) HL) as (Hn0 & Hal & _ & Hb).
  rewrite u_Z2bv in Hlo, Hhi, Hal by lia.
  pose proof HC as [Ht Hs0 Hs1 _ _].
  rewrite LSTK_val in Ht.
  split; [unfold bok; lia|]. split; [lia|].
  intros i Hi.
  assert (Hi' : (0 <= i < round16 n)%Z) by (pose proof (round16_ge n Hn0); lia).
  destruct (Hb i Hi') as (_ & Hd & _).
  unfold at_ in Hd. rewrite u_Z2bv in Hd by lia. exact Hd.
Qed.

(* [comment removed for export] *)
Lemma tsw_bytes : forall m (a : Z) (k : nat) (v : Z), (0 <= a)%Z -> (a + Z.of_nat k <= 2 ^ 64)%Z ->
  (forall i, (0 <= i < Z.of_nat k)%Z -> m (Z_to_bv 64 (a + i)) <> None) ->
  rdn SEGS m (Z_to_bv 64 a) k = Some (Z_to_le_bytes k v) -> bytes_at m a (Z_to_le_bytes k v).
Proof.
  intros m a k v Ha Hk Hd Hr.
  apply (rdn_bytes_at SEGS); rewrite ?length_Z_to_le_bytes; assumption.
Qed.

(* [comment removed for export] *)
Lemma tsw_rec : forall m (sel sy sx cy cx data name : Z), (0 <= sel)%Z -> (sel + 32 < 2 ^ 64)%Z ->
  (forall i, (0 <= i < 32)%Z -> m (Z_to_bv 64 (sel + i)) <> None) ->
  (0 <= sy < 2 ^ 32)%Z -> (0 <= sx < 2 ^ 32)%Z -> (0 <= cy < 2 ^ 32)%Z -> (0 <= cx < 2 ^ 32)%Z -> (0 <= data < 2 ^ 64)%Z -> (0 <= name < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (sel + 0)) 4 = Some (Z_to_le_bytes 4 sy) -> rdn SEGS m (Z_to_bv 64 (sel + 4)) 4 = Some (Z_to_le_bytes 4 sx) ->
  rdn SEGS m (Z_to_bv 64 (sel + 8)) 4 = Some (Z_to_le_bytes 4 cy) -> rdn SEGS m (Z_to_bv 64 (sel + 12)) 4 = Some (Z_to_le_bytes 4 cx) ->
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 data) -> rdn SEGS m (Z_to_bv 64 (sel + 24)) 8 = Some (Z_to_le_bytes 8 name) ->
  RECat m sel (sel_flds sy sx cy cx data name).
Proof.
  intros m sel sy sx cy cx data name H0 H32 Hd Hsy Hsx Hcy Hcx Hdt Hnm R0 R4 R8 R12 R16 R24.
  unfold RECat, sel_flds. cbn [flds_len flds_wf flds_bytes].
  split; [lia|]. split; [lia|]. split.
  - change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z.
    repeat split; lia.
  - rewrite !bytes_at_app, !length_Z_to_le_bytes.
    repeat split;
      match goal with
      | |- bytes_at m _ [] => intros i Hi; cbn [length Z.of_nat] in Hi; lia
      | |- bytes_at m ?a (Z_to_le_bytes ?k ?v) =>
          apply tsw_bytes;
          [ lia | lia
          | intros i Hi; replace (a + i)%Z with (sel + (a - sel + i))%Z by lia; apply Hd; lia
          | match goal with H : rdn SEGS m (Z_to_bv 64 ?b) k = Some (Z_to_le_bytes k v) |- _ => replace a with b by lia; exact H end ]
      end.
Qed.


(* [comment removed for export] *)
Lemma tsw_shape : forall C A A' m' md' (sel arr r0 r1 r2 r3 r4 cy cx : Z),
  Cok C -> W C A' m' md' ->
  live A' (Z_to_bv 64 sel) = Some 32%Z -> live A (Z_to_bv 64 sel) = None -> live (c_A0 C) (Z_to_bv 64 sel) = None -> (0 <= sel < 2 ^ 64)%Z ->
  live A' (Z_to_bv 64 arr) = Some 40%Z -> live A (Z_to_bv 64 arr) = None -> live (c_A0 C) (Z_to_bv 64 arr) = None -> (0 <= arr < 2 ^ 64)%Z ->
  live A' (Z_to_bv 64 r0) = Some 24%Z -> live A (Z_to_bv 64 r0) = None -> live (c_A0 C) (Z_to_bv 64 r0) = None -> (0 <= r0 < 2 ^ 64)%Z ->
  live A' (Z_to_bv 64 r1) = Some 24%Z -> live A (Z_to_bv 64 r1) = None -> live (c_A0 C) (Z_to_bv 64 r1) = None -> (0 <= r1 < 2 ^ 64)%Z ->
  live A' (Z_to_bv 64 r2) = Some 24%Z -> live A (Z_to_bv 64 r2) = None -> live (c_A0 C) (Z_to_bv 64 r2) = None -> (0 <= r2 < 2 ^ 64)%Z ->
  live A' (Z_to_bv 64 r3) = Some 24%Z -> live A (Z_to_bv 64 r3) = None -> live (c_A0 C) (Z_to_bv 64 r3) = None -> (0 <= r3 < 2 ^ 64)%Z ->
  live A' (Z_to_bv 64 r4) = Some 24%Z -> live A (Z_to_bv 64 r4) = None -> live (c_A0 C) (Z_to_bv 64 r4) = None -> (0 <= r4 < 2 ^ 64)%Z ->
  (forall q : word, ~ In q [Z_to_bv 64 r4; Z_to_bv 64 r3; Z_to_bv 64 r2; Z_to_bv 64 r1; Z_to_bv 64 r0; Z_to_bv 64 arr; Z_to_bv 64 sel] -> live A' q = live A q) ->
  Z_to_bv 64 r0 <> Z_to_bv 64 r1 -> Z_to_bv 64 r0 <> Z_to_bv 64 r2 -> Z_to_bv 64 r0 <> Z_to_bv 64 r3 -> Z_to_bv 64 r0 <> Z_to_bv 64 r4 ->
  Z_to_bv 64 r1 <> Z_to_bv 64 r2 -> Z_to_bv 64 r1 <> Z_to_bv 64 r3 -> Z_to_bv 64 r1 <> Z_to_bv 64 r4 ->
  Z_to_bv 64 r2 <> Z_to_bv 64 r3 -> Z_to_bv 64 r2 <> Z_to_bv 64 r4 -> Z_to_bv 64 r3 <> Z_to_bv 64 r4 ->
  (0 <= cy < 5)%Z -> (0 <= cx < 6)%Z ->
  rdn SEGS m' (Z_to_bv 64 (sel + 0)) 4 = Some (Z_to_le_bytes 4 5) -> rdn SEGS m' (Z_to_bv 64 (sel + 4)) 4 = Some (Z_to_le_bytes 4 6) ->
  rdn SEGS m' (Z_to_bv 64 (sel + 8)) 4 = Some (Z_to_le_bytes 4 cy) -> rdn SEGS m' (Z_to_bv 64 (sel + 12)) 4 = Some (Z_to_le_bytes 4 cx) ->
  rdn SEGS m' (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 arr) -> rdn SEGS m' (Z_to_bv 64 (sel + 24)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m' (Z_to_bv 64 (arr + 0)) 8 = Some (Z_to_le_bytes 8 r0) -> rdn SEGS m' (Z_to_bv 64 (arr + 8)) 8 = Some (Z_to_le_bytes 8 r1) ->
  rdn SEGS m' (Z_to_bv 64 (arr + 16)) 8 = Some (Z_to_le_bytes 8 r2) -> rdn SEGS m' (Z_to_bv 64 (arr + 24)) 8 = Some (Z_to_le_bytes 8 r3) ->
  rdn SEGS m' (Z_to_bv 64 (arr + 32)) 8 = Some (Z_to_le_bytes 8 r4) ->
  sel_at (alloc_top (c_vm C)) A' m' sel (SELV 5 6 cy cx arr 0 (tsel_rowp r0 r1 r2 r3 r4)) /\
  sel_off A sel (SELV 5 6 cy cx arr 0 (tsel_rowp r0 r1 r2 r3 r4)) /\ sel_off (c_A0 C) sel (SELV 5 6 cy cx arr 0 (tsel_rowp r0 r1 r2 r3 r4)) /\
  sel_only A A' sel (SELV 5 6 cy cx arr 0 (tsel_rowp r0 r1 r2 r3 r4)).
Proof.
  intros C A A' m' md' sel arr r0 r1 r2 r3 r4 cy cx HC HW Ls Lsa Lsc Rs La Laa Lac Ra
    L0 L0a L0c R0 L1 L1a L1c R1 L2 L2a L2c R2 L3 L3a L3c R3 L4 L4a L4c R4 Hfr
    N01 N02 N03 N04 N12 N13 N14 N23 N24 N34 Hcy Hcx Fsy Fsx Fcy Fcx Fdt Fnm F0 F1 F2 F3 F4.
  destruct (tsw_blk C A' m' md' sel 32 HC HW Ls Rs ltac:(lia)) as (Bs & Ts & Ds).
  destruct (tsw_blk C A' m' md' arr 40 HC HW La Ra ltac:(lia)) as (Ba & Ta & Da).
  destruct (tsw_blk C A' m' md' r0 24 HC HW L0 R0 ltac:(lia)) as (B0 & _ & _).
  destruct (tsw_blk C A' m' md' r1 24 HC HW L1 R1 ltac:(lia)) as (B1 & _ & _).
  destruct (tsw_blk C A' m' md' r2 24 HC HW L2 R2 ltac:(lia)) as (B2 & _ & _).
  destruct (tsw_blk C A' m' md' r3 24 HC HW L3 R3 ltac:(lia)) as (B3 & _ & _).
  destruct (tsw_blk C A' m' md' r4 24 HC HW L4 R4 ltac:(lia)) as (B4 & _ & _).
  assert (P0 : tsel_rowp r0 r1 r2 r3 r4 0 = r0) by reflexivity.
  assert (P1 : tsel_rowp r0 r1 r2 r3 r4 1 = r1) by reflexivity.
  assert (P2 : tsel_rowp r0 r1 r2 r3 r4 2 = r2) by reflexivity.
  assert (P3 : tsel_rowp r0 r1 r2 r3 r4 3 = r3) by reflexivity.
  assert (P4 : tsel_rowp r0 r1 r2 r3 r4 4 = r4) by reflexivity.
  assert (Nas : arr <> sel) by congruence.
  assert (N0a : r0 <> arr) by congruence. assert (N1a : r1 <> arr) by congruence. assert (N2a : r2 <> arr) by congruence.
  assert (N3a : r3 <> arr) by congruence. assert (N4a : r4 <> arr) by congruence.
  assert (N0s : r0 <> sel) by congruence. assert (N1s : r1 <> sel) by congruence. assert (N2s : r2 <> sel) by congruence.
  assert (N3s : r3 <> sel) by congruence. assert (N4s : r4 <> sel) by congruence.
  split; [|split; [|split]].
  - unfold sel_at; cbn [v_sy v_sx v_cy v_cx v_data v_name v_rows].
    split; [lia|]. split; [lia|]. split; [exact Bs|]. split; [exact Ls|].
    split; [apply tsw_rec; try lia; assumption|].
    split; [exact Ba|]. split; [exact La|]. split; [exact Nas|]. split.
    + intros i Hi.
      assert (Ei : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4)%Z) by lia.
      destruct Ei as [->|[->|[->|[->| ->]]]]; rewrite ?P0, ?P1, ?P2, ?P3, ?P4;
        (split; [assumption|]); (split; [assumption|]); (split; [assumption|]); (split; [assumption|]);
        (apply tsw_bytes; [lia | lia | | assumption]);
        intros k Hk;
        match goal with |- m' (Z_to_bv 64 (arr + ?o + ?kk)) <> None =>
          replace (arr + o + kk)%Z with (arr + (o + kk))%Z by lia; apply Da; lia end.
    + intros i j Hi Hj Hij.
      assert (Ei : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4)%Z) by lia.
      assert (Ej : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4)%Z) by lia.
      destruct Ei as [->|[->|[->|[->| ->]]]]; destruct Ej as [->|[->|[->|[->| ->]]]];
        rewrite ?P0, ?P1, ?P2, ?P3, ?P4; congruence.
  - intros p Hp. unfold sel_blk in Hp. cbn [v_data v_sy v_rows] in Hp.
    destruct Hp as [->|[->|(i & Hi & ->)]]; [assumption | assumption |].
    assert (Ei : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4)%Z) by lia.
    destruct Ei as [->|[->|[->|[->| ->]]]]; rewrite ?P0, ?P1, ?P2, ?P3, ?P4; assumption.
  - intros p Hp. unfold sel_blk in Hp. cbn [v_data v_sy v_rows] in Hp.
    destruct Hp as [->|[->|(i & Hi & ->)]]; [assumption | assumption |].
    assert (Ei : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4)%Z) by lia.
    destruct Ei as [->|[->|[->|[->| ->]]]]; rewrite ?P0, ?P1, ?P2, ?P3, ?P4; assumption.
  - intros q Hq. apply Hfr. intros HI. cbn [In] in HI.
    destruct HI as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; subst q.
    + apply (Hq r4); [|reflexivity]. unfold sel_blk. right; right. exists 4%Z. split; [cbn [v_sy]; lia | reflexivity].
    + apply (Hq r3); [|reflexivity]. unfold sel_blk. right; right. exists 3%Z. split; [cbn [v_sy]; lia | reflexivity].
    + apply (Hq r2); [|reflexivity]. unfold sel_blk. right; right. exists 2%Z. split; [cbn [v_sy]; lia | reflexivity].
    + apply (Hq r1); [|reflexivity]. unfold sel_blk. right; right. exists 1%Z. split; [cbn [v_sy]; lia | reflexivity].
    + apply (Hq r0); [|reflexivity]. unfold sel_blk. right; right. exists 0%Z. split; [cbn [v_sy]; lia | reflexivity].
    + apply (Hq arr); [|reflexivity]. unfold sel_blk. right; left. reflexivity.
    + apply (Hq sel); [|reflexivity]. unfold sel_blk. left. reflexivity.
Qed.

Ltac tsw_cells :=
  let i := fresh "i" in let j := fresh "j" in let Hi := fresh "Hi" in let Hj := fresh "Hj" in
  intros i j Hi Hj; cbn [v_sy v_sx] in Hi, Hj;
  assert (Ei : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4)%Z) by lia; assert (Ej : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5)%Z) by lia;
  destruct Ei as [->|[->|[->|[->| ->]]]]; destruct Ej as [->|[->|[->|[->|[->| ->]]]]]; assumption.

(* [comment removed for export] *)
Theorem selCreateFromString_W : forall (K : nat) C A m md regs (s : Z) (ret : word) (S : TSet),
  (1 <= K <= 4)%nat -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELSTR_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 (tsel_text K) -> getr regs 11 = Z_to_bv 64 5 -> getr regs 12 = Z_to_bv 64 6 -> getr regs 13 = Z_to_bv 64 0 ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_selstr <= kR)%Z -> (RB_selstr <= bR)%Z ->
  (forall A' m' vm' regs' (sel : Z) (sv : selv),
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' -> sub_live A A' ->
     getr regs' 10 = Z_to_bv 64 sel ->
     sel_at (alloc_top (c_vm C)) A' m' sel sv ->
     v_sy sv = 5%Z -> v_sx sv = 6%Z -> v_cy sv = tsel_cy K -> v_cx sv = tsel_cx K -> v_name sv = 0%Z ->
     sel_cells m' sv (tsel K) ->
     sel_off A sel sv -> sel_off (c_A0 C) sel sv -> sel_only A A' sel sv ->
     aroom A' vm' (kR - RK_selstr) (bR - RB_selstr) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_selstr) m al_rom) md) S.
Proof.
  intros K C A m md regs s ret S HKr HC HW Hsp Hal Hlo Hhi Hra Hret Htp Ha0 Ha1 Ha2 Ha3 kR bR Hroom HkR HbR HK.
  unfold PC_selstr.
  assert (EK : K = 1%nat \/ K = 2%nat \/ K = 3%nat \/ K = 4%nat) by lia.
  destruct EK as [->|[->|[->| ->]]].
  - apply (selstr_chain1 fx C A m md regs s ret S HC HW Hsp Hal Hlo Hhi Hra Hret Htp Ha0 Ha1 Ha2 Ha3 kR bR Hroom HkR HbR).
    intros A' m' vm' regs' sel arr r0 r1 r2 r3 r4 HW' Hcs Hsub HPM Hroom' Hfr Hr10; intros.
    pose proof (tsw_shape C A A' m' (with_vmmaps vm' md) sel arr r0 r1 r2 r3 r4 1 3) as HSH.
    repeat match type of HSH with ?P -> _ => let Hp := fresh "Hp" in assert (Hp : P) by (first [assumption | lia]); specialize (HSH Hp); clear Hp end.
    destruct HSH as (Hat & Hoff & Hoff0 & Honly).
    apply (HK A' m' vm' regs' sel (SELV 5 6 1 3 arr 0 (tsel_rowp r0 r1 r2 r3 r4))); try assumption; try reflexivity.
    tsw_cells.
  - apply (selstr_chain2 fx C A m md regs s ret S HC HW Hsp Hal Hlo Hhi Hra Hret Htp Ha0 Ha1 Ha2 Ha3 kR bR Hroom HkR HbR).
    intros A' m' vm' regs' sel arr r0 r1 r2 r3 r4 HW' Hcs Hsub HPM Hroom' Hfr Hr10; intros.
    pose proof (tsw_shape C A A' m' (with_vmmaps vm' md) sel arr r0 r1 r2 r3 r4 1 2) as HSH.
    repeat match type of HSH with ?P -> _ => let Hp := fresh "Hp" in assert (Hp : P) by (first [assumption | lia]); specialize (HSH Hp); clear Hp end.
    destruct HSH as (Hat & Hoff & Hoff0 & Honly).
    apply (HK A' m' vm' regs' sel (SELV 5 6 1 2 arr 0 (tsel_rowp r0 r1 r2 r3 r4))); try assumption; try reflexivity.
    tsw_cells.
  - apply (selstr_chain3 fx C A m md regs s ret S HC HW Hsp Hal Hlo Hhi Hra Hret Htp Ha0 Ha1 Ha2 Ha3 kR bR Hroom HkR HbR).
    intros A' m' vm' regs' sel arr r0 r1 r2 r3 r4 HW' Hcs Hsub HPM Hroom' Hfr Hr10; intros.
    pose proof (tsw_shape C A A' m' (with_vmmaps vm' md) sel arr r0 r1 r2 r3 r4 3 3) as HSH.
    repeat match type of HSH with ?P -> _ => let Hp := fresh "Hp" in assert (Hp : P) by (first [assumption | lia]); specialize (HSH Hp); clear Hp end.
    destruct HSH as (Hat & Hoff & Hoff0 & Honly).
    apply (HK A' m' vm' regs' sel (SELV 5 6 3 3 arr 0 (tsel_rowp r0 r1 r2 r3 r4))); try assumption; try reflexivity.
    tsw_cells.
  - apply (selstr_chain4 fx C A m md regs s ret S HC HW Hsp Hal Hlo Hhi Hra Hret Htp Ha0 Ha1 Ha2 Ha3 kR bR Hroom HkR HbR).
    intros A' m' vm' regs' sel arr r0 r1 r2 r3 r4 HW' Hcs Hsub HPM Hroom' Hfr Hr10; intros.
    pose proof (tsw_shape C A A' m' (with_vmmaps vm' md) sel arr r0 r1 r2 r3 r4 3 2) as HSH.
    repeat match type of HSH with ?P -> _ => let Hp := fresh "Hp" in assert (Hp : P) by (first [assumption | lia]); specialize (HSH Hp); clear Hp end.
    destruct HSH as (Hat & Hoff & Hoff0 & Honly).
    apply (HK A' m' vm' regs' sel (SELV 5 6 3 2 arr 0 (tsel_rowp r0 r1 r2 r3 r4))); try assumption; try reflexivity.
    tsw_cells.
Qed.

End TextSel.
