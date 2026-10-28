(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import F_malloc_free F_malloc_enframe MallocBlocks MallocHINV MallocFacts_B MallocFacts_A.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog MAlign.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_A MallocKit_B MallocKit_B2 MallocModel_B MallocKit_B3 MallocFacts_Bpres F_mm_syscalls F_ntf F_free_C F_free_K F_free.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocFacts_inv MallocFacts_inv2 MallocFacts_inv3.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMallocKit_A RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_get_meta RF_mm_syscalls RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RF_free_A RF_free_B RF_free_C RF_ntf RF_free_K RF_free RF_realloc_A RF_realloc_B RF_aligned_B RF_aligned_H.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import MI_Kit MI_Inv MI_Arith MI_Read MI_Pres2 MI_WFree MI_Geom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition wframe (W : list ivl) (lo len : Z) (m0 m : mem) : Prop :=
  munch W m0 m /\ wmono ctusegs m0 m /\ mem_inv ctusegs m /\ wr_at ctusegs m lo len.

Lemma wframe_write W lo len m0 m a bs :
  wframe W lo len m0 m -> lo <= a -> a + Z.of_nat (length bs) <= lo + len -> inside W a (Z.of_nat (length bs)) ->
  wframe W lo len m0 (write_to_mem m (wa a) bs).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros (MU & WM & MI & WR) Ha Hb Hin. pose proof WR as (L0 & L1 & _).
  split; [apply munch_write; [exact MU| lia| lia| exact Hin]|].
  split; [apply wmono_write; exact WM|].
  split.
  - apply mem_inv_store; [exact MI|]. replace (wa a) with (wa (lo + (a - lo))) by (f_equal; lia).
    apply (wr_at_store_ok ctusegs m lo len (a - lo) (length bs) WR); lia.
  - eapply wr_at_transport; [exact WR|]. apply wmono_write. apply wmono_refl.
Qed.

(* [comment removed for export] *)
Definition raligned_W (S P' n E : Z) : list ivl := [(S - 3, S); (P' - 4, P'); (P' + n, E)].

Lemma wframe_rss m0 m S P E n b3 :
  wframe (raligned_W S P n E) (S - 3) (E - S + 3) m0 m -> S <= P -> P + n <= E -> 0 <= n ->
  wframe (raligned_W S P n E) (S - 3) (E - S + 3) m0 (rss_mem m P E n b3).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros F SP PN N0. unfold rss_mem. set (r := E - P - n).
  assert (F1 : wframe (raligned_W S P n E) (S - 3) (E - S + 3) m0 (if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0])).
  { destruct (Z.eqb_spec r 0); [exact F|]. apply wframe_write; [exact F| lia| cbn [length]; lia| cbn [length]; unfold raligned_W, inside; right; right; left; lia]. }
  assert (F2 : forall mx v, wframe (raligned_W S P n E) (S - 3) (E - S + 3) m0 mx ->
               wframe (raligned_W S P n E) (S - 3) (E - S + 3) m0 (write_to_mem mx (wa (P - 3)) [b8 v])).
  { intros mx v Fx. apply wframe_write; [exact Fx| lia| cbn [length]; lia| cbn [length]; unfold raligned_W, inside; right; left; lia]. }
  destruct (5 <=? r) eqn:R5; cbv beta iota zeta.
  - apply Z.leb_le in R5. apply F2.
    apply wframe_write; [| lia| rewrite length_le4; lia| rewrite length_le4; unfold raligned_W, inside; right; right; left; lia].
    apply wframe_write; [exact F1| lia| cbn [length]; lia| cbn [length]; unfold raligned_W, inside; right; right; left; lia].
  - apply F2. exact F1.
Qed.

Lemma wframe_raligned_mem m S P E n idx b3 adj q' :
  mem_inv ctusegs m -> wr_at ctusegs m (S - 3) (E - S + 3) ->
  S <= P -> 0 <= adj -> (adj = 0 \/ 16 <= adj) -> P + adj + n <= E -> 0 <= n ->
  wframe (raligned_W S (P + adj) n E) (S - 3) (E - S + 3) m (raligned_mem m P S E n idx b3 adj q').
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros MI WR SP A0 A16 PE N0.
  assert (F0 : wframe (raligned_W S (P + adj) n E) (S - 3) (E - S + 3) m m).
  { split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI| exact WR]. }
  unfold raligned_mem. destruct (Z.eqb_spec adj 0) as [E0|NE].
  - rewrite E0, Z.add_0_r in *. apply wframe_rss; [exact F0| lia| lia| lia].
  - apply wframe_write; [| lia| rewrite length_le2; lia| rewrite length_le2; unfold raligned_W, inside; left; lia].
    apply wframe_write; [| lia| cbn [length]; lia| cbn [length]; unfold raligned_W, inside; left; lia].
    apply wframe_rss; [| lia| lia| lia].
    apply wframe_write; [| lia| rewrite length_le2; lia| rewrite length_le2; unfold raligned_W, inside; right; left; lia].
    apply wframe_write; [| lia| cbn [length]; lia| cbn [length]; unfold raligned_W, inside; right; left; lia].
    apply wframe_write; [exact F0| lia| cbn [length]; lia| cbn [length]; unfold raligned_W, inside; right; left; lia].
Qed.

(* [comment removed for export] *)
Definition zopaque (x : Z) : Z := x.
Definition zopaqueP (P : Prop) : Prop := P.

Lemma adj_facts (P al : Z) : 0 <= P -> P mod 16 = 0 -> (al = 32 \/ al = 64) ->
  let adj := (- P) mod al in 0 <= adj <= al - 16 /\ adj mod 16 = 0 /\ (P + adj) mod al = 0 /\ (adj = 0 \/ 16 <= adj).
Proof.
  intros P0 P16 HAL. cbv zeta. assert (AL0 : 0 < al) by lia. pose proof (Z.mod_pos_bound (- P) al AL0) as MB.
  assert (M16 : ((- P) mod al) mod 16 = 0).
  { destruct HAL as [-> | ->].
    - rewrite <- (Znumtheory.Zmod_div_mod 16 32 (- P)); [| lia| lia| exists 2; reflexivity].
      replace (- P) with ((- (P / 16)) * 16) by (pose proof (Z.div_mod P 16 ltac:(lia)); lia). rewrite Z_mod_mult. reflexivity.
    - rewrite <- (Znumtheory.Zmod_div_mod 16 64 (- P)); [| lia| lia| exists 4; reflexivity].
      replace (- P) with ((- (P / 16)) * 16) by (pose proof (Z.div_mod P 16 ltac:(lia)); lia). rewrite Z_mod_mult. reflexivity. }
  pose proof (Z.div_mod ((- P) mod al) 16 ltac:(lia)) as D1. pose proof (Z.div_mod al 16 ltac:(lia)) as D2.
  split; [destruct HAL as [-> | ->]; lia|]. split; [exact M16|]. split; [| lia].
  rewrite Zplus_mod_idemp_r. replace (P + - P) with 0 by lia. apply Z.mod_0_l. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rss_rep : forall st m (p e : aptr) r (n b3 : Z),
  rmrep st m -> ticks_ok st -> fst e = fst p ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
  4 <= snd p -> snd p + n <= snd e -> snd e + 4 <= round_up_pg (r_len r) -> 0 <= n -> snd e - snd p - n < 2^32 -> 0 <= b3 ->
  (forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> snd b + 9 <= snd p - 3 \/ snd e <= snd b) ->
  rmrep (set_size_m p e n b3 st) (rss_mem m (r_base r + snd p) (r_base r + snd e) n b3) /\ ticks_ok (set_size_m p e n b3 st).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m p e r n b3 MR TK Efst Hr Hk P4 PN EHI N0 R32 B3 NOGRP.
  unfold set_size_m, rss_mem.
  replace (r_base r + snd e - (r_base r + snd p) - n) with (snd e - snd p - n) by lia.
  set (res := snd e - snd p - n).
  assert (RES0 : 0 <= res) by (subst res; lia).
  (* [comment removed for export] *)
  set (st1 := if negb (res =? 0) then wr8 (aadd e (- res)) 0 st else st).
  set (m1 := if res =? 0 then m else write_to_mem m (wa (r_base r + snd e - res)) [b8 0]).
  assert (ST1 : rmrep st1 m1 /\ ticks_ok st1 /\ s_regions st1 = s_regions st /\ s_groups st1 = s_groups st).
  { subst st1 m1. destruct (Z.eqb_spec res 0) as [E0|NE0]; cbn [negb].
    - split; [exact MR|]. split; [exact TK|]. split; reflexivity.
    - split; [| split; [apply ticks_ok_wr8; exact TK| split; reflexivity]].
      replace (r_base r + snd e - res) with (r_base r + snd (aadd e (- res))) by (cbn [aadd snd]; lia).
      apply (rmrep_wr8 st m (aadd e (- res)) 0 r MR TK); cbn [aadd fst snd]; [rewrite Efst; exact Hr| exact Hk| lia| | lia].
      intros b gh Hb Hf. rewrite Efst in Hf. destruct (NOGRP b gh Hb Hf); lia. }
  clearbody st1 m1. destruct ST1 as (MR1 & TK1 & ER1 & EG1).
  (* [comment removed for export] *)
  set (st2r := if 5 <=? res then (wr32 (aadd e (-4)) res (wr8 (aadd e (-5)) 0 st1), 5) else (st1, res)).
  set (m2r := if 5 <=? res then (write_to_mem (write_to_mem m1 (wa (r_base r + snd e - 5)) [b8 0]) (wa (r_base r + snd e - 4)) (le4 (wz res)), 5) else (m1, res)).
  assert (ST2 : rmrep (fst st2r) (fst m2r) /\ ticks_ok (fst st2r) /\ s_regions (fst st2r) = s_regions st /\ s_groups (fst st2r) = s_groups st
                /\ snd st2r = snd m2r /\ 0 <= snd m2r <= 5).
  { subst st2r m2r. destruct (Z.leb_spec 5 res) as [R5|R5]; cbn [fst snd].
    - assert (MA : rmrep (wr8 (aadd e (-5)) 0 st1) (write_to_mem m1 (wa (r_base r + snd e - 5)) [b8 0]) /\ ticks_ok (wr8 (aadd e (-5)) 0 st1)).
      { split; [| apply ticks_ok_wr8; exact TK1].
        replace (r_base r + snd e - 5) with (r_base r + snd (aadd e (-5))) by (cbn [aadd snd]; lia).
        apply (rmrep_wr8 st1 m1 (aadd e (-5)) 0 r MR1 TK1); cbn [aadd fst snd]; [rewrite ER1, Efst; exact Hr| exact Hk| lia| | lia].
        intros b gh Hb Hf. rewrite EG1 in Hb. rewrite Efst in Hf. destruct (NOGRP b gh Hb Hf); lia. }
      destruct MA as [MRa TKa].
      pose proof (rmrep_wr32 (wr8 (aadd e (-5)) 0 st1) _ (aadd e (-4)) res r MRa TKa) as X. cbn [aadd fst snd] in X.
      replace (r_base r + (snd e + -4)) with (r_base r + snd e - 4) in X by lia.
      destruct (X ltac:(rewrite Efst; cbn; rewrite ER1; exact Hr) Hk ltac:(lia) ltac:(lia)
                  ltac:(intros b gh Hb Hf; cbn in Hb; rewrite EG1 in Hb; rewrite Efst in Hf; destruct (NOGRP b gh Hb Hf); lia) ltac:(lia)) as [MRb TKb].
      split; [exact MRb|]. split; [exact TKb|]. split; [cbn; exact ER1|]. split; [cbn; exact EG1|]. split; [reflexivity| lia].
    - split; [exact MR1|]. split; [exact TK1|]. split; [exact ER1|]. split; [exact EG1|]. split; [reflexivity| lia]. }
  clearbody st2r m2r. destruct st2r as [st2 r2]. destruct m2r as [m2 r2']. cbn [fst snd] in ST2.
  destruct ST2 as (MR2 & TK2 & ER2 & EG2 & <- & R5).
  (* [comment removed for export] *)
  assert (VB : 0 <= Z.land b3 31 + Z.shiftl r2 5 < 256).
  { rewrite Z.shiftl_mul_pow2 by lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5) ltac:(lia)). cbn in *. lia. }
  split; [| apply ticks_ok_wr8; exact TK2].
  replace (r_base r + snd p - 3) with (r_base r + snd (aadd p (-3))) by (cbn [aadd snd]; lia).
  apply (rmrep_wr8 st2 m2 (aadd p (-3)) _ r MR2 TK2); cbn [aadd fst snd]; [rewrite ER2; exact Hr| exact Hk| lia| | exact VB].
  intros b gh Hb Hf. rewrite EG2 in Hb. destruct (NOGRP b gh Hb Hf); lia.
Qed.

Ltac eq_crunch :=
  first [ reflexivity
        | lazymatch goal with
          | |- wa _ = wa _ => f_equal; lia
          | |- Z.div _ _ = Z.div _ _ => first [f_equal; lia | lia]
          | |- @eq Z _ _ => lia
          | |- @eq N _ _ => first [reflexivity | lia]
          | |- _ => progress f_equal; eq_crunch
          end ].

(* [comment removed for export] *)
Lemma realign_rep : forall st m (g bm : aptr) r (i n off adj b3 : Z),
  let stride := get_stride (get_meta_rec st g) in
  let sS := snd bm + 16 + stride * i in let po := sS + 16 * off in let e := sS + stride - 4 in let pa := po + adj in
  rmrep st m -> ticks_ok st -> m_mem (get_meta_rec st g) = Some bm ->
  (s_regions st) !! (fst bm) = Some r -> r_kind r = RKGroup ->
  0 <= snd bm -> 16 <= stride -> 0 <= stride * i -> 0 <= i < 32 -> e + 4 <= round_up_pg (r_len r) ->
  0 <= off -> 0 <= adj -> (adj = 0 \/ 16 <= adj) -> 0 <= n -> 16 * off + adj + n <= stride - 4 -> stride - 4 - 16 * off - adj - n < 2^32 ->
  (i = 0 \/ stride * (i + 1) < 2^20) -> 16 * off + adj <= 16 * 258 -> 0 <= b3 -> Z.land b3 31 = i ->
  (forall b gh, (s_groups st) !! b = Some gh -> fst b = fst bm -> snd b + 9 <= sS - 4 \/ e <= snd b) ->
  rmrep (fst (realign_at st g i n off adj))
        (raligned_mem m (r_base r + po) (r_base r + sS) (r_base r + e) n i b3 adj ((r_base r + po + adj - (r_base r + snd bm + 16)) / 16))
  /\ ticks_ok (fst (realign_at st g i n off adj)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until b3. intros stride sS po e pa MR TK Hmem Hr Hk B0 S16 SI0 I32 SPAN OFF0 A0 A16 N0 FIT R32 Q20 O258 B3 B31 NOGRP.
  subst pa e po sS.
  assert (K31 : Z.land i 31 = i) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  set (sS := snd bm + 16 + stride * i) in *. set (po := sS + 16 * off) in *. set (e := sS + stride - 4) in *. set (pa := po + adj).
  (* [comment removed for export] *)
  assert (EQ : fst (realign_at st g i n off adj) =
     if adj =? 0 then set_size_m (fst bm, po) (fst bm, e) n i st
     else wr16 (fst bm, sS - 2) ((pa - sS) / 16) (wr8 (fst bm, sS - 3) 224 (set_size_m (fst bm, pa) (fst bm, e) n i
            (wr16 (fst bm, pa - 2) ((pa - (snd bm + 16)) / 16) (wr8 (fst bm, pa - 3) i (wr8 (fst bm, pa - 4) 0 st)))))).
  { unfold realign_at. fold stride. rewrite Hmem. cbn [default from_option id]. unfold aadd. cbn [fst snd].
    subst pa e po sS. unfold UNIT, IB. destruct (adj =? 0); cbn [fst]; eq_crunch. }
  rewrite EQ. clear EQ. unfold raligned_mem.
  destruct (Z.eqb_spec adj 0) as [AZ|ANZ].
  - (* [comment removed for export] *)
    replace (set_size_m (fst bm, po) (fst bm, e) n i st) with (set_size_m (fst bm, po) (fst bm, e) n b3 st)
      by (unfold set_size_m; rewrite B31, K31; reflexivity).
    pose proof (rss_rep st m (fst bm, po) (fst bm, e) r n b3 MR TK eq_refl Hr Hk) as X. cbn [fst snd] in X.
    destruct (X ltac:(subst po sS; lia) ltac:(subst e po sS; lia) ltac:(lia) N0 ltac:(subst e po sS; lia) B3
                ltac:(intros b gh Hb Hf; destruct (NOGRP b gh Hb Hf); subst po sS; lia)) as [X1 X2].
    split; [exact X1| exact X2].
  - (* [comment removed for export] *)
    assert (A16' : 16 <= adj) by lia.
    assert (Q' : 0 <= (pa - (snd bm + 16)) / 16 < 65536).
    { subst pa po sS. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. destruct Q20 as [-> | Q]; lia. }
    assert (Q2 : 0 <= (pa - sS) / 16 < 65536).
    { subst pa po sS. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. lia. }
    (* [comment removed for export] *)
    pose proof (rmrep_wr8 st m (fst bm, pa - 4) 0 r MR TK Hr Hk ltac:(cbn [snd]; subst pa po sS e; lia)
                  ltac:(intros b gh Hb Hf; cbn [fst snd] in Hf |- *; destruct (NOGRP b gh Hb Hf); subst pa po sS e; lia) ltac:(lia)) as M1.
    cbn [snd] in M1. pose proof (ticks_ok_wr8 st (fst bm, pa - 4) 0 TK) as T1.
    set (st1 := wr8 (fst bm, pa - 4) 0 st) in *.
    (* [comment removed for export] *)
    pose proof (rmrep_wr8 st1 _ (fst bm, pa - 3) i r M1 T1 Hr Hk ltac:(cbn [snd]; subst pa po sS e; lia)
                  ltac:(intros b gh Hb Hf; cbn [fst snd] in Hf |- *; destruct (NOGRP b gh Hb Hf); subst pa po sS e; lia) ltac:(lia)) as M2.
    cbn [snd] in M2. pose proof (ticks_ok_wr8 st1 (fst bm, pa - 3) i T1) as T2.
    set (st2 := wr8 (fst bm, pa - 3) i st1) in *.
    (* [comment removed for export] *)
    pose proof (rmrep_wr16 st2 _ (fst bm, pa - 2) ((pa - (snd bm + 16)) / 16) r M2 T2 Hr Hk ltac:(cbn [snd]; subst pa po sS e; lia) ltac:(cbn [snd]; subst pa po sS e; lia)
                  ltac:(intros b gh Hb Hf; cbn [fst snd] in Hf |- *; destruct (NOGRP b gh Hb Hf); subst pa po sS e; lia) Q') as M3.
    cbn [snd] in M3. pose proof (ticks_ok_wr16 st2 (fst bm, pa - 2) ((pa - (snd bm + 16)) / 16) T2) as T3.
    set (st3 := wr16 (fst bm, pa - 2) ((pa - (snd bm + 16)) / 16) st2) in *.
    (* [comment removed for export] *)
    pose proof (rss_rep st3 _ (fst bm, pa) (fst bm, e) r n i M3 T3 eq_refl Hr Hk) as X. cbn [fst snd] in X.
    destruct (X ltac:(subst pa po sS; lia) ltac:(subst e pa po sS; lia) ltac:(lia) N0 ltac:(subst e pa po sS; lia) ltac:(lia)
                ltac:(intros b gh Hb Hf; destruct (NOGRP b gh Hb Hf); subst pa po sS; lia)) as [M4 T4]. clear X.
    set (st4 := set_size_m (fst bm, pa) (fst bm, e) n i st3) in *.
    assert (ER4 : s_regions st4 = s_regions st /\ s_groups st4 = s_groups st).
    { subst st4. unfold set_size_m. destruct (5 <=? _); destruct (negb _); split; reflexivity. }
    destruct ER4 as [ER4 EG4].
    (* [comment removed for export] *)
    pose proof (rmrep_wr8 st4 _ (fst bm, sS - 3) 224 r M4 T4 ltac:(cbn [fst]; rewrite ER4; exact Hr) Hk ltac:(cbn [snd]; subst po sS e; lia)
                  ltac:(intros b gh Hb Hf; cbn [fst snd] in Hf |- *; rewrite EG4 in Hb; destruct (NOGRP b gh Hb Hf); subst po sS e; lia) ltac:(lia)) as M5.
    cbn [snd] in M5. pose proof (ticks_ok_wr8 st4 (fst bm, sS - 3) 224 T4) as T5.
    set (st5 := wr8 (fst bm, sS - 3) 224 st4) in *.
    (* [comment removed for export] *)
    pose proof (rmrep_wr16 st5 _ (fst bm, sS - 2) ((pa - sS) / 16) r M5 T5 ltac:(change (s_regions st4 !! fst bm = Some r); rewrite ER4; exact Hr) Hk
                  ltac:(cbn [snd]; subst po sS e; lia) ltac:(cbn [snd]; subst po sS e; lia)
                  ltac:(intros b gh Hb Hf; cbn [fst snd] in Hf |- *; change (s_groups st4 !! b = Some gh) in Hb; rewrite EG4 in Hb; destruct (NOGRP b gh Hb Hf); subst po sS e; lia) Q2) as M6.
    cbn [snd] in M6. pose proof (ticks_ok_wr16 st5 (fst bm, sS - 2) ((pa - sS) / 16) T5) as T6.
    split; [| exact T6].
    match goal with |- rmrep _ ?mx => match type of M6 with rmrep _ ?my => replace mx with my; [exact M6|] end end.
    subst pa. eq_crunch.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma raligned_hdr_walk_eq : forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 s0v s1v : word) F fc (m : word -> option byte) (P Bb G A n al mp b3 q : Z) (avail freed last_idx freeable sc maplen secret : Z) (prev next : word) (junk : list byte)
    (idx stride S E : Z),
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let adj := (- P) mod al in let P' := P + adj in
  idx = Z.land b3 31 ->
  stride = (if (last_idx =? 0) && negb (maplen =? 0) then 4096 * maplen - 16 else 16 * size_class sc) ->
  S = Bb + 16 + stride * idx -> E = Bb + 16 + stride * (idx + 1) - 4 ->
  P mod 16 = 0 -> 16 * q + 16 <= P -> P + 16 <= 2^64 -> Bb = P - 16 * q - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  ov_read_bytes ctusegs m (wa (P - 4)) 1 = Some [b8 0] ->
  ov_read_bytes ctusegs m (wa (P - 3)) 1 = Some [b8 b3] ->
  ov_read_bytes ctusegs m (wa (P - 2)) 2 = Some (le2 (wz q)) ->
  ov_read_bytes ctusegs m (wa Bb) 8 = Some (le8 (wz G)) ->
  rw_cells ctusegs m G [C8 prev; C8 next; C8 (wz Bb); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes ctusegs m (wa A) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes ctusegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  (sc < 48 -> ov_read_bytes ctusegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= q < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= q < size_class sc * (idx + 1)) -> (48 <= sc -> sc = 63) ->
  (maplen <> 0 -> q <= maplen * 256 - 1) -> (maplen = 0 \/ last_idx <> 0 -> sc < 48) -> 0 < P ->
  rw_cells ctusegs m (bv_unsigned sp) [CB 8 junk; C8 s1v; C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 0x2b4c40); C8 s0v; C8 ra0] ->
  wr_at ctusegs m mp 8 -> 0 <= mp -> mp + 8 <= 2^64 -> bv_unsigned sp + 48 <= mp \/ mp + 8 <= bv_unsigned sp ->
  mem_inv ctusegs m -> bv_unsigned sp + 48 <= 2^64 ->
  wr_at ctusegs m (S - 3) (E - S + 3) -> bytes_at ctusegs m (P - 3) [b8 b3] ->
  0 <= Bb -> Bb mod 16 = 0 -> 16 <= stride -> stride mod 16 = 0 -> E + 5 <= 2^63 ->
  S <= P -> P - S <= 16 * 255 -> 0 <= n -> (al = 32 \/ al = 64) -> P + n + al - 16 <= E ->
  E - P - n + al < 2^31 -> (idx = 0 \/ stride * (idx + 1) < 2^20) ->
  (E <= bv_unsigned sp \/ bv_unsigned sp + 48 <= S - 3) -> (E <= mp \/ mp + 8 <= S - 3) ->
  evt ctusegs (raligned_ret_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc
               (raligned_mem m P S E n idx b3 adj ((P' - (Bb + 16)) / 16)) P' mp)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 al) (Z_to_bv 64 n) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b4d18) fc None m (seg_rom ctusegs)).
Proof.
  intros until E. intros mword adj P' -> -> -> ->. intros.
  eapply raligned_hdr_walk with (G:=G) (A:=A) (avail:=avail) (freed:=freed) (freeable:=freeable) (secret:=secret) (prev:=prev) (next:=next); eassumption.
Qed.

(* [comment removed for export] *)
Definition raligned_tail_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (st : mstate) (LB : list block) (blk : block) (off n al mp : Z) : machine_state -> Prop :=
  fun ms' => exists (g : aptr) (i adj : Z) (r : region) (mR : mem) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    let A' := blk_addr blk + adj in
    let stride := get_stride (get_meta_rec st g) in
    let S := blk_addr blk - UNIT * off in let E := S + stride - IB in
    ms' = MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 0) (Z_to_bv 64 A') a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None (write_to_mem mR (wa mp) (le8 (Z_to_bv 64 A'))) (seg_rom ctusegs)
    /\ s_slots st !! (blk_slot blk) = Some (g, i)
    /\ (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
    /\ (i = 0 \/ stride * (i + 1) < 2^20) /\ stride - UNIT * off - n < 2^32
    /\ 0 <= adj /\ adj mod UNIT = 0 /\ adj + n <= blk_size blk /\ off + adj / UNIT <= 258 /\ A' mod al = 0
    /\ rmrep (fst (realign_at st g i n off adj)) mR /\ ticks_ok (fst (realign_at st g i n off adj))
    /\ wframe (raligned_W S A' n E) (S - 3) (E - S + 3) m mR
    /\ r_base r + 16 <= S /\ E + 4 <= r_base r + round_up_pg (r_len r) /\ blk_addr blk + blk_size blk <= E /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
    /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x355000 <= r_base r)
    /\ (forall b, In b LB -> blk_slot b <> blk_slot blk -> blk_addr b + blk_size b <= S - 4 \/ E <= blk_addr b).

Lemma raligned_tail_spec : forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (ra0 s0v s1v : word) F fc m
    (st : mstate) (LB : list block) (blk : block) (off n al mp : Z) L BL LS (junk : list byte),
  CINV st LB -> In blk LB -> 0 <= off <= 255 -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  INVL x0 st L BL LS -> CORR st LB BL ->
  rmrep st m -> ticks_ok st -> mem_inv ctusegs m -> c_init_done (ctx st) <> 0 ->
  blk_size blk = n + al - 16 -> 0 <= n -> (al = 32 \/ al = 64) -> n + al - 16 < 2^32 ->
  (forall g i, s_slots st !! (blk_slot blk) = Some (g, i) -> get_stride (get_meta_rec st g) - IB - blk_size blk < 2^30) ->
  rw_cells ctusegs m (bv_unsigned sp) [CB 8 junk; C8 s1v; C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 0x2b4c40); C8 s0v; C8 ra0] ->
  wr_at ctusegs m mp 8 -> alloc_ceiling <= bv_unsigned sp -> bv_unsigned sp + 48 <= mp -> mp + 8 <= 2^64 ->
  evt ctusegs (raligned_tail_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc m st LB blk off n al mp)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 al) (Z_to_bv 64 n) (Z_to_bv 64 (blk_addr blk)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b4d18) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros C Hin OFF HA INV CR HMR TK MI INI HSZ N0 HAL NR S30 FR WMP CSP SPMP MP8.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  (* [comment removed for export] *)
  destruct (MallocFacts_inv.Forall2_In_l _ _ _ _ CR Hin) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[ck bo] nk]. cbn [bslot boff bsize fst snd] in C1, C2, C3.
  assert (bo = off) as -> by (rewrite HA, <- C1 in C3; unfold UNIT in C3; lia).
  subst ck nk.
  (* [comment removed for export] *)
  pose proof (KINV_of_CINV _ _ C) as K0.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as BK.
  destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
  assert (off' = off) as -> by (rewrite HA in OA; unfold UNIT in OA; lia).
  clear OA. specialize (S30 g i SL).
  set (c0 := blk_slot blk) in *. set (n0 := blk_size blk) in *.
  pose proof (ci_gmetas _ _ C b g HB) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
  pose proof HMR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
  destruct (block_facts x0 st L BL LS INV c0 off n0 Hk) as (g' & bm & i' & ai & a & ar & ka & BF).
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as SL'. rewrite SL in SL'. inversion SL'. subst g' i'. clear SL'.
  pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as Hmem'. unfold MI_Inv.MR in Hmem'. rewrite (go_mem _ _ _ GO) in Hmem'. inversion Hmem'. subst bm. clear Hmem'.
  set (mr := get_meta_rec st g) in *.
  set (stride := get_stride mr) in *.
  pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI. fold mr in S16, SM, LI. fold stride in S16, SM.
  destruct (ki_slts _ _ _ K0 _ _ _ SL) as (GMg & Ec & _). fold c0 in Ec.
  assert (Hr0 : s_regions st !! fst c0 = Some r) by (rewrite <- FB; exact Hr).
  assert (Cc : conc st c0 = r_base r + snd c0) by (apply conc_region'; exact Hr0).
  assert (Cb : conc st b = r_base r + snd b) by (apply conc_region'; exact Hr).
  assert (Sc : snd c0 = snd b + 16 + stride * i).
  { rewrite Ec. rewrite (slot_start'_mem _ b i (go_mem _ _ _ GO)). cbn. unfold UNIT. subst stride mr. lia. }
  assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SIL : stride * (i + 1) <= stride * (m_last_idx mr + 1)).
  { apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
  unfold MallocFacts_B.sstart_of, sstart_of in SPAN. fold mr in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN. fold stride in SPAN.
  (* [comment removed for export] *)
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SHB. unfold blk_shadow_ok in SHB. cbn [bslot boff bsize fst snd] in SHB.
  rewrite (gbase_bm st c0 off n0 g b i ai a ar ka BF) in SHB.
  unfold MI_Inv.MR in SHB. fold mr in SHB. fold stride in SHB.
  destruct SHB as (K4 & K3 & K2 & K1 & Q & K5 & Kr0 & KU).
  pose proof (q16 st c0 off n0 g b i ai a ar ka BF) as [Q16 _]. unfold MI_Inv.MR in Q16. fold mr in Q16. fold stride in Q16.
  pose proof (bf_hdr0 _ _ _ _ _ _ _ _ _ _ _ BF) as H0. unfold MI_Inv.MR in H0. fold mr in H0.
  pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. unfold MI_Inv.MR in FIT. fold mr in FIT. fold stride in FIT.
  unfold known, SHd in K4, K3, K2, K1, K5, Kr0, H0. cbn [fst snd] in K4, K3, K2, K1, K5, Kr0, H0.
  set (po := snd c0 + UNIT * off) in *.
  set (e := snd c0 + stride - IB) in *.
  set (res := e - po - n0) in *.
  set (q := (po - snd b - UNIT) / UNIT) in *.
  assert (RES0 : 0 <= res) by (subst res e po; unfold UNIT, IB in *; lia).
  cbn [aadd snd] in Q16. fold po in Q16. fold q in Q16.
  destruct (SH (fst c0) r Hr0 Kr) as [HWr HBy].
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL.
  unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in RBC.
  assert (PO16 : 16 <= po) by (subst po; unfold UNIT in *; lia).
  assert (EHIr : e + 4 <= round_up_pg (r_len r)) by (subst e; unfold UNIT, IB in *; lia).
  assert (POE : po + n0 + res = e) by (subst res; lia).
  (* [comment removed for export] *)
  set (b3 := i + 32 * Z.min res 5) in *.
  assert (IDXe : Z.land b3 31 = i) by (apply land31_idx; lia).
  set (P := r_base r + po).
  assert (PEQ : P = blk_addr blk) by (rewrite HA, Cc; unfold P, po; lia).
  (* [comment removed for export] *)
  destruct (rmrep_shadow_read st m (fst c0) r (po - 4) 0 HMR Hr0 Kr ltac:(lia) K4) as [R4 _].
  destruct (rmrep_shadow_read st m (fst c0) r (po - 3) b3 HMR Hr0 Kr ltac:(lia) K3) as [R3 B3R].
  destruct (rmrep_shadow_read2 st m (fst c0) r (po - 2) (byte_of q 0) (byte_of q 1) HMR Hr0 Kr ltac:(lia) ltac:(lia) K2
              ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact K1)) as (R2 & LO & HI).
  rewrite <- le2_lohi in R2 by lia. rewrite (u16_bytes q Q) in R2.
  (* [comment removed for export] *)
  destruct HB as [ai0 Hgh].
  destruct (rmrep_group_read st m b _ HMR Hgh) as [RG _]. cbn [g_meta pw oconc] in RG.
  pose proof (rmrep_meta_chunk st m g HMR (go_slot _ _ _ GO)) as MM. fold mr in MM. unfold meta_cells in MM.
  rewrite (go_mem _ _ _ GO) in MM. cbn [pw oconc] in MM. unfold meta_word in MM.
  (* [comment removed for export] *)
  destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Har & Hchk & Hal & Hka & Em).
  pose proof (rmrep_area_check_read st m a ar HMR Har) as RA. rewrite Hchk in RA.
  pose proof (rmrep_ctx_secret_read st m HMR) as RC. rewrite (rsec_init _ _ INI) in RC.
  change (s_ctx st) with (ctx st) in RA.
  rewrite <- (wz_mod64 (c_secret (ctx st) + bv_unsigned rr_secret)) in RA, RC.
  destruct (WA a ar Har) as (rg & Hrg & A00 & A01 & AAL & ANG & _).
  destruct (WR (fst a) rg Hrg) as (RB0g & RBALg & RL0g & RBCg & _).
  unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in RBCg.
  assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * ka)).
  { rewrite Em. unfold mslot. rewrite conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  assert (Hm : (r_base rg + snd a + (AREA_HDR + META_SIZE * ka)) mod 4096 = AREA_HDR + META_SIZE * ka).
  { apply area_slot_mod; [exact RBALg| exact AAL| exact Hka]. }
  assert (HAa : conc st a = conc st g - conc st g mod 4096).
  { rewrite HG, Hm. rewrite (conc_region' st a rg Hrg). lia. }
  pose proof (round_up_pg_ge (r_len rg)) as RUG.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  destruct BC as [(r0 & Hr0' & _ & A16 & AEND & AL & UNK) _ _].
  fold c0 in Hr0'. rewrite Hr0 in Hr0'. inversion Hr0'. subst r0. clear Hr0' UNK.
  set (E := r_base r + e).
  set (Sa := r_base r + snd c0).
  assert (STRW : stride = (if (m_last_idx mr =? 0) && negb (m_maplen mr =? 0) then 4096 * m_maplen mr - 16 else 16 * size_class (m_sizeclass mr))).
  { unfold stride, get_stride. destruct ((m_last_idx mr =? 0) && negb (m_maplen mr =? 0)); unfold UNIT; lia. }
  pose proof (go_sc _ _ _ GO) as GSC. fold mr in GSC.
  pose proof (go_maplen _ _ _ GO) as GML. fold mr in GML.
  pose proof (go_avail _ _ _ GO) as GAV. pose proof (go_freed _ _ _ GO) as GFR. fold mr in GAV, GFR.
  pose proof (go_freeable _ _ _ GO) as GFB. fold mr in GFB.
  assert (NA : Z.testbit (m_avail mr) i = false) by (destruct (Z.testbit (m_avail mr) i) eqn:E1; [exfalso; apply NFR; right; exact E1| reflexivity]).
  assert (NF : Z.testbit (m_freed mr) i = false) by (destruct (Z.testbit (m_freed mr) i) eqn:E1; [exfalso; apply NFR; left; exact E1| reflexivity]).
  (* [comment removed for export] *)
  pose proof (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF) as NH. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as EC0. unfold MI_Inv.MR in EC0. fold mr in EC0.
  assert (HSTi : sstart mr i = snd c0) by (rewrite EC0; reflexivity).
  pose proof (sstart_succ st g i) as SS. unfold MI_Inv.MR in SS. fold mr in SS. fold stride in SS.
  assert (Hhosts : MI_Inv.hosts st b g) by (exists ai0; exact Hgh).
  assert (HiR : 0 <= i <= m_last_idx (MI_Inv.MR st g)) by (unfold MI_Inv.MR; fold mr; exact I).
  assert (NH' : s_groups st !! (fst b, sstart (MI_Inv.MR st g) i) = None) by (rewrite FB; unfold MI_Inv.MR; fold mr; rewrite HSTi, <- surjective_pairing; exact NH).
  assert (NOGRP : forall b' gh, s_groups st !! b' = Some gh -> fst b' = fst b -> snd b' + 9 <= snd c0 - 4 \/ e <= snd b').
  { intros b' gh Hb' Hf'. destruct (MallocFacts_inv2.hdr_hosts x0 st L BL LS INV b' gh Hb') as [m' Hm'].
    destruct (MallocFacts_inv3.sep_ghdr' x0 st L BL LS INV g b i m' b' Hhosts HiR NH' Hm' Hf') as [X|X];
      unfold MI_Inv.MR in X; fold mr in X; rewrite ?SS, ?HSTi in X; subst e; unfold IB; lia. }
  assert (NOBLK : forall b2, In b2 LB -> blk_slot b2 <> c0 -> blk_addr b2 + blk_size b2 <= Sa - 4 \/ E <= blk_addr b2).
  { intros b2 Hb2 NEb.
    destruct (MallocFacts_inv2.LB_geo x0 st L BL LS INV LB CR b2 Hb2) as (c2 & off2 & n2 & m2 & bm2 & i2 & r2 & Hk2 & C21 & C22 & Hm2 & Hi2 & Ec2 & NH2 & Hr2 & Kr2 & Ea2 & Ho2 & Hn2 & Fit2).
    pose proof (sstart_succ st m2 i2) as SS2.
    destruct (N.eq_dec (fst bm2) (fst b)) as [Ef|NEf].
    - rewrite Ef, Hr in Hr2. inversion Hr2. subst r2.
      assert (NE : m2 <> g \/ i2 <> i).
      { destruct (aptr_eq_dec m2 g) as [->|]; [right| now left]. intros ->. apply NEb. rewrite C21, Ec2, Ef, FB. fold mr. rewrite HSTi. destruct c0; reflexivity. }
      rewrite Ec2 in NH2.
      destruct (MI_Geom.sep_ext x0 st BL LS IM IG IS g b i Hhosts HiR NH' m2 bm2 i2 Hm2 Ef Hi2 NE NH2) as [X|X];
        rewrite Ea2, C22; clear - X SS SS2 Fit2 Hn2 Ho2 HSTi S16 SI0; subst E Sa e; unfold MI_Inv.MR, UNIT, IB in *; subst stride mr; lia.
    - pose proof (lr_lo_group r Kr) as LR. pose proof (lr_lo_group r2 Kr2) as LR2.
      pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) b2 Hb2) as BC2.
      destruct BC2 as [(r2' & Hr2' & _ & A16b & AENDb & _) _ _]. rewrite C21, Ec2 in Hr2'. cbn [fst] in Hr2'. rewrite Hr2 in Hr2'. inversion Hr2'. subst r2'. clear Hr2'.
      destruct (DJ _ _ _ _ Hr2 Hr0 ltac:(rewrite FB in NEf; exact NEf)) as [X|X]; rewrite ?LR, ?LR2 in X;
        clear - X A16b AENDb EHIr RB0 B0 SI0 Sc; subst E Sa e; unfold UNIT, IB in *; subst stride mr; lia. }
  (* [comment removed for export] *)
  destruct (MallocFacts_inv2.hosts_GO x0 st L BL LS INV b g Hhosts) as (aiG & _ & GOK).
  assert (Q20 : i = 0 \/ stride * (i + 1) < 2^20).
  { destruct (g_sc _ _ _ _ _ _ GOK) as [[Hsc48 _]|(_ & Hli0 & _)]; [| left; unfold MI_Inv.MR in Hli0; fold mr in Hli0; lia].
    right. destruct (g_stride _ _ _ _ _ _ GOK (proj2 Hsc48)) as (_ & _ & G20). unfold MI_Inv.MR, cnt_of in G20. fold mr in G20. fold stride in G20.
    clear - G20 SIL. lia. }
  (* [comment removed for export] *)
  pose proof (adj_facts P al ltac:(lia) ltac:(rewrite PEQ; exact AL) HAL) as AF. cbv zeta in AF.
  remember ((- P) mod al) as adj eqn:Eadj in AF. change (adj = zopaque ((- P) mod al)) in Eadj.
  destruct AF as (ADJR & ADJ16 & PAL & ADJB). change (zopaque ((P + adj) mod al) = 0) in PAL.
  clearbody q. clearbody b3.
  (* [comment removed for export] *)
  assert (ALB : 32 <= al <= 64) by (destruct HAL; lia).
  change (zopaqueP (al = 32 \/ al = 64)) in HAL. change (zopaqueP (i = 0 \/ stride * (i + 1) < 2 ^ 20)) in Q20.
  change (zopaqueP (adj = 0 \/ 16 <= adj)) in ADJB.
  clear IR IA IM IL IG IS ISH K4 K2 K1 K5 Kr0 KU H0 CX GL AR GR WA WG Hres DJ NH NH' EC0 HSTi SS HiR GOK Har Hchk Hal Em Hrg RBALg RL0g Hm LO HI AAL ANG.
  unfold UNIT, IB in *.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  rewrite <- PEQ.
  eapply evt_mono.
  { eapply raligned_hdr_walk_eq with (P:=P) (G:=conc st g) (Bb:=conc st b) (A:=conc st a) (n:=n) (b3:=b3) (q:=q)
       (avail:=m_avail mr) (freed:=m_freed mr) (last_idx:=m_last_idx mr) (freeable:=m_freeable mr) (sc:=m_sizeclass mr) (maplen:=m_maplen mr)
       (secret:=(c_secret (ctx st) + bv_unsigned rr_secret) mod 2^64) (prev:=pw st (m_prev mr)) (next:=pw st (m_next mr))
       (idx:=i) (stride:=stride) (S:=Sa) (E:=E).
    - symmetry. exact IDXe.
    - exact STRW.
    - subst Sa. rewrite Cb, Sc. clear - CEIL_RANGE__; lia.
    - subst E e. rewrite Cb, Sc. clear - CEIL_RANGE__; lia.
    - rewrite PEQ. exact AL.
    - clear - Q16 SI0 OFF RB0 B0 Sc; lia.
    - clear - POE RES0 SZ EHIr RBC PO16 CEIL_RANGE__; lia.
    - rewrite Cb. clear - Q16 Sc; lia.
    - exact HAa.
    - rewrite HG. unfold AREA_HDR, META_SIZE in *. clear - RB0g A00 Hka; lia.
    - rewrite HG. unfold AREA_HDR, META_SIZE, NSLOTS in *. clear - RB0g A00 A01 Hka RBCg RUG CEIL_RANGE__; lia.
    - replace (P - 4) with (r_base r + (po - 4)) by (clear - CEIL_RANGE__; lia). exact R4.
    - replace (P - 3) with (r_base r + (po - 3)) by (clear - CEIL_RANGE__; lia). exact R3.
    - replace (P - 2) with (r_base r + (po - 2)) by (clear - CEIL_RANGE__; lia). exact R2.
    - exact RG.
    - exact MM.
    - exact RA.
    - exact RC.
    - intros Hlt. apply rsize_classes_read; [exact MI| clear - Hlt GSC; lia].
    - exact B3R.
    - exact Q.
    - exact GAV.
    - exact GFR.
    - apply rsec_range.
    - clear - LI; lia.
    - clear - GFB; lia.
    - clear - GSC; lia.
    - clear - GML; lia.
    - clear - I; lia.
    - exact NA.
    - exact NF.
    - intros Hsc.
      destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(Hsc0 & Hle & Hst)| E63]; [| unfold MI_Inv.MR in E63; fold mr in E63; clear - Hsc E63; lia].
      unfold MI_Inv.MR in Hle, Hst. fold mr in Hle, Hst. fold stride in Hle, Hst.
      pose proof (size_class_bound _ Hsc0) as SB. unfold MI_Inv.MR in SB. fold mr in SB.
      assert (A1 : stride = 16 * size_class (m_sizeclass mr) \/ m_last_idx mr = 0) by tauto.
      assert (B1 : stride <= 16 * size_class (m_sizeclass mr) \/ 292 <= size_class (m_sizeclass mr)).
      { destruct Hle as [Hle|H28]; [left; exact Hle| right; apply size_class_28; clear - H28 Hsc0 Hsc; lia]. }
      pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF258.
      exact (guard16_arith _ _ _ _ _ _ _ (proj1 SB) Q16 FIT SZ OFF258 I A1 B1).
    - intros Hsc. clear - Hsc GSC; lia.
    - intros Hml. destruct (TOP Hml) as [B00 TOPE].
      pose proof (guard17_arith stride i off n0 q (m_last_idx mr) (m_maplen mr) S16 Q16 FIT SZ (proj1 OFF) I ltac:(clear - B00 TOPE SPAN; lia)) as G17.
      replace (m_maplen mr * 4096 / 16) with (m_maplen mr * 256) in G17
        by (clear - CEIL_RANGE__; rewrite <- (Z.div_mul (m_maplen mr * 256) 16) by lia; f_equal; lia).
      exact G17.
    - clear - GSC; lia.
    - clear - RB0 B0 SI0 OFF Sc; lia.
    - exact FR.
    - exact WMP.
    - clear - SPMP SPR; lia.
    - exact MP8.
    - left. clear - SPMP; lia.
    - exact MI.
    - clear - SPMP MP8; lia.
    - (* [comment removed for export] *)
      destruct HWr as (_ & _ & HW). subst Sa E e. split; [clear - RB0 B0 SI0 Sc; lia|]. split; [clear - EHIr RBC CEIL_RANGE__; lia|].
      intros j Hj. replace (r_base r + snd c0 - 3 + j) with (r_base r + (snd c0 - 3 + j)) by (clear - CEIL_RANGE__; lia).
      apply HW. clear - Hj B0 SI0 Sc EHIr S16; lia.
    - replace (P - 3) with (r_base r + (po - 3)) by (clear - CEIL_RANGE__; lia). exact (proj1 (HBy (po - 3) b3 ltac:(clear - PO16 EHIr POE RES0 SZ; lia) K3)).
    - rewrite Cb. clear - RB0 B0; lia.
    - rewrite Cb. pose proof (Z.div_mod (r_base r) 4096 ltac:(clear - CEIL_RANGE__; lia)) as D1. rewrite RBAL in D1. pose proof (Z.div_mod (snd b) 16 ltac:(clear - CEIL_RANGE__; lia)) as D2. rewrite B16 in D2.
      replace (r_base r + snd b) with ((256 * (r_base r / 4096) + snd b / 16) * 16) by (clear - D1 D2; lia). apply Z_mod_mult.
    - exact S16.
    - exact SM.
    - clear - EHIr RBC CEIL_RANGE__; lia.
    - clear - OFF; lia.
    - clear - OFF; lia.
    - exact N0.
    - exact HAL.
    - clear - POE RES0 HSZ; lia.
    - clear - S30 OFF HSZ ALB N0 FIT POE; lia.
    - exact Q20.
    - left. clear - EHIr RBC CSP; lia.
    - left. clear - EHIr RBC CSP SPMP; lia. }
  (* [comment removed for export] *)
  cbv beta. unfold zopaque in Eadj, PAL. rewrite <- Eadj. clear Eadj. intros ms' RP. unfold raligned_ret_post in RP.
  destruct RP as (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & ->).
  unfold raligned_tail_post.
  exists g, i, adj, r. eexists. exists x5, x6, x7, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31.
  cbv zeta. unfold UNIT, IB. rewrite <- ?PEQ. fold mr. fold stride.
  replace (P - 16 * off) with Sa by (clear - CEIL_RANGE__; lia).
  replace (Sa + stride - 4) with E by (clear - CEIL_RANGE__; lia).
  split.
  { reflexivity. }
  split; [exact SL|]. split; [exact Hr0|]. split; [exact Kr|].
  split; [exact Q20|]. split; [clear - S30 OFF HSZ ALB N0 FIT; lia|].
  split; [clear - ADJR; lia|]. split; [exact ADJ16|]. split; [clear - ADJR HSZ; lia|].
  split; [clear - ADJR ALB OFF; lia|].
  split; [exact PAL|].
  (* [comment removed for export] *)
  pose proof (realign_rep st m g b r i n off adj b3 HMR TK (go_mem _ _ _ GO) Hr Kr B0 S16 SI0 ltac:(clear - I LI; lia) ltac:(clear - EHIr Sc; try subst stride; try subst mr; lia)
                (proj1 OFF) (proj1 ADJR) ADJB N0 ltac:(clear - FIT HSZ ADJR; try subst stride; try subst mr; lia) ltac:(clear - S30 FIT HSZ ADJR ALB N0 OFF; try subst stride; try subst mr; lia) Q20
                ltac:(clear - OFF ADJR ALB; lia) (proj1 B3R) IDXe
                ltac:(intros b' gh Hb' Hf'; destruct (NOGRP b' gh Hb' Hf') as [X|X]; [left| right]; clear - X Sc; try subst stride; try subst mr; lia)) as [MRR TKR].
  fold mr in MRR. fold stride in MRR. rewrite <- !Sc in MRR.
  replace (r_base r + (snd c0 + 16 * off)) with P in MRR by (clear - CEIL_RANGE__; lia).
  replace (r_base r + (snd c0 + stride - 4)) with E in MRR by (clear - CEIL_RANGE__; lia).
  change (r_base r + snd c0) with Sa in MRR. rewrite <- Cb in MRR.
  split; [exact MRR|]. split; [exact TKR|].
  split.
  { destruct HWr as (_ & _ & HW).
    apply wframe_raligned_mem; [exact MI| | clear - OFF; lia| clear - ADJR; lia| exact ADJB| clear - POE RES0 HSZ ADJR; lia| exact N0].
    subst Sa E e. split; [clear - RB0 B0 SI0 Sc; lia|]. split; [clear - EHIr RBC CEIL_RANGE__; lia|].
    intros j Hj. replace (r_base r + snd c0 - 3 + j) with (r_base r + (snd c0 - 3 + j)) by (clear - CEIL_RANGE__; lia).
    apply HW. clear - Hj B0 SI0 Sc EHIr S16; lia. }
  split; [clear - B0 SI0 Sc; lia|].
  split; [clear - EHIr; lia|]. split; [fold n0; clear - POE RES0; lia|]. split; [exact RBC|].
  split.
  { pose proof (rregion_addr_facts st m (fst c0) r HMR Hr0) as (_ & _ & _ & RI). apply RI. clear - EHIr PO16 POE RES0 SZ; lia. }
  exact NOBLK.
Qed.

End WithCeiling0.
