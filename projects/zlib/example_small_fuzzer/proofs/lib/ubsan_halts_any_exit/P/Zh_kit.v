(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MonadX.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Image OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.SysStep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ITree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Nodes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Decode OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Arr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.FP OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Cells.Bytes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.MonadX.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_tac.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Exit Printf_stdio_iface Zlib_iface Driver_iface Drv_kit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_tac.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Driver_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Drv_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.


Lemma Z_to_le_bytes_inv : forall (bs : list byte), Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
  assert (R0 : 0 <= bytes_le_to_Z bs).
  { clear. induction bs as [|c cs IHc]; cbn [bytes_le_to_Z]; [lia|]. pose proof (bv_unsigned_in_range 8 c) as Rc. change (bv_modulus 8) with 256 in Rc.
    rewrite lor_shiftl8_add by lia. lia. }
  rewrite lor_shiftl8_add by lia. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    symmetry. apply (Z.mod_unique_pos _ _ (bytes_le_to_Z bs)); lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs); [exact IH|].
    apply (Z.div_unique_pos _ _ _ (bv_unsigned b)); lia.
Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> exists z, 0 <= z < 2^64 /\ le8 (Z_to_bv 64 z) = bs.
Proof.
  intros bs L. exists (bytes_le_to_Z bs mod 2^64). split; [apply Z.mod_pos_bound; lia|].
  unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_mod by lia.
  rewrite <- (Z_to_le_bytes_inv bs) at 2. rewrite L.
  rewrite <- (Z_to_le_bytes_mod 8 (bytes_le_to_Z bs) 64) by lia. reflexivity.
Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> exists z, 0 <= z < 2^32 /\ le4 (Z_to_bv 64 z) = bs.
Proof.
  intros bs L. exists (bytes_le_to_Z bs mod 2^32). assert (R : 0 <= bytes_le_to_Z bs mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
  split; [exact R|].
  unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite (Z.mod_small _ (2^64)) by lia.
  rewrite <- (Z_to_le_bytes_inv bs) at 2. rewrite L.
  rewrite <- (Z_to_le_bytes_mod 4 (bytes_le_to_Z bs) 32) by lia. reflexivity.
Qed.

Lemma rw_cells_addr_eq : forall m A A' cs, rw_cells psegs m A cs -> A = A' -> rw_cells psegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.

Lemma rw_cells_recast : forall m A cs cs', rw_cells psegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells psegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb.
  assert (Es : cells_size cs' = cells_size cs).
  { rewrite <- (cells_bytes_length cs' Hwf'), <- (cells_bytes_length cs Hwf), Eb. reflexivity. }
  split; [split|]; [exact Hwf'| rewrite Eb; exact Hb| rewrite Es; exact Hw].
Qed.

Lemma zs_pub_of_bytes : forall bs : list byte, length bs = 48%nat ->
  exists ni ai ti no ao to p1 p2,
    cells_bytes (zs_pub ni ai ti no ao to p1 p2) = bs /\ cells_wf (zs_pub ni ai ti no ao to p1 p2)
    /\ 0 <= ni < 2^64 /\ 0 <= ai < 2^32 /\ 0 <= ti < 2^64 /\ 0 <= no < 2^64 /\ 0 <= ao < 2^32 /\ 0 <= to < 2^64.
Proof.
  intros bs L.
  pose proof (mk_CB_cells_bytes [8; 4; 4; 8; 8; 4; 4; 8]%nat bs L) as EB.
  pose proof (mk_CB_cells_wf [8; 4; 4; 8; 8; 4; 4; 8]%nat bs L) as WF.
  cbn [mk_CB_cells] in EB, WF. cbn [cells_wf cell_wf] in WF.
  destruct WF as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & _).
  set (c0 := firstn 8 bs) in *. set (r0 := skipn 8 bs) in *.
  set (c1 := firstn 4 r0) in *. set (r1 := skipn 4 r0) in *.
  set (c2 := firstn 4 r1) in *. set (r2 := skipn 4 r1) in *.
  set (c3 := firstn 8 r2) in *. set (r3 := skipn 8 r2) in *.
  set (c4 := firstn 8 r3) in *. set (r4 := skipn 8 r3) in *.
  set (c5 := firstn 4 r4) in *. set (r5 := skipn 4 r4) in *.
  set (c6 := firstn 4 r5) in *. set (r6 := skipn 4 r5) in *.
  set (c7 := firstn 8 r6) in *.
  destruct (le8_of_bytes c0 L0) as (ni & Rni & Eni). destruct (le4_of_bytes c1 L1) as (ai & Rai & Eai).
  destruct (le8_of_bytes c3 L3) as (ti & Rti & Eti). destruct (le8_of_bytes c4 L4) as (no & Rno & Eno).
  destruct (le4_of_bytes c5 L5) as (ao & Rao & Eao). destruct (le8_of_bytes c7 L7) as (to & Rto & Eto).
  exists ni, ai, ti, no, ao, to, c2, c6.
  split; [| split; [| repeat split; lia]].
  - unfold zs_pub, wz. cbn [cells_bytes cbytes] in EB |- *. rewrite Eni, Eai, Eti, Eno, Eao, Eto. exact EB.
  - unfold zs_pub. cbn [cells_wf cell_wf]. repeat split; assumption.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition LXW (m : mem) : Prop := lx_statics m /\ zl_statics m /\ stderr_wfile0 m.
Definition lxw_addr (a : Z) : Prop := lxs_addr a \/ zls_addr a \/ stderr_addr a.

Lemma lxw_addr_range : forall a, lxw_addr a -> 0x28000 <= a < 0x5b000 /\ ~ ralloc_static a.
Proof.
  intros a H. unfold lxw_addr, lxs_addr, zls_addr, stderr_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO,
    RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_GOT_STDERR, LX_STDERR_PTR, ZL_RELRO_LO, ZL_RELRO_HI, ZL_GOT_LO, ZL_GOT_HI, ZH_STATICS, ZL_MREPL in *. lia.
Qed.

Lemma LXW_agree : forall (P : Z -> Prop) m m', agree_on P m m' -> (forall a, lxw_addr a -> P a) -> LXW m -> LXW m'.
Proof.
  intros P m m' AG HP (A1 & A2 & A3). split; [| split].
  - eapply lx_statics_agree; [exact AG| | exact A1]. intros a Ha. apply HP. left. exact Ha.
  - eapply zl_statics_agree; [exact AG| | exact A2]. intros a Ha. apply HP. right; left. exact Ha.
  - eapply stderr_wfile0_agree; [exact AG| | exact A3]. intros a Ha. apply HP. right; right. exact Ha.
Qed.

Lemma LXW_agree_se : forall (P : Z -> Prop) m m', agree_on P m m' -> (forall a, lxs_addr a \/ zls_addr a -> P a) ->
  stderr_wfile0 m' -> LXW m -> LXW m'.
Proof.
  intros P m m' AG HP SE (A1 & A2 & _). split; [| split; [| exact SE]].
  - eapply lx_statics_agree; [exact AG| | exact A1]. intros a Ha. apply HP. left. exact Ha.
  - eapply zl_statics_agree; [exact AG| | exact A2]. intros a Ha. apply HP. right. exact Ha.
Qed.

Lemma LXW_heap : forall LB SP m m', rheap_pres LB SP m m' -> LXW m -> LXW m'.
Proof.
  intros LB SP m m' HP. apply (LXW_agree _ _ _ (agree_of_heap_pres _ _ _ _ HP)).
  intros a Ha. destruct (lxw_addr_range a Ha) as [R NS]. right; left. split; [lia| exact NS].
Qed.

Lemma LXW_lx : forall LB SP X m m', lx_pres LB SP X m m' -> (forall a, lxw_addr a -> ~ rin_ivs X a) -> LXW m -> LXW m'.
Proof.
  intros LB SP X m m' HP HX. apply (LXW_agree _ _ _ (agree_of_lx_pres _ _ _ _ _ HP)).
  intros a Ha. destruct (lxw_addr_range a Ha) as [R NS]. split; [apply HX; exact Ha| right; right; split; [lia| exact NS]].
Qed.

Lemma LXW_munch : forall W m m', munch W m m' -> wmono psegs m m' -> (forall a, 0x28000 <= a < 0x5b000 -> outside W a) -> LXW m -> LXW m'.
Proof.
  intros W m m' MU WM HW. apply (LXW_agree _ _ _ (agree_on_of_munch _ _ _ MU WM)).
  intros a Ha. apply HW. destruct (lxw_addr_range a Ha) as [R _]. lia.
Qed.

Lemma lx_pres_of_munch : forall LB' SP X W m m',
  munch W m m' -> wmono psegs m m' -> (forall a, lx_client LB' SP X a -> outside W a) -> lx_pres LB' SP X m m'.
Proof. intros LB' SP X W m m' MU WM HW. eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)| exact HW]. Qed.

Lemma lx_env_munch_gen : forall W m m' s OW LB (sp sp' tp : word) B lo errv canary,
  RHEAP_frame_stmt ->
  lx_env m s OW LB sp tp B lo errv canary -> munch W m m' -> wmono psegs m m' -> mem_inv psegs m' ->
  stk psegs m' lo (bv_unsigned sp') -> bv_unsigned sp' <= B ->
  Forall (rclient_write_ok (OW ++ LB)) W ->
  (forall a, B <= a \/ (0x28000 <= a < 0x5b000 /\ ~ stderr_addr a /\ ~ (ZH_STATICS <= a < ZH_STATICS + 16)) -> outside W a) ->
  stderr_wfile0 m' -> (exists v1 v2 : word, rw_cells psegs m' ZH_STATICS [C8 v1; C8 v2]) ->
  lx_env m' s OW LB sp' tp B lo errv canary.
Proof.
  intros W m m' s OW LB sp sp' tp B lo errv canary HFRAME (HP & LXS & ZLS & SEW & SSP & AUX & SPB & B63 & ST & LOC & LOG & ERR & TP & MI) MU WM MI' ST' SPB' WOK OUT SEW' ZHC'.
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  assert (IMG : forall a, 0x28000 <= a < 0x5b000 -> ~ stderr_addr a -> ~ (ZH_STATICS <= a < ZH_STATICS + 16) -> outside W a) by (intros a Ha Hs Hz; apply OUT; right; auto).
  unfold lx_env. split; [eapply HFRAME; eassumption|].
  split. { eapply lx_statics_agree; [exact AG| | exact LXS]. intros a Ha. apply IMG; unfold lxs_addr, stderr_addr, LX_GOT_STDERR, LX_STDERR_PTR, ZH_STATICS in *; lia. }
  split. { destruct ZLS as (N1 & N2 & _ & MRP). unfold zl_statics.
           assert (TR : forall a : word, outside W (bv_unsigned a) -> m a = None -> m' a = None).
           { intros a Po E. pose proof (bv_unsigned_in_range 64 a) as Ra. change (bv_modulus 64) with (2^64) in Ra.
             destruct (AG (bv_unsigned a) Ra Po) as [E' _]. unfold wa in E'. rewrite Z_to_bv_bv_unsigned in E'. congruence. }
           split; [intros a Ha; apply TR; [apply IMG; unfold stderr_addr, ZL_RELRO_LO, ZL_RELRO_HI, ZH_STATICS in *; lia| apply N1; exact Ha]|].
           split; [intros a Ha; apply TR; [apply IMG; unfold stderr_addr, ZL_GOT_LO, ZL_GOT_HI, ZH_STATICS in *; lia| apply N2; exact Ha]|].
           split; [exact ZHC'|]. eapply rw_cells_agree; [exact AG| exact MRP|]. intros a Ha. cbn in Ha. apply IMG; unfold stderr_addr, ZL_MREPL, ZH_STATICS in *; lia. }
  split; [exact SEW'|].
  split. { eapply ssp_cells_agree; [exact AG| | exact SSP]. intros a Ha. apply IMG; unfold ssp_addr, stderr_addr, got_ssp, ssp_guard, ZH_STATICS in *; lia. }
  split. { eapply rauxv_ok_agree; [exact AG| | | exact AUX]; intros a Ha; [apply OUT; left; exact Ha| apply IMG; unfold RAUXV_CELL, stderr_addr, ZH_STATICS in *; lia]. }
  split; [exact SPB'|]. split; [exact B63|]. split; [exact ST'|]. split; [exact LOC|]. split; [exact LOG|].
  split. { eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. rewrite TP in Ha. unfold RMallocRep.RATP in Ha. unfold wz in Ha. rewrite unsigned_lit in Ha by lia.
           change (Z.of_nat (cells_size [C4 errv])) with 4 in Ha. apply IMG; unfold stderr_addr, ZH_STATICS; lia. }
  split; [exact TP| exact MI'].
Qed.

Lemma lx_env_munch_se : forall W m m' s OW LB (sp sp' tp : word) B lo errv canary,
  RHEAP_frame_stmt ->
  lx_env m s OW LB sp tp B lo errv canary -> munch W m m' -> wmono psegs m m' -> mem_inv psegs m' ->
  stk psegs m' lo (bv_unsigned sp') -> bv_unsigned sp' <= B ->
  Forall (rclient_write_ok (OW ++ LB)) W ->
  (forall a, B <= a \/ (0x28000 <= a < 0x5b000 /\ ~ stderr_addr a) -> outside W a) ->
  stderr_wfile0 m' ->
  lx_env m' s OW LB sp' tp B lo errv canary.
Proof.
  intros W m m' s OW LB sp sp' tp B lo errv canary HFRAME ENV MU WM MI' ST' SPB' WOK OUT SEW'.
  eapply lx_env_munch_gen; try eassumption.
  - intros a [Ha|(Ha & Hs & _)]; apply OUT; [left; exact Ha| right; split; assumption].
  - destruct ENV as (_ & _ & (_ & _ & (v1 & v2 & ZHC) & _) & _). exists v1, v2.
    eapply rw_cells_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact ZHC|]. intros a Ha. cbn in Ha. apply OUT. right. unfold stderr_addr, ZH_STATICS in *. lia.
Qed.

Lemma lx_env_munch : forall W m m' s OW LB (sp sp' tp : word) B lo errv canary,
  RHEAP_frame_stmt ->
  lx_env m s OW LB sp tp B lo errv canary -> munch W m m' -> wmono psegs m m' -> mem_inv psegs m' ->
  stk psegs m' lo (bv_unsigned sp') -> bv_unsigned sp' <= B ->
  Forall (rclient_write_ok (OW ++ LB)) W ->
  (forall a, B <= a \/ 0x28000 <= a < 0x5b000 -> outside W a) ->
  lx_env m' s OW LB sp' tp B lo errv canary.
Proof.
  intros W m m' s OW LB sp sp' tp B lo errv canary HFRAME ENV MU WM MI' ST' SPB' WOK OUT.
  eapply lx_env_munch_se; try eassumption.
  - intros a [Ha|[Ha _]]; apply OUT; [left| right]; exact Ha.
  - destruct ENV as (_ & _ & _ & SEW & _). eapply stderr_wfile0_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SEW].
    intros a Ha. apply OUT. right. unfold stderr_addr in Ha. lia.
Qed.

Lemma u8arr_agree : forall (P : Z -> Prop) m m' A bs, agree_on P m m' -> u8arr psegs m A bs ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> u8arr psegs m' A bs.
Proof.
  intros P m m' A bs AG [Hb Hw] HP. split; [eapply bytes_at_agree; eassumption| eapply wr_at_agree; eassumption].
Qed.

Lemma to_bytes_len0 : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.

Lemma bytes_at_inj : forall m a (l1 l2 : list byte), bytes_at psegs m a l1 -> bytes_at psegs m a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length l1)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None l1 i) Hi), (proj2 (nth_error_None l2 i) ltac:(lia)). reflexivity.
Qed.

Lemma ssp_canary : forall m s LB (c : word), ssp_cells m c -> RHEAP s LB m -> c = rr_guard.
Proof.
  intros m s LB c [_ H1] HP. destruct (RHEAP_ssp _ _ _ HP) as [_ H2].
  apply rw_cells_bytes_at in H1, H2. cbn [cells_bytes cbytes] in H1, H2. rewrite !app_nil_r in H1, H2.
  pose proof (bytes_at_inj _ _ _ _ H1 H2 ltac:(rewrite !Mem.length_le8; reflexivity)) as E.
  rewrite <- (Mem.le_bytes_to_word_le8 c), <- (Mem.le_bytes_to_word_le8 rr_guard), E. reflexivity.
Qed.

Lemma lx_env_heap : forall m m' s s' OW OW' LB (sp tp : word) B lo errv errv' canary,
  lx_env m s OW LB sp tp B lo errv canary -> rheap_pres LB (bv_unsigned sp) m m' -> RHEAP s' (OW' ++ LB) m' ->
  mem_inv psegs m' -> stk psegs m' lo (bv_unsigned sp) -> rw_cells psegs m' (errno_addr tp) [C4 errv'] -> rauxv_ok m' B ->
  lx_env m' s' OW' LB sp tp B lo errv' canary.
Proof.
  intros m m' s s' OW OW' LB sp tp B lo errv errv' canary (HP & LXS & ZLS & SEW & SSP & AUX & SPB & B63 & ST & LOC & LOG & ERR & TP & MI) PRES HP' MI' ST' ERR' AUX'.
  destruct (LXW_heap _ _ _ _ PRES (conj LXS (conj ZLS SEW))) as (LXS' & ZLS' & SEW').
  unfold lx_env. split; [exact HP'|]. split; [exact LXS'|]. split; [exact ZLS'|]. split; [exact SEW'|].
  split; [rewrite (ssp_canary _ _ _ _ SSP HP); exact (RHEAP_ssp _ _ _ HP')|].
  repeat (split; [assumption|]). assumption.
Qed.

Lemma payload_ok_agree : forall (P : Z -> Prop) m m' LB D d, agree_on P m m' -> payload_ok m LB D d ->
  (forall a, D <= a < D + zlength d -> P a) -> payload_ok m' LB D d.
Proof.
  intros P m m' LB D d AG (PB & PF & PD & PD2 & PD3 & PIN) HP. split; [| repeat (split; [assumption|]); assumption].
  eapply bytes_at_agree; [exact AG| exact PB|]. intros a Ha. rewrite to_bytes_len0 in Ha. apply HP. unfold zlength. lia.
Qed.

Lemma payload_ok_mono : forall m LB LB' D d, payload_ok m LB D d -> (forall b, In b LB -> In b LB') -> payload_ok m LB' D d.
Proof.
  intros m LB LB' D d (PB & PF & PD & PD2 & PD3 & PIN) HL. repeat (split; [assumption|]).
  destruct PIN as [E|(b & Hb & Hr)]; [left; exact E| right; exists b; split; [apply HL; exact Hb| exact Hr]].
Qed.

Lemma lx_env_blocks : forall m s OW LB OW' LB' (sp tp : word) B lo errv canary,
  lx_env m s OW LB sp tp B lo errv canary -> RHEAP s (OW' ++ LB') m -> lx_env m s OW' LB' sp tp B lo errv canary.
Proof.
  intros m s OW LB OW' LB' sp tp B lo errv canary (_ & REST) HP. split; [exact HP| exact REST].
Qed.

Lemma lx_pres_sub : forall LB SP X LB' SP' X' m m', lx_pres LB SP X m m' ->
  (forall a, lx_client LB' SP' X' a -> lx_client LB SP X a) -> lx_pres LB' SP' X' m m'.
Proof. intros LB SP X LB' SP' X' m m' H HC a Ha Hc. apply H; [exact Ha| apply HC; exact Hc]. Qed.

Lemma lx_env_sp : forall m s OW LB (sp sp' tp : word) B lo errv canary,
  lx_env m s OW LB sp tp B lo errv canary -> stk psegs m lo (bv_unsigned sp') -> bv_unsigned sp' <= B ->
  lx_env m s OW LB sp' tp B lo errv canary.
Proof.
  intros m s OW LB sp sp' tp B lo errv canary (HP & LXS & ZLS & SEW & SSP & AUX & SPB & B63 & ST & LOC & LOG & ERR & TP & MI) ST' SPB'.
  unfold lx_env. repeat (split; [assumption|]). assumption.
Qed.

Lemma heap_sep : forall s L1 L2 m b1 b2, RHEAP_blocks_nodup_stmt -> RHEAP_blocks_disjoint_stmt ->
  RHEAP s (L1 ++ L2) m -> In b1 L1 -> In b2 L2 ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
  intros s L1 L2 m b1 b2 HND HBD HP H1 H2.
  apply (HBD _ _ _ _ _ HP); [apply in_or_app; left; exact H1| apply in_or_app; right; exact H2|].
  pose proof (HND _ _ _ HP) as ND. rewrite map_app in ND.
  intros E. revert ND. apply (in_map blk_id) in H1, H2. rewrite E in H1. clear - H1 H2.
  induction (map blk_id L1) as [|x l IH]; [contradiction|]. cbn [app]. intros ND. inversion ND as [|? ? NI ND']; subst.
  destruct H1 as [->|H1]; [apply NI; apply in_or_app; right; exact H2| exact (IH H1 ND')].
Qed.

Lemma blocks_write_ok : forall (LBz LB : list block),
  Forall (rclient_write_ok (LBz ++ LB)) (map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBz).
Proof.
  intros LBz LB. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as (b & <- & Hb).
  right; right. exists b. split; [apply in_or_app; left; exact Hb| cbn [fst snd]; lia].
Qed.
End WithCeiling0.

Section BindR.
  Import ITree.Exc.
  Lemma impl_bind_assoc_r : forall {A B C} (t : itree node A) (g : A -> itree node B) (f : B -> itree node C) Q ms,
    impl psegs (at_node psegs) (ITree.bind node (ITree.bind node t g) f) Q ms ->
    impl psegs (at_node psegs) (ITree.bind node t (fun x => ITree.bind node (g x) f)) Q ms.
  Proof.
    intros A B C t. induction t as [r|n k IH]; intros g f Q ms H; cbn [ITree.bind] in *.
    - exact H.
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. apply IH. apply Hk.
  Qed.

  Context {St : Type}.
  Lemma implM_bind_assoc_r : forall {A B C} (m : @M St A) (g : A -> @M St B) (f : B -> @M St C) s Q ms,
    implM psegs (Monad.mbind (Monad.mbind m g) f) s Q ms ->
    implM psegs (Monad.mbind m (fun a => Monad.mbind (g a) f)) s Q ms.
  Proof.
    intros A B C m g f s Q ms H. unfold implM, Monad.mbind, ebind in *.
    apply impl_bind_assoc_r in H. eapply MonadX.impl_bind_cong; [| exact H].
    intros [|[a s']] ms'; cbn [ITree.bind fst snd]; intros H'; exact H'.
  Qed.

  Lemma implM_bind2 : forall {A B C} (m : @M St A) (g : A -> @M St B) (f : B -> @M St C) s Q1 Q ms,
    implM psegs (Monad.mbind m g) s Q1 ms ->
    (forall b s' ms', Q1 b s' ms' -> implM psegs (f b) s' Q ms') ->
    implM psegs (Monad.mbind m (fun a => Monad.mbind (g a) f)) s Q ms.
  Proof. intros A B C m g f s Q1 Q ms H1 H2. apply implM_bind_assoc_r. eapply implM_bind; eassumption. Qed.
End BindR.


Lemma to_bytes_norm8 : forall l, to_bytes (norm8 l) = to_bytes l.
Proof.
  induction l as [|b l IH]; [reflexivity|]. cbn [norm8 map to_bytes] in *. unfold to_bytes in *. cbn [map]. f_equal; [| exact IH].
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_mod. lia.
Qed.

Lemma to_bytes_zrepeat0 : forall n, to_bytes (zrepeat 0 n) = MallocRep.zeros (Z.to_nat n).
Proof. intros n. unfold to_bytes, zrepeat, MallocRep.zeros, MallocRep.b8. apply map_repeat. Qed.

Lemma to_bytes_len : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.
