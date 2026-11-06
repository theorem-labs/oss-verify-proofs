(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac ITree Nodes SysStep Decode NodesSoundMem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Export PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import F_mm_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_syscalls RMallocRep RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Realloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.



(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require JunkAbs.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MoveFacts.
Variable segs : list Segment.
Variables (m : word -> option byte) (old d on nn : Z).
Hypothesis Hold : (0 <= old /\ old + on <= 2^64)%Z.
Hypothesis Hd : (0 <= d /\ d + nn <= 2^64)%Z.
Hypothesis Hon : (0 < on)%Z.
Hypothesis Hnn : (on < nn)%Z.
Hypothesis Hdisj : (old + on <= d \/ d + nn <= old)%Z.
Let m' := move_mem m old d on nn.

Lemma wview_move_outside : forall x : word,
  (bv_unsigned x < d \/ d + nn <= bv_unsigned x)%Z -> (bv_unsigned x < old \/ old + on <= bv_unsigned x)%Z ->
  wview segs m' x = wview segs m x.
Proof. intros x H1 H2. unfold wview, m'. rewrite (move_mem_outside m old d on nn Hold Hd Hon Hnn Hdisj x H1 H2). reflexivity. Qed.

Lemma rw_cells_move_other : forall A cs,
  rw_cells segs m A cs ->
  (A + Z.of_nat (cells_size cs) <= d \/ d + nn <= A)%Z -> (A + Z.of_nat (cells_size cs) <= old \/ old + on <= A)%Z ->
  rw_cells segs m' A cs.
Proof.
  intros A cs [[Hwf Hb] Hw] D1 D2. split; [split; [exact Hwf|]|].
  - unfold m'. apply bytes_at_mremap_other; try assumption; rewrite cells_bytes_length by assumption; assumption.
  - (nelim Hw 3%nat; intros W0 W1 W). split; [lia|]. split; [lia|]. intros i Hi.
    rewrite wview_move_outside; [apply W; exact Hi| rewrite wa_unsigned by lia; lia| rewrite wa_unsigned by lia; lia].
Qed.

Lemma stk_move_other : forall lo hi, stk segs m lo hi -> (d + nn <= lo)%Z -> (old + on <= lo)%Z -> stk segs m' lo hi.
Proof using Hd Hdisj Hnn Hold Hon.
  intros lo hi (H0 & H1 & H) D1 D2. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw (b & Hb)]. split.
  - rewrite wview_move_outside; [exact Hw| rewrite wa_unsigned by lia; lia| rewrite wa_unsigned by lia; lia].
  - exists b. unfold mrd, m' in *. rewrite (move_mem_outside m old d on nn Hold Hd Hon Hnn Hdisj); [exact Hb| rewrite wa_unsigned by lia; lia| rewrite wa_unsigned by lia; lia].
Qed.

Lemma munch_move : forall W m0, munch W m0 m -> inside W d nn -> inside W old on -> munch W m0 m'.
Proof using Hd Hdisj Hnn Hold Hon. intros W m0 MU I1 I2. unfold m'. apply munch_mremap_move; assumption. Qed.
End MoveFacts.

(* [comment removed for export] *)
Lemma evt_done_or_run segs (SANE : Prop) (Q : machine_state -> Prop) ms :
  (~ SANE -> (fun ms' => SANE -> Q ms') ms) -> (SANE -> evt segs (fun ms' => SANE -> Q ms') ms) ->
  (SANE \/ ~ SANE) -> evt segs (fun ms' => SANE -> Q ms') ms.
Proof using . intros H1 H2 [S|NS]; [apply H2; exact S| apply evt_done; apply H1; exact NS]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mrm_inplace (old on nn : Z) (m : word -> option byte) : word -> option byte :=
  if (nn =? on)%Z then m
  else if (nn <? on)%Z then apply_unmaps m [(wa (old + nn), Z_to_bv 64 (on - nn))]
  else apply_zeros m [(wa (old + on), Z_to_bv 64 (nn - on))].

(* [comment removed for export] *)
Definition mrm_sane_inplace (old on nn : Z) : Prop :=
  (on < nn)%Z -> (old + nn <= alloc_ceiling)%Z /\ ranges_free ref_reserved (old + on) (nn - on) = true.
Definition mrm_sane_moved (old on nn d : Z) : Prop :=
  ranges_free ref_reserved d nn = true /\ (old + on <= d \/ d + nn <= old)%Z.

Definition rmremap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (old on nn : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : mremap_ans) : machine_state -> Prop :=
  fun ms' =>
    match a with
    | MrErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom psegs)
        /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
        /\ wmono psegs m m' /\ mem_inv psegs m'
        /\ stk psegs m' lo (bv_unsigned sp)
        /\ rw_cells psegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)]
        /\ (1 <= e <= 4095)%Z
    | MrInPlace => mrm_sane_inplace old on nn -> exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 old) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None (mrm_inplace old on nn m2) (seg_rom psegs)
        /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2
        /\ wmono psegs m m2 /\ mem_inv psegs (mrm_inplace old on nn m2)
        /\ stk psegs (mrm_inplace old on nn m2) lo (bv_unsigned sp)
        /\ rw_cells psegs m2 (errno_addr tp) [C4 errv]
    | MrMoved d => mrm_sane_moved old on nn d -> exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None (move_mem m2 old d on nn) (seg_rom psegs)
        /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2
        /\ wmono psegs m m2 /\ mem_inv psegs (move_mem m2 old d on nn)
        /\ stk psegs (move_mem m2 old d on nn) lo (bv_unsigned sp)
        /\ rw_cells psegs m2 (errno_addr tp) [C4 errv]
        /\ (on < nn)%Z /\ d <> old /\ (0 < d)%Z /\ (d mod 4096 = 0)%Z /\ (d + nn <= alloc_ceiling)%Z
    end.

Lemma rmremap_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (old on nn : Z) (errv canary : word) (lo : Z),
  stk psegs m lo (bv_unsigned sp) ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  rw_cells psegs m RGOT_SSP [C8 (wz RSSP_GUARD)] -> rw_cells psegs m RSSP_GUARD [C8 canary] ->
  mem_inv psegs m ->
  a0 = Z_to_bv 64 old -> a1 = Z_to_bv 64 on -> a2 = Z_to_bv 64 nn -> a3 = Z_to_bv 64 1 ->
  (0 < old)%Z -> (old mod 4096 = 0)%Z -> (0 < on)%Z -> (on mod 4096 = 0)%Z -> (0 < nn < 2^62)%Z -> (nn mod 4096 = 0)%Z ->
  (old + on <= alloc_ceiling)%Z -> ranges_free ref_reserved old on = true -> wr_at psegs m old on ->
  (lo <= bv_unsigned sp - 112)%Z -> (alloc_ceiling <= lo)%Z ->
  tp = Z_to_bv 64 RATP ->
  impl psegs (at_node psegs) (enode (NMremap old on nn Realloc.MREMAP_MAYMOVE) (dec_mremap old on nn []))
       (epost (rmremap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc old on nn errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmremap_entry) fc None m (seg_rom psegs)).
Proof using .
  intros until lo. intros ST ERR GOT GRD MI -> -> -> -> OLD0 OLDA ON0 ONA NN NNA OCEIL OLDF SRCW LO CEIL TPE.
  (nelimp (rreserved_disjoint _ _ OLDF) 4%nat; intros OD1 OD2 OD3 OD4).
  assert (TP : (bv_unsigned tp = 211088)%Z) by (rewrite TPE; apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU1.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  unfold alloc_ceiling in CEIL, OCEIL.
  assert (EON : mmap_len on = on) by (apply NodesSound.mmap_len_of_aligned; exact ONA).
  assert (ENN : mmap_len nn = nn) by (apply NodesSound.mmap_len_of_aligned; exact NNA).
  unfold rmremap_entry, RGOT_SSP, RSSP_GUARD, Realloc.MREMAP_MAYMOVE in *. unfold wz in GOT. apply impl_enode.
  carve_frame 96%nat ST.
  (* [comment removed for export] *)
  do 7 step. step. step. do 4 step. step. step. step. step.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  (* [comment removed for export] *)
  step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. apply K1. reflexivity. } clear K1.
  (* [comment removed for export] *)
  step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. pose proof (dec_mremap_Some _ _ _ _ _ _ Hdec) as D. clear Hdec. cbv zeta in D. rewrite EON, ENN in D.
    (* [comment removed for export] *)
    assert (TAIL : forall mX (r : Z) (Q : machine_state -> Prop), (0 <= r <= 2^64 - 4096)%Z ->
      rw_cells psegs mX (bv_unsigned sp + -96) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))))); C8 canary; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra; C8 a4; C8 a5; C8 a6; C8 a7] ->
      rw_cells psegs mX 342776 [C8 canary] -> stk psegs mX lo (bv_unsigned sp + -96) -> mem_inv psegs mX ->
      (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6', stk psegs mX lo (bv_unsigned sp) ->
         Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None mX (seg_rom psegs))) ->
      evt psegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 139556) t1 t2 (Z_to_bv 64 (-1)) (Z_to_bv 64 342776)
                        (Z_to_bv 64 r) (Z_to_bv 64 on) (Z_to_bv 64 nn) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 9223372036854775807) a6 (Z_to_bv 64 216)
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x171a0) fc None mX (seg_rom psegs))).
    { intros mX r Q HR FRX GRDX STX MIX HQ.
      (* [comment removed for export] *)
      step. step. step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } step.
      (* [comment removed for export] *)
      step. step. step. step. if_cases K3; zify_cond K3. { exfalso. apply K3. reflexivity. } clear K3.
      do 8 step. release_frame FRX STX (bv_unsigned sp). step.
      apply evt_done. apply HQ. exact STX. }
  destruct ans as [e| |dd].
  - (* [comment removed for export] *)
    clear MU1. destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | heap_lia_pruned | heap_lia_pruned | heap_lia_pruned | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    (* [comment removed for export] *)
    step. step. step. step. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. } clear K2.
    do 8 step. release_frame FR ST (bv_unsigned sp). step.
    unfold rmremap_post. finish; lia.
  - (* [comment removed for export] *)
    clear MU.
    assert (CASES : exists mx, rsp = mkEffectU (Z_to_bv 64 old) [] (match mx with Some (inr z) => [z] | _ => [] end)
                                                 (match mx with Some (inl u) => [u] | _ => [] end) [] []
              /\ match mx with
                 | None => nn = on
                 | Some (inl u) => (nn < on)%Z /\ u = (wa (old + nn), Z_to_bv 64 (on - nn))
                 | Some (inr z) => (on < nn)%Z /\ z = (wa (old + on), Z_to_bv 64 (nn - on))
                 end).
    { destruct D as [[E ->]|[[E ->]|[E ->]]].
      - exists None. split; [reflexivity| exact E].
      - exists (Some (inl (wa (old + nn), Z_to_bv 64 (on - nn)))). split; [reflexivity| auto].
      - exists (Some (inr (wa (old + on), Z_to_bv 64 (nn - on)))). split; [reflexivity| auto]. }
    clear D. (nelim CASES 3%nat; intros mx -> HMX).
    destruct mx as [[u|z]|].
    + (* [comment removed for export] *)
      destruct HMX as [LT ->]. sys_nret_raw.
      assert (Hua : (0 <= old + nn < 2^64)%Z) by lia. assert (Hun : (0 <= on - nn < 2^64)%Z) by lia. assert (Huan : (old + nn + (on - nn) <= 2^64)%Z) by lia.
      pose proof (rw_cells_unmaps_other psegs _ (old + nn) (on - nn) Hua Hun Huan _ _ FR ltac:(cbn; lia)) as FR'.
      pose proof (rw_cells_unmaps_other psegs _ (old + nn) (on - nn) Hua Hun Huan _ _ GRD ltac:(cbn; lia)) as GRD'.
      pose proof (stk_unmaps_other psegs _ (old + nn) (on - nn) Hua Hun Huan _ _ ST ltac:(lia)) as ST'.
      pose proof (mem_inv_unmaps psegs _ (old + nn) (on - nn) Hua Hun Huan MI) as MI'.
      apply TAIL; [lia| exact FR'| exact GRD'| exact ST'| exact MI'|].
      intros until t6'. intros STF _. unfold mrm_inplace.
      replace (nn =? on)%Z with false by (symmetry; apply Z.eqb_neq; lia). replace (nn <? on)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      nexists 14%nat. exists m0. split; [reflexivity|]. split; [exact MU1|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STF| exact ERR].
    + (* [comment removed for export] *)
      destruct HMX as [LT ->]. sys_nret_raw.
      apply (evt_done_or_run _ (mrm_sane_inplace old on nn)).
      { intros NS. intros SANE. exfalso. exact (NS SANE). }
      2:{ unfold mrm_sane_inplace, alloc_ceiling. destruct (ranges_free ref_reserved (old + on) (nn - on));
            destruct (Z.le_gt_cases (old + nn) alloc_ceiling); first [left; intros _; split; [assumption| reflexivity] | right; intros X; destruct (X LT); try discriminate; lia]. }
      intros SANE. destruct (SANE LT) as [CE RF]. unfold alloc_ceiling in CE.
      (nelimp (rreserved_disjoint _ _ RF) 4%nat; intros D1 D2 D3 D4).
      assert (Hza : (0 <= old + on < 2^64)%Z) by lia. assert (Hzn : (0 <= nn - on < 2^64)%Z) by lia. assert (Hzan : (old + on + (nn - on) <= 2^64)%Z) by lia.
      pose proof (rw_cells_zeros_other psegs _ (old + on) (nn - on) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR'.
      pose proof (rw_cells_zeros_other psegs _ (old + on) (nn - on) Hza Hzn Hzan _ _ GRD ltac:(cbn; lia)) as GRD'.
      pose proof (stk_zeros psegs _ (old + on) (nn - on) Hza Hzn Hzan _ _ ST) as ST'.
      assert (MI' : mem_inv psegs (apply_zeros m0 [(wa (old + on), Z_to_bv 64 (nn - on))])).
      { apply (mem_inv_zeros psegs _ (old + on) (nn - on) Hza Hzn Hzan MI); [intros x Hx; apply ref_ro_addr_false; lia | unfold TASK_SIZE; lia]. }
      apply TAIL; [lia| exact FR'| exact GRD'| exact ST'| exact MI'|].
      intros until t6'. intros STF _. unfold mrm_inplace.
      replace (nn =? on)%Z with false by (symmetry; apply Z.eqb_neq; lia). replace (nn <? on)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      nexists 14%nat. exists m0. split; [reflexivity|]. split; [exact MU1|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STF| exact ERR].
    + (* [comment removed for export] *)
      subst nn. sys_nret.
      apply TAIL; [lia| exact FR| exact GRD| exact ST| exact MI|].
      intros until t6'. intros STF _. unfold mrm_inplace. rewrite Z.eqb_refl.
      nexists 14%nat. exists m0. split; [reflexivity|]. split; [exact MU1|]. split; [exact WM|]. split; [exact MI|]. split; [exact STF| exact ERR].
  - (* [comment removed for export] *)
    clear MU. (nelim D 4%nat; intros LT NE AOK ->).
    pose proof (mmap_addr_ok_true _ _ _ AOK) as ((XA & X0 & XC) & _). try rewrite alloc_ceiling_val in XC. rewrite ENN in XC.
    rewrite NodesSound.page_size_val in XA.
    rewrite nret_MSsvc_copy1, ?mkR_set_a0. simp_regs.
    replace (Z_to_bv 64 0x1719c + Z_to_bv 64 4 : word) with (Z_to_bv 64 0x171a0 : word) by (rewrite lit_add_lit; reflexivity).
    rewrite ?(unsigned_lit dd) by lia.
    replace (apply_copy m0 (apply_zeros (apply_unmaps m0 [(Z_to_bv 64 old, Z_to_bv 64 on)]) [(wa (dd + on), Z_to_bv 64 (nn - on))])
              (mkCopy (Z_to_bv 64 old) (Z_to_bv 64 dd) (Z_to_bv 64 on))) with (move_mem m0 old dd on nn)
      by (unfold move_mem; rewrite lit_add_lit; reflexivity).
    apply (evt_done_or_run _ (mrm_sane_moved old on nn dd)).
    { intros NS. intros SANE. exfalso. exact (NS SANE). }
    2:{ unfold mrm_sane_moved. destruct (ranges_free ref_reserved dd nn);
          destruct (Z.le_gt_cases (old + on) dd); destruct (Z.le_gt_cases (dd + nn) old);
          first [left; split; [reflexivity| heap_lia_pruned] | right; intros [X Y]; try discriminate; heap_lia_pruned]. }
    intros [RF DJ]. (nelimp (rreserved_disjoint _ _ RF) 4%nat; intros D1 D2 D3 D4).
    assert (Hold : (0 <= old /\ old + on <= 2^64)%Z) by lia. assert (Hd : (0 <= dd /\ dd + nn <= 2^64)%Z) by lia.
    pose proof (rw_cells_move_other psegs m0 old dd on nn Hold Hd ON0 LT DJ _ _ FR ltac:(cbn; clear - XC CEIL LO; lia) ltac:(cbn; clear - OCEIL CEIL LO; lia)) as FR'.
    pose proof (rw_cells_move_other psegs m0 old dd on nn Hold Hd ON0 LT DJ _ _ GRD ltac:(cbn; clear - D4 NN; lia) ltac:(cbn; clear - OD4 ON0; lia)) as GRD'.
    pose proof (stk_move_other psegs m0 old dd on nn Hold Hd ON0 LT DJ _ _ ST ltac:(clear - XC CEIL; lia) ltac:(clear - OCEIL CEIL; lia)) as ST'.
    assert (SRC : forall i, (0 <= i < on)%Z -> m0 (wa (old + i)) <> None).
    { intros i Hi. (nelim SRCW 3%nat; intros _ _ W). specialize (W i Hi).
      rewrite ref_wview_overlay in W by (rewrite wa_unsigned by (clear - Hold Hi; lia); clear - OD1 OD2 OD3 OD4 ON0 Hi Hold; lia). exact W. }
    assert (MI' : mem_inv psegs (move_mem m0 old dd on nn)).
    { apply (mem_inv_mremap_move psegs m0 old dd on nn Hold Hd ON0 LT DJ MI);
        [intros x Hx; apply ref_ro_addr_false; clear - Hx D1 D2 D3 D4 NN; lia | unfold TASK_SIZE; clear - XC CEIL; lia]. }
    apply TAIL; [clear - X0 XC NN; lia| exact FR'| exact GRD'| exact ST'| exact MI'|].
    intros until t6'. intros STF _.
    nexists 14%nat. exists m0. split; [reflexivity|]. split; [exact MU1|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STF|]. split; [exact ERR|].
    unfold alloc_ceiling. repeat split; clear - LT NE X0 XA XC; lia.
Qed.


End CeilWrap.
