(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib PFLib LeptDefs LeptStructs LeptRecs LeptArith LeptArith2 LeptNuma LeptEdgeFP LeptRoom LeptRoom9.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9LeptStderr V9LeptBase.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9CL7a.
Import V9CL7a.V9LeptErr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9CL8a.
Import V9CL8a.V9LeptPixHdr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9LeptCmap2 V9LeptPixCopy V9LeptEdge_iface V9LeptNfeSegs V9LeptEdgeSegs2 V9LeptNgi.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section EdgeW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V9Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma str_pmes_msg : str16 0x115d7 29. Proof. str16_tac. Qed.
Lemma str_pmes_proc : str16 0x152ed 24. Proof. str16_tac. Qed.

(* [comment removed for export] *)
Definition pmcells (M : word -> option byte) (s : Z) (ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : word) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) /\ rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) /\
  rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) /\ rdn SEGS M (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) /\
  rdn SEGS M (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) /\ rdn SEGS M (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v21) /\
  rdn SEGS M (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v22) /\ rdn SEGS M (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v23) /\
  rdn SEGS M (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v24) /\ rdn SEGS M (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v25).

(* [comment removed for export] *)
Lemma pmcells_eq : forall M M' s ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25, (88 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (forall x : word, (s - 88 <= u x < s)%Z -> M' x = M x) ->
  pmcells M s ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 -> pmcells M' s ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25.
Proof.
  intros M M' s ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 Hs Hs64 E (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11). unfold pmcells.
  repeat split; (match goal with |- rdn _ _ ?a _ = _ => match goal with H : rdn _ _ a _ = _ |- _ => rewrite <- H end end;
                 apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros x Hx; cbn in Hx; apply E; lia]).
Qed.

Lemma pmcells_FRM : forall C M M' s s' ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25, Cok C -> FRM C s' M M' ->
  (c_top C - LSTK <= s')%Z -> (s' <= s - 88)%Z -> (s <= c_top C)%Z ->
  pmcells M s ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 -> pmcells M' s ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25.
Proof.
  intros C M M' s s' ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 CK F Hlo Hs' Hhi (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
  pose proof CK as [T1 T2 T3 T4 T5]. unfold pmcells.
  rewrite !(FRM_rdn16 C s' M M' _ _ CK F) by lia. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma ngi_c1_val : rdn SEGS (fun _ => None) (Z_to_bv 64 0x1c680) 8 = Some (Z_to_le_bytes 8 D_ONE). Proof. vm_refl_bv. Qed.
Lemma ngi_c2_val : rdn SEGS (fun _ => None) (Z_to_bv 64 0x1c430) 8 = Some (Z_to_le_bytes 8 D_HALF). Proof. vm_refl_bv. Qed.
Lemma ngi_c3_val : rdn SEGS (fun _ => None) (Z_to_bv 64 0x1c478) 8 = Some (Z_to_le_bytes 8 D_LO). Proof. vm_refl_bv. Qed.
Lemma ngi_c4_val : rdn SEGS (fun _ => None) (Z_to_bv 64 0x1c348) 8 = Some (Z_to_le_bytes 8 D_HI). Proof. vm_refl_bv. Qed.
Lemma W_ngi_c1 : forall C A m md, W C A m md -> rdn SEGS m (Z_to_bv 64 0x1c680) 8 = Some (Z_to_le_bytes 8 D_ONE).
Proof. intros C A m md HW. rewrite <- p16_segs. rewrite (W_rdn_ro C A m md 0x1c680 8 HW); [rewrite p16_segs; exact ngi_c1_val | |]; cbn [fst snd ll_ro LLU16]; lia. Qed.
Lemma W_ngi_c2 : forall C A m md, W C A m md -> rdn SEGS m (Z_to_bv 64 0x1c430) 8 = Some (Z_to_le_bytes 8 D_HALF).
Proof. intros C A m md HW. rewrite <- p16_segs. rewrite (W_rdn_ro C A m md 0x1c430 8 HW); [rewrite p16_segs; exact ngi_c2_val | |]; cbn [fst snd ll_ro LLU16]; lia. Qed.
Lemma W_ngi_c3 : forall C A m md, W C A m md -> rdn SEGS m (Z_to_bv 64 0x1c478) 8 = Some (Z_to_le_bytes 8 D_LO).
Proof. intros C A m md HW. rewrite <- p16_segs. rewrite (W_rdn_ro C A m md 0x1c478 8 HW); [rewrite p16_segs; exact ngi_c3_val | |]; cbn [fst snd ll_ro LLU16]; lia. Qed.
Lemma W_ngi_c4 : forall C A m md, W C A m md -> rdn SEGS m (Z_to_bv 64 0x1c348) 8 = Some (Z_to_le_bytes 8 D_HI).
Proof. intros C A m md HW. rewrite <- p16_segs. rewrite (W_rdn_ro C A m md 0x1c348 8 HW); [rewrite p16_segs; exact ngi_c4_val | |]; cbn [fst snd ll_ro LLU16]; lia. Qed.

(* [comment removed for export] *)
Lemma prof_cells_mem : forall m m' arr n lo hi, (0 <= arr)%Z -> (arr + 4 * n < 2 ^ 64)%Z ->
  prof_cells SEGS m arr n lo hi -> (forall x : word, (arr <= u x < arr + 4 * n)%Z -> m' x = m x) -> prof_cells SEGS m' arr n lo hi.
Proof.
  intros m m' arr n lo hi Ha Hn P E i Hi. destruct (P i Hi) as (v & Hv & NC). exists v. split; [exact Hv|].
  unfold ncell in *. rewrite <- NC. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply E. lia.
Qed.
Lemma prof_cells_weaken : forall m arr n lo hi hi', (hi <= hi')%Z -> prof_cells SEGS m arr n lo hi -> prof_cells SEGS m arr n lo hi'.
Proof. intros m arr n lo hi hi' H P i Hi. destruct (P i Hi) as (v & Hv & NC). exists v. split; [lia | exact NC]. Qed.

(* [comment removed for export] *)
Lemma m16_8 : forall x : Z, (x mod 16 = 0)%Z -> (x mod 8 = 0)%Z.
Proof. intros x H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. apply Z.mod_divide; [lia|]. exists (2 * q)%Z. lia. Qed.
Lemma m16_4 : forall x : Z, (x mod 16 = 0)%Z -> (x mod 4 = 0)%Z.
Proof. intros x H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. apply Z.mod_divide; [lia|]. exists (4 * q)%Z. lia. Qed.
Lemma m16_4k : forall x k : Z, (x mod 16 = 0)%Z -> (k mod 4 = 0)%Z -> ((x - k) mod 4 = 0)%Z.
Proof.
  intros x k H K. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. apply Z.mod_divide in K; [|lia]. destruct K as [p ->].
  apply Z.mod_divide; [lia|]. exists (4 * q - p)%Z. lia.
Qed.

#[local] Definition pm_rest : list (bv 5) := [3; 4; 26; 27]%bv.

Lemma pm_R_of : forall r r' s, pm_R r s -> (forall x, In x [2; 8; 9; 18; 19; 20]%bv -> getr r' x = getr r x) -> pm_R r' s.
Proof.
  intros r r' s (H2 & H8 & H9 & H18 & H19 & H20) E. unfold pm_R.
  rewrite !E by (cbn; tauto). repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma pm_loop : forall (k : nat) (fx : FPState) C A A1 m md vm1 regs (ret : word) (s na arr h i pv nj js : Z) M r (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 2048 <= s)%Z -> (s + 16 <= c_top C)%Z ->
  W C A1 M (with_vmmaps vm1 md) -> POSTM C A (s + 16) m M -> sub_live A A1 ->
  numa_at C A1 M na h h arr -> prof_cells SEGS M arr h 0 19999 -> rdn SEGS M (Z_to_bv 64 (s - 104)) 8 = Some (Z_to_le_bytes 8 na) ->
  rdn SEGS M (Z_to_bv 64 (s - 92)) 4 = Some (Z_to_le_bytes 4 pv) -> (0 <= pv <= 19999)%Z -> (0 <= nj <= i - 1)%Z -> (0 <= js <= (i - 1) * 19999)%Z ->
  pmcells M s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) ->
  pm_R r s -> getr r 21 = Z_to_bv 64 h -> getr r 22 = Z_to_bv 64 i -> getr r 23 = Z_to_bv 64 js -> getr r 24 = Z_to_bv 64 nj -> getr r 25 = Z_to_bv 64 IMIN ->
  (1 <= i < h)%Z -> (h <= 20000)%Z -> Z.of_nat k = (h - i)%Z ->
  (forall x, In x pm_rest -> getr r x = getr regs x) ->
  (forall (fx' : FPState) M' r', frm_zero (@fp_csr fx') -> W C A1 M' (with_vmmaps vm1 md) -> POSTM C A (s + 16) m M' ->
     numa_at C A1 M' na h h arr -> rdn SEGS M' (Z_to_bv 64 (s - 104)) 8 = Some (Z_to_le_bytes 8 na) ->
     pmcells M' s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) ->
     pm_R r' s -> getr r' 21 = Z_to_bv 64 h -> (forall x, In x pm_rest -> getr r' x = getr regs x) ->
     realizes SEGS (mkCfg (@mkst fx' r' (0x826cc : word) M' al_rom) (with_vmmaps vm1 md)) S) ->
  realizes SEGS (mkCfg (@mkst fx r (0x82594 : word) M al_rom) (with_vmmaps vm1 md)) S.
Proof.
  induction k as [|k IH]; intros fx C A A1 m md vm1 regs ret s na arr h i pv nj js M r S Hz CK Hs16 Hlo Hhi HW PM SUB NA PCL Cna Rpv Hpv Hnj Hjs PC PR R21 R22 R23 R24 R25 Hi Hh Hk RR HX; [lia|].
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  pose proof NA as (RN & Hal & Harr & Hala & NEa & Hna & Hn & L1 & L01 & L2 & L02).
  pose proof (NUMA_wf M na h h 1 arr RN) as (_ & _ & _ & Warr & Wna0 & Wna64).
  destruct (blk_range C A1 M _ (Z_to_bv 64 na) 32 CK HW L1 ltac:(lia)) as [Gna Tna]. rewrite u_Z2bv in Gna, Tna by lia.
  destruct (blk_range C A1 M _ (Z_to_bv 64 arr) _ CK HW L2 ltac:(lia)) as [Gar Tar]. rewrite u_Z2bv in Gar, Tar by lia.
  (* [comment removed for export] *)
  destruct (pm_L al_rom fx r M s na i ltac:(lia) ltac:(lia) ltac:(lia) Cna PR R22) as (r1 & RUN1 & PR1 & Q22 & Q1 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  destruct (PCL i ltac:(lia)) as (nv & Hnv & NC). unfold ncell in NC.
  destruct (ngi_run al_rom fx r1 M na h h 1 arr i (s - 96) nv (Z_to_bv 64 0x825a4) Hz RN ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(lia) ltac:(lia) (m16_4k s 96 Hs16 eq_refl) (m16_8 na Hal) (m16_4 arr Hala) Hnv NC
              (W_ngi_c1 C A1 M _ HW) (W_ngi_c2 C A1 M _ HW) (W_ngi_c3 C A1 M _ HW) (W_ngi_c4 C A1 M _ HW)
              (W_sok_win C A1 M _ (s - 96) 4 CK HW ltac:(lia) ltac:(cbn; lia)) ltac:(red; apply bv_eq; reflexivity) Q1 Q10 Q11 Q12)
    as (fr2 & cs2 & r2 & RUN2 & Hz2 & V10 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN2 |].
  replace (Z_to_bv 64 0x825a4) with (0x825a4 : word) by (apply bv_eq; reflexivity).
  set (M2 := wbytes (wbytes M (Z_to_bv 64 (s - 96)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 96)) (word_to_le_bytes 4 (Z_to_bv 64 nv))).
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A (s + 16) m M2) by (subst M2; wp_win CK).
  destruct WP2 as [HW2 PM2].
  assert (OUT2 : forall x : word, ~ (s - 96 <= u x < s - 92)%Z -> M2 x = M x).
  { intros x Hx. subst M2. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (Rnv : rdn SEGS M2 (Z_to_bv 64 (s - 96)) 4 = Some (Z_to_le_bytes 4 nv)).
  { subst M2. rewrite <- (w2l_Z4 nv) by lia. apply rdn_wbytes_hit4; rewrite u_Z2bv by lia; lia. }
  assert (Rpv' : rdn SEGS M2 (Z_to_bv 64 (s - 92)) 4 = Some (Z_to_le_bytes 4 pv)).
  { rewrite <- Rpv. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUT2. lia. }
  assert (PR2 : pm_R r2 s) by (apply (pm_R_of r1); [exact PR1 | intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]); destruct Hx]).
  assert (R21' : getr r2 21 = Z_to_bv 64 h) by (csr; reflexivity).
  assert (R22' : getr r2 22 = Z_to_bv 64 i) by (csr; reflexivity).
  assert (R23' : getr r2 23 = Z_to_bv 64 js) by (csr; reflexivity).
  assert (R24' : getr r2 24 = Z_to_bv 64 nj) by (csr; reflexivity).
  assert (R25' : getr r2 25 = Z_to_bv 64 IMIN) by (csr; reflexivity).
  assert (Bjs : (0 <= js <= 19999 * 19999)%Z) by nia.
  pose proof (W_sok_win C A1 M2 _ (s - 92) 4 CK HW2 ltac:(lia) ltac:(cbn; lia)) as SOK2.
  set (nj' := (nj + (if (nv =? pv)%Z then 0 else 1))%Z). set (js' := (js + Z.abs (nv - pv))%Z).
  assert (Bnj' : (0 <= nj' <= i)%Z) by (subst nj'; destruct (nv =? pv)%Z; lia).
  assert (Bjs' : (0 <= js' <= (i + 1 - 1) * 19999)%Z) by (subst js'; lia).
  set (M3 := wbytes M2 (Z_to_bv 64 (s - 92)) (Z_to_le_bytes 4 nv)).
  assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A (s + 16) m M3).
  { subst M3. apply (WP_win C A1 A m M2 _ _ _ (s + 16) CK (conj HW2 PM2) SUB); rewrite ?length_Z_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  destruct WP3 as [HW3 PM3].
  assert (OUT3 : forall x : word, ~ (s - 96 <= u x < s - 88)%Z -> M3 x = M x).
  { intros x Hx. subst M3. rewrite wbytes_outside; [apply OUT2; lia | rewrite length_Z_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_Z_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  destruct (Z_lt_ge_dec (i + 1) h) as [NX|LAST].
  - (* [comment removed for export] *)
    destruct (pm_L2n al_rom (mkFP fr2 cs2) r2 M2 s h i nv pv nj js ltac:(lia) ltac:(lia) ltac:(lia) NX ltac:(lia) Rnv Rpv' Hnv Hpv ltac:(lia) Bjs SOK2 PR2 R21' R22' R23' R24' R25')
      as (r3 & RUN3 & PR3 & Q21 & Q22n & Q23n & Q24n & Q25n & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
    fold M3. fold nj' in Q24n. fold js' in Q23n.
    apply (IH (mkFP fr2 cs2) C A A1 m md vm1 regs ret s na arr h (i + 1)%Z nv nj' js' M3 r3 S Hz2 CK Hs16 Hlo Hhi HW3 PM3 SUB).
    + apply (numa_at_mem C A1 M M3 _ _ _ _ NA). intros x Hx. apply OUT3. lia.
    + apply (prof_cells_mem M M3 arr h 0 19999 ltac:(lia) ltac:(lia) PCL). intros x Hx. apply OUT3. lia.
    + rewrite <- Cna. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUT3. lia.
    + subst M3. rewrite <- (length_Z_to_le_bytes 4 nv) at 2. apply rdn_wbytes_hit. rewrite length_Z_to_le_bytes, u_Z2bv by lia. cbn. lia.
    + exact Hnv.
    + lia.
    + exact Bjs'.
    + apply (pmcells_eq M M3); [lia | lia | intros x Hx; apply OUT3; lia | exact PC].
    + exact PR3.
    + exact Q21.
    + exact Q22n.
    + exact Q23n.
    + exact Q24n.
    + exact Q25n.
    + lia.
    + exact Hh.
    + lia.
    + intros x Hx. rewrite <- (RR x Hx). unfold pm_rest in Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]). destruct Hx.
    + exact HX.
  - (* [comment removed for export] *)
    destruct (pm_L2x al_rom (mkFP fr2 cs2) r2 M2 s h i nv pv nj js ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Rnv Rpv' Hnv Hpv ltac:(lia) Bjs SOK2 PR2 R21' R22' R23' R24' R25')
      as (r3 & RUN3 & PR3 & Q21 & Q23n & Q24n & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
    fold M3.
    apply (HX (mkFP fr2 cs2) M3 r3 Hz2 HW3 PM3).
    + apply (numa_at_mem C A1 M M3 _ _ _ _ NA). intros x Hx. apply OUT3. lia.
    + rewrite <- Cna. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUT3. lia.
    + apply (pmcells_eq M M3); [lia | lia | intros x Hx; apply OUT3; lia | exact PC].
    + exact PR3.
    + exact Q21.
    + intros x Hx. rewrite <- (RR x Hx). unfold pm_rest in Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]). destruct Hx.
Qed.

Section Main.
Hypothesis HND : numaDestroy_contract.
Hypothesis HGEP : pixGetEdgeProfile_contract.
Hypothesis HNFE : numaFindExtrema_contract.

(* [comment removed for export] *)
Lemma pm_end : forall (fx : FPState) C A A1 m md vm1 regs (ret : word) (s na arr h : Z) M r (S : TSet) (kF bF : Z),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 + NDS_STACK <= s)%Z -> (s + 16 <= c_top C)%Z -> ret_ok ret ->
  W C A1 M (with_vmmaps vm1 md) -> POSTM C A (s + 16) m M ->
  numa_at C A1 M na h h arr -> rdn SEGS M (Z_to_bv 64 (s - 104)) 8 = Some (Z_to_le_bytes 8 na) ->
  live A (Z_to_bv 64 na) = None -> live A (Z_to_bv 64 arr) = None ->
  (forall q, q <> Z_to_bv 64 na -> q <> Z_to_bv 64 arr -> live A1 q = live A q) ->
  pmcells M s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) ->
  pm_R r s -> getr r 4 = Z_to_bv 64 TP9 -> (forall x, In x pm_rest -> getr r x = getr regs x) -> getr regs 2 = Z_to_bv 64 s ->
  aroom A1 vm1 kF bF ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A (s + 16) m m' ->
     (forall q, live A' q = live A q) -> aroom A' vm' kF bF ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx r (0x82754 : word) M al_rom) (with_vmmaps vm1 md)) S.
Proof.
  intros fx C A A1 m md vm1 regs ret s na arr h M r S kF bF CK Hs16 Hlo Hhi Hret HW PM NA Cna LnaA LarrA LQ PC PR R4 RR H2 Hrm K.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold NDS_STACK, ALLOC_STACK in *.
  destruct (pm_F al_rom fx r M s ltac:(lia) ltac:(lia) PR) as (r1 & RUN1 & PR1 & Q1 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  destruct PR1 as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20).
  replace (0x61794 : word) with (Z_to_bv 64 PC_numaDestroy) by (apply bv_eq; reflexivity).
  apply (HND fx C A1 M (with_vmmaps vm1 md) r1 (s - 112)%Z (s - 104)%Z na h h arr (Z_to_bv 64 0x8275c) S CK HW Y2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold NDS_STACK, ALLOC_STACK; lia) ltac:(lia) ltac:(lia)
           ltac:(rewrite <- Zminus_mod_idemp_l; replace (s mod 8)%Z with 0%Z by (symmetry; apply Z.mod_divide; [lia | apply Z.mod_divide in Hs16; [destruct Hs16 as [q ->]; exists (2 * q)%Z; lia | lia]]); reflexivity)
           Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) Q10 Cna NA).
  intros A2 m2 vm2 r2 HW2 CS2 Lna2 Larr2 LQ2 PM2 R02 HRT. rewrite ?with_vmmaps_twice in HW2 |- *.
  replace (Z_to_bv 64 0x8275c) with (0x8275c : word) by (apply bv_eq; reflexivity).
  pose proof (HRT _ _ Hrm (proj1 (aroom_nonneg _ _ _ _ Hrm)) (proj2 (aroom_nonneg _ _ _ _ Hrm))) as Hrm2. rewrite !Z.sub_0_r in Hrm2.
  assert (LQA : forall q, live A2 q = live A q).
  { intros q. destruct (bv_eq_dec _ q (Z_to_bv 64 na)) as [->|N1]; [rewrite Lna2, LnaA; reflexivity|].
    destruct (bv_eq_dec _ q (Z_to_bv 64 arr)) as [->|N2]; [rewrite Larr2, LarrA; reflexivity|].
    rewrite (LQ2 q N1 N2). exact (LQ q N1 N2). }
  destruct PM2 as [F2 L2].
  assert (PMf : POSTM C A (s + 16) m m2).
  { eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C A A2); [apply sub_live_eq; intros q; exact (LQA q)|].
    eapply POSTM_mono; [| exact (conj F2 L2)]. lia. }
  pose proof (pmcells_FRM C M m2 s (s - 104 + 8) _ _ _ _ _ _ _ _ _ _ _ CK F2 ltac:(lia) ltac:(lia) ltac:(lia) PC) as (C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25).
  destruct (pm_G al_rom fx r2 m2 s ret _ _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) Hret C1 C8 C9 C18 C19 C20 C21 C22 C23 C24 C25 ltac:(csr; reflexivity))
    as (r3 & RUN3 & Z2 & Z10 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  apply (K A2 m2 vm2 r3 HW2); [| exact PMf | exact LQA | exact Hrm2].
  apply cs_kept_of_rest; [rewrite Z2, H2; reflexivity | exact Z8 | exact Z9 |].
  intros x Hx. unfold cs_rest in Hx. cbn in Hx.
  destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; try assumption;
    (match goal with |- getr _ ?x = _ => rewrite <- (RR x ltac:(unfold pm_rest; cbn; tauto)) end; csr; reflexivity).
Qed.

(* [comment removed for export] *)
Lemma pm_tail : forall (fx : FPState) C A A1 m md vm1 regs (ret : word) (s na arr h : Z) M r (S : TSet) (kR1 bR1 : Z),
  frm_zero (@fp_csr fx) -> Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 + NFE_STACK <= s)%Z -> (s + 16 <= c_top C)%Z -> ret_ok ret ->
  W C A1 M (with_vmmaps vm1 md) -> POSTM C A (s + 16) m M -> sub_live A A1 ->
  numa_at C A1 M na h h arr -> (2 <= h <= 20000)%Z -> rdn SEGS M (Z_to_bv 64 (s - 104)) 8 = Some (Z_to_le_bytes 8 na) ->
  live A (Z_to_bv 64 na) = None -> live A (Z_to_bv 64 arr) = None ->
  (forall q, q <> Z_to_bv 64 na -> q <> Z_to_bv 64 arr -> live A1 q = live A q) ->
  pmcells M s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) ->
  pm_R r s -> (forall x, In x pm_rest -> getr r x = getr regs x) -> getr regs 2 = Z_to_bv 64 s -> getr regs 4 = Z_to_bv 64 TP9 ->
  aroom A1 vm1 kR1 bR1 -> (RK_nfe <= kR1)%Z -> (RB_nfe <= bR1)%Z ->
  (forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A (s + 16) m m' ->
     (forall q, live A' q = live A q) -> aroom A' vm' (kR1 - RK_nfe) (bR1 - RB_nfe) ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx r (0x826cc : word) M al_rom) (with_vmmaps vm1 md)) S.
Proof.
  intros fx C A A1 m md vm1 regs ret s na arr h M r S kR1 bR1 Hz CK Hs16 Hlo Hhi Hret HW PM SUB NA Hh Cna LnaA LarrA LQ PC PR RR H2 H4 Hrm Hrk Hrb K.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  unfold NFE_STACK, NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  pose proof NA as (RN & Hal & Harr & Hala & NEa & Hna & Hn & L1 & L01 & L2 & L02).
  pose proof (NUMA_wf M na h h 1 arr RN) as (_ & _ & _ & Warr & Wna0 & Wna64).
  destruct (blk_range C A1 M _ (Z_to_bv 64 na) 32 CK HW L1 ltac:(lia)) as [Gna Tna]. rewrite u_Z2bv in Gna, Tna by lia.
  (* [comment removed for export] *)
  destruct (pm_D al_rom fx r M s na (getr r 21) (getr r 23) (getr r 24) Hz ltac:(lia) ltac:(lia) ltac:(lia) Hs16 Cna
              (W_sok_win C A1 M _ (s + 4) 12 CK HW ltac:(lia) ltac:(cbn; lia)) PR eq_refl eq_refl eq_refl)
    as (fr1 & cs1 & r1 & bs1 & bs2 & RUN1 & Hz1 & Lb1 & Lb2 & PR1 & Q1 & Q10 & Q11 & QF & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes M (Z_to_bv 64 (s + 12)) bs1) (Z_to_bv 64 (s + 8)) bs2).
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A (s + 16) m M1).
  { subst M1. apply (WP_win C A1 A m _ _ _ _ (s + 16) CK); [| exact SUB | rewrite u_Z2bv by lia; lia | rewrite Lb2, u_Z2bv by lia; cbn; lia | lia].
    apply (WP_win C A1 A m M _ _ _ (s + 16) CK (conj HW PM) SUB); [rewrite u_Z2bv by lia; lia | rewrite Lb1, u_Z2bv by lia; cbn; lia | lia]. }
  destruct WP1 as [HW1 PM1].
  assert (OUT1 : forall x : word, ~ (s + 8 <= u x < s + 16)%Z -> M1 x = M x).
  { intros x Hx. subst M1. rewrite !wbytes_outside; rewrite ?Lb1, ?Lb2, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (NA1 : numa_at C A1 M1 na h h arr) by (apply (numa_at_mem C A1 M M1 _ _ _ _ NA); intros x Hx; apply OUT1; lia).
  destruct PR1 as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20).
  replace (0x613c0 : word) with (Z_to_bv 64 PC_numaFindExtrema) by (apply bv_eq; reflexivity).
  apply (HNFE (mkFP fr1 cs1) C A1 M1 (with_vmmaps vm1 md) r1 (s - 112)%Z na h h arr (Z_to_bv 64 0x82720) S Hz1 CK HW1 Y2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold NFE_STACK, NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)
           Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) Q10 Q11 QF NA1 Hh
           kR1 bR1 Hrm Hrk Hrb).
  intros fx2 A2 m2 vm2 r2 nad nalloc' c arr' Hz2 HW2 CS2 PM2 A10 NAD LnadA LarrdA LQ2 Hrm2. rewrite ?with_vmmaps_twice in HW2 |- *.
  replace (Z_to_bv 64 0x82720) with (0x82720 : word) by (apply bv_eq; reflexivity).
  pose proof NAD as (RD & Hald & Harrd & Halad & NEd & Hnad & Hnd & Ld1 & Ld01 & Ld2 & Ld02).
  pose proof (NUMA_wf m2 nad nalloc' c 1 arr' RD) as (_ & _ & _ & Warrd & Wnad0 & Wnad64).
  destruct (blk_range C A2 m2 _ (Z_to_bv 64 nad) 32 CK HW2 Ld1 ltac:(lia)) as [Gnad Tnad]. rewrite u_Z2bv in Gnad, Tnad by lia.
  assert (SUB12 : sub_live A1 A2) by (apply (sub_live_new2 A1 A2 _ _ _ _ LnadA LarrdA Ld1 Ld2 LQ2)).
  assert (SUB2 : sub_live A A2) by (eapply sub_live_trans; [exact SUB | exact SUB12]).
  destruct PM2 as [F2 LK2].
  assert (PM2' : POSTM C A (s + 16) m m2).
  { eapply POSTM_trans; [exact PM1|]. apply (POSTM_sub C A A1 _ _ _ SUB). eapply POSTM_mono; [| exact (conj F2 LK2)]. lia. }
  assert (NA2 : numa_at C A2 m2 na h h arr) by (apply (numa_at_keep C A1 A2 M1 m2 _ _ _ _ NA1 SUB12 LK2)).
  assert (NEnn : Z_to_bv 64 na <> Z_to_bv 64 nad) by (intros E; rewrite E in L1; rewrite L1 in LnadA; discriminate).
  assert (NEna : Z_to_bv 64 na <> Z_to_bv 64 arr') by (intros E; rewrite E in L1; rewrite L1 in LarrdA; discriminate).
  assert (NEan : Z_to_bv 64 arr <> Z_to_bv 64 nad) by (intros E; rewrite E in L2; rewrite L2 in LnadA; discriminate).
  assert (NEaa : Z_to_bv 64 arr <> Z_to_bv 64 arr') by (intros E; rewrite E in L2; rewrite L2 in LarrdA; discriminate).
  assert (Cna2 : rdn SEGS m2 (Z_to_bv 64 (s - 104)) 8 = Some (Z_to_le_bytes 8 na)).
  { rewrite (FRM_rdn16 C (s - 112) M1 m2 (s - 104) 8 CK F2) by lia. rewrite <- Cna. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUT1. lia. }
  assert (PC2 : pmcells m2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)).
  { apply (pmcells_FRM C M1 m2 s (s - 112) _ _ _ _ _ _ _ _ _ _ _ CK F2 ltac:(lia) ltac:(lia) ltac:(lia)). apply (pmcells_eq M M1); [lia | lia | intros x Hx; apply OUT1; lia | exact PC]. }
  assert (PR2 : pm_R r2 s).
  { apply (pm_R_of r1); [unfold pm_R; repeat split; assumption | intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]); destruct Hx]. }
  (* [comment removed for export] *)
  destruct (pm_E al_rom fx2 r2 m2 s nad c (getr r2 21) Hz2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold NUMA_NMAX in *; lia) Hs16 (m16_8 nad Hald)
              (NUMA_rd_n SEGS m2 nad nalloc' c 1 arr' RD)
              (W_sok_win C A2 m2 _ (s - 112) 8 CK HW2 ltac:(lia) ltac:(cbn; lia)) (W_sok_win C A2 m2 _ (s + 4) 12 CK HW2 ltac:(lia) ltac:(cbn; lia))
              PR2 A10 eq_refl)
    as (fr3 & cs3 & r3 & bs3 & RUN3 & Hz3 & Lb3 & PR3 & V1 & V10 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  set (M3 := wbytes (wbytes m2 (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 nad))) (Z_to_bv 64 (s + 4)) bs3).
  assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C A (s + 16) m M3).
  { subst M3. apply (WP_win C A2 A m _ _ _ _ (s + 16) CK); [| exact SUB2 | rewrite u_Z2bv by lia; lia | rewrite Lb3, u_Z2bv by lia; cbn; lia | lia].
    apply (WP_win C A2 A m m2 _ _ _ (s + 16) CK (conj HW2 PM2') SUB2); [rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia]. }
  destruct WP3 as [HW3 PM3].
  assert (OUT3 : forall x : word, ~ (s - 112 <= u x < s - 104)%Z -> ~ (s + 4 <= u x < s + 8)%Z -> M3 x = m2 x).
  { intros x Hx Hx'. subst M3. rewrite !wbytes_outside; rewrite ?Lb3, ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (NAD3 : numa_at C A2 M3 nad nalloc' c arr') by (apply (numa_at_mem C A2 m2 M3 _ _ _ _ NAD); intros x Hx; apply OUT3; lia).
  assert (Rpp3 : rdn SEGS M3 (Z_to_bv 64 (s - 112)) 8 = Some (Z_to_le_bytes 8 nad)).
  { subst M3. rewrite rdn_wbytes_out_Z by (rewrite Lb3; cbn; lia). rewrite <- w2l_Z8 by lia. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
  destruct PR3 as (X2 & X8 & X9 & X18 & X19 & X20).
  replace (0x61794 : word) with (Z_to_bv 64 PC_numaDestroy) by (apply bv_eq; reflexivity).
  apply (HND (mkFP fr3 cs3) C A2 M3 (with_vmmaps vm2 md) r3 (s - 112)%Z (s - 112)%Z nad nalloc' c arr' (Z_to_bv 64 0x82754) S CK HW3 X2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold NDS_STACK, ALLOC_STACK; lia) ltac:(lia) ltac:(lia)
           ltac:(rewrite <- Zminus_mod_idemp_l; replace (s mod 8)%Z with 0%Z by (symmetry; apply Z.mod_divide; [lia | apply Z.mod_divide in Hs16; [destruct Hs16 as [q ->]; exists (2 * q)%Z; lia | lia]]); reflexivity)
           V1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) V10 Rpp3 NAD3).
  intros A4 m4 vm4 r4 HW4 CS4 Lnad4 Larrd4 LQ4 PM4 R04 HRT4. rewrite ?with_vmmaps_twice in HW4 |- *.
  replace (Z_to_bv 64 0x82754) with (0x82754 : word) by (apply bv_eq; reflexivity).
  pose proof (HRT4 _ _ Hrm2 (proj1 (aroom_nonneg _ _ _ _ Hrm2)) (proj2 (aroom_nonneg _ _ _ _ Hrm2))) as Hrm4. rewrite !Z.sub_0_r in Hrm4.
  destruct PM4 as [F4 LK4].
  assert (Lna4 : live A4 (Z_to_bv 64 na) = Some 32%Z) by (rewrite (LQ4 _ NEnn NEna); exact (SUB12 _ _ L1)).
  assert (Lar4 : live A4 (Z_to_bv 64 arr) = Some (4 * h)%Z) by (rewrite (LQ4 _ NEan NEaa); exact (SUB12 _ _ L2)).
  assert (LQ14 : forall q, live A4 q = live A1 q).
  { intros q. destruct (bv_eq_dec _ q (Z_to_bv 64 nad)) as [->|N1]; [rewrite Lnad4, LnadA; reflexivity|].
    destruct (bv_eq_dec _ q (Z_to_bv 64 arr')) as [->|N2]; [rewrite Larrd4, LarrdA; reflexivity|].
    rewrite (LQ4 q N1 N2). exact (LQ2 q N1 N2). }
  assert (SUB4 : sub_live A A4) by (intros q k Lq; rewrite LQ14; exact (SUB q k Lq)).
  apply (pm_end (mkFP fr3 cs3) C A A4 m md vm4 regs ret s na arr h m4 r4 S (kR1 - RK_nfe)%Z (bR1 - RB_nfe)%Z CK Hs16
           ltac:(unfold NDS_STACK, ALLOC_STACK; lia) Hhi Hret HW4).
  - eapply POSTM_trans; [exact PM3|]. apply (POSTM_sub C A A4 _ _ _ SUB4). eapply POSTM_mono; [| exact (conj F4 LK4)]. lia.
  - apply (numa_at_livk C A2 A4 M3 m4 _ _ _ _); [| exact Lna4 | exact Lar4 | exact LK4].
    apply (numa_at_mem C A2 m2 M3 _ _ _ _ NA2). intros x Hx. apply OUT3; lia.
  - rewrite (FRM_rdn16 C (s - 112 + 8) M3 m4 (s - 104) 8 CK F4) by lia. rewrite <- Cna2. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUT3; lia.
  - exact LnaA.
  - exact LarrA.
  - intros q N1 N2. rewrite LQ14. exact (LQ q N1 N2).
  - apply (pmcells_FRM C M3 m4 s (s - 112 + 8) _ _ _ _ _ _ _ _ _ _ _ CK F4 ltac:(lia) ltac:(lia) ltac:(lia)). apply (pmcells_eq m2 M3); [lia | lia | intros x Hx; apply OUT3; lia | exact PC2].
  - apply (pm_R_of r3); [unfold pm_R; repeat split; assumption | intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]); destruct Hx].
  - csr. reflexivity.
  - intros x Hx. rewrite <- (RR x Hx). unfold pm_rest in Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]). destruct Hx.
  - exact H2.
  - exact Hrm4.
  - intros A' m' vm' regs' HW' CS' PM' LQ' Hrm'. exact (K (mkFP fr3 cs3) A' m' vm' regs' Hz3 HW' CS' PM' LQ' Hrm').
Qed.

Theorem pixMeasureEdgeSmoothness_W : pixMeasureEdgeSmoothness_contract.
Proof.
  unfold pixMeasureEdgeSmoothness_contract, PMES_STACK, GEP_STACK, NAN_STACK, NEX_STACK, RNW_STACK, TP9.
  intros fx C A m md regs s pixs w h d cm data ret S Hz CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 H14 H15 H16 H17 PX HOK Hw Hh Lp Ld kR bR Hrm Hrk Hrb K.
  unfold PC_pixMeasureEdgeSmoothness. replace (Z_to_bv 64 0x82400) with (0x82400 : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF, CALLOC_STACK, ALLOC_STACK in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd. cbn [p_d hdv] in Rd.
  destruct HOK as (DV & Hw2 & Hh2 & Hsz).
  assert (Hd31 : (0 <= d < 2 ^ 31)%Z) by (unfold dval in DV; lia).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (PIX_rd_d SEGS _ _ _ PX) as Cd. cbn [p_d hdv] in Cd.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  (* [comment removed for export] *)
  destruct (pm_A0 al_rom fx regs m s pixs d ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hd31 Hs16 (m16_8 pixs ALp) Cd
              (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn; lia)) (W_sok_win C A m md (s + 4) 12 CK HW ltac:(lia) ltac:(cbn; lia))
              H2 H1 H10 H11 H12 H13 H14 H15 H16 H17) as (r1 & RUN1 & R1 & Q21 & Q22 & Q23 & Q24 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M0 := PMESM m s ret regs).
  assert (WP0 : W C A M0 md /\ POSTM C A (s + 16) m M0) by (subst M0; unfold PMESM, PMESF; wp_win CK).
  destruct WP0 as [HW0 PM0].
  assert (PC0 : pmcells M0 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)).
  { subst M0. unfold pmcells, PMESM, PMESF. repeat split; rdn_solve. }
  destruct (Z.eq_dec d 1) as [D1|Dn1].
  2:{ (* [comment removed for export] *)
    destruct PC0 as (C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25). destruct R1 as (Y2 & _).
    destruct (pm_Ae al_rom fx r1 M0 s d ret _ _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) Hd31 Dn1 (W_sev_got C A M0 md HW0) (W_sev C A M0 md HW0)
                C1 C8 C9 C18 C19 C20 C21 C22 C23 C24 C25 Y2 Q10) as (r2 & RUN2 & Z2 & Z1 & Z10 & Z11 & Z12 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN2 |].
    replace (0x5d1c4 : word) with (0x5d1c4 : word) by reflexivity.
    apply (returnErrorInt_W C A M0 md r2 s 0x115d7 0x152ed 29 24 ret (Z_to_bv 64 1) S CK HW0 Z2 Hs16 ltac:(unfold LSF; lia) ltac:(lia) Z1 Hret
             Z10 Z11 Z12 str_pmes_msg str_pmes_proc).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    rewrite <- (with_vmmaps_same md). apply (K fx A m4 (m_vmmaps md) r5 Hz).
    - rewrite with_vmmaps_same. exact HW4.
    - apply cs_kept_intro; csr; try reflexivity.
    - eapply POSTM_trans; [exact PM0|].
      eapply (POSTM_range C A M0 _ m4); [exact CK | exact HW0 | exact OUT4 | lia | lia | lia].
    - intros q; reflexivity.
    - pose proof (RB_pmes_nonneg h ltac:(lia)). rewrite RK_pmes_val in *. apply (aroom_mono _ _ _ _ _ _ Hrm); lia. }
  (* [comment removed for export] *)
  subst d. destruct R1 as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20).
  destruct (pm_A1 al_rom fx r1 M0 s pixs (conj Y2 (conj Y8 (conj Y9 (conj Y18 (conj Y19 Y20))))) Q21 Q22 Q23 Q10) as (r2 & RUN2 & Z1 & Z10 & Z11 & Z12 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN2 |].
  destruct PM0 as [F0 L0].
  assert (PX0 : PIXat M0 pixs (hdv w h 1 cm data)).
  { apply (PIXat_frame m M0 _ _ PX). intros x Hx. exact (LIVK_at A m M0 pixs 64 x L0 Lp ltac:(lia) ltac:(lia) Hx). }
  assert (Z2 : getr r2 2 = Z_to_bv 64 (s - 112)) by (csr; reflexivity).
  assert (Z4 : getr r2 4 = Z_to_bv 64 TP9) by (csr; reflexivity).
  replace (0x82768 : word) with (Z_to_bv 64 PC_pixGetEdgeProfile) by (apply bv_eq; reflexivity).
  apply (HGEP fx C A M0 md r2 (s - 112)%Z pixs w h cm data (Z_to_bv 64 0x82544) S Hz CK HW0 Z2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold GEP_STACK, NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia) Z1 ltac:(red; apply bv_eq; reflexivity) Z4 Z10 Z11 Z12
           PX0 (conj DV (conj Hw2 (conj Hh2 Hsz))) Hw Hh Lp Ld kR bR Hrm ltac:(rewrite RK_pmes_val in Hrk; unfold RK_numa; lia)
           ltac:(rewrite RB_pmes_split, RB_nfe_val in Hrb; lia)).
  intros fx1 A1 m1 vm1 r3 na arr Hz1 HW1 CS1 PM1 A10 NA LnaA LarrA LQ1 PCLw Hrm1.
  pose proof (prof_cells_weaken m1 arr h 0 (w - 1) 19999 ltac:(lia) PCLw) as PCL1.
  replace (Z_to_bv 64 0x82544) with (0x82544 : word) by (apply bv_eq; reflexivity).
  pose proof NA as (RN & Hal & Harr & Hala & NEa & Hna & Hn & L1 & L01 & L2 & L02).
  pose proof (NUMA_wf m1 na h h 1 arr RN) as (_ & _ & _ & Warr & Wna0 & Wna64).
  destruct (blk_range C A1 m1 _ (Z_to_bv 64 na) 32 CK HW1 L1 ltac:(lia)) as [Gna Tna]. rewrite u_Z2bv in Gna, Tna by lia.
  assert (SUB1 : sub_live A A1) by (apply (sub_live_new2 A A1 _ _ _ _ LnaA LarrA L1 L2 LQ1)).
  destruct PM1 as [F1 LK1].
  assert (PMm1 : POSTM C A (s + 16) m m1).
  { eapply POSTM_trans; [exact (conj F0 L0)|]. eapply POSTM_mono; [| exact (conj F1 LK1)]. lia. }
  assert (PC1 : pmcells m1 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25))
    by (apply (pmcells_FRM C M0 m1 s (s - 112) _ _ _ _ _ _ _ _ _ _ _ CK F1 ltac:(lia) ltac:(lia) ltac:(lia) PC0)).
  assert (PR3 : pm_R r3 s).
  { apply (pm_R_of r1); [unfold pm_R; repeat split; assumption | intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]); destruct Hx]. }
  assert (RR3 : forall x, In x pm_rest -> getr r3 x = getr regs x).
  { intros x Hx. unfold pm_rest in Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]). destruct Hx. }
  assert (Hrk1 : (RK_nfe <= kR - RK_numa)%Z) by (rewrite RK_pmes_val, RK_nfe_val in *; unfold RK_numa; lia).
  assert (Hrb1 : (RB_nfe <= bR - RB_numa h)%Z) by (rewrite RB_pmes_split in Hrb; lia).
  assert (KE : forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A (s + 16) m m' ->
             (forall q, live A' q = live A q) -> aroom A' vm' (kR - RK_numa - RK_nfe) (bR - RB_numa h - RB_nfe) ->
             realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) (with_vmmaps vm' md)) S).
  { intros fx' A' m' vm' regs' Hz' HW' CS' PM' LQ' Hrm'. apply (K fx' A' m' vm' regs' Hz' HW' CS' PM' LQ').
    replace (kR - RK_pmes)%Z with (kR - RK_numa - RK_nfe)%Z by (rewrite RK_pmes_val, RK_nfe_val; unfold RK_numa; lia).
    replace (bR - RB_pmes h)%Z with (bR - RB_numa h - RB_nfe)%Z by (rewrite RB_pmes_split; lia). exact Hrm'. }
  destruct (Z_lt_ge_dec h 2) as [H1row|H2rows].
  { (* [comment removed for export] *)
    destruct (pm_B0 al_rom fx1 r3 m1 s na h ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (m16_8 na Hal) (NUMA_rd_n SEGS m1 na h h 1 arr RN)
                (W_sok_win C A1 m1 _ (s - 104) 8 CK HW1 ltac:(lia) ltac:(cbn; lia)) PR3 A10) as (r4 & RUN4 & PR4 & V10 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN4 |].
    set (M2 := wbytes m1 (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (Z_to_bv 64 na))).
    assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A (s + 16) m M2).
    { subst M2. apply (WP_win C A1 A m m1 _ _ _ (s + 16) CK (conj HW1 PMm1) SUB1); [rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia]. }
    destruct WP2 as [HW2 PM2].
    assert (OUT2 : forall x : word, ~ (s - 104 <= u x < s - 96)%Z -> M2 x = m1 x).
    { intros x Hx. subst M2. rewrite wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    destruct (pm_B1 al_rom fx1 r4 M2 s h ltac:(lia) PR4 V10) as (r5 & RUN5 & PR5 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN5 |].
    apply (pm_end fx1 C A A1 m md vm1 regs ret s na arr h M2 r5 S (kR - RK_numa)%Z (bR - RB_numa h)%Z CK Hs16
             ltac:(unfold NDS_STACK, ALLOC_STACK; lia) Hhi Hret HW2 PM2).
    - apply (numa_at_mem C A1 m1 M2 _ _ _ _ NA). intros x Hx. apply OUT2. lia.
    - subst M2. rewrite <- w2l_Z8 by lia. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
    - exact LnaA.
    - exact LarrA.
    - exact LQ1.
    - apply (pmcells_eq m1 M2); [lia | lia | intros x Hx; apply OUT2; lia | exact PC1].
    - exact PR5.
    - csr. reflexivity.
    - intros x Hx. rewrite <- (RR3 x Hx). unfold pm_rest in Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]). destruct Hx.
    - exact H2.
    - exact Hrm1.
    - intros A' m' vm' regs' HW' CS' PM' LQ' Hrm'. apply (KE fx1 A' m' vm' regs' Hz1 HW' CS' PM' LQ').
      pose proof (aroom_nonneg _ _ _ _ Hrm'). rewrite RB_nfe_val, RK_nfe_val in *. apply (aroom_mono _ _ _ _ _ _ Hrm'); lia. }
  (* [comment removed for export] *)
  destruct (pm_B al_rom fx1 r3 m1 s na h ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (m16_8 na Hal) (NUMA_rd_n SEGS m1 na h h 1 arr RN)
              (W_sok_win C A1 m1 _ (s - 104) 8 CK HW1 ltac:(lia) ltac:(cbn; lia)) PR3 ltac:(csr; reflexivity) A10)
    as (r4 & RUN4 & PR4 & V21 & V1 & V10 & V11 & V12 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN4 |].
  set (M2 := wbytes m1 (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (Z_to_bv 64 na))).
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A (s + 16) m M2).
  { subst M2. apply (WP_win C A1 A m m1 _ _ _ (s + 16) CK (conj HW1 PMm1) SUB1); [rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia]. }
  destruct WP2 as [HW2 PM2].
  assert (OUT2 : forall x : word, ~ (s - 104 <= u x < s - 96)%Z -> M2 x = m1 x).
  { intros x Hx. subst M2. rewrite wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (NA2 : numa_at C A1 M2 na h h arr) by (apply (numa_at_mem C A1 m1 M2 _ _ _ _ NA); intros x Hx; apply OUT2; lia).
  pose proof NA2 as (RN2 & _).
  destruct (blk_range C A1 M2 _ (Z_to_bv 64 arr) _ CK HW2 L2 ltac:(lia)) as [Gar Tar]. rewrite u_Z2bv in Gar, Tar by lia.
  assert (PCL2 : prof_cells SEGS M2 arr h 0 19999).
  { apply (prof_cells_mem m1 M2 arr h 0 19999 ltac:(lia) ltac:(lia) PCL1). intros x Hx. apply OUT2. lia. }
  destruct (PCL2 0%Z ltac:(lia)) as (pv0 & Hpv0 & NC0). unfold ncell in NC0.
  destruct (ngi_run al_rom fx1 r4 M2 na h h 1 arr 0 (s - 92) pv0 (Z_to_bv 64 0x82574) Hz1 RN2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(lia) ltac:(lia) (m16_4k s 92 Hs16 eq_refl) (m16_8 na Hal) (m16_4 arr Hala) Hpv0 NC0
              (W_ngi_c1 C A1 M2 _ HW2) (W_ngi_c2 C A1 M2 _ HW2) (W_ngi_c3 C A1 M2 _ HW2) (W_ngi_c4 C A1 M2 _ HW2)
              (W_sok_win C A1 M2 _ (s - 92) 4 CK HW2 ltac:(lia) ltac:(cbn; lia)) ltac:(red; apply bv_eq; reflexivity) V1 V10 V11 V12)
    as (fr5 & cs5 & r5 & RUN5 & Hz5 & W10 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN5 |].
  replace (Z_to_bv 64 0x82574) with (0x82574 : word) by (apply bv_eq; reflexivity).
  set (M3 := wbytes (wbytes M2 (Z_to_bv 64 (s - 92)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 92)) (word_to_le_bytes 4 (Z_to_bv 64 pv0))).
  assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A (s + 16) m M3).
  { subst M3. apply (WP_win C A1 A m _ _ _ _ (s + 16) CK); [| exact SUB1 | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia].
    apply (WP_win C A1 A m M2 _ _ _ (s + 16) CK (conj HW2 PM2) SUB1); [rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia]. }
  destruct WP3 as [HW3 PM3].
  assert (OUT3 : forall x : word, ~ (s - 104 <= u x < s - 88)%Z -> M3 x = m1 x).
  { intros x Hx. subst M3. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. apply OUT2. lia. }
  assert (PR5 : pm_R r5 s) by (apply (pm_R_of r4); [exact PR4 | intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]); destruct Hx]).
  destruct (pm_C al_rom (mkFP fr5 cs5) r5 M3 s PR5) as (r6 & RUN6 & PR6 & X22 & X23 & X24 & X25 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN6 |].
  apply (pm_loop (Z.to_nat (h - 1)) (mkFP fr5 cs5) C A A1 m md vm1 regs ret s na arr h 1 pv0 0 0 M3 r6 S Hz5 CK Hs16 ltac:(lia) Hhi HW3 PM3 SUB1).
  - apply (numa_at_mem C A1 m1 M3 _ _ _ _ NA). intros x Hx. apply OUT3. lia.
  - apply (prof_cells_mem m1 M3 arr h 0 19999 ltac:(lia) ltac:(lia) PCL1). intros x Hx. apply OUT3. lia.
  - subst M3. rewrite !rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia). subst M2. rewrite <- w2l_Z8 by lia. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
  - subst M3. rewrite <- (w2l_Z4 pv0) by lia. apply rdn_wbytes_hit4; rewrite u_Z2bv by lia; lia.
  - exact Hpv0.
  - lia.
  - lia.
  - apply (pmcells_eq m1 M3); [lia | lia | intros x Hx; apply OUT3; lia | exact PC1].
  - exact PR6.
  - csr. reflexivity.
  - exact X22.
  - exact X23.
  - exact X24.
  - exact X25.
  - lia.
  - lia.
  - rewrite Z2Nat.id by lia. reflexivity.
  - intros x Hx. rewrite <- (RR3 x Hx). unfold pm_rest in Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]). destruct Hx.
  - intros fx7 M7 r7 Hz7 HW7 PM7 NA7 Cna7 PC7 PR7 R21 RR7.
    apply (pm_tail fx7 C A A1 m md vm1 regs ret s na arr h M7 r7 S (kR - RK_numa)%Z (bR - RB_numa h)%Z Hz7 CK Hs16
             ltac:(unfold NFE_STACK, NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK; lia) Hhi Hret HW7 PM7 SUB1 NA7 ltac:(lia) Cna7 LnaA LarrA LQ1 PC7 PR7 RR7 H2 H4
             Hrm1 Hrk1 Hrb1 KE).
Qed.

End Main.

End EdgeW.
