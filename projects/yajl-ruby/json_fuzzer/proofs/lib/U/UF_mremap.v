(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac SysStep ITree Nodes Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import F_mm_syscalls.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UF_syscalls UMallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Malloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition rmremap_entry : Z := 0x1a054.

(* [comment removed for export] *)
Definition mremap_mem (a : mremap_ans) (old osz nsz : Z) (m2 : word -> option byte) : word -> option byte :=
  match a with
  | MrErr _ => m2
  | MrSame => if osz =? nsz then m2
              else if nsz <? osz then apply_unmaps m2 [(wa (old + nsz), Z_to_bv 64 (osz - nsz))]
              else apply_zeros m2 [(wa (old + osz), Z_to_bv 64 (nsz - osz))]
  | MrMoved d => apply_copy m2 (apply_zeros (apply_unmaps m2 [(wa old, Z_to_bv 64 osz)]) [(wa (d + osz), Z_to_bv 64 (nsz - osz))])
                            (mkCopy (wa old) (wa d) (Z_to_bv 64 osz))
  end.

Definition mremap_ret (a : mremap_ans) (old : Z) : word :=
  match a with MrErr _ => Z_to_bv 64 (-1) | MrSame => Z_to_bv 64 old | MrMoved d => Z_to_bv 64 d end.

Definition mremap_errno (a : mremap_ans) (errv : word) : word :=
  match a with MrErr e => Z_to_bv 64 e | _ => errv end.

(* [comment removed for export] *)
Definition mremap_good (old osz nsz : Z) (a : mremap_ans) : Prop :=
  match a with
  | MrErr _ => True
  | MrSame => osz < nsz -> old + nsz <= alloc_ceiling /\ (old + nsz <= 0x10000 \/ 0x57000 <= old + osz)
  | MrMoved d => (d + nsz <= 0x10000 \/ 0x57000 <= d) /\ (old + osz <= d \/ d + nsz <= old)
  end.

(* [comment removed for export] *)
Definition mremap_decoded (old osz nsz : Z) (a : mremap_ans) : Prop :=
  match a with
  | MrErr e => 1 <= e <= 4095
  | MrSame => True
  | MrMoved d => osz < nsz /\ mremap_dst_ok nsz [] old d = true
  end.

Definition rmremap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (old osz nsz : Z) (errv canary : word) (lo : Z) (m : word -> option byte) (a : mremap_ans)
    : machine_state -> Prop :=
  fun ms' => mremap_decoded old osz nsz a /\ (mremap_good old osz nsz a ->
    exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (mremap_ret a old) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None (mremap_mem a old osz nsz m2) (seg_rom usegs)
        /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m2
        /\ wmono usegs m m2 /\ mem_inv usegs m2
        /\ stk usegs m2 lo (bv_unsigned sp)
        /\ rw_cells usegs m2 (errno_addr tp) [C4 (mremap_errno a errv)]
        /\ rw_cells usegs m2 RGOT_SSP [C8 (wz RSSP_GUARD)]
        /\ rw_cells usegs m2 RSSP_GUARD [C8 canary]
        /\ match a with
           | MrErr e => 1 <= e <= 4095
           | MrSame => True
           | MrMoved d => osz < nsz /\ mremap_dst_ok nsz [] old d = true
           end).

Lemma rmremap_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (old osz nsz : Z) (errv canary : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  rw_cells usegs m RGOT_SSP [C8 (wz RSSP_GUARD)] ->
  rw_cells usegs m RSSP_GUARD [C8 canary] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 old -> a1 = Z_to_bv 64 osz -> a2 = Z_to_bv 64 nsz -> a3 = Z_to_bv 64 1 ->
  0 < old -> 0 < osz -> old + osz <= alloc_ceiling -> (old + osz <= 0x10000 \/ 0x57000 <= old) ->
  0 < nsz < 2^63 - 1 ->
  lo <= bv_unsigned sp - 112 -> alloc_ceiling <= lo ->
  tp = Z_to_bv 64 RATP ->
  impl usegs (at_node usegs) (enode (NMremap old osz nsz 1) (dec_mremap old osz nsz []))
       (epost (rmremap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc old osz nsz errv canary lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmremap_entry) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST ERR GOT SSP MI -> -> -> -> OLD0 OSZ0 OC IMG NSZ LO CEIL TP.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold alloc_ceiling in CEIL, OC.
  assert (ETP : bv_unsigned tp = 0x356a0) by (rewrite TP; unfold RATP; apply unsigned_lit; lia).
  unfold RGOT_SSP, RSSP_GUARD in *.
  unfold rmremap_entry. apply impl_enode.
  carve_frame 96%nat ST.
  do 7 step.
  (* [comment removed for export] *)
  do 6 step. change (wz 350480) with (Z_to_bv 64 350480) at 1. do 4 step.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. cbn in K0. lia. }
  clear K0.
  (* [comment removed for export] *)
  step. step. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. } clear K1.
  (* [comment removed for export] *)
  step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_mremap_Some in Hdec.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  destruct ans as [e| |d].
  - (* [comment removed for export] *)
    destruct Hdec as [-> He]. unfold efferr, eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    (* [comment removed for export] *)
    step. step. step. step.
    if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    do 9 step. release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold rmremap_post. split; [exact He|]. intros _. do 15 eexists.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact ERR|].
    split; [assumption|]. split; [assumption|]. exact He.
  - (* [comment removed for export] *)
    pose proof FR as FR0. pose proof ST as ST0. release_frame FR0 ST0 (bv_unsigned sp).
    (* [comment removed for export] *)
    assert (EPI : forall mX,
      rw_cells usegs mX (bv_unsigned sp + -96)
        [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk)))))));
         C8 canary; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra; C8 a4; C8 a5; C8 a6; C8 a7] ->
      rw_cells usegs mX 350480 [C8 canary] -> mem_inv usegs mX ->
      mX = mremap_mem MrSame old osz nsz m0 ->
      evt usegs (rmremap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc old osz nsz errv canary lo m MrSame)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 147568) t1 t2 (Z_to_bv 64 (-1)) (Z_to_bv 64 350480)
                 (Z_to_bv 64 old) (Z_to_bv 64 osz) (Z_to_bv 64 nsz) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 9223372036854775807) a6 (Z_to_bv 64 216)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1a0ec) fc None mX (seg_rom usegs))).
    { intros mX FRX SSPX MIX EmX.
      step. step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
      step. step. step. step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
      do 9 step.
      apply evt_done. unfold rmremap_post. split; [exact I|]. intros _. do 14 eexists. exists m0.
      split; [rewrite EmX; cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST0|]. split; [exact ERR|].
      split; [exact GOT|]. split; [exact SSP|]. exact I. }
    unfold mkR in EPI.
    destruct Hdec as [[Eq ->] | [[LT ->] | [GT ->]]].
    + (* [comment removed for export] *)
      unfold eff0. sys_nret. apply EPI; [exact FR| exact SSP| exact MI|].
      unfold mremap_mem. rewrite (proj2 (Z.eqb_eq _ _) Eq). reflexivity.
    + (* [comment removed for export] *)
      sys_nret_raw.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m' := mm) end.
      assert (Hza : 0 <= old + nsz < 2^64) by lia. assert (Hzn : 0 <= osz - nsz < 2^64) by lia. assert (Hzan : old + nsz + (osz - nsz) <= 2^64) by lia.
      apply EPI.
      * apply (rw_cells_unmaps_other usegs _ _ _ Hza Hzn Hzan _ _ FR). cbn; lia.
      * apply (rw_cells_unmaps_other usegs _ _ _ Hza Hzn Hzan _ _ SSP). cbn; lia.
      * apply (mem_inv_unmaps _ _ _ _ Hza Hzn Hzan MI).
      * unfold mremap_mem. replace (osz =? nsz) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (nsz <? osz) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    + (* [comment removed for export] *)
      sys_nret_raw.
      destruct (Z_le_dec (old + nsz) alloc_ceiling) as [GC|GC].
      2:{ apply evt_done. unfold rmremap_post. split; [exact I|]. intros G. exfalso. destruct (G GT) as [G1 _]. exact (GC G1). }
      assert (GI : {old + nsz <= 0x10000 \/ 0x57000 <= old + osz} + {~ (old + nsz <= 0x10000 \/ 0x57000 <= old + osz)}).
      { destruct (Z_le_dec (old + nsz) 0x10000); [left; lia|]. destruct (Z_le_dec 0x57000 (old + osz)); [left; lia|]. right; lia. }
      destruct GI as [GI|GI].
      2:{ apply evt_done. unfold rmremap_post. split; [exact I|]. intros G. exfalso. destruct (G GT) as [_ G2]. exact (GI G2). }
      unfold alloc_ceiling in GC.
      assert (Hza : 0 <= old + osz < 2^64) by lia. assert (Hzn : 0 <= nsz - osz < 2^64) by lia. assert (Hzan : old + osz + (nsz - osz) <= 2^64) by lia.
      apply EPI.
      * apply (rw_cells_zeros_other usegs _ _ _ Hza Hzn Hzan _ _ FR). cbn; lia.
      * apply (rw_cells_zeros_other usegs _ _ _ Hza Hzn Hzan _ _ SSP). cbn; lia.
      * apply (mem_inv_zeros _ _ _ _ Hza Hzn Hzan MI). intros x Hx. apply ref_ro_addr_false. lia.
      * unfold mremap_mem. replace (osz =? nsz) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (nsz <? osz) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - (* [comment removed for export] *)
    destruct Hdec as (GT & DOK & ->).
    pose proof (mremap_dst_ok_true _ _ _ _ DOK) as ((DAL & D0 & DC & DNE) & _). unfold alloc_ceiling in DC.
    pose proof FR as FR0. pose proof ST as ST0. release_frame FR0 ST0 (bv_unsigned sp).
    rewrite nret_MSsvc_gen; rewrite ?mkR_set_a0; simp_regs.
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4)%bv _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word)%bv with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
    end.
    pose proof (apply_mem_mremap_move m0 old osz d nsz) as AMM. unfold wa in AMM. rewrite AMM. clear AMM.
    assert (GI : {mremap_good old osz nsz (MrMoved d)} + {~ mremap_good old osz nsz (MrMoved d)}).
    { unfold mremap_good.
      destruct (Z_le_dec (old + osz) d) as [A1|A1]; [| destruct (Z_le_dec (d + nsz) old) as [A2|A2]; [| right; lia]].
      all: destruct (Z_le_dec (d + nsz) 0x10000); [left; lia|]; destruct (Z_le_dec 0x57000 d); [left; lia| right; lia]. }
    destruct GI as [[G1 G2]|GI].
    2:{ apply evt_done. unfold rmremap_post. split; [split; [exact GT| exact DOK]|]. intros G. exfalso. exact (GI G). }
    assert (Hold : 0 <= old) by lia. assert (Hon : old + osz <= 2^64) by lia. assert (Hd : 0 <= d) by lia. assert (Hdn : d + nsz <= 2^64) by lia.
    pose proof (rw_cells_mremap_other usegs m0 old osz d nsz Hold OSZ0 Hon Hd GT Hdn G2 _ _ FR ltac:(cbn; lia) ltac:(cbn; lia)) as FRX.
    pose proof (rw_cells_mremap_other usegs m0 old osz d nsz Hold OSZ0 Hon Hd GT Hdn G2 _ _ SSP ltac:(cbn; lia) ltac:(cbn; lia)) as SSPX.
    pose proof (mem_inv_mremap usegs m0 old osz d nsz Hold OSZ0 Hon Hd GT Hdn G2 MI ltac:(intros x Hx; apply ref_ro_addr_false; lia)) as MIX.
    unfold wa in FRX, SSPX, MIX.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m' := mm) in * end.
    clear FR ST. assert (Em : m' = mremap_mem (MrMoved d) old osz nsz m0) by reflexivity. clearbody m'.
    step. step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
    step. step. step. step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    do 9 step.
    apply evt_done. unfold rmremap_post. split; [split; [exact GT| exact DOK]|]. intros _. do 14 eexists. exists m0.
    split; [rewrite <- Em; cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST0|]. split; [exact ERR|].
    split; [exact GOT|]. split; [exact SSP|]. split; [exact GT| exact DOK].
Qed.
End RC__1.
