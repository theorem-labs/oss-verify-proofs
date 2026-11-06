(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A F_mm_syscalls.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_AB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface F_malloc_bigw F_malloc_big.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W10 ASlot_W11 ASlot_W14 ASlot_W15 ASlot_W16 ASlot_W17 ASlot_W18 ASlot_I ASlot_M0 ASlot_M2 ASlot_M3 ASlot_M4P.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require MallocFacts_inv4.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ASlot_M4 () : Init.string Init.list := ["Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.m_next"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "OSSVerify.KrLib.Heap.Malloc.m_prev"; "OSSVerify.KrLib.Heap.Malloc.active"; "OSSVerify.KrLib.Heap.Malloc.M"; "OSSVerify.KrLib.Heap.Malloc.ag_tail"; "OSSVerify.KrLib.Heap.Malloc.full_lay"; "OSSVerify.KrLib.Heap.ASlot_I.as_kq"; "OSSVerify.KrLib.Heap.ASlot_W14.st_model"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.ASlot_W16.mm_final"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Heap.Malloc.round_up_pg"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Heap.Malloc.mctx"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "OSSVerify.KrLib.Heap.Malloc.step_seq"; "OSSVerify.KrLib.Heap.Malloc.account_bounce"; "OSSVerify.KrLib.Heap.Malloc.upd_ctx"; "stdpp.gmap.gmap"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.Z_countable"; "OSSVerify.KrLib.Heap.Malloc.c_active"; "OSSVerify.KrLib.Heap.Malloc.c_usage"; "OSSVerify.KrLib.Heap.Malloc.brkstate"; "OSSVerify.KrLib.Heap.Malloc.c_brk"; "OSSVerify.KrLib.Heap.Malloc.c_mmap_counter"; "OSSVerify.KrLib.Heap.Malloc.c_free_meta_head"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta"; "OSSVerify.KrLib.Heap.Malloc.c_secret"; "OSSVerify.KrLib.Heap.Malloc.c_init_done"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta_count"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta_area_count"; "OSSVerify.KrLib.Heap.Malloc.c_meta_alloc_shift"; "OSSVerify.KrLib.Heap.Malloc.c_meta_area_head"; "OSSVerify.KrLib.Heap.Malloc.c_meta_area_tail"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta_areas"; "OSSVerify.KrLib.Heap.Prog.PState"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "OSSVerify.KrLib.Heap.ASlot_I.as_post2"; "OSSVerify.KrLib.Heap.MallocTree.implT"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section MMEQ.
Context {R : Type}.
Variables (sc req : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

Definition mm_after (st2 : mstate) (m : aptr) (c nd : Z) : Z -> Malloc.M R :=
  let size := UNIT * size_class sc in
  let st1 := step_seq (account_bounce sc st2) in
  fun r =>
        if negb (mmap_answer_ok (s_ceil st1) (live_ranges st1) nd r) then bad_answer bail else
        if is_err r then free_meta m st1 (fun st2 => as_kq sc k bail st2 None) bail
        else
          let '(st2, rid) := new_region RKGroup r nd st1 in
          let st3 := upd_meta m (m_set_maplen (Z.shiftr nd 12)) st2 in
          let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
          let ai := (4096 - UNIT) / size - 1 in
          let ai := if c - 1 <? ai then c - 1 else ai in
          let ai := if ai <? 0 then 0 else ai in
          ag_tail full_lay st4 sc m (rid, 0) c ai (as_kq sc k bail).

#[using="Type"] Lemma ag_mmap_eq st2 m cnt :
  ag_mmap sc req k bail st2 m cnt =
  (let '(c, nd) := mm_final (UNIT * size_class sc) req (mm_usage1 (step_seq (account_bounce sc st2)) sc (usage st2 sc))
                              (mm_cnt_red sc (UNIT * size_class sc) cnt (mm_usage1 (step_seq (account_bounce sc st2)) sc (usage st2 sc)) (is_bouncing sc st2))
                              (is_bouncing sc st2) in
   SVis (EMmap 0 nd PROT_RW (MAP_PRIVATE + MAP_ANON)) (mm_after st2 m c nd)).
Proof. reflexivity. Qed.
End MMEQ.

Section TAILEQ.
Context {R : Type}.
Variables (sc : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
#[using="Type"] Lemma ag_tail_kq_eq stT mm p c ai : ltac2:(CDefT.buildp (gd_tbl_ASlot_M4 ()) "P,(0.$1.(2.(3.O5.O4.))(4.$5.))P,(0.$1.(6.(3.O5.O4.))(4.$5.))P,(0.$1.(7.O5.Vsc,)(4.$5.))(0.(8.VR,)(9.VR,$:.O5.Vsc,O4.O3.O2.O1.(;.VR,Vsc,Vk,Vbail,))A2.Vk,(<.O5.Vsc,O2.O1.O4.O3.)=)")
(* [comment removed for export] *).
Proof.
  intros HN HP HA. unfold ag_tail, as_kq. cbv zeta. cbn [lh_hdr full_lay].
  rewrite as_queue_eq.
  2:{ unfold upd_meta, add_slots. rewrite get_meta_rec_put_same. cbn [m_next m_set_avail].
      rewrite rec_set_slots, rec_put_group, get_meta_rec_put_same. cbn [m_next m_prev m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
      rewrite rec_set_usage, rec_hdr_havoc. exact HN. }
  2:{ unfold upd_meta, add_slots. rewrite get_meta_rec_put_same. cbn [m_prev m_set_avail].
      rewrite rec_set_slots, rec_put_group, get_meta_rec_put_same. cbn [m_next m_prev m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
      rewrite rec_set_usage, rec_hdr_havoc. exact HP. }
  unfold as_queue_st. cbn [get_head].
  match goal with |- context [active ?X sc] => replace (active X sc) with (active stT sc) by reflexivity end.
  rewrite HA. unfold as_fm_single, st_model. cbn [set_head]. reflexivity.
Qed.
End TAILEQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mm_cnt_red_range sc size cnt u1 nos : 1 <= cnt <= 32 -> 1 <= mm_cnt_red sc size cnt u1 nos <= 32.
Proof.
  intros H. unfold mm_cnt_red.
  destruct (_ && _); [|lia]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); lia.
Qed.

Lemma round_up_pg_props x : 0 <= x -> x <= round_up_pg x < x + 4096 /\ round_up_pg x mod 4096 = 0.
Proof.
  intros Hx. unfold round_up_pg. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma mm_final_props size req u1 cnt nos c nd : ltac2:(CDefT.buildp (gd_tbl_ASlot_M4 ()) "P,(=.(>.+1.O4.)(>.O4.+20.))P,(>.+10.O7.)P,(>.=O6.)P,(>.(?.O6.+4.)O7.)P,(0.(10.$11.$11.)(12.O7.O6.O5.O4.O3.)(13.$11.$11.O2.O1.))(=.(=.(>.+1.O2.)(>.O2.O4.))(=.(0.$11.(14.O1.+1000.)=)(=.(>.(?.O6.+14.)O1.)(15.(=.(0.$11.O2.+1.)(0.$11.O1.(16.(?.O6.+14.))))(=.(>.(?.(17.O7.O2.)+10.)O1.)(0.$11.O1.(16.(?.(17.O7.O2.)+10.))))))))")
(* [comment removed for export] *).
Proof.
  intros HC HS HR HF E. unfold mm_final, mm_small in E. cbv zeta in E.
  pose proof (round_up_pg_props (req + 20) ltac:(lia)) as [R1 R2].
  pose proof (round_up_pg_props (size * cnt + 16) ltac:(nia)) as [N1 N2].
  change (req + IB + UNIT) with (req + 4 + 16) in E. replace (req + 4 + 16) with (req + 20) in E by lia.
  change (size * cnt + UNIT) with (size * cnt + 16) in E.
  destruct (negb nos && (cnt <=? 7)).
  - destruct (Z.ltb_spec (round_up_pg (req + 20)) (size + UNIT)) as [L|G]; cbn [orb] in E.
    + inversion E; subst. unfold UNIT in L. split; [lia|]. split; [lia|]. split; [lia|]. left; auto.
    + destruct ((4 * PGSZ <=? round_up_pg (req + 20)) && (u1 <? 2 * cnt)).
      * inversion E; subst. unfold UNIT in G. split; [lia|]. split; [lia|]. split; [lia|]. left; auto.
      * inversion E; subst. split; [lia|]. split; [lia|]. split; [nia|]. right; split; [nia| reflexivity].
  - inversion E; subst. split; [lia|]. split; [lia|]. split; [nia|]. right; split; [nia| reflexivity].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stS_shape sc st2 : ltac2:(CDefT.buildp (gd_tbl_ASlot_M4 ()) "(18.P,$19.$19.Lf,P,$19.$19.(=.(0.$1:.(1;.(1<.O2.O1.))(1=.R1.O1.))Pc,$19.(=.(0.(1>.$11.$1?.$20.$5.)(21.A1.R2.R1.)(21.R1.))(=.(0.(1>.$11.$1?.$20.$11.)(22.A1.R2.R1.)(22.R1.))(=.(0.$23.(24.A1.R2.R1.)(24.R1.))(=.(0.$11.(25.A1.R2.R1.)(25.R1.))(=.(0.$1.(26.A1.R2.R1.)(26.R1.))(=.(0.$1.(27.A1.R2.R1.)(27.R1.))(=.(0.$11.(28.A1.R2.R1.)(28.R1.))(=.(0.$11.(29.A1.R2.R1.)(29.R1.))(=.(0.$11.(2:.A1.R2.R1.)(2:.R1.))(=.(0.$11.(2;.A1.R2.R1.)(2;.R1.))(=.(0.$11.(2<.A1.R2.R1.)(2<.R1.))(=.(0.$1.(2=.A1.R2.R1.)(2=.R1.))(=.(0.$1.(2>.A1.R2.R1.)(2>.R1.))(0.$1.(2?.A1.R2.R1.)(2?.R1.)))))))))))))))))")
(* [comment removed for export] *).
Proof.
  assert (AB : exists g, account_bounce sc st2 = upd_ctx g st2 /\ forall c, g c = c \/ exists v, g c = set_bounces_map (<[sc - 7 := v]> (c_bounces c)) c).
  { unfold account_bounce, set_bounce.
    destruct (sc_in_seq_range sc); [| exists (fun c => c); split; [destruct st2; reflexivity| intros; left; reflexivity]].
    destruct (negb _ && _); [| exists (fun c => c); split; [destruct st2; reflexivity| intros; left; reflexivity]].
    destruct (_ <? 100); (eexists; split; [reflexivity| intros c; right; eexists; reflexivity]). }
  ddestruct AB as (g & EG & HG).
  rewrite step_seq_eq. rewrite EG.
  destruct (c_seq (ctx (upd_ctx g st2)) =? 255).
  - exists (fun c => set_seq 1 (set_unmap_seq_map ∅ (g c))). split; [destruct st2; reflexivity|].
    intros c. destruct (HG c) as [E|[v E]]; rewrite E; repeat split; reflexivity.
  - exists (fun c => set_seq (c_seq (g c) + 1) (g c)). split; [destruct st2; reflexivity|].
    intros c. destruct (HG c) as [E|[v E]]; rewrite E; repeat split; reflexivity.
Qed.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_ok m (bv_unsigned sp).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CLO : ALLOC_CEIL_LO <= lo.   (* [comment removed for export] *)
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis MED : rw_cells asegs m MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : ltac2:(CDefT.buildp (gd_tbl_ASlot_M4 ()) "Pst1,$1:.Pidx,$11.Ps',$30.Pms',$31.P,(32.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vo,Vm,Vst0,Vst,Vs,Vlo,Vsc,Vreq,R4.R3.R2.R1.)(33.VR,Vo,A2.Vk,R5.R4.R3.VQ,R2.)")
(* [comment removed for export] *).
Let F0 : ISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Variable am_pre : mstate -> Prop.
Hypothesis AM : alloc_meta_stmt am_pre.
Hypothesis AMP : AMP_AS am_pre.


End LEVEL.
