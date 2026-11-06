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
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MallocTree () : Init.string Init.list := ["Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Heap.F_syscalls.asegs"; "AUXV_CELL"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Heap.MallocRep.wz"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u64s"; "auxv_list"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Heap.MallocRep.zeros"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Heap.Malloc.ALLOC_CEIL_LO"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.list"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.Frame.disjoint_from"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.Lib.Mem.wa"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "Corelib.Init.Datatypes.None"; "stdpp.bitvector.definitions.bv_unsigned"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Heap.MallocRep.CTX"; "Corelib.Numbers.BinNums.N"; "OSSVerify.KrLib.Heap.Malloc.region"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc.r_kind"; "OSSVerify.KrLib.Heap.MallocRep.lr_lo"; "OSSVerify.KrLib.Heap.Malloc.r_base"; "OSSVerify.KrLib.Heap.Malloc.round_up_pg"; "OSSVerify.KrLib.Heap.Malloc.r_len"; "fresh_addr"; "OSSVerify.KrLib.Heap.Malloc.s_reserved"; "OSSVerify.KrLib.Heap.Malloc.s_ceil"; "OSSVerify.KrLib.Heap.Malloc.rkind"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Heap.MallocRep.pw"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Cells.C4"; "auxv_ok"; "pres_except"; "alloc_fp"; "OSSVerify.KrLib.Heap.Malloc.RKGroup"; "OSSVerify.KrLib.Heap.MallocRep.mrep"; "OSSVerify.KrLib.Heap.MallocRep.ticks_ok"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "OSSVerify.KrLib.Heap.Prog.ps_m"; "OSSVerify.KrLib.Heap.Prog.ps_fa"; "Corelib.Init.Datatypes.unit"; "OSSVerify.KrLib.Heap.Prog.ps_so"; "am_rel"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.M"; "mem"; "OSSVerify.KrLib.Heap.Prog.PState"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "brk_link_ps"; "Stdlib.ZArith.BinInt.Z.sub"; "AM_STACK"; "am_post"; "implT"; "OSSVerify.KrLib.Heap.Malloc.alloc_meta"; "OSSVerify.KrLib.Heap.MallocRep.alloc_meta_entry"].


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem := word -> option byte.

Definition pans_mem (o : mem) (q : aptr) (caddr hint : Z) : Z :=
  match mrd asegs o (wa caddr) with Some b => bv_unsigned b | None => 0 end.
Definition pupd_mem (o : mem) (e : ev) (z : Z) : mem := o.

Lemma pans_mem_range : forall o q c h, 0 <= pans_mem o q c h < 256.
Proof.
  intros. unfold pans_mem. destruct (mrd asegs o (wa c)) as [b|]; [|lia].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Definition mrun {R} (o : mem) (t : Malloc.M R) : Malloc.M (mem * R) := prun pans_mem pupd_mem o t.

Lemma mrun_ret {R} o (r : R) : mrun o (SRet r) = SRet (o, r).
Proof. reflexivity. Qed.
Lemma mrun_peek {R} o p c h (k : Z -> Malloc.M R) : mrun o (SVis (EPeek p c h) k) = mrun o (k (pans_mem o p c h)).
Proof. reflexivity. Qed.
Lemma mrun_vis {R} o e (k : Z -> Malloc.M R) :
  match e with EPeek _ _ _ => False | _ => True end ->
  mrun o (SVis e k) = SVis e (fun z => mrun o (k z)).
Proof. intros He. destruct e; try reflexivity. destruct He. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Definition implT {R} (o : mem) (t : Malloc.M R) (s : PState)
           (Q : R -> PState -> machine_state -> Prop) (ms : machine_state) : Prop :=
  implM asegs (membed (mrun o t)) s (fun r s' ms' => Q (snd r) s' ms') ms.


Lemma implT_evt {R} o (t : Malloc.M R) s Q P ms :
  evt asegs P ms -> (forall ms', P ms' -> implT o t s Q ms') -> implT o t s Q ms.
Proof. intros H K. unfold implT in *. eapply implM_evt; eauto. Qed.


Lemma steq_sym {E A R} (t1 t2 : stree E A R) : steq t1 t2 -> steq t2 t1.
Proof. induction 1; constructor; auto. Qed.


(* [comment removed for export] *)
Lemma implT_from_evt {R} o (t : Malloc.M R) s Q ms :
  evt asegs (fun ms' => implT o t s Q ms') ms -> implT o t s Q ms.
Proof. intros H. eapply implT_evt; [exact H|]. intros ms' H'; exact H'. Qed.
Ltac iprefixT := apply implT_from_evt.


Definition mmap_val (a : mmap_ans) : Z := match a with MmErr e => neg_errno e | MmOk x => x end.
Definition fixed_val (addr : Z) (a : fixed_ans) : Z :=
  match a with FxKept e => neg_errno e | FxDone => addr | FxLost e => neg_errno e end.
Definition range_val (a : range_ans) : Z := match a with RgErr e => neg_errno e | RgDone _ => 0 end.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition leaf_of {R} (o : mem) (t : Malloc.M R) (r : R) : Prop :=
  exists ans o', follow (mrun o t) ans = Some (o', r).

Lemma leaf_of_ret {R} o (r : R) : leaf_of o (SRet r) r.
Proof. dexists [], o. reflexivity. Qed.

Lemma leaf_of_vis {R} o e (k : Z -> Malloc.M R) z r :
  match e with EPeek _ _ _ => False | EUndef _ => False | _ => True end ->
  leaf_of o (k z) r -> leaf_of o (SVis e k) r.
Proof.
  (intros He dd_H; ddestruct dd_H as (ans & o' & H)). dexists (z :: ans), o'. unfold mrun, prun. cbn [eruns].
  destruct e; cbn [psel]; try exact H; destruct He.
Qed.

Lemma leaf_of_peek {R} o p c h (k : Z -> Malloc.M R) r :
  leaf_of o (k (pans_mem o p c h)) r -> leaf_of o (SVis (EPeek p c h) k) r.
Proof. (intros dd_H; ddestruct dd_H as (ans & o' & H)). dexists ans, o'. rewrite mrun_peek. exact H. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ptr_rel (p : optr) (r : option bptr) : Prop :=
  match p, r with
  | None, None => True
  | Some pf, Some b => fst pf = fst (fst b) /\ exists off, snd pf = snd (fst b) + UNIT * off
  | _, _ => False
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AUXV_CELL : Z := LIBC + 8.

Definition auxv_list (x3 x4 x5 x6 x11 x12 x23 rnd : Z) : list word :=
  map wz [3; x3; 4; x4; 5; x5; 6; x6; 11; x11; 12; x12; 23; x23; 25; rnd; 0; 0].

Definition auxv_ok (m : mem) (B : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocTree ()) "(0.$1.Lav,$1.(0.$1.Lx3,$1.(0.$1.Lx4,$1.(0.$1.Lx5,$1.(0.$1.Lx6,$1.(0.$1.Lx11,$1.(0.$1.Lx12,$1.(0.$1.Lx23,$1.(0.$1.Lrnd,$1.(2.(3.$4.O2.$5.(6.$7.(8.(9.R9.))(:.$7.)))(2.(;.$4.O2.R9.(<.(=.R8.R7.R6.R5.R4.R3.R2.R1.)))(2.(;.$4.O2.(>.R1.+8.)(?.#8.))(2.(10.$11.O1.)(2.(10.O1.R9.)(2.(10.(>.R9.+90.)(12.+2.+40.))(2.(10.O1.(>.R1.+8.))(2.(10.(>.R1.+10.)(12.+2.+40.))(2.(2.(10.=R8.)(13.R8.(12.+2.+40.)))(2.(2.(10.=R7.)(13.R7.(12.+2.+40.)))(2.(2.(10.=R6.)(13.R6.(12.+2.+40.)))(2.(2.(10.=R5.)(13.R5.(12.+2.+40.)))(2.(2.(10.=R4.)(13.R4.(12.+2.+40.)))(2.(2.(10.=R3.)(13.R3.(12.+2.+40.)))(2.(2.(10.=R2.)(13.R2.(12.+2.+40.)))(2.(10.=R1.)(13.R1.(12.+2.+40.)))))))))))))))))))))))))))")
(* [comment removed for export] *).


Lemma Forall_disjoint_from : ltac2:(CDefT.buildp (gd_tbl_MallocTree ()) "PP,P,(14.$1.$1.)SpPW,(15.(14.$1.$1.))Pa,$1.Pn,$1.P,(16.(14.$1.$1.)R4.R3.)P,Plo,$1.Phi,$1.P,A1.R7.(17.$1.$1.R2.R1.)(18.(10.(>.R6.R5.)R3.)(10.R2.R6.))(19.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros P W a n F HP. induction F as [|[lo hi] W Hx F IH]; cbn; [exact I|]. split; [apply (HP _ _ Hx)| exact IH].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pres_except (C : Z -> Prop) (m m' : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocTree ()) "Pa,$1.P,(2.(10.=R1.)(13.R1.(12.+2.+40.)))P,(1:.A1.O3.R2.)(2.(1;.(1<.(1=.&8.))A1.O1.(1>.R3.)A1.O2.(1>.R3.))P,(1:.(1;.(1<.(1=.&8.))(1?.$4.O2.(1>.R3.))(20.(1=.&8.))))(1:.(1;.(1<.(1=.&8.))(1?.$4.O1.(1>.R4.))(20.(1=.&8.)))))")
(* [comment removed for export] *).


(* [comment removed for export] *)
Definition alloc_fp (K : rkind -> Prop) (st1 : mstate) (lo sp : Z) (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocTree ()) "(18.(2.(10.O3.O1.)(13.O1.O2.))(18.(2.(10.(>.(21.&40.(22.&40.+1:620.))-:4.)O1.)(13.O1.(>.(>.(21.&40.(22.&40.+1:620.))-:4.)+4.)))(18.(2.(10.$23.O1.)(13.O1.(>.$23.+3:0.)))(0.$24.Lrid,$24.(0.$25.Lr,$25.(2.(1;.(1<.$25.)(26.$24.$25.(27.$24.$28.$29.$25.)(2:.$24.$28.$29.$25.)R2.(2;.O4.))(2<.$25.R1.))(2.A1.O5.(2=.R1.)(2.(10.(2>.R1.)O1.)(13.O1.(>.(2?.R1.)(30.(31.R1.))))))))))))")
(* [comment removed for export] *).
  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition brk_link_ps (st : mstate) (s : PState) : Prop :=
  match c_brk (ctx st) with
  | BrkLive rid off => ps_brk s = conc st (rid, off)
  | _ => True
  end.

(* [comment removed for export] *)
Definition optr_in (P : N -> Prop) (p : optr) : Prop :=
  match p with Some q => P (fst q) | None => True end.

Definition ptrs_in (P : N -> Prop) (st : mstate) : Prop :=
  let c := ctx st in
  optr_in P (c_free_meta_head c) /\ optr_in P (c_avail_meta c) /\ optr_in P (c_meta_area_head c)
  /\ optr_in P (c_meta_area_tail c) /\ optr_in P (c_avail_meta_areas c)
  /\ (forall sc, optr_in P (active st sc))
  /\ match c_brk c with BrkLive rid _ => P rid | _ => True end
  /\ (forall g, optr_in P (m_prev (get_meta_rec st g)) /\ optr_in P (m_next (get_meta_rec st g))
             /\ optr_in P (m_mem (get_meta_rec st g)))
  /\ (forall a ar, (s_areas st) !! a = Some ar -> P (fst a) /\ optr_in P (a_next ar))
  /\ (forall b gh, (s_groups st) !! b = Some gh -> P (fst b) /\ optr_in P (g_meta gh)).

Lemma ptrs_in_mono (P P' : N -> Prop) st : (forall r, P r -> P' r) -> ptrs_in P st -> ptrs_in P' st.
Proof.
  (intros HP dd_H; ddestruct dd_H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10)).
  assert (OM : forall p, optr_in P p -> optr_in P' p) by (intros [q|]; cbn; auto).
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  split; [intros sc; apply OM, H6|]. split; [destruct (c_brk (ctx st)); auto|].
  split; [intros g; ddestruct (H8 g) as (X1 & X2 & X3); auto|].
  split; [intros a ar Ha; destruct (H9 a ar Ha); auto|].
  intros b gh Hb; destruct (H10 b gh Hb); auto.
Qed.

(* [comment removed for export] *)
Record am_rel (st st1 : mstate) (mo : optr) : Prop := mkAMR {
  amr_active : forall sc, active st1 sc = active st sc;
  amr_usage : forall sc, usage st1 sc = usage st sc;
  amr_bounces : forall i, bounces st1 i = bounces st i;
  amr_unmap_seq : forall i, unmap_seq st1 i = unmap_seq st i;
  amr_seq : c_seq (ctx st1) = c_seq (ctx st);
  amr_counter : c_mmap_counter (ctx st1) = c_mmap_counter (ctx st);
  amr_groups : s_groups st1 = s_groups st;
  amr_slots : s_slots st1 = s_slots st;
  amr_shadow : s_shadow st1 = s_shadow st;
  amr_tick : s_tick st1 = s_tick st;
  amr_reserved : s_reserved st1 = s_reserved st;
  (* [comment removed for export] *)
  amr_metas : forall g, Some g <> mo ->
      (m_mem (get_meta_rec st g) <> None \/ m_next (get_meta_rec st g) = None) ->
      get_meta_rec st1 g = get_meta_rec st g;
  (* [comment removed for export] *)
  amr_result : forall m, mo = Some m -> get_meta_rec st1 m = meta0 /\ meta_slot st1 m;
  (* [comment removed for export] *)
  amr_regions : forall rid r, (s_regions st) !! rid = Some r ->
      exists r', (s_regions st1) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r
                 /\ r_len r <= r_len r' /\ (r_kind r = RKGroup -> r' = r);
  amr_new : forall rid r', (s_regions st1) !! rid = Some r' -> (s_regions st) !! rid = None -> r_kind r' <> RKGroup;
  amr_next_rid : (s_next_rid st <= s_next_rid st1)%N;
  amr_areas : forall a, is_Some ((s_areas st) !! a) -> is_Some ((s_areas st1) !! a);
  (* [comment removed for export] *)
  amr_ptrs : forall P : N -> Prop,
      (forall rid r, (s_regions st1) !! rid = Some r -> r_kind r <> RKGroup -> P rid) ->
      ptrs_in P st -> ptrs_in P st1;
  (* [comment removed for export] *)
  amr_fresh : forall rid, (s_next_rid st1 <= rid)%N -> (s_regions st1) !! rid = None /\ (s_shadow st1) !! rid = (s_shadow st) !! rid
}.

Definition AM_STACK : Z := 128.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fresh_addr (st : mstate) (a : Z) : Prop :=
  a < s_ceil st /\ ranges_free (live_ranges st) a 1 = true.

Lemma ranges_free_In l a n b k : ranges_free l a n = true -> In (b, k) l -> a + n <= b \/ b + k <= a.
Proof.
  intros H HI. unfold ranges_free in H. apply (proj1 (forallb_forall _ _) H) in HI. cbn [fst snd] in HI.
  unfold iv_disjoint in HI. apply Bool.orb_prop in HI. destruct HI as [X|X]; apply Z.leb_le in X; lia.
Qed.

Lemma ranges_free_intro l a n : (forall b k, In (b, k) l -> a + n <= b \/ b + k <= a) -> ranges_free l a n = true.
Proof.
  intros H. unfold ranges_free. apply (proj2 (forallb_forall _ _)). intros [b k] HI. cbn [fst snd].
  unfold iv_disjoint. destruct (H b k HI) as [X|X]; [rewrite (proj2 (Z.leb_le _ _) X); reflexivity|].
  rewrite (proj2 (Z.leb_le _ _) X). apply Bool.orb_true_r.
Qed.

Lemma ranges_free_sub l a n a' n' : ranges_free l a n = true -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> ranges_free l a' n' = true.
Proof.
  intros H H1 H2 H3. apply ranges_free_intro. intros b k HI. pose proof (ranges_free_In l a n b k H HI). lia.
Qed.

Lemma In_live_ranges st rid r : (s_regions st) !! rid = Some r ->
  In (region_live_range r) (live_ranges st).
Proof.
  intros Hr. unfold live_ranges. apply in_or_app. right. apply in_map_iff. exists (rid, r). split; [reflexivity|].
  apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma fresh_live_region st a rid r : ltac2:(CDefT.buildp (gd_tbl_MallocTree ()) "P,(32.O4.O3.)P,(1;.(1<.$25.)(26.$24.$25.(27.$24.$28.$29.$25.)(2:.$24.$28.$29.$25.)O2.(2;.O4.))(2<.$25.O1.))(18.(10.(>.O3.+1.)(2>.O1.))(10.(>.(2?.O1.)(30.(31.O1.)))O3.))")
(* [comment removed for export] *).
Proof.
  intros [_ FR] Hr. pose proof (In_live_ranges st rid r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ FR HI); lia).
Qed.


(* [comment removed for export] *)
Lemma fresh_addr_anti st st' a : ltac2:(CDefT.buildp (gd_tbl_MallocTree ()) "P,(1;.(15.(14.$1.$1.))(33.O2.)(33.O3.))P,(1;.$1.(34.O2.)(34.O3.))P,Prid,$24.Pr,$25.P,(1;.(1<.$25.)(26.$24.$25.(27.$24.$28.$29.$25.)(2:.$24.$28.$29.$25.)R2.(2;.O3.))(2<.$25.R1.))(0.$25.Lr',$25.(2.(1;.(1<.$25.)(26.$24.$25.(27.$24.$28.$29.$25.)(2:.$24.$28.$29.$25.)R4.(2;.O2.))(2<.$25.R1.))(2.(1;.$35.(2=.R1.)(2=.R3.))(2.(1;.$1.(2?.R1.)(2?.R3.))(10.(31.R3.)(31.R1.))))))P,(32.O2.O1.)(32.O3.O1.)")
(* [comment removed for export] *).
Proof.
  intros RS RC HR [FC FR]. split; [rewrite <- RC; exact FC|]. apply ranges_free_intro. intros b k HI.
  unfold live_ranges in HI. apply in_app_or in HI. destruct HI as [HI|HI].
  - apply (ranges_free_In (live_ranges st') a 1 b k FR). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI.
  - apply in_map_iff in HI. ddestruct HI as ([rid r] & E & HI). cbn [snd] in E.
    apply (proj2 (list_elem_of_In _ _)) in HI. apply elem_of_map_to_list in HI.
    ddestruct (HR rid r HI) as (r' & Hr' & K' & B' & L').
    pose proof (In_live_ranges st' rid r' Hr') as HI'.
    assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
    { unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
    unfold region_live_range in HI', E. rewrite K', B' in HI'.
    destruct (r_kind r); inversion E; subst; (pose proof (ranges_free_In _ _ _ _ _ FR HI'); lia).
Qed.

Definition am_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (s : PState) (lo : Z) (m : mem)
    (st1 : mstate) (mo : optr) (s' : PState) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_MallocTree ()) "Lms',$36.(0.(1=.&40.)Lt0,(1=.&40.)(0.(1=.&40.)Lt1,(1=.&40.)(0.(1=.&40.)Lt2,(1=.&40.)(0.(1=.&40.)La1,(1=.&40.)(0.(1=.&40.)La2,(1=.&40.)(0.(1=.&40.)La3,(1=.&40.)(0.(1=.&40.)La4,(1=.&40.)(0.(1=.&40.)La5,(1=.&40.)(0.(1=.&40.)La6,(1=.&40.)(0.(1=.&40.)La7,(1=.&40.)(0.(1=.&40.)Lt3,(1=.&40.)(0.(1=.&40.)Lt4,(1=.&40.)(0.(1=.&40.)Lt5,(1=.&40.)(0.(1=.&40.)Lt6,(1=.&40.)(0.P,(1=.&40.)(1<.(1=.&8.))Lm',P,(1=.&40.)(1<.(1=.&8.))(0.(1=.&40.)Lerrv',(1=.&40.)(2.(1;.$36.R11.(37.(38.O19.O18.O17.O16.R10.R?.R>.O15.O14.(39.O3.O2.)R=.R<.R;.R:.R9.R8.R7.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R6.R5.R4.R3.)O9.(3:.O19.)O8.(20.(1=.&40.))R2.(3;.$4.)))(2.(3<.$4.R2.)(2.(3=.$4.R2.O5.(21.&40.O18.))(2.(3.$4.R2.(>.(21.&40.O16.)-:4.)(6.$7.(3>.R1.)(:.$7.)))(2.(3?.R2.(21.&40.O18.))(2.(40.La,$1.(18.(41.Lk,$35.(1:.(1;.$35.R1.$42.))O3.O5.(21.&40.O18.)R1.)(32.O7.R1.))O4.R2.)(2.(43.O3.R2.)(2.(44.O3.)(2.(1;.$45.(46.O1.)(46.O6.))(2.(1;.(14.$1.$1.)(47.O1.)(47.O6.))(2.(1;.$48.(49.O1.)(49.O6.))(4:.O7.O3.O2.))))))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition alloc_meta_stmt (am_pre : mstate -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocTree ()) "PR,StPk,P,$45.P,$4;.(4<.R3.)Pbail,(4<.R2.)Po,$4=.Ps,$4>.PQ,P,R5.P,$4>.P,$36.SpPra,(1=.&40.)Psp,(1=.&40.)Pgp,(1=.&40.)Ptp,(1=.&40.)Pt0,(1=.&40.)Pt1,(1=.&40.)Pt2,(1=.&40.)Ps0,(1=.&40.)Ps1,(1=.&40.)Pa0,(1=.&40.)Pa1,(1=.&40.)Pa2,(1=.&40.)Pa3,(1=.&40.)Pa4,(1=.&40.)Pa5,(1=.&40.)Pa6,(1=.&40.)Pa7,(1=.&40.)Ps2,(1=.&40.)Ps3,(1=.&40.)Ps4,(1=.&40.)Ps5,(1=.&40.)Ps6,(1=.&40.)Ps7,(1=.&40.)Ps8,(1=.&40.)Ps9,(1=.&40.)Ps10,(1=.&40.)Ps11,(1=.&40.)Pt3,(1=.&40.)Pt4,(1=.&40.)Pt5,(1=.&40.)Pt6,(1=.&40.)PF,(4?.&5.(1=.&40.))Pfc,(1=.&20.)Pm,$4=.Pst,$45.Plo,$1.Perrv,(1=.&40.)P,A1.O1.R3.P,(43.R4.R5.)P,(44.R5.)P,(50.R6.R2:.)P,(3?.R8.(21.&40.R28.))P,(3=.$4.R9.R7.(21.&40.R29.))P,(10.(34.R9.)R8.)P,(10.R9.(51.(21.&40.R2;.)$52.))P,(3.$4.R<.(>.(21.&40.R2:.)-:4.)(6.$7.(3>.R9.)(:.$7.)))P,(3<.$4.R=.)P,(1;.(1=.&40.)R2=.(22.&40.+1:800.))P,(1;.(1=.&40.)R2=.(22.&40.+1:620.))P,Pst1,$45.Pmo,$4;.Ps',$4>.Pms',$36.P,(53.R35.R34.R33.R32.R2>.R2=.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R16.R15.R13.R37.R12.R14.R4.R3.R2.R1.)P,(50.R5.R3.)(54.R3=.R3:.A2.R3<.R6.R5.R4.R38.R3.)(54.R38.R35.(55.R38.R10.R37.R36.)R34.R33.(37.(38.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R13.(22.&40.$56.)R12.(20.(1=.&40.))R11.(3;.$4.)))")
(* [comment removed for export] *).
