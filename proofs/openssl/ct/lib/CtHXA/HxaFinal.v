(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Malloc Prog ApState ApOwner.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require CtOwner.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow SegRw.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs D_cs D_libiface D_libkit RT_main_clx.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxImg HxQuery HxLearn.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HXS Require Import HxsStep HxsStepSound HxsHookSound HxsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXS Require Import HxsHookCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXA Require Import HxaInit HxaImage HxaInv HxaHooks HxaHk HxaHkDefs HxaHkRelease HxaRun HxaIface HxaHandoffImg HxaMain HxaQuery.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import BnHeapA LibKitA BnRepDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface LibaAp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition T_MK : int := 52.
Definition T_SA : int := 54.
Definition T_ND : int := 56.
Definition T_ES : int := 3772.
Definition T_XL : int := 3290.
Definition T_OL : int := 36.
Definition Q_memset_func : query := Q 6 5958624 0 160 (kbs_Z 8 0x1c29c8).   (* [comment removed for export] *)
Definition Q_malloc_impl : query := Q 6 5958624 0 32 (kbs_Z 8 0x1fce24).   (* [comment removed for export] *)
Definition Q_free_impl : query := Q 6 5958624 0 96 (kbs_Z 8 0x1fd334).   (* [comment removed for export] *)
Definition Q_no_customize : query := Q 8 12207808 0 1536 (kbs_Z 1 0x1).   (* [comment removed for export] *)
Definition Q_realloc_impl : query := Q 6 5958624 0 64 (kbs_Z 8 0x1fd224).   (* [comment removed for export] *)
Definition Q_master_once : query := Q 8 12207808 0 832 (kbs_Z 4 0x2).   (* [comment removed for export] *)
Definition Q_master_init : query := Q 8 12207808 0 896 (kbs_Z 1 0x1).   (* [comment removed for export] *)
Definition Q_master_key : query := Q 8 12207808 0 864 (kbs_Z 4 0x3).   (* [comment removed for export] *)
Definition Q_dc_inited : query := Q 8 12207808 0 928 (kbs_Z 1 0x1).   (* [comment removed for export] *)
Definition Q_dc_key : query := Q 8 12207808 0 1376 (kbs_Z 4 0x4).   (* [comment removed for export] *)
Definition Q_dc_once1 : query := Q 8 12207808 0 1472 (kbs_Z 4 0x2).   (* [comment removed for export] *)
Definition Q_dc_once1_ret : query := Q 8 12207808 0 1504 (kbs_Z 4 0x1).   (* [comment removed for export] *)
Definition Q_dc_once2 : query := Q 8 12207808 0 1408 (kbs_Z 4 0x2).   (* [comment removed for export] *)
Definition Q_dc_once2_ret : query := Q 8 12207808 0 1440 (kbs_Z 4 0x1).   (* [comment removed for export] *)
Definition Q_dc_exlock : query := Q 8 12207808 0 968 (kbs_ptr T_XL).   (* [comment removed for export] *)
Definition Q_dc_exmeth_bio : query := Q 8 12207808 0 1072 (kbs_Z 8 0x0).   (* [comment removed for export] *)
Definition Q_dc_conf_diag : query := Q 8 12207808 0 1284 (kbs_Z 4 0x0).   (* [comment removed for export] *)
Definition Q_stopped : query := Q 8 12207808 0 64 (kbs_Z 1 0x0).   (* [comment removed for export] *)
Definition Q_base_once : query := Q 8 12207808 0 256 (kbs_Z 4 0x2).   (* [comment removed for export] *)
Definition Q_base_ret : query := Q 8 12207808 0 288 (kbs_Z 4 0x1).   (* [comment removed for export] *)
Definition Q_in_init_key : query := Q 8 12207808 0 160 (kbs_Z 4 0x2).   (* [comment removed for export] *)
Definition Q_optsdone_lock : query := Q 8 12207808 0 96 (kbs_ptr T_OL).   (* [comment removed for export] *)
Definition Q_tsd_dc_slot : query := Q 15 12363680 0 24 (kbs_Z 8 0x0).   (* [comment removed for export] *)
Definition Q_tsd_mk_slot : query := Q 15 12363680 0 16 (kbs_ptr T_MK).   (* [comment removed for export] *)
Definition Q_tsd_used : query := Q 10 12227418 0 0 (kbs_any 1).   (* [comment removed for export] *)
Definition Q_conf_meth8 : query := Q 6 5958624 0 392 (kbs_Z 8 0x265200 ++ kbs_Z 8 0x2652a8 ++ kbs_Z 8 0x265348).   (* [comment removed for export] *)
Definition Q_conf_meth72 : query := Q 6 5958624 0 456 (kbs_Z 8 0x266d58).   (* [comment removed for export] *)
Definition Q_cancelbuf : query := Q 11 12227472 0 0 (kbs_any 8).   (* [comment removed for export] *)
Definition Q_base_inited : query := Q 8 12207808 0 0 (kbs_any 1).   (* [comment removed for export] *)
Definition Q_do_cleanup : query := Q 8 12207808 0 32 (kbs_Z 1 0x0).   (* [comment removed for export] *)
Definition Q_config_once : query := Q 8 12207808 0 576 (kbs_Z 4 0x0).   (* [comment removed for export] *)
Definition Q_config_inited : query := Q 8 12207808 0 608 (kbs_Z 4 0x0).   (* [comment removed for export] *)
Definition Q_optsdone : query := Q 8 12207808 0 224 (kbs_Z 8 0x2).   (* [comment removed for export] *)
Definition Q_obj_once : query := Q 8 12207808 0 2176 (kbs_Z 4 0x0).   (* [comment removed for export] *)
Definition Q_obj_inited : query := Q 8 12207808 0 2208 (kbs_Z 4 0x0).   (* [comment removed for export] *)
Definition Q_obj_added : query := Q 8 12207808 0 2112 (kbs_Z 8 0x0).   (* [comment removed for export] *)
Definition Q_obj_lock : query := Q 8 12207808 0 2144 (kbs_Z 8 0x0).   (* [comment removed for export] *)
Definition Q_tsd_init_slot : query := Q 15 12363680 0 8 (kbs_Z 8 0x0).   (* [comment removed for export] *)
Definition Q_mk_sa : query := Q T_MK 0 72 24 (kbs_ptr T_SA).
Definition Q_sa : query := Q T_SA 0 32 0 (kbs_Z 4 0x1 ++ kbs_any 4 ++ kbs_Z 8 0x0 ++ kbs_Z 8 0x1 ++ kbs_ptr T_ND).
Definition Q_nd : query := Q T_ND 0 128 0 (kbs_ptr T_ES).
Definition Q_xl : query := Q T_XL 0 40 0 (kbs_Z 4 0x0 ++ kbs_Z 4 0x0 ++ kbs_Z 4 0x0 ++ kbs_Z 4 0x0 ++ kbs_Z 4 0x0 ++ kbs_Z 4 0x0 ++ kbs_Z 4 0x0 ++ kbs_Z 4 0x0 ++ kbs_Z 4 0x0 ++ kbs_Z 4 0x0).
Definition Q_es0 : query := Q T_ES 0 904 0 (kbs_bytes (repeat 0 64)).      (* [comment removed for export] *)
Definition Q_es1 : query := Q T_ES 0 904 64 (kbs_bytes (repeat 0 64)).     (* [comment removed for export] *)
Definition Q_es2 : query := Q T_ES 0 904 128 (kbs_bytes (repeat 0 128)).   (* [comment removed for export] *)
Definition Q_es3 : query := Q T_ES 0 904 256 (kbs_bytes (repeat 0 128)).   (* [comment removed for export] *)
Definition Q_es4 : query := Q T_ES 0 904 384 (kbs_bytes (repeat 0 128)).   (* [comment removed for export] *)
Definition Q_es5 : query := Q T_ES 0 904 512 (kbs_bytes (repeat 0 64)).    (* [comment removed for export] *)
Definition Q_es6 : query := Q T_ES 0 904 576 (kbs_bytes (repeat 0 128)).   (* [comment removed for export] *)
Definition Q_es7 : query := Q T_ES 0 904 704 (kbs_bytes (repeat 255 64)).  (* [comment removed for export] *)
Definition Q_es8 : query := Q T_ES 0 904 768 (kbs_bytes (repeat 0 128)).   (* [comment removed for export] *)
Definition Q_es9 : query := Q T_ES 0 904 896 (kbs_Z 4 0x0 ++ kbs_Z 4 0x0).  (* [comment removed for export] *)
Definition Q_ol : query := Q T_OL 0 40 0 (kbs_any 8).
Definition QS : list query :=
  [Q_memset_func; Q_malloc_impl; Q_free_impl; Q_no_customize; Q_realloc_impl; Q_master_once; Q_master_init; Q_master_key; Q_dc_inited; Q_dc_key; Q_dc_once1; Q_dc_once1_ret; Q_dc_once2; Q_dc_once2_ret; Q_dc_exlock; Q_dc_exmeth_bio; Q_dc_conf_diag; Q_stopped; Q_base_once; Q_base_ret; Q_in_init_key; Q_optsdone_lock; Q_tsd_dc_slot; Q_tsd_mk_slot; Q_tsd_used; Q_conf_meth8; Q_conf_meth72; Q_cancelbuf; Q_base_inited; Q_do_cleanup; Q_config_once; Q_config_inited; Q_optsdone; Q_obj_once; Q_obj_inited; Q_obj_added; Q_obj_lock; Q_tsd_init_slot;
   Q_mk_sa; Q_sa; Q_nd; Q_xl; Q_es0; Q_es1; Q_es2; Q_es3; Q_es4; Q_es5; Q_es6; Q_es7; Q_es8; Q_es9; Q_ol].
Definition TAGS6 : list int := [T_MK; T_SA; T_ND; T_ES; T_XL; T_OL].

(* [comment removed for export] *)
Definition blk_al_ok (S : sstate) (t : int) : bool :=
  match mget (s_mem S) t with Some rg => ((rg_al rg =? 4) || (rg_al rg =? 6))%uint63 | None => false end.
(* [comment removed for export] *)
Definition rgwr_ok (S : sstate) (t : int) : bool := match mget (s_mem S) t with Some rg => rg_wr rg | None => false end.

Definition fin_ok (x : icache * @xres xcd) : bool :=
  match snd x with
  | XDone cd St => forallb (q_ok St) QS && forallb (fun t => existsb (fun t' => (t =? t')%uint63) (x_blocks cd)) TAGS6
                   && forallb (blk_al_ok St) (x_blocks cd) && forallb (rgwr_ok St) [8; 10; 11; 15]%uint63
  | _ => false
  end.

(* [comment removed for export] *)
Lemma fin_checked_0 : fin_ok (run_result 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fin_checked_16 : fin_ok (run_result 16) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition id_of (M : HxMem.mem) (t : int) : Prog.bptr := ((0%N, rsize M t), to_Z t).
Definition OW_of (rho : valuation) (M : HxMem.mem) (bl : list int) : list block := map (fun t => (id_of M t, rho t, rsize M t)) bl.

Lemma OW_an (rho : valuation) (M : HxMem.mem) (bl : list int) : map blk_an (OW_of rho M bl) = blk_list rho M bl.
Proof. unfold OW_of, blk_list. rewrite map_map. apply map_ext. intros t. reflexivity. Qed.

Lemma ids_nodup_of (M : HxMem.mem) : forall l : list int, List.NoDup (map to_Z l) -> List.NoDup (map (id_of M) l).
Proof.
  intros l H. apply (NoDup_map_inv snd). rewrite map_map. cbn [id_of snd]. exact H.
Qed.

Lemma OW_ids_nodup (rho : valuation) (M : HxMem.mem) (bl : list int) : List.NoDup bl -> List.NoDup (map blk_id (OW_of rho M bl)).
Proof.
  intros H. unfold OW_of. rewrite map_map. cbn [blk_id fst]. apply ids_nodup_of.
  induction H as [|t l Hni Hnd IH]; [constructor|]. cbn [map]. constructor; [|exact IH].
  intros Hin. apply in_map_iff in Hin as (t' & E & Ht'). apply to_Z_inj in E. subst t'. exact (Hni Ht').
Qed.

Lemma ids5_nodup (M : HxMem.mem) : List.NoDup (map (id_of M) [T_ES; T_MK; T_SA; T_ND; T_XL]).
Proof. apply ids_nodup_of. vm_compute. repeat (constructor; [cbn [In]; intuition lia|]). constructor. Qed.

(* [comment removed for export] *)
Lemma bptr_eqb_id (M : HxMem.mem) (t0 t : int) : bptr_eqb (id_of M t0) (id_of M t) = true <-> t0 = t.
Proof.
  unfold bptr_eqb, id_of. cbn [fst snd]. rewrite Bool.andb_true_iff, Z.eqb_eq. split.
  - intros [_ E]. apply to_Z_inj. exact E.
  - intros ->. split; [| reflexivity]. unfold Malloc.aptr_eqb. cbn [fst snd]. rewrite N.eqb_refl, Z.eqb_refl. reflexivity.
Qed.
Lemma badr_OW (rho : valuation) (M : HxMem.mem) : forall (bl : list int) t, List.NoDup bl -> In t bl -> badr (OW_of rho M bl) (id_of M t) = rho t.
Proof.
  induction bl as [|t0 bl IH]; intros t ND Hin; [destruct Hin|]. cbn [OW_of map badr blk_id blk_addr fst snd].
  inversion ND as [|x l Hni Hnd]; subst.
  destruct (bptr_eqb (id_of M t0) (id_of M t)) eqn:E.
  - apply (proj1 (bptr_eqb_id M t0 t)) in E. subst t0. reflexivity.
  - destruct Hin as [->|Hin]; [rewrite (proj2 (bptr_eqb_id M t t) eq_refl) in E; discriminate|]. exact (IH t Hnd Hin).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive citem : Type := IZ8 (z : Z) | IZ4 (z : Z) | IZ1 (z : Z) | IP (t : int) | IB (zs : list Z).

Fixpoint kbs_items (l : list citem) : list kb :=
  match l with
  | [] => []
  | IZ8 z :: l' => kbs_Z 8 z ++ kbs_items l'
  | IZ4 z :: l' => kbs_Z 4 z ++ kbs_items l'
  | IZ1 z :: l' => kbs_Z 1 z ++ kbs_items l'
  | IP t :: l' => kbs_ptr t ++ kbs_items l'
  | IB zs :: l' => kbs_bytes zs ++ kbs_items l'
  end.
Fixpoint cells_items (rho : valuation) (l : list citem) : list Cells.cell :=
  match l with
  | [] => []
  | IZ8 z :: l' => C8 (wz z) :: cells_items rho l'
  | IZ4 z :: l' => C4 (wz z) :: cells_items rho l'
  | IZ1 z :: l' => C1 (Z_to_bv 8 z) :: cells_items rho l'
  | IP t :: l' => C8 (wz (rho t)) :: cells_items rho l'
  | IB zs :: l' => CB (length zs) (map (Z_to_bv 8) zs) :: cells_items rho l'
  end.
Fixpoint items_ok (rho : valuation) (l : list citem) : Prop :=
  match l with
  | [] => True
  | IZ8 z :: l' => 0 <= z < 2 ^ 64 /\ items_ok rho l'
  | IZ4 z :: l' => 0 <= z < 2 ^ 64 /\ items_ok rho l'
  | IZ1 z :: l' => 0 <= z /\ items_ok rho l'
  | IP t :: l' => 0 < rho t < 2 ^ 63 /\ items_ok rho l'
  | IB zs :: l' => items_ok rho l'
  end.
Lemma F2_bytes' (rho : valuation) (zs : list Z) (ks : list kb) (cs : list Cells.cell) (bs : list byte) :
  (forall bs', Forall2 (kb_ok rho) ks bs' -> bs' = cells_bytes cs) ->
  Forall2 (kb_ok rho) (kbs_bytes zs ++ ks) bs -> bs = cells_bytes (CB (length zs) (map (Z_to_bv 8) zs) :: cs).
Proof.
  intros Hk H. destruct (Forall2_app_split _ _ _ _ H) as (b1 & b2 & -> & F1 & F2). cbn [cells_bytes cbytes].
  rewrite (Hk b2 F2). f_equal. pose proof (F2_bytes rho zs b1 F1) as E. cbn [cells_bytes cbytes] in E. rewrite app_nil_r in E. exact E.
Qed.
Lemma items_bytes (rho : valuation) : forall (l : list citem) (bs : list byte),
  items_ok rho l -> Forall2 (kb_ok rho) (kbs_items l) bs -> bs = cells_bytes (cells_items rho l).
Proof.
  induction l as [|[z|z|z|k|zs] l IH]; intros bs Hok H; cbn [kbs_items cells_items items_ok] in *.
  - exact (F2_nil rho bs H).
  - destruct Hok as [Hz Hok]. exact (F2_lit8 rho z _ _ bs Hz (fun bs' H' => IH bs' Hok H') H).
  - destruct Hok as [Hz Hok]. exact (F2_lit4 rho z _ _ bs Hz (fun bs' H' => IH bs' Hok H') H).
  - destruct Hok as [Hz Hok]. exact (F2_lit1 rho z _ _ bs Hz (fun bs' H' => IH bs' Hok H') H).
  - destruct Hok as [Hz Hok]. exact (F2_ptr rho k _ _ bs ltac:(lia) ltac:(lia) (fun bs' H' => IH bs' Hok H') H).
  - exact (F2_bytes' rho zs _ _ bs (fun bs' H' => IH bs' Hok H') H).
Qed.
Lemma items_wf (rho : valuation) : forall l, cells_wf (cells_items rho l).
Proof. induction l as [|[z|z|z|k|zs] l IH]; cbn; auto. split; [apply length_map | exact IH]. Qed.
Lemma items_len (rho : valuation) : forall l, length (kbs_items l) = cells_size (cells_items rho l).
Proof.
  induction l as [|[z|z|z|k|zs] l IH]; cbn [kbs_items cells_items cells_size csize]; [reflexivity| | | | |];
    rewrite length_app, IH; cbn; rewrite ?kbs_Z_length, ?kbs_ptr_length, ?kbs_bytes_length; try reflexivity; try lia.
  all: first [reflexivity | unfold kbs_Z, kbs_ptr, kbs_bytes; rewrite ?length_map, ?length_seq; cbn; lia].
Qed.

Section Final.
Variable RT : rt_sig.

Local Ltac qin := unfold QS; cbn [In]; repeat (first [left; reflexivity | right]).

(* [comment removed for export] *)
Lemma q_items_ro (rho : valuation) (S : sstate) (m : word -> option byte) (q : query) (l : list citem) :
  Rmem ctasegs rho (s_mem S) m -> q_ok S q = true -> q_ks q = kbs_items l -> items_ok rho l ->
  ro_cells ctasegs m (q_addr rho q) (cells_items rho l).
Proof. intros HR Hq Ek Hok. apply (q_cells rho S m q _ HR Hq (items_wf rho l)). rewrite Ek. intros bs H. exact (items_bytes rho l bs Hok H). Qed.

(* [comment removed for export] *)
Lemma q_items_rw (rho : valuation) (S : sstate) (m : word -> option byte) (q : query) (l : list citem) :
  Rmem ctasegs rho (s_mem S) m -> q_ok S q = true -> rgwr_ok S (q_tag q) = true -> q_ks q = kbs_items l -> items_ok rho l ->
  rw_cells ctasegs m (q_addr rho q) (cells_items rho l).
Proof.
  intros HR Hq Hw Ek Hok. destruct (q_sound rho S m q HR Hq) as (rg & bs & Eg & HF & Hb & Hwr & _).
  unfold rgwr_ok in Hw. rewrite Eg in Hw. rewrite Ek in HF. rewrite (items_bytes rho l bs Hok HF) in Hb.
  split; [split; [apply items_wf | exact Hb]|]. rewrite <- (items_len rho l), <- Ek. exact (Hwr Hw).
Qed.

(* [comment removed for export] *)
Lemma q_items_blk (rho : valuation) (S : sstate) (m : word -> option byte) (q : query) (l : list citem) :
  Rmem ctasegs rho (s_mem S) m -> q_ok S q = true -> q_lo q = 0 -> q_ks q = kbs_items l -> items_ok rho l ->
  rw_cells ctasegs m (rho (q_tag q) + q_off q) (cells_items rho l).
Proof.
  intros HR Hq E0 Ek Hok. apply (q_rw_cells rho S m q _ HR Hq E0 (items_wf rho l)); [rewrite Ek; apply items_len|].
  rewrite Ek. intros bs H. exact (items_bytes rho l bs Hok H).
Qed.

(* [comment removed for export] *)
Lemma bytes_of_Z (bs : list byte) (zs : list Z) : map bv_unsigned bs = zs -> bs = map (Z_to_bv 8) zs.
Proof.
  revert zs. induction bs as [|b bs IH]; intros [|z zs] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. cbn [map]. f_equal; [|exact (IH zs H2)]. apply bv_eq. rewrite Z_to_bv_unsigned, <- H1. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma u32arr_of_CB (m : word -> option byte) (A : Z) (ws : list word) (zs : list Z) :
  rw_cells ctasegs m A [CB (length zs) (map (Z_to_bv 8) zs)] -> map bv_unsigned (u32s ws) = zs -> u32arr ctasegs m A ws.
Proof.
  intros [[_ HB] HW] E. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. rewrite <- (bytes_of_Z _ _ E) in HB.
  split; [exact HB|]. pose proof (f_equal (@length Z) E) as L. rewrite length_map, u32s_length in L.
  cbn [cells_size csize Nat.add] in HW. rewrite Nat.add_0_r in HW. replace (4 * Z.of_nat (length ws)) with (Z.of_nat (length zs)) by lia. exact HW.
Qed.
Lemma u64arr_of_CB (m : word -> option byte) (A : Z) (ws : list word) (zs : list Z) :
  rw_cells ctasegs m A [CB (length zs) (map (Z_to_bv 8) zs)] -> map bv_unsigned (u64s ws) = zs -> u64arr ctasegs m A ws.
Proof.
  intros [[_ HB] HW] E. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. rewrite <- (bytes_of_Z _ _ E) in HB.
  split; [exact HB|]. pose proof (f_equal (@length Z) E) as L. rewrite length_map, u64s_length in L.
  cbn [cells_size csize Nat.add] in HW. rewrite Nat.add_0_r in HW. replace (8 * Z.of_nat (length ws)) with (Z.of_nat (length zs)) by lia. exact HW.
Qed.

(* [comment removed for export] *)
Ltac ROq RO q l := let X := fresh in pose proof (RO q l ltac:(qin) eq_refl ltac:(cbn [items_ok]; repeat split; try exact I; lia)) as X;
                   unfold q_addr in X; cbn [q_lo q_tag q_off Z.eqb Z.add Pos.add cells_items
                     Q_memset_func Q_malloc_impl Q_free_impl Q_no_customize Q_realloc_impl Q_master_once Q_master_init Q_master_key Q_dc_inited Q_dc_key Q_dc_once1 Q_dc_once1_ret Q_dc_once2 Q_dc_once2_ret Q_dc_exlock Q_dc_exmeth_bio Q_dc_conf_diag Q_stopped Q_base_once Q_base_ret Q_in_init_key Q_optsdone_lock Q_tsd_dc_slot Q_tsd_mk_slot Q_tsd_used Q_conf_meth8 Q_conf_meth72 Q_cancelbuf Q_base_inited Q_do_cleanup Q_config_once Q_config_inited Q_optsdone Q_obj_once Q_obj_inited Q_obj_added Q_obj_lock Q_tsd_init_slot] in X; exact X.
Ltac RWq RW q W l := let X := fresh in pose proof (RW q l ltac:(qin) W eq_refl ltac:(cbn [items_ok]; repeat split; try exact I; lia)) as X;
                   unfold q_addr in X; cbn [q_lo q_tag q_off Z.eqb Z.add Pos.add cells_items
                     Q_memset_func Q_malloc_impl Q_free_impl Q_no_customize Q_realloc_impl Q_master_once Q_master_init Q_master_key Q_dc_inited Q_dc_key Q_dc_once1 Q_dc_once1_ret Q_dc_once2 Q_dc_once2_ret Q_dc_exlock Q_dc_exmeth_bio Q_dc_conf_diag Q_stopped Q_base_once Q_base_ret Q_in_init_key Q_optsdone_lock Q_tsd_dc_slot Q_tsd_mk_slot Q_tsd_used Q_conf_meth8 Q_conf_meth72 Q_cancelbuf Q_base_inited Q_do_cleanup Q_config_once Q_config_inited Q_optsdone Q_obj_once Q_obj_inited Q_obj_added Q_obj_lock Q_tsd_init_slot] in X; exact X.

Theorem LIBA_final_A : forall (ri : int) (ic : icache) (cd : xcd) (S : sstate) (CL : list (Z * Z)) (lo sp0 : Z) (m0 : word -> option byte) (cr0 anc : Z)
    (rho : valuation) (Σ' : rts RT) (ms' : machine_state),
  ri = 0%uint63 \/ ri = 16%uint63 -> run_result ri = (ic, XDone cd S) ->
  lib_pristineA m0 ->
  XInv ctasegs SHBW (ghost RT) (FInv RT CL lo sp0 (to_Z ri) m0 cr0 anc XP_INIT) (GH RT Σ') rho cd S ms' ->
  LIBA RT Σ' (blk_list rho (s_mem S) (x_blocks cd)) (ms_mem ms').
Proof.
  intros ri ic cd S CL lo sp0 m0 cr0 anc rho Σ' ms' H_ri Erun HPRIS [[HRn _] [HF _]].
  assert (Hfin : fin_ok (run_result ri) = true) by (destruct H_ri as [-> | ->]; [exact fin_checked_0 | exact fin_checked_16]).
  rewrite Erun in Hfin. cbn [fin_ok snd] in Hfin.
  apply andb_prop in Hfin as [Hfin HWR]. apply andb_prop in Hfin as [Hfin HAl]. apply andb_prop in Hfin as [HQ HT].
  assert (fin_q : forall q, In q QS -> q_ok S q = true) by exact (proj1 (forallb_forall (q_ok S) QS) HQ).
  assert (fin_t : forall t, In t TAGS6 -> In t (x_blocks cd)).
  { intros t Ht. pose proof (proj1 (forallb_forall _ _) HT t Ht) as X. cbv beta in X. apply existsb_exists in X as (t' & Hin & E). apply Uint63.eqb_spec in E. subst t'. exact Hin. }
  assert (fin_w : forall t, In t [8; 10; 11; 15]%uint63 -> rgwr_ok S t = true) by exact (proj1 (forallb_forall _ _) HWR).
  set (m' := ms_mem ms') in *. pose proof (Rn_R ctasegs rho S ms' HRn) as (_ & _ & _ & _ & HR). fold m' in HR.
  pose proof HF as (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hrho & HART & Hmi & Hstk & Hbnd & Hcnt & Hagr & Hanc & _).
  set (OW := OW_of rho (s_mem S) (x_blocks cd)).
  rewrite <- (OW_an rho (s_mem S) (x_blocks cd)). fold OW.
  assert (NDbl : List.NoDup (x_blocks cd)) by exact (NoDup_app_remove_r _ _ Hnd).
  (* [comment removed for export] *)
  assert (q_blk : forall q, In q QS -> q_lo q = 0 -> In (q_tag q) TAGS6 ->
            In (id_of (s_mem S) (q_tag q), rho (q_tag q), q_size q) OW /\ 0 < rho (q_tag q) /\ rho (q_tag q) + q_size q < 2 ^ 63 /\ badr OW (id_of (s_mem S) (q_tag q)) = rho (q_tag q)).
  { intros q Hq E0 Ht. destruct (q_sound rho S m' q HR (fin_q q Hq)) as (rg & bs & Eg & _ & _ & _ & Hh).
    destruct (Hh E0) as (Ea & Es & Hwr & Hne & Hpos & Hr0 & Hr1). split; [|split; [exact Hr0| split; [exact Hr1| apply badr_OW; [exact NDbl | exact (fin_t _ Ht)]]]].
    unfold OW, OW_of. apply in_map_iff. exists (q_tag q). split; [|exact (fin_t _ Ht)]. rewrite (rsize_get _ _ rg Eg), Es. reflexivity. }
  destruct (q_blk Q_mk_sa ltac:(qin) eq_refl ltac:(cbn; tauto)) as (IMK & PMK & LMK & AMK).
  destruct (q_blk Q_sa ltac:(qin) eq_refl ltac:(cbn; tauto)) as (ISA & PSA & LSA & ASA).
  destruct (q_blk Q_nd ltac:(qin) eq_refl ltac:(cbn; tauto)) as (IND & PND & LND & AND).
  destruct (q_blk Q_es0 ltac:(qin) eq_refl ltac:(cbn; tauto)) as (IES & PES & LES & AES).
  destruct (q_blk Q_xl ltac:(qin) eq_refl ltac:(cbn; tauto)) as (IXL & PXL & LXL & AXL).
  destruct (q_blk Q_ol ltac:(qin) eq_refl ltac:(cbn; tauto)) as (IOL & POL & LOL & AOL).
  cbn [q_tag q_size Q_mk_sa Q_sa Q_nd Q_es0 Q_xl Q_ol] in IMK, PMK, LMK, AMK, ISA, PSA, LSA, ASA, IND, PND, LND, AND, IES, PES, LES, AES, IXL, PXL, LXL, AXL, IOL, POL, LOL, AOL.
  (* [comment removed for export] *)
  assert (HokOW : Forall blk_okA OW).
  { apply Forall_forall. intros b Hb. unfold OW, OW_of in Hb. apply in_map_iff in Hb as (t & <- & Ht). unfold blk_okA, id_of, gsz. cbn [blk_addr blk_size blk_id fst snd].
    destruct (proj1 Hlink t Ht) as (rg & Eg & Ea & Ew & Hs0). rewrite (rsize_get _ _ rg Eg). split; [|split; [exact Hs0| reflexivity]].
    pose proof (proj1 (forallb_forall _ _) HAl t Ht) as X. unfold blk_al_ok in X. rewrite Eg in X.
    destruct (proj1 HR t rg Eg) as (_ & _ & _ & _ & _ & _ & Hmod & _). unfold rbase in Hmod. rewrite Ea in Hmod.
    apply orb_prop in X. destruct X as [X|X]; apply Uint63.eqb_spec in X; rewrite X in Hmod;
      [replace (2 ^ to_Z 4%uint63) with 16 in Hmod by (vm_compute; reflexivity); exact Hmod
      | replace (2 ^ to_Z 6%uint63) with 64 in Hmod by (vm_compute; reflexivity); clear - Hmod; Z.div_mod_to_equations; lia]. }
  assert (HndOW : List.NoDup (map blk_id OW)) by (apply OW_ids_nodup; exact NDbl).
  clearbody OW.
  exists ap_ls0, OW. split; [reflexivity|]. split; [exact HndOW|]. split; [exact HokOW|].
  split; [| exact CtOwner.ct_linv_init].      (* [comment removed for export] *)
  (* [comment removed for export] *)
  set (E := CtRepP.ApRepDefs.mkE 0 (rho T_ES) (rho T_MK) (rho T_SA) (rho T_ND) (rho T_XL)
                                  (id_of (s_mem S) 0%uint63) (id_of (s_mem S) T_ES) (id_of (s_mem S) T_MK) (id_of (s_mem S) T_SA) (id_of (s_mem S) T_ND) (id_of (s_mem S) T_XL) CnfInit).
  exists E.
  assert (NDE : List.NoDup (env_ids E)) by (unfold E, CtRepP.ApRepDefs.env_ids, CtRepP.ApRepDefs.env_blocks; cbn [map blk_id fst snd CtRepP.ApRepDefs.p_bio CtRepP.ApRepDefs.p_es CtRepP.ApRepDefs.p_mk CtRepP.ApRepDefs.p_sa CtRepP.ApRepDefs.p_nd CtRepP.ApRepDefs.p_xl]; exact (ids5_nodup (s_mem S))).
  split; [| split; [exact (ids_ok_of_ls0 E NDE) | apply data_cells_ls0]].
  split; [exact (proj1 ap_linv_init)|]. split; [reflexivity|].
  exists 0.
  (* [comment removed for export] *)
  assert (RO : forall q l, In q QS -> q_ks q = kbs_items l -> items_ok rho l -> ro_cells ctasegs m' (q_addr rho q) (cells_items rho l))
    by (intros q l Hq Ek Hok; exact (q_items_ro rho S m' q l HR (fin_q q Hq) Ek Hok)).
  assert (RW : forall q l, In q QS -> rgwr_ok S (q_tag q) = true -> q_ks q = kbs_items l -> items_ok rho l -> rw_cells ctasegs m' (q_addr rho q) (cells_items rho l))
    by (intros q l Hq Hw Ek Hok; exact (q_items_rw rho S m' q l HR (fin_q q Hq) Hw Ek Hok)).
  assert (BLK : forall q l, In q QS -> q_lo q = 0 -> q_ks q = kbs_items l -> items_ok rho l -> rw_cells ctasegs m' (rho (q_tag q) + q_off q) (cells_items rho l))
    by (intros q l Hq E0 Ek Hok; exact (q_items_blk rho S m' q l HR (fin_q q Hq) E0 Ek Hok)).
  assert (W8 : rgwr_ok S 8 = true) by (apply fin_w; cbn; tauto). assert (W10 : rgwr_ok S 10 = true) by (apply fin_w; cbn; tauto). assert (W11 : rgwr_ok S 11 = true) by (apply fin_w; cbn; tauto). assert (W15 : rgwr_ok S 15 = true) by (apply fin_w; cbn; tauto).
  unfold ap_state. split.
  { (* [comment removed for export] *)
    unfold CtRepP.ApRepDefs.ap_env_ok, CtRepP.ApRepDefs.env_blocks, E.
    cbn [CtRepP.ApRepDefs.e_bio CtRepP.ApRepDefs.e_es CtRepP.ApRepDefs.e_mk CtRepP.ApRepDefs.e_sa CtRepP.ApRepDefs.e_nd CtRepP.ApRepDefs.e_xl
         CtRepP.ApRepDefs.p_bio CtRepP.ApRepDefs.p_es CtRepP.ApRepDefs.p_mk CtRepP.ApRepDefs.p_sa CtRepP.ApRepDefs.p_nd CtRepP.ApRepDefs.p_xl blk_addr blk_size fst snd].
    unfold ES_SIZE, MUTEX_SIZE.
    split; [repeat constructor; assumption|]. split; [exact HndOW|].
    pose proof (proj1 (Forall_forall _ _) HokOW _ IES) as [ME _].
    pose proof (proj1 (Forall_forall _ _) HokOW _ IMK) as [MM _]. pose proof (proj1 (Forall_forall _ _) HokOW _ ISA) as [MS _].
    pose proof (proj1 (Forall_forall _ _) HokOW _ IND) as [MN _]. pose proof (proj1 (Forall_forall _ _) HokOW _ IXL) as [MX _].
    cbn [blk_addr blk_size fst snd] in ME, MM, MS, MN, MX.
    repeat constructor; cbn [blk_addr blk_size fst snd]; try assumption; lia. }
  split.
  { (* [comment removed for export] *)
    unfold ap_statics_fixed, crypto_statics, realloc_statics, E.
    cbn [CtRepP.ApRepDefs.e_bio CtRepP.ApRepDefs.e_xl CtRepP.ApRepDefs.e_mk].
    split. { split. { ROq RO Q_memset_func [IZ8 0x1c29c8]. }
             split. { ROq RO Q_malloc_impl [IZ8 0x1fce24]. }
             split. { ROq RO Q_free_impl [IZ8 0x1fd334]. }
             ROq RO Q_no_customize [IZ1 1]. }
    split. { ROq RO Q_realloc_impl [IZ8 0x1fd224]. }
    split. { exact I. }
    split. { ROq RO Q_master_once [IZ4 2]. }
    split. { ROq RO Q_master_init [IZ1 1]. }
    split. { ROq RO Q_master_key [IZ4 3]. }
    split. { ROq RO Q_dc_inited [IZ1 1]. }
    split. { ROq RO Q_dc_key [IZ4 4]. }
    split. { ROq RO Q_dc_once1 [IZ4 2]. }
    split. { ROq RO Q_dc_once1_ret [IZ4 1]. }
    split. { ROq RO Q_dc_once2 [IZ4 2]. }
    split. { ROq RO Q_dc_once2_ret [IZ4 1]. }
    split. { ROq RO Q_dc_exlock [IP T_XL]. }
    split. { ROq RO Q_dc_exmeth_bio [IZ8 0]. }
    split. { ROq RO Q_dc_conf_diag [IZ4 0]. }
    split. { ROq RO Q_stopped [IZ1 0]. }
    split. { ROq RO Q_base_once [IZ4 2]. }
    split. { ROq RO Q_base_ret [IZ4 1]. }
    split. { ROq RO Q_in_init_key [IZ4 2]. }
    split. { exists (wz (rho T_OL)). ROq RO Q_optsdone_lock [IP T_OL]. }
    split. { ROq RO Q_tsd_dc_slot [IZ8 0]. }
    split. { ROq RO Q_tsd_mk_slot [IP T_MK]. }
    split. { (* [comment removed for export] *) destruct (seg_rw_c1 ctasegs m' AP_TSD_USED ltac:(vm_compute; reflexivity)) as [u Hu]. exists u. exact Hu. }
    split. { ROq RO Q_conf_meth8 [IZ8 0x265200; IZ8 0x2652a8; IZ8 0x265348]. }
    split. { ROq RO Q_conf_meth72 [IZ8 0x266d58]. }
    split. { (* [comment removed for export] *) destruct (seg_rw_c8' m' AP_CANCELBUF ltac:(vm_compute; reflexivity)) as [cb Hcb]. exists cb. exact Hcb. }
    split. { (* [comment removed for export] *) destruct (seg_rw_c1 ctasegs m' OI_BASE_INITED ltac:(vm_compute; reflexivity)) as [b0 Hb0]. exists b0. exact Hb0. }
    RWq RW Q_do_cleanup W8 [IZ1 0]. }
  split.
  { (* [comment removed for export] *)
    unfold E. cbn [as_cnf st_of_ls ap_ls0 ls_cnf CtRepP.ApRepDefs.e_stage CtRepP.ApRepDefs.stage_once CtRepP.ApRepDefs.stage_tsd]. unfold ap_statics_cnf.
    cbn [CtRepP.ApRepDefs.stage_once CtRepP.ApRepDefs.stage_tsd].
    split. { RWq RW Q_config_once W8 [IZ4 0]. }
    split. { RWq RW Q_config_inited W8 [IZ4 0]. }
    split. { RWq RW Q_optsdone W8 [IZ8 2]. }
    split. { RWq RW Q_obj_once W8 [IZ4 0]. }
    split. { RWq RW Q_obj_inited W8 [IZ4 0]. }
    split. { RWq RW Q_obj_added W8 [IZ8 0]. }
    split. { RWq RW Q_obj_lock W8 [IZ8 0]. }
    RWq RW Q_tsd_init_slot W15 [IZ8 0]. }
  split.
  { (* [comment removed for export] *)
    unfold tl_chain, E. cbn [CtRepP.ApRepDefs.e_mk CtRepP.ApRepDefs.e_sa CtRepP.ApRepDefs.e_nd CtRepP.ApRepDefs.e_es]. unfold OFF_MK_SA.
    split. { pose proof (BLK Q_mk_sa [IP T_SA] ltac:(qin) eq_refl eq_refl ltac:(cbn [items_ok]; lia)) as X. cbn [q_tag q_off Q_mk_sa cells_items] in X. destruct X as [X _]. exact X. }
    split. { destruct (q_sound rho S m' Q_sa HR (fin_q Q_sa ltac:(qin))) as (rg & bs & _ & HFs & Hb & _).
             unfold q_addr in Hb. cbn [q_lo q_tag q_off Q_sa Z.eqb] in Hb. rewrite Z.add_0_r in Hb.
             unfold Q_sa in HFs. cbn [q_ks] in HFs.
             destruct (Forall2_app_split _ _ _ _ HFs) as (b1 & r1 & -> & F1 & HF1).
             destruct (Forall2_app_split _ _ _ _ HF1) as (pad & r2 & -> & F2 & HF2).
             exists pad. unfold sa_cells. split; [cbn [cells_wf cell_wf]; split; [exact I|]; split; [symmetry; exact (Forall2_length F2)|]; cbn; tauto|].
             cbn [cells_bytes cbytes]. rewrite (bs_lit4 rho 1 b1 ltac:(lia) F1) in Hb.
             assert (E2 : r2 = cells_bytes [C8 (wz 0); C8 (wz 1); C8 (wz (rho T_ND))]).
             { eapply (F2_lit8 rho 0); [lia | | exact HF2]. intros b3 H3.
               eapply (F2_lit8 rho 1); [lia | | exact H3]. intros b4 H4.
               eapply (F2_tail rho _ b4 (fun b => b = cells_bytes [C8 (wz (rho T_ND))])); [|exact H4]. intros b' H'.
               exact (F2_ptr rho T_ND [] [] b' PND ltac:(lia) (F2_nil rho) H'). }
             rewrite E2 in Hb. exact Hb. }
    pose proof (BLK Q_nd [IP T_ES] ltac:(qin) eq_refl eq_refl ltac:(cbn [items_ok]; lia)) as X. cbn [q_tag q_off Q_nd cells_items] in X. rewrite Z.add_0_r in X. destruct X as [X _]. exact X. }
  split.
  { (* [comment removed for export] *)
    unfold exlock_free, mutex_free_cells, zeros4, E. cbn [CtRepP.ApRepDefs.e_xl repeat].
    pose proof (BLK Q_xl [IZ4 0; IZ4 0; IZ4 0; IZ4 0; IZ4 0; IZ4 0; IZ4 0; IZ4 0; IZ4 0; IZ4 0] ltac:(qin) eq_refl eq_refl ltac:(cbn [items_ok]; repeat split; try exact I; lia)) as X.
    cbn [q_tag q_off Q_xl cells_items] in X. rewrite Z.add_0_r in X. exact X. }
  split.
  { (* [comment removed for export] *) exact I. }
  (* [comment removed for export] *)
  unfold err_rep. split; [repeat split; reflexivity|].
  split.
  { unfold es_at, E. cbn [CtRepP.ApRepDefs.e_es st_of_ls ap_ls0 ls_data ls_cnf as_marks as_buf as_data as_dflags as_file as_line as_func as_top as_bottom map repeat optr osize Z.of_nat].
    unfold ESO_FLAGS, ESO_MARKS, ESO_BUFFER, ESO_DATA, ESO_DSIZE, ESO_DFLAGS, ESO_FILE, ESO_LINE, ESO_FUNC, ESO_TOP, ERR_NUM. cbn [repeat map optr osize].
    Local Ltac esq BLK q zs := let X := fresh in pose proof (BLK q [IB zs] ltac:(qin) eq_refl ltac:(vm_compute; reflexivity) I) as X; cbn [q_tag q_off cells_items] in X;
                           unfold Q_es0, Q_es1, Q_es2, Q_es3, Q_es4, Q_es5, Q_es6, Q_es7, Q_es8 in X; cbn [q_tag q_off] in X;
                           first [ apply (u32arr_of_CB _ _ _ _ X); vm_compute; reflexivity | apply (u64arr_of_CB _ _ _ _ X); vm_compute; reflexivity ].
    split. { esq BLK Q_es0 (repeat 0 64). }
    split. { esq BLK Q_es1 (repeat 0 64). }
    split. { esq BLK Q_es2 (repeat 0 128). }
    split. { esq BLK Q_es3 (repeat 0 128). }
    split. { esq BLK Q_es4 (repeat 0 128). }
    split. { esq BLK Q_es5 (repeat 0 64). }
    split. { esq BLK Q_es6 (repeat 0 128). }
    split. { esq BLK Q_es7 (repeat 255 64). }
    split. { esq BLK Q_es8 (repeat 0 128). }
    pose proof (BLK Q_es9 [IZ4 0; IZ4 0] ltac:(qin) eq_refl eq_refl ltac:(cbn [items_ok]; repeat split; try exact I; lia)) as X.
    cbn [q_tag q_off Q_es9 cells_items] in X. exact X. }
  cbn [as_file as_func as_data st_of_ls ap_ls0 ls_data repeat ERR_NUM]. repeat split; repeat constructor.
Qed.

End Final.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Close.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.
(* [comment removed for export] *)
Hypothesis LIVE_POS : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> 0 < n.
Hypothesis PMA : posix_memalign_init_contract RT.

Theorem init_cps_A : init_cps RT (LIBA RT).
Proof. exact (init_cps_hx RT AF RTC LIVE_POS PMA (LIBA RT) (LIBA_final_A RT)). Qed.

End Close.
