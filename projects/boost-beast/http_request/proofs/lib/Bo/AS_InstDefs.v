(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes AsanAllocCons.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsIface7 AsDriverLaws AsSR AsChain FakeStackRep.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AllocWf AllocKit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AllocRep AllocRepFacts AllocRepX SecLazy AsDepotInv AsDepotHash AG_Malloc2 AG_MallocLarge3 AG_MallocAll.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record iparams : Type := IP {
  ip_fsb : Z;                 (* [comment removed for export] *)
  ip_D   : Z;                 (* [comment removed for export] *)
  ip_TR  : list (list Z)      (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Record ist {HCEIL : HeapCeil} : Type := IST { i_s : ast ; i_d : depot }.
Arguments IST {HCEIL} _ _.

Section Defs.
  Context {HCEIL : HeapCeil}.
  Variable p : iparams.

  (* [comment removed for export] *)
  Definition ICm (n : Z) : Z := if n <=? 64512 then 0 else 4 * n.
  Definition ICf (n : Z) : Z := 0.
  Definition ILIVE_MAX : Z := ADRV_LIVE.
  Definition ILIVE_CNT_MAX : Z := ADRV_CNT.
  Definition Ialloc_ok (x : ist) (LB : list block) (n : Z) : Prop :=
    lb_bytes LB + n <= ILIVE_MAX /\ Z.of_nat (length LB) + 1 <= ILIVE_CNT_MAX.

  (* [comment removed for export] *)
  Definition lbp (LB : list block) : list (Z * Z) := map (fun b => (blk_addr b, blk_size b)) LB.
  Definition Ilb_remove (q : bptr) (LB : list block) : list block := filter (fun b => negb (blk_id b =? q)) LB.

  (* [comment removed for export] *)
  Definition dtv_cov (mo : Model) : Prop :=
    forall x : word, ip_D p <= bv_unsigned x < ip_D p + kPageSize -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Definition IK (x : ist) (mo : Model) : Prop := AMODELX (i_s x) mo /\ depot_cov (i_d x) mo /\ dtv_cov mo.

  (* [comment removed for export] *)
  Definition TRH : list Z := map depot_hash (ip_TR p).
  Fixpoint zinb (x : Z) (l : list Z) : bool := match l with [] => false | y :: l' => if Z.eqb x y then true else zinb x l' end.
  Definition wildh (h : Z) : bool := negb (zinb h TRH).
  Definition nwild (d : depot) : Z := Z.of_nat (length (List.filter wildh (tl (d_K d)))).
  Definition depot_trw (d : depot) : Prop :=
       1 <= d_ids d
    /\ List.NoDup (d_K d)
    /\ d_frames d <= 32 * d_ids d
    /\ nwild d <= AWMAX.
  (* [comment removed for export] *)
  Definition depot_tr (d : depot) : Prop :=
       1 <= d_ids d
    /\ (forall id, 2 <= id <= d_ids d -> In (d_hash d id) (map depot_hash (ip_TR p)))
    /\ List.NoDup (d_K d)
    /\ d_frames d <= 32 * d_ids d.
  (* [comment removed for export] *)
  Definition IAL (x : ist) : Z := Z.min (a_AL (i_s x)) (ACWILD * (AWMAX - nwild (i_d x))).

  (* [comment removed for export] *)
  Definition ISPRES (s : ast) (m : mem) : Prop :=
    forall a, hceil <= a < a_top s -> wview bsegs m (wa a) <> None.

  (* [comment removed for export] *)
  Definition ATHR (m : mem) : Prop :=
       rw_cells bsegs m (ATP + 8) [C8 (wz (ip_D p))]
    /\ rw_cells bsegs m (ip_D p + 24) [C8 (wz ATP)]
    /\ 0 < ip_D p /\ ip_D p mod 8 = 0 /\ ip_D p + 32 <= aceil /\ akobj (ip_D p) kPageSize.

  (* [comment removed for export] *)
  Definition IDAPART (s : ast) (d : depot) : Prop :=
       disj (a_sb s) (kSpaceSize + kPageSize) (ip_D p) kPageSize /\ disj (a_thr s) kPageSize (ip_D p) kPageSize
    /\ disj (a_pa s) kPtrArrayReserve (ip_D p) kPageSize
    /\ disj (d_nb d) (16 * 65536) (ip_D p) kPageSize /\ disj (d_sb d) (8 * 262144) (ip_D p) kPageSize.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition PINVI (st : astate) : Prop := PINV st /\ INITQ st.

  Definition IRHEAP (x : ist) (LB : list block) (m : mem) : Prop :=
    let s := i_s x in let d := i_d x in
       ARHEAP s (lbp LB) m /\ Forall (fun b => blk_id b = blk_addr b /\ 1 <= blk_size b <= 2 ^ 28) LB
    /\ Z.of_nat (length LB) <= ILIVE_CNT_MAX                (* [comment removed for export] *)
    /\ awin_vis s m /\ flagsx_rep m
    /\ DEPOT bsegs d m /\ depot_placed s d /\ depot_trw d                            (* [comment removed for export] *)
    /\ disj (a_fsb s) AFS_SIZE (d_nb d) (16 * 65536) /\ disj (a_fsb s) AFS_SIZE (d_sb d) (8 * 262144)
    /\ a_fsb s = ip_fsb p /\ ip_fsb p mod 4096 = 0 /\ disj (a_fsb s) AFS_SIZE (ip_D p) kPageSize
    /\ ATHR m
    /\ (exists tb te : bv 64, rw_cells bsegs m (a_thr s + 48) [C8 tb; C8 te])    (* [comment removed for export] *)
    /\ ashadow_visible s                                                          (* [comment removed for export] *)
    /\ IDAPART s d                                                                (* [comment removed for export] *)
    /\ (forall sc, In sc (as_sec (a_st s)) -> disj (sc_map_beg sc) (sc_map_size sc) (ip_D p) kPageSize)    (* [comment removed for export] *)
    /\ PINVI (a_st s)                                                            (* [comment removed for export] *)
    /\ ISPRES s m.                                                               (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition Irauxv_ok (m : mem) (B : Z) : Prop := B + 16 <= 2 ^ 47.

  (* [comment removed for export] *)
  Definition KHp : asr :=
    {| as_St := ist ;
       as_SR := AsSR.SR ;
       as_VIS := AsSR.VIS ist (fun x => a_L (i_s x)) (fun x => a_S (i_s x)) ;
       as_AKREL := AsSR.AKREL ist (fun x => a_L (i_s x)) (fun x => a_S (i_s x)) (fun x => a_Zr (i_s x)) IK ;
       as_MPRES := nonvm_same ;
       as_RHEAP := IRHEAP ;
       as_RFS := RFSI (ip_fsb p) ;
       as_rauxv_ok := Irauxv_ok ;
       as_lb_remove := Ilb_remove ;
       as_alloc_ok := Ialloc_ok ;
       as_LIVE_MAX := ILIVE_MAX ; as_LIVE_CNT_MAX := ILIVE_CNT_MAX ;
       as_AL := IAL ;                                       (* [comment removed for export] *)
       as_Cm := ICm ; as_Cf := ICf ;
       as_chain := achain ;
       as_TR := ip_TR p ;
       as_FSB := ip_fsb p |}.
End Defs.
