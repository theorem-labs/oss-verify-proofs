(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel BReach BazyRestrict BazyLedger BazySR BazyNodes BothAllocCons.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsDriverLaws BsSR BsChain BakeStackRep BllocWf BllocKit BllocRep BllocRepFacts BllocRepX BecLazy BsDepotInv BsDepotHash BG_Malloc2 BG_MallocLarge3 BG_MallocAll BothAllocCons RtB_Iface.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Record iparams : Type := IP {
  ip_fsb : Z;
  ip_D   : Z;
  ip_TR  : list (list Z);
  ip_TB  : Z
}.

Record ist {HCEIL : HeapCeil} : Type := IST { i_s : ast ; i_d : depot }.
Arguments IST {HCEIL} _ _.

Section Defs.
  Context {HCEIL : HeapCeil}.
  Variable p : iparams.

  Definition ICm (n : Z) : Z := if n <=? 64512 then 0 else 4 * n.
  Definition ICf (n : Z) : Z := 0.

  Definition ILIVE_MAX : Z := 736 * 2 ^ 20.
  Definition ILIVE_CNT_MAX : Z := CNTB.
  Definition Ialloc_ok (x : ist) (LB : list block) (n : Z) : Prop :=
    lb_small LB + nsmall n <= LIVEW /\ Z.of_nat (length LB) + 1 <= ILIVE_CNT_MAX /\ nlarge LB + nlg n <= LMAX.

  Definition lbp (LB : list block) : list (Z * Z) := map (fun b => (blk_addr b, blk_size b)) LB.
  Definition Ilb_remove (q : bptr) (LB : list block) : list block := filter (fun b => negb (blk_id b =? q)) LB.

  Definition dtv_cov (mo : Model) : Prop :=
    forall x : word, ip_D p <= bv_unsigned x < ip_D p + kPageSize -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.

  Definition AHM_SIZE : Z := 0x38e000.
  Definition AHM_B1 : Z := 0x1e34f8.
  Definition AHM_B2 : Z := 0x2cf448.
  Definition tb_cov (mo : Model) : Prop :=
    forall x : word, ip_TB p <= bv_unsigned x < ip_TB p + AHM_SIZE -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Definition IK (x : ist) (mo : Model) : Prop := AMODELX (i_s x) mo /\ depot_cov (i_d x) mo /\ dtv_cov mo /\ tb_cov mo.

  Definition depot_tr (d : depot) : Prop :=
       1 <= d_ids d
    /\ (forall id, 2 <= id <= d_ids d -> In (d_hash d id) (map depot_hash (ip_TR p)))
    /\ List.NoDup (d_K d)
    /\ d_frames d <= 32 * d_ids d.

  Definition ATHR (m : mem) : Prop :=
       rw_cells asegs m (ATP + 8) [C8 (wz (ip_D p))]
    /\ rw_cells asegs m (ip_D p + 24) [C8 (wz ATP)]
    /\ 0 < ip_D p /\ ip_D p mod 8 = 0 /\ ip_D p + 32 <= aceil /\ akobj (ip_D p) kPageSize.

  Definition IDAPART (s : ast) (d : depot) : Prop :=
       disj (a_sb s) (kSpaceSize + kPageSize) (ip_D p) kPageSize /\ disj (a_thr s) kPageSize (ip_D p) kPageSize
    /\ disj (a_pa s) kPtrArrayReserve (ip_D p) kPageSize
    /\ disj (d_nb d) (16 * 65536) (ip_D p) kPageSize /\ disj (d_sb d) (8 * 32768) (ip_D p) kPageSize.

  Definition AHMI (s : ast) (d : depot) (m : mem) : Prop :=
       rw_cells asegs m AIMM_OBJ [C8 (wz (ip_TB p))]
    /\ rw_cells asegs m (ip_TB p + AHM_B1) [CB 96 (repeat (b8 0) 96)]
    /\ rw_cells asegs m (ip_TB p + AHM_B2) [CB 96 (repeat (b8 0) 96)]
    /\ 0 < ip_TB p /\ ip_TB p mod 4096 = 0 /\ akobj (ip_TB p) AHM_SIZE /\ ip_TB p + AHM_SIZE <= aceil
    /\ disj (a_sb s) (kSpaceSize + kPageSize) (ip_TB p) AHM_SIZE /\ disj (a_thr s) kPageSize (ip_TB p) AHM_SIZE
    /\ disj (a_pa s) kPtrArrayReserve (ip_TB p) AHM_SIZE
    /\ disj (d_nb d) (16 * 65536) (ip_TB p) AHM_SIZE /\ disj (d_sb d) (8 * 32768) (ip_TB p) AHM_SIZE
    /\ disj (a_fsb s) AFS_SIZE (ip_TB p) AHM_SIZE /\ disj (ip_D p) kPageSize (ip_TB p) AHM_SIZE
    /\ (forall sc, In sc (as_sec (a_st s)) -> disj (sc_map_beg sc) (sc_map_size sc) (ip_TB p) AHM_SIZE).

  Definition PINVI (st : astate) : Prop := PINV st /\ INITQ st.

  Definition IRHEAP (x : ist) (LB : list block) (m : mem) : Prop :=
    let s := i_s x in let d := i_d x in
       ARHEAP s (lbp LB) m /\ Forall (fun b => blk_id b = blk_addr b /\ 1 <= blk_size b <= 2 ^ 28) LB
    /\ (Z.of_nat (length LB) <= ILIVE_CNT_MAX /\ lb_small LB <= LIVEW /\ nlarge LB <= LMAX)
    /\ awin_vis s m /\ flagsx_rep m
    /\ DEPOT asegs d m /\ depot_placed s d /\ depot_tr d
    /\ disj (a_fsb s) AFS_SIZE (d_nb d) (16 * 65536) /\ disj (a_fsb s) AFS_SIZE (d_sb d) (8 * 32768)
    /\ a_fsb s = ip_fsb p /\ ip_fsb p mod 4096 = 0 /\ disj (a_fsb s) AFS_SIZE (ip_D p) kPageSize
    /\ ATHR m
    /\ (exists tb te : bv 64, rw_cells asegs m (a_thr s + 48) [C8 tb; C8 te])
    /\ ashadow_visible s
    /\ IDAPART s d
    /\ (forall sc, In sc (as_sec (a_st s)) -> disj (sc_map_beg sc) (sc_map_size sc) (ip_D p) kPageSize)
    /\ PINVI (a_st s)
    /\ AHMI s d m.

  Definition Irauxv_ok (m : mem) (B : Z) : Prop := B + 16 <= 2 ^ 47.

  Definition KHp : asr :=
    {| as_St := ist ;
       as_SR := BsSR.SR ;
       as_VIS := BsSR.VIS ist (fun x => a_L (i_s x)) (fun x => a_S (i_s x)) ;
       as_AKREL := BsSR.AKREL ist (fun x => a_L (i_s x)) (fun x => a_S (i_s x)) (fun x => a_Zr (i_s x)) IK ;
       as_MPRES := nonvm_same ;
       as_RHEAP := IRHEAP ;
       as_RFS := RFSI (ip_fsb p) ;
       as_rauxv_ok := Irauxv_ok ;
       as_lb_remove := Ilb_remove ;
       as_alloc_ok := Ialloc_ok ;
       as_LIVE_MAX := ILIVE_MAX ; as_LIVE_CNT_MAX := ILIVE_CNT_MAX ;
       as_AL := fun x => a_AL (i_s x) ;
       as_Cm := ICm ; as_Cf := ICf ;
       as_chain := achain ;
       as_TR := ip_TR p ;
       as_FSB := ip_fsb p |}.
End Defs.
