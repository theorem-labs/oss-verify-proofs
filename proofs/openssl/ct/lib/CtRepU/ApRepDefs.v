(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Image.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prog ApState ApOwner.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AP_PREFIX_METH : Z := 0x2d3898.        (* [comment removed for export] *)
Definition AP_DC_INITED : Z := 0x330770.         (* [comment removed for export] *)
Definition AP_DC_KEY : Z := 0x330774.            (* [comment removed for export] *)
Definition AP_DC_ONCE1 : Z := 0x330778.          (* [comment removed for export] *)
Definition AP_DC_ONCE2 : Z := 0x330780.          (* [comment removed for export] *)
Definition AP_DC_EXLOCK : Z := 0x330790.         (* [comment removed for export] *)
Definition AP_DC_EXMETH_BIO : Z := 0x3307f8.     (* [comment removed for export] *)
Definition AP_DC_CONF_DIAG : Z := 0x3308cc.      (* [comment removed for export] *)
Definition AP_IN_INIT_KEY : Z := 0x3306fc.       (* [comment removed for export] *)
Definition AP_CONFIG_ONCE : Z := 0x33071c.       (* [comment removed for export] *)
Definition AP_CONFIG_INITED : Z := 0x330720.     (* [comment removed for export] *)
Definition AP_OPTSDONE_LOCK : Z := 0x330730.     (* [comment removed for export] *)
Definition AP_OBJ_ONCE : Z := 0x330980.          (* [comment removed for export] *)
Definition AP_OBJ_INITED : Z := 0x330984.        (* [comment removed for export] *)
Definition AP_OBJ_ADDED : Z := 0x330988.         (* [comment removed for export] *)
Definition AP_OBJ_LOCK : Z := 0x330990.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AP_LH_COMP : Z := 0xfc7e8.            (* [comment removed for export] *)
Definition AP_LH_HASH : Z := 0xfc694.            (* [comment removed for export] *)
Definition AP_LH_HASHW : Z := 0xfc92c.           (* [comment removed for export] *)
Definition AP_LH_COMPW : Z := 0xfc94c.
Definition AP_LH_DAW : Z := 0xfc96c.
Definition AP_LH_DAAW : Z := 0xfc98c.
(* [comment removed for export] *)
Definition AP_CONF_METH : Z := 0x31fe28.
Definition DEF_CREATE : Z := 0x125e6c.   Definition DEF_INIT_DEFAULT : Z := 0x125ef8.   Definition DEF_DESTROY : Z := 0x125f60.   Definition DEF_LOAD : Z := 0x126fc4.
(* [comment removed for export] *)
Definition AP_CANCELBUF : Z := 0x3331c8.
(* [comment removed for export] *)
Inductive cnf_stage : Type := CnfInit | CnfMid.
Definition stage_once (sg : cnf_stage) : Z := match sg with CnfInit => 0 | CnfMid => 1 end.
Definition stage_tsd (sg : cnf_stage) : Z := match sg with CnfInit => 0 | CnfMid => 2^64 - 1 end.
Definition AP_OPENSSL_CONFIGURED : Z := 0x333150. (* [comment removed for export] *)
Definition AP_TSD_DC_SLOT : Z := 0x3545a8.      (* [comment removed for export] *)
Definition AP_TSD_INIT_SLOT : Z := 0x354598.    (* [comment removed for export] *)
Definition AP_TSD_USED : Z := 0x333192.         (* [comment removed for export] *)
Definition V_OPTSDONE_CNF : Z := 0x42.           (* [comment removed for export] *)
Definition V_CR_NO_CUSTOMIZE : Z := 1.
(* [comment removed for export] *)
Definition SCT_FREE_GOT : Z := 0x31e898.
Definition SCT_FREE_VA : Z := 0x19d50c.
Definition V_IN_INIT_KEY : Z := 1.   (* [comment removed for export] *)
Definition V_DC_KEY : Z := 3.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition SZ_OBJ_LOCK : Z := 40.  Definition SZ_ADDED : Z := 104.  Definition SZ_ADDED_BUCKETS : Z := 128.
(* [comment removed for export] *)
Definition lhash_cells (bk : Z) : list cell :=
  [C8 (wz bk); C8 (wz AP_LH_COMP); C8 (wz AP_LH_HASH); C8 (wz AP_LH_HASHW); C8 (wz AP_LH_COMPW); C8 (wz AP_LH_DAW); C8 (wz AP_LH_DAAW);
   C4 (wz 8); C4 (wz 16); C4 (wz 0); C4 (wz 8); C8 (wz 512); C8 (wz 256); C8 (wz 0); C4 (wz 0); C4 (wz 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record ap_env : Type := mkE {
  e_bio : Z; e_es : Z; e_mk : Z; e_sa : Z; e_nd : Z; e_xl : Z;          (* [comment removed for export] *)
  p_bio : bptr; p_es : bptr; p_mk : bptr; p_sa : bptr; p_nd : bptr; p_xl : bptr;  (* [comment removed for export] *)
  e_stage : cnf_stage                                                  (* [comment removed for export] *)
}.
Definition env_blocks (E : ap_env) : list block :=
  [(p_es E, e_es E, ES_SIZE); (p_mk E, e_mk E, 72); (p_sa E, e_sa E, 32); (p_nd E, e_nd E, 128); (p_xl E, e_xl E, MUTEX_SIZE)].
Definition env_ids (E : ap_env) : list bptr := map blk_id (env_blocks E).

(* [comment removed for export] *)
Fixpoint badr (OW : list block) (p : bptr) : Z :=
  match OW with [] => 0 | b :: OW' => if bptr_eqb (blk_id b) p then blk_addr b else badr OW' p end.

Section WithSegs.
(* [comment removed for export] *)
Let segs := ctusegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition crypto_statics (m : mem) : Prop :=
  ro_cells segs m CR_GOT_MALLOC [C8 (wz CRYPTO_MALLOC)]
  /\ ro_cells segs m CR_GOT_FREE [C8 (wz CRYPTO_FREE)]
  /\ ro_cells segs m CR_MEMSET_FUNC [C8 (wz MEMSET)]
  /\ ro_cells segs m CR_MALLOC_IMPL [C8 (wz CRYPTO_MALLOC)]
  /\ ro_cells segs m CR_FREE_IMPL [C8 (wz CRYPTO_FREE)]
  /\ ro_cells segs m CR_NO_CUSTOMIZE [C1 (Z_to_bv 8 1)].
(* [comment removed for export] *)
Definition realloc_statics (m : mem) : Prop :=
  ro_cells segs m (CR_GOT_MALLOC + 8) [C8 (wz CRYPTO_REALLOC)] /\ ro_cells segs m CR_REALLOC_IMPL [C8 (wz CRYPTO_REALLOC)].

(* [comment removed for export] *)
Definition ap_statics_fixed (m : mem) (E : ap_env) : Prop :=
  crypto_statics m /\ realloc_statics m
  /\ True                                                              (* [comment removed for export] *)
  /\ ro_cells segs m TL_MASTER_ONCE8 [C4 (wz 1); C4 (wz 2)]            (* [comment removed for export] *)
  /\ ro_cells segs m TL_MASTER_KEY8 [C4 (wz K_MASTER_KEY)]
  /\ ro_cells segs m AP_DC_INITED [C1 (Z_to_bv 8 1)]
  /\ ro_cells segs m AP_DC_KEY [C4 (wz V_DC_KEY)]
  /\ ro_cells segs m AP_DC_ONCE1 [C4 (wz 2); C4 (wz 1)]
  /\ ro_cells segs m AP_DC_ONCE2 [C4 (wz 2); C4 (wz 1)]
  /\ ro_cells segs m AP_DC_EXLOCK [C8 (wz (e_xl E))]
  /\ ro_cells segs m AP_DC_EXMETH_BIO [C8 (wz 0)]
  /\ ro_cells segs m AP_DC_CONF_DIAG [C4 (wz 0)]
  /\ ro_cells segs m OI_STOPPED [C1 (Z_to_bv 8 0)]
  /\ ro_cells segs m OI_BASE_ONCE [C4 (wz 2); C4 (wz 1)]
  /\ ro_cells segs m AP_IN_INIT_KEY [C4 (wz V_IN_INIT_KEY)]
  /\ (exists lk, ro_cells segs m AP_OPTSDONE_LOCK [C8 lk])
  /\ ro_cells segs m TCB_TSD [C8 (wz TSD_MAIN)]
  /\ ro_cells segs m AP_TSD_DC_SLOT [C8 (wz 0)]
  /\ ro_cells segs m TSD_MK_SLOT [C8 (wz (e_mk E))]
  /\ rw_cells segs m AP_TSD_USED [C1 (Z_to_bv 8 1)]
  (* [comment removed for export] *)
  /\ ro_cells segs m (AP_CONF_METH + 8) [C8 (wz DEF_CREATE); C8 (wz DEF_INIT_DEFAULT); C8 (wz DEF_DESTROY)]
  /\ ro_cells segs m (AP_CONF_METH + 72) [C8 (wz DEF_LOAD)]
  /\ (exists cb : word, rw_cells segs m AP_CANCELBUF [C8 cb])
  /\ (exists b0 : byte, rw_cells segs m OI_BASE_INITED [C1 b0])
  /\ rw_cells segs m OI_DO_CLEANUP [C1 (Z_to_bv 8 0)]
  (* [comment removed for export] *)
  /\ ro_cells segs m SCT_FREE_GOT [C8 (wz SCT_FREE_VA)].

(* [comment removed for export] *)
Definition ap_statics_cnf (m : mem) (OW : list block) (sg : cnf_stage) (cnf : option (bptr * bptr * bptr)) : Prop :=
  match cnf with
  | None =>
      rw_cells segs m AP_CONFIG_ONCE [C4 (wz (stage_once sg)); C4 (wz 0)]   (* [comment removed for export] *)
      /\ rw_cells segs m OI_OPTSDONE [C8 (wz V_OI_OPTSDONE)]
      /\ rw_cells segs m AP_OBJ_ONCE [C4 (wz 0); C4 (wz 0)]                 (* [comment removed for export] *)
      /\ rw_cells segs m AP_OBJ_ADDED [C8 (wz 0); C8 (wz 0)]                (* [comment removed for export] *)
      /\ rw_cells segs m AP_OPENSSL_CONFIGURED [C1 (Z_to_bv 8 0)]
      /\ rw_cells segs m AP_TSD_INIT_SLOT [C8 (wz (stage_tsd sg))]
  | Some (lk, lh, bk) =>
      rw_cells segs m AP_CONFIG_ONCE [C4 (wz 2); C4 (wz 1)]
      /\ rw_cells segs m OI_OPTSDONE [C8 (wz V_OPTSDONE_CNF)]
      /\ rw_cells segs m AP_OBJ_ONCE [C4 (wz 2); C4 (wz 1)]
      /\ rw_cells segs m AP_OBJ_ADDED [C8 (wz (badr OW lh)); C8 (wz (badr OW lk))]     (* [comment removed for export] *)
      /\ rw_cells segs m AP_OPENSSL_CONFIGURED [C1 (Z_to_bv 8 1)]
      /\ rw_cells segs m AP_TSD_INIT_SLOT [C8 (wz (2^64 - 1))]
      /\ In (lk, badr OW lk, SZ_OBJ_LOCK) OW /\ In (lh, badr OW lh, SZ_ADDED) OW /\ In (bk, badr OW bk, SZ_ADDED_BUCKETS) OW
      /\ rw_cells segs m (badr OW lk) mutex_free_cells
      /\ rw_cells segs m (badr OW lh) (lhash_cells (badr OW bk))         (* [comment removed for export] *)
      /\ rw_cells segs m (badr OW bk) (c8s (repeat 0 16))
  end.

(* [comment removed for export] *)
Definition IMG_LO : Z := 0x2c2e98.
Definition IMG_HI : Z := 0x31e730.
Definition ap_img (m : mem) : Prop := forall a, IMG_LO <= a < IMG_HI -> mrd segs m (wa a) = seg_rom segs (wa a).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tl_chain (m : mem) (E : ap_env) : Prop :=
  ro_cells segs m (e_mk E + OFF_MK_SA) [C8 (wz (e_sa E))]
  /\ (exists pad, ro_cells segs m (e_sa E) (sa_cells pad (e_nd E)))
  /\ ro_cells segs m (e_nd E) [C8 (wz (e_es E))].

(* [comment removed for export] *)
Definition exlock_free (m : mem) (E : ap_env) : Prop := rw_cells segs m (e_xl E) mutex_free_cells.

(* [comment removed for export] *)
Definition bio_out_rep (m : mem) (E : ap_env) (pv nw : Z) : Prop := True.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition optb_ok (OW : list block) (o : option (bptr * Z)) : Prop :=
  match o with Some (p, n) => In (p, badr OW p, n) OW /\ 0 < badr OW p | None => True end.
(* [comment removed for export] *)
Definition wl (l : list Z) : list word := map wz l.
Definition es_at (m : mem) (A : Z) (st : ap_st bptr) (adr : bptr -> Z) : Prop :=
  u32arr segs m (A + ESO_FLAGS) (wl (repeat 0 ERR_NUM))
  /\ u32arr segs m (A + ESO_MARKS) (wl (as_marks st))
  /\ u64arr segs m (A + ESO_BUFFER) (wl (as_buf st))
  /\ u64arr segs m (A + ESO_DATA) (wl (map (optr adr) (as_data st)))
  /\ u64arr segs m (A + ESO_DSIZE) (wl (map osize (as_data st)))
  /\ u32arr segs m (A + ESO_DFLAGS) (wl (as_dflags st))
  /\ u64arr segs m (A + ESO_FILE) (wl (map (optr adr) (as_file st)))
  /\ u32arr segs m (A + ESO_LINE) (wl (as_line st))
  /\ u64arr segs m (A + ESO_FUNC) (wl (map (optr adr) (as_func st)))
  /\ rw_cells segs m (A + ESO_TOP) [C4 (wz (Z.of_nat (as_top st))); C4 (wz (Z.of_nat (as_bottom st)))].

Definition err_rep (m : mem) (E : ap_env) (OW : list block) (st : ap_st bptr) : Prop :=
  es_shape st /\ es_at m (e_es E) st (badr OW)
  /\ Forall (optb_ok OW) (as_file st) /\ Forall (optb_ok OW) (as_func st) /\ Forall (optb_ok OW) (as_data st).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition blocks_match (OW : list block) (X : list (bptr * Z)) : Prop :=
  forall p n, In (p, n) X -> In (p, badr OW p, n) OW.

Definition ap_env_ok (E : ap_env) (OW : list block) : Prop :=
  Forall (fun b => In b OW) (env_blocks E) /\ List.NoDup (map blk_id OW)
  /\ Forall (fun b => 0 < blk_addr b /\ blk_addr b + blk_size b < 2^63 /\ blk_addr b mod 16 = 0) (env_blocks E).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ap_state (st : ap_st bptr) (m : mem) (OW : list block) (E : ap_env) (bo : Z * Z) : Prop :=
  ap_env_ok E OW /\ ap_img m
  /\ ap_statics_fixed m E /\ ap_statics_cnf m OW (e_stage E) (as_cnf st)
  /\ tl_chain m E /\ exlock_free m E
  /\ bio_out_rep m E (fst bo) (snd bo)
  /\ err_rep m E OW st.

(* [comment removed for export] *)
Definition ap_lib_state (ls : ap_ls bptr) (m : mem) (OW : list block) (E : ap_env) : Prop :=
  ap_ls_wf ls /\ e_stage E = CnfInit /\ exists nw, ap_state (st_of_ls ls) m OW E (0, nw).

Definition ap_lib_inv (ls : ap_ls bptr) (m : mem) (OW : list block) : Prop := exists E, ap_lib_state ls m OW E.

End WithSegs.
