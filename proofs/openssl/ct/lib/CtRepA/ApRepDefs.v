(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prog ApState ApOwner.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_libiface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import BnRepDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require ApRepDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BIO_OUT : Z := 0xba46c0.               (* [comment removed for export] *)
Definition NULL_METHOD : Z := 0x54daa0.           (* [comment removed for export] *)
Definition TSD_MAIN : Z := 0xbca798.              (* [comment removed for export] *)
Definition TCB_TSD : Z := 0xba9398.
Definition K_MASTER_KEY : Z := 3.   (* [comment removed for export] *)                 (* [comment removed for export] *)
Definition V_DC_KEY : Z := 4.   (* [comment removed for export] *)                     (* [comment removed for export] *)
Definition V_IN_INIT_KEY : Z := 2.   (* [comment removed for export] *)                (* [comment removed for export] *)
Definition TL_MASTER_ONCE : Z := 0xba4a00.        (* [comment removed for export] *)
Definition TL_MASTER_KEY : Z := 0xba4a20.         (* [comment removed for export] *)
Definition TL_MASTER_INIT : Z := 0xba4a40.        (* [comment removed for export] *)
Definition TSD_MK_SLOT : Z := TSD_MAIN + 8 * K_MASTER_KEY.   (* [comment removed for export] *)
Definition OI_STOPPED : Z := 0xba4700.            (* [comment removed for export] *)
Definition OI_BASE_ONCE : Z := 0xba47c0.          (* [comment removed for export] *)
Definition OI_BASE_RET : Z := 0xba47e0.           (* [comment removed for export] *)
Definition OI_OPTSDONE : Z := 0xba47a0.           (* [comment removed for export] *)
Definition V_OI_OPTSDONE : Z := 2.
Definition OI_BASE_INITED : Z := D_libiface.OSSL_BASE_INITED.       (* [comment removed for export] *)
Definition OI_DO_CLEANUP : Z := D_libiface.OSSL_DO_GLOBAL_CLEANUP.   (* [comment removed for export] *)
Definition CR_REALLOC_IMPL : Z := 0x5aec20.       (* [comment removed for export] *)
Definition CR_GOT_REALLOC : Z := 0x5aa898.        (* [comment removed for export] *)
Definition CRYPTO_REALLOC : Z := 0x1fd224.
(* [comment removed for export] *)
Definition AP_PREFIX_METH : Z := 0x5489c0.        (* [comment removed for export] *)
Definition AP_DC_INITED : Z := 0xba4a60.         (* [comment removed for export] *)
Definition AP_DC_KEY : Z := 0xba4c20.            (* [comment removed for export] *)
Definition AP_DC_ONCE1 : Z := 0xba4c80.          (* [comment removed for export] *)
Definition AP_DC_ONCE1_RET : Z := 0xba4ca0.      (* [comment removed for export] *)
Definition AP_DC_ONCE2 : Z := 0xba4c40.          (* [comment removed for export] *)
Definition AP_DC_ONCE2_RET : Z := 0xba4c60.      (* [comment removed for export] *)
Definition AP_DC_INT : Z := 0xba4a80.            (* [comment removed for export] *)
Definition AP_DC_EXLOCK : Z := AP_DC_INT + 8.    (* [comment removed for export] *)
Definition AP_DC_EXMETH_BIO : Z := AP_DC_INT + 112.  (* [comment removed for export] *)
Definition AP_DC_CONF_DIAG : Z := AP_DC_INT + 324.   (* [comment removed for export] *)
Definition AP_IN_INIT_KEY : Z := 0xba4760.       (* [comment removed for export] *)
Definition AP_CONFIG_ONCE : Z := 0xba4900.       (* [comment removed for export] *)
Definition AP_CONFIG_INITED : Z := 0xba4920.     (* [comment removed for export] *)
Definition AP_OPTSDONE_LOCK : Z := 0xba4720.     (* [comment removed for export] *)
Definition AP_OBJ_ONCE : Z := 0xba4f40.          (* [comment removed for export] *)
Definition AP_OBJ_INITED : Z := 0xba4f60.        (* [comment removed for export] *)
Definition AP_OBJ_ADDED : Z := 0xba4f00.         (* [comment removed for export] *)
Definition AP_OBJ_LOCK : Z := 0xba4f20.          (* [comment removed for export] *)
Definition AP_LH_COMP : Z := 0x221cbc.           (* [comment removed for export] *)
Definition AP_LH_HASH : Z := 0x221ab4.           (* [comment removed for export] *)
Definition AP_LH_HASHW : Z := 0x221ec0.          (* [comment removed for export] *)
Definition AP_LH_COMPW : Z := 0x221ee0.          (* [comment removed for export] *)
Definition AP_LH_DAW : Z := 0x221f00.            (* [comment removed for export] *)
Definition AP_LH_DAAW : Z := 0x221f20.           (* [comment removed for export] *)
Definition AP_CONF_METH : Z := 0x5aed60.         (* [comment removed for export] *)
Definition DEF_CREATE : Z := 0x265200.   Definition DEF_INIT_DEFAULT : Z := 0x2652a8.   Definition DEF_DESTROY : Z := 0x265348.   Definition DEF_LOAD : Z := 0x266d58.
Definition AP_CANCELBUF : Z := 0xba9390.         (* [comment removed for export] *)
Definition AP_OPENSSL_CONFIGURED : Z := 0xba8ac0. (* [comment removed for export] *)
Definition AP_TSD_DC_SLOT : Z := TSD_MAIN + 8 * V_DC_KEY.        (* [comment removed for export] *)
Definition AP_TSD_INIT_SLOT : Z := TSD_MAIN + 8 * V_IN_INIT_KEY. (* [comment removed for export] *)
Definition AP_TSD_USED : Z := 0xba935a.         (* [comment removed for export] *)
Definition V_OPTSDONE_CNF : Z := 0x42.
Definition V_CR_NO_CUSTOMIZE : Z := 1.
(* [comment removed for export] *)
Notation cnf_stage := CtRepP.ApRepDefs.cnf_stage.
Notation CnfInit := CtRepP.ApRepDefs.CnfInit.
Notation CnfMid := CtRepP.ApRepDefs.CnfMid.
Notation stage_once := CtRepP.ApRepDefs.stage_once.
Notation stage_tsd := CtRepP.ApRepDefs.stage_tsd.
Notation SZ_OBJ_LOCK := CtRepP.ApRepDefs.SZ_OBJ_LOCK.
Notation SZ_ADDED := CtRepP.ApRepDefs.SZ_ADDED.
Notation SZ_ADDED_BUCKETS := CtRepP.ApRepDefs.SZ_ADDED_BUCKETS.
Definition lhash_cells (bk : Z) : list cell :=
  [C8 (wz bk); C8 (wz AP_LH_COMP); C8 (wz AP_LH_HASH); C8 (wz AP_LH_HASHW); C8 (wz AP_LH_COMPW); C8 (wz AP_LH_DAW); C8 (wz AP_LH_DAAW);
   C4 (wz 8); C4 (wz 16); C4 (wz 0); C4 (wz 8); C8 (wz 512); C8 (wz 256); C8 (wz 0); C4 (wz 0); C4 (wz 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation ap_env := CtRepP.ApRepDefs.ap_env.
Notation mkE := CtRepP.ApRepDefs.mkE.
Notation e_bio := CtRepP.ApRepDefs.e_bio.  Notation e_es := CtRepP.ApRepDefs.e_es.  Notation e_mk := CtRepP.ApRepDefs.e_mk.
Notation e_sa := CtRepP.ApRepDefs.e_sa.    Notation e_nd := CtRepP.ApRepDefs.e_nd.  Notation e_xl := CtRepP.ApRepDefs.e_xl.
Notation p_bio := CtRepP.ApRepDefs.p_bio.  Notation p_es := CtRepP.ApRepDefs.p_es.  Notation p_mk := CtRepP.ApRepDefs.p_mk.
Notation p_sa := CtRepP.ApRepDefs.p_sa.    Notation p_nd := CtRepP.ApRepDefs.p_nd.  Notation p_xl := CtRepP.ApRepDefs.p_xl.
Notation e_stage := CtRepP.ApRepDefs.e_stage.
Notation env_blocks := CtRepP.ApRepDefs.env_blocks.
Notation env_ids := CtRepP.ApRepDefs.env_ids.
Notation badr := CtRepP.ApRepDefs.badr.
Notation blocks_match := CtRepP.ApRepDefs.blocks_match.
Notation ap_env_ok := CtRepP.ApRepDefs.ap_env_ok.

Notation crypto_statics := BnRepDefs.crypto_statics.
Definition OFF_MK_SA : Z := 24.
Notation optb_ok := CtRepP.ApRepDefs.optb_ok.
Notation wl := CtRepP.ApRepDefs.wl.

Section WithSegs.
Let segs := ctasegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition realloc_statics (m : mem) : Prop := ro_cells segs m CR_REALLOC_IMPL [C8 (wz CRYPTO_REALLOC)].

(* [comment removed for export] *)
Definition ap_statics_fixed (m : mem) (E : ap_env) : Prop :=
  crypto_statics m /\ realloc_statics m
  /\ True                                                              (* [comment removed for export] *)
  /\ ro_cells segs m TL_MASTER_ONCE [C4 (wz 2)] /\ ro_cells segs m TL_MASTER_INIT [C1 (Z_to_bv 8 1)]
  /\ ro_cells segs m TL_MASTER_KEY [C4 (wz K_MASTER_KEY)]
  /\ ro_cells segs m AP_DC_INITED [C1 (Z_to_bv 8 1)]
  /\ ro_cells segs m AP_DC_KEY [C4 (wz V_DC_KEY)]
  /\ ro_cells segs m AP_DC_ONCE1 [C4 (wz 2)] /\ ro_cells segs m AP_DC_ONCE1_RET [C4 (wz 1)]
  /\ ro_cells segs m AP_DC_ONCE2 [C4 (wz 2)] /\ ro_cells segs m AP_DC_ONCE2_RET [C4 (wz 1)]
  /\ ro_cells segs m AP_DC_EXLOCK [C8 (wz (e_xl E))]
  /\ ro_cells segs m AP_DC_EXMETH_BIO [C8 (wz 0)]
  /\ ro_cells segs m AP_DC_CONF_DIAG [C4 (wz 0)]
  /\ ro_cells segs m OI_STOPPED [C1 (Z_to_bv 8 0)]
  /\ ro_cells segs m OI_BASE_ONCE [C4 (wz 2)] /\ ro_cells segs m OI_BASE_RET [C4 (wz 1)]
  /\ ro_cells segs m AP_IN_INIT_KEY [C4 (wz V_IN_INIT_KEY)]
  /\ (exists lk, ro_cells segs m AP_OPTSDONE_LOCK [C8 lk])
  /\ ro_cells segs m AP_TSD_DC_SLOT [C8 (wz 0)]
  /\ ro_cells segs m TSD_MK_SLOT [C8 (wz (e_mk E))]
  /\ (exists u : byte, rw_cells segs m AP_TSD_USED [C1 u])       (* [comment removed for export] *)
  /\ ro_cells segs m (AP_CONF_METH + 8) [C8 (wz DEF_CREATE); C8 (wz DEF_INIT_DEFAULT); C8 (wz DEF_DESTROY)]
  /\ ro_cells segs m (AP_CONF_METH + 72) [C8 (wz DEF_LOAD)]
  /\ (exists cb : word, rw_cells segs m AP_CANCELBUF [C8 cb])
  /\ (exists b0 : byte, rw_cells segs m OI_BASE_INITED [C1 b0])
  /\ rw_cells segs m OI_DO_CLEANUP [C1 (Z_to_bv 8 0)].

(* [comment removed for export] *)
Definition ap_statics_cnf (m : mem) (OW : list block) (sg : cnf_stage) (cnf : option (bptr * bptr * bptr)) : Prop :=
  match cnf with
  | None =>
      rw_cells segs m AP_CONFIG_ONCE [C4 (wz (stage_once sg))] /\ rw_cells segs m AP_CONFIG_INITED [C4 (wz 0)]
      /\ rw_cells segs m OI_OPTSDONE [C8 (wz V_OI_OPTSDONE)]
      /\ rw_cells segs m AP_OBJ_ONCE [C4 (wz 0)] /\ rw_cells segs m AP_OBJ_INITED [C4 (wz 0)]
      /\ rw_cells segs m AP_OBJ_ADDED [C8 (wz 0)] /\ rw_cells segs m AP_OBJ_LOCK [C8 (wz 0)]
      /\ rw_cells segs m AP_TSD_INIT_SLOT [C8 (wz (stage_tsd sg))]
  | Some (lk, lh, bk) =>
      rw_cells segs m AP_CONFIG_ONCE [C4 (wz 2)] /\ rw_cells segs m AP_CONFIG_INITED [C4 (wz 1)]
      /\ rw_cells segs m OI_OPTSDONE [C8 (wz V_OPTSDONE_CNF)]
      /\ rw_cells segs m AP_OBJ_ONCE [C4 (wz 2)] /\ rw_cells segs m AP_OBJ_INITED [C4 (wz 1)]
      /\ rw_cells segs m AP_OBJ_ADDED [C8 (wz (badr OW lh))] /\ rw_cells segs m AP_OBJ_LOCK [C8 (wz (badr OW lk))]
      /\ rw_cells segs m AP_TSD_INIT_SLOT [C8 (wz (2^64 - 1))]
      /\ In (lk, badr OW lk, SZ_OBJ_LOCK) OW /\ In (lh, badr OW lh, SZ_ADDED) OW /\ In (bk, badr OW bk, SZ_ADDED_BUCKETS) OW
      /\ rw_cells segs m (badr OW lk) mutex_free_cells
      /\ rw_cells segs m (badr OW lh) (lhash_cells (badr OW bk))
      /\ rw_cells segs m (badr OW bk) (c8s (repeat 0 16))
  end.

(* [comment removed for export] *)
Definition ap_img (m : mem) : Prop := relro_pristine m.

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
Definition ap_state (st : ap_st bptr) (m : mem) (OW : list block) (E : ap_env) (bo : Z * Z) : Prop :=
  ap_env_ok E OW
  /\ ap_statics_fixed m E /\ ap_statics_cnf m OW (e_stage E) (as_cnf st)
  /\ tl_chain m E /\ exlock_free m E
  /\ bio_out_rep m E (fst bo) (snd bo)
  /\ err_rep m E OW st.

(* [comment removed for export] *)
Definition ap_lib_state (ls : ap_ls bptr) (m : mem) (OW : list block) (E : ap_env) : Prop :=
  ap_ls_wf ls /\ e_stage E = CnfInit /\ exists nw, ap_state (st_of_ls ls) m OW E (0, nw).

Definition ap_lib_inv (ls : ap_ls bptr) (m : mem) (OW : list block) : Prop := exists E, ap_lib_state ls m OW E.

End WithSegs.

(* [comment removed for export] *)
Definition LIBW_S : list (Z * Z) := [(0x5aebe0, 0x5af400); (0xba46c0, 0xba8ae0); (0xba935a, 0xba935b); (0xba9390, 0xba9398); (0xbca7a0, 0xbcab98)].
