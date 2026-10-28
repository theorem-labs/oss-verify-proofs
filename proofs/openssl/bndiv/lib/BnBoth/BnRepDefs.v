(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition BN_B1 : Z := 0xbd6080.   Definition BN_B2 : Z := 0xbd60a0.   Definition BN_B3 : Z := 0xbd60c0.
Definition BN_B4 : Z := 0xbd60e0.   Definition BN_B5 : Z := 0xbd6100.   Definition BN_CTX : Z := 0xbd6120.
(* [comment removed for export] *)
Definition CR_MALLOC_IMPL : Z := 0x5e6680.   (* [comment removed for export] *)
Definition CR_FREE_IMPL : Z := 0x5e66c0.     (* [comment removed for export] *)
Definition CR_GOT_MALLOC : Z := 0x5e22d8.    (* [comment removed for export] *)
Definition CR_GOT_FREE : Z := 0x5e22f0.      (* [comment removed for export] *)
Definition CR_MEMSET_FUNC : Z := 0x5e6660.   (* [comment removed for export] *)
Definition CR_NO_CUSTOMIZE : Z := 0xbd6140.  (* [comment removed for export] *)
Definition CRYPTO_MALLOC : Z := 0x1f261c.
Definition CRYPTO_FREE : Z := 0x1f2b40.
Definition MEMSET : Z := 0x1bcc34.           (* [comment removed for export] *)
(* [comment removed for export] *)
Definition OI_STOPPED : Z := 0xbd6620.       (* [comment removed for export] *)
Definition OI_OPTSDONE : Z := 0xbd66c0.      (* [comment removed for export] *)
Definition OI_BASE_ONCE : Z := 0xbd66e0.     (* [comment removed for export] *)
Definition OI_BASE_RET : Z := 0xbd6700.      (* [comment removed for export] *)
Definition TL_MASTER_ONCE : Z := 0xbd61e0.   (* [comment removed for export] *)
Definition TL_MASTER_KEY : Z := 0xbd6200.    (* [comment removed for export] *)
Definition TL_MASTER_KEY_IDX : Z := 3.       (* [comment removed for export] *)
Definition TSD_MAIN : Z := 0xbfc1f8.         (* [comment removed for export] *)
(* [comment removed for export] *)
Definition OSSL_BASE_INITED : Z := 0xbd65e0.
Definition OSSL_DO_GLOBAL_CLEANUP : Z := 0xbd6600.
Definition ossl_exit_cells (m : mem) : Prop :=
  exists b0 : byte, rw_cells bsegs m OSSL_BASE_INITED [C1 b0] /\ rw_cells bsegs m OSSL_DO_GLOBAL_CLEANUP [C1 (Z_to_bv 8 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition bn_cells (D : Z) (b : bignum bptr) : list cell :=
  [C8 (wz D); C4 (wz (Z.of_nat (bn_top b))); C4 (wz (Z.of_nat (bn_dmax b))); C4 (wz (Z.b2z (bn_neg b))); C4 (wz (bn_flags b))].

(* [comment removed for export] *)
Definition bn_arr (m : mem) (OW : list block) (D : Z) (b : bignum bptr) : Prop :=
  match bn_d b with
  | None => D = 0 /\ bn_buf b = []
  | Some p => In (p, D, 8 * Z.of_nat (bn_dmax b)) OW /\ u64arr bsegs m D (wlimbs (bn_buf b))
  end.

Definition bn_rep (m : mem) (OW : list block) (a : Z) (b : bignum bptr) : Prop :=
  exists D, rw_cells bsegs m a (bn_cells D b) /\ bn_arr m OW D b.

(* [comment removed for export] *)
Definition bnR : Type := Z -> bignum bptr -> bnref -> Prop.
Definition repR (m : mem) (OW : list block) : bnR := fun a b _ => bn_rep m OW a b.
Definition holeR (hs : list bnref) (m : mem) (OW : list block) : bnR := fun a b r => In r hs \/ bn_rep m OW a b.

(* [comment removed for export] *)
Fixpoint bns_gen (R : bnR) (a : Z) (l : list (bignum bptr)) (i : nat) : Prop :=
  match l with
  | [] => True
  | b :: l' => R a b (RPool i) /\ bns_gen R (a + 24) l' (S i)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ctx_cells (H Cu I : Z) (c : bn_ctx bptr) : list cell :=
  [C8 (wz H); C8 (wz Cu); C8 (wz H);
   C4 (wz (Z.of_nat (cx_pused c))); C4 (wz (Z.of_nat (cx_psize c)));
   C8 (wz I); C4 (wz (Z.of_nat (length (cx_frames c)))); C4 (wz (Z.of_nat (cx_ssize c)));
   C4 (wz (Z.of_nat (cx_used c))); C4 (wz (Z.of_nat (cx_err_stack c))); C4 (wz (Z.b2z (cx_too_many c)));
   C4 (wz 0); C8 (wz 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pool_mem (m : mem) (H Cu : Z) (c : bn_ctx bptr) : Prop :=
  match cx_head c with
  | None => Cu = 0 /\ cx_current c = None
  | Some p => rw_cells bsegs m (H + 384) [C8 (wz 0); C8 (wz 0)]
              /\ ((cx_current c = None /\ Cu = 0) \/ (cx_current c = Some p /\ Cu = H))
  end.

Definition pool_gen (R : bnR) (cxo : bool) (m : mem) (OW : list block) (H Cu : Z) (c : bn_ctx bptr) : Prop :=
  match cx_head c with
  | None => H = 0 /\ cx_vals c = []
  | Some p => In (p, H, 400) OW /\ length (cx_vals c) = 16%nat /\ bns_gen R H (cx_vals c) 0
  end /\ (cxo = false -> pool_mem m H Cu c).

(* [comment removed for export] *)
Definition stack_rep (m : mem) (OW : list block) (I : Z) (c : bn_ctx bptr) : Prop :=
  match cx_indexes c with
  | None => I = 0 /\ cx_ssize c = 0%nat /\ cx_frames c = []
  | Some q => In (q, I, 128) OW /\ cx_ssize c = 32%nat
              /\ exists stale : list word,
                   (length (cx_frames c) + length stale = 32)%nat
                   /\ u32arr bsegs m I (map (fun k => wz (Z.of_nat k)) (cx_frames c) ++ stale)
  end.

Definition ctx_gen (R : bnR) (cxo : bool) (m : mem) (OW : list block) (a : Z) (c : bn_ctx bptr) : Prop :=
  exists H Cu I, (cxo = false -> rw_cells bsegs m a (ctx_cells H Cu I c) /\ stack_rep m OW I c) /\ pool_gen R cxo m OW H Cu c.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record bn_addrs : Type := mkAD {
  ad_b1 : Z; ad_b2 : Z; ad_b3 : Z; ad_b4 : Z; ad_b5 : Z; ad_ctx : Z;
  ad_p1 : bptr; ad_p2 : bptr; ad_p3 : bptr; ad_p4 : bptr; ad_p5 : bptr; ad_pc : bptr }.

Definition ad_ids (AD : bn_addrs) : list bptr := [ad_p1 AD; ad_p2 AD; ad_p3 AD; ad_p4 AD; ad_p5 AD; ad_pc AD].

Definition ad_blocks (OW : list block) (AD : bn_addrs) : Prop :=
  In (ad_p1 AD, ad_b1 AD, 24) OW /\ In (ad_p2 AD, ad_b2 AD, 24) OW /\ In (ad_p3 AD, ad_b3 AD, 24) OW
  /\ In (ad_p4 AD, ad_b4 AD, 24) OW /\ In (ad_p5 AD, ad_b5 AD, 24) OW /\ In (ad_pc AD, ad_ctx AD, 72) OW.

(* [comment removed for export] *)
Definition ad_statics (m : mem) (AD : bn_addrs) : Prop :=
  ro_cells bsegs m BN_B1 [C8 (wz (ad_b1 AD))] /\ ro_cells bsegs m BN_B2 [C8 (wz (ad_b2 AD))] /\ ro_cells bsegs m BN_B3 [C8 (wz (ad_b3 AD))]
  /\ ro_cells bsegs m BN_B4 [C8 (wz (ad_b4 AD))] /\ ro_cells bsegs m BN_B5 [C8 (wz (ad_b5 AD))] /\ ro_cells bsegs m BN_CTX [C8 (wz (ad_ctx AD))].

Definition bn_mem_gen (R : bnR) (cxo : bool) (ls : lstate bptr) (m : mem) (OW : list block) (AD : bn_addrs) : Prop :=
  ad_statics m AD /\ ad_blocks OW AD
  /\ R (ad_b1 AD) (ls_b1 ls) RB1 /\ R (ad_b2 AD) (ls_b2 ls) RB2 /\ R (ad_b3 AD) (ls_b3 ls) RB3
  /\ R (ad_b4 AD) (ls_b4 ls) RB4 /\ R (ad_b5 AD) (ls_b5 ls) RB5
  /\ ctx_gen R cxo m OW (ad_ctx AD) (ls_ctx ls).

Definition bn_mem (ls : lstate bptr) (m : mem) (OW : list block) (AD : bn_addrs) : Prop := bn_mem_gen (repR m OW) false ls m OW AD.

(* [comment removed for export] *)
Definition ref_at (ls : lstate bptr) (OW : list block) (AD : bn_addrs) (r : bnref) (a : Z) : Prop :=
  match r with
  | RB1 => a = ad_b1 AD | RB2 => a = ad_b2 AD | RB3 => a = ad_b3 AD | RB4 => a = ad_b4 AD | RB5 => a = ad_b5 AD
  | RPool i => exists p H, cx_head (ls_ctx ls) = Some p /\ In (p, H, 400) OW /\ (i < 16)%nat /\ a = H + 24 * Z.of_nat i
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition crypto_statics (m : mem) : Prop :=
  ro_cells bsegs m CR_MEMSET_FUNC [C8 (wz MEMSET)]
  /\ ro_cells bsegs m CR_MALLOC_IMPL [C8 (wz CRYPTO_MALLOC)]
  /\ ro_cells bsegs m CR_FREE_IMPL [C8 (wz CRYPTO_FREE)]
  /\ ro_cells bsegs m CR_NO_CUSTOMIZE [C1 (Z_to_bv 8 1)].

(* [comment removed for export] *)
Definition ES_CLEARED : list byte :=
  repeat (Z_to_bv 8 0) 704 ++ repeat (Z_to_bv 8 255) 64 ++ repeat (Z_to_bv 8 0) 136.

(* [comment removed for export] *)
Record err_addrs : Type := mkEA {
  ea_MK : Z; ea_SA : Z; ea_ND : Z; ea_ES : Z;
  ea_pk : bptr; ea_ps : bptr; ea_pn : bptr; ea_pe : bptr }.

Definition ea_ids (EA : err_addrs) : list bptr := [ea_pk EA; ea_ps EA; ea_pn EA; ea_pe EA].

(* [comment removed for export] *)
Definition err_statics (m : mem) : Prop :=
  ro_cells bsegs m OI_STOPPED [C1 (Z_to_bv 8 0)]
  /\ ro_cells bsegs m OI_OPTSDONE [C8 (wz 2)]
  /\ ro_cells bsegs m OI_BASE_ONCE [C4 (wz 2)] /\ ro_cells bsegs m OI_BASE_RET [C4 (wz 1)]
  /\ ro_cells bsegs m TL_MASTER_ONCE [C4 (wz 2)] /\ ro_cells bsegs m TL_MASTER_KEY [C4 (wz TL_MASTER_KEY_IDX)].

Definition err_mem (m : mem) (OW : list block) (EA : err_addrs) : Prop :=
  In (ea_pk EA, ea_MK EA, 72) OW /\ In (ea_ps EA, ea_SA EA, 32) OW /\ In (ea_pn EA, ea_ND EA, 128) OW /\ In (ea_pe EA, ea_ES EA, 904) OW
  /\ ro_cells bsegs m (TSD_MAIN + 8 * TL_MASTER_KEY_IDX) [C8 (wz (ea_MK EA))]        (* [comment removed for export] *)
  /\ ro_cells bsegs m (ea_MK EA + 24) [C8 (wz (ea_SA EA))]                           (* [comment removed for export] *)
  /\ (exists pad : list byte,
        ro_cells bsegs m (ea_SA EA) [C4 (wz 1); CB 4 pad; C8 (wz 0); C8 (wz 1); C8 (wz (ea_ND EA))])   (* [comment removed for export] *)
  /\ ro_cells bsegs m (ea_ND EA) [C8 (wz (ea_ES EA))]                                (* [comment removed for export] *)
  /\ rw_cells bsegs m (ea_ES EA) [CB 904 ES_CLEARED].

Definition err_inv (m : mem) (OW : list block) (EA : err_addrs) : Prop := err_statics m /\ err_mem m OW EA.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bn_state_hc (cxo : bool) (hs : list bnref) (ls : lstate bptr) (m : mem) (OW : list block) (AD : bn_addrs) (EA : err_addrs) : Prop :=
  st_okm ls /\ List.NoDup (ad_ids AD ++ ea_ids EA ++ map fst (blocks_of ls)) /\ bn_mem_gen (holeR hs m OW) cxo ls m OW AD.

(* [comment removed for export] *)
Definition lib_state_hc (cxo : bool) (hs : list bnref) (ls : lstate bptr) (m : mem) (OW : list block) (AD : bn_addrs) (EA : err_addrs) : Prop :=
  crypto_statics m /\ err_inv m OW EA /\ ossl_exit_cells m /\ bn_state_hc cxo hs ls m OW AD EA.

Notation lib_state_h := (lib_state_hc false).
Notation bn_state_h := (bn_state_hc false).
Definition bn_state := bn_state_hc false [].
Definition lib_state := lib_state_hc false [].

(* [comment removed for export] *)
Definition lib_inv_bn (ls : lstate bptr) (m : mem) (OW : list block) : Prop :=
  exists AD EA, lib_state ls m OW AD EA.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition BN_NEW_BYTES : list byte := repeat (Z_to_bv 8 0) 20 ++ [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].

Definition init_factsA (m : mem) (OW : list block) : Prop :=
  exists (AD : bn_addrs) (EA : err_addrs),
    List.NoDup (ad_ids AD ++ ea_ids EA)
    /\ ad_blocks OW AD
    /\ ad_statics m AD
    /\ rw_cells bsegs m (ad_b1 AD) [CB 24 BN_NEW_BYTES] /\ rw_cells bsegs m (ad_b2 AD) [CB 24 BN_NEW_BYTES]
    /\ rw_cells bsegs m (ad_b3 AD) [CB 24 BN_NEW_BYTES] /\ rw_cells bsegs m (ad_b4 AD) [CB 24 BN_NEW_BYTES]
    /\ rw_cells bsegs m (ad_b5 AD) [CB 24 BN_NEW_BYTES]
    /\ rw_cells bsegs m (ad_ctx AD) [CB 72 (repeat (Z_to_bv 8 0) 72)]
    /\ crypto_statics m /\ err_inv m OW EA /\ ossl_exit_cells m.

