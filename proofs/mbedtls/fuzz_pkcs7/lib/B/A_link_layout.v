(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Mem Cells HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require P_ecp_sinv P_pk_sinv.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_amemmove_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Record a_layout_ok (R : art_layout) : Prop := ALO {
  (* [comment removed for export] *)
  alo_img    : asan_img_ok (arl_AL R);
  alo_wf     : al_wf (arl_AL R);
  alo_dimg   : hl_img_lo (arl_L R) <= hl_data_lo (arl_L R) /\ hl_data_hi (arl_L R) <= hl_img_hi (arl_L R);
  alo_img_w  : hl_img_lo (arl_L R) <= 65536 /\ 987136 <= hl_img_hi (arl_L R);
  alo_roimg  : forall a : Z, ro_addr asegs (wa a) = true -> 0 <= a < 2 ^ 64 -> hl_img_lo (arl_L R) <= a < hl_img_hi (arl_L R);
  alo_primg  : forall a : Z, rtc_prist a -> hl_img_lo (arl_L R) <= a < hl_img_hi (arl_L R);
  alo_ceil   : hl_data_hi (arl_L R) <= @alloc_ceiling (arl_L R);
  alo_rtc    : forall m, arl_rtc R m -> asan_rtc m;
  (* [comment removed for export] *)
  alo_malloc   : arl_malloc R = 0x69480;
  alo_calloc   : arl_calloc R = 0x69484;
  alo_free     : arl_free R = 0x6947c;
  alo_amemcpy  : arl_amemcpy R = 0x67dbc;
  alo_amemset  : arl_amemset R = 0x68258;
  alo_memcpy_i : arl_memcpy_i R = 0x67db8;
  alo_memset_i : arl_memset_i R = 0x67db4;
  alo_memcmp_i : arl_memcmp_i R = 0x58704;
  alo_smalloc0 : arl_smalloc R 0 = 0x52ef8;
  alo_smalloc1 : arl_smalloc R 1 = 0x5306c;
  alo_smalloc2 : arl_smalloc R 2 = 0x531fc;
  alo_smalloc3 : arl_smalloc R 3 = 0x53398;
  alo_smalloc4 : arl_smalloc R 4 = 0x53544;
  alo_smalloc5 : arl_smalloc R 5 = 0x53710;
  alo_sfree5   : arl_sfree5 R = 0x5391c;
  alo_set00    : arl_set00 R = 0x6b228;
  alo_setf5    : arl_setf5 R = 0x6b330;
  alo_setf8    : arl_setf8 R = 0x6b348;
  alo_rip      : arl_rip R = 0x6aee4;
  alo_uar_got  : arl_uar_got R = 0x0f5ea8;
  (* [comment removed for export] *)
  alo_need_malloc  : 0 <= arl_need_malloc R;
  alo_need_free    : 0 <= arl_need_free R;
  alo_need_smalloc : 0 <= arl_need_smalloc R;
  alo_need_amem    : 0 <= arl_need_amem R;
  alo_need_bcmp    : 0 <= arl_need_bcmp R;
  alo_need_setsh   : 0 <= arl_need_setsh R;
  alo_need_rip     : 0 <= arl_need_rip R;
  (* [comment removed for export] *)
  alo_nsh          : arl_need_setsh R <= Z.max (arl_need_malloc R) (Z.max (arl_need_free R) (arl_need_amem R));
  (* [comment removed for export] *)
  alo_ids_lok      : P_ecp_sinv.ecp_ids_lok (arl_L R) 0x63c0a0 0x63c0c0;
  alo_mc_lok       : P_pk_sinv.mc_lok (arl_L R) 0x63c120
}.

Record a_hia_ok (R : art_layout) (HIA : artA asegs R) : Prop := AHO {
  aho_nodup : forall (h : HST asegs R HIA) (LB LF : list blk) (m : mem), HM asegs R HIA h LB LF m -> List.NoDup (map fst LB);
  (* [comment removed for export] *)
  aho_amemmove : amemmove_stmtA asegs R HIA A_ASAN_MEMMOVE;
  (* [comment removed for export] *)
  aho_ssmap : forall (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (g : Z),
    HM asegs R HIA h LB LF m -> arl_stklo R <= g < hstkhi asegs R HIA h -> m (wa (shadow_of (arl_AL R) g)) <> None;
  (* [comment removed for export] *)
  aho_hmperm : forall (h : HST asegs R HIA) (LB LB' LF : list blk) (m : mem), HM asegs R HIA h LB LF m -> Permutation.Permutation LB LB' ->
    exists h', HM asegs R HIA h' LB' LF m /\ hcs asegs R HIA h' = hcs asegs R HIA h /\ htop asegs R HIA h' = htop asegs R HIA h
               /\ hstkhi asegs R HIA h' = hstkhi asegs R HIA h /\ hflag asegs R HIA h' = hflag asegs R HIA h
               /\ havol asegs R HIA h' = havol asegs R HIA h /\ hfr asegs R HIA h' = hfr asegs R HIA h
               /\ (forall mo, HK asegs R HIA h' mo <-> HK asegs R HIA h mo)
}.

Lemma alo_gsb : forall R, a_layout_ok R -> al_gsb (arl_AL R) = AGSB.
Proof. intros R LO. ddestruct (alo_img R LO) as (_ & _ & _ & G). exact G. Qed.

(* [comment removed for export] *)
Ltac alink_lo LO :=
  first [ exact (alo_img _ LO) | exact (alo_wf _ LO) | exact (alo_dimg _ LO) | exact (alo_img_w _ LO) | exact (alo_roimg _ LO)
        | exact (alo_primg _ LO) | exact (alo_ceil _ LO) | exact (alo_rtc _ LO)
        | exact (alo_malloc _ LO) | exact (alo_calloc _ LO) | exact (alo_free _ LO) | exact (alo_amemcpy _ LO) | exact (alo_amemset _ LO)
        | exact (alo_memcpy_i _ LO) | exact (alo_memset_i _ LO) | exact (alo_memcmp_i _ LO)
        | exact (alo_smalloc0 _ LO) | exact (alo_smalloc1 _ LO) | exact (alo_smalloc2 _ LO) | exact (alo_smalloc3 _ LO)
        | exact (alo_smalloc4 _ LO) | exact (alo_smalloc5 _ LO) | exact (alo_sfree5 _ LO) | exact (alo_uar_got _ LO)
        | exact (alo_set00 _ LO) | exact (alo_setf5 _ LO) | exact (alo_setf8 _ LO) | exact (alo_rip _ LO)
        | exact (alo_need_malloc _ LO) | exact (alo_need_free _ LO) | exact (alo_need_smalloc _ LO) | exact (alo_need_amem _ LO)
        | exact (alo_need_bcmp _ LO) | exact (alo_need_setsh _ LO) | exact (alo_need_rip _ LO) | exact (alo_gsb _ LO) | exact (alo_nsh _ LO) ].
