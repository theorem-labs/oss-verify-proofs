(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_libiface_pem D_agree Fz_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_grow Fz_W1_writec Fz_W1_read Fz_W1_pploc Fz_W3_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition J_END1 : Z := 0x30c450.   (* [comment removed for export] *)
Definition J_END : Z := 0x30c45c.   (* [comment removed for export] *)
Definition J_FREE1 : Z := 0x30c3dc.   (* [comment removed for export] *)
Definition J_FREE1X : Z := 0x30c3f8.   (* [comment removed for export] *)
Definition J_RAISE1 : Z := 0x30c3a4.   (* [comment removed for export] *)
Definition J_GN : Z := 0x30c340.   (* [comment removed for export] *)
Definition J_GNG : Z := 0x30c388.   (* [comment removed for export] *)
Definition J_NAME : Z := 0x30c56c.   (* [comment removed for export] *)
Definition J_NGETS : Z := 0x30c5e0.   (* [comment removed for export] *)
Definition J_HD : Z := 0x30c658.   (* [comment removed for export] *)
Definition J_HD2 : Z := 0x30c6d4.   (* [comment removed for export] *)
Definition J_PUTS : Z := 0x30c71c.   (* [comment removed for export] *)
Definition J_GETS1 : Z := 0x30c758.   (* [comment removed for export] *)
Definition J_GETS2 : Z := 0x30c7b0.   (* [comment removed for export] *)
Definition J_ENDLINE : Z := 0x30c7e8.   (* [comment removed for export] *)
Definition J_LFREE : Z := 0x30c8b4.   (* [comment removed for export] *)
Definition J_RAISE2 : Z := 0x30c850.   (* [comment removed for export] *)
Definition J_FREE2 : Z := 0x30c888.   (* [comment removed for export] *)
Definition J_TAIL : Z := 0x30c8cc.   (* [comment removed for export] *)
Definition J_INI : Z := 0x30c954.   (* [comment removed for export] *)
Definition J_DEC : Z := 0x30ca04.   (* [comment removed for export] *)
Definition J_RZT : Z := 0x30cb28.   (* [comment removed for export] *)
Definition J_OUTFREE : Z := 0x30cbb4.   (* [comment removed for export] *)
Definition J_RELOAD : Z := 0x30cc28.   (* [comment removed for export] *)
Definition J_RAISE0 : Z := 0x30c220.   (* [comment removed for export] *)
Definition J_J0N : Z := 0x30c268.   (* [comment removed for export] *)
Definition J_J0G : Z := 0x30c2fc.   (* [comment removed for export] *)
Definition LIT_FILE : Z := 0xa18c0.     Definition LIT_FILE_SZ : Z := 21.   (* [comment removed for export] *)
Definition LIT_FUNC : Z := 0xa1c00.     Definition LIT_FUNC_SZ : Z := 16.
Definition LIT_GETNAME : Z := 0xa1c80.  Definition LIT_GETNAME_SZ : Z := 9.
Definition LIT_GETHD : Z := 0xa1cc0.    Definition LIT_GETHD_SZ : Z := 20.
Definition LIT_BEGIN : Z := 0xa1b80.    Definition LIT_BEGIN_SZ : Z := 12.
Definition LIT_TAIL : Z := 0xa1ba0.     Definition LIT_TAIL_SZ : Z := 7.
Definition LIT_ENDSTR : Z := 0xa1bc0.   Definition LIT_ENDSTR_SZ : Z := 10.
Definition e_icpt_strncmp : Z := 0x1ac574.
Definition e_icpt_memchr : Z := 0x1ac590.
Definition e_icpt_strlen : Z := 0x1ac568.
Definition FF_MAGIC : Z := 0x41b58ab3.
Definition FF_DESCR : Z := 0x24d8a.
Definition FF_MAGIC_RET : Z := 0x45e0360e.

(* [comment removed for export] *)
Definition PEM_RAS_new : list Z := [0x30c298; 0x30c2a4].
Definition PEM_RAS_pmal : list Z := [0x30c2c4; 0x30c598; 0x30c5d4; 0x30ca28; 0x30ca54].
Definition PEM_RAS_pfree : list Z := [0x30c3f4; 0x30c478; 0x30c5c4; 0x30c8a0; 0x30c8cc; 0x30cbd8; 0x30cc10].
Definition PEM_RAS_bfree : list Z := [0x30c480; 0x30c488].
Definition PEM_RAS_puts : list Z := [0x30c730].
Definition PEM_RAS_enew : list Z := [0x30c228; 0x30c3ac; 0x30c858; 0x30c90c; 0x30cb30].
Definition PEM_RAS_edbg : list Z := [0x30c244; 0x30c3c8; 0x30c874; 0x30c928; 0x30cb4c].
Definition PEM_RAS_eerr : list Z := [0x30c25c; 0x30c3dc; 0x30c888; 0x30c93c; 0x30cb60].
Definition PEM_RAS_cnew : list Z := [0x30c950].
Definition PEM_RAS_cfree : list Z := [0x30c464].
Definition PEM_RAS : list Z :=
  PEM_RAS_new ++ PEM_RAS_pmal ++ PEM_RAS_pfree ++ PEM_RAS_bfree ++ PEM_RAS_puts ++ PEM_RAS_enew ++ PEM_RAS_edbg ++ PEM_RAS_eerr ++ PEM_RAS_cnew ++ PEM_RAS_cfree.
Definition PEM_SITES : list (Z * Z) := map (fun r => (r, FZ_PEM_READ_BIO)) PEM_RAS.
Definition PEM_CALLS : list (Z * Z) :=
     map (fun r => (r, FZ_BIO_NEW)) PEM_RAS_new
  ++ concat (map (fun r => [(r, FZ_PEM_MALLOC); (r, e_CRYPTO_malloc); (r, e_CRYPTO_secure_malloc)]) PEM_RAS_pmal)
  ++ concat (map (fun r => [(r, FZ_PEM_FREE); (r, e_CRYPTO_free); (r, e_free); (r, e_CRYPTO_secure_clear_free)]) PEM_RAS_pfree)
  ++ map (fun r => (r, FZ_BIO_FREE)) PEM_RAS_bfree
  ++ map (fun r => (r, FZ_BIO_PUTS)) PEM_RAS_puts
  ++ map (fun r => (r, FZ_ERR_NEW)) PEM_RAS_enew
  ++ map (fun r => (r, FZ_ERR_SET_DEBUG)) PEM_RAS_edbg
  ++ map (fun r => (r, FZ_ERR_SET_ERROR)) PEM_RAS_eerr
  ++ concat (map (fun r => [(r, FZ_EVP_CTX_NEW); (r, e_CRYPTO_zalloc)]) PEM_RAS_cnew)
  ++ concat (map (fun r => [(r, FZ_EVP_CTX_FREE); (r, e_CRYPTO_free); (r, e_free)]) PEM_RAS_cfree).

(* [comment removed for export] *)
Definition ff_cells (hj : list byte) (lenv : word) (j1 : list byte) (tav : word) (j2 : list byte) (bmv : word) (j3 : list byte) : list cell :=
  [C8 (wz FF_MAGIC); C8 (wz FF_DESCR); CB 16 hj; C4 lenv; CB 12 j1; C4 tav; CB 12 j2; C8 bmv; CB 48 j3].
(* [comment removed for export] *)
Definition ff_shadow (sj : list byte) : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4);
   C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); CB 4 sj].

Section W3. 
  Variable RT : rt_sig.
  Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
  Variable errst_at_rest : Z -> list (Z * Z) -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list (Z * Z) -> mem -> Prop.
  Variables FZ_SITES FZ_CALLS : list (Z * Z).

  (* [comment removed for export] *)
  Record pem_entry : Type := PEMENT {
    e_ra : word; e_sp : word; e_gp : word; e_s0 : word; e_s1 : word; e_s2 : word; e_s3 : word; e_s4 : word; e_s5 : word; e_s6 : word; e_s7 : word;
    e_s8 : word; e_s9 : word; e_s10 : word; e_s11 : word;
    e_Σ : rts RT; e_PMc : Model -> Prop; e_m : mem; e_lo : Z; e_outer : list Z; e_canary : word; e_LBL : list (Z * Z); e_E : Z;
    e_K : mbk; e_BI : Z; e_meth : Z; e_blen : Z; e_bmax : Z; e_boff : Z; e_flags : Z;
    e_PN : Z; e_PH : Z; e_PD : Z; e_PLN : Z; e_on : word; e_oh : word; e_od : word; e_ol : word;
    e_pd : Z; e_f : Z; e_fsj : list byte }.
  Definition e_PL (en : pem_entry) : Z := bv_unsigned (e_sp en).            (* [comment removed for export] *)
  Definition e_sp1 (en : pem_entry) : Z := e_PL en - 352 - e_pd en.         (* [comment removed for export] *)
  Definition e_plen (en : pem_entry) : Z := e_blen en - e_boff en.
  Definition e_live (en : pem_entry) : list (Z * Z) := rt_live RT (e_Σ en).
  Definition e_frames (en : pem_entry) : list (Z * nat) := rt_frames RT (e_Σ en).
  (* [comment removed for export] *)
  Definition pem_saved (en : pem_entry) : list cell :=
    [C8 (e_s11 en); C8 (e_s10 en); C8 (e_s9 en); C8 (e_s8 en); C8 (e_s7 en); C8 (e_s6 en); C8 (e_s5 en); C8 (e_s4 en); C8 (e_s3 en); C8 (e_s2 en); C8 (e_s1 en);
     C8 (e_s0 en); C8 (e_ra en)].
  (* [comment removed for export] *)
  Definition pem_W (en : pem_entry) : list (Z * Z) :=
    [(e_PN en, e_PN en + 8); (e_PH en, e_PH en + 8); (e_PD en, e_PD en + 8); (e_PLN en, e_PLN en + 8); (e_E en, e_E en + 904)]
    ++ mbio_W (e_K en) (e_bmax en) ++ lib_W (e_LBL en).
  (* [comment removed for export] *)
  Definition loc_E (en : pem_entry) (hBv dBv : Z) : list cell :=
    [C8 (wz (e_PD en)); C8 (wz (e_PH en)); C8 (wz (e_PN en)); C8 (wz (e_f en)); C8 (wz hBv); C8 (wz dBv); C8 (wz (e_f en)); C8 (wz (e_flags en));
     C8 (wz (shad (e_PN en))); C8 (wz (shad (e_PLN en))); C8 (wz (e_PLN en)); C8 (wz (shad (e_PD en))); C8 (wz (shad (e_PH en))); C8 (wz (e_BI en))].
  (* [comment removed for export] *)
  Definition loc_F (en : pem_entry) : list cell := [C8 (wz (e_f en + 48)); C8 (wz (e_f en + 32)); C8 (wz (e_f en + 64))].
  (* [comment removed for export] *)
  Definition loc_H (LB2 tmp : Z) : list cell :=
    [C8 (wz (Z.land (LB2 + 253) 7)); C8 (wz (Z.land LB2 7)); C8 (wz tmp); C8 (wz (shad (LB2 + 253))); C8 (wz (LB2 + 253)); C8 (wz (shad LB2)); C8 (wz LIT_ENDSTR)].

  Definition pem_post (en : pem_entry) : config -> Prop :=
    fun c => exists (Σ' : rts RT),
         apost RT (e_Σ en) Σ' (e_PMc en) (e_ra en) (e_sp en) (e_gp en) (wz TP_A) (e_s0 en) (e_s1 en) (e_s2 en) (e_s3 en) (e_s4 en) (e_s5 en) (e_s6 en) (e_s7 en)
               (e_s8 en) (e_s9 en) (e_s10 en) (e_s11 en) (e_lo en) (e_m en) (e_live en) (pem_W en) (e_canary en)
           (fun v m' => sec_off m' /\ pem_read_res libenv errst_live (e_K en) (e_BI en) (e_meth en) (e_blen en) (e_bmax en) (e_boff en)
                                      (e_PN en) (e_PH en) (e_PD en) (e_PLN en) (e_E en) (e_LBL en) (e_live en) v (rt_live RT Σ') m') c
      /\ rt_frames RT Σ' = e_frames en /\ rt_sp0 RT Σ' = rt_sp0 RT (e_Σ en) /\ rt_credit RT (e_Σ en) - pem_credit (e_plen en) <= rt_credit RT Σ'
      /\ rt_cg RT Σ' = rt_cg RT (e_Σ en).

  (* [comment removed for export] *)
  Definition pem_com (en : pem_entry) (Σ : rts RT) (m : mem) (off crem lrem : Z) (cur : list (Z * Z)) : Prop :=
       ART RT Σ m /\ mem_inv asegs m /\ stk asegs m (e_lo en) (e_sp1 en)
    /\ (e_pd en = 0 \/ e_pd en = 16) /\ (e_PL en) mod 32 = e_pd en /\ e_PL en + 16 <= USTACK_TOP
    /\ rt_sp0 RT Σ - STACK_WIN <= e_lo en /\ e_lo en + RT_STACK + PEM_CALLEE_STACK <= e_sp1 en /\ 0x10007fff8000 <= e_lo en
    /\ cl_env m (Z_to_bv 8 1) (e_canary en) /\ sec_off m
    /\ libenv m (e_LBL en) (e_E en) /\ incl_live (e_LBL en) (e_live en) /\ In (e_E en, 904) (e_live en) /\ ~ In (e_E en, 904) (e_LBL en)
    /\ (forall e, In e ((e_E en, 904) :: e_LBL en) -> ~ In (fst e) (mbio_blocks (e_K en) ++ map fst cur))
    /\ mbio_rep (rt_live RT Σ) m (e_K en) (e_BI en) (e_meth en) (e_blen en) (e_bmax en) off /\ e_boff en <= off <= e_blen en /\ (0 <= e_boff en /\ e_blen en < 2 ^ 26)
    /\ (forall e, In e (mbio_ent (e_K en) (e_bmax en)) -> In e (e_live en))
    (* [comment removed for export] *)
    /\ Permutation (rt_live RT Σ) (cur ++ e_live en) /\ (forall e, In e cur -> ~ In (fst e) (map fst (e_live en)))
    /\ List.NoDup (map fst cur ++ e_E en :: mbio_blocks (e_K en)) /\ (forall e, In e (rt_live RT Σ) -> 0 < snd e)
    (* [comment removed for export] *)
    /\ rt_frames RT Σ = (e_f en, 1%nat) :: e_frames en /\ (length (e_frames en) + 3 < FRAMES_MAX)%nat /\ rt_sp0 RT Σ = rt_sp0 RT (e_Σ en) /\ rt_cg RT Σ = rt_cg RT (e_Σ en)
    /\ Z.of_nat (length (rt_live RT Σ)) + lrem <= LIVE_MAX /\ 0 <= lrem
    /\ rt_credit RT (e_Σ en) - pem_credit (e_plen en) + crem <= rt_credit RT Σ /\ 0 <= crem /\ pem_credit (e_plen en) <= rt_credit RT (e_Σ en)
    /\ cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS /\ cg_sub PEM_SITES PEM_CALLS FZ_SITES FZ_CALLS
    /\ cg_ctx (rt_cg RT Σ) FZ_PEM_READ_BIO (bv_unsigned (e_ra en) :: e_outer en) /\ uw_chain m (e_sp en) (e_s0 en) (e_outer en)
    (* [comment removed for export] *)
    /\ 0 < e_f en /\ (e_f en) mod 64 = 0 /\ e_f en + 128 < USTACK_TOP /\ SEGTOP_A <= e_f en /\ (e_f en + 128 <= 0x7fff8000 \/ 0x10007fff8000 <= e_f en)
    /\ rw_cells asegs m (shad (e_f en)) (ff_shadow (e_fsj en))
    (* [comment removed for export] *)
    /\ rw_cells asegs m (e_PL en + -104) (pem_saved en)
    /\ rt_pres_fp (e_live en) (e_frames en) (e_PL en) (pem_W en) (e_m en) m
    /\ 0 <= e_flags en < 256
    (* [comment removed for export] *)
    /\ List.NoDup [e_PN en; e_PH en; e_PD en; e_PLN en]
    /\ Forall (fun P => P mod 8 = 0 /\ pp_loc (e_frames en) (e_m en) USTACK_TOP P) [e_PN en; e_PH en; e_PD en; e_PLN en]
    (* [comment removed for export] *)
    /\ fdfs_only (e_PMc en) /\ mat_stable (e_PMc en).

  (* [comment removed for export] *)
  Definition pem_frame (en : pem_entry) (m : mem) (j0 : list byte) (lH : list cell) (lF : list cell) (endv : word) (hBv dBv : Z) (x1 x2 : word) (gap : list byte) : Prop :=
       rw_cells asegs m (e_sp1 en) [CB 24 j0] /\ rw_cells asegs m (e_sp1 en + 24) lH /\ Z.of_nat (cells_size lH) = 56
    /\ rw_cells asegs m (e_sp1 en + 80) lF /\ Z.of_nat (cells_size lF) = 24
    /\ rw_cells asegs m (e_sp1 en + 104) [C8 endv] /\ rw_cells asegs m (e_sp1 en + 112) (loc_E en hBv dBv)
    /\ rw_cells asegs m (e_sp1 en + 224) [C8 x1; C8 x2; C8 (wz (e_f en))] /\ rw_cells asegs m (e_sp1 en + 248) [CB (Z.to_nat (e_pd en)) gap].

  (* [comment removed for export] *)
  Definition pem_err (en : pem_entry) (Σ : rts RT) (strs : list (Z * Z)) (m : mem) : Prop :=
       ((strs = [] /\ errst_at_rest (e_E en) [] m) \/ (exists top bot, errst_live (e_E en) top bot strs m /\ (length strs <= 2)%nat))
    /\ Forall (fun e => 0 < snd e <= 64) strs /\ (forall e, In e strs -> In e (rt_live RT Σ)) /\ (forall e, In e strs -> ~ In (fst e) (map fst (e_live en))).

  (* [comment removed for export] *)
  Definition out_null (en : pem_entry) (m : mem) : Prop :=
    rw_cells asegs m (e_PN en) [C8 (wz 0)] /\ rw_cells asegs m (e_PH en) [C8 (wz 0)] /\ rw_cells asegs m (e_PD en) [C8 (wz 0)] /\ rw_cells asegs m (e_PLN en) [C8 (wz 0)].

  (* [comment removed for export] *)
  Definition pem_ms (en : pem_entry) (pc : Z) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) : machine_state :=
    MS (mkR ra (wz (e_sp1 en)) (e_gp en) (wz TP_A) t0 t1 t2 (e_sp en) (wz (e_sp1 en)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
            s6 s7 (wz (shad (e_f en))) (wz SHB) s10 s11 t3 t4 t5 t6) F (wz pc) fc None m (seg_rom asegs).
  Definition pem_at (en : pem_entry) (Σ : rts RT) (ms : machine_state) : Prop := cps asegs (ASTA RT Σ (e_PMc en) (eq ms)) (pem_post en).

  (* [comment removed for export] *)
  Definition C_END : Z := 16.
  (* [comment removed for export] *)
  Definition grow_cap (en : pem_entry) : Z := gr_n (2 * e_plen en + 8) + gr_n (2 * e_plen en + 8) / 4 + 2 ^ 16.
  Definition grow_pot (en : pem_entry) (maxX maxY : Z) : Z := 10 * (grow_cap en - maxX - maxY).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition END0_stmt : Prop :=
    forall (en : pem_entry) Σ m off crem lrem strs (nj : nat) (jj : list byte) hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 s11 t3 t4 t5 t6 : word),
    pem_com en Σ m off crem lrem strs -> pem_err en Σ strs m -> C_END <= crem ->
    rw_cells asegs m (e_sp1 en) [CB nj jj] -> Z.of_nat nj = 248 + e_pd en -> rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null en m ->
    pem_at en Σ (pem_ms en J_END1 m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f en)) (wz 0) (wz (e_flags en)) s5 (wz (e_f en)) (wz 0) s10 s11 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition opt_ent (o : option (Z * Z)) : list (Z * Z) := match o with Some e => [e] | None => [] end.
  Definition END_stmt : Prop :=
    forall (en : pem_entry) Σ m off crem lrem strs news j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (eH eD : Z) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
           (octx oname : option (Z * Z)) (ctxv namev nn hBv dBv ret : Z)
           (KX KY : mbk) (BMX BMY methX methY lenX maxX offX lenY maxY offY : Z) (blwX blwY : word),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent octx ++ opt_ent oname in
    pem_com en Σ m off crem lrem (cur ++ strs ++ news) -> pem_err en Σ strs m -> C_END <= crem ->
    pem_frame en m j0 lH lF endv eH eD x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) ->
    match octx with None => ctxv = 0 | Some e => e = (ctxv, ECTX) end ->
    match oname with None => namev = 0 | Some e => e = (namev, nn) /\ 1 <= nn /\ rw_cells asegs m namev [CB 0%nat []] end ->
    mbio_repx (rt_live RT Σ) m KX hBv BMX blwX methX lenX maxX offX -> mbio_repx (rt_live RT Σ) m KY dBv BMY blwY methY lenY maxY offY ->
    pem_out ret m (e_PN en) (e_PH en) (e_PD en) (e_PLN en) news -> 254 * news_sz news <= 255 * (off - e_boff en) + 254 * 512 ->
    pem_at en Σ (pem_ms en J_END m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f en)) (wz dBv) (wz (e_flags en)) (wz ret) (wz (e_f en))
                          (wz hBv) (wz namev) (wz ctxv) t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition RELOAD_stmt : Prop :=
    forall (en : pem_entry) Σ m off crem lrem strs news j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (eH eD : Z) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 t3 t4 t5 t6 : word)
           (octx oname : option (Z * Z)) (ctxv namev nn hBv dBv ret : Z)
           (KX KY : mbk) (BMX BMY methX methY lenX maxX offX lenY maxY offY : Z) (blwX blwY : word),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent octx ++ opt_ent oname in
    pem_com en Σ m off crem lrem (cur ++ strs ++ news) -> pem_err en Σ strs m -> C_END <= crem ->
    pem_frame en m j0 lH lF endv eH eD x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) ->
    match octx with None => ctxv = 0 | Some e => e = (ctxv, ECTX) end ->
    match oname with None => namev = 0 | Some e => e = (namev, nn) /\ 1 <= nn /\ rw_cells asegs m namev [CB 0%nat []] end ->
    mbio_repx (rt_live RT Σ) m KX hBv BMX blwX methX lenX maxX offX -> mbio_repx (rt_live RT Σ) m KY dBv BMY blwY methY lenY maxY offY ->
    pem_out ret m (e_PN en) (e_PH en) (e_PD en) (e_PLN en) news -> 254 * news_sz news <= 255 * (off - e_boff en) + 254 * 512 ->
    pem_at en Σ (pem_ms en J_RELOAD m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz dBv) s4 (wz ret) s6 (wz hBv) (wz namev) (wz ctxv) t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition FREE1X_stmt : Prop :=
    forall (en : pem_entry) Σ m off crem lrem strs j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s11 t3 t4 t5 t6 : word)
           (oname : option (Z * Z)) (namev nn hBv dBv : Z) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent oname in
    pem_com en Σ m off crem lrem (cur ++ strs) -> pem_err en Σ strs m -> C_END <= crem ->
    pem_frame en m j0 lH lF endv hBv dBv x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null en m ->
    match oname with None => namev = 0 | Some e => e = (namev, nn) /\ 1 <= nn /\ rw_cells asegs m namev [CB 0%nat []] end ->
    mbio_rep (rt_live RT Σ) m KX hBv methX lenX maxX 0 -> mbio_rep (rt_live RT Σ) m KY dBv methY lenY maxY 0 ->
    pem_at en Σ (pem_ms en J_FREE1X m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz (e_flags en)) s5 s6 s7 (wz namev) s11 t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition FREE1_stmt : Prop :=
    forall (en : pem_entry) Σ m off crem lrem strs j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s10 s11 t3 t4 t5 t6 : word)
           (LB1 hBv dBv : Z) (bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)] in
    pem_com en Σ m off crem lrem (cur ++ strs) -> pem_err en Σ strs m -> C_END + 1 <= crem ->
    pem_frame en m j0 lH lF endv hBv dBv x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null en m ->
    LB1 mod 16 = 0 -> length bs = 256%nat -> rw_cells asegs m LB1 [CB 256 bs] ->
    mbio_rep (rt_live RT Σ) m KX hBv methX lenX maxX 0 -> mbio_rep (rt_live RT Σ) m KY dBv methY lenY maxY 0 ->
    pem_at en Σ (pem_ms en J_FREE1 m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz LB1) s6 s7 s10 s11 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition RAISE1_stmt : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s10 s11 t3 t4 t5 t6 : word)
           (LB1 hBv dBv : Z) (bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)] in
    pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E en) [] m -> C_END + 6 <= crem -> 2 <= lrem ->
    pem_frame en m j0 lH lF endv hBv dBv x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null en m ->
    LB1 mod 16 = 0 -> length bs = 256%nat -> rw_cells asegs m LB1 [CB 256 bs] ->
    mbio_rep (rt_live RT Σ) m KX hBv methX lenX maxX 0 -> mbio_rep (rt_live RT Σ) m KY dBv methY lenY maxY 0 ->
    pem_at en Σ (pem_ms en J_RAISE1 m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz LB1) s6 s7 s10 s11 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition gn_need (en : pem_entry) (off : Z) : Z := C_END + 8 + 2 * (e_blen en - off) + grow_pot en 0 0.
  Definition GN_at (N : Z) : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a2 a4 a5 a6 a7 s3 s7 t3 t4 t5 t6 : word)
           (LB1 hBv dBv len fcall : Z) (bs : list byte) (KX KY : mbk) (methX methY maxX maxY : Z),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)] in
    e_blen en - off <= N ->
    pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E en) [] m -> gn_need en off <= crem -> 12 <= lrem ->
    pem_frame en m j0 lH (loc_F en) endv hBv dBv x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null en m ->
    LB1 mod 16 = 0 -> length bs = 256%nat -> rw_cells asegs m LB1 [CB 256 bs] -> 1 <= len <= 254 -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) ->
    0 <= fcall <= 1 ->
    mbio_rep (rt_live RT Σ) m KX hBv methX 0 maxX 0 -> mbio_rep (rt_live RT Σ) m KY dBv methY 0 maxY 0 -> maxX = 0 -> maxY = 0 ->
    pem_at en Σ (pem_ms en J_GN m F fc xra t0 t1 t2 a0 (wz len) a2 (wz fcall) a4 a5 a6 a7
                          (wz 6) s3 (wz LIT_BEGIN) (wz LB1) (wz LIT_TAIL) s7 (wz (Z.land (e_flags en) (Z.lnot 4))) (wz (LB1 - 6)) t3 t4 t5 t6).
  Definition GNG_at (N : Z) : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 t3 t4 t5 t6 : word)
           (LB1 hBv dBv : Z) (bs : list byte) (KX KY : mbk) (methX methY maxX maxY : Z),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)] in
    e_blen en - off <= N ->
    pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E en) [] m -> gn_need en off <= crem -> 12 <= lrem ->
    pem_frame en m j0 lH (loc_F en) endv hBv dBv x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null en m ->
    LB1 mod 16 = 0 -> length bs = 256%nat -> rw_cells asegs m LB1 [CB 256 bs] ->
    mbio_rep (rt_live RT Σ) m KX hBv methX 0 maxX 0 -> mbio_rep (rt_live RT Σ) m KY dBv methY 0 maxY 0 -> maxX = 0 -> maxY = 0 ->
    pem_at en Σ (pem_ms en J_GNG m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                          (wz 6) s3 (wz LIT_BEGIN) (wz LB1) (wz LIT_TAIL) s7 (wz (Z.land (e_flags en) (Z.lnot 4))) (wz (LB1 - 6)) t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition NAME_stmt : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
           (LB1 hBv dBv len' : Z) (bs : list byte) (KX KY : mbk) (methX methY maxX maxY : Z),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)] in
    pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E en) [] m -> gn_need en off <= crem -> 12 <= lrem ->
    pem_frame en m j0 lH (loc_F en) endv hBv dBv x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null en m ->
    LB1 mod 16 = 0 -> length bs = 256%nat -> rw_cells asegs m LB1 [CB 256 bs] -> 17 <= len' <= 255 ->
    nth_error bs (Z.to_nat (len' - 1)) = Some (Z_to_bv 8 10) -> nth_error bs (Z.to_nat len') = Some (Z_to_bv 8 0) ->
    mbio_rep (rt_live RT Σ) m KX hBv methX 0 maxX 0 -> mbio_rep (rt_live RT Σ) m KY dBv methY 0 maxY 0 -> maxX = 0 -> maxY = 0 ->
    pem_at en Σ (pem_ms en J_NAME m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                          (wz 6) (wz (LB1 + len' - 6)) (wz LIT_BEGIN) (wz LB1) (wz LIT_TAIL) (wz len') (wz (Z.land (e_flags en) (Z.lnot 4))) (wz (LB1 - 6)) t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition NGETS_stmt : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word)
           (LB2 namev nn hBv dBv : Z) (bn junk : list byte) (KX KY : mbk) (methX methY maxX maxY : Z),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)] in
    pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E en) [] m -> gn_need en off - 1 <= crem -> 11 <= lrem ->
    pem_frame en m j0 lH (loc_F en) endv hBv dBv x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null en m ->
    LB2 mod 16 = 0 -> length junk = 256%nat -> rw_cells asegs m LB2 [CB 256 junk] ->
    namev mod 16 = 0 -> 1 <= nn <= 239 -> length bn = Z.to_nat nn -> rw_cells asegs m namev [CB (Z.to_nat nn) bn] -> In (Z_to_bv 8 0) bn ->
    mbio_rep (rt_live RT Σ) m KX hBv methX 0 maxX 0 -> mbio_rep (rt_live RT Σ) m KY dBv methY 0 maxY 0 -> maxX = 0 -> maxY = 0 ->
    pem_at en Σ (pem_ms en J_NGETS m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz namev) (wz LB2) t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hd_need (en : pem_entry) (off maxX maxY : Z) : Z := C_END + 8 + 2 * (e_blen en - off) + grow_pot en maxX maxY.
  Definition hd_inv (en : pem_entry) (Σ : rts RT) (m : mem) (off crem lrem extra : Z) (j0 : list byte) (endv x1 x2 : word) (gap hj : list byte) (lenv : word) (j1 : list byte)
      (tav : word) (j2 : list byte) (bmv : word) (j3 : list byte) (LB2 namev nn hBv dBv tmp : Z) (bn bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY got : Z) : Prop :=
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)] in
       pem_com en Σ m off crem lrem cur /\ errst_at_rest (e_E en) [] m /\ hd_need en off maxX maxY + extra <= crem
    /\ (9 <= lrem /\ 19 <= lrem + Z.of_nat (length (mbio_ent KX maxX)) + Z.of_nat (length (mbio_ent KY maxY)))
    /\ pem_frame en m j0 (loc_H LB2 tmp) (loc_F en) endv hBv dBv x1 x2 gap /\ rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) /\ out_null en m
    /\ LB2 mod 16 = 0 /\ length bs = 256%nat /\ rw_cells asegs m LB2 [CB 256 bs]
    /\ namev mod 16 = 0 /\ 1 <= nn <= 239 /\ length bn = Z.to_nat nn /\ rw_cells asegs m namev [CB (Z.to_nat nn) bn] /\ In (Z_to_bv 8 0) bn
    /\ mbio_rep (rt_live RT Σ) m KX hBv methX lenX maxX 0 /\ mbio_rep (rt_live RT Σ) m KY dBv methY lenY maxY 0
    /\ 0 <= got <= 2 /\ (got < 2 -> tmp = hBv /\ lenY = 0 /\ maxY = 0 /\ endv = wz 0) /\ (got = 2 -> tmp = dBv) /\ (endv = wz 0 \/ endv = wz 1)
    /\ lenX + lenY <= 2 * (off - e_boff en) /\ maxX <= gr_n (lenX + 255) /\ maxY <= gr_n (lenY + 255).
  Definition HD_at (N : Z) : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 (pv : word) endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word)
           (LB2 namev nn hBv dBv tmp len got prev : Z) (bn bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    e_blen en - off <= N ->
    hd_inv en Σ m off crem lrem 0 j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 LB2 namev nn hBv dBv tmp bn bs KX KY methX methY lenX maxX lenY maxY got ->
    1 <= len <= 254 -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) -> 0 <= prev <= 1 ->
    (len < 254 -> off < e_blen en -> nth_error bs (Z.to_nat (len - 1)) = Some (Z_to_bv 8 10)) -> 254 * (lenX + lenY) <= 255 * (off - len - e_boff en) ->
    pem_at en Σ (pem_ms en J_HD m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz tmp) s3 (wz prev) (wz len) (wz got) pv (wz namev) (wz LB2) t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition GETS1_at (N : Z) : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 t3 t4 t5 t6 : word)
           (LB2 namev nn hBv dBv tmp got partial : Z) (bn bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    e_blen en - off <= N ->
    hd_inv en Σ m off crem lrem (-1) j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 LB2 namev nn hBv dBv tmp bn bs KX KY methX methY lenX maxX lenY maxY got ->
    0 <= partial <= 1 -> 254 * (lenX + lenY) <= 255 * (off - e_boff en) + (if off =? e_blen en then 254 else 0) ->
    pem_at en Σ (pem_ms en J_GETS1 m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz tmp) s3 s4 s5 (wz got) (wz partial) (wz namev) (wz LB2) t3 t4 t5 t6).
  Definition GETS2_at (N : Z) : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 t3 t4 t5 t6 : word)
           (LB2 namev nn hBv dBv tmp got got' partial : Z) (bn bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    e_blen en - off <= N ->
    hd_inv en Σ m off crem lrem (-1) j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 LB2 namev nn hBv dBv tmp bn bs KX KY methX methY lenX maxX lenY maxY got' ->
    0 <= partial <= 1 -> 0 <= got <= 2 -> 254 * (lenX + lenY) <= 255 * (off - e_boff en) + (if off =? e_blen en then 254 else 0) ->
    pem_at en Σ (pem_ms en J_GETS2 m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz got') s3 s4 s5 (wz got) (wz partial) (wz namev) (wz LB2) t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition HD2_at (N : Z) : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word)
           (LB2 namev nn hBv dBv tmp len got prev partial mask : Z) (bn bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    e_blen en - off <= N ->
    hd_inv en Σ m off crem lrem 0 j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 LB2 namev nn hBv dBv tmp bn bs KX KY methX methY lenX maxX lenY maxY got ->
    1 <= len <= 254 -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) -> 0 <= prev <= 1 -> 0 <= partial <= 1 ->
    (mask = e_flags en \/ mask = Z.land (e_flags en) (Z.lnot 4)) ->
    (len < 254 -> off < e_blen en -> nth_error bs (Z.to_nat (len - 1)) = Some (Z_to_bv 8 10)) -> 254 * (lenX + lenY) <= 255 * (off - len - e_boff en) ->
    pem_at en Σ (pem_ms en J_HD2 m F fc xra t0 t1 t2 a0 a1 (wz mask) a3 a4 a5 a6 a7 (wz tmp) s3 (wz prev) (wz len) (wz got) (wz partial) (wz namev) (wz LB2) t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition PUTS_at (N : Z) : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word)
           (LB2 namev nn hBv dBv tmp len len' got prev partial : Z) (bn bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    e_blen en - off <= N ->
    hd_inv en Σ m off crem lrem 0 j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 LB2 namev nn hBv dBv tmp bn bs KX KY methX methY lenX maxX lenY maxY got ->
    1 <= len' <= 255 -> nth_error bs (Z.to_nat (len' - 1)) = Some (Z_to_bv 8 10) -> nth_error bs (Z.to_nat len') = Some (Z_to_bv 8 0) ->
    0 <= prev <= 1 -> 0 <= partial <= 1 ->
    1 <= len <= 254 -> len' <= len + 1 -> (len < 254 -> off < e_blen en -> len' <= len) -> 254 * (lenX + lenY) <= 255 * (off - len - e_boff en) ->
    pem_at en Σ (pem_ms en J_PUTS m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz tmp) (wz len') (wz prev) s5 (wz got) (wz partial) (wz namev) (wz LB2) t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition ENDLINE_at (N : Z) : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 t3 t4 t5 t6 : word)
           (LB2 namev nn hBv dBv tmp len' got prev : Z) (bn bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    hd_inv en Σ m off crem lrem 0 j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 LB2 namev nn hBv dBv tmp bn bs KX KY methX methY lenX maxX lenY maxY got ->
    1 <= len' <= 255 -> nth_error bs (Z.to_nat len') = Some (Z_to_bv 8 0) -> 0 <= prev <= 1 -> 254 * (lenX + lenY) <= 255 * (off - e_boff en) ->
    pem_at en Σ (pem_ms en J_ENDLINE m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz got) s7 (wz namev) (wz LB2) t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition LFREE_stmt : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 t3 t4 t5 t6 : word)
           (LB2 namev nn hBv dBv hB' dB' : Z) (bn bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)] in
    pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E en) [] m -> C_END + 8 + mcost (lenX + 1) + mcost lenY <= crem -> 8 <= lrem ->
    pem_frame en m j0 lH (loc_F en) endv hBv dBv x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null en m ->
    LB2 mod 16 = 0 -> length bs = 256%nat -> rw_cells asegs m LB2 [CB 256 bs] ->
    namev mod 16 = 0 -> 1 <= nn <= 239 -> length bn = Z.to_nat nn -> rw_cells asegs m namev [CB (Z.to_nat nn) bn] -> In (Z_to_bv 8 0) bn ->
    mbio_rep (rt_live RT Σ) m KX hBv methX lenX maxX 0 -> mbio_rep (rt_live RT Σ) m KY dBv methY lenY maxY 0 -> 254 * (lenX + lenY) <= 255 * (off - e_boff en) ->
    ((hB' = hBv /\ dB' = dBv) \/ (hB' = dBv /\ dB' = hBv /\ lenY = 0 /\ maxY = 0)) ->
    pem_at en Σ (pem_ms en J_LFREE m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f en)) (wz dB') s4 s5 (wz (e_f en)) (wz hB') (wz namev) (wz LB2) t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition RAISE2_stmt : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word)
           (LB2 namev nn hBv dBv line : Z) (bn bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)] in
    pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E en) [] m -> C_END + 7 <= crem -> 2 <= lrem -> 0 <= line < 2 ^ 31 ->
    pem_frame en m j0 lH (loc_F en) endv hBv dBv x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null en m ->
    LB2 mod 16 = 0 -> length bs = 256%nat -> rw_cells asegs m LB2 [CB 256 bs] ->
    namev mod 16 = 0 -> 1 <= nn <= 239 -> length bn = Z.to_nat nn -> rw_cells asegs m namev [CB (Z.to_nat nn) bn] ->
    mbio_rep (rt_live RT Σ) m KX hBv methX lenX maxX 0 -> mbio_rep (rt_live RT Σ) m KY dBv methY lenY maxY 0 ->
    pem_at en Σ (pem_ms en J_RAISE2 m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz line) s3 s4 s5 s6 s7 (wz namev) (wz LB2) t3 t4 t5 t6).
  Definition FREE2_stmt : Prop :=
    forall (en : pem_entry) Σ m off crem lrem strs j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word)
           (LB2 namev nn hBv dBv : Z) (bn bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)] in
    pem_com en Σ m off crem lrem (cur ++ strs) -> pem_err en Σ strs m -> C_END + 1 <= crem ->
    pem_frame en m j0 lH (loc_F en) endv hBv dBv x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null en m ->
    LB2 mod 16 = 0 -> length bs = 256%nat -> rw_cells asegs m LB2 [CB 256 bs] ->
    namev mod 16 = 0 -> 1 <= nn <= 239 -> length bn = Z.to_nat nn -> rw_cells asegs m namev [CB (Z.to_nat nn) bn] ->
    mbio_rep (rt_live RT Σ) m KX hBv methX lenX maxX 0 -> mbio_rep (rt_live RT Σ) m KY dBv methY lenY maxY 0 ->
    pem_at en Σ (pem_ms en J_FREE2 m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz namev) (wz LB2) t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition TAIL_stmt : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (eH eD : Z) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s11 t3 t4 t5 t6 : word)
           (namev nn hBv dBv : Z) (bn : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn)] in
    pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E en) [] m -> C_END + 7 + mcost (lenX + 1) + mcost lenY <= crem -> 8 <= lrem ->
    pem_frame en m j0 lH (loc_F en) endv eH eD x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null en m ->
    namev mod 16 = 0 -> 1 <= nn <= 239 -> length bn = Z.to_nat nn -> rw_cells asegs m namev [CB (Z.to_nat nn) bn] -> In (Z_to_bv 8 0) bn ->
    mbio_rep (rt_live RT Σ) m KX hBv methX lenX maxX 0 -> mbio_rep (rt_live RT Σ) m KY dBv methY lenY maxY 0 -> 254 * (lenX + lenY) <= 255 * (off - e_boff en) ->
    pem_at en Σ (pem_ms en J_TAIL m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f en)) (wz dBv) (wz (e_flags en)) s5 (wz (e_f en)) (wz hBv) (wz namev) s11 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition INI_stmt : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 lH endv x1 x2 gap hj j1 tav j2 j3
           (F : bvmap 5 word) (fc : bv 32) (eH eD : Z) (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s11 t3 t4 t5 t6 : word)
           (ctxv namev nn hBv dBv BMY : Z) (bn : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)] in
    pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E en) [] m -> C_END + 7 + mcost (lenX + 1) + mcost lenY <= crem -> 7 <= lrem ->
    pem_frame en m j0 lH (loc_F en) endv eH eD x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj (wz lenY) j1 tav j2 (wz BMY) j3) -> out_null en m ->
    ctxv mod 16 = 0 -> rw_cells asegs m ctxv [CB (Z.to_nat ECTX) (repeat (Z_to_bv 8 0) (Z.to_nat ECTX))] ->
    namev mod 16 = 0 -> 1 <= nn <= 239 -> length bn = Z.to_nat nn -> rw_cells asegs m namev [CB (Z.to_nat nn) bn] -> In (Z_to_bv 8 0) bn ->
    mbio_rep (rt_live RT Σ) m KX hBv methX lenX maxX 0 -> mbio_repx (rt_live RT Σ) m KY dBv BMY (wz lenY) methY lenY maxY 0 -> 1 <= lenY -> 254 * (lenX + lenY) <= 255 * (off - e_boff en) ->
    pem_at en Σ (pem_ms en J_INI m F fc xra t0 t1 t2 (wz ctxv) a1 a2 a3 a4 a5 a6 a7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz namev) s11 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition DEC_stmt : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 lH endv x1 x2 gap hj j1 tav j2 j3 cj
           (F : bvmap 5 word) (fc : bv 32) (eH eD : Z) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 t3 t4 t5 t6 : word)
           (ctxv namev nn hBv dBv BMY dlen : Z) (bn : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)] in
    pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E en) [] m -> C_END + 4 + mcost (lenX + 1) + mcost lenY <= crem -> 6 <= lrem ->
    pem_frame en m j0 lH (loc_F en) endv eH eD x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj (wz dlen) j1 tav j2 (wz BMY) j3) -> out_null en m ->
    ctxv mod 16 = 0 -> length cj = Z.to_nat ECTX -> rw_cells asegs m ctxv [CB (Z.to_nat ECTX) cj] ->
    namev mod 16 = 0 -> 1 <= nn <= 239 -> length bn = Z.to_nat nn -> rw_cells asegs m namev [CB (Z.to_nat nn) bn] -> In (Z_to_bv 8 0) bn ->
    mbio_rep (rt_live RT Σ) m KX hBv methX lenX maxX 0 -> mbio_repx (rt_live RT Σ) m KY dBv BMY (wz dlen) methY lenY maxY 0 -> 0 <= dlen <= lenY -> 254 * (lenX + lenY) <= 255 * (off - e_boff en) ->
    pem_at en Σ (pem_ms en J_DEC m F fc xra t0 t1 t2 a0 a1 (wz 0) a3 a4 a5 a6 a7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz namev) (wz ctxv) t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition RZT_stmt : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 cj
           (F : bvmap 5 word) (fc : bv 32) (eH eD : Z) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 t3 t4 t5 t6 : word)
           (ctxv namev nn hBv dBv : Z) (bn : list byte) (KX KY : mbk) (BMX BMY methX methY lenX maxX offX lenY maxY offY : Z) (blwX blwY : word),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)] in
    pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E en) [] m -> C_END + 6 <= crem -> 2 <= lrem ->
    pem_frame en m j0 lH (loc_F en) endv eH eD x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null en m ->
    ctxv mod 16 = 0 -> length cj = Z.to_nat ECTX -> rw_cells asegs m ctxv [CB (Z.to_nat ECTX) cj] ->
    namev mod 16 = 0 -> 1 <= nn <= 239 -> length bn = Z.to_nat nn -> rw_cells asegs m namev [CB (Z.to_nat nn) bn] -> In (Z_to_bv 8 0) bn ->
    mbio_repx (rt_live RT Σ) m KX hBv BMX blwX methX lenX maxX offX -> mbio_repx (rt_live RT Σ) m KY dBv BMY blwY methY lenY maxY offY ->
    pem_at en Σ (pem_ms en J_RZT m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz namev) (wz ctxv) t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition OUTFREE_stmt : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 cj
           (F : bvmap 5 word) (fc : bv 32) (eH eD : Z) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 t3 t4 t5 t6 : word)
           (ohdr : option (Z * Z)) (ctxv namev nn hBv dBv HD nh : Z) (bn bh : list byte) (KX KY : mbk) (BMX BMY methX methY lenX maxX offX lenY maxY offY : Z) (blwX blwY : word),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)] ++ opt_ent ohdr in
    pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E en) [] m -> C_END + 2 <= crem ->
    pem_frame en m j0 lH (loc_F en) endv eH eD x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) ->
    ctxv mod 16 = 0 -> length cj = Z.to_nat ECTX -> rw_cells asegs m ctxv [CB (Z.to_nat ECTX) cj] ->
    namev mod 16 = 0 -> 1 <= nn <= 239 -> length bn = Z.to_nat nn -> rw_cells asegs m namev [CB (Z.to_nat nn) bn] -> In (Z_to_bv 8 0) bn ->
    match ohdr with None => HD = 0 | Some e => e = (HD, nh) /\ 1 <= nh /\ HD mod 16 = 0 /\ length bh = Z.to_nat nh /\ rw_cells asegs m HD [CB (Z.to_nat nh) bh] end ->
    mbio_repx (rt_live RT Σ) m KX hBv BMX blwX methX lenX maxX offX -> mbio_repx (rt_live RT Σ) m KY dBv BMY blwY methY lenY maxY offY ->
    rw_cells asegs m (e_PN en) [C8 (wz 0)] -> rw_cells asegs m (e_PH en) [C8 (wz HD)] -> rw_cells asegs m (e_PD en) [C8 (wz 0)] -> rw_cells asegs m (e_PLN en) [C8 (wz 0)] ->
    pem_at en Σ (pem_ms en J_OUTFREE m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz namev) (wz ctxv) t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition RAISE0_stmt : Prop :=
    forall (en : pem_entry) Σ m crem lrem j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s10 s11 t3 t4 t5 t6 : word) (lE : list cell),
    pem_com en Σ m (e_boff en) crem lrem [] -> errst_at_rest (e_E en) [] m -> C_END + 6 <= crem -> 2 <= lrem ->
    rw_cells asegs m (e_sp1 en) [CB 24 j0] -> rw_cells asegs m (e_sp1 en + 24) lH -> Z.of_nat (cells_size lH) = 56 ->
    rw_cells asegs m (e_sp1 en + 80) lF -> Z.of_nat (cells_size lF) = 24 -> rw_cells asegs m (e_sp1 en + 104) [C8 endv] ->
    rw_cells asegs m (e_sp1 en + 112) lE -> Z.of_nat (cells_size lE) = 104 -> rw_cells asegs m (e_sp1 en + 216) [C8 (wz (e_BI en))] ->
    rw_cells asegs m (e_sp1 en + 224) [C8 x1; C8 x2; C8 (wz (e_f en))] -> rw_cells asegs m (e_sp1 en + 248) [CB (Z.to_nat (e_pd en)) gap] ->
    rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null en m ->
    pem_at en Σ (pem_ms en J_RAISE0 m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f en)) s3 (wz (e_flags en)) s5 (wz (e_f en)) s7
                          s10 s11 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition J0N_stmt : Prop :=
    forall (en : pem_entry) Σ m crem lrem j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a0 a1 a6 a7 s7 t3 t4 t5 t6 : word) (lE : list cell),
    pem_com en Σ m (e_boff en) crem lrem [] -> errst_at_rest (e_E en) [] m -> gn_need en (e_boff en) + 4 <= crem -> 21 <= lrem ->
    rw_cells asegs m (e_sp1 en) [CB 24 j0] -> rw_cells asegs m (e_sp1 en + 24) lH -> Z.of_nat (cells_size lH) = 56 ->
    rw_cells asegs m (e_sp1 en + 80) lF -> Z.of_nat (cells_size lF) = 24 -> rw_cells asegs m (e_sp1 en + 104) [C8 endv] ->
    rw_cells asegs m (e_sp1 en + 112) lE -> Z.of_nat (cells_size lE) = 104 -> rw_cells asegs m (e_sp1 en + 216) [C8 (wz (e_BI en))] ->
    rw_cells asegs m (e_sp1 en + 224) [C8 x1; C8 x2; C8 (wz (e_f en))] -> rw_cells asegs m (e_sp1 en + 248) [CB (Z.to_nat (e_pd en)) gap] ->
    rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null en m ->
    pem_at en Σ (pem_ms en J_J0N m F fc xra t0 t1 t2 a0 a1 (wz (shad (e_PD en))) (wz (shad (e_PH en))) (wz (shad (e_PLN en))) (wz (shad (e_PN en))) a6 a7
                          (wz (e_f en)) (wz (e_PLN en)) (wz (e_flags en)) (wz (e_PN en)) (wz (e_f en)) s7 (wz (e_PD en)) (wz (e_PH en)) t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition J0G_stmt : Prop :=
    forall (en : pem_entry) Σ m off crem lrem j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3
           (F : bvmap 5 word) (fc : bv 32) (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s10 s11 t3 t4 t5 t6 : word)
           (LB1 hBv dBv len : Z) (bs : list byte) (KX KY : mbk) (methX methY maxX maxY : Z),
    let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)] in
    pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E en) [] m -> gn_need en off <= crem -> 12 <= lrem ->
    pem_frame en m j0 lH lF endv hBv dBv x1 x2 gap -> rw_cells asegs m (e_f en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null en m ->
    LB1 mod 16 = 0 -> length bs = 256%nat -> rw_cells asegs m LB1 [CB 256 bs] -> 1 <= len <= 254 -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) ->
    mbio_rep (rt_live RT Σ) m KX hBv methX 0 maxX 0 -> mbio_rep (rt_live RT Σ) m KY dBv methY 0 maxY 0 -> maxX = 0 -> maxY = 0 ->
    pem_at en Σ (pem_ms en J_J0G m F fc xra t0 t1 t2 (wz len) a1 a2 a3 a4 a5 a6 a7 s2 (wz dBv) s4 (wz LB1) s6 (wz hBv) s10 s11 t3 t4 t5 t6).
End W3.
